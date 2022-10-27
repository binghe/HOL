/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
========================================================================*/


// Trusted SAT evaluation

#include <ctype.h>

#include "tbdd.h"
#include "prover.h"
#include "clause.h"
#include "pseudoboolean.h"


using namespace trustbdd;

#define DEFAULT_SEED 123456

// GC Parameters
// Minimum number of dead nodes to trigger GC
#define COLLECT_MIN_LRAT 150000
#define COLLECT_MIN_DRAT  20000
// Minimum fraction of dead:total nodes to trigger GC
#define COLLECT_FRACTION 0.10

// Functions to aid parsing of schedule lines


// Skip line.  Return either \n or EOF
static int skip_line(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    return c;
    }
    return c;
}

// Skip any whitespace characters other than newline
// Read and return either EOF or first non-space character (possibly newline)
static int skip_space(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    return c;
	if (!isspace(c)) {
	    return c;
	}
    }
    return c;
}

// Read rest of line, trimming off leading spaces and trailing newline.
// Return line length
static int get_line(FILE *infile, char *buf, int maxlen) {
    int c = skip_space(infile);
    int pos = 0;
    if (c == EOF || c == '\n') {
	buf[pos] = 0;
	return pos;
    }
    buf[pos++] = c;
    while (true) {
	c = getc(infile);
	if (c == '\n' || c == EOF) {
	    if (pos < maxlen)
		buf[pos] = 0;
	    else
		buf[--pos] = 0;
	    break;
	}
	if (pos < maxlen)
	    buf[pos++] = c;
    }
    return pos;
}


// Read line and parse as set of numbers.  Return either \n or EOF
static int get_numbers(FILE *infile, std::vector<int> &numbers) {
    int c;
    int val;
    numbers.resize(0,0);
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    break;
	if (isspace(c))
	    continue;
	ungetc(c, infile);
	if (fscanf(infile, "%d", &val) != 1) {
	    break;
	}
	numbers.push_back(val);
    }
    return c;
}

// Read line and parse as set of numbers.  Return either \n or EOF
static int get_number_pairs(FILE *infile, std::vector<int> &numbers1, std::vector<int> &numbers2, char sep) {
    int c;
    int val;
    numbers1.resize(0,0);
    numbers2.resize(0,0);
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    break;
	if (isspace(c))
	    continue;
	ungetc(c, infile);
	if (fscanf(infile, "%d", &val) != 1) {
	    break;
	}
	numbers1.push_back(val);
	c = getc(infile);
	if (c != sep) {
	    /** ERROR **/
	    c = 0;
	    break;
	}
	if (fscanf(infile, "%d", &val) != 1) {
	    c = 0;
	    break;
	}
	numbers2.push_back(val);
    }
    return c;
}

/*
  Generator for phase selection when generating solutions
 */
typedef enum { GENERATE_LOW, GENERATE_HIGH, GENERATE_RANDOM } generator_t;

class PhaseGenerator {
public:

    PhaseGenerator(generator_t gtype, int seed) 
    {
	if (gtype == GENERATE_RANDOM)
	    seq = new Sequencer(seed);
	else
	    seq = NULL;
    }

    PhaseGenerator(PhaseGenerator &pg) {
	gtype = pg.gtype;
	seq = new Sequencer(*(pg.seq));
    }

    ~PhaseGenerator() { if (seq) delete seq; }

    int phase() {
	switch (gtype) {
	case GENERATE_LOW:
	    return 0;
	case GENERATE_HIGH:
	    return 1;
	default:
	    return seq->next() & 0x1;
	}
    }

private:
    Sequencer *seq;
    generator_t gtype;
    
};


/*
  Represent one step in solution generation following sequence of
  existential quantifications. Solution represented as cube BDD
 */
class Quantification {
    
public:
    Quantification(ilist vars, bdd lconstraint) {
	variables = ilist_copy(vars);
	ilist_sort(variables);
	local_constraint = lconstraint;
    }

    Quantification(std::vector<int> &vars, bdd lconstraint) {
	variables = ilist_copy_list(vars.data(), vars.size());
	local_constraint = lconstraint;
    }


    ~Quantification() { ilist_free(variables); }

    // Extend partial solution BDD with assignments to quantified variables
    bdd solve_step(bdd solution, PhaseGenerator *pg) {
	// Only need to consider part of local constraint consistent with partial solution
	bdd constraint = bdd_restrict(local_constraint, solution);
	for (int i = ilist_length(variables)-1; i >= 0; i--) {
	    int var = variables[i];
	    int p = pg->phase();
	    bdd litbdd = p ? bdd_ithvar(var) : bdd_nithvar(var);
	    bdd nconstraint = bdd_restrict(constraint, litbdd);
	    if (nconstraint == bdd_false()) {
		p = !p;
		litbdd = p ? bdd_ithvar(var) : bdd_nithvar(var);
		nconstraint = bdd_restrict(constraint, litbdd);
	    }
	    constraint = nconstraint;
	    solution = bdd_and(litbdd, solution);
	    if (verbosity_level >= 3) {
		std::cout << "c Assigned value " << p << " to variable V" << var << std::endl;
	    }
	}
	return solution;
    }

    // Impose top-level constraint on this level.  Return resulting existential quantification
    bdd exclude_step(bdd upper_constraint) {
	bdd nlocal_constraint = bdd_and(local_constraint, upper_constraint);
	if (nlocal_constraint == local_constraint)
	    return bdd_true();
	if (verbosity_level >= 3) {
	    printf("c Imposing new constraint on variables V"); ilist_print(variables, stdout, " V"); printf("\n");
	}
	local_constraint = nlocal_constraint;
	bdd varbdd = bdd_makeset(variables, ilist_length(variables));
	bdd down_constraint = bdd_exist(local_constraint, varbdd);
	return down_constraint;
    }

    // Variables used in quantification
    ilist variables;
    // Local constraint before quantification
    bdd local_constraint;

};

class Solver {
public:

    Solver(PhaseGenerator *pg) {
	phase_gen = pg;
	constraint_function = bdd_true();
    }

    ~Solver() { 
	constraint_function = bdd_true();
	for (Quantification *qs : qsteps) delete qs;
    }

    void set_constraint(bdd bfun) {
	constraint_function = bfun;
    }

    void add_step(ilist vars, bdd fun) {
	qsteps.push_back(new Quantification(vars, fun));
    }

    void add_step(std::vector<int> &vars, bdd fun) {
	qsteps.push_back(new Quantification(vars, fun));
    }



    // Generate another solution BDD 
    bdd next_solution() {
	if (constraint_function == bdd_false())
	    return bdd_false();
	bdd solution = bdd_true();
	bdd constraint = bdd_true();
	for (int i = qsteps.size()-1; i >= 0; i--)
	    solution = qsteps[i]->solve_step(solution, phase_gen);
	return solution;
    }

    // Impose additional constraint on set of solutions
    void impose_constraint(bdd constraint) {
	for (int i = 0; i < qsteps.size(); i++) {
	    constraint = qsteps[i]->exclude_step(constraint);
	    if (constraint == bdd_true())
		break;
	}
	constraint_function = bdd_and(constraint_function, constraint);
    }

private:
    PhaseGenerator *phase_gen;
    bdd constraint_function;
    std::vector<Quantification*> qsteps;

};



static int next_term_id = 1;

class Term {
private:
    int term_id;
    bool is_active;
    tbdd tfun;
    xor_constraint *xor_equation;
    int node_count;

public:
    Term (tbdd t) { 
	term_id = next_term_id++;
	is_active = true; 
	tfun = t;
	node_count = bdd_nodecount(t.get_root());
	xor_equation = NULL;
    }

    // Returns number of dead nodes generated
    int deactivate() {
	tfun = tbdd_null();  // Should delete reference to previous value
	is_active = false;
	int rval = node_count;
	node_count = 0;
	if (xor_equation != NULL)
	    delete xor_equation;
	xor_equation = NULL;
	return rval;
    }

    bool active() {
	return is_active;
    }

    tbdd &get_fun() { return tfun; }

    bdd get_root() { return tfun.get_root(); }

    int get_clause_id() { return tfun.get_clause_id(); }

    xor_constraint *get_equation() { return xor_equation; }

    void set_equation(xor_constraint *eq) { xor_equation = eq; }

    void set_term_id(int val) { term_id = val; }

    int get_term_id() { return term_id; }

    int get_node_count() { return node_count; }

private:

};

class TermSet {
private:
    int min_active;
    std::vector<Term *> terms;
    int clause_count;
    int32_t max_variable;
    int verblevel;
    proof_type_t proof_type;
    // Estimated total number of nodes
    int total_count;
    // Estimated number of unreachable nodes
    int dead_count;
    // Counters used by proof generator
    int variable_count;
    int last_clause_id;
  
    // For generating solutions
    bool generate_solution;
    Solver *solver;

    // For managing bucket elimination
    // Track which variables have been assigned to a bucket
    std::unordered_set<int> eliminated_variables;

    // Statistics
    int and_count;
    int quant_count;
    int equation_count;
    int max_bdd;

    void check_gc() {
	int collect_min = proof_type == PROOF_LRAT ? COLLECT_MIN_LRAT : COLLECT_MIN_DRAT;
	if (dead_count >= collect_min && (double) dead_count / total_count >= COLLECT_FRACTION) {
	    if (verbosity_level >= 2) {
		std::cout << "c Initiating GC.  Estimated total nodes = " << total_count << ".  Estimated dead nodes = " << dead_count << std::endl;
	    }
	    bdd_gbc();
	    total_count -= dead_count;
	    dead_count = 0;
	}
    }

    // Prepare to load with new set of terms
    void reset() {
	next_term_id = 1;
	min_active = 1;
	// Will number terms starting at 1
	terms.resize(1, NULL);
    }

public:

    TermSet(CNF &cnf, FILE *proof_file, ilist variable_ordering, int verb, proof_type_t ptype, bool binary, Solver *sol) {
	verblevel = verb;
	proof_type = ptype;
	tbdd_set_verbose(verb);
	total_count = dead_count = 0;
	clause_count = cnf.clause_count();
	max_variable = cnf.max_variable();
	last_clause_id = clause_count;
	variable_count = max_variable;
	solver = sol;

	ilist *clauses = new ilist[clause_count];
	for (int i = 0; i < clause_count; i++) {
	    Clause *cp = cnf[i];
	    clauses[i] = cp->data();
	}
	int rcode;
	tbdd_set_verbose(verblevel);
	if ((rcode = tbdd_init(proof_file, &variable_count, &last_clause_id, clauses, variable_ordering, ptype, binary)) != 0) {
	    fprintf(stdout, "c Initialization failed.  Return code = %d\n", rcode);
	    exit(1);
	}
	// Want to number terms starting at 1
	terms.resize(1, NULL);
	for (int i = 1; i <= clause_count; i++) {
	    tbdd tc = tbdd_from_clause_id(i);
	    add(new Term(tc));
	}
	min_active = 1;
	and_count = 0;
	quant_count = 0;
	equation_count = 0;
	max_bdd = 0;
    }
  
    void add(Term *tp) {
	tp->set_term_id(terms.size());
	max_bdd = std::max(max_bdd, bdd_nodecount(tp->get_root()));
	terms.push_back(tp);
	if (verblevel >= 4) 
	    std::cout << "c Adding term #" << tp->get_term_id() << std::endl;
	total_count += tp->get_node_count();
    }

    Term *conjunct(Term *tp1, Term *tp2) {
	tbdd tr1 = tp1->get_fun();
	tbdd tr2 = tp2->get_fun();
	tbdd nfun = tbdd_and(tr1, tr2);
	add(new Term(nfun));
	dead_count += tp1->deactivate();
	dead_count += tp2->deactivate();
	check_gc();
	and_count++;
	return terms.back();
    }

    Term *equantify(Term *tp, std::vector<int> &vars) {
	int *varset = vars.data();
	bdd varbdd = bdd_makeset(varset, vars.size());
	bdd nroot = bdd_exist(tp->get_root(), varbdd);
	tbdd tfun = tbdd_validate(nroot, tp->get_fun());
	for (int var : vars) {
	    eliminated_variables.insert(var);
	}
	if (solver)
	    solver->add_step(vars, tp->get_root());
	add(new Term(tfun));
	dead_count += tp->deactivate();
	check_gc();
	quant_count++;
	return terms.back();
    }

    Term *equantify(Term *tp, int32_t var) {
	std::vector<int> vars;
	vars.push_back(var);
	return equantify(tp, vars);
    }

    Term *xor_constrain(Term *tp, std::vector<int> &vars, int constant) {
	ilist variables = ilist_copy_list(vars.data(), vars.size());
	xor_constraint *xor_equation = new xor_constraint(variables, constant, tp->get_fun());
	Term *tpn = new Term(xor_equation->get_validation());
	tpn->set_equation(xor_equation);
	add(tpn);
	dead_count += tp->deactivate();
	check_gc();
	equation_count++;
	return terms.back();
    }

    // Form conjunction of terms until reduce to <= 1 term
    // Effectively performs a tree reduction
    // Return final bdd
    tbdd tree_reduce() {
	Term *tp1, *tp2;
	while (true) {
	    while (min_active < terms.size() && !terms[min_active]->active())
		min_active++;
	    if (min_active >= terms.size())
		// Didn't find any terms.  Formula is tautology
		return tbdd_tautology();
	    tp1 = terms[min_active++];
	    while (min_active < terms.size() && !terms[min_active]->active())
		min_active++;
	    if (min_active >= terms.size()) {
		// There was only one term left
		tbdd result = tp1->get_fun();
		dead_count +=  tp1->deactivate();
		return result;
	    }
	    tp2 = terms[min_active++];
	    Term *tpn = conjunct(tp1, tp2);
	    if (tpn->get_root() == bdd_false()) {
		tbdd result = tpn->get_fun();
		return result;
	    }
	}
    }


    tbdd bucket_reduce() {
	std::vector<int> *buckets = new std::vector<int>[max_variable+1];
	int tcount = 0;
	int bcount = 0;
	for (int i = min_active; i < terms.size(); i++) {
	    Term *tp = terms[i];
	    if (!tp->active())
		continue;
	    bdd root = tp->get_root();
	    if (root == bdd_false()) {
		// Formula is trivially false
		tbdd result = tp->get_fun();
		return result;
	    }
	    if (root != bdd_true()) {
		int toplevel = bdd_var2level(bdd_var(root));
		if (buckets[toplevel].size() == 0)
		    bcount++;
		buckets[toplevel].push_back(i);
		tcount++;
	    }
	}
	if (verblevel >= 1)
	    std::cout << "c Placed " << tcount << " terms into " << bcount << " buckets." << std::endl;

	// Report status ~20 times during bucket elimination
	int report_level = bcount / 20;
	if (report_level == 0)
	    report_level = 1;

	for (int blevel = 1 ; blevel <= max_variable; blevel++) {
	    int next_idx = 0;
	    int bvar = bdd_level2var(blevel);
	    if (buckets[blevel].size() == 0) {
		if (solver && eliminated_variables.count(blevel) == 0) {
		    // Insert step so that solver will assign value to blevel
		    int vbuf[ILIST_OVHD+1];
		    ilist vlist = ilist_make(vbuf, 1);
		    ilist_fill1(vlist, bvar);
		    solver->add_step(vlist, bdd_true());
		}
		if (verblevel >= 3)
		    std::cout << "c Bucket " << blevel << " empty.  Skipping" << std::endl;
		continue;
	    }
	    while (next_idx < buckets[blevel].size() - 1) {
		Term *tp1 = terms[buckets[blevel][next_idx++]];
		Term *tp2 = terms[buckets[blevel][next_idx++]];
		Term *tpn = conjunct(tp1, tp2);
		bdd root = tpn->get_root();
		if (root == bdd_false()) {
		    if (verblevel >= 3)
			std::cout << "c Bucket " << blevel << " Conjunction of terms " 
				  << tp1->get_term_id() << " and " << tp2->get_term_id() << " yields FALSE" << std::endl;
		    tbdd result = tpn->get_fun();
		    return result;
		}
		int toplevel = bdd_var2level(bdd_var(root));
		if (verblevel >= 3)
		    std::cout << "c Bucket " << blevel << " Conjunction of terms " 
			      << tp1->get_term_id() << " and " << tp2->get_term_id() << " yields term " 
			      << tpn->get_term_id() << " with " << tpn->get_node_count() << " nodes, and with top level " << toplevel << std::endl;
		buckets[toplevel].push_back(tpn->get_term_id());
	    }
	    if (next_idx == buckets[blevel].size()-1) {
		Term *tp = terms[buckets[blevel][next_idx]];
		Term *tpn = equantify(tp, bvar);

		bdd root = tpn->get_root();
		if (verblevel >= 1 && (blevel % report_level == 0 || verblevel >= 3))
		    std::cout << "c Bucket " << blevel << " Reduced to term with " << tpn->get_node_count() << " nodes" << std::endl;
		if (root == bdd_true()) {
		    if (verblevel >= 3)
			std::cout << "c Bucket " << blevel << " Quantification of term " 
				  << tp->get_term_id() << " yields TRUE" << std::endl;
		} else {
		    int toplevel = bdd_var2level(bdd_var(root));
		    buckets[toplevel].push_back(tpn->get_term_id());
		    if (verblevel >= 3) {
			std::cout << "c Bucket " << blevel << " Quantification of term " 
				  << tp->get_term_id() << " yields term " << tpn->get_term_id() 
				  << " with top level " << toplevel << std::endl;
		    }

		}
	    } else {
		if (solver) {
		    // Insert step so that solver will assign value to blevel
		    int vbuf[ILIST_OVHD+1];
		    ilist vlist = ilist_make(vbuf, 1);
		    ilist_fill1(vlist, bvar);
		    solver->add_step(vlist, bdd_true());
		}
		if (verblevel >= 3)
		    std::cout << "c Bucket " << blevel << " cleared before quantifying." << std::endl;
	    }
	}
	// If get here, formula must be satisfiable
	if (verblevel >= 1) {
	    std::cout << "c Tautology" << std::endl;
	}
	return tbdd_tautology();
    }

    tbdd schedule_reduce(FILE *schedfile) {
	int line = 1;
	int modulus = INT_MAX;
	int constant;
	int i;
	std::vector<Term *> term_stack;
	std::vector<int> numbers;
	std::vector<int> numbers2;
	while (true) {
	    int c;
	    if ((c = skip_space(schedfile)) == EOF)
		break;
	    switch(c) {
	    case '\n':
		line++;
		break;
	    case '#':
		c = skip_line(schedfile);
		line++;
		break;
	    case 'i': 
		if (term_stack.size() > 0 && verblevel > 0) {
		    char buf[1024];
		    int len = get_line(schedfile, buf, 1024);
		    Term *tp = term_stack.back();
		    int term_id = tp->get_term_id();
		    bdd root = tp->get_root();
		    std::cout << "c Term #" << term_id << ". Nodes = " << bdd_nodecount(root) << ". " << buf << std::endl;
		}
		break;
	    case 'c':
		c = get_numbers(schedfile, numbers);
		if (c != '\n' && c != EOF) {
		    fprintf(stdout, "c Schedule line #%d.  Clause command. Non-numeric argument '%c'\n", line, c);
		    exit(1);
		}
		for (int i = 0; i < numbers.size(); i++) {
		    int ci = numbers[i];
		    if (ci < 1 || ci > clause_count) {
			fprintf(stdout, "c Schedule line #%d.  Invalid clause number %d\n", line, ci);
			exit(1);
		    }
		    if (ci >= terms.size()) {
			fprintf(stdout, "c Schedule line #%d.  Internal error.  Attempting to get clause #%d, but only have %d terms\n", line, ci, (int) terms.size()-1);
			exit(1);
		    }
		    term_stack.push_back(terms[ci]);
		}
		if (verblevel >= 3) {
		    std::cout << "c Schedule line #" << line << ".  Pushed " << numbers.size() 
			      << " clauses.  Stack size = " << term_stack.size() << std::endl;
		}
		line ++;
		break;
	    case 'a':
		c = get_numbers(schedfile, numbers);
		if (c != '\n' && c != EOF) {
		    fprintf(stdout, "c Schedule line #%d.  And command. Non-numeric argument '%c'\n", line, c);
		    exit(1);
		}
		if (numbers.size() != 1) {
		    fprintf(stdout, "c Schedule line #%d.  Should specify number of conjunctions\n", line);
		    exit(1);
		} else {
		    int ccount = numbers[0];
		    if (ccount < 1 || ccount > term_stack.size()-1) {
			fprintf(stdout, 
				"Schedule line #%d.  Cannot perform %d conjunctions.  Stack size = %d\n",
				line, ccount, (int) term_stack.size());
			exit(1);
		    }
		    Term *product = term_stack.back();
		    term_stack.pop_back();
		    if (!product->active()) {
			fprintf(stdout, "c Schedule line #%d.  Attempting to reuse clause #%d\n", line, product->get_term_id());
			exit(1);
		    }
		    while (ccount-- > 0) {
			Term *tp = term_stack.back();
			term_stack.pop_back();
			if (!tp->active()) {
			    fprintf(stdout, "c Schedule line #%d.  Attempting to reuse clause #%d\n", line, tp->get_term_id());
			    exit(1);
			}
			product = conjunct(product, tp);
			if (product->get_root() == bdd_false()) {
			    if (verblevel >= 2) {
				std::cout << "c Schedule line #" << line << ".  Generated BDD 0" << std::endl;
			    }
			    tbdd result = product->get_fun();
			    return result;
			}
		    }
		    term_stack.push_back(product);
		    if (verblevel >= 3) {
			std::cout << "c Schedule line #" << line << ".  Performed " << numbers[0]
				  << " conjunctions to get term #" << product->get_term_id() << ".  Stack size = " << term_stack.size() << std::endl;
		    }
		}
		line ++;
		break;
	    case 'q':
		c = get_numbers(schedfile, numbers);
		if (c != '\n' && c != EOF) {
		    fprintf(stdout, "c Schedule line #%d.  Quantify command. Non-numeric argument '%c'\n", line, c);
		    exit(1);
		}
		for (int i = 0; i < numbers.size(); i++) {
		    int vi = numbers[i];
		    if (vi < 1 || vi > max_variable) {
			fprintf(stdout, "c Schedule line #%d.  Invalid variable %d\n", line, vi);
			exit(1);
		    }
		}
		if (term_stack.size() < 1) {
		    fprintf(stdout, "c Schedule line #%d.  Cannot quantify.  Stack is empty\n", line);
		    exit(1);
		} else {
		    Term *tp = term_stack.back();
		    term_stack.pop_back();
		    Term *tpn = equantify(tp, numbers);
		    term_stack.push_back(tpn);
		    if (verblevel >= 3) {
			std::cout << "c Schedule line #" << line << ".  Quantified " << numbers.size()
				  << " variables to get Term #" << tpn->get_term_id() << ".  Stack size = " << term_stack.size() << std::endl;
		    }
		}
		line ++;
		break;
	    case '=':
		// See if there's a modulus 
		c = getc(schedfile);
		if (isdigit(c)) {
		    ungetc(c, schedfile);
		    if (fscanf(schedfile, "%d", &modulus) != 1) {
			fprintf(stdout, "c Schedule line #%d.  Invalid modulus\n", line);
			exit(1);
		    } else if (modulus != 2) {
			fprintf(stdout, "c Schedule line #%d.  Only support modulus 2\n", line);
			exit(1);
		    }
		} else {
		    fprintf(stdout, "c Schedule line #%d.  Modulus required\n", line);
		    exit(1);
		}
		if (fscanf(schedfile, "%d", &constant) != 1) {
		    fprintf(stdout, "c Schedule line #%d.  Constant term required\n", line);
		    exit(1);
		}
		if (constant < 0 || constant >= modulus) {
		    fprintf(stdout, "c Schedule line #%d.  Constant term %d invalid.  Must be between 0 and %d\n", line, constant, modulus-1);
		    exit(1);
		}
		c = get_number_pairs(schedfile, numbers2, numbers, '.');
		if (c != '\n' && c != EOF) {
		    fprintf(stdout, "c Schedule line #%d.  Could not parse equation terms\n", line);
		    exit(1);
		}
		for (i = 0; i < numbers2.size(); i++) {
		    int coeff = numbers2[i];
		    if (coeff != 1) {
			fprintf(stdout, "c Schedule line #%d.  Invalid coefficient %d\n", line, coeff);
			exit(1);
		    }
		}
		if (term_stack.size() < 1) {
		    fprintf(stdout, "c Schedule line #%d.  Cannot extract equation.  Stack is empty\n", line);
		    exit(1);
		} else {
		    Term *tp = term_stack.back();
		    term_stack.pop_back();
		    Term *tpn = xor_constrain(tp, numbers, constant);
		    term_stack.push_back(tpn);
		    if (verblevel >= 3) {
			std::cout << "c Schedule line #" << line << ".  Xor constraint with " << numbers.size()
				  << " variables to get Term #" << tpn->get_term_id() <<  ".  Stack size = " << term_stack.size() << std::endl;
		    }
		}
		line ++;
		break;
	    case 'g':
		c = get_numbers(schedfile, numbers);
		if (c != '\n' && c != EOF) {
		    fprintf(stdout, "c Schedule line #%d.  Gauss command. Non-numeric argument '%c'\n", line, c);
		    exit(1);
		}
		if (numbers.size() < 1) {
		    fprintf(stdout, "c Schedule line #%d.  Should specify number of equations to sum\n", line);
		    exit(1);
		} else {
		    int ecount = numbers[0];
		    if (ecount < 1 || ecount > term_stack.size()) {
			fprintf(stdout, 
				"Schedule line #%d.  Cannot perform Gaussian elimination on %d equations.  Stack size = %d\n",
				line, ecount, (int) term_stack.size());
			exit(1);
		    }
		    std::unordered_set<int> ivars;
		    for (int i = 1; i < numbers.size(); i++)
			ivars.insert(numbers[i]);
		    xor_set xset;
		    for (i = 0; i < ecount; i++) {
			int si = term_stack.size() - i - 1;
			Term *tp = term_stack[si];
			if (tp->get_equation() == NULL) {
			    fprintf(stdout, "c Schedule line #%d.  Term %d does not have an associated equation\n", line, tp->get_term_id());
			    exit(1);
			}
			xset.add(*tp->get_equation());
			dead_count += tp->deactivate();
		    }
		    xor_set eset, iset;
		    ilist pivot_sequence = xset.gauss_jordan(ivars, eset, iset);
		    if (eset.is_infeasible()) {
			if (verblevel >= 2) {
			    std::cout << "c Schedule line #" << line << ".  Generated infeasible constraint" << std::endl;
			}
			tbdd result = eset.xlist[0]->get_validation();
			ilist_free(pivot_sequence);
			return result;
		    } else {
			for (i = 0; i < ecount; i++) {
			    Term *tp = term_stack.back();
			    term_stack.pop_back();
			    dead_count += tp->deactivate();
			}
			// Equations over internal variables have already been eliminated
			// but they should be added to solver infrastructure
			for (int pid = 0; pid < iset.xlist.size(); pid++) {
			    xor_constraint *xc = iset.xlist[pid];
			    int pvar = pivot_sequence[pid];
			    int vbuf[ILIST_OVHD+1];
			    ilist vlist = ilist_make(vbuf, 1);
			    ilist_fill1(vlist, pvar);
			    solver->add_step(vlist, xc->get_validation().get_root());
			    eliminated_variables.insert(pvar);
			}
			int first_term = -1;
			int last_term = -1;
			// Set up equations over external variables for bucket elimination
			for (xor_constraint *xc : eset.xlist) {
			    Term *tpn = new Term(xc->get_validation());
			    last_term = tpn->get_term_id();
			    if (first_term < 0)
				first_term = last_term;
			    term_stack.push_back(tpn);
			}
			check_gc();
			if (verblevel >= 3) {
			    std::cout << "c Schedule line #" << line << ".  G-J elim on " << ecount << 
				" equations gives Terms #" << first_term << "--#" << last_term << ".  Stack size = " << term_stack.size() << std::endl;
			}
		    }
		}
		line++;
		break;
	    default:
		fprintf(stdout, "c Schedule line #%d.  Unknown command '%c'\n", line, c);
		break;
	    }
	}
	if (term_stack.size() != 1) {
	    if (verblevel >= 2)
		std::cout << "c After executing schedule, have " << term_stack.size() << " terms.  Switching to bucket elimination" << std::endl;
	    // Hack things up to treat remaining terms as entire set
	    reset();
	    for (Term *tp : term_stack) {
		add(new Term(tp->get_fun()));
	    }
	    return bucket_reduce();

	}
	Term *tp = term_stack.back();
	return tp->get_fun();
    }

    void show_statistics() {
	bddStat s;
	bdd_stats(s);
	std::cout << and_count << " conjunctions, " << quant_count << " quantifications." << std::endl;
	std::cout << equation_count << " equations" << std::endl;
	bdd_printstat();
	std::cout << "c Total BDD nodes: " << s.produced <<std::endl;
	std::cout << "c Max BDD size: " << max_bdd << std::endl;
#if 0
	std::cout << "c Total clauses: " << s.clausenum << std::endl;
	std::cout << "c Max live clauses: " << s.maxclausenum << std::endl;
	std::cout << "c Total variables: " << s.variablenum << std::endl;
#endif
    }

};

bool solve(FILE *cnf_file, FILE *proof_file, FILE *order_file, FILE *sched_file, bool bucket, int verblevel, proof_type_t ptype, bool binary, int max_solutions) {
    CNF cset = CNF(cnf_file);
    fclose(cnf_file);
    if (cset.failed()) {
	if (verblevel >= 1)
	    std::cout << "c Aborted" << std::endl;
	return false;
    }
    if (verblevel >= 1)
	if (verblevel >= 1)
	    std::cout << "c Read " << cset.clause_count() << " clauses.  " 
		      << cset.max_variable() << " variables" << std::endl;
    PhaseGenerator pg(GENERATE_RANDOM, DEFAULT_SEED);
    Solver solver(&pg);
    ilist variable_ordering = NULL;
    if (order_file != NULL) {
	variable_ordering = ilist_read_file(order_file);
	if (variable_ordering == NULL) {
	    std::cerr << "c ERROR: Invalid number encountered in ordering file" << std::endl;
	    return false;
	}
    }
    TermSet tset(cset, proof_file, variable_ordering, verblevel, ptype, binary, &solver);
    tbdd tr = tbdd_tautology();
    if (sched_file != NULL)
	tr = tset.schedule_reduce(sched_file);
    else if (bucket)
	tr = tset.bucket_reduce();
    else {
	tr = tset.tree_reduce();
	bdd r = tr.get_root();
	std::cout << "c Final BDD size = " << bdd_nodecount(r) << std::endl;
	if (r != bdd_false()) {
	    // Enable solution generation
	    ilist vlist = ilist_new(1);
	    for (int v = 1; v <= cset.max_variable(); v++)
		vlist = ilist_push(vlist, v);
	    solver.add_step(vlist, r);
	    tr = tbdd_tautology();
	    ilist_free(vlist);
	}
    }
    bdd r = tr.get_root();
    if (r == bdd_false())
	std::cout << "s UNSATISFIABLE" << std::endl;
    else {
	std::cout << "s SATISFIABLE" << std::endl;
	// Generate solutions
	solver.set_constraint(r);
	for (int i = 0; i < max_solutions; i++) {
	    bdd s = solver.next_solution();
	    if (s == bdd_false())
		break;
	    ilist slist = bdd_decode_cube(s);
	    printf("v "); ilist_print(slist, stdout, " "); printf(" 0\n");
	    ilist_free(slist);
	    // Now exclude this solution from future enumerations.
	    if (i < max_solutions-1)
		solver.impose_constraint(bdd_not(s));
	}
    }
    tbdd_done();
    return true;
}

