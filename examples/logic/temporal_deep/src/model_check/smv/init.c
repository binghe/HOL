#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <unistd.h>

#include "storage.h"
#include "hash.h"
#include "node.h"
#include "init.h"
#include "bdd.h"

/* Global variables */

int KEYTABLESIZE=32749, APPLY_CACHE_SIZE=32749, MINI_CACHE_SIZE=32749;

int heuristics = 0,verbose = 0,option_print_reachable=0,
  option_forward_search = 1,option_round_robin = 0,
  option_incremental = 0,option_restrict_trans = 0, option_interactive = 0,
  option_AG_only = 0, option_conj_part = 0, option_changes_only = 1;
int option_print_node_length=40;
int option_print_width = 79;
int interactive_mode = 0;
int conj_part_limit = 0;

/* Whether to reorder when everything is done */
int option_final_reorder = 0;

double fudge_factor;
char *output_order_file = 0,*input_order_file = 0;
char *input_file = "stdin";
char *myname = "smv";
hash_ptr seq_hash;
char* addrstart;
char *option_dump_reachable = NULL;

extern node_ptr parse_tree;
#ifdef REORDER
int reorder = 0;
int reorder_bits = 10;
int reorder_size = 10000;
int reorder_minsize = 2000;
int reorder_maxsize = 300000;
float reorder_factor = 1.25;
#endif
#ifdef OTHER_SIMP
int option_othersimp = 0;
int option_gc_factor = 3;
int option_gc_limit = 32; /* max size of memory in MB. Default is 32MB. */
int option_early = 0;
int option_checktrans = 1;
int option_drip=0;
int option_output_often=0;
#endif

#ifdef SMV_SIGNALS
/* Quit after outputting the order file with -quit option (default),
   but don't quit with -noquit. */
int option_quit = 1, option_pid=1;
#endif

static node_ptr atom_stack=0;

jmp_buf longjmp_buf;
int longjmp_on_err = 0;

#ifdef SERGEYDEBUG
extern unsigned apply_cache_access_count;
extern unsigned apply_cache_hit_count;
#endif

int indent_size = 0;

/* Timers for the variable reordering */
extern clock_t reorder_variables_utime,
  reorder_variables_stime;

/* Functions */

void init_eval(){}

void signal_handler(sig)
int sig;
{
  int i;

  printf("\nSMV caught signal %d... ",sig);
  if(sig==10) /* SIGUSR1 */
    if(!reorder) {
      printf("Dynamic variable reordering ON at %d < nodes < %d\n\n",
	     reorder_size, reorder_maxsize);
      reorder = 1;
    }
    else {
      printf("Dynamic variable reordering OFF\n\n");
      reorder = 0;
    }
  else if(sig==12) { /* SIGUSR2 */
    printf("Force garbage collection\n\n");
    reset_maxnodes();
  }
  else {
    printf("\n");
    print_usage();
    exit(1);
  }
  for(i = 0 ; i < 32 ; i++)
    if((i != SIGSEGV) && (i != SIGCONT) && (i != SIGTSTP))
      signal(i, signal_handler);
}

void open_input(filename)
char *filename;
{
  extern int yylineno;
  extern FILE *yyin;
  input_file = filename;
  if(!(yyin = fopen(filename,"r")))
    rpterr("cannot open %s for input",filename);
  yylineno = 1;
}

void close_input()
{
  extern int yylineno;
  input_file = 0;
  yylineno = 0;
}

void undefined(s)
node_ptr s;
{
  start_err();
  print_node(stderr,s);
  fprintf(stderr," undefined");
  finish_err();
}

void redefining(s)
node_ptr s;
{
  start_err();
  fprintf(stderr,"redefining ");
  print_node(stderr,s);
  finish_err();
}

void circular(s)
node_ptr s;
{
  start_err();
  fprintf(stderr,"recursively defined: ");
  print_node(stderr,s);
  finish_err();
}

void toomanyvars(s)
node_ptr s;
{
  start_err();
  fprintf(stderr,"too many variables");
  finish_err();
}

void start_err()
{
  extern int yylineno;
  fprintf(stderr,"\n");
  if(input_file)fprintf(stderr,"file %s: ",input_file);
  if(yylineno)fprintf(stderr,"line %d: ",yylineno);
}

void finish_err()
{
  fprintf(stderr,"\n");
  while(atom_stack){
    node_ptr s = car(atom_stack);
    atom_stack = cdr(atom_stack);
    fprintf(stderr,"in definition of ");
    print_node(stderr,s);
    if(s->lineno)
      fprintf(stderr," at line %d",s->lineno);
    fprintf(stderr,"\n");
  }
  if(longjmp_on_err)longjmp(longjmp_buf,1);
  my_exit(1);
}

int my_setjmp()
{
  int v;
  longjmp_on_err = 1;
  v = setjmp(longjmp_buf);
  if(v)
    longjmp_on_err = 0;
  return(v);
}

void cancel_my_setjmp()
{
    longjmp_on_err = 0;
}  
  

void my_exit(n)
int n;
{
  if(verbose)fprintf(stderr,"%s: exit(%d)\n ",myname,n);
  if(verbose && n)print_usage();
  remove(".smv-pid");
  exit(n);
}

void print_usage()
{
  struct tms buffer;
  printf("\nresources used:\n");
  times(&buffer);
  printf("user time: %g s, system time: %g s\n",
	 buffer.tms_utime/(double)CLK_TCK,
	 buffer.tms_stime/(double)CLK_TCK);
  if(reorder) {
    printf("Dynamic variable reordering: user time: %g s, system time: %g s\n",
	   reorder_variables_utime/(double)CLK_TCK,
	   reorder_variables_stime/(double)CLK_TCK);
    printf("Time without reordering: user time: %g s, system time: %g s\n",
	   (buffer.tms_utime-reorder_variables_utime)/(double)CLK_TCK,
	   (buffer.tms_stime-reorder_variables_stime)/(double)CLK_TCK);
  }
  printf("BDD nodes allocated: %d\n",get_bdd_nodes_allocated());
  printf("Bytes allocated: %d\n",(unsigned)((char *)sbrk(0)-addrstart));
#ifdef SERGEYDEBUG
  printf("Apply cache: %u, hits: %u, hit rate: %2.1f %%\n",
	 apply_cache_access_count, apply_cache_hit_count,
	 (100.0*(float)apply_cache_hit_count)/(float)apply_cache_access_count);
#endif
}

/*VARARGS1*/
void rpterr(const char* format, ...)
{
  va_list argptr;
  va_start(argptr, format);
  start_err();
  vfprintf(stderr, format, argptr);
  finish_err();
  va_end(argptr);
}

/*VARARGS1*/
void catastrophe(const char* format, ...)
{
  va_list argptr;
  va_start(argptr, format);
  
  fprintf(stderr,"\n\n*** internal error *** ");
#ifdef VERSION
  fprintf(stderr,"\n%s", VERSION);
#endif
  vfprintf(stderr, format, argptr);
  fprintf(stderr,"\nPlease report this error to sergey.berezin@cs.cmu.edu\n");
  fprintf(stderr,"Send a copy of this output and your input.\n");

  va_end(argptr);
  my_exit(1);
}

void push_atom(s)
node_ptr s;
{
  atom_stack = cons(s,atom_stack);
}

void pop_atom()
{
  node_ptr temp;
  if(!atom_stack)catastrophe("pop_atom: stack empty");
  temp = cdr(atom_stack);
  free_node(atom_stack);
  atom_stack = temp;
}

void yyerror(s)
char *s;
{
    extern char yytext[];
    start_err();
    fprintf(stderr,"at token \"%s\": %s\n",&yytext,s);
    if(!interactive_mode)finish_err();
}

int yywrap()
{
  return(1);
}

void indent(stream)
FILE *stream;
{
  int i;
  for(i=0;i<indent_size;i++)fprintf(stream,"  ");
}

void indent_node(stream,s1,n,s2)
FILE *stream;
char *s1,*s2;
node_ptr n;
{
  indent(stream);
  fprintf(stream,"%s",s1);
  print_node(stream,n);
  fprintf(stream,"%s",s2);
}
