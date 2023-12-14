(* ========================================================================== *)
(* FILE          : CCSScript.sml                                              *)
(* DESCRIPTION   : A formalization of the process algebra CCS in HOL          *)
(*                                                                            *)
(* COPYRIGHTS    : 1991-1995 University of Cambridge (Monica Nesi)            *)
(*                 2016-2017 University of Bologna, Italy (Chun Tian)         *)
(*                 2018-2019 Fondazione Bruno Kessler, Italy (Chun Tian)      *)
(*                 2023-2024 The Australian National University (Chun Tian)   *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib relationTheory optionTheory listTheory CCSLib
     rich_listTheory;

open generic_termsTheory binderLib nomsetTheory nomdatatype;

open LabelTheory;

val _ = new_theory "CCS1";

val set_ss = std_ss ++ PRED_SET_ss;

(* The old way (no alpha conversion)

   NOTE: it defined “:('a, 'b) CCS” where 'a is the set of recursion variables,
         and 'b is the type of label/actions.

Datatype: CCS = nil
              | var 'a
              | prefix ('b Action) CCS
              | sum CCS CCS
              | par CCS CCS
              | restr ('b Label set) CCS
              | relab CCS ('b Relabeling)
              | rec 'a CCS
End
 *)

(* The new way based on "examples/lambda/basics/generic_termsTheory

   NOTE: it defines “:'a CCS” where 'a is 'b of the old “:('a,'b) CCS”.
 *)
val tyname = "CCS";

(* ‘GVAR s vv’ corresponds to ‘var 'a’ *)
val vp = “(\n u:unit. n = 0)”;                                  (* 0. var *)

val rep_t = “:unit + 'a Action + unit + unit + 'a Label set + 'a Relabeling + unit”;
val d_tm = mk_var("d", rep_t);

(* ‘GLAM v bv ts us’ corresponds to everything else. *)
val lp =
  “(\n ^d_tm tns uns.
     n = 0 /\ ISL d /\ tns = [] ∧ uns = []  \/                  (* 1. nil *)
     n = 0 /\ ISR d /\ ISL (OUTR d) /\ tns = [] /\ uns = [0] \/ (* 2. prefix *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISL (OUTR (OUTR d)) /\
              tns = [] /\ uns = [0;0] \/                        (* 3. sum *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISR (OUTR (OUTR d)) /\
              ISL (OUTR (OUTR (OUTR d))) /\
              tns = [] /\ uns = [0;0] \/                        (* 4. par *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISR (OUTR (OUTR d)) /\
              ISR (OUTR (OUTR (OUTR d))) /\
              ISL (OUTR (OUTR (OUTR (OUTR d)))) /\
              tns = [] ∧ uns = [0] \/                           (* 5. restr *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISR (OUTR (OUTR d)) /\
              ISR (OUTR (OUTR (OUTR d))) /\
              ISR (OUTR (OUTR (OUTR (OUTR d)))) /\
              ISL (OUTR (OUTR (OUTR (OUTR (OUTR d))))) /\
              tns = [] /\ uns = [0] \/                          (* 6. relab *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISR (OUTR (OUTR d)) /\
              ISR (OUTR (OUTR (OUTR d))) /\
              ISR (OUTR (OUTR (OUTR (OUTR d)))) /\
              ISR (OUTR (OUTR (OUTR (OUTR (OUTR d))))) /\
              tns = [0] ∧ uns = [])”;                           (* 7. rec *)

val {term_ABS_pseudo11, term_REP_11, genind_term_REP, genind_exists,
     termP, absrep_id, repabs_pseudo_id, term_REP_t, term_ABS_t, newty, ...} =
    new_type_step1 tyname 0 {vp = vp, lp = lp};

(* ----------------------------------------------------------------------
    CCS operators
   ---------------------------------------------------------------------- *)

val [gvar,glam] = genind_rules |> SPEC_ALL |> CONJUNCTS;

(* var *)
val var_t = mk_var("var", “:string -> ^newty”)
val var_def = new_definition(
   "var_def", “^var_t s = ^term_ABS_t (GVAR s ())”);
val var_termP = prove(
  mk_comb(termP, var_def |> SPEC_ALL |> concl |> rhs |> rand),
  srw_tac [][genind_rules]);
val var_t = defined_const var_def;

(* nil *)
val nil_t = mk_var("nil", “:^newty”);
val nil_def = new_definition(
   "nil_def", “^nil_t = ^term_ABS_t (GLAM ARB (INL ()) [] [])”);
val nil_termP = prove(“^termP (GLAM x (INL ()) [] [])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val nil_t = defined_const nil_def;
val nil_def' = prove(“^term_ABS_t (GLAM v (INL ()) [] []) = ^nil_t”,
    srw_tac [][nil_def, GLAM_NIL_EQ, term_ABS_pseudo11, nil_termP]);

val _ = TeX_notation { hol = "nil", TeX = ("\\ensuremath{\\mathbf{0}}", 1) };

(* prefix *)
val prefix_t = mk_var("prefix", “:'a Action -> ^newty -> ^newty”);
val prefix_def = new_definition(
   "prefix_def",
  “^prefix_t u E = ^term_ABS_t (GLAM ARB (INR (INL u)) [] [^term_REP_t E])”);
val prefix_termP = prove(
  “^termP (GLAM x (INR (INL u)) [] [^term_REP_t E])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val prefix_t = defined_const prefix_def;
val prefix_def' = prove(
  “^term_ABS_t (GLAM v (INR (INL u)) [] [^term_REP_t E]) = ^prefix_t u E”,
    srw_tac [][prefix_def, GLAM_NIL_EQ, term_ABS_pseudo11, prefix_termP]);

(* sum *)
val sum_t = mk_var("sum", “:^newty -> ^newty -> ^newty”);
val sum_def = new_definition(
   "sum_def",
  “^sum_t E1 E2 = ^term_ABS_t (GLAM ARB (INR (INR (INL ()))) []
                                        [^term_REP_t E1; ^term_REP_t E2])”);
val sum_termP = prove(
  “^termP (GLAM x (INR (INR (INL ()))) [] [^term_REP_t E1; ^term_REP_t E2])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val sum_t = defined_const sum_def;
val sum_def' = prove(
  “^term_ABS_t (GLAM v (INR (INR (INL ()))) []
                       [^term_REP_t E1; ^term_REP_t E2]) = ^sum_t E1 E2”,
    srw_tac [][sum_def, GLAM_NIL_EQ, term_ABS_pseudo11, sum_termP]);

val _ = overload_on ("+", ``sum``); (* priority: 500 *)
val _ = TeX_notation { hol = "+", TeX = ("\\ensuremath{+}", 1) };

(* par *)
val par_t = mk_var("par", “:^newty -> ^newty -> ^newty”);
val par_def = new_definition(
   "par_def",
  “^par_t E1 E2 = ^term_ABS_t (GLAM ARB (INR (INR (INR (INL ())))) []
                                        [^term_REP_t E1; ^term_REP_t E2])”);
val par_termP = prove(
  “^termP (GLAM x (INR (INR (INR (INL ())))) []
                  [^term_REP_t E1; ^term_REP_t E2])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val par_t = defined_const par_def;
val par_def' = prove(
  “^term_ABS_t (GLAM v (INR (INR (INR (INL ())))) []
                       [^term_REP_t E1; ^term_REP_t E2]) = ^par_t E1 E2”,
    srw_tac [][par_def, GLAM_NIL_EQ, term_ABS_pseudo11, par_termP]);

val _ = set_mapped_fixity {fixity = Infixl 600,
                           tok = "||", term_name = "par"};

(* val _ = Unicode.unicode_version {u = UTF8.chr 0x007C, tmnm = "par"}; *)
val _ = TeX_notation { hol = "||", TeX = ("\\ensuremath{\\mid}", 1) };

(* restr *)
val restr_t = mk_var("restr", “:'a Label set -> ^newty -> ^newty”);
val restr_def = new_definition(
   "restr_def",
  “^restr_t L E = ^term_ABS_t (GLAM ARB (INR (INR (INR (INR (INL L))))) []
                                        [^term_REP_t E])”);
val restr_termP = prove(
  “^termP (GLAM x (INR (INR (INR (INR (INL L))))) [] [^term_REP_t E])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val restr_t = defined_const restr_def;
val restr_def' = prove(
  “^term_ABS_t (GLAM v (INR (INR (INR (INR (INL L))))) [] [^term_REP_t E]) =
   ^restr_t L E”,
    srw_tac [][restr_def, GLAM_NIL_EQ, term_ABS_pseudo11, restr_termP]);

(* compact representation for single-action restriction *)
val _ = overload_on("nu", “λ(n :'a) P. restr {name n} P”);

val _ = add_rule {term_name = "nu", fixity = Closefix,
                  pp_elements = [TOK ("(" ^ UnicodeChars.nu), TM, TOK ")"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

(* relab *)
val relab_t = mk_var("relab", “:^newty -> 'a Relabeling -> ^newty”);
val relab_def = new_definition(
   "relab_def",
  “^relab_t E rf =
   ^term_ABS_t (GLAM ARB (INR (INR (INR (INR (INR (INL rf)))))) []
                         [^term_REP_t E])”);
val relab_termP = prove(
  “^termP (GLAM x (INR (INR (INR (INR (INR (INL rf)))))) [] [^term_REP_t E])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val relab_t = defined_const relab_def;
val relab_def' = prove(
  “^term_ABS_t (GLAM v (INR (INR (INR (INR (INR (INL rf)))))) []
                       [^term_REP_t E]) =
   ^relab_t E rf”,
    srw_tac [][relab_def, GLAM_NIL_EQ, term_ABS_pseudo11, relab_termP]);

(* rec *)
val rec_t = mk_var("rec", “:string -> ^newty -> ^newty”);
val rec_def = new_definition(
   "rec_def",
  “^rec_t X E =
   ^term_ABS_t (GLAM X (INR (INR (INR (INR (INR (INR ()))))))
                       [^term_REP_t E] [])”);
val rec_termP = prove(
  “^termP (GLAM X (INR (INR (INR (INR (INR (INR ())))))) [^term_REP_t E] [])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val rec_t = defined_const rec_def;

val _ =
    add_rule { term_name = "prefix", fixity = Infixr 700,
        pp_elements = [ BreakSpace(0,0), TOK "..", BreakSpace(0,0) ],
        paren_style = OnlyIfNecessary,
        block_style = (AroundSamePrec, (PP.CONSISTENT, 0)) };

val _ = TeX_notation { hol = "..", TeX = ("\\ensuremath{\\ldotp}", 1) };

(* ----------------------------------------------------------------------
    tpm (permutation of CCS recursion variables)
   ---------------------------------------------------------------------- *)

val cons_info =
    [{con_termP = var_termP,    con_def = var_def},
     {con_termP = nil_termP,    con_def = SYM nil_def'},
     {con_termP = prefix_termP, con_def = SYM prefix_def'},
     {con_termP = sum_termP,    con_def = SYM sum_def'},
     {con_termP = par_termP,    con_def = SYM par_def'},
     {con_termP = restr_termP,  con_def = SYM restr_def'},
     {con_termP = relab_termP,  con_def = SYM relab_def'},
     {con_termP = rec_termP,    con_def = rec_def}];

val tpm_name_pfx = "t";
val {tpm_thm, term_REP_tpm, t_pmact_t, tpm_t} =
    define_permutation {name_pfx = tpm_name_pfx, name = tyname,
                        term_REP_t = term_REP_t,
                        term_ABS_t = term_ABS_t,
                        absrep_id = absrep_id,
                        repabs_pseudo_id = repabs_pseudo_id,
                        cons_info = cons_info, newty = newty,
                        genind_term_REP = genind_term_REP};

Theorem tpm_eqr:
    t = tpm pi u <=> tpm (REVERSE pi) t = u
Proof
    METIS_TAC [pmact_inverse]
QED

Theorem tpm_eql:
    tpm pi t = u <=> t = tpm (REVERSE pi) u
Proof
    simp[tpm_eqr]
QED

Theorem tpm_CONS :
    tpm ((x,y)::pi) t = tpm [(x,y)] (tpm pi t)
Proof
  SRW_TAC [][GSYM pmact_decompose]
QED

(* ----------------------------------------------------------------------
    support and FV
   ---------------------------------------------------------------------- *)

val term_REP_eqv = prove(
   “support (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t {}”,
    srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_tpm, pmact_sing_inv]);

val supp_term_REP = prove(
   “supp (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t = {}”,
    REWRITE_TAC [GSYM SUBSET_EMPTY]
 >> MATCH_MP_TAC (GEN_ALL supp_smallest)
 >> srw_tac [][term_REP_eqv]);

val tpm_def' =
    term_REP_tpm |> AP_TERM term_ABS_t |> PURE_REWRITE_RULE [absrep_id];

val t = mk_var("t", newty);
val supptpm_support = prove(
   “support ^t_pmact_t ^t (supp gt_pmact (^term_REP_t ^t))”,
    srw_tac [][support_def, tpm_def', supp_fresh, absrep_id]);

val supptpm_apart = prove(
   “x IN supp gt_pmact (^term_REP_t ^t) /\ y NOTIN supp gt_pmact (^term_REP_t ^t)
    ==> ^tpm_t [(x,y)] ^t <> ^t”,
    srw_tac [][tpm_def']
 >> DISCH_THEN (MP_TAC o AP_TERM term_REP_t)
 >> srw_tac [][repabs_pseudo_id, genind_gtpm_eqn, genind_term_REP, supp_apart]);

val supp_tpm = prove(
   “supp ^t_pmact_t ^t = supp gt_pmact (^term_REP_t ^t)”,
    match_mp_tac (GEN_ALL supp_unique_apart)
 >> srw_tac [][supptpm_support, supptpm_apart, FINITE_GFV]);

val _ = overload_on ("FV", “supp ^t_pmact_t”);

val _ = set_fixity "#" (Infix(NONASSOC, 450));
val _ = overload_on ("#", “\X (E :'a CCS). X NOTIN FV E”);

Theorem FINITE_FV[simp] :
    FINITE (FV t)
Proof
    srw_tac [][supp_tpm, FINITE_GFV]
QED

Theorem FV_EMPTY :
    FV t = {} <=> !v. v NOTIN FV t
Proof
    SIMP_TAC (srw_ss()) [EXTENSION]
QED

fun supp_clause {con_termP, con_def} = let
  val t = mk_comb(“supp ^t_pmact_t”, lhand (concl (SPEC_ALL con_def)))
in
  t |> REWRITE_CONV [supp_tpm, con_def, MATCH_MP repabs_pseudo_id con_termP,
                     GFV_thm]
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_tpm]
    |> GEN_ALL
end

Theorem FV_thm[simp] = LIST_CONJ (map supp_clause cons_info)

val [FV_var, FV_nil, FV_prefix, FV_sum, FV_par,
     FV_restr, FV_relab, FV_rec] =
    map save_thm
        (combine (["FV_var", "FV_nil", "FV_prefix", "FV_sum", "FV_par",
                   "FV_restr", "FV_relab", "FV_rec"], CONJUNCTS FV_thm));

(* |- !x t p. x IN FV (tpm p t) <=> lswapstr (REVERSE p) x IN FV t *)
Theorem FV_tpm[simp] = “x IN FV (tpm p t)”
                       |> REWRITE_CONV [perm_supp, pmact_IN]
                       |> GEN_ALL

(* ----------------------------------------------------------------------
    term induction
   ---------------------------------------------------------------------- *)

fun genit th = let
  val (_, args) = strip_comb (concl th)
  val (tm, x) = case args of [x,y] => (x,y) | _ => raise Fail "Bind"
  val ty = type_of tm
  val t = mk_var("t", ty)
in
  th |> INST [tm |-> t] |> GEN x |> GEN t
end

val LIST_REL_CONS1 = listTheory.LIST_REL_CONS1;
val LIST_REL_NIL = listTheory.LIST_REL_NIL;

val term_ind =
    bvc_genind
        |> INST_TYPE [alpha |-> rep_t, beta |-> “:unit”]
        |> Q.INST [‘vp’ |-> ‘^vp’, ‘lp’ |-> ‘^lp’]
        |> SIMP_RULE std_ss [LIST_REL_CONS1, RIGHT_AND_OVER_OR,
                             LEFT_AND_OVER_OR, DISJ_IMP_THM, LIST_REL_NIL]
        |> Q.SPECL [‘\n t0 x. Q t0 x’, ‘fv’]
        |> UNDISCH |> Q.SPEC ‘0’ |> DISCH_ALL
        |> SIMP_RULE (std_ss ++ DNF_ss)
                     [sumTheory.FORALL_SUM, supp_listpm,
                      IN_UNION, NOT_IN_EMPTY, oneTheory.FORALL_ONE,
                      genind_exists, LIST_REL_CONS1, LIST_REL_NIL]
        |> Q.INST [‘Q’ |-> ‘\t. P (^term_ABS_t t)’]
        |> SIMP_RULE std_ss [GSYM var_def, GSYM nil_def, nil_def', prefix_def',
                             sum_def', par_def', restr_def', relab_def',
                             GSYM rec_def, absrep_id]
        |> SIMP_RULE (srw_ss()) [GSYM supp_tpm]
        |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                  [ASSUME “!x:'c. FINITE (fv x:string set)”]
        |> SPEC_ALL |> UNDISCH
        |> genit |> DISCH_ALL |> Q.GENL [‘P’, ‘fv’];

fun mkX_ind th = th |> Q.SPECL [‘\t x. Q t’, ‘\x. X’]
                    |> SIMP_RULE std_ss [] |> Q.GEN ‘X’
                    |> Q.INST [‘Q’ |-> ‘P’] |> Q.GEN ‘P’;

Theorem CCS_induction = mkX_ind term_ind

Theorem simple_induction =
    CCS_induction |> Q.SPECL [‘P’, ‘{}’]
                  |> REWRITE_RULE [FINITE_EMPTY, NOT_IN_EMPTY]
                  |> Q.GEN ‘P’

Theorem rec_eq_thm =
  “(rec u t1 = rec v t2)”
     |> SIMP_CONV (srw_ss()) [rec_def, rec_termP, term_ABS_pseudo11,
                              GLAM_eq_thm, term_REP_11, GSYM term_REP_tpm,
                              GSYM supp_tpm]
     |> Q.GENL [‘u’, ‘v’, ‘t1’, ‘t2’]

Theorem tpm_ALPHA :
    v # u ==> (rec x u = rec v (tpm [(v,x)] u))
Proof
    SRW_TAC [boolSimps.CONJ_ss][rec_eq_thm, pmact_flip_args]
QED

(* ----------------------------------------------------------------------
    term recursion
   ---------------------------------------------------------------------- *)

val (_, repty) = dom_rng (type_of term_REP_t);
val repty' = ty_antiq repty;

val LENGTH_NIL' =
    CONV_RULE (BINDER_CONV (LAND_CONV (REWR_CONV EQ_SYM_EQ)))
              listTheory.LENGTH_NIL;

val LENGTH1 = prove(
   “(1 = LENGTH l) <=> ?e. l = [e]”,
    Cases_on ‘l’ >> srw_tac [][listTheory.LENGTH_NIL]);

val LENGTH2 = prove(
   “(2 = LENGTH l) <=> ?a b. l = [a;b]”,
    Cases_on ‘l’ >> srw_tac [][LENGTH1]);

val termP_elim = prove(
   “(!g. ^termP g ==> P g) <=> (!t. P (^term_REP_t t))”,
    srw_tac [][EQ_IMP_THM] >- srw_tac [][genind_term_REP]
 >> first_x_assum (qspec_then ‘^term_ABS_t g’ mp_tac)
 >> srw_tac [][repabs_pseudo_id]);

val termP_removal =
    nomdatatype.termP_removal {
      elimth = termP_elim, absrep_id = absrep_id,
      tpm_def = AP_TERM term_ABS_t term_REP_tpm |> REWRITE_RULE [absrep_id],
      termP = termP, repty = repty};

val termP0 = prove(
   “genind ^vp ^lp n t <=> ^termP t ∧ (n = 0)”,
    EQ_TAC >> simp_tac (srw_ss()) [] >> strip_tac
 >> qsuff_tac ‘n = 0’ >- (strip_tac >> srw_tac [][])
 >> pop_assum mp_tac
 >> Q.ISPEC_THEN ‘t’ STRUCT_CASES_TAC gterm_cases
 >> srw_tac [][genind_GVAR, genind_GLAM_eqn]);

val u_tm = mk_var("u", rep_t);

(* “tvf :string -> 'q -> 'r” *)
val tvf = “λ(s:string) (u:unit) (p:ρ). tvf s p : 'r”; (* var *)

(* nil:    “tnf :'q -> 'r”
   prefix: “tff :('q -> 'r) -> 'a Action -> 'a CCS -> 'q -> 'r”
   sum:    “tsf :('q -> 'r) -> ('q -> 'r) -> 'a CCS -> 'a CCS -> 'q -> 'r”
   par:    “tpf :('q -> 'r) -> ('q -> 'r) -> 'a CCS -> 'a CCS -> 'q -> 'r”
   restr:  “trf :('q -> 'r) -> ('a Label -> bool) -> 'a CCS -> 'q -> 'r”
   relab:  “tlf :('q -> 'r) -> 'a CCS -> 'a Relabeling -> 'q -> 'r”
   rec:    “tcf :('q -> 'r) -> string -> 'a CCS -> 'q -> 'r”  
 *)
val tlf =
   “λ(v:string) ^u_tm (ds1:('q -> 'r) list) (ds2:('q -> 'r) list)
                      (ts1:^repty' list) (ts2:^repty' list) (p :'q).
       if ISL u then
         tnf p :'r
       else if ISL (OUTR u) then
         tff (HD ds2) (OUTL (OUTR u)) (^term_ABS_t (HD ts2)) p :'r
       else if ISL (OUTR (OUTR u)) then
         tsf (HD ds2) (HD (TL ds2))
             (^term_ABS_t (HD ts2)) (^term_ABS_t (HD (TL ts2))) p :'r
       else if ISL (OUTR (OUTR (OUTR u))) then
         tpf (HD ds2) (HD (TL ds2))
             (^term_ABS_t (HD ts2)) (^term_ABS_t (HD (TL ts2))) p :'r
       else if ISL (OUTR (OUTR (OUTR (OUTR u)))) then
         trf (HD ds2) (OUTL (OUTR (OUTR (OUTR (OUTR u)))))
             (^term_ABS_t (HD ts2)) p :'r
       else if ISL (OUTR (OUTR (OUTR (OUTR (OUTR u))))) then
         tlf (HD ds2) (^term_ABS_t (HD ts2))
             (OUTL (OUTR (OUTR (OUTR (OUTR (OUTR u)))))) p :'r
       else
         tcf (HD ds1) v (^term_ABS_t (HD ts1)) p :'r”;

Theorem parameter_tm_recursion =
  parameter_gtm_recursion
      |> INST_TYPE [alpha |-> rep_t, beta |-> “:unit”, gamma |-> “:'r”]
      |> Q.INST [‘lf’ |-> ‘^tlf’, ‘vf’ |-> ‘^tvf’, ‘vp’ |-> ‘^vp’,
                 ‘lp’ |-> ‘^lp’, ‘n’ |-> ‘0’]
      |> SIMP_RULE (srw_ss()) [sumTheory.FORALL_SUM, FORALL_AND_THM,
                               GSYM RIGHT_FORALL_IMP_THM, IMP_CONJ_THM,
                               GSYM RIGHT_EXISTS_AND_THM,
                               GSYM LEFT_EXISTS_AND_THM,
                               GSYM LEFT_FORALL_IMP_THM,
                               LIST_REL_CONS1, genind_GVAR,
                               genind_GLAM_eqn, sidecond_def,
                               NEWFCB_def, relsupp_def,
                               LENGTH_NIL', LENGTH1, LENGTH2]
      |> ONCE_REWRITE_RULE [termP0]
      |> SIMP_RULE (srw_ss() ++ DNF_ss) [LENGTH1, LENGTH2,
                                         listTheory.LENGTH_NIL]
      |> CONV_RULE (DEPTH_CONV termP_removal)
      |> SIMP_RULE (srw_ss()) [GSYM supp_tpm, SYM term_REP_tpm]
      |> UNDISCH
      |> rpt_hyp_dest_conj
      |> lift_exfunction {repabs_pseudo_id = repabs_pseudo_id,
                          term_REP_t = term_REP_t,
                          cons_info = cons_info}
      |> DISCH_ALL
      |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                [ASSUME ``FINITE (A:string set)``,
                                 ASSUME ``!p:ρ. FINITE (supp ppm p)``]
      |> UNDISCH_ALL |> DISCH_ALL
      |> REWRITE_RULE [AND_IMP_INTRO]
      |> CONV_RULE (LAND_CONV (REWRITE_CONV [GSYM CONJ_ASSOC]))
      |> Q.INST [‘tvf’ |-> ‘vr’, (* var *)
                 ‘tnf’ |-> ‘nl’, (* nil *)
                 ‘tff’ |-> ‘pf’, (* prefix *)
                 ‘tsf’ |-> ‘sm’, (* sum *)
                 ‘tpf’ |-> ‘pr’, (* par *)
                 ‘trf’ |-> ‘rs’, (* restr *)
                 ‘tlf’ |-> ‘rl’, (* relab *)
                 ‘tcf’ |-> ‘re’, (* rec *)
                 ‘dpm’ |-> ‘apm’]
      |> CONV_RULE (REDEPTH_CONV sort_uvars)

val FORALL_ONE = oneTheory.FORALL_ONE;
val FORALL_ONE_FN = oneTheory.FORALL_ONE_FN;
val EXISTS_ONE_FN = oneTheory.EXISTS_ONE_FN;

Theorem tm_recursion = 
  parameter_tm_recursion
      |> Q.INST_TYPE [‘:'q’ |-> ‘:unit’]
      |> Q.INST [‘ppm’ |-> ‘discrete_pmact’,
                  ‘vr’ |-> ‘\s u. vru s’,
                  ‘nl’ |-> ‘\u. nlu’,
                  ‘pf’ |-> ‘\r a t u. pfu (r()) a t’,
                  ‘sm’ |-> ‘\r1 r2 t1 t2 u. smu (r1()) (r2()) t1 t2’,
                  ‘pr’ |-> ‘\r1 r2 t1 t2 u. pru (r1()) (r2()) t1 t2’,
                  ‘rs’ |-> ‘\r L t u. rsu (r()) L t’,
                  ‘rl’ |-> ‘\r t rf u. rlu (r()) t rf’,
                  ‘re’ |-> ‘\r v t u. reu (r()) v t’]
      |> SIMP_RULE (srw_ss()) [FORALL_ONE, FORALL_ONE_FN, EXISTS_ONE_FN,
                               fnpm_def]
      |> SIMP_RULE (srw_ss() ++ CONJ_ss) [supp_unitfn]
      |> Q.INST [‘vru’ |-> ‘vr’,
                 ‘nlu’ |-> ‘nl’,
                 ‘pfu’ |-> ‘pf’,
                 ‘smu’ |-> ‘sm’,
                 ‘pru’ |-> ‘pr’,
                 ‘rsu’ |-> ‘rs’,
                 ‘rlu’ |-> ‘rl’,
                 ‘reu’ |-> ‘re’]

(* ----------------------------------------------------------------------
    cases theorem
   ---------------------------------------------------------------------- *)

Theorem CCS_cases :
    !t. t = nil \/ (?a. t = var a) \/ (?u E. t = prefix u E) \/
        (?E1 E2. t = sum E1 E2) \/ (?E1 E2. t = par E1 E2) \/
        (?L E. t = restr L E) \/ (?E rf. t = relab E rf) \/
         ?X E. t = rec X E
Proof
    HO_MATCH_MP_TAC simple_induction
 >> SRW_TAC [][] (* 161 subgoals here *)
 >> METIS_TAC []
QED

Theorem CCS_distinct[simp] :
    (!X.     nil <> var X :'a CCS) /\
    (!u E.   nil <> prefix u E :'a CCS) /\
    (!E1 E2. nil <> E1 + E2 :'a CCS) /\
    (!E1 E2. nil <> E1 || E2 :'a CCS) /\
    (!L E.   nil <> restr L E :'a CCS) /\
    (!E rf.  nil <> relab E rf :'a CCS) /\
    (!X E.   nil <> rec X E :'a CCS) /\
    (!X u E.   var X <> prefix u E :'a CCS) /\
    (!X E1 E2. var X <> E1 + E2 :'a CCS) /\
    (!X E1 E2. var X <> E1 || E2 :'a CCS) /\
    (!X L E.   var X <> restr L E :'a CCS) /\
    (!X E rf.  var X <> relab E rf :'a CCS) /\
    (!X Y E.   var X <> rec Y E :'a CCS) /\
    (!u E E1 E2. prefix u E <> E1 + E2 :'a CCS) /\
    (!u E E1 E2. prefix u E <> E1 || E2 :'a CCS) /\
    (!u E L E'.  prefix u E <> restr L E' :'a CCS) /\
    (!u E E' rf. prefix u E <> relab E' rf :'a CCS) /\
    (!u E X E'.  prefix u E <> rec X E' :'a CCS) /\
    (!E1 E2 E3 E4. E1 + E2 <> E3 || E4 :'a CCS) /\
    (!E1 E2 L E.   E1 + E2 <> restr L E :'a CCS) /\
    (!E1 E2 E rf.  E1 + E2 <> relab E rf :'a CCS) /\
    (!E1 E2 X E.   E1 + E2 <> rec X E :'a CCS) /\
    (!E1 E2 L E.   E1 || E2 <> (restr L) E :'a CCS) /\
    (!E1 E2 E rf.  E1 || E2 <> relab E rf :'a CCS) /\
    (!E1 E2 X E.   E1 || E2 <> rec X E :'a CCS) /\
    (!L E E' rf. restr L E <> relab E' rf :'a CCS) /\
    (!L E X E'.  restr L E <> rec X E' :'a CCS) /\
     !E rf X E'. relab E rf <> rec X E' :'a CCS
Proof
    srw_tac [] [nil_def, nil_termP, var_def, var_termP,
                prefix_def, prefix_termP, sum_def, sum_termP,
                par_def, par_termP, restr_def, restr_termP,
                relab_def, relab_termP, rec_def, rec_termP,
                term_ABS_pseudo11, gterm_distinct, GLAM_eq_thm]
QED

local
    val thm = CONJUNCTS CCS_distinct;
    val CCS_distinct_LIST = thm @ (map GSYM thm);
in
    val CCS_distinct' = save_thm
      ("CCS_distinct'", LIST_CONJ CCS_distinct_LIST);
end

Theorem CCS_distinct_exists :
    !p :'a CCS. ?q. q <> p
Proof
    Q.X_GEN_TAC ‘p’
 >> MP_TAC (Q.SPEC ‘p’ CCS_cases) >> rw []
 >- (Q.EXISTS_TAC ‘prefix a nil’ >> rw [CCS_distinct'])
 >> Q.EXISTS_TAC ‘nil’
 >> rw [CCS_distinct]
QED

(* cf. rec_eq_thm for “rec X E = rec X' E'” *)
Theorem CCS_11[simp] :
    (!X X'. var X = var X' :'a CCS <=> X = X') /\
    (!u E u' E' :'a CCS. prefix u E = prefix u' E' <=> u = u' /\ E = E') /\
    (!E1 E2 E1' E2' :'a CCS. E1 + E2 = E1' + E2' <=> E1 = E1' /\ E2 = E2') /\
    (!E1 E2 E1' E2' :'a CCS. E1 || E2 = E1' || E2' <=> E1 = E1' /\ E2 = E2') /\
    (!L E L' E' :'a CCS. restr L E = restr L' E' <=> L = L' /\ E = E') /\
    (!(E :'a CCS) rf E' rf'. relab E rf = relab E' rf' <=> E = E' /\ rf = rf')
Proof
    srw_tac [] [nil_def, nil_termP, var_def, var_termP,
                prefix_def, prefix_termP, sum_def, sum_termP,
                par_def, par_termP, restr_def, restr_termP,
                relab_def, relab_termP,
                term_ABS_pseudo11, gterm_11, term_REP_11]
 >> rw [Once CONJ_COMM]
QED

val _ = export_theory ();
val _ = html_theory "CCS1";
