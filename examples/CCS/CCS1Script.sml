(******************************************************************************
 *
 *   Milner's Calculus of Concurrent System (CCS) in HOL4
 *
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna, Italy (Author: Chun Tian)
 * Copyright 2018-2019  Fondazione Bruno Kessler, Italy (Author: Chun Tian)
 * Copyright 2023-2024  The Australian National University (Author: Chun Tian)
 *
 ******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib relationTheory optionTheory listTheory CCSLib
     rich_listTheory;

open generic_termsTheory binderLib nomsetTheory nomdatatype;

val _ = new_theory "CCS1";

val set_ss = std_ss ++ PRED_SET_ss;

(******************************************************************************)
(*                                                                            *)
(*                           Labels and Actions                               *)
(*                                                                            *)
(******************************************************************************)

(* Define the set of labels as the union of names (`in`) (strings) and
   co-names (`out`) (complement of names) *)
Datatype: Label = name 'b | coname 'b
End

(* Define structural induction on labels
   !P. (!s. P (name s)) /\ (!s. P (coname s)) ==> !L. P L
 *)
val Label_induction = TypeBase.induction_of ``:'b Label``;

(* The structural cases theorem for the type Label
   !LL. (?s. LL = name s) \/ ?s. LL = coname s
 *)
val Label_cases = TypeBase.nchotomy_of ``:'b Label``;

(* The distinction and injectivity theorems for the type Label
   !a' a. name a <> coname a'
   (!a a'. (name a = name a') <=> (a = a')) /\
       !a a'. (coname a = coname a') <=> (a = a')
 *)
val Label_distinct = TypeBase.distinct_of ``:'b Label``;
val Label_distinct' = save_thm ("Label_distinct'", GSYM Label_distinct);

val Label_not_eq = save_thm (
   "Label_not_eq", STRIP_FORALL_RULE EQF_INTRO Label_distinct);

val Label_not_eq' = save_thm (
   "Label_not_eq'", STRIP_FORALL_RULE
                        (PURE_REWRITE_RULE [SYM_CONV ``name s = coname s'``])
                        Label_not_eq);

val Label_11 = TypeBase.one_one_of ``:'b Label``;

(* NEW: define the set of actions as the OPTION of Label *)
Type Action[pp] = ``:'b Label option``;

val _ = overload_on ("tau",   ``NONE :'b Action``);
val _ = overload_on ("label", ``SOME :'b Label -> 'b Action``);

val _ = Unicode.unicode_version { u = UnicodeChars.tau, tmnm = "tau" };
val _ = TeX_notation { hol = "tau", TeX = ("\\ensuremath{\\tau}", 1) };

(* The compact representation for (visible) input and output actions, is
   suggested by Michael Norrish *)
val _ = overload_on ("In", ``\a. label (name a)``);
val _ = overload_on ("Out", ``\a. label (coname a)``);

val _ = TeX_notation { hol = "In",  TeX = ("\\HOLTokenInputAct", 1) };
val _ = TeX_notation { hol = "Out", TeX = ("\\HOLTokenOutputAct", 1) };

(* Define structural induction on actions
   !P. P tau /\ (!L. P (label L)) ==> !A. P A
 *)
val Action_induction = save_thm (
   "Action_induction", INST_TYPE [``:'a`` |-> ``:'b Label``] option_induction);

(* The structural cases theorem for the type Action
   !AA. (AA = tau) \/ ?L. AA = label L
 *)
val Action_cases = save_thm (
   "Action_cases", INST_TYPE [``:'a`` |-> ``:'b Label``] option_nchotomy);

(* The distinction and injectivity theorems for the type Action
   !a. tau <> label a
   !a a'. (label a = label a') <=> (a = a')
 *)
val Action_distinct = save_thm (
   "Action_distinct", INST_TYPE [``:'a`` |-> ``:'b Label``] NOT_NONE_SOME);

val Action_distinct_label = save_thm (
   "Action_distinct_label", INST_TYPE [``:'a`` |-> ``:'b Label``] NOT_SOME_NONE);

val Action_11 = save_thm (
   "Action_11", INST_TYPE [``:'a`` |-> ``:'b Label``] SOME_11);

(* !A. A <> tau ==> ?L. A = label L *)
val Action_no_tau_is_Label = save_thm (
   "Action_no_tau_is_Label",
    Q.GEN `A` (DISJ_IMP (Q.SPEC `A` Action_cases)));

(* Extract the label from a visible action, LABEL: Action -> Label. *)
val _ = overload_on ("LABEL", ``THE :'b Label option -> 'b Label``);

(* |- !x. LABEL (label x) = x *)
val LABEL_def = save_thm (
   "LABEL_def", INST_TYPE [``:'a`` |-> ``:'b Label``] THE_DEF);

(* |- (!x. IS_SOME (label x) <=> T) /\ (IS_SOME 't <=> F) *)
val IS_LABEL_def = save_thm (
   "IS_LABEL_def", INST_TYPE [``:'a`` |-> ``:'b Label``] IS_SOME_DEF);

val _ = export_rewrites ["LABEL_def", "IS_LABEL_def"];

(* Define the complement of a label, COMPL: Label -> Label. *)
val COMPL_LAB_def = Define `(COMPL_LAB (name (s :'b)) = (coname s)) /\
                            (COMPL_LAB (coname s) = (name s))`;

val _ = overload_on ("COMPL", ``COMPL_LAB``);
val _ = export_rewrites ["COMPL_LAB_def"];

val coname_COMPL = store_thm
  ("coname_COMPL", ``!(s :'b). coname s = COMPL (name s)``,
    REWRITE_TAC [COMPL_LAB_def]);

val COMPL_COMPL_LAB = store_thm (
   "COMPL_COMPL_LAB", ``!(l :'b Label). COMPL_LAB (COMPL_LAB l) = l``,
    Induct >> REWRITE_TAC [COMPL_LAB_def]);

(* Extend the complement to actions, COMPL_ACT: Action -> Action. *)
val COMPL_ACT_def = Define `
   (COMPL_ACT (label (l: 'b Label)) = label (COMPL l)) /\
   (COMPL_ACT tau = tau)`;

val _ = overload_on ("COMPL", ``COMPL_ACT``);
val _ = export_rewrites ["COMPL_ACT_def"];

Theorem COMPL_COMPL_ACT :
    !(a :'b Action). COMPL_ACT (COMPL_ACT a) = a
Proof
    Induct_on `a`
 >- REWRITE_TAC [COMPL_ACT_def]
 >> REWRITE_TAC [COMPL_ACT_def, COMPL_COMPL_LAB]
QED

(* auxiliary theorem about complementary labels. *)
Theorem COMPL_THM :
    !(l :'b Label) s. (l <> name s ==> COMPL l <> coname s) /\
                      (l <> coname s ==> COMPL l <> name s)
Proof
    Induct_on `l`
 >| [ (* case 1 *)
      rpt GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_11, COMPL_LAB_def],
        REWRITE_TAC [Label_distinct, COMPL_LAB_def, Label_distinct'] ] ,
      (* case 2 *)
      rpt GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_distinct, COMPL_LAB_def, Label_distinct'],
        REWRITE_TAC [Label_11, COMPL_LAB_def] ] ]
QED

(* Relabeling function is subtype of `:'b Label -> 'b Label *)
val Is_Relabeling_def = Define `
    Is_Relabeling (f: 'b Label -> 'b Label) = (!s. f (coname s) = COMPL (f (name s)))`;

val EXISTS_Relabeling = store_thm ("EXISTS_Relabeling",
  ``?(f: 'b Label -> 'b Label). Is_Relabeling f``,
    Q.EXISTS_TAC `\a. a`
 >> PURE_ONCE_REWRITE_TAC [Is_Relabeling_def]
 >> BETA_TAC
 >> REWRITE_TAC [COMPL_LAB_def]);

(* |- ?rep. TYPE_DEFINITION Is_Relabeling rep *)
val Relabeling_TY_DEF = new_type_definition ("Relabeling", EXISTS_Relabeling);

(* |- (!a. ABS_Relabeling (REP_Relabeling a) = a) /\
       !r. Is_Relabeling r <=> (REP_Relabeling (ABS_Relabeling r) = r)
 *)
val Relabeling_ISO_DEF =
    define_new_type_bijections {ABS  = "ABS_Relabeling",
                                REP  = "REP_Relabeling",
                                name = "Relabeling_ISO_DEF",
                                tyax =  Relabeling_TY_DEF};

(* ABS_Relabeling_one_one =
   !r r'.
      Is_Relabeling r ==> Is_Relabeling r' ==>
      ((ABS_Relabeling r = ABS_Relabeling r') <=> (r = r'))

   ABS_Relabeling_onto =
   !a. ?r. (a = ABS_Relabeling r) /\ Is_Relabeling r

   REP_Relabeling_one_one =
   !a a'. (REP_Relabeling a = REP_Relabeling a') <=> (a = a')

   REP_Relabeling_onto =
   !r. Is_Relabeling r <=> ?a. r = REP_Relabeling a
 *)
val [ABS_Relabeling_one_one, ABS_Relabeling_onto,
     REP_Relabeling_one_one, REP_Relabeling_onto] =
    map (fn f => f Relabeling_ISO_DEF)
        [prove_abs_fn_one_one, prove_abs_fn_onto,
         prove_rep_fn_one_one, prove_rep_fn_onto];

Theorem REP_Relabeling_THM :
    !rf :'b Relabeling. Is_Relabeling (REP_Relabeling rf)
Proof
    GEN_TAC
 >> REWRITE_TAC [REP_Relabeling_onto]
 >> Q.EXISTS_TAC `rf`
 >> REWRITE_TAC []
QED

(* Relabeling labels is extended to actions by renaming tau as tau. *)
val relabel_def = Define `
   (relabel (rf :'b Relabeling) tau = tau) /\
   (relabel rf (label l) = label (REP_Relabeling rf l))`;

(* If the renaming of an action is a label, that action is a label. *)
Theorem Relab_label :
    !(rf :'b Relabeling) u l. (relabel rf u = label l) ==> ?l'. u = label l'
Proof
    Induct_on `u`
 >- REWRITE_TAC [relabel_def, Action_distinct]
 >> REWRITE_TAC [relabel_def]
 >> rpt STRIP_TAC
 >> EXISTS_TAC ``a :'b Label``
 >> REWRITE_TAC []
QED

(* If the renaming of an action is tau, that action is tau. *)
Theorem Relab_tau :
    !(rf :'b Relabeling) u. (relabel rf u = tau) ==> (u = tau)
Proof
    Induct_on `u`
 >> REWRITE_TAC [relabel_def, Action_distinct_label]
QED

(* Apply_Relab: ((Label # Label) list) -> Label -> Label
   (SND of any pair is a name, FST can be either name or coname)
 *)
val Apply_Relab_def = Define `
   (Apply_Relab ([]: ('b Label # 'b Label) list) l = l) /\
   (Apply_Relab ((newold: 'b Label # 'b Label) :: ls) l =
          if (SND newold = l)         then (FST newold)
     else if (COMPL (SND newold) = l) then (COMPL (FST newold))
     else (Apply_Relab ls l))`;

Theorem Apply_Relab_COMPL_THM :
    !labl (s: 'b). Apply_Relab labl (coname s) =
            COMPL (Apply_Relab labl (name s))
Proof
    Induct >- REWRITE_TAC [Apply_Relab_def, COMPL_LAB_def]
 >> rpt GEN_TAC
 >> REWRITE_TAC [Apply_Relab_def]
 >> COND_CASES_TAC
 >- art [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :'b Label # 'b Label) = name s``
 >- art [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM >> art []
QED

Theorem IS_RELABELING :
    !labl :('b Label # 'b Label) list. Is_Relabeling (Apply_Relab labl)
Proof
    Induct
 >- REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def, COMPL_LAB_def]
 >> GEN_TAC
 >> REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def]
 >> GEN_TAC
 >> COND_CASES_TAC
 >- art [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :'b Label # 'b Label) = name s``
 >- art [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM
 >> art [Apply_Relab_COMPL_THM]
QED

(* Defining a relabelling function through substitution-like notation.
   RELAB: (Label # Label) list -> Relabeling
 *)
val RELAB_def = Define `
    RELAB (labl :('b Label # 'b Label) list) = ABS_Relabeling (Apply_Relab labl)`;

(* !labl labl'.
     (RELAB labl = RELAB labl') <=> (Apply_Relab labl = Apply_Relab labl')
 *)
val APPLY_RELAB_THM = save_thm (
   "APPLY_RELAB_THM",
    Q.GENL [`labl`, `labl'`]
      (REWRITE_RULE [GSYM RELAB_def]
        (MATCH_MP (MATCH_MP ABS_Relabeling_one_one
                            (Q.SPEC `labl` IS_RELABELING))
                  (Q.SPEC `labl` IS_RELABELING))));

(******************************************************************************)
(*  Type (and term) of CCS agents                                             *)
(******************************************************************************)

(* Define the type of (pure) CCS agent expressions. (old way)
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

(* new way based on "examples/lambda/basics/generic_termsTheory *)
val tyname = "CCS";

(* ‘GVAR s vv’ corresponds to ‘var 'a’ *)
val vp = “(\n u:unit. n = 0)”;                                  (* 0. var *)

val lp_t = “:unit + 'a Action + unit + unit + 'a Label set + 'a Relabeling + unit”;
val d = mk_var("d", lp_t);

(* ‘GLAM v bv ts us’ corresponds to everything else. *)
val lp =
  “(\n ^d tns uns.
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

(* rpm (recursion permutation) *)
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

(* support *)
Theorem term_REP_eqv[local] :
    support (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t {}
Proof
    srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_tpm, pmact_sing_inv]
QED

Theorem supp_term_REP[local] :
    supp (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t = {}
Proof
    REWRITE_TAC [GSYM SUBSET_EMPTY]
 >> MATCH_MP_TAC (GEN_ALL supp_smallest)
 >> srw_tac [][term_REP_eqv]
QED

Theorem tpm_def'[local] =
    term_REP_tpm |> AP_TERM term_ABS_t |> PURE_REWRITE_RULE [absrep_id]

val t = mk_var("t", newty);
Theorem supptpm_support[local] :
    support ^t_pmact_t ^t (supp gt_pmact (^term_REP_t ^t))
Proof
    srw_tac [][support_def, tpm_def', supp_fresh, absrep_id]
QED

Theorem supptpm_apart[local] :
    x IN supp gt_pmact (^term_REP_t ^t) /\ y NOTIN supp gt_pmact (^term_REP_t ^t)
    ==> ^tpm_t [(x,y)] ^t <> ^t
Proof
    srw_tac [][tpm_def']
 >> DISCH_THEN (MP_TAC o AP_TERM term_REP_t)
 >> srw_tac [][repabs_pseudo_id, genind_gtpm_eqn, genind_term_REP, supp_apart]
QED

Theorem supp_tpm[local] :
    supp ^t_pmact_t ^t = supp gt_pmact (^term_REP_t ^t)
Proof
    match_mp_tac (GEN_ALL supp_unique_apart)
 >> srw_tac [][supptpm_support, supptpm_apart, FINITE_GFV]
QED

Overload FV = “supp ^t_pmact_t”

Theorem FINITE_FV[simp]:
    FINITE (FV t)
Proof
    srw_tac [][supp_tpm, FINITE_GFV]
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

(* term induction *)
fun genit th = let
  val (_, args) = strip_comb (concl th)
  val (tm, x) = case args of [x,y] => (x,y) | _ => raise Fail "Bind"
  val ty = type_of tm
  val t = mk_var("t", ty)
in
  th |> INST [tm |-> t] |> GEN x |> GEN t
end

val term_ind =
    bvc_genind
        |> INST_TYPE [alpha |-> lp_t, beta |-> “:unit”]
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

(* end of the new way *)

val _ = export_theory ();
val _ = html_theory "CCS1";
