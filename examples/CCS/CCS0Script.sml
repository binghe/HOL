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

val _ = new_theory "CCS0";

val set_ss = std_ss ++ PRED_SET_ss;

(* ----------------------------------------------------------------------
    Labels and Actions
   ---------------------------------------------------------------------- *)

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
(*  The Type “:'a CCS”                                                        *)
(******************************************************************************)

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

val _ = overload_on ("nu", “restr”);
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

(* nil:    “tnf :'r”
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
         tnf :'r
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

val FORALL_ONE = prove(
  ``(!u:one. P u) = P ()``,
  SRW_TAC [][EQ_IMP_THM, oneTheory.one_induction]);

val FORALL_ONE_FN = prove(
  ``(!uf : one -> 'a. P uf) = !a. P (\u. a)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (Q.SPEC_THEN `uf ()` MP_TAC) THEN
  Q_TAC SUFF_TAC `(\y. uf()) = uf` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][FUN_EQ_THM, oneTheory.one]);

val EXISTS_ONE_FN = prove(
  ``(?f : 'a -> one -> 'b. P f) = (?f : 'a -> 'b. P (\x u. f x))``,
  SRW_TAC [][EQ_IMP_THM] THENL [
    Q.EXISTS_TAC `\a. f a ()` THEN SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `(\x u. f x ()) = f` THEN1 SRW_TAC [][] THEN
    SRW_TAC [][FUN_EQ_THM, oneTheory.one],
    Q.EXISTS_TAC `\a u. f a` THEN SRW_TAC [][]
  ]);

Theorem tm_recursion = 
  parameter_tm_recursion
      |> Q.INST_TYPE [‘:'q’ |-> ‘:unit’]
      |> Q.INST [‘ppm’ |-> ‘discrete_pmact’,
                  ‘vr’ |-> ‘\s u. vru s’,
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
                 ‘pfu’ |-> ‘pf’,
                 ‘smu’ |-> ‘sm’,
                 ‘pru’ |-> ‘pr’,
                 ‘rsu’ |-> ‘rs’,
                 ‘rlu’ |-> ‘rl’,
                 ‘reu’ |-> ‘re’]

(* ----------------------------------------------------------------------
    cases theorem
   ---------------------------------------------------------------------- *)

(* aka CCS_cases *)
Theorem CCS_nchotomy :
    !t. t = nil \/ (?a. t = var a) \/ (?u E. t = prefix u E) \/
        (?E1 E2. t = sum E1 E2) \/ (?E1 E2. t = par E1 E2) \/
        (?L E. t = (restr L) E) \/ (?E rf. t = relab E rf) \/
         ?X E. t = rec X E
Proof
    HO_MATCH_MP_TAC simple_induction
 >> SRW_TAC [][] (* 161 subgoals here *)
 >> METIS_TAC []
QED

val _ = export_theory ();
val _ = html_theory "CCS0";
