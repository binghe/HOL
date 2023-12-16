(* ========================================================================== *)
(* FILE          : LabelScript.sml (was part of CCSScript.sml)                *)
(* DESCRIPTION   : A formalization of the process algebra CCS in HOL          *)
(*                                                                            *)
(* COPYRIGHTS    : 1991-1995 University of Cambridge (Monica Nesi)            *)
(*                 2016-2017 University of Bologna, Italy (Chun Tian)         *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib relationTheory optionTheory listTheory CCSLib
     rich_listTheory;

open generic_termsTheory binderLib nomsetTheory nomdatatype;

val _ = new_theory "Label";

val set_ss = std_ss ++ PRED_SET_ss;

(* ----------------------------------------------------------------------
    Labels and Actions
   ---------------------------------------------------------------------- *)

(* Define the set of labels as the union of names (`in`) (strings) and
   co-names (`out`) (complement of names) *)
Datatype: Label = name 'a | coname 'a
End

(* Define structural induction on labels
   !P. (!s. P (name s)) /\ (!s. P (coname s)) ==> !L. P L
 *)
val Label_induction = TypeBase.induction_of ``:'a Label``;

(* The structural cases theorem for the type Label
   !LL. (?s. LL = name s) \/ ?s. LL = coname s
 *)
val Label_cases = TypeBase.nchotomy_of ``:'a Label``;

(* The distinction and injectivity theorems for the type Label
   !a' a. name a <> coname a'
   (!a a'. (name a = name a') <=> (a = a')) /\
       !a a'. (coname a = coname a') <=> (a = a')
 *)
val Label_distinct = TypeBase.distinct_of ``:'a Label``;
val Label_distinct' = save_thm ("Label_distinct'", GSYM Label_distinct);

val Label_not_eq = save_thm (
   "Label_not_eq", STRIP_FORALL_RULE EQF_INTRO Label_distinct);

val Label_not_eq' = save_thm (
   "Label_not_eq'", STRIP_FORALL_RULE
                        (PURE_REWRITE_RULE [SYM_CONV ``name s = coname s'``])
                        Label_not_eq);

val Label_11 = TypeBase.one_one_of ``:'a Label``;

(* NEW: define the set of actions as the OPTION of Label *)
Type Action[pp] = ``:'a Label option``;

val _ = overload_on ("tau",   ``NONE :'a Action``);
val _ = overload_on ("label", ``SOME :'a Label -> 'a Action``);

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
   "Action_induction", INST_TYPE [``:'a`` |-> ``:'a Label``] option_induction);

(* The structural cases theorem for the type Action
   !AA. (AA = tau) \/ ?L. AA = label L
 *)
val Action_cases = save_thm (
   "Action_cases", INST_TYPE [``:'a`` |-> ``:'a Label``] option_nchotomy);

(* The distinction and injectivity theorems for the type Action
   !a. tau <> label a
   !a a'. (label a = label a') <=> (a = a')
 *)
val Action_distinct = save_thm (
   "Action_distinct", INST_TYPE [``:'a`` |-> ``:'a Label``] NOT_NONE_SOME);

val Action_distinct_label = save_thm (
   "Action_distinct_label", INST_TYPE [``:'a`` |-> ``:'a Label``] NOT_SOME_NONE);

val Action_11 = save_thm (
   "Action_11", INST_TYPE [``:'a`` |-> ``:'a Label``] SOME_11);

(* !A. A <> tau ==> ?L. A = label L *)
val Action_no_tau_is_Label = save_thm (
   "Action_no_tau_is_Label",
    Q.GEN `A` (DISJ_IMP (Q.SPEC `A` Action_cases)));

(* Extract the label from a visible action, LABEL: Action -> Label. *)
val _ = overload_on ("LABEL", ``THE :'a Label option -> 'a Label``);

(* |- !x. LABEL (label x) = x *)
val LABEL_def = save_thm (
   "LABEL_def", INST_TYPE [``:'a`` |-> ``:'a Label``] THE_DEF);

(* |- (!x. IS_SOME (label x) <=> T) /\ (IS_SOME 't <=> F) *)
val IS_LABEL_def = save_thm (
   "IS_LABEL_def", INST_TYPE [``:'a`` |-> ``:'a Label``] IS_SOME_DEF);

val _ = export_rewrites ["LABEL_def", "IS_LABEL_def"];

(* Define the complement of a label, COMPL: Label -> Label. *)
val COMPL_LAB_def = Define `(COMPL_LAB (name (s :'a)) = (coname s)) /\
                            (COMPL_LAB (coname s) = (name s))`;

val _ = overload_on ("COMPL", ``COMPL_LAB``);
val _ = export_rewrites ["COMPL_LAB_def"];

val coname_COMPL = store_thm
  ("coname_COMPL", ``!(s :'a). coname s = COMPL (name s)``,
    REWRITE_TAC [COMPL_LAB_def]);

val COMPL_COMPL_LAB = store_thm (
   "COMPL_COMPL_LAB", ``!(l :'a Label). COMPL_LAB (COMPL_LAB l) = l``,
    Induct >> REWRITE_TAC [COMPL_LAB_def]);

(* Extend the complement to actions, COMPL_ACT: Action -> Action. *)
val COMPL_ACT_def = Define `
   (COMPL_ACT (label (l: 'a Label)) = label (COMPL l)) /\
   (COMPL_ACT tau = tau)`;

val _ = overload_on ("COMPL", ``COMPL_ACT``);
val _ = export_rewrites ["COMPL_ACT_def"];

Theorem COMPL_COMPL_ACT :
    !(a :'a Action). COMPL_ACT (COMPL_ACT a) = a
Proof
    Induct_on `a`
 >- REWRITE_TAC [COMPL_ACT_def]
 >> REWRITE_TAC [COMPL_ACT_def, COMPL_COMPL_LAB]
QED

(* auxiliary theorem about complementary labels. *)
Theorem COMPL_THM :
    !(l :'a Label) s. (l <> name s ==> COMPL l <> coname s) /\
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

(* Relabeling function is subtype of `:'a Label -> 'a Label *)
val Is_Relabeling_def = Define `
    Is_Relabeling (f: 'a Label -> 'a Label) = (!s. f (coname s) = COMPL (f (name s)))`;

val EXISTS_Relabeling = store_thm ("EXISTS_Relabeling",
  ``?(f: 'a Label -> 'a Label). Is_Relabeling f``,
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
    !rf :'a Relabeling. Is_Relabeling (REP_Relabeling rf)
Proof
    GEN_TAC
 >> REWRITE_TAC [REP_Relabeling_onto]
 >> Q.EXISTS_TAC `rf`
 >> REWRITE_TAC []
QED

(* Relabeling labels is extended to actions by renaming tau as tau. *)
val relabel_def = Define `
   (relabel (rf :'a Relabeling) tau = tau) /\
   (relabel rf (label l) = label (REP_Relabeling rf l))`;

(* If the renaming of an action is a label, that action is a label. *)
Theorem Relab_label :
    !(rf :'a Relabeling) u l. (relabel rf u = label l) ==> ?l'. u = label l'
Proof
    Induct_on `u`
 >- REWRITE_TAC [relabel_def, Action_distinct]
 >> REWRITE_TAC [relabel_def]
 >> rpt STRIP_TAC
 >> EXISTS_TAC ``a :'a Label``
 >> REWRITE_TAC []
QED

(* If the renaming of an action is tau, that action is tau. *)
Theorem Relab_tau :
    !(rf :'a Relabeling) u. (relabel rf u = tau) ==> (u = tau)
Proof
    Induct_on `u`
 >> REWRITE_TAC [relabel_def, Action_distinct_label]
QED

(* Apply_Relab: ((Label # Label) list) -> Label -> Label
   (SND of any pair is a name, FST can be either name or coname)
 *)
val Apply_Relab_def = Define `
   (Apply_Relab ([]: ('a Label # 'a Label) list) l = l) /\
   (Apply_Relab ((newold: 'a Label # 'a Label) :: ls) l =
          if (SND newold = l)         then (FST newold)
     else if (COMPL (SND newold) = l) then (COMPL (FST newold))
     else (Apply_Relab ls l))`;

Theorem Apply_Relab_COMPL_THM :
    !labl (s: 'a). Apply_Relab labl (coname s) =
            COMPL (Apply_Relab labl (name s))
Proof
    Induct >- REWRITE_TAC [Apply_Relab_def, COMPL_LAB_def]
 >> rpt GEN_TAC
 >> REWRITE_TAC [Apply_Relab_def]
 >> COND_CASES_TAC
 >- art [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :'a Label # 'a Label) = name s``
 >- art [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM >> art []
QED

Theorem IS_RELABELING :
    !labl :('a Label # 'a Label) list. Is_Relabeling (Apply_Relab labl)
Proof
    Induct
 >- REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def, COMPL_LAB_def]
 >> GEN_TAC
 >> REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def]
 >> GEN_TAC
 >> COND_CASES_TAC
 >- art [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :'a Label # 'a Label) = name s``
 >- art [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM
 >> art [Apply_Relab_COMPL_THM]
QED

(* Defining a relabelling function through substitution-like notation.
   RELAB: (Label # Label) list -> Relabeling
 *)
val RELAB_def = Define `
    RELAB (labl :('a Label # 'a Label) list) = ABS_Relabeling (Apply_Relab labl)`;

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

val _ = export_theory ();
val _ = html_theory "Label";
