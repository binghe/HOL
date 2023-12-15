(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna, Italy (Author: Chun Tian)
 * Copyright 2018-2019  Fondazione Bruno Kessler, Italy (Author: Chun Tian)
 * Copyright 2023-2024  The Australian National University (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib relationTheory optionTheory listTheory CCSLib
     rich_listTheory;

open LabelTheory CCSTheory;

val _ = new_theory "Trans";

val set_ss = std_ss ++ PRED_SET_ss;

val (CCS_size_tm, CCS_size_def) = TypeBase.size_of ``:('a, 'b) CCS``;

(**********************************************************************)
(*              Free and bound (recursion) variables                  *)
(**********************************************************************)

(* ('a, 'b) CCS -> 'a set (set of free variables) *)
Definition FV_def :
   (FV (nil :('a, 'b) CCS) = (EMPTY :'a set)) /\
   (FV (prefix u p)        = FV p) /\
   (FV (sum p q)           = (FV p) UNION (FV q)) /\
   (FV (par p q)           = (FV p) UNION (FV q)) /\
   (FV (restr L p)         = FV p) /\
   (FV (relab p rf)        = FV p) /\
   (FV (var X)             = {X}) /\
   (FV (rec X p)           = (FV p) DELETE X)
End

(* broken into separate theorems *)
val [FV_nil,   FV_prefix, FV_sum, FV_par,
     FV_restr, FV_relab,  FV_var, FV_rec] =
    map save_thm
        (combine (["FV_nil",   "FV_prefix",
                   "FV_sum",   "FV_par",
                   "FV_restr", "FV_relab",
                   "FV_var",   "FV_rec"], CONJUNCTS FV_def));

Theorem FV_SUBSET :
    !X E E'. FV (CCS_Subst E E' X) SUBSET (FV E) UNION (FV E')
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [FV_def, CCS_Subst_def]
 >> ASM_SET_TAC []
QED

(* This stronger result doesn't lead to a simpler proof
   of TRANS_FV, as FV_SUBSET_REC cannot be further improved *)
Theorem FV_SUBSET_PRO :
    !X E E'. FV (CCS_Subst E E' X) SUBSET ((FV E) DELETE X) UNION (FV E')
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [FV_def, CCS_Subst_def]
 >> ASM_SET_TAC []
QED

Theorem FV_SUBSET_REC :
    !X E. FV (CCS_Subst E (rec X E) X) SUBSET (FV E)
Proof
    rpt GEN_TAC
 >> ASSUME_TAC (Q.SPECL [`X`, `E`, `rec X E`] FV_SUBSET)
 >> ASM_SET_TAC [FV_def]
QED

Theorem NOTIN_FV_lemma :
    !X E E'. X NOTIN FV (CCS_Subst E (rec X E') X)
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_def]
QED

Theorem FV_SUBSET_REC_PRO :
    !X E. FV (CCS_Subst E (rec X E) X) SUBSET (FV E) DELETE X
Proof
    rpt GEN_TAC
 >> ASSUME_TAC (Q.SPECL [`X`, `E`] FV_SUBSET_REC)
 >> ASSUME_TAC (Q.SPECL [`X`, `E`, `E`] NOTIN_FV_lemma)
 >> ASM_SET_TAC []
QED

Theorem TRANS_FV :
    !E u E'. TRANS E u E' ==> FV E' SUBSET (FV E)
Proof
    HO_MATCH_MP_TAC TRANS_IND (* strongind is useless *)
 >> RW_TAC set_ss [FV_def] (* 7 subgoals *)
 >> TRY (ASM_SET_TAC []) (* 1 - 6 *)
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `FV (CCS_Subst E (rec X E) X)`
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> REWRITE_TAC [FV_SUBSET_REC_PRO]
QED

Theorem CCS_Subst_elim :
    !X E. X NOTIN (FV E) ==> !E'. (CCS_Subst E E' X = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* one left *)
 >> Cases_on `a = X` >- fs []
 >> RES_TAC >> ASM_SIMP_TAC std_ss []
QED

Theorem CCS_Subst_elim_IMP_NOTIN :
    !X E. (!E'. CCS_Subst E E' X = E) ==> X NOTIN (FV E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* 2 goals left *)
 >- (CCONTR_TAC >> fs [] \\
     PROVE_TAC [Q.SPEC `var a` CCS_distinct_exists])
 >> Cases_on `X = a` >- fs []
 >> DISJ1_TAC >> fs []
QED

(* if E[t/X] = E[t'/X] for all t t', X must not be free in E *)
Theorem CCS_Subst_IMP_NOTIN_FV :
    !X E. (!E1 E2. CCS_Subst E E1 X = CCS_Subst E E2 X) ==> X NOTIN (FV E)
Proof
    Suff `!X E. X IN (FV E) ==> ?E1 E2. CCS_Subst E E1 X <> CCS_Subst E E2 X`
 >- METIS_TAC []
 >> GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* 5 subgoals left *)
 >- (Q.EXISTS_TAC `nil` >> METIS_TAC [CCS_distinct_exists]) >>
 RES_TAC >> take [`E1`, `E2`] >> art []
QED

Theorem FV_REC_PREF :
    !X E u E'. FV (CCS_Subst E (rec X (prefix u E')) X) =
               FV (CCS_Subst E (rec X E') X)
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_def]
QED

Theorem FV_REC_SUM :
    !X E E1 E2. FV (CCS_Subst E (rec X (E1 + E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* 4 subgoals *)
 >> SET_TAC []
QED

Theorem FV_REC_PAR :
    !X E E1 E2. FV (CCS_Subst E (rec X (par E1 E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* 4 subgoals *)
 >> SET_TAC []
QED

Theorem FINITE_FV :
    !E. FINITE (FV E)
Proof
    Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_def]
QED

(* ('a, 'b) CCS -> 'a set (set of bound variables) *)
Definition BV_def :
   (BV (nil :('a, 'b) CCS) = (EMPTY :'a set)) /\
   (BV (prefix u p)        = BV p) /\
   (BV (sum p q)           = (BV p) UNION (BV q)) /\
   (BV (par p q)           = (BV p) UNION (BV q)) /\
   (BV (restr L p)         = BV p) /\
   (BV (relab p rf)        = BV p) /\
   (BV (var X)             = EMPTY) /\
   (BV (rec X p)           = X INSERT (BV p))
End

(* broken into separate theorems *)
val [BV_nil,   BV_prefix, BV_sum, BV_par,
     BV_restr, BV_relab,  BV_var, BV_rec] =
    map save_thm
        (combine (["BV_nil",   "BV_prefix",
                   "BV_sum",   "BV_par",
                   "BV_restr", "BV_relab",
                   "BV_var",   "BV_rec"], CONJUNCTS BV_def));

Theorem BV_SUBSET :
    !X E E'. BV (CCS_Subst E E' X) SUBSET (BV E) UNION (BV E')
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [BV_def, CCS_Subst_def]
 >> ASM_SET_TAC []
QED

Theorem BV_SUBSET_REC :
    !X E. BV (CCS_Subst E (rec X E) X) SUBSET (X INSERT (BV E))
Proof
    rpt GEN_TAC
 >> ASSUME_TAC (Q.SPECL [`X`, `E`, `rec X E`] BV_SUBSET)
 >> ASM_SET_TAC [BV_def]
QED

Theorem TRANS_BV :
    !E u E'. TRANS E u E' ==> BV E' SUBSET BV E
Proof
    HO_MATCH_MP_TAC TRANS_ind
 >> RW_TAC set_ss [BV_def] (* 7 subgoals *)
 >> TRY (ASM_SET_TAC []) (* 1 - 6 *)
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `BV (CCS_Subst E (rec X E) X)` >> art []
 >> fs [BV_SUBSET_REC]
QED

Theorem BV_REC :
    !X E. X IN BV (rec X E)
Proof
    RW_TAC std_ss [BV_def, IN_INSERT]
QED

Theorem BV_SUBSET_rules :
    !X E E'. (BV E)  SUBSET (BV (rec X E)) /\
             (BV E)  SUBSET (BV (sum E E')) /\
             (BV E') SUBSET (BV (sum E E')) /\
             (BV E)  SUBSET (BV (par E E')) /\
             (BV E') SUBSET (BV (par E E'))
Proof
    rpt GEN_TAC >> SET_TAC [BV_def]
QED

Theorem FINITE_BV :
    !E. FINITE (BV E)
Proof
    Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, BV_def]
QED

(* i.e. closed term *)
Definition IS_PROC_def :
    IS_PROC E <=> (FV E = EMPTY)
End

Definition ALL_PROC_def :
    ALL_PROC Es <=> EVERY IS_PROC Es
End

Theorem IS_PROC_EL :
    !Es n. ALL_PROC Es /\ n < LENGTH Es ==> IS_PROC (EL n Es)
Proof
    RW_TAC list_ss [ALL_PROC_def, EVERY_MEM, MEM_EL]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `n` >> art []
QED

Theorem IS_PROC_prefix :
    !P u. IS_PROC (prefix u P) <=> IS_PROC P
Proof
    RW_TAC std_ss [IS_PROC_def, FV_def]
QED

Theorem IS_PROC_sum :
    !P Q. IS_PROC (sum P Q) <=> IS_PROC P /\ IS_PROC Q
Proof
    RW_TAC set_ss [IS_PROC_def, FV_def]
QED

Theorem IS_PROC_par :
    !P Q. IS_PROC (par P Q) <=> IS_PROC P /\ IS_PROC Q
Proof
    RW_TAC set_ss [IS_PROC_def, FV_def]
QED

Theorem IS_PROC_restr :
    !P L. IS_PROC (restr L P) <=> IS_PROC P
Proof
    RW_TAC set_ss [IS_PROC_def, FV_def]
QED

Theorem IS_PROC_relab :
    !P rf. IS_PROC (relab P rf) <=> IS_PROC P
Proof
    RW_TAC set_ss [IS_PROC_def, FV_def]
QED

Theorem TRANS_PROC :
    !E u E'. TRANS E u E' /\ IS_PROC E ==> IS_PROC E'
Proof
    RW_TAC std_ss [IS_PROC_def]
 >> `FV E' SUBSET FV E` by PROVE_TAC [TRANS_FV]
 >> rfs []
QED

(**********************************************************************)
(*                Free and bound names (sorts) ('b)                   *)
(**********************************************************************)

(* Learnt from Robert Beers (not used so far) *)
Definition ALL_IDENTICAL :
    ALL_IDENTICAL t = ?x. !y. MEM y t ==> (y = x)
End

(* (FN :('a, 'b) CCS -> 'a list -> 'b Label set) *)
val FN_definition = `
   (FN (nil :('a, 'b) CCS) J  = (EMPTY :'b Label set)) /\
   (FN (prefix (label l) p) J = l INSERT (FN p J)) /\   (* here! *)
   (FN (prefix tau p) J       = FN p J) /\
   (FN (sum p q) J            = (FN p J) UNION (FN q J)) /\
   (FN (par p q) J            = (FN p J) UNION (FN q J)) /\
   (FN (restr L p) J          = (FN p J) DIFF (L UNION (IMAGE COMPL_LAB L))) /\
   (FN (relab p rf) J         = IMAGE (REP_Relabeling rf) (FN p J)) /\ (* here *)
   (FN (var X) J              = EMPTY) /\
   (FN (rec X p) J            = if (MEM X J) then
                                    FN (CCS_Subst p (rec X p) X) (DELETE_ELEMENT X J)
                                else EMPTY)`;

(* (BN :('a, 'b) CCS -> 'a list -> 'b Label set) *)
val BN_definition = `
   (BN (nil :('a, 'b) CCS) J  = (EMPTY :'b Label set)) /\
   (BN (prefix u p) J         = BN p J) /\
   (BN (sum p q) J            = (BN p J) UNION (BN q J)) /\
   (BN (par p q) J            = (BN p J) UNION (BN q J)) /\
   (BN (restr L p) J          = (BN p J) UNION L) /\ (* here *)
   (BN (relab p rf) J         = BN p J) /\
   (BN (var X) J              = EMPTY) /\
   (BN (rec X p) J            = if (MEM X J) then
                                    BN (CCS_Subst p (rec X p) X) (DELETE_ELEMENT X J)
                                else EMPTY)`;

(* This is how we get the correct tactics (FN_tac):
 - val FN_defn = Hol_defn "FN" FN_definition;
 - Defn.tgoal FN_defn;
 *)
local
  val tactic = (* the use of `($< LEX $<)` is learnt from Ramana Kumar *)
      WF_REL_TAC `inv_image ($< LEX $<)
                            (\x. (LENGTH (SND x), ^CCS_size_tm (\x. 0) (\x. 0) (FST x)))`
   >> rpt STRIP_TAC >- (IMP_RES_TAC LENGTH_DELETE_ELEMENT_LE >> art [])
   >> REWRITE_TAC [CCS_size_def]
   >> simp [];
in
  val FN_def = TotalDefn.tDefine "FN" FN_definition tactic;
  val BN_def = TotalDefn.tDefine "BN" BN_definition tactic;
end;

(* (free_names :('a, 'b) CCS -> 'b Label set) collects all visible
   labels (also called "sorts") as the prefix, w.r.t relabeling operators. *)
val free_names_def = Define
   `free_names p = FN p (SET_TO_LIST (BV p))`;

(* (bound_names :('a, 'b) CCS -> 'b Label set) collects all visible
   labels by the restriction operator. *)
val bound_names_def = Define
   `bound_names p = BN p (SET_TO_LIST (BV p))`;

val FN_UNIV1 = store_thm ("FN_UNIV1",
  ``!p. free_names p <> (UNIV :'b Label set) ==> ?a. a NOTIN free_names p``,
    PROVE_TAC [EQ_UNIV]);

val FN_UNIV2 = store_thm ("FN_UNIV2",
  ``!p q. free_names p UNION free_names q <> (UNIV :'b Label set) ==>
          ?a. a NOTIN free_names p /\ a NOTIN free_names q``,
    PROVE_TAC [EQ_UNIV, IN_UNION]);

val _ = export_theory ();
val _ = html_theory "Trans";
