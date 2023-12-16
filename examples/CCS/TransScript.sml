(* ========================================================================== *)
(* FILE          : TransScript.sml (was part of CCSScript.sml)                *)
(* DESCRIPTION   : A formalization of the process algebra CCS in HOL          *)
(*                                                                            *)
(* COPYRIGHTS    : 1991-1995 University of Cambridge (Monica Nesi)            *)
(*                 2016-2017 University of Bologna, Italy (Chun Tian)         *)
(*                 2018-2019 Fondazione Bruno Kessler, Italy (Chun Tian)      *)
(*                 2023-2024 Australian National University (Chun Tian)       *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib relationTheory optionTheory listTheory
     rich_listTheory binderLib;

open CCSLib LabelTheory CCSTheory;

val _ = new_theory "Trans";

val set_ss = std_ss ++ PRED_SET_ss;

(******************************************************************************)
(*                                                                            *)
(*            Definition of the transition relation for pure CCS              *)
(*                                                                            *)
(******************************************************************************)

Type transition[pp] = “:'a CCS -> 'a Action -> 'a CCS -> bool”

(* Inductive definition of the transition relation TRANS for CCS.
   TRANS: CCS -> Action -> CCS -> bool
 *)
Inductive TRANS :
    (!E u.                           TRANS (prefix u E) u E) /\         (* PREFIX *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (sum E E') u E1) /\          (* SUM1 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (sum E' E) u E1) /\          (* SUM2 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (par E E') u (par E1 E')) /\ (* PAR1 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (par E' E) u (par E' E1)) /\ (* PAR2 *)
    (!E l E1 E' E2. TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2
                ==> TRANS (par E E') tau (par E1 E2)) /\                (* PAR3 *)
    (!E u E' l L.   TRANS E u E' /\ ((u = tau) \/
                                     ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
                ==> TRANS (restr L E) u (restr L E')) /\                (* RESTR *)
    (!E u E' rf.    TRANS E u E'
                ==> TRANS (relab E rf) (relabel rf u) (relab E' rf)) /\ (* RELABELING *)
    (!E u X E1.     TRANS (CCS_Subst E (rec X E) X) u E1
                ==> TRANS (rec X E) u E1)                               (* REC *)
End

val _ =
    add_rule { term_name = "TRANS", fixity = Infix (NONASSOC, 450),
        pp_elements = [ BreakSpace(1,0), TOK "--", HardSpace 0, TM, HardSpace 0,
                        TOK "->", BreakSpace(1,0) ],
        paren_style = OnlyIfNecessary,
        block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

val _ = TeX_notation { hol = "--", TeX = ("\\HOLTokenTransBegin", 1) };
val _ = TeX_notation { hol = "->", TeX = ("\\HOLTokenTransEnd", 1) };

(* The rules for the transition relation TRANS as individual theorems. *)
val [PREFIX, SUM1, SUM2, PAR1, PAR2, PAR3, RESTR, RELABELING, REC] =
    map save_thm
        (combine (["PREFIX", "SUM1", "SUM2", "PAR1", "PAR2", "PAR3", "RESTR",
                   "RELABELING", "REC"],
                  CONJUNCTS TRANS_rules));

val TRANS_IND = save_thm ("TRANS_IND",
    TRANS_ind |> (Q.SPEC `P`) |> GEN_ALL);

(* The process nil has no transitions.
   !u E. ~TRANS nil u E
 *)
Theorem NIL_NO_TRANS =
    TRANS_cases |> Q.SPECL [‘nil’, ‘u’, ‘E’]
                |> REWRITE_RULE [CCS_distinct]
                |> Q.GENL [‘u’, ‘E’]

(* !u E. nil --u-> E <=> F *)
val NIL_NO_TRANS_EQF = save_thm (
   "NIL_NO_TRANS_EQF",
    Q.GENL [`u`, `E`] (EQF_INTRO (SPEC_ALL NIL_NO_TRANS)));

(* If a process can do an action, the process is not `nil`. *)
Theorem TRANS_IMP_NO_NIL :
    !E u E'. TRANS E u E' ==> E <> nil
Proof
    PROVE_TAC [NIL_NO_TRANS]
QED

(* An recursion variable has no transition.
   !X u E. ~TRANS (var X) u E
 *)
val VAR_NO_TRANS = save_thm ("VAR_NO_TRANS",
    Q.GENL [`X`, `u`, `E`]
           (REWRITE_RULE [CCS_distinct', CCS_one_one]
                         (Q.SPECL [`var X`, `u`, `E`] TRANS_cases)));

(* !u E u' E'. TRANS (prefix u E) u' E' <=> (u' = u) /\ (E' = E) *)
Theorem TRANS_PREFIX_EQ =
        TRANS_cases |> Q.SPECL [‘prefix u E’, ‘u'’, ‘E'’]
                    |> REWRITE_RULE [CCS_distinct', CCS_one_one]
                    |> ONCE_REWRITE_RHS_RULE [EQ_SYM_EQ]
                    |> Q.GENL [‘u’, ‘E’, ‘u'’, ‘E'’]

(* !u E u' E'. u..E --u'-> E' ==> (u' = u) /\ (E' = E) *)
val TRANS_PREFIX = save_thm (
   "TRANS_PREFIX", EQ_IMP_LR TRANS_PREFIX_EQ);

(******************************************************************************)
(*                                                                            *)
(*                The transitions of a binary summation                       *)
(*                                                                            *)
(******************************************************************************)

(* !P P' u P''.
         P + P' --u-> P'' <=>
         (?E E'. (P = E /\ P' = E') /\ E --u-> P'') \/
          ?E E'. (P = E' /\ P' = E) /\ E --u-> P''
 *)
Theorem SUM_cases_EQ =
        TRANS_cases |> Q.SPECL [‘sum P P'’, ‘u’, ‘P''’]
                    |> REWRITE_RULE [CCS_distinct', CCS_one_one]
                    |> Q.GENL [‘P’, ‘P'’, ‘u’, ‘P''’]

val SUM_cases = save_thm (
   "SUM_cases", EQ_IMP_LR SUM_cases_EQ);

Theorem TRANS_SUM_EQ :
    !E E' u E''. TRANS (sum E E') u E'' <=> TRANS E u E'' \/ TRANS E' u E''
Proof
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC SUM_cases >> art [],
      (* goal 2 (of 2) *)
      STRIP_TAC >| (* 2 sub-goals here *)
      [ MATCH_MP_TAC SUM1 >> art [],
        MATCH_MP_TAC SUM2 >> art [] ] ]
QED

(* for CCS_TRANS_CONV *)
val TRANS_SUM_EQ' = store_thm (
   "TRANS_SUM_EQ'",
  ``!E1 E2 u E. TRANS (sum E1 E2) u E <=> TRANS E1 u E \/ TRANS E2 u E``,
    REWRITE_TAC [TRANS_SUM_EQ]);

val TRANS_SUM = save_thm (
   "TRANS_SUM", EQ_IMP_LR TRANS_SUM_EQ);

val TRANS_COMM_EQ = store_thm ("TRANS_COMM_EQ",
  ``!E E' E'' u. TRANS (sum E E') u E'' <=> TRANS (sum E' E) u E''``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ MATCH_MP_TAC SUM2, MATCH_MP_TAC SUM1 ] \\
      art [],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ MATCH_MP_TAC SUM2, MATCH_MP_TAC SUM1 ] \\
      art [] ]);

val TRANS_ASSOC_EQ = store_thm ("TRANS_ASSOC_EQ",
  ``!E E' E'' E1 u. TRANS (sum (sum E E') E'') u E1 <=> TRANS (sum E (sum E' E'')) u E1``,
    rpt GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC TRANS_SUM >| (* 4 sub-goals here *)
        [ MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM2 >> MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM2 >> MATCH_MP_TAC SUM1 ] \\
        art [],
        (* goal 1.2 (of 2) *)
        MATCH_MP_TAC SUM2 >> MATCH_MP_TAC SUM2 \\
        art [] ],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM1 \\
        art [],
        IMP_RES_TAC TRANS_SUM >| (* 4 sub-goals here *)
        [ MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM2,
          MATCH_MP_TAC SUM2,
          MATCH_MP_TAC SUM2 ] >> art [] ] ]);

val TRANS_ASSOC_RL = save_thm (
   "TRANS_ASSOC_RL", EQ_IMP_RL TRANS_ASSOC_EQ);

val TRANS_SUM_NIL_EQ = store_thm (
   "TRANS_SUM_NIL_EQ",
  ``!E u E'. TRANS (sum E nil) u E' <=> TRANS E u E'``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM \\
      IMP_RES_TAC NIL_NO_TRANS,
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      MATCH_MP_TAC SUM1 >> art [] ]);

(* !E u E'. E + nil --u-> E' ==> E --u-> E' *)
val TRANS_SUM_NIL = save_thm ("TRANS_SUM_NIL", EQ_IMP_LR TRANS_SUM_NIL_EQ);

val TRANS_P_SUM_P_EQ = store_thm ("TRANS_P_SUM_P_EQ",
  ``!E u E'. TRANS (sum E E) u E' = TRANS E u E'``,
    rpt GEN_TAC
 >> EQ_TAC
 >| [ DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM,
      DISCH_TAC \\
      MATCH_MP_TAC SUM1 >> art [] ]);

val TRANS_P_SUM_P = save_thm
  ("TRANS_P_SUM_P", EQ_IMP_LR TRANS_P_SUM_P_EQ);

val PAR_cases_EQ = save_thm ("PAR_cases_EQ",
    Q.GENL [`P`, `P'`, `u`, `P''`]
        (REWRITE_RULE [CCS_distinct', CCS_one_one]
                      (Q.SPECL [`par P P'`, `u`, `P''`] TRANS_cases)));

val PAR_cases = save_thm ("PAR_cases", EQ_IMP_LR PAR_cases_EQ);

(* NOTE: the shape of this theorem can be easily derived from above definition
   by replacing REWRITE_RULE with SIMP_RULE, however the inner existential
   variable (E1) has a different name. *)
Theorem TRANS_PAR_EQ :
    !E E' u E''. TRANS (par E E') u E'' <=>
                 (?E1. (E'' = par E1 E') /\ TRANS E u E1) \/
                 (?E1. (E'' = par E E1) /\ TRANS E' u E1) \/
                 (?E1 E2 l. (u = tau) /\ (E'' = par E1 E2) /\
                            TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2)
Proof
    rpt GEN_TAC >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* case 1 (LR) *)
      STRIP_TAC \\
      IMP_RES_TAC PAR_cases >| (* 3 sub-goals here *)
      [ (* goal 1.1 *)
        DISJ1_TAC \\
        Q.EXISTS_TAC `E1` >> art [],
        (* goal 1.2 *)
        DISJ2_TAC >> DISJ1_TAC \\
        Q.EXISTS_TAC `E1` >> art [],
        (* goal 1.3 *)
        DISJ2_TAC >> DISJ2_TAC \\
        take [`E1`, `E2`, `l`] >> art [] ],
      (* case 2 (RL) *)
      STRIP_TAC >> art [] (* 3 sub-goals, same initial tactics *)
   >| [ MATCH_MP_TAC PAR1 >> art [],
        MATCH_MP_TAC PAR2 >> art [],
        MATCH_MP_TAC PAR3 \\
        Q.EXISTS_TAC `l` >> art [] ] ]
QED

val TRANS_PAR = save_thm ("TRANS_PAR", EQ_IMP_LR TRANS_PAR_EQ);

val TRANS_PAR_P_NIL = store_thm ("TRANS_PAR_P_NIL",
  ``!E u E'. TRANS (par E nil) u E' ==> (?E''. TRANS E u E'' /\ (E' = par E'' nil))``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR
 >| [ Q.EXISTS_TAC `E1` >> art [],
      IMP_RES_TAC NIL_NO_TRANS,
      IMP_RES_TAC NIL_NO_TRANS ]);

val TRANS_PAR_NO_SYNCR = store_thm ("TRANS_PAR_NO_SYNCR",
  ``!(l :'a Label) l'. l <> COMPL l' ==>
        !E E' E''. ~(TRANS (par (prefix (label l) E) (prefix (label l') E')) tau E'')``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR (* 3 sub-goals here *)
 >| [ IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_11 \\
      CHECK_ASSUME_TAC
        (REWRITE_RULE [SYM (ASSUME ``(l'' :'a Label) = l``),
                       SYM (ASSUME ``COMPL (l'' :'a Label) = l'``), COMPL_COMPL_LAB]
                      (ASSUME ``~(l = COMPL (l' :'a Label))``)) \\
      RW_TAC bool_ss [] ]);

val RESTR_cases_EQ = save_thm (
   "RESTR_cases_EQ",
    Q.GENL [`P'`, `u`, `L`, `P`]
           (REWRITE_RULE [CCS_distinct', CCS_one_one, Action_distinct, Action_11]
                         (Q.SPECL [`restr L P`, `u`, `P'`] TRANS_cases)));

val RESTR_cases = save_thm (
   "RESTR_cases", EQ_IMP_LR RESTR_cases_EQ);

Theorem TRANS_RESTR_EQ :
    !E L u E'.
     TRANS (restr L E) u E' <=>
     ?E'' l. (E' = restr L E'') /\ TRANS E u E'' /\
             ((u = tau) \/ ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
Proof
  let val a1 = ASSUME ``(u :'a Action) = tau``
      and a2 = ASSUME ``u = label (l :'a Label)``
      and a3 = ASSUME ``TRANS E'' u E'''``
      and a4 = ASSUME ``TRANS E u E''``
  in
    rpt GEN_TAC
 >> EQ_TAC >| (* two goals here *)
    [ (* case 1 (LR) *)
      STRIP_TAC \\
      IMP_RES_TAC RESTR_cases \\ (* two sub-goals here, first two steps are shared *)
      take [`E'''`, `l`] >|
      [ (* goal 1.1 *)
        art [REWRITE_RULE [a1] a3],
        (* goal 1.2 *)
        art [REWRITE_RULE [a2] a3] ],
      (* case 2 (RL) *)
      STRIP_TAC >> art [] >| (* two sub-goals here *)
      [ (* sub-goal 2.1 *)
        MATCH_MP_TAC RESTR \\
        art [REWRITE_RULE [a1] a4],
        (* sub-goal 2.2 *)
        MATCH_MP_TAC RESTR \\
        Q.EXISTS_TAC `l` \\
        art [REWRITE_RULE [a2] a4] ] ]
  end
QED

val TRANS_RESTR = save_thm (
   "TRANS_RESTR", EQ_IMP_LR TRANS_RESTR_EQ);

val TRANS_P_RESTR = store_thm (
   "TRANS_P_RESTR",
  ``!E u E' L. TRANS (restr L E) u (restr L E') ==> TRANS E u E'``,
  let
      val thm = REWRITE_RULE [CCS_one_one]
                  (ASSUME ``restr (L :'a Label set) E' = restr L E''``)
  in
      rpt STRIP_TAC \\
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ FILTER_ASM_REWRITE_TAC (fn t => t !~ ``(u :'a Action) = tau``) [thm],
        FILTER_ASM_REWRITE_TAC (fn t => t !~ ``(u :'a Action) = label l``) [thm]
      ]
  end);

val RESTR_NIL_NO_TRANS = store_thm ("RESTR_NIL_NO_TRANS",
  ``!(L :'a Label set) u E. ~(TRANS (restr L nil) u E)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RESTR (* two sub-goals here, but same proofs *)
 >> IMP_RES_TAC NIL_NO_TRANS);

val TRANS_IMP_NO_RESTR_NIL = store_thm ("TRANS_IMP_NO_RESTR_NIL",
  ``!E u E'. TRANS E u E' ==> !L. ~(E = restr L nil)``,
    rpt STRIP_TAC
 >> ASSUME_TAC (REWRITE_RULE [ASSUME ``E = restr L nil``]
                             (ASSUME ``TRANS E u E'``))
 >> IMP_RES_TAC RESTR_NIL_NO_TRANS);

val TRANS_RESTR_NO_NIL = store_thm ("TRANS_RESTR_NO_NIL",
  ``!E L u E'. TRANS (restr L E) u (restr L E') ==> ~(E = nil)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RESTR
 >> ASSUME_TAC (REWRITE_RULE [ASSUME ``E = nil``]
                             (ASSUME ``TRANS E u E''``))
 >> IMP_RES_TAC NIL_NO_TRANS);

val RESTR_LABEL_NO_TRANS = store_thm ("RESTR_LABEL_NO_TRANS",
  ``!(l :'a Label) L. (l IN L) \/ ((COMPL l) IN L) ==>
                      (!E u E'. ~(TRANS (restr L (prefix (label l) E)) u E'))``,
    rpt STRIP_TAC (* 2 goals here *)
 >| [ (* goal 1 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 1.1 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``, Action_distinct]
                        (ASSUME ``(u :'a Action) = label l``)),
        (* goal 1.2 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (MP (REWRITE_RULE
                [REWRITE_RULE [ASSUME ``(u :'a Action) = label l'``, Action_11]
                              (ASSUME ``(u :'a Action) = label l``)]
                (ASSUME ``~((l' :'a Label) IN L)``))
              (ASSUME ``(l :'a Label) IN L``)) ],
      (* goal 2 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 2.1 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``, Action_distinct]
                        (ASSUME ``(u :'a Action) = label l``)),
        (* goal 2.2 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (MP (REWRITE_RULE
                [REWRITE_RULE [ASSUME ``(u :'a Action) = label l'``, Action_11]
                              (ASSUME ``(u :'a Action) = label l``)]
                (ASSUME ``~((COMPL (l' :'a Label)) IN L)``))
              (ASSUME ``(COMPL (l :'a Label)) IN L``)) ] ]);

(* |- !E rf u P.
         relab E rf --u-> P <=>
         ?E' u' E'' rf'.
             ((E = E') /\ (rf = rf')) /\ (u = relabel rf' u') /\
             (P = relab E'' rf') /\ E' --u'-> E''
 *)
val RELAB_cases_EQ = save_thm
  ("RELAB_cases_EQ",
    TRANS_cases |> (Q.SPEC `relab E rf`)
                |> (REWRITE_RULE [CCS_distinct', CCS_one_one])
                |> (Q.SPECL [`u`, `P`])
                |> (Q.GENL [`E`, `rf`, `u`, `P`]));

val RELAB_cases = save_thm ("RELAB_cases", EQ_IMP_LR RELAB_cases_EQ);

Theorem TRANS_RELAB_EQ :
    !E rf u E'. TRANS (relab E rf) u E' <=>
                ?u' E''. (u = relabel rf u') /\
                         (E' = relab E'' rf) /\ TRANS E u' E''
Proof
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC RELAB_cases \\
      take [`u'`, `E'''`] >> art [],
      (* goal 2 (of 2) *)
      STRIP_TAC \\
      PURE_ONCE_ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC RELABELING \\
      PURE_ONCE_ASM_REWRITE_TAC [] ]
QED

val TRANS_RELAB = save_thm ("TRANS_RELAB", EQ_IMP_LR TRANS_RELAB_EQ);

val TRANS_RELAB_labl = save_thm ("TRANS_RELAB_labl",
    Q.GENL [`E`, `labl`] (Q.SPECL [`E`, `RELAB labl`] TRANS_RELAB));

val RELAB_NIL_NO_TRANS = store_thm ("RELAB_NIL_NO_TRANS",
  ``!(rf :'a Relabeling) u E. ~(TRANS (relab nil rf) u E)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RELAB
 >> IMP_RES_TAC NIL_NO_TRANS);

(* |- !X E u E'.
         rec X E --u-> E' <=>
         ?E'' X'. ((X = X') /\ (E = E'')) /\ [rec X' E''/X'] E'' --u-> E'
 *)
val REC_cases_EQ = save_thm
  ("REC_cases_EQ",
    TRANS_cases |> (Q.SPEC `rec X E`)
                |> (REWRITE_RULE [CCS_distinct', CCS_one_one])
                |> (Q.SPECL [`u`, `E'`])
                |> (Q.GENL [`X`, `E`, `u`, `E'`]));

val REC_cases = save_thm ("REC_cases", EQ_IMP_LR REC_cases_EQ);

Theorem TRANS_REC_EQ :
    !X E u E'. TRANS (rec X E) u E' <=> TRANS (CCS_Subst E (rec X E) X) u E'
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- PURE_ONCE_REWRITE_TAC [REC]
 >> PURE_ONCE_REWRITE_TAC [REC_cases_EQ]
 >> rpt STRIP_TAC
 >> fs [rec_eq_thm, CCS_Subst]
 >> rename1 ‘X <> Y’
 >> rename1 ‘X # P’
 (* stage work *)
 >> rw [fresh_tpm_subst]
 >> Q.ABBREV_TAC ‘E = [var X/Y] P’
 >> Know ‘rec X E = rec Y ([var Y/X] E)’
 >- (MATCH_MP_TAC SIMPLE_ALPHA \\
     rw [Abbr ‘E’, FV_SUB])
 >> Rewr'
 >> rw [Abbr ‘E’]
 >> Know ‘[var Y/X] ([var X/Y] P) = P’
 >- (MATCH_MP_TAC lemma15b >> art [])
 >> Rewr'
 >> Suff ‘[rec Y P/X] ([var X/Y] P) = [rec Y P/Y] P’
 >- rw []
 >> MATCH_MP_TAC lemma15a >> art []
QED

val TRANS_REC = save_thm ("TRANS_REC", EQ_IMP_LR TRANS_REC_EQ);

Theorem TRANS_FV :
    !E u E'. TRANS E u E' ==> FV E' SUBSET (FV E)
Proof
    HO_MATCH_MP_TAC TRANS_IND (* strongind is useless *)
 >> RW_TAC set_ss [FV_thm] (* 7 subgoals *)
 >> TRY (ASM_SET_TAC []) (* 1 - 6 *)
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `FV (CCS_Subst E (rec X E) X)`
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> REWRITE_TAC [FV_SUBSET_REC_PRO]
QED

(*
Theorem CCS_Subst_IMP_NOTIN :
    !X E. (!E'. CCS_Subst E E' X = E) ==> X NOTIN (FV E)
Proof
    cheat
QED

(* if E[t/X] = E[t'/X] for all t t', X must not be free in E *)
Theorem CCS_Subst_IMP_NOTIN_FV :
    !X E. (!E1 E2. CCS_Subst E E1 X = CCS_Subst E E2 X) ==> X NOTIN (FV E)
Proof
    cheat
QED

Theorem FV_REC_PREF :
    !X E u E'. FV (CCS_Subst E (rec X (prefix u E')) X) =
               FV (CCS_Subst E (rec X E') X)
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_thm]
QED

Theorem FV_REC_SUM :
    !X E E1 E2. FV (CCS_Subst E (rec X (E1 + E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_thm] (* 4 subgoals *)
 >> SET_TAC []
QED

Theorem FV_REC_PAR :
    !X E E1 E2. FV (CCS_Subst E (rec X (par E1 E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_thm] (* 4 subgoals *)
 >> SET_TAC []
QED
 *)

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
    RW_TAC std_ss [IS_PROC_def, FV_thm]
QED

Theorem IS_PROC_sum :
    !P Q. IS_PROC (sum P Q) <=> IS_PROC P /\ IS_PROC Q
Proof
    RW_TAC set_ss [IS_PROC_def, FV_thm]
QED

Theorem IS_PROC_par :
    !P Q. IS_PROC (par P Q) <=> IS_PROC P /\ IS_PROC Q
Proof
    RW_TAC set_ss [IS_PROC_def, FV_thm]
QED

Theorem IS_PROC_restr :
    !P L. IS_PROC (restr L P) <=> IS_PROC P
Proof
    RW_TAC set_ss [IS_PROC_def, FV_thm]
QED

Theorem IS_PROC_relab :
    !P rf. IS_PROC (relab P rf) <=> IS_PROC P
Proof
    RW_TAC set_ss [IS_PROC_def, FV_thm]
QED

Theorem TRANS_PROC :
    !E u E'. TRANS E u E' /\ IS_PROC E ==> IS_PROC E'
Proof
    RW_TAC std_ss [IS_PROC_def]
 >> `FV E' SUBSET FV E` by PROVE_TAC [TRANS_FV]
 >> rfs []
QED

val _ = export_theory ();
val _ = html_theory "Trans";
