(* ========================================================================== *)
(* FILE          : CongruenceScript.sml                                       *)
(* DESCRIPTION   : The theory of congruence and guarded contexts              *)
(*                                                                            *)
(* THESIS        : A Formalization of Unique Solutions of Equations in        *)
(*                 Process Algebra                                            *)
(* AUTHOR        : (c) 2017 Chun Tian, University of Bologna, Italy           *)
(*                 (c) 2018 Chun Tian, Fondazione Bruno Kessler (FBK)         *)
(* DATE          : 2017-2018                                                  *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib relationTheory combinTheory arithmeticTheory;

open CCSLib LabelTheory CCSTheory TransTheory binderLib;
open StrongEQTheory StrongLawsTheory WeakEQTheory WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory ObsCongrConv;
open BisimulationUptoTheory;

val _ = new_theory "Congruence";

val set_ss = std_ss ++ PRED_SET_ss;

(******************************************************************************)
(*                                                                            *)
(*                StrongEQ is preserved by recursive definition               *)
(*                                                                            *)
(******************************************************************************)

Theorem FV_SUBSET_lemma[local] :
    !P X. FV P SUBSET {X} /\ Y <> X ==> Y # P
Proof
    rpt STRIP_TAC
 >> ‘Y IN {X}’ by METIS_TAC [SUBSET_DEF]
 >> fs []
QED

Theorem STRONG_EQUIV_PRESD_BY_REC_lemma :
    !G P Q X. FV P SUBSET {X} /\ FV Q SUBSET {X} /\ StrongEQ P Q /\
              FV G SUBSET {X} /\ CCS_Subst G (rec X P) X --u-> E1 ==>
         ?E2. CCS_Subst G (rec X Q) X --u-> E2 /\
              (STRONG_EQUIV O
               (\x y. ?G. FV G SUBSET {X} /\
                          x = CCS_Subst G (rec X P) X /\
                          y = CCS_Subst G (rec X Q) X) O STRONG_EQUIV) E1 E2
Proof
    HO_MATCH_MP_TAC simple_induction
 >> rw [] (* 8 subgoals *)
 >| [ (* goal 1 (of 8) *)
      fs [TRANS_REC_EQ] (* hard but possible *)\\
      cheat,
      (* goal 2 (of 8) *)
      FULL_SIMP_TAC std_ss [CCS_Subst_nil, NIL_NO_TRANS],
      (* goal 3 (of 8) *)
      FULL_SIMP_TAC std_ss [CCS_Subst_def, TRANS_PREFIX_EQ] \\
      rw [O_DEF] \\
      Q.EXISTS_TAC ‘CCS_Subst G (rec X Q) X’ >> rw [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC ‘CCS_Subst G (rec X P) X’ >> rw [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC ‘G’ >> art [],
      (* goal 4 (of 8): SUM *)
      cheat,
      (* goal 5 (of 8): PAR *)
      cheat, (* FULL_SIMP_TAC std_ss [TRANS_PAR_EQ] *)
      (* goal 6 (of 8):  *)
      cheat, (* FULL_SIMP_TAC std_ss [TRANS_RESTR_EQ] *)
      (* goal 7 (of 8) *)
      cheat, (* FULL_SIMP_TAC std_ss [TRANS_RELAB_EQ] *)
      (* goal 8 (of 8) *)
      rename1 ‘FV G DELETE Y SUBSET {X}’ \\
      Cases_on ‘Y = X’ (* trivial case *)
      >- (‘X # rec Y G’ by rw [FV_thm] \\
          gs [CCS_Subst_elim] \\
          Q.EXISTS_TAC ‘E1’ >> rw [O_DEF] \\
          Q.EXISTS_TAC ‘E1’ >> rw [STRONG_EQUIV_REFL] \\
          Q.EXISTS_TAC ‘E1’ >> rw [STRONG_EQUIV_REFL] \\
          Know ‘X # E1’
          >- (CCONTR_TAC >> fs [] \\
             ‘X IN FV (rec X G)’ by METIS_TAC [SUBSET_DEF, TRANS_FV] \\
              fs [FV_thm]) >> DISCH_TAC \\
          Q.EXISTS_TAC ‘E1’ >> ASM_SIMP_TAC std_ss [CCS_Subst_elim] \\
          MATCH_MP_TAC SUBSET_TRANS \\
          Q.EXISTS_TAC ‘FV (rec X G)’ \\
          CONJ_TAC >- (MATCH_MP_TAC TRANS_FV >> Q.EXISTS_TAC ‘u’ >> art []) \\
          rw [FV_thm]) \\
      Know ‘Y # rec X P /\ Y # rec X Q’
      >- (rw [FV_thm] >> PROVE_TAC [FV_SUBSET_lemma]) >> STRIP_TAC \\
      gs [CCS_Subst_rec] \\
      cheat ]
QED

(* Proposition 4.12 of [1, p.99] or Theorem 4.2 of [2, p.182]

   NOTE: The textbook requirement ‘FV P SUBSET {X} /\ FV Q SUBSET {X}’ is
   necessary, because: if P and Q contains unbounded ‘var s’ subterms other
   than ‘var X’, then these ‘var s’, together with ‘var X’ should all have
   no contributions in making transitions (see VAR_NO_TRANS), but further
   wrapping both P and Q with ‘rec X’ may additionally cause more transitions
   on the side with ‘var X’. In another words, let

   P = a..var X and Q = a..var Y

   clearly P ~ Q since they both have just one transitions (--a->). But then

   rec X P := rec X (a..var X)   and
   rec X Q := rec X (a..var Y)   (X <> Y)

   behave differently in bisimilarity tests: ‘rec X P’ has infinite many a-
   transitions, while ‘rec X Q’ still has just one a-transition, thus no more
   bisimilar.

   To prevent this issue, we must at least require that subterms like ‘var Y’
   do not occur, i.e.

      "P contains free variables at most X"  or  FV P SUBSET {X}.

   Note that it doesn't forbid bounded variables, e.g. rec Z (var Z + var X)
 *)
Theorem STRONG_EQUIV_PRESD_BY_REC :
    !X P Q. FV P SUBSET {X} /\ FV Q SUBSET {X} /\ StrongEQ P Q ==>
            STRONG_EQUIV (rec X P) (rec X Q)
Proof
    rpt STRIP_TAC
 (* applying STRONG_EQUIV_BY_BISIM_UPTO *)
 >> MATCH_MP_TAC STRONG_EQUIV_BY_BISIM_UPTO
 >> Q.EXISTS_TAC ‘\x y. ?G. FV G SUBSET {X} /\
                            x = CCS_Subst G (rec X P) X /\
                            y = CCS_Subst G (rec X Q) X’
 >> BETA_TAC
 >> reverse CONJ_TAC
 >- (Q.EXISTS_TAC ‘var X’ >> rw [FV_thm, CCS_Subst_var_fix])
 (* stage work *)
 >> rw [STRONG_BISIM_UPTO]
 (* applying STRONG_EQUIV_PRESD_BY_REC_lemma *)
 >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_REC_lemma >> art [])
 >> Know ‘!E1. (STRONG_EQUIV O (\x y. ?G. FV G SUBSET {X} /\
                                      x = CCS_Subst G (rec X P) X /\
                                      y = CCS_Subst G (rec X Q) X) O
                STRONG_EQUIV) E1 E2 <=>
               (STRONG_EQUIV O (\x y. ?G. FV G SUBSET {X} /\
                                      x = CCS_Subst G (rec X Q) X /\
                                      y = CCS_Subst G (rec X P) X) O
                STRONG_EQUIV) E2 E1’
 >- (rw [O_DEF] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘CCS_Subst G' (rec X P) X’ >> rw [STRONG_EQUIV_SYM] \\
       Q.EXISTS_TAC ‘CCS_Subst G' (rec X Q) X’ >> rw [STRONG_EQUIV_SYM] \\
       Q.EXISTS_TAC ‘G'’ >> art [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘CCS_Subst G' (rec X Q) X’ >> rw [STRONG_EQUIV_SYM] \\
       Q.EXISTS_TAC ‘CCS_Subst G' (rec X P) X’ >> rw [STRONG_EQUIV_SYM] \\
       Q.EXISTS_TAC ‘G'’ >> art [] ])
 >> Rewr'
 (* applying STRONG_EQUIV_PRESD_BY_REC_lemma again *)
 >> MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_REC_lemma
 >> rw [StrongEQ_SYM]
QED

Theorem StrongEQ_preserved_by_rec :
    !X P Q. FV P SUBSET {X} /\ FV Q SUBSET {X} /\ StrongEQ P Q ==>
            StrongEQ (rec X P) (rec X Q)
Proof
    rpt STRIP_TAC
 >> Know ‘StrongEQ (rec X P) (rec X Q) <=> STRONG_EQUIV (rec X P) (rec X Q)’
 >- (MATCH_MP_TAC StrongEQ_alt_closed \\
     rw [closed_def, FV_thm] >> ASM_SET_TAC [])
 >> Rewr'
 >> MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_REC >> art []
QED

(******************************************************************************)
(*                                                                            *)
(*                one-hole contexts and multi-hole contexts                   *)
(*                                                                            *)
(******************************************************************************)

val _ = type_abbrev_pp ("context", ``:'a CCS -> 'a CCS``);

Definition IS_CONST_def :
    IS_CONST (e :'a context) <=> !t1 t2. e t1 = e t2
End

Theorem IS_CONST_alt :
    !e. IS_CONST e <=> ?p. !t. (e t = p)
Proof
    RW_TAC std_ss [IS_CONST_def]
 >> METIS_TAC []
QED

Theorem IS_CONST_thm :
    !e. IS_CONST e <=> ?p. e = \t. p
Proof
    rw [IS_CONST_alt, FUN_EQ_THM]
QED

(* ONE HOLE CONTEXT (unused)

   NEW: added OH_CONTEXT9 (\t. rec v (c t)) -- Chun Tian, 18 dec 2023
 *)
Inductive OH_CONTEXT :
    (                        OH_CONTEXT (\t. t)) /\              (* OH_CONTEXT1 *)
    (!a c.  OH_CONTEXT c ==> OH_CONTEXT (\t. prefix a (c t))) /\ (* OH_CONTEXT2 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. sum (c t) x)) /\    (* OH_CONTEXT3 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. sum x (c t))) /\    (* OH_CONTEXT4 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. par (c t) x)) /\    (* OH_CONTEXT5 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. par x (c t))) /\    (* OH_CONTEXT6 *)
    (!L c.  OH_CONTEXT c ==> OH_CONTEXT (\t. restr L (c t))) /\  (* OH_CONTEXT7 *)
    (!rf c. OH_CONTEXT c ==> OH_CONTEXT (\t. relab (c t) rf)) /\ (* OH_CONTEXT8 *)
    (!v c.  OH_CONTEXT c ==> OH_CONTEXT (\t. rec v (c t)))       (* OH_CONTEXT9 *)
End

(* renamed following chap2Theory of the lambda example *)
Overload one_hole_context = “OH_CONTEXT”

val [OH_CONTEXT1, OH_CONTEXT2, OH_CONTEXT3, OH_CONTEXT4, OH_CONTEXT5, OH_CONTEXT6,
     OH_CONTEXT7, OH_CONTEXT8, OH_CONTEXT9] =
    map save_thm
        (combine (["OH_CONTEXT1", "OH_CONTEXT2", "OH_CONTEXT3", "OH_CONTEXT4",
                   "OH_CONTEXT5", "OH_CONTEXT6", "OH_CONTEXT7", "OH_CONTEXT8",
                   "OH_CONTEXT9"],
                  CONJUNCTS OH_CONTEXT_rules));

Theorem OH_CONTEXT_combin :
    !c1 c2. OH_CONTEXT c1 /\ OH_CONTEXT c2 ==> OH_CONTEXT (c1 o c2)
Proof
    rpt STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c1`, `c`)
 >> HO_MATCH_MP_TAC OH_CONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> REPEAT STRIP_TAC (* 8 sub-goals here *)
 >| [ FULL_SIMP_TAC std_ss [OH_CONTEXT2],
      FULL_SIMP_TAC std_ss [OH_CONTEXT3],
      FULL_SIMP_TAC std_ss [OH_CONTEXT4],
      FULL_SIMP_TAC std_ss [OH_CONTEXT5],
      FULL_SIMP_TAC std_ss [OH_CONTEXT6],
      FULL_SIMP_TAC std_ss [OH_CONTEXT7],
      FULL_SIMP_TAC std_ss [OH_CONTEXT8],
      FULL_SIMP_TAC std_ss [OH_CONTEXT9] ]
QED

(* Multi-hole (or non-hole) contexts

   NEW: added [CONTEXT8] for (\t. rec v (e t)), while CONTEXT2 is replaced by
        CONTEXT2a and CONTEXT2b.                    -- Chun Tian, 18 dec 2023
 *)
Inductive CONTEXT :
    (        CONTEXT (\t. t)) /\                               (* CONTEXT1 *)
    (        CONTEXT (\t. nil)) /\                             (* CONTEXT2a *)
    (!s.     CONTEXT (\t. var s)) /\                           (* CONTEXT2b *)
    (!a e.   CONTEXT e ==> CONTEXT (\t. prefix a (e t))) /\    (* CONTEXT3 *)
    (!e1 e2. CONTEXT e1 /\ CONTEXT e2
                       ==> CONTEXT (\t. sum (e1 t) (e2 t))) /\ (* CONTEXT4 *)
    (!e1 e2. CONTEXT e1 /\ CONTEXT e2
                       ==> CONTEXT (\t. par (e1 t) (e2 t))) /\ (* CONTEXT5 *)
    (!L e.   CONTEXT e ==> CONTEXT (\t. restr L (e t))) /\     (* CONTEXT6 *)
    (!rf e.  CONTEXT e ==> CONTEXT (\t. relab (e t) rf)) /\    (* CONTEXT7 *)
    (!v e.   CONTEXT e ==> CONTEXT (\t. rec v (e t)))          (* CONTEXT8 *)
End

val [CONTEXT1, CONTEXT2a, CONTEXT2b, CONTEXT3, CONTEXT4, CONTEXT5, CONTEXT6,
     CONTEXT7, CONTEXT8] =
    map save_thm
        (combine (["CONTEXT1", "CONTEXT2a", "CONTEXT2b", "CONTEXT3", "CONTEXT4",
                   "CONTEXT5", "CONTEXT6", "CONTEXT7", "CONTEXT8"],
                  CONJUNCTS CONTEXT_rules));

Theorem CONTEXT3a :
    !a. CONTEXT (\t. prefix a t)
Proof
    ASSUME_TAC CONTEXT1
 >> IMP_RES_TAC CONTEXT3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []
QED

(* cf. chap2Theory.constant_contexts_exist *)
Theorem CONTEXT2 :
    !t. CONTEXT (\x. t)
Proof
    HO_MATCH_MP_TAC simple_induction
 >> rpt STRIP_TAC
 >> SRW_TAC [][CONTEXT_rules]
QED

Theorem CONTEXT_CONST :
    !e. IS_CONST e ==> CONTEXT e
Proof
    rw [IS_CONST_thm]
 >> rw [CONTEXT2]
QED

Theorem CONTEXT3_backward :
    !e u. CONTEXT (\t. prefix u (e t)) ==> CONTEXT e
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o
               (ONCE_REWRITE_RULE [CONTEXT_cases]))
 >> fs [FUN_EQ_THM] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM (MP_TAC o (Q.SPEC `nil`)) >> rw [],
      (* goal 2 (of 2) *)
      METIS_TAC [] ]
QED

Theorem CONTEXT3_full :
    !e u. CONTEXT (\t. prefix u (e t)) <=> CONTEXT e
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >- REWRITE_TAC [CONTEXT3_backward]
 >> REWRITE_TAC [CONTEXT3]
QED

Theorem CONTEXT4_backward :
    !e e'. CONTEXT (\t. sum (e t) (e' t)) ==> CONTEXT e /\ CONTEXT e'
Proof
    rpt STRIP_TAC \\ (* 2 sub-goals here, same tacticals *)
  ( POP_ASSUM (STRIP_ASSUME_TAC o
               (ONCE_REWRITE_RULE [CONTEXT_cases])) (* 7 sub-goals here *)
 >> fs [FUN_EQ_THM] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM (MP_TAC o (Q.SPEC `nil`)) \\
      SIMP_TAC std_ss [CCS_distinct],
      (* goal 2 (of 2) *)
      METIS_TAC [] ] )
QED

Theorem CONTEXT4_full :
    !e e'. CONTEXT (\t. sum (e t) (e' t)) <=> CONTEXT e /\ CONTEXT e'
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >- REWRITE_TAC [CONTEXT4_backward]
 >> REWRITE_TAC [CONTEXT4]
QED

Theorem CONTEXT5_backward :
    !e e'. CONTEXT (\t. par (e t) (e' t)) ==> CONTEXT e /\ CONTEXT e'
Proof
    rpt STRIP_TAC \\ (* 2 sub-goals here, same tacticals *)
  ( POP_ASSUM (STRIP_ASSUME_TAC o
               (ONCE_REWRITE_RULE [CONTEXT_cases])) (* 7 sub-goals here *)
 >> fs [FUN_EQ_THM] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM (MP_TAC o (Q.SPEC `nil`)) \\
      SIMP_TAC std_ss [CCS_distinct],
      (* goal 2 (of 3) *)
      METIS_TAC [] ] )
QED

Theorem CONTEXT5_full :
    !e e'. CONTEXT (\t. par (e t) (e' t)) <=> CONTEXT e /\ CONTEXT e'
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >- REWRITE_TAC [CONTEXT5_backward]
 >> REWRITE_TAC [CONTEXT5]
QED

Theorem CONTEXT6_backward :
    !e L. CONTEXT (\t. restr L (e t)) ==> CONTEXT e
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [CONTEXT_cases]))
 >> fs [FUN_EQ_THM] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM (MP_TAC o (Q.SPEC `nil`)) \\
      SIMP_TAC std_ss [CCS_distinct],
      (* goal 2 (of 2) *)
      METIS_TAC [] ]
QED

Theorem CONTEXT6_full :
    !e L. CONTEXT (\t. restr L (e t)) <=> CONTEXT e
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >- REWRITE_TAC [CONTEXT6_backward]
 >> REWRITE_TAC [CONTEXT6]
QED

Theorem CONTEXT7_backward :
    !e rf. CONTEXT (\t. relab (e t) rf) ==> CONTEXT e
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [CONTEXT_cases]))
 >> fs [FUN_EQ_THM] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM (MP_TAC o (Q.SPEC `nil`)) \\
      SIMP_TAC std_ss [CCS_distinct],
      (* goal 2 (of 2) *)
      METIS_TAC [] ]
QED

Theorem CONTEXT7_full :
    !e rf. CONTEXT (\t. relab (e t) rf) <=> CONTEXT e
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >- REWRITE_TAC [CONTEXT7_backward]
 >> REWRITE_TAC [CONTEXT7]
QED

(*
Theorem CONTEXT8_backward :
    !v e. CONTEXT (\t. rec v (e t)) ==> CONTEXT e
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [CONTEXT_cases]))
 >> fs [FUN_EQ_THM] (* 2 subgoals left *)
 >- (POP_ASSUM (MP_TAC o (Q.SPEC ‘nil’)) \\
     SIMP_TAC std_ss [CCS_distinct])
 (* key assumption: !t. rec v (e t) = rec v' (e' t) *)
 >> FULL_SIMP_TAC std_ss [rec_eq_thm]
 >> Cases_on ‘v = v'’
 >> fs [FORALL_AND_THM] >- METIS_TAC []
 >> qabbrev_tac ‘pi = [(v,v')]’
 >> ‘e = \t. tpm pi (e' t)’ by METIS_TAC []
 >> POP_ORW
 >> MATCH_MP_TAC CONTEXT_tpm >> art []
QED

Theorem CONTEXT8_full :
    !v e. CONTEXT (\t. rec v (e t)) <=> CONTEXT e
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >- REWRITE_TAC [CONTEXT8_backward]
 >> REWRITE_TAC [CONTEXT8]
QED
 *)

Theorem CONTEXT_combin :
    !c1 c2. CONTEXT c1 /\ CONTEXT c2 ==> CONTEXT (c1 o c2)
Proof
    REPEAT STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c1`, `c`)
 >> HO_MATCH_MP_TAC CONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> REPEAT STRIP_TAC (* 8 sub-goals here *)
 >| [ REWRITE_TAC [CONTEXT2a],
      REWRITE_TAC [CONTEXT2b],
      FULL_SIMP_TAC std_ss [CONTEXT3],
      FULL_SIMP_TAC std_ss [CONTEXT4],
      FULL_SIMP_TAC std_ss [CONTEXT5],
      FULL_SIMP_TAC std_ss [CONTEXT6],
      FULL_SIMP_TAC std_ss [CONTEXT7],
      FULL_SIMP_TAC std_ss [CONTEXT8] ]
QED

(* One-hole contexts are also multi-hole contexts *)
Theorem OH_CONTEXT_IMP_CONTEXT :
    !c. OH_CONTEXT c ==> CONTEXT c
Proof
    Induct_on `OH_CONTEXT`
 >> rpt STRIP_TAC (* 9 sub-goals here *)
 >| [ (* goal 1 (of 9) *)
      REWRITE_TAC [CONTEXT1],
      (* goal 2 (of 9) *)
      MATCH_MP_TAC CONTEXT3 >> art [],
      (* goal 3 (of 9) *)
     `CONTEXT (\y. x)` by REWRITE_TAC [CONTEXT2] \\
      Know `CONTEXT (\t. c t + (\y. x) t)`
      >- (MATCH_MP_TAC CONTEXT4 >> art []) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 4 (of 9) *)
     `CONTEXT (\y. x)` by REWRITE_TAC [CONTEXT2] \\
      Know `CONTEXT (\t. (\y. x) t + c t)`
      >- (MATCH_MP_TAC CONTEXT4 >> art []) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 5 (of 9) *)
     `CONTEXT (\y. x)` by REWRITE_TAC [CONTEXT2] \\
      Know `CONTEXT (\t. par (c t) ((\y. x) t))`
      >- (MATCH_MP_TAC CONTEXT5 >> art []) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 6 (of 9) *)
     `CONTEXT (\y. x)` by REWRITE_TAC [CONTEXT2] \\
      Know `CONTEXT (\t. par ((\y. x) t) (c t))`
      >- (MATCH_MP_TAC CONTEXT5 >> art []) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 7 (of 9) *)
      MATCH_MP_TAC CONTEXT6 >> art [],
      (* goal 8 (of 9) *)
      MATCH_MP_TAC CONTEXT7 >> art [],
      (* goal 9 (of 9) *)
      MATCH_MP_TAC CONTEXT8 >> art [] ]
QED

Theorem STRONG_EQUIV_SUBST_CONTEXT :
    !P Q. STRONG_EQUIV P Q ==> !E. CONTEXT E ==> STRONG_EQUIV (E P) (E Q)
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `CONTEXT`
 >> BETA_TAC >> rpt STRIP_TAC (* 9 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [STRONG_EQUIV_REFL]
 >- REWRITE_TAC [STRONG_EQUIV_REFL]
 >| [ (* goal 1 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX >> art [],
      (* goal 2 (of 6) *)
      IMP_RES_TAC STRONG_EQUIV_PRESD_BY_SUM,
      (* goal 3 (of 6) *)
      IMP_RES_TAC STRONG_EQUIV_PRESD_BY_PAR,
      (* goal 4 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art [],
      (* goal 5 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art [],
      (* goal 6 (of 6) *)
      cheat ]
QED

Theorem OBS_CONGR_SUBST_CONTEXT :
    !P Q. OBS_CONGR P Q ==> !E. CONTEXT E ==> OBS_CONGR (E P) (E Q)
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `CONTEXT` >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [OBS_CONGR_REFL]
 >- REWRITE_TAC [OBS_CONGR_REFL]
 >| [ (* goal 1 (of 6) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_PREFIX >> art [],
      (* goal 2 (of 6) *)
      IMP_RES_TAC OBS_CONGR_PRESD_BY_SUM,
      (* goal 3 (of 6) *)
      IMP_RES_TAC OBS_CONGR_PRESD_BY_PAR,
      (* goal 4 (of 6) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_RESTR >> art [],
      (* goal 5 (of 6) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_RELAB >> art [],
      (* goal 5 (of 6) *)
      cheat ]
QED

(******************************************************************************)
(*                                                                            *)
(*             Multi-hole context with guarded sums (GCONTEXT)                *)
(*                                                                            *)
(******************************************************************************)

Inductive GCONTEXT :
    (        GCONTEXT (\t. t)) /\                                (* GCONTEXT1 *)
    (!p.     GCONTEXT (\t. p)) /\                                (* GCONTEXT2 *)
    (!a e.   GCONTEXT e ==> GCONTEXT (\t. prefix a (e t))) /\    (* GCONTEXT3 *)
    (!a1 a2 e1 e2.
             GCONTEXT e1 /\ GCONTEXT e2
                        ==> GCONTEXT (\t. sum (prefix a1 (e1 t)) (* GCONTEXT4 *)
                                              (prefix a2 (e2 t)))) /\
    (!e1 e2. GCONTEXT e1 /\ GCONTEXT e2
                        ==> GCONTEXT (\t. par (e1 t) (e2 t))) /\ (* GCONTEXT5 *)
    (!L e.   GCONTEXT e ==> GCONTEXT (\t. restr L (e t))) /\     (* GCONTEXT6 *)
    (!rf e.  GCONTEXT e ==> GCONTEXT (\t. relab (e t) rf))       (* GCONTEXT7 *)
End

val [GCONTEXT1, GCONTEXT2, GCONTEXT3, GCONTEXT4, GCONTEXT5,
     GCONTEXT6, GCONTEXT7] =
    map save_thm
        (combine (["GCONTEXT1", "GCONTEXT2", "GCONTEXT3", "GCONTEXT4",
                   "GCONTEXT5", "GCONTEXT6", "GCONTEXT7"],
                  CONJUNCTS GCONTEXT_rules));

val GCONTEXT3a = store_thm (
   "GCONTEXT3a",
  ``!a :'a Action. GCONTEXT (\t. prefix a t)``,
    ASSUME_TAC GCONTEXT1
 >> IMP_RES_TAC GCONTEXT3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

val GCONTEXT_combin = store_thm (
   "GCONTEXT_combin", ``!c1 c2. GCONTEXT c1 /\ GCONTEXT c2 ==> GCONTEXT (c1 o c2)``,
    REPEAT STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c1`, `c`)
 >> HO_MATCH_MP_TAC GCONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> rpt STRIP_TAC (* 6 sub-goals here *)
 >| [ REWRITE_TAC [GCONTEXT2],
      FULL_SIMP_TAC std_ss [GCONTEXT3],
      FULL_SIMP_TAC std_ss [GCONTEXT4],
      FULL_SIMP_TAC std_ss [GCONTEXT5],
      FULL_SIMP_TAC std_ss [GCONTEXT6],
      FULL_SIMP_TAC std_ss [GCONTEXT7] ]);

val GCONTEXT_IMP_CONTEXT = store_thm (
   "GCONTEXT_IMP_CONTEXT", ``!c. GCONTEXT c ==> CONTEXT c``,
    Induct_on `GCONTEXT`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      REWRITE_TAC [CONTEXT1],
      (* goal 2 (of 7) *)
      REWRITE_TAC [CONTEXT2],
      (* goal 3 (of 7) *)
      MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [],
      (* goal 4 (of 7) *)
      Know `CONTEXT (\t. (prefix a1 (e1 t)))`
      >- ( MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [] ) \\
      Know `CONTEXT (\t. (prefix a2 (e2 t)))`
      >- ( MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [] ) \\
      KILL_TAC \\
      NTAC 2 DISCH_TAC \\
      Know `CONTEXT (\t. (\t. (prefix a1 (e1 t))) t + (\t. (prefix a2 (e2 t))) t)`
      >- ( MATCH_MP_TAC CONTEXT4 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 5 (of 7) *)
      MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [],
      (* goal 6 (of 7) *)
      MATCH_MP_TAC CONTEXT6 >> ASM_REWRITE_TAC [],
      (* goal 7 (of 7) *)
      MATCH_MP_TAC CONTEXT7 >> ASM_REWRITE_TAC [] ]);

val WEAK_EQUIV_SUBST_GCONTEXT = store_thm (
   "WEAK_EQUIV_SUBST_GCONTEXT",
  ``!P Q. WEAK_EQUIV P Q ==> !E. GCONTEXT E ==> WEAK_EQUIV (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `GCONTEXT`
 >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [WEAK_EQUIV_REFL]
 >| [ (* goal 1 (of 5) *)
      MATCH_MP_TAC WEAK_EQUIV_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 2 (of 5) *)
      MATCH_MP_TAC WEAK_EQUIV_PRESD_BY_GUARDED_SUM \\
      ASM_REWRITE_TAC [],
      (* goal 3 (of 5) *)
      IMP_RES_TAC WEAK_EQUIV_PRESD_BY_PAR,
      (* goal 4 (of 5) *)
      MATCH_MP_TAC WEAK_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [],
      (* goal 5 (of 5) *)
      MATCH_MP_TAC WEAK_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ]);

(******************************************************************************)
(*                                                                            *)
(*                      congruence and precongruence                         *)
(*                                                                            *)
(******************************************************************************)

Definition precongruence :
    precongruence R = PreOrder R /\
        !x y ctx. CONTEXT ctx ==> R x y ==> R (ctx x) (ctx y)
End

(* a special version of precongruence with only guarded sums *)
Definition precongruence' :
    precongruence' R = PreOrder R /\
        !x y ctx. GCONTEXT ctx ==> R x y ==> R (ctx x) (ctx y)
End

(* The definition of congruence for CCS, TODO: use precongruence *)
Definition congruence :
    congruence R = equivalence R /\
        !x y ctx. CONTEXT ctx ==> R x y ==> R (ctx x) (ctx y)
End

(* a special version of congruence with only guarded sums *)
Definition congruence' :
    congruence' R = equivalence R /\
        !x y ctx. GCONTEXT ctx ==> R x y ==> R (ctx x) (ctx y)
End

val STRONG_EQUIV_congruence = store_thm (
   "STRONG_EQUIV_congruence", ``congruence STRONG_EQUIV``,
    REWRITE_TAC [congruence, STRONG_EQUIV_equivalence]
 >> PROVE_TAC [STRONG_EQUIV_SUBST_CONTEXT]);

val WEAK_EQUIV_congruence = store_thm (
   "WEAK_EQUIV_congruence", ``congruence' WEAK_EQUIV``,
    REWRITE_TAC [congruence', WEAK_EQUIV_equivalence]
 >> PROVE_TAC [WEAK_EQUIV_SUBST_GCONTEXT]);

val OBS_CONGR_congruence = store_thm (
   "OBS_CONGR_congruence", ``congruence OBS_CONGR``,
    REWRITE_TAC [congruence, OBS_CONGR_equivalence]
 >> PROVE_TAC [OBS_CONGR_SUBST_CONTEXT]);

(* Building (pre)congruence closure from any relation on CCS *)
val CC_def = Define `
    CC R = (\g h. !c. CONTEXT c ==> R (c g) (c h))`;

val GCC_def = Define `
    GCC R = (\g h. !c. GCONTEXT c ==> R (c g) (c h))`;

val CC_precongruence = store_thm (
   "CC_precongruence", ``!R. PreOrder R ==> precongruence (CC R)``,
    REWRITE_TAC [precongruence, CC_def]
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [PreOrder] \\
      rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        REWRITE_TAC [reflexive_def] >> BETA_TAC \\
        rpt STRIP_TAC \\
        PROVE_TAC [PreOrder, reflexive_def],
        (* goal 1.2 (of 2) *)
        REWRITE_TAC [transitive_def] >> BETA_TAC \\
        rpt STRIP_TAC >> RES_TAC \\
        PROVE_TAC [PreOrder, transitive_def] ],
      (* goal 2 (of 2) *)
      `CONTEXT (c o ctx)` by PROVE_TAC [CONTEXT_combin] \\
      RES_TAC >> FULL_SIMP_TAC std_ss [o_THM] ]);

(* The relation built by CC is indeed a congruence *)
val CC_congruence = store_thm (
   "CC_congruence", ``!R. equivalence R ==> congruence (CC R)``,
    REWRITE_TAC [congruence, CC_def]
 >> RW_TAC std_ss [] (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [equivalence_def] \\
      rpt STRIP_TAC >| (* 3 sub-goals here *)
      [ (* goal 1.1 (of 3) *)
        REWRITE_TAC [reflexive_def] >> BETA_TAC \\
        rpt STRIP_TAC \\
        PROVE_TAC [equivalence_def, reflexive_def],
        (* goal 1.2 (of 3) *)
        REWRITE_TAC [symmetric_def] >> BETA_TAC \\
        rpt GEN_TAC >> EQ_TAC >> rpt STRIP_TAC >> RES_TAC \\ (* 2 sub-goals here *)
        PROVE_TAC [equivalence_def, symmetric_def],
        (* goal 1.3 (of 3) *)
        REWRITE_TAC [transitive_def] >> BETA_TAC \\
        rpt STRIP_TAC >> RES_TAC \\
        PROVE_TAC [equivalence_def, transitive_def] ],
      (* goal 2 (of 2) *)
      `CONTEXT (c o ctx)` by PROVE_TAC [CONTEXT_combin] \\
      RES_TAC >> FULL_SIMP_TAC std_ss [o_THM] ]);

(* The congruence is finer than original relation *)
val CC_is_finer = store_thm (
   "CC_is_finer", ``!R. (CC R) RSUBSET R``,
    REWRITE_TAC [RSUBSET]
 >> REPEAT GEN_TAC
 >> REWRITE_TAC [CC_def]
 >> BETA_TAC
 >> REPEAT STRIP_TAC
 >> `CONTEXT (\x. x)` by PROVE_TAC [CONTEXT_rules]
 >> RES_TAC
 >> POP_ASSUM (ACCEPT_TAC o BETA_RULE));

(* The congruence built by above method is the coarsest congruence contained in R *)
val CC_is_coarsest = store_thm (
   "CC_is_coarsest",
  ``!R R'. congruence R' /\ R' RSUBSET R ==> R' RSUBSET (CC R)``,
    REWRITE_TAC [congruence, RSUBSET, CC_def]
 >> RW_TAC std_ss []);

Theorem PCC_is_coarsest :
    !R R'. precongruence R' /\ R' RSUBSET R ==> R' RSUBSET (CC R)
Proof
    REWRITE_TAC [precongruence, RSUBSET, CC_def]
 >> RW_TAC std_ss []
QED

(******************************************************************************)
(*                                                                            *)
(*                     Weakly guarded (WG) expressions                        *)
(*                                                                            *)
(******************************************************************************)

Inductive WG :
    (!p.                        WG (\t. p)) /\                 (* WG2 *)
    (!a e.   CONTEXT e      ==> WG (\t. prefix a (e t))) /\    (* WG3 *)
    (!e1 e2. WG e1 /\ WG e2 ==> WG (\t. sum (e1 t) (e2 t))) /\ (* WG4 *)
    (!e1 e2. WG e1 /\ WG e2 ==> WG (\t. par (e1 t) (e2 t))) /\ (* WG5 *)
    (!L e.   WG e           ==> WG (\t. restr L (e t))) /\     (* WG6 *)
    (!rf e.  WG e           ==> WG (\t. relab (e t) rf))       (* WG7 *)
End

val [WG2, WG3, WG4, WG5, WG6, WG7] =
    map save_thm
        (combine (["WG2", "WG3", "WG4", "WG5", "WG6", "WG7"], CONJUNCTS WG_rules));

Theorem WG1 : (* WG1 is derivable from WG3 *)
    !a :'a Action. WG (\t. prefix a t)
Proof
    ASSUME_TAC CONTEXT1
 >> IMP_RES_TAC WG3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> art []
QED

Theorem NO_WG0 :
    ~WG (\t. t)
Proof
    ONCE_REWRITE_TAC [WG_cases] >> rpt STRIP_TAC (* 6 subgoals *)
 >- (fs [FUN_EQ_THM] \\
     STRIP_ASSUME_TAC (Q.SPEC `p` CCS_distinct_exists) >> METIS_TAC [])
 >> fs [FUN_EQ_THM]
 >> Q.PAT_X_ASSUM `!t. t = X` (ASSUME_TAC o (Q.SPEC `nil`))
 >> fs [CCS_distinct]
QED

Theorem WG_CONST :
    !e. IS_CONST e ==> WG e
Proof
    RW_TAC std_ss [IS_CONST_def]
 >> Know `e = (\t. e nil)` >- fs [FUN_EQ_THM]
 >> Rewr' >> REWRITE_TAC [WG2]
QED

Theorem NO_WG8 :
    !e X. ~IS_CONST e ==> ~WG (\t. rec X (e t))
Proof
    rpt GEN_TAC >> ONCE_REWRITE_TAC [WG_cases]
 >> fs [FUN_EQ_THM, IS_CONST_def]
 >> rpt STRIP_TAC
 >> Cases_on `p` >> fs [FUN_EQ_THM]
 >> METIS_TAC []
QED

Theorem WG8_IMP_CONST :
    !e X. WG (\t. rec X (e t)) ==> IS_CONST e
Proof
    METIS_TAC [NO_WG8]
QED

Theorem WG3_backward :
    !e u. WG (\t. prefix u (e t)) ==> CONTEXT e
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [WG_cases]
 >> RW_TAC std_ss [FUN_EQ_THM] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      Cases_on `p` (* 8 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- (FULL_SIMP_TAC std_ss [CCS_11] \\
          rename1 `!t. (u = o') /\ (e t = C')` \\
         `(e = \t. C')` by PROVE_TAC [] >> art [CONTEXT2])
      >> PROVE_TAC [CCS_distinct],
      (* goal 2 (of 2) *)
      METIS_TAC [] ]
QED

Theorem WG4_backward :
    !e e'. WG (\t. sum (e t) (e' t)) ==> WG e /\ WG e'
Proof
    rpt STRIP_TAC \\ (* 2 sub-goals here, same tacticals *)
  ( POP_ASSUM (STRIP_ASSUME_TAC o
               (ONCE_REWRITE_RULE [WG_cases])) (* 6 sub-goals here *)
 >| [ (* goal 1 (of 6) *)
      fs [FUN_EQ_THM] \\
      Cases_on `p` (* 8 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- (FULL_SIMP_TAC std_ss [CCS_11] \\
          rename1 `!t. (e t = C') /\ (e' t = C0)` \\
         `(e = \t. C') /\ (e' = \t. C0)` by PROVE_TAC [] \\
          ASM_REWRITE_TAC [WG2])
      >> PROVE_TAC [CCS_distinct],
      (* goal 2 (of 6) *)
      fs [FUN_EQ_THM],
      (* goal 3 (of 6) *)
      fs [FUN_EQ_THM] >> METIS_TAC [],
      (* goal 4 (of 6) *)
      fs [FUN_EQ_THM],
      (* goal 5 (of 6) *)
      fs [FUN_EQ_THM],
      (* goal 6 (of 6) *)
      fs [FUN_EQ_THM] ] )
QED

Theorem WG5_backward :
    !e e'. WG (\t. par (e t) (e' t)) ==> WG e /\ WG e'
Proof
    rpt STRIP_TAC \\ (* 2 subgoals here, same tacticals *)
  ( POP_ASSUM (STRIP_ASSUME_TAC o
               (ONCE_REWRITE_RULE [WG_cases])) \\ (* 6 subgoals here *)
    fs [FUN_EQ_THM] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      Cases_on `p` (* 8 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- (FULL_SIMP_TAC std_ss [CCS_11] \\
          rename1 `!t. (e t = C') /\ (e' t = C0)` \\
         `(e = \t. C') /\ (e' = \t. C0)` by PROVE_TAC [] \\
          ASM_REWRITE_TAC [WG2])
      >> PROVE_TAC [CCS_distinct],
      (* goal 2 (of 2) *)
      METIS_TAC [] ] )
QED

Theorem WG6_backward :
    !e L. WG (\t. restr L (e t)) ==> WG e
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [WG_cases]))
 >> fs [FUN_EQ_THM] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      Cases_on `p` (* 8 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- (FULL_SIMP_TAC std_ss [CCS_11] \\
          rename1 `!t. (L = f) /\ (e t = C')` \\
         `(e = \t. C')` by PROVE_TAC [] >> art [WG2])
      >> PROVE_TAC [CCS_distinct],
      (* goal 2 (of 2) *)
      METIS_TAC [] ]
QED

Theorem WG7_backward :
    !e rf. WG (\t. relab (e t) rf) ==> WG e
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [WG_cases]))
 >> fs [FUN_EQ_THM]
 >| [ (* goal 1 (of 2) *)
      Cases_on `p` (* 8 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- (FULL_SIMP_TAC std_ss [CCS_11] \\
          rename1 `!t. (e t = C') /\ (rf = R)` \\
         `(e = \t. C')` by PROVE_TAC [] >> art [WG2])
      >> PROVE_TAC [CCS_distinct],
      (* goal 2 (of 2) *)
      METIS_TAC [] ]
QED

Theorem WG8_backward :
    !e X. WG (\t. rec X (e t)) ==> WG e
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC WG_CONST
 >> MATCH_MP_TAC WG8_IMP_CONST
 >> Q.EXISTS_TAC `X` >> art []
QED

(* Weakly guarded expressions are also expressions *)
val WG_IMP_CONTEXT = store_thm (
   "WG_IMP_CONTEXT", ``!e. WG e ==> CONTEXT e``,
    Induct_on `WG`
 >> rpt STRIP_TAC (* 6 sub-goals here *)
 >| [ REWRITE_TAC [CONTEXT2],
      MATCH_MP_TAC CONTEXT3 >> art [],
      MATCH_MP_TAC CONTEXT4 >> art [],
      MATCH_MP_TAC CONTEXT5 >> art [],
      MATCH_MP_TAC CONTEXT6 >> art [],
      MATCH_MP_TAC CONTEXT7 >> art [] ]);

val CONTEXT_WG_combin = store_thm (
   "CONTEXT_WG_combin", ``!c e. CONTEXT c /\ WG e ==> WG (c o e)``,
    rpt STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c`, `c`)
 >> HO_MATCH_MP_TAC CONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> rpt STRIP_TAC >> RES_TAC (* 6 sub-goals here *)
 >| [ (* goal 1 (of 6) *)
      REWRITE_TAC [WG2],
      (* goal 2 (of 6) *)
      IMP_RES_TAC WG_IMP_CONTEXT \\
      MP_TAC (Q.SPECL [`a`, `(\x. (c :'a context) (e x))`] WG3) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 3 (of 6) *)
      MP_TAC (Q.SPECL [`(\x. (c :'a context) (e x))`,
                       `(\x. (c' :'a context) (e x))`] WG4) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 4 (of 6) *)
      MP_TAC (Q.SPECL [`(\x. (c :'a context) (e x))`,
                       `(\x. (c' :'a context) (e x))`] WG5) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 5 (of 6) *)
      MP_TAC (Q.SPECL [`L`, `(\x. (c :'a context) (e x))`] WG6) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 6 (of 6) *)
      MP_TAC (Q.SPECL [`rf`, `(\x. (c :'a context) (e x))`] WG7) \\
      BETA_TAC >> RW_TAC std_ss [] ]);

(******************************************************************************)
(*                                                                            *)
(*                     Strongly guarded (SG) expressions                      *)
(*                                                                            *)
(******************************************************************************)

(* X is guarded in E if each occurrence of X is within some subexpression of E of
   the form l.F *)
Inductive SG :
    (!p.                        SG (\t. p)) /\                      (* SG1 *)
    (!l e.   CONTEXT e      ==> SG (\t. prefix (label l) (e t))) /\ (* SG2 *)
    (!a e.   SG e           ==> SG (\t. prefix a (e t))) /\         (* SG3 *)
    (!e1 e2. SG e1 /\ SG e2 ==> SG (\t. sum (e1 t) (e2 t))) /\      (* SG4 *)
    (!e1 e2. SG e1 /\ SG e2 ==> SG (\t. par (e1 t) (e2 t))) /\      (* SG5 *)
    (!L e.   SG e           ==> SG (\t. restr L (e t))) /\          (* SG6 *)
    (!rf e.  SG e           ==> SG (\t. relab (e t) rf))            (* SG7 *)
End

val [SG1, SG2, SG3, SG4, SG5, SG6, SG7] =
    map save_thm
        (combine (["SG1", "SG2", "SG3", "SG4", "SG5", "SG6", "SG7"],
                  CONJUNCTS SG_rules));

(* Strongly guarded expressions are expressions *)
val SG_IMP_CONTEXT = store_thm (
   "SG_IMP_CONTEXT", ``!e. SG e ==> CONTEXT e``,
    Induct_on `SG`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ REWRITE_TAC [CONTEXT2],
      MATCH_MP_TAC CONTEXT3 >> art [],
      MATCH_MP_TAC CONTEXT3 >> art [],
      MATCH_MP_TAC CONTEXT4 >> art [],
      MATCH_MP_TAC CONTEXT5 >> art [],
      MATCH_MP_TAC CONTEXT6 >> art [],
      MATCH_MP_TAC CONTEXT7 >> art [] ]);

(* Strong guardness implies weak guardness *)
val SG_IMP_WG = store_thm (
   "SG_IMP_WG", ``!e. SG e ==> WG e``,
    Induct_on `SG`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ REWRITE_TAC [WG2],
      MATCH_MP_TAC WG3 >> art [],
      MATCH_MP_TAC WG3 >> IMP_RES_TAC SG_IMP_CONTEXT,
      MATCH_MP_TAC WG4 >> art [],
      MATCH_MP_TAC WG5 >> art [],
      MATCH_MP_TAC WG6 >> art [],
      MATCH_MP_TAC WG7 >> art [] ]);

val lemma = Q.prove (`!p :'a CCS. ?q. q <> p`,
    Cases_on `p`
 >- ( Q.EXISTS_TAC `nil + nil` >> PROVE_TAC [CCS_distinct'] )
 >> ( Q.EXISTS_TAC `nil` >> PROVE_TAC [CCS_distinct'] ));

(* an important backward property of SG *)
Theorem SG3_backward :
    !e. SG (\t. prefix tau (e t)) ==> SG e
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
      Cases_on `p` (* 8 or 9 sub-goals here *)
      >- PROVE_TAC [CCS_distinct']
      >- PROVE_TAC [CCS_distinct']
      >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
           `(e = \t. C') \/ (e = \t. C)` by PROVE_TAC [] \\ (* 2 sub-goals *)
           ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
      >> PROVE_TAC [CCS_distinct'],
      (* goal 2 (of 7) *)
      qpat_x_assum `(\t. prefix tau (e t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_11, Action_distinct],
      (* goal 3 (of 7) *)
      qpat_x_assum `(\t. prefix tau (e t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      FULL_SIMP_TAC std_ss [CCS_11] \\
      METIS_TAC [],
      (* goal 4 (of 7) *)
      qpat_x_assum `(\t. prefix tau (e t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 5 (of 7) *)
      qpat_x_assum `(\t. prefix tau (e t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 6 (of 7) *)
      qpat_x_assum `(\t. prefix tau (e t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 7 (of 7) *)
      qpat_x_assum `(\t. prefix tau (e t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'] ]
QED

(* another important backward property of SG *)
Theorem SG4_backward :
    !e e'. SG (\t. sum (e t) (e' t)) ==> SG e /\ SG e'
Proof
    rpt STRIP_TAC \\ (* 2 sub-goals here, same tacticals *)
  ( POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
      Cases_on `p` (* 8 or 9 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
           `((e = \t. C) \/ (e = \t. C')) /\ (e' = \t. C0)` by PROVE_TAC [] \\
           ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
      >> PROVE_TAC [CCS_distinct],
      (* goal 2 (of 7) *)
      qpat_x_assum `(\t. sum (e t) (e' t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 3 (of 7) *)
      qpat_x_assum `(\t. sum (e t) (e' t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 4 (of 7) *)
      qpat_x_assum `(\t. sum (e t) (e' t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      FULL_SIMP_TAC std_ss [CCS_11] \\
      METIS_TAC [],
      (* goal 5 (of 7) *)
      qpat_x_assum `(\t. sum (e t) (e' t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 6 (of 7) *)
      qpat_x_assum `(\t. sum (e t) (e' t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 7 (of 7) *)
      qpat_x_assum `(\t. sum (e t) (e' t)) = X`
        (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'] ] )
QED

val SG10 = store_thm ("SG10",
  ``!e e'. SG (\t. sum (prefix tau (e t)) (prefix tau (e' t))) ==> SG e /\ SG e'``,
    rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) >| (* 7 sub-goals here *)
      [ (* goal 1.1 (of 7) *)
        POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
        Cases_on `p` (* 8 or 9 sub-goals here *)
        >- PROVE_TAC [CCS_distinct]
        >- PROVE_TAC [CCS_distinct]
        >- PROVE_TAC [CCS_distinct]
        >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
             (TRY (Cases_on `C'`) >> TRY (Cases_on `C`)) (* 8 or 9 sub-goals here *)
          >- PROVE_TAC [CCS_distinct]
          >- PROVE_TAC [CCS_distinct]
          >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
               `(e = \t. C'') \/ (e = \t. C')` by PROVE_TAC [] \\
               ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
          >> PROVE_TAC [CCS_distinct] )
        >> PROVE_TAC [CCS_distinct],
        (* goal 1.2 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.3 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.4 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        FULL_SIMP_TAC std_ss [CCS_11] \\
        `e1 = \t. prefix tau (e t)` by PROVE_TAC [] \\
        FULL_SIMP_TAC std_ss [] \\
        IMP_RES_TAC SG3_backward,
        (* goal 1.5 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.6 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.7 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'] ],
      (* goal 2 (of 2) *)
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) >| (* 7 sub-goals here *)
      [ (* goal 1.1 (of 7) *)
        POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
        Cases_on `p` (* 8 or 9 sub-goals here *)
        >- PROVE_TAC [CCS_distinct]
        >- PROVE_TAC [CCS_distinct]
        >- PROVE_TAC [CCS_distinct]
        >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
             Cases_on `C0` (* 8 or 9 sub-goals here *)
          >- PROVE_TAC [CCS_distinct]
          >- PROVE_TAC [CCS_distinct]
          >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
               `(e' = \t. C'') \/ (e' = \t. C')` by PROVE_TAC [] \\
               ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
          >> PROVE_TAC [CCS_distinct] )
        >> PROVE_TAC [CCS_distinct],
        (* goal 1.2 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.3 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.4 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        FULL_SIMP_TAC std_ss [CCS_11] \\
        `e2 = \t. prefix tau (e' t)` by PROVE_TAC [] \\
        FULL_SIMP_TAC std_ss [] \\
        IMP_RES_TAC SG3_backward,
        (* goal 1.5 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.6 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.7 (of 7) *)
        qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'] ]]);

val SG11 = store_thm ("SG11",
  ``!e e' L. SG (\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) ==> SG e``,
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
      Cases_on `p` (* 8 or 9 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
           (TRY (Cases_on `C'`) >> TRY (Cases_on `C`)) (* 8 or 9 sub-goals here *)
        >- PROVE_TAC [CCS_distinct]
        >- PROVE_TAC [CCS_distinct]
        >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
             `(e = \t. C'') \/ (e = \t. C')` by PROVE_TAC [] \\
             ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
        >> PROVE_TAC [CCS_distinct] )
      >> PROVE_TAC [CCS_distinct],
      (* goal 2 (of 7) *)
      qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 3 (of 7) *)
      qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 4 (of 7) *)
      qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      FULL_SIMP_TAC std_ss [CCS_11] \\
      `e1 = \t. prefix tau (e t)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\
      IMP_RES_TAC SG3_backward,
      (* goal 5 (of 7) *)
      qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 6 (of 7) *)
      qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 7 (of 7) *)
      qpat_x_assum `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'] ]);

val SG11' = store_thm ("SG11'",
  ``!e e' L. SG (\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) ==> SG e'``,
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
      Cases_on `p` (* 8 or 9 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
           Cases_on `C0` (* 8 or 9 sub-goals here *)
        >- PROVE_TAC [CCS_distinct]
        >- PROVE_TAC [CCS_distinct]
        >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
             `(e' = \t. C'') \/ (e' = \t. C')` by PROVE_TAC [] \\
             ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
        >> PROVE_TAC [CCS_distinct] )
      >> PROVE_TAC [CCS_distinct],
      (* goal 2 (of 7) *)
      qpat_x_assum `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 3 (of 7) *)
      qpat_x_assum `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 4 (of 7) *)
      qpat_x_assum `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      FULL_SIMP_TAC std_ss [CCS_11] \\
      `e2 = \t. prefix tau (e' t)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\
      IMP_RES_TAC SG3_backward,
      (* goal 5 (of 7) *)
      qpat_x_assum `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 6 (of 7) *)
      qpat_x_assum `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 7 (of 7) *)
      qpat_x_assum `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
          (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'] ]);

(******************************************************************************)
(*                                                                            *)
(*                        Sequential (SEQ) expressions                        *)
(*                                                                            *)
(******************************************************************************)

(* X is sequential in E if every subexpression of E which contains X, apart from
   X itself, is of the form a.F or Sigma F_i *)
Inductive SEQ :
    (                             SEQ (\t. t)) /\              (* SEQ1 *)
    (!p.                          SEQ (\t. p)) /\              (* SEQ2 *)
    (!a e.   SEQ e            ==> SEQ (\t. prefix a (e t))) /\ (* SEQ3 *)
    (!e1 e2. SEQ e1 /\ SEQ e2 ==> SEQ (\t. sum (e1 t) (e2 t))) (* SEQ4 *)
End

val [SEQ1, SEQ2, SEQ3, SEQ4] =
    map save_thm (combine (["SEQ1", "SEQ2", "SEQ3", "SEQ4"], CONJUNCTS SEQ_rules));

val SEQ3a = store_thm ("SEQ3a",
  ``!a :'a Action. SEQ (\t. prefix a t)``,
    ASSUME_TAC SEQ1
 >> IMP_RES_TAC SEQ3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

val SEQ_IMP_CONTEXT = store_thm (
   "SEQ_IMP_CONTEXT", ``!e. SEQ e ==> CONTEXT e``,
    Induct_on `SEQ`
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ REWRITE_TAC [CONTEXT1],
      REWRITE_TAC [CONTEXT2],
      MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC CONTEXT4 >> ASM_REWRITE_TAC [] ]);

val SEQ_combin = store_thm (
   "SEQ_combin", ``!E. SEQ E ==> !E'. SEQ E' ==> SEQ (E o E')``,
    Induct_on `SEQ`
 >> REWRITE_TAC [o_DEF] >> BETA_TAC
 >> REWRITE_TAC [ETA_THM]
 >> rpt STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [SEQ2],
      (* goal 2 (of 3) *)
      RES_TAC >> IMP_RES_TAC SEQ3 \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      POP_ASSUM (MP_TAC o (Q.SPEC `a`)) \\
      KILL_TAC \\
      BETA_TAC >> DISCH_TAC >> METIS_TAC [],
      (* goal 3 (of 3) *)
      `SEQ (\x. E (E'' x)) /\ SEQ (\x. E' (E'' x))` by METIS_TAC [] \\
      METIS_TAC [SEQ4] ]);

val OBS_CONGR_SUBST_SEQ = store_thm (
   "OBS_CONGR_SUBST_SEQ",
  ``!P Q. OBS_CONGR P Q ==> !E. SEQ E ==> OBS_CONGR (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `SEQ` >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [OBS_CONGR_REFL]
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_PREFIX \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC OBS_CONGR_PRESD_BY_SUM ]);

(* Sequential expression with guarded sums *)
Inductive GSEQ :
    (                         GSEQ (\t. t)) /\                 (* GSEQ1 *)
    (!p.                      GSEQ (\t. p)) /\                 (* GSEQ2 *)
    (!a e.        GSEQ e  ==> GSEQ (\t. prefix a (e t))) /\    (* GSEQ3 *)
    (!a1 a2 e1 e2.
       GSEQ e1 /\ GSEQ e2 ==> GSEQ (\t. sum (prefix a1 (e1 t)) (* GSEQ4 *)
                                            (prefix a2 (e2 t))))
End

val [GSEQ1, GSEQ2, GSEQ3, GSEQ4] =
    map save_thm (combine (["GSEQ1", "GSEQ2", "GSEQ3", "GSEQ4"],
                           CONJUNCTS GSEQ_rules));

val GSEQ3a = store_thm ("GSEQ3a",
  ``!a :'a Action. GSEQ (\t. prefix a t)``,
    ASSUME_TAC GSEQ1
 >> IMP_RES_TAC GSEQ3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

val GSEQ_IMP_CONTEXT = store_thm (
   "GSEQ_IMP_CONTEXT", ``!e. GSEQ e ==> CONTEXT e``,
    Induct_on `GSEQ`
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ REWRITE_TAC [CONTEXT1],
      REWRITE_TAC [CONTEXT2],
      MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [],
      qpat_x_assum `CONTEXT e1` (ASSUME_TAC o (Q.SPEC `a1`) o (MATCH_MP CONTEXT3)) \\
      qpat_x_assum `CONTEXT e2` (ASSUME_TAC o (Q.SPEC `a2`) o (MATCH_MP CONTEXT3)) \\
      MP_TAC (Q.SPECL [`\t. (prefix a1 (e1 t))`, `\t. (prefix a2 (e2 t))`] CONTEXT4) \\
      BETA_TAC >> RW_TAC std_ss [] ]);

val GSEQ_combin = store_thm (
   "GSEQ_combin", ``!E. GSEQ E ==> !E'. GSEQ E' ==> GSEQ (E o E')``,
    Induct_on `GSEQ`
 >> REWRITE_TAC [o_DEF] >> BETA_TAC
 >> REWRITE_TAC [ETA_THM]
 >> rpt STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [GSEQ2],
      (* goal 2 (of 3) *)
      RES_TAC >> IMP_RES_TAC GSEQ3 \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      POP_ASSUM (MP_TAC o (Q.SPEC `a`)) \\
      KILL_TAC \\
      BETA_TAC >> DISCH_TAC >> METIS_TAC [],
      (* goal 3 (of 3) *)
      `GSEQ (\x. E (E'' x)) /\ GSEQ (\x. E' (E'' x))` by METIS_TAC [] \\
      METIS_TAC [GSEQ4] ]);

val WEAK_EQUIV_SUBST_GSEQ = store_thm (
   "WEAK_EQUIV_SUBST_GSEQ",
  ``!P Q. WEAK_EQUIV P Q ==> !E. GSEQ E ==> WEAK_EQUIV (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [WEAK_EQUIV_REFL]
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC WEAK_EQUIV_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC WEAK_EQUIV_PRESD_BY_GUARDED_SUM \\
      ASM_REWRITE_TAC [] ]);

(* A combined (strong) induction theorem for SG + SEQ expression, it's easier to prove
   this induction theorem than defining another combined inductive relation SG_SEQ and
   prove SG /\ SEQ = SQ_SEQ, which is a combinatorial explosion of cases.
 *)
val SG_SEQ_strong_induction = store_thm (
   "SG_SEQ_strong_induction",
  ``!R. (!p. R (\t. p)) /\
        (!(l :'a Label) e. SEQ e ==> R (\t. prefix (label l) (e t))) /\
        (!(a :'a Action) e. SG e /\ SEQ e /\ R e ==> R (\t. prefix a (e t))) /\
        (!e1 e2. SG e1 /\ SEQ e1 /\ R e1 /\
                 SG e2 /\ SEQ e2 /\ R e2 ==> R (\t. sum (e1 t) (e2 t)))
        ==> (!e. SG e /\ SEQ e ==> R e)``,
    rpt STRIP_TAC
 >> qpat_x_assum `SG e` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`e`, `e`)
 >> Induct_on `SEQ`
 >> rpt STRIP_TAC >> FULL_SIMP_TAC std_ss []  (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      Suff `~SG (\t. t)` >- PROVE_TAC [] \\
      KILL_TAC \\
      CCONTR_TAC >> FULL_SIMP_TAC std_ss [] \\
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
      >- ( POP_ASSUM (MP_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
           STRIP_ASSUME_TAC (Q.SPEC `p` lemma) >> PROVE_TAC [] ) \\
      qpat_x_assum `(\t. t) = X`
        (ASSUME_TAC o BETA_RULE o (Q.SPEC `nil`) o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 2 (of 3) *)
      reverse (Cases_on `a`) >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        qpat_x_assum `!l e. SEQ e ==> P` MATCH_MP_TAC \\
        ASM_REWRITE_TAC [],
        (* goal 2.2 (of 2) *)
        Suff `SG e` >- ( DISCH_TAC \\
                         qpat_x_assum `!a e. SG e /\ SEQ e /\ R e ==> P` MATCH_MP_TAC \\
                         ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG3_backward >> ASM_REWRITE_TAC [] ],
      (* goal 3 (of 3) *)
      qpat_x_assum `!e1 e2. X` MATCH_MP_TAC \\
      ASM_REWRITE_TAC [] \\
      Suff `SG e /\ SG e'` >- ( STRIP_TAC >> ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
      POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
      MATCH_MP_TAC SG4_backward >> ASM_REWRITE_TAC [] ]);

val SG_GSEQ_strong_induction = store_thm (
   "SG_GSEQ_strong_induction",
  ``!R. (!p. R (\t. p)) /\
        (!(l :'a Label) e. GSEQ e ==> R (\t. prefix (label l) (e t))) /\
        (!(a :'a Action) e. SG e /\ GSEQ e /\ R e ==> R (\t. prefix a (e t))) /\
        (!e1 e2.       SG e1 /\ GSEQ e1 /\ R e1 /\ SG e2 /\ GSEQ e2 /\ R e2
                   ==> R (\t. sum (prefix tau (e1 t)) (prefix tau (e2 t)))) /\
        (!l2 e1 e2.    SG e1 /\ GSEQ e1 /\ R e1 /\ GSEQ e2
                   ==> R (\t. sum (prefix tau (e1 t)) (prefix (label l2) (e2 t)))) /\
        (!l1 e1 e2.    GSEQ e1 /\ SG e2 /\ GSEQ e2 /\ R e2
                   ==> R (\t. sum (prefix (label l1) (e1 t)) (prefix tau (e2 t)))) /\
        (!l1 l2 e1 e2. GSEQ e1 /\ GSEQ e2
                   ==> R (\t. sum (prefix (label l1) (e1 t)) (prefix (label l2) (e2 t))))
        ==> (!e. SG e /\ GSEQ e ==> R e)``,
    rpt STRIP_TAC
 >> qpat_x_assum `SG e` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`e`, `e`)
 >> Induct_on `GSEQ`
 >> rpt STRIP_TAC >> FULL_SIMP_TAC std_ss [] (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      Suff `~SG (\t. t)` >- PROVE_TAC [] \\
      KILL_TAC \\
      CCONTR_TAC >> FULL_SIMP_TAC std_ss [] \\
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
      >- ( POP_ASSUM (MP_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
           STRIP_ASSUME_TAC (Q.SPEC `p` lemma) >> PROVE_TAC [] ) \\
      qpat_x_assum `(\t. t) = X`
        (ASSUME_TAC o BETA_RULE o (Q.SPEC `nil`) o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 2 (of 3) *)
      reverse (Cases_on `a`) >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        qpat_x_assum `!l e. GSEQ e ==> P` MATCH_MP_TAC \\
        ASM_REWRITE_TAC [],
        (* goal 2.2 (of 2) *)
        Suff `SG e` >- ( DISCH_TAC \\
                         qpat_x_assum `!a e. SG e /\ GSEQ e /\ R e ==> P` MATCH_MP_TAC \\
                         ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG3_backward >> ASM_REWRITE_TAC [] ],
      (* goal 3 (of 3) *)
      Cases_on `a1` >> Cases_on `a2` >| (* 4 sub-goals here *)
      [ (* goal 3.1 (of 4) *)
        qpat_x_assum `!e1 e2. X ==> R (\t. prefix tau (e1 t) + prefix tau (e2 t))` MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] \\
        Suff `SG e /\ SG e'` >- ( STRIP_TAC >> ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG10 >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 4) *)
        qpat_x_assum `!l2 e1 e2. X ==> R (\t. prefix tau (e1 t) + prefix (label l2) (e2 t))`
          MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] \\
        Suff `SG e` >- ( STRIP_TAC >> ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG11 >> take [`e'`, `x`] >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 4) *)
        qpat_x_assum `!l1 e1 e2. X ==> R (\t. prefix (label l1) (e1 t) + prefix tau (e2 t))`
          MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] \\
        Suff `SG e'` >- ( STRIP_TAC >> ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG11' >> take [`e`, `x`] >> ASM_REWRITE_TAC [],
        (* goal 3.4 (of 4) *)
        qpat_x_assum `!l1 l2 e1 e2. X ==> R (\t. prefix (label l1) (e1 t) + prefix (label l2) (e2 t))`
          MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] ] ]);

val SG_SEQ_combin = store_thm (
   "SG_SEQ_combin", ``!E. SG E /\ SEQ E ==> !H. SEQ H ==> (SG (H o E) /\ SEQ (H o E))``,
    HO_MATCH_MP_TAC SG_SEQ_strong_induction
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC >> rpt STRIP_TAC (* 8 sub-goals here *)
 >| [ (* goal 1 (of 8) *)
      REWRITE_TAC [SG1],
      (* goal 2 (of 8) *)
      REWRITE_TAC [SEQ2],
      (* goal 3 (of 8) *)
      POP_ASSUM MP_TAC >> Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `SEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 3.1 (of 4) *)
        IMP_RES_TAC SEQ_IMP_CONTEXT \\
        MATCH_MP_TAC SG2 >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 3.3 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM MP_TAC >> BETA_TAC \\
        STRIP_TAC >> METIS_TAC [],
        (* goal 3.4 (of 4) *)
        IMP_RES_TAC (Q.SPECL [`\x. H (prefix (label l) (E x))`,
                              `\x. H' (prefix (label l) (E x))`] SG4) \\
        POP_ASSUM K_TAC \\
        POP_ASSUM MP_TAC \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [] ],
      (* goal 4 (of 8) *)
      ASSUME_TAC (Q.SPECL [`label l`, `E`] SEQ3) \\
      RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` SEQ_combin) \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> KILL_TAC \\
      REWRITE_TAC [o_DEF] >> BETA_TAC \\
      REWRITE_TAC [],
      (* goal 5 (of 8) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `SEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 5.1 (of 4) *)
        MATCH_MP_TAC SG3 >> ASM_REWRITE_TAC [],
        (* goal 5.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 5.3 (of 4) *)
        ASSUME_TAC (Q.SPECL [`a' :'a Action`,
                             `\x. (H :'a CCS -> 'a CCS) (prefix a (E x))`] SG3) \\
        POP_ASSUM MP_TAC \\
        BETA_TAC >> rpt STRIP_TAC >> RES_TAC,
        (* goal 5.4 (of 4) *)
        IMP_RES_TAC (Q.SPECL [`\x. H (prefix a (E x))`, `\x. H' (prefix a (E x))`] SG4) \\
        POP_ASSUM K_TAC \\
        POP_ASSUM MP_TAC \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 6 (of 8) *)
      ASSUME_TAC (Q.SPECL [`a :'a Action`, `E`] SEQ3) \\
      RES_TAC >> NTAC 4 (POP_ASSUM K_TAC) \\
      ASSUME_TAC (Q.SPEC `H` SEQ_combin) \\
      POP_ASSUM (ASSUME_TAC o (fn th => MP th (ASSUME ``SEQ H``))) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `\t. prefix a (E t)`)) \\
      POP_ASSUM MP_TAC \\
      REWRITE_TAC [o_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      PROVE_TAC [],
      (* goal 7 (of 8) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `SEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 7.1 (of 4) *)
        MATCH_MP_TAC SG4 >> ASM_REWRITE_TAC [],
        (* goal 7.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 7.3 (of 4) *)
        ASSUME_TAC (Q.SPECL [`a :'a Action`,
                             `\x. (H :'a CCS -> 'a CCS) (E x + E' x)`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC \\
        PROVE_TAC [],
        (* goal 7.4 (of 4) *)
        IMP_RES_TAC (Q.SPECL [`\x. H (E x + E' x)`,
                              `\x. H' (E x + E' x)`] SG4) \\
        POP_ASSUM K_TAC \\
        POP_ASSUM MP_TAC \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 8 (of 8) *)
      ASSUME_TAC (Q.SPECL [`E`, `E'`] SEQ4) \\
      NTAC 2 (qpat_x_assum `!H. X` K_TAC) >> RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` SEQ_combin) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [] ]);

val SG_GSEQ_combin = store_thm (
   "SG_GSEQ_combin", ``!E. SG E /\ GSEQ E ==> !H. GSEQ H ==> (SG (H o E) /\ GSEQ (H o E))``,
    HO_MATCH_MP_TAC SG_GSEQ_strong_induction
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC >> rpt STRIP_TAC (* 14 sub-goals here *)
 >| [ (* goal 1 (of 14) *)
      REWRITE_TAC [SG1],
      (* goal 2 (of 14) *)
      REWRITE_TAC [GSEQ2],
      (* goal 3 (of 14) *)
      POP_ASSUM MP_TAC >> Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 3.1 (of 4) *)
        IMP_RES_TAC GSEQ_IMP_CONTEXT \\
        MATCH_MP_TAC SG2 >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 3.3 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM MP_TAC >> BETA_TAC \\
        STRIP_TAC >> METIS_TAC [],
        (* goal 3.4 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix a1 (H (prefix (label l) (E t))))`,
                              `\t. (prefix a2 (H' (prefix (label l) (E t))))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [] ],
      (* goal 4 (of 14) *)
      ASSUME_TAC (Q.SPECL [`label l`, `E`] GSEQ3) \\
      RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> KILL_TAC \\
      REWRITE_TAC [o_DEF] >> BETA_TAC \\
      REWRITE_TAC [],
      (* goal 5 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 5.1 (of 4) *)
        MATCH_MP_TAC SG3 >> ASM_REWRITE_TAC [],
        (* goal 5.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 5.3 (of 4) *)
        ASSUME_TAC (Q.SPECL [`a' :'a Action`,
                             `\x. (H :'a CCS -> 'a CCS) (prefix a (E x))`] SG3) \\
        POP_ASSUM MP_TAC \\
        BETA_TAC >> rpt STRIP_TAC >> RES_TAC,
        (* goal 5.4 (of 4) *)
        IMP_RES_TAC SG3 >> POP_ASSUM K_TAC \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix a1 (H (prefix a (E t))))`,
                              `\t. (prefix a2 (H' (prefix a (E t))))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [] ],
      (* goal 6 (of 14) *)
      ASSUME_TAC (Q.SPECL [`a :'a Action`, `E`] GSEQ3) \\
      RES_TAC >> NTAC 4 (POP_ASSUM K_TAC) \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
      POP_ASSUM (ASSUME_TAC o (fn th => MP th (ASSUME ``GSEQ H``))) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `\t. prefix a (E t)`)) \\
      POP_ASSUM MP_TAC \\
      REWRITE_TAC [o_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      PROVE_TAC [],
      (* goal 7 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 7.1 (of 4) *)
        IMP_RES_TAC SG3 \\
        NTAC 2 (POP_ASSUM (MP_TAC o (Q.SPEC `tau`))) >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix tau (E t))`, `\t. (prefix tau (E' t))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [],
        (* goal 7.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 7.3 (of 4) *)
        ASSUME_TAC
          (Q.SPECL [`a :'a Action`,
                    `\x. (H :'a CCS -> 'a CCS) (tau..(E x) + tau..(E' x))`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC \\
        PROVE_TAC [],
        (* goal 7.4 (of 4) *)
        IMP_RES_TAC SG3 >> NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. a1..(H (tau..(E t) + tau..(E' t)))`,
                              `\t. a2..(H' (tau..(E t) + tau..(E' t)))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 8 (of 14) *)
      ASSUME_TAC (Q.SPECL [`tau`, `tau`, `E`, `E'`] GSEQ4) \\
      NTAC 2 (qpat_x_assum `!H. X` K_TAC) >> RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [],
      (* goal 9 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 9.1 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `tau`)) \\
        IMP_RES_TAC GSEQ_IMP_CONTEXT \\
        POP_ASSUM K_TAC \\
        IMP_RES_TAC SG2 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `l2`)) \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix tau (E t))`, `\t. (prefix (label l2) (e2 t))`] SG4) \\
        POP_ASSUM MP_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [],
        (* goal 9.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 9.3 (of 4) *)
        ASSUME_TAC
          (Q.SPECL [`a :'a Action`,
                    `\x. (H :'a CCS -> 'a CCS) (tau..(E x) + (label l2)..(e2 x))`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC \\
        PROVE_TAC [],
        (* goal 9.4 (of 4) *)
        IMP_RES_TAC SG3 >> POP_ASSUM K_TAC \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. a1..(H (tau..(E t) + (label l2)..(e2 t)))`,
                              `\t. a2..(H' (tau..(E t) + (label l2)..(e2 t)))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 10 (of 14) *)
      ASSUME_TAC (Q.SPECL [`tau`, `label l2`, `E`, `e2`] GSEQ4) \\
      qpat_x_assum `!H. X` K_TAC >> RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [],
      (* goal 11 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 11.1 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `tau`)) \\
        IMP_RES_TAC GSEQ_IMP_CONTEXT \\
        qpat_x_assum `CONTEXT E` K_TAC \\
        IMP_RES_TAC SG2 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `l1`)) \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix (label l1) (e1 t))`,
                              `\t. (prefix tau (E t))`] SG4) \\
        POP_ASSUM MP_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [],
        (* goal 11.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 11.3 (of 4) *)
        ASSUME_TAC
          (Q.SPECL [`a :'a Action`,
                    `\x. (H :'a CCS -> 'a CCS)
                           ((label l1)..(e1 x) + tau..(E x))`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC \\
        PROVE_TAC [],
        (* goal 11.4 (of 4) *)
        IMP_RES_TAC SG3 >> POP_ASSUM K_TAC \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. a1..(H ((label l2)..(e2 t) + tau..(E t)))`,
                              `\t. a2..(H' ((label l2)..(e2 t) + tau..(E t)))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 12 (of 14) *)
      ASSUME_TAC (Q.SPECL [`label l1`, `tau`, `e1`, `E`] GSEQ4) \\
      qpat_x_assum `!H. X` K_TAC >> RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [],
      (* goal 13 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 13.1 (of 4) *)
        IMP_RES_TAC GSEQ_IMP_CONTEXT \\
        IMP_RES_TAC SG2 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `l2`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `l1`)) \\
        rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix (label l1) (e1 t))`,
                              `\t. (prefix (label l2) (e2 t))`] SG4) \\
        POP_ASSUM K_TAC \\
        POP_ASSUM MP_TAC >> KILL_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [],
        (* goal 13.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 13.3 (of 4) *)
        ASSUME_TAC
          (Q.SPECL [`a :'a Action`,
                    `\x. (H :'a CCS -> 'a CCS)
                         ((label l1)..(e1 x) + (label l2)..(e2 x))`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC >> PROVE_TAC [],
        (* goal 13.4 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. a1..(H ((label l1)..(e1 t) + (label l2)..(e2 t)))`,
                              `\t. a2..(H' ((label l1)..(e1 t) + (label l2)..(e2 t)))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC >> KILL_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [] ],
      (* goal 14 (of 14) *)
      MP_TAC (Q.SPECL [`label l1`, `label l2`, `e1`, `e2`] GSEQ4) \\
      MP_TAC (Q.SPEC `H` GSEQ_combin) \\
      RW_TAC std_ss [] \\
      qpat_x_assum `!E'. GSEQ E' ==> X`
        (MP_TAC o (Q.SPEC `\t. (label l1)..(e1 t) + (label l2)..(e2 t)`)) \\
      REWRITE_TAC [o_DEF] >> BETA_TAC >> METIS_TAC [] ]);

(******************************************************************************)
(*                                                                            *)
(*               Weakly guarded expressions with guarded sums                 *)
(*                                                                            *)
(******************************************************************************)

(* The only difference from WG is at WGS4, in which the sum has prefixed args,
   and the underlying e1 & e2 can be simply GCONTEXT. *)
val (WGS_rules, WGS_ind, WGS_cases) = Hol_reln `
    (!p.                          WGS (\t. p)) /\                   (* WGS2 *)
    (!a e.   GCONTEXT e       ==> WGS (\t. prefix a (e t))) /\      (* WGS3 *)
    (!a1 a2 e1 e2.
             GCONTEXT e1 /\ GCONTEXT e2
                              ==> WGS (\t. sum (prefix a1 (e1 t))   (* WGS4 *)
                                               (prefix a2 (e2 t)))) /\
    (!e1 e2. WGS e1 /\ WGS e2 ==> WGS (\t. par (e1 t) (e2 t))) /\   (* WGS5 *)
    (!L e.   WGS e            ==> WGS (\t. restr L (e t))) /\       (* WGS6 *)
    (!rf e.  WGS e            ==> WGS (\t. relab (e t) rf)) `;      (* WGS7 *)

val WGS_strongind = DB.fetch "-" "WGS_strongind";

val [WGS2, WGS3, WGS4, WGS5, WGS6, WGS7] =
    map save_thm
        (combine (["WGS2", "WGS3", "WGS4", "WGS5", "WGS6", "WGS7"],
                  CONJUNCTS WGS_rules));

(** WGS1 is derivable from WGS3 *)
val WGS1 = store_thm ("WGS1",
  ``!a :'a Action. WGS (\t. prefix a t)``,
    ASSUME_TAC GCONTEXT1
 >> IMP_RES_TAC WGS3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC
 >> REWRITE_TAC []);

val WGS_IMP_GCONTEXT = store_thm (
   "WGS_IMP_GCONTEXT", ``!e. WGS e ==> GCONTEXT e``,
    Induct_on `WGS`
 >> rpt STRIP_TAC (* 6 sub-goals here *)
 >| [ REWRITE_TAC [GCONTEXT2],
      MATCH_MP_TAC GCONTEXT3 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC GCONTEXT4 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC GCONTEXT5 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC GCONTEXT6 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC GCONTEXT7 >> ASM_REWRITE_TAC [] ]);

val WGS_IMP_CONTEXT = store_thm (
   "WGS_IMP_CONTEXT", ``!e. WGS e ==> CONTEXT e``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC GCONTEXT_IMP_CONTEXT
 >> IMP_RES_TAC WGS_IMP_GCONTEXT);

val GCONTEXT_WGS_combin = store_thm (
   "GCONTEXT_WGS_combin", ``!c e. GCONTEXT c /\ WGS e ==> WGS (c o e)``,
    rpt STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c`, `c`)
 >> HO_MATCH_MP_TAC GCONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> rpt STRIP_TAC >> RES_TAC (* 6 sub-goals here *)
 >| [ (* goal 1 (of 6) *)
      REWRITE_TAC [WGS2],
      (* goal 2 (of 6) *)
      IMP_RES_TAC WGS_IMP_GCONTEXT \\
      MP_TAC (Q.SPECL [`a`, `(\x. (c :'a context) (e x))`] WGS3) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 3 (of 6) *)
      MP_TAC (Q.SPECL [`a1`, `a2`, `(\x. (c :'a context) (e x))`,
                                   `(\x. (c' :'a context) (e x))`] WGS4) \\
      BETA_TAC \\
      IMP_RES_TAC WGS_IMP_GCONTEXT >> RW_TAC std_ss [],
      (* goal 4 (of 6) *)
      MP_TAC (Q.SPECL [`(\x. (c :'a context) (e x))`,
                       `(\x. (c' :'a context) (e x))`] WGS5) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 5 (of 6) *)
      MP_TAC (Q.SPECL [`L`, `(\x. (c :'a context) (e x))`] WGS6) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 6 (of 6) *)
      MP_TAC (Q.SPECL [`rf`, `(\x. (c :'a context) (e x))`] WGS7) \\
      BETA_TAC >> RW_TAC std_ss [] ]);

val _ = export_theory ();
val _ = html_theory "Congruence";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.

 *)
