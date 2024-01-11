(* ========================================================================== *)
(* FILE          : FutureScript.sml                                           *)
(* DESCRIPTION   : "Future" theory of CCS (for potentially open terms)        *)
(*                                                                            *)
(* COPYRIGHTS    : 2023-2024 Australian National University (Chun Tian)       *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory bisimulationTheory listTheory finite_mapTheory;

(* lambda theories *)
open binderLib;

(* local theories *)
open CCSLib CCSTheory CCSSyntax CCSConv;
open StrongEQTheory StrongEQLib StrongLawsTheory;
open WeakEQTheory WeakEQLib WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory;
open CongruenceTheory CoarsestCongrTheory;
open TraceTheory ExpansionTheory ContractionTheory;
open BisimulationUptoTheory UniqueSolutionsTheory;
(* open MultivariateTheory; *)

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val _ = new_theory "Future";

Theorem TRANS_tpm :
    !pi E u E'. TRANS E u E' ==> TRANS (tpm pi E) u (tpm pi E')
Proof
    Q.X_GEN_TAC ‘pi’
 >> HO_MATCH_MP_TAC TRANS_IND >> rw [tpm_thm, CCS_Subst]
 (* 10 subgoals *)
 >- (rw [PREFIX])
 >- (MATCH_MP_TAC SUM1 >> art [])
 >- (MATCH_MP_TAC SUM2 >> art [])
 >- (MATCH_MP_TAC PAR1 >> art [])
 >- (MATCH_MP_TAC PAR2 >> art [])
 >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC ‘l’ >> art [])
 >- (MATCH_MP_TAC RESTR >> rw [])
 >- (MATCH_MP_TAC RESTR >> Q.EXISTS_TAC ‘l’ >> art [])
 >- (MATCH_MP_TAC RELABELING >> art [])
 (* stage work *)
 >> fs [tpm_subst]
 >> MATCH_MP_TAC REC' >> rw []
 >> Q.PAT_X_ASSUM ‘TRANS _ u (tpm pi E')’ K_TAC
 >> ‘var (lswapstr pi X) = tpm pi (var X)’ by rw [tpm_thm] >> POP_ORW
 >> CCONTR_TAC
 >> fs [tpm_eqr]
QED

Theorem TRANS_tpm_eq :
    !pi E u E'. TRANS E u E' <=> TRANS (tpm pi E) u (tpm pi E')
Proof
    rpt GEN_TAC
 >> EQ_TAC >- rw [TRANS_tpm]
 >> DISCH_TAC
 >> ‘E = tpm (REVERSE pi) (tpm pi E)’ by rw [] >> POP_ORW
 >> ‘E' = tpm (REVERSE pi) (tpm pi E')’ by rw [] >> POP_ORW
 >> MATCH_MP_TAC TRANS_tpm >> art []
QED

Theorem STRONG_EQUIV_tpm_cong_lemma[local] :
    !u v P Q. STRONG_EQUIV P Q ==> STRONG_EQUIV (tpm [(u,v)] P) (tpm [(u,v)] Q)
Proof
    qx_genl_tac [‘u’, ‘v’]
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘{u;v}’ >> rw [] (* 8 subgoals *)
 >> cheat
(*
    rpt STRIP_TAC
 >> rw [Once PROPERTY_STAR]
 >| [ (* goal 1 (of 2) *)
      Know ‘tpm (REVERSE pi) (tpm pi P) --u-> tpm (REVERSE pi) E1’
      >- (art [GSYM TRANS_tpm_eq]) >> rw [] \\
      IMP_RES_TAC PROPERTY_STAR_LEFT \\
      Q.EXISTS_TAC ‘tpm pi E2’ >> rw [GSYM TRANS_tpm_eq] \\
      cheat,
      (* goal 2 (of 2) *)
      cheat ]
 *)
QED

(* If the possibly free variable X of E were substituted by two equivalent terms,
   the resulting two terms must be also equivalent.

   NOTE: The similar statement |- STRONG_EQUIV P Q ==> STRONG_EQUIV ([E/X] P) ([E/X] Q)
         does NOT hold. The antecedent ‘STRONG_EQUIV P Q’ must be ‘StrongEQ P Q’.

   This theorem uses the new ‘SUB’ instead of the old ‘CCS_Subst’, and the theorem
   STRONG_UNFOLDING' is needed in handling the (only) non-trivial recursion case.
 *)
Theorem STRONG_EQUIV_SUB_cong :
    !E P Q X. STRONG_EQUIV P Q ==> STRONG_EQUIV ([P/X] E) ([Q/X] E)
Proof
    HO_MATCH_MP_TAC simple_induction >> rw [] (* 7 subgoals *)
 >- (Cases_on ‘s = X’ >> rw [SUB_THM])
 >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX >> rw [])
 >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_SUM >> rw [])
 >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> rw [])
 >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR  >> rw [])
 >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB  >> rw [])
 (* applying NEW_TAC *)
 >> Q.ABBREV_TAC ‘Z = FV P UNION FV Q UNION FV E UNION {X;y}’
 >> ‘FINITE Z’ by rw [Abbr ‘Z’]
 >> NEW_TAC "z" “Z :string set”
 >> Q.PAT_X_ASSUM ‘FINITE Z’ K_TAC
 >> fs [Abbr ‘Z’]
 >> rename1 ‘Z <> Y’
 (* applying SIMPLE_ALPHA *)
 >> Know ‘rec Y E = rec Z ([var Z/Y] E)’
 >- (MATCH_MP_TAC SIMPLE_ALPHA >> art [])
 >> Rewr'
 (* applying fresh_tpm_subst *)
 >> Know ‘[var Z/Y] E = tpm [(Z,Y)] E’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC fresh_tpm_subst >> art [])
 >> Rewr'
 >> Q.ABBREV_TAC ‘E' = tpm [(Z,Y)] E’ (* [var Z/Y] E’ *)
 (* applying SUB_REC *)
 >> Know ‘[P/X] (rec Z E') = rec Z ([P/X] E')’
 >- (MATCH_MP_TAC SUB_REC >> rw [])
 >> Rewr'
 >> Know ‘[Q/X] (rec Z E') = rec Z ([Q/X] E')’
 >- (MATCH_MP_TAC SUB_REC >> rw [])
 >> Rewr'
 (* applying STRONG_UNFOLDING' *)
 >> Q.ABBREV_TAC ‘E1 = [P/X] E'’
 >> Q.ABBREV_TAC ‘E2 = [Q/X] E'’
 >> MATCH_MP_TAC STRONG_EQUIV_TRANS
 >> Q.EXISTS_TAC ‘[rec Z E1/Z] E1’
 >> CONJ_TAC >- rw [STRONG_UNFOLDING']
 >> MATCH_MP_TAC STRONG_EQUIV_TRANS
 >> Q.EXISTS_TAC ‘[rec Z E2/Z] E2’
 >> reverse CONJ_TAC >- rw [Once STRONG_EQUIV_SYM_EQ, STRONG_UNFOLDING']
 (* special case: Y = X *)
 >> Cases_on ‘Y = X’
 >- (POP_ASSUM (fs o wrap) \\
     Know ‘E1 = E' /\ E2 = E'’
     >- (rw [Abbr ‘E1’, Abbr ‘E2’] \\ (* 2 subgoals, same tactics *)
         MATCH_MP_TAC lemma14b >> rw [Abbr ‘E'’, FV_tpm]) \\
     DISCH_THEN (fs o wrap))
 >> Know ‘!P Q X. STRONG_EQUIV P Q ==> STRONG_EQUIV ([P/X] E') ([Q/X] E')’
 >> cheat
QED

(* fmap_rel_ind *)
Theorem STRONG_EQUIV_ssub_cong :
    !E fm1 fm2. fmap_rel STRONG_EQUIV fm1 fm2 ==> STRONG_EQUIV (fm1 ' E) (fm2 ' E)
Proof
    HO_MATCH_MP_TAC simple_induction >> rw [FINITE_FV]
 (* 9 subgoals *)
 >- fs [fmap_rel_def]
 (* 8 subgoals left *)
 >- fs [fmap_rel_def]
 (* 7 subgoals left *)
 >- fs [fmap_rel_def]
 (* 6 subgoals left *)
 >- (Q.PAT_X_ASSUM ‘!fm1 fm2. P’ (MP_TAC o (Q.SPECL [‘fm1’, ‘fm2’])) >> rw [] \\
     MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX >> rw [])
 (* 5 subgoals left *)
 >- (Q.PAT_X_ASSUM ‘!fm1 fm2. P’ (MP_TAC o (Q.SPECL [‘fm1’, ‘fm2’])) >> rw [] \\
     Q.PAT_X_ASSUM ‘!fm1 fm2. P’ (MP_TAC o (Q.SPECL [‘fm1’, ‘fm2’])) >> rw [] \\
     MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_SUM >> rw [])
 (* 4 subgoals left *)
 >- (Q.PAT_X_ASSUM ‘!fm1 fm2. P’ (MP_TAC o (Q.SPECL [‘fm1’, ‘fm2’])) >> rw [] \\
     Q.PAT_X_ASSUM ‘!fm1 fm2. P’ (MP_TAC o (Q.SPECL [‘fm1’, ‘fm2’])) >> rw [] \\
     MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> rw [])
 (* 3 subgoals left *)
 >- (Q.PAT_X_ASSUM ‘!fm1 fm2. P’ (MP_TAC o (Q.SPECL [‘fm1’, ‘fm2’])) >> rw [] \\
     MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> rw [])
 (* 2 subgoals left *)
 >- (Q.PAT_X_ASSUM ‘!fm1 fm2. P’ (MP_TAC o (Q.SPECL [‘fm1’, ‘fm2’])) >> rw [] \\
     MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> rw [])
 >> qabbrev_tac ‘X = {y} UNION FV E UNION FDOM fm1 UNION FDOM fm2
                     UNION (BIGUNION (IMAGE (\s. FV (fm1 ' s)) (FDOM fm1)))
                     UNION (BIGUNION (IMAGE (\s. FV (fm2 ' s)) (FDOM fm2)))’
 >> ‘FINITE X’ by (rw [Abbr ‘X’] >> rw [FINITE_FV])
 >> NEW_TAC "z" “X :string set”
 >> Q.PAT_X_ASSUM ‘FINITE X’ K_TAC
 >> fs [Abbr ‘X’]
 (* stage work *)
 >> Know ‘rec y E = rec z ([var z/y] E)’
 >- (MATCH_MP_TAC SIMPLE_ALPHA >> art [])
 >> Rewr'
 >> qabbrev_tac ‘P = [var z/y] E’
 >> Know ‘fm1 ' (rec z P) = rec z (fm1 ' P)’
 >- (MATCH_MP_TAC ssub_rec >> rw [] >> METIS_TAC [])
 >> Rewr'
 >> Know ‘fm2 ' (rec z P) = rec z (fm2 ' P)’
 >- (MATCH_MP_TAC ssub_rec >> rw [] >> METIS_TAC [])
 >> Rewr'
 (* applying STRONG_UNFOLDING' *)
 >> Q.ABBREV_TAC ‘E1 = fm1 ' P’
 >> Q.ABBREV_TAC ‘E2 = fm2 ' P’
 >> MATCH_MP_TAC STRONG_EQUIV_TRANS
 >> Q.EXISTS_TAC ‘[rec z E1/z] E1’
 >> CONJ_TAC >- rw [STRONG_UNFOLDING']
 >> MATCH_MP_TAC STRONG_EQUIV_TRANS
 >> Q.EXISTS_TAC ‘[rec z E2/z] E2’
 >> reverse CONJ_TAC >- rw [Once STRONG_EQUIV_SYM_EQ, STRONG_UNFOLDING']
 (* stage work *)
 >> cheat
QED

(******************************************************************************)
(*                                                                            *)
(*        Strong equivalence for potentially open terms (StrongEQ)            *)
(*                                                                            *)
(******************************************************************************)

(* The purpose of ‘extension R’ is to modify the existing relation R such that
   two potentially open CCS terms (with open variables) must satisfy R even when
   these variables were substituted to the same arbitrary term.

   There's no requirements on the ssub ‘fm’: it's FDOM and FRANGE can be anything,
   but if the two terms are still equivalent for all possible fm, then we are
   sure that their open variables must be in the same transiton position, thus
   are equivalent in the extensive sense.
 *)
Definition extension_def :
    extension R = \P Q. !fm. R (fm ' P) (fm ' Q)
End

Overload TC = “extension” (* ^+ *)

Theorem extension_RSUBSET :
    !R. (extension R) RSUBSET R
Proof
    rw [RSUBSET, extension_def]
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘FEMPTY’))
 >> rw [ssub_FEMPTY]
QED

Overload StrongEQ = “extension STRONG_EQUIV”

(* |- !x y. StrongEQ x y ==> STRONG_EQUIV x y *)
Theorem StrongEQ_IMP_STRONG_EQUIV =
    REWRITE_RULE [RSUBSET] (Q.SPEC ‘STRONG_EQUIV’ extension_RSUBSET)

(* Definition 5 of [1, p.98] (see also [2, p.181])

   If any of P and Q is not closed, but all their closed simultaneous
   substitutions are strong bisimular, then so is P and Q.

   NOTE: ‘fm’ is not required to cover all FVs of P and Q, those free vars
         which is not substituted, will be treated as nil (i.e. no transitions).
         Furthermore, if ‘FDOM fm’ is larger than ‘FV P UNION FV Q’, the extra
         keys won't cause any trouble.

   |- !P Q. StrongEQ P Q <=> !fm. STRONG_EQUIV (fm ' P) (fm ' Q)
 *)
Theorem StrongEQ_def =
    SIMP_RULE std_ss [FUN_EQ_THM] (Q.SPEC ‘STRONG_EQUIV’ extension_def)

Theorem StrongEQ_REFL[simp] :
    !E. StrongEQ E E
Proof
    rw [StrongEQ_def]
QED

Theorem StrongEQ_symmetric :
    symmetric StrongEQ
Proof
    rw [symmetric_def, StrongEQ_def]
 >> rw [Once STRONG_EQUIV_SYM_EQ]
QED

(* |- !x y. StrongEQ x y ==> StrongEQ y x *)
Theorem StrongEQ_SYM =
    StrongEQ_symmetric |> REWRITE_RULE [symmetric_def] |> iffLR

Theorem StrongEQ_SYM_EQ :
    !P Q. StrongEQ P Q <=> StrongEQ Q P
Proof
    rpt GEN_TAC >> EQ_TAC >> rw [StrongEQ_SYM]
QED

Theorem StrongEQ_TRANS :
    !E1 E2 E3. StrongEQ E1 E2 /\ StrongEQ E2 E3 ==> StrongEQ E1 E3
Proof
    rw [StrongEQ_def]
 >> MATCH_MP_TAC STRONG_EQUIV_TRANS
 >> Q.EXISTS_TAC ‘fm ' E2’ >> rw []
QED

Theorem StrongEQ_equivalence :
    equivalence StrongEQ
Proof
    rw [equivalence_def, reflexive_def, StrongEQ_symmetric, StrongEQ_REFL,
        transitive_def]
 >> MATCH_MP_TAC StrongEQ_TRANS
 >> Q.EXISTS_TAC ‘y’ >> art []
QED

(* NOTE: the opposite direction doesn't hold *)
Theorem StrongEQ_IMP_SUBST :
    !X P Q. StrongEQ P Q ==> !E. STRONG_EQUIV ([E/X] P) ([E/X] Q)
Proof
    rw [StrongEQ_def]
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘FEMPTY |+ (X,E)’))
 >> rw [single_ssub]
QED

(* Key result: if the same free variables in P and Q were substituted with non-identical
   but strong equivalent terms, the resulting substituted two terms are still equivalent.

   The proof idea is the following: by induction on P, if a free ‘var s’ is reached, then
   Q at the same transition position must be also ‘var s’ (otherwise StrongEQ cannot hold),
   then both ‘var s’ are substituted with E1 and E2 satisfying STRONG_EQUIV E1 E2, and
   thus is strong equivalence. Other induction cases do not involved substitutions at all.
 *)
Theorem StrongEQ_alt :
    !P Q. StrongEQ P Q <=>
          !fm1 fm2. FDOM fm1 = FDOM fm2 /\
                    (!s. s IN FDOM fm1 ==> STRONG_EQUIV (fm1 ' s) (fm2 ' s)) ==>
                    STRONG_EQUIV (fm1 ' P) (fm2 ' Q)
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC >- rw [StrongEQ_def]
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘StrongEQ P Q’ MP_TAC
 >> Q.ID_SPEC_TAC ‘Q’
 >> Q.ID_SPEC_TAC ‘P’
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘FDOM fm1
                  UNION (BIGUNION (IMAGE (\s. FV (fm1 ' s)) (FDOM fm1)))
                  UNION (BIGUNION (IMAGE (\s. FV (fm2 ' s)) (FDOM fm1)))’
 >> rw [] >> rw [FINITE_FV] (* 9 subgoals *)
 (* goal 1 (of 9) *)
 >- (MATCH_MP_TAC STRONG_EQUIV_TRANS \\
     Q.EXISTS_TAC ‘fm2 ' s’ >> rw [] \\
     FULL_SIMP_TAC std_ss [StrongEQ_def] \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘fm2’)) >> rw [])
 (* goal 2 (of 9) *)
 >- (FULL_SIMP_TAC std_ss [StrongEQ_def] \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘fm2’)) >> rw [])
 (* goal 3 (of 9) *)
 >- (FULL_SIMP_TAC std_ss [StrongEQ_def, ssub_thm])
 (* goal 4 (of 9) *)
 >- (FULL_SIMP_TAC std_ss [StrongEQ_def, ssub_thm] \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘fm2’)) >> rw [] \\
     MATCH_MP_TAC STRONG_EQUIV_TRANS \\
     Q.EXISTS_TAC ‘u..fm2 ' E’ >> art [] \\
     MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX \\
     FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 (* goal 5 (of 9) *)
 >- (MATCH_MP_TAC STRONG_EQUIV_TRANS \\
     Q.EXISTS_TAC ‘fm2 ' E1 + fm2 ' E2’ \\
     CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_SUM >> rw []) \\
     FULL_SIMP_TAC std_ss [StrongEQ_def, ssub_thm])
 (* goal 6 (of 9) *)
 >- (MATCH_MP_TAC STRONG_EQUIV_TRANS \\
     Q.EXISTS_TAC ‘fm2 ' E1 || fm2 ' E2’ \\
     CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> rw []) \\
     FULL_SIMP_TAC std_ss [StrongEQ_def, ssub_thm])
 (* goal 7 (of 9) *)
 >- (Q.PAT_X_ASSUM ‘!Q. StrongEQ E Q ==> P’ (MP_TAC o (Q.SPEC ‘E’)) >> rw [] \\
     MATCH_MP_TAC STRONG_EQUIV_TRANS \\
     Q.EXISTS_TAC ‘restr L (fm2 ' E)’ \\
     CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
     FULL_SIMP_TAC std_ss [StrongEQ_def, ssub_thm])
 (* goal 8 (of 9) *)
 >- (Q.PAT_X_ASSUM ‘!Q. StrongEQ E Q ==> P’ (MP_TAC o (Q.SPEC ‘E’)) >> rw [] \\
     MATCH_MP_TAC STRONG_EQUIV_TRANS \\
     Q.EXISTS_TAC ‘relab (fm2 ' E) rf’ \\
     CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art []) \\
     FULL_SIMP_TAC std_ss [StrongEQ_def, ssub_thm])
 (* goal 9 (of 9) *)
 >> Q.PAT_X_ASSUM ‘!Q. StrongEQ E Q ==> P’ (MP_TAC o (Q.SPEC ‘E’)) >> rw []
 >> FULL_SIMP_TAC std_ss [StrongEQ_def, ssub_thm]
 >> MATCH_MP_TAC STRONG_EQUIV_TRANS
 >> Q.EXISTS_TAC ‘fm2 ' (rec y E)’ >> art []
 >> Know ‘fm1 ' (rec y E) = rec y (fm1 ' E)’
 >- (MATCH_MP_TAC ssub_rec >> rw [] >> METIS_TAC [])
 >> Rewr'
 >> Know ‘fm2 ' (rec y E) = rec y (fm2 ' E)’
 >- (MATCH_MP_TAC ssub_rec >> rw [] >> METIS_TAC [])
 >> Rewr'
 >> cheat
QED

(******************************************************************************)
(*                                                                            *)
(*                StrongEQ is preserved by recursive definition               *)
(*                                                                            *)
(******************************************************************************)

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
 >> rw [CCS_Subst] (* 8 subgoals *)
 >| [ (* goal 1 (of 8) *)
      fs [TRANS_REC_EQ, CCS_Subst] (* this adds ‘P <> var X’, very useful *) \\
      cheat,
      (* goal 2 (of 8) *)
      FULL_SIMP_TAC bool_ss [NIL_NO_TRANS],
      (* goal 3 (of 8) *)
      fs [TRANS_PREFIX_EQ, O_DEF] \\
      Q.EXISTS_TAC ‘[rec X Q/X] G’ >> rw [] \\
      Q.EXISTS_TAC ‘[rec X P/X] G’ >> rw [] \\
      Q.EXISTS_TAC ‘G’ >> art [],
      (* goal 4 (of 8): SUM *)
      fs [TRANS_SUM_EQ] >| (* 2 subgoals *)
      [ (* goal 4.1 (of 2) *)
        Q.PAT_X_ASSUM ‘!P Q X. FV P SUBSET {X} /\ FV Q SUBSET {X} /\ StrongEQ P Q /\
                               FV G SUBSET {X} /\
                               [rec X P/X] G --u-> E1 ==> _’
                      (MP_TAC o (Q.SPECL [‘P’, ‘Q’, ‘X’])) >> rw [O_DEF] \\
        Q.EXISTS_TAC ‘E2’ >> rw [] \\
        rename1 ‘STRONG_EQUIV ([rec X Q/X] G2) E2’ \\
        Q.EXISTS_TAC ‘[rec X Q/X] G2’ >> rw [] \\
        Q.EXISTS_TAC ‘[rec X P/X] G2’ >> rw [] \\
        Q.EXISTS_TAC ‘G2’ >> art [],
        (* goal 4.2 (of 2) *)
        Q.PAT_X_ASSUM ‘!P Q X. FV P SUBSET {X} /\ FV Q SUBSET {X} /\ StrongEQ P Q /\
                               FV G' SUBSET {X} /\
                               [rec X P/X] G' --u-> E1 ==> _’
                      (MP_TAC o (Q.SPECL [‘P’, ‘Q’, ‘X’])) >> rw [O_DEF] \\
        Q.EXISTS_TAC ‘E2’ >> rw [] \\
        rename1 ‘STRONG_EQUIV ([rec X Q/X] G2) E2’ \\
        Q.EXISTS_TAC ‘[rec X Q/X] G2’ >> rw [] \\
        Q.EXISTS_TAC ‘[rec X P/X] G2’ >> rw [] \\
        Q.EXISTS_TAC ‘G2’ >> art [] ],
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
          gs [lemma14b] \\
          Q.EXISTS_TAC ‘E1’ >> rw [O_DEF] \\
          Q.EXISTS_TAC ‘E1’ >> rw [STRONG_EQUIV_REFL] \\
          Q.EXISTS_TAC ‘E1’ >> rw [STRONG_EQUIV_REFL] \\
          Know ‘X # E1’
          >- (CCONTR_TAC >> fs [] \\
             ‘X IN FV (rec X G)’ by METIS_TAC [SUBSET_DEF, TRANS_FV] \\
              fs [FV_thm]) >> DISCH_TAC \\
          Q.EXISTS_TAC ‘E1’ >> ASM_SIMP_TAC std_ss [lemma14b] \\
          MATCH_MP_TAC SUBSET_TRANS \\
          Q.EXISTS_TAC ‘FV (rec X G)’ \\
          CONJ_TAC >- (MATCH_MP_TAC TRANS_FV >> Q.EXISTS_TAC ‘u’ >> art []) \\
          rw [FV_thm]) \\
      Know ‘Y # rec X P /\ Y # rec X Q’
      >- (rw [FV_thm] >> PROVE_TAC [FV_SUBSET_lemma]) >> STRIP_TAC \\
      gs [SUB_THM] \\
      cheat ]
QED

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

(*
Theorem StrongEQ_subst_rec_lemma :
    !P Q v. FV P SUBSET {v} /\ FV Q SUBSET {v} /\ StrongEQ P Q ==>
            STRONG_EQUIV (rec v P) (rec v Q)
Proof
    rpt STRIP_TAC
 >> rw [Once PROPERTY_STAR]
 >| [ (* goal 1 (of 2) *)
      fs [TRANS_REC_EQ, CCS_Subst] \\
      Know ‘STRONG_EQUIV ([rec v P/v] P) ([rec v Q/v] Q)’
QED

(* Substitution of free variables to ‘nil’ preserves strong bisimilarity. *)
Theorem STRONG_EQUIV_ssub_lemma :
    !fm E. (!y. y IN FDOM fm ==> fm ' y = nil) ==> STRONG_EQUIV E (fm ' E)
Proof
    Q.X_GEN_TAC ‘fm’
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘FDOM fm’
 >> rw [] (* 7 subgoals *)
 >| [ (* goal 1 (of 7) *)
      rw [FUN_FMAP_DEF, PROPERTY_STAR, NIL_NO_TRANS, VAR_NO_TRANS],
      (* goal 2 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX >> rw [],
      (* goal 3 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_SUM >> rw [],
      (* goal 4 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> rw [],
      (* goal 5 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> rw [],
      (* goal 6 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> rw [],
      (* goal 7 (of 7) *)
      cheat ]
QED

Definition StrongEQ_def :
    StrongEQ P Q = !fm. (!y. y IN FDOM fm ==> closed (fm ' y)) ==>
                        STRONG_EQUIV (fm ' P) (fm ' Q)
End

Theorem StrongEQ_alt_closed :
    !P Q. closed P /\ closed Q ==> (StrongEQ P Q <=> STRONG_EQUIV P Q)
Proof
    rw [StrongEQ_def]
QED

Theorem SUBSET_SING[local] :
    !X x. X SUBSET {x} <=> X = {} \/ X = {x}
Proof
    SET_TAC []
QED

(* TODO *)
Theorem StrongEQ_alt_single :
    !X P Q. FV P SUBSET {X} /\ FV Q SUBSET {X} ==>
           (StrongEQ P Q <=> !E. closed E ==> STRONG_EQUIV ([E/X] P) ([E/X] Q))
Proof
    rpt STRIP_TAC
 >> Cases_on ‘closed P /\ closed Q’
 >- (rw [StrongEQ_alt_closed] \\
     Suff ‘!E. closed E ==> [E/X] P = P /\ [E/X] Q = Q’ >- METIS_TAC [] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC lemma14b >> fs [closed_def])
 >> rw [StrongEQ_def]
 (*
 >> ‘FV P UNION FV Q SUBSET {X}’ by ASM_SET_TAC []
 >> Know ‘FV P UNION FV Q = {X}’
 >- (Suff ‘FV P UNION FV Q <> {}’ >- METIS_TAC [SUBSET_SING_CASES] \\
     CCONTR_TAC >> fs [closed_def])
 >> Rewr'
 *)
 >> EQ_TAC
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!fm. _ ==> STRONG_EQUIV (fm ' P) (fm ' Q)’
       (MP_TAC o (Q.SPEC ‘FEMPTY |+ (X,E)’)) \\
     simp [FDOM_FUPDATE] \\
     rw [FEMPTY_update_apply])
 (* stage work *)
 >> rpt STRIP_TAC





 >> qabbrev_tac ‘E = fm ' X’
 >> qabbrev_tac ‘fm' = FEMPTY |+ (X,E)’
 >> Know ‘fm = fm'’
 >- (rw [Abbr ‘fm'’, GSYM fmap_EQ_THM])
 >> Rewr'
 >> Know ‘fm' ' P = [E/X] P /\ fm' ' Q = [E/X] Q’
 >- (rw [Abbr ‘fm'’, FEMPTY_update_apply])
 >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> rw [Abbr ‘E’]
QED

Theorem StrongEQ_alt_subst' :
    !X P Q. FV P SUBSET {X} /\ FV Q SUBSET {X} ==>
           (StrongEQ P Q <=> !E. closed E ==> StrongEQ ([E/X] P) ([E/X] Q))
Proof
    rpt STRIP_TAC
 >> Know ‘StrongEQ P Q <=> !E. closed E ==> STRONG_EQUIV ([E/X] P) ([E/X] Q)’
 >- (MATCH_MP_TAC StrongEQ_alt_subst >> art [])
 >> Rewr'
 >> Suff ‘!E. closed E ==>
             (STRONG_EQUIV ([E/X] P) ([E/X] Q) <=> StrongEQ ([E/X] P) ([E/X] Q))’
 >- METIS_TAC []
 >> rw [closed_def]
 >> Suff ‘closed ([E/X] P) /\ closed ([E/X] Q)’
 >- rw [StrongEQ_alt_closed]
 >> rw [closed_def, FV_SUB]
 >> ASM_SET_TAC []
QED

Theorem StrongEQ_subst_lemma :
    !E. FV E SUBSET {X} /\ closed P /\ closed Q /\ StrongEQ P Q ==>
        StrongEQ ([P/X] E) ([Q/X] E)
Proof
    HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘{X}’
 >> rw [] (* 6 subgoals *)
 >| [ (* goal 1 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX >> rw [],
      (* goal 2 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_SUM >> rw [],
      (* goal 3 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> rw [],
      (* goal 4 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> rw [],
      (* goal 5 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> rw [],
      (* goal 6 (of 6) *)
      ALL_TAC ]
 (* stage work *)
 >> rename1 ‘Y <> X’
 >>
    cheat
QED

Theorem StrongEQ_preserved_by_rec :
    !X P Q. StrongEQ P Q ==> StrongEQ (rec X P) (rec X Q)
Proof
    rpt STRIP_TAC
 >> Know ‘StrongEQ (rec X P) (rec X Q) <=> STRONG_EQUIV (rec X P) (rec X Q)’
 >- (MATCH_MP_TAC StrongEQ_alt_closed \\
     rw [closed_def, FV_thm] >> ASM_SET_TAC [])
 >> Rewr'
 >> MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_REC >> art []
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
 >> REWRITE_TAC [combinTheory.o_DEF]
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
 *)

val _ = export_theory ();
val _ = html_theory "Future";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.
 [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer (2015).
 *)
