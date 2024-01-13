(* ========================================================================== *)
(* FILE          : FutureScript.sml                                           *)
(* DESCRIPTION   : "Future" theory of CCS (for potentially open terms)        *)
(*                                                                            *)
(* COPYRIGHTS    : 2023-2024 Australian National University (Chun Tian)       *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory bisimulationTheory listTheory rich_listTheory
     finite_mapTheory;

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
open MultivariateTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val _ = new_theory "Future";

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

Theorem StrongEQ_alt_closed :
    !P Q. closed P /\ closed Q ==> (StrongEQ P Q <=> STRONG_EQUIV P Q)
Proof
    rw [StrongEQ_def, ssub_value']
QED

Theorem StrongEQ_REFL[simp] :
    !E. StrongEQ E E
Proof
    rw [StrongEQ_def]
QED

Theorem StrongEQ_reflexive :
    reflexive StrongEQ
Proof
    rw [reflexive_def]
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

Theorem StrongEQ_transitive :
    transitive StrongEQ
Proof
    rw [transitive_def]
 >> MATCH_MP_TAC StrongEQ_TRANS
 >> Q.EXISTS_TAC ‘y’ >> art []
QED

Theorem StrongEQ_equivalence :
    equivalence StrongEQ
Proof
    rw [equivalence_def,
        StrongEQ_reflexive, StrongEQ_symmetric, StrongEQ_transitive]
QED

(* NOTE: the opposite direction doesn't hold, unless X is the only FV *)
Theorem StrongEQ_IMP_SUBST :
    !X P Q. StrongEQ P Q ==> !E. STRONG_EQUIV ([E/X] P) ([E/X] Q)
Proof
    rw [StrongEQ_def]
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘FEMPTY |+ (X,E)’))
 >> rw [single_ssub]
QED

Theorem SUBSET_SING[local] :
    !X Y. Y SUBSET {X} <=> Y = {} \/ Y = {X}
Proof
    SET_TAC []
QED

Theorem StrongEQ_EQ_SUBST_lemma :
    !P X E fm. FV P SUBSET {X} /\ E = fm ' (var X) ==> fm ' P = [E/X] P
Proof
    RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [SUBSET_SING] >- rw [ssub_value, lemma14b]
 >> Q.ID_SPEC_TAC ‘fm’
 >> HO_MATCH_MP_TAC fmap_INDUCT >> rw []
 >- (rename1 ‘Y NOTIN FDOM fm’ \\
    ‘Y <> X’ by PROVE_TAC [] \\
     cheat)
 >> cheat
QED

Theorem StrongEQ_EQ_SUBST :
    !X P Q. FV P SUBSET {X} /\ FV Q SUBSET {X} ==>
           (StrongEQ P Q <=> !E. STRONG_EQUIV ([E/X] P) ([E/X] Q))
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- rw [StrongEQ_IMP_SUBST]
 >> rw [StrongEQ_def]
 >> qabbrev_tac ‘E = fm ' (var X)’
 >> Know ‘fm ' P = [E/X] P’
 >- (MATCH_MP_TAC StrongEQ_EQ_SUBST_lemma >> rw [Abbr ‘E’])
 >> Know ‘fm ' Q = [E/X] Q’
 >- (MATCH_MP_TAC StrongEQ_EQ_SUBST_lemma >> rw [Abbr ‘E’])
 >> rw []
QED

(* An easy corollary of STRONG_UNIQUE_SOLUTION_EXTENDED

   cf. Proposition 4.12 of [1, p.99] or Theorem 4.2 of [2, p.182]
 *)
Theorem STRONG_EQUIV_PRESD_BY_REC :
    !P Q X. weakly_guarded [X] [P; Q] ==>
            StrongEQ P Q ==> STRONG_EQUIV (rec X P) (rec X Q)
Proof
    rw [weakly_guarded_def, CCS_Subst]
 >> ‘!E. STRONG_EQUIV ([E/X] P) ([E/X] Q)’
       by PROVE_TAC [StrongEQ_IMP_SUBST]
 >> MATCH_MP_TAC STRONG_UNIQUE_SOLUTION_EXTENDED
 >> qexistsl_tac [‘\t. [t/X] P’, ‘\t. [t/X] Q’] >> simp []
 >> rw [STRONG_UNFOLDING']
QED

Theorem TRANS_tpm :
    !pi E u E'. TRANS E u E' ==> TRANS (tpm pi E) u (tpm pi E')
Proof
    Q.X_GEN_TAC ‘pi’
 >> HO_MATCH_MP_TAC TRANS_IND >> rw [tpm_thm, CCS_Subst] (* 10 subgoals *)
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
 >> ‘var (lswapstr pi X) = tpm pi (var X)’ by rw [tpm_thm]
 >> POP_ORW
 >> CCONTR_TAC
 >> fs [tpm_eqr]
QED

Theorem TRANS_tpm_eq :
    !pi E u E'. TRANS E u E' <=> TRANS (tpm pi E) u (tpm pi E')
Proof
    rpt GEN_TAC
 >> EQ_TAC >- rw [TRANS_tpm]
 >> DISCH_TAC
 >> ‘E  = tpm (REVERSE pi) (tpm pi E )’ by rw [] >> POP_ORW
 >> ‘E' = tpm (REVERSE pi) (tpm pi E')’ by rw [] >> POP_ORW
 >> MATCH_MP_TAC TRANS_tpm >> art []
QED

val _ = export_theory ();
val _ = html_theory "Future";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.
 [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer (2015).
 *)
