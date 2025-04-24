(* ========================================================================== *)
(* FILE          : OpenTermScript.sml                                         *)
(* DESCRIPTION   : The theory of CCS for possibly open terms                  *)
(*                                                                            *)
(* COPYRIGHTS    : 2023-2024 Australian National University (Chun Tian)       *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory bisimulationTheory listTheory rich_listTheory
     finite_mapTheory;

(* lambda theories *)
open binderLib;

(* local theories *)
open CCSLib CCSTheory CCSSyntax CCSConv StrongEQTheory StrongEQLib
     StrongLawsTheory WeakEQTheory WeakEQLib WeakLawsTheory ObsCongrTheory
     ObsCongrLib ObsCongrLawsTheory CongruenceTheory CoarsestCongrTheory
     TraceTheory ExpansionTheory ContractionTheory BisimulationUptoTheory
     UniqueSolutionsTheory MultivariateTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val _ = new_theory "OpenTerm";

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

(* ‘extension R’ is contained in the original relation *)
Theorem extension_RSUBSET :
    !R. (extension R) RSUBSET R
Proof
    rw [RSUBSET, extension_def]
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘FEMPTY’))
 >> rw [ssub_FEMPTY]
QED

Theorem extension_equivalence :
    !R. equivalence R ==> equivalence (extension R)
Proof
    rw [equivalence_def, extension_def]
 >- fs [reflexive_def]
 >- fs [symmetric_def]
 >> fs [transitive_def]
 >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘fm ' P'’ >> art []
QED

Overload StrongEQ = “extension STRONG_EQUIV”

(* Definition 5 of [1, p.98] (see also [2, p.181])

   If any of P and Q is not closed, but all their closed simultaneous
   substitutions are strong bisimular, then so is P and Q.

   NOTE: ‘fm’ is not required to cover all FVs of P and Q. The free vars who
         is not substituted, will be treated as nil having no transitions.
         Furthermore, if ‘FDOM fm’ is larger than ‘FV P UNION FV Q’, the extra
         keys won't cause any further changes to P and Q.

   |- !P Q. StrongEQ P Q <=> !fm. STRONG_EQUIV (fm ' P) (fm ' Q)
 *)
Theorem StrongEQ_def =
    SIMP_RULE std_ss [FUN_EQ_THM] (Q.SPEC ‘STRONG_EQUIV’ extension_def)

(* |- !x y. StrongEQ x y ==> STRONG_EQUIV x y *)
Theorem StrongEQ_IMP_STRONG_EQUIV =
    extension_RSUBSET |> Q.SPEC ‘STRONG_EQUIV’ |> REWRITE_RULE [RSUBSET]

Theorem StrongEQ_alt_closed :
    !P Q. closed P /\ closed Q ==> (StrongEQ P Q <=> STRONG_EQUIV P Q)
Proof
    rw [StrongEQ_def, ssub_value']
QED

(* NOTE: the opposite direction doesn't hold, unless X is the only FV *)
Theorem StrongEQ_IMP_STRONG_EQUIV_SUB :
    !X P Q. StrongEQ P Q ==> !E. STRONG_EQUIV ([E/X] P) ([E/X] Q)
Proof
    rw [StrongEQ_def]
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘FEMPTY |+ (X,E)’))
 >> rw [single_ssub]
QED

(* An easy corollary of STRONG_UNIQUE_SOLUTION_EXT

   cf. Proposition 4.12 of [1, p.99] or Theorem 4.2 of [2, p.182]
 *)
Theorem STRONG_EQUIV_PRESD_BY_REC :
    !P Q X. weakly_guarded {X} [P; Q] /\ StrongEQ P Q ==>
            STRONG_EQUIV (rec X P) (rec X Q)
Proof
    rw [weakly_guarded_def, CCS_Subst]
 >> ‘!E. STRONG_EQUIV ([E/X] P) ([E/X] Q)’
       by PROVE_TAC [StrongEQ_IMP_STRONG_EQUIV_SUB]
 >> MATCH_MP_TAC STRONG_UNIQUE_SOLUTION_EXT
 >> qexistsl_tac [‘\t. [t/X] P’, ‘\t. [t/X] Q’] >> simp []
 >> rw [STRONG_UNFOLDING']
QED

(* special case when P, Q contains free variables up to X, a classic condition *)
Theorem StrongEQ_alt_SUB :
    !P Q X. FV P SUBSET {X} /\ FV Q SUBSET {X} ==>
           (StrongEQ P Q <=> !E. STRONG_EQUIV ([E/X] P) ([E/X] Q))
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [StrongEQ_IMP_STRONG_EQUIV_SUB]
 >> rw [StrongEQ_def]
 (* preparing for ssub_reduce_thm *)
 >> ‘FV P = {} \/ FV P = {X}’ by ASM_SET_TAC []
 >- (fs [ssub_value, lemma14b] \\
    ‘FV Q = {} \/ FV Q = {X}’ by ASM_SET_TAC []
     >- (fs [ssub_value, lemma14b]) \\
     Cases_on ‘DISJOINT (FV Q) (FDOM fm)’
     >- (rw [ssub_14b] \\
         Q.PAT_X_ASSUM ‘!E. _’ (MP_TAC o (Q.SPEC ‘var X’)) \\
         rw [lemma14a]) \\
     gs [DISJOINT_ALT] \\
     Know ‘fm ' Q = [fm ' X/X] Q’
     >- (MATCH_MP_TAC ssub_reduce_thm >> ASM_SET_TAC []) >> Rewr' \\
     qabbrev_tac ‘E = fm ' X’ >> rw [])
 >> ‘FV Q = {} \/ FV Q = {X}’ by ASM_SET_TAC []
 >- (fs [ssub_value, lemma14b] \\
     Cases_on ‘DISJOINT (FV P) (FDOM fm)’
     >- (rw [ssub_14b] \\
         Q.PAT_X_ASSUM ‘!E. _’ (MP_TAC o (Q.SPEC ‘var X’)) \\
         rw [lemma14a]) \\
     gs [DISJOINT_ALT] \\
     Know ‘fm ' P = [fm ' X/X] P’
     >- (MATCH_MP_TAC ssub_reduce_thm >> ASM_SET_TAC []) >> Rewr' \\
     qabbrev_tac ‘E = fm ' X’ >> rw [])
 (* stage work *)
 >> Cases_on ‘DISJOINT (FV P) (FDOM fm)’
 >- (rw [ssub_14b] \\
     Cases_on ‘DISJOINT (FV Q) (FDOM fm)’
     >- (rw [ssub_14b] \\
         Q.PAT_X_ASSUM ‘!E. _’ (MP_TAC o (Q.SPEC ‘var X’)) \\
         rw [lemma14a]) \\
     gs [DISJOINT_ALT])
 >> gs [DISJOINT_ALT]
 >> Know ‘fm ' P = [fm ' X/X] P’
 >- (MATCH_MP_TAC ssub_reduce_thm >> ASM_SET_TAC []) >> Rewr'
 >> Know ‘fm ' Q = [fm ' X/X] Q’
 >- (MATCH_MP_TAC ssub_reduce_thm >> ASM_SET_TAC []) >> Rewr'
 >> rw []
QED

Theorem StrongEQ_equivalence :
    equivalence StrongEQ
Proof
    MATCH_MP_TAC extension_equivalence
 >> REWRITE_TAC [STRONG_EQUIV_equivalence]
QED

(* To actually use [StrongEQ_equivalence]: *)
val theorems =
    REWRITE_RULE [equivalence_def, reflexive_def, symmetric_def, transitive_def]
                 StrongEQ_equivalence;

Theorem StrongEQ_REFL   = cj 1 theorems
Theorem StrongEQ_SYM_EQ = cj 2 theorems
Theorem StrongEQ_TRANS  = cj 3 theorems
Theorem StrongEQ_SYM    = iffLR StrongEQ_SYM_EQ

(* cf. "Open Bisimilarity" [3, p.281] *)
Theorem StrongEQ_alt_closed_substitutions :
    !P Q. StrongEQ P Q <=>
          !fm. FDOM fm = FV P UNION FV Q /\
               (!s. s IN FDOM fm ==> closed (fm ' s))
           ==> STRONG_EQUIV (fm ' P) (fm ' Q)
Proof
    rpt GEN_TAC
 >> EQ_TAC >- rw [StrongEQ_def]
 (* stage work *)
 >> rpt STRIP_TAC
 >> cheat
QED

(******************************************************************************)
(*                                                                            *)
(*         Multi-hole (or no-hole) contexts with recursion support            *)
(*                                                                            *)
(******************************************************************************)

(* NOTE: Unlike in the case of lambda calculus, one-hole contexts are not very
         useful, because the treatments of the two holes for ‘sum’ and ‘par’ are
         completely symmetry (in lambda calculus, on the other hand, the type of
        ‘t1’ and ‘t2’ in ‘APP t1 t2’ are different, leading to sometimes very
         different proofs.)  There's no proof cases in which one-hole contexts
         must be used to finish the proof.             -- Chun Tian, 20 gen 2024
 *)
Inductive ctxt :
    (                   ctxt (\t. t)) /\                 (* ctxt1 *)
    (!s.                ctxt (\t. var s)) /\             (* ctxt2 *)
    (!a e.   ctxt e ==> ctxt (\t. prefix a (e t))) /\    (* ctxt3 *)
    (!e1 e2. ctxt e1 /\ ctxt e2
                    ==> ctxt (\t. sum (e1 t) (e2 t))) /\ (* ctxt4 *)
    (!e1 e2. ctxt e1 /\ ctxt e2
                    ==> ctxt (\t. par (e1 t) (e2 t))) /\ (* ctxt5 *)
    (!L e.   ctxt e ==> ctxt (\t. restr L (e t))) /\     (* ctxt6 *)
    (!e rf.  ctxt e ==> ctxt (\t. relab (e t) rf)) /\    (* ctxt7 *)
    (!v e.   ctxt e ==> ctxt (\t. rec v (e t)))          (* ctxt8 *)
End

val [ctxt1, ctxt2, ctxt3, ctxt4, ctxt5, ctxt6, ctxt7, ctxt8] =
    map save_thm
        (combine (["ctxt1", "ctxt2", "ctxt3", "ctxt4", "ctxt5",
                   "ctxt6", "ctxt7", "ctxt8"],
                  CONJUNCTS ctxt_rules));

(* |- !a. ctxt (\t. a..t) *)
Theorem ctxt3a =
        ctxt3 |> Q.SPECL [‘a’, ‘\t. t’]
              |> REWRITE_RULE [ctxt1] |> BETA_RULE |> GEN_ALL

Theorem constant_contexts_exist :
    !(t :'a CCS). ctxt (\x. t)
Proof
    HO_MATCH_MP_TAC simple_induction
 >> SRW_TAC [][ctxt_rules]
QED

val _ = export_theory ();
val _ = html_theory "OpenTerm";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.
 [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer (2015).
 [3] S. Schafer and G. Smolka, “Tower Induction and Up-to Techniques for CCS with
     Fixed Points,” in LNCS 10226 - Relational and Algebraic Methods in Computer
     Science (RAMiCS 2017), P. Höfner, D. Pous, and G. Struth, Eds. Cham: Springer
     International Publishing, 2017.
 *)
