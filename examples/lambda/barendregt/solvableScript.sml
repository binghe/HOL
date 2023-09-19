(*---------------------------------------------------------------------------*
 * solvableScript.sml: theory of solvable lambda terms                       *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open pred_setTheory hurdUtils;

open termTheory appFOLDLTheory chap2Theory standardisationTheory;

val _ = new_theory "solvable";

(* NOTE: when proving an open term M is solvable, the choice of ‘vs’ in
  ‘LAMl vs M’ is important and determines the order of Ns, thus the
   following definition (closure) doesn't work:

   closure M = LAMl (SET_TO_LIST (FV M)) M
 *)
Definition closure_of_def :
    closure_of M = {LAMl vs M | vs | ALL_DISTINCT vs /\ set vs = FV M}
End

Theorem closure_of_closed[simp] :
    !M. FV M = {} ==> closure_of M = {M}
Proof
    rw [closure_of_def]
 >> rw [Once EXTENSION]
QED

(* NOTE: ‘ALL_DISTINCT vs’ is required (TODO: optimized this proof) *)
Theorem LIST_TO_SET_SING :
    !vs x. ALL_DISTINCT vs /\ set vs = {x} <=> vs = [x]
Proof
    rpt GEN_TAC >> reverse EQ_TAC >- rw []
 >> Cases_on ‘vs’ >> rw []
 >- (fs [Once EXTENSION] >> METIS_TAC [])
 >> Know ‘h = x’
 >- (fs [Once EXTENSION] >> METIS_TAC [])
 >> DISCH_THEN (fs o wrap)
 >> Cases_on ‘set t = {}’ >- fs []
 >> ‘?y. y IN set t’ by METIS_TAC [MEMBER_NOT_EMPTY]
 >> Cases_on ‘x = y’ >- PROVE_TAC []
 >> fs [Once EXTENSION]
 >> METIS_TAC []
QED

Theorem closure_of_sing :
    !M v. FV M = {v} ==> closure_of M = {LAM v M}
Proof
    rw [closure_of_def, LIST_TO_SET_SING]
 >> rw [Once EXTENSION]
QED

(* 8.3.1 (ii) [1, p.171] *)
Definition solvable_def :
    solvable (M :term) = ?M'. M' IN closure_of M /\ ?Ns. M' @* Ns == I
End

(* 8.3.1 (i) [1, p.171] *)
Theorem solvable_alt_closed :
    !M. FV M = {} ==> (solvable M <=> ?Ns. M @* Ns == I)
Proof
    rw [solvable_def]
QED

(* 8.3.1 (iii) [1, p.171] *)
Overload unsolvable = “$~ o solvable”

(* 8.3.2 Examples of solvable terms [1, p.171] *)
Theorem solvable_K :
    solvable K
Proof
    rw [solvable_alt_closed]
 >> Q.EXISTS_TAC ‘[I; I]’
 >> rw [lameq_K]
QED

(* copied from chap2Script.sml *)
fun betafy ss =
    simpLib.add_relsimp {refl = GEN_ALL lameq_refl,
                         trans = List.nth(CONJUNCTS lameq_rules, 3),
                         weakenings = [lameq_weaken_cong],
                         subsets = [],
                         rewrs = [hd (CONJUNCTS lameq_rules)]} ss ++
    simpLib.SSFRAG {rewrs = [],
                    ac = [],  convs = [],
                    congs = [lameq_app_cong,
                             SPEC_ALL (last (CONJUNCTS lameq_rules)),
                             lameq_sub_cong],
                    dprocs = [], filter = NONE, name = NONE};

Theorem solvable_xIO :
    solvable (VAR x @@ I @@ Omega)
Proof
    Q.ABBREV_TAC ‘M = VAR x @@ I @@ Omega’
 >> ‘FV M = {x}’ by rw [Abbr ‘M’]
 >> ‘closure_of M = {LAM x M}’ by PROVE_TAC [closure_of_sing]
 >> rw [solvable_def]
 >> Q.EXISTS_TAC ‘[K]’ >> simp []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [Abbr ‘M’, lameq_K]
 >> KILL_TAC
 >> rw [SUB_THM, FV_I, lemma14b]
QED

val _ = reveal "Y"; (* chap2Theory *)

Theorem solvable_Y :
    solvable Y
Proof
    rw [solvable_alt_closed, FV_Y]
 >> Q.EXISTS_TAC ‘[K @@ I]’ >> simp []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [YYf, Once YffYf, lameq_K]
QED

val _ = export_theory ();
val _ = html_theory "solvable";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
 *)
