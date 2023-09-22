(*---------------------------------------------------------------------------*
 * solvableScript.sml (or chap8_3): Theory of Solvable Lambda Terms          *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory finite_mapTheory hurdUtils;

open termTheory appFOLDLTheory chap2Theory standardisationTheory;

val _ = new_theory "solvable";

Definition closures_def :
    closures M = {LAMl vs M | vs | ALL_DISTINCT vs /\ set vs = FV M}
End

Definition closed_def :
    closed (M :term) <=> FV M = {}
End

Theorem closures_of_closed[simp] :
    !M. closed M ==> closures M = {M}
Proof
    rw [closures_def, closed_def]
 >> rw [Once EXTENSION]
QED

(* NOTE: ‘ALL_DISTINCT vs’ is required (TODO: optimized this proof) *)
Theorem LIST_TO_SET_SING :
    !vs x. ALL_DISTINCT vs /\ set vs = {x} <=> vs = [x]
Proof
    rpt GEN_TAC >> reverse EQ_TAC >- rw []
 (* necessary case analysis, to use ALL_DISTINCT *)
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

Theorem closures_of_open_sing :
    !M v. FV M = {v} ==> closures M = {LAM v M}
Proof
    rw [closures_def, LIST_TO_SET_SING]
 >> rw [Once EXTENSION]
QED

(* 8.3.1 (ii) [1, p.171] *)
Definition solvable_def :
    solvable (M :term) = ?M'. M' IN closures M /\ ?Ns. M' @* Ns == I
End

(* 8.3.1 (i) [1, p.171] *)
Theorem solvable_of_closed :
    !M. closed M ==> (solvable M <=> ?Ns. M @* Ns == I)
Proof
    rw [solvable_def, closed_def]
QED

Theorem solvable_of_closed' =
    REWRITE_RULE [closed_def] solvable_of_closed

(* 8.3.1 (iii) [1, p.171] *)
Overload unsolvable = “$~ o solvable”

(* 8.3.2 Examples of solvable terms [1, p.171] *)
Theorem solvable_K :
    solvable K
Proof
    rw [solvable_of_closed']
 >> Q.EXISTS_TAC ‘[I; I]’
 >> rw [lameq_K]
QED

(* copied from chap2Script.sml [2] *)
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

Theorem lameq_trans[local] = List.nth(CONJUNCTS lameq_rules, 3)

Theorem solvable_xIO :
    solvable (VAR x @@ I @@ Omega)
Proof
    Q.ABBREV_TAC ‘M = VAR x @@ I @@ Omega’
 >> ‘FV M = {x}’ by rw [Abbr ‘M’]
 >> ‘closures M = {LAM x M}’ by PROVE_TAC [closures_of_open_sing]
 >> rw [solvable_def]
 >> Q.EXISTS_TAC ‘[K]’ >> simp []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [Abbr ‘M’, lameq_K]
 >> KILL_TAC
 >> rw [SUB_THM, lemma14b]
QED

val _ = reveal "Y"; (* from chap2Theory *)

Theorem solvable_Y :
    solvable Y
Proof
    rw [solvable_of_closed']
 >> Q.EXISTS_TAC ‘[K @@ I]’ >> simp []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [YYf, Once YffYf, lameq_K]
QED

(* ‘closure M’ is one element in ‘closures M’, useful when an arbitrary one is needed. *)
Definition closure_def :
    closure M = LAMl (SET_TO_LIST (FV M)) M
End

Theorem closure_in_closures :
    !M. closure M IN closures M
Proof
    rw [closure_def, closures_def]
 >> Q.EXISTS_TAC ‘SET_TO_LIST (FV M)’
 >> rw [SET_TO_LIST_INV]
QED

Theorem closure_stable[simp] :
    !M. closed M ==> closure M = M
Proof
    rw [closure_def, closed_def]
QED

Theorem closure_open_sing :
    !M v. FV M = {v} ==> closure M = LAM v M
Proof
    rw [closure_def]
QED

(* TODO: move to chap2Theory *)
Theorem I_alt :
    !s. I = LAM s (VAR s)
Proof
    Q.X_GEN_TAC ‘x’
 >> REWRITE_TAC [I_def, Once EQ_SYM_EQ]
 >> Cases_on ‘x = "x"’ >- rw []
 >> Q.ABBREV_TAC ‘u :term = VAR x’
 >> Q.ABBREV_TAC ‘y = "x"’
 >> ‘y NOTIN FV u’ by rw [Abbr ‘u’]
 >> Know ‘LAM x u = LAM y ([VAR y/x] u)’
 >- (MATCH_MP_TAC SIMPLE_ALPHA >> art [])
 >> Rewr'
 >> Suff ‘[VAR y/x] u = VAR y’ >- rw []
 >> rw [Abbr ‘u’]
QED

Theorem closure_of_var[simp] :
    closure (VAR x) = I
Proof
    Know ‘closure (VAR x) = LAM x (VAR x)’
 >- (MATCH_MP_TAC closure_open_sing >> rw [])
 >> Rewr'
 >> REWRITE_TAC [Q.SPEC ‘x’ I_alt]
QED

Theorem closures_imp_closed :
    !M N. N IN closures M ==> closed N
Proof
    rw [closures_def, closed_def]
 >> simp [FV_LAMl]
QED

(* |- !M N. N IN closures M ==> FV N = {} *)
Theorem FV_closures = REWRITE_RULE [closed_def] closures_imp_closed

Theorem FV_closure[simp] :
    FV (closure M) = {}
Proof
    MATCH_MP_TAC FV_closures
 >> Q.EXISTS_TAC ‘M’
 >> rw [closure_in_closures]
QED

Theorem SUB_I[simp] :
    [N/v] I = I
Proof
    rw [lemma14b]
QED

Theorem ssub_I[simp] :
    ssub fm I = I
Proof
    rw [ssub_value]
QED

(* TODO: move to finite_mapTheory *)
Theorem FUN_FMAP_INSERT :
    !f e s. FINITE s /\ e NOTIN s ==>
            FUN_FMAP f (e INSERT s) = FUN_FMAP f s |+ (e,f e)
Proof
    rw [fmap_EXT]
 >- rw [FUN_FMAP_DEF]
 >> ‘x IN e INSERT s’ by ASM_SET_TAC []
 >> ‘x <> e’ by METIS_TAC []
 >> rw [FAPPLY_FUPDATE_THM, FUN_FMAP_DEF]
QED

(* TODO: move to termTheory *)
Theorem FV_ssub :
    !fm N. (!y. y IN FDOM fm ==> FV (fm ' y) = {}) ==>
           FV (fm ' N) = FV N DIFF FDOM fm
Proof
    rpt STRIP_TAC
 >> Q.ID_SPEC_TAC ‘N’
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘FDOM fm’
 >> rw [SUB_VAR, SUB_THM, ssub_thm]
 >> SET_TAC []
QED

(* cf. lameq_sub_cong *)
Theorem lameq_ssub_cong :
    M == N ==> fm ' M == fm ' N
Proof
    cheat
QED

Theorem ssub_appstar :
    fm ' (M @* Ns) = (fm ' M) @* MAP (ssub fm) Ns
Proof
    Q.ID_SPEC_TAC ‘Ns’
 >> HO_MATCH_MP_TAC SNOC_INDUCT
 >> rw [SNOC_APPEND, SYM appstar_SNOC]
QED

(* alternative definition of solvable terms involving all closed terms *)
Theorem solvable_alt_closed :
    !M. closed M ==> (solvable M <=> ?Ns. M @* Ns == I /\ EVERY closed Ns)
Proof
    rw [solvable_of_closed, closed_def]
 >> reverse EQ_TAC
 >- (STRIP_TAC >> Q.EXISTS_TAC ‘Ns’ >> rw [])
 (* stage work *)
 >> STRIP_TAC
 (* get all free variables in Ns *)
 >> Q.ABBREV_TAC ‘vs = BIGUNION (IMAGE FV (set Ns))’
 >> ‘FINITE vs’
      by (Q.UNABBREV_TAC ‘vs’ >> MATCH_MP_TAC FINITE_BIGUNION \\
          rw [IMAGE_FINITE] >> rw [FINITE_FV])
 >> ‘!N. MEM N Ns ==> FV N SUBSET vs’
      by (rw [Abbr ‘vs’, SUBSET_DEF, IN_BIGUNION_IMAGE] \\
          Q.EXISTS_TAC ‘N’ >> art [])
 (* construct the variable substitution *)
 >> Q.ABBREV_TAC ‘fm = FUN_FMAP (\x. I) vs’
 >> Q.EXISTS_TAC ‘MAP (ssub fm) Ns’
 >> reverse CONJ_TAC (* EVERY closed (MAP ($' fm) Ns) *)
 >- (rw [EVERY_MAP, EVERY_EL, closed_def] \\
     Q.ABBREV_TAC ‘N = EL n Ns’ \\
    ‘MEM N Ns’ by PROVE_TAC [MEM_EL] \\
    ‘{} = FV N DIFF vs’ by ASM_SET_TAC [] >> POP_ORW \\
    ‘vs = FDOM fm’ by rw [Abbr ‘fm’] >> POP_ORW \\
     MATCH_MP_TAC FV_ssub \\
     rw [Abbr ‘fm’, FUN_FMAP_DEF, FAPPLY_FUPDATE_THM])
 (* stage work *)
 >> MATCH_MP_TAC lameq_trans
 >> Q.EXISTS_TAC ‘fm ' (M @* Ns)’
 >> reverse CONJ_TAC >- PROVE_TAC [lameq_ssub_cong, ssub_I]
 >> rw [ssub_appstar]
 >> Suff ‘fm ' M = M’ >- rw []
 >> MATCH_MP_TAC ssub_value >> art []
QED

val _ = export_theory ();
val _ = html_theory "solvable";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
   [2] Hankin, C.: Lambda Calculi: A Guide for Computer Scientists.
       Clarendon Press, Oxford (1994).
 *)
