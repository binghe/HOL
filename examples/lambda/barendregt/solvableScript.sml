(*---------------------------------------------------------------------------*
 * solvableScript.sml (or chap8_3): Theory of Solvable Lambda Terms          *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

(* core theories *)
open pred_setTheory listTheory sortingTheory finite_mapTheory hurdUtils;

(* lambda theories *)
open termTheory appFOLDLTheory chap2Theory standardisationTheory;

val _ = new_theory "solvable";

(*---------------------------------------------------------------------------*
 * closed terms and closures of (open or closed) terms
 *---------------------------------------------------------------------------*)

(* A term is "closed" if it's FV is empty (otherwise the term is open).

   NOTE: the set of all closed terms forms $\Lambda_0$ found in textbooks.
 *)
Definition closed_def :
    closed (M :term) <=> FV M = {}
End

(* By prefixing a list of abstractions of FVs, any term can be "closed". The
   set ‘closures M’ represent such closures with different order of FVs.
 *)
Definition closures_def :
    closures M = {LAMl vs M | vs | ALL_DISTINCT vs /\ set vs = FV M}
End

Theorem closures_not_empty :
    !M. closures M <> {}
Proof
    Q.X_GEN_TAC ‘M’
 >> rw [GSYM MEMBER_NOT_EMPTY]
 >> Q.EXISTS_TAC ‘LAMl (SET_TO_LIST (FV M)) M’
 >> rw [closures_def]
 >> Q.EXISTS_TAC ‘SET_TO_LIST (FV M)’
 >> rw [SET_TO_LIST_INV]
QED

Theorem closures_of_closed[simp] :
    !M. closed M ==> closures M = {M}
Proof
    rw [closures_def, closed_def]
 >> rw [Once EXTENSION]
QED

(* NOTE: ‘ALL_DISTINCT vs’ is required (FIXME: optimized this proof) *)
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

(* ‘closure M’ is just one arbitrary element in ‘closures M’. *)
Overload closure = “\M. CHOICE (closures M)”

Theorem closure_in_closures :
    !M. closure M IN closures M
Proof
    rw [CHOICE_DEF, closures_not_empty]
QED

Theorem closure_idem[simp] :
    !M. closed M ==> closure M = M
Proof
    rw [closures_of_closed]
QED

Theorem closure_open_sing :
    !M v. FV M = {v} ==> closure M = LAM v M
Proof
    rpt STRIP_TAC
 >> ‘closures M = {LAM v M}’ by PROVE_TAC [closures_of_open_sing]
 >> rw []
QED

(*---------------------------------------------------------------------------*
 * solvable terms and some equivalent definitions
 *---------------------------------------------------------------------------*)

(* 8.3.1 (ii) [1, p.171] *)
Definition solvable_def :
    solvable (M :term) = ?M' Ns. M' IN closures M /\ M' @* Ns == I
End

(* 8.3.1 (i) [1, p.171] *)
Theorem solvable_of_closed :
    !M. closed M ==> (solvable M <=> ?Ns. M @* Ns == I)
Proof
    rw [solvable_def, closed_def]
QED

(* |- !M. FV M = {} ==> (solvable M <=> ?Ns. M @* Ns == I) *)
Theorem solvable_of_closed'[local] =
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

Theorem lameq_symm[local] = List.nth(CONJUNCTS lameq_rules, 2)
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

(* FIXME: move to chap2Theory *)
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

(* not used
Theorem SUB_I[simp] :
    [N/v] I = I
Proof
    rw [lemma14b]
QED
 *)

Theorem ssub_I :
    ssub fm I = I
Proof
    rw [ssub_value]
QED

(* FIXME: move to finite_mapTheory *)
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

(* FIXME: move to termTheory *)
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

Theorem ssub_LAM = List.nth(CONJUNCTS ssub_thm, 2)

(* FIXME: can ‘(!y. y IN FDOM fm ==> FV (fm ' y) = {})’ be removed? *)
Theorem ssub_update_apply :
    !fm. s NOTIN FDOM fm /\ (!y. y IN FDOM fm ==> FV (fm ' y) = {}) ==>
         (fm |+ (s,M)) ' N = [M/s] (fm ' (N :term))
Proof
    rpt STRIP_TAC
 >> Q.ID_SPEC_TAC ‘N’
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘s INSERT (FDOM fm UNION FV M)’
 >> rw [SUB_VAR, SUB_THM, ssub_thm, FAPPLY_FUPDATE_THM]
 >> TRY (METIS_TAC [])
 >- (MATCH_MP_TAC (GSYM lemma14b) \\
     METIS_TAC [NOT_IN_EMPTY])
 >> Suff ‘(fm |+ (s,M)) ' (LAM y N) = LAM y ((fm |+ (s,M)) ' N)’ >- rw []
 >> MATCH_MP_TAC ssub_LAM >> rw [FAPPLY_FUPDATE_THM]
QED

(* FIXME: can ‘(!y. y IN FDOM fm ==> FV (fm ' y) = {})’ be removed? *)
Theorem lameq_ssub_cong :
    !fm. (!y. y IN FDOM fm ==> FV (fm ' y) = {}) /\
          M == N ==> fm ' M == fm ' N
Proof
    HO_MATCH_MP_TAC fmap_INDUCT >> rw [FAPPLY_FUPDATE_THM]
 >> Know ‘!y. y IN FDOM fm ==> FV (fm ' y) = {}’
 >- (Q.X_GEN_TAC ‘z’ >> DISCH_TAC \\
    ‘z <> x’ by PROVE_TAC [] \\
     Q.PAT_X_ASSUM ‘!y. y = x \/ y IN FDOM fm ==> P’ (MP_TAC o (Q.SPEC ‘z’)) \\
     RW_TAC std_ss [])
 >> DISCH_TAC
 >> ‘fm ' M == fm ' N’ by PROVE_TAC []
 >> Know ‘(fm |+ (x,y)) ' M = [y/x] (fm ' M)’
 >- (MATCH_MP_TAC ssub_update_apply >> art [])
 >> Rewr'
 >> Know ‘(fm |+ (x,y)) ' N = [y/x] (fm ' N)’
 >- (MATCH_MP_TAC ssub_update_apply >> art [])
 >> Rewr'
 >> ASM_SIMP_TAC (betafy (srw_ss())) []
QED

(* FIXME: move to appFOLDLTheory *)
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
 (* collect all free variables in Ns into vs *)
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
 >> reverse CONJ_TAC
 >- (ONCE_REWRITE_TAC [SYM ssub_I] \\
     MATCH_MP_TAC lameq_ssub_cong \\
     rw [Abbr ‘fm’, FUN_FMAP_DEF, FAPPLY_FUPDATE_THM])
 >> rw [ssub_appstar]
 >> Suff ‘fm ' M = M’ >- rw []
 >> MATCH_MP_TAC ssub_value >> art []
QED

(* cf. solvable_def, adding ‘EVERY closed Ns’ in RHS *)
Theorem solvable_alt :
    !M. solvable M <=> ?M' Ns. M' IN closures M /\ M' @* Ns == I /\ EVERY closed Ns
Proof
    Q.X_GEN_TAC ‘M’
 >> reverse EQ_TAC
 >- (rw [solvable_def] \\
     qexistsl_tac [‘M'’, ‘Ns’] >> art [])
 >> rw [solvable_def]
 >> Q.EXISTS_TAC ‘M'’ >> art []
 >> ‘closed M'’ by PROVE_TAC [closures_imp_closed]
 >> Suff ‘solvable M'’ >- rw [solvable_alt_closed]
 >> rw [solvable_of_closed]
 >> Q.EXISTS_TAC ‘Ns’ >> art []
QED

(* cf. solvable_def, with the existential quantifier "upgraded" to universal. *)
Theorem solvable_alt_all_closures :
    !M. solvable M <=> !M'. M' IN closures M ==> ?Ns. M' @* Ns == I /\ EVERY closed Ns
Proof
    Q.X_GEN_TAC ‘M’
 >> reverse EQ_TAC
 >- (rw [solvable_def] >> Q.EXISTS_TAC ‘closure M’ \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘closure M’)) >> rw [closure_in_closures] \\
     Q.EXISTS_TAC ‘Ns’ >> art [])
 (* stage work *)
 >> STRIP_TAC
 >> Q.X_GEN_TAC ‘M0’ >> DISCH_TAC
 >> ‘closed M0’ by PROVE_TAC [closures_imp_closed]
 >> Suff ‘solvable M0’ >- PROVE_TAC [solvable_alt_closed]
 >> rw [solvable_of_closed]
 (* applying solvable_alt *)
 >> fs [solvable_alt, closures_def]
 >> Know ‘PERM vs vs'’
 >- (‘set vs = set vs'’ by PROVE_TAC [] \\
     ‘PERM vs  (SET_TO_LIST (set vs)) /\
      PERM vs' (SET_TO_LIST (set vs'))’
        by PROVE_TAC [ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] \\
     PROVE_TAC [PERM_TRANS, PERM_SYM])
 (* this asserts an bijection ‘f’ mapping vs to vs' *)
 >> DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERM_BIJ))
 (* stage work *)
 >> Q.ABBREV_TAC ‘n = LENGTH vs’
 >> Q.ABBREV_TAC ‘m = LENGTH Ns’
 >> Q.ABBREV_TAC ‘g = \i. if i < m then EL i Ns else I’
 (* permute the first n element of gN (Ns) *)
 >> Q.ABBREV_TAC ‘Ns' = GENLIST (\i. if i < n then g (f i) else g i) m’
 >> Q.EXISTS_TAC ‘Ns'’
 >> Suff ‘LAMl vs M @* Ns = LAMl vs' M @* Ns'’ >- PROVE_TAC []
 >> Q.PAT_X_ASSUM ‘M' = LAMl vs M’ K_TAC
 >> Q.PAT_X_ASSUM ‘M' @* Ns == I’  K_TAC
 (* stage work *)
 >> cheat
QED

(* based on ‘ssub’, allowing ‘FDOM fm’ bigger than ‘FV M’ *)
Definition closed_substitution_instances_def :
    closed_substitution_instances M =
       {fm ' M | fm | FV M SUBSET FDOM fm /\ !v. v IN FDOM fm ==> closed (fm ' v)}
End

(* cf. lameq_I *)
Theorem lameq_appstar_cong :
    !M N Ns. M == N ==> M @* Ns == N @* Ns
Proof
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC SNOC_INDUCT >> rw []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [SNOC_APPEND, SYM appstar_SNOC]
QED

Theorem solvable_alt_closed_substitution_instance_lemma[local] :
    !Ns. FV M = set vs /\ ALL_DISTINCT vs /\ LAMl vs M @* Ns == I /\
         LENGTH vs <= LENGTH Ns /\ EVERY closed Ns
     ==> ?M' Ns'. M' IN closed_substitution_instances M /\
                  M' @* Ns' == I /\ EVERY closed Ns'
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘n = LENGTH vs’
 >> Q.ABBREV_TAC ‘m = LENGTH Ns’
 >> Q.PAT_X_ASSUM ‘LAMl vs M @* Ns == I’ MP_TAC
 >> Q.ABBREV_TAC ‘Ns0 = TAKE n Ns’
 >> ‘LENGTH Ns0 = n’ by rw [Abbr ‘Ns0’, LENGTH_TAKE]
 >> Q.ABBREV_TAC ‘Ns1 = DROP n Ns’
 >> ‘Ns = Ns0 ++ Ns1’ by rw [Abbr ‘Ns0’, Abbr ‘Ns1’, TAKE_DROP]
 >> ‘EVERY closed Ns0 /\ EVERY closed Ns1’
      by FULL_SIMP_TAC std_ss [EVERY_APPEND]
 >> Q.PAT_X_ASSUM ‘Ns = Ns0 ++ Ns1’ (ONCE_REWRITE_TAC o wrap)
 >> REWRITE_TAC [appstar_APPEND]
 >> Q.ABBREV_TAC ‘fm = FEMPTY |++ ZIP (vs,Ns0)’
 (* stage work *)
 >> Suff ‘LAMl vs M @* Ns0 == fm ' M’
 >- (NTAC 2 DISCH_TAC \\
    ‘LAMl vs M @* Ns0 @* Ns1 == fm ' M @* Ns1’ by PROVE_TAC [lameq_appstar_cong] \\
    ‘fm ' M @* Ns1 == I’ by PROVE_TAC [lameq_trans, lameq_symm] \\
     qexistsl_tac [‘fm ' M’, ‘Ns1’] \\
     rw [closed_substitution_instances_def] \\
     Q.EXISTS_TAC ‘fm’ >> rw [Abbr ‘fm’] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rw [SUBSET_DEF, MEM_MAP, MEM_ZIP, FDOM_FUPDATE_LIST] \\
       Cases_on ‘INDEX_OF x vs’ >- fs [INDEX_OF_eq_NONE] \\
       rename1 ‘INDEX_OF x vs = SOME k’ \\
       fs [INDEX_OF_eq_SOME] \\
       Q.EXISTS_TAC ‘(x,EL k Ns0)’ >> simp [] \\
       Q.EXISTS_TAC ‘k’ >> simp [],
       (* goal 2 (of 2) *)
       gs [MEM_MAP, MEM_ZIP, FDOM_FUPDATE_LIST] \\
       Suff ‘(FEMPTY |++ ZIP (vs,Ns0)) ' (EL n vs) = EL n Ns0’
       >- (Rewr' \\
           Q.PAT_X_ASSUM ‘EVERY closed Ns0’ MP_TAC \\
           rw [EVERY_MEM] >> POP_ASSUM MATCH_MP_TAC \\
           rw [MEM_EL] \\
           Q.EXISTS_TAC ‘n’ >> rw []) \\
       MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
       Q.EXISTS_TAC ‘n’ \\
       rw [LENGTH_ZIP, EL_MAP, MAP_ZIP, EL_ZIP] \\
       rename1 ‘j < LENGTH Ns0’ >> ‘j <> n’ by rw [] \\
       METIS_TAC [EL_ALL_DISTINCT_EL_EQ] ])
 >> cheat
QED

(* Theorem 8.3.3 (i) *)
Theorem solvable_alt_closed_substitution_instance :
    !M. solvable M <=> ?M' Ns. M' IN closed_substitution_instances M /\
                               M' @* Ns == I /\ EVERY closed Ns
Proof
    Q.X_GEN_TAC ‘M’
 >> EQ_TAC
 >- (rw [solvable_alt, closures_def] \\
     Q.ABBREV_TAC ‘n = LENGTH vs’ \\
     Q.ABBREV_TAC ‘m = LENGTH Ns’ \\
     Cases_on ‘n <= m’
     >- (MATCH_MP_TAC solvable_alt_closed_substitution_instance_lemma \\
         Q.EXISTS_TAC ‘Ns’ >> rw []) \\
     Q.ABBREV_TAC ‘Is = GENLIST (\i. I) (n - m)’ \\
    ‘(LAMl vs M @* Ns) @* Is == I @* Is’ by PROVE_TAC [lameq_appstar_cong] \\
     Know ‘I @* Is == I’
     >- (Know ‘!e. MEM e Is ==> e = I’
         >- (rw [Abbr ‘Is’, MEM_GENLIST]) \\
         Q.ID_SPEC_TAC ‘Is’ \\
         HO_MATCH_MP_TAC SNOC_INDUCT >> rw [] \\
         ASM_SIMP_TAC (betafy (srw_ss())) [SNOC_APPEND, SYM appstar_SNOC, lameq_I]) \\
     DISCH_TAC \\
     FULL_SIMP_TAC std_ss [GSYM appstar_APPEND] \\
     Q.ABBREV_TAC ‘Ns' = Ns ++ Is’ \\
    ‘LENGTH Ns' = n’ by (rw [Abbr ‘Ns'’, Abbr ‘Is’]) \\
    ‘LAMl vs M @* Ns' == I’ by PROVE_TAC [lameq_trans] \\
     Know ‘EVERY closed Ns'’
     >- (rw [EVERY_APPEND, Abbr ‘Ns'’] \\
         rw [EVERY_MEM, Abbr ‘Is’, closed_def, MEM_GENLIST] \\
         REWRITE_TAC [FV_I]) >> DISCH_TAC \\
     MATCH_MP_TAC solvable_alt_closed_substitution_instance_lemma \\
     Q.EXISTS_TAC ‘Ns'’ >> rw [])
 (* stage work *)
 >> cheat
QED

val _ = export_theory ();
val _ = html_theory "solvable";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
   [2] Hankin, C.: Lambda Calculi: A Guide for Computer Scientists.
       Clarendon Press, Oxford (1994).
 *)
