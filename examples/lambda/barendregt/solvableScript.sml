(*---------------------------------------------------------------------------*
 * solvableScript.sml (or chap8_3): Theory of Solvable Lambda Terms          *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

(* core theories *)
open arithmeticTheory pred_setTheory listTheory sortingTheory finite_mapTheory
     hurdUtils;

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

Theorem lameq_symm[local]  = List.nth(CONJUNCTS lameq_rules, 2)
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

(* NOTE: ‘FV M = {}’ is additionally required *)
Theorem ssub_update_apply' :
    !fm. s NOTIN FDOM fm /\ (!y. y IN FDOM fm ==> FV (fm ' y) = {}) /\
         FV M = {} ==> (fm |+ (s,M)) ' N = fm ' ([M/s] N)
Proof
    rpt STRIP_TAC
 >> Q.ID_SPEC_TAC ‘N’
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘s INSERT (FDOM fm)’
 >> rw [SUB_VAR, SUB_THM, ssub_thm, FAPPLY_FUPDATE_THM]
 >> TRY (METIS_TAC [])
 >- (MATCH_MP_TAC (GSYM ssub_value) >> art [])
 >> Know ‘(fm |+ (s,M)) ' (LAM y N) = LAM y ((fm |+ (s,M)) ' N)’
 >- (MATCH_MP_TAC ssub_LAM >> rw [FAPPLY_FUPDATE_THM])
 >> Rewr'
 >> ASM_SIMP_TAC (betafy (srw_ss())) []
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

Definition closed_substitution_instances_def :
    closed_substitution_instances M =
       {fm ' M | fm | FDOM fm = FV M /\ !v. v IN FDOM fm ==> closed (fm ' v)}
End

(* cf. lameq_I *)
Theorem lameq_appstar_cong :
    !M N Ns. M == N ==> M @* Ns == N @* Ns
Proof
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC SNOC_INDUCT >> rw []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [SNOC_APPEND, SYM appstar_SNOC]
QED

Theorem LAMl_SUB :
    !M N v vs. ALL_DISTINCT vs /\ ~MEM v vs /\ FV N = {} ==>
               [N/v] (LAMl vs M) == LAMl vs ([N/v] M)
Proof
    rpt STRIP_TAC
 >> Induct_on ‘vs’ >> rw []
 >> ASM_SIMP_TAC (betafy (srw_ss())) []
QED

Theorem LAMl_appstar :
    !vs M Ns. ALL_DISTINCT vs /\ LENGTH vs = LENGTH Ns /\ EVERY closed Ns ==>
              LAMl vs M @* Ns == (FEMPTY |++ ZIP (vs,Ns)) ' M
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘L = ZIP (vs,Ns)’
 >> ‘Ns = MAP SND L /\ vs = MAP FST L’ by rw [Abbr ‘L’, MAP_ZIP]
 >> FULL_SIMP_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘EVERY closed (MAP SND L)’ MP_TAC
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT (MAP FST L)’ MP_TAC
 >> KILL_TAC
 >> Q.ID_SPEC_TAC ‘M’
 (* stage work *)
 >> Induct_on ‘L’ >> rw []
 >- (Suff ‘FEMPTY |++ [] = FEMPTY :string |-> term’ >- rw [] \\
     rw [FUPDATE_LIST_EQ_FEMPTY])
 >> Q.ABBREV_TAC ‘v = FST h’
 >> Q.ABBREV_TAC ‘vs = MAP FST L’
 >> Q.ABBREV_TAC ‘N = SND h’
 >> Q.ABBREV_TAC ‘Ns = MAP SND L’
 (* RHS rewriting *)
 >> ‘h :: L = [h] ++ L’ by rw [] >> POP_ORW
 >> rw [FUPDATE_LIST_APPEND]
 >> Know ‘FEMPTY |++ [h] |++ L = FEMPTY |++ L |++ [h]’
 >- (MATCH_MP_TAC FUPDATE_LIST_APPEND_COMMUTES \\
     rw [DISJOINT_ALT])
 >> Rewr'
 >> rw [GSYM FUPDATE_EQ_FUPDATE_LIST]
 >> Q.ABBREV_TAC ‘fm = FEMPTY |++ L’
 >> FULL_SIMP_TAC std_ss []
 >> ‘h = (v,N)’ by rw [Abbr ‘v’, Abbr ‘N’] >> POP_ORW
 >> Know ‘(fm |+ (v,N)) ' M = fm ' ([N/v] M)’
 >- (MATCH_MP_TAC ssub_update_apply' \\
     Q.PAT_X_ASSUM ‘closed N’ MP_TAC \\
     rw [Abbr ‘fm’, FDOM_FUPDATE_LIST, closed_def] \\
     Cases_on ‘INDEX_OF y vs’ >- fs [INDEX_OF_eq_NONE] \\
     rename1 ‘INDEX_OF y vs = SOME n’ \\
     fs [INDEX_OF_eq_SOME] \\
     Q.PAT_X_ASSUM ‘EL n vs = y’ (ONCE_REWRITE_TAC o wrap o SYM) \\
    ‘LENGTH L = LENGTH vs’ by rw [Abbr ‘vs’, LENGTH_MAP] \\
     Know ‘(FEMPTY |++ L) ' (EL n vs) = EL n Ns’
     >- (MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
         Q.EXISTS_TAC ‘n’ >> rw [] \\
        ‘m <> n’ by rw [] \\
         METIS_TAC [EL_ALL_DISTINCT_EL_EQ]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘EVERY closed Ns’ MP_TAC \\
     rw [EVERY_MEM, closed_def] \\
     POP_ASSUM MATCH_MP_TAC >> rw [MEM_EL] \\
    ‘LENGTH L = LENGTH Ns’ by rw [Abbr ‘Ns’, LENGTH_MAP] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> Rewr'
 (* LHS rewriting *)
 >> Know ‘LAM v (LAMl vs M) @@ N == LAMl vs ([N/v] M)’
 >- (SIMP_TAC (betafy (srw_ss())) [] \\
     MATCH_MP_TAC LAMl_SUB \\
     Q.PAT_X_ASSUM ‘closed N’ MP_TAC >> rw [closed_def])
 >> DISCH_TAC
 >> MATCH_MP_TAC lameq_trans
 >> Q.EXISTS_TAC ‘LAMl vs ([N/v] M) @* Ns’ >> art []
 >> MATCH_MP_TAC lameq_appstar_cong >> art []
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
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘fm = FEMPTY |++ ZIP (vs,Ns0)’
 >> Know ‘LAMl vs M @* Ns0 == fm ' M’
 >- (Q.UNABBREV_TAC ‘fm’ \\
     MATCH_MP_TAC LAMl_appstar >> rw [])
 >> DISCH_TAC
 >> ‘LAMl vs M @* Ns0 @* Ns1 == fm ' M @* Ns1’ by PROVE_TAC [lameq_appstar_cong]
 >> ‘fm ' M @* Ns1 == I’ by PROVE_TAC [lameq_trans, lameq_symm]
 >> qexistsl_tac [‘fm ' M’, ‘Ns1’]
 >> rw [closed_substitution_instances_def]
 >> Q.EXISTS_TAC ‘fm’ >> rw [Abbr ‘fm’]
 >- rw [MEM_MAP, MEM_ZIP, FDOM_FUPDATE_LIST, MAP_ZIP]
 >> gs [MEM_MAP, MEM_ZIP, FDOM_FUPDATE_LIST]
 >> Suff ‘(FEMPTY |++ ZIP (vs,Ns0)) ' (EL n vs) = EL n Ns0’
 >- (Rewr' \\
     Q.PAT_X_ASSUM ‘EVERY closed Ns0’ MP_TAC >> rw [EVERY_MEM] \\
     POP_ASSUM MATCH_MP_TAC >> rw [MEM_EL] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM
 >> Q.EXISTS_TAC ‘n’
 >> rw [LENGTH_ZIP, EL_MAP, MAP_ZIP, EL_ZIP]
 >> rename1 ‘j < LENGTH Ns0’
 >> ‘j <> n’ by rw []
 >> METIS_TAC [EL_ALL_DISTINCT_EL_EQ]
QED

Theorem I_appstar :
    I @* (GENLIST (\i. I) n) == I
Proof
    Q.ABBREV_TAC ‘Is = GENLIST (\i. I) n’
 >> Know ‘!e. MEM e Is ==> e = I’
 >- rw [Abbr ‘Is’, MEM_GENLIST]
 >> Q.ID_SPEC_TAC ‘Is’
 >> HO_MATCH_MP_TAC SNOC_INDUCT >> rw []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [SNOC_APPEND, SYM appstar_SNOC, lameq_I]
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
    ‘I @* Is == I’ by PROVE_TAC [I_appstar] \\
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
 >> rw [solvable_def, closed_substitution_instances_def]
 >> Q.ABBREV_TAC ‘vss = FDOM fm’
 >> ‘FINITE vss’ by rw [FDOM_FINITE, Abbr ‘vss’]
 (* preparing for LAMl_appstar *)
 >> Q.ABBREV_TAC ‘vs = SET_TO_LIST vss’
 >> ‘ALL_DISTINCT vs’ by PROVE_TAC [Abbr ‘vs’, ALL_DISTINCT_SET_TO_LIST]
 >> Q.ABBREV_TAC ‘Ps = MAP (\v. fm ' v) vs’
 >> ‘LENGTH Ps = LENGTH vs’ by rw [Abbr ‘Ps’]
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘fm ' M @* Ns == I’ MP_TAC
 >> Know ‘fm = (FEMPTY |++ ZIP (vs,Ps))’
 >- (rw [fmap_EXT, FDOM_FUPDATE_LIST, MAP_ZIP]
     >- rw [Abbr ‘vs’, SET_TO_LIST_INV] \\
    ‘MEM x vs’ by rw [Abbr ‘vs’] \\
     Cases_on ‘INDEX_OF x vs’ >- fs [INDEX_OF_eq_NONE] \\
     rename1 ‘INDEX_OF x vs = SOME n’ \\
     fs [INDEX_OF_eq_SOME] \\
     Q.PAT_X_ASSUM ‘EL n vs = x’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.ABBREV_TAC ‘L = ZIP (vs,Ps)’ \\
    ‘LENGTH L = LENGTH vs’ by rw [Abbr ‘L’, LENGTH_ZIP] \\
     Know ‘(FEMPTY |++ L) ' (EL n vs) = EL n Ps’
     >- (MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
         Q.EXISTS_TAC ‘n’ >> rw [EL_MAP, Abbr ‘L’, EL_ZIP] \\
        ‘m <> n’ by rw [] \\
         METIS_TAC [EL_ALL_DISTINCT_EL_EQ]) >> Rewr' \\
     rw [Abbr ‘Ps’, EL_MAP])
 >> Rewr'
 >> DISCH_TAC
 >> Know ‘LAMl vs M @* Ps == (FEMPTY |++ ZIP (vs,Ps)) ' M’
 >- (MATCH_MP_TAC LAMl_appstar >> art [] \\
     rw [Abbr ‘Ps’, EVERY_MEM, MEM_MAP] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     POP_ASSUM MP_TAC \\
     rw [Abbr ‘vs’, MEM_SET_TO_LIST])
 >> DISCH_TAC
 >> Know ‘LAMl vs M @* Ps @* Ns == (FEMPTY |++ ZIP (vs,Ps)) ' M @* Ns’
 >- (MATCH_MP_TAC lameq_appstar_cong >> art [])
 >> DISCH_TAC
 >> ‘LAMl vs M @* Ps @* Ns == I’ by PROVE_TAC [lameq_trans]
 >> qexistsl_tac [‘LAMl vs M’, ‘Ps ++ Ns’]
 >> rw [appstar_APPEND, closures_def]
 >> Q.EXISTS_TAC ‘vs’ >> art []
 >> rw [Abbr ‘vs’, SET_TO_LIST_INV]
QED

Theorem solvable_alt_all_closures_lemma[local] :
    !Ns. ALL_DISTINCT vs /\ ALL_DISTINCT vs' /\
         set vs = FV M /\ set vs' = FV M /\
         LENGTH vs <= LENGTH Ns /\ EVERY closed Ns /\
         LAMl vs M @* Ns == I ==> ?Ns'. LAMl vs' M @* Ns' == I
Proof
    rpt STRIP_TAC
 >> Know ‘PERM vs vs'’
 >- (‘set vs = set vs'’ by PROVE_TAC [] \\
     ‘PERM vs  (SET_TO_LIST (set vs)) /\
      PERM vs' (SET_TO_LIST (set vs'))’
        by PROVE_TAC [ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] \\
     PROVE_TAC [PERM_TRANS, PERM_SYM])
 (* asserts an bijection ‘f’ mapping vs to vs' *)
 >> DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERM_BIJ))
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
 >> DISCH_TAC
 (* construct the 1st finite map *)
 >> Q.ABBREV_TAC ‘fm = FEMPTY |++ ZIP (vs,Ns0)’
 >> Know ‘LAMl vs M @* Ns0 == fm ' M’
 >- (Q.UNABBREV_TAC ‘fm’ \\
     MATCH_MP_TAC LAMl_appstar >> rw [])
 >> DISCH_TAC
 >> ‘LAMl vs M @* Ns0 @* Ns1 == fm ' M @* Ns1’ by PROVE_TAC [lameq_appstar_cong]
 >> ‘fm ' M @* Ns1 == I’ by PROVE_TAC [lameq_trans, lameq_symm]
 (* Ns0' is the permuted version of Ns0 *)
 >> Q.ABBREV_TAC ‘Ns0' = GENLIST (\i. EL (f i) Ns0) n’
 >> ‘LENGTH Ns0' = n’ by rw [Abbr ‘Ns0'’, LENGTH_GENLIST]
 >> Know ‘EVERY closed Ns0'’
 >- (Q.PAT_X_ASSUM ‘EVERY closed Ns0’ MP_TAC \\
     rw [Abbr ‘Ns0'’, EVERY_MEM, MEM_GENLIST, LENGTH_GENLIST] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> rw [MEM_EL] \\
     Q.ABBREV_TAC ‘n = LENGTH Ns0’ \\
     Q.EXISTS_TAC ‘f i’ >> art [] \\
     Q.PAT_X_ASSUM ‘f PERMUTES count n’ MP_TAC \\
     rw [BIJ_ALT, IN_FUNSET])
 >> DISCH_TAC
 (* stage work *)
 >> Q.EXISTS_TAC ‘Ns0' ++ Ns1’
 >> REWRITE_TAC [appstar_APPEND]
 (* construct the 2nd finite map *)
 >> Q.ABBREV_TAC ‘fm' = FEMPTY |++ ZIP (vs',Ns0')’
 >> Know ‘LAMl vs' M @* Ns0' == fm' ' M’
 >- (Q.UNABBREV_TAC ‘fm'’ \\
     MATCH_MP_TAC LAMl_appstar >> rw [])
 >> DISCH_TAC
 >> ‘LAMl vs' M @* Ns0' @* Ns1 == fm' ' M @* Ns1’ by PROVE_TAC [lameq_appstar_cong]
 >> MATCH_MP_TAC lameq_trans
 >> Q.EXISTS_TAC ‘fm' ' M @* Ns1’ >> art []
 >> MATCH_MP_TAC lameq_trans
 >> Q.EXISTS_TAC ‘fm ' M @* Ns1’ >> art []
 >> Suff ‘fm = fm'’ >- rw []
 (* cleanup uncessary assumptions *)
 >> Q.PAT_X_ASSUM ‘LAMl vs M @* Ns0 @* Ns1 == I’                K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs M @* Ns0 == fm ' M’                  K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs M @* Ns0 @* Ns1 == fm ' M @* Ns1’    K_TAC
 >> Q.PAT_X_ASSUM ‘fm ' M @* Ns1 == I’                          K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs' M @* Ns0' == fm' ' M’               K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs' M @* Ns0' @* Ns1 == fm' ' M @* Ns1’ K_TAC
 (* g is bijection inversion of f *)
 >> MP_TAC (Q.ISPECL [‘f :num -> num’, ‘count n’, ‘count n’] BIJ_INV)
 >> RW_TAC std_ss [IN_COUNT]
 >> ‘LENGTH vs = LENGTH Ns0’ by PROVE_TAC []
 (* final goal: fm = fm' *)
 >> rw [Abbr ‘fm’, Abbr ‘fm'’, fmap_EXT, FDOM_FUPDATE_LIST, MAP_ZIP]
 >> ‘MEM x vs’ by PROVE_TAC []
 >> Cases_on ‘INDEX_OF x vs’ >- fs [INDEX_OF_eq_NONE]
 >> rename1 ‘INDEX_OF x vs = SOME n’
 >> fs [INDEX_OF_eq_SOME]
 >> Q.PAT_X_ASSUM ‘EL n vs = x’ (ONCE_REWRITE_TAC o wrap o SYM)
 (* applying FUPDATE_LIST_APPLY_MEM *)
 >> Know ‘(FEMPTY |++ ZIP (vs,Ns0)) ' (EL n vs) = EL n Ns0’
 >- (MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
     Q.EXISTS_TAC ‘n’ \\
     rw [LENGTH_ZIP, EL_MAP, MAP_ZIP, EL_ZIP] \\
     rename1 ‘n < k’ >> ‘k <> n’ by rw [] \\
     METIS_TAC [EL_ALL_DISTINCT_EL_EQ])
 >> Rewr'
 >> Q.ABBREV_TAC ‘n0 = LENGTH Ns0'’
 >> Know ‘g n < n0’
 >- (Q.PAT_X_ASSUM ‘g PERMUTES count n0’ MP_TAC \\
     rw [BIJ_ALT, IN_FUNSET])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘vs' = GENLIST (\i. EL (f i) vs) n0’
 >> ‘LENGTH vs' = LENGTH Ns0'’ by rw [Abbr ‘vs'’, LENGTH_GENLIST]
 >> ‘EL n vs = EL (g n) vs'’
       by (rw [Abbr ‘vs'’, EL_GENLIST]) >> POP_ORW
 >> Q.ABBREV_TAC ‘i = g n’
 >> Know ‘(FEMPTY |++ ZIP (vs',Ns0')) ' (EL i vs') = EL i Ns0'’
 >- (MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
     Q.EXISTS_TAC ‘i’ \\
     rw [LENGTH_ZIP, EL_MAP, MAP_ZIP, EL_ZIP] \\
     rename1 ‘i < j’ >> ‘j <> i’ by rw [] \\
     METIS_TAC [EL_ALL_DISTINCT_EL_EQ])
 >> Rewr'
 >> rw [Abbr ‘Ns0'’, Abbr ‘i’, EL_GENLIST]
QED

(* cf. solvable_def, with the existential quantifier "upgraded" to universal.

   NOTE: this proof needs sortingTheory (PERM)
 *)
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
 >> Q.ABBREV_TAC ‘n = LENGTH vs’
 >> Q.ABBREV_TAC ‘m = LENGTH Ns’
 >> Cases_on ‘n <= m’
 >- (MATCH_MP_TAC solvable_alt_all_closures_lemma \\
     Q.EXISTS_TAC ‘Ns’ >> rw [])
 (* additional steps when ‘m < n’ *)
 >> Q.ABBREV_TAC ‘Is = GENLIST (\i. I) (n - m)’
 >> ‘(LAMl vs M @* Ns) @* Is == I @* Is’ by PROVE_TAC [lameq_appstar_cong]
 >> ‘I @* Is == I’ by METIS_TAC [I_appstar]
 >> ‘LAMl vs M @* (Ns ++ Is) == I @* Is’ by rw [appstar_APPEND]
 >> Q.ABBREV_TAC ‘Ns' = Ns ++ Is’
 >> ‘LENGTH Ns' = n’ by (rw [Abbr ‘Ns'’, Abbr ‘Is’])
 >> ‘LAMl vs M @* Ns' == I’ by PROVE_TAC [lameq_trans]
 >> Know ‘EVERY closed Ns'’
 >- (rw [EVERY_APPEND, Abbr ‘Ns'’] \\
     rw [EVERY_MEM, Abbr ‘Is’, closed_def, MEM_GENLIST] \\
     REWRITE_TAC [FV_I])
 >> DISCH_TAC
 >> MATCH_MP_TAC solvable_alt_all_closures_lemma
 >> Q.EXISTS_TAC ‘Ns'’ >> rw []
QED

(* Theorem 8.3.3 (ii) *)
Theorem solvable_iff_LAM_solvable :
    !M x. solvable M <=> solvable (LAM x M)
Proof
    cheat
QED

val _ = export_theory ();
val _ = html_theory "solvable";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
   [2] Hankin, C.: Lambda Calculi: A Guide for Computer Scientists.
       Clarendon Press, Oxford (1994).
 *)
