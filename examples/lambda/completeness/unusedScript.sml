(*---------------------------------------------------------------------------*
 * boehm_treeScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])         *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory rich_listTheory
     llistTheory relationTheory ltreeTheory pathTheory posetTheory hurdUtils;

open basic_swapTheory binderLib termTheory appFOLDLTheory chap2Theory
     chap3Theory head_reductionTheory standardisationTheory solvableTheory;

open pure_dBTheory;

val _ = new_theory "unused";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)

(* A dB-term M is hnf if its corresponding Lambda term is hnf *)
Overload dhnf = “\M. hnf (toTerm M)”

Theorem dhnf_fromTerm[simp] :
    !M. dhnf (fromTerm M) <=> hnf M
Proof
    rw [o_DEF]
QED

(* dB version of hnf_cases (only the ==> direction) *)
Theorem dhnf_cases :
    !M. dhnf M ==> ?n y Ms. M = dABSi n (dV y @* Ms)
Proof
    RW_TAC std_ss [hnf_cases]
 >> qabbrev_tac ‘n = LENGTH vs’
 >> Q.EXISTS_TAC ‘n’
 >> Know ‘fromTerm (toTerm M) = fromTerm (LAMl vs (VAR y @* args))’
 >- (art [fromTerm_11])
 >> Q.PAT_X_ASSUM ‘toTerm M = LAMl vs (VAR y @* args)’ K_TAC
 >> REWRITE_TAC [fromtoTerm]
 >> rw [fromTerm_LAMl, fromTerm_appstar]
 >> qabbrev_tac ‘vs' = MAP s2n vs’
 >> qabbrev_tac ‘Ms = MAP fromTerm args’
 >> qabbrev_tac ‘y' = s2n y’
 >> Know ‘dLAMl vs' (dV y' @* Ms) =
          dABSi (LENGTH vs')
            (FOLDL lift (dV y' @* Ms) (GENLIST I (LENGTH vs')) ISUB
             ZIP (GENLIST dV (LENGTH vs'),
                  MAP (\i. i + LENGTH vs') (REVERSE vs')))’
 >- (MATCH_MP_TAC dLAMl_to_dABSi_applied \\
     qunabbrev_tac ‘vs'’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [])
 >> ‘LENGTH vs' = n’ by rw [Abbr ‘vs'’] >> POP_ORW
 >> Rewr'
 >> simp [FOLDL_lift_appstar, isub_appstar]
 >> Know ‘FOLDL lift (dV y') (GENLIST I n) = dV (y' + n)’
 >- (KILL_TAC \\
     Induct_on ‘n’ >> rw [GENLIST, FOLDL_SNOC])
 >> Rewr'
 >> qabbrev_tac ‘Ms' = MAP (\e. FOLDL lift e (GENLIST I n)) Ms’
 >> reverse (Cases_on ‘MEM y vs’)
 >- (‘~MEM y' vs'’ by (rw [Abbr ‘y'’, Abbr ‘vs'’, MEM_MAP]) \\
     ‘~MEM y' (REVERSE vs')’ by PROVE_TAC [MEM_REVERSE] \\
     Suff ‘dV (y' + n) ISUB ZIP (GENLIST dV n,MAP (\i. i + n) (REVERSE vs')) =
           dV (y' + n)’ >- (Rewr' >> METIS_TAC []) \\
     MATCH_MP_TAC isub_dV_fresh \\
     qabbrev_tac ‘l1 = GENLIST dV n’ \\
     qabbrev_tac ‘l2 = MAP (\i. i + n) (REVERSE vs')’ \\
    ‘LENGTH l1 = n’ by rw [Abbr ‘l1’] \\
    ‘LENGTH l2 = n’ by rw [Abbr ‘l2’, Abbr ‘n’, Abbr ‘vs'’] \\
     simp [DOM_ALT_MAP_SND, MAP_ZIP] \\
     rw [Abbr ‘l2’, MEM_MAP])
 (* stage work *)
 >> ‘MEM y' vs'’ by (rw [Abbr ‘y'’, Abbr ‘vs'’, MEM_MAP])
 >> ‘MEM y' (REVERSE vs')’ by PROVE_TAC [MEM_REVERSE]
 >> ‘?j. j < LENGTH (REVERSE vs') /\ y' = EL j (REVERSE vs')’
        by METIS_TAC [MEM_EL]
 >> ‘LENGTH (REVERSE vs') = n’ by rw [Abbr ‘vs'’, Abbr ‘n’]
 >> qabbrev_tac ‘Ns = MAP (\i. i + n) (REVERSE vs')’
 >> ‘LENGTH Ns = n’ by rw [Abbr ‘Ns’]
 >> Know ‘ALL_DISTINCT Ns’
 >- (qunabbrev_tac ‘Ns’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [] \\
     qunabbrev_tac ‘vs'’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [])
 >> DISCH_TAC
 >> Suff ‘dV (y' + n) ISUB ZIP (GENLIST dV n,Ns) = EL j (GENLIST dV n)’
 >- (Rewr' \\
     simp [EL_GENLIST] >> METIS_TAC [])
 >> MATCH_MP_TAC isub_dV_once >> simp []
 >> CONJ_TAC >- (rw [Abbr ‘Ns’, EL_MAP])
 >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC
 >> ‘n <= EL i Ns’ by rw [Abbr ‘Ns’, EL_MAP]
 >> Suff ‘FVS (ZIP (GENLIST dV n,Ns)) = count n’ >- rw []
 >> Q.PAT_X_ASSUM ‘LENGTH Ns = n’ MP_TAC
 >> KILL_TAC >> Q.ID_SPEC_TAC ‘Ns’
 >> Induct_on ‘n’ >> rw [dFVS_def]
 >> ‘Ns <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘LENGTH (FRONT Ns) = n’ by rw [LENGTH_FRONT]
 >> ‘Ns = SNOC (LAST Ns) (FRONT Ns)’
      by (rw [APPEND_FRONT_LAST, SNOC_APPEND]) >> POP_ORW
 >> Q.PAT_X_ASSUM ‘!Ns. LENGTH Ns = n ==> P’ (MP_TAC o (Q.SPEC ‘FRONT Ns’))
 >> rw [GENLIST, COUNT_SUC, dFVS_SNOC, ZIP_SNOC, dFV_def]
 >> SET_TAC []
QED

(* |- ?f f' f''. !M. dhnf M ==> M = dABS (f M) (dV (f' M) @* f'' M) *)
val dhnf_cases' = dhnf_cases
               |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM];

(* Explicit definitions of hnf components (easier to work with) by Michael Norrish:

   1. The number of leading dABS (can be zero):
 *)
Definition dABSn_def :
   (dABSn (dV n)       = 0) /\
   (dABSn (dAPP t1 t2) = 0) /\
   (dABSn (dABS t)     = 1 + dABSn t)
End

(* 2. The head variable of hnf (always exists) *)
Definition dVn_def :
   (dVn (dV n)       = n) /\
   (dVn (dABS t)     = dVn t) /\
   (dVn (dAPP t1 t2) = dVn t1)
End

(* 2. The list of terms after appstar (may be empty) *)
Definition dAPPl_def :
   (dAPPl (dV n)       = []) /\
   (dAPPl (dABS t)     = dAPPl t) /\
   (dAPPl (dAPP t1 t2) = SNOC t2 (dAPPl t1))
End

(* The "main" part of a hnf *)
Definition dhnf_head_def :
    dhnf_head M = dABSi (dABSn M) (dV (dVn M))
End

val _ = export_rewrites ["dABSn_def", "dVn_def", "dAPPl_def"];

Theorem dABSn_dABSi[simp] :
    dABSn (dABSi n t) = n + dABSn t
Proof
    Induct_on ‘n’ >> rw [FUNPOW_SUC]
QED

Theorem dABSn_dV_appstar[simp] :
    dABSn (dV y @* Ns) = 0
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT
 >> rw [appstar_SNOC]
QED

Theorem dVn_dABSi[simp] :
    dVn (dABSi n t) = dVn t
Proof
    Induct_on ‘n’ >> rw [FUNPOW_SUC]
QED

Theorem dVn_appstar[simp] :
    dVn (M @* Ns) = dVn M
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT >> rw []
QED

Theorem dAPPl_dABSi[simp] :
    dAPPl (dABSi n t) = dAPPl t
Proof
    Induct_on ‘n’ >> rw [FUNPOW_SUC]
QED

Theorem dAPPl_dV_appstar[simp] :
    dAPPl (dV y @* Ns) = Ns
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT >> rw [dappstar_APPEND]
QED

Theorem dhnf_thm :
    !M. dhnf M ==> M = dABSi (dABSn M) (dV (dVn M) @* dAPPl M)
Proof
    rpt STRIP_TAC
 >> ‘?n y Ms. M = dABSi n (dV y @* Ms)’ by METIS_TAC [dhnf_cases]
 >> rw []
QED

Definition principle_hnf_def :
    principle_hnf = fromTerm o last o head_reduction_path o toTerm
End

Overload solvable = “solvable o toTerm”

(* The needed unfolding function for ltree_unfold for Boehm Tree *)
Definition dBT_generator_def :
    dBT_generator (M :pdb) = if solvable M then
                               let M' = principle_hnf M in
                                 (SOME (dhnf_head M'), fromList (dAPPl M'))
                             else
                               (NONE, LNIL)
End

(* The Boehm tree of M, all in dB terms *)
Definition dBT_def :
    dBT = ltree_unfold dBT_generator
End

(* M = dABSi (dABSn M) (dV (dVn M) @* dAPPl M)
   N = dABSi (dABSn N) (dV (dVn N) @* dAPPl N)

   n  = dABSn M, y  = dVn M, m  = LENGTH (dAPPL M)
   n' = dABSn N, y' = dVn N, m' = LENGTH (dAPPL N)
 *)
Definition dB_equivalent_def :
    dB_equivalent (M :pdb) (N :pdb) =
       if solvable M /\ solvable N then
          let M0 = principle_hnf M;
              N0 = principle_hnf N;
              y  = dVn M0;
              y' = dVn N0;
              n  = dABSn M0;
              n' = dABSn N0;
              m  = LENGTH (dAPPl M0);
              m' = LENGTH (dAPPl N0);
          in
              y = y' /\ n + m' = n' + m
       else
          ~solvable M /\ ~solvable N
End

Overload equivalent = “dB_equivalent”

Theorem equivalent_alt_solvable :
    !M N. solvable M /\ solvable N ==>
         (equivalent M (N :pdb) <=>
          let M0 = principle_hnf M;
              N0 = principle_hnf N
          in
              dVn M0 = dVn N0 /\
              dABSn M0 + LENGTH (dAPPl N0) = dABSn N0 + LENGTH (dAPPl M0))
Proof
    rw [dB_equivalent_def]
QED

val _ = export_theory ();
val _ = html_theory "unused";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
