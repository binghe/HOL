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

val _ = new_theory "boehm_tree";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)

(* A dB-term M is hnf if its corresponding Lambda term is hnf *)
Overload dhnf = “\M. hnf (toTerm M)”

Theorem dhnf_fromTerm[simp] :
    !M. dhnf (fromTerm M) <=> hnf M
Proof
    rw [o_DEF]
QED

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
val _ = html_theory "boehm_tree";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
