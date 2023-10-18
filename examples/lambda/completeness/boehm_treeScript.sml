(*---------------------------------------------------------------------------*
 * boehm_treeScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])         *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory llistTheory
     ltreeTheory pathTheory;

(* theories in ../basics *)
open binderLib termTheory appFOLDLTheory;

(* theories in ../barendregt *)
open chap2Theory chap3Theory head_reductionTheory standardisationTheory
     solvableTheory;

(* theories in ../other-models *)
open pure_dBTheory;

val _ = new_theory "boehm_tree";

(*---------------------------------------------------------------------------*
 * Principle Head Normal Forms (phnf)
 *---------------------------------------------------------------------------*)

 (* Definition 8.3.20 [1, p.177]

   A term may have several hnf's, e.g. if any of its hnf can still do beta
   reductions, after such reductions the term is still an hnf by definition.
   The (unique) terminating term of head reduction path is called "principle"
   hnf, which is used for defining Boehm trees.
 *)
Definition phnf_def :
    phnf (M :term) = last (head_reduction_path M)
End

(* TODO: move to solvableTheory *)
Theorem solvable_phnf :
    !M. solvable M ==> hnf (phnf M)
Proof
    rw [solvable_iff_has_hnf, phnf_def, head_reduction_path_def, corollary11_4_8]
QED

(* TODO: move to pure_DBTheory *)
Definition dABS_body_def :
    dABS_body (dABS s) = s
End

Definition dAPP_rator_def :
    dAPP_rator (dAPP s t) = s
End

Definition dAPP_rand_def :
    dAPP_rand (dAPP s t) = t
End

Overload "@*" = “\f args. FOLDL dAPP f args”

Definition dB_hnf_def :
    dB_hnf M = hnf (toTerm M)
End

Theorem hnf_iff_dB_hnf :
    !M. hnf M <=> dB_hnf (fromTerm M)
Proof
    rw [dB_hnf_def]
QED

(* dB version of hnf_cases *)
Theorem dB_hnf_cases :
    !M. dB_hnf M <=> ?n y Ms. M = FUNPOW dABS n ((dV y) @* Ms)
Proof
    cheat
QED

(*
Definition BT0_def :
   (BT0 (M :term) ([] :num list) = if unsolvable M then NONE
                                  else ARB) /\
   (BT0 (M :term) (k::ks) = if unsolvable M then ARB else
                           ARB)
End

(* NOTE: “hnf_of” is undefined
   (cf. normal_orderTheory.bnf_of_def or head_reductionTheory)
 *)
Definition BT_def :
   BT M = if unsolvable M then (\s. NONE)
          else BT0 (hnf_of M)
End

(* When M is solvable and has principal hnf *)
Definition BTe_def :
   (BTe (M :term) ([] :num list) =
        if has_hnf M then (SOME (LAMl vs (VAR y)), LENGTH Ms)
        else (NONE, 0)) /\
   (BTe M (k::xs) =
        if has_hnf M then BTe [EL k Ms] xs
        else (NONE, 0)
End
*)

val _ = export_theory ();
val _ = html_theory "boehm_tree";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
