(*---------------------------------------------------------------------------*
 * boehmScript.sml: (Effective) Boehm Trees                                  *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open pred_setTheory listTheory llistTheory ltreeTheory optionTheory;

(* theories in ../basics *)
open binderLib termTheory appFOLDLTheory;

(* theories in ../barendregt *)
open head_reductionTheory standardisationTheory;

(* local theories *)
open pure_dBTheory;

val _ = new_theory "boehm_tree";

(* Definition 8.3.20 [1, p.177]

   A term may have several hnf's, e.g. if any of its hnf can still do beta
   reductions, after such reductions the term is still an hnf by definition.
   The (unique) terminating term of head reduction path is called "principle"
   hnf, which is used for defining Boehm trees.
 *)
Definition principle_hnf_def :
    principle_hnf (M :term) = last (head_reduction_path M)
End

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
