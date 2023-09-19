(*---------------------------------------------------------------------------*
 * boehmScript.sml: (Effective) Boehm Trees                                  *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open pred_setTheory listTheory optionTheory;

(* theories in ../basics *)
open binderLib termTheory appFOLDLTheory;

(* theories in ../barendregt *)
open head_reductionTheory standardisationTheory;

(* local theories *)
open pure_dBTheory;

val _ = new_theory "boehm_tree";

(* Definition 10.1.1 [1, p.215]
Definition labelled_tree_def :
   labelled_tree (symbols :'a set) (nodes :num list set) (phi :num list -> 'a option) =
     ([] IN nodes /\
      (!s t. s IN nodes /\ t <<= s ==> t IN nodes) /\
      (!s. s IN nodes ==> THE (phi s) IN symbols))
End

(* Take out vs y and Ms from “LAMl vs ((VAR y) @* Ms)”

val (is_abs_thm, _) = define_recursive_term_function
  `(is_abs (VAR s) = F) /\
   (is_abs (t1 @@ t2) = F) /\
   (is_abs (LAM v t) = T)`;

   TODO: Couldn't prove function with swap over range

   If use ‘is_abs’ instead, how to take out the lambda body?
 *)
val (hnf_LAMl_thm, _) = define_recursive_term_function
   ‘(hnf_LAMl ((VAR s) :term) = []) /\
    (hnf_LAMl (M @@ N) = []) /\
    (hnf_LAMl (LAM v M) = v::hnf_LAMl M)’;

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
