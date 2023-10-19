(*---------------------------------------------------------------------------*
 * boehm_treeScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])         *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory llistTheory
     ltreeTheory pathTheory hurdUtils;

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

Theorem solvable_phnf :
    !M. solvable M ==> hnf (phnf M)
Proof
    rw [solvable_iff_has_hnf, phnf_def, head_reduction_path_def, corollary11_4_8]
QED

Definition dABS_body_def :
    dABS_body (dABS s) = s
End

Definition dAPP_rator_def :
    dAPP_rator (dAPP s t) = s
End

Definition dAPP_rand_def :
    dAPP_rand (dAPP s t) = t
End

(* A dB-term M is hnf if its corresponding Lambda term is hnf *)
Definition dhnf_def :
    dhnf M = hnf (toTerm M)
End

Theorem dhnf_fromTerm[simp] :
    !M. dhnf (fromTerm M) <=> hnf M
Proof
    rw [dhnf_def]
QED

(* A sample:

> SIMP_CONV arith_ss [dLAM_def, lift_def, nipkow_lift_lemma1, sub_def, lift_sub]
                     “dLAM v2 (dLAM v1 (dLAM v0 t))”;
# val it =
   |- dLAM v2 (dLAM v1 (dLAM v0 t)) =
      dABS
        (dABS
           (dABS ([dV 2/v2 + 3] ([dV 1/v1 + 3] ([dV 0/v0 + 3] (lift (lift (lift t 0) 0) 0)))))):
   thm
 *)
Theorem LAMl_to_dABSl :
    !vs. ALL_DISTINCT (vs :num list) ==>
           let n = LENGTH vs;
             body = FOLDL lift t (GENLIST (\x. 0) n);
             is = ZIP (GENLIST dV n, MAP (\i. i + n) (REVERSE vs))
           in LAMl vs t = dABSl n (body ISUB is)
Proof
    Induct_on ‘vs’ >- rw [isub_def]
 >> rw [isub_def, GSYM SNOC_APPEND, MAP_SNOC,
        FUNPOW_SUC, GENLIST, FOLDL_SNOC, dLAM_def]
 >> fs []
 >> qabbrev_tac ‘n = LENGTH vs’
 >> rw [lift_dABSl]
 >> cheat
QED

(* |- !t vs.
        ALL_DISTINCT vs ==>
        LAMl vs t =
        dABSl (LENGTH vs)
          (FOLDL lift t (GENLIST (\x. 0) (LENGTH vs)) ISUB
           ZIP (GENLIST dV (LENGTH vs),MAP (\i. i + LENGTH vs) (REVERSE vs)))
 *)
Theorem LAMl_to_dABSl_applied = GEN_ALL (SIMP_RULE std_ss [LET_DEF] LAMl_to_dABSl)

(* dB version of hnf_cases *)
Theorem dhnf_cases :
    !M. dhnf M <=> ?n y Ms. M = dABSl n (dV y @* Ms)
Proof
    RW_TAC std_ss [dhnf_def, hnf_cases]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (qabbrev_tac ‘n = LENGTH vs’ >> Q.EXISTS_TAC ‘n’ \\
     Know ‘fromTerm (toTerm M) = fromTerm (LAMl vs (VAR y @* args))’
     >- (art [fromTerm_11]) \\
     rw [fromTerm_LAMl, fromTerm_appstar] \\
     qabbrev_tac ‘vs' = MAP s2n vs’ \\
     qabbrev_tac ‘Ms = MAP fromTerm args’ \\
     qabbrev_tac ‘y' = s2n y’ \\
     Know ‘LAMl vs' (dV y' @* Ms) =
           dABSl (LENGTH vs')
             (FOLDL lift (dV y' @* Ms) (GENLIST (\x. 0) (LENGTH vs')) ISUB
              ZIP (GENLIST dV (LENGTH vs'),MAP (\i. i + LENGTH vs') (REVERSE vs')))’
     >- (MATCH_MP_TAC LAMl_to_dABSl_applied \\
         qunabbrev_tac ‘vs'’ \\
         MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw []) \\
    ‘LENGTH vs' = n’ by rw [Abbr ‘vs'’] >> POP_ORW >> Rewr' \\
     simp [FOLDL_lift_appstar, isub_appstar] \\
     cheat)
 (* stage work *)
 >> cheat
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
