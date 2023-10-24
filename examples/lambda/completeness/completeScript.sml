(*---------------------------------------------------------------------------*
 * completeScript.sml: The completeness of Lambda theories
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory llistTheory
     ltreeTheory pathTheory posetTheory relationTheory finite_mapTheory
     hurdUtils;

open binderLib termTheory appFOLDLTheory chap2Theory chap3Theory
     head_reductionTheory standardisationTheory solvableTheory pure_dBTheory;

open boehm_treeTheory;

val _ = new_theory "complete";

val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)

(* Theorem 2.1.36 [1, p.34] or Corollary 15.1.5

   NOTE: This theorem is not necessary if the antecedent of Theorem 2.1.40 is
   replaced by ‘has_benf M /\ has_benf N’.
 *)
Theorem has_benf_iff_has_bnf :
    !M. has_benf M <=> has_bnf M
Proof
    cheat
QED

(* Theorem 2.1.39 [1, p.35] or Theorem 10.4.3 (i) [1, p.256] *)
Theorem benf_incompatible :
    !M N. benf M /\ benf N /\ M <> N ==> incompatible M N
Proof
    cheat
QED

val _ = set_fixity "RINSERT" (Infixr 490)

(* ‘RINSERT’ inserts one more pair into an existing relation *)
Definition RINSERT :
    $RINSERT r R = \x y. R x y \/ (x = FST r /\ y = SND r)
End

(* Theorem 2.1.40 [1, p.35] (Hilbert-Post completeness of beta+eta) *)
Theorem lameta_completeness :
    !M N. has_bnf M /\ has_bnf N ==>
          lameta M N \/ ~consistent (conversion ((M,N) RINSERT (beta RUNION eta)))
Proof
    cheat
QED

val _ = export_theory();
val _ = html_theory "complete";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
