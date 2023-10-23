(*---------------------------------------------------------------------------*
 * completenessScript.sml: The completeness of Lambda terms
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory llistTheory
     ltreeTheory pathTheory posetTheory hurdUtils;

open binderLib termTheory appFOLDLTheory chap2Theory chap3Theory
     head_reductionTheory standardisationTheory solvableTheory pure_dBTheory;

open boehm_treeTheory;

val _ = new_theory "completeness";

val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)



val _ = export_theory();
val _ = html_theory "completeness";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
