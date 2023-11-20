(*---------------------------------------------------------------------------*
 * chap15_1Script.sml: Beta-Eta-reductions (Chapter 15.1 of [1])             *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

open pred_setTheory termTheory chap3Theory;

val _ = new_theory "chap15_1";

val _ = export_theory ();

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
   [2] Takahashi, M.: Parallel Reductions in λ-Calculus. Inf. Comput. (1995).
 *)
