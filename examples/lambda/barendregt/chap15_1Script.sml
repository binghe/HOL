(*---------------------------------------------------------------------------*
 * chap15_1Script.sml: Beta-Eta-reductions (Chapter 15.1 of [1])             *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

open pred_setTheory termTheory chap3Theory;

val _ = new_theory "chap15_1";

(* Theorem 2.1.36 [1, p.34] aka Corollary 15.1.5 [1, p.386]

   NOTE: This theorem is not necessary if the antecedent of Theorem 2.1.40 is
         replaced by ‘has_benf M /\ has_benf N’.

   Used by: has_bnf_imp_lameta_complete
 *)
Theorem has_benf_iff_has_bnf :
    !M. has_benf M <=> has_bnf M
Proof
    cheat
QED

val _ = export_theory ();

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
   [2] Takahashi, M.: Parallel Reductions in λ-Calculus. Inf. Comput. (1995).
 *)
