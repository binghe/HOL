open HolKernel boolLib bossLib Parse;

open dep_rewrite pred_setTheory bagTheory gcdsetTheory;

open numberTheory monoidTheory monoidMapTheory;

(* Theory about folding a monoid (or group) operation over a bag of elements *)

val _ = new_theory"gbag";

val _ = export_theory();
