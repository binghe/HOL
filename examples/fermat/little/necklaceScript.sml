open HolKernel boolLib bossLib Parse;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory rich_listTheory gcdsetTheory
     logrootTheory numberTheory combinatoricsTheory;

(* ------------------------------------------------------------------------- *)

(* declare new theory at start *)
val _ = new_theory "necklace";

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
