(* ------------------------------------------------------------------------- *)
(* Helper Theorems - a collection of useful results -- for Sets.             *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperSet";

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
