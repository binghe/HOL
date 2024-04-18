(* ------------------------------------------------------------------------- *)
(* Count Helper.                                                             *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperCount";

(* ------------------------------------------------------------------------- *)

open arithmeticTheory pred_setTheory gcdsetTheory numberTheory
     combinatoricsTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
