(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "Gauss";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory dividesTheory logrootTheory
     gcdTheory gcdsetTheory numberTheory combinatoricsTheory primeTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
