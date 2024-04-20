(* ------------------------------------------------------------------------- *)
(* Monoid Order and Invertibles                                              *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "monoidOrder";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory dividesTheory gcdTheory numberTheory
     primeTheory;

(* val _ = load "monoidTheory"; *)
open monoidTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();
val _ = html_theory "monoidOrder";

(*===========================================================================*)
