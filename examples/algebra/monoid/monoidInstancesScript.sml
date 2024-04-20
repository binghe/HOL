(* ------------------------------------------------------------------------- *)
(* Applying Monoid Theory: Monoid Instances                                  *)
(* ------------------------------------------------------------------------- *)

(*

Monoid Instances
===============
The important ones:

 Zn -- Addition Modulo n, n > 0.
Z*n -- Multiplication Modulo n, n > 1.

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "monoidInstances";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory arithmeticTheory dividesTheory gcdTheory listTheory
     rich_listTheory logrootTheory numberTheory combinatoricsTheory;

open monoidTheory monoidMapTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
