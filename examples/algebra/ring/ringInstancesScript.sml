(* ------------------------------------------------------------------------- *)
(* Applying Ring Theory: Ring Instances                                      *)
(* ------------------------------------------------------------------------- *)

(*

Ring Instances
===============
The important ones:

Z_n -- Arithmetic under Modulo n.

*)
(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringInstances";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open prim_recTheory pred_setTheory arithmeticTheory dividesTheory gcdTheory
     numberTheory combinatoricsTheory whileTheory primeTheory;

open monoidTheory groupTheory ringTheory ringMapTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
