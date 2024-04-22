(* ------------------------------------------------------------------------- *)
(* Ring Theory -- Ideal and Quotient Ring.                                   *)
(* ------------------------------------------------------------------------- *)

(*

Ideal
=====
additive subgroup with multiplicative closure with all elements.

Quotient Ring
==============
R/I where I is an ideal.

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "quotientRing";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory dividesTheory pred_setTheory numberTheory
     combinatoricsTheory;

open monoidTheory groupTheory ringTheory ringIdealTheory;
open ringMapTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
