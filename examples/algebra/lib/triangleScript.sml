(* ------------------------------------------------------------------------- *)
(* Leibniz Harmonic Triangle                                                 *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "triangle";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open arithmeticTheory pred_setTheory listTheory rich_listTheory relationTheory
     dividesTheory gcdTheory gcdsetTheory listRangeTheory numberTheory
     combinatoricsTheory;

open binomialTheory EulerTheory; (* for upto_by_count *)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
