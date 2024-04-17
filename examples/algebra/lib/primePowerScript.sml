(* ------------------------------------------------------------------------- *)
(* Prime Power                                                               *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "primePower";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open arithmeticTheory pred_setTheory listTheory numberTheory dividesTheory
     gcdTheory gcdsetTheory logrootTheory optionTheory rich_listTheory
     listRangeTheory;

open logPowerTheory triangleTheory EulerTheory combinatoricsTheory;


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
