(* ------------------------------------------------------------------------- *)
(* Ring Maps                                                                 *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringMap";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory arithmeticTheory dividesTheory gcdTheory gcdsetTheory
     numberTheory combinatoricsTheory;

open monoidTheory groupTheory;

(* val _ = load "ringUnitTheory"; *)
open ringTheory ringUnitTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
