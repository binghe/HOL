(* ------------------------------------------------------------------------- *)
(* Ideals in Ring                                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringIdeal";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory gcdsetTheory numberTheory
     combinatoricsTheory;

open ringTheory;
open groupTheory;
open monoidTheory;
open ringMapTheory;

open ringUnitTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
