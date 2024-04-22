(* ------------------------------------------------------------------------- *)
(* Divisibility in Ring                                                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringDivides";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory dep_rewrite numberTheory
     combinatoricsTheory bagTheory containerTheory;

open ringIdealTheory;
open ringUnitTheory;
open ringTheory;
open groupTheory;
open monoidTheory;

open ringMapTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
