(* ------------------------------------------------------------------------- *)
(* Mobius Function and Inversion.                                            *)
(* ------------------------------------------------------------------------- *)
(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "Mobius";

(* ------------------------------------------------------------------------- *)

open jcLib;

open pred_setTheory listTheory prim_recTheory arithmeticTheory dividesTheory
     gcdTheory gcdsetTheory;

open numberTheory combinatoricsTheory;

open GaussTheory;
open EulerTheory;

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
