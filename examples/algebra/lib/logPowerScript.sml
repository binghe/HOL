(* ------------------------------------------------------------------------- *)
(* Integer Functions Computation.                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* ------------------------------------------------------------------------- *)

open jcLib;

open pred_setTheory arithmeticTheory dividesTheory gcdTheory logrootTheory
     numberTheory combinatoricsTheory;

(* declare new theory at start *)
val _ = new_theory "logPower";


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
