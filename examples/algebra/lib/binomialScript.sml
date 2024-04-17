(* ------------------------------------------------------------------------- *)
(* Binomial coefficients and expansion.                                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "binomial";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory rich_listTheory arithmeticTheory dividesTheory
     gcdTheory numberTheory combinatoricsTheory;

(* ------------------------------------------------------------------------- *)
(* Binomial scripts in HOL:
C:\jc\www\ml\hol\info\Hol\examples\miller\RSA\summationScript.sml
C:\jc\www\ml\hol\info\Hol\examples\miller\RSA\powerScript.sml
C:\jc\www\ml\hol\info\Hol\examples\miller\RSA\binomialScript.sml
*)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
