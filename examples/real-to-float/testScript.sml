(*---------------------------------------------------------------------------*
 * dragonScript.sml:                                                         *
 *                                                                           *
 * A template theory script suitable for Holmake. If you are going to use it *
 * for theory "x", you must change the name of this file to "xScript.sml",   *
 * and the argument to "new_theory" below must be changed to be "x".         *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib fcpTheory fcpLib wordsTheory wordsLib realTheory
     realLib intrealTheory intLib;

open binary_ieeeTheory machine_ieeeTheory;

(* set the default number type to :num *)
val _ = prefer_num ();

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val _ = new_theory "test";

(* ‘fraction x’ to mean x mod 1 or ‘x - flr x’, the fractional part of x *)
Definition fraction_def :
    fraction x = x - real_of_int (INT_FLOOR x)
End

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory ();
