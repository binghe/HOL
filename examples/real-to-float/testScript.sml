(*---------------------------------------------------------------------------*
 * testScript.sml:                                                           *
 *                                                                           *
 * A template theory script suitable for Holmake. If you are going to use it *
 * for theory "x", you must change the name of this file to "xScript.sml",   *
 * and the argument to "new_theory" below must be changed to be "x".         *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open numLib fcpTheory fcpLib wordsLib realLib intLib hurdUtils;

open arithmeticTheory realTheory intrealTheory wordsTheory binary_ieeeTheory
     machine_ieeeTheory;

(* set the default number type to :num *)
val _ = prefer_num ();

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val _ = new_theory "test";

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory ();

(* References:

   [1] https://en.wikipedia.org/wiki/Fractional_part
   [2] Graham, R.L., Knuth, D.E., Patashnik, O.: Concrete Mathematics. 2nd Eds.
       Addison-Wesley Publishing Company (1994).
 *)
