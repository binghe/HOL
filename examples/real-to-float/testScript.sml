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

(* ‘frac x’ to mean x mod 1 or ‘x - flr x’, the fractional part of x [1]

   NOTE: For the negative numbers, here it is defined in the same way as for
   positive numbers [2] (thus ‘frac 3.6 = 0.6’ but ‘frac ~3.6 = 0.4’.)

   TODO: move this definition and supporting theorems to intrealTheory.
 *)
Definition frac_def :
    frac x = x - real_of_int (INT_FLOOR x)
End

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory ();

(* References:

   [1] https://en.wikipedia.org/wiki/Fractional_part
   [2] Graham, R.L., Knuth, D.E., Patashnik, O.: Concrete Mathematics. 2nd Eds.
       Addison-Wesley Publishing Company (1994).
 *)
