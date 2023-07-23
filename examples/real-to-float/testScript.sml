(*---------------------------------------------------------------------------*
 * testScript.sml:                                                           *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open intLib realLib fcpLib wordsLib hurdUtils;

open whileTheory optionTheory arithmeticTheory realTheory listTheory fcpTheory
     intrealTheory wordsTheory binary_ieeeTheory machine_ieeeTheory
     stringTheory;

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val _ = new_theory "test";

val _ = numLib.prefer_num();

val _ = monadsyntax.enable_monadsyntax(); (* enable do/od syntax *)
val _ = List.app monadsyntax.enable_monad ["list", "option"];

val test_monad = “do
     list <- some_monad;
     assert(list <> []);
     return (HD list + 1)
od”;

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory ();

(* References:

   [1] https://en.wikipedia.org/wiki/Fractional_part
   [2] Graham, R.L., Knuth, D.E., Patashnik, O.: Concrete Mathematics. 2nd Eds.
       Addison-Wesley Publishing Company (1994).
 *)
