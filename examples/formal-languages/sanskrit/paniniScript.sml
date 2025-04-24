(*---------------------------------------------------------------------------*
 *                    Traditional Sanskrit Grammar                           *
 *                                                                           *
 *                  Chun Tian, School of Computing,                          *
 *                Australian National University (2024)                      *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open SKTheory;

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val theory_name = "panini";
val _ = new_theory theory_name;



(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory();
val _ = html_theory theory_name;
