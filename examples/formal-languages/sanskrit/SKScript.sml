(*---------------------------------------------------------------------------*
 *   The Siddhānta Kaumudī (settled moonlight) of Bhaṭṭoji Dīkṣta in HOL4    *
 *                                                                           *
 *                  Chun Tian, School of Computing,                          *
 *                Australian National University (2024)                      *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val theory_name = "SK";
val _ = new_theory theory_name;

(* Load the fxp library for XML processing *)
val cwd = OS.FileSys.getDir();
val _ = OS.FileSys.chDir "fxp";
structure Word8 = PolyWord8;
val _ = use "poly-fxpLib.ML";
val _ = OS.FileSys.chDir cwd;

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory();
val _ = html_theory theory_name;
