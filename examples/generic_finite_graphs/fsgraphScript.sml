(* ------------------------------------------------------------------------- *)
(* Sample theorems for finite simple graphs (:'a fsgraph) [1]                *)
(* Authors: Chun Tian                                                        *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pathTheory genericGraphTheory;

val _ = new_theory "fsgraph";

(* ------------------------------------------------------------------------- *)
(*  Definitions                                                              *)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(*  Theorems                                                                 *)
(* ------------------------------------------------------------------------- *)

val  _ = export_theory();

(* References:

  [1] Reinhard Diestel, Graph Theory, Fourth Edition (2010, Second, corrected
      printing 2012), Springer Science+Business Media, 2012.
 *)
