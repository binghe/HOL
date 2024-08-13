(* ========================================================================= *)
(* The Ergodic Theory                                                        *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open sigma_algebraTheory measureTheory probabilityTheory;

val _ = new_theory "ergodic";



val _ = export_theory ();
val _ = html_theory "ergodic";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).

 *)
