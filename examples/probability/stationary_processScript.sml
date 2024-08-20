(* ========================================================================= *)
(* Stationary Process (Wide Sense)                                           *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory;

open sigma_algebraTheory borelTheory measureTheory probabilityTheory;

open stochastic_processTheory;

val _ = new_theory "stationary_process";

(* ------------------------------------------------------------------------- *)
(*  Stationary process                                                       *)
(* ------------------------------------------------------------------------- *)

val _ = export_theory ();
val _ = html_theory "stationary_process";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).

 *)
