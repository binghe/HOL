(* ========================================================================= *)
(* The Central Limit Theorems                                                *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open sigma_algebraTheory measureTheory borelTheory probabilityTheory
     distributionTheory;

val _ = new_theory "central_limit";



val _ = export_theory ();
val _ = html_theory "central_limit";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).

 *)
