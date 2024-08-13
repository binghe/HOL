(* ========================================================================= *)
(* The Ergodic Theory                                                        *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open sigma_algebraTheory measureTheory probabilityTheory;

val _ = new_theory "ergodic";

Definition measure_preserving_transformation_def :
    measure_preserving_transformation (p :'a m_space) (t :'a -> 'a) <=>
      t IN measurable (p_space p,events p) (p_space p,events p) /\
      !s. s IN events p ==>
          prob p (PREIMAGE t s INTER p_space p) = prob p s
End

Overload mp_trans = “measure_preserving_transformation”

val _ = export_theory ();
val _ = html_theory "ergodic";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).

 *)
