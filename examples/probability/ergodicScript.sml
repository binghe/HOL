(* ========================================================================= *)
(* The Ergodic Theory                                                        *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory sigma_algebraTheory measureTheory probabilityTheory;

val _ = new_theory "ergodic";

Definition measure_preserving_trans :
    measure_preserving_trans p t <=> t IN measure_preserving p (p :'a m_space)
End

Theorem measure_preserving_trans_def :
    !p t. measure_preserving_trans p t <=>
          t IN measurable (p_space p,events p) (p_space p,events p) /\
          !s. s IN events p ==>
              prob p (PREIMAGE t s INTER p_space p) = prob p s
Proof
    rw [measure_preserving_trans, measure_preserving_def,
        p_space_def, events_def, prob_def]
QED

Theorem measure_preserving_trans_measurable :
    !p t. measure_preserving_trans p t ==>
          t IN (p_space p -> p_space p) /\
          !s. s IN events p ==> PREIMAGE t s INTER p_space p IN events p
Proof
    rw [measure_preserving_trans_def, IN_MEASURABLE]
QED

val _ = export_theory ();
val _ = html_theory "ergodic";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).

 *)
