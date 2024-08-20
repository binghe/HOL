(* ========================================================================= *)
(* The Ergodic Theory                                                        *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory;

open sigma_algebraTheory borelTheory measureTheory probabilityTheory

open stochastic_processTheory;

val _ = new_theory "ergodic";

(* Definition 5.1.3 [2, p.34] (measure-preserving transformation) *)
Definition mpt_def :
    mpt p t <=> t IN measure_preserving p (p :'a m_space)
End

Theorem mpt_thm :
    !p t. mpt p t <=>
          t IN measurable (p_space p,events p) (p_space p,events p) /\
          !s. s IN events p ==>
              prob p (PREIMAGE t s INTER p_space p) = prob p s
Proof
    rw [mpt_def, measure_preserving_def, p_space_def, events_def, prob_def]
QED

Theorem mpt_measurable :
    !p t. t IN measurable (p_space p,events p) (p_space p,events p) <=>
          t IN (p_space p -> p_space p) /\
          !s. s IN events p ==> PREIMAGE t s INTER p_space p IN events p
Proof
    rw [mpt_thm, IN_MEASURABLE]
QED

(* ------------------------------------------------------------------------- *)
(*  Stationary process                                                       *)
(* ------------------------------------------------------------------------- *)

(* Definition 5.1.1 [2, p.33] *)
Definition stationary_process_def :
    stationary_process p (X :num -> 'a -> extreal) <=>
    !B k. B IN subsets Borel_inf ==>
          prob p {x | x IN p_space p /\ (\i. X i x) IN B} =
          prob p {x | x IN p_space p /\ (\i. X (k + i) x) IN B}
End

val _ = export_theory ();
val _ = html_theory "ergodic";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Billingsley, P.: Probability and Measure (3rd Edition). Wiley-Interscience (1995).

 *)
