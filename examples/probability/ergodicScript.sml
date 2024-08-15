(* ========================================================================= *)
(* The Ergodic Theory                                                        *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory sigma_algebraTheory measureTheory probabilityTheory;

val _ = new_theory "ergodic";

(* Definition 5.1.3 [2, p.34] (measure-preserving transformation).
   Author: Chun Tian
 *)
Definition mpt_def :
    mpt p t <=> t IN measure_preserving p (p :'a m_space)
End

(* Author: Chun Tian *)
Theorem mpt_thm :
    !p t. mpt p t <=>
          t IN measurable (p_space p,events p) (p_space p,events p) /\
          !s. s IN events p ==>
              prob p (PREIMAGE t s INTER p_space p) = prob p s
Proof
    rw [mpt_def, measure_preserving_def, p_space_def, events_def, prob_def]
QED

(* Author: Chun Tian *)
Theorem mpt_measurable :
    !p t. t IN measurable (p_space p,events p) (p_space p,events p) <=>
          t IN (p_space p -> p_space p) /\
          !s. s IN events p ==> PREIMAGE t s INTER p_space p IN events p
Proof
    rw [mpt_thm, IN_MEASURABLE]
QED

val _ = export_theory ();
val _ = html_theory "ergodic";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).

 *)
