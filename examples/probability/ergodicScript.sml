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
(*  Infinite-dimensional Borel space [1, p.178]                              *)
(* ------------------------------------------------------------------------- *)

Definition cylinder_sets_def :
    cylinder_sets (h :num -> extreal set) (N :num) =
      {f :num -> extreal | !i. i < N ==> f i IN h i}
End

Definition Borel_inf0_def :
    Borel_inf0 = sigma UNIV {cylinder_sets h N |
                             !i. i < N ==> ?a. h i = {x | x < Normal a}}
End

Definition Borel_inf1_def :
    Borel_inf1 = sigma UNIV {cylinder_sets h N |
                             !i. i < N ==> h i IN subsets Borel}
End

Definition list_rectangle_def :
    list_rectangle (h :num -> 'a set) N =
      {v | LENGTH v = N /\ !i. i < N ==> EL i v IN h i}
End
Overload rectangle = “list_rectangle”

Definition cylinder2list_def :
    cylinder2list c N = IMAGE (\f. GENLIST f N) c
End

Definition sigma_lists_def :
   sigma_lists B N = sigma_functions (list_rectangle (\n. space B) N) (\n. B) EL (count N)
End

Definition Borel_lists_def :
   Borel_lists N = sigma_lists Borel N
End

Definition Borel_inf2_def :
    Borel_inf2 = sigma UNIV {c | ?N. cylinder2list c N IN subsets (Borel_lists N)}
End

Overload Borel_inf = “Borel_inf0”

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
  [3] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).

 *)
