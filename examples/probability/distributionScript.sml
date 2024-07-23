(* ========================================================================= *)
(*                                                                           *)
(*    Probability Density Function and Normal Random Variables [1]           *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*    Ported to latest HOL4 by Chun Tian <binghe.lisp@gmail.com> (2021)      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory numLib logrootTheory hurdUtils pred_setTheory
     pred_setLib;

open realTheory realLib seqTheory transcTheory real_sigmaTheory iterateTheory
     real_topologyTheory;

open util_probTheory sigma_algebraTheory extrealTheory real_borelTheory
     measureTheory borelTheory lebesgueTheory probabilityTheory;

val _ = new_theory "distribution";

(* moved here from probabilityTheory *)
Definition PDF_def :
    PDF p X = RN_deriv (distribution p X) lborel
End

Theorem PDF_LE_POS :
    !p X. prob_space p /\ random_variable X p borel /\
          distribution p X << lborel ==> !x. 0 <= PDF p X x
Proof
    rpt STRIP_TAC
 >> `measure_space (space borel, subsets borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space, prob_space_def,
                     sigma_algebra_borel]
 >> ASSUME_TAC sigma_finite_lborel
 >> ASSUME_TAC measure_space_lborel
 >> MP_TAC (ISPECL [“lborel”, “distribution (p :'a m_space) (X :'a -> real)”]
                   Radon_Nikodym')
 >> RW_TAC std_ss [m_space_lborel, sets_lborel, space_borel, IN_UNIV]
 >> fs [PDF_def, RN_deriv_def, m_space_def, measurable_sets_def,
        m_space_lborel, sets_lborel, space_borel]
 >> SELECT_ELIM_TAC >> METIS_TAC []
QED

Theorem EXPECTATION_PDF_1 : (* was: INTEGRAL_PDF_1 *)
    !p X. prob_space p /\ random_variable X p borel /\
          distribution p X << lborel ==>
          expectation lborel (PDF p X) = 1
Proof
    rpt STRIP_TAC
 >> `prob_space (space borel, subsets borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space, sigma_algebra_borel]
 >> NTAC 2 (POP_ASSUM MP_TAC) >> KILL_TAC
 >> RW_TAC std_ss [prob_space_def, p_space_def, m_space_def, measure_def,
                   expectation_def]
 >> ASSUME_TAC sigma_finite_lborel
 >> ASSUME_TAC measure_space_lborel
 >> MP_TAC (ISPECL [“lborel”, “distribution (p :'a m_space) (X :'a -> real)”]
                   Radon_Nikodym')
 >> RW_TAC std_ss [m_space_lborel, sets_lborel, m_space_def, measure_def,
                   space_borel, IN_UNIV]
 >> fs [PDF_def, RN_deriv_def, m_space_def, measurable_sets_def,
        m_space_lborel, sets_lborel, space_borel]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC >- METIS_TAC []
 >> Q.X_GEN_TAC `g`
 >> RW_TAC std_ss [density_measure_def]
 >> POP_ASSUM (MP_TAC o Q.SPEC `space borel`)
 >> Know `space borel IN subsets borel`
 >- (`sigma_algebra borel` by PROVE_TAC [sigma_algebra_borel] \\
     PROVE_TAC [sigma_algebra_def, ALGEBRA_SPACE])
 >> RW_TAC std_ss []
 >> Know `integral lborel g = pos_fn_integral lborel g`
 >- (MATCH_MP_TAC integral_pos_fn >> art [])
 >> Rewr'
 >> Know `pos_fn_integral lborel g =
          pos_fn_integral lborel (\x. g x * indicator_fn (space borel) x)`
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     RW_TAC std_ss [m_space_lborel, indicator_fn_def, mul_rone, mul_rzero, le_refl])
 >> Rewr'
 >> POP_ORW
 >> rw [space_borel]
QED

(* alias for internal porting purposes *)
Theorem INTEGRAL_PDF_1[local] = EXPECTATION_PDF_1

(* ------------------------------------------------------------------------- *)
(* normal_density                                                            *)
(* ------------------------------------------------------------------------- *)

(* m = mean, s = standard deviation (s^2 = variance) *)
Definition normal_density_def :
    normal_density m s x =
      (1 / sqrt (2 * pi * s pow 2)) * exp (-((x - m) pow 2) / (2 * s pow 2))
End

Overload std_normal_density = “normal_density 0 1”



(* END *)
val _ = export_theory();
val _ = html_theory "distribution";

(* References:

  [1] Qasim, M.: Formalization of Normal Random Variables, Concordia University (2016).
 *)
