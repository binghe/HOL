(* ========================================================================= *)
(*   Probability Density Function Theory (normal_rvTheory)                   *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*   Enriched by Chun TIAN (The Australian National University, 2024)        *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory numLib logrootTheory hurdUtils pred_setLib
     pred_setTheory realTheory realLib seqTheory transcTheory real_sigmaTheory
     iterateTheory topologyTheory real_topologyTheory derivativeTheory;

open util_probTheory sigma_algebraTheory extrealTheory real_borelTheory
     measureTheory borelTheory lebesgueTheory martingaleTheory
     probabilityTheory;

val _ = new_theory "distribution"; (* was: "normal_rv" *)

(* ------------------------------------------------------------------------- *)
(*  Weak convergence (of distributions)                                      *)
(* ------------------------------------------------------------------------- *)

(* See, e.g., [2, p.117] *)
Definition weak_converge_def :
    weak_converge fi (f :extreal measure) =
    !g. g bounded_on UNIV /\ g o Normal continuous_on UNIV ==>
        ((\n. integral (space Borel,subsets Borel,fi n) g) -->
          integral (space Borel,subsets Borel,f) g) sequentially
End
Overload "-->" = “weak_converge”

Theorem converge_in_dist_alt_weak :
    !p X Y. prob_space p /\
           (!n. random_variable (X n) p Borel) /\ random_variable Y p Borel ==>
           ((X --> Y) (in_distribution p) <=>
            (\n. distribution p (X n)) --> distribution p Y)
Proof
    rw [converge_in_dist, weak_converge_def, expectation_def, distribution_distr,
        random_variable_def, p_space_def, events_def, prob_space_def]
 (* applying integral_distr *)
 >> Know ‘!Z. Z IN Borel_measurable (measurable_space p) /\
              g IN Borel_measurable Borel ==>
              integral (space Borel,subsets Borel,distr p Z) g = integral p (g o Z)’
 >- (rpt STRIP_TAC \\
     MP_TAC (Q.SPECL [‘p’, ‘Borel’, ‘Z’, ‘g’]
                     (INST_TYPE [beta |-> “:extreal”] integral_distr)) \\
     rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 (* TODO: extreal-valued continuous function is Borel-measurable *)
 >> cheat
QED

(* ------------------------------------------------------------------------- *)
(*  PDF                                                                      *)
(* ------------------------------------------------------------------------- *)

(* This definition comes from HVG's original work (real-based)

   cf. probabilityTheory.prob_density_function_def (extreal-based)
 *)
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
     rw [m_space_lborel, indicator_fn_def, mul_rone, mul_rzero, le_refl])
 >> Rewr'
 >> POP_ORW >> rw [space_borel]
QED

(* ------------------------------------------------------------------------- *)
(*  Normal density                                                           *)
(* ------------------------------------------------------------------------- *)

(* NOTE: ‘normal_density m s’ is a function of “:real -> real”, where m is the
   expectation, s is the standard deviation.
 *)
Definition normal_density :
    normal_density mu sig x =
      (1 / sqrt (2 * pi * sig pow 2)) * exp (-((x - mu) pow 2) / (2 * sig pow 2))
End

Overload std_normal_density = “normal_density 0 1”

Theorem std_normal_density_def :
    !x. std_normal_density x = (1 / sqrt (2 * pi)) * exp (-(x pow 2) / 2)
Proof
    RW_TAC std_ss [normal_density]
 >> SIMP_TAC real_ss [REAL_SUB_RZERO, POW_ONE]
QED

Theorem normal_density_nonneg :
    !mu sig x. 0 <= normal_density mu sig x
Proof
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LE, GSYM REAL_INV_1OVER, REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC real_ss [REAL_LE_LT, PI_POS],
   ALL_TAC] THEN
  SIMP_TAC real_ss [REAL_LE_POW2]
QED

Theorem normal_density_pos :
    !mu sig. 0 < sig ==> 0 < normal_density mu sig x
Proof
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LT, GSYM REAL_INV_1OVER, REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC real_ss [PI_POS], ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT >> art []
QED

Theorem normal_density_continuous_on :
    !mu sig s. normal_density mu sig continuous_on s
Proof
    rpt GEN_TAC
 >> ‘normal_density mu sig =
       (\x. 1 / sqrt (2 * pi * sig pow 2) *
            exp (-((x - mu) pow 2) / (2 * sig pow 2)))’
       by rw [normal_density, FUN_EQ_THM]
 >> POP_ORW
 >> HO_MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE)
 >> reverse CONJ_TAC
 >- (‘$* (1 / sqrt (2 * pi * sig pow 2)) = \x. (1 / sqrt (2 * pi * sig pow 2)) * x’
       by rw [FUN_EQ_THM] >> POP_ORW \\
     HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL >> rw [CONTINUOUS_ON_ID])
 >> HO_MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE)
 >> reverse CONJ_TAC
 >- rw [CONTINUOUS_ON_EXP]
 >> REWRITE_TAC [real_div, Once REAL_MUL_COMM]
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL
 >> REWRITE_TAC [Once REAL_NEG_MINUS1]
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_POW
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_SUB
 >> rw [CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST]
QED

Theorem in_measurable_borel_normal_density :
    !mu sig. normal_density mu sig IN borel_measurable borel
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC in_borel_measurable_continuous_on
 >> rw [normal_density_continuous_on]
QED

Theorem IN_MEASURABLE_BOREL_normal_density :
    !mu sig. Normal o normal_density mu sig IN Borel_measurable borel
Proof
    rpt GEN_TAC
 >> HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL'
 >> rw [sigma_algebra_borel, in_measurable_borel_normal_density]
QED

Overload ext_normal_density = “\mu sig. Normal o normal_density mu sig o real”

Definition normal_measure_def :
    normal_measure mu sig s =
      pos_fn_integral ext_lborel (\x. ext_normal_density mu sig x * indicator_fn s x)
End

Definition normal_rv_def :
    normal_rv X p mu sig <=> real_random_variable X p /\
                             !s. s IN subsets Borel ==>
                                 distribution p X s = normal_measure mu sig s
End

(* TODO *)
Theorem extreal_exp_alt :
    ∀x :extreal. exp x = ext_suminf (λn. inv (&FACT n) * x pow n)
Proof
    cheat
QED

val _ = export_theory ();
val _ = html_theory "distribution";

(* References:

  [1] Qasim, M.: Formalization of Normal Random Variables, Concordia University (2016).
  [2] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Edition).
      World Scientific Publishing Company (2006).

 *)
