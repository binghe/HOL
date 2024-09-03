(* ========================================================================= *)
(*   Probability Density Function Theory (and Normal Random Variables)       *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory numLib logrootTheory hurdUtils pred_setLib
     pred_setTheory realTheory realLib seqTheory transcTheory real_sigmaTheory
     iterateTheory topologyTheory real_topologyTheory;

open util_probTheory sigma_algebraTheory extrealTheory real_borelTheory
     measureTheory borelTheory lebesgueTheory probabilityTheory;

val _ = new_theory "distribution"; (* was: "normal_rv" *)

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

(*
val normal_density_nonneg = store_thm ("normal_density_nonneg",
  ``!mu sig x. 0 <= normal_density mu sig x``,
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LE, GSYM REAL_INV_1OVER, REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC real_ss [REAL_LE_LT, PI_POS],
   ALL_TAC] THEN
  SIMP_TAC real_ss [REAL_LE_POW2]);

val normal_density_pos = store_thm ("normal_density_pos",
  ``!mu sig. 0 < sig ==> 0 < normal_density mu sig x``,
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LT, GSYM REAL_INV_1OVER, REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC real_ss [PI_POS], ALL_TAC] THEN
  SIMP_TAC std_ss [POW_2, REAL_POASQ] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_SIMP_TAC std_ss []);

(* normal_density IN measurable borel Borel *)

val restrict_space = new_definition ("restrict_space",
  ``restrict_space M sp = 
    (sp INTER m_space M, 
     IMAGE (\a. a INTER sp) (measurable_sets M), 
     measure M)``);

val space_restrict_space = store_thm ("space_restrict_space",
  ``!M sp. m_space (restrict_space M sp) = (sp INTER m_space M)``,
  SIMP_TAC std_ss [restrict_space, m_space_def]);

val space_restrict_space2 = store_thm ("space_restrict_space2",
  ``!M sp. measure_space M /\ sp IN measurable_sets M ==> 
         (m_space (restrict_space M sp) = sp)``,
  RW_TAC std_ss [restrict_space, m_space_def] THEN
  `sp SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
  ASM_SET_TAC []);

val sets_restrict_space = store_thm ("sets_restrict_space",
  ``!M sp. measurable_sets (restrict_space M sp) = IMAGE (\a. a INTER sp) (measurable_sets M)``,
  RW_TAC std_ss [restrict_space, measurable_sets_def]);

val borel_measurable_continuous_on1 = store_thm ("borel_measurable_continuous_on1",
  ``!f. f continuous_on UNIV ==> f IN borel_measurable borel``,
  RW_TAC std_ss [borel_measurable] THEN
  Q.ABBREV_TAC `M = (space borel, subsets borel, (\x:real->bool. 0))` THEN
  Q_TAC SUFF_TAC `f IN measurable (m_space M, measurable_sets M) borel` THENL
  [Q.UNABBREV_TAC `M` THEN SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [SPACE], ALL_TAC] THEN
  MATCH_MP_TAC borel_measurableI THEN CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `topology_hvg$Open {x | x IN UNIV /\ f x IN s}` THENL
   [DISCH_TAC,
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC std_ss [OPEN_UNIV]] THEN
   Q.UNABBREV_TAC `M` THEN SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [PREIMAGE_def, space_borel, INTER_UNIV] THEN
   MATCH_MP_TAC borel_open THEN ASM_SET_TAC [],
   ALL_TAC] THEN
  Q.UNABBREV_TAC `M` THEN SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
  RW_TAC std_ss [measure_space_def] THENL
  [SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
   SIMP_TAC std_ss [positive_def, measurable_sets_def, measure_def, le_refl],
   ALL_TAC] THEN
  SIMP_TAC std_ss [countably_additive_def, measurable_sets_def, measure_def] THEN
  SIMP_TAC std_ss [o_DEF, suminf_0]);

val IN_MEASURABLE_BOREL_normal_density = store_thm ("IN_MEASURABLE_BOREL_normal_density",
  ``!mu sig. (\x. Normal (normal_density mu sig x)) IN
            measurable (m_space lborel, measurable_sets lborel) Borel``,
  RW_TAC std_ss [normal_density, GSYM extreal_mul_def] THEN
  MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
  Q.EXISTS_TAC `(\x. Normal (exp (-((x - mu) pow 2) / (2 * sig pow 2))))` THEN
  Q.EXISTS_TAC `(1 / sqrt (2 * pi * sig pow 2))` THEN CONJ_TAC THENL
  [RW_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [GSYM space_borel, SPACE, sigma_algebra_borel], ALL_TAC] THEN
  SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `(\x. Normal ((\x. exp (-((x - mu) pow 2) / (2 * sig pow 2))) x)) IN
                    measurable (m_space lborel,measurable_sets lborel) Borel` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN MATCH_MP_TAC borel_IMP_Borel THEN
  SIMP_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN 
  SIMP_TAC std_ss [GSYM space_borel, SPACE, GSYM borel_measurable] THEN 
  MATCH_MP_TAC borel_measurable_continuous_on1 THEN
  Q_TAC SUFF_TAC `(\x. exp ((\x. -((x - mu) pow 2) / (2 * sig pow 2)) x)) 
                       continuous_on univ(:real)` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE) THEN
  SIMP_TAC std_ss [CONTINUOUS_ON_EXP, real_div] THEN
  Q_TAC SUFF_TAC `(\x. -inv (2 * sig pow 2) * (\x. ((x - mu) pow 2)) x) 
                       continuous_on univ(:real)` THENL
  [SIMP_TAC real_ss [REAL_MUL_COMM], ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  ONCE_REWRITE_TAC [METIS [] ``(x - mu) = (\x:real. x - mu) x``] THEN
  MATCH_MP_TAC CONTINUOUS_ON_POW THEN SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `(\x. (\x. x) x - (\x. mu) x) continuous_on univ(:real)` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  SIMP_TAC std_ss [CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST]);
  
val _ = hide "normal_pmeasure";

val normal_pmeasure = new_definition("normal_pmeasure",``normal_pmeasure mu sig =
     (\A. if A IN measurable_sets lborel then
          pos_fn_integral lborel
            (\x. (\x. Normal (normal_density mu sig x)) x *
               indicator_fn A x) else 0)``);

val _ = hide "normal_rv";

val normal_rv = new_definition("normal_rv",``normal_rv X p mu sig =
   (random_variable X p borel /\
   (measurable_distr p X = normal_pmeasure mu sig))``);

*)

val _ = export_theory();
val _ = html_theory "distribution";

(* References:

  [1] Qasim, M.: Formalization of Normal Random Variables, Concordia University (2016).
 *)
