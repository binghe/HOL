(* ========================================================================= *)
(* The Central Limit Theorems                                                *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open pairTheory combinTheory optionTheory prim_recTheory arithmeticTheory
     pred_setTheory pred_setLib topologyTheory hurdUtils;

open realTheory realLib iterateTheory seqTheory transcTheory real_sigmaTheory
     real_topologyTheory realaxTheory extreal_baseTheory derivativeTheory;

open extrealTheory sigma_algebraTheory measureTheory real_borelTheory borelTheory
     lebesgueTheory martingaleTheory probabilityTheory;

open distributionTheory stochastic_processTheory;

val _ = new_theory "central_limit";

val _ = intLib.deprecate_int();
val _ = ratLib.deprecate_rat();

(* ------------------------------------------------------------------------- *)
(*  Liapunov inequality                                                      *)
(* ------------------------------------------------------------------------- *)

Theorem liapounov_ineq_lemma:
    !m u p. measure_space m ∧
            measure m (m_space m) < PosInf ∧
            1 < p ∧ p < PosInf ∧
            u ∈ lp_space p m  ⇒
            ∫⁺ m (λx. abs (u x)) ≤ seminorm p m u * ((measure m (m_space m)) powr (1 - inv(p)))
Proof
    rpt STRIP_TAC
 >> ‘p ≠ PosInf’ by rw [lt_imp_ne]
 >> ‘0 < p’ by METIS_TAC [lt_trans, lt_01]
 >> ‘p ≠ 0’ by rw [lt_imp_ne]
 >> ‘inv(p) ≠ NegInf ∧ inv(p) ≠ PosInf’ by rw [inv_not_infty]
 >> ‘p ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> ‘0 < inv (p)’ by METIS_TAC [inv_pos']
 >> ‘inv(p) ≠ 0’ by rw [lt_imp_ne]
 >> Know ‘inv (p) < 1’
 >- (‘1 * inv(p) < p * inv(p)’ by rw [lt_rmul] \\
     ‘p / p = p * inv(p)’ by rw [div_eq_mul_rinv] \\
     ‘p / p = 1’ by METIS_TAC [div_refl_pos] \\
     ‘inv(p) = 1 * inv(p)’ by rw [] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘0 < 1 - inv(p)’ by rw [sub_zero_lt]
 >> ‘1 - inv(p) ≠ 0’ by rw [lt_imp_ne]
 >> Know ‘1 - inv(p) ≠ NegInf’
 >- (‘∃a. inv(p) = Normal a’ by METIS_TAC [extreal_cases] \\
     ‘∃c. Normal 1 - Normal a = Normal c’ by METIS_TAC [extreal_sub_def] \\
     Know ‘1 - inv(p) = Normal c’
     >- (‘1 = Normal 1’ by rw[] >> rw[]) >> rw [])
 >> DISCH_TAC
 >> Know ‘1 - inv(p) ≠ PosInf’
 >- (‘∃b. inv(p) = Normal b’ by METIS_TAC [extreal_cases]
     >> ‘∃d. Normal 1 - Normal b = Normal d’ by METIS_TAC [extreal_sub_def]
     >> Know ‘1 - inv(p) = Normal d’
     >- (‘1 = Normal 1’ by rw [] >> rw []) >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘q = inv(1- inv(p))’
 >> Know ‘inv(p) + inv(q) = 1’
 >- (rw [Abbr ‘q’, inv_inv] \\
     rw [sub_add2, inv_not_infty])
 >> DISCH_TAC
 >> Know ‘0 < q’
 >- (Q.UNABBREV_TAC ‘q’ \\
     MATCH_MP_TAC inv_pos' \\
     CONJ_TAC
     >- (MATCH_MP_TAC sub_zero_lt \\
         MP_TAC (Q.SPECL [‘p’, ‘1’] inv_lt_antimono) \\
         simp [lt_01, inv_one]) \\
    rw [])
 >> DISCH_TAC
 >> Know ‘q ≠ PosInf’
 >- (Q.UNABBREV_TAC ‘q’ \\
     rw [inv_not_infty])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘m’, ‘u’, ‘λx. 1’, ‘p’, ‘q’]
            Hoelder_inequality')
 >> impl_tac
 >> simp[]
 >- (rw [lp_space_def]
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' \\
         rw [measure_space_def])
     >> ‘abs 1 = 1’ by rw [abs_refl]
     >> rw []
     >> Know ‘1 powr q = 1’
     >- (MATCH_MP_TAC one_powr \\
         MATCH_MP_TAC lt_imp_le \\
         rw [])
     >> DISCH_TAC
     >> simp []
     >> MP_TAC (Q.SPECL [‘m’, ‘1’] pos_fn_integral_const)
     >> impl_tac
     >> simp []
     >> DISCH_TAC
     >> ‘1 = Normal 1’ by rw []
     >> rw []
     >> ‘measure m (m_space m) ≠ +∞’ by rw [lt_imp_ne]
     >> rw [mul_not_infty])
 >> DISCH_TAC
 >> Know ‘seminorm q m (λx. 1) = ((measure m (m_space m)) powr (1 - inv(p)))’
 >- (rw [seminorm_def] \\
     Know ‘inv (q) = 1 - inv (p)’
     >- (Q.UNABBREV_TAC ‘q’ \\
         rw [inv_inv]) \\
     DISCH_TAC \\
     rw [] \\
    ‘abs 1 = 1’ by rw [abs_refl] \\
     rw [] \\
     Know ‘1 powr q = 1’
     >- (MATCH_MP_TAC one_powr \\
         MATCH_MP_TAC lt_imp_le \\
         rw []) \\
     DISCH_TAC  \\
    ‘1 = Normal 1’ by rw [] \\
     simp [] \\
     Know ‘∫⁺ m (λx. Normal 1) =  measure m (m_space m)’
     >- (MP_TAC (Q.SPECL [‘m’, ‘1’] pos_fn_integral_const) \\
         impl_tac \\
         simp [] \\
        ‘1 * measure m (m_space m) =  measure m (m_space m) ’ by rw [mul_lone] \\
         simp [] \\
         DISCH_TAC \\
         METIS_TAC []) \\
     DISCH_TAC \\
     simp [])
 >> DISCH_TAC
 >> METIS_TAC []
QED

Theorem liapounov_ineq:
    !m u r r'. measure_space m /\ u IN lp_space r m ∧  u IN lp_space r' m ∧
               measure m (m_space m) < PosInf ∧
               0 < r ∧
               r < r' ∧
               r' < PosInf  ==>
               seminorm r m u ≤ seminorm r' m u * (measure m (m_space m)) powr (inv(r) - inv(r'))
Proof
    rpt STRIP_TAC
 >> ‘0 < r'’ by METIS_TAC [lt_trans]
 >> ‘r < PosInf’ by METIS_TAC [lt_trans]
 >> ‘r ≠ 0 ∧ r' ≠ 0’ by rw [lt_imp_ne]
 >> ‘r ≠ PosInf ∧ r' ≠ PosInf ’ by rw [lt_imp_ne]
 >> ‘NegInf < r ∧ NegInf < r'’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> ‘r ≠ NegInf ∧ r' ≠ NegInf’ by METIS_TAC [lt_imp_ne]
 >> Know ‘inv r <> PosInf /\ inv r <> NegInf’
 >- (MATCH_MP_TAC inv_not_infty >> art []) >> DISCH_TAC
 >> Know ‘inv r' <> PosInf /\ inv r' <> NegInf’
 >- (MATCH_MP_TAC inv_not_infty >> art []) >> DISCH_TAC
 >> ‘0 < inv (r) ∧ 0 < inv (r')’ by METIS_TAC [inv_pos']
 >> ‘inv(r) ≠ 0 ∧ inv(r') ≠ 0’ by rw [lt_imp_ne]
 >> ‘inv(r') * r ≠ NegInf ∧ inv(r') * r ≠ PosInf’ by METIS_TAC [mul_not_infty2]
 >>  ‘r' * inv(r) ≠ NegInf ∧ r' * inv(r) ≠ PosInf’ by METIS_TAC [mul_not_infty2]
 >> Know ‘1 < r' * r⁻¹’
 >- (‘r * inv(r) < r' * inv(r)’ by rw [lt_rmul] \\
     ‘r / r = r * inv(r)’ by rw [div_eq_mul_rinv] \\
     ‘r / r = 1’ by METIS_TAC [div_refl_pos] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘0 < r' * inv(r)’ by METIS_TAC [lt_01, lt_trans]
 >> MP_TAC (Q.SPECL [‘m’, ‘λx. abs (u x) powr r’, ‘r'* inv(r)’]
            liapounov_ineq_lemma)
 >> impl_tac
 >> simp[]
 >- (CONJ_TAC
     >- (‘∃a. r' * inv(r) = Normal a’ by METIS_TAC [extreal_cases] \\
          rw[lt_infty])
     >> gs [lp_space_alt_finite]
     >> CONJ_TAC
     >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR \\
         CONJ_TAC
         >- (‘u IN measurable (m_space m,measurable_sets m) Borel’
                by gs [lp_space_def]) \\
         CONJ_TAC
         >- (MATCH_MP_TAC lt_imp_le \\
             rw []) \\
             simp [])
      >> ‘∀x. abs (abs (u x) powr r) = abs (u x) powr r’ by rw [abs_pos, powr_pos, abs_refl]
      >> POP_ORW
      >> ‘∀x. (abs (u x) powr r) powr (r' * r⁻¹) = abs (u x) powr (r * (r' * r⁻¹))’ by rw [powr_powr]
      >> POP_ORW
      >> ‘r * (r' * r⁻¹) = r * inv(r) * r'’ by PROVE_TAC [mul_comm, mul_assoc]
      >> ‘inv(r) * r = r / r’ by rw [GSYM div_eq_mul_linv]
      >> ‘r * inv(r) = inv(r) * r’ by PROVE_TAC [mul_comm]
      >> ‘r / r = 1’ by METIS_TAC [div_refl_pos]
      >> FULL_SIMP_TAC std_ss [mul_lone])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘mu =  measure m (m_space m)’
 >> Know ‘0 ≤ mu’
 >- (Q.UNABBREV_TAC ‘mu’ \\
     MATCH_MP_TAC MEASURE_POSITIVE \\
     simp[] \\
     METIS_TAC[MEASURE_SPACE_MSPACE_MEASURABLE])
 >> DISCH_TAC
 >> ‘∀x. abs (abs (u x) powr r) = abs (u x) powr r’ by rw [abs_pos, powr_pos, abs_refl]
 >> FULL_SIMP_TAC std_ss []
 >> Know ‘seminorm (r' * r⁻¹) m (λx. abs (u x) powr r) = (seminorm r' m u) powr r’
 >- (rw [seminorm_def] \\
     ‘∀x. (abs (u x) powr r) powr (r' * r⁻¹) =  abs (u x) powr (r * (r' * r⁻¹))’ by rw [abs_pos, powr_powr] \\
     POP_ORW \\
     ‘∀x. abs (u x) powr (r * (r' * r⁻¹)) = abs (u x) powr (r⁻¹ * r * r')’ by PROVE_TAC [mul_assoc, mul_comm] \\
     POP_ORW \\
     ‘∀x. abs (u x) powr (r⁻¹ * r * r') = abs (u x) powr r'’ by rw [mul_linv_pos, mul_lone] \\
     POP_ORW \\
     ‘inv(r' * inv(r)) = inv(r') * r’ by rw [inv_mul, inv_inv] \\
     POP_ORW \\
     Know ‘0 ≤ ∫⁺ m (λx. abs (u x) powr r')’
     >- (MATCH_MP_TAC pos_fn_integral_pos \\
         simp[] \\
         METIS_TAC [abs_pos, powr_pos]) \\
     DISCH_TAC \\
     ‘∫⁺ m (λx. abs (u x) powr r') powr (r'⁻¹ * r) = (∫⁺ m (λx. abs (u x) powr r') powr r'⁻¹) powr r’
         by rw [GSYM powr_powr])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> Q.ABBREV_TAC ‘A =  ∫⁺ m (λx. abs (u x) powr r)’
 >> Q.ABBREV_TAC ‘B =  seminorm r' m u powr r * mu powr (1 − (r' * r⁻¹)⁻¹)’
 >> simp []
 >> Know ‘A powr inv(r) ≤ B powr inv(r)’
 >- (Know ‘0 ≤ A’
     >- (rw [Abbr ‘A’] \\
         MATCH_MP_TAC pos_fn_integral_pos \\
         simp[] \\
         METIS_TAC [abs_pos, powr_pos]) \\
     DISCH_TAC \\
     Know ‘0 ≤ B’
     >- (rw[Abbr ‘B’] \\
        ‘0 ≤ seminorm r' m u’ by PROVE_TAC [seminorm_pos] \\
        ‘0 ≤ seminorm r' m u powr r’ by PROVE_TAC [powr_pos] \\
        ‘0 ≤  mu powr (1 − (r' * r⁻¹)⁻¹)’ by PROVE_TAC [powr_pos] \\
         METIS_TAC [le_mul]) \\
     DISCH_TAC \\
     METIS_TAC [GSYM powr_mono_eq])
 >> DISCH_TAC
 >> Q.UNABBREV_TAC ‘A’
 >> Q.UNABBREV_TAC ‘B’
 >> ‘∫⁺ m (λx. abs (u x) powr r) powr inv(r) = seminorm r m u’ by rw [seminorm_def]
 >> FULL_SIMP_TAC std_ss []
 >> Q.ABBREV_TAC ‘C = seminorm r' m u’
 >> Q.ABBREV_TAC ‘D = mu powr (1 − (r' * r⁻¹)⁻¹)’
 >> simp[]
 >> Know ‘(C powr r * D) powr r⁻¹ = C * D powr inv(r)’
 >- (‘0 ≤ C’ by PROVE_TAC [seminorm_pos] \\
     ‘0 ≤ C powr r’ by PROVE_TAC [powr_pos] \\
     ‘0 ≤ D’ by METIS_TAC [powr_pos] \\
     ‘(C powr r * D) powr r⁻¹ = (C powr r) powr r⁻¹ * D powr inv(r)’ by METIS_TAC [mul_powr] \\
     ‘(C powr r) powr r⁻¹ = C powr (r * inv(r))’ by METIS_TAC [powr_powr] \\
     ‘C powr (r * inv(r)) = C’ by METIS_TAC [GSYM div_eq_mul_rinv, div_refl_pos, powr_1] \\
      simp [])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> Q.UNABBREV_TAC ‘C’
 >> Q.UNABBREV_TAC ‘D’
 >> Know ‘(mu powr (1 − (r' * r⁻¹)⁻¹)) powr r⁻¹ =
           mu powr (r⁻¹ − r'⁻¹)’
 >- (Know ‘r * inv(r') < 1’
     >- (‘r * inv(r') < r' * inv(r')’ by rw [lt_rmul] \\
         ‘r' / r' = r' * inv(r')’ by rw [div_eq_mul_rinv] \\
         ‘r' / r' = 1’ by METIS_TAC [div_refl_pos] \\
          METIS_TAC []) \\
     DISCH_TAC \\
    ‘r * r'⁻¹ = r'⁻¹ * r’ by METIS_TAC [mul_comm] \\
     FULL_SIMP_TAC std_ss [] \\
    ‘(r' * r⁻¹)⁻¹ = inv(r') * r’ by METIS_TAC [inv_mul, inv_inv, mul_comm] \\
     simp [] \\
    ‘0 < 1 - inv(r') * r’ by METIS_TAC [sub_zero_lt] \\
     Know ‘1 − r'⁻¹ * r ≠ PosInf’
     >- (‘∃b. r'⁻¹ * r  = Normal b’ by METIS_TAC [extreal_cases] \\
          rw [sub_not_infty]) \\
     DISCH_TAC \\
    ‘(mu powr (1 − r'⁻¹ * r)) powr r⁻¹ = mu powr ((1 − r'⁻¹ * r) * inv(r))’
         by METIS_TAC [powr_powr] \\
     POP_ORW \\
    ‘(1 − r'⁻¹ * r) * r⁻¹ =  r⁻¹ * (1 − r'⁻¹ * r)’ by METIS_TAC [mul_comm] \\
     POP_ORW \\
    ‘r⁻¹ * (1 − r'⁻¹ * r) = ((r⁻¹) * 1) - (r⁻¹ * (r'⁻¹ * r))’ by rw [sub_ldistrib] \\
     POP_ORW \\
    ‘r⁻¹ * (r'⁻¹ * r) = r⁻¹ * r * r'⁻¹’ by METIS_TAC [mul_assoc] \\
     POP_ORW \\
    ‘inv(r) * r = r / r’ by rw [GSYM div_eq_mul_linv] \\
    ‘r / r = 1’ by METIS_TAC [div_refl_pos] \\
     FULL_SIMP_TAC std_ss [] \\
     POP_ORW \\
    ‘r⁻¹ * 1 − 1 * r'⁻¹ = r⁻¹ − r'⁻¹’ by rw [mul_rone] \\
     POP_ORW \\
     rw [])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss[]
QED

Theorem liapounov_ineq_rv:
    !p u r r'. prob_space p /\ u IN lp_space r p ∧  u IN lp_space r' p ∧
               0 < r ∧
               r < r' ∧
               r' < PosInf  ==>
               seminorm r p u ≤ seminorm r' p u
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [prob_space_def]
 >> MP_TAC (Q.SPECL [‘p’, ‘u’, ‘r’, ‘r'’]
            liapounov_ineq)
 >> impl_tac
 >> simp []
 >> DISCH_TAC
 >> Know ‘0 < r⁻¹ − r'⁻¹’
 >- (‘0 < r'’ by METIS_TAC [lt_trans] \\
     ‘inv(r') < inv(r)’ by METIS_TAC [inv_lt_antimono] \\
     METIS_TAC [sub_zero_lt])
 >> DISCH_TAC
 >> Know ‘1 powr (r⁻¹ − r'⁻¹) = 1’
 >- (MATCH_MP_TAC one_powr \\
     MATCH_MP_TAC lt_imp_le \\
     rw [])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> ‘seminorm r' p u * 1 = seminorm r' p u’ by rw [mul_rone]
 >> FULL_SIMP_TAC std_ss []
QED

(* ------------------------------------------------------------------------- *)
(*  Add to BorelTheory                                                       *)
(* ------------------------------------------------------------------------- *)

Theorem IN_MEASURABLE_BOREL_SUM_CMUL:
    ∀a f g s z.
      FINITE s ∧ sigma_algebra a ∧ (∀i. i ∈ s ⇒ f i ∈ Borel_measurable a) ∧
      (∀x. x ∈ space a ⇒ g x = Normal z * ∑ (λi. f i x) s) ⇒
      g ∈ Borel_measurable a
Proof
    RW_TAC std_ss []
 >> Cases_on `Normal z = 0`
 >- METIS_TAC [IN_MEASURABLE_BOREL_CONST, mul_lzero]
 >> Q.ABBREV_TAC ‘h = λx. ∑ (λi. (f: β -> α -> extreal) i x) s’
 >> ‘∀x. h x = ∑ (λi. f i x) s’ by rw[Abbr ‘h’]
 >> MP_TAC (Q.SPECL [‘a’, ‘(f: 'b -> 'a -> extreal)’, ‘h’, ‘s’]
             IN_MEASURABLE_BOREL_SUM')
 >> impl_tac
 >- (METIS_TAC [])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘a’, ‘h’, ‘λx. Normal z * h x’, ‘z’]
             IN_MEASURABLE_BOREL_CMUL)
 >> impl_tac
 >- (METIS_TAC [])
 >> ‘!x. x IN space a ==> (Normal z * h x = g x)’ by rw [Abbr ‘h’]
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘a’, ‘g’, ‘λx. Normal z * h x’]
             IN_MEASURABLE_BOREL_EQ')
 >> impl_tac
 >> BETA_TAC
 >- (METIS_TAC [])
 >> simp []
QED

Theorem IN_BOREL_MEASURABLE_POW :
    ∀a n f g.
      sigma_algebra a ∧ f ∈ Borel_measurable a ∧
      (∀x. x ∈ space a ⇒ g x = f x pow n) ∧
      (∀x. x ∈ space a ⇒ f x ≠ −∞ ∧ f x ≠ +∞) ⇒
      g ∈ Borel_measurable a
Proof
    STRIP_TAC
 >> Induct_on ‘n’
 >- (FULL_SIMP_TAC std_ss [pow_0] \\
     METIS_TAC [IN_MEASURABLE_BOREL_CONST])
 >> rpt STRIP_TAC
 >> fs [extreal_pow]
 >> irule IN_MEASURABLE_BOREL_MUL
 >> simp []
 >> qexistsl [‘f’, ‘λx. f x pow n’]
 >> ‘∀x. x ∈ space a ⇒ f x pow n ≠ −∞ ∧ f x pow n ≠ +∞’ by rw [pow_not_infty]
 >> simp []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> qexists ‘f’
 >> simp []
QED

(********************************* DELETE ******************************)

Theorem MEASURABLE_SPACE_PROD :
  !M1 M2. measure_space M1 /\ measure_space M2 ==>
          measurable_space (M1 CROSS M2) =
          measurable_space M1 CROSS measurable_space M2
Proof
  cheat
QED

(***********************************************************************)

(* ------------------------------------------------------------------------- *)
(*  Add to probabilityTheory                                                 *)
(* ------------------------------------------------------------------------- *)

Theorem real_to_extreal_rv[local]:
    ∀p X. prob_space p ∧ random_variable X p borel ⇒
          real_random_variable (Normal o X) p
Proof
    rw [real_random_variable_def, random_variable_def]
 >> irule IN_MEASURABLE_BOREL_IMP_BOREL'
 >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, prob_space_def, p_space_def, events_def, measure_space_def]
QED

Theorem extreal_to_real_rv[local]:
    ∀p X. prob_space p ∧
        real_random_variable (Normal o X) p ⇒
        random_variable X p borel
Proof
    rw [real_random_variable_def, random_variable_def]
 >> MP_TAC (Q.SPECL [‘(p_space p,events p)’, ‘Normal o X’]
            in_borel_measurable_from_Borel)
 >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, prob_space_def, p_space_def, events_def, measure_space_def]
 >> rw [o_DEF]
 >> METIS_TAC []
QED

Theorem real_random_variable_equiv:
    ∀p X. prob_space p ⇒
          (real_random_variable (Normal o X) p ⇔
             random_variable X p borel)
Proof
    rw [real_random_variable_def, random_variable_def,
        AND_INTRO_THM, EQ_IMP_THM]
 >- (MP_TAC (Q.SPECL [‘(p_space p,events p)’, ‘Normal o X’]
             in_borel_measurable_from_Borel) \\
     FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, prob_space_def,
                           p_space_def, events_def, measure_space_def] \\
     rw [o_DEF] \\
     METIS_TAC [])
 >> irule IN_MEASURABLE_BOREL_IMP_BOREL'
 >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, prob_space_def, p_space_def, events_def, measure_space_def]
QED

Theorem real_random_variable_abs:
    ∀p X.
          prob_space p ∧ real_random_variable X p ⇒
          real_random_variable (λx. abs (X x)) p
Proof
    rpt STRIP_TAC
 >> fs [real_random_variable, prob_space_def, p_space_def, events_def]
 >> CONJ_TAC
 (* (λx. abs (X x)) ∈ Borel_measurable (measurable_space p) *)
 >- (irule IN_MEASURABLE_BOREL_ABS \\
     FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, measure_space_def] \\
     qexists ‘X’ \\
     simp [])
 (* ∀x. x ∈ m_space p ⇒ abs (X x) ≠ −∞ ∧ abs (X x) ≠ +∞ *)
 >> Q.X_GEN_TAC ‘x’
 >> DISCH_TAC
 >> ‘?z. X x = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw[extreal_abs_def]
QED

Theorem real_random_variable_exp:
  ∀p X r. prob_space p ∧ real_random_variable X p ⇒ real_random_variable (λx. exp (X x)) p
Proof
  rpt GEN_TAC
  >> simp [real_random_variable, prob_space_def, p_space_def, events_def]
  >> STRIP_TAC
  >> CONJ_TAC
  >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP >>  qexists_tac ‘X’ >> rw [])
  >> Q.X_GEN_TAC ‘x’
  >> DISCH_TAC
  >> ‘?z. X x = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW
  >> rw[extreal_exp_def]
QED

Theorem real_random_variable_exp_normal:
  ∀p X r s. prob_space p ∧ real_random_variable X p ⇒
            real_random_variable (λx. exp (Normal s * X x)) p
Proof
  rw [real_random_variable_cmul, real_random_variable_exp]
QED

Theorem lim_null:
  ∀f l.
    (∃N. ∀n. N ≤ n ⇒ f n ≠ +∞ ∧ f n ≠ −∞) ∧ l ≠ +∞ ∧ l ≠ −∞ ⇒
    ((f --> l) sequentially ⇔ ((λn. (real (f n) − real l)) --> 0) sequentially)
Proof
  rpt STRIP_TAC
  >> (MP_TAC o (Q.SPECL [‘sequentially’, ‘real o f’, ‘real l’]) o
             (INST_TYPE [alpha |-> ``:num``])) real_topologyTheory.LIM_NULL
  >> simp [o_DEF]
  >> DISCH_THEN (REWRITE_TAC o wrap o SYM)
  >> MATCH_MP_TAC (REWRITE_RULE [o_DEF] extreal_lim_sequentially_eq)
  >> simp []
  >> qexists ‘N’
  >> simp []
QED

Theorem m_space_ext_lborel[simp] :
    m_space ext_lborel = space Borel
Proof
    rw [m_space_def, ext_lborel_def]
QED

(*independent_identical_distribution*)
Definition iid_def :
  iid p X E A J ⇔ identical_distribution p X E J ∧
                  pairwise_indep_vars p X A J
End

Theorem real_random_variable_sum_cdiv :
    ∀p X s n. prob_space p ∧
              (∀i. real_random_variable (X i) p) ∧
              0 < s n ∧ s n ≠ +∞ ∧ s n ≠ −∞  ⇒
              real_random_variable ((λx. ∑ (λi. X i x) (count n) / s n)) p
Proof
    rpt STRIP_TAC
 >> BETA_TAC
 >> ‘∃r. Normal r = s n’ by METIS_TAC [extreal_cases]
 >> ‘0 < r’ by POP_ASSUM (fs o wrap o SYM)
 >> Know ‘∀x. ∑ (λi. X i x) (count n) / s n = ∑ (λi. X i x) (count n) / Normal r’
 >- (qx_gen_tac ‘x’ \\
     POP_ORW \\
     rw [])
 >> DISCH_TAC
 >> Know ‘real_random_variable (λx. ∑ (λi. X i x) (count n)) p’
 >- (HO_MATCH_MP_TAC real_random_variable_sum \\
     rw [])
 >> DISCH_TAC
 >> Know ‘real_random_variable (λx. ∑ (λi. X i x) (count n) / Normal r) p’
 >- (HO_MATCH_MP_TAC real_random_variable_cdiv \\
     simp [] \\
     ‘r ≠ 0’ by METIS_TAC [REAL_LT_IMP_NE] \\
     fs [])
 >> DISCH_TAC
 >> METIS_TAC []
QED

Theorem IN_PSPACE_PROD_SIGMA :
    ∀a b z. z ∈ p_space (a × b) ⇔ FST z ∈ p_space a ∧ SND z ∈ p_space b
Proof
  simp [p_space_def, prod_measure_space_def]
QED

Theorem real_random_variable_pair_components_finite :
    ∀p q r X Y (n :num).
      prob_space p ∧
      prob_space q ∧ r = p CROSS q ∧
      (∀i. i < n ⇒ real_random_variable (X i) p) ∧
      (∀i. i < n ⇒ real_random_variable (Y i) q) ⇒
      (∀i. i < n ⇒
           real_random_variable (X i ∘ FST) r ∧
           real_random_variable (Y i ∘ SND) r)
Proof
    NTAC 7 STRIP_TAC
 >> Know ‘(p_space (p × q),events (p × q)) =
          (p_space p,events p) × (p_space q,events q)’
 >- (fs [p_space_def, events_def, prob_space_def] \\
     irule MEASURABLE_SPACE_PROD \\
     simp [])
 >> DISCH_TAC
 >> rw []
 >- (fs [real_random_variable_def, random_variable_def] \\
     CONJ_TAC
      >- (MATCH_MP_TAC MEASURABLE_COMP \\
          qexists ‘(p_space p,events p)’ \\
          simp [] \\
          irule MEASURABLE_FST \\
          METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA]) \\
      simp [IN_PSPACE_PROD_SIGMA])
 >> fs [real_random_variable_def, random_variable_def]
 >> CONJ_TAC
 >- (MATCH_MP_TAC MEASURABLE_COMP \\
     qexists ‘(p_space q,events q)’ \\
     simp [] \\
     irule MEASURABLE_SND \\
     METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> simp [IN_PSPACE_PROD_SIGMA]
QED

Theorem random_variable_pair_components_finite :
    ∀p q r X Y (n :num).
      prob_space p ∧
      prob_space q ∧ r = p CROSS q ∧
      (∀i. i < n ⇒ real_random_variable (X i) p) ∧
      (∀i. i < n ⇒ random_variable (Y i) q Borel) ⇒
      (∀i. i < n ⇒
           real_random_variable (X i ∘ FST) r ∧
           random_variable (Y i ∘ SND) r Borel)
Proof
    NTAC 7 STRIP_TAC
 >> Know ‘(p_space (p × q),events (p × q)) =
          (p_space p,events p) × (p_space q,events q)’
 >- (fs [p_space_def, events_def, prob_space_def] \\
     irule MEASURABLE_SPACE_PROD \\
     simp [])
 >> DISCH_TAC
 >> rw []
 >- (fs [real_random_variable_def, random_variable_def] \\
     CONJ_TAC
     >- (MATCH_MP_TAC MEASURABLE_COMP \\
         qexists ‘(p_space p,events p)’ \\
         simp [] \\
         irule MEASURABLE_FST \\
        METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA]) \\
     simp [IN_PSPACE_PROD_SIGMA])
 >> fs [random_variable_def]
 >> MATCH_MP_TAC MEASURABLE_COMP
 >>  qexists ‘(p_space q,events q)’
 >> simp []
 >> irule MEASURABLE_SND
 >> METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA]
QED

(* ------------------------------------------------------------------------- *)
(*  Expectation                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem expectation_alt_add[local]:
  ∀p X Y.
          prob_space p ∧
          real_random_variable X p ∧
          integrable p X ∧
          real_random_variable Y p ∧
          integrable p Y ⇒
          expectation p (λx. X x + Y x) = expectation p X + expectation p Y
Proof
    rw [expectation_def, prob_space_def, real_random_variable_def, p_space_def]
 >> MATCH_MP_TAC integral_add
 >> simp []
QED

Theorem expectation_add:
    ∀p f g.
      prob_space p ∧ integrable p f ∧ integrable p g ⇒
      expectation p (λx. f x + g x) = expectation p f + expectation p g
Proof
  rw [expectation_def, prob_space_def]
  >> MATCH_MP_TAC integral_add'
  >> simp []
QED

Theorem expectation_add'[local]:
  ∀p X Y.
          prob_space p ∧
          random_variable X p borel ∧
          integrable p (Normal o X) ∧
          random_variable Y p borel ∧
          integrable p (Normal o Y) ⇒
          expectation p (Normal o (λx. X x + Y x)) =
          expectation p (Normal o X) + expectation p (Normal o Y)
Proof
    rw []
 >> MP_TAC (Q.SPECL [‘p’, ‘Normal o X’, ‘Normal o Y’]
            expectation_alt_add)
 >> simp []
 >> STRIP_TAC
 >> Know ‘expectation p (λx. Normal (X x) + Normal (Y x)) =
          expectation p (Normal ∘ (λx. X x + Y x))’
 >- (MATCH_MP_TAC expectation_cong \\
     rw[extreal_add_eq])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [integrable_def]
 >> ‘real_random_variable (Normal ∘ X) p’
     by rw [real_random_variable_def, random_variable_def, p_space_def, events_def]
 >> ‘real_random_variable (Normal ∘ Y) p’
     by rw [real_random_variable_def, random_variable_def, p_space_def, events_def]
 >> FULL_SIMP_TAC std_ss []
QED

Theorem expectation_sub:
  ∀p X Y.
          prob_space p ∧
          real_random_variable X p ∧
          integrable p X ∧
          real_random_variable Y p ∧
          integrable p Y ⇒
          expectation p (λx. X x - Y x) = expectation p X - expectation p Y
Proof
    rw [expectation_def, prob_space_def, real_random_variable_def, p_space_def]
 >> MATCH_MP_TAC integral_sub
 >> simp []
QED

Theorem expectation_sub':
  ∀p X Y.
          prob_space p ∧
          random_variable X p borel ∧
          integrable p (Normal o X) ∧
          random_variable Y p borel ∧
          integrable p (Normal o Y) ⇒
          expectation p (Normal o (λx. X x - Y x)) =
          expectation p (Normal o X) - expectation p (Normal o Y)
Proof
    rw []
 >> MP_TAC (Q.SPECL [‘p’, ‘Normal o X’, ‘Normal o Y’]
            expectation_sub)
 >> simp []
 >> STRIP_TAC
 >> Know ‘expectation p (λx. Normal (X x) - Normal (Y x)) =
          expectation p (Normal ∘ (λx. X x - Y x))’
 >- (MATCH_MP_TAC expectation_cong \\
     rw[extreal_sub_eq])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [integrable_def]
 >> ‘real_random_variable (Normal ∘ X) p’
     by rw [real_random_variable_def, random_variable_def, p_space_def, events_def]
 >> ‘real_random_variable (Normal ∘ Y) p’
     by rw [real_random_variable_def, random_variable_def, p_space_def, events_def]
 >> FULL_SIMP_TAC std_ss []
QED

Theorem expectation_mono:
    ∀p X Y.
            prob_space p ∧
            real_random_variable X p ∧
            integrable p X ∧
            real_random_variable Y p ∧
            integrable p Y ∧
            (∀x. x IN p_space p ⇒ X x ≤ Y x) ⇒
            expectation p X ≤ expectation p Y
Proof
    rw []
 >> Q.ABBREV_TAC ‘Z = λx. Y x - X x’
 >> ‘∀x. x IN p_space p ⇒ Z x = Y x - X x’ by rw [Abbr ‘Z’]
 >> ‘real_random_variable Z p’ by rw [Abbr ‘Z’, real_random_variable_sub]
 >> Know ‘∀x. x IN p_space p ⇒ 0 ≤ Z x’
 >- (fs [Abbr ‘Z’, real_random_variable_def] \\
     METIS_TAC [sub_zero_le])
 >> DISCH_TAC
 >> Know ‘integrable p Z’
 >- (fs [Abbr ‘Z’] \\
     MP_TAC (Q.SPECL [‘p’, ‘Y’, ‘X’]
             integrable_sub') \\
     fs [prob_space_def])
 >> DISCH_TAC
 >> Know ‘0 ≤ expectation p Z’
 >- (irule expectation_pos \\
     simp [])
 >> DISCH_TAC
 >> Know ‘∀x. x IN p_space p ⇒ Z x + X x = Y x’
 >- (fs [Abbr ‘Z’, real_random_variable_def] \\
     GEN_TAC \\
     STRIP_TAC \\
     METIS_TAC [sub_add])
 >> DISCH_TAC
 >> Know ‘expectation p (λx. Z x + X x) =
          expectation p (λx. Y x)’
 >- (MATCH_MP_TAC expectation_cong \\
     rw [])
 >> DISCH_TAC
 >> Know ‘expectation p (λx. Z x + X x) =
          expectation p Z + expectation p X’
 >- (MATCH_MP_TAC expectation_alt_add \\
     simp [])
 >> rpt STRIP_TAC
 >> ‘expectation p (λx. Y x) =
     expectation p Z + expectation p X’ by fs []
 >> ‘expectation p (λx. Y x) = expectation p Y’ by METIS_TAC []
 >> FULL_SIMP_TAC std_ss []
 >> POP_ORW
 >> ‘expectation p X ≠ PosInf ∧ expectation p X ≠ NegInf’
    by METIS_TAC [expectation_finite]
 >> ‘expectation p Z ≠ PosInf ∧ expectation p Z ≠ NegInf’
    by METIS_TAC [expectation_finite]
 >> ‘expectation p Z + expectation p X =
     expectation p X + expectation p Z’ by METIS_TAC [add_comm]
 >> POP_ORW
 >> METIS_TAC [le_addr_imp]
QED

Theorem expectation_mono':
    ∀p X Y.
            prob_space p ∧
            random_variable X p borel ∧
            integrable p (Normal o X) ∧
            random_variable Y p borel ∧
            integrable p (Normal o Y) ∧
            (∀x. X x ≤ Y x) ⇒
            expectation p (Normal o X) ≤ expectation p (Normal o Y)
Proof
    rw []
 >> MP_TAC (Q.SPECL [‘p’, ‘Normal o X’, ‘Normal o Y’]
            expectation_mono)
 >> fs []
 >> STRIP_TAC
 >> ‘real_random_variable (Normal ∘ X) p’ by METIS_TAC [real_to_extreal_rv]
 >> ‘real_random_variable (Normal ∘ Y) p’ by METIS_TAC [real_to_extreal_rv]
 >> fs []
QED

Theorem expectation_mono_alt:
    ∀p f g.
            prob_space p ∧ integrable p f ∧ integrable p g ∧
            (∀x. x ∈ p_space p ⇒ f x ≤ g x) ⇒
            expectation p f ≤ expectation p g
Proof
    rw [prob_space_def, p_space_def, expectation_def]
 >> MATCH_MP_TAC integral_mono >> art []
QED


(* ------------------------------------------------------------------------- *)
(*  Moment generating function                                               *)
(* ------------------------------------------------------------------------- *)

Definition mgf_def:
   mgf p X s =  expectation p (\x. exp (Normal s * X x))
End

Theorem mgf_0:
    !p X. prob_space p ==> mgf p X 0 = 1
Proof
    RW_TAC std_ss [mgf_def, mul_lzero, exp_0, normal_0]
 >> MATCH_MP_TAC expectation_const >> art[]
QED

Theorem mgf_linear:
    ∀p X a b s. prob_space p ∧ real_random_variable X p ∧
                integrable p (λx. exp (Normal (a * s) * X x))  ⇒
                mgf p (λx.( Normal a * X x) + Normal b) s =  (exp (Normal s * Normal b)) * mgf p X (a * s)
Proof
    rw [mgf_def, real_random_variable_def]
 >> Know ‘ expectation p (λx. exp (Normal s * ((Normal a * X x) + Normal b)))
         = expectation p (λx. exp ((Normal s * (Normal a * X x)) + Normal s * Normal b))’
 >- (MATCH_MP_TAC expectation_cong  >> rw[] >> AP_TERM_TAC
     >> ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases] >> rw[]
     >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq] >> rw[add_ldistrib_normal2]) >> Rewr'
 >> Know ‘expectation p
         (λx. exp (Normal s * (Normal a * X x) + Normal s * Normal b)) =
          expectation p (λx. (exp (Normal s * (Normal a * X x))) * exp (Normal s * Normal b))’
 >- (MATCH_MP_TAC expectation_cong
     >> rw[exp_add]
     >> ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases]>> rw[]
     >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq] >> rw[]
     >> ‘∃e. Normal s * Normal d = Normal e’ by METIS_TAC [extreal_mul_eq] >> rw[]
     >> ‘∃f. Normal s * Normal b = Normal f’ by METIS_TAC [extreal_mul_eq] >> rw[exp_add]) >> Rewr'
 >> ‘∃g. exp (Normal s * Normal b) = Normal g’ by  METIS_TAC [extreal_mul_eq, normal_exp]
 >> rw[]
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm]
 >> rw [mul_assoc, extreal_mul_eq]
 >> HO_MATCH_MP_TAC expectation_cmul
 >> ASM_REWRITE_TAC []
QED

Theorem mgf_sum:
    !p X Y s . prob_space p ∧ real_random_variable X p  ∧
               real_random_variable Y p  ∧
               indep_vars p X Y Borel Borel ∧
               mgf p (\x. X x + Y x) s ≠ PosInf ∧
               mgf p X s ≠ PosInf ∧
               mgf p Y s ≠ PosInf  ==>
               mgf p (\x. X x + Y x) s = mgf p X s * mgf p Y s
Proof
    rw [mgf_def, real_random_variable_def]
 >> Know ‘expectation p (\x. exp (Normal s * (X x + Y x))) =
          expectation p (\x. exp ((Normal s * X x) + (Normal s * Y x)))’
 >-(MATCH_MP_TAC expectation_cong >> rw[] >> AP_TERM_TAC
    >> MATCH_MP_TAC add_ldistrib_normal >> rw[])
    >> Rewr'
 >> Know ‘expectation p (λx. exp (Normal s * X x + Normal s * Y x)) =
          expectation p (λx. exp (Normal s * X x) * exp (Normal s * Y x))’
 >- (MATCH_MP_TAC expectation_cong  >> rw[] >> MATCH_MP_TAC exp_add >> DISJ2_TAC
     >> ‘∃a. X x = Normal a’ by METIS_TAC [extreal_cases]
     >> ‘∃b. Y x = Normal b’ by METIS_TAC [extreal_cases]
     >> rw[extreal_mul_eq]) >> Rewr'
 >> HO_MATCH_MP_TAC indep_vars_expectation
 >> simp[]
 >> CONJ_TAC
   (* real_random_variable (λx. exp (Normal s * X x)) p *)
 >- (MATCH_MP_TAC real_random_variable_exp_normal
     >> fs[real_random_variable, random_variable_def])
 >> CONJ_TAC
   (* real_random_variable (λx. exp (Normal s * X x)) p *)
 >- (MATCH_MP_TAC real_random_variable_exp_normal
     >> fs[real_random_variable, random_variable_def])
 >> CONJ_TAC
   (* indep_vars p (λx. exp (Normal s * X x)) (λx. exp (Normal s * Y x)) Borel Borel *)
 >- (Q.ABBREV_TAC ‘f = λx. exp (Normal s * x)’
     >> simp[]
     >> MATCH_MP_TAC (REWRITE_RULE [o_DEF] indep_rv_cong) >> csimp[]
     >> Q.UNABBREV_TAC ‘f’
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
     >> simp[] >> Q.EXISTS_TAC ‘λx. Normal s * x’ >> simp[SIGMA_ALGEBRA_BOREL]
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
     >> qexistsl [‘λx. x’, ‘s’]
     >> simp[SIGMA_ALGEBRA_BOREL, IN_MEASURABLE_BOREL_BOREL_I])
 >> Know ‘(λx. exp (Normal s * X x)) ∈ Borel_measurable (measurable_space p)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
     >> Q.EXISTS_TAC ‘λx. Normal s * X x’
     >> fs [prob_space_def, measure_space_def]
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
     >> qexistsl [‘X’, ‘s’] >> simp[random_variable_def]
     >> fs [random_variable_def, p_space_def, events_def])
 >> DISCH_TAC
 >> Know ‘(λx. exp (Normal s * Y x)) ∈ Borel_measurable (measurable_space p)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
     >> Q.EXISTS_TAC ‘λx. Normal s * Y x’
     >> fs [prob_space_def, measure_space_def]
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
     >> qexistsl [‘Y’, ‘s’] >> simp[random_variable_def]
     >> fs [random_variable_def, p_space_def, events_def])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘f = λx. exp (Normal s * X x)’ >> simp[]
 >> ‘∀x. x ∈ p_space p ⇒ 0 ≤  f x’ by METIS_TAC [exp_pos]
 >> Q.ABBREV_TAC ‘g = λx. exp (Normal s * Y x)’ >> simp[]
 >> ‘∀x. x ∈ p_space p ⇒ 0 ≤  g x’ by METIS_TAC [exp_pos]
 >> CONJ_TAC (* integrable p f *)
    >- (Suff ‘ pos_fn_integral p f <> PosInf’
        >- FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, integrable_pos, expectation_def]
        >> ‘∫ p f = ∫⁺ p f ’ by METIS_TAC[integral_pos_fn, prob_space_def, p_space_def]
        >> METIS_TAC [expectation_def]
        >> simp[])
    >- (Suff ‘ pos_fn_integral p g <> PosInf’
        >- FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, integrable_pos, expectation_def]
        >> ‘∫ p g = ∫⁺ p g ’ by METIS_TAC[integral_pos_fn, prob_space_def, p_space_def]
        >> METIS_TAC [expectation_def])
QED


(* ------------------------------------------------------------------------- *)
(*  Add to real_borelTheory                                                  *)
(* ------------------------------------------------------------------------- *)

Theorem in_borel_measurable_pow:
    !a n f g. sigma_algebra a /\
              f IN measurable a borel /\
              (!x. x IN space a ==> (g x = (f x) pow n)) ==>
                   g IN measurable a borel
Proof
    STRIP_TAC
 >> Induct_on ‘n’
 >- (FULL_SIMP_TAC std_ss [pow0] \\
     METIS_TAC [in_borel_measurable_const])
 >> rpt STRIP_TAC
 >> fs [real_pow]
 >> irule in_borel_measurable_mul
 >> simp []
 >> qexistsl [‘f’, ‘λx. f x pow n’]
 >> simp []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> qexists ‘f’
 >> simp []
QED

Theorem in_measurable_borel_eq:
    ∀a f g.
      (∀x. x ∈ space a ⇒ f x = g x) ∧ g ∈ borel_measurable a ⇒
      f ∈ borel_measurable a
Proof
    rw [measurable_def, IN_FUNSET]
 >> Know ‘PREIMAGE f s INTER space a = PREIMAGE g s INTER space a’
 >- (rw [Once EXTENSION, PREIMAGE_def] \\
     METIS_TAC [])
 >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem in_measurable_borel_comp_borel:
    ∀a f g h.
      f ∈ borel_measurable borel ∧ g ∈ borel_measurable a ∧
      (∀x. x ∈ space a ⇒ h x = f (g x)) ⇒
      h ∈ borel_measurable a
Proof
    rw[]
 >> dxrule_all_then assume_tac MEASURABLE_COMP
 >> irule in_measurable_borel_eq >> qexists_tac ‘f o g’ >> simp[]
QED

(* ------------------------------------------------------------------------- *)
(*  Add to extrealTheory                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem sqrt_imp_PosInf:
    ∀x. sqrt x = PosInf ∧ 0 ≤ x ⇔ x = PosInf
Proof
    rw []
 >> EQ_TAC
 >- (STRIP_TAC \\
     CCONTR_TAC \\
     ‘x ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_trans] \\
     ‘∃r. Normal r = x’ by METIS_TAC [extreal_cases] \\
     rw [cj 1 extreal_sqrt_def] \\
     fs [extreal_sqrt_def])
 >> simp [cj 2 extreal_sqrt_def]
QED

Theorem sqrt_infty:
    ∀x. x ≠ PosInf ∧ 0 ≤ x ⇒ sqrt x ≠ PosInf
Proof
    rw []
 >> CCONTR_TAC
 >> fs [sqrt_imp_PosInf, cj 2 extreal_sqrt_def]
 >> ‘x ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> ‘∃r. Normal r = x’ by METIS_TAC [extreal_cases]
 >> rw [cj 1 extreal_sqrt_def]
 >> fs [extreal_sqrt_def]
QED

Theorem  max_lt:
  ∀x y z. max x y < z ⇔ x < z ∧ y < z
Proof
  rpt STRIP_TAC
  >> EQ_TAC
  >- (STRIP_TAC \\
      ‘x ≤ max x y’ by rw [le_max1] \\
      ‘y ≤ max x y’ by rw [le_max2] \\
      METIS_TAC [let_trans])
  >> STRIP_TAC
  >> Cases_on ‘x ≤ y’
  >- (rw [extreal_max_def])
  >> rw [extreal_max_def]
QED

Theorem lt_min:
  ∀z x y. z < min x y ⇔ z < x ∧ z < y
Proof
    rpt STRIP_TAC
 >> EQ_TAC
 >- (STRIP_TAC \\
     ‘min x y ≤ x’ by rw [min_le1] \\
     ‘min x y ≤ y’ by rw [min_le2] \\
     METIS_TAC [lte_trans])
 >> STRIP_TAC
 >> Cases_on ‘x ≤ y’
 >- (rw [extreal_min_def])
 >> rw [extreal_min_def]
QED

Theorem sup_in:
    ∀a s. a ∈ s ⇒ a ≤ sup s
Proof
  rw [le_sup']
QED

Theorem sup_not_in:
    ∀a s. sup s < a ⇒ a ∉ s
Proof
  rw []
  >> CCONTR_TAC
  >> ‘a ≤ sup s’ by METIS_TAC [sup_in]
  >> METIS_TAC [let_antisym]
QED

Theorem sup_not_in_imp_le:
    ∀s (a:extreal). (∀(x:extreal). a ≤ x ⇒ x ∉ s) ∧ a ∉ s ⇒ sup s ≤ a
Proof
  rpt STRIP_TAC
  >> Know ‘∀x. x ∈ s ⇒ x < a’
  >- (GEN_TAC \\
      STRIP_TAC \\
      Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
      CCONTR_TAC \\
      fs [extreal_not_lt])
  >> STRIP_TAC
  >> Know ‘sup s ≤ a’
  >- (rw [sup_le'] \\
      Q.PAT_X_ASSUM ‘∀x. x IN s ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘y’) \\
      gs [] \\
      METIS_TAC [lt_imp_le])
  >> DISCH_TAC
  >> METIS_TAC [GSYM lt_le]
QED

Theorem ext_liminf_const :
    ∀c. liminf (λx. (c : extreal)) = c
Proof
    rw [ext_liminf_def]
 >> Know ‘IMAGE (λm. inf {c | x | m ≤ x}) 𝕌(:num) = {c}’
 >- ((MP_TAC o (Q.SPECL [‘UNIV’, ‘c’]) o
             (INST_TYPE [beta |-> ``:extreal``, alpha |-> ``:num``])) IMAGE_CONST \\
     rw [UNIV_NOT_EMPTY] \\
     POP_ASSUM (fs o wrap o SYM) \\
     MATCH_MP_TAC IMAGE_CONG \\
     simp [] \\
          strip_tac \\
     (* ∀x. inf {c | x' | x ≤ x'} = c *)
     sg ‘ {c | x' | x ≤ x'} = {c}’
     >- (rw [Once EXTENSION] >> iff_tac
         >- (SET_TAC []) \\
         rw [IN_DEF] \\
         qexists ‘x’ \\
         simp [ratTheory.RAT_LEQ_REF]) \\
     POP_ORW \\
     SET_TAC [inf_sing])
 >> Rewr'
 >> rw [GSYM sup_sing]
QED

Theorem ext_limsup_const :
    ∀c. limsup (λn. (c : extreal)) = c
Proof
    rw [ext_limsup_def]
 >> Know ‘IMAGE (λm. sup {c | x | m ≤ x}) 𝕌(:num) = {c}’
 >- ((MP_TAC o (Q.SPECL [‘UNIV’, ‘c’]) o
             (INST_TYPE [beta |-> ``:extreal``, alpha |-> ``:num``])) IMAGE_CONST \\
     rw [UNIV_NOT_EMPTY] \\
     POP_ASSUM (fs o wrap o SYM) \\
     MATCH_MP_TAC IMAGE_CONG \\
     simp [] \\
     strip_tac \\
     sg  ‘{c | x' | x ≤ x'} = {c}’
     >- (rw [Once EXTENSION] >> iff_tac
         >- (SET_TAC []) \\
         rw [IN_DEF] \\
         qexists ‘x’ \\
         simp [ratTheory.RAT_LEQ_REF]) \\
     POP_ORW \\
     SET_TAC [sup_sing])
 >> Rewr'
 >> rw [GSYM inf_sing]
QED

Theorem ext_limsup_eq :
    ∀(a :num -> extreal) b. a = b ⇒ limsup a = limsup b
Proof
    rw [ext_limsup_def]
QED

Theorem ext_liminf_eq :
    ∀(a :num -> extreal) b. a = b ⇒ liminf a = liminf b
Proof
    rw [ext_liminf_def]
QED

Theorem lim_null_equiv_extreal_real :
    ∀f l.
          (∃N. ∀n. N ≤ n ⇒ f n ≠ +∞ ∧ f n ≠ −∞) ∧ l ≠ +∞ ∧ l ≠ −∞ ⇒
          (((λx. f x − l) ⟶ 0) sequentially ⇔ ((λn. real (f n) − real l) ⟶ 0) sequentially)
Proof
    rw [GSYM lim_null, EXTREAL_LIM_SEQUENTIALLY]
 >> EQ_TAC
 >- (STRIP_TAC \\
     qx_gen_tac ‘e’ \\
     rw [] \\
     Q.PAT_X_ASSUM ‘∀e. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘e’) \\
     gs [] \\
     qexists ‘MAX N N'’ \\
     qx_gen_tac ‘n’ \\
     STRIP_TAC \\
     Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘n’) \\
     gs [MAX_LE] \\
     Know ‘dist extreal_mr1 (f n − l,0) = dist extreal_mr1 (f n,l)’
     >- (‘∃r. Normal r = l’ by METIS_TAC [extreal_cases] \\
         rw [] \\
         Q.PAT_X_ASSUM ‘∀n. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘n’) \\
         gs [] \\
         ‘∃a. Normal a = f n’ by METIS_TAC [extreal_cases] \\
         ‘dist extreal_mr1 (f n − Normal r,0) = dist extreal_mr1 (Normal a − Normal r,0)’ by rw [] \\
         POP_ORW \\
         ‘dist extreal_mr1 (f n,Normal r) = dist extreal_mr1 (Normal a, Normal r)’ by rw [] \\
         POP_ORW \\
         ‘Normal a - Normal r = Normal (a - r)’ by METIS_TAC [extreal_sub_def] \\
         POP_ORW \\
         rw [GSYM normal_0, extreal_mr1_normal]) \\
     DISCH_THEN (fs o wrap))
 >> STRIP_TAC
 >> qx_gen_tac ‘e’
 >> rw []
 >> Q.PAT_X_ASSUM ‘∀e. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘e’)
 >> gs []
 >> qexists ‘MAX N N'’
 >> qx_gen_tac ‘n’
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘n’)
 >> gs [MAX_LE]
 >> Know ‘dist extreal_mr1 (f n − l,0) = dist extreal_mr1 (f n,l)’
 >- (‘∃r. Normal r = l’ by METIS_TAC [extreal_cases] \\
     rw [] \\
     Q.PAT_X_ASSUM ‘∀n. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘n’) \\
     gs [] \\
     ‘∃a. Normal a = f n’ by METIS_TAC [extreal_cases] \\
     ‘dist extreal_mr1 (f n − Normal r,0) = dist extreal_mr1 (Normal a − Normal r,0)’ by rw [] \\
     POP_ORW \\
     ‘dist extreal_mr1 (f n,Normal r) = dist extreal_mr1 (Normal a, Normal r)’ by rw [] \\
     POP_ORW \\
     ‘Normal a - Normal r = Normal (a - r)’ by METIS_TAC [extreal_sub_def] \\
     POP_ORW \\
     rw [GSYM normal_0, extreal_mr1_normal])
 >> DISCH_THEN (fs o wrap)
QED

Theorem EXTREAL_SUM_IMAGE_CDIV:
    ∀s. FINITE s ⇒
        ∀f c.
          ((∀x. x ∈ s ⇒ f x ≠ −∞) ∨ (∀x. x ∈ s ⇒ f x ≠ +∞)) ∧ c ≠ 0 ⇒
          ∑ (λx. f x / Normal c) s = ∑ f s / Normal c
Proof
    rw [extreal_div_def, extreal_inv_def, Once mul_comm]
 >- (‘∑ f s * Normal c⁻¹ = Normal c⁻¹ *  ∑ f s’ by rw [mul_comm] \\
     POP_ORW \\
     irule EXTREAL_SUM_IMAGE_CMUL \\
     art [])
 >> ‘∑ f s * Normal c⁻¹ = Normal c⁻¹ *  ∑ f s’ by rw [mul_comm]
 >> POP_ORW
 >> irule EXTREAL_SUM_IMAGE_CMUL
 >> art []
QED

(* ------------------------------------------------------------------------- *)
(*  Big O Notation                                                           *)
(* ------------------------------------------------------------------------- *)

Definition BigO_def:
  BigO f g ⇔ ∃(c:real) (n0:num). 0 < c ∧
                                  ∀(n:num). n0 ≤ n ⇒
                                            abs (f n) ≤ c * abs (g n)
End

Theorem BigO_MUL:
  ∀f1 g1 f2 g2. BigO f1 g1 ∧
                BigO f2 g2 ⇒ BigO (λn. f1 n * f2 n) (λn. g1 n * g2 n)
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [BigO_def]
 >> qexistsl_tac [‘c * c'’, ‘MAX n0 n0'’]
 >> rw [REAL_MAX_LE, REAL_LT_MUL']
 >> Q.PAT_X_ASSUM ‘∀n. n0 ≤ n ⇒ abs (f1 n) ≤ c * abs (g1 n)’
    (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Q.PAT_X_ASSUM ‘∀n. n0' ≤ n ⇒ abs (f2 n) ≤ c' * abs (g2 n)’
    (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Know ‘abs (f1 n) * abs (f2 n) ≤ c * abs (g1 n) * (c' * abs (g2 n))’
 >- (MATCH_MP_TAC REAL_LE_MUL2 \\
     fs [] \\
     rw [])
 >> DISCH_TAC
 >> ‘abs (f1 n) * abs (f2 n) = abs (f1 n * f2 n)’ by rw [GSYM ABS_MUL]
 >> ‘c * abs (g1 n) * (c' * abs (g2 n)) = c * c' * abs (g1 n * g2 n)’
     by rw [REAL_MUL_ASSOC, REAL_MUL_COMM, GSYM ABS_MUL]
 >> FULL_SIMP_TAC std_ss []
QED

Theorem BigO_ADD:
  ∀f1 f2 g1 g2. BigO f1 g1 ∧ BigO f2 g2 ⇒
                BigO (λn. f1 n + f2 n) (λn. abs (g1 n) + abs (g2 n))
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [BigO_def]
 >> qexistsl_tac [‘max c c'’, ‘MAX n0 n0'’]
 >> CONJ_TAC
 (* 0 < max c c' *)
 >- (rw [REAL_LT_MAX])
 >> GEN_TAC
 >> Q.PAT_X_ASSUM ‘∀n. n0 ≤ n ⇒ abs (f1 n) ≤ c * abs (g1 n)’
     (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Q.PAT_X_ASSUM ‘∀n. n0' ≤ n ⇒ abs (f2 n) ≤ c' * abs (g2 n)’
     (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Know ‘abs (f1 n + f2 n) ≤ c * abs (g1 n) + c' * abs (g2 n)’
 >- (‘abs (f1 n + f2 n) ≤ abs (f1 n) + abs (f2 n)’ by rw [ABS_TRIANGLE] \\
     Know ‘abs (f1 n) + abs (f2 n) ≤ c * abs (g1 n) + c' * abs (g2 n)’
     >- (MATCH_MP_TAC REAL_LE_ADD2 \\
         METIS_TAC []) \\
     DISCH_TAC \\
     METIS_TAC [REAL_LE_TRANS])
 >> DISCH_TAC
 >> Know ‘c * abs (g1 n) + c' * abs (g2 n) ≤ abs((abs (g1 n) + abs (g2 n))) * max c c'’
 >- (Know ‘c * abs (g1 n) ≤ max c c' * abs (g1 n)’
     >- (‘c ≤ max c c'’ by rw [REAL_LE_MAX1] \\
         Cases_on ‘abs (g1 n) = 0’
         >- (METIS_TAC [REAL_MUL_RZERO, REAL_NEG_0, REAL_EQ_IMP_LE]) \\
             ‘0 ≤ abs (g1 n)’ by METIS_TAC [ABS_POS]  \\
             ‘0 < abs (g1 n)’ by METIS_TAC [REAL_LT_LE] \\
         simp [GSYM REAL_LE_LMUL]) \\
    DISCH_TAC \\
    Know ‘c' * abs (g2 n) ≤ max c c' * abs (g2 n)’
    >- (‘c' ≤ max c c'’ by rw [REAL_LE_MAX2] \\
        Cases_on ‘abs (g2 n) = 0’
        >- (METIS_TAC [REAL_MUL_RZERO, REAL_NEG_0, REAL_EQ_IMP_LE]) \\
            ‘0 ≤ abs (g2 n)’ by METIS_TAC [ABS_POS]  \\
            ‘0 < abs (g2 n)’ by  METIS_TAC [REAL_LT_LE] \\
            simp [GSYM REAL_LE_LMUL]) \\
    DISCH_TAC \\
    Know ‘c * abs (g1 n) + c' * abs (g2 n) ≤ max c c' * abs (g1 n) + max c c' * abs (g2 n)’
    >- (MATCH_MP_TAC REAL_LE_ADD2 \\
        METIS_TAC []) \\
    DISCH_TAC \\
    ‘max c c' * abs (g1 n) + max c c' * abs (g2 n) = (abs (g1 n) + abs (g2 n)) * max c c'’
    by rw [GSYM REAL_ADD_RDISTRIB] \\
    FULL_SIMP_TAC std_ss [] \\
    Know ‘(abs (g1 n) + abs (g2 n)) * max c c' = abs((abs (g1 n) + abs (g2 n))) * max c c'’
    >- (Q.ABBREV_TAC ‘A =  abs (g1 n) + abs (g2 n)’ \\
        Know ‘0 ≤ A’
        >- (rw [abs] \\
            METIS_TAC [ABS_POS, REAL_LE_ADD]) \\
        DISCH_TAC \\
        ‘abs A = A’ by METIS_TAC [abs] \\
        simp []) \\
    DISCH_TAC \\
    METIS_TAC [REAL_LE_TRANS])
 >> DISCH_TAC
 >> METIS_TAC [REAL_LE_TRANS]
QED

Theorem BigO_ADD_MAX:
  ∀f1 f2 g1 g2. BigO f1 g1 ∧ BigO f2 g2 ⇒
                BigO (λn. f1 n + f2 n) (λn. max (abs(g1 n)) (abs(g2 n)))
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [BigO_def]
 >> qexistsl_tac [‘c + c'’, ‘MAX n0 n0'’]
 >> CONJ_TAC
 >- (METIS_TAC [REAL_LT_ADD])
 >> GEN_TAC
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [MAX_LE]
 >> Q.PAT_X_ASSUM ‘∀n. n0 ≤ n ⇒ abs (f1 n) ≤ c * abs (g1 n)’
     (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Q.PAT_X_ASSUM ‘∀n. n0' ≤ n ⇒ abs (f2 n) ≤ c' * abs (g2 n)’
     (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Know ‘abs (f1 n + f2 n) ≤ c * abs (g1 n) + c' * abs (g2 n)’
 >- (‘abs (f1 n + f2 n) ≤ abs (f1 n) + abs (f2 n)’ by rw [ABS_TRIANGLE] \\
     Know ‘abs (f1 n) + abs (f2 n) ≤ c * abs (g1 n) + c' * abs (g2 n)’
     >- (MATCH_MP_TAC REAL_LE_ADD2 \\
         METIS_TAC []) \\
     DISCH_TAC \\
     METIS_TAC [REAL_LE_TRANS])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘A = max (abs (g1 n)) (abs (g2 n))’
 >> rw []
 >> Know ‘c * abs (g1 n) + c' * abs (g2 n) ≤ abs A * (c + c')’
 >- (‘abs (g1 n) ≤ A’ by METIS_TAC [Abbr ‘A’, REAL_LE_MAX1] \\
     ‘abs (g2 n) ≤ A’ by METIS_TAC [Abbr ‘A’, REAL_LE_MAX2] \\
     ‘c * abs (g1 n) ≤ c * A’ by simp [REAL_LE_LMUL] \\
     ‘c' * abs (g2 n) ≤ c' * A’ by simp [REAL_LE_LMUL] \\
     ‘0 ≤ abs (g1 n)’ by METIS_TAC [ABS_POS]\\
     ‘0 ≤ A’ by METIS_TAC [REAL_LE_TRANS] \\
     ‘A = abs A’ by rw [abs] \\
     ‘c * abs (g1 n) + c' * abs (g2 n) ≤  c * A + c' * A’ by METIS_TAC [REAL_LE_ADD2] \\
     ‘c * A + c' * A = A * (c + c')’ by rw [GSYM REAL_ADD_RDISTRIB] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> METIS_TAC [REAL_LE_TRANS]
QED

Theorem BigO_MUL_CONST:
    ∀f g k. k ≠ 0 ∧ BigO f g ⇒ BigO (λn. k * f n) g
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [BigO_def]
 >> qexistsl_tac [‘abs k * c’, ‘n0’]
 >> CONJ_TAC
 (* 0 < abs k * c *)
 >- (‘0 < abs k’ by rw [ABS_NZ'] \\
     METIS_TAC [REAL_LT_RMUL_0])
 >> GEN_TAC
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘∀n. n0 ≤ n ⇒ abs (f n) ≤ c * abs (g n)’
    (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> ‘abs (k * f n) = abs k * abs (f n)’ by METIS_TAC [ABS_MUL]
 >> ‘0 < abs k’ by rw [ABS_NZ']
 >> ‘abs k * abs (f n) ≤ abs k * c * abs (g n)’ by simp [GSYM REAL_LE_LMUL]
 >> ‘abs k * c * abs (g n) = c * abs k * abs (g n)’ by rw [REAL_MUL_COMM]
 >> simp []
QED

Theorem BigO_SUM:
  ∀f g.
        (∀n. BigO (f n) (g n)) ⇒
         ∀n. BigO (λx. SIGMA (λi. f i x) (count n))
        (\x. SIGMA (λi. abs(g i x)) (count n))
Proof
    rw [BigO_def]
 >> fs[SKOLEM_THM]
 >> Cases_on ‘n’
 >- (simp[] \\
     Q.EXISTS_TAC ‘1’ \\
     simp[])
 >> Q.ABBREV_TAC ‘C = sup (IMAGE f' (count1 n'))’
 >> Q.ABBREV_TAC ‘N = MAX_SET (IMAGE f'' (count1 n'))’
 >> qexistsl_tac [‘C’, ‘N’]
 >> sg ‘0 < C’
    (* 0 < C *)
 >- (simp [Abbr ‘C’] \\
     MP_TAC (Q.SPECL [‘IMAGE f' (count1 n')’, ‘0’]
             REAL_LT_SUP_FINITE) \\
     rw [] \\
     Q.EXISTS_TAC ‘f' n'’ \\
     CONJ_ASM2_TAC
     >- (Q.EXISTS_TAC ‘n'’ \\
         simp []) \\
     simp [])
 >> simp []
 >> GEN_TAC
 >> STRIP_TAC
 >> (MP_TAC o (Q.SPECL [`λi. f i (x: num)`,`count1 n'`]) o
              (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_ABS_TRIANGLE
 >> rw [o_DEF]
 >> Know ‘∀n. n ≤ n' ⇒ f' n ≤ C’
 >- (rw [Abbr ‘C’] \\
     irule REAL_SUP_UBOUND_LE' \\
     simp [] \\
     qexists ‘REAL_SUM_IMAGE f' (count1 n')’ \\
     rw [] \\
     rename1 ‘i < SUC n'’ \\
     irule REAL_SUM_IMAGE_POS_MEM_LE \\
     simp [] \\
     GEN_TAC \\
     rw [] \\
     ‘0 < f' x'’ by METIS_TAC [] \\
     METIS_TAC [REAL_LT_IMP_LE])
 >> DISCH_TAC
 >> Know ‘∑ (λi. abs (C * abs (g i x))) (count1 n') = C * abs (∑ (λi. abs (g i x)) (count1 n'))’
 >- (‘∑ (λi. abs (C * abs (g i x))) (count1 n') =
      ∑ (λi. abs C * abs (abs (g i x))) (count1 n')’ by rw [ABS_MUL] \\
     ‘0 ≤ C’ by METIS_TAC [REAL_LT_IMP_LE] \\
     ‘abs C = C’ by rw [ABS_REFL] \\
     FULL_SIMP_TAC std_ss [] \\
     Know ‘∑ (λi. C * abs (abs (g i x))) (count1 n') =
           C * abs (∑ (λi. abs (g i x)) (count1 n'))’
     >- ((MP_TAC o (Q.SPECL [`count1 n'`]) o
                   (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_CMUL \\
         rw [] \\
         DISJ2_TAC \\
         (MP_TAC o (Q.SPECL [`λi. abs (g i (x: num))` ,`count1 n'`]) o
                   (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_POS \\
         rw []) \\
     DISCH_TAC \\
     METIS_TAC [REAL_LE_TRANS])
  >> DISCH_TAC
  >> MATCH_MP_TAC REAL_LE_TRANS
  >> Q.EXISTS_TAC ‘∑ (λi. abs (f i x)) (count1 n')’
  >> rw []
  >> POP_ASSUM (rw o wrap o SYM)
  >> irule REAL_SUM_IMAGE_MONO
  >> CONJ_TAC
  >- (Q.X_GEN_TAC ‘i’ \\
      BETA_TAC \\
      STRIP_TAC \\
      simp [] \\
      Q.PAT_X_ASSUM ‘∀n. 0 < f' n ∧ ∀n'. f'' n ≤ n' ⇒
                                         abs (f n n') ≤ f' n * abs (g n n')’
      (MP_TAC o Q.SPEC ‘i’) \\
      STRIP_TAC \\
      POP_ASSUM (MP_TAC o Q.SPEC ‘x’) \\
      STRIP_TAC \\
      sg ‘f'' i ≤ x’
      >- (‘f'' i ≤ N’ by rw [Abbr ‘N’, in_max_set] \\
          METIS_TAC [LE_TRANS]) \\
      FULL_SIMP_TAC std_ss [] \\
      (* abs (f i x) ≤ abs (C * abs (g i x)) *)
      Know ‘f' i * abs (g i x) ≤ abs (C * abs (g i x))’
      >- (‘abs (C * abs (g i x)) = abs C * abs (g i x)’ by METIS_TAC [ABS_MUL, ABS_ABS] \\
          ‘0 ≤ C’ by METIS_TAC [REAL_LT_IMP_LE] \\
          ‘C = abs C’ by rw [abs] \\
          POP_ASSUM (rw o wrap o SYM) \\
          Know ‘f' i ≤ C’
          >- (‘i ≤ n'’ by  fs [count1_def] \\
              Q.PAT_X_ASSUM ‘∀n. n ≤ n' ⇒ f' n ≤ C’ (MP_TAC o (Q.SPEC ‘i’)) \\
              METIS_TAC [] \\
              simp []) \\
          DISCH_TAC \\
          Cases_on ‘abs (g i x) = 0’
          >- (METIS_TAC [REAL_MUL_RZERO, REAL_NEG_0, REAL_EQ_IMP_LE]) \\
          ‘0 ≤ abs (g i x)’ by METIS_TAC [ABS_POS]  \\
          ‘0 < abs (g i x)’ by METIS_TAC [REAL_LT_LE] \\
          simp [GSYM REAL_LE_LMUL]) \\
      METIS_TAC [REAL_LE_TRANS])
  >> simp []
QED

(* ------------------------------------------------------------------------- *)
(*  Differentiable                                                           *)
(* ------------------------------------------------------------------------- *)

Definition diff_def :
    (diff 0       f x = f x) /\
    (diff (SUC m) f x = @y. ((diff m f) diffl y)(x))
End

Theorem diff_thm :
    !f. (!m t. ?x. (diff m f diffl x) t) ==>
        (diff 0 f = f) /\
        (!m t. ((diff m f) diffl (diff (SUC m) f t))(t))
Proof
    rw [diff_def, FUN_EQ_THM]
 >> SELECT_ELIM_TAC >> simp []
QED

Definition higher_differentiable_def:
    (higher_differentiable 0 f x <=> T) /\
    (higher_differentiable (SUC m) f x <=> ?y. (diff m f diffl y) x /\
                                              higher_differentiable m f x)
End

Theorem higher_differentiable_thm:
    !f.
        (diff 0 f = f) /\
        (!m t. (higher_differentiable (SUC m) f t ==>
               (diff m f diffl (diff (SUC m) f t)) t))
Proof
    rw [higher_differentiable_def, diff_def, FUN_EQ_THM]
 >> SELECT_ELIM_TAC >> simp []
 >> qexists ‘y’ >> simp []
QED

Theorem higher_differentiable_mono:
    ∀f n m t. m ≤ n ∧ higher_differentiable n f t ⇒
              higher_differentiable m f t
Proof
    rpt STRIP_TAC
 >> Cases_on ‘m = n’
 >- (fs [])
 >> Induct_on ‘n’
 >- (rw [higher_differentiable_def])
 >> rw []
 >> Cases_on ‘m’
 >- (simp [higher_differentiable_def])
 >> ‘n < SUC n’ by rw [LESS_SUC_REFL]
 >> ‘n < SUC n ⇒
     higher_differentiable (SUC n) f t ⇒
     higher_differentiable n f t’ by METIS_TAC [higher_differentiable_def]
 >> rw []
 >> Cases_on ‘SUC n' = n’
 >- (rw [])
 >> Suff ‘SUC n' < n’
 >- (fs [])
 >> MATCH_MP_TAC LESS_NOT_SUC
 >> simp []
QED

Theorem diff_0[simp]:
    diff 0 f = f
Proof
    rw [FUN_EQ_THM, diff_def]
QED

Theorem diff1_def:
    ∀f x. diff 1 f x = @y. (f diffl y) x
Proof
    EVAL_TAC
 >> simp []
QED

Theorem higher_differentiable_1:
    ∀f x.
          higher_differentiable 1 f x ⇔
          ∃y. (f diffl y) x
Proof
    rpt STRIP_TAC
 >> MP_TAC ( Q.SPECL [‘0’, ‘f’, ‘x’] (cj 2 higher_differentiable_def))
 >> simp [cj 1 higher_differentiable_def]
QED

Theorem higher_differentiable_imp_continuous:
    ∀f x. higher_differentiable 1 f x ⇒
          f continuous (at x)
Proof
    rw [higher_differentiable_1, GSYM limTheory.contl_eq_continuous_at]
 >> METIS_TAC [limTheory.DIFF_CONT]
QED

Theorem higher_differentiable_1_eq_differentiable:
    ∀f x. higher_differentiable 1 f x <=> f differentiable at x
Proof
    rw []
 >> fs [higher_differentiable_1, limTheory.diffl_has_vector_derivative,
        GSYM limTheory.differentiable_alt, limTheory.differentiable_has_vector_derivative]
QED

Theorem higher_differentiable_1_eq_differentiable_on:
    ∀f. (∀x. higher_differentiable 1 f x) ⇔ f differentiable_on 𝕌(:real)
Proof
    rw [higher_differentiable_1_eq_differentiable, derivativeTheory.differentiable_on]
 >> METIS_TAC [netsTheory.WITHIN_UNIV]
QED

(* ------------------------------------------------------------------------- *)
(*  real_limsup & real_liminf                                                *)
(* ------------------------------------------------------------------------- *)

Definition real_limsup_def:
  real_limsup (a :num -> real) = inf (IMAGE (\m. sup {a n | m <= n}) UNIV)
End

Definition real_liminf_def:
   real_liminf (a :num -> real) = sup (IMAGE (\m. inf {a n | m <= n}) UNIV)
End

val _ = overload_on ("limsup", ``real_limsup``);
val _ = overload_on ("liminf", ``real_liminf``);

(*REAL_INF_LE', REAL_IMP_LE_INF'*)
Theorem limsup_normal:
    ∀a r. limsup (λx. Normal (a x)) = Normal r ⇒ real_limsup a = r
Proof
    rw [real_limsup_def, ext_limsup_def]
 >> fs [inf_eq']
 >> qmatch_abbrev_tac ‘inf s = r’
 >> ‘s ≠ {}’ by rw [Abbr ‘s’]
 >> Know ‘∀x. x ∈ s ⇒ r ≤ x’
 >- (rw [Abbr ‘s’] \\
     REWRITE_TAC [GSYM extreal_le_eq] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     qexists ‘m’ \\
     fs [sup_eq'] \\
     rw []
     >- (rw [] \\ (*sup_le'*)
         irule REAL_SUP_UBOUND_LE' \\
         CONJ_ASM2_TAC
         >- (qexists ‘sup {a n | m ≤ n}’ \\
             Q.ABBREV_TAC ‘p = {a n | m ≤ n}’ \\
             (* qmatch_abbrev_tac ‘∀x. x IN p ==> x ≤ sup p’*)
             MP_TAC (Q.SPEC ‘p’ SUP_FINITE) \\
             impl_tac
             >- (simp [FINITE_DEF] \\
                 (* FINITE {a n | m ≤ n} *)
                 FIRST_X_ASSUM (Q.SPEC_THEN ‘Normal (a x)’ MP_TAC) \\
                 STRIP_TAC \\
                 Suff ‘∀z. (∃m. (∀y. (∃x. y = Normal (a x) ∧ m ≤ x) ⇒ y ≤ z) ∧
                                ∀y. (∀z. (∃x. z = Normal (a x) ∧ m ≤ x) ⇒ z ≤ y) ⇒ z ≤ y) ⇒
                           Normal (a x) ≤ z’
                 >- (STRIP_TAC \\
                     fs [] \\
                     POP_ASSUM (MP_TAC o Q.SPEC ‘Normal r’) \\
                     STRIP_TAC \\
                     cheat) \\
                 cheat) \\
            simp [])\\
        CONJ_TAC
       (* {a n | m ≤ n} ≠ ∅ *)
        >- (REWRITE_TAC [GSYM MEMBER_NOT_EMPTY] \\
            qexists ‘a x’ \\
            simp [] \\
            qexists ‘x’ \\
            METIS_TAC[]) \\
       fs [] \\
       qexists ‘x’ \\
       simp []) \\
     (* Normal (sup {a n | m ≤ n}) ≤ y *)
     POP_ASSUM (MP_TAC o (Q.SPEC ‘Normal (sup {(a: num -> real) n | (m: num) ≤ n})’)) \\
     fs [] \\
     Suff ‘∃x. sup {a n | m ≤ n} = a x ∧ m ≤ x’
     >- (fs []) \\
     cheat)
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘s’, ‘r’] REAL_IMP_LE_INF')
 >> impl_tac
 >- (simp [])
 >> DISCH_TAC
    >> Know ‘∀x. x ∈ s ⇒ x ≤ r’
    >- (rw [Abbr ‘s’] \\
        REWRITE_TAC [GSYM extreal_le_eq] \\
        Q.PAT_X_ASSUM ‘∀y. (∀z. (∃m. z = sup {Normal (a x) | m ≤ x}) ⇒ y ≤ z) ⇒ y ≤ Normal r’ MATCH_MP_TAC \\
        STRIP_TAC \\
        fs [sup_eq'] \\
        rw [] \\
        cheat)
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘s’, ‘r’] REAL_IMP_INF_LE')
 >> impl_tac
 >- (CONJ_TAC
     >- (qexists ‘r’ \\
         simp []) \\
     qexists ‘sup {a n | m ≤ n}’ \\
     CONJ_TAC
     >- (rw [Abbr ‘s’] \\
         qexists ‘m’ \\
         simp []) \\
     Q.PAT_X_ASSUM ‘∀y. (∃m. y = sup {Normal (a x) | m ≤ x}) ⇒ Normal r ≤ y’ (K ALL_TAC) \\
     REWRITE_TAC [GSYM extreal_le_eq] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     GEN_TAC \\
     rw [] \\
     (* Normal (sup {a n | m ≤ n}) ≤ sup {Normal (a x) | m' ≤ x} *)
     Know ‘sup {a n | m ≤ n} = r’
     >- (rw [Abbr ‘s’] \\
         cheat) \\
     REWRITE_TAC [GSYM extreal_11] \\
     DISCH_TAC \\
     cheat)
 >> DISCH_TAC
 >> METIS_TAC [REAL_LE_ANTISYM]
QED

Theorem liminf_normal:
    ∀a r. liminf (λx. Normal (a x)) = Normal r ⇒ real_liminf a = r
Proof
    rw [real_liminf_def, ext_liminf_def]
 >> cheat
QED

  (*
Theorem real_limsup_tactic1[local]:
    ∀a l.
          limsup (λx. Normal (a x)) = Normal l ⇔
          limsup a = l
Proof
  rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘a’, ‘l’] limsup_normal)
 >> simp []
QED

Theorem real_limsup_tactic2[local]:
    ∀a l.
          liminf (λx. Normal (a x)) = Normal l ⇔
          liminf a = l
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘a’, ‘l’] liminf_normal)
 >> simp []
QED

Theorem real_limsup_thm:
    ∀(a :num -> real) (l :real).
                      ((a ⟶ l) sequentially ⇔
                       limsup a = l ∧ liminf a = l)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘Normal o a’, ‘l’]
            ext_limsup_thm)
 >> impl_tac
 >- (simp [extreal_not_infty])
 >> simp [o_DEF, real_normal]
 >> STRIP_TAC
 >> ‘((λx. a x) ⟶ l) sequentially ⇔ (a ⟶ l) sequentially’ by METIS_TAC []
 >> fs [real_limsup_tactic1, real_limsup_tactic2]
QED
  *)

(*ext_limsup_def, (martingle) ext_limsup_thm*)
Theorem in_borel_measurable_diff:
  ∀a f g.
    sigma_algebra a ∧ f ∈ borel_measurable a ∧
    (∀x. x ∈ space a ⇒ g x = diff 1 f x) ⇒
    g ∈ borel_measurable a
Proof
    fs [diff1_def, limTheory.diffl, diff_def]
    >> rpt STRIP_TAC
  >> cheat
QED

(*
Theorem IN_MEASURABLE_BOREL_DIFF:
  ∀a f g.
    sigma_algebra a ∧ f ∈ Borel_measurable a ∧
    (∀x. x ∈ space a ⇒ f x ≠ −∞ ∧ f x ≠ +∞) ∧
    (∀x. x ∈ space a ⇒ g x = Normal o (diff 1 (real o f)) x) ⇒
    g ∈ Borel_measurable a
Proof
  fs [diff1_def, limTheory.diffl, diff_def]
  >> rpt STRIP_TAC
  >> cheat
QED
*)



(* ------------------------------------------------------------------------- *)
(*  Taylor Theorem                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem TAYLOR_REMAINDER:
    ∀(n :num) x f.
              ∃(M :extreal) t.
                               abs (Normal (diff n f t)) ≤ M ⇒
      abs (Normal ((diff n f t / ((&FACT n) :real))) * Normal x pow n) ≤
      M / (Normal (&FACT n)) * abs (Normal x) pow n
Proof
    rpt GEN_TAC
 >> qexistsl [‘M’, ‘t’]
 >> STRIP_TAC
 >> ‘Normal x pow n = Normal (x pow n)’ by rw [extreal_pow_def]
 >> POP_ORW
 >> ‘abs (Normal x) = Normal (abs x)’ by METIS_TAC [extreal_abs_def]
 >> POP_ORW
 >> ‘Normal (abs x) pow n = Normal ((abs x) pow n)’ by rw [extreal_pow_def]
 >> POP_ORW
 >> ‘abs x pow n = abs (x pow n)’ by rw [POW_ABS]
 >> POP_ORW
 >> Cases_on ‘x pow n = 0’
 >- (‘abs (Normal (diff n f t / &FACT n) * Normal (x pow n)) = 0’
      by METIS_TAC [normal_0, mul_rzero, abs_0] \\
     ‘M / Normal (&FACT n) * Normal (abs (x pow n)) = 0’
      by METIS_TAC [ABS_0, normal_0, mul_rzero] \\
      simp [])
 >> Know ‘!n. (0: real) < &FACT n’
 >- (EVAL_TAC \\
     rw [FACT_LESS, LE_1])
 >> DISCH_TAC
 >> ‘∀n. (0: real) <= &FACT n’ by METIS_TAC [REAL_LT_IMP_LE]
 >> ‘∀n. (0: real) ≠ &FACT n’ by METIS_TAC [REAL_LT_IMP_NE]
 >> Know ‘0 ≤ M’
 >- (simp [sup_le] \\
     rw [le_sup] \\
     METIS_TAC [abs_pos, le_trans])
 >> DISCH_TAC
 >> ‘NegInf ≠ M’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> Cases_on ‘M = PosInf’
 >- (‘M / Normal (&FACT n) = PosInf’ by METIS_TAC [infty_div] \\
     ‘0 < Normal (abs (x pow n))’ by rw [abs_gt_0] \\
     ‘M / Normal (&FACT n) * Normal (abs (x pow n)) = PosInf’ by METIS_TAC [mul_infty] \\
     rw [])
 >> ‘∃r. M = Normal r’ by METIS_TAC [extreal_cases]
 >> rw []
 >> ‘Normal (diff n f t / &FACT n) * Normal (x pow n) =
     Normal (diff n f t / &FACT n * x pow n)’ by METIS_TAC [extreal_mul_def]
 >> POP_ORW
 >> ‘Normal r / Normal (&FACT n) = Normal (r / &FACT n)’ by METIS_TAC [extreal_div_eq]
 >> POP_ORW
 >> ‘Normal (r / &FACT n) * Normal (abs (x pow n)) =
     Normal (r / &FACT n * abs (x pow n))’ by METIS_TAC [extreal_mul_def]
 >> POP_ORW
 >> ‘abs (Normal (diff n f t / &FACT n * x pow n)) =
     Normal (abs (diff n f t / &FACT n * x pow n))’ by METIS_TAC [extreal_abs_def]
 >> POP_ORW
 >> ‘abs (Normal (diff n f t)) = Normal (abs (diff n f t))’ by METIS_TAC [extreal_abs_def]
 >> FULL_SIMP_TAC std_ss [extreal_le_eq]
 >> ‘abs (diff n f t) / &FACT n ≤ r / &FACT n’ by rw [REAL_LE_RDIV_CANCEL]
 >> ‘abs (&FACT n) = (&FACT n: real)’ by rw [ABS_REFL]
 >> ‘abs (diff n f t) / &FACT n = abs (diff n f t / &FACT n)’ by METIS_TAC [GSYM ABS_DIV]
 >> FULL_SIMP_TAC std_ss []
 >> ‘0 < abs (x pow n)’ by METIS_TAC [ABS_NZ]
 >> ‘abs (diff n f t / &FACT n) * abs (x pow n) ≤ r / &FACT n * abs (x pow n)’
     by METIS_TAC [GSYM REAL_LE_RMUL]
 >> ‘abs (diff n f t / &FACT n) * abs (x pow n) = abs (diff n f t / &FACT n * x pow n)’
     by METIS_TAC [GSYM ABS_MUL]
 >> FULL_SIMP_TAC std_ss []
QED

Theorem TAYLOR_THEOREM:
    ∀f a x n.
              a < x ∧ 0 < n ∧
              (!m t. m < n ∧ a ≤ t ∧ t ≤ x ⇒ higher_differentiable (SUC m) f t) ⇒
              ∃t. a < t ∧ t < x ∧
                  f x =
                        sum (0,n) (λm. diff m f a / &FACT m * (x − a) pow m) +
                        diff n f t / &FACT n * (x − a) pow n
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘g = λx. f (x + a)’
 >> ‘∀x. g x = f (x + a)’ by rw [Abbr ‘g’]
 >> POP_ASSUM (MP_TAC o Q.SPEC ‘x - a’)
 >> ‘f (x - a + a) = f x’ by METIS_TAC [REAL_SUB_ADD]
 >> POP_ORW
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘diff' = \n x. diff n f (x + a)’
 >> MP_TAC (Q.SPECL [‘g’, ‘diff'’, ‘x - a’, ‘n’] MCLAURIN)
 >> impl_tac
 >- (CONJ_TAC
     >- (rw [REAL_SUB_LT]) \\
     CONJ_TAC
     >- (fs []) \\
     CONJ_TAC
     >- (rw [Abbr ‘diff'’] \\
         METIS_TAC []) \\
     Q.UNABBREV_TAC ‘diff'’ \\
     BETA_TAC \\
     qx_genl_tac [‘m’, ‘t’] \\
     STRIP_TAC \\
     ‘a ≤ t + a’ by rw [REAL_LE_ADDL] \\
     ‘t + a ≤ x’ by METIS_TAC [REAL_LE_SUB_LADD] \\
     Q.PAT_X_ASSUM ‘∀m t. m < n ∧ a ≤ t ∧ t ≤ x ⇒
                          higher_differentiable (SUC m) f t’
     (MP_TAC o Q.SPECL [‘m’, ‘t + a’]) \\
     DISCH_TAC \\
     MP_TAC (Q.SPECL [‘diff (m:num) f’, ‘λx. (x + a)’, ‘diff (SUC m) f (t + a:real)’, ‘1’, ‘t’]
             limTheory.DIFF_CHAIN) \\
     impl_tac
     >- (CONJ_TAC
         >- (BETA_TAC \\
             MP_TAC (Q.SPEC ‘f’ higher_differentiable_thm) \\
             rw []) \\
         Know ‘((λx. x + a) diffl (1 + 0)) t’
         >- (MP_TAC (Q.SPECL [‘λx. x’, ‘λx. a’, ‘1’, ‘0’, ‘t’] limTheory.DIFF_ADD) \\
             impl_tac \\
             METIS_TAC [limTheory.DIFF_X, limTheory.DIFF_CONST] \\
             BETA_TAC \\
             simp []) \\
         simp [REAL_ADD_RID]) \\
         simp [])
 >> simp[]
 >> DISCH_THEN (Q.X_CHOOSE_TAC ‘t’)
 >> Q.EXISTS_TAC ‘t + a’
 >> CONJ_TAC
 >- (rw [REAL_LT_ADDL])
 >> CONJ_TAC
 >- (rw [REAL_LT_ADD_SUB])
 >> Know ‘∀m. diff' m 0 = diff m f a’
 >- (Q.UNABBREV_TAC ‘diff'’ \\
     BETA_TAC \\
     simp [])
 >> DISCH_TAC
 >> simp []
QED

Theorem TAYLOR_REMAINDER_EXPECTATION:
    ∀p n X f.
            prob_space p ∧ random_variable X p borel ∧
            integrable p (Normal o X) ∧
            integrable p (λx. Normal (X x pow n)) ⇒
         ∃M (t: real).
            abs (Normal (diff n f t)) ≤ M ⇒
            expectation p (λx. abs (Normal (diff n f t/ &FACT n) * (Normal ∘ X) x pow n)) ≤
            M / Normal (&FACT n) * expectation p (λx. abs ((Normal ∘ X) x) pow n)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘n’, ‘X x’, ‘f’]
            TAYLOR_REMAINDER)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘M’
               (Q.X_CHOOSE_THEN ‘t’ ASSUME_TAC))
 >> qexistsl [‘M’, ‘t’]
 >> STRIP_TAC
 >> fs [o_DEF]
 >> Know ‘integrable p (λx'. abs (Normal (X x' pow n)))’
 >- (MP_TAC (Q.SPECL [‘p’, ‘λx. Normal (X x pow n)’]
             integrable_abs) \\
     FULL_SIMP_TAC std_ss [prob_space_def, o_DEF])
 >> DISCH_TAC
 >> ‘∀x'. abs (Normal (X x')) pow n = abs (Normal (X x') pow n)’
     by rw [extreal_abs_def, extreal_pow_def, POW_ABS]
 >> rw []
 >> ‘∀x'. Normal (X x') pow n = Normal ((X x') pow n)’ by rw [extreal_pow_def]
 >> rw []
 >> Cases_on ‘expectation p (λx'. abs (Normal (X x' pow n))) = 0’
 >- (rw [] \\
     Q.ABBREV_TAC ‘c = diff n f t / &FACT n’ \\
     ‘∀x'. abs (Normal c * Normal (X x' pow n)) =
           abs (Normal c) * abs (Normal (X x' pow n))’ by rw [abs_mul] \\
     POP_ORW \\
     ‘abs (Normal c) = Normal (abs c)’ by rw [extreal_abs_def] \\
     POP_ORW \\
     ‘expectation p (λx'. Normal (abs c) * abs (Normal (X x' pow n)))  =
      Normal (abs c) * expectation p (λx'. abs (Normal (X x' pow n)))’
     by METIS_TAC [expectation_cmul] \\
     POP_ORW \\
     Q.PAT_X_ASSUM ‘expectation p (λx'. abs (Normal (X x' pow n))) = 0’ MP_TAC \\
     rw [])
 >> Know ‘0 ≤ M’
 >- (simp [sup_le] \\
     rw [le_sup] \\
     METIS_TAC [abs_pos, le_trans])
 >> DISCH_TAC
 >> ‘M ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> Know ‘!n. (0: real) < &FACT n’
 >- (EVAL_TAC \\
     rw [FACT_LESS, LE_1])
 >> DISCH_TAC
 >> ‘∀n. (0: real) <= &FACT n’ by METIS_TAC [REAL_LT_IMP_LE]
 >> ‘∀n. (0: real) ≠ &FACT n’ by METIS_TAC [REAL_LT_IMP_NE]
 >> ‘∀x'. abs (Normal (X x')) pow n = abs (Normal (X x') pow n)’
     by rw [extreal_abs_def, extreal_pow_def, POW_ABS]
 >> rw []
 >> Cases_on ‘∀x'. Normal (X x' pow n) = 0’
 >- (rw [abs_0, expectation_zero])
 >> FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
 >> Cases_on ‘M = PosInf’
 >- (Know ‘M / Normal (&FACT n) * expectation p (λx'. abs (Normal (X x' pow n))) = PosInf’
     >- (‘M / Normal (&FACT n) = PosInf’ by METIS_TAC [infty_div] \\
         POP_ORW \\
         MATCH_MP_TAC (cj 1 mul_infty) \\
         ‘∀x'. 0 ≤ abs (Normal (X x' pow n))’ by METIS_TAC [abs_pos] \\
         Know ‘0 ≤ expectation p (λx'. abs (Normal (X x' pow n)))’
         >- (irule expectation_pos \\
             simp []) \\
         DISCH_TAC \\
         simp [lt_le]) \\
     DISCH_TAC \\
     rw [])
 >> ‘∃r. M = Normal r’ by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss []
 >> ‘Normal r / Normal (&FACT n) = Normal (r / &FACT n)’ by METIS_TAC [extreal_div_eq]
 >> POP_ORW
 >> Know ‘expectation p (λx'. Normal (r / &FACT n) * abs (Normal (X x' pow n))) =
          Normal (r / &FACT n) * expectation p (λx'. abs (Normal (X x' pow n)))’
 >- (MP_TAC (Q.SPECL [‘p’, ‘λx'. abs (Normal (X x' pow n))’, ‘r / &FACT n’]
             expectation_cmul) \\
     simp [])
 >> DISCH_TAC
 >> POP_ASSUM (rw o wrap o SYM)
 >> irule expectation_mono
 >> BETA_TAC
 >> simp []
 >> CONJ_TAC
 >- (GEN_TAC \\
     STRIP_TAC \\
     ‘abs (Normal (diff n f t / &FACT n) * Normal (X x'' pow n)) =
      abs (Normal (diff n f t / &FACT n)) * abs (Normal (X x'' pow n))’ by rw [abs_mul] \\
     POP_ORW \\
     irule le_rmul_imp \\
     simp [abs_pos] \\
     ‘abs (Normal (diff n f t / &FACT n)) =
      abs (Normal (diff n f t) / Normal (&FACT n))’ by METIS_TAC [extreal_div_eq] \\
     POP_ORW \\
     Know ‘abs (Normal (diff n f t) / Normal (&FACT n)) =
           abs (Normal (diff n f t)) / abs (Normal (&FACT n))’
     >- (irule abs_div \\
         simp [extreal_not_infty]) \\
     Rewr' \\
     ‘abs (Normal (&FACT n)) = Normal (&FACT n)’ by rw [abs_refl] \\
     POP_ORW \\
     ‘Normal r / Normal (&FACT n) = Normal (r / &FACT n)’
     by METIS_TAC [extreal_div_eq] \\
     POP_ASSUM (rw o wrap o SYM) \\
     irule ldiv_le_imp \\
     simp [cj 2 extreal_not_infty])
 >> CONJ_TAC
 >- (Q.ABBREV_TAC ‘h = λx'. Normal (diff n f t / &FACT n) *
                            Normal (X x' pow n)’ \\
     ‘∀x'. h x' = Normal (diff n f t / &FACT n) *
                  Normal (X x' pow n)’ by rw [Abbr ‘h’] \\
     MP_TAC (Q.SPECL [‘p’, ‘h’]
             integrable_abs) \\
             Q.UNABBREV_TAC ‘h’ \\
     fs [prob_space_def] \\
     POP_ORW \\
     impl_tac
     >- (MP_TAC (Q.SPECL [‘p’, ‘λx'. Normal (X x' pow n)’,
                          ‘diff n f t / &FACT n’]
                 integrable_cmul) \\
     simp [] \\
     impl_tac \\
     simp [o_DEF]) \\
     simp [o_DEF])
 >> CONJ_TAC
 >- (MP_TAC (Q.SPECL [‘p’, ‘λx'. abs (Normal (X x' pow n))’,
                      ‘r / &FACT n’]
             integrable_cmul) \\
     fs [o_DEF, prob_space_def])
 >> Know ‘(λx'. (X x') pow n) ∈ borel_measurable (measurable_space p)’
 >- (irule in_borel_measurable_pow \\
     fs [SIGMA_ALGEBRA_BOREL, prob_space_def] \\
     qexistsl_tac [‘X’, ‘n’] \\
     fs [random_variable_def, p_space_def, events_def] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> CONJ_TAC
 >- (Q.ABBREV_TAC ‘c = diff n f t / &FACT n’ \\
     MP_TAC (Q.SPECL [‘p’, ‘λx'. Normal c * Normal (X x' pow n)’]
             real_random_variable_abs) \\
     simp [] \\
     Know ‘real_random_variable (λx. Normal (X x pow n)) p’
     >- (fs [real_random_variable_def, random_variable_def, p_space_def,
             events_def, extreal_not_infty, abs_not_infty] \\
         METIS_TAC [IN_MEASURABLE_BOREL_IMP_BOREL]) \\
     DISCH_TAC \\
     MP_TAC (Q.SPECL [‘p’, ‘λx. Normal (X x pow n)’, ‘c’]
             real_random_variable_cmul) \\
     simp [])
 >> Know ‘real_random_variable (λx'. Normal (X x' pow n)) p’
 >- (fs [real_random_variable_def, random_variable_def, p_space_def, events_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_IMP_BOREL])
 >> DISCH_TAC
 >> Know ‘real_random_variable (λx''. abs (Normal (X x'' pow n))) p’
 >- (fs [real_random_variable_def, random_variable_def, p_space_def,
         events_def, extreal_not_infty, abs_not_infty] \\
     MP_TAC (Q.SPECL [‘measurable_space p’, ‘λx'. Normal (X x' pow n)’]
             IN_MEASURABLE_BOREL_ABS') \\
     fs [SIGMA_ALGEBRA_BOREL, prob_space_def, o_DEF])
 >> MP_TAC (Q.SPECL [‘p’, ‘λx'. abs (Normal (X x')) pow n’,
                     ‘r / &FACT n’]
            real_random_variable_cmul)
 >> simp []
QED

Theorem TAYLOR_REMAINDER_EXPECTATION_REAL_RV :
    ∀p n X f.
      prob_space p ∧ real_random_variable X p ∧
      integrable p X ∧
      integrable p (λx. (X x pow n)) ⇒
      ∃M t.
         abs (Normal (diff n f t)) ≤ M ⇒
         expectation p
                     (λx. abs (Normal (diff n f t / &FACT n) * X x pow n)) ≤
         M / Normal (&FACT n) *
         expectation p (λx. abs (X x) pow n)
Proof
    rw [real_random_variable_def]
 >> MP_TAC (Q.SPECL [‘p’, ‘n’, ‘real o X’, ‘f’] TAYLOR_REMAINDER_EXPECTATION)
 >> simp []
 >> Know ‘random_variable (real ∘ X) p borel’
 >- (fs [random_variable_def] \\
     METIS_TAC [in_borel_measurable_from_Borel, EVENTS_SIGMA_ALGEBRA])
 >> Rewr
 >> Know ‘integrable p (Normal ∘ real ∘ X)’
 >- (Know ‘∀x. x IN p_space p ⇒ (Normal o real o X) x = X x’
     >- (rw [o_DEF] \\
         Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
         irule normal_real \\
         gs []) \\
     DISCH_TAC \\
     Know ‘integrable p (Normal ∘ real ∘ X) ⇔ integrable p X’
     >- (irule integrable_cong \\
         fs [prob_space_def, p_space_def]) \\
     Rewr \\
     fs [])
 >> Rewr
 >> Know ‘integrable p (λx. Normal (real (X x) pow n))’
 >- (‘∀x. Normal (real (X x) pow n) = (Normal (real (X x))) pow n’ by rw [extreal_pow_def] \\
     POP_ASSUM (rw o wrap) \\
     Know ‘∀x. x IN p_space p ⇒ Normal (real (X x)) pow n = X x pow n’
     >- (rw [] \\
         Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
         ‘Normal (real (X x)) = X x’ by METIS_TAC [normal_real] \\
         POP_ORW \\
         rw []) \\
        DISCH_TAC \\
        Know ‘integrable p (λx. Normal (real (X x)) pow n) ⇔ integrable p (λx. X x pow n)’
     >- (irule integrable_cong \\
         fs [prob_space_def, p_space_def]) \\
     Rewr \\
     fs [])
 >> Rewr
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘M’
                 (Q.X_CHOOSE_THEN ‘t’ ASSUME_TAC))
 >> qexistsl [‘M’, ‘t’]
 >> STRIP_TAC
 >> fs []
 >> Q.ABBREV_TAC ‘g = λx. abs (Normal (diff n f t / &FACT n) * Normal (real (X x)) pow n)’
 >> Q.ABBREV_TAC ‘h = λx. abs (Normal (diff n f t / &FACT n) * X x pow n)’
 >> Know ‘∀x. x ∈ p_space p ⇒ g x = h x’
 >- (rw [Abbr ‘g’, Abbr ‘h’] \\
     Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     fs [normal_real])
 >> DISCH_TAC
 >> ‘expectation p g = expectation p h’ by METIS_TAC [expectation_cong]
 >> POP_ASSUM (rw o wrap o SYM)
 >> Q.ABBREV_TAC ‘c = λx. abs (Normal (real (X x))) pow n’
 >> Q.ABBREV_TAC ‘d = λx. abs (X x) pow n’
 >> Know ‘∀x. x ∈ p_space p ⇒ c x = d x’
 >- (rw [Abbr ‘c’, Abbr ‘d’] \\
     Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     fs [normal_real])
 >> DISCH_TAC
 >> ‘expectation p c = expectation p d’ by METIS_TAC [expectation_cong]
 >> POP_ASSUM (rw o wrap o SYM)
QED

(* ------------------------------------------------------------------------- *)
(*  Convergence in distribution                                              *)
(* ------------------------------------------------------------------------- *)

Theorem converge_in_dist_cong_full:
    !p X Y A B m. prob_space p ∧
                 (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) /\
                 (!x. x IN p_space p ==> A x = B x) ==>
                 ((X --> A) (in_distribution p) <=> (Y --> B) (in_distribution p))
Proof
    rw [converge_in_dist_def, EXTREAL_LIM_SEQUENTIALLY]
 >> EQ_TAC >> rw []
 >- (Q.PAT_X_ASSUM ‘ ∀f. bounded (IMAGE f 𝕌(:real)) ∧ f continuous_on 𝕌(:real)
                         ==> P’ (MP_TAC o (Q.SPEC ‘f’)) >> rw []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw []
 >> Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE]
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ Y n) =
        expectation p (Normal ∘ f ∘ real ∘ X n)’
 >- (MATCH_MP_TAC expectation_cong \\ rw [])
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ B) =
          expectation p (Normal ∘ f ∘ real ∘ A)’
 >- (MATCH_MP_TAC expectation_cong \\ rw [])
 >> METIS_TAC [])
 >> Q.PAT_X_ASSUM ‘ ∀f. bounded (IMAGE f 𝕌(:real)) ∧ f continuous_on 𝕌(:real)
                        ==> P’ (MP_TAC o (Q.SPEC ‘f’)) >> rw []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw []
 >> Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE]
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ Y n) =
        expectation p (Normal ∘ f ∘ real ∘ X n)’
 >- (MATCH_MP_TAC expectation_cong \\ rw [])
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ B) =
        expectation p (Normal ∘ f ∘ real ∘ A)’
 >- (MATCH_MP_TAC expectation_cong \\ rw [])
 >> METIS_TAC []
QED

Theorem converge_in_dist_cong:
    ∀p X Y Z m. prob_space p ∧
               (∀n x. m ≤ n ∧ x ∈ p_space p ⇒ X n x = Y n x) ⇒
               ((X ⟶ Z) (in_distribution p) ⇔ (Y ⟶ Z) (in_distribution p))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC converge_in_dist_cong_full
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

Definition CnR_def:
    CnR n = {f | (∀x. higher_differentiable n f x) ∧
                      (∀m. m ≤ n ⇒ bounded (IMAGE (diff m f) 𝕌(:real))) }
End

Definition CinftyR_def:
    CinftyR = { f | (∀n x. higher_differentiable n f x) ∧
                           (∀n. bounded (IMAGE (diff n f) 𝕌(:real))) }
End

Definition C_b_def:
    C_b ⇔ { f | f continuous_on 𝕌(:real) ∧ bounded (IMAGE f 𝕌(:real)) }
End

Theorem CinftyR_subset_C3:
    CinftyR ⊆ CnR 3
Proof
    rw [CinftyR_def, CnR_def, SUBSET_DEF]
QED

Theorem C3_subset_C1:
    CnR 3 ⊆ CnR 1
Proof
    rw [CnR_def, SUBSET_DEF]
 >> MATCH_MP_TAC higher_differentiable_mono
 >> qexists ‘3’
 >> simp []
QED

Theorem C1_subset_C_b:
    CnR 1 ⊆ C_b
Proof
  rw [CnR_def, C_b_def, SUBSET_DEF]
  >- (rename1 ‘∀x. higher_differentiable 1 f x’ \\
      MP_TAC (Q.SPECL [‘f’, ‘𝕌(:real)’] derivativeTheory.DIFFERENTIABLE_IMP_CONTINUOUS_ON) \\
      rw [] \\
      Suff ‘f differentiable_on 𝕌(:real)’
      >- (simp []) \\
      METIS_TAC [higher_differentiable_1_eq_differentiable_on])
  >> POP_ASSUM (MP_TAC o Q.SPEC ‘0’)
  >> rw[diff_0]
QED

Theorem C3_subset_C_b:
    CnR 3 ⊆ C_b
Proof
    METIS_TAC [C3_subset_C1, C1_subset_C_b, SUBSET_TRANS]
QED

Theorem CinftyR_subset_C_b:
    CinftyR ⊆ C_b
Proof
    METIS_TAC [CinftyR_subset_C3, C3_subset_C_b, SUBSET_TRANS]
QED

Definition Lipschitz_fun_def:
  Lipschitz_fun (f: real -> real) ⇔ ∃ l. (0 < l) ∧ (∀ x y. abs (f x - f y) ≤ l * abs (x - y))
End

Definition C_bounded_lipschitz_def:
    C_bounded_lipschitz ⇔ { f | Lipschitz_fun f ∧ bounded (IMAGE f 𝕌(:real)) }
End

Theorem class_lipschitz_subset_C_b:
    C_bounded_lipschitz ⊆ C_b
Proof
    rw [C_bounded_lipschitz_def, C_b_def, SUBSET_DEF]
 >> rename1 ‘Lipschitz_fun f’
 >> fs [Lipschitz_fun_def, continuous_on_def, netsTheory.WITHIN_UNIV,
        continuous_at, metricTheory.dist]
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> qexists ‘e / l’
 >> CONJ_TAC
 >- (simp [REAL_LT_DIV])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘∀x y. _’ (MP_TAC o Q.SPECL [‘x'’, ‘x’])
 >> rw []
 >> ‘l ≠ 0’ by METIS_TAC [REAL_POS_NZ]
 >> MP_TAC (Q.SPECL [‘abs (f x' − (f:real -> real) x)’, ‘l * abs (x' − x)’, ‘e’] REAL_LET_TRANS)
 >> simp []
 >> STRIP_TAC
 >> Suff ‘l * abs (x' − x) < e’
 >- (fs [])
 >> MP_TAC (Q.SPECL [‘l’, ‘abs (x' − x)’, ‘e / l’] REAL_LT_LMUL_IMP)
 >> simp []
QED

Theorem higher_differentiable_bounded_imp_lipschitz:
    ∀f. (∀x. higher_differentiable 1 f x) ∧
        bounded (IMAGE (diff 1 f) 𝕌(:real)) ⇒
        Lipschitz_fun f
Proof
    rpt STRIP_TAC
 >> ‘∀x. f contl x’ by METIS_TAC [higher_differentiable_imp_continuous,
                                  GSYM limTheory.contl_eq_continuous_at]
 >> ‘∀x. f differentiable x’ by fs [higher_differentiable_1_eq_differentiable,
                                    GSYM limTheory.differentiable_alt]
 >> fs [Lipschitz_fun_def, bounded_def, diff1_def, higher_differentiable_1]
 >> Cases_on ‘a = 0’
 >- (Know ‘∀x. (f diffl 0) x’
     >- (GEN_TAC \\
         Q.PAT_X_ASSUM ‘∀x. ∃y. (f diffl y) x’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
         Q.PAT_X_ASSUM ‘∀x. (∃x'. x = @y. (f diffl y) x') ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘y’) \\
         gs [REAL_ABS_LE0] \\
         Know ‘(∃x'. y = @y. (f diffl y) x')’
         >- (qexists ‘x’ \\
             SELECT_ELIM_TAC \\
             CONJ_TAC
             >- (qexists ‘y’ \\
                 simp []) \\
             qx_gen_tac ‘z’ \\
             STRIP_TAC \\
             MATCH_MP_TAC limTheory.DIFF_UNIQ \\
             qexistsl [‘f’, ‘x’] \\
             rw []) \\
     DISCH_THEN (fs o wrap)) \\
     DISCH_TAC \\
     qexists ‘1’ \\
     gs [] \\
     MP_TAC (Q.SPEC ‘f’ limTheory.DIFF_ISCONST_ALL) \\
     gs [] \\
     STRIP_TAC \\
     ‘∀x y. f x - f y = 0’ by rw [REAL_SUB_0] \\
     POP_ASSUM (rw o wrap))
 >> qexists ‘a’
 >> sg ‘0 < a’
 >- (Q.PAT_X_ASSUM ‘∀x. ∃y. (f diffl y) x’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     Q.PAT_X_ASSUM ‘∀x. (∃x'. x = @y. (f diffl y) x') ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘y’) \\
     gs [REAL_ABS_LE0] \\
     Know ‘(∃x'. y = @y. (f diffl y) x')’
     >- (qexists ‘x’ \\
         SELECT_ELIM_TAC \\
         CONJ_TAC
         >- (qexists ‘y’ \\
             simp []) \\
         qx_gen_tac ‘z’ \\
         STRIP_TAC \\
         MATCH_MP_TAC limTheory.DIFF_UNIQ \\
         qexistsl [‘f’, ‘x’] \\
         rw []) \\
     DISCH_THEN (fs o wrap) \\
     ‘0 ≤ abs y’ by rw [ABS_POS] \\
     ‘0 ≤ a’ by METIS_TAC [REAL_LE_TRANS] \\
     METIS_TAC [REAL_LT_LE])
 >> simp []
 >> rpt GEN_TAC
 >> Cases_on ‘x = y’
 >- (rw [GSYM REAL_SUB_0])
 >> Cases_on ‘x < y’
 >- (MP_TAC (Q.SPECL [‘f’, ‘x’, ‘y’] limTheory.MVT) \\
     simp [] \\
     STRIP_TAC \\
     ‘abs (f y − f x) = abs (l * (y − x))’ by rw [abs] \\
     ‘abs (l * (y − x)) = abs l * abs (y - x)’ by rw [ABS_MUL] \\
     Q.PAT_X_ASSUM ‘∀x. (∃x'. x = @y. (f diffl y) x') ⇒ abs x ≤ a’ (STRIP_ASSUME_TAC o Q.SPEC ‘l’) \\
     Know ‘(∃x'. l = @y. (f diffl y) x')’
     >- (qexists ‘z’ \\
         SELECT_ELIM_TAC \\
         CONJ_TAC
         >- (qexists ‘l’ \\
             simp []) \\
         qx_gen_tac ‘r’ \\
         STRIP_TAC \\
         MATCH_MP_TAC limTheory.DIFF_UNIQ \\
         qexistsl [‘f’, ‘z’] \\
         rw []) \\
     DISCH_THEN (fs o wrap) \\
     ‘0 ≤ abs (y − x)’ by METIS_TAC [ABS_POS] \\
     ‘abs l * abs (y − x) ≤ a * abs (y − x)’ by METIS_TAC [REAL_LE_RMUL_IMP] \\
     gs [ABS_SUB])
 >> fs [REAL_NOT_LT]
 >> ‘y < x’ by  METIS_TAC [REAL_LT_LE]
 >> MP_TAC (Q.SPECL [‘f’, ‘y’, ‘x’] limTheory.MVT)
 >> simp []
 >> STRIP_TAC
 >> ‘abs (f x − f y) = abs (l * (x − y))’ by rw [abs]
 >> ‘abs (l * (x − y)) = abs l * abs (x - y)’ by rw [ABS_MUL]
 >> Q.PAT_X_ASSUM ‘∀x. (∃x'. x = @y. (f diffl y) x') ⇒ abs x ≤ a’ (STRIP_ASSUME_TAC o Q.SPEC ‘l’)
 >> Know ‘(∃x'. l = @y. (f diffl y) x')’
    >- (qexists ‘z’ \\
        SELECT_ELIM_TAC \\
        CONJ_TAC
        >- (qexists ‘l’ \\
            simp []) \\
        qx_gen_tac ‘r’ \\
        STRIP_TAC \\
        MATCH_MP_TAC limTheory.DIFF_UNIQ \\
        qexistsl [‘f’, ‘z’] \\
        rw [])
 >> DISCH_THEN (fs o wrap)
QED

Theorem C_infty_subset_class_lipschitz:
    CinftyR ⊆ C_bounded_lipschitz
Proof
    rw [C_bounded_lipschitz_def, CinftyR_def, SUBSET_DEF]
 >- (rename1 ‘Lipschitz_fun f’ \\
     Q.PAT_X_ASSUM ‘∀n x. higher_differentiable n f x’ (MP_TAC o Q.SPEC ‘1’) \\
     Q.PAT_X_ASSUM ‘∀n. _’ (MP_TAC o Q.SPEC ‘1’) \\
     METIS_TAC [higher_differentiable_bounded_imp_lipschitz])
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘0’))
 >> simp []
QED

Theorem in_borel_measurable_CnR:
  ∀f. f IN CnR 3 ⇒
      f ∈ borel_measurable borel
Proof
  rpt STRIP_TAC
  >> Know ‘f IN C_b’
  >- (MP_TAC (C3_subset_C_b) \\
      fs [SUBSET_DEF])
  >> DISCH_TAC
  >> fs [C_b_def]
  >> MP_TAC (Q.SPEC ‘f’ in_borel_measurable_continuous_on)
  >> gs []
QED

(* ------------------------------------------------------------------------- *)
(*  Add to lebeguesTheory                                                    *)
(* ------------------------------------------------------------------------- *)

Theorem integrable_cdiv:
  ∀m f c.
    measure_space m ∧ integrable m f ∧ c ≠ 0 ⇒
    integrable m (λx. f x / Normal c)
Proof
  rw [extreal_div_def, extreal_inv_def, Once mul_comm]
  >> MATCH_MP_TAC integrable_cmul >> art []
QED

Theorem integrable_bounded_continuous:
    ∀p X f. prob_space p ∧
            real_random_variable X p ∧
            f ∈ C_b ⇒
            integrable p (Normal ∘ f ∘ real ∘ X)
Proof
    rw [C_b_def, bounded_def]
 >> MP_TAC (Q.SPECL [‘p’, ‘λx. Normal a’, ‘Normal ∘ f ∘ real ∘ X’] integrable_bounded)
 >> fs [prob_space_def]
 >> impl_tac
 >- (CONJ_TAC
     >- (MATCH_MP_TAC integrable_const \\
         fs []) \\
     CONJ_TAC
     >- (irule IN_MEASURABLE_BOREL_COMP_BOREL \\
         qexistsl [‘Normal o f o real’, ‘X’] \\
         fs [real_random_variable, p_space_def, events_def] \\
         MP_TAC (real_in_borel_measurable) \\
         DISCH_TAC \\
         MP_TAC (Q.SPEC ‘f’ in_borel_measurable_continuous_on) \\
         rw [] \\
         Know ‘Normal ∘ f ∈ Borel_measurable borel’
         >- (irule IN_MEASURABLE_BOREL_IMP_BOREL' \\
             simp [sigma_algebra_borel]) \\
         DISCH_TAC \\
         irule IN_MEASURABLE_BOREL_IMP_BOREL' \\
         simp [SIGMA_ALGEBRA_BOREL] \\
         irule in_measurable_borel_comp_borel \\
         qexistsl [‘f’, ‘real’] \\
         rw []) \\
     qx_gen_tac ‘x’ \\
     STRIP_TAC \\
     Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘f (real (X x))’) \\
     Know ‘∃x'. f (real (X x)) = f x'’
     >- (qexists ‘real (X x)’ \\
         simp []) \\
     DISCH_THEN (fs o wrap) \\
     ‘abs (Normal (f (real (X x)))) = Normal (abs (f (real (X x))))’ by METIS_TAC [extreal_abs_def] \\
     POP_ORW \\
     rw [extreal_le_eq])
 >> simp []
QED

Theorem integrable_bounded_continuous_rv :
    ∀p X f. prob_space p ∧
            random_variable X p borel ∧
            f ∈ C_b ⇒
            integrable p (Normal ∘ f ∘ X)
Proof
  rw [C_b_def, bounded_def]
  >> MP_TAC (Q.SPECL [‘p’, ‘λx. Normal a’, ‘Normal ∘ (f: real -> real) ∘ X’] integrable_bounded)
 >> fs [prob_space_def]
 >> impl_tac
 >- (CONJ_TAC
     >- (MATCH_MP_TAC integrable_const \\
         fs []) \\
     CONJ_TAC
     >- (irule IN_MEASURABLE_BOREL_IMP_BOREL' \\
         fs [random_variable_def, p_space_def, events_def] \\
         MP_TAC (Q.SPEC ‘f’ in_borel_measurable_continuous_on) \\
         rw [] \\
         irule in_measurable_borel_comp_borel \\
         qexistsl [‘f’, ‘X’] \\
         rw []) \\
     rw [] \\
     Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘(f: real -> real) (X x)’) \\
     Know ‘∃x'. f ((X x)) = f x'’
     >- (qexists ‘(X x)’ \\
         simp []) \\
     DISCH_THEN (fs o wrap) \\
     ‘abs (Normal (f ((X x)))) = Normal (abs (f ((X x))))’ by METIS_TAC [extreal_abs_def] \\
     POP_ORW \\
     rw [extreal_le_eq])
 >> simp []
QED

Theorem integrable_sum_cdiv :
    ∀p X s n. prob_space p ∧
              (∀i. real_random_variable (X i) p) ∧
              (∀i. integrable p (X i)) ∧
              0 < s n ∧ s n ≠ +∞ ∧ s n ≠ −∞  ⇒
              integrable p ((λx. ∑ (λi. X i x) (count n) / s n))
Proof
    rpt STRIP_TAC
 >> BETA_TAC
 >> ‘∃r. Normal r = s n’ by METIS_TAC [extreal_cases]
 >> ‘0 < r’ by POP_ASSUM (fs o wrap o SYM)
 >> Know ‘∀x. ∑ (λi. X i x) (count n) / s n = ∑ (λi. X i x) (count n) / Normal r’
 >- (qx_gen_tac ‘x’ \\
     POP_ORW \\
     rw [])
 >> DISCH_TAC
 >> Know ‘integrable p (λx. ∑ (λi. X i x) (count n))’
 >- (HO_MATCH_MP_TAC integrable_sum \\
     fs [prob_space_def, real_random_variable_def, p_space_def])
 >> DISCH_TAC
 >> Know ‘integrable p (λx. ∑ (λi. X i x) (count n) / Normal r)’
 >- (HO_MATCH_MP_TAC integrable_cdiv \\
     simp [] \\
     ‘r ≠ 0’ by METIS_TAC [REAL_LT_IMP_NE] \\
     fs [prob_space_def])
 >> DISCH_TAC
 >> METIS_TAC []
QED

(* ------------------------------------------------------------------------- *)
(*  Add to topologyTheory                                                    *)
(* ------------------------------------------------------------------------- *)

Definition ext_open_def:
  ext_open s ⇔
    open_in (mtop extreal_mr1) s
End

Definition ext_closed_def:
  ext_closed s ⇔ ext_open (UNIV DIFF s)
End

val _ = overload_on ("open", ``ext_open``);
val _ = overload_on ("closed", ``ext_closed``);

Theorem ext_open_univ:
  ext_open UNIV
Proof
  rw [ext_open_def, metricTheory.MTOP_OPEN, metricTheory.mtop, IN_UNIV]
  >> METIS_TAC [REAL_LT_01]
QED

Theorem ext_closed_univ:
  ext_closed UNIV
Proof
  rw [ext_closed_def, ext_open_def, metricTheory.MTOP_OPEN, metricTheory.mtop, IN_UNIV]
QED

Theorem ext_open_closed_compl:
  ∀G. ext_open G ⇒ ext_closed (UNIV DIFF G)
Proof
  rw [ext_open_def, ext_closed_def, IN_UNIV, DIFF_DEF]
QED

Definition ext_CLOSED_interval_def :
    ext_CLOSED_interval (l :(extreal # extreal) list) =
    {x:extreal | FST (HD l) <= x /\ x <= SND (HD l)}
End

val _ = overload_on ("interval", ``ext_CLOSED_interval``);

Theorem ext_lambda_closed_interval :
    ∀(a :extreal) (b :extreal).
      a ≤ b ∧ a ≠ NegInf ∧ a ≠ PosInf ∧ b ≠ NegInf ∧ b ≠ PosInf ⇒
      lambda (real_set (interval [(a,b)])) = b - a
Proof
    rpt STRIP_TAC
 >> ‘∃r. a = Normal r’ by METIS_TAC [extreal_cases]
 >> gs []
 >> ‘∃c. b = Normal c’ by METIS_TAC [extreal_cases]
 >> gs []
 >> rw [ext_CLOSED_interval_def, real_set_def]
 >> qabbrev_tac ‘s = interval [(Normal r, Normal c)]’
 >> ‘{real x | x ≠ PosInf ∧ x ≠ NegInf ∧ Normal r ≤ x ∧ x ≤ Normal c} = real_set s’
   by simp [real_set_def, Abbr ‘s’, ext_CLOSED_interval_def]
 >> POP_ORW
 >> Know ‘real_set s = interval [(r, c)]’
 >- (rw [real_set_def, Abbr ‘s’, ext_CLOSED_interval_def, CLOSED_interval, Once EXTENSION] \\
     EQ_TAC
     >- (DISCH_TAC \\
         POP_ASSUM (Q.X_CHOOSE_THEN `y` STRIP_ASSUME_TAC) \\
         ‘∃d. y = Normal d’ by METIS_TAC [extreal_cases] \\
         gs []) \\
     STRIP_TAC \\
     qexists ‘Normal x’ \\
     rw [])
 >> Rewr'
 >> MP_TAC (Q.SPECL [‘r’, ‘c’] lambda_closed_interval)
 >> simp []
 >> ‘Normal (c - r) = Normal c - Normal r’ by METIS_TAC [extreal_sub_def]
 >> POP_ASSUM (rw o wrap o SYM)
QED

Definition ext_right_open_interval_def:
    ext_right_open_interval a b = {x | a ≤ x ∧ x < (b: extreal)}
End

val _ = overload_on ("right_open_interval", ``ext_right_open_interval``);


Theorem ext_lambda_closed_open_interval :
    ∀(a :extreal) (b :extreal).
      a ≤ b ∧ a ≠ NegInf ∧ a ≠ PosInf ∧ b ≠ NegInf ∧ b ≠ PosInf ⇒
      lambda (real_set (right_open_interval a b)) = b - a
Proof
    rpt STRIP_TAC
 >> ‘∃r. a = Normal r’ by METIS_TAC [extreal_cases]
 >> gs []
 >> ‘∃c. b = Normal c’ by METIS_TAC [extreal_cases]
 >> gs []
 >> rw [ext_right_open_interval_def, real_set_def]
 >> qabbrev_tac ‘s = right_open_interval (Normal r) (Normal c)’
 >> ‘{real x | x ≠ PosInf ∧ x ≠ NegInf ∧ Normal r ≤ x ∧ x < Normal c} = real_set s’
   by simp [real_set_def, Abbr ‘s’, ext_right_open_interval_def]
 >> POP_ORW
 >> Know ‘real_set s = right_open_interval r c’
 >- (rw [real_set_def, Abbr ‘s’, ext_right_open_interval_def, right_open_interval, Once EXTENSION] \\
     EQ_TAC
     >- (DISCH_TAC \\
         POP_ASSUM (Q.X_CHOOSE_THEN `y` STRIP_ASSUME_TAC) \\
         ‘∃d. y = Normal d’ by METIS_TAC [extreal_cases] \\
         gs []) \\
     STRIP_TAC \\
     qexists ‘Normal x’ \\
     rw [])
 >> Rewr'
 >> MP_TAC (Q.SPECL [‘r’, ‘c’] lambda_prop)
 >> simp []
 >> ‘Normal (c - r) = Normal c - Normal r’ by METIS_TAC [extreal_sub_def]
 >> POP_ASSUM (rw o wrap o SYM)
QED


(* ------------------------------------------------------------------------- *)
(*  Local                                                                    *)
(* ------------------------------------------------------------------------- *)

Theorem integrable_CnR_comp[local]:
  ∀p f X.
    prob_space p ∧
    real_random_variable X p ∧
    integrable p X ∧
    f ∈ CnR 3 ⇒
    integrable p (Normal ∘ f ∘ real ∘ X)
Proof
  rpt STRIP_TAC
  >> irule integrable_bounded_continuous
  >> simp []
  >> MP_TAC (C3_subset_C_b)
  >> fs [SUBSET_DEF]
QED

Theorem real_random_variable_CnR_comp[local] :
    ∀p f X.
      prob_space p ∧
      real_random_variable X p ∧
      f ∈ CnR 3 ⇒
      real_random_variable (Normal ∘ f ∘ real ∘ X) p
Proof
    rw [real_random_variable_def, random_variable_def]
 >> simp [p_space_def, events_def]
 >> MP_TAC (C3_subset_C_b)
 >> fs [SUBSET_DEF]
 >> DISCH_THEN (STRIP_ASSUME_TAC o Q.SPEC ‘f’)
 >> gs [C_b_def]
 >> irule IN_MEASURABLE_BOREL_COMP_BOREL
 >> qexistsl [‘Normal o f o real’, ‘X’]
 >> fs [real_random_variable, p_space_def, events_def]
 >> MP_TAC (real_in_borel_measurable)
 >> DISCH_TAC
 >> MP_TAC (Q.SPEC ‘f’ in_borel_measurable_continuous_on)
 >> rw []
 >> Know ‘Normal ∘ f ∈ Borel_measurable borel’
 >- (irule IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> irule IN_MEASURABLE_BOREL_IMP_BOREL'
 >> simp [SIGMA_ALGEBRA_BOREL]
 >> irule in_measurable_borel_comp_borel
 >> qexistsl [‘f’, ‘real’]
 >> rw []
QED

Theorem add_not_infty_alt[local]:
  ∀a b. a + b ≠ +∞ ∧ a ≠ NegInf ∧ b ≠ NegInf ⇒ a ≠ +∞ ∧ b ≠ +∞
Proof
  RW_TAC std_ss []
  >> (CCONTR_TAC \\
      fs [add_infty])
QED

Theorem integrable_alt_def[local] :
    ∀m f. measure_space m ⇒ (integrable m f ⇔
                               f ∈ Borel_measurable (measurable_space m) ∧ ∫ m (abs o f) ≠ PosInf)
Proof
    rw [integrable_def]
 >> ‘∫ m (abs ∘ f) = ∫⁺ m (abs ∘ f)’ by METIS_TAC [integral_abs_pos_fn]
 >> simp [FN_ABS']
 >> ‘∀x. 0 ≤ f⁺ x’ by fs [FN_PLUS_ALT, le_max2]
 >> Know ‘∀x. 0 ≤ f⁻ x’
 >- (rw [FN_MINUS_ALT] \\
     ‘min (f x) 0 ≤ 0’ by rw [min_le2] \\
     qmatch_abbrev_tac ‘0 ≤ -(a: extreal)’ \\
     fs [le_negr])
 >> DISCH_TAC
 >> EQ_TAC >> simp []
 >- (STRIP_TAC \\
    Know ‘∫⁺ m (λx. f⁺ x + f⁻ x) = ∫⁺ m f⁺ + ∫⁺ m f⁻’
    >- (irule pos_fn_integral_add \\
        simp [] \\
        ‘f⁺ ∈ Borel_measurable (measurable_space m) ∧
         f⁻ ∈ Borel_measurable (measurable_space m)’
          by METIS_TAC [IN_MEASURABLE_BOREL_PLUS_MINUS, measure_space_def] \\
        fs []) \\
    METIS_TAC [add_not_infty])
 >> STRIP_TAC
 >> Know ‘∫⁺ m (λx. f⁺ x + f⁻ x) = ∫⁺ m f⁺ + ∫⁺ m f⁻’
 >- (irule pos_fn_integral_add \\
     simp [] \\
     ‘f⁺ ∈ Borel_measurable (measurable_space m) ∧
      f⁻ ∈ Borel_measurable (measurable_space m)’
       by METIS_TAC [IN_MEASURABLE_BOREL_PLUS_MINUS, measure_space_def] \\
     fs [])
 >> DISCH_THEN (fs o wrap)
 >> irule add_not_infty_alt
 >> art []
 >> ‘0 ≤ ∫⁺ m f⁺’ by METIS_TAC [pos_fn_integral_pos]
 >> ‘0 ≤ ∫⁺ m f⁻’ by METIS_TAC [pos_fn_integral_pos]
 >> METIS_TAC [extreal_0_simps, lt_trans]
QED

Theorem integrable_pair_components_finite[local]:
    ∀p q r X Y (n :num).
      prob_space p ∧
      prob_space q ∧ r = p CROSS q ∧
      (∀e1 e2. e1 ∈ events p ∧ e2 ∈ events q ⇒
               e1 × e2 ∈ events r ∧ prob r (e1 × e2) = prob p e1 * prob q e2) ∧
      (∀i. i < n ⇒ integrable p (X i)) ∧
      (∀i. i < n ⇒ integrable q (Y i)) ⇒
      (∀i. i < n ⇒
           integrable r (X i ∘ FST) ∧
           integrable r (Y i ∘ SND))
Proof
    NTAC 7 STRIP_TAC
 >> Know ‘measurable_space (p × q) = measurable_space p × measurable_space q’
 >- (fs [prob_space_def] \\
     irule MEASURABLE_SPACE_PROD \\
     simp [])
 >> DISCH_TAC
 >> ‘sigma_finite_measure_space p ∧ sigma_finite_measure_space q’
   by METIS_TAC [prob_space_def, sigma_finite_measure_space_def, FINITE_IMP_SIGMA_FINITE, extreal_1_simps]
 >> rw []
 >- (Q.PAT_X_ASSUM ‘∀i. i < n ⇒ integrable p (X i)’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) \\
     gs [integrable_alt_def, prob_space_def] \\
     Q.ABBREV_TAC ‘r = p CROSS q’ \\
     Q.ABBREV_TAC ‘A = λi. X i o FST’ \\
     (MP_TAC o (Q.SPECL [‘r’, ‘A (i: num)’]) o
              (INST_TYPE [alpha |-> “:(α # β)”])) integrable_alt_def \\
     Know ‘measure_space r’
     >- (rw [Abbr ‘r’] \\
         irule measure_space_prod_measure \\
         fs [sigma_finite_measure_space_def] \\
         METIS_TAC [FINITE_IMP_SIGMA_FINITE, extreal_1_simps]) \\
     DISCH_TAC \\
     Know ‘X i ∘ FST ∈
           Borel_measurable (measurable_space p × measurable_space q)’
     >- (rw [Abbr ‘A’] \\
         MATCH_MP_TAC MEASURABLE_COMP \\
         qexists ‘(measurable_space p)’ \\
         simp [Abbr ‘r’] \\
         irule MEASURABLE_FST \\
         METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA]) \\
     DISCH_TAC \\
     gs [Abbr ‘r’, Abbr ‘A’] \\
     DISCH_THEN (rw o wrap) \\
     Q.ABBREV_TAC ‘f = abs o X i ∘ FST’ \\
     MP_TAC (Q.SPECL [‘m_space p’, ‘m_space q’, ‘measurable_sets p’, ‘measurable_sets q’,
                      ‘measure p’, ‘measure q’, ‘f’] (cj 5 TONELLI)) \\
     simp [] \\
     Know ‘f ∈ Borel_measurable (measurable_space p × measurable_space q)’
     >- (rw [Abbr ‘f’] \\
         Q.ABBREV_TAC ‘r = p CROSS q’ \\
         fs [] \\
         Q.PAT_X_ASSUM ‘measurable_space r = _’ (fs o wrap o SYM) \\
         irule IN_MEASURABLE_BOREL_ABS' \\
         rw [MEASURE_SPACE_SIGMA_ALGEBRA]) \\
     Rewr \\
     ‘(∀s. FST s ∈ m_space p ∧ SND s ∈ m_space q ⇒ 0 ≤ f s)’ by (rw [Abbr ‘f’, IN_PSPACE_PROD_SIGMA]) \\
     simp [] \\
     DISCH_TAC \\
     Know ‘∫ p (abs ∘ X i) = ∫⁺ p (abs ∘ X i)’ >- (irule integral_pos_fn >> simp []) \\
     DISCH_THEN (fs o wrap) \\
     Know ‘∫ (p × q) f = ∫⁺ (p × q) f’ >- (irule integral_pos_fn >> rw [Abbr ‘f’]) \\
     Rewr' \\
     POP_ORW \\
     rw [Abbr ‘f’] \\
     Know ‘0 ≤ ∫⁺ p (abs ∘ X i)’ >- (irule pos_fn_integral_pos >> simp []) \\
     DISCH_TAC \\
     ‘∫⁺ p (abs ∘ X i) ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_le] \\
     ‘∃a. ∫⁺ p (abs ∘ X i) = Normal a’ by METIS_TAC [extreal_cases] \\
     ‘∫⁺ p (abs ∘ X i) = ∫⁺ p (λx. abs (X i x))’ by METIS_TAC [] \\
     gs [] \\
     fs [pos_fn_integral_const, extreal_1_simps])
 >> Q.PAT_X_ASSUM ‘∀i. i < n ⇒ integrable q (Y i)’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’)
 >> gs [integrable_alt_def, prob_space_def]
 >> Q.ABBREV_TAC ‘r = p CROSS q’
 >> Q.ABBREV_TAC ‘A = λi. Y i o SND’
 >> (MP_TAC o (Q.SPECL [‘r’, ‘A (i: num)’]) o
            (INST_TYPE [alpha |-> “:(α # β)”])) integrable_alt_def
 >> Know ‘measure_space r’
 >- (rw [Abbr ‘r’] \\
     irule measure_space_prod_measure \\
     fs [sigma_finite_measure_space_def] \\
     METIS_TAC [FINITE_IMP_SIGMA_FINITE, extreal_1_simps])
 >> DISCH_TAC
 >> Know ‘Y i ∘ SND ∈
          Borel_measurable (measurable_space p × measurable_space q)’
 >- (rw [Abbr ‘A’] \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     qexists ‘(measurable_space q)’ \\
     simp [Abbr ‘r’] \\
     irule MEASURABLE_SND \\
     METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> DISCH_TAC
 >> gs [Abbr ‘r’, Abbr ‘A’]
 >> DISCH_THEN (rw o wrap)
 >> Q.ABBREV_TAC ‘f = abs o Y i ∘ SND’
 >> MP_TAC (Q.SPECL [‘m_space p’, ‘m_space q’, ‘measurable_sets p’, ‘measurable_sets q’,
                     ‘measure p’, ‘measure q’, ‘f’] (cj 6 TONELLI))
 >> simp []
 >> Know ‘f ∈ Borel_measurable (measurable_space p × measurable_space q)’
 >- (rw [Abbr ‘f’] \\
     Q.ABBREV_TAC ‘r = p CROSS q’ \\
     fs [] \\
     Q.PAT_X_ASSUM ‘measurable_space r = _’ (fs o wrap o SYM) \\
     irule IN_MEASURABLE_BOREL_ABS' \\
     rw [MEASURE_SPACE_SIGMA_ALGEBRA])
 >>  Rewr
 >> ‘(∀s. FST s ∈ m_space p ∧ SND s ∈ m_space q ⇒ 0 ≤ f s)’ by (rw [Abbr ‘f’, IN_PSPACE_PROD_SIGMA])
 >> simp []
 >> DISCH_TAC
 >> Know ‘∫ q (abs ∘ Y i) = ∫⁺ q (abs ∘ Y i)’ >- (irule integral_pos_fn >> simp [])
 >> DISCH_THEN (fs o wrap)
 >> Know ‘∫ (p × q) f = ∫⁺ (p × q) f’ >- (irule integral_pos_fn >> rw [Abbr ‘f’])
 >> Rewr'
 >> POP_ORW
 >> rw [Abbr ‘f’]
 >> Know ‘0 ≤ ∫⁺ q (abs ∘ Y i)’ >- (irule pos_fn_integral_pos >> simp [])
 >> DISCH_TAC
 >> ‘∫⁺ q (abs ∘ Y i) ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_le]
 >> ‘∃a. ∫⁺ q (abs ∘ Y i) = Normal a’ by METIS_TAC [extreal_cases]
 >> ‘∫⁺ q (abs ∘ Y i) = ∫⁺ q (λx. abs (Y i x))’ by METIS_TAC []
 >> gs []
 >> fs [pos_fn_integral_const, extreal_1_simps]
QED

Theorem integrable_fst :
    ∀p q f.
      prob_space p ∧ prob_space q ∧ integrable p f ⇒
      integrable (p CROSS q) (f ∘ FST)
Proof
    rw [prob_space_def]
 >> Q.ABBREV_TAC ‘r = p CROSS q’
 >> ‘sigma_finite_measure_space p ∧ sigma_finite_measure_space q’
   by METIS_TAC [prob_space_def, sigma_finite_measure_space_def, FINITE_IMP_SIGMA_FINITE, extreal_1_simps]
 >> Know ‘measure_space r’
 >- (rw [Abbr ‘r’] \\
     irule measure_space_prod_measure \\
     fs [sigma_finite_measure_space_def] \\
     METIS_TAC [FINITE_IMP_SIGMA_FINITE, extreal_1_simps])
 >> DISCH_TAC
 >> gs [integrable_alt_def]
 >> Know ‘measurable_space (p × q) = measurable_space p × measurable_space q’
 >- (irule MEASURABLE_SPACE_PROD >> simp [])
 >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC MEASURABLE_COMP \\
     qexists ‘(measurable_space p)’ \\
     rw [Abbr ‘r’] \\
     irule MEASURABLE_FST \\
     METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘h = abs o f ∘ FST’
 >> MP_TAC (Q.SPECL [‘m_space p’, ‘m_space q’, ‘measurable_sets p’, ‘measurable_sets q’,
                     ‘measure p’, ‘measure q’, ‘h’] (cj 5 TONELLI))
 >> simp []
 >> Know ‘h ∈ Borel_measurable (measurable_space p × measurable_space q)’
 >- (rw [Abbr ‘h’] \\
     irule IN_MEASURABLE_BOREL_ABS' \\
     METIS_TAC [Abbr ‘r’, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> Rewr
 >> ‘(∀s. FST s ∈ m_space p ∧ SND s ∈ m_space q ⇒ 0 ≤ h s)’ by (rw [Abbr ‘h’, IN_PSPACE_PROD_SIGMA])
 >> simp []
 >> DISCH_TAC
 >> Know ‘∫ r h = ∫⁺ r h’ >- (irule integral_pos_fn >> simp [Abbr ‘h’])
 >> DISCH_THEN (fs o wrap)
 >> rw [Abbr ‘h’]
 >> Know ‘0 ≤ ∫⁺ p (λx. abs (f x))’ >- (irule pos_fn_integral_pos >> simp [])
 >> DISCH_TAC
 >> ‘∫⁺ p (λx. abs (f x)) ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_le]
 >> Know ‘∫ p (abs o f) = ∫⁺ p (abs o f)’ >- (irule integral_pos_fn >> rw [])
 >> DISCH_TAC
 >> ‘∫⁺ p (abs o f) = ∫⁺ p (λx. abs (f x))’ by METIS_TAC []                                                  >> ‘∃a. ∫⁺ p (λx. abs (f x)) = Normal a’ by METIS_TAC [extreal_cases]
 >> gs []
 >> fs [pos_fn_integral_const, extreal_1_simps]
QED

Theorem integrable_snd :
    ∀p q f.
      prob_space p ∧ prob_space q ∧ integrable q f ⇒
      integrable (p CROSS q) (f ∘ SND)
Proof
    rw [prob_space_def]
 >> Q.ABBREV_TAC ‘r = p CROSS q’
 >> ‘sigma_finite_measure_space p ∧ sigma_finite_measure_space q’
   by METIS_TAC [prob_space_def, sigma_finite_measure_space_def, FINITE_IMP_SIGMA_FINITE, extreal_1_simps]
 >> Know ‘measure_space r’
 >- (rw [Abbr ‘r’] \\
     irule measure_space_prod_measure \\
     fs [sigma_finite_measure_space_def] \\
     METIS_TAC [FINITE_IMP_SIGMA_FINITE, extreal_1_simps])
 >> DISCH_TAC
 >> gs [integrable_alt_def]
 >> Know ‘measurable_space (p × q) = measurable_space p × measurable_space q’
 >- (irule MEASURABLE_SPACE_PROD >> simp [])
 >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC MEASURABLE_COMP \\
     qexists ‘(measurable_space q)’ \\
     rw [Abbr ‘r’] \\
     irule MEASURABLE_SND \\
     METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘h = abs o f ∘ SND’
 >> MP_TAC (Q.SPECL [‘m_space p’, ‘m_space q’, ‘measurable_sets p’, ‘measurable_sets q’,
                     ‘measure p’, ‘measure q’, ‘h’] (cj 6 TONELLI))
 >> simp []
 >> Know ‘h ∈ Borel_measurable (measurable_space p × measurable_space q)’
 >- (rw [Abbr ‘h’] \\
     irule IN_MEASURABLE_BOREL_ABS' \\
     METIS_TAC [Abbr ‘r’, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> Rewr
 >> ‘(∀s. FST s ∈ m_space p ∧ SND s ∈ m_space q ⇒ 0 ≤ h s)’ by (rw [Abbr ‘h’, IN_PSPACE_PROD_SIGMA])
 >> simp []
 >> DISCH_TAC
 >> Know ‘∫ r h = ∫⁺ r h’ >- (irule integral_pos_fn >> simp [Abbr ‘h’])
 >> DISCH_THEN (fs o wrap)
 >> rw [Abbr ‘h’]
 >> Know ‘0 ≤ ∫⁺ q (λy. abs (f y))’ >- (irule pos_fn_integral_pos >> simp [])
 >> DISCH_TAC
 >> ‘∫⁺ q (λy. abs (f y)) ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_le]
 >> Know ‘∫ q (abs o f) = ∫⁺ q (abs o f)’ >- (irule integral_pos_fn >> rw [])
 >> DISCH_TAC
 >> ‘∫⁺ q (abs o f) = ∫⁺ q (λy. abs (f y))’ by METIS_TAC []
 >> ‘∃a. ∫⁺ q (λy. abs (f y)) = Normal a’ by METIS_TAC [extreal_cases]
 >> gs []
 >> fs [pos_fn_integral_const, extreal_1_simps]
QED

val expectation_compose_tactic =
    simp [] >> STRIP_TAC >> gs []
    >> irule integral_cong
    >> gs [] >> rw []
    >> Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’)
    >> gs [p_space_def]
    >> ‘∃a. f x = Normal a’ by METIS_TAC [extreal_cases]
    >> POP_ORW >> rw [integral_const];

Theorem expectation_compose_fst :
    ∀p q f.
      prob_space p ∧ prob_space q ∧
      (∀x. x IN p_space p ⇒ (f x) ≠ PosInf ∧ (f x) ≠ NegInf) ∧
      integrable p f ⇒
      expectation p f = expectation (p CROSS q) (f ∘ FST)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘r = p CROSS q’
 >> ‘integrable (p × q) (f ∘ FST)’ by METIS_TAC [integrable_fst]
 >> fs [prob_space_def, expectation_def]
 >> Know ‘measurable_space (p × q) = measurable_space p × measurable_space q’
 >- (rw [Abbr ‘r’] \\
     irule MEASURABLE_SPACE_PROD \\
     simp [])
 >> DISCH_TAC
 >> ‘sigma_finite_measure_space p ∧ sigma_finite_measure_space q’
   by METIS_TAC [prob_space_def, sigma_finite_measure_space_def, FINITE_IMP_SIGMA_FINITE, extreal_1_simps]
 >> rw []
 >> gs [integrable_alt_def]
 >> Know ‘f o FST ∈ Borel_measurable (measurable_space p × measurable_space q)’
 >- (MATCH_MP_TAC MEASURABLE_COMP \\
     qexists ‘(measurable_space p)’ \\
     art [] \\
     irule MEASURABLE_FST \\
     METIS_TAC [MEASURE_SPACE_SIGMA_ALGEBRA])
 >> DISCH_TAC
 >> Know ‘∫⁺ (p × q) (abs ∘ f ∘ FST) ≠ +∞’
 >- (Q.ABBREV_TAC ‘h = f o FST’ \\
     ‘h ∈ Borel_measurable (measurable_space r)’ by fs [] \\
     Know ‘measure_space r’
     >- (rw [Abbr ‘r’] \\
         irule measure_space_prod_measure \\
         fs [sigma_finite_measure_space_def] \\
         METIS_TAC [FINITE_IMP_SIGMA_FINITE, extreal_1_simps]) \\
     DISCH_TAC \\
     rw [GSYM integrable_abs_alt] \\
     irule integrable_abs \\
     simp [Abbr ‘h’, Abbr ‘r’])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘m_space p’, ‘m_space q’, ‘measurable_sets p’, ‘measurable_sets q’,
                     ‘measure p’, ‘measure q’, ‘f o FST’] (cj 10 FUBINI))
 >> expectation_compose_tactic
QED

Theorem expectation_compose_snd :
    ∀p q f.
      prob_space p ∧ prob_space q ∧
      (∀x. x IN p_space q ⇒ (f x) ≠ PosInf ∧ (f x) ≠ NegInf) ∧
      integrable q f ⇒
      expectation q f = expectation (p CROSS q) (f ∘ SND)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘r = p CROSS q’
 >> ‘integrable (p × q) (f ∘ SND)’ by METIS_TAC [integrable_snd]
 >> fs [prob_space_def, expectation_def]
 >> Know ‘measurable_space (p × q) = measurable_space p × measurable_space q’
 >- (rw [Abbr ‘r’] \\
     irule MEASURABLE_SPACE_PROD \\
     simp [])
 >> DISCH_TAC
 >> ‘sigma_finite_measure_space p ∧ sigma_finite_measure_space q’
   by METIS_TAC [prob_space_def, sigma_finite_measure_space_def, FINITE_IMP_SIGMA_FINITE, extreal_1_simps]
 >> rw []
 >> gs [integrable_alt_def]
 >> Know ‘f o SND ∈ Borel_measurable (measurable_space p × measurable_space q)’
 >- (MATCH_MP_TAC MEASURABLE_COMP \\
     qexists ‘(measurable_space q)’ \\
     art [] \\
     irule MEASURABLE_SND \\
     METIS_TAC [MEASURE_SPACE_SIGMA_ALGEBRA])
 >> DISCH_TAC
 >> Know ‘∫⁺ (p × q) (abs ∘ f ∘ SND) ≠ +∞’
 >- (Q.ABBREV_TAC ‘h = f o SND’ \\
     ‘h ∈ Borel_measurable (measurable_space r)’ by fs [] \\
     Know ‘measure_space r’
     >- (rw [Abbr ‘r’] \\
         irule measure_space_prod_measure \\
         fs [sigma_finite_measure_space_def] \\
         METIS_TAC [FINITE_IMP_SIGMA_FINITE, extreal_1_simps]) \\
     DISCH_TAC \\
     rw [GSYM integrable_abs_alt] \\
     irule integrable_abs \\
     simp [Abbr ‘h’, Abbr ‘r’])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘m_space p’, ‘m_space q’, ‘measurable_sets p’, ‘measurable_sets q’,
                     ‘measure p’, ‘measure q’, ‘f o SND’] (cj 9 FUBINI))
 >> expectation_compose_tactic
QED

Theorem clt_real_random_variable_partial_sum1 :
    ∀p X Y Z f n.
      prob_space p ∧
      (∀i. real_random_variable (X i) p) ∧
      (∀i. real_random_variable (Y i) p) ∧
      (∀i. integrable p (X i)) ∧
      (∀i. integrable p (Y i)) ∧
      Z = (λj x. ∑ (λi. Y i x) (count j) +
                 ∑ (λi. X i x) (count n DIFF count1 j)) ⇒
      ∀j. j < n ⇒ real_random_variable (Z j) p ∧ integrable p (Z j)
Proof
  rpt STRIP_TAC
  >- (gs [] \\
      Know ‘real_random_variable (λx. ∑ (λi. Y i x) (count j)) p’
      >- (irule real_random_variable_sum \\
          simp []) \\
      DISCH_TAC \\
      Know ‘real_random_variable (λx. ∑ (λi. X i x) (count n DIFF count1 j)) p’
      >- (irule real_random_variable_sum \\
          simp []) \\
      DISCH_TAC \\
      MP_TAC (Q.SPECL [‘p’, ‘λx. ∑ (λi. Y i x) (count j)’,
                       ‘λx. ∑ (λi. X i x) (count n DIFF count1 j)’] real_random_variable_add) \\
      simp [])
  >> gs []
  >> Know ‘integrable p (λx. ∑ (λi. Y i x) (count j))’
  >- (irule integrable_sum' \\
      fs [prob_space_def])
  >> DISCH_TAC
  >> Know ‘integrable p (λx. ∑ (λi. X i x) (count n DIFF count1 j))’
  >- (irule integrable_sum' \\
      fs [prob_space_def])
  >> DISCH_TAC
  >> MP_TAC (Q.SPECL [‘p’, ‘λx. ∑ (λi. Y i x) (count j)’,
                      ‘λx. ∑ (λi. X i x) (count n DIFF count1 j)’] integrable_add')
  >> fs [prob_space_def]
QED

Theorem clt_real_random_variable_partial_sum :
    ∀p X Y Z f n.
      prob_space p ∧
      (∀i. real_random_variable (X i) p) ∧
      (∀i. real_random_variable (Y i) p) ∧
      (∀i. integrable p (X i)) ∧
      (∀i. integrable p (Y i)) ∧
      Z = (λj x. ∑ (λi. Y i x) (count j) +
                 ∑ (λi. X i x) (count n DIFF count j)) ⇒
      ∀j. j < n ⇒ real_random_variable (Z j) p ∧ integrable p (Z j)
Proof
  rpt STRIP_TAC
  >- (gs [] \\
      Know ‘real_random_variable (λx. ∑ (λi. Y i x) (count j)) p’
      >- (irule real_random_variable_sum \\
          simp []) \\
      DISCH_TAC \\
      Know ‘real_random_variable (λx. ∑ (λi. X i x) (count n DIFF count j)) p’
      >- (irule real_random_variable_sum \\
          simp []) \\
      DISCH_TAC \\
      MP_TAC (Q.SPECL [‘p’, ‘λx. ∑ (λi. Y i x) (count j)’,
                       ‘λx. ∑ (λi. X i x) (count n DIFF count j)’] real_random_variable_add) \\
      simp [])
  >> gs []
  >> Know ‘integrable p (λx. ∑ (λi. Y i x) (count j))’
  >- (irule integrable_sum' \\
      fs [prob_space_def])
  >> DISCH_TAC
  >> Know ‘integrable p (λx. ∑ (λi. X i x) (count n DIFF count j))’
  >- (irule integrable_sum' \\
      fs [prob_space_def])
  >> DISCH_TAC
  >> MP_TAC (Q.SPECL [‘p’, ‘λx. ∑ (λi. Y i x) (count j)’,
                   ‘λx. ∑ (λi. X i x) (count n DIFF count j)’] integrable_add')
  >> fs [prob_space_def]
QED

Theorem random_variable_borel_imp_Borel :
    ∀p X.
      prob_space p ∧
      (∀x. x ∈ p_space p ⇒ X x ≠ +∞ ∧ X x ≠ −∞) ∧
      random_variable (real ∘ X) p borel ⇒
      random_variable X p Borel
Proof
    rpt STRIP_TAC
 >> fs [random_variable_def, p_space_def, events_def]
 >> MP_TAC (Q.SPECL [‘(measurable_space p)’, ‘real o X’] IN_MEASURABLE_BOREL_IMP_BOREL')
 >> fs [sigma_algebra_borel, prob_space_def]
 >> Know ‘∀x. x IN m_space p ⇒ (Normal ∘ real ∘ X) x = X x’
 >- (rw [] \\
     Q.PAT_X_ASSUM ‘∀x. x IN m_space p ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     fs [normal_real])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘(measurable_space p)’, ‘Normal ∘ real ∘ X’, ‘X’] IN_MEASURABLE_BOREL_CONG')
 >> fs []
QED

Theorem in_measurable_borel_imp_Borel :
  ∀p X.
    prob_space p ∧
    (∀x. x ∈ p_space p ⇒ X x ≠ +∞ ∧ X x ≠ −∞) ∧
    real ∘ X ∈ borel_measurable (measurable_space p) ⇒
    X ∈ Borel_measurable (measurable_space p)
Proof
  rpt STRIP_TAC
  >> MP_TAC (Q.SPECL [‘(measurable_space p)’, ‘real o X’] IN_MEASURABLE_BOREL_IMP_BOREL')
  >> fs [sigma_algebra_borel, prob_space_def, p_space_def]
  >> Know ‘∀x. x IN m_space p ⇒ (Normal ∘ real ∘ X) x = X x’
  >- (rw [] \\
      Q.PAT_X_ASSUM ‘∀x. x IN m_space p ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
      fs [normal_real])
  >> DISCH_TAC
  >> MP_TAC (Q.SPECL [‘(measurable_space p)’, ‘Normal ∘ real ∘ X’, ‘X’] IN_MEASURABLE_BOREL_CONG')
  >> fs []
QED

Theorem clt_real_random_variable_sum_compose :
    ∀p X s f n. prob_space p ∧
              (∀i. real_random_variable (X i) p) ∧
              (∀i. integrable p (X i)) ∧
              0 < s n ∧ s n ≠ +∞ ∧ s n ≠ −∞ ∧
              f IN CnR 3 ⇒
              real_random_variable (Normal ∘ f ∘ real ∘ ((λx. ∑ (λi. X i x) (count n) / s n))) p
Proof
  rpt STRIP_TAC
  >> Know ‘real_random_variable ((λx. ∑ (λi. X i x) (count n) / s n)) p’
  >- (MATCH_MP_TAC real_random_variable_sum_cdiv \\
      simp [])
  >> DISCH_TAC
  >> Q.ABBREV_TAC ‘R = λx. ∑ (λi. X i x) (count n) / s n’
  >> fs [real_random_variable_def, random_variable_def]
  >> MP_TAC (Q.SPECL [‘(p_space p,events p)’, ‘R’] in_borel_measurable_from_Borel)
  >> fs []
  >> ‘sigma_algebra (p_space p,events p)’ by METIS_TAC [EVENTS_SIGMA_ALGEBRA]
  >> rw []
  >> ‘f ∈ borel_measurable borel’ by METIS_TAC [in_borel_measurable_CnR]
  >> MP_TAC (Q.SPECL [‘(p_space p,events p)’, ‘f’, ‘real ∘ R’, ‘h’] in_measurable_borel_comp_borel)
  >> simp []
  >> STRIP_TAC
  >> dxrule_all_then assume_tac MEASURABLE_COMP
  >> MP_TAC (Q.SPECL [‘f ∘ real ∘ R’, ‘p’] IN_MEASURABLE_BOREL_IMP_BOREL)
  >> fs [p_space_def, events_def]
QED

Theorem clt_expectation_not_infty :
    ∀p X f. prob_space p ∧
            real_random_variable X p ∧
            integrable p X ∧
            f IN CnR 3 ⇒
            expectation p (Normal ∘ f ∘ real ∘ X) ≠ +∞ ∧
            expectation p (Normal ∘ f ∘ real ∘ X) ≠ −∞
Proof
    NTAC 4 STRIP_TAC
 >> MATCH_MP_TAC expectation_finite
 >> simp []
 >> irule integrable_bounded_continuous
 >> simp []
 >> MP_TAC (C3_subset_C_b)
 >> rw [SUBSET_DEF]
QED

Theorem clt_expectation_sum_not_infty :
    ∀p X s R f n.
      prob_space p ∧
      (∀i. real_random_variable (X i) p) ∧
      (∀i. integrable p (X i)) ∧
      (∀i. variance p (X i) < +∞) ∧
      (∀i. expectation p (X i) = 0) ∧
      0 < s n ∧ s n ≠ +∞ ∧ s n ≠ −∞ ∧
      R = (λn x. ∑ (λi. X i x) (count n) / s n) ∧
      f ∈ CnR 3 ⇒
        expectation p (Normal ∘ f ∘ real ∘ R n) ≠ +∞ ∧
        expectation p (Normal ∘ f ∘ real ∘ R n) ≠ −∞
Proof
    NTAC 7 STRIP_TAC
 >> MATCH_MP_TAC expectation_finite
 >> simp []
 >> irule integrable_bounded_continuous
 >> simp []
 >> CONJ_TAC
 >- (MP_TAC (C3_subset_C_b) \\
     rw [SUBSET_DEF])
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘s’] real_random_variable_sum_cdiv)
 >> simp []
QED

Theorem add_sub_cancel [local]:
    ∀x y z. x ≠ −∞ ∧ x ≠ +∞ ∧
            y ≠ −∞ ∧ y ≠ +∞ ∧
            z ≠ −∞ ∧ z ≠ +∞ ⇒
            x + y - (y + z) = x - z
Proof
    rw []
 >> ‘∃a. x = Normal a’ by METIS_TAC [extreal_cases]
 >> POP_ORW
 >> ‘∃b. y = Normal b’ by METIS_TAC [extreal_cases]
 >> POP_ORW
 >> ‘∃c. z = Normal c’ by METIS_TAC [extreal_cases]
 >> POP_ORW
 >> ‘Normal a + Normal b = Normal (a + b)’ by fs [extreal_add_def]
 >> POP_ORW
 >> ‘Normal b + Normal c = Normal (b + c)’ by fs [extreal_add_def]
 >> POP_ORW
 >> ‘Normal a − Normal c = Normal (a - c)’ by fs [extreal_sub_def]
 >> POP_ORW
 >> ‘Normal (a + b) − Normal (b + c) = Normal (a + b - (b + c))’ by fs [extreal_sub_def]
 >> POP_ORW
 >> rw [extreal_11]
 >> REAL_ARITH_TAC
QED



Definition third_moment_def:
  third_moment p X = central_moment p X 3
End

Definition absolute_third_moment_def:
  absolute_third_moment p X  = absolute_moment p X 0 3
End

Definition second_moments_def:
  second_moments p X n = SIGMA (λi. central_moment p (X i) 2) (count1 n)
End

Definition third_moments_def:
  third_moments p X n = SIGMA (λi. third_moment p (X i)) (count1 n)
End

Definition ext_normal_density_def:
  ext_normal_density mu sig = Normal o normal_density mu sig o real
End

Definition ext_normal_pmeasure_def :
    ext_normal_pmeasure mu sig s = normal_pmeasure mu sig (real_set s)
End

(********************************* DELETE ******************************)

Definition ext_normal_rv_def :
    ext_normal_rv X p mu sig <=>
    (!x. x IN p_space p ==> X x <> PosInf /\ X x <> NegInf) /\
    normal_rv (real o X) p mu sig
End

Theorem expectation_of_normal_rv :
  !p X mu sig. prob_space p /\ normal_rv X p mu sig ==>
               integrable p (Normal o X) /\ expectation p (Normal o X) = Normal mu
Proof
  cheat
QED

Theorem expectation_of_normal_rv' :
  !p X mu sig. prob_space p /\ ext_normal_rv X p mu sig ==>
               integrable p X /\ expectation p X = Normal mu
Proof
  cheat
QED

(***********************************************************************)


Theorem normal_absolute_third_moment:
    ∀p X sig. normal_rv X p 0 sig ⇒
              absolute_third_moment p (Normal o X) = sqrt (8 / π)  *  variance p (Normal o X)  *
                                                     sqrt (variance p (Normal o X))
Proof
    cheat
QED

Theorem finite_variance_imp_second_moments:
  ∀p X. (∀i. variance p (X i) < PosInf) ⇒
        (∀n. second_moments p X n < PosInf)
Proof
  rw [variance_def, second_moments_def]
  >> ‘∀i. central_moment p (X i) 2 ≠ PosInf’ by METIS_TAC [lt_imp_ne]
  >> Suff ‘∑ (λi. central_moment p (X i) 2) (count1 n) ≠ +∞’
  >- (METIS_TAC [lt_infty])
  >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF
  >> simp []
QED

Theorem second_moments_variance_def:
  ∀p X n. second_moments p X n = ∑ (λi. variance p (X i)) (count1 n)
Proof
  rw [second_moments_def, variance_def]
QED

Theorem second_moments_pos:
  ∀p X n. prob_space p ⇒ 0 ≤ second_moments p X n
Proof
  rw [second_moments_variance_def]
  >> irule EXTREAL_SUM_IMAGE_POS
  >> simp [variance_pos]
QED

Theorem ext_normal_rv_integrable :
  ∀p X mu sig.
    0 < sig ∧ prob_space p ∧ ext_normal_rv X p mu sig ⇒
    integrable p X
Proof
  rpt STRIP_TAC
  >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘mu’, ‘sig’] expectation_of_normal_rv')
  >> simp []
QED

(* ------------------------------------------------------------------------- *)
(*  Lindeberg Replacement Trick                                              *)
(* ------------------------------------------------------------------------- *)

Theorem partial_sum_telescoping:
    ∀(X: num -> 'a -> real) Y Z (n:num) x (j:num).
         j + 1 < n ∧
         (∀j. Z j x = ∑ (λi. Y i x) (count j) +
                      ∑ (λi. X i x) (count n DIFF count (SUC j))) ⇒
         Y j x + Z j x = X (j + 1) x + Z (j + 1) x
Proof
    rw [ADD1]
 >> ‘Y j x + (∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count (j + 1))) =
     Y j x + ∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count (j + 1))’ by rw [REAL_ADD_ASSOC]
 >> POP_ORW
 >> Know ‘Y j x + ∑ (λi. Y i x) (count j) = ∑ (λi. Y i x) (count (j + 1))’
 >- (‘Y j x =  ∑ (λi. Y i x) {j}’ by rw[REAL_SUM_IMAGE_SING] \\
    (MP_TAC o (Q.SPECL [`{j}` ,`count j`]) o
              (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_DISJOINT_UNION \\
     impl_tac
     >- (simp []) \\
     DISCH_TAC \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘λi. Y i x’) \\
     STRIP_TAC \\
     ‘{j} ∪ (count j) = count (j + 1)’ by rw [Once EXTENSION] \\
     FULL_SIMP_TAC std_ss [])
 >> DISCH_THEN (fs o wrap)
 >> ‘X (j + 1) x + (∑ (λi. Y i x) (count (j + 1)) + ∑ (λi. X i x) (count n DIFF count (j + 2))) =
     X (j + 1) x + ∑ (λi. Y i x) (count (j + 1)) + ∑ (λi. X i x) (count n DIFF count (j + 2))’
     by rw [REAL_ADD_ASSOC]
 >> rw [REAL_ADD_ASSOC]
 >> ‘X (j + 1) x + ∑ (λi. Y i x) (count (j + 1)) + ∑ (λi. X i x) (count n DIFF count (j + 2)) =
     ∑ (λi. Y i x) (count (j + 1)) + X (j + 1) x  + ∑ (λi. X i x) (count n DIFF count (j + 2))’
     by rw [REAL_ADD_COMM]
 >> POP_ORW
 >> Know ‘X (j + 1) x  + ∑ (λi. X i x) (count n DIFF count (j + 2)) =
          ∑ (λi. X i x) (count n DIFF count (j + 1))’
 >- (‘X (j + 1) x =  ∑ (λi. X i x) {j + 1}’ by rw[REAL_SUM_IMAGE_SING] \\
    (MP_TAC o (Q.SPECL [`{j + 1}` ,`(count n DIFF count (j + 2))`]) o
              (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_DISJOINT_UNION \\
    impl_tac
    >- (simp []) \\
    DISCH_TAC \\
    POP_ASSUM (MP_TAC o Q.SPEC ‘λi. X i x’) \\
    STRIP_TAC \\
    Know ‘{j + 1} ∪ (count n DIFF count (j + 2)) = (count n DIFF count (j + 1))’
    >- (simp [ADD1, count_def, DIFF_DEF, EXTENSION]) \\
    DISCH_TAC \\
     FULL_SIMP_TAC std_ss [])
 >> STRIP_TAC
 >> fs [GSYM REAL_ADD_ASSOC]
QED

Theorem SUM_SUB_GEN :
    ∀(f:num -> extreal) n.
      (∀x. f x ≠ NegInf ∧ f x ≠ PosInf) ⇒
      ∑ (λj. f j − f (j + 1)) (count n) = f 0 − f n
Proof
    rpt STRIP_TAC
 >> Induct_on ‘n’
 >- (rw [EXTREAL_SUM_IMAGE_COUNT_ZERO, sub_refl])
 >> ‘count1 n = count n ∪ {n}’ by rw [Once EXTENSION]
 >> POP_ORW
 >> Know ‘∑ (λj. f j − f (j + 1)) (count n ∪ {n}) =
          ∑ (λj. f j − f (j + 1)) (count n) + (f n - f (SUC n))’
 >- (Q.ABBREV_TAC ‘h = λj. f j − f (j + 1)’ \\
     (MP_TAC o (Q.SPECL [‘count n’, ‘{n}’]) o
             (INST_TYPE [alpha |-> ``:num``])) EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
     simp [] \\
     DISCH_TAC \\
     POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘h’) \\
     Know ‘∀x. x < n ∨ x = n ⇒ h x ≠ −∞’
     >- (fs [Abbr ‘h’] \\
         Know ‘∀x. x < n ∨ x = n ⇒ (λj. f j) x ≠ −∞’
         >- (BETA_TAC \\
             rw [GSYM le_lt]) \\
         DISCH_TAC \\
         Know ‘∀x. x < n ∨ x = n ⇒ (λj. f (j + 1)) x ≠ −∞’
         >- (BETA_TAC \\
             rw [GSYM le_lt]) \\
         DISCH_TAC \\
         fs [sub_not_infty]) \\
     DISCH_TAC \\
     Know ‘∀x. x < n ∨ x = n ⇒ h x ≠ +∞’
     >- (fs [Abbr ‘h’] \\
         Know ‘∀x. x < n ∨ x = n ⇒ (λj. f j) x ≠ +∞’
         >- (BETA_TAC \\
             rw [GSYM le_lt]) \\
         DISCH_TAC \\
         Know ‘∀x. x < n ∨ x = n ⇒ (λj. f (j + 1)) x ≠ +∞’
         >- (BETA_TAC \\
             rw [GSYM le_lt]) \\
         DISCH_TAC \\
         fs [sub_not_infty]) \\
     DISCH_TAC \\
     ‘∑ h (count n ∪ {n}) = ∑ h (count n) + h n’ by METIS_TAC [] \\
     POP_ORW \\
     Q.PAT_X_ASSUM ‘ ∑ h (count n) = _’ (rw o wrap) \\
     rw [Abbr ‘h’, ADD1] \\
     DISCH_THEN (fs o wrap) \\
     ‘f 0 ≠ NegInf ∧ f 0 ≠ PosInf’ by METIS_TAC [] \\
     ‘f n ≠ NegInf ∧ f n ≠ PosInf’ by METIS_TAC [] \\
     ‘f (SUC n) ≠ NegInf ∧ f (SUC n) ≠ PosInf’ by METIS_TAC [])
 >> Rewr'
 >> POP_ORW
 >> ‘f 0 ≠ NegInf ∧ f 0 ≠ PosInf’ by METIS_TAC []
 >> ‘f n ≠ NegInf ∧ f n ≠ PosInf’ by METIS_TAC []
 >> ‘f (SUC n) ≠ NegInf ∧ f (SUC n) ≠ PosInf’ by METIS_TAC []
 >> rw [add2_sub2]
 >> METIS_TAC [add_sub_cancel]
QED

Theorem SUM_SUB_GEN_WEAKEN :
    ∀f n.
      (∀j. j ≤ n ⇒ f j ≠ +∞ ∧ f j ≠ −∞) ⇒
      ∑ (λj. f j − f (j + 1)) (count n) = f 0 − f n
Proof
  rpt STRIP_TAC
  >> Q.ABBREV_TAC ‘g = λi. if i ≤ n then f i else 0’
  >> Know ‘∀i. g i ≠ +∞ ∧ g i ≠ −∞’
  >- (GEN_TAC \\
      Cases_on ‘n < i’ >- (fs [Abbr ‘g’]) \\
      fs [NOT_LESS] \\
      Cases_on ‘i < n’
      >- (Q.PAT_X_ASSUM ‘∀j. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) \\
          fs [Abbr ‘g’]) \\
      fs [NOT_LESS] \\
      ‘i = n’ by fs [GSYM EQ_LESS_EQ] \\
      fs [Abbr ‘g’])
  >> STRIP_TAC
  >> MP_TAC (Q.SPECL [‘g’, ‘n’] SUM_SUB_GEN)
  >> fs []
  >> DISCH_TAC
  >> Know ‘∑ (λj. g j − g (j + 1)) (count n) =
           ∑ (λj. f j − f (j + 1)) (count n)’
  >- (irule EXTREAL_SUM_IMAGE_EQ \\
      simp [] \\
      CONJ_TAC
      >- (rw [Abbr ‘g’]) \\
      DISJ2_TAC \\
      rw [Abbr ‘g’] \\
      fs [sub_not_infty])
  >> DISCH_THEN (fs o wrap o SYM)
  >> rw [Abbr ‘g’]
QED


Theorem abs_3[local]:
    ∀x. abs (x pow 3) = (abs x) pow 3
Proof
    RW_TAC std_ss []
 >> Cases_on ‘x = PosInf’
 >- (gs [] \\
     EVAL_TAC)
 >> Cases_on ‘x = NegInf’
 >- (gs [] \\
     EVAL_TAC)
 >> ‘∃r. x = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ORW
 >> ‘Normal r pow 3 = Normal (r pow 3)’ by rw [extreal_pow_def]
 >> ‘abs (Normal r pow 3) = abs (Normal (r pow 3))’ by rw []
 >> ‘abs (Normal (r pow 3)) = Normal (abs (r pow 3))’ by rw [extreal_abs_def]
 >> gs []
 >> ‘abs (Normal r) = Normal (abs r)’ by rw [extreal_abs_def]
 >> ‘Normal (abs r) pow 3 = Normal ((abs r) pow 3)’ by rw [extreal_pow_def]
 >> gs []
 >> rw [POW_ABS]
QED

Theorem clt_expectation_sum_not_infty_normal_rv[local] :
  ∀p N f. prob_space p ∧
          ext_normal_rv N p 0 1 ∧
          f ∈ CnR 3 ⇒
          expectation p (Normal ∘ f ∘ real ∘ N) ≠ +∞ ∧
          expectation p (Normal ∘ f ∘ real ∘ N) ≠ −∞
Proof
  NTAC 4 STRIP_TAC
  >> MATCH_MP_TAC expectation_finite
  >> simp []
  >> irule integrable_bounded_continuous
  >> fs [ext_normal_rv_def, real_random_variable_def, normal_rv_def]
  >> MP_TAC (C3_subset_C_b)
  >> rw [SUBSET_DEF]
  >> METIS_TAC [random_variable_borel_imp_Borel]
QED

Theorem lp_space_imp_L1_space :
    ∀p f m. measure_space m ∧ measure m (m_space m) < +∞ ⇒
            (1 ≤ p ∧ p ≠ +∞ ∧ f ∈ lp_space p m ⇒ f ∈ L1_space m)
Proof
    RW_TAC std_ss []
 >> Cases_on ‘p = 1’
 >- (rw [lp_space_def])
 >> fs [lp_space_alt_finite]
 >> STRONG_CONJ_TAC
 >- (fs [lp_space_def])
 >> STRIP_TAC
 >> rw [abs_pos, powr_1]
 >> MP_TAC (Q.SPECL [‘m’, ‘f’, ‘p’] liapounov_ineq_lemma)
 >> simp [lt_le]
 >> STRIP_TAC
 >> Know ‘seminorm p m f ≠ +∞’
 >- (MP_TAC (Q.SPECL [‘p’, ‘m’, ‘f’] lp_space_alt_seminorm) \\
     fs [] \\
     ‘0 < p’ by METIS_TAC [lt_01, lte_trans] \\
     fs [ineq_imp])
 >> DISCH_TAC
 >> Know ‘seminorm p m f ≠ NegInf’
 >- (‘0 ≤ seminorm p m f’ by METIS_TAC [seminorm_pos, lt_01, lte_trans] \\
     METIS_TAC [extreal_0_simps, lt_trans])
 >> DISCH_TAC
 >> ‘∃r. seminorm p m f = Normal r’ by METIS_TAC [extreal_cases]
 >> fs []
 >> rpt (Q.PAT_X_ASSUM ‘T’ (K_TAC))
 >> Know ‘measure m (m_space m) powr (1 − p⁻¹) ≠ +∞ ∧ measure m (m_space m) powr (1 − p⁻¹) ≠ NegInf’
 >- (Know ‘0 ≤ measure m (m_space m)’
     >- (‘m_space m ∈ measurable_sets m’ by METIS_TAC [MEASURE_SPACE_SPACE] \\
         fs [measure_space_def, positive_def] \\
         Q.PAT_X_ASSUM ‘∀s. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘m_space m’)) \\
     DISCH_TAC \\
     Know ‘0 < 1 - inv p’
     >- (‘inv p ≤ 1’ by METIS_TAC [lt_01, inv_le_antimono_imp, inv_one] \\
         ‘0 ≠ p’ by METIS_TAC [lt_01, lte_trans, ineq_imp] \\
         ‘0 ≤ 1 - inv p’ by METIS_TAC [sub_zero_le, inv_not_infty] \\
         CCONTR_TAC \\
         fs [extreal_not_lt] \\
         ‘p = 1’ by METIS_TAC [le_antisym, sub_0, inv_one, lt_01, lte_trans, inv_inj]) \\
     DISCH_TAC \\
     ‘measure m (m_space m) ≠ PosInf ∧ measure m (m_space m) ≠ NegInf’ by
       METIS_TAC [ineq_imp, extreal_0_simps, lt_trans] \\
     ‘∃a. measure m (m_space m) = Normal a’ by METIS_TAC [extreal_cases] \\
     fs [] \\
     rpt (Q.PAT_X_ASSUM ‘T’ (K_TAC)) \\
     ‘0 ≤ Normal a powr (1 − p⁻¹)’ by rw [powr_pos] \\
     ‘Normal a powr (1 − p⁻¹) ≠ −∞’ by METIS_TAC [extreal_0_simps, lt_trans] \\
     art [] \\
     ‘1 - inv p ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_trans] \\
     ‘0 ≠ p’ by METIS_TAC [lt_01, lte_trans, ineq_imp] \\
     ‘1 - inv p ≠ PosInf’ by METIS_TAC [inv_not_infty, extreal_1_simps, sub_not_infty] \\
     ‘∃b. 1 - inv p = Normal b’ by METIS_TAC [extreal_cases] \\
     fs [] \\
      Cases_on ‘a = 0’
     >- (gs [normal_0] \\
         ‘0 < Normal b’ by rw [extreal_0_simps] \\
         METIS_TAC [zero_rpow, extreal_0_simps]) \\
     ‘0 < a’ by METIS_TAC [REAL_LT_LE] \\
     METIS_TAC [normal_powr, extreal_not_infty])
 >> DISCH_TAC
 >> ‘∃d. measure m (m_space m) powr (1 − p⁻¹) = Normal d’ by METIS_TAC [extreal_cases]
 >> fs [extreal_mul_eq]
 >> rpt (Q.PAT_X_ASSUM ‘T’ (K_TAC))
 >> ‘Normal (d * r) < PosInf’ by fs [lt_infty]
 >> METIS_TAC [let_trans, lt_imp_ne]
QED

Theorem clt_integrable_lemma[local] :
    ∀p X.
          prob_space p ∧
          real_random_variable X p ∧
          expectation p (λx. (abs (X x)) pow 3) < PosInf ⇒
          integrable p X ∧ integrable p (λx. (X x)³)
Proof
    NTAC 3 STRIP_TAC
 >> fs [real_random_variable_def, random_variable_def, expectation_def]
 >> Know ‘X ∈ lp_space 3 p’
 >- (fs [lp_space_def, p_space_def, events_def] \\
     ‘∀x. abs (X x) powr 3 = abs (X x) pow 3’ by METIS_TAC [gen_powr, abs_pos] \\
     POP_ORW \\
     Know ‘∫ p (λx. (abs (X x))³) = ∫⁺ p (λx. (abs (X x))³)’
     >- (‘∀x. (abs (X x))³ = abs ((X x)³)’ by rw [abs_3] \\
         POP_ORW \\
         MP_TAC (Q.SPECL [‘p’, ‘λx. (X x) pow 3’] integral_abs_pos_fn) \\
         fs [prob_space_def, o_DEF]) \\
     DISCH_THEN (fs o wrap o SYM)  \\
     METIS_TAC [lt_imp_ne])
 >> DISCH_TAC
 >> Know ‘X ∈ lp_space 1 p’
 >- (MP_TAC (Q.SPECL [‘3’, ‘X’, ‘p’] lp_space_imp_L1_space) \\
     fs [prob_space_def] \\
     ‘(1:extreal) ≤ 3’ by EVAL_TAC \\
     simp [])
 >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (METIS_TAC [L1_space_alt_integrable, prob_space_def])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘λx. (X x)³’] integrable_alt_def)
 >> fs [prob_space_def]
 >> STRIP_TAC
 >> POP_ORW
 >> CONJ_TAC
 >- (MP_TAC (Q.SPECL [‘measurable_space p’, ‘3’, ‘X’, ‘λx. (X x)³’] IN_BOREL_MEASURABLE_POW) \\
     fs [measure_space_def, p_space_def, events_def])
 >> ‘∀x. abs ((X x)³) = (abs (X x))³’ by rw [GSYM abs_3]
 >> rw [o_DEF]
 >> POP_ORW
 >> METIS_TAC [lt_imp_ne]
QED

Theorem REAL_SUM_IMAGE_COUNT_THREE[local] :
    ∀(f :num -> real). ∑ f (count 3) = f 0 + f 1 + f 2
Proof
  rw []
  >> ‘count 3 = {0;1;2}’ by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
  >> ‘{1:num} DELETE 0 = {1}’ by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
  >> ‘{2:num} DELETE 1 = {2}’ by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
  >> ‘{1:num; 2} DELETE 0 = {1;2}’ by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
  >> FULL_SIMP_TAC real_ss [FINITE_SING, FINITE_INSERT, REAL_SUM_IMAGE_THM,
                            REAL_SUM_IMAGE_SING, IN_INSERT, NOT_IN_EMPTY,
                            REAL_ADD_ASSOC]
QED

val clt_tactic1 =
    Know ‘∀n. s n ≠ NegInf ∧ s n ≠ PosInf’
    >- (simp [Abbr ‘s’] \\
        qx_gen_tac ‘n’ \\
        CONJ_TAC
        >- (Suff ‘0 ≤ sqrt (second_moments p X n)’
            >- (STRIP_TAC \\
                METIS_TAC [extreal_0_simps, lt_trans]) \\
            MATCH_MP_TAC sqrt_pos_le \\
            rw [second_moments_variance_def] \\
            irule EXTREAL_SUM_IMAGE_POS \\
            simp [variance_pos]) \\
        irule sqrt_infty \\
        CONJ_TAC
        >- (Suff ‘second_moments p X n < +∞’
            >- (METIS_TAC [lt_imp_ne]) \\
            irule finite_variance_imp_second_moments \\
            simp []) \\
        METIS_TAC [second_moments_pos])
    >> DISCH_TAC
    >> Know ‘∀n. 0 ≤ s n’
    >- (fs [variance_def, Abbr ‘s’] \\
        GEN_TAC \\
        MATCH_MP_TAC sqrt_pos_le \\
        rw [second_moments_def] \\
        Q.ABBREV_TAC ‘G = λi. central_moment p (X i) 2’ \\
        MATCH_MP_TAC (INST_TYPE [alpha |-> “:num”] EXTREAL_SUM_IMAGE_POS) \\
        simp[] \\
        rw[Abbr ‘G’, central_moment_def]\\
        ‘moment p (X x) 0 2 = second_moment p (X x) 0’ by EVAL_TAC \\
        simp[] \\
        MP_TAC (Q.SPECL [‘p’, ‘X (x:num)’, ‘0’]
                 second_moment_pos) \\
        simp[] \\
        DISCH_TAC)
    >> DISCH_TAC
    >> ‘∀n. 0 < s n’ by rw[lt_le];

(********************************* DELETE ******************************)

Theorem prob_space_distr_of :
  !p M X. prob_space p /\ measure_space M /\
          random_variable X p (measurable_space M) ==> prob_space (distr_of p M X)
Proof
  cheat
QED

Theorem converge_in_dist_third_alt' :
  !p X Y. prob_space p /\
          (!n. real_random_variable (X n) p) /\ real_random_variable Y p ==>
          ((X --> Y) (in_distribution p) <=>
           ∀f.
             f IN CnR 3 ⇒
             ((\n. expectation p (Normal o f o real o (X n))) -->
                                                              expectation p (Normal o f o real o Y)) sequentially)
Proof
  cheat
QED

(***********************************************************************)

Theorem real_random_variable_prod_measure_fst[local] :
    ∀p q X (N :num).
      prob_space p ∧
      prob_space (q :'a list m_space) ∧
      (∀i. i < N ⇒ real_random_variable (X i) p) ⇒
      (∀i. i < N ⇒ real_random_variable (X i ∘ FST) (p CROSS q))
Proof
  rpt STRIP_TAC
  >> Know ‘(p_space (p × q),events (p × q)) =
           (p_space p,events p) × (p_space q,events q)’
  >- (fs [p_space_def, events_def, prob_space_def] \\
      irule MEASURABLE_SPACE_PROD \\
      simp [])
  >> DISCH_TAC
  >> rw []
  >> fs [real_random_variable_def, random_variable_def]
  >> CONJ_TAC
  >- (MATCH_MP_TAC MEASURABLE_COMP \\
      qexists ‘(p_space p,events p)’ \\
      simp [] \\
      irule MEASURABLE_FST \\
      METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA])
  >> simp [IN_PSPACE_PROD_SIGMA]
QED

Theorem real_random_variable_prod_measure_snd[local] :
  ∀p q X (N :num).
    prob_space p ∧
    prob_space (q :'a list m_space) ∧
    (∀i. i < N ⇒ real_random_variable (X i) q) ⇒
    (∀i. i < N ⇒ real_random_variable (X i ∘ SND) (p CROSS q))
Proof
  rpt STRIP_TAC
  >> Know ‘(p_space (p × q),events (p × q)) =
           (p_space p,events p) × (p_space q,events q)’
  >- (fs [p_space_def, events_def, prob_space_def] \\
      irule MEASURABLE_SPACE_PROD \\
      simp [])
  >> DISCH_TAC
  >> rw []
  >> fs [real_random_variable_def, random_variable_def]
  >> CONJ_TAC
  >- (MATCH_MP_TAC MEASURABLE_COMP \\
      qexists ‘(p_space q,events q)’ \\
      simp [] \\
      irule MEASURABLE_SND \\
      METIS_TAC [p_space_def, events_def, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA])
  >> simp [IN_PSPACE_PROD_SIGMA]
QED

Theorem expectation_multidimentional_compose_fst[local] :
  ∀p q f.
    prob_space p ∧ prob_space (q :'a list m_space) ∧
    (∀x. x ∈ p_space p ⇒ f x ≠ +∞ ∧ f x ≠ −∞) ∧ integrable p f ⇒
    expectation p f = expectation (p × q) (f ∘ FST)
Proof
  rpt STRIP_TAC
  >> (MP_TAC o (Q.SPECL [‘p’, ‘q’, ‘f’]) o
             (INST_TYPE [beta |-> ``:('a list)``, alpha |-> “:'b”])) expectation_compose_fst
  >> METIS_TAC []
QED

Theorem expectation_multidimentional_compose_snd[local] :
  ∀p q f.
    prob_space p ∧ prob_space (q :'a list m_space) ∧
    (∀x. x ∈ p_space q ⇒ f x ≠ +∞ ∧ f x ≠ −∞) ∧ integrable q f ⇒
    expectation q f = expectation (p × q) (f ∘ SND)
Proof
  rpt STRIP_TAC
  >> (MP_TAC o (Q.SPECL [‘p’, ‘q’, ‘f’]) o
             (INST_TYPE [beta |-> ``:('a list)``, alpha |-> “:'b”])) expectation_compose_snd
  >> METIS_TAC []
QED

Theorem clt_expectation_not_infty_rv :
    ∀p X f. prob_space p ∧ random_variable X p Borel ∧ integrable p X ∧
            f ∈ CnR 3 ⇒
            expectation p (Normal ∘ f ∘ real ∘ X) ≠ +∞ ∧
            expectation p (Normal ∘ f ∘ real ∘ X) ≠ −∞
Proof
    NTAC 4 STRIP_TAC
 >> MATCH_MP_TAC expectation_finite
 >> simp []
 >> irule integrable_bounded_continuous_rv
 >> simp []
 >> MP_TAC (C3_subset_C_b)
 >> rw [SUBSET_DEF]
 >> fs [random_variable_def, p_space_def, events_def]
 >> METIS_TAC [in_borel_measurable_from_Borel, prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA]
QED

Theorem clt_partial_sum_lemma[local] :
  ∀p X Y Z f n.
    prob_space p ∧
    (∀i. i < n ⇒
         real_random_variable (X i) p ∧
         real_random_variable (Y i) p ∧
         integrable p (X i) ∧
         integrable p (Y i)) ∧
    Z = (λj x. ∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count j)) ⇒
    ∀j. j < n ⇒ real_random_variable (Z j) p ∧ integrable p (Z j)
Proof
    NTAC 7 STRIP_TAC
 >> fs [real_random_variable_def, random_variable_def, prob_space_def, p_space_def, events_def]
 >> POP_ORW
 >> Q.ABBREV_TAC ‘Z = (λj x. ∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count j))’
 >> fs []
 >> GEN_TAC >> STRIP_TAC >> STRONG_CONJ_TAC
 >- (CONJ_TAC
     >- (rw [Abbr ‘Z’] >> irule IN_MEASURABLE_BOREL_ADD' \\
         simp [MEASURE_SPACE_SIGMA_ALGEBRA] \\
         qexistsl [‘λx. ∑ (λi. Y i x) (count j)’, ‘λx. ∑ (λi. X i x) (count n DIFF count j)’] \\
         simp [MEASURE_SPACE_SIGMA_ALGEBRA] \\
         CONJ_TAC
         >- ((MP_TAC o (Q.SPECL [‘(measurable_space p)’ ,‘Y’, ‘λx. ∑ (λi. Y i x) (count j)’, ‘count j’]) o
                     (INST_TYPE [beta |-> “:num”])) IN_MEASURABLE_BOREL_SUM' \\
             simp [MEASURE_SPACE_SIGMA_ALGEBRA]) \\
         (MP_TAC o (Q.SPECL [‘(measurable_space p)’ ,‘X’,
                             ‘λx. ∑ (λi. X i x) (count n DIFF count j)’, ‘count n DIFF count j’]) o
                 (INST_TYPE [beta |-> “:num”])) IN_MEASURABLE_BOREL_SUM' \\
         simp [MEASURE_SPACE_SIGMA_ALGEBRA]) \\
     simp [Abbr ‘Z’] \\
     Know ‘∀x. x ∈ m_space p ⇒
               (∀i. i < j ⇒ Y i x ≠ −∞ ∧ Y i x ≠ +∞) ∧
               (∀i. i ∈ count n DIFF count j ⇒ X i x ≠ −∞ ∧ X i x ≠ +∞)’
     >- (GEN_TAC >> STRIP_TAC >> CONJ_TAC
         >- (GEN_TAC >> STRIP_TAC \\
             Q.PAT_X_ASSUM ‘ ∀i. i < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) \\
             gs [lt_trans]) \\
         GEN_TAC >> STRIP_TAC \\
         Q.PAT_X_ASSUM ‘ ∀i. i < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) \\
         gs [lt_trans]) >> STRIP_TAC \\
     Know ‘∀x. x ∈ m_space p ⇒
               ∑ (λi. Y i x) (count j) ≠ −∞ ∧ ∑ (λi. Y i x) (count j) ≠ +∞’
     >- (GEN_TAC >> STRIP_TAC >> CONJ_TAC
         >- (irule EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp []) \\
         irule EXTREAL_SUM_IMAGE_NOT_POSINF >> simp []) >> STRIP_TAC \\
     Know ‘∀x. x ∈ m_space p ⇒
               ∑ (λi. X i x) (count n DIFF count j) ≠ −∞ ∧ ∑ (λi. X i x) (count n DIFF count j) ≠ +∞’
     >- (GEN_TAC >> STRIP_TAC >> CONJ_TAC
         >- (irule EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp []) \\
         irule EXTREAL_SUM_IMAGE_NOT_POSINF >> simp []) >> STRIP_TAC \\
     METIS_TAC [add_not_infty])
 >> STRIP_TAC
 >> rw [integrable_alt_def]
 >> qmatch_abbrev_tac ‘integral p (abs o A) ≠ PosInf’
 >> Know ‘integrable p (λx. ∑ (λi. Y i x) (count j))’
 >- (irule integrable_sum' >> rw [count_def]) >> DISCH_TAC
 >> Know ‘integrable p (λx. ∑ (λi. X i x) (count n DIFF count j))’
 >- (irule integrable_sum' >> rw [count_def]) >> DISCH_TAC
 >> Know ‘integrable p (abs o A)’
 >- (irule integrable_abs \\
     simp [Abbr ‘A’] \\
     (MP_TAC o (Q.SPECL [‘p’, ‘λx. ∑ (λi. Y i x) (count j)’, ‘λx. ∑ (λi. X i x) (count n DIFF count j)’]) o
             (INST_TYPE [beta |-> “:num”])) integrable_add' \\
     simp [MEASURE_SPACE_SIGMA_ALGEBRA]) >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘abs o A’] integrable_normal_integral)
 >> rw [] >> METIS_TAC [extreal_not_infty]
QED

(* eq 15 *)
Theorem clt_Lindeberg_replacement_trick_bounded[local] :
    ∀p X Y f s Z n.
      prob_space p ∧ f ∈ CnR 3 ∧
      (∀i. i < n ⇒ real_random_variable (X i) p ∧
                   real_random_variable (Y i) p ∧
                   integrable p (X i) ∧
                   integrable p (Y i)) ∧
      0 < s n ∧ s n ≠ +∞ ∧ s n ≠ −∞ ∧
      (∀j x. j < n ⇒
             Z j x = ∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count1 j)) ⇒
      expectation p (Normal ∘ f ∘ real ∘ (λx. ∑ (λi. X i x) (count n) / s n)) −
                  expectation p (Normal ∘ f ∘ real ∘ (λx. ∑ (λi. Y i x) (count n) / s n)) =
      ∑ (λj. expectation p (Normal ∘ f ∘ real ∘ (λx. (X j x + Z j x) / s n)) −
                         expectation p (Normal ∘ f ∘ real ∘ (λx. (Y j x + Z j x) / s n))) (count n)
Proof
    rpt STRIP_TAC
 >> Know ‘integrable p (λx. ∑ (λi. Y i x) (count n))’
 >- (irule integrable_sum' >> fs [prob_space_def])
 >> DISCH_TAC
 >> Know ‘integrable p (λx. ∑ (λi. Y i x) (count n) / s n)’
 >- (‘∃c. s n = Normal c’ by METIS_TAC [extreal_cases] \\
     fs [] \\
     Q.ABBREV_TAC ‘h = λx. ∑ (λi. Y i x) (count n)’ \\
     fs [] >> irule integrable_cdiv >> METIS_TAC [REAL_LT_LE, prob_space_def])
 >> Know ‘real_random_variable (λx. ∑ (λi. Y i x) (count n)) p’
 >- (irule real_random_variable_sum >> fs [])
 >> DISCH_TAC
 >> Know ‘real_random_variable (λx. ∑ (λi. Y i x) (count n) / s n) p’
 >- (‘∃c. s n = Normal c’ by METIS_TAC [extreal_cases] \\
     fs [] \\
     Q.ABBREV_TAC ‘h = λx. ∑ (λi. Y i x) (count n)’ \\
     fs [] >> irule real_random_variable_cdiv >> METIS_TAC [REAL_LT_LE])
 >> DISCH_TAC
 >> Know ‘integrable p
          (Normal ∘ f ∘ real ∘ (λx. ∑ (λi. Y i x) (count n) / s n))’
 >- (Q.ABBREV_TAC ‘h = λx. ∑ (λi. Y i x) (count n) / s n’ \\
     irule integrable_bounded_continuous \\
     MP_TAC (C3_subset_C_b) >> rw [SUBSET_DEF])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘S_X = (λx. ∑ (λi. X i x) (count n) / s n)’
 >> Q.ABBREV_TAC ‘S_Y = (λx. ∑ (λi. Y i x) (count n) / s n)’
 >> Q.ABBREV_TAC ‘f_X = Normal ∘ f ∘ real ∘ S_X’
 >> Q.ABBREV_TAC ‘f_Y = Normal ∘ f ∘ real ∘ S_Y’
 >> Q.ABBREV_TAC ‘G = (λj x. ∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count j))’
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘Y’, ‘G’, ‘f’, ‘n’] clt_partial_sum_lemma)
 >> rw []
 >> Know ‘∀j. j < n ⇒ real_random_variable (λx. G j x / s n) p ∧
                      integrable p (λx. G j x / s n)’
 >- (GEN_TAC >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘ ∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) \\
     gs [] >> ‘∃c. s n = Normal c’ by METIS_TAC [extreal_cases] \\
     fs [] >> CONJ_TAC
     >- (irule real_random_variable_cdiv >> METIS_TAC [REAL_LT_LE]) \\
     irule integrable_cdiv >> METIS_TAC [prob_space_def, REAL_LT_LE])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘g = λj. Normal ∘ f ∘ real ∘ (λx. G j x / s n)’
 >> ‘f_X = g 0’ by rw [Abbr ‘f_X’, Abbr ‘g’, Abbr ‘S_X’, Abbr ‘G’]
 >> ‘f_Y = g n’ by simp [Abbr ‘f_Y’, Abbr ‘g’, Abbr ‘S_Y’, Abbr ‘G’]
 >> gs []
 >> MP_TAC (Q.SPECL [‘λj. expectation p (g j)’, ‘n’] SUM_SUB_GEN_WEAKEN)
 >> Know ‘∀j. j ≤ n ⇒ (λj. expectation p (g j)) j ≠ +∞ ∧ (λj. expectation p (g j)) j ≠ −∞’
 >- (GEN_TAC >> STRIP_TAC \\
     Cases_on ‘j = n’
     >- (BETA_TAC >> gs [Abbr ‘g’] \\
         irule expectation_finite \\
         METIS_TAC [Abbr ‘G’, Abbr ‘S_Y’, Abbr ‘f_Y’]) \\
     ‘j < n’ by gs [GSYM LT_LE] \\
     Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                        real_random_variable (λx. G j x / s n) p ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) \\
     gs [] \\
     (MP_TAC o (Q.SPECL [‘p’, ‘λx. G (j :num) x / s (n :num)’, ‘f’]) o
             (INST_TYPE [beta |-> “:num”])) clt_expectation_not_infty \\
      gs []) >> Rewr >> BETA_TAC
 >> DISCH_THEN (fs o wrap o SYM)
 >> irule EXTREAL_SUM_IMAGE_EQ'
 >> simp []
 >> Q.X_GEN_TAC ‘j’ >> rw []
 >> Q.PAT_X_ASSUM ‘∀j x. j < n ⇒ _’ K_TAC
 >> Q.ABBREV_TAC ‘Z = (λx'. ∑ (λi. Y i x') (count j) + ∑ (λi. X i x') (count n DIFF count1 j))’
 >> fs [Abbr ‘g’]
 >> Know ‘expectation p (Normal ∘ f ∘ real ∘ (λx. G j x / s n)) =
          expectation p (Normal ∘ f ∘ real ∘ (λx'. (X j x' + Z x') / s n))’
 >- (NTAC 2 (Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ K_TAC) \\
     Q.PAT_X_ASSUM ‘ Normal ∘ f ∘ real ∘ S_X = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘ Normal ∘ f ∘ real ∘ S_Y = _’ K_TAC \\
     irule expectation_cong >> simp [] \\
     Know ‘∀x. x ∈ p_space p ⇒ G j x = (X j x + Z x)’
     >- (simp [Abbr ‘G’, Abbr ‘Z’] \\
         Know ‘∀x. x IN p_space p ⇒ X j x ≠ PosInf ∧ X j x ≠ NegInf’
         >- (Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
              (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs [real_random_variable_def]) \\
         DISCH_TAC \\
         Know ‘∀x. x IN p_space p ⇒ ∑ (λi. Y i x) (count j) ≠ PosInf ∧ ∑ (λi. Y i x) (count j) ≠ NegInf’
         >- (GEN_TAC >> STRIP_TAC >> CONJ_TAC
             >- (irule EXTREAL_SUM_IMAGE_NOT_POSINF >> simp [] \\
                 Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
                 ‘i < j’ by METIS_TAC [LESS_TRANS] \\
                 Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
                  (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
             irule EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp [] \\
             Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
             ‘i < j’ by METIS_TAC [LESS_TRANS] \\
             Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
              (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
         DISCH_TAC \\
         Know ‘∀x. x IN p_space p ⇒ ∑ (λi. X i x) (count n DIFF count j) ≠ PosInf ∧
                                    ∑ (λi. X i x) (count n DIFF count j) ≠ NegInf’
         >- (GEN_TAC >> STRIP_TAC >> CONJ_TAC
             >- (irule EXTREAL_SUM_IMAGE_NOT_POSINF >> simp [] \\
                 Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
                 Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
                  (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
             irule EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp [] \\
             Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
             Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
              (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
         DISCH_TAC \\
         Know ‘∀x. x IN p_space p ⇒ ∑ (λi. X i x) (count n DIFF count1 j) ≠ PosInf ∧
                                    ∑ (λi. X i x) (count n DIFF count1 j) ≠ NegInf’
         >- (GEN_TAC >> STRIP_TAC >> CONJ_TAC
             >- (irule EXTREAL_SUM_IMAGE_NOT_POSINF >> simp [] \\
                 Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
                 Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
                  (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
             irule EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp [] \\
             Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
             Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
              (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
         DISCH_TAC \\
         ‘∀x. x ∈ p_space p ⇒
              X j x + (∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count1 j)) =
              X j x + ∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count1 j)’
           by  METIS_TAC [add_assoc] \\
         POP_ASSUM (fs o wrap) \\
         ‘∀x. x ∈ p_space p ⇒ X j x + ∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count1 j) =
                              ∑ (λi. Y i x) (count j) + X j x + ∑ (λi. X i x) (count n DIFF count1 j)’
           by METIS_TAC [add_comm] \\
         POP_ASSUM (fs o wrap) \\
         ‘∀x. x ∈ p_space p ⇒ ∑ (λi. Y i x) (count j) + X j x + ∑ (λi. X i x) (count n DIFF count1 j) =
                              ∑ (λi. Y i x) (count j) + (X j x + ∑ (λi. X i x) (count n DIFF count1 j))’
           by METIS_TAC [GSYM add_assoc] \\
         POP_ASSUM (fs o wrap) \\
         Know ‘∀x. x ∈ p_space p ⇒ ∑ (λi. X i x) (count n DIFF count j) =
                                    (X j x + ∑ (λi. X i x) (count n DIFF count1 j))’
         >- (GEN_TAC >> STRIP_TAC \\
             Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒
                                ∑ (λi. X i x) (count n DIFF count1 j) ≠ +∞ ∧ _’
              (STRIP_ASSUME_TAC o Q.SPEC ‘x’) >> gs [] \\
             ‘X j x = ∑ (λi. X i x) {j}’ by rw [EXTREAL_SUM_IMAGE_SING] \\
             POP_ORW \\
             ‘count n DIFF count j = {j} UNION (count n DIFF count1 j)’ by rw [Once EXTENSION] \\
             POP_ORW \\
             irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
             Know ‘∀x'. x' ∈ {j} ∪ (count n DIFF count1 j) ⇒ (λi. X i x) x' ≠ +∞’
             >- (‘count n DIFF count j = {j} UNION (count n DIFF count1 j)’ by rw [Once EXTENSION] \\
                 GEN_TAC >> STRIP_TAC \\
                 BETA_TAC >> fs [] \\
                 Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
                  (STRIP_ASSUME_TAC o Q.SPEC ‘x'’) >> gs [real_random_variable_def]) \\
             DISCH_TAC >> fs [] >> DISJ2_TAC >> METIS_TAC []) \\
         DISCH_TAC \\
         POP_ASSUM (fs o wrap)) \\
     DISCH_THEN (fs o wrap))
 >> DISCH_THEN (fs o wrap)
 >> Know ‘expectation p (Normal ∘ f ∘ real ∘ (λx. G (j + 1) x / s n)) =
          expectation p (Normal ∘ f ∘ real ∘ (λx'. (Y j x' + Z x') / s n))’
 >- (NTAC 2 (Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ K_TAC) \\
     Q.PAT_X_ASSUM ‘ Normal ∘ f ∘ real ∘ S_X = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘ Normal ∘ f ∘ real ∘ S_Y = _’ K_TAC \\
     irule expectation_cong >> simp [] \\
     Know ‘∀x. x ∈ p_space p ⇒ G (j + 1) x = Y j x + Z x’
     >- (simp [Abbr ‘G’, Abbr ‘Z’] \\
         Know ‘∀x. x IN p_space p ⇒ Y j x ≠ PosInf ∧ Y j x ≠ NegInf’
         >- (Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
              (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs [real_random_variable_def]) \\
         DISCH_TAC \\
         Know ‘∀x. x IN p_space p ⇒ ∑ (λi. Y i x) (count j) ≠ PosInf ∧ ∑ (λi. Y i x) (count j) ≠ NegInf’
          >- (GEN_TAC >> STRIP_TAC >> CONJ_TAC
              >- (irule EXTREAL_SUM_IMAGE_NOT_POSINF >> simp [] \\
                  Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
                  ‘i < j’ by METIS_TAC [LESS_TRANS] \\
                  Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
                   (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
              irule EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp [] \\
              Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
              ‘i < j’ by METIS_TAC [LESS_TRANS] \\
              Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
               (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
         DISCH_TAC \\
         Know ‘∀x. x IN p_space p ⇒ ∑ (λi. Y i x) (count (j + 1)) ≠ PosInf ∧ ∑ (λi. Y i x) (count (j + 1)) ≠ NegInf’
         >- (GEN_TAC >> STRIP_TAC \\
             ‘count (j + 1) = count j ∪ {j}’ by rw [Once EXTENSION] \\
             POP_ORW \\
             Know ‘∑ (λi. Y i x) (count j ∪ {j}) = ∑ (λi. Y i x) (count j) + ∑ (λi. Y i x) {j}’
             >- (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
                 simp [] >> DISJ2_TAC >> rw []
                 >- (Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
                      (STRIP_ASSUME_TAC o Q.SPEC ‘x'’) \\
                     ‘x' < n’ by METIS_TAC [LESS_TRANS] \\
                     gs [real_random_variable_def]) \\
                 Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒ Y j x ≠ +∞ ∧ Y j x ≠ −∞’
                  (STRIP_ASSUME_TAC o Q.SPEC ‘x’) >> fs []) \\
             Rewr \\
             NTAC 2 (Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’)) \\
             gs [add_not_infty]) \\
         DISCH_TAC \\
         Know ‘∀x. x ∈ p_space p ⇒
                   ∑ (λi. X i x) (count n DIFF count1 j) ≠ +∞ ∧
                   ∑ (λi. X i x) (count n DIFF count1 j) ≠ −∞’
         >- (GEN_TAC >> STRIP_TAC >> CONJ_TAC
             >- (irule EXTREAL_SUM_IMAGE_NOT_POSINF >> simp [] \\
                 Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
                 Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
                  (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
             irule EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp [] \\
             Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
             Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
              (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [real_random_variable_def]) \\
          DISCH_TAC \\
         ‘∀x. x ∈ p_space p ⇒
              Y j x + (∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count1 j)) =
              Y j x + ∑ (λi. Y i x) (count j) + ∑ (λi. X i x) (count n DIFF count1 j)’
           by  METIS_TAC [add_assoc] \\
         POP_ASSUM (fs o wrap) \\
         Know ‘∀x. x ∈ p_space p ⇒ ∑ (λi. Y i x) (count (j + 1)) = Y j x + ∑ (λi. Y i x) (count j)’
         >- (GEN_TAC >> STRIP_TAC \\
             Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒
                                ∑ (λi. Y i x) (count (j + 1)) ≠ +∞ ∧ _’
              (STRIP_ASSUME_TAC o Q.SPEC ‘x’) >> gs [] \\
             ‘Y j x = ∑ (λi. Y i x) {j}’ by rw [EXTREAL_SUM_IMAGE_SING] \\
             POP_ORW \\
             ‘count (j + 1) = {j} UNION (count j)’ by rw [Once EXTENSION] \\
             POP_ORW \\
             irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
             simp [] >> DISJ2_TAC >> rw []
             >- (Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒ Y j x ≠ +∞ ∧ Y j x ≠ −∞’
                  (STRIP_ASSUME_TAC o Q.SPEC ‘x’) >> gs []) \\
             Q.PAT_X_ASSUM ‘∀i. i < n ⇒ real_random_variable (X i) p ∧ _’
              (STRIP_ASSUME_TAC o Q.SPEC ‘x'’) \\
             ‘x' < n’ by METIS_TAC [LESS_TRANS] \\
             gs [real_random_variable_def]) \\
            DISCH_THEN (fs o wrap) \\
         ‘count (j + 1) = count1 j’ by rw [Once EXTENSION] \\
         POP_ORW >> gs []) \\
     DISCH_THEN (fs o wrap))
 >> DISCH_THEN (fs o wrap)
QED

(*
(* eq 16 *)
Theorem TAYLOR_EXPECTATION_THIRD_ORDER_BOUND[local] :
    ∀p X Z f.
      prob_space p ∧
      real_random_variable X p ∧
      real_random_variable Z p ∧
      expectation p (λx. (abs (X x))³) < +∞ ∧
      indep_vars p X Z Borel Borel ∧
      f IN CnR 3 ⇒
      (∃M t. abs (Normal (diff 3 f t)) ≤ M ⇒
           abs (
             expectation p (Normal o f o real o (λx. X x + Z x)) -
             expectation p (Normal o f o real o Z) -
             expectation p (Normal o (diff 1 f) o real o Z) * expectation p X -
             1 / 2 *
             expectation p (Normal o (diff 2 f) o real o Z) *
             expectation p ((λx. (X x) pow 2))) ≤
           M / 6 * expectation p ((λx. abs (X x) pow 3)))
Proof
  RW_TAC std_ss []
  >> MP_TAC (Q.SPECL [‘p’, ‘3’, ‘X’, ‘f’] TAYLOR_REMAINDER_EXPECTATION_REAL_RV)
  >> ‘integrable p X ∧ integrable p (λx. (X x)³)’ by METIS_TAC [clt_integrable_lemma]
  >> simp []
  >> DISCH_THEN (Q.X_CHOOSE_THEN ‘M’
                  (Q.X_CHOOSE_THEN ‘t’ ASSUME_TAC))
  >> qexistsl [‘M’, ‘t’]
  >> STRIP_TAC
  >> fs []
  >> Know ‘∀x. x IN p_space p ⇒ f (real (X x + Z x)) = f (real (Z x)) + diff 1 f (real (Z x)) * real (X x) +
                                                       (1 / 2) * diff 2 f (real (Z x)) * (real (X x)) pow 2 +
                                                       diff 3 f t / 6 * real (X x) pow 3’
  >- (rw [] \\
      fs [real_random_variable_def] \\
      rpt (Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’)) >> gs [] \\
      ‘∃a. X x = Normal a’ by METIS_TAC [extreal_cases] \\
      ‘∃b. Z x = Normal b’ by METIS_TAC [extreal_cases] >> gs [extreal_add_def, real_normal] \\
      MP_TAC (Q.SPECL [‘f’, ‘(min b (b + a))’, ‘(max b (b + a))’, ‘3’] TAYLOR_THEOREM) \\
             simp []





      Cases_on ‘X x < 0’
      >- (fs [real_random_variable_def] \\
          rpt (Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’)) >> gs [] \\
          ‘∃a. X x = Normal a’ by METIS_TAC [extreal_cases] \\
          ‘∃b. Z x = Normal b’ by METIS_TAC [extreal_cases] >> gs [extreal_add_def, real_normal] \\
          MP_TAC (Q.SPECL [‘f’, ‘a + b’, ‘b’, ‘3’] TAYLOR_THEOREM) \\
          impl_tac
          >- (simp [] >> CONJ_TAC
              >- (MP_TAC (Q.SPECL [‘a’, ‘0’, ‘b’] (GSYM REAL_LT_RADD)) \\
                  ‘0 + b = b’ by gs [REAL_ADD_LID] \\
                  METIS_TAC []) \\
              fs [CnR_def] >> rpt GEN_TAC \\
              STRIP_TAC \\
              Q.PAT_X_ASSUM ‘∀x. higher_differentiable 3 f x’ (STRIP_ASSUME_TAC o Q.SPEC ‘t'’) \\
              ‘SUC m ≤ 3’ by METIS_TAC [LESS_EQ] \\
              METIS_TAC [higher_differentiable_mono]) \\
          STRIP_TAC \\
          Know ‘b - (a + b) = -a’
          >- (‘a + b = b + a’ by rw [REAL_ADD_COMM] >> POP_ORW \\
              rw [REAL_ADD_SUB2]) >> DISCH_TAC \\
          fs [] \\
          Q.ABBREV_TAC ‘g = λm. (&FACT m)⁻¹ * -a pow m * diff m f (a + b)’ \\
          (MP_TAC o (Q.SPECL [‘3’, ‘g’]) o
                  (INST_TYPE [alpha |-> “:num”])) REAL_SUM_IMAGE_EQ_sum \\
          DISCH_TAC \\
          Q.PAT_X_ASSUM ‘f b = _’ (MP_TAC) \\
          POP_ORW \\
          rw [REAL_SUM_IMAGE_COUNT_THREE, Abbr ‘g’] \\
          ‘(&FACT 0) = (1 :real)’ by EVAL_TAC >> ‘(&FACT 0)⁻¹ = 1’ by gs [REAL_INV1] \\
          ‘(&FACT 1) = (1 :real)’ by EVAL_TAC >> ‘(&FACT 1)⁻¹ = 1’ by fs [REAL_INV1] \\
          ‘(&FACT 2) = (2 :real)’ by EVAL_TAC >> ‘(&FACT 2)⁻¹ = 1 / 2’ by cheat \\
          ‘(&FACT 3) = (6: real)’ by EVAL_TAC >> ‘(&FACT 3)⁻¹ = 1 / 6’ by cheat \\ (* METIS_TAC [REAL_INV_1OVER]*)
          fs [] \\
          NTAC 8 (POP_ASSUM K_TAC) \\
          cheat) \\
      cheat) \\
  cheat
QED
*)

Theorem taylor_diff_expectation_bound:
    ∀p X Y Z f M n.
      prob_space p ∧
      (∀(j :num). j < n ⇒
                  real_random_variable (X j) p ∧
                  real_random_variable (Y j) p ∧
                  real_random_variable (Z j) p ∧
                  integrable p (λx. (abs (X j x))³) ∧
                  integrable p (λx. (abs (Y j x))³) ∧
                  indep_vars p (X j) (Z j) Borel Borel ∧
                  indep_vars p (Y j) (Z j) Borel Borel) ∧
      f ∈ CnR 3 ∧
      (∀t. abs (Normal (diff 3 f t)) ≤ M)  ⇒
      ∀(j :num). j < n ⇒
          abs (expectation p (Normal ∘ f ∘ real ∘ (λx. X j x + Z j x)) -
               expectation p (Normal ∘ f ∘ real ∘ (λx. Y j x + Z j x))) ≤
          M / 6 * (expectation p (λx. abs (X j x)³) + expectation p (λx. abs (Y j x)³))
Proof
  cheat
QED

Theorem IN_MEASURABLE_BOREL_CDIV :
    ∀a f g z.
      sigma_algebra a ∧ f ∈ Borel_measurable a ∧ z ≠ 0 ∧
      (∀x. x ∈ space a ⇒ g x = f x / Normal z) ⇒
      g ∈ Borel_measurable a
Proof
  cheat
QED

Theorem pow_abs :
    ∀c n. abs (c pow n) = (abs c) pow n
Proof
    rpt STRIP_TAC
 >> Cases_on ‘c = PosInf’
 >- (gs [] \\
     Cases_on ‘n = 0’
     >- (gs [abs_refl, extreal_1_simps]) \\
     gs [extreal_pow_def, extreal_abs_def])
 >> Cases_on ‘c = NegInf’
 >- (gs [] \\
     Cases_on ‘n = 0’
     >- (gs [abs_refl, extreal_1_simps]) \\
     Cases_on ‘EVEN n’
     >- (gs [extreal_pow_def, extreal_abs_def]) \\
     gs [extreal_pow_def, extreal_abs_def])
 >> ‘∃r. c = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘Normal r pow n = Normal (r pow n)’ by rw [extreal_pow_def] >> POP_ORW
 >> ‘abs (Normal (r pow n)) = Normal (abs (r pow n))’ by rw [extreal_abs_def] >> POP_ORW
 >> ‘abs (Normal r) = Normal (abs r)’ by rw [extreal_abs_def] >> POP_ORW
 >> ‘Normal (abs r) pow n = Normal ((abs r) pow n)’ by rw [extreal_pow_def]
 >> METIS_TAC [extreal_11, POW_ABS]
QED

val taylor_tactic1 =
    ‘Normal r ≠ 0’ by METIS_TAC [GSYM extreal_lt_eq, lt_le, normal_0] \\
    Q.PAT_X_ASSUM ‘(Normal r)³ = Normal r³’ (rw o wrap o SYM) \\
    ‘abs (Normal r) = Normal r’ by METIS_TAC [GSYM abs_refl, GSYM extreal_lt_eq, normal_0, lt_imp_le] \\
    ‘0 < Normal r’ by METIS_TAC [GSYM extreal_lt_eq, normal_0] \\
    ‘abs (Normal c)³ = (abs (Normal c))³’ by rw [pow_abs] \\
    ‘abs (Normal r)³ = (abs (Normal r))³’ by rw [pow_abs] \\
    ‘abs (Normal r)³ = (Normal r)³’ by METIS_TAC [pow_eq] \\
    ‘0 < Normal r’ by METIS_TAC [GSYM extreal_lt_eq, normal_0] \\
    ‘(Normal c / Normal r)³ = (Normal c)³ / (Normal r)³’ by METIS_TAC [pow_div] \\
    POP_ORW \\
    ‘(Normal r)³ ≠ 0’ by METIS_TAC [pow_pos_lt, GSYM extreal_lt_eq, normal_0, lt_le] \\
    METIS_TAC [abs_div, extreal_pow_def,extreal_not_infty];

val taylor_tactic2 =
    ‘Normal r ≠ 0’ by METIS_TAC [GSYM extreal_lt_eq, lt_le, normal_0] \\
    ‘abs (Normal c / Normal r) = abs (Normal c) / abs (Normal r)’ by METIS_TAC [abs_div, extreal_not_infty] \\
    POP_ORW \\
    ‘abs (Normal r) = Normal r’ by METIS_TAC [GSYM abs_refl, GSYM extreal_lt_eq, normal_0, lt_imp_le] \\
    POP_ORW \\
    ‘0 < Normal r’ by METIS_TAC [GSYM extreal_lt_eq, normal_0] \\
    METIS_TAC [extreal_abs_def, pow_div,  extreal_not_infty];

Theorem integrable_abs_third[local] :
    ∀p X. prob_space p ∧
          real_random_variable X p ∧
          integrable p (λx. (abs (X x))³) ⇒ integrable p (λx. abs (X x)³)
Proof
    rpt STRIP_TAC
 >> Suff ‘∀x. x IN p_space p ⇒ (abs (X x))³ = abs (X x)³’
 >- (STRIP_TAC \\
     irule integrable_eq \\
     fs [prob_space_def, p_space_def] \\
     qexists ‘λx. (abs (X x))³’ \\
     METIS_TAC [])
 >> fs [real_random_variable_def]
 >> rw []
 >> Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’)
 >> ‘∃r. X x = Normal r’ by METIS_TAC [extreal_cases]
 >> gs []
 >> METIS_TAC [GSYM pow_abs]
QED

Theorem sum_eq_zero[local] :
    ∀a b. a ≠ NegInf ∧ a ≠ PosInf ∧
          b ≠ NegInf ∧ b ≠ PosInf ∧
          0 ≤ a ∧ 0 ≤ b ∧ a + b = 0 ⇒ a = 0 ∧ b = 0
Proof
    rpt STRIP_TAC
 >- (CCONTR_TAC
     >- (‘0 < a’ by METIS_TAC [lt_le] \\
         ‘0 < a + b’ by METIS_TAC [lte_add] \\
         ‘0 ≠ a + b’ by METIS_TAC [lt_imp_ne] >> fs []))
 >> CCONTR_TAC
 >- (‘0 < b’ by METIS_TAC [lt_le] \\
     ‘0 < a + b’ by METIS_TAC [let_add] \\
     ‘0 ≠ a + b’ by METIS_TAC [lt_imp_ne] >> fs [])
QED

Theorem expectation_abs_zero[local] :
  ∀p X.
    prob_space p ∧ real_random_variable X p ∧
    expectation p (abs ∘ X) = 0 ⇒
    ∀x. x ∈ p_space p ⇒ X x = 0
Proof
    cheat
QED

Theorem real_random_variable_pow_three[local] :
    ∀p X. prob_space p ∧ real_random_variable X p ⇒
          real_random_variable (λx. (X x)³) p
Proof
  rpt STRIP_TAC
  >> fs [real_random_variable_def, random_variable_def, p_space_def, events_def]
  >> CONJ_TAC
  >- (irule IN_BOREL_MEASURABLE_POW \\
      fs [prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA] \\
      qexistsl [‘X’, ‘3’] \\
      simp [])
  >> GEN_TAC >> STRIP_TAC
  >> Q.PAT_X_ASSUM ‘∀x. _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’)
  >> ‘∃r. X x = Normal r’ by METIS_TAC [extreal_cases] >> gs []
  >> METIS_TAC [pow_not_infty, extreal_not_infty]
QED

Theorem expectation_zero_from_cube_zero[local] :
  ∀p X. prob_space p ∧ real_random_variable X p ∧
        expectation p (λx. abs (X x)³) = 0 ⇒
        ∀x. x ∈ p_space p ⇒ X x = 0
Proof
  rw [real_random_variable_def]
  >> ‘∀x. 0 ≤ abs (X x)³’ by METIS_TAC [abs_pos]
  >> MP_TAC (Q.SPECL [‘p’, ‘λx. (X x)³’] expectation_abs_zero)
  >> simp []
  >> ‘real_random_variable (λx. (X x)³) p’ by METIS_TAC [real_random_variable_pow_three, real_random_variable_def]
  >> STRIP_TAC
  >> gs [o_DEF]
  >> POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) >> gs []
  >> METIS_TAC [pow_zero_imp]
QED

val taylor_tactic3 =
    Know ‘expectation p (λx. abs (X j x)³) ≠ −∞ ∧
          expectation p (λx. abs (X j x)³) ≠ +∞’
    >- (MP_TAC (Q.SPECL [‘p’, ‘λx. abs (X (j :num) x)³’] expectation_finite) \\
        simp [] \\
        Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                           real_random_variable (X j) p ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs []) \\
    DISCH_TAC \\
    Know ‘expectation p (λx. abs (Y j x)³) ≠ −∞ ∧
          expectation p (λx. abs (Y j x)³) ≠ +∞’
     >- (MP_TAC (Q.SPECL [‘p’, ‘λx. abs (Y (j :num) x)³’] expectation_finite) \\
         simp [] \\
         Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                            real_random_variable (X j) p ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs [] \\
         METIS_TAC []);

Theorem taylor_diff_expectation_bound_scaled :
    ∀p X Y Z f M s n.
      prob_space p ∧
      (∀(j :num). j < n ⇒
                  real_random_variable (X j) p ∧
                  real_random_variable (Y j) p ∧
                  real_random_variable (Z j) p ∧
                  integrable p (λx. (abs (X j x))³) ∧
                  integrable p (λx. (abs (Y j x))³) ∧
                  indep_vars p (X j) (Z j) Borel Borel ∧
                  indep_vars p (Y j) (Z j) Borel Borel) ∧
      f ∈ CnR 3 ∧
      0 < s n ∧ s n ≠ +∞ ∧ s n ≠ −∞ ∧
      (∀t. abs (Normal (diff 3 f t)) ≤ M) ⇒
      ∀j. j < n ⇒
          abs (expectation p (Normal ∘ f ∘ real ∘ (λx. (X j x + Z j x) / s n)) -
               expectation p (Normal ∘ f ∘ real ∘ (λx. (Y j x + Z j x) / s n)))
          ≤ M / (6 * (s n pow 3)) *
            (expectation p (λx. abs (X j x)³) + expectation p (λx. abs (Y j x)³))
Proof
    rpt STRIP_TAC
 >> ‘∃r. s n = Normal r’ by METIS_TAC [extreal_cases] >> gs []
 >> ‘r ≠ 0’ by METIS_TAC [REAL_LT_LE]
 >> ‘integrable p (λx. abs (X j x)³)’ by METIS_TAC [integrable_abs_third]
 >> ‘integrable p (λx. abs (Y j x)³)’ by METIS_TAC [integrable_abs_third]
 >> Cases_on ‘M = PosInf’
 >- (gs [] \\
     Know ‘+∞ / (6 * (Normal r)³) = PosInf’
     >- (‘(Normal r)³ = Normal r³’ by rw [extreal_pow_def] >> POP_ORW \\
         ‘6 = Normal 6’ by EVAL_TAC >> POP_ORW \\
         ‘Normal 6 * Normal r³ = Normal (6 * r³)’ by rw [extreal_mul_def] >> POP_ORW \\
         irule (cj 1 infty_div) \\
         ‘0 < r³’ by METIS_TAC [REAL_POW_LT] \\
         ‘0 < 6:real’ by simp [] \\
         METIS_TAC [REAL_LT_MUL, REAL_0]) >> Rewr \\
     Know ‘0 ≤ expectation p (λx. abs (X j x)³)’
     >- (irule expectation_pos >> METIS_TAC [abs_pos]) >> DISCH_TAC \\
     Know ‘0 ≤ expectation p (λx. abs (Y j x)³)’
     >- (irule expectation_pos >> METIS_TAC [abs_pos]) >> DISCH_TAC \\
     ‘0 ≤ expectation p (λx. abs (X j x)³) + expectation p (λx. abs (Y j x)³)’ by METIS_TAC [le_add] \\
     Cases_on ‘expectation p (λx. abs (X j x)³) + expectation p (λx. abs (Y j x)³) = 0’
     >- (gs [] \\
         Know ‘expectation p (λx. abs (X j x)³) = 0 ∧ expectation p (λx. abs (Y j x)³) = 0’
         >- (irule sum_eq_zero >> simp [] \\
             taylor_tactic3 >> METIS_TAC []) \\
         STRIP_TAC \\
         ‘∀x. x ∈ p_space p ⇒ X j x = 0’ by METIS_TAC [expectation_zero_from_cube_zero] \\
         ‘∀x. x ∈ p_space p ⇒ Y j x = 0’ by METIS_TAC [expectation_zero_from_cube_zero] \\
         ‘∀x. x ∈ p_space p ⇒ X j x + Z j x = Y j x + Z j x’ by METIS_TAC [] \\
         Know ‘expectation p (Normal ∘ f ∘ real ∘ (λx. (X j x + Z j x) / Normal r)) =
               expectation p (Normal ∘ f ∘ real ∘ (λx. (Y j x + Z j x) / Normal r))’
         >- (irule expectation_cong >> simp []) >> Rewr \\
         irule sub_refl \\
         Q.ABBREV_TAC ‘h = Normal ∘ f ∘ real ∘ (λx. (Y j x + Z j x) / Normal r)’ \\
         MP_TAC (Q.SPECL [‘p’, ‘h’] expectation_finite) \\
         Know ‘integrable p h’
         >- (rw [Abbr ‘h’] \\
             irule integrable_bounded_continuous \\
             Know ‘f IN C_b’
             >- (MP_TAC (C3_subset_C_b) \\
                 fs [SUBSET_DEF]) >> gs [] \\
             STRIP_TAC \\
             MP_TAC (Q.SPECL [‘p’, ‘λx. (Y (j :num) x + Z j x)’, ‘r’] real_random_variable_cdiv) \\
             simp [] \\
             Suff ‘real_random_variable (λx. Y j x + Z j x) p’ >- (rw []) \\
             irule real_random_variable_add >> METIS_TAC []) >> simp []) \\
     Know ‘expectation p (λx. abs (X j x)³) + expectation p (λx. abs (Y j x)³) ≠ PosInf ∧
           expectation p (λx. abs (X j x)³) + expectation p (λx. abs (Y j x)³) ≠ NegInf’
     >- (taylor_tactic3 >> METIS_TAC [add_not_infty]) >> DISCH_TAC \\
     ‘∃a. expectation p (λx. abs (X j x)³) + expectation p (λx. abs (Y j x)³) = Normal a’
       by METIS_TAC [extreal_cases] >> gs [] \\
     ‘0 < a’ by METIS_TAC [REAL_LT_LE] >> gs [extreal_mul_def])
 >> Q.ABBREV_TAC ‘X' = λj x. X j x / s n’
 >> Q.ABBREV_TAC ‘Y' = λj x. Y j x / s n’
 >> Q.ABBREV_TAC ‘Z' = λj x. Z j x / s n’
 >> Know ‘∀x. x IN p_space p ⇒ X' j x + Z' j x = (X j x + Z j x) / Normal r’
 >- (rw [Abbr ‘X'’, Abbr ‘Z'’] \\
     irule div_add >> simp [] \\
     Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) \\
     gs [real_random_variable_def])
 >> STRIP_TAC
 >> Know ‘expectation p
          (Normal ∘ f ∘ real ∘ (λx. (X j x + Z j x) / Normal r)) =
          expectation p (Normal ∘ f ∘ real ∘ (λx. X' j x + Z' j x))’
 >- (irule expectation_cong >> simp [extreal_11])
 >> Rewr
 >> Know ‘∀x. x IN p_space p ⇒ Y' j x + Z' j x = (Y j x + Z j x) / Normal r’
 >- (rw [Abbr ‘Y'’, Abbr ‘Z'’] \\
     irule div_add >> simp [] \\
     Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) \\
     gs [real_random_variable_def])
 >> STRIP_TAC
 >> Know ‘expectation p
          (Normal ∘ f ∘ real ∘ (λx. (Y j x + Z j x) / Normal r)) =
          expectation p (Normal ∘ f ∘ real ∘ (λx. Y' j x + Z' j x))’
 >- (irule expectation_cong >> simp [extreal_11]) >> Rewr
 >> Know ‘∀j. j < n ⇒
              real_random_variable (X' j) p ∧ real_random_variable (Y' j) p ∧
              real_random_variable (Z' j) p ∧
              integrable p (λx. (abs (X' j x))³) ∧
              integrable p (λx. (abs (Y' j x))³) ∧
              indep_vars p (X' j) (Z' j) Borel Borel ∧
              indep_vars p (Y' j) (Z' j) Borel Borel’
 >- (Q.X_GEN_TAC ‘i’ >> STRIP_TAC >> STRONG_CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [Abbr ‘X'’] \\
         METIS_TAC [real_random_variable_cdiv]) \\
     DISCH_TAC >> STRONG_CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [Abbr ‘Y'’] \\
         METIS_TAC [real_random_variable_cdiv]) \\
     DISCH_TAC >> STRONG_CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [Abbr ‘Z'’] \\
         METIS_TAC [real_random_variable_cdiv]) \\
     DISCH_TAC >> STRONG_CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [Abbr ‘X'’] \\
         fs [real_random_variable_def] \\
         Know ‘∀x. x IN p_space p ⇒ (abs (X i x / Normal r))³ = abs (X i x) pow 3 / (Normal r) pow 3’
         >- (rw [] \\
             Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒ X i x ≠ −∞ ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
             ‘∃c. X i x = Normal c’ by METIS_TAC [extreal_cases] >> rw [] \\
             taylor_tactic2) >> DISCH_TAC \\
         ‘(Normal r) pow 3 = Normal (r pow 3)’ by rw [extreal_pow_def] \\
         Know ‘integrable p (λx. (abs (X i x))³ / ((Normal r) pow 3))’
         >- (POP_ORW \\
             MP_TAC (Q.SPECL [‘p’, ‘λx. (abs (X (i :num) x))³’, ‘r³’] integrable_cdiv) \\
             METIS_TAC [prob_space_def, REAL_POW_LT, REAL_LT_LE]) \\
         DISCH_TAC \\
         irule integrable_eq \\
         fs [prob_space_def] \\
         qexists ‘λx. (abs (X i x))³ / Normal r³’ \\ gs [p_space_def]) \\
     DISCH_TAC >> STRONG_CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [Abbr ‘Y'’] \\
         fs [real_random_variable_def] \\
         Know ‘∀x. x IN p_space p ⇒ (abs (Y i x / Normal r))³ = abs (Y i x) pow 3 / (Normal r) pow 3’
         >- (rw [] \\
             Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒ X i x ≠ −∞ ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
             ‘∃c. Y i x = Normal c’ by METIS_TAC [extreal_cases] >> rw [] \\
             taylor_tactic2) >> DISCH_TAC \\
         ‘(Normal r) pow 3 = Normal (r pow 3)’ by rw [extreal_pow_def] \\
         Know ‘integrable p (λx. (abs (Y i x))³ / ((Normal r) pow 3))’
         >- (POP_ORW \\
             MP_TAC (Q.SPECL [‘p’, ‘λx. (abs (Y (i :num) x))³’, ‘r³’] integrable_cdiv) \\
             METIS_TAC [prob_space_def, REAL_POW_LT, REAL_LT_LE]) \\
         DISCH_TAC \\
         irule integrable_eq \\
         fs [prob_space_def] \\
         qexists ‘λx. (abs (Y i x))³ / Normal r³’ \\ gs [p_space_def]) \\
     DISCH_TAC >> STRONG_CONJ_TAC
     >- (rw [Abbr ‘X'’, Abbr ‘Z'’] \\
         Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [] \\
         (MP_TAC o (Q.SPECL [‘p’, ‘X (i :num)’, ‘Z (i :num)’, ‘Borel’, ‘Borel’,
                             ‘λx. x / Normal r’, ‘λx. x / Normal r’]) o
                 (INST_TYPE [beta |-> “:extreal”])) indep_rv_cong \\
         Suff ‘(λx. x / Normal r) ∈ Borel_measurable Borel’
         >- (fs [real_random_variable_def, o_DEF]) \\
         irule IN_MEASURABLE_BOREL_CDIV >> simp [SIGMA_ALGEBRA_BOREL] \\
         qexistsl [‘λx. x’, ‘r’] >> METIS_TAC [IN_MEASURABLE_BOREL_BOREL_I]) \\
     DISCH_TAC \\
     rw [Abbr ‘Y'’, Abbr ‘Z'’] \\
     Q.PAT_X_ASSUM ‘∀j. j < n ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [] \\
     (MP_TAC o (Q.SPECL [‘p’, ‘Y (i :num)’, ‘Z (i :num)’, ‘Borel’, ‘Borel’, ‘λx. x / Normal r’, ‘λx. x / Normal r’]) o
             (INST_TYPE [beta |-> “:extreal”])) indep_rv_cong \\
     Suff ‘(λx. x / Normal r) ∈ Borel_measurable Borel’
     >- (fs [real_random_variable_def, o_DEF]) \\
     irule IN_MEASURABLE_BOREL_CDIV >> simp [SIGMA_ALGEBRA_BOREL] \\
     qexistsl [‘λx. x’, ‘r’] >> METIS_TAC [IN_MEASURABLE_BOREL_BOREL_I])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X'’, ‘Y'’, ‘Z'’, ‘f’, ‘M’, ‘n’] taylor_diff_expectation_bound)
 >> simp []
 >> STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs []
 >> Know ‘M / (6 * (Normal r)³) * (expectation p (λx. abs (X j x)³) + expectation p (λx. abs (Y j x)³)) =
          M / 6 * (expectation p (λx. abs (X' j x)³) + expectation p (λx. abs (Y' j x)³))’
 >- (rw [Abbr ‘X'’, Abbr ‘Y'’] \\
     Know ‘expectation p (λx. abs (X j x / Normal r)³) =
           expectation p (λx. abs (X j x)³) / (Normal r)³’
     >- (‘(Normal r) pow 3 = Normal (r pow 3)’ by rw [extreal_pow_def] \\
         MP_TAC (Q.SPECL [‘p’, ‘λx. abs (X (j :num) x)³’, ‘r pow 3’] expectation_cdiv) \\
         simp [] >> gs [] \\
         DISCH_THEN (fs o wrap o SYM) \\
         Know ‘∀x. x IN p_space p ⇒ abs (X j x / Normal r)³ = abs ((X j x) pow 3) / Normal (r pow 3)’
         >- (rw [] \\
             Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                                real_random_variable (X j) p ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs [] \\
             fs [real_random_variable_def] \\
             Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒ X j x ≠ −∞ ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
             ‘∃c. X j x = Normal c’ by METIS_TAC [extreal_cases] >> rw [] \\
             taylor_tactic1) >> STRIP_TAC \\
         irule expectation_cong >> fs []) >> Rewr \\
     Know ‘expectation p (λx. abs (Y j x / Normal r)³) =
           expectation p (λx. abs (Y j x)³) / (Normal r)³’
     >- (‘(Normal r) pow 3 = Normal (r pow 3)’ by rw [extreal_pow_def] \\
         MP_TAC (Q.SPECL [‘p’, ‘λx. abs (Y (j :num) x)³’, ‘r pow 3’] expectation_cdiv) \\
         simp [] >> gs [] \\
         DISCH_THEN (fs o wrap o SYM) \\
         Know ‘∀x. x IN p_space p ⇒ abs (Y j x / Normal r)³ = abs ((Y j x) pow 3) / Normal (r pow 3)’
         >- (rw [] \\
             Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                                real_random_variable (X j) p ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs [] \\
             fs [real_random_variable_def] \\
             Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒ Y j x ≠ −∞ ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
             ‘∃c. Y j x = Normal c’ by METIS_TAC [extreal_cases] >> rw [] \\
             taylor_tactic1) >> STRIP_TAC \\
         irule expectation_cong >> fs []) >> Rewr \\
     Know ‘expectation p (λx. abs (X j x)³) / (Normal r)³ +
           expectation p (λx. abs (Y j x)³) / (Normal r)³ =
           (expectation p (λx. abs (X j x)³)  +
            expectation p (λx. abs (Y j x)³)) / (Normal r)³’
     >- (irule div_add \\
         ‘(Normal r)³ ≠ 0’ by METIS_TAC [pow_pos_lt, GSYM extreal_lt_eq, normal_0, lt_le] \\
         simp [] \\
         Know ‘expectation p (λx. abs (X j x)³) ≠ −∞ ∧
               expectation p (λx. abs (X j x)³) ≠ +∞’
         >- (MP_TAC (Q.SPECL [‘p’, ‘λx. abs (X (j :num) x)³’] expectation_finite) \\
             simp [] \\
             Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                                real_random_variable (X j) p ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs [] \\
             ‘integrable p (λx. abs (X j x)³)’ by METIS_TAC [integrable_abs_third] >> gs []) >> Rewr \\
         MP_TAC (Q.SPECL [‘p’, ‘λx. abs (Y (j :num) x)³’] expectation_finite) \\
         simp [] \\
         Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                            real_random_variable (X j) p ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs [] \\
         ‘integrable p (λx. abs (Y j x)³)’ by METIS_TAC [integrable_abs_third] >> gs []) >> Rewr \\
     Q.ABBREV_TAC ‘h = (expectation p (λx. abs (X j x)³) + expectation p (λx. abs (Y j x)³))’ \\
     ‘M ≠ NegInf’ by METIS_TAC [abs_pos, le_trans,extreal_0_simps, lt_le] \\
     Know ‘M / (6 * (Normal r)³) = M * inv (6 * (Normal r)³)’
     >- (irule div_eq_mul_rinv \\
         simp [] \\
         ‘(Normal r)³ = Normal r³’ by rw [extreal_pow_def] >> POP_ORW \\
         ‘6 = Normal 6’ by EVAL_TAC >> POP_ORW \\
         ‘Normal 6 * Normal r³ = Normal (6 * r³)’ by rw [extreal_mul_def] >> POP_ORW \\
         rw [cj 14 extreal_0_simps]) >> Rewr \\
     Know ‘h / (Normal r)³ = h * inv ((Normal r)³)’
     >- (irule div_eq_mul_rinv \\
         Know ‘expectation p (λx. abs (X j x)³) ≠ −∞ ∧
               expectation p (λx. abs (X j x)³) ≠ +∞’
         >- (MP_TAC (Q.SPECL [‘p’, ‘λx. abs (X (j :num) x)³’] expectation_finite) \\
             simp [] \\
             Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                                real_random_variable (X j) p ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs [] \\
             ‘integrable p (λx. abs (X j x)³)’ by METIS_TAC [integrable_abs_third] >> gs []) >> DISCH_TAC \\
         Know ‘expectation p (λx. abs (Y j x)³) ≠ −∞ ∧
               expectation p (λx. abs (Y j x)³) ≠ +∞’
         >- (MP_TAC (Q.SPECL [‘p’, ‘λx. abs (Y (j :num) x)³’] expectation_finite) \\
             simp [] \\
             Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                                real_random_variable (X j) p ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs [] \\
             ‘integrable p (λx. abs (Y j x)³)’ by METIS_TAC [integrable_abs_third] >> gs []) >> DISCH_TAC \\
         ‘h ≠ −∞ ∧ h ≠ +∞’ by METIS_TAC [Abbr ‘h’, add_not_infty] >> simp [] \\
         METIS_TAC [pow_pos_lt, normal_0, GSYM extreal_lt_eq]) >> Rewr \\
     ‘M / 6 = M * inv 6’ by (irule div_eq_mul_rinv >> simp [] >> EVAL_TAC) >> POP_ORW \\
     ‘h * (Normal r)³ ⁻¹ = (Normal r)³ ⁻¹ * h’ by METIS_TAC [mul_comm] >> POP_ORW \\
     ‘(6 * (Normal r)³)⁻¹ =  6⁻¹ * (Normal r)³ ⁻¹’ by (irule inv_mul >> EVAL_TAC >> METIS_TAC [POW_NZ]) \\
     POP_ORW \\
     ‘M * (6⁻¹ * (Normal r)³ ⁻¹) = M * 6⁻¹ * (Normal r)³ ⁻¹’ by METIS_TAC [mul_assoc] >> POP_ORW \\
     METIS_TAC [mul_assoc]) >> Rewr >> fs []
QED

Theorem EXTREAL_SUM_IMAGE_ABS_TRIANGLE :
    ∀f s. FINITE s ⇒ abs (∑ f s) ≤ ∑ (λx. abs (f x)) s
Proof
    ‘∀f l. (!x. MEM x l ⇒ T) ⇒
           abs (FOLDR (λe acc. f e + acc) 0x l) ≤
           FOLDR (λe acc. abs (f e) + acc) 0x l’
    suffices_by rw [EXTREAL_SUM_IMAGE_ALT_FOLDR]
 >> Induct_on ‘l’ >> rw[listTheory.FOLDR]
 >> ‘abs (f h + FOLDR (λe acc. f e + acc) 0x l)
     ≤ abs (f h) + abs (FOLDR (λe acc. f e + acc) 0x l)’ by (irule abs_triangle_full >> simp[])
 >> ‘abs (FOLDR (λe acc. f e + acc) 0x l)
     ≤ FOLDR (λe acc. abs (f e) + acc) 0x l’ by simp[]
 >> ‘abs (f h) + abs (FOLDR (λe acc. f e + acc) 0x l)
     ≤ abs (f h) + FOLDR (λe acc. abs (f e) + acc) 0x l’ by (irule le_add2 >> simp[])
 >> METIS_TAC [le_trans]
QED

Theorem EXTREAL_SUM_IMAGE_ABS_LE :
    ∀f g s. FINITE s ∧ (∀x. x ∈ s ⇒ abs (f x) ≤ g x) ⇒ abs (∑ f s) ≤ ∑ g s
Proof
    rpt STRIP_TAC
  >> ‘abs (∑ f s) ≤ ∑ (λx. abs (f x)) s’ by (irule EXTREAL_SUM_IMAGE_ABS_TRIANGLE >> rw[])
  >> ‘(∀x. x ∈ s ⇒ (λx. abs (f x)) x ≤ g x)’ by simp[]
  >> ‘∑ (λx. abs (f x)) s ≤ ∑ g s’ by (irule EXTREAL_SUM_IMAGE_MONO' >> rw[])
  >> METIS_TAC [le_trans]
QED

(* eq 17 *)
Theorem clt_lindeberg_taylor_error_bound :
    ∀r X Y Z f M s n.
      prob_space r ∧
      (∀(j :num). j < n ⇒
           real_random_variable (X j) r ∧
           real_random_variable (Y j) r ∧
           real_random_variable (Z j) r ∧
           integrable r (λx. (abs (X j x))³) ∧
           integrable r (λx. (abs (Y j x))³) ∧
           indep_vars r (X j) (Z j) Borel Borel ∧
           indep_vars r (Y j) (Z j) Borel Borel) ∧
      f ∈ CnR 3 ∧
      M = sup (IMAGE (λt. abs (Normal (diff 3 f t))) UNIV) ∧
      0 < s n ∧ s n ≠ +∞ ∧ s n ≠ −∞ ⇒
      abs (∑ (λj. expectation r (Normal ∘ f ∘ real ∘ (λx. (X j x + Z j x) / s n)) −
                              expectation r (Normal ∘ f ∘ real ∘ (λx. (Y j x + Z j x) / s n))) (count n)) ≤
      M / (6 * (s n) pow 3)  * ∑ (λj. expectation r (λx. (abs (X j x))³ + (abs (Y j x))³)) (count n)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘Y’, ‘Z’, ‘f’, ‘M’, ‘s’, ‘n’] taylor_diff_expectation_bound_scaled)
 >> simp []
 >> Know ‘∀t. abs (Normal (diff 3 f t)) ≤
              sup (IMAGE (λt. abs (Normal (diff 3 f t))) 𝕌(:real))’
 >- (cheat)
 >> Rewr
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘M = _ ’ K_TAC
 >> Q.ABBREV_TAC ‘M = sup (IMAGE (λt. abs (Normal (diff 3 f t))) 𝕌(:real))’
 >> Q.ABBREV_TAC ‘g = λj.  M / (6 * (s n)³) *
                           (expectation r (λx. (abs (X j x))³) +
                            expectation r (λx. (abs (Y j x))³))’
 >> Q.ABBREV_TAC ‘h = λj. expectation r (Normal ∘ f ∘ real ∘ (λx. (X j x + Z j x) / s n)) −
                          expectation r (Normal ∘ f ∘ real ∘ (λx. (Y j x + Z j x) / s n))’
 >> gs []
 >> (MP_TAC o (Q.SPECL [‘h’, ‘g’, ‘count n’]) o
            (INST_TYPE [alpha |-> “:num”])) EXTREAL_SUM_IMAGE_ABS_LE
 >> simp [Abbr ‘h’, Abbr ‘g’]
 >> Know ‘∑ (λj. M / (6 * (s n)³) * (expectation r (λx. (abs (X j x))³) +
                                     expectation r (λx. (abs (Y j x))³))) (count n) =
          M / (6 * (s n)³) * ∑ (λj. expectation r (λx. (abs (X j x))³ + (abs (Y j x))³)) (count n)’
 >- (Q.ABBREV_TAC ‘g = λj x. (abs (X j x))³’ \\
     Q.ABBREV_TAC ‘h = λj x. (abs (Y j x))³’ >> gs [] \\
     Know ‘∀j. j < n ⇒ expectation r (λx. g j x) + expectation r (λx. h j x) =
                       expectation r (λx. g j x + h j x)’
     >- (rw [] \\
         MP_TAC (Q.SPECL [‘r’, ‘g (j :num)’, ‘h (j :num)’] (GSYM expectation_add)) \\
         simp [] \\
         Q.PAT_X_ASSUM ‘∀j. j < n ⇒
                            real_random_variable (X j) r ∧ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) \\
         METIS_TAC [ETA_AX]) \\
     DISCH_TAC \\
     Know ‘∑ (λj. expectation r (λx. g j x + h j x)) (count n) =
           ∑ (λj. (expectation r (λx. g j x) + expectation r (λx. h j x))) (count n)’
     >- (irule EXTREAL_SUM_IMAGE_EQ' >> simp [] \\
         Q.X_GEN_TAC ‘j’ >> rw []) >> rw [] \\
     Q.ABBREV_TAC ‘u = λj. expectation r (λx. g j x) + expectation r (λx. h j x)’ \\
     gs [] \\
     Know ‘M / (6 * (s n)³) ≠ PosInf ∧  M / (6 * (s n)³) ≠ NegInf’
     >- (cheat) \\
     STRIP_TAC \\
     ‘∃c.  M / (6 * (s n)³) = Normal c’ by METIS_TAC [extreal_cases] >> gs [] \\
     irule EXTREAL_SUM_IMAGE_CMUL \\
     simp [] \\
     DISJ2_TAC >> cheat)
 >> cheat
QED


(*prob_space_eq, measure_space_density_of, density_measure_def*)

Theorem measure_density :
    ∀m f s. measure (density m f) s = ∫⁺ m (λx. f x * 𝟙 s x)
Proof
  rw [measure_def, density]
QED

Theorem sets_ext_lborel :
    subsets Borel = measurable_sets ext_lborel
Proof
  rw [measurable_sets_def, ext_lborel_def]
QED

Theorem ext_lborel_Borel :
    measurable_space ext_lborel = Borel
Proof
    rw [ext_lborel_def]
QED

Theorem random_variable_Borel_imp_borel :
  ∀p X. prob_space p ∧ random_variable X p Borel ⇒ random_variable (real o X) p borel
Proof
  rw [random_variable_def, p_space_def, events_def, prob_space_def]
  >> irule in_borel_measurable_from_Borel
  >> simp [MEASURE_SPACE_SIGMA_ALGEBRA]
QED

Theorem MEASURABLE_PREIMAGE_BOREL :
    ∀f m.
      f ∈ Borel_measurable (measurable_space m) ⇒
      ∀s. s ∈ subsets Borel ⇒
         PREIMAGE f s ∩ m_space m ∈ measurable_sets m
Proof
    rpt STRIP_TAC
 >> (MP_TAC o (Q.SPECL [‘measurable_space m’, ‘Borel’, ‘f’]) o
            (INST_TYPE [beta |-> “:extreal”])) IN_MEASURABLE
 >> simp []
QED

Theorem measurable_preimage_borel :
  ∀f m.
    f ∈ borel_measurable (measurable_space m) ⇒
    ∀s. s ∈ subsets borel ⇒
        PREIMAGE f s ∩ m_space m ∈ measurable_sets m
Proof
  rpt STRIP_TAC
  >> (MP_TAC o (Q.SPECL [‘measurable_space m’, ‘borel’, ‘f’]) o
             (INST_TYPE [beta |-> “:real”])) IN_MEASURABLE
  >> simp []
QED

Theorem MEASURE_EMPTY_OUSIDE :
    ∀p s. measure_space p ∧ s ⊆ (UNIV DIFF m_space p) ∧ s ∈ measurable_sets p ⇒ measure p s = 0
Proof
    rpt STRIP_TAC
 >> Know ‘s INTER m_space p = {}’
 >- (rw [IN_INTER, EXTENSION, NOT_IN_EMPTY] \\
     fs [SUBSET_DEF, DIFF_DEF] \\
     METIS_TAC [])
 >> STRIP_TAC
 >> ‘s ⊆ m_space p’ by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE]
 >> Know ‘s = {}’
 >- (fs [INTER_DEF, SUBSET_DEF] >> cheat)
 >> gs [] >> METIS_TAC [MEASURE_EMPTY]
QED

Theorem normal_rv_eq :
    ∀p X Y mu sig.
      prob_space p ∧ normal_rv X p mu sig ∧
      (∀x. x ∈ p_space p ⇒ Y x = X x) ⇒ normal_rv Y p mu sig
Proof
    rw [normal_rv_def, random_variable_def, p_space_def, events_def]
 >- (irule in_borel_measurable_add \\
     fs [prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA] \\
     qexistsl [‘X’, ‘λx. 0’] >> simp [] \\
     irule in_borel_measurable_const \\
     fs [MEASURE_SPACE_SIGMA_ALGEBRA] \\
     qexists ‘0’ >> simp [])
 >> Q.PAT_X_ASSUM ‘∀s. s ∈ subsets borel ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘s’)
 >> gs [] >> POP_ASSUM (rw o wrap o SYM)
 >> rw [distribution_def, PREIMAGE_def] >> AP_TERM_TAC
 >> rw [Once EXTENSION, INTER_DEF]
 >> EQ_TAC >> rw [] >> METIS_TAC [p_space_def]
QED

Theorem normal_rv_affine_weaken :
    !X p mu sig Y a b.
    prob_space p /\ a <> 0 /\ 0 < sig /\
    normal_rv X p mu sig /\ (!x. x IN p_space p ⇒ Y x = b + a * X x) ==>
    normal_rv Y p (b + a * mu) (abs a * sig)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘f = λx. b + a * X x’ >> fs []
 >> MP_TAC (Q.SPECL [‘X’, ‘p’, ‘mu’, ‘sig’, ‘f’, ‘a’, ‘b’] normal_rv_affine')
 >> simp []
 >> METIS_TAC [normal_rv_eq]
QED

Theorem ext_normal_rv_affine :
    ∀X p mu sig Y a b.
      prob_space p ∧ a ≠ 0 ∧ 0 < sig ∧ ext_normal_rv X p mu sig ∧
      (∀x. Y x = Normal b + (Normal a) * X x) ⇒
      ext_normal_rv Y p (b + (a * mu)) ((abs a * sig))
Proof
    rpt STRIP_TAC
 >> fs [ext_normal_rv_def]
 >> STRONG_CONJ_TAC
 >- (GEN_TAC >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘∀x. x ∈ p_space p ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     ‘∃r. X x = Normal r’ by METIS_TAC [extreal_cases] >> fs [] \\
     METIS_TAC [extreal_not_infty, extreal_add_def, extreal_mul_def])
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘real o X’, ‘p’, ‘mu’, ‘sig’, ‘real o Y’, ‘a’, ‘b’] normal_rv_affine_weaken)
 >> simp []
 >> ‘∀x. x ∈ p_space p ⇒
         real (Normal b + Normal a * X x) = b + a * real (X x)’
   by METIS_TAC [extreal_cases, extreal_add_def, extreal_mul_def, real_normal]
 >> fs []
QED

Theorem MEASURABLE_EL'[local] :
  ∀p p' n i.
     prob_space p ∧ prob_space p' ∧
      i < n ∧ measurable_space p' = sigma_lists (measurable_space p) n ⇒
      EL i ∈ measurable (measurable_space p') (measurable_space p)
Proof
  rw []
  >> MP_TAC (Q.SPECL [‘measurable_space p’, ‘n’] MEASURABLE_EL)
  >> fs [prob_space_def, MEASURE_SPACE_SIGMA_ALGEBRA]
  >> STRIP_TAC >> POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs []
QED

Theorem in_measurable_borel_comp :
  ∀a b f g h.
    f ∈ borel_measurable b ∧ g ∈ measurable a b ∧
    (∀x. x ∈ space a ⇒ h x = f (g x)) ⇒
    h ∈ borel_measurable a
Proof
    rw [] >> dxrule_all_then assume_tac MEASURABLE_COMP
 >> irule in_measurable_borel_eq >> qexists_tac ‘f o g’ >> simp[]
QED

val indep_vars_tactic1 =
Know ‘∀i x. i < n ∧ x ∈ p_space p' ⇒ EL i x ∈ p_space p’
>- (rw [p_space_def, m_space_def, Once EXTENSION] \\
    ‘p_space p' = space (measurable_space p')’ by fs [p_space_def] \\
    ‘p_space p = space (measurable_space p)’ by fs [p_space_def] \\
    ‘space (measurable_space p') = rectangle (λi. space (measurable_space p)) n’
      by METIS_TAC [space_sigma_lists] \\
    ‘x ∈ rectangle (λi. p_space p) n’ by fs [p_space_def] \\
    fs [IN_list_rectangle]) >> DISCH_TAC ;


Theorem existence_of_indep_vars :
    ∀(p :α m_space) N (D :num -> real) n.
      prob_space p ∧ 0 < n ∧ ext_normal_rv N p 0 1 ∧
      (∀i. i < n ⇒ 0 < (D i)) ⇒
      ∃(p' :α list m_space) Y.
        prob_space p' ∧ (∀(i :num). i < n ⇒ ext_normal_rv (Y i) p' 0 (D i)) ∧
        indep_vars p' Y (λi. Borel) (count n)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘Y = λi x. Normal (D i) * (N x)’
 >> Know ‘∀(i :num). i < n ⇒ ext_normal_rv (Y i) p 0 (D i)’
    >- (rw [] \\
        MP_TAC (Q.SPECL [‘N’, ‘p’, ‘0’, ‘1’, ‘Y (i :num)’, ‘D (i :num)’, ‘0’] ext_normal_rv_affine) \\
        simp [] \\
        ‘D i ≠ 0’ by METIS_TAC [REAL_LT_LE] >> simp [] \\
        ‘abs (D i) = D i’ by METIS_TAC [ABS_REFL, REAL_LT_IMP_LE]
        >> simp [normal_0]) >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘n’] existence_of_multidimensional_prob_space')
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘p'’ STRIP_ASSUME_TAC)
 >> Q.ABBREV_TAC ‘Y' = λi x. Y i (EL i x)’
 >> qexistsl [‘p'’, ‘Y'’] >> art []
 >> CONJ_TAC
    >- (indep_vars_tactic1 \\
        fs [Abbr ‘Y'’, ext_normal_rv_def] \\
        fs [o_DEF, normal_rv_def] >> rw []
        >- (fs [random_variable_def, p_space_def, events_def] \\
            ‘sigma_lists (measurable_space p) n = measurable_space p'’ by rw [] \\
            POP_ORW \\
            Q.PAT_X_ASSUM ‘ ∀i'. i' < n ⇒ (∀x. x ∈ m_space p ⇒ Y i' x ≠ +∞ ∧ Y i' x ≠ −∞) ∧ _’
             (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [] \\
            (MP_TAC o (Q.SPECL [‘measurable_space p'’, ‘measurable_space p’, ‘real o Y (i :num)’,
                                ‘EL (i :num)’, ‘λx. real (Y i (EL i x))’]) o
                    (INST_TYPE [alpha |-> “:('a list)”, beta |-> “:'a”])) in_measurable_borel_comp \\
            simp [o_DEF] >> METIS_TAC [MEASURABLE_EL', ETA_AX]) \\
        fs [distribution_def] \\
        Q.PAT_X_ASSUM ‘T’ K_TAC \\
        Q.ABBREV_TAC ‘f = λi x. real (Y i x)’ >> fs [] \\
        ‘(\x. f i (EL i x)) = f i o (EL i)’ by rw [FUN_EQ_THM, o_DEF] \\
        POP_ORW \\
        Q.ABBREV_TAC ‘h = λj. if j = i then PREIMAGE (f j) s ∩ p_space p
                              else p_space p’ \\
        Know ‘PREIMAGE (f i ∘ EL i) s ∩ p_space p' = rectangle h n’
        >- (‘space (measurable_space p') = rectangle (λi. space (measurable_space p)) n’
              by METIS_TAC [space_sigma_lists, p_space_def] \\
            ‘p_space p' = rectangle (λi. p_space p) n’ by fs [p_space_def] \\
            fs [Once EXTENSION, IN_list_rectangle, Abbr ‘h’, IN_PREIMAGE, p_space_def] \\
            NTAC 2 (Q.PAT_X_ASSUM ‘T’ K_TAC) >> POP_ORW >> rw [] \\
            EQ_TAC >> rw []
            >- (Cases_on ‘j = i’ >> rw [])
            >- (POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> fs []) \\
            METIS_TAC [IN_INTER]) >> Rewr' \\
        Q.PAT_X_ASSUM ‘∀i'. i' < n ⇒ (∀x. x ∈ p_space p ⇒ Y i' x ≠ +∞ ∧ Y i' x ≠ −∞) ∧ _’
         (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [] \\
        Q.PAT_X_ASSUM ‘∀s'. s' ∈ subsets borel ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘s’) >> gs [] \\
        POP_ASSUM (rw  o wrap o SYM) \\
        Q.PAT_X_ASSUM ‘∀h. (∀i. i < n ⇒ h i ∈ events p) ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘h’) \\
        Know ‘∀i. i < n ⇒ h i ∈ events p’
        >- (Q.X_GEN_TAC ‘j’ >> POP_ASSUM K_TAC >> rw [Abbr ‘h’]
            >- (fs [p_space_def, events_def, random_variable_def] \\
                METIS_TAC [measurable_preimage_borel, events_def, p_space_def]) \\
            METIS_TAC [EVENTS_SPACE]) >> STRIP_TAC >> gs [] \\
        ‘∀i. i < n ⇒ count n = {i} ∪ (count n DELETE i)’
          by rw [DELETE_DEF, UNION_DEF, DIFF_DEF, count_def, Once EXTENSION] \\
        POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘i’) >> gs [] >> POP_ORW \\
        Know ‘∏ (λx. prob p (h x)) ({i} ∪ (count n DELETE i)) =
              ∏ (λx. prob p (h x)) {i} * ∏ (λx. prob p (h x)) (count n DELETE i)’
        >- (irule EXTREAL_PROD_IMAGE_DISJOINT_UNION >> simp [DISJOINT_DIFF]) >> Rewr \\
        Know ‘∏ (λx. prob p (h x)) (count n DELETE i) = 1’
        >- (Know ‘∏ (λx. prob p (h x)) (count n DELETE i) =
                  ∏ (λi. 1) (count n DELETE i)’
            >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ \\
                rw [Abbr ‘h’, o_DEF] >> rw [PROB_UNIV]) >> Rewr \\
            irule EXTREAL_PROD_IMAGE_1 >> fs []) >> Rewr \\
        rw [PREIMAGE_def, Abbr ‘f’, mul_rone] \\
        rw [PREIMAGE_def, Abbr ‘h’])
 >> rw [indep_vars_def, IN_DFUNSET]
 >> Q.ABBREV_TAC ‘h = λj. if j ∈ N' then PREIMAGE (Y j) (E j) ∩ p_space p else p_space p’
 >> Know ‘∀j. j IN N' ⇒ PREIMAGE (Y' j) (E j) ∩ p_space p'
                        = PREIMAGE (EL j) (PREIMAGE (Y j) (E j)) ∩ p_space p'’
 >- (rw [Abbr ‘Y'’, PREIMAGE_def, Once EXTENSION]) >> DISCH_TAC
 >> Know ‘∀j. j IN N' ⇒ PREIMAGE (EL j) (PREIMAGE (Y j) (E j)) ∩ p_space p' =
                        PREIMAGE (EL j) (h j) ∩ p_space p' ’
 >- (rw [Abbr ‘h’, PREIMAGE_def, Once EXTENSION] \\
     EQ_TAC >> rw [] \\
     indep_vars_tactic1 \\
     POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [‘j’, ‘x’]) >> gs [count_def, SUBSET_DEF])
 >> DISCH_TAC
 >> Know ‘BIGINTER (IMAGE (λj. PREIMAGE (Y' j) (E j) ∩ p_space p') N') =
          BIGINTER (IMAGE (λj. PREIMAGE (EL j) (h j) ∩ p_space p') N')’
 >-(AP_TERM_TAC >> rw [IMAGE_DEF, Once EXTENSION] \\
    EQ_TAC >> rw [] >> qexists ‘j’ >> rw [])
    >> Rewr



 >> Know ‘BIGINTER (IMAGE (λj. PREIMAGE (EL j) (h j) ∩ p_space p') N') =
          rectangle h n INTER p_space p'’
    >- (rw [BIGINTER_IMAGE, list_rectangle_def, IN_GSPEC_IFF, IN_PREIMAGE, IN_INTER, Abbr ‘h’, Once EXTENSION] \\
   (*     >> EQ_TAC >> simp [] >> STRIP_TAC
        >- (GEN_TAC >> STRIP_TAC \\
            ‘j < n’ by fs [count_def, SUBSET_DEF] \\
            Q.PAT_X_ASSUM ‘∀j. j < n ⇒ EL j x ∈ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘j’) >> gs []) \\*)
        cheat)
 >> Rewr
 >> Q.PAT_X_ASSUM ‘∀h. (∀i. i < n ⇒ h i ∈ events p) ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘h’)
 >> Know ‘∀i. i < n ⇒ h i ∈ events p’
 >- (cheat) >> DISCH_THEN (fs o wrap)
 >> Know ‘∏ (prob p ∘ h) N' = ∏ (prob p' ∘ (λn. PREIMAGE (Y' n) (E n) ∩ p_space p')) N'’
 >- (cheat) >> DISCH_THEN (fs o wrap o SYM)
 >> Know ‘prob p' (rectangle h n ∩ p_space p') = prob p' (rectangle h n)’
 >- (cheat) >> Rewr
 >> POP_ORW
 >> ‘count n = N' UNION (count n DIFF N')’ by METIS_TAC [UNION_DIFF] >> POP_ORW
 >> Know ‘∏ (prob p ∘ h) (N' ∪ (count n DIFF N')) =
          ∏ (prob p ∘ h) N' * ∏ (prob p ∘ h) (count n DIFF N')’
 >- (irule EXTREAL_PROD_IMAGE_DISJOINT_UNION >> simp [DISJOINT_DIFF]) >> Rewr
 >> Know ‘∏ (prob p ∘ h) (count n DIFF N') = 1’
 >- (Know ‘∏ (prob p ∘ h) (count n DIFF N') =
           ∏ (λi. 1) (count n DIFF N')’
     >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ \\
         rw [Abbr ‘h’, o_DEF] >> rw [PROB_UNIV]) >> Rewr \\
     irule EXTREAL_PROD_IMAGE_1 >> fs []) >> Rewr
 >> METIS_TAC [mul_rone]
QED

Theorem PROD_PROB_SPACE :
    ∀p1 p2.
      prob_space p1 ∧ prob_space p2 ⇒
      prob_space (p1 CROSS p2)
Proof
  rpt STRIP_TAC
  >> ‘sigma_finite p1 ∧ sigma_finite p2’ by METIS_TAC [PROB_SPACE_SIGMA_FINITE]
  >> fs [prob_space_def, p_space_def, prob_def, events_def]
  >> STRONG_CONJ_TAC
  >- (irule measure_space_prod_measure \\
      simp [sigma_finite_measure_space_def])
  >> STRIP_TAC
  >> rw [prod_measure_space_def, prod_sigma_def, SPACE_PROD_SIGMA]
  >> ‘m_space p1 IN measurable_sets p1’ by METIS_TAC [EVENTS_SPACE, p_space_def, events_def, prob_space_def]
  >> ‘m_space p2 IN measurable_sets p2’ by METIS_TAC [EVENTS_SPACE, p_space_def, events_def, prob_space_def]
  >>  METIS_TAC [PROD_MEASURE_CROSS, mul_rone]
QED

Theorem construct_auxiliary_seq :
    ∀p1 (p2 :'a list m_space) X Y (n :num).
      prob_space p1 ∧ prob_space p2 ∧ 0 < n ∧
      (∀i. i < n ⇒ real_random_variable (X i) p1) ∧
      (∀i. i < n ⇒ real_random_variable (Y i) p2) ⇒
      ∃p X' Y' Z.
        (p = p1 CROSS p2) ∧
        (X' = λi. X i ∘ FST) ∧
        (Y' = λi. Y i ∘ SND) ∧
        prob_space p ∧
        (∀i. i < n ⇒ real_random_variable (X' i) p) ∧
        (∀i. i < n ⇒ real_random_variable (Y' i) p) ∧
        (Z = λi x. if i < n then X' i x else Y' (i - n) x) ∧
        indep_vars p Z (λ(i :num). Borel) (count (2*n))
Proof
  rpt STRIP_TAC
 >> (MP_TAC o (Q.SPECL [‘p1’, ‘p2’]) o
             (INST_TYPE [beta |-> (“:'a list”), alpha |-> “:'b”] )) PROD_PROB_SPACE
 >> simp [] >> STRIP_TAC
 >> Q.ABBREV_TAC ‘(X' :num -> β # α list -> extreal) = λi. X i ∘ FST’
 >> Q.ABBREV_TAC ‘Y' = λi. Y i ∘ SND’
 >> Q.ABBREV_TAC ‘Z = λ(i :num) x. if i < n then X' i x else Y' (i - n) x’
 >> STRONG_CONJ_TAC
 >- (METIS_TAC [Abbr ‘p’, Abbr ‘X'’, real_random_variable_prod_measure_fst])
 >> STRIP_TAC
 >> STRONG_CONJ_TAC
 >- (METIS_TAC [Abbr ‘p’, Abbr ‘Y'’, real_random_variable_prod_measure_snd])
 >> STRIP_TAC
 >> cheat
QED

Theorem central_limit_theorem :
    ∀p X N.
      prob_space p ∧
      ext_normal_rv N p 0 1 ∧
      (∀i. real_random_variable (X i) p) ∧
      (∀n. indep_vars p X (λi. Borel) (count n)) ∧
      (∀i. expectation p (X i) = 0) ∧
      (∀i. expectation p (λx. (abs (X i x))³) < +∞) ∧
      (∀i. variance p (X i) < PosInf) ∧
      (∀i. variance p (X i) ≠ 0) ∧
      (∀n. (sqrt (second_moments p X n)) ≠ 0) ∧
      ((\n. (third_moments p X n) / ((sqrt (second_moments p X n)) pow 3)) --> 0) sequentially ⇒
      ((\n x. (SIGMA (λi. X i x) (count n)) / (sqrt (second_moments p X n))) --> N) (in_distribution p)
Proof

  rpt STRIP_TAC
  >> Q.ABBREV_TAC ‘s = λn. sqrt (second_moments p X n)’
  >> fs []
  >> Q.ABBREV_TAC ‘b = λn. third_moments p X n’
  >> fs []
  >> Q.ABBREV_TAC ‘R = λn x. ∑ (λi. X i x) (count n) / s n’
  >> clt_tactic1
  >> Q.PAT_X_ASSUM ‘∀n. 0 ≤ s n’ (K_TAC)
  >> ‘∀i. integrable p (X i) ∧ integrable p (λx. (X i x)³)’ by METIS_TAC [clt_integrable_lemma]
  >> Know ‘∀i. real_random_variable (R i) p’
  >- (Q.X_GEN_TAC ‘n’ \\
      drule real_random_variable_sum_cdiv \\
      STRIP_TAC \\
      POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [‘X’, ‘s’, ‘n’]) \\
      gs [] \\
      fs [Abbr ‘R’])
  >> DISCH_TAC
  >> Know ‘∀i. integrable p (R i)’
  >- (Q.X_GEN_TAC ‘n’ \\
      drule integrable_sum_cdiv \\
      STRIP_TAC \\
      POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [‘X’, ‘s’, ‘n’]) \\
      gs [] \\
      fs [Abbr ‘R’])
  >> DISCH_TAC
  >> MP_TAC (Q.SPECL [‘p’, ‘R’, ‘N’] converge_in_dist_third_alt')
  >> Know ‘real_random_variable N p’
  >- (fs [ext_normal_rv_def, real_random_variable_def, normal_rv_def] \\
      METIS_TAC [random_variable_borel_imp_Borel])
  >> Rewr
  >> fs []
  >> rpt STRIP_TAC
  >> Q.PAT_X_ASSUM ‘(R ⟶ N) (in_distribution p) ⇔ _’ (K_TAC)
  >> Q.ABBREV_TAC ‘M = λn. expectation p (Normal ∘ f ∘ real ∘ R n)’
  >> Q.ABBREV_TAC ‘Q = expectation p (Normal ∘ f ∘ real o N)’
  >> Know ‘Q ≠ +∞ ∧ Q ≠ −∞’
  >- (simp [Abbr ‘Q’] \\
      MATCH_MP_TAC clt_expectation_sum_not_infty_normal_rv \\
      rw [ext_normal_rv_def])
  >> DISCH_TAC
  >> Know ‘∀n. 0 ≤ n ⇒ M n ≠ +∞ ∧ M n ≠ −∞’
  >- (Q.UNABBREV_TAC ‘M’ \\
      BETA_TAC \\
      MP_TAC (Q.SPECL [‘p’, ‘X’, ‘s’, ‘R’, ‘f’] clt_expectation_sum_not_infty) \\
      simp [])
  >> DISCH_TAC
  >> Suff ‘((λx. M x - Q) --> 0) sequentially’
  >- (MP_TAC (Q.SPECL [‘M’, ‘Q’] lim_null) \\
      simp [] \\
      DISCH_THEN (fs o wrap) \\
      STRIP_TAC \\
      METIS_TAC [lim_null_equiv_extreal_real])
  >> NTAC 2 (POP_ASSUM (K_TAC))
  >> rw [Abbr ‘M’, Abbr ‘Q’]
  >> fs [EXTREAL_LIM_SEQUENTIALLY]
  (** Constructing Y **)
  >> ‘∀i. 0 ≤ variance p (X i)’ by METIS_TAC [variance_pos]
  >> ‘∀i. variance p (X i) ≠ NegInf /\ variance p (X i) ≠ PosInf’
    by METIS_TAC [extreal_0_simps, lt_trans, lt_le]
  >> rw []
  >> ‘0 < (2 :real)’ by simp []
  >> ‘0 < e / 2’ by METIS_TAC [REAL_LT_DIV]
  >> Q.PAT_X_ASSUM ‘ ∀e. 0 < e ⇒ _’ (STRIP_ASSUME_TAC o Q.SPEC ‘e / 2’)
  >> gs []
  >> qexists ‘MAX N' 1’
  >> rename1 ‘MAX k 1’
  >> Q.X_GEN_TAC ‘n’
  >> STRIP_TAC
  >> ‘1 ≤ n’ by METIS_TAC [MAX_LE, MAX_DEF]
  >> ‘0 < (1 :num)’ by simp []
  >> ‘0 < n’ by METIS_TAC [LESS_LESS_EQ_TRANS]
  >> gs []
  >> ‘∀i. i < n ⇒ sqrt (real (variance p (X i))) ≠ 0’ by cheat
  >> ‘∀i. i < n ⇒ 0 < real (variance p (X i))’ by cheat
  >> MP_TAC (Q.SPECL [‘p’, ‘N’, ‘λi. real (variance p (X i))’, ‘n’] existence_of_indep_vars)
  >> simp []
  >> STRIP_TAC
  >> (MP_TAC o (Q.SPECL [‘p’, ‘p'’, ‘X’, ‘Y’, ‘n’]) o
              (INST_TYPE [beta |-> “:'a”])) construct_auxiliary_seq
  >> simp []
  >> Know ‘∀i. i < n ⇒ real_random_variable (Y i) p'’
  >- (rw [] \\
      Q.PAT_X_ASSUM ‘∀i. i < n ⇒ ext_normal_rv (Y i) p' 0 (real (variance p (X i)))’
       (STRIP_ASSUME_TAC o Q.SPEC ‘i’) \\
      gs [ext_normal_rv_def, normal_rv_def, real_random_variable_def] \\
      irule random_variable_borel_imp_Borel >> fs [])
  >> Rewr
  >> STRIP_TAC
  >> Know ‘∀i. i < n ⇒ 0 < variance p (X i)’
  >- (rw [] \\
      Q.PAT_X_ASSUM ‘∀i. variance p (X i) ≠ 0’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) \\
      Q.PAT_X_ASSUM ‘∀i. 0 ≤ variance p (X i)’ (STRIP_ASSUME_TAC o Q.SPEC ‘i’) \\
      rw [lt_le])
  >> Rewr
  (** Eq 15 **)
  >> Q.ABBREV_TAC ‘(Y' :num -> 'a # α list -> extreal) = λi. Y i o SND’
  >> fs []
  >> Q.ABBREV_TAC ‘(X' :num -> 'a # α list -> extreal) = λi. X i o FST’
  >> fs []
  >> ‘∀x. (R n ∘ FST) x = ∑ (λi. X' i x) (count n) / s n’ by rw [Abbr ‘X'’, Abbr ‘R’]
  >> Q.ABBREV_TAC ‘r = p CROSS p'’
  >> Know ‘expectation p (Normal ∘ f ∘ real ∘ R n) =
           expectation r (Normal ∘ f ∘ real ∘ R n o FST)’
  >- (Q.ABBREV_TAC ‘h = Normal ∘ f ∘ real ∘ R n’ \\
      ‘expectation r (Normal ∘ f ∘ real ∘ R n ∘ FST) = expectation r (h ∘ FST)’ by rw [Abbr ‘h’] \\
      POP_ASSUM (rw o wrap) \\
      gs [Abbr ‘r’] \\
      irule expectation_multidimentional_compose_fst \\
      simp [] \\
      fs [Abbr ‘h’] \\
      METIS_TAC [integrable_CnR_comp, real_random_variable_CnR_comp])
  >> Rewr'
  >> Q.ABBREV_TAC ‘g = R n ∘ (FST :α # α list -> α)’
  >> Q.ABBREV_TAC ‘h = λx. ∑ (λi. X' i x) (count n) / s n’
  >> (MP_TAC o (Q.SPECL [‘r’, ‘g’, ‘h’]) o
             (INST_TYPE [alpha |-> ``: ('a # 'a list)``])) expectation_cong
  >> rw []
  >> ‘expectation r (Normal ∘ f ∘ real ∘ g) = expectation r (Normal ∘ f ∘ real ∘ h)’ by METIS_TAC [expectation_cong]
  >> POP_ORW
  >> rw [Abbr ‘h’]
 >> Know ‘expectation p (Normal ∘ f ∘ real ∘ N) =
           expectation r (Normal ∘ f ∘ real ∘ (λx. ∑ (λi. Y' i x) (count n) / s n))’
  >- (cheat)
  >> DISCH_THEN (fs o wrap)
  >> Q.ABBREV_TAC ‘Z = λj w. ∑ (λi. Y' i w) (count j) + ∑ (λi. X' i w) (count n DIFF count1 j)’
  >> (MP_TAC o (Q.SPECL [‘r’, ‘X'’, ‘Y'’, ‘f’, ‘s’, ‘Z’, ‘n’]) o
             (INST_TYPE [alpha |-> “:('a # 'a list)”])) clt_Lindeberg_replacement_trick_bounded
  >> simp []
  >> Know ‘∀i. i < n ⇒ integrable p' (Y i)’
  >- (GEN_TAC >> STRIP_TAC \\
      fs [integrable_alt_def, prob_space_def] \\
      cheat) (*  ∫ pp (abs ∘ Y i) = 0 ≠ PosInf*)
  >> DISCH_TAC
  >> Know ‘∀i. i < n ⇒ integrable r (X' i) ∧ integrable r (Y' i)’
  >- (METIS_TAC [Abbr ‘X'’, Abbr ‘r’, Abbr ‘Y'’, integrable_fst, integrable_snd])
  >> DISCH_TAC >> simp []
  >> DISCH_THEN (rw o wrap)
  >> (MP_TAC o (Q.SPECL [‘r’, ‘X'’, ‘Y'’, ‘Z’, ‘f’ ,‘n’]) o
             (INST_TYPE [alpha |-> “:('a # 'a list)”])) clt_real_random_variable_partial_sum1
  >> simp []
  >> DISCH_TAC
  >> Q.ABBREV_TAC ‘(M :extreal) = sup (IMAGE (λt. abs (Normal (diff 3 f t))) UNIV)’
  >> (MP_TAC o (Q.SPECL [‘r’, ‘X'’, ‘Y'’, ‘Z’, ‘s’, ‘n’, ‘f’, ‘M’]) o
             (INST_TYPE [alpha |-> “:('a # 'a list)”])) clt_lindeberg_taylor_error_bound
  >> simp []
  >>  cheat
QED




(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory();
val _ = html_theory "central_limit";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [4] Qasim, M.: Formalization of Normal Random Variables, Concordia University (2016).
  [5] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Edition).
      World Scientific Publishing Company (2006).


 *)
