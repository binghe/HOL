(* ========================================================================= *)
(* The Central Limit Theorems                                                *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open pairTheory combinTheory optionTheory prim_recTheory arithmeticTheory
                pred_setTheory pred_setLib topologyTheory hurdUtils;

open realTheory realLib iterateTheory seqTheory transcTheory real_sigmaTheory
                real_topologyTheory;

open util_probTheory extrealTheory sigma_algebraTheory measureTheory
     real_borelTheory borelTheory lebesgueTheory martingaleTheory
     probabilityTheory derivativeTheory;

val _ = new_theory "central_limit";


Definition mgf_def:
  mgf p X s  =
  expectation p (\x. exp (Normal s * X x))
End

Theorem mgf_0:
  !p X. prob_space p ==> mgf p X 0 = 1
Proof
  RW_TAC std_ss [mgf_def, mul_lzero, exp_0, normal_0]
  >> MATCH_MP_TAC expectation_const >> art[]
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
  ∀p X r. prob_space p ∧ real_random_variable X p ⇒
                     real_random_variable (λx. exp (Normal s * X x)) p
Proof
  rw [real_random_variable_cmul, real_random_variable_exp]
QED

Theorem mgf_linear:
  ∀p X a b s. prob_space p ∧ real_random_variable X p ∧
              integrable p (λx. exp (Normal (a * s) * X x))  ⇒
              mgf p (λx.( Normal a * X x) + Normal b) s =  (exp (Normal s * Normal b)) * mgf p X (a * s)

Proof
  rw [mgf_def, real_random_variable_def]
  >> Know ‘ expectation p (λx. exp (Normal s * ((Normal a * X x) + Normal b)))
            = expectation p (λx. exp ((Normal s * (Normal a * X x)) + Normal s * Normal b))’
  >- ( MATCH_MP_TAC expectation_cong  >> rw[] >> AP_TERM_TAC
      >> ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases] >> rw[]
      >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq] >> rw[add_ldistrib_normal2]
    ) >> Rewr'
  >> Know ‘expectation p
           (λx. exp (Normal s * (Normal a * X x) + Normal s * Normal b)) =
           expectation p (λx. (exp (Normal s * (Normal a * X x))) * exp (Normal s * Normal b))’
  >- ( MATCH_MP_TAC expectation_cong
       >> rw[exp_add]
       >>  ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases]>> rw[]
       >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq] >> rw[]
       >> ‘∃e. Normal s * Normal d = Normal e’ by METIS_TAC [extreal_mul_eq] >> rw[]
       >> ‘∃f. Normal s * Normal b = Normal f’ by METIS_TAC [extreal_mul_eq] >> rw[exp_add]
     ) >> Rewr'
  >> ‘∃g. exp (Normal s * Normal b) = Normal g’ by  METIS_TAC [extreal_mul_eq, normal_exp]
  >> rw[]
  >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm]
  >> rw [mul_assoc, extreal_mul_eq]
  >> HO_MATCH_MP_TAC expectation_cmul
  >> ASM_REWRITE_TAC []
QED

Theorem mgf_sum:
  !p X Y s . prob_space p /\ real_random_variable X p  /\
             real_random_variable Y p  /\ indep_vars p X Y Borel Borel
             ∧  mgf p (\x. X x + Y x) s ≠ PosInf ∧  mgf p X s ≠ PosInf
             ∧  mgf p Y s ≠ PosInf  ==>
            mgf p (\x. X x + Y x) s = mgf p X s * mgf p Y s
Proof
  rw [mgf_def, real_random_variable_def]
  >> Know ‘expectation p (\x. exp (Normal s * (X x + Y x))) =
                       expectation p (\x. exp ((Normal s * X x) + (Normal s * Y x)))’
  >-( MATCH_MP_TAC expectation_cong >> rw[] >> AP_TERM_TAC
      >> MATCH_MP_TAC add_ldistrib_normal >> rw[])
      >> Rewr'
  >> Know ‘ expectation p (λx. exp (Normal s * X x + Normal s * Y x)) =
            expectation p (λx. exp (Normal s * X x) * exp (Normal s * Y x))’
  >- ( MATCH_MP_TAC expectation_cong  >> rw[] >> MATCH_MP_TAC exp_add >> DISJ2_TAC
       >> ‘∃a. X x = Normal a’ by METIS_TAC [extreal_cases]
       >>  ‘∃b. Y x = Normal b’ by METIS_TAC [extreal_cases]
       >> rw[extreal_mul_eq]) >> Rewr'
  >> HO_MATCH_MP_TAC indep_vars_expectation
  >> simp[]

  >> CONJ_TAC
     (* real_random_variable (λx. exp (Normal s * X x)) p *)
  >- ( MATCH_MP_TAC real_random_variable_exp_normal
       >>  fs[real_random_variable, random_variable_def] )

  >> CONJ_TAC
     (* real_random_variable (λx. exp (Normal s * X x)) p *)
  >- ( MATCH_MP_TAC real_random_variable_exp_normal
       >>  fs[real_random_variable, random_variable_def] )

  >> CONJ_TAC
     (* indep_vars p (λx. exp (Normal s * X x)) (λx. exp (Normal s * Y x)) Borel Borel *)
  >- ( Q.ABBREV_TAC ‘f = λx. exp (Normal s * x)’
       >> simp []
       >> MATCH_MP_TAC ( REWRITE_RULE [o_DEF] indep_rv_cong )   >> csimp[]
       >> Q.UNABBREV_TAC ‘f’
       >> MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
       >> simp [] >> Q.EXISTS_TAC ‘λx. Normal s * x’ >> simp[SIGMA_ALGEBRA_BOREL]
       >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
       >> qexistsl [‘λx. x’, ‘s’]
       >> simp[SIGMA_ALGEBRA_BOREL,  IN_MEASURABLE_BOREL_BOREL_I])

  >> Know ‘(λx. exp (Normal s * X x)) ∈ Borel_measurable (measurable_space p)’
  >- ( MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
       >> Q.EXISTS_TAC ‘λx. Normal s * X x’
       >> fs [prob_space_def, measure_space_def]
       >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
       >> qexistsl [‘X’, ‘s’] >> simp[random_variable_def]
       >> fs [random_variable_def, p_space_def, events_def])
  >> DISCH_TAC

  >> Know ‘(λx. exp (Normal s * Y x)) ∈ Borel_measurable (measurable_space p)’
  >- ( MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
       >> Q.EXISTS_TAC ‘λx. Normal s * Y x’
       >> fs [prob_space_def, measure_space_def]
       >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
       >> qexistsl [‘Y’, ‘s’] >> simp[random_variable_def]
       >> fs [random_variable_def, p_space_def, events_def])
  >> DISCH_TAC

  >> Q.ABBREV_TAC ‘f = λx. exp (Normal s * X x)’ >> simp []
  >> ‘∀x. x ∈ p_space p ⇒ 0 ≤  f x’ by METIS_TAC [exp_pos]
  >> Q.ABBREV_TAC ‘g = λx. exp (Normal s * Y x)’ >> simp []
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

(*------------------------------------------------------------------*)

Theorem mgf_sum_independent:
  ∀p X s (J : 'index set). prob_space p /\ FINITE J /\
                           (∀i. i IN J ⇒ real_random_variable (X i) p)
                           ==> mgf p (λx. SIGMA (λi. X i x) J) s =
                                   PI (λi. mgf p (X i) s) J
Proof
  rpt GEN_TAC
  >> STRIP_TAC
  >> FULL_SIMP_TAC std_ss [mgf_def]
  >> Know ‘expectation p (λx. exp (Normal s * ∑ (λi. X i x) J)) =
           expectation p (λx.  ∏ (λi. exp (Normal s * X i x)) J)’
           >- ( MATCH_MP_TAC expectation_cong >> rw[]

)



QED



Theorem mgf_uniqueness_discreate:
  ∀p X Y s. prob_space p ∧ FINITE (p_space p) ∧
                       real_random_variable X p ∧
                       real_random_variable Y p ∧
            mgf p X s ≠ PosInf ∧
            mgf p X s ≠ NegInf ∧
            mgf p Y s ≠ PosInf ∧
            mgf p Y s ≠ NegInf ∧
            mgf p X s = mgf p Y s ⇒
            distribution p X = distribution p Y
Proof


QED


Theorem mgf_uniqueness:
  ∀p X Y s. prob_space p ∧ real_random_variable X p ∧ real_random_variable Y p ∧
            mgf p X s ≠ PosInf ∧
            mgf p X s ≠ NegInf ∧
            mgf p Y s ≠ PosInf ∧
            mgf p Y s ≠ NegInf ∧
            mgf p X s = mgf p Y s ⇒
            distribution p X =  distribution p Y
Proof
  rw [mgf_def, distribution_def]

  >> qexists_tac ‘x’

  (** expectation p (λx. exp (Normal s * X x)) =
           expectation p (λx. exp (Normal s * Y x)) **)
  >> Q.PAT_X_ASSUM ‘expectation p (λx. exp (Normal s * X x)) =
                    expectation p (λx. exp (Normal s * Y x))’ MP_TAC
  >> MATCH_MP_TAC expectation_cong
QED



(*independent_identical_distribution*)
Definition iid_def:
  iid p X E A J ⇔  identical_distribution p X E J ∧
                 pairwise_indep_vars p X A J
End

Definition normal_distribution_def:
  ∀ p X J. normal_distribution p X J M V ⇔
           real_random_variable p X ∧
           (∀ i. i ∈ J) ∧
           M = expectation p (λi. X i) ∧ M  ≠ PosInf ∧ M ≠ NegInf ∧
           V = variance p X ∧ V > 0 ∧ V ≠ PosInf ⇒
           pdf p X =
           (1 / (sqrt (2 * pi * V))) *
           exp ( - ((X i - M) ** 2) / (2 * V))
End

Theorem central_limit_theorem_iid:
  ∀p X E A J . prob_space p ∧
               iid p X E A J ∧
               (∀i. i IN J ⇒ variance p (X i) ≠ PosInf ∧
               variance p (X i) ≠ NegInf) ∧
               (∀i. i IN J ⇒ real_random_variable (X i) p) ⇒
               ( (λi x. (Σ (X i x) J / n) - expectation p (X i)) /(sqrt (variance p (X 0)) / sqrt(& i)) -->
                    normal_distribution p X J 0 1  (in_distribution p)
Proof
QED


Theorem mgf_derivative:
  ∀mgf mgf' p X s. (mgf p X s) has_derivative (mgf' p X s) net (at 0) ⇒
            mgf' p X 0 = expectation p (\x.  X x)
Proof
QED




val _ = export_theory ();
val _ = html_theory "central_limit";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).

 *)