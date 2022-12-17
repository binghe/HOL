(* ------------------------------------------------------------------------- *)
(*  Kolmogorov's Inequalities and Convergence of Series                      *)
(*                                                                           *)
(*  Author: Dr. Chun Tian <binghe.lisp@gmail.com> (2022 - 2023)              *)
(*          Fondazione Bruno Kessler (FBK), Italy                            *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory pred_setTheory pred_setLib logrootTheory
     numLib realTheory realLib seqTheory transcTheory real_sigmaTheory
     iterateTheory real_topologyTheory hurdUtils util_probTheory;

open sigma_algebraTheory extrealTheory measureTheory borelTheory
     lebesgueTheory martingaleTheory probabilityTheory;

(* local theories *)
open stochastic_processTheory;

(* val _ = intLib.deprecate_int(); *)

val _ = new_theory "convergence";

val set_ss = std_ss ++ PRED_SET_ss;

val _ = hide "S";
val _ = hide "W";

(* Kolmogorov's two remarkable inequalities. This is the first one.

   This is Theorem 5.3.1 [2, p.121], see also [5, p.7]

   Remark. If we replace the ‘max_fn_seq (\i. abs o Z i) (SUC n) x’ in the formula
   by ‘abs (Z (SUC n))’, this becomes a simple case of Chebyshev's inequality, of
   which it is thus an essential improvement.

   NOTE: Z(0) = X(0), Z(1) = X(0) + X(1), ...
 *)

Theorem events_max_fn_seq[local] :
    !p Z. prob_space p /\ (!n. real_random_variable (Z n) p) ==>
          !e N. {x | x IN p_space p /\ e < max_fn_seq (\i. abs o Z i) N x} IN events p
Proof
    rw [prob_space_def, p_space_def, events_def, real_random_variable]
 >> Q.ABBREV_TAC ‘f = max_fn_seq (\i. abs o Z i) N’
 >> ‘{x | x IN m_space p /\ e < f x} = {x | e < f x} INTER m_space p’ by SET_TAC []
 >> POP_ORW
 >> Suff ‘f IN measurable (m_space p,measurable_sets p) Borel’
 >- (METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE, measure_space_def])
 >> Q.UNABBREV_TAC ‘f’
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX_FN_SEQ >> rw []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS' >> rw []
QED

Theorem Kolmogorov_maximal_inequality_1 :
    !p X Z.
       prob_space p /\ (!n. real_random_variable (X n) p) /\
       indep_vars p X (\n. Borel) UNIV /\
      (!n. finite_second_moments p (X n)) /\ (!n. expectation p (X n) = 0) /\
      (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count (SUC n)))
   ==> !e N. 0 < e /\ e <> PosInf ==>
             prob p {x | x IN p_space p /\ e < max_fn_seq (\i. abs o Z i) N x}
          <= variance p (Z N) / e pow 2
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> qx_genl_tac [‘E’, ‘N’] >> STRIP_TAC
 >> ‘E <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> ‘?e. 0 < e /\ E = Normal e’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW
 >> rw [extreal_pow_def]
 >> ‘measure_space p’ by PROVE_TAC [prob_space_def] (* frequently needed *)
 >> ‘!n. integrable p (X n)’ by PROVE_TAC [finite_second_moments_imp_integrable]
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘real_random_variable (Z n) p <=>
           real_random_variable (\x. SIGMA (\i. X i x) (count (SUC n))) p’
     >- (MATCH_MP_TAC real_random_variable_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC real_random_variable_sum >> rw [])
 >> DISCH_TAC
 (* event A and its properties *)
 >> Q.ABBREV_TAC ‘A = {x | x IN p_space p /\ Normal e < max_fn_seq (\i. abs o Z i) N x}’
 >> ‘A IN events p’ by METIS_TAC [events_max_fn_seq]
 >> Know ‘!x. x IN A ==> ?d. d <= N /\ Normal e < abs (Z d x)’
 >- (rw [Abbr ‘A’, GSPECIFICATION] \\
     fs [lt_max_fn_seq, o_DEF] \\
     Q.EXISTS_TAC ‘i’ >> art [] >> METIS_TAC [])
 >> DISCH_TAC
 (* Define v as the "first time" that the indicated maximum exceeds ‘e’ *)
 >> Q.ABBREV_TAC ‘v = \x. LEAST j. j <= N /\ Normal e < abs (Z j x)’
 (* properties of ‘v’ relative to ‘A’ *)
 >> Know ‘!x. x IN A ==> v x <= N’
 >- (rpt STRIP_TAC \\
    ‘?d. d <= N /\ Normal e < abs (Z d x)’ by METIS_TAC [] \\
     rw [Abbr ‘v’, GSPECIFICATION] \\
     LEAST_ELIM_TAC >> simp [])
 >> DISCH_TAC
 >> Know ‘!x. x IN A ==> Normal e < abs (Z (v x) x) /\
                         !i. i < v x ==> abs (Z i x) <= Normal e’
 >- (rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rw [Abbr ‘v’] >> LEAST_ELIM_TAC >> simp [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘i < v x’ MP_TAC \\
       simp [Abbr ‘v’] >> LEAST_ELIM_TAC >> rw [extreal_lt_def] \\
      ‘i <= N’ by rw [] >> METIS_TAC [] ])
 >> DISCH_TAC
 (* define ‘a’ (partition of A), ‘a k’ is meaningful only when ‘k <= N’  *)
 >> Q.ABBREV_TAC ‘a = \k. {x | x IN A /\ v x = k}’
 (* special case: ‘a 0’ *)
 >> Know ‘a 0 = {x | x IN A /\ Normal e < abs (Z 0 x)}’
 >- (rw [Abbr ‘a’, Once EXTENSION] >> EQ_TAC >> rw [] >- METIS_TAC [] \\
     CCONTR_TAC >> ‘0 < v x’ by rw [] \\
     METIS_TAC [extreal_lt_def])
 >> DISCH_TAC
 >> Know ‘!k. 0 < k ==>
              a k = {x | x IN A /\ max_fn_seq (\i. abs o Z i) (PRE k) x <= Normal e /\
                         Normal e < abs (Z k x)}’
 >- (rw [Abbr ‘a’, Once EXTENSION] >> EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rw [max_fn_seq_le, o_DEF],
       (* goal 2 (of 3) *)
       METIS_TAC [],
       (* goal 3 (of 3) *)
       CCONTR_TAC >> ‘v x < k \/ k < v x’ by rw [] >| (* 2 subgoals *)
       [ (* goal 3.1 (of 2) *)
         Q.PAT_X_ASSUM ‘max_fn_seq (\i. abs o Z i) (PRE k) x <= Normal e’ MP_TAC \\
         rw [lt_max_fn_seq, o_DEF, GSYM extreal_lt_def] \\
         Q.EXISTS_TAC ‘v x’ >> rw [],
         (* goal 3.2 (of 2) *)
         METIS_TAC [let_antisym] ] ])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!k. a k IN events p’
 >- (Q.X_GEN_TAC ‘k’ \\
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                           real_random_variable] \\
     Cases_on ‘k’
     >- (Q.PAT_X_ASSUM ‘a 0 = _’ (ONCE_REWRITE_TAC o wrap) \\
        ‘{x | x IN A /\ Normal e < abs (Z 0 x)} =
          A INTER ({x | Normal e < abs (Z 0 x)} INTER m_space p)’ by ASM_SET_TAC [] \\
         POP_ORW \\
         MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
         Q.ABBREV_TAC ‘f = \x. abs (Z 0 x)’ >> simp [] \\
         Suff ‘f IN measurable (m_space p,measurable_sets p) Borel’
         >- METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE, measure_space_def] \\
         Q.UNABBREV_TAC ‘f’ \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS >> BETA_TAC \\
         Q.EXISTS_TAC ‘Z 0’ >> rw []) \\
     Q.PAT_X_ASSUM ‘!k. 0 < k ==> _’
       (fn th => ONCE_REWRITE_TAC [MATCH_MP th (DECIDE “0 < SUC n”)]) \\
    ‘PRE (SUC n) = n’ by rw [] >> POP_ORW \\
     Q.ABBREV_TAC ‘f = max_fn_seq (\i. abs o Z i) n’ \\
     Q.ABBREV_TAC ‘g = abs o Z (SUC n)’ \\
    ‘!x. abs (Z (SUC n) x) = g x’ by simp [Abbr ‘g’] >> POP_ORW \\
    ‘A SUBSET m_space p’ by PROVE_TAC [MEASURE_SPACE_SUBSET_MSPACE] \\
    ‘{x | x IN A /\ f x <= Normal e /\ Normal e < g x} = A INTER
          (({x | f x <= Normal e} INTER m_space p) INTER
          ({x | Normal e < g x} INTER m_space p))’ by ASM_SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
     MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
     Suff ‘f IN measurable (m_space p,measurable_sets p) Borel /\
           g IN measurable (m_space p,measurable_sets p) Borel’
     >- (METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE, measure_space_def]) \\
     qunabbrevl_tac [‘f’, ‘g’] \\
     ‘!i. (abs o Z i) IN measurable (m_space p,measurable_sets p) Borel’
        by METIS_TAC [IN_MEASURABLE_BOREL_ABS', measure_space_def] >> art [] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX_FN_SEQ >> rw [])
 >> DISCH_TAC
 >> ‘!i j. i <> j ==> DISJOINT (a i) (a j)’
       by (rw [Abbr ‘a’, DISJOINT_ALT])
 (* The range ‘count (SUC n)’ indicates from a(0) to a(N) *)
 >> Know ‘unint A = BIGUNION (IMAGE a (count (SUC N)))’
 >- (rw [markerTheory.unint_def, Once EXTENSION, IN_BIGUNION_IMAGE] \\
     reverse EQ_TAC (* easy goal first *)
     >- (DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ MP_TAC) \\
         rw [Abbr ‘a’]) \\
     DISCH_TAC >> Q.EXISTS_TAC ‘v x’ \\
     CONJ_TAC >- rw [GSYM LESS_EQ_IFF_LESS_SUC] \\
    ‘v x = 0 \/ 0 < v x’ by rw [] >- (rw [] >> METIS_TAC []) \\
     Q.PAT_X_ASSUM ‘!k. 0 < k ==> a k = _’
       (fn th => ONCE_REWRITE_TAC [MATCH_MP th (ASSUME “(0 :num) < v x”)]) \\
     rw [max_fn_seq_le, o_DEF])
 >> DISCH_TAC
 (* preliminary rewriting on the goal *)
 >> Know ‘prob p A <= variance p (Z N) / Normal (e pow 2) <=>
          prob p A * Normal (e pow 2) <= variance p (Z N)’
 >- (MATCH_MP_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ] le_rdiv) \\
     rw [REAL_POW_POS] >> PROVE_TAC [REAL_LT_IMP_NE])
 >> Rewr'
 >> Know ‘variance p (Z N) = expectation p (\x. Z N x pow 2)’
 >- (REWRITE_TAC [variance_alt] \\
     MATCH_MP_TAC expectation_cong >> rw [] \\
     Suff ‘expectation p (Z N) = 0’ >- rw [] \\
     Know ‘expectation p (Z N) =
           expectation p (\x. SIGMA (\i. X i x) (count (SUC N)))’
     >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
     Know ‘expectation p (\x. SIGMA (\i. X i x) (count (SUC N))) =
           SIGMA (\i. expectation p (X i)) (count (SUC N))’
     >- (MATCH_MP_TAC expectation_sum >> rw []) >> Rewr' \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 >> rw [])
 >> Know ‘expectation p (\x. Z N x pow 2) = pos_fn_integral p (\x. Z N x pow 2)’
 >- (REWRITE_TAC [expectation_def] \\
     MATCH_MP_TAC integral_pos_fn >> rw [le_pow2])
 >> NTAC 2 Rewr'
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘pos_fn_integral p (\x. Z N x pow 2 * indicator_fn A x)’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC pos_fn_integral_mono \\
     RW_TAC std_ss [] >- (MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS]) \\
     Cases_on ‘x IN A’ >> rw [indicator_fn_def, le_pow2])
 (* stage work *)
 >> Q.ABBREV_TAC ‘D = \i x. Z N x - Z i x’
 >> Know ‘!n. real_random_variable (D n) p’
 >- (RW_TAC std_ss [Abbr ‘D’] \\
     MATCH_MP_TAC real_random_variable_sub >> art [])
 >> DISCH_TAC
 (* applying sub_add2 *)
 >> Know ‘!i x. x IN m_space p ==> Z N x = Z i x + D i x’
 >- (rpt STRIP_TAC \\
     SIMP_TAC std_ss [Abbr ‘D’, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC sub_add2 \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (Z n) p’
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable_def, p_space_def])) \\
     PROVE_TAC [])
 >> DISCH_TAC
 (* applying add_pow2 *)
 >> Know ‘!i x. x IN m_space p ==>
                0 <= Z i x pow 2 + D i x pow 2 + 2 * (Z i x * D i x)’
 >- (RW_TAC std_ss [mul_assoc] \\
     Suff ‘Z i x pow 2 + D i x pow 2 + 2 * Z i x * D i x =
           (Z i x + D i x) pow 2’ >- (Rewr' >> REWRITE_TAC [le_pow2]) \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC add_pow2 \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (Z n) p’
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable_def, p_space_def])) \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (D n) p’
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable_def, p_space_def])) \\
     PROVE_TAC [])
 >> DISCH_TAC
 (* applying pos_fn_integral_disjoint_sets_sum *)
 >> Know ‘pos_fn_integral p (\x. Z N x pow 2 * indicator_fn A x) =
          SIGMA (\i. pos_fn_integral p (\x. Z N x pow 2 * indicator_fn (a i) x))
                (count (SUC N))’
 >- (Q.PAT_X_ASSUM ‘unint A = BIGUNION (IMAGE a (count (SUC N)))’
       (ONCE_REWRITE_TAC o wrap o REWRITE_RULE [markerTheory.unint_def]) \\
     HO_MATCH_MP_TAC pos_fn_integral_disjoint_sets_sum \\
     fs [prob_space_def, le_pow2, events_def, p_space_def, real_random_variable] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POW >> rw [])
 (* change all ‘pos_fn_integral’ to ‘integral’ *)
 >> Know ‘!i. pos_fn_integral p (\x. Z N x pow 2 * indicator_fn (a i) x) =
                     integral p (\x. Z N x pow 2 * indicator_fn (a i) x)’
 >- (Q.X_GEN_TAC ‘i’ >> ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     HO_MATCH_MP_TAC integral_pos_fn >> rw [] \\
     MATCH_MP_TAC le_mul >> SIMP_TAC std_ss [le_pow2, INDICATOR_FN_POS])
 >> Rewr'
 >> Know ‘!i. integral p (\x. Z N x pow 2 * indicator_fn (a i) x) =
              integral p (\x. (Z i x + D i x) pow 2 * indicator_fn (a i) x)’
 >- (Q.X_GEN_TAC ‘i’ >> MATCH_MP_TAC integral_cong >> rw [] \\
     Suff ‘Z N x = Z i x + D i x’ >- Rewr \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> Rewr'
 >> Know ‘!i. integral p (\x. (Z i x + D i x) pow 2 * indicator_fn (a i) x) =
              integral p (\x. (Z i x pow 2 + D i x pow 2 + 2 * (Z i x * D i x)) *
                               indicator_fn (a i) x)’
 >- (Q.X_GEN_TAC ‘i’ >> MATCH_MP_TAC integral_cong >> rw [] \\
     Suff ‘(Z i x + D i x) pow 2 =
            Z i x pow 2 + D i x pow 2 + 2 * (Z i x * D i x)’ >- Rewr \\
     REWRITE_TAC [mul_assoc] \\
     MATCH_MP_TAC add_pow2 \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (Z n) p’
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable_def, p_space_def])) \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (D n) p’
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable_def, p_space_def])) \\
     PROVE_TAC [])
 >> Rewr'
 >> Know ‘!i. integral p (\x. (Z i x pow 2 + D i x pow 2 + 2 * (Z i x * D i x)) *
                              indicator_fn (a i) x) =
              integral p (\x. (Z i x pow 2 + D i x pow 2) * indicator_fn (a i) x +
                              (2 * (Z i x * D i x * indicator_fn (a i) x)))’
 >- (Q.X_GEN_TAC ‘i’ >> HO_MATCH_MP_TAC integral_cong >> rw [] \\
     Cases_on ‘x IN a i’ (* 2 subgoals, same tactics *) \\
     POP_ASSUM MP_TAC \\
     SIMP_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, add_rzero, le_refl])
 >> Rewr'
 >> Know ‘!i x. (Z i x pow 2 + D i x pow 2) * indicator_fn (a i) x =
                 Z i x pow 2 * indicator_fn (a i) x +
                 D i x pow 2 * indicator_fn (a i) x’
 >- (rpt GEN_TAC >> MATCH_MP_TAC add_rdistrib \\
     DISJ1_TAC >> SIMP_TAC std_ss [le_pow2])
 >> Rewr'
 (* applying finite_second_moments_sum and *_sub *)
 >> Know ‘!n. finite_second_moments p (Z n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘finite_second_moments p (Z n) <=>
           finite_second_moments p (\x. SIGMA (\i. X i x) (count (SUC n)))’
     >- (MATCH_MP_TAC finite_second_moments_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC finite_second_moments_sum >> rw [])
 >> DISCH_TAC
 >> Know ‘!n. finite_second_moments p (D n)’
 >- (RW_TAC std_ss [Abbr ‘D’] \\
     MATCH_MP_TAC finite_second_moments_sub >> art [])
 >> DISCH_TAC
 >> ‘!n. integrable p (D n)’ by METIS_TAC [finite_second_moments_imp_integrable]
 (* applying finite_second_moments_imp_integrable_mul *)
 >> Know ‘!i. integrable p (\x. Z i x * D i x)’
 >- (Q.X_GEN_TAC ‘i’ \\
     MATCH_MP_TAC finite_second_moments_imp_integrable_mul >> art [])
 >> DISCH_TAC
 >> Know ‘!i. integrable p (\x. Z i x * D i x * indicator_fn (a i) x)’
 >- (Q.X_GEN_TAC ‘i’ \\
     HO_MATCH_MP_TAC integrable_mul_indicator \\
     FULL_SIMP_TAC std_ss [prob_space_def, events_def])
 >> DISCH_TAC
 >> Know ‘(!i. integrable p (\x. Z i x pow 2 * indicator_fn (a i) x)) /\
          (!i. integrable p (\x. D i x pow 2 * indicator_fn (a i) x))’
 >- (CONJ_TAC (* 2 subgoals, same tactics *) \\
     ( Q.X_GEN_TAC ‘i’ \\
       HO_MATCH_MP_TAC integrable_mul_indicator \\
       CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
       CONJ_TAC >- FULL_SIMP_TAC std_ss [events_def] \\
       METIS_TAC [finite_second_moments_eq_integrable_square] ))
 >> STRIP_TAC
 (* a temporary property, to be deleted soon *)
 >> Know ‘!i. integrable p (\x. 2 * (Z i x * D i x * indicator_fn (a i) x))’
 >- (Q.X_GEN_TAC ‘i’ \\
     REWRITE_TAC [extreal_of_num_def] \\
     HO_MATCH_MP_TAC integrable_cmul \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> DISCH_TAC
 (* applying integral_add3 *)
 >> Know ‘!i. integral p (\x. Z i x pow 2 * indicator_fn (a i) x +
                              D i x pow 2 * indicator_fn (a i) x +
                              2 * (Z i x * D i x * indicator_fn (a i) x)) =
              integral p (\x. Z i x pow 2 * indicator_fn (a i) x) +
              integral p (\x. D i x pow 2 * indicator_fn (a i) x) +
              integral p (\x. 2 * (Z i x * D i x * indicator_fn (a i) x))’
 >- (Q.X_GEN_TAC ‘i’ \\
     HO_MATCH_MP_TAC integral_add3 >> rw [])
 >> Rewr'
 >> Know ‘!i. integral p (\x. 2 * (Z i x * D i x * indicator_fn (a i) x)) =
              2 * integral p (\x. Z i x * D i x * indicator_fn (a i) x)’
 >- (Q.X_GEN_TAC ‘i’ \\
     REWRITE_TAC [extreal_of_num_def] \\
     HO_MATCH_MP_TAC integral_cmul >> rw [])
 >> Rewr'
 >> POP_ASSUM K_TAC (* !i. integrable p (\x. 2 * ...) *)
 (* preparing for indep_vars_expectation *)
 >> Q.ABBREV_TAC ‘W = \i x. Z i x * indicator_fn (a i) x’
 >> ‘!i x. Z i x * D i x * indicator_fn (a i) x =
           W i x * D i x’ by PROVE_TAC [mul_comm, mul_assoc]
 >> Q.PAT_X_ASSUM ‘!i. integrable p (\x. Z i x * D i x * indicator_fn (a i) x)’ MP_TAC
 >> POP_ORW
 >> DISCH_TAC (* !i. integrable p (\x. W i x * D i x) *)
 >> Know ‘!n. real_random_variable (W n) p’
 >- (Q.X_GEN_TAC ‘n’ >> Q.UNABBREV_TAC ‘W’ >> BETA_TAC \\
     MATCH_MP_TAC real_random_variable_mul_indicator >> art [])
 >> DISCH_TAC
 >> Know ‘!n. integrable p (W n)’
 >- (Q.X_GEN_TAC ‘n’ >> Q.UNABBREV_TAC ‘W’ >> BETA_TAC \\
     MATCH_MP_TAC integrable_mul_indicator \\
     FULL_SIMP_TAC std_ss [prob_space_def, events_def] \\
     MATCH_MP_TAC finite_second_moments_imp_integrable \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> DISCH_TAC
 (* applying indep_vars_expectation *)
 >> Know ‘!i. i <= N ==> expectation p (\x. W i x * D i x) =
                         expectation p (W i) * expectation p (D i)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC indep_vars_expectation >> art [] \\
     (* TODO: ‘indep_vars p (W i) (D i) Borel Borel’ *)
     cheat)
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!n. n <= N ==> expectation p (D n) = 0’
 >- (Q.X_GEN_TAC ‘n’ \\
     RW_TAC std_ss [Abbr ‘D’] \\
  (* choose J such that ‘count (SUC N) = J UNION (count (SUC n))’ *)
     Q.ABBREV_TAC ‘J = {i | n < i /\ i <= N}’ \\
    ‘J SUBSET count (SUC N)’ by rw [Abbr ‘J’, SUBSET_DEF] \\
    ‘FINITE J’ by PROVE_TAC [SUBSET_FINITE, FINITE_COUNT] \\
     Know ‘expectation p (\x. Z N x - Z n x) =
           expectation p (\x. SIGMA (\i. X i x) J)’
     >- (MATCH_MP_TAC expectation_cong >> art [] \\
         BETA_TAC >> rpt STRIP_TAC \\
         Know ‘Z N x - Z n x = SIGMA (\i. X i x) J <=>
               Z N x = SIGMA (\i. X i x) J + Z n x’
         >- (MATCH_MP_TAC eq_sub_radd \\
             Q.PAT_X_ASSUM ‘!n. real_random_variable (Z n) p’ MP_TAC \\
             rw [real_random_variable_def]) >> Rewr' \\
      (* applying EXTREAL_SUM_IMAGE_DISJOINT_UNION *)
         ASM_SIMP_TAC std_ss [] \\
        ‘count (SUC N) = J UNION (count (SUC n))’ by rw [Abbr ‘J’, Once EXTENSION] \\
         POP_ORW >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’ MP_TAC \\
         rw [Abbr ‘J’, real_random_variable_def, DISJOINT_ALT]) >> Rewr' \\
  (* applying expectation_sum *)
     Know ‘expectation p (\x. SIGMA (\i. X i x) J) = SIGMA (\i. expectation p (X i)) J’
     >- (MATCH_MP_TAC expectation_sum >> rw [Abbr ‘J’]) >> Rewr' \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 >> rw [])
 >> DISCH_TAC
 >> Know ‘!i. i <= N ==> expectation p (\x. W i x * D i x) = 0’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i <= N ==> expectation p (\x. W i x * D i x) = _’
       (fn th => ONCE_REWRITE_TAC [MATCH_MP th (ASSUME “i <= (N :num)”)]) \\
     Q.PAT_X_ASSUM ‘!i. i <= N ==> expectation p (D i) = 0’
       (fn th => ONCE_REWRITE_TAC [MATCH_MP th (ASSUME “i <= (N :num)”)]) \\
     REWRITE_TAC [mul_rzero])
 (* cleanup used assumptions *)
 >> Q.PAT_X_ASSUM ‘!i. i <= N ==> expectation p (\x. W i x * D i x) = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘!i. i <= N ==> expectation p (D i) = 0’               K_TAC
 >> DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [expectation_def]))
 (* stage work *)
 >> Know ‘SIGMA
            (\i. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) +
                 integral p (\x. D i x pow 2 * indicator_fn (a i) x) +
                 2 * integral p (\x. W i x * D i x)) (count (SUC N)) =
          SIGMA
            (\i. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) +
                 integral p (\x. D i x pow 2 * indicator_fn (a i) x)) (count (SUC N))’
 >- (irule EXTREAL_SUM_IMAGE_EQ \\
     SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT, LT_SUC_LE] \\
    ‘!i. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) <> PosInf /\
         integral p (\x. Z i x pow 2 * indicator_fn (a i) x) <> NegInf’
       by METIS_TAC [integrable_finite_integral] \\
    ‘!i. integral p (\x. D i x pow 2 * indicator_fn (a i) x) <> PosInf /\
         integral p (\x. D i x pow 2 * indicator_fn (a i) x) <> NegInf’
       by METIS_TAC [integrable_finite_integral] \\
    ‘!i. integral p (\x. W i x * D i x) <> PosInf /\
         integral p (\x. W i x * D i x) <> NegInf’
       by METIS_TAC [integrable_finite_integral] \\
     reverse CONJ_TAC
     >- (DISJ2_TAC (* or DISJ1_TAC *) \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
        ‘?z. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) = Normal z’
            by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?d. integral p (\x. D i x pow 2 * indicator_fn (a i) x) = Normal d’
            by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?c. integral p (\x. W i x * D i x) = Normal c’
            by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_of_num_def, extreal_not_infty, extreal_add_def, extreal_mul_def]) \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. i <= N ==> integral p (\x. W i x * D i x) = 0’
       (fn th => ONCE_REWRITE_TAC [MATCH_MP th (ASSUME “i <= (N :num)”)]) \\
     REWRITE_TAC [mul_rzero, add_rzero])
 >> Rewr'
 (* rewrite the goal again! *)
 >> Rewr'
 (* now eliminate D *)
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC
     ‘SIGMA (\i. integral p (\x. Z i x pow 2 * indicator_fn (a i) x)) (count (SUC N))’
 >> reverse CONJ_TAC
 >- (irule EXTREAL_SUM_IMAGE_MONO \\
     SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT, LT_SUC_LE] \\
    ‘!i. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) <> PosInf /\
         integral p (\x. Z i x pow 2 * indicator_fn (a i) x) <> NegInf’
       by METIS_TAC [integrable_finite_integral] \\
    ‘!i. integral p (\x. D i x pow 2 * indicator_fn (a i) x) <> PosInf /\
         integral p (\x. D i x pow 2 * indicator_fn (a i) x) <> NegInf’
       by METIS_TAC [integrable_finite_integral] \\
     reverse CONJ_TAC
     >- (DISJ2_TAC (* or DISJ1_TAC *) \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
        ‘?z. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) = Normal z’
            by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?d. integral p (\x. D i x pow 2 * indicator_fn (a i) x) = Normal d’
            by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_not_infty, extreal_add_def]) \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC le_addr_imp \\
     MATCH_MP_TAC integral_pos >> BETA_TAC \\
     Q.PAT_X_ASSUM ‘measure_space p’ (REWRITE_TAC o wrap) \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS])
 (* applying PROB_FINITE_ADDITIVE *)
 >> Know ‘prob p A = SIGMA (prob p o a) (count (SUC N))’
 >- (MATCH_MP_TAC PROB_FINITE_ADDITIVE >> rw [] \\
     FULL_SIMP_TAC std_ss [markerTheory.unint_def])
 >> Rewr'
 (* apply mul_comm on LHS only *)
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm]
 (* applying EXTREAL_SUM_IMAGE_CMUL *)
 >> Know ‘Normal (e pow 2) * SIGMA (prob p o a) (count (SUC N)) =
          SIGMA (\x. Normal (e pow 2) * (prob p o a) x) (count (SUC N))’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     irule EXTREAL_SUM_IMAGE_CMUL \\
     SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT, LT_SUC_LE] \\
     DISJ1_TAC >> PROVE_TAC [PROB_FINITE])
 >> Rewr'
 (* applying EXTREAL_SUM_IMAGE_MONO *)
 >> irule EXTREAL_SUM_IMAGE_MONO
 >> SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT, LT_SUC_LE]
 >> reverse CONJ_TAC
 >- (DISJ1_TAC (* easier *) \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC le_mul >> rw [le_pow2, PROB_POSITIVE],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC integral_pos >> BETA_TAC \\
       Q.PAT_X_ASSUM ‘measure_space p’ (REWRITE_TAC o wrap) \\
       rpt STRIP_TAC \\
       MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS] ])
 >> Q.X_GEN_TAC ‘i’
 >> DISCH_TAC
 (* applying integral_cmul_indicator *)
 >> Know ‘Normal (e pow 2) * prob p (a i) =
          integral p (\x. Normal (e pow 2) * indicator_fn (a i) x)’
 >- (REWRITE_TAC [prob_def, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC integral_cmul_indicator \\
     Q.PAT_X_ASSUM ‘measure_space p’ (REWRITE_TAC o wrap) \\
     REWRITE_TAC [GSYM lt_infty] \\
     Q.PAT_ASSUM ‘!k. a k IN events p’
      (REWRITE_TAC o wrap o (REWRITE_RULE [events_def])) \\
     Suff ‘prob p (a i) <> PosInf’ >- REWRITE_TAC [prob_def] \\
     METIS_TAC [PROB_FINITE])
 >> Rewr'
 (* stage work *)
 >> MATCH_MP_TAC integral_mono >> rw []
 >- (MATCH_MP_TAC integrable_cmul >> art [] \\
     MATCH_MP_TAC integrable_indicator >> art [] \\
     Q.PAT_ASSUM ‘!k. a k IN events p’
       (REWRITE_TAC o wrap o (REWRITE_RULE [events_def])) \\
     REWRITE_TAC [GSYM lt_infty] \\
     Suff ‘prob p (a i) <> PosInf’ >- REWRITE_TAC [prob_def] \\
     METIS_TAC [PROB_FINITE])
 (* finall stage *)
 >> reverse (Cases_on ‘x IN a i’)
 >- (‘indicator_fn (a i) x = 0’ by METIS_TAC [indicator_fn_def] >> simp [])
 (* ‘x IN a i’ from now on *)
 >> ‘indicator_fn (a i) x = 1’ by METIS_TAC [indicator_fn_def]
 >> simp []
 >> ‘Normal (e pow 2) = (Normal e) pow 2’ by rw [extreal_pow_def]
 >> POP_ORW
 >> ‘Z i x pow 2 = abs (Z i x) pow 2’ by rw [abs_pow2]
 >> POP_ORW
 >> Know ‘Normal e pow 2 <= abs (Z i x) pow 2 <=> Normal e <= abs (Z i x)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC pow2_le_eq >> rw [extreal_of_num_def, abs_pos] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> Rewr'
 >> MATCH_MP_TAC lt_imp_le
 >> Q.PAT_X_ASSUM ‘x IN a i’ MP_TAC
 >> ‘i = 0 \/ 0 < i’ by rw []
 >> rw []
QED

(* Kolmogorov's two remarkable inequalities, the second one.

   This is Theorem 5.3.2 [2, p.123], see also [5, p.7] (Kolmogorov’s Inequalities (b))

   NOTE: ‘abs (X n x - expectation p (X n)) <= A’ implies ‘finite_second_moments p (X n)’,
         but ‘integrable p (X n)’ must be put first to make sure ‘expectation p (X n)’ is
         specified and finite (but may not be zero).
 *)
Theorem Kolmogorov_maximal_inequality_2 :
    !p X Z A.
       prob_space p /\ (!n. real_random_variable (X n) p) /\
       indep_vars p X (\n. Borel) UNIV /\
      (!n. integrable p (X n)) /\ 0 < A /\ A <> PosInf /\
      (!n x. x IN p_space p ==> abs (X n x - expectation p (X n)) <= A) /\
      (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count (SUC n)))
   ==> !e N. 0 < e /\ e <> PosInf /\ 0 < variance p (Z N) ==>
             prob p {x | x IN p_space p /\ max_fn_seq (\i. abs o Z i) N x <= e}
          <= (2 * A + 4 * e) pow 2 / variance p (Z N)
Proof
    rpt STRIP_TAC
 >> cheat
QED

(* This is Exercise 5.3 (3) [2, p.128], a companion of Theorem 5.3.2 under the joint
   hypotheses in Theorem 5.3.1 and 5.3.2. This is Kolmogorov’s Inequalities (b) of [5, p.7].

   A better estimate ‘(A + e) pow 2’ than ‘(2 * A + 4 * e) pow 2’ has been obtained here.

  "Every serious student of probability theory should read:

   A. N. Kolmogoroff, Uber die Summen durch den Zufall bestimmten unabhangiger
   Grossen, Math. Annalen 99 (1928), 309-319; Bermerkungen, 102 (1929), 484-488. [8]

   This contains Theorems 5.3.1 to 5.3.3 as well as the original version of Theorem 5.2.3."

  -- Kai Lai Chung, "A Course in Probability Theory." [2, p.149]
 *)
Theorem Kolmogorov_maximal_inequality_3 :
    !p X A Z.
       prob_space p /\ (!n. real_random_variable (X n) p) /\
       indep_vars p X (\n. Borel) UNIV /\
      (!n. expectation p (X n) = 0) /\ A <> PosInf /\
      (!n x. x IN p_space p ==> abs (X n x) <= A) /\
      (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count (SUC n)))
   ==> !e N. 0 < e /\ e <> PosInf /\ 0 < variance p (Z N) ==>
             prob p {x | x IN p_space p /\ max_fn_seq (\i. abs o Z i) N x <= e}
          <= (A + e) pow 2 / variance p (Z N)
Proof
    cheat
QED

(* Or, in another equivalent form, the above theorem provides a lower bound for

   prob p {x | x IN p_space p /\ e < max_fn_seq (\i. abs o Z i) N x}

   while Kolmogorov_maximal_inequality_1 provides a upper bound: variance(Z) / e pow 2

   NOTE: when ‘variance p (Z N) = 0’, using only Kolmogorov_maximal_inequality we
         get ‘prob p E <= 0’ thus ‘= 0’.
 *)
Theorem Kolmogorov_maximal_inequality :
    !p X A Z.
       prob_space p /\ (!n. real_random_variable (X n) p) /\
       indep_vars p X (\n. Borel) UNIV /\
      (!n. expectation p (X n) = 0) /\ 0 < A /\ A <> PosInf /\
      (!n x. x IN p_space p ==> abs (X n x) <= A) /\
      (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count (SUC n)))
   ==> !e N. 0 < e /\ e <> PosInf /\ 0 < variance p (Z N) ==>
             prob p {x | x IN p_space p /\ e < max_fn_seq (\i. abs o Z i) N x} IN
             {r | 1 - (A + e) pow 2 / variance p (Z N) <= r /\
                  r <= variance p (Z N) / e pow 2}
Proof
    rpt STRIP_TAC >> simp []
 >> ‘A <> NegInf’ by METIS_TAC [pos_not_neginf, lt_imp_le]
 >> Know ‘!n. finite_second_moments p (X n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC bounded_imp_finite_second_moments \\
    ‘?r. A = Normal r’ by METIS_TAC [extreal_cases] \\
     fs [real_random_variable_def] >> Q.EXISTS_TAC ‘r’ >> rw [])
 >> DISCH_TAC
 >> reverse CONJ_TAC
 >- (irule Kolmogorov_maximal_inequality_1 >> art [] \\
     Q.EXISTS_TAC ‘X’ >> simp [])
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘real_random_variable (Z n) p <=>
           real_random_variable (\x. SIGMA (\i. X i x) (count (SUC n))) p’
     >- (MATCH_MP_TAC real_random_variable_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC real_random_variable_sum >> rw [])
 >> DISCH_TAC
 >> Know ‘!n. finite_second_moments p (Z n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘finite_second_moments p (Z n) <=>
           finite_second_moments p (\x. SIGMA (\i. X i x) (count (SUC n)))’
     >- (MATCH_MP_TAC finite_second_moments_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC finite_second_moments_sum >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘E = {x | x IN p_space p /\ e < max_fn_seq (\i. abs o Z i) N x}’
 >> ‘E IN events p’ by METIS_TAC [events_max_fn_seq]
 >> ‘variance p (Z N) <> PosInf’
      by METIS_TAC [finite_second_moments_eq_finite_variance,lt_infty]
 >> ‘variance p (Z N) <> NegInf’
      by METIS_TAC [pos_not_neginf, variance_pos]
 (* applying sub_le_switch2 *)
 >> Know ‘1 - (A + e) pow 2 / variance p (Z N) <= prob p E <=>
          1 - prob p E <= (A + e) pow 2 / variance p (Z N)’
 >- (MATCH_MP_TAC sub_le_switch2 \\
     rw [extreal_of_num_def, extreal_not_infty]
     >- (MATCH_MP_TAC pos_not_neginf \\
        ‘?r. 0 < r /\ variance p (Z N) = Normal r’
           by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
         MATCH_MP_TAC le_div >> rw [le_pow2]) \\
    ‘?a. A = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘e <> NegInf’ by METIS_TAC [pos_not_neginf, lt_imp_le] \\
    ‘?b. e = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     simp [extreal_add_def, extreal_pow_def] \\
     Suff ‘variance p (Z N) <> 0’ >- METIS_TAC [div_not_infty] \\
     PROVE_TAC [lt_imp_ne])
 >> Rewr'
 >> Know ‘1 - prob p E = prob p (p_space p DIFF E)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC PROB_COMPL >> art [])
 >> Rewr'
 >> Suff ‘p_space p DIFF E = {x | x IN p_space p /\ max_fn_seq (\i. abs o Z i) N x <= e}’
 >- (Rewr' >> irule Kolmogorov_maximal_inequality_3 >> art [] \\
     Q.EXISTS_TAC ‘X’ >> rw [])
 >> rw [Once EXTENSION, Abbr ‘E’, extreal_lt_def]
 >> METIS_TAC []
QED

val _ = export_theory ();
val _ = html_theory "convergence";
