(* ------------------------------------------------------------------------- *)
(*  Convergence of series (Chapter 5.3 of [2, p.121])                        *)
(*                                                                           *)
(* Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2022)                 *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory pred_setTheory pred_setLib logrootTheory
     numLib hurdUtils;

open realTheory realLib seqTheory transcTheory real_sigmaTheory iterateTheory
     real_topologyTheory;

open util_probTheory sigma_algebraTheory extrealTheory measureTheory
     borelTheory lebesgueTheory martingaleTheory probabilityTheory;

(* local theories *)
open stochastic_processTheory;

(* val _ = intLib.deprecate_int(); *)

val _ = new_theory "convergence";

fun PRINT_TAC s gl = (print ("** " ^ s ^ "\n"); ALL_TAC gl)
val set_ss = std_ss ++ PRED_SET_ss;

val _ = hide "S";
val _ = hide "W";

val max_fn_seq_tm = “max_fn_seq (\i. abs o Z i) (SUC n) x”;
val variance_tm   = “variance p (Z (SUC n))”;

Theorem real_random_variable_mul_indicator :
    !p E X. prob_space p /\ E IN events p /\ real_random_variable X p ==>
            real_random_variable (\x. X x * indicator_fn E x) p
Proof
    RW_TAC std_ss [real_random_variable]
 >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     fs [prob_space_def, measure_space_def, p_space_def, events_def])
 >> ‘?r. 0 <= r /\ r <= 1 /\ indicator_fn E x = Normal r’
        by METIS_TAC [indicator_fn_normal] >> POP_ORW
 >> ONCE_REWRITE_TAC [mul_comm]
 >> METIS_TAC [mul_not_infty]
QED

(* Kolmogorov's two remarkable inequalities, the first one.

   This is Theorem 5.3.1 [2, p.121], see also [5, p.7]

   Remark. If we replace the ‘max_fn_seq (\i. abs o Z i) (SUC n) x’ in the formula
   by ‘abs (Z (SUC n))’, this becomes a simple case of Chebyshev's inequality, of
   which it is thus an essential improvement.
 *)
Theorem Kolmogorov_maximal_inequality_1_lemma[local] :
    !p X. prob_space p /\ indep_vars p X (\n. Borel) UNIV /\
         (!n. real_random_variable (X n) p) /\
         (!n. finite_second_moments p (X n)) /\
         (!n. expectation p (X n) = 0)
      ==> !e n. 0 < e ==>
                let Z n x = SIGMA (\i. X i x) (count n) in
                  prob p {x | x IN p_space p /\ Normal e < ^max_fn_seq_tm} <=
                  ^variance_tm / Normal (e pow 2)
Proof
    RW_TAC std_ss [] (* this also converts ‘let’ to Abbrev *)
 >> ‘measure_space p’ by PROVE_TAC [prob_space_def]
 >> ‘!n. real_random_variable (Z n) p’
      by (rw [Abbr ‘Z’] >> MATCH_MP_TAC real_random_variable_sum >> rw [])
 >> ‘!x. Z 0 x = 0’ by (rw [Abbr ‘Z’, EXTREAL_SUM_IMAGE_EMPTY])
 (* Event A and its properties *)
 >> Q.ABBREV_TAC
     ‘A = {x | x IN p_space p /\ Normal e < max_fn_seq (\i. abs o Z i) (SUC n) x}’
 >> Know ‘A IN events p’
 >- (FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                           real_random_variable, Abbr ‘A’] \\
     Q.ABBREV_TAC ‘f = max_fn_seq (\i. abs o Z i) (SUC n)’ \\
    ‘{x | x IN m_space p /\ Normal e < f x} = {x | Normal e < f x} INTER m_space p’
        by SET_TAC [] >> POP_ORW \\
     Suff ‘f IN measurable (m_space p,measurable_sets p) Borel’
     >- (METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) \\
     Q.UNABBREV_TAC ‘f’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX_FN_SEQ >> rw [] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS' >> rw [])
 >> DISCH_TAC
 >> Know ‘!x. x IN A ==> ?d. d <= n /\ Normal e < abs (Z (SUC d) x)’
 >- (rw [Abbr ‘A’, GSPECIFICATION] \\
     fs [lt_max_fn_seq, o_DEF] \\
     rename1 ‘j <= SUC n’ \\
     Cases_on ‘j = 0’ >- (gs [] >> fs [extreal_of_num_def, extreal_lt_eq] \\
                          PROVE_TAC [REAL_LT_ANTISYM]) \\
    ‘SUC (PRE j) = j’ by rw [] \\
     Q.EXISTS_TAC ‘PRE j’ >> rw [])
 >> DISCH_TAC
 (* Define v as the "first time" that the indicated maximum exceeds ‘e’ *)
 >> Q.ABBREV_TAC ‘v = \x. LEAST j. j <= n /\ Normal e < abs (Z (SUC j) x)’
 (* properties of ‘v’ w.r.t. ‘A’ *)
 >> Know ‘!x. x IN A ==> v x <= n’
 >- (rw [Abbr ‘A’, Abbr ‘v’, GSPECIFICATION] \\
     LEAST_ELIM_TAC >> simp [])
 >> DISCH_TAC
 >> Know ‘!x. x IN A ==> Normal e < abs (Z (SUC (v x)) x) /\
                        !i. i <= v x ==> abs (Z i x) <= Normal e’
 >- (Q.X_GEN_TAC ‘x’ >> simp [Abbr ‘A’, GSPECIFICATION] >> STRIP_TAC \\
     Q.UNABBREV_TAC ‘v’ >> BETA_TAC >> LEAST_ELIM_TAC >> simp [] \\
     Q.X_GEN_TAC ‘j’ >> rw [extreal_lt_def] >> fs [GSYM extreal_lt_def] \\
     Cases_on ‘i = 0’ >- (rw [] >> rw [extreal_of_num_def, extreal_le_eq] \\
                          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
    ‘PRE i <= n’ by rw [] \\
    ‘SUC (PRE i) = i’ by rw [] \\
     Q.PAT_X_ASSUM ‘!k. k < j ==> P’ (MP_TAC o (Q.SPEC ‘PRE i’)) >> rw [])
 >> DISCH_TAC
 (* define ‘a’ (partition of A), ‘a k’ is meaningful only when ‘k <= n’  *)
 >> Q.ABBREV_TAC ‘a = \k. {x | x IN A /\ v x = k}’
 >> Know ‘!k. a k = {x | x IN A /\ max_fn_seq (\i. abs o Z i) k x <= Normal e /\
                                   Normal e < max_fn_seq (\i. abs o Z i) (SUC k) x}’
 >- (rw [Abbr ‘a’, Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rw [max_fn_seq_le, o_DEF],
       (* goal 2 (of 3) *)
       rw [lt_max_fn_seq, o_DEF] \\
       Q.EXISTS_TAC ‘SUC (v x)’ >> rw [],
       (* goal 3 (of 3), ‘k <= n’ is not needed *)
       Q.PAT_X_ASSUM ‘!x. x IN A ==> Normal e < abs (Z (SUC (v x)) x) /\ P’ K_TAC \\
       Q.UNABBREV_TAC ‘v’ >> BETA_TAC >> LEAST_ELIM_TAC >> simp [] \\
       Q.X_GEN_TAC ‘j’ >> rw [extreal_lt_def] >> fs [GSYM extreal_lt_def] \\
       Q.PAT_X_ASSUM ‘max_fn_seq (\i. abs o Z i) k x <= Normal e’ MP_TAC \\
       Q.PAT_X_ASSUM ‘Normal e < max_fn_seq (\i. abs o Z i) (SUC k) x’ MP_TAC \\
       rw [max_fn_seq_le, lt_max_fn_seq, o_DEF] \\
       CCONTR_TAC >> ‘j < k \/ k < j’ by rw [] >| (* 2 subgoals *)
       [ (* goal 3.1 (of 2) *)
        ‘SUC j <= k’ by rw [] >> METIS_TAC [let_antisym],
         (* goal 3.2 (of 2) *)
        ‘SUC k <= j’ by rw [] >> ‘i <= j’ by rw [] \\
         Cases_on ‘i = 0’ >- (gs [] >> fs [extreal_of_num_def, extreal_lt_eq] \\
                              METIS_TAC [REAL_LT_ANTISYM]) \\
        ‘PRE i < j’ by rw [] \\
         Q.PAT_X_ASSUM ‘!m. m < j ==> abs (Z (SUC m) x) <= Normal e’
           (MP_TAC o (Q.SPEC ‘PRE i’)) \\
        ‘SUC (PRE i) = i’ by rw [] \\
         METIS_TAC [let_antisym] ] ])
 >> DISCH_TAC
 >> Know ‘!k. a k IN events p’
 >- (Q.X_GEN_TAC ‘k’ >> POP_ORW \\
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                           real_random_variable] \\
     Q.ABBREV_TAC ‘f = max_fn_seq (\i. abs o Z i) k’ \\
     Q.ABBREV_TAC ‘g = max_fn_seq (\i. abs o Z i) (SUC k)’ \\
    ‘A SUBSET m_space p’ by PROVE_TAC [MEASURE_SPACE_SUBSET_MSPACE] \\
    ‘{x | x IN A /\ f x <= Normal e /\ Normal e < g x} = A INTER
          (({x | f x <= Normal e} INTER m_space p) INTER
          ({x | Normal e < g x} INTER m_space p))’ by ASM_SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
     MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
     Suff ‘f IN measurable (m_space p,measurable_sets p) Borel /\
           g IN measurable (m_space p,measurable_sets p) Borel’
     >- (METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) \\
     qunabbrevl_tac [‘f’, ‘g’] \\
     ‘!i. (abs o Z i) IN measurable (m_space p,measurable_sets p) Borel’
        by METIS_TAC [IN_MEASURABLE_BOREL_ABS', measure_space_def] \\
     CONJ_TAC (* 2 subgoals, same tactics *) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX_FN_SEQ >> rw [])
 >> DISCH_TAC
 >> Know ‘!i j. i <> j ==> DISJOINT (a i) (a j)’
 >- (Q.PAT_X_ASSUM ‘!k. a k = _’ K_TAC (* to prevent ‘a’ from being wrongly written *) \\
     rw [Abbr ‘a’, DISJOINT_ALT])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘A = BIGUNION (IMAGE a (count (SUC n)))’
 >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
     reverse EQ_TAC (* easy goal first *)
     >- DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
     DISCH_TAC >> Q.EXISTS_TAC ‘v x’ \\
     rw [max_fn_seq_le, o_DEF, GSYM LESS_EQ_IFF_LESS_SUC] \\
     rw [lt_max_fn_seq, o_DEF] \\
     Q.EXISTS_TAC ‘SUC (v x)’ >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘D = \i x. Z n x - Z i x’
 >> Know ‘!n. real_random_variable (D n) p’
 >- (RW_TAC std_ss [Abbr ‘D’] \\
     MATCH_MP_TAC real_random_variable_sub >> art [])
 >> DISCH_TAC
 (* applying sub_add2 *)
 >> Know ‘!i x. x IN m_space p ==> Z n x = Z i x + D i x’
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
 >> Know ‘pos_fn_integral p (\x. Z n x pow 2 * indicator_fn A x) =
          SIGMA (\i. pos_fn_integral p (\x. Z n x pow 2 * indicator_fn (a i) x))
                (count (SUC n))’
 >- (Q.PAT_X_ASSUM ‘A = _’ (ONCE_REWRITE_TAC o wrap) \\
     HO_MATCH_MP_TAC pos_fn_integral_disjoint_sets_sum \\
     fs [prob_space_def, le_pow2, events_def, p_space_def, real_random_variable] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POW >> rw [])
 (* change all ‘pos_fn_integral’ to ‘integral’ *)
 >> Know ‘!i. pos_fn_integral p (\x. Z n x pow 2 * indicator_fn (a i) x) =
                     integral p (\x. Z n x pow 2 * indicator_fn (a i) x)’
 >- (Q.X_GEN_TAC ‘i’ >> ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     HO_MATCH_MP_TAC integral_pos_fn \\
     CONJ_TAC >- art [] (* measure_space p *) \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC le_mul >> SIMP_TAC std_ss [le_pow2, INDICATOR_FN_POS])
 >> Rewr'
 >> Know ‘!i. integral p (\x. Z n x pow 2 * indicator_fn (a i) x) =
              integral p (\x. (Z i x + D i x) pow 2 * indicator_fn (a i) x)’
 >- (Q.X_GEN_TAC ‘i’ \\
     MATCH_MP_TAC integral_cong >> BETA_TAC \\
     CONJ_TAC >- art [] (* measure_space p *) \\
     rpt STRIP_TAC \\
     Suff ‘Z n x = Z i x + D i x’ >- Rewr \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> Rewr'
 >> Know ‘!i. integral p (\x. (Z i x + D i x) pow 2 * indicator_fn (a i) x) =
              integral p (\x. (Z i x pow 2 + D i x pow 2 + 2 * (Z i x * D i x)) *
                               indicator_fn (a i) x)’
 >- (Q.X_GEN_TAC ‘i’ \\
     HO_MATCH_MP_TAC integral_cong \\
     CONJ_TAC >- art [] (* measure_space p *) \\
     rpt STRIP_TAC \\
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
 >- (Q.X_GEN_TAC ‘i’ \\
     HO_MATCH_MP_TAC integral_cong \\
     CONJ_TAC >- art [] (* measure_space p *) \\
     rpt STRIP_TAC \\
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
 >> Know ‘!i. finite_second_moments p (Z i)’
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     MATCH_MP_TAC finite_second_moments_sum >> rw [])
 >> DISCH_TAC
 >> Know ‘!i. finite_second_moments p (D i)’
 >- (RW_TAC std_ss [Abbr ‘D’] \\
     MATCH_MP_TAC finite_second_moments_sub >> art [])
 >> DISCH_TAC
 >> ‘!i. integrable p (D i)’ by METIS_TAC [finite_second_moments_imp_integrable]
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
 >> Know ‘!i. real_random_variable (W i) p’
 >- (Q.X_GEN_TAC ‘i’ >> Q.UNABBREV_TAC ‘W’ >> BETA_TAC \\
     MATCH_MP_TAC real_random_variable_mul_indicator >> art [])
 >> DISCH_TAC
 >> Know ‘!i. integrable p (W i)’
 >- (Q.X_GEN_TAC ‘i’ >> Q.UNABBREV_TAC ‘W’ >> BETA_TAC \\
     MATCH_MP_TAC integrable_mul_indicator \\
     FULL_SIMP_TAC std_ss [prob_space_def, events_def] \\
     MATCH_MP_TAC finite_second_moments_imp_integrable \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> DISCH_TAC
 (* applying indep_vars_expectation *)
 >> Know ‘!i. i <= n ==> expectation p (\x. W i x * D i x) =
                         expectation p (W i) * expectation p (D i)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC indep_vars_expectation >> art [] \\
     (* skip the hard part for now *)
     cheat)
 >> REWRITE_TAC [expectation_def]
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!i. i <= n ==> integral p (D i) = 0’
 >- (Q.X_GEN_TAC ‘m’ \\ (* don't use ‘i’ here as we're going to expand ‘Z’ to ‘X i n’ *)
     RW_TAC std_ss [Abbr ‘D’] \\
     Know ‘!x. x IN m_space p ==>
               Z n x = Z m x + SIGMA (\i. X i x) {i | m <= i /\ i < n}’
     >- (
         cheat) \\
     cheat
     )
 >> Know ‘SIGMA
            (\i. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) +
                 integral p (\x. D i x pow 2 * indicator_fn (a i) x) +
                 2 * integral p (\x. W i x * D i x)) (count (SUC n)) =
          SIGMA
            (\i. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) +
                 integral p (\x. D i x pow 2 * indicator_fn (a i) x) +
                 2 * integral p (W i) * integral p (D i)) (count (SUC n))’
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
    ‘!i. integral p (W i) <> PosInf /\ integral p (W i) <> NegInf’
       by METIS_TAC [integrable_finite_integral] \\
    ‘!i. integral p (D i) <> PosInf /\ integral p (D i) <> NegInf’
       by METIS_TAC [integrable_finite_integral] \\
     reverse CONJ_TAC
     >- (DISJ2_TAC (* or DISJ1_TAC *) \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
        ‘?z. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) = Normal z’
            by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?d. integral p (\x. D i x pow 2 * indicator_fn (a i) x) = Normal d’
            by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?wd. integral p (\x. W i x * D i x) = Normal wd’
            by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?w. integral p (W i) = Normal w’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?d'. integral p (D i) = Normal d'’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_of_num_def, extreal_not_infty, extreal_add_def, extreal_mul_def]) \\
    Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
    Know ‘integral p (\x. Z i x pow 2 * indicator_fn (a i) x) +
          integral p (\x. D i x pow 2 * indicator_fn (a i) x) +
          2 * integral p (\x. W i x * D i x) =
          integral p (\x. Z i x pow 2 * indicator_fn (a i) x) +
          integral p (\x. D i x pow 2 * indicator_fn (a i) x) +
          2 * integral p (W i) * integral p (D i) <=>
          2 * integral p (\x. W i x * D i x) = 2 * integral p (W i) * integral p (D i)’
    >- (MATCH_MP_TAC EXTREAL_EQ_LADD \\
       ‘?z. integral p (\x. Z i x pow 2 * indicator_fn (a i) x) = Normal z’
           by METIS_TAC [extreal_cases] >> POP_ORW \\
       ‘?d. integral p (\x. D i x pow 2 * indicator_fn (a i) x) = Normal d’
           by METIS_TAC [extreal_cases] >> POP_ORW \\
        rw [extreal_not_infty, extreal_add_def]) >> Rewr' \\
     REWRITE_TAC [GSYM mul_assoc] \\
     Know ‘2 * integral p (\x. W i x * D i x) = 2 * (integral p (W i) * integral p (D i)) <=>
           2 = 0 \/ integral p (\x. W i x * D i x) = integral p (W i) * integral p (D i)’
     >- (MATCH_MP_TAC mul_lcancel >> rw [extreal_of_num_def]) >> Rewr' \\
     DISJ2_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> Rewr'
 >> 
    cheat
QED

(* The final form without LET *)
Theorem Kolmogorov_maximal_inequality_1 :
  !p X Z. prob_space p /\ indep_vars p X (\n. Borel) UNIV /\
         (!n. real_random_variable (X n) p) /\
         (!n. finite_second_moments p (X n)) /\
         (!n. expectation p (X n) = 0) /\
         (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count n))
      ==> !e n. 0 < e ==>
                prob p {x | x IN p_space p /\ Normal e < max_fn_seq (\i. abs o Z i) n x}
             <= variance p (Z n) / Normal (e pow 2)
Proof
    rpt STRIP_TAC
 >> ‘!x. x IN p_space p ==> Z 0 x = 0’ by rw [EXTREAL_SUM_IMAGE_EMPTY]
 >> Cases_on ‘n’
 >- (rw [max_fn_seq_def] \\
     Know ‘{x | x IN p_space p /\ Normal e < abs (Z 0 x)} = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY, extreal_of_num_def, extreal_lt_eq] \\
         STRONG_DISJ_TAC \\
         rw [extreal_lt_def] \\
         rw [extreal_of_num_def, extreal_le_eq] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr' \\
     rw [PROB_EMPTY] \\
     MATCH_MP_TAC le_div >> rw [variance_pos] \\
     PROVE_TAC [REAL_LT_IMP_NE])
 >> MP_TAC (Q.SPECL [‘p’, ‘X’] Kolmogorov_maximal_inequality_1_lemma)
 >> SIMP_TAC std_ss [LET_DEF, o_DEF]
 >> Know ‘!n. variance p (\x. SIGMA (\i. X i x) (count (SUC n))) = variance p (Z (SUC n))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC variance_cong >> rw [])
 >> Rewr'
 >> Know ‘!e n. {x | x IN p_space p /\ Normal e <
                     max_fn_seq (\i x. abs (SIGMA (\i. X i x) (count i))) (SUC n) x} =
                {x | x IN p_space p /\ Normal e < max_fn_seq (\i x. abs (Z i x)) (SUC n) x}’
 >- (rw [Once EXTENSION] \\
     Suff ‘x IN p_space p ==>
            (max_fn_seq (\i y. abs (SIGMA (\i. X i y) (count i))) (SUC n) x =
             max_fn_seq (\i y. abs (Z i y)) (SUC n) x)’ >- METIS_TAC [] \\
     DISCH_TAC >> MATCH_MP_TAC max_fn_seq_cong >> rw [])
 >> Rewr'
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
QED

(* Kolmogorov's two remarkable inequalities, the second one.

   This is Theorem 5.3.2 [2, p.123], see also [5, p.7] (Kolmogorov’s Inequalities (b))

   NOTE: ‘abs (X n x - expectation p (X n)) <= A’ implies ‘finite_second_moments p (X n)’,
         but ‘integrable p (X n)’ must be put first to make sure ‘expectation p (X n)’ is
         specified and finite (but may not be zero).
 *)
Theorem Kolmogorov_maximal_inequality_2 :
    !p X A. prob_space p /\ indep_vars p X (\n. Borel) UNIV /\
           (!n. real_random_variable (X n) p) /\
           (!n. integrable p (X n)) /\
           (!n x. x IN p_space p ==> abs (X n x - expectation p (X n)) <= Normal A)
        ==> !e n. 0 < e ==>
                 (let Z n x = SIGMA (\i. X i x) (count n) in
                    prob p {x | x IN p_space p /\ ^max_fn_seq_tm <= Normal e} <=
                    Normal (2 * A + 4 * e) pow 2 / ^variance_tm)
Proof
    cheat
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
    !p X A. prob_space p /\ indep_vars p X (\n. Borel) UNIV /\
           (!n. real_random_variable (X n) p) /\
           (!n. expectation p (X n) = 0) /\
           (!n x. x IN p_space p ==> abs (X n x) <= Normal A)
        ==> !e n. 0 < e ==>
                 (let Z n x = SIGMA (\i. X i x) (count n) in
                    prob p {x | x IN p_space p /\ ^max_fn_seq_tm <= Normal e} <=
                    Normal (A + e) pow 2 / ^variance_tm)
Proof
    cheat
QED

(* Or, in another equivalent form, the above theorem provides a lower bound for

       ‘prob p {x | x IN p_space p /\ Normal e < ^max_fn_seq’}

   while Kolmogorov_maximal_inequality_1 provides a upper bound: ‘^variance / Normal e pow 2’
 *)
Theorem Kolmogorov_maximal_inequality_3' :
    !p X A. prob_space p /\ (!n. real_random_variable (X n) p) /\
            indep_vars p X (\n. Borel) UNIV /\
           (!n. expectation p (X n) = 0) /\
           (!n x. x IN p_space p ==> abs (X n x) <= Normal A) ==>
            !e n. 0 < e ==>
                  1 - Normal (A + e) pow 2 / ^variance_tm <=
                  prob p {x | x IN p_space p /\ Normal e < ^max_fn_seq_tm}
Proof
    cheat
QED

val _ = export_theory ();
val _ = html_theory "convergence";
