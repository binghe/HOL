(* ------------------------------------------------------------------------- *)
(*  Convergence Concepts and Convergence of Series                           *)
(*                                                                           *)
(*  Author: Chun Tian <binghe.lisp@gmail.com> (2022 - 2023)                  *)
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

(*
  "Every serious student of probability theory should read:

   A. N. Kolmogoroff, Uber die Summen durch den Zufall bestimmten unabhangiger
   Grossen, Math. Annalen 99 (1928), 309-319; Bermerkungen, 102 (1929), 484-488. [8]

   This contains Theorems 5.3.1 to 5.3.3 as well as the original version of Theorem 5.2.3."

  -- Kai Lai Chung, "A Course in Probability Theory." [2, p.149]
 *)

val _ = new_theory "convergence";

val set_ss = std_ss ++ PRED_SET_ss;

val _ = hide "S";
val _ = hide "W";

(* ========================================================================= *)
(* Convergence Concepts                                                      *)
(* ========================================================================= *)

val _ = Datatype `convergence_mode = almost_everywhere   ('a p_space)
                                   | in_probability      ('a p_space)
                                   | in_lebesgue extreal ('a p_space)
                                   | in_distribution     ('a p_space)`;

(* convergence of extreal-valued random series [1, p.68,70], only works
   for real-valued random variables (cf. real_random_variable_def)
 *)
Definition converge_def :
   (* X(n) converges to Y (a.e.) *)
   (converge (X :num->'a->extreal) (Y :'a->extreal) (almost_everywhere p) =
     AE x::p. ((\n. real (X n x)) --> real (Y x)) sequentially) /\

   (* X(n) converges to Y (in pr.) *)
   (converge (X :num->'a->extreal) (Y :'a->extreal) (in_probability p) =
     !e. 0 < e /\ e <> PosInf ==>
         ((\n. real (prob p {x | x IN p_space p /\ e < abs (X n x - Y x)})) --> 0)
           sequentially) /\

   (* X(n) converges to Y (in L^r) *)
   (converge (X :num->'a->extreal) (Y :'a->extreal) (in_lebesgue r p) <=>
     0 < r /\ r <> PosInf /\
     (!n. expectation p (\x. (abs (X n x)) powr r) <> PosInf) /\
     (expectation p (\x. (abs (Y x)) powr r) <> PosInf) /\
     ((\n. real (expectation p (\x. (abs (X n x - Y x)) powr r))) --> 0)
       sequentially)

   (* X(n) converges to Y in distribution (see [4, p.306] or [2, p.96])
   (converge (X :num->'a->extreal) (Y :'a->extreal) (in_distribution p) =
     !f. (* TODO: f is bounded and continuous ==> *)
         ((\n. real (expectation p (f o (X n)))) -->
               real (expectation p (f o Y))) sequentially)
    *)
End

(* "-->" is defined in util_probTheory; *)
Overload "-->" = “converge”

(* AE x::p. X_n(x) --> Y(x) *)
Theorem converge_AE_def =
   (List.nth (CONJUNCTS converge_def, 0)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`]);

(* !e. 0 < e ==> Prob {e < |X_n - Y|} --> 0 *)
Theorem converge_PR_def =
   (List.nth (CONJUNCTS converge_def, 1)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`]);

(* X_n IN L^p /\ Y IN L^p /\ E [|X_n - Y|^p] --> 0 *)
Theorem converge_LP_def =
   (List.nth (CONJUNCTS converge_def, 2)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`, `r`]);

(* tidy up theory exports, learnt from Magnus Myreen *)
val _ = List.app Theory.delete_binding
  ["convergence_mode_TY_DEF",
   "convergence_mode_case_def",
   "convergence_mode_size_def",
   "convergence_mode_11",
   "convergence_mode_Axiom",
   "convergence_mode_case_cong",
   "convergence_mode_case_eq",
   "convergence_mode_distinct",
   "convergence_mode_induction",
   "convergence_mode_nchotomy",
   "datatype_convergence_mode",
   "converge_def"];

(* alternative definition of converge_LP based on absolute moment *)
Theorem converge_LP_alt_absolute_moment :
   !p X Y k. prob_space p /\ (!n. real_random_variable (X n) p) /\
             real_random_variable Y p ==>
       ((X --> Y) (in_lebesgue (&k :extreal) p) <=>
        0 < k /\
        (!n. expectation p (\x. (abs (X n x)) pow k) <> PosInf) /\
        (expectation p (\x. (abs (Y x)) pow k) <> PosInf) /\
        ((\n. real (absolute_moment p (\x. X n x - Y x) 0 k)) --> 0) sequentially)
Proof
    RW_TAC std_ss [converge_LP_def, absolute_moment_def, sub_rzero, num_not_infty]
 >> Know `!Z. 0 < k ==> abs Z powr &k = abs Z pow k`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC gen_powr >> REWRITE_TAC [abs_pos]) >> DISCH_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (STRONG_CONJ_TAC
     >- (`(0 :real) < &k` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
         FULL_SIMP_TAC real_ss []) >> DISCH_TAC \\
     fs [] >> rfs [])
 >> fs [] >> rfs []
 >> `(0 :real) < &k` by RW_TAC real_ss []
 >> METIS_TAC [extreal_of_num_def, extreal_lt_eq]
QED

(* alternative definition of converge_LP using `pow k` explicitly *)
Theorem converge_LP_alt_pow =
        SIMP_RULE std_ss [absolute_moment_def, sub_rzero]
                  converge_LP_alt_absolute_moment;

(* Theorem 4.1.1 [1, p.69] (2) *)
Theorem converge_AE_alt_sup :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            (sup (IMAGE (\m. prob p {x | x IN p_space p /\
                                         !n. m <= n ==> abs (X n x - Y x) <= e})
                        univ(:num)) = 1))
Proof
    RW_TAC std_ss [real_random_variable_def]
 >> Q.ABBREV_TAC
     `A = \m e. BIGINTER
                  (IMAGE (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e}) (from m))`
 >> Q.ABBREV_TAC
     `E = \m e. {x | x IN p_space p /\ !n. m <= n ==> abs (X n x - Y x) <= e}`
 >> Know `!m e. {x | x IN p_space p /\
                     !n. m <= n ==> abs (X n x - Y x) <= e} = E m e`
 >- METIS_TAC [] >> Rewr'
 >> Know `!m e. E m e = A m e`
 >- (RW_TAC set_ss [Abbr `E`, Abbr `A`, Once EXTENSION, IN_BIGINTER_IMAGE, IN_FROM] \\
     EQ_TAC >> RW_TAC std_ss [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) >> Rewr'
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> Know `!e n. {x | x IN p_space p /\ abs (X n x - Y x) <= e} IN events p`
 >- (RW_TAC std_ss [abs_bounds] \\
     Q.ABBREV_TAC `f = \x. X n x - Y x` \\
    `f IN measurable (m_space p,measurable_sets p) Borel`
       by (Q.UNABBREV_TAC `f` \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
           qexistsl_tac [`X n`, `Y`] \\
           fs [prob_space_def, p_space_def, events_def, space_def,
               measure_space_def, random_variable_def]) \\
     Know `{x | x IN p_space p /\ -e <= X n x - Y x /\ X n x - Y x <= e} =
           ({x | -e <= f x} INTER p_space p) INTER ({x | f x <= e} INTER p_space p)`
     >- (Q.UNABBREV_TAC `f` >> BETA_TAC >> SET_TAC []) >> Rewr' \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> Know `!m e. A m e IN events p`
 >- (RW_TAC std_ss [Abbr `A`] \\
     MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [COUNTABLE_FROM, FROM_NOT_EMPTY] \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_FROM] \\
     METIS_TAC []) >> DISCH_TAC
 >> Q.UNABBREV_TAC `E`
 >> Know `!e. BIGUNION (IMAGE (\m. A m e) univ(:num)) IN events p`
 >- (GEN_TAC \\
     MATCH_MP_TAC EVENTS_COUNTABLE_UNION >> art [] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC image_countable >> REWRITE_TAC [COUNTABLE_NUM]) \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] >> PROVE_TAC []) >> DISCH_TAC
 >> Know `!m e. A m e SUBSET A (SUC m) e`
 >- (RW_TAC set_ss [Abbr `A`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM]
     >- (Q.PAT_X_ASSUM `!n. m <= n ==> P`
          (STRIP_ASSUME_TAC o (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) \\
    `m <= n` by RW_TAC arith_ss [] >> METIS_TAC []) >> DISCH_TAC
 (* Part I: AE ==> (liminf = 1) *)
 >> EQ_TAC
 >- (RW_TAC std_ss [converge_AE_def, AE_DEF, null_set_def, LIM_SEQUENTIALLY, dist] \\
     Know `!x. x IN m_space p DIFF N ==> ?m. x IN (A m e)`
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM `!x. x IN m_space p DIFF N ==> P` (MP_TAC o (Q.SPEC `x`)) \\
         RW_TAC std_ss [] \\
        `e <> NegInf` by METIS_TAC [pos_not_neginf, lt_imp_le] \\
        `?r. e = Normal r` by METIS_TAC [extreal_cases] \\
        `0 < r` by METIS_TAC [extreal_lt_eq, extreal_of_num_def] \\
         Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `r`)) \\
         RW_TAC std_ss [] \\
         Q.EXISTS_TAC `N'` \\
         RW_TAC set_ss [Abbr `A`, IN_BIGINTER_IMAGE, IN_FROM]
         >- METIS_TAC [DIFF_SUBSET, SUBSET_DEF, p_space_def] \\
         Q.PAT_X_ASSUM `!n. N' <= n ==> P` (MP_TAC o (Q.SPEC `n`)) \\
         RW_TAC std_ss [] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
        ‘m_space p DIFF N SUBSET m_space p’ by SET_TAC [] \\
        ‘x IN m_space p’ by METIS_TAC [SUBSET_DEF] \\
        `?a. X n x = Normal a` by METIS_TAC [extreal_cases] \\
        `?b. Y x = Normal b` by METIS_TAC [extreal_cases] \\
         MATCH_MP_TAC lt_imp_le \\
         FULL_SIMP_TAC std_ss [real_normal, extreal_sub_def, extreal_abs_def, extreal_lt_eq]) \\
     DISCH_TAC \\
    `(m_space p DIFF N) SUBSET BIGUNION (IMAGE (\m. A m e) univ(:num))`
        by (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV]) \\
     Know `sup (IMAGE (prob p o (\m. A m e)) univ(:num)) =
           prob p (BIGUNION (IMAGE (\m. A m e) univ(:num)))`
     >- (REWRITE_TAC [prob_def] \\
         MATCH_MP_TAC MONOTONE_CONVERGENCE \\
         CONJ_TAC >- fs [prob_space_def] \\
         RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def]) \\
     SIMP_TAC std_ss [o_DEF] >> DISCH_THEN K_TAC \\
     REWRITE_TAC [GSYM le_antisym] \\
     CONJ_TAC >- (MATCH_MP_TAC PROB_LE_1 >> art []) \\
     fs [GSYM p_space_def, GSYM events_def, GSYM prob_def] \\
     Know `prob p (p_space p DIFF N) = 1 - prob p N`
     >- (MATCH_MP_TAC PROB_COMPL >> art []) >> art [sub_rzero] \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
     MATCH_MP_TAC PROB_INCREASING >> art [] \\
     MATCH_MP_TAC EVENTS_COMPL >> PROVE_TAC [EVENTS_SPACE])
 (* Part II: (liminf = 1) ==> AE *)
 >> RW_TAC std_ss [converge_AE_def, AE_DEF, null_set_def, LIM_SEQUENTIALLY, dist]
 >> Q.ABBREV_TAC `B = \e. BIGUNION (IMAGE (\m. A m e) univ(:num))`
 >> Know `!e. 0 < e /\ e <> PosInf ==> (prob p (B e) = 1)`
 >- (RW_TAC std_ss [Abbr `B`] \\
     Suff `sup (IMAGE (prob p o (\m. A m e)) univ(:num)) =
           prob p (BIGUNION (IMAGE (\m. A m e) univ(:num)))` >- METIS_TAC [] \\
     REWRITE_TAC [prob_def] \\
     MATCH_MP_TAC MONOTONE_CONVERGENCE \\
     CONJ_TAC >- fs [prob_space_def] \\
     RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def])
 >> Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` K_TAC
 >> DISCH_TAC
 >> Q.ABBREV_TAC `C = BIGINTER (IMAGE (\n. B (1 / &SUC n)) univ(:num))`
 >> Know `C IN events p`
 >- (Q.UNABBREV_TAC `C` \\
     MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [COUNTABLE_NUM] \\
     reverse CONJ_TAC >- (SET_TAC []) \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] \\
     Q.UNABBREV_TAC `B` >> METIS_TAC [])
 >> DISCH_TAC
 >> Know `prob p C = 1`
 >- (Q.UNABBREV_TAC `C` >> REWRITE_TAC [prob_def] \\
    `measure p (BIGINTER (IMAGE (\n. B (1 / &SUC n)) univ(:num))) =
      inf (IMAGE (measure p o (\n. B (1 / &SUC n))) univ(:num))`
     by (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC MONOTONE_CONVERGENCE_BIGINTER \\
         ASM_SIMP_TAC std_ss [] \\
         CONJ_TAC >- fs [prob_space_def] \\
         STRONG_CONJ_TAC
         >- RW_TAC std_ss [IN_FUNSET, IN_UNIV, Abbr `B`, GSYM events_def] \\
         RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def, GSYM prob_def]
         >- METIS_TAC [PROB_FINITE] \\
         RW_TAC std_ss [Abbr `B`, SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV] \\
         Q.EXISTS_TAC `m` >> POP_ASSUM MP_TAC \\
         NTAC 6 (POP_ASSUM K_TAC) \\ (* up to Abbrev A *)
         RW_TAC set_ss [Abbr `A`, IN_BIGINTER_IMAGE, IN_FROM]
         >- (Q.PAT_X_ASSUM `!n'. m <= n' ==> x IN p_space p /\ _`
               (STRIP_ASSUME_TAC o (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) \\
         rename1 `m <= N` \\
         Q.PAT_X_ASSUM `!n'. m <= n' ==> x IN p_space p /\ _`
           (MP_TAC o (Q.SPEC `N`)) >> RW_TAC std_ss [] \\
         fs [abs_bounds] \\
        `(&SUC n) :real <> 0` by RW_TAC real_ss [] \\
        `(&SUC (SUC n)) :real <> 0` by RW_TAC real_ss [] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC le_trans \\
           Q.EXISTS_TAC `-(1 / &SUC (SUC n))` >> art [] \\
           rw [extreal_of_num_def, extreal_div_eq, extreal_ainv_def,
               extreal_le_eq] \\
           rw [GSYM REAL_INV_1OVER],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC le_trans \\
           Q.EXISTS_TAC `1 / &SUC (SUC n)` >> art [] \\
           rw [extreal_of_num_def, extreal_div_eq, extreal_ainv_def, extreal_le_eq] \\
           rw [GSYM REAL_INV_1OVER]
         ]) >> POP_ORW \\
     REWRITE_TAC [GSYM prob_def] \\
     Suff `IMAGE (prob p o (\n. B (1 / &SUC n))) univ(:num) = (\y. y = 1)`
     >- (Rewr' >> REWRITE_TAC [inf_const]) \\
     RW_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_UNIV] \\
     SIMP_TAC std_ss [IN_APP] \\
     EQ_TAC >> RW_TAC std_ss []
     >- (FIRST_X_ASSUM MATCH_MP_TAC \\
        `(&SUC x') :real <> 0` by RW_TAC real_ss [] \\
         rw [extreal_of_num_def, extreal_div_eq, extreal_lt_eq, extreal_not_infty] \\
         MATCH_MP_TAC REAL_LT_DIV >> RW_TAC real_ss []) \\
     Q.EXISTS_TAC `0` (* any number is fine *) \\
     MATCH_MP_TAC EQ_SYM \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
    `(&SUC 0) :real <> 0` by RW_TAC real_ss [] \\
     rw [extreal_of_num_def, extreal_div_eq, extreal_lt_eq, extreal_not_infty])
 >> DISCH_TAC
 >> Q.EXISTS_TAC `p_space p DIFF C`
 >> REWRITE_TAC [GSYM CONJ_ASSOC, GSYM events_def, GSYM prob_def, GSYM p_space_def]
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC EVENTS_COMPL >> art []) >> DISCH_TAC
 >> CONJ_TAC
 >- (Know `prob p (p_space p DIFF C) = 1 - prob p C`
     >- (MATCH_MP_TAC PROB_COMPL >> art []) >> Rewr' >> art [] \\
     MATCH_MP_TAC sub_refl >> rw [extreal_of_num_def])
 >> rw [] (* p_space p DIFF (p_space p DIFF C) is simplified *)
 >> Q.PAT_X_ASSUM `x IN C` MP_TAC
 >> Q.PAT_X_ASSUM `C IN events p` K_TAC
 >> Q.PAT_X_ASSUM `prob p C = 1` K_TAC
 >> Q.PAT_X_ASSUM `p_space p DIFF C IN events p` K_TAC
 >> Q.UNABBREV_TAC `C`
 >> RW_TAC std_ss [IN_BIGINTER_IMAGE, IN_UNIV]
 >> Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> _` K_TAC
 >> Q.UNABBREV_TAC `B` >> fs []
 >> MP_TAC (Q.SPEC `e` REAL_ARCH_INV_SUC) >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!n. ?s. x IN s /\ P` (STRIP_ASSUME_TAC o (Q.SPEC `n`))
 >> Q.PAT_X_ASSUM `x IN s` MP_TAC >> POP_ORW
 >> Q.PAT_X_ASSUM `!m e. A m e SUBSET A (SUC m) e` K_TAC
 >> Q.PAT_X_ASSUM `!e. BIGUNION (IMAGE (\m. A m e) UNIV) IN events p` K_TAC
 >> Q.PAT_X_ASSUM `!m e. A m e IN events p` K_TAC
 >> Q.UNABBREV_TAC `A`
 >> RW_TAC set_ss [IN_BIGINTER_IMAGE, IN_FROM]
 >> Q.EXISTS_TAC `m`
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC `inv (&SUC n)` >> art []
 >> rename1 `m <= N`
 >> Q.PAT_X_ASSUM `!n'. m <= n' ==> P` (MP_TAC o (Q.SPEC `N`))
 >> RW_TAC std_ss []
 >> `?a. X N x = Normal a` by METIS_TAC [extreal_cases]
 >> `?b. Y x = Normal b` by METIS_TAC [extreal_cases]
 >> `(&SUC n) :real <> 0` by RW_TAC real_ss []
 >> fs [real_normal, extreal_sub_def, extreal_abs_def, extreal_inv_eq,
        extreal_of_num_def, extreal_div_eq, extreal_le_eq, real_div]
QED

(* Theorem 4.1.1 [1, p.69] (2') *)
Theorem converge_AE_alt_inf :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            (inf (IMAGE (\m. prob p {x | x IN p_space p /\
                                         ?n. m <= n /\ e < abs (X n x - Y x)})
                        univ(:num)) = 0))
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`p`, `X`, `Y`] converge_AE_alt_sup)
 >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
 >> Q.ABBREV_TAC
     `E = \m e. {x | x IN p_space p /\ !n. m <= n ==> abs (X n x - Y x) <= e}`
 >> `!m e. {x | x IN p_space p /\
                     !n. m <= n ==> abs (X n x - Y x) <= e} = E m e`
      by METIS_TAC [] >> POP_ORW
 >> Know `!m e. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (X n x - Y x)} =
                p_space p DIFF (E m e)`
 >- (RW_TAC set_ss [Abbr `E`, Once EXTENSION] \\
     EQ_TAC >> RW_TAC std_ss [GSYM extreal_lt_def] \\
     Q.EXISTS_TAC `n` >> art []) >> Rewr'
 >> Q.ABBREV_TAC
     `A = \m e. BIGINTER
                  (IMAGE (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e}) (from m))`
 >> Know `!m e. E m e = A m e`
 >- (RW_TAC set_ss [Abbr `E`, Abbr `A`, Once EXTENSION, IN_BIGINTER_IMAGE, IN_FROM] \\
     EQ_TAC >> RW_TAC std_ss [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) >> Rewr'
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> fs [real_random_variable_def]
 >> Know `!e n. {x | x IN p_space p /\ abs (X n x - Y x) <= e} IN events p`
 >- (RW_TAC std_ss [abs_bounds] \\
     Q.ABBREV_TAC `f = \x. X n x - Y x` \\
    `f IN measurable (m_space p,measurable_sets p) Borel`
       by (Q.UNABBREV_TAC `f` \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
           qexistsl_tac [`X n`, `Y`] \\
           fs [prob_space_def, p_space_def, events_def, space_def,
               measure_space_def, random_variable_def]) \\
     Know `{x | x IN p_space p /\ -e <= X n x - Y x /\ X n x - Y x <= e} =
           ({x | -e <= f x} INTER p_space p) INTER ({x | f x <= e} INTER p_space p)`
     >- (Q.UNABBREV_TAC `f` >> BETA_TAC >> SET_TAC []) >> Rewr' \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> Know `!m e. A m e IN events p`
 >- (RW_TAC std_ss [Abbr `A`] \\
     MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [COUNTABLE_FROM, FROM_NOT_EMPTY] \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_FROM] \\
     METIS_TAC []) >> DISCH_TAC
 >> Q.UNABBREV_TAC `E`
 >> Know `!e. BIGUNION (IMAGE (\m. A m e) univ(:num)) IN events p`
 >- (GEN_TAC >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC image_countable >> REWRITE_TAC [COUNTABLE_NUM]) \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] >> PROVE_TAC []) >> DISCH_TAC
 >> Know `!m e. A m e SUBSET A (SUC m) e`
 >- (RW_TAC set_ss [Abbr `A`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM]
     >- (Q.PAT_X_ASSUM `!n. m <= n ==> P`
          (STRIP_ASSUME_TAC o (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) \\
    `m <= n` by RW_TAC arith_ss [] >> METIS_TAC []) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!e n. {x | x IN p_space p /\ P} IN events p` K_TAC
 >> Q.ABBREV_TAC `B = \m e. p_space p DIFF A m e`
 >> Know `!m e. p_space p DIFF A m e = B m e` >- METIS_TAC [] >> Rewr'
 >> `!m e. B m e IN events p` by METIS_TAC [EVENTS_COMPL]
 >> Know `!e. BIGINTER (IMAGE (\m. B m e) univ(:num)) IN events p`
 >- (GEN_TAC >> MATCH_MP_TAC EVENTS_COUNTABLE_INTER >> art [] \\
     CONJ_TAC
     >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] >> PROVE_TAC []) \\
     CONJ_TAC >- (MATCH_MP_TAC image_countable >> REWRITE_TAC [COUNTABLE_NUM]) \\
     RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_IMAGE, IN_UNIV]) >> DISCH_TAC
 >> Know `!m e. B (SUC m) e SUBSET B m e`
 >- (RW_TAC set_ss [Abbr `B`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM] \\
     ASM_SET_TAC []) >> DISCH_TAC
 >> Suff `!e. 0 < e /\ e <> PosInf ==>
            ((sup (IMAGE (\m. prob p (A m e)) univ(:num)) = 1) <=>
             (inf (IMAGE (\m. prob p (B m e)) univ(:num)) = 0))` >- METIS_TAC []
 >> rpt STRIP_TAC
 >> Know `sup (IMAGE (prob p o (\m. A m e)) univ(:num)) =
          prob p (BIGUNION (IMAGE (\m. A m e) univ(:num)))`
 >- (REWRITE_TAC [prob_def] \\
     MATCH_MP_TAC MONOTONE_CONVERGENCE \\
     CONJ_TAC >- fs [prob_space_def] \\
     RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def])
 >> SIMP_TAC std_ss [o_DEF] >> DISCH_THEN K_TAC
 >> Know `inf (IMAGE (prob p o (\m. B m e)) univ(:num)) =
          prob p (BIGINTER (IMAGE (\m. B m e) univ(:num)))`
 >- (REWRITE_TAC [prob_def] \\
     MATCH_MP_TAC MONOTONE_CONVERGENCE_BIGINTER \\
     CONJ_TAC >- fs [prob_space_def] \\
     RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def, GSYM prob_def] \\
     PROVE_TAC [PROB_FINITE])
 >> SIMP_TAC std_ss [o_DEF] >> DISCH_THEN K_TAC
 >> Know `BIGUNION (IMAGE (\m. A m e) univ(:num)) =
          p_space p DIFF (BIGINTER (IMAGE (\m. B m e) univ(:num)))`
 >- (RW_TAC std_ss [Once EXTENSION, Abbr `B`, IN_DIFF, IN_UNIV,
                    IN_BIGUNION_IMAGE, IN_BIGINTER_IMAGE] \\
     EQ_TAC >> RW_TAC std_ss [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       irule PROB_SPACE_IN_PSPACE >> art [] \\
       Q.EXISTS_TAC `A m e` >> art [],
       (* goal 2 (of 3) *)
       Q.EXISTS_TAC `m` >> DISJ2_TAC >> art [],
       (* goal 3 (of 3) *)
       Q.EXISTS_TAC `m` >> art [] ]) >> Rewr'
 >> Know `prob p (p_space p DIFF BIGINTER (IMAGE (\m. B m e) univ(:num))) =
          1 - prob p (BIGINTER (IMAGE (\m. B m e) univ(:num)))`
 >- (MATCH_MP_TAC PROB_COMPL >> art []) >> Rewr'
 >> `prob p (BIGINTER (IMAGE (\m. B m e) univ(:num))) <> PosInf /\
     prob p (BIGINTER (IMAGE (\m. B m e) univ(:num))) <> NegInf`
       by METIS_TAC [PROB_FINITE]
 >> `?r. prob p (BIGINTER (IMAGE (\m. B m e) univ(:num))) = Normal r`
       by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_of_num_def, extreal_sub_def, extreal_11]
 >> REAL_ARITH_TAC
QED

(* Theorem 4.1.2 [1, p.70]: convergence a.e. implies convergence in pr. *)
Theorem converge_AE_imp_PR :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p /\
           (X --> Y) (almost_everywhere p) ==> (X --> Y) (in_probability p)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> MP_TAC (Q.SPECL [`p`, `X`, `Y`] converge_AE_alt_inf)
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `(X --> Y) (almost_everywhere p) <=> P` K_TAC
 >> RW_TAC real_ss [converge_PR_def, LIM_SEQUENTIALLY, dist]
 >> rename1 `0 < r`
 >> fs [real_random_variable_def]
 >> Q.ABBREV_TAC `D = \n. {x | x IN p_space p /\ e < abs (X n x - Y x)}`
 >> `!n. {x | x IN p_space p /\ e < abs (X n x - Y x)} = D n`
      by METIS_TAC [] >> POP_ORW
 >> Q.ABBREV_TAC `B = \m. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (X n x - Y x)}`
 >> Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` (MP_TAC o (Q.SPEC `e`))
 >> `!m. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (X n x - Y x)} = B m`
      by METIS_TAC [] >> POP_ORW
 >> RW_TAC std_ss []
 >> Know `!n. D n SUBSET B n`
 >- (RW_TAC set_ss [Abbr `D`, Abbr `B`, SUBSET_DEF] \\
     Q.EXISTS_TAC `n` >> art [LESS_EQ_REFL]) >> DISCH_TAC
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> Q.ABBREV_TAC `f = \n x. X n x - Y x`
 >> Know `!n. (f n) IN measurable (m_space p,measurable_sets p) Borel`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`X n`, `Y`] \\
     fs [prob_space_def, p_space_def, events_def, space_def,
         measure_space_def, random_variable_def]) >> DISCH_TAC
 >> Know `!n. D n IN events p`
 >- (GEN_TAC >> Q.UNABBREV_TAC `D` >> BETA_TAC \\
    `{x | x IN p_space p /\ e < abs (X n x - Y x)} =
     p_space p DIFF {x | x IN p_space p /\ abs (X n x - Y x) <= e}`
        by (RW_TAC set_ss [Once EXTENSION, GSYM extreal_lt_def] \\
            METIS_TAC []) >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> art [] \\
     RW_TAC std_ss [abs_bounds] \\
    `{x | x IN p_space p /\ -e <= f n x /\ f n x <= e} =
     ({x | -e <= f n x} INTER p_space p) INTER ({x | f n x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> `!n. 0 <= prob p (D n)` by METIS_TAC [PROB_POSITIVE]
 >> `!n. prob p (D n) <> PosInf /\ prob p (D n) <> NegInf` by METIS_TAC [PROB_FINITE]
 >> Know `!n. abs (real (prob p (D n))) = real (prob p (D n))`
 >- (RW_TAC std_ss [ABS_REFL] \\
     ASM_SIMP_TAC std_ss [GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def]) >> Rewr'
 >> ASM_SIMP_TAC std_ss [GSYM extreal_lt_eq, normal_real]
 >> Q.ABBREV_TAC
     `E = \m. {x | x IN p_space p /\ !n. m <= n ==> abs (X n x - Y x) <= e}`
 >> Know `!m. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (X n x - Y x)} =
              p_space p DIFF (E m)`
 >- (RW_TAC set_ss [Abbr `E`, Once EXTENSION] \\
     EQ_TAC >> RW_TAC std_ss [GSYM extreal_lt_def] \\
     Q.EXISTS_TAC `n` >> art [])
 >> DISCH_THEN (fs o wrap)
 >> Q.ABBREV_TAC
     `A = \m. BIGINTER
                (IMAGE (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e}) (from m))`
 >> Know `!m. E m = A m`
 >- (RW_TAC set_ss [Abbr `E`, Abbr `A`, Once EXTENSION, IN_BIGINTER_IMAGE, IN_FROM] \\
     EQ_TAC >> RW_TAC std_ss [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`)))
 >> DISCH_THEN (fs o wrap)
 >> Know `!m. A m SUBSET A (SUC m)`
 >- (RW_TAC set_ss [Abbr `A`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM]
     >- (Q.PAT_X_ASSUM `!n. m <= n ==> P`
           (STRIP_ASSUME_TAC o (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) \\
    `m <= n` by RW_TAC arith_ss [] >> METIS_TAC []) >> DISCH_TAC
 >> Know `!m. B (SUC m) SUBSET B m`
 >- (RW_TAC set_ss [Abbr `B`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM] \\
     ASM_SET_TAC []) >> DISCH_TAC
 >> Know `!m n. m <= n ==> B n SUBSET B m`
 >- (GEN_TAC >> Induct_on `n`
     >- (DISCH_TAC >> `m = 0` by RW_TAC arith_ss [] >> art [SUBSET_REFL]) \\
     DISCH_TAC \\
    `m = SUC n \/ m < SUC n` by RW_TAC arith_ss [] >- art [SUBSET_REFL] \\
    `m <= n` by RW_TAC arith_ss [] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `B n` >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Know `!n. B n IN events p`
 >- (GEN_TAC >> Q.UNABBREV_TAC `B` >> BETA_TAC \\
     MATCH_MP_TAC EVENTS_COMPL >> art [] \\
     Q.UNABBREV_TAC `A` >> BETA_TAC \\
     MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [COUNTABLE_FROM, FROM_NOT_EMPTY] \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_FROM] \\
     rename1 `n <= m` >> REWRITE_TAC [abs_bounds] \\
    `{x | x IN p_space p /\ -e <= f m x /\ f m x <= e} =
     ({x | -e <= f m x} INTER p_space p) INTER ({x | f m x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> `!n. prob p (D n) <= prob p (B n)` by METIS_TAC [PROB_INCREASING]
 >> Know `inf (IMAGE (\m. prob p (B m)) univ(:num)) < Normal r`
 >- (ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_lt_eq])
 >> RW_TAC std_ss [GSYM inf_lt', IN_IMAGE, IN_UNIV]
 >> Q.EXISTS_TAC `m` >> rpt STRIP_TAC
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `prob p (B n)`  >> art []
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `prob p (B m)`  >> art []
 >> MATCH_MP_TAC PROB_INCREASING >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC   >> art []
QED

(* converge_AE_alt_sup restated by liminf, cf. PROB_LIMINF *)
Theorem converge_AE_alt_liminf :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            prob p (liminf (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e})) = 1)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`p`, `X`, `Y`] converge_AE_alt_sup)
 >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
 >> Suff `!e. 0 < e /\ e <> PosInf ==>
            ((sup
               (IMAGE
                  (\m. prob p
                         {x |
                          x IN p_space p /\
                          !n. m <= n ==> abs (X n x - Y x) <= e}) univ(:num)) = 1) <=>
             (prob p (liminf (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e})) = 1))`
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> fs [real_random_variable_def]
 >> Q.ABBREV_TAC `f = \n x. X n x - Y x`
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> Know `!n. (f n) IN measurable (m_space p,measurable_sets p) Borel`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`X n`, `Y`] \\
     fs [prob_space_def, p_space_def, events_def, space_def,
         measure_space_def, random_variable_def]) >> DISCH_TAC
 >> Q.ABBREV_TAC `E = \n. {x | x IN p_space p /\ abs (X n x - Y x) <= e}`
 >> Know `!n. E n IN events p`
 >- (RW_TAC std_ss [Abbr `E`, abs_bounds] \\
    `{x | x IN p_space p /\ -e <= f n x /\ f n x <= e} =
     ({x | -e <= f n x} INTER p_space p) INTER ({x | f n x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [PROB_LIMINF]
 >> Suff `!m. {x | x IN p_space p /\ !n. m <= n ==> abs (f n x) <= e} =
              (BIGINTER {E n | m <= n})` >- rw []
 >> GEN_TAC
 >> `{E n | m <= n} = (IMAGE E (from m))`
      by (RW_TAC set_ss [Abbr `E`, IN_FROM, Once EXTENSION]) >> POP_ORW
 >> RW_TAC set_ss [Abbr `E`, Abbr `f`, Once EXTENSION, IN_BIGINTER_IMAGE, IN_FROM]
 >> EQ_TAC >> RW_TAC std_ss []
 >> POP_ASSUM (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))
QED

(* converge_AE_alt_inf restated by limsup, cf. PROB_LIMSUP

   Theorem 4.2.2 [1, p.77] (extended version), also see Borel_Cantelli_Lemma1.
 *)
Theorem converge_AE_alt_limsup :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            prob p (limsup (\n. {x | x IN p_space p /\ e < abs (X n x - Y x)})) = 0)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`p`, `X`, `Y`] converge_AE_alt_inf)
 >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
 >> Suff `!e. 0 < e /\ e <> PosInf ==>
            ((inf
               (IMAGE
                  (\m. prob p
                         {x |
                          x IN p_space p /\
                          ?n. m <= n /\ e < abs (X n x - Y x)}) univ(:num)) = 0) <=>
             (prob p (limsup (\n. {x | x IN p_space p /\ e < abs (X n x - Y x)})) = 0))`
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> fs [real_random_variable_def]
 >> Q.ABBREV_TAC `f = \n x. X n x - Y x`
 >> Know `!n. (f n) IN measurable (m_space p,measurable_sets p) Borel`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`X n`, `Y`] \\
     fs [prob_space_def, p_space_def, events_def, space_def,
         measure_space_def, random_variable_def]) >> DISCH_TAC
 >> Q.ABBREV_TAC `E = \n. {x | x IN p_space p /\ e < abs (X n x - Y x)}`
 >> Know `!n. E n IN events p`
 >- (RW_TAC std_ss [Abbr `E`] \\
   `{x | x IN p_space p /\ e < abs (f n x)} =
     p_space p DIFF {x | x IN p_space p /\ abs (f n x) <= e}`
        by (RW_TAC set_ss [Once EXTENSION, GSYM extreal_lt_def] \\
            METIS_TAC []) >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> art [] \\
     REWRITE_TAC [abs_bounds] \\
    `{x | x IN p_space p /\ -e <= f n x /\ f n x <= e} =
     ({x | -e <= f n x} INTER p_space p) INTER ({x | f n x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 (* applying PROB_LIMSUP *)
 >> ASM_SIMP_TAC std_ss [PROB_LIMSUP]
 >> Suff `!m. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (f n x)} =
              (BIGUNION {E n | m <= n})` >- rw []
 >> GEN_TAC
 >> `{E n | m <= n} = (IMAGE E (from m))`
      by (RW_TAC set_ss [Abbr `E`, IN_FROM, Once EXTENSION]) >> POP_ORW
 >> RW_TAC set_ss [Abbr `E`, Abbr `f`, Once EXTENSION, IN_BIGUNION_IMAGE, IN_FROM]
 >> EQ_TAC >> RW_TAC std_ss [] >- art []
 >> Q.EXISTS_TAC `n` >> art []
QED

(* Theorem 4.2.2 [1, p.77] (original version) *)
Theorem converge_AE_alt_limsup' :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) ==>
         ((X --> (\x. 0)) (almost_everywhere p) <=>
          !e. 0 < e /\ e <> PosInf ==>
              prob p (limsup (\n. {x | x IN p_space p /\ e < abs (X n x)})) = 0)
Proof
    rpt STRIP_TAC
 >> ‘real_random_variable (\x. 0) p’ by METIS_TAC [real_random_variable_zero]
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘\x. 0’] converge_AE_alt_limsup)
 >> RW_TAC std_ss [sub_rzero]
QED

Theorem converge_AE_to_zero :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        ((\n x. X n x - Y x) --> (\x. 0)) (almost_everywhere p))
Proof
    rpt STRIP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> Q.ABBREV_TAC `Z = \n x. X n x - Y x`
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (RW_TAC std_ss [Abbr `Z`] \\
     MATCH_MP_TAC real_random_variable_sub >> art [])
 >> RW_TAC std_ss [converge_AE_alt_limsup, sub_rzero]
QED

Theorem converge_PR_to_zero :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (in_probability p) <=>
        ((\n x. X n x - Y x) --> (\x. 0)) (in_probability p))
Proof
    rpt STRIP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> Q.ABBREV_TAC `Z = \n x. X n x - Y x`
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (RW_TAC std_ss [Abbr `Z`] \\
     MATCH_MP_TAC real_random_variable_sub >> art [])
 >> DISCH_TAC
 >> RW_TAC std_ss [converge_PR_def, sub_rzero]
QED

Theorem converge_AE_imp_PR' :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
         (X --> (\x. 0)) (almost_everywhere p) ==>
         (X --> (\x. 0)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> irule converge_AE_imp_PR
 >> rw [real_random_variable_zero]
QED

(* Theorem 4.1.4 [2, p.71], for moments (integer-valued) only. *)
Theorem converge_LP_imp_PR' :
    !p X k. prob_space p /\ (!n. real_random_variable (X n) p) /\
            (X --> (\x. 0)) (in_lebesgue (&k :extreal) p) ==>
            (X --> (\x. 0)) (in_probability p)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> RW_TAC real_ss [converge_LP_alt_pow, converge_PR_def, LIM_SEQUENTIALLY,
                    dist, expectation_def, sub_rzero, REAL_SUB_RZERO]
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> fs [real_random_variable_def]
 >> rename1 `0 < d` (* the last assumption *)
 >> Know `!n. {x | x IN p_space p /\ e < abs (X n x)} IN events p`
 >- (GEN_TAC \\
    `{x | x IN p_space p /\ e < abs (X n x)} =
     p_space p DIFF {x | x IN p_space p /\ abs (X n x) <= e}`
        by (RW_TAC set_ss [Once EXTENSION, GSYM extreal_lt_def] \\
            METIS_TAC []) >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> art [] \\
     REWRITE_TAC [abs_bounds] \\
    `{x | x IN p_space p /\ -e <= X n x /\ X n x <= e} =
     ({x | -e <= X n x} INTER p_space p) INTER ({x | X n x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     fs [random_variable_def, events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> Know `!n. abs (real (prob p {x | x IN p_space p /\ e < abs (X n x)})) =
                   real (prob p {x | x IN p_space p /\ e < abs (X n x)})`
 >- (GEN_TAC \\
    `prob p {x | x IN p_space p /\ e < abs (X n x)} <> PosInf /\
     prob p {x | x IN p_space p /\ e < abs (X n x)} <> NegInf`
        by METIS_TAC [PROB_FINITE] \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def] \\
     MATCH_MP_TAC PROB_POSITIVE >> art []) >> Rewr'
 >> Know `!n. 0 <= integral p (\x. abs (X n x) pow k)`
 >- (GEN_TAC >> MATCH_MP_TAC integral_pos \\
     fs [prob_space_def] \\
     rpt STRIP_TAC >> MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos])
 >> DISCH_TAC
 >> `!n. integral p (\x. abs (X n x) pow k) <> NegInf`
       by METIS_TAC [pos_not_neginf]
 >> Know `!n. abs (real (integral p (\x. abs (X n x) pow k))) =
                   real (integral p (\x. abs (X n x) pow k))`
 >- (GEN_TAC \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def])
 >> DISCH_THEN (fs o wrap)
 >> Know `!n. integrable p (\x. abs (X n x) pow k)`
 >- (Q.X_GEN_TAC ‘n’ \\
     fs [prob_space_def, random_variable_def, p_space_def, events_def] \\
     Know `measure_space p /\
           (!x. x IN m_space p ==> 0 <= (\x. abs (X n x) pow k) x)`
     >- (RW_TAC std_ss [] \\
         MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos]) \\
     DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP integrable_pos)) \\
     reverse CONJ_TAC
     >- (Suff `pos_fn_integral p (\x. abs (X n x) pow k) =
                      integral p (\x. abs (X n x) pow k)` >- rw [] \\
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC integral_pos_fn \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos]) \\
     ONCE_REWRITE_TAC [METIS_PROVE []
       ``(\x. abs (X n x) pow k) = (\x. (\x. abs (X n x)) x pow k)``] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
     Q.EXISTS_TAC `X n` >> fs [measure_space_def])
 >> DISCH_TAC
 (* eliminate all `real (prob p ...)` *)
 >> `!n. real (prob p {x | x IN p_space p /\ e < abs (X n x)}) < d <=>
               prob p {x | x IN p_space p /\ e < abs (X n x)} < Normal d`
       by (METIS_TAC [PROB_FINITE, normal_real, extreal_lt_eq]) >> POP_ORW
 >> `!n. integral p (\x. abs (X n x) pow k) <> NegInf`
       by (METIS_TAC [pos_not_neginf])
 >> `!e n. real (integral p (\x. abs (X n x) pow k)) < e <=>
                 integral p (\x. abs (X n x) pow k) < Normal e`
       by (METIS_TAC [normal_real, extreal_lt_eq])
 >> POP_ASSUM (fs o wrap)
 (* prepare for prob_markov_ineq *)
 >> `e <> NegInf` by METIS_TAC [lt_imp_le, pos_not_neginf]
 >> `?E. e = Normal E` by METIS_TAC [extreal_cases]
 >> `0 < E` by METIS_TAC [extreal_of_num_def, extreal_lt_eq]
 >> Q.PAT_X_ASSUM `!e. 0 < e ==> ?N. P` (MP_TAC o (Q.SPEC `d * E pow k`))
 >> `0 < E pow k` by PROVE_TAC [REAL_POW_LT]
 >> Know `0 < d * E pow k` >- (MATCH_MP_TAC REAL_LT_MUL >> art [])
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `N` >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `!n. N <= n ==> P`
      (MP_TAC o (REWRITE_RULE [GSYM expectation_def]) o (Q.SPEC `n`))
 >> RW_TAC std_ss [GSYM extreal_mul_def]
 >> Know `!m x. x IN p_space p ==>
               (Normal E < abs (X m x) <=> Normal (E pow k) < abs (X m x) pow k)`
 >- (rpt STRIP_TAC \\
    `?r. X m x = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
     SIMP_TAC std_ss [extreal_abs_def, extreal_pow_def, extreal_lt_eq] \\
    `k <> 0` by RW_TAC arith_ss [] \\
     EQ_TAC >> STRIP_TAC
     >- (MATCH_MP_TAC REAL_POW_LT2 >> art [] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM real_lte])) \\
    `abs r pow k <= E pow k` by METIS_TAC [POW_LE, ABS_POS] \\
     METIS_TAC [REAL_LTE_ANTISYM])
 >> DISCH_TAC
 >> Know ‘!m. {x | x IN p_space p /\ Normal E < abs (X m x)} =
              {x | x IN p_space p /\ Normal (E pow k) < abs (X m x) pow k}’
 >- (rw [Once EXTENSION] \\
     METIS_TAC [])
 >> DISCH_THEN (fs o wrap)
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `prob p {x | x IN p_space p /\ Normal (E pow k) <= abs (X n x) pow k}`
 >> CONJ_TAC (* from `<` to `<=` *)
 >- (MATCH_MP_TAC PROB_INCREASING >> art [] \\
     reverse CONJ_TAC
     >- (RW_TAC set_ss [SUBSET_DEF] >> MATCH_MP_TAC lt_imp_le >> art []) \\
     fs [random_variable_def, prob_space_def, events_def, p_space_def] \\
    `{x | x IN m_space p /\ Normal (E pow k) <= abs (X n x) pow k} =
     {x | Normal (E pow k) <= (\x. abs (X n x) pow k) x} INTER m_space p`
        by SET_TAC [] >> POP_ORW \\
     Suff `(\x. abs (X n x) pow k) IN measurable (m_space p,measurable_sets p) Borel`
     >- rw [IN_MEASURABLE_BOREL_ALL_MEASURE] \\
    `!x. abs (X n x) = (\x. abs (X n x)) x` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS >> Q.EXISTS_TAC `X n` \\
     FULL_SIMP_TAC std_ss [measure_space_def])
 (* applying prob_markov_ineq *)
 >> Q.ABBREV_TAC `Y = \x. abs (X n x) pow k`
 >> Know `!x. abs (X n x) pow k = abs (Y x)`
 >- (RW_TAC std_ss [Abbr `Y`, Once EQ_SYM_EQ, abs_refl] \\
     MATCH_MP_TAC pow_pos_le >> rw [abs_pos]) >> Rewr'
 >> `{x | x IN p_space p /\ Normal (E pow k) <= abs (Y x)} =
     {x | Normal (E pow k) <= abs (Y x)} INTER p_space p` by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `inv (Normal (E pow k)) * expectation p (abs o Y)`
 >> CONJ_TAC
 >- (MATCH_MP_TAC prob_markov_ineq \\
     RW_TAC std_ss [Abbr `Y`, extreal_of_num_def, extreal_lt_eq])
 >> Know `abs o Y = Y`
 >- (RW_TAC std_ss [o_DEF, Abbr `Y`, abs_refl, FUN_EQ_THM] \\
     MATCH_MP_TAC pow_pos_le >> rw [abs_pos]) >> Rewr'
 >> `0 < Normal (E pow k) /\ Normal (E pow k) <> PosInf`
       by (ASM_SIMP_TAC std_ss [extreal_not_infty, extreal_of_num_def, extreal_lt_eq])
 >> Know `inv (Normal (E pow k)) * expectation p Y < Normal d <=>
          Normal (E pow k) * (inv (Normal (E pow k)) * expectation p Y) <
          Normal (E pow k) * Normal d`
 >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC lt_lmul >> art []) >> Rewr'
 >> ASM_SIMP_TAC std_ss [mul_assoc, mul_lone,
                         ONCE_REWRITE_RULE [mul_comm] mul_linv_pos]
 >> ASM_REWRITE_TAC [Once mul_comm]
QED

Theorem converge_AE_cong_full :
    !p X Y A B m. (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) /\
                  (!x. x IN p_space p ==> A x = B x) ==>
                  ((X --> A) (almost_everywhere p) <=> (Y --> B) (almost_everywhere p))
Proof
    rw [p_space_def, converge_AE_def, AE_DEF, LIM_SEQUENTIALLY, dist]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘N’ >> rw [] \\
      Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N ==> P’ (MP_TAC o (Q.SPEC ‘x’)) \\
      rw [] >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      Q.EXISTS_TAC ‘MAX N' m’ >> rw [MAX_LE] \\
     ‘Y n x = X n x’ by METIS_TAC [] >> POP_ORW \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘N’ >> rw [] \\
      Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N ==> P’ (MP_TAC o (Q.SPEC ‘x’)) \\
      rw [] >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      Q.EXISTS_TAC ‘MAX N' m’ >> rw [MAX_LE] ]
QED

Theorem converge_AE_cong :
    !p X Y Z m. (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) ==>
                ((X --> Z) (almost_everywhere p) <=> (Y --> Z) (almost_everywhere p))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC converge_AE_cong_full
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

Theorem converge_PR_cong_full :
    !p X Y A B m. (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) /\
                  (!x. x IN p_space p ==> A x = B x) ==>
                  ((X --> A) (in_probability p) <=> (Y --> B) (in_probability p))
Proof
    rw [converge_PR_def, LIM_SEQUENTIALLY, dist]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e /\ e <> PosInf ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      rename1 ‘0 < (E :real)’ \\
      POP_ASSUM (MP_TAC o (Q.SPEC ‘E’)) >> rw [] \\
      Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE] \\
      Know ‘{x | x IN p_space p /\ e < abs (Y n x - B x)} =
            {x | x IN p_space p /\ e < abs (X n x - A x)}’
      >- (rw [Once EXTENSION] \\
          EQ_TAC >> rw [] >> METIS_TAC []) >> Rewr' \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e /\ e <> PosInf ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      rename1 ‘0 < (E :real)’ \\
      POP_ASSUM (MP_TAC o (Q.SPEC ‘E’)) >> rw [] \\
      Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE] \\
      Know ‘{x | x IN p_space p /\ e < abs (X n x - A x)} =
            {x | x IN p_space p /\ e < abs (Y n x - B x)}’
      >- (rw [Once EXTENSION] \\
          EQ_TAC >> rw [] >> METIS_TAC []) >> Rewr' \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] ]
QED

Theorem converge_PR_cong :
    !p X Y Z m. (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) ==>
                ((X --> Z) (in_probability p) <=> (Y --> Z) (in_probability p))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC converge_PR_cong_full
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

Theorem converge_LP_cong :
    !p X Y Z k. prob_space p /\
               (!n x. x IN p_space p ==> X n x = Y n x) ==>
               ((X --> Z) (in_lebesgue k p) <=> (Y --> Z) (in_lebesgue k p))
Proof
    rw [converge_LP_def, LIM_SEQUENTIALLY, dist]
 >> EQ_TAC >> RW_TAC std_ss []
 >| [ (* goal 1 (of 4) *)
      Know ‘expectation p (\x. abs (Y n x) powr k) =
            expectation p (\x. abs (X n x) powr k)’
      >- (MATCH_MP_TAC expectation_cong >> rw []) \\
      DISCH_THEN (ASM_REWRITE_TAC o wrap),
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      Q.EXISTS_TAC ‘N’ >> rw [] \\
      Know ‘expectation p (\x. abs (Y n x - Z x) powr k) =
            expectation p (\x. abs (X n x - Z x) powr k)’
      >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 3 (of 4) *)
      Know ‘expectation p (\x. abs (X n x) powr k) =
            expectation p (\x. abs (Y n x) powr k)’
      >- (MATCH_MP_TAC expectation_cong >> rw []) \\
      DISCH_THEN (ASM_REWRITE_TAC o wrap),
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      Q.EXISTS_TAC ‘N’ >> rw [] \\
      Know ‘expectation p (\x. abs (X n x - Z x) powr k) =
            expectation p (\x. abs (Y n x - Z x) powr k)’
      >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] ]
QED

(*
Theorem WLLN_uncorrelated_L2 :

    has been moved to examples/probability/large_numberTheory with improved statements.
 *)

Theorem converge_AE_to_zero' :
    !p X Y Z. prob_space p /\ (!n. real_random_variable (X n) p) /\
              real_random_variable Y p /\
             (!n x. x IN p_space p ==> Z n x = X n x - Y x) ==>
             ((X --> Y) (almost_everywhere p) <=> (Z --> (\x. 0)) (almost_everywhere p))
Proof
    rw [converge_AE_to_zero]
 >> MATCH_MP_TAC converge_AE_cong
 >> Q.EXISTS_TAC ‘0’ >> rw []
QED

Theorem converge_PR_to_zero' :
    !p X Y Z. prob_space p /\ (!n. real_random_variable (X n) p) /\
              real_random_variable Y p /\
             (!n x. x IN p_space p ==> Z n x = X n x - Y x) ==>
             ((X --> Y) (in_probability p) <=> (Z --> (\x. 0)) (in_probability p))
Proof
    rw [converge_PR_to_zero]
 >> MATCH_MP_TAC converge_PR_cong
 >> Q.EXISTS_TAC ‘0’ >> rw []
QED

Theorem converge_AE_alt_shift :
    !D p X Y. (X               --> Y) (almost_everywhere p) <=>
              ((\n. X (n + D)) --> Y) (almost_everywhere p)
Proof
    RW_TAC std_ss [converge_AE_def, AE_DEF, GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]
 >> EQ_TAC >> rw [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘N’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!x. x IN m_space p /\ x NOTIN N ==> P` (MP_TAC o (Q.SPEC `x`)) \\
      RW_TAC std_ss [] \\
      rename1 `z IN null_set p` \\
      Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`)) >> RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘N’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘D + n’)) >> rw [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `N` >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!x. x IN m_space p /\ x NOTIN N ==> P` (MP_TAC o (Q.SPEC `x`)) \\
      RW_TAC std_ss [] \\
      rename1 `z IN null_set p` \\
      Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`)) >> RW_TAC std_ss [] \\
      Q.EXISTS_TAC `D + N` >> rpt STRIP_TAC \\
     ‘N <= n - D’ by rw [] \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n - D’)) >> rw [] ]
QED

Theorem converge_PR_alt_shift :
    !D p X Y. (X               --> Y) (in_probability p) <=>
              ((\n. X (n + D)) --> Y) (in_probability p)
Proof
    RW_TAC std_ss [converge_PR_def, LIM_SEQUENTIALLY, dist]
 >> EQ_TAC >> RW_TAC std_ss [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      rename1 `E <> PosInf` \\
      Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` (MP_TAC o (Q.SPEC `E`)) \\
      RW_TAC std_ss [] \\
      rename1 `0 < e` (* this changes the last matching assumption *) \\
      Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`)) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘N’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n + D’)) \\
      RW_TAC arith_ss [],
      (* goal 2 (of 2) *)
      rename1 `E <> PosInf` \\
      Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` (MP_TAC o (Q.SPEC `E`)) \\
      RW_TAC std_ss [] \\
      rename1 `0 < e` (* this changes the last matching assumption *) \\
      Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`)) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘N + D’ >> RW_TAC std_ss [] \\
      ‘N <= n - D’ by rw [] \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n - D’)) \\
      RW_TAC arith_ss [] ]
QED

(* |- !p X Y. ((\n. X (SUC n)) --> Y) (almost_everywhere p) ==>
              (X               --> Y) (almost_everywhere p)
 *)
Theorem converge_AE_shift =
        converge_AE_alt_shift |> (Q.SPECL [‘1’, ‘p’, ‘X’, ‘Y’])
                              |> (snd o EQ_IMP_RULE)
                              |> (REWRITE_RULE [GSYM ADD1])
                              |> Q.GENL [‘p’, ‘X’, ‘Y’]

(* |- !p X Y. ((\n. X (SUC n)) --> Y) (in_probability p) ==>
              (X               --> Y) (in_probability p)
 *)
Theorem converge_PR_shift =
        converge_PR_alt_shift |> (Q.SPECL [‘1’, ‘p’, ‘X’, ‘Y’])
                              |> (snd o EQ_IMP_RULE)
                              |> (REWRITE_RULE [GSYM ADD1])
                              |> Q.GENL [‘p’, ‘X’, ‘Y’]

Theorem converge_PR_add_to_zero :
    !p X Y. prob_space p /\
           (!n. real_random_variable (X n) p) /\
           (!n. real_random_variable (Y n) p) /\
           (X --> (\x. 0)) (in_probability p) /\
           (Y --> (\x. 0)) (in_probability p) ==>
       ((\n x. X n x + Y n x) --> (\x. 0)) (in_probability p)
Proof
    rw [converge_PR_def, LIM_SEQUENTIALLY, dist]
 >> rename1 ‘0 < (E :real)’ (* the last assumption with ‘e'’ is affected *)
 >> ‘e <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> Know `0 < e / 2`
 >- (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
                     [extreal_of_num_def] \\
     MATCH_MP_TAC lt_div >> RW_TAC real_ss [])
 >> DISCH_TAC
 >> Know ‘e / 2 <> PosInf’
 >- (‘?r. e = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_of_num_def, extreal_not_infty, extreal_div_eq, GSYM ne_02])
 >> DISCH_TAC
 >> Know ‘0 < E / 2’
 >- (MATCH_MP_TAC REAL_LT_DIV >> rw [])
 >> DISCH_TAC
 >> NTAC 2 (Q.PAT_X_ASSUM ‘!e. 0 < e /\ e <> PosInf ==> P’ (MP_TAC o (Q.SPEC ‘e / 2’)))
 >> RW_TAC std_ss []
 >> NTAC 2 (Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘E / 2’)))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘MAX N N'’
 >> rw [MAX_LE]
 >> NTAC 2 (Q.PAT_X_ASSUM ‘!n. _ <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’)))
 >> RW_TAC std_ss []
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 (* stage work *)
 >> Know `!Z b. real_random_variable Z p ==>
                {x | x IN p_space p /\ b < abs (Z x)} IN events p`
 >- (rpt GEN_TAC >> DISCH_TAC \\
    `{x | x IN p_space p /\ b < abs (Z x)} =
      p_space p DIFF {x | x IN p_space p /\ abs (Z x) <= b}`
        by (RW_TAC set_ss [Once EXTENSION, GSYM extreal_lt_def] \\
            METIS_TAC []) >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> art [abs_bounds] \\
    `{x | x IN p_space p /\ -b <= Z x /\ Z x <= b} =
     ({x | -b <= Z x} INTER p_space p) INTER ({x | Z x <= b} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER \\
     fs [real_random_variable, events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘A = {x | x IN p_space p /\ e / 2 < abs (X n x)}’
 >> Q.ABBREV_TAC ‘B = {x | x IN p_space p /\ e / 2 < abs (Y n x)}’
 (* simplify X-related assumptions *)
 >> Know ‘A IN events p’
 >- (Q.UNABBREV_TAC ‘A’ >> FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Know `abs (real (prob p A)) = real (prob p A)`
 >- (‘prob p A <> PosInf /\ prob p A <> NegInf’ by METIS_TAC [PROB_FINITE] \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def] \\
     MATCH_MP_TAC PROB_POSITIVE >> rw [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> `real (prob p A) < E / 2 <=> prob p A < Normal (E / 2)`
       by (METIS_TAC [PROB_FINITE, normal_real, extreal_lt_eq])
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 (* simplify Y-related assumptions *)
 >> Know ‘B IN events p’
 >- (Q.UNABBREV_TAC ‘B’ >> FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Know `abs (real (prob p B)) = real (prob p B)`
 >- (‘prob p B <> PosInf /\ prob p B <> NegInf’ by METIS_TAC [PROB_FINITE] \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def] \\
     MATCH_MP_TAC PROB_POSITIVE >> rw [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> `real (prob p B) < E / 2 <=> prob p B < Normal (E / 2)`
       by (METIS_TAC [PROB_FINITE, normal_real, extreal_lt_eq])
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> ‘A UNION B IN events p’ by PROVE_TAC [EVENTS_UNION]
 (* simplify goal *)
 >> Know ‘!n. real_random_variable (\x. X n x + Y n x) p’
 >- (Q.X_GEN_TAC ‘i’ \\
     MATCH_MP_TAC real_random_variable_add >> art[])
 >> DISCH_TAC
 >> Know ‘{x | x IN p_space p /\ e < abs (X n x + Y n x)} IN events p’
 >- (FIRST_X_ASSUM HO_MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Know ‘abs (real (prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)})) =
              (real (prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)}))’
 >- (‘prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)} <> PosInf /\
      prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)} <> NegInf’
        by METIS_TAC [PROB_FINITE] \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def] \\
     MATCH_MP_TAC PROB_POSITIVE >> rw [])
 >> Rewr'
 >> ‘real (prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)}) < E <=>
           prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)} < Normal E’
      by (METIS_TAC [PROB_FINITE, normal_real, extreal_lt_eq])
 >> POP_ORW
 (* final stage *)
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘prob p (A UNION B)’
 >> CONJ_TAC
 >- (MATCH_MP_TAC PROB_INCREASING \\
     rw [Abbr ‘A’, Abbr ‘B’, SUBSET_DEF] \\
     SPOSE_NOT_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [extreal_lt_def])) \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Know ‘abs (X n x + Y n x) <= e / 2 + e / 2’
     >- (MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC ‘abs (X n x) + abs (Y n x)’ \\
         CONJ_TAC >- (MATCH_MP_TAC abs_triangle >> rw []) \\
         MATCH_MP_TAC le_add2 >> art []) \\
     Suff ‘e / 2 + e / 2 = e’ >- rw [GSYM extreal_lt_def] \\
     REWRITE_TAC [half_double])
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘prob p A + prob p B’
 >> CONJ_TAC
 >- (MATCH_MP_TAC PROB_SUBADDITIVE >> art [])
 >> Suff ‘Normal E = Normal (E / 2) + Normal (E / 2)’
 >- (Rewr' >> MATCH_MP_TAC lt_add2 >> art [])
 >> rw [extreal_add_def]
 >> REWRITE_TAC [REAL_HALF_DOUBLE]
QED

Theorem converge_PR_add :
    !p X Y A B. prob_space p /\
               (!n. real_random_variable (X n) p) /\
                real_random_variable A p /\ (X --> A) (in_probability p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable B p /\ (Y --> B) (in_probability p) ==>
       ((\n x. X n x + Y n x) --> (\x. A x + B x)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> Know ‘(X --> A) (in_probability p) <=>
          ((\n x. X n x - A x) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘(Y --> B) (in_probability p) <=>
          ((\n x. Y n x - B x) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘((\n x. X n x + Y n x) --> (\x. A x + B x)) (in_probability p) <=>
          ((\n x. X n x + Y n x - (A x + B x)) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero' >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC real_random_variable_add >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC real_random_variable_add >> art [] ])
 >> Rewr'
 >> Know ‘((\n x. (X n x - A x) + (Y n x - B x)) --> (\x. 0)) (in_probability p)’
 >- (HO_MATCH_MP_TAC converge_PR_add_to_zero >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC real_random_variable_sub >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC real_random_variable_sub >> art [] ])
 >> DISCH_TAC
 >> Suff ‘((\n x. X n x + Y n x - (A x + B x)) --> (\x. 0)) (in_probability p) <=>
          ((\n x. X n x - A x + (Y n x - B x)) --> (\x. 0)) (in_probability p)’
 >- DISCH_THEN (art o wrap)
 >> MATCH_MP_TAC converge_PR_cong
 >> Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss []
 >> FULL_SIMP_TAC std_ss [real_random_variable_def]
 >> ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?c. A x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?d. B x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_add_def, extreal_sub_def, extreal_11]
 >> REAL_ARITH_TAC
QED

Theorem converge_PR_ainv_to_zero :
    !p X. (X --> (\x. 0)) (in_probability p) ==>
          ((\n x. -X n x) --> (\x. 0)) (in_probability p)
Proof
    rw [converge_PR_def, LIM_SEQUENTIALLY, dist]
 >> Q.PAT_X_ASSUM ‘!e. 0 < e /\ e <> PosInf => P’ (MP_TAC o (Q.SPEC ‘e’))
 >> RW_TAC std_ss []
 >> rename1 ‘0 < (E :real)’
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘E’))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘N’
 >> RW_TAC std_ss [abs_neg_eq]
QED

Theorem converge_PR_ainv :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p /\
            (X --> Y) (in_probability p) ==>
         ((\n x. -X n x) --> (\x. -Y x)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> Know ‘(X --> Y) (in_probability p) <=>
          ((\n x. X n x - Y x) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘((\n x. -X n x) --> (\x. -Y x)) (in_probability p) <=>
          ((\n x. (\n x. -X n x) n x - (\x. -Y x) x) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero >> rw [] >| (* 2 subgoals *)
     [ MATCH_MP_TAC real_random_variable_ainv >> art [],
       MATCH_MP_TAC real_random_variable_ainv >> art [] ])
 >> Rewr'
 >> BETA_TAC
 >> Know ‘((\n x. -X n x - -Y x) --> (\x. 0)) (in_probability p) <=>
          ((\n x. -(X n x - Y x)) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_cong \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
    ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. Y x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_ainv_def, extreal_sub_def] \\
     REAL_ARITH_TAC)
 >> Rewr'
 >> HO_MATCH_MP_TAC converge_PR_ainv_to_zero >> rw []
 >> MATCH_MP_TAC real_random_variable_sub >> art []
QED

Theorem converge_PR_sub :
    !p X Y A B. prob_space p /\
               (!n. real_random_variable (X n) p) /\
                real_random_variable A p /\ (X --> A) (in_probability p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable B p /\ (Y --> B) (in_probability p) ==>
       ((\n x. X n x - Y n x) --> (\x. A x - B x)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘\n x. -Y n x’, ‘A’, ‘\x. -B x’] converge_PR_add)
 >> BETA_TAC >> art []
 >> Know ‘((\n x. X n x + -Y n x) --> (\x. A x + -B x)) (in_probability p) <=>
          ((\n x. X n x - Y n x) --> (\x. A x - B x)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_cong_full \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_ainv_def, extreal_add_def, extreal_sub_def] \\
       REAL_ARITH_TAC,
       (* goal 2 (of 2) *)
      ‘?c. A x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?d. B x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_ainv_def, extreal_add_def, extreal_sub_def] \\
       REAL_ARITH_TAC ])
 >> Rewr'
 >> Know ‘!n. real_random_variable (\x. -Y n x) p’
 >- (GEN_TAC >> MATCH_MP_TAC real_random_variable_ainv >> art [])
 >> Know ‘real_random_variable (\x. -B x) p’
 >- (MATCH_MP_TAC real_random_variable_ainv >> art [])
 >> Know ‘((\n x. -Y n x) --> (\x. -B x)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_ainv >> art [])
 >> RW_TAC std_ss []
QED

Theorem converge_PR_to_limit :
    !p X M m. prob_space p /\ (!n. real_random_variable (X n) p) /\
              (M --> m) sequentially /\
              ((\n x. X n x - Normal (M n)) --> (\x. 0)) (in_probability p) ==>
              (X --> (\x. Normal m)) (in_probability p)
Proof
    rpt STRIP_TAC
 (* applying converge_PR_cong_full *)
 >> Know ‘(X --> (\x. Normal m)) (in_probability p) <=>
          ((\n x. X n x - Normal (M n) + Normal (M n)) --> (\x. 0 + Normal m))
           (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_cong_full \\
     Q.EXISTS_TAC ‘0’ >> rw [sub_add_normal]) >> Rewr'
 >> HO_MATCH_MP_TAC converge_PR_add
 >> rw [real_random_variable_zero, real_random_variable_const]
 >- (HO_MATCH_MP_TAC real_random_variable_sub \\
     rw [real_random_variable_const] \\
    ‘(\x. X n x) = X n’ by METIS_TAC [] >> POP_ASSUM (art o wrap))
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’ K_TAC
 >> POP_ASSUM K_TAC (* (X n x - M n) --> 0 *)
 (* stage work, now ‘X n’ disappeared, left only M and m *)
 >> POP_ASSUM MP_TAC
 >> rw [converge_PR_def, LIM_SEQUENTIALLY, dist]
 >> ‘e <> NegInf’ by PROVE_TAC [lt_imp_le, pos_not_neginf]
 >> rename1 ‘0 < (z :real)’
 >> ‘?E. e = Normal E /\ 0 < E’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o Q.SPEC ‘E’)
 >> RW_TAC std_ss [extreal_sub_def, extreal_abs_def, extreal_lt_eq]
 >> Q.EXISTS_TAC ‘N’
 >> rpt STRIP_TAC
 >> Suff ‘{x | x IN p_space p /\ E < abs (M n - m)} = {}’
 >- rw [PROB_EMPTY, real_0]
 >> rw [Once EXTENSION, GSYM real_lte]
 >> DISJ2_TAC
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* M and m are extreal-valued. This form is used by WLLN_IID directly. *)
Theorem converge_PR_to_limit' :
    !p X M m. prob_space p /\ (!n. real_random_variable (X n) p) /\
              (!n. M n <> PosInf /\ M n <> NegInf) /\ m <> PosInf /\ m <> NegInf /\
              ((real o M) --> real m) sequentially /\
              ((\n x. X n x - M n) --> (\x. 0)) (in_probability p) ==>
              (X --> (\x. m)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> ‘?r. m = Normal r’ by METIS_TAC [extreal_cases] >> fs []
 >> MATCH_MP_TAC converge_PR_to_limit
 >> Q.EXISTS_TAC ‘real o M’ >> art []
 >> Suff ‘((\n x. X n x - Normal ((real o M) n)) --> (\x. 0)) (in_probability p) <=>
          ((\n x. X n x - M n) --> (\x. 0)) (in_probability p)’ >- rw []
 >> MATCH_MP_TAC converge_PR_cong
 >> Q.EXISTS_TAC ‘0’ >> rw [normal_real]
QED

Theorem converge_AE_add_to_zero :
    !p X Y. prob_space p /\
           (!n. real_random_variable (X n) p) /\
           (!n. real_random_variable (Y n) p) /\
           (X --> (\x. 0)) (almost_everywhere p) /\
           (Y --> (\x. 0)) (almost_everywhere p) ==>
       ((\n x. X n x + Y n x) --> (\x. 0)) (almost_everywhere p)
Proof
    rw [converge_AE_def, AE_DEF, LIM_SEQUENTIALLY, dist, real_random_variable_def,
        p_space_def]
 >> Q.EXISTS_TAC ‘N UNION N'’
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC (REWRITE_RULE [IN_APP] NULL_SET_UNION) \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> rw []
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N ==> P’ (MP_TAC o (Q.SPEC ‘x’))
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N' ==> P’ (MP_TAC o (Q.SPEC ‘x’))
 >> RW_TAC std_ss []
 >> ‘0 < e / 2’ by rw [REAL_LT_DIV]
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e / 2’))
 >> RW_TAC std_ss []
 >> rename1 ‘!n. N1 <= n ==> abs (real (Y n x)) < e / 2’
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e / 2’))
 >> RW_TAC std_ss []
 >> rename1 ‘!n. N2 <= n ==> abs (real (X n x)) < e / 2’
 >> Q.EXISTS_TAC ‘MAX N1 N2’
 >> rw [MAX_LE]
 >> Q.PAT_X_ASSUM ‘!n. N1 <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’))
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!n. N2 <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’))
 >> RW_TAC std_ss []
 >> ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> FULL_SIMP_TAC std_ss [extreal_add_def, real_normal]
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘abs a + abs b’
 >> REWRITE_TAC [ABS_TRIANGLE]
 >> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM REAL_HALF_DOUBLE]
 >> MATCH_MP_TAC REAL_LT_ADD2 >> art []
QED

Theorem converge_AE_add :
    !p X Y A B. prob_space p /\
               (!n. real_random_variable (X n) p) /\
                real_random_variable A p /\ (X --> A) (almost_everywhere p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable B p /\ (Y --> B) (almost_everywhere p) ==>
       ((\n x. X n x + Y n x) --> (\x. A x + B x)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Know ‘(X --> A) (almost_everywhere p) <=>
          ((\n x. X n x - A x) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘(Y --> B) (almost_everywhere p) <=>
          ((\n x. Y n x - B x) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘((\n x. X n x + Y n x) --> (\x. A x + B x)) (almost_everywhere p) <=>
          ((\n x. X n x + Y n x - (A x + B x)) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero' >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC real_random_variable_add >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC real_random_variable_add >> art [] ])
 >> Rewr'
 >> Know ‘((\n x. (X n x - A x) + (Y n x - B x)) --> (\x. 0)) (almost_everywhere p)’
 >- (HO_MATCH_MP_TAC converge_AE_add_to_zero >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC real_random_variable_sub >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC real_random_variable_sub >> art [] ])
 >> DISCH_TAC
 >> Suff ‘((\n x. X n x + Y n x - (A x + B x)) --> (\x. 0)) (almost_everywhere p) <=>
          ((\n x. X n x - A x + (Y n x - B x)) --> (\x. 0)) (almost_everywhere p)’
 >- DISCH_THEN (art o wrap)
 >> MATCH_MP_TAC converge_AE_cong
 >> Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss []
 >> FULL_SIMP_TAC std_ss [real_random_variable_def]
 >> ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?c. A x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?d. B x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_add_def, extreal_sub_def, extreal_11]
 >> REAL_ARITH_TAC
QED

Theorem converge_AE_ainv_to_zero :
    !p X. (!n. real_random_variable (X n) p) /\
          (X --> (\x. 0)) (almost_everywhere p) ==>
          ((\n x. -X n x) --> (\x. 0)) (almost_everywhere p)
Proof
    rw [converge_AE_def, AE_DEF, LIM_SEQUENTIALLY, dist,
        real_random_variable_def, p_space_def]
 >> Q.EXISTS_TAC ‘N’ >> rw []
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N ==> P’ (MP_TAC o (Q.SPEC ‘x’))
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’))
 >> RW_TAC std_ss []
 >> rename1 ‘!n. M <= n ==> abs (real (X n x)) < e’
 >> Q.EXISTS_TAC ‘M’ >> rw []
 >> Q.PAT_X_ASSUM ‘!n. M <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’))
 >> RW_TAC std_ss []
 >> ‘?r. X n x = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> FULL_SIMP_TAC std_ss [extreal_ainv_def, real_normal, ABS_NEG]
QED

Theorem converge_AE_ainv :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p /\
            (X --> Y) (almost_everywhere p) ==>
         ((\n x. -X n x) --> (\x. -Y x)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Know ‘(X --> Y) (almost_everywhere p) <=>
          ((\n x. X n x - Y x) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘((\n x. -X n x) --> (\x. -Y x)) (almost_everywhere p) <=>
          ((\n x. (\n x. -X n x) n x - (\x. -Y x) x) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero >> rw [] >| (* 2 subgoals *)
     [ MATCH_MP_TAC real_random_variable_ainv >> art [],
       MATCH_MP_TAC real_random_variable_ainv >> art [] ])
 >> Rewr'
 >> BETA_TAC
 >> Know ‘((\n x. -X n x - -Y x) --> (\x. 0)) (almost_everywhere p) <=>
          ((\n x. -(X n x - Y x)) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
    ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. Y x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_ainv_def, extreal_sub_def] \\
     REAL_ARITH_TAC)
 >> Rewr'
 >> HO_MATCH_MP_TAC converge_AE_ainv_to_zero >> rw []
 >> MATCH_MP_TAC real_random_variable_sub >> art []
QED

Theorem converge_AE_sub :
    !p X Y A B. prob_space p /\
               (!n. real_random_variable (X n) p) /\
                real_random_variable A p /\ (X --> A) (almost_everywhere p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable B p /\ (Y --> B) (almost_everywhere p) ==>
       ((\n x. X n x - Y n x) --> (\x. A x - B x)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘\n x. -Y n x’, ‘A’, ‘\x. -B x’] converge_AE_add)
 >> BETA_TAC >> art []
 >> Know ‘((\n x. X n x + -Y n x) --> (\x. A x + -B x)) (almost_everywhere p) <=>
          ((\n x. X n x - Y n x) --> (\x. A x - B x)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong_full \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_ainv_def, extreal_add_def, extreal_sub_def] \\
       REAL_ARITH_TAC,
       (* goal 2 (of 2) *)
      ‘?c. A x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?d. B x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_ainv_def, extreal_add_def, extreal_sub_def] \\
       REAL_ARITH_TAC ])
 >> Rewr'
 >> Know ‘!n. real_random_variable (\x. -Y n x) p’
 >- (GEN_TAC >> MATCH_MP_TAC real_random_variable_ainv >> art [])
 >> Know ‘real_random_variable (\x. -B x) p’
 >- (MATCH_MP_TAC real_random_variable_ainv >> art [])
 >> Know ‘((\n x. -Y n x) --> (\x. -B x)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_ainv >> art [])
 >> RW_TAC std_ss []
QED

Theorem converge_AE_to_limit :
    !p X M m. prob_space p /\ (!n. real_random_variable (X n) p) /\
              (M --> m) sequentially /\
              ((\n x. X n x - Normal (M n)) --> (\x. 0)) (almost_everywhere p) ==>
              (X --> (\x. Normal m)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 (* applying converge_PR_cong_full *)
 >> Know ‘(X --> (\x. Normal m)) (almost_everywhere p) <=>
          ((\n x. X n x - Normal (M n) + Normal (M n)) --> (\x. 0 + Normal m))
           (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong_full \\
     Q.EXISTS_TAC ‘0’ >> rw [sub_add_normal]) >> Rewr'
 >> HO_MATCH_MP_TAC converge_AE_add
 >> rw [real_random_variable_zero, real_random_variable_const]
 >- (HO_MATCH_MP_TAC real_random_variable_sub \\
     rw [real_random_variable_const] \\
    ‘(\x. X n x) = X n’ by METIS_TAC [] >> POP_ASSUM (art o wrap))
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’ K_TAC
 >> POP_ASSUM K_TAC (* (X n x - M n) --> 0 *)
 (* stage work, now ‘X n’ disappeared, left only M and m *)
 >> POP_ASSUM MP_TAC
 >> rw [converge_AE_def, AE_DEF, null_set_def, LIM_SEQUENTIALLY, dist]
 >> Q.EXISTS_TAC ‘{}’
 >> FULL_SIMP_TAC std_ss [prob_space_def]
 >> ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE, MEASURE_EMPTY]
QED

(* M and m are extreal-valued. This form is used by WLLN_IID directly. *)
Theorem converge_AE_to_limit' :
    !p X M m. prob_space p /\ (!n. real_random_variable (X n) p) /\
              (!n. M n <> PosInf /\ M n <> NegInf) /\ m <> PosInf /\ m <> NegInf /\
              ((real o M) --> real m) sequentially /\
              ((\n x. X n x - M n) --> (\x. 0)) (almost_everywhere p) ==>
              (X --> (\x. m)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> ‘?r. m = Normal r’ by METIS_TAC [extreal_cases] >> fs []
 >> MATCH_MP_TAC converge_AE_to_limit
 >> Q.EXISTS_TAC ‘real o M’ >> art []
 >> Suff ‘((\n x. X n x - Normal ((real o M) n)) --> (\x. 0)) (almost_everywhere p) <=>
          ((\n x. X n x - M n) --> (\x. 0)) (almost_everywhere p)’ >- rw []
 >> MATCH_MP_TAC converge_AE_cong
 >> Q.EXISTS_TAC ‘0’ >> rw [normal_real]
QED

(* Kolmogorov's two remarkable inequalities. This is the first one.

   This is Theorem 5.3.1 [2, p.121], see also [5, p.7]

   Remark. If we replace the ‘max_fn_seq (\i. abs o Z i) (SUC n) x’ in the formula
   by ‘abs (Z (SUC n))’, this becomes a simple case of Chebyshev's inequality, of
   which it is thus an essential improvement.

   NOTE: Z(0) = X(0), Z(1) = X(0) + X(1), ...
 *)

Theorem events_max_fn_seq[local] :
    !p Z. prob_space p /\ (!n. real_random_variable (Z n) p) ==>
          !e n. {x | x IN p_space p /\ e < max_fn_seq (\i. abs o Z i) n x} IN events p
Proof
    RW_TAC std_ss [prob_space_def, p_space_def, events_def, real_random_variable]
 >> Q.ABBREV_TAC ‘f = max_fn_seq (\i. abs o Z i) n’
 >> ‘{x | x IN m_space p /\ e < f x} = {x | e < f x} INTER m_space p’ by SET_TAC []
 >> POP_ORW
 >> Suff ‘f IN measurable (m_space p,measurable_sets p) Borel’
 >- (METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE, measure_space_def])
 >> Q.UNABBREV_TAC ‘f’
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX_FN_SEQ >> rw []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS' >> rw []
QED

Theorem events_max_fn_seq'[local] :
    !p Z. prob_space p /\ (!n. real_random_variable (Z n) p) ==>
          !e n. {x | x IN p_space p /\ max_fn_seq (\i. abs o Z i) n x <= e} IN events p
Proof
    RW_TAC std_ss [prob_space_def, p_space_def, events_def, real_random_variable]
 >> Q.ABBREV_TAC ‘f = max_fn_seq (\i. abs o Z i) n’
 >> ‘{x | x IN m_space p /\ f x <= e} = {x | f x <= e} INTER m_space p’ by SET_TAC []
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
      (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count1 n))
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
           real_random_variable (\x. SIGMA (\i. X i x) (count1 n)) p’
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
 (* The range ‘count1 n’ indicates from a(0) to a(N) *)
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
           finite_second_moments p (\x. SIGMA (\i. X i x) (count1 n))’
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
  (* choose J such that ‘count (SUC N) = J UNION (count1 n)’ *)
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
        ‘count (SUC N) = J UNION (count1 n)’ by rw [Abbr ‘J’, Once EXTENSION] \\
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
         but ‘integrable p (X n)’ must be put first to make sure ‘expectation p (X n)’
         exists and is finite.
 *)
Theorem Kolmogorov_maximal_inequality_2 :
    !p X Z A.
       prob_space p /\ (!n. real_random_variable (X n) p) /\
       indep_vars p X (\n. Borel) UNIV /\
      (!n. integrable p (X n)) /\ A <> PosInf /\
      (!n x. x IN p_space p ==> abs (X n x - expectation p (X n)) <= A) /\
      (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count1 n))
   ==> !e N. 0 < e /\ e <> PosInf /\ 0 < variance p (Z N) ==>
             prob p {x | x IN p_space p /\ max_fn_seq (\i. abs o Z i) N x <= e}
          <= (2 * A + 4 * e) pow 2 / variance p (Z N)
Proof
    rpt STRIP_TAC
 (* impossible case: A < 0 *)
 >> ‘A < 0 \/ 0 <= A’ by PROVE_TAC [let_total]
 >- (‘?x. x IN p_space p’ by METIS_TAC [PROB_SPACE_NOT_EMPTY, MEMBER_NOT_EMPTY] \\
     ‘abs (X 0 x - expectation p (X 0)) <= A’ by PROVE_TAC [] \\
     ‘0 <= abs (X 0 x - expectation p (X 0))’ by PROVE_TAC [abs_pos] \\
     ‘abs (X 0 x - expectation p (X 0)) < 0’ by PROVE_TAC [let_trans] \\
     METIS_TAC [let_antisym])
 >> ‘A <> NegInf’ by PROVE_TAC [pos_not_neginf]
 >> Know ‘!n. finite_second_moments p (X n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC bounded_imp_finite_second_moments' >> art [] \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [real_random_variable_def] \\
    ‘?a. A = Normal a’ by METIS_TAC [extreal_cases] \\
     Q.EXISTS_TAC ‘a’ >> rw [])
 >> DISCH_TAC
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘real_random_variable (Z n) p <=>
           real_random_variable (\x. SIGMA (\i. X i x) (count1 n)) p’
     >- (MATCH_MP_TAC real_random_variable_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC real_random_variable_sum >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘M = \n. {x | x IN p_space p /\ max_fn_seq (\i. abs o Z i) n x <= e}’
 >> ‘!n. M n IN events p’ by METIS_TAC [events_max_fn_seq']
 >> ‘!n. M (SUC n) SUBSET M n’
       by (rw [Abbr ‘M’, SUBSET_DEF, max_fn_seq_def, max_le])
 >> Know ‘!m n. m <= n ==> M n SUBSET M m’
 >- (rpt GEN_TAC \\
     Induct_on ‘n - m’ >> rw [] (* 2 subgoals *)
     >- (‘m = n’ by rw [] >> METIS_TAC [SUBSET_REFL]) \\
    ‘0 < n - m’ by rw [] \\
    ‘0 < n’ by rw [] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘M (PRE n)’ \\
     CONJ_TAC >- (‘n = SUC (PRE n)’ by rw [] >> METIS_TAC []) \\
     FIRST_X_ASSUM irule >> rw [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!n. M (SUC n) SUBSET M n’ K_TAC
 (* start working on the goal *)
 >> simp []
 (* trivial case: A = 0 (conflict with ‘0 < variance p (Z N)’) *)
 >> ‘A = 0 \/ 0 < A’ by PROVE_TAC [le_lt]
 >- (POP_ASSUM (fs o wrap) \\
     Suff ‘variance p (Z N) = 0’ >- METIS_TAC [lt_le] \\
     Know ‘variance p (Z N) = variance p (\x. SIGMA (\n. X n x) (count1 N))’
     >- (MATCH_MP_TAC variance_cong >> rw []) >> Rewr' \\
     Know ‘variance p (\x. SIGMA (\n. X n x) (count1 N)) =
           SIGMA (\n. variance p (X n)) (count1 N)’
     >- (MATCH_MP_TAC variance_sum' >> rw [] \\
         MATCH_MP_TAC total_imp_pairwise_indep_vars >> simp [SIGMA_ALGEBRA_BOREL] \\
         fs [real_random_variable_def] \\
         MATCH_MP_TAC indep_vars_subset \\
         Q.EXISTS_TAC ‘univ(:num)’ >> rw []) >> Rewr' \\
     REWRITE_TAC [variance_alt] \\
     Know ‘!n. expectation p (\x. (X n x - expectation p (X n)) pow 2) =
               expectation p (\x. 0 pow 2)’
     >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
     rw [zero_pow, expectation_zero, EXTREAL_SUM_IMAGE_ZERO])
 >> Know ‘!n. finite_second_moments p (Z n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘finite_second_moments p (Z n) <=>
           finite_second_moments p (\x. SIGMA (\i. X i x) (count1 n))’
     >- (MATCH_MP_TAC finite_second_moments_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC finite_second_moments_sum >> rw [])
 >> DISCH_TAC
 >> ‘prob p (M N) = 0 \/ 0 < prob p (M N)’ by METIS_TAC [PROB_POSITIVE, le_lt]
 (* another trivial case: prob p (M N) = 0 *)
 >- (POP_ORW \\
    ‘variance p (Z N) <> PosInf’
       by METIS_TAC [lt_infty, finite_second_moments_eq_finite_variance] \\
    ‘variance p (Z N) <> NegInf’ by METIS_TAC [lt_imp_le, pos_not_neginf] \\
    ‘?r. 0 < r /\ variance p (Z N) = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
     MATCH_MP_TAC le_div >> rw [le_pow2])
 (* stage work *)
 >> Know ‘!n. n <= N ==> 0 < prob p (M n)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘prob p (M N)’ >> art [] \\
     MATCH_MP_TAC PROB_INCREASING >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘0 < prob p (M N)’ K_TAC
 >> Q.ABBREV_TAC ‘D = \n. if n = 0 then p_space p else M (n - 1) DIFF M n’
 >> Know ‘!n. D n IN events p’
 >- (rw [Abbr ‘D’, EVENTS_SPACE] \\
     MATCH_MP_TAC EVENTS_DIFF >> art [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘Y = \n x. X n x - expectation p (X n)’
 >> FULL_SIMP_TAC bool_ss []
 >> Know ‘!n. real_random_variable (Y n) p’
 >- (rw [Abbr ‘Y’] \\
     HO_MATCH_MP_TAC real_random_variable_sub \\
    ‘(\x. X n x) = X n’ by METIS_TAC [] >> rw [] \\
     MATCH_MP_TAC real_random_variable_const >> art [] \\
     METIS_TAC [integrable_imp_finite_expectation])
 >> DISCH_TAC
 >> Know ‘!n. finite_second_moments p (Y n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC bounded_imp_finite_second_moments \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
    ‘?r. A = Normal r’ by METIS_TAC [extreal_cases] \\
     Q.EXISTS_TAC ‘r’ >> rw [])
 >> DISCH_TAC
 >> ‘!n. integrable p (Y n)’ by PROVE_TAC [finite_second_moments_imp_integrable]
 >> ‘!n x. x IN p_space p ==> Y n x <> NegInf /\ Y n x <> PosInf’
       by FULL_SIMP_TAC std_ss [real_random_variable_def]
 >> Q.ABBREV_TAC ‘W = \n x. SIGMA (\i. Y i x) (count1 n)’
 >> Know ‘!n. finite_second_moments p (W n)’
 >- (rw [Abbr ‘W’] >> MATCH_MP_TAC finite_second_moments_sum >> rw [])
 >> DISCH_TAC
 >> Know ‘!n. real_random_variable (W n) p’
 >- (rw [Abbr ‘W’] >> MATCH_MP_TAC real_random_variable_sum >> rw [])
 >> DISCH_TAC
 >> ‘!n. integrable p (W n)’ by PROVE_TAC [finite_second_moments_imp_integrable]
 >> Know ‘!k. integrable p (\x. W k x * indicator_fn (M k) x)’
 >- (Q.X_GEN_TAC ‘k’ \\
     MATCH_MP_TAC integrable_mul_indicator >> fs [events_def, prob_space_def])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘a = \k. inv (prob p (M k)) *
                          integral p (\x. W k x * indicator_fn (M k) x)’
 >> Know ‘!k. k <= N ==> a k <> NegInf /\ a k <> PosInf’
 >- (Q.X_GEN_TAC ‘k’ >> DISCH_TAC >> simp [Abbr ‘a’] \\
    ‘?r. integral p (\x. W k x * indicator_fn (M k) x) = Normal r’
       by METIS_TAC [integrable_normal_integral, prob_space_def] >> POP_ORW \\
    ‘?z. 0 < z /\ prob p (M k) = Normal z’
       by METIS_TAC [prob_normal, extreal_lt_eq, extreal_of_num_def] >> POP_ORW \\
    ‘z <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     rw [extreal_inv_eq, extreal_mul_def, extreal_not_infty])
 >> DISCH_TAC
 >> ‘!n x. x IN p_space p ==> W n x <> NegInf /\ W n x <> PosInf’
       by PROVE_TAC [real_random_variable_def]
 >> ‘measure_space p /\ measure p (m_space p) < PosInf’
      by (fs [prob_space_def, p_space_def, extreal_of_num_def, lt_infty])
 (* A key result of ‘a’ *)
 >> Know ‘!k. k <= N ==>
              expectation p (\x. (W k x - a k) * indicator_fn (M k) x) = 0’
 >- (Q.X_GEN_TAC ‘k’ >> DISCH_TAC \\
     Know ‘expectation p (\x. (W k x - a k) * indicator_fn (M k) x) =
           expectation p (\x. W k x * indicator_fn (M k) x -
                                 a k * indicator_fn (M k) x)’
     >- (MATCH_MP_TAC expectation_cong >> rw [] \\
         MATCH_MP_TAC sub_rdistrib \\
        ‘?r. indicator_fn (M k) x = Normal r’ by METIS_TAC [indicator_fn_normal] \\
         rw [extreal_not_infty]) >> Rewr' \\
     Know ‘expectation p (\x. W k x * indicator_fn (M k) x - a k * indicator_fn (M k) x) =
           expectation p (\x. W k x * indicator_fn (M k) x) -
           expectation p (\x.   a k * indicator_fn (M k) x)’
     >- (REWRITE_TAC [expectation_def] \\
         HO_MATCH_MP_TAC integral_sub' >> rw [] \\
         HO_MATCH_MP_TAC integrable_mul_indicator >> fs [events_def] \\
        ‘?r. a k = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         MATCH_MP_TAC integrable_const >> art []) >> Rewr' \\
     MATCH_MP_TAC sub_eq_0 >> rw [integrable_imp_finite_expectation] \\
     Know ‘expectation p (\x. a k * indicator_fn (M k) x) =
           a k * expectation p (\x. indicator_fn (M k) x)’
     >- (‘?r. a k = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         HO_MATCH_MP_TAC expectation_cmul >> art [] \\
        ‘(\x. indicator_fn (M k) x) = indicator_fn (M k)’ by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC integrable_indicator \\
         Suff ‘prob p (M k) < PosInf’ >- fs [events_def, prob_def] \\
        ‘?r. prob p (M k) = Normal r’ by METIS_TAC [prob_normal] \\
         rw [lt_infty, extreal_not_infty]) >> Rewr' \\
    ‘(\x. indicator_fn (M k) x) = indicator_fn (M k)’ by METIS_TAC [] >> POP_ORW \\
     rw [expectation_indicator, expectation_def] \\
    ‘a k * prob p (M k) = prob p (M k) * a k’ by rw [mul_comm] >> POP_ORW \\
     simp [Abbr ‘a’, mul_assoc] \\
     Suff ‘prob p (M k) * inv (prob p (M k)) = 1’ >- rw [] \\
     ONCE_REWRITE_TAC [mul_comm] \\
     MATCH_MP_TAC mul_linv_pos >> rw [] \\
    ‘?r. prob p (M k) = Normal r’ by METIS_TAC [prob_normal] \\
     rw [extreal_not_infty])
 >> DISCH_TAC
 (* applying pos_fn_integral_disjoint_sets *)
 >> Q.ABBREV_TAC ‘Q = \n x. (W n x - a n) pow 2’
 >> Know ‘!k. k < N ==> pos_fn_integral p (\x. Q (SUC k) x * indicator_fn (M k) x) =
                        pos_fn_integral p (\x. Q (SUC k) x * indicator_fn (M (SUC k)) x) +
                        pos_fn_integral p (\x. Q (SUC k) x * indicator_fn (D (SUC k)) x)’
 >- (rpt STRIP_TAC \\
     Know ‘M k = M (SUC k) UNION D (SUC k)’
     >- (rw [Abbr ‘D’] \\
         Q.PAT_X_ASSUM ‘!m n. m <= n ==> M n SUBSET M m’ (MP_TAC o (Q.SPECL [‘k’, ‘SUC k’])) \\
         simp [] >> SET_TAC []) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_disjoint_sets \\
     FULL_SIMP_TAC std_ss [events_def] \\
     rw [Abbr ‘Q’, le_pow2] >- rw [DISJOINT_ALT, Abbr ‘D’] \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB' \\
     qexistsl_tac [‘W (SUC k)’, ‘\x. a (SUC k)’] >> simp [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> simp []) \\
     Q.PAT_X_ASSUM ‘!n. integrable p (W n)’ MP_TAC \\
     rw [integrable_def])
 >> DISCH_TAC
 >> Know ‘!k x. x IN p_space p /\ k < N ==>
                W (SUC k) x - a (SUC k) =
               (W k x - a k) + (a k - a (SUC k)) + Y (SUC k) x’
 >- (rpt STRIP_TAC \\
     Know ‘W (SUC k) x = W k x + Y (SUC k) x’
     >- (rw [Abbr ‘W’] \\
         MATCH_MP_TAC (BETA_RULE (Q.SPECL [‘\i. Y i x’, ‘SUC k’]
                                          EXTREAL_SUM_IMAGE_COUNT_SUC)) \\
         rw []) >> Rewr' \\
    ‘?z1. W k x = Normal z1’       by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?z2. W (SUC k) x = Normal z2’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?z3. Y (SUC k) x = Normal z3’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?z4. a k = Normal z4’         by METIS_TAC [LT_LE, extreal_cases] >> POP_ORW \\
    ‘?z5. a (SUC k) = Normal z5’   by METIS_TAC [LESS_EQ, extreal_cases] >> POP_ORW \\
     rw [extreal_add_def, extreal_sub_def] >> REAL_ARITH_TAC)
 >> DISCH_TAC
 >>
    cheat
QED

(* This is Exercise 5.3 (3) [2, p.128], a companion of Theorem 5.3.2 under the joint
   hypotheses in Theorem 5.3.1 and 5.3.2. This is Kolmogorov’s Inequalities (b) of [5, p.7].

   A better estimate ‘(A + e) pow 2’ than ‘(2 * A + 4 * e) pow 2’ has been obtained here.
 *)
Theorem Kolmogorov_maximal_inequality_3 :
    !p X A Z.
       prob_space p /\ (!n. real_random_variable (X n) p) /\
       indep_vars p X (\n. Borel) UNIV /\
      (!n. expectation p (X n) = 0) /\ A <> PosInf /\
      (!n x. x IN p_space p ==> abs (X n x) <= A) /\
      (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count1 n))
   ==> !e N. 0 < e /\ e <> PosInf /\ 0 < variance p (Z N) ==>
             prob p {x | x IN p_space p /\ max_fn_seq (\i. abs o Z i) N x <= e}
          <= (A + e) pow 2 / variance p (Z N)
Proof
    cheat
QED

(* Or, in another equivalent form, the above theorem provides a lower bound for

   prob p {x | x IN p_space p /\ e < max_fn_seq (\i. abs o Z i) N x}

   while Kolmogorov_maximal_inequality_1 provides a upper bound: variance(Z) / e pow 2

   NOTE: when ‘variance p (Z N) = 0’, using only Kolmogorov_maximal_inequality one can
         get ‘prob p E <= 0’, and thus ‘prob p E = 0’.
 *)
Theorem Kolmogorov_maximal_inequality :
    !p X A Z.
       prob_space p /\ (!n. real_random_variable (X n) p) /\
       indep_vars p X (\n. Borel) UNIV /\
      (!n. expectation p (X n) = 0) /\ A <> PosInf /\
      (!n x. x IN p_space p ==> abs (X n x) <= A) /\
      (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count1 n))
   ==> !e N. 0 < e /\ e <> PosInf /\ 0 < variance p (Z N) ==>
             prob p {x | x IN p_space p /\ e < max_fn_seq (\i. abs o Z i) N x} IN
             {r | 1 - (A + e) pow 2 / variance p (Z N) <= r /\
                  r <= variance p (Z N) / e pow 2}
Proof
    rpt STRIP_TAC
 (* impossible case: A < 0 *)
 >> ‘A < 0 \/ 0 <= A’ by PROVE_TAC [let_total]
 >- (‘?x. x IN p_space p’ by METIS_TAC [PROB_SPACE_NOT_EMPTY, MEMBER_NOT_EMPTY] \\
     ‘abs (X 0 x) <= A’ by PROVE_TAC [] \\
     ‘0 <= abs (X 0 x)’ by PROVE_TAC [abs_pos] \\
     ‘abs (X 0 x) < 0’ by PROVE_TAC [let_trans] \\
     METIS_TAC [let_antisym])
 >> ‘A <> NegInf’ by METIS_TAC [pos_not_neginf]
 >> Know ‘!n. finite_second_moments p (X n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC bounded_imp_finite_second_moments \\
    ‘?r. A = Normal r’ by METIS_TAC [extreal_cases] \\
     fs [real_random_variable_def] >> Q.EXISTS_TAC ‘r’ >> rw [])
 >> DISCH_TAC
 >> simp [] (* eliminate {r | ... } *)
 >> reverse CONJ_TAC
 >- (irule Kolmogorov_maximal_inequality_1 >> art [] \\
     Q.EXISTS_TAC ‘X’ >> simp [])
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘real_random_variable (Z n) p <=>
           real_random_variable (\x. SIGMA (\i. X i x) (count1 n)) p’
     >- (MATCH_MP_TAC real_random_variable_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC real_random_variable_sum >> rw [])
 >> DISCH_TAC
 >> Know ‘!n. finite_second_moments p (Z n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘finite_second_moments p (Z n) <=>
           finite_second_moments p (\x. SIGMA (\i. X i x) (count1 n))’
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
