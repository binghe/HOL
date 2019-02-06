(* ------------------------------------------------------------------------- *)
(* The theory of martingales for sigma-finite measure spaces [1]             *)
(*                                                                           *)
(* Author: Chun Tian (2019)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory realTheory prim_recTheory pairTheory relationTheory
     seqTheory pred_setTheory res_quanTheory res_quanTools transcTheory
     pairTheory combinTheory realLib optionTheory real_sigmaTheory;

open hurdUtils util_probTheory extrealTheory measureTheory lebesgueTheory;

val _ = new_theory "martingale";

(* "The theory of martingales as we know it now goes back to
    Doob and most of the material of this and the following chapter can be found in
    his seminal monograph [2] from 1953.

    We want to understand martingales as an analysis tool which will be useful
    for the study of L^p- and almost everywhere convergence and, in particular,
    for the further development of measure and integration theory. Our presentation
    differs somewhat from the standard way to introduce martingales - conditional
    expectations will be defined later in Chapter 22 - but the results and their
    proofs are pretty much the usual ones."

  -- Rene L. Schilling, Measures, Integrals and Martingales [1] *)

(* ------------------------------------------------------------------------- *)
(*  Basic version of martingales (Chapter 17 of [1])                         *)
(* ------------------------------------------------------------------------- *)

val sub_sigma_algebra_def = Define
   `sub_sigma_algebra a b = sigma_algebra a /\ sigma_algebra b /\
                           (space a = space b) /\ (subsets a) SUBSET (subsets b)`;

(* sub_sigma_algebra is a partial-order between sigma-algebras *)
val SUB_SIGMA_ALGEBRA_REFL = store_thm
  ("SUB_SIGMA_ALGEBRA_REFL",
  ``!a. sigma_algebra a ==> sub_sigma_algebra a a``,
    RW_TAC std_ss [sub_sigma_algebra_def, SUBSET_REFL]);

val SUB_SIGMA_ALGEBRA_TRANS = store_thm
  ("SUB_SIGMA_ALGEBRA_TRANS",
  ``!a b c. sub_sigma_algebra a b /\ sub_sigma_algebra b c ==> sub_sigma_algebra a c``,
    RW_TAC std_ss [sub_sigma_algebra_def]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `subsets b` >> art []);

val SUB_SIGMA_ALGEBRA_ANTISYM = store_thm
  ("SUB_SIGMA_ALGEBRA_ANTISYM",
  ``!a b. sub_sigma_algebra a b /\ sub_sigma_algebra b a ==> (a = b)``,
    RW_TAC std_ss [sub_sigma_algebra_def]
 >> Q.PAT_X_ASSUM `space b = space a` K_TAC
 >> ONCE_REWRITE_TAC [GSYM SPACE]
 >> ASM_REWRITE_TAC [CLOSED_PAIR_EQ]
 >> MATCH_MP_TAC SUBSET_ANTISYM >> art []);

val SUB_SIGMA_ALGEBRA_ORDER = store_thm
  ("SUB_SIGMA_ALGEBRA_ORDER", ``Order sub_sigma_algebra``,
    RW_TAC std_ss [Order, antisymmetric_def, transitive_def]
 >- (MATCH_MP_TAC SUB_SIGMA_ALGEBRA_ANTISYM >> art [])
 >> IMP_RES_TAC SUB_SIGMA_ALGEBRA_TRANS);

val SUB_SIGMA_ALGEBRA_MEASURE_SPACE = store_thm
  ("SUB_SIGMA_ALGEBRA_MEASURE_SPACE",
  ``!m a. measure_space m /\ sub_sigma_algebra a (m_space m,measurable_sets m) ==>
          measure_space (m_space m,subsets a,measure m)``,
    RW_TAC std_ss [sub_sigma_algebra_def, space_def, subsets_def]
 >> MATCH_MP_TAC MEASURE_SPACE_RESTRICTION
 >> Q.EXISTS_TAC `measurable_sets m`
 >> simp [MEASURE_SPACE_REDUCE]
 >> METIS_TAC [SPACE]);

(* `filtration A` is the set of all filtrations of A *)
val filtration_def = Define
   `filtration A (a :num -> 'a algebra) =
      (!n. sub_sigma_algebra (a n) A) /\
      (!i j. i <= j ==> subsets (a i) SUBSET subsets (a j))`;

val FILTRATION_BOUNDED = store_thm
  ("FILTRATION_BOUNDED",
  ``!A a. filtration A a ==> !n. sub_sigma_algebra (a n) A``,
    PROVE_TAC [filtration_def]);

val FILTRATION_MONO = store_thm
  ("FILTRATION_MONO",
  ``!A a. filtration A a ==> !i j. i <= j ==> subsets (a i) SUBSET subsets (a j)``,
    PROVE_TAC [filtration_def]);

(* all sigma-algebras in `filtration A` are subset of A *)
val FILTRATION_SUBSETS = store_thm
  ("FILTRATION_SUBSETS",
  ``!A a. filtration A a ==> !n. subsets (a n) SUBSET (subsets A)``,
    RW_TAC std_ss [filtration_def, sub_sigma_algebra_def]);

val FILTRATION = store_thm
  ("FILTRATION",
  ``!A a. filtration A a = (!n. sub_sigma_algebra (a n) A) /\
                           (!n. subsets (a n) SUBSET (subsets A)) /\
                           (!i j. i <= j ==> subsets (a i) SUBSET subsets (a j))``,
    rpt GEN_TAC >> EQ_TAC
 >- (DISCH_TAC >> IMP_RES_TAC FILTRATION_SUBSETS \\
     fs [filtration_def])
 >> RW_TAC std_ss [filtration_def]);

val filtered_measure_space_def = Define
   `filtered_measure_space (sp,sts,m) a =
             measure_space (sp,sts,m) /\ filtration (sp,sts) a`;

(* `sigma_finite_FMS = sigma_finite_filtered_measure_space` *)
val sigma_finite_filtered_measure_space_def = Define
   `sigma_finite_filtered_measure_space (sp,sts,m) a =
                 filtered_measure_space (sp,sts,m) a /\ sigma_finite (sp,subsets (a 0),m)`;

(* a shorter abbreviation *)
val _ = overload_on ("sigma_finite_FMS",
                    ``sigma_finite_filtered_measure_space``);

val sigma_finite_FMS_def =
    sigma_finite_filtered_measure_space_def;

(* all sub measure spaces of a sigma-finite fms are also sigma-finite *)
val SIGMA_FINITE_FMS_IMP = store_thm
  ("SIGMA_FINITE_FMS_IMP",
  ``!sp sts a m. sigma_finite_FMS (sp,sts,m) a ==> !n. sigma_finite (sp,subsets (a n),m)``,
 (* proof *)
    RW_TAC std_ss [sigma_finite_FMS_def, filtered_measure_space_def, filtration_def]
 >> Know `measure_space (sp,subsets (a 0),m) /\
          measure_space (sp,subsets (a n),m)`
 >- (CONJ_TAC \\ (* 2 subgoals, same tactics *)
     MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def, measure_def]
                                (Q.SPEC `(sp,sts,m)` SUB_SIGMA_ALGEBRA_MEASURE_SPACE)) >> art [])
 >> STRIP_TAC
 >> POP_ASSUM (simp o wrap o (MATCH_MP SIGMA_FINITE_ALT))
 >> POP_ASSUM (fs o wrap o (MATCH_MP SIGMA_FINITE_ALT))
 >> Q.EXISTS_TAC `f`
 >> fs [IN_FUNSET, IN_UNIV, measurable_sets_def, m_space_def, measure_def]
 >> `0 <= n` by RW_TAC arith_ss []
 >> METIS_TAC [SUBSET_DEF]);

(* extended definition *)
val SIGMA_FINITE_FMS = store_thm
  ("SIGMA_FINITE_FMS",
  ``!sp sts a m. sigma_finite_FMS (sp,sts,m) a =
                 filtered_measure_space (sp,sts,m) a /\
                 !n. sigma_finite (sp,subsets (a n),m)``,
    rpt GEN_TAC >> EQ_TAC
 >- (DISCH_TAC >> IMP_RES_TAC SIGMA_FINITE_FMS_IMP \\
     fs [sigma_finite_FMS_def])
 >> RW_TAC std_ss [sigma_finite_FMS_def]);

(* the smallest sigma-algebra generated by all (a n) *)
val infty_sigma_algebra_def = Define
   `infty_sigma_algebra sp a = sigma sp (BIGUNION (IMAGE (\(i :num). subsets (a i)) UNIV))`;

val INFTY_SIGMA_ALGEBRA_BOUNDED = store_thm
  ("INFTY_SIGMA_ALGEBRA_BOUNDED",
  ``!A a. filtration A a ==> sub_sigma_algebra (infty_sigma_algebra (space A) a) A``,
    RW_TAC std_ss [sub_sigma_algebra_def, FILTRATION, infty_sigma_algebra_def]
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     RW_TAC std_ss [subset_class_def, IN_BIGUNION_IMAGE, IN_UNIV] \\
    `x IN subsets A` by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def, space_def, subsets_def])
 >- REWRITE_TAC [SPACE_SIGMA]
 >> MATCH_MP_TAC SIGMA_SUBSET >> art []
 >> RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV]
 >> PROVE_TAC [SUBSET_DEF]);

val INFTY_SIGMA_ALGEBRA_MAXIMAL = store_thm
  ("INFTY_SIGMA_ALGEBRA_MAXIMAL",
  ``!A a. filtration A a ==> !n. sub_sigma_algebra (a n) (infty_sigma_algebra (space A) a)``,
    RW_TAC std_ss [sub_sigma_algebra_def, FILTRATION, infty_sigma_algebra_def]
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     RW_TAC std_ss [subset_class_def, IN_BIGUNION_IMAGE, IN_UNIV] \\
    `x IN subsets A` by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def, space_def, subsets_def])
 >- REWRITE_TAC [SPACE_SIGMA]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `BIGUNION (IMAGE (\i. subsets (a i)) univ(:num))`
 >> CONJ_TAC
 >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `n` >> art [])
 >> REWRITE_TAC [SIGMA_SUBSET_SUBSETS]);

(* `prob_martingale` will be the probability version of `martingale` *)
val martingale_def = Define
   `martingale m a u =
      sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u (SUC n) x * indicator_fn s x) =
            integral m (\x. u n x * indicator_fn s x))`;

val super_martingale_def = Define
   `super_martingale m a u =
      sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u (SUC n) x * indicator_fn s x) <=
            integral m (\x. u n x * indicator_fn s x))`;

val sub_martingale_def = Define
   `sub_martingale m a u =
      sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u n x * indicator_fn s x) <=
            integral m (\x. u (SUC n) x * indicator_fn s x))`;

(* u is a martingale if, and only if, it is both a sub- and a supermartingale *)
val MARTINGALE_BOTH_SUB_SUPER = store_thm
  ("MARTINGALE_BOTH_SUB_SUPER",
  ``!m a u. martingale m a u = sub_martingale m a u /\ super_martingale m a u``,
    RW_TAC std_ss [martingale_def, sub_martingale_def, super_martingale_def]
 >> EQ_TAC >> RW_TAC std_ss [le_refl]
 >> ASM_SIMP_TAC std_ss [GSYM le_antisym]);

(* ------------------------------------------------------------------------- *)
(*  General version of martingales with poset indexes (Chapter 19 of [1])    *)
(* ------------------------------------------------------------------------- *)

open posetTheory;

val POSET_NUM_LE = store_thm
  ("POSET_NUM_LE", ``poset (univ(:num),$<=)``,
    RW_TAC std_ss [poset_def]
 >- (Q.EXISTS_TAC `0` >> REWRITE_TAC [GSYM IN_APP, IN_UNIV])
 >- (MATCH_MP_TAC LESS_EQUAL_ANTISYM >> art [])
 >> MATCH_MP_TAC LESS_EQ_TRANS
 >> Q.EXISTS_TAC `y` >> art []);

(* below J is an index set, R is a partial order on J *)
val filtration_I_def = Define
   `filtration_I A a (J,R) =
      poset (J,R) /\ (!n. n IN J ==> sub_sigma_algebra (a n) A) /\
      (!i j. i IN J /\ j IN J /\ R i j ==> subsets (a i) SUBSET subsets (a j))`;

val FILTRATION_ALT = store_thm
  ("FILTRATION_ALT",
  ``!A a. filtration A a = filtration_I A a (univ(:num),$<=)``,
    RW_TAC std_ss [filtration_def, filtration_I_def, POSET_NUM_LE, IN_UNIV]);

val filtered_measure_space_I_def = Define
   `filtered_measure_space_I (sp,sts,m) a (J,R) =
             measure_space (sp,sts,m) /\ filtration_I (sp,sts) a (J,R)`;

val FILTERED_MEASURE_SPACE_ALT = store_thm
  ("FILTERED_MEASURE_SPACE_ALT",
  ``!sp sts m a. filtered_measure_space (sp,sts,m) a =
                 filtered_measure_space_I (sp,sts,m) a (univ(:num),$<=)``,
    RW_TAC std_ss [filtered_measure_space_def, filtered_measure_space_I_def,
                   FILTRATION_ALT, POSET_NUM_LE, IN_UNIV]);

val sigma_finite_filtered_measure_space_I_def = Define
   `sigma_finite_filtered_measure_space_I (sp,sts,m) a (J,R) =
          filtered_measure_space_I (sp,sts,m) a (J,R) /\
          !n. n IN J ==> sigma_finite (sp,subsets (a n),m)`;

(* a shorter abbreviation *)
val _ = overload_on ("sigma_finite_FMS_I",
                    ``sigma_finite_filtered_measure_space_I``);

val sigma_finite_FMS_I_def =
    sigma_finite_filtered_measure_space_I_def;

val SIGMA_FINITE_FMS_ALT = store_thm
  ("SIGMA_FINITE_FMS_ALT",
  ``!sp sts m a. sigma_finite_FMS (sp,sts,m) a =
                 sigma_finite_FMS_I (sp,sts,m) a (univ(:num),$<=)``,
    RW_TAC std_ss [SIGMA_FINITE_FMS, sigma_finite_FMS_I_def,
                   FILTERED_MEASURE_SPACE_ALT, IN_UNIV]);

val infty_sigma_algebra_I_def = Define
   `infty_sigma_algebra_I sp a I = sigma sp (BIGUNION (IMAGE (\i. subsets (a i)) I))`;

(* `martingale_I m a u (univ(:num),$<=) = martingale m a u` *)
val martingale_I_def = Define
   `martingale_I m a u (J,R) =
      sigma_finite_FMS_I m a (J,R) /\ (!n. n IN J ==> integrable m (u n)) /\
      !i j s. i IN J /\ j IN J /\ R i j /\ s IN (subsets (a i)) ==>
           (integral m (\x. u i x * indicator_fn s x) =
            integral m (\x. u j x * indicator_fn s x))`;

(* or "upwards directed" *)
val upwards_filtering_def = Define
   `upwards_filtering (J,R) =
      !a b. a IN J /\ b IN J ==> ?c. c IN J /\ R a c /\ R b c`;

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales. Cambridge University Press (2005).
  [2] Doob, J.L.: Stochastic processes. Wiley-Interscience (1990).
 *)
