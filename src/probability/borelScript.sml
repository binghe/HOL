(* ------------------------------------------------------------------------- *)
(* Borel Space and Borel-measurable functions                                *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar (2013) [2]              *)
(* HVG Group, Concordia University, Montreal                                 *)
(*                                                                           *)
(* Further enriched by Chun Tian (2019)                                      *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble [3] (2010)                               *)
(* Cambridge University                                                      *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib
     arithmeticTheory optionTheory pred_setTheory res_quanTheory res_quanTools
     listTheory rich_listTheory pairTheory numpairTheory combinTheory
     realTheory realLib seqTheory transcTheory real_sigmaTheory;

open hurdUtils real_topologyTheory util_probTheory extrealTheory measureTheory;

val _ = new_theory "borel";

(* ------------------------------------------------------------------------- *)
(*  Indicator functions                                                      *)
(* ------------------------------------------------------------------------- *)

(* `indicator_fn s` maps x to 0 or 1 when x IN or NOTIN s *)
val indicator_fn_def = Define
   `indicator_fn s = \x. if x IN s then (1 :extreal) else (0 :extreal)`;

val _ = Unicode.unicode_version {u = UTF8.chr 0x1D7D9, tmnm = "indicator_fn"};

val INDICATOR_FN_POS = store_thm
  ("INDICATOR_FN_POS", ``!s x. 0 <= indicator_fn s x``,
    RW_TAC std_ss [indicator_fn_def]
 >- RW_TAC real_ss [extreal_of_num_def, extreal_le_eq]
 >> REWRITE_TAC [le_refl]);

val indicator_fn_not_infty = store_thm (* new *)
  ("indicator_fn_not_infty",
  ``!s x. indicator_fn s x <> NegInf /\ indicator_fn s x <> PosInf``,
    RW_TAC std_ss []
 >- (MATCH_MP_TAC pos_not_neginf \\
     REWRITE_TAC [INDICATOR_FN_POS])
 >> Cases_on `x IN s`
 >> ASM_SIMP_TAC std_ss [indicator_fn_def, extreal_of_num_def, extreal_not_infty]);

val INDICATOR_FN_SING_1 = store_thm
  ("INDICATOR_FN_SING_1", ``!x y. (x = y) ==> (indicator_fn {x} y = 1)``,
    RW_TAC std_ss [indicator_fn_def, IN_SING]);

val INDICATOR_FN_SING_0 = store_thm
  ("INDICATOR_FN_SING_0", ``!x y. x <> y ==> (indicator_fn {x} y = 0)``,
    RW_TAC std_ss [indicator_fn_def, IN_SING]);

(* Properties of the indicator function [1, p.13] *)
val INDICATOR_FN_INTER = store_thm (* new *)
  ("INDICATOR_FN_INTER",
  ``!A B. indicator_fn (A INTER B) = (\t. (indicator_fn A t) * (indicator_fn B t))``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> RW_TAC std_ss [indicator_fn_def, mul_lone, IN_INTER, mul_lzero]
 >> FULL_SIMP_TAC std_ss []);

val INDICATOR_FN_INTER_MIN = store_thm (* new *)
  ("INDICATOR_FN_INTER_MIN",
  ``!A B. indicator_fn (A INTER B) = (\t. min (indicator_fn A t) (indicator_fn B t))``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B`
 >> fs [extreal_of_num_def, extreal_min_def, extreal_le_eq]);

val INDICATOR_FN_DIFF = store_thm (* new *)
  ("INDICATOR_FN_DIFF",
  ``!A B. indicator_fn (A DIFF B) = (\t. indicator_fn A t - indicator_fn (A INTER B) t)``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A DIFF B) t = if t IN (A DIFF B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_DIFF, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B` >> fs [sub_rzero]
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC sub_refl
 >> PROVE_TAC [extreal_of_num_def, extreal_not_infty]);

val INDICATOR_FN_DIFF_SPACE = store_thm (* new *)
  ("INDICATOR_FN_DIFF_SPACE",
  ``!A B sp. A SUBSET sp /\ B SUBSET sp ==>
            (indicator_fn (A INTER (sp DIFF B)) =
             (\t. indicator_fn A t - indicator_fn (A INTER B) t))``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A DIFF B) t = if t IN (A DIFF B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_DIFF, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B` >> fs [SUBSET_DEF, sub_rzero]
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC sub_refl
 >> PROVE_TAC [extreal_of_num_def, extreal_not_infty]);

val INDICATOR_FN_UNION_MAX = store_thm (* new *)
  ("INDICATOR_FN_UNION_MAX",
  ``!A B. indicator_fn (A UNION B) = (\t. max (indicator_fn A t) (indicator_fn B t))``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A UNION B) t = if t IN (A UNION B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_UNION]
 >> Cases_on `t IN A` >> Cases_on `t IN B`
 >> fs [extreal_max_def, extreal_le_eq, extreal_of_num_def]);

val INDICATOR_FN_UNION_MIN = store_thm (* new *)
  ("INDICATOR_FN_UNION_MIN",
  ``!A B. indicator_fn (A UNION B) = (\t. min (indicator_fn A t + indicator_fn B t) 1)``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A UNION B) t = if t IN (A UNION B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_UNION]
 >> Cases_on `t IN A` >> Cases_on `t IN B`
 >> fs [extreal_max_def, extreal_add_def, extreal_of_num_def, extreal_min_def, extreal_le_eq]);

val INDICATOR_FN_UNION = store_thm (* new *)
  ("INDICATOR_FN_UNION",
  ``!A B. indicator_fn (A UNION B) =
          (\t. indicator_fn A t + indicator_fn B t - indicator_fn (A INTER B) t)``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> `indicator_fn (A UNION B) t = if t IN (A UNION B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_UNION, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B` >> fs [add_lzero, add_rzero, mul_rzero, sub_rzero]
 >> fs [extreal_add_def, extreal_sub_def, extreal_of_num_def]);

val indicator_fn_split = store_thm
  ("indicator_fn_split",
  ``!(r:num->bool) s (b:num->('a->bool)).
       FINITE r /\ (BIGUNION (IMAGE b r) = s) /\
       (!i j. i IN r /\ j IN r /\ i <> j ==> DISJOINT (b i) (b j)) ==>
       !a. a SUBSET s ==>
          (indicator_fn a = (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))``,
 (* proof *)
    Suff `!r. FINITE r ==>
            (\r. !s (b:num->('a->bool)).
             FINITE r /\
             (BIGUNION (IMAGE b r) = s) /\
             (!i j. i IN r /\ j IN r /\ i <> j ==> DISJOINT (b i) (b j)) ==>
             !a. a SUBSET s ==>
                 ((indicator_fn a) =
                  (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))) r`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IMAGE_EMPTY, BIGUNION_EMPTY,
                   SUBSET_EMPTY, indicator_fn_def, NOT_IN_EMPTY,
                   FINITE_INSERT, IMAGE_INSERT, DELETE_NON_ELEMENT,
                   IN_INSERT, BIGUNION_INSERT]
 >> Q.PAT_X_ASSUM `!b. P ==> !a. Q ==> (x = y)`
      (MP_TAC o Q.ISPEC `(b :num -> 'a -> bool)`)
 >> RW_TAC std_ss [SUBSET_DEF]
 >> POP_ASSUM (MP_TAC o Q.ISPEC `a DIFF ((b :num -> 'a -> bool) e)`)
 >> Know `(!x. x IN a DIFF b e ==> x IN BIGUNION (IMAGE b s))`
 >- METIS_TAC [SUBSET_DEF, IN_UNION, IN_DIFF]
 >> RW_TAC std_ss [FUN_EQ_THM]
 >> `!i. i IN e INSERT s ==> (\i. if x IN a INTER b i then 1 else 0) i <> NegInf`
      by METIS_TAC [extreal_of_num_def, extreal_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >> Know `SIGMA (\i. (if x IN a INTER b i then 1 else 0)) s =
          SIGMA (\i. (if x IN (a DIFF b e) INTER b i then 1 else 0)) s`
 >- (`!i. i IN s ==> (\i. if x IN a INTER b i then 1 else 0) i <> NegInf`
      by METIS_TAC [extreal_of_num_def,extreal_not_infty] \\
     `!i. i IN s ==> (\i. if x IN (a DIFF b e) INTER b i then 1 else 0) i <> NegInf`
      by METIS_TAC [extreal_of_num_def,extreal_not_infty] \\
     FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool)`)
                               EXTREAL_SUM_IMAGE_IN_IF] \\
     FULL_SIMP_TAC std_ss [(Q.SPEC `(\i. if x IN (a DIFF b e) INTER b i then 1 else 0)`
                            o UNDISCH o Q.ISPEC `(s :num -> bool)`)
                               EXTREAL_SUM_IMAGE_IN_IF] \\
     MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``) \\
     RW_TAC std_ss [FUN_EQ_THM, IN_INTER, IN_DIFF] \\
     FULL_SIMP_TAC real_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF, IN_INTER,
                            NOT_IN_EMPTY, EXTENSION, GSPECIFICATION] \\
     RW_TAC real_ss [extreal_of_num_def] >> METIS_TAC []) >> STRIP_TAC
 >> `SIGMA (\i. if x IN a INTER b i then 1 else 0) s = (if x IN a DIFF b e then 1 else 0)`
      by METIS_TAC []
 >> POP_ORW
 >> RW_TAC real_ss [IN_INTER, IN_DIFF, EXTREAL_SUM_IMAGE_ZERO, add_rzero, add_lzero]
 >> FULL_SIMP_TAC std_ss []
 >> `x IN BIGUNION (IMAGE b s)` by METIS_TAC [SUBSET_DEF,IN_UNION]
 >> FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE]
 >> `s = {x'} UNION (s DIFF {x'})` by METIS_TAC [UNION_DIFF, SUBSET_DEF, IN_SING]
 >> POP_ORW
 >> `FINITE {x'} /\ FINITE (s DIFF {x'})` by METIS_TAC [FINITE_SING, FINITE_DIFF]
 >> `DISJOINT {x'} (s DIFF {x'})` by METIS_TAC [EXTENSION, IN_DISJOINT, IN_DIFF, IN_SING]
 >> `!i. (\i. if x IN b i then 1 else 0) i <> NegInf`
       by METIS_TAC [extreal_of_num_def,extreal_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_DISJOINT_UNION]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING]
 >> Suff `SIGMA (\i. if x IN b i then 1 else 0) (s DIFF {x'}) = 0`
 >- METIS_TAC [add_rzero]
 >> FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool) DIFF {x'}`)
                              EXTREAL_SUM_IMAGE_IN_IF]
 >> Suff `(\i. if i IN s DIFF {x'} then if x IN b i then 1 else 0 else 0) = (\x. 0)`
 >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
 >> RW_TAC std_ss [FUN_EQ_THM, IN_DIFF, IN_SING]
 >> METIS_TAC [IN_SING, IN_DIFF, IN_DISJOINT]);

val indicator_fn_suminf = store_thm
  ("indicator_fn_suminf",
  ``!a x. (!m n. m <> n ==> DISJOINT (a m) (a n)) ==>
          (suminf (\i. indicator_fn (a i) x) = indicator_fn (BIGUNION (IMAGE a univ(:num))) x)``,
  RW_TAC std_ss [ext_suminf_def, sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> Cases_on `~(x IN BIGUNION (IMAGE a univ(:num)))`
      >- (FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE,IN_UNIV]
          >> RW_TAC std_ss [indicator_fn_def,EXTREAL_SUM_IMAGE_ZERO,FINITE_COUNT,le_refl,le_01])
      >> FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE,IN_UNIV,indicator_fn_def]
      >> Reverse (RW_TAC std_ss [])
      >- METIS_TAC []
      >> `!n. n <> x' ==> ~(x IN a n)` by METIS_TAC [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
      >> Cases_on `~(x' IN count n)`
      >- (`SIGMA (\i. if x IN a i then 1 else 0) (count n) = 0`
            by (MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
                >> RW_TAC real_ss [FINITE_COUNT]
                >> METIS_TAC [])
          >> RW_TAC std_ss [le_01])
      >> `count n = ((count n) DELETE x') UNION {x'}`
          by (RW_TAC std_ss [EXTENSION,IN_DELETE,IN_UNION,IN_SING,IN_COUNT]
              >> METIS_TAC [])
      >> POP_ORW
      >> `DISJOINT ((count n) DELETE x') ({x'})`
                by RW_TAC std_ss [DISJOINT_DEF, EXTENSION,IN_INTER, NOT_IN_EMPTY,
                                  IN_SING, IN_DELETE]
      >> `!n. (\i. if x IN a i then 1 else 0) n <> NegInf` by RW_TAC std_ss [num_not_infty]
      >> FULL_SIMP_TAC std_ss [FINITE_COUNT, FINITE_DELETE, FINITE_SING,
                               EXTREAL_SUM_IMAGE_DISJOINT_UNION, EXTREAL_SUM_IMAGE_SING]
      >> Suff `SIGMA (\i. if x IN a i then 1 else 0) (count n DELETE x') = 0`
      >- RW_TAC std_ss [add_lzero,le_refl]
      >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
      >> RW_TAC std_ss [FINITE_COUNT,FINITE_DELETE]
      >> METIS_TAC [IN_DELETE])
  >> `!n. SIGMA (\i. indicator_fn (a i) x) (count n) <= y`
       by (RW_TAC std_ss []
           >> POP_ASSUM MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
           >> METIS_TAC [])
  >> Reverse (RW_TAC std_ss [indicator_fn_def,IN_BIGUNION_IMAGE,IN_UNIV])
  >- (`0 <= SIGMA (\i. indicator_fn (a i) x) (count 0)`
        by RW_TAC std_ss [COUNT_ZERO,EXTREAL_SUM_IMAGE_EMPTY,le_refl]
      >> METIS_TAC [le_trans])
  >> Suff `SIGMA (\i. indicator_fn (a i) x) (count (SUC x'')) = 1` (* could be x' here *)
  >- METIS_TAC []
  >> `!i. (\i. indicator_fn (a i) x) i <> NegInf`
        by RW_TAC std_ss [indicator_fn_def,num_not_infty]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,FINITE_COUNT,COUNT_SUC]
  >> Suff `SIGMA (\i. indicator_fn (a i) x) (count x'' DELETE x'') = 0`
  >- RW_TAC std_ss [indicator_fn_def,add_rzero]
  >> `!n. n <> x'' ==> ~(x IN a n)` by METIS_TAC [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
  >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
  >> FULL_SIMP_TAC std_ss [FINITE_COUNT,FINITE_DELETE,IN_COUNT,IN_DELETE,indicator_fn_def]);


(* ------------------------------------------------------------------------- *)
(*  Positive and negative parts of functions                                 *)
(* ------------------------------------------------------------------------- *)

val fn_plus_def = Define (* f+ *)
   `fn_plus (f :'a -> extreal) = (\x. if 0 < f x then f x else 0)`;

val fn_minus_def = Define (* f- *)
   `fn_minus (f :'a -> extreal) = (\x. if f x < 0 then ~(f x) else 0)`;

(* alternative definitions of fn_plus and fn_minus using max/min *)
val FN_PLUS_ALT = store_thm
  ("FN_PLUS_ALT", ``!f. fn_plus f = (\x. max (f x) 0)``,
    RW_TAC std_ss [fn_plus_def, extreal_max_def]
 >> FUN_EQ_TAC >> GEN_TAC >> BETA_TAC
 >> Cases_on `0 < f x`
 >- (`~(f x <= 0)` by PROVE_TAC [let_antisym] >> fs [])
 >> `f x <= 0` by PROVE_TAC [extreal_lt_def]
 >> fs []);

val FN_MINUS_ALT = store_thm
  ("FN_MINUS_ALT", ``!f. fn_minus f = (\x. -min (f x) 0)``,
    RW_TAC std_ss [fn_minus_def, extreal_min_def]
 >> FUN_EQ_TAC >> GEN_TAC >> BETA_TAC
 >> Cases_on `f x < 0`
 >- (`f x <= 0` by PROVE_TAC [lt_imp_le] >> fs [])
 >> fs []
 >> `0 <= f x` by PROVE_TAC [extreal_lt_def]
 >> Cases_on `f x <= 0`
 >- (`f x = 0` by PROVE_TAC [le_antisym] >> fs [neg_0])
 >> fs [neg_0]);

val FN_DECOMP = store_thm (* new *)
  ("FN_DECOMP", ``!f x. f x = fn_plus f x - fn_minus f x``,
    RW_TAC std_ss [fn_plus_def, fn_minus_def]
 >- METIS_TAC [lt_antisym]
 >- REWRITE_TAC [sub_rzero]
 >- (`0 - -f x = 0 + f x` by METIS_TAC [sub_rneg, extreal_of_num_def] \\
     POP_ORW >> REWRITE_TAC [add_lzero])
 >> REWRITE_TAC [sub_rzero]
 >> METIS_TAC [extreal_lt_def, le_antisym]);

val FN_DECOMP' = store_thm (* new *)
  ("FN_DECOMP'", ``!f. f = (\x. fn_plus f x - fn_minus f x)``,
    METIS_TAC [FN_DECOMP]);

(* `fn_plus f x + fn_minus f x` is always defined (same reason as above) *)
val FN_ABS = store_thm (* new *)
  ("FN_ABS", ``!f x. (abs o f) x = fn_plus f x + fn_minus f x``,
 (* proof *)
    RW_TAC std_ss [o_DEF, fn_plus_def, fn_minus_def, add_rzero, add_lzero]
 >> Q.ABBREV_TAC `e = f x` (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      METIS_TAC [lt_antisym],
      (* goal 2 (of 4) *)
      Cases_on `e` >- METIS_TAC [extreal_of_num_def, lt_infty]
      >- REWRITE_TAC [extreal_abs_def] \\
      REWRITE_TAC [extreal_abs_def, extreal_11] \\
     `0 <= r` by METIS_TAC [extreal_of_num_def, extreal_lt_eq, REAL_LT_IMP_LE] \\
      METIS_TAC [abs],
      (* goal 3 (of 4) *)
      Cases_on `e` >- REWRITE_TAC [extreal_abs_def, extreal_ainv_def]
      >- METIS_TAC [extreal_of_num_def, lt_infty] \\
      REWRITE_TAC [extreal_abs_def, extreal_ainv_def, extreal_11] \\
     `r < 0` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
      METIS_TAC [real_lte, abs],
      (* goal 4 (of 4) *)
     `e = 0` by METIS_TAC [extreal_lt_def, le_antisym] \\
      PROVE_TAC [abs_0] ]);

val FN_ABS' = store_thm (* new *)
  ("FN_ABS'", ``!f. (abs o f) = (\x. fn_plus f x + fn_minus f x)``,
    METIS_TAC [FN_ABS]);

val FN_PLUS_POS = store_thm
  ("FN_PLUS_POS", ``!g x. 0 <= (fn_plus g) x``,
  RW_TAC real_ss [fn_plus_def, FUN_EQ_THM, lt_imp_le, le_refl]);

val FN_MINUS_POS = store_thm
  ("FN_MINUS_POS", ``!g x. 0 <= (fn_minus g) x``,
  RW_TAC real_ss [fn_minus_def, FUN_EQ_THM, le_refl]
  >> METIS_TAC [le_neg, lt_imp_le, neg_0]);

val FN_PLUS_POS_ID = store_thm
  ("FN_PLUS_POS_ID", ``!g. (!x. 0 <= g x) ==> ((fn_plus g) = g)``,
  RW_TAC real_ss [fn_plus_def,FUN_EQ_THM]
  >> Cases_on `g x = 0` >- METIS_TAC []
  >> METIS_TAC [le_lt]);

val FN_PLUS_NEG_ZERO = store_thm
  ("FN_PLUS_NEG_ZERO",
  ``!g. (!x. g x <= 0) ==> (fn_plus g = (\x. 0))``,
    RW_TAC real_ss [fn_plus_def, FUN_EQ_THM]
 >> `~(0 < g x)` by PROVE_TAC [extreal_lt_def]
 >> fs []);

val FN_MINUS_POS_ZERO = store_thm
  ("FN_MINUS_POS_ZERO",
  ``!g. (!x. 0 <= g x) ==> (fn_minus g = (\x. 0))``,
    RW_TAC real_ss [fn_minus_def, FUN_EQ_THM]
 >> Cases_on `g x = 0` >- METIS_TAC [neg_0]
 >> `0 < g x` by METIS_TAC [lt_le]
 >> METIS_TAC [extreal_lt_def]);

val FN_MINUS_TO_PLUS = store_thm
  ("FN_MINUS_TO_PLUS", ``!f. fn_minus (\x. -(f x)) = fn_plus f``,
    RW_TAC std_ss [fn_plus_def, fn_minus_def, neg_neg]
 >> `!x. -f x < 0 <=> 0 < f x` by PROVE_TAC [neg_0, lt_neg]
 >> POP_ORW >> REWRITE_TAC []);

val FN_PLUS_TO_MINUS = store_thm
  ("FN_PLUS_TO_MINUS", ``!f. fn_plus (\x. -(f x)) = fn_minus f``,
    RW_TAC std_ss [fn_plus_def, fn_minus_def, neg_neg]
 >> `!x. 0 < -f x <=> f x < 0` by PROVE_TAC [neg_0, lt_neg]
 >> POP_ORW >> REWRITE_TAC []);

val FN_PLUS_NOT_INFTY = store_thm
  ("FN_PLUS_NOT_INFTY", ``!f. (!x. f x <> PosInf) ==> !x. fn_plus f x <> PosInf``,
    RW_TAC std_ss [fn_plus_def]
 >> Cases_on `0 < f x` >- PROVE_TAC []
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]);

val FN_MINUS_NOT_INFTY = store_thm
  ("FN_MINUS_NOT_INFTY", ``!f. (!x. f x <> NegInf) ==> !x. fn_minus f x <> PosInf``,
    RW_TAC std_ss [fn_minus_def]
 >> Cases_on `f x < 0`
 >- PROVE_TAC [extreal_ainv_def, neg_neg]
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]);

val FN_PLUS_CMUL = store_thm
  ("FN_PLUS_CMUL",
  ``!f c. (0 <= c ==> (fn_plus (\x. Normal c * f x) = (\x. Normal c * fn_plus f x))) /\
          (c <= 0 ==> (fn_plus (\x. Normal c * f x) = (\x. -Normal c * fn_minus f x)))``,
    RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
 >- (Cases_on `0 < f x`
     >- METIS_TAC [let_mul, extreal_of_num_def, extreal_le_def, extreal_lt_def, le_antisym]
     >> RW_TAC std_ss [mul_rzero]
     >> METIS_TAC [mul_le, extreal_lt_def, extreal_le_def, extreal_of_num_def, lt_imp_le,
                   le_antisym])
 >> RW_TAC std_ss [mul_rzero, neg_mul2]
 >- METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
               le_antisym, mul_comm]
 >> METIS_TAC [le_mul_neg, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
               le_antisym]);

val FN_PLUS_CMUL_full = store_thm
  ("FN_PLUS_CMUL_full",
  ``!f c. (0 <= c ==> (fn_plus (\x. c * f x) = (\x. c * fn_plus f x))) /\
          (c <= 0 ==> (fn_plus (\x. c * f x) = (\x. -c * fn_minus f x)))``,
    rpt GEN_TAC
 >> Cases_on `c`
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     FUN_EQ_TAC >> RW_TAC std_ss [fn_plus_def, fn_minus_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       REWRITE_TAC [neg_mul2],
       (* goal 2 (of 4) *)
      `0 <= f x` by PROVE_TAC [extreal_lt_def] \\
      `NegInf <= 0` by PROVE_TAC [le_infty] \\
      `NegInf * f x <= 0` by PROVE_TAC [mul_le'] \\
       PROVE_TAC [let_antisym],
       (* goal 3 (of 4) *)
      `NegInf < 0` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `0 < NegInf * f x` by PROVE_TAC [lt_mul_neg],
       (* goal 4 (of 4) *)
       REWRITE_TAC [mul_rzero] ])
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     FUN_EQ_TAC >> RW_TAC std_ss [fn_plus_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
      `f x <= 0` by PROVE_TAC [extreal_lt_def] \\
       fs [le_lt] \\
      `0 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `PosInf * f x < 0` by PROVE_TAC [mul_lt] \\
       PROVE_TAC [lt_antisym],
       (* goal 2 (of 3) *)
      `0 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `0 < PosInf * f x` by PROVE_TAC [lt_mul],
       (* goal 3 (of 3) *)
       REWRITE_TAC [mul_rzero] ])
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `0 <= r` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_PLUS_CMUL],
      (* goal 2 (of 2) *)
     `r <= 0` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_PLUS_CMUL] ]);

val FN_MINUS_CMUL = store_thm
  ("FN_MINUS_CMUL",
  ``!f c. (0 <= c ==> (fn_minus (\x. Normal c * f x) = (\x. Normal c * fn_minus f x))) /\
          (c <= 0 ==> (fn_minus (\x. Normal c * f x) = (\x. -Normal c * fn_plus f x)))``,
    RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
 >- (RW_TAC std_ss [mul_rzero, mul_rneg, neg_eq0]
     >- METIS_TAC [le_mul, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
                   le_antisym]
     >> METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
                   le_antisym, neg_eq0])
 >> RW_TAC std_ss [mul_rzero, neg_eq0, mul_lneg, neg_0]
 >- METIS_TAC [le_mul_neg, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
               le_antisym]
 >> METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
               le_antisym, neg_eq0, mul_comm]);

val FN_MINUS_CMUL_full = store_thm
  ("FN_MINUS_CMUL_full",
  ``!f c. (0 <= c ==> (fn_minus (\x. c * f x) = (\x. c * fn_minus f x))) /\
          (c <= 0 ==> (fn_minus (\x. c * f x) = (\x. -c * fn_plus f x)))``,
    rpt GEN_TAC
 >> Cases_on `c`
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     FUN_EQ_TAC >> RW_TAC std_ss [fn_plus_def, fn_minus_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       REWRITE_TAC [GSYM mul_lneg],
       (* goal 2 (of 4) *)
      `f x <= 0` by PROVE_TAC [extreal_lt_def] \\
      `NegInf <= 0` by PROVE_TAC [le_infty] \\
      `0 <= NegInf * f x` by PROVE_TAC [le_mul_neg] \\
       PROVE_TAC [let_antisym],
       (* goal 3 (of 4) *)
      `NegInf < 0` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `NegInf * f x < 0` by PROVE_TAC [mul_lt'],
       (* goal 4 (of 4) *)
       REWRITE_TAC [mul_rzero] ])
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     FUN_EQ_TAC >> RW_TAC std_ss [fn_minus_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       REWRITE_TAC [GSYM mul_rneg],
       (* goal 2 (of 4) *)
      `0 <= f x` by PROVE_TAC [extreal_lt_def] \\
      `0 <= PosInf` by PROVE_TAC [le_infty] \\
      `0 <= PosInf * f x` by PROVE_TAC [le_mul] \\
       PROVE_TAC [let_antisym],
       (* goal 3 (of 4) *)
      `0 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `PosInf * f x < 0` by PROVE_TAC [mul_lt],
       (* goal 3 (of 4) *)
       REWRITE_TAC [mul_rzero] ])
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `0 <= r` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_MINUS_CMUL],
      (* goal 2 (of 2) *)
     `r <= 0` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_MINUS_CMUL] ]);

val FN_PLUS_FMUL = store_thm
  ("FN_PLUS_FMUL",
  ``!f c. (!x. 0 <= c x) ==> (fn_plus (\x. c x * f x) = (\x. c x * fn_plus f x))``,
    RW_TAC std_ss [fn_plus_def, FUN_EQ_THM]
 >> Cases_on `0 < f x`
 >- (`0 <= c x * f x` by PROVE_TAC [let_mul] \\
     fs [le_lt])
 >> `f x <= 0` by PROVE_TAC [extreal_lt_def]
 >> `c x * f x <= 0` by PROVE_TAC [mul_le]
 >> `~(0 < c x * f x)` by PROVE_TAC [extreal_lt_def]
 >> fs [mul_rzero]);

val FN_MINUS_FMUL = store_thm
  ("FN_MINUS_FMUL",
  ``!f c. (!x. 0 <= c x) ==> (fn_minus (\x. c x * f x) = (\x. c x * fn_minus f x))``,
    RW_TAC std_ss [fn_minus_def, FUN_EQ_THM]
 >> Cases_on `0 < f x`
 >- (`0 <= c x * f x` by PROVE_TAC [let_mul] \\
     `~(c x * f x < 0)` by PROVE_TAC [extreal_lt_def] \\
     `~(f x < 0)` by PROVE_TAC [lt_antisym] \\
     fs [mul_rzero])
 >> `f x <= 0` by PROVE_TAC [extreal_lt_def]
 >> `c x * f x <= 0` by PROVE_TAC [mul_le]
 >> `~(0 < c x * f x)` by PROVE_TAC [extreal_lt_def]
 >> fs [le_lt, lt_refl, mul_rzero, neg_0]
 >- REWRITE_TAC [GSYM mul_rneg]
 >> fs [entire, neg_0]);

val FN_PLUS_ADD_LE = store_thm
  ("FN_PLUS_ADD_LE",
  ``!f g x. fn_plus (\x. f x + g x) x <= (fn_plus f x) + (fn_plus g x)``,
    RW_TAC real_ss [fn_plus_def, add_rzero, add_lzero, le_refl, le_add2]
 >> METIS_TAC [le_refl, extreal_lt_def, le_add2, add_lzero, add_rzero, lt_imp_le]);

(* more antecedents added: no mixing of PosInf and NegInf *)
val FN_MINUS_ADD_LE = store_thm
  ("FN_MINUS_ADD_LE",
  ``!f g x. (f x <> NegInf) /\ (g x <> NegInf) \/
            (f x <> PosInf) /\ (g x <> PosInf) ==>
            fn_minus (\x. f x + g x) x <= (fn_minus f x) + (fn_minus g x)``,
    rpt GEN_TAC
 >> DISCH_TAC
 >> MP_TAC (BETA_RULE (Q.SPECL [`\x. -f x`, `\x. -g x`, `x`] FN_PLUS_ADD_LE))
 >> Suff `fn_plus (\x. -f x + -g x) x = fn_minus (\x. f x + g x) x`
 >- (Rewr' >> REWRITE_TAC [FN_PLUS_TO_MINUS])
 >> SIMP_TAC std_ss [fn_plus_def, fn_minus_def]
 >> Know `-f x + -g x = -(f x + g x)`
 >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC neg_add >> art []) >> Rewr
 >> `0 < -(f x + g x) <=> f x + g x < 0` by PROVE_TAC [neg_0, lt_neg] >> POP_ORW
 >> REWRITE_TAC []);

val FN_PLUS_LE_ABS = store_thm
  ("FN_PLUS_LE_ABS", ``!f x. fn_plus f x <= abs (f x)``,
    rpt GEN_TAC
 >> REWRITE_TAC [SIMP_RULE std_ss [o_DEF] FN_ABS]
 >> ACCEPT_TAC
      (REWRITE_RULE [le_refl, add_rzero, FN_MINUS_POS]
                    (Q.SPECL [`fn_plus f x`, `fn_plus f x`, `0`, `fn_minus f x`] le_add2)));

val FN_MINUS_LE_ABS = store_thm
  ("FN_MINUS_LE_ABS", ``!f x. fn_minus f x <= abs (f x)``,
    rpt GEN_TAC
 >> REWRITE_TAC [SIMP_RULE std_ss [o_DEF] FN_ABS]
 >> ACCEPT_TAC
      (REWRITE_RULE [le_refl, add_lzero, FN_PLUS_POS]
                    (Q.SPECL [`0`, `fn_plus f x`, `fn_minus f x`, `fn_minus f x`] le_add2)));

(* ******************************************* *)
(*   Non-negative functions                    *)
(* ******************************************* *)

val nonneg_def = Define
   `nonneg (f :'a -> extreal) = !x. 0 <= f x`;

val nonneg_abs = store_thm
  ("nonneg_abs", ``!f. nonneg (abs o f)``,
    RW_TAC std_ss [o_DEF, nonneg_def, abs_pos]);

val nonneg_fn_plus = store_thm
  ("nonneg_fn_plus", ``!f. nonneg f ==> (fn_plus f = f)``,
    RW_TAC std_ss [nonneg_def, fn_plus_def]
 >> FUN_EQ_TAC
 >> RW_TAC std_ss []
 >> PROVE_TAC [le_lt]);

val nonneg_fn_minus = store_thm
  ("nonneg_fn_minus", ``!f. nonneg f ==> (fn_minus f = (\x. 0))``,
    RW_TAC std_ss [nonneg_def, fn_minus_def]
 >> FUN_EQ_TAC
 >> RW_TAC std_ss [extreal_lt_def]);


(* ******************************************* *)
(*    Borel Space and Measurable functions     *)
(* ******************************************* *)

(* c.f. "borel_space_def" of (old) real_borelTheory *)
val Borel_def = Define
   `Borel = sigma univ(:extreal) (IMAGE (\a. {x | x < Normal a}) univ(:real))`;

(* compatible with (old) real_borelTheory *)
val _ = overload_on ("borel_measurable", ``\a. measurable a Borel``);

val SPACE_BOREL = store_thm
  ("SPACE_BOREL", ``space Borel = UNIV``,
    METIS_TAC [Borel_def, sigma_def, space_def]);

val SIGMA_ALGEBRA_BOREL = store_thm
  ("SIGMA_ALGEBRA_BOREL", ``sigma_algebra Borel``,
    RW_TAC std_ss [Borel_def]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
 >> RW_TAC std_ss [subset_class_def,SUBSET_UNIV]);

val MEASURABLE_BOREL = store_thm
  ("MEASURABLE_BOREL",
  ``!f a. f IN measurable a Borel =
         sigma_algebra a /\ f IN (space a -> UNIV) /\
         !c. ((PREIMAGE f {x| x < Normal c}) INTER (space a)) IN subsets a``,
    RW_TAC std_ss []
 >> `sigma_algebra Borel` by RW_TAC std_ss [SIGMA_ALGEBRA_BOREL]
 >> `space Borel = UNIV` by RW_TAC std_ss [Borel_def, space_def, SPACE_SIGMA]
 >> EQ_TAC
 >- (RW_TAC std_ss [Borel_def, IN_MEASURABLE, IN_FUNSET, IN_UNIV, subsets_def, GSPECIFICATION]
     >> POP_ASSUM MATCH_MP_TAC
     >> MATCH_MP_TAC IN_SIGMA
     >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
     >> METIS_TAC [])
 >> RW_TAC std_ss [Borel_def]
 >> MATCH_MP_TAC MEASURABLE_SIGMA
 >> RW_TAC std_ss [subset_class_def,SUBSET_UNIV,IN_IMAGE,IN_UNIV]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL = store_thm
  ("IN_MEASURABLE_BOREL",
  ``!f a. f IN measurable a Borel =
          sigma_algebra a /\ f IN (space a -> UNIV) /\
          !c. ({x | f x < Normal c} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  >> `!c. {x | f x < Normal c} = PREIMAGE f {x| x < Normal c}`
       by RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION]
  >> RW_TAC std_ss [MEASURABLE_BOREL]);

val IN_MEASURABLE_BOREL_NEGINF = store_thm
  ("IN_MEASURABLE_BOREL_NEGINF",
  ``!f a. f IN measurable a Borel ==>
          ({x | f x = NegInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> Know `{x | f x = NegInf} INTER space a =
          BIGINTER (IMAGE (\n. {x | f x < -(&n)} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC >- METIS_TAC [num_not_infty,lt_infty,extreal_ainv_def,extreal_of_num_def] \\
     RW_TAC std_ss [] \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     METIS_TAC [SIMP_EXTREAL_ARCH_NEG, extreal_lt_def,extreal_ainv_def,neg_neg,lt_neg])
 >> Rewr'
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `- &n = Normal (- &n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_NOT_POSINF = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_NOT_POSINF",
  ``!f a. f IN measurable a Borel ==>
          ({x | f x <> PosInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> Know `{x | f x <> PosInf} INTER space a =
          BIGUNION (IMAGE (\n. {x | f x < &n} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (rpt STRIP_TAC \\
         `?n. f x <= &n` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC n` >> art [] \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n` >> art [] \\
         SIMP_TAC arith_ss [extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >- METIS_TAC [num_not_infty, lt_infty] \\
     ASM_REWRITE_TAC [])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | f x < c} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [lt_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- (REWRITE_TAC [GSYM lt_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [])
 >> fs [IN_MEASURABLE_BOREL]);

(* the same theorems with more meaningful names, new *)
val IN_MEASURABLE_BOREL_RO = save_thm
  ("IN_MEASURABLE_BOREL_RO", IN_MEASURABLE_BOREL_IMP);

val IN_MEASURABLE_BOREL_ALT1 = store_thm
  ("IN_MEASURABLE_BOREL_ALT1",
  ``!f a. f IN measurable a Borel =
          sigma_algebra a /\ f IN (space a -> UNIV) /\
          !c. ({x | Normal c <= f x} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> EQ_TAC
 >- (RW_TAC std_ss []
     >> `{x | Normal c <= f x} = PREIMAGE f {x | Normal c <= x}`
         by RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]
     >> `!c. {x | f x < Normal c} = PREIMAGE f {x | x < Normal c}`
         by RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]
     >> `!c. space a DIFF ((PREIMAGE f {x | x < Normal c}) INTER space a) IN subsets a`
         by METIS_TAC [sigma_algebra_def, algebra_def]
     >> `!c. space a DIFF (PREIMAGE f {x | x < Normal c}) IN subsets a` by METIS_TAC [DIFF_INTER2]
     >> `!c. (PREIMAGE f (COMPL {x | x < Normal c}) INTER space a) IN subsets a`
         by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
     >> `!c. COMPL {x | x < Normal c} = {x | Normal c <= x}`
         by RW_TAC std_ss [EXTENSION, IN_COMPL, IN_UNIV, IN_DIFF, GSPECIFICATION, extreal_lt_def]
     >> FULL_SIMP_TAC std_ss [])
 >> RW_TAC std_ss []
 >> `{x | f x < Normal c} = PREIMAGE f {x | x < Normal c}`
     by RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]
 >> `!c. {x | Normal c <= f x} = PREIMAGE f {x | Normal c <= x}`
     by RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]
 >> `!c. space a DIFF ((PREIMAGE f {x | Normal c <= x}) INTER space a) IN subsets a`
     by METIS_TAC [sigma_algebra_def,algebra_def]
 >> `!c. space a DIFF (PREIMAGE f {x | Normal c <= x}) IN subsets a` by METIS_TAC [DIFF_INTER2]
 >> `!c. (PREIMAGE f (COMPL {x | Normal c <= x}) INTER space a) IN subsets a`
     by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
 >> `!c. COMPL {x | Normal c <= x} = {x | x < Normal c}`
     by RW_TAC std_ss [EXTENSION, IN_COMPL, IN_UNIV, IN_DIFF, GSPECIFICATION, extreal_lt_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT2 = store_thm
  ("IN_MEASURABLE_BOREL_ALT2",
  ``!f a. f IN measurable a Borel =
          sigma_algebra a /\ f IN (space a -> UNIV) /\
          !c. ({x | f x <= Normal c} INTER space a) IN subsets a``,
    RW_TAC std_ss []
 >> EQ_TAC
 >- (RW_TAC std_ss [IN_MEASURABLE_BOREL]
     >> `!c. {x | f x <= Normal c} INTER (space a) =
             BIGINTER (IMAGE (\n:num. {x | f x < Normal (c + (1/2) pow n)} INTER space a) UNIV)`
        by (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV,IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss [GSPECIFICATION,GSYM extreal_add_def]
                >> `0:real < (1 / 2) pow n` by RW_TAC real_ss [REAL_POW_LT]
                >> `0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
                >> Cases_on `f x = NegInf` >- METIS_TAC [lt_infty,extreal_add_def]
                >> METIS_TAC [let_add2,extreal_of_num_def,extreal_not_infty,add_rzero,le_infty])
             >> RW_TAC std_ss [GSPECIFICATION]
             >> `!n. f x < Normal (c + (1 / 2) pow n)` by METIS_TAC []
             >> `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n) ` by RW_TAC real_ss [FUN_EQ_THM]
             >> `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
             >> `(\n. c + (1 / 2) pow n) --> c` by METIS_TAC [SEQ_CONST, Q.SPECL [`(\n:num. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD,REAL_ADD_RID]
             >> Cases_on `f x = NegInf` >- METIS_TAC [le_infty]
             >> `f x <> PosInf` by METIS_TAC [lt_infty]
             >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
             >> FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
             >> METIS_TAC [REAL_LT_IMP_LE,
                           Q.SPECL [`r`,`c`,`(\n. c + (1 / 2) pow n)`] LE_SEQ_IMP_LE_LIM])
     >> `BIGINTER (IMAGE (\n:num. {x | f x < Normal (c + (1 / 2) pow n)} INTER space a) UNIV)
           IN subsets a`
         by (RW_TAC std_ss []
             >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN_BIGINTER
             >> RW_TAC std_ss []
             >> `(\n. {x | f x < Normal (c + (1/2) pow n)} INTER space a) IN (UNIV -> subsets a)`
                 by (RW_TAC std_ss [IN_FUNSET])
             >> METIS_TAC [])
     >> METIS_TAC [])
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c. {x | f x < Normal c} INTER (space a) =
         BIGUNION (IMAGE (\n:num. {x | f x <= Normal (c - (1/2) pow n)} INTER space a) UNIV)`
     by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV,IN_INTER,GSPECIFICATION]
         >> `(\n. c - (1 / 2) pow n) = (\n. (\n. c) n - (\n. (1 / 2) pow n) n)`
             by RW_TAC real_ss [FUN_EQ_THM]
         >> `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST]
         >> `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
         >> `(\n. c - (1 / 2) pow n) --> c`
             by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_SUB, REAL_SUB_RZERO]
         >> EQ_TAC
         >- (RW_TAC std_ss []
             >> Cases_on `f x = NegInf` >- METIS_TAC [le_infty]
             >> `f x <> PosInf` by METIS_TAC [lt_infty]
             >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
             >> FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
             >> `!e:real. 0 < e ==> ?N. !n. n >= N ==> abs ((1 / 2) pow n) < e`
                 by FULL_SIMP_TAC real_ss [Q.SPECL [`(\n. (1/2) pow n)`,`0`] SEQ, REAL_SUB_RZERO]
             >> `!n. abs ((1 / 2) pow n):real = (1 / 2) pow n`
                 by FULL_SIMP_TAC real_ss [POW_POS, ABS_REFL]
             >> `!e:real. 0 < e ==> ?N. !n. n >= N ==> (1 / 2) pow n < e` by METIS_TAC []
             >> `?N. !n. n >= N ==> (1 / 2) pow n < c - r` by METIS_TAC [REAL_SUB_LT]
             >> Q.EXISTS_TAC `N`
             >> `(1 / 2) pow N < c - r` by FULL_SIMP_TAC real_ss []
             >> FULL_SIMP_TAC real_ss [GSYM REAL_LT_ADD_SUB,REAL_ADD_COMM,REAL_LT_IMP_LE])
         >> RW_TAC std_ss []
         >- (`!n. - ((1 / 2) pow n) < 0:real`
              by METIS_TAC [REAL_POW_LT, REAL_NEG_0, REAL_LT_NEG, EVAL ``0:real < 1/2``]
             >> `!n. c - (1 / 2) pow n < c` by METIS_TAC [REAL_LT_IADD,REAL_ADD_RID,real_sub]
             >> Cases_on `f x = NegInf` >- METIS_TAC [lt_infty]
             >> `f x <> PosInf` by METIS_TAC [le_infty,extreal_not_infty]
             >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
             >> FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
             >> METIS_TAC [REAL_LET_TRANS])
         >> METIS_TAC [])
 >> FULL_SIMP_TAC std_ss []
 >> MATCH_MP_TAC SIGMA_ALGEBRA_ENUM
 >> RW_TAC std_ss [IN_FUNSET]);

val IN_MEASURABLE_BOREL_ALT2_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT2_IMP",
  ``!f a. f IN measurable a Borel ==> !c. ({x | f x <= c} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [])
 >- (REWRITE_TAC [le_infty, GSPEC_T, INTER_UNIV] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_SPACE])
 >> fs [IN_MEASURABLE_BOREL_ALT2]);

val IN_MEASURABLE_BOREL_RC = save_thm
  ("IN_MEASURABLE_BOREL_RC", IN_MEASURABLE_BOREL_ALT2_IMP);

val IN_MEASURABLE_BOREL_ALT3 = store_thm
  ("IN_MEASURABLE_BOREL_ALT3",
  ``!f a. f IN measurable a Borel =
          sigma_algebra a /\ f IN (space a -> UNIV) /\
          !c. ({x | Normal c < f x} INTER space a) IN subsets a``,
 RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2,GSPECIFICATION]
 >> EQ_TAC
 >- (RW_TAC std_ss []
     >> `{x|Normal c < f x} = PREIMAGE f {x | Normal c < x}` by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
     >> `!c. {x | f x <= Normal c} = PREIMAGE f {x | x <= Normal c}` by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
     >> `!c. space a DIFF ((PREIMAGE f {x | x <= Normal c}) INTER space a) IN subsets a` by METIS_TAC [sigma_algebra_def,algebra_def]
     >> `!c. space a DIFF (PREIMAGE f {x | x <= Normal c}) IN subsets a` by METIS_TAC [DIFF_INTER2]
     >> `!c. (PREIMAGE f (COMPL {x | x <= Normal c}) INTER space a) IN subsets a` by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
     >> `COMPL {x | x <= Normal c} = {x | Normal c < x}` by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_COMPL,extreal_lt_def]
     >> METIS_TAC [])
 >> RW_TAC std_ss []
 >> `{x | f x <= Normal c} = PREIMAGE f {x | x <= Normal c}` by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
 >> `!c. { x | Normal c < f x } = PREIMAGE f { x | Normal c < x }` by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
 >> `!c. space a DIFF ((PREIMAGE f {x | Normal c < x}) INTER space a) IN subsets a` by METIS_TAC [sigma_algebra_def,algebra_def]
 >> `!c. space a DIFF (PREIMAGE f {x | Normal c < x}) IN subsets a` by METIS_TAC [DIFF_INTER2]
 >> `!c. (PREIMAGE f (COMPL {x | Normal c < x}) INTER space a) IN subsets a` by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
 >> `COMPL {x | Normal c < x} = {x | x <= Normal c}` by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_COMPL,extreal_lt_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_POSINF = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_POSINF",
  ``!f a. f IN measurable a Borel ==>
          ({x | f x = PosInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT3, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> Know `{x | f x = PosInf} INTER space a =
          BIGINTER (IMAGE (\n. {x | &n < f x} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC >- METIS_TAC [num_not_infty, lt_infty, extreal_ainv_def, extreal_of_num_def] \\
     RW_TAC std_ss [] \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     METIS_TAC [SIMP_EXTREAL_ARCH, extreal_lt_def])
 >> Rewr'
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_NOT_NEGINF = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_NOT_NEGINF",
  ``!f a. f IN measurable a Borel ==>
          ({x | f x <> NegInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT3, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> Know `{x | f x <> NegInf} INTER space a =
          BIGUNION (IMAGE (\n. {x | -(&n) < f x} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (rpt STRIP_TAC \\
         `?n. -(&n) <= f x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC `SUC n` >> art [] \\
         MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >- METIS_TAC [num_not_infty, lt_infty] \\
     ASM_REWRITE_TAC [])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT1_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT1_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | c <= f x} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [le_infty, GSPEC_T, INTER_UNIV] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_SPACE])
 >- (REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [])
 >> fs [IN_MEASURABLE_BOREL_ALT1]);

val IN_MEASURABLE_BOREL_CR = save_thm
  ("IN_MEASURABLE_BOREL_CR", IN_MEASURABLE_BOREL_ALT1_IMP);

val IN_MEASURABLE_BOREL_ALT3_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT3_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | c < f x} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [])
 >- (REWRITE_TAC [lt_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >> fs [IN_MEASURABLE_BOREL_ALT3]);

val IN_MEASURABLE_BOREL_OR = save_thm
  ("IN_MEASURABLE_BOREL_OR", IN_MEASURABLE_BOREL_ALT3_IMP);

val IN_MEASURABLE_BOREL_ALT4 = store_thm
  ("IN_MEASURABLE_BOREL_ALT4",
  ``!f a. (!x. f x <> NegInf) ==>
          (f IN measurable a Borel =
           sigma_algebra a /\ f IN (space a -> UNIV) /\
           !c d. ({x | Normal c <= f x /\ f x < Normal d} INTER space a) IN subsets a)``,
  RW_TAC std_ss []
  >> EQ_TAC
  >- (STRIP_TAC
      >> CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL]
      >> CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL]
      >> RW_TAC std_ss []
      >> `(!d. {x | f x < Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL]
      >> `(!c. {x | Normal c <= f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
      >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
      >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) IN subsets a`
          by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
      >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) =
                 ({x | Normal c <= f x} INTER {x | f x < Normal d} INTER space a)`
          by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
      >> `{x | Normal c <= f x} INTER {x | f x < Normal d} = {x | Normal c <= f x /\ f x < Normal d}`
          by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> `{x | Normal c <= f x} INTER {x | f x < Normal d} = {x | Normal c <= f x /\ f x < Normal d}`
          by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> METIS_TAC [])
  >> RW_TAC std_ss [IN_MEASURABLE_BOREL]
  >> `!c. {x | f x < Normal c} INTER (space a) =
          BIGUNION (IMAGE (\n:num. {x | Normal (- &n) <= f x /\ f x < Normal c} INTER space a) UNIV)`
        by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV,IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss [GSPECIFICATION]
                >> `f x <> PosInf` by METIS_TAC [lt_infty]
                >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
                >> METIS_TAC [SIMP_REAL_ARCH_NEG,extreal_le_def])
            >> RW_TAC std_ss [GSPECIFICATION] >> METIS_TAC [lt_infty])
  >> `BIGUNION (IMAGE (\n:num. {x | Normal (- &n) <= f x /\ f x < Normal c } INTER space a) UNIV) IN subsets a`
        by (RW_TAC std_ss []
            >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
            >> RW_TAC std_ss []
            >> `(\n. {x | Normal (- &n) <= f x /\ f x < Normal c} INTER space a) IN (UNIV -> subsets a)`
                by (RW_TAC std_ss [IN_FUNSET])
            >> `{x | Normal (-&n) <= f x /\ f x < Normal c} INTER space a IN subsets a` by METIS_TAC []
            >> METIS_TAC [])
  >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT5 = store_thm
  ("IN_MEASURABLE_BOREL_ALT5",
  ``!f a. (!x. f x <> NegInf) ==>
          (f IN measurable a Borel =
           sigma_algebra a /\ f IN (space a -> UNIV) /\
           !c d. ({x | Normal c < f x /\ f x <= Normal d} INTER space a) IN subsets a)``,
    RW_TAC std_ss []
 >> EQ_TAC
 >- ((RW_TAC std_ss [] >| [METIS_TAC [IN_MEASURABLE_BOREL], METIS_TAC [IN_MEASURABLE_BOREL], ALL_TAC])
     >> `(!d. {x | f x <= Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
     >> `(!c. {x | Normal c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
     >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
     >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) IN subsets a`
          by METIS_TAC [sigma_algebra_def,ALGEBRA_INTER]
     >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x <=  Normal d} INTER space a)) =
                ({x | Normal c < f x} INTER {x | f x <= Normal d} INTER space a)`
          by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
     >> `{x | Normal c < f x} INTER {x | f x <= Normal d} = {x | Normal c < f x /\ f x <= Normal d}`
          by RW_TAC std_ss [EXTENSION ,GSPECIFICATION, IN_INTER]
     >> `{x | Normal c < f x} INTER {x | f x <= Normal d} = {x | Normal c < f x /\ f x <= Normal d}`
          by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
     >> METIS_TAC [])
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2]
 >> `!c. {x | f x <= Normal c} INTER (space a) =
          BIGUNION (IMAGE (\n:num. {x | Normal (- &n) < f x /\ f x <= Normal c } INTER space a) UNIV)`
        by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss [GSPECIFICATION]
                >> `f x <> PosInf` by METIS_TAC [le_infty,extreal_not_infty]
                >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
                >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
                >> (MP_TAC o Q.SPEC `r`) SIMP_REAL_ARCH_NEG
                >> RW_TAC real_ss []
                >> Q.EXISTS_TAC `n+1`
                >> ONCE_REWRITE_TAC [GSYM REAL_ADD]
                >> RW_TAC real_ss [REAL_NEG_ADD, REAL_LT_ADD_SUB,REAL_LT_ADD1])
            >> RW_TAC std_ss [GSPECIFICATION] >> METIS_TAC [lt_infty])
 >> `BIGUNION (IMAGE (\n:num. {x | Normal (- &n) < f x /\ f x <= Normal c } INTER space a) UNIV) IN subsets a`
     by (RW_TAC std_ss []
         >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
         >> RW_TAC std_ss []
         >> `(\n. {x | Normal (-&n) < f x /\ f x <= Normal c} INTER space a) IN (UNIV -> subsets a)`
            by FULL_SIMP_TAC real_ss [IN_FUNSET, GSPECIFICATION, IN_INTER]
         >> `{x | Normal (-&n) < f x /\ f x <= Normal c} INTER space a IN subsets a` by METIS_TAC []
         >> METIS_TAC [])
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT6 = store_thm
  ("IN_MEASURABLE_BOREL_ALT6",
  ``!f a. (!x. f x <> NegInf) ==>
          (f IN measurable a Borel =
           sigma_algebra a /\ f IN (space a -> UNIV) /\
           !c d. ({x| Normal c <= f x /\ f x <= Normal d} INTER space a) IN subsets a)``,
  RW_TAC std_ss []
  >> EQ_TAC
  >- ((RW_TAC std_ss [] >| [METIS_TAC [IN_MEASURABLE_BOREL], METIS_TAC [IN_MEASURABLE_BOREL], ALL_TAC])
      >> `(!d. {x | f x <= Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
      >> `(!c. {x | Normal c <= f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
      >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
      >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) IN subsets a`
         by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
      >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) =
                ({x | Normal c <= f x} INTER {x | f x <= Normal d} INTER space a)`
         by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
      >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
         by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
         by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> METIS_TAC [])
  >> RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT4]
  >> `!c. {x | Normal c <= f x /\ f x < Normal d} INTER (space a) =
          BIGUNION (IMAGE (\n:num. {x | Normal c <= f x /\ f x <= Normal (d - (1/2) pow n)} INTER space a) UNIV)`
      by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER, GSPECIFICATION]
          >> `(\n. c - (1 / 2) pow n) = (\n. (\n. c) n - (\n. (1 / 2) pow n) n) ` by RW_TAC real_ss [FUN_EQ_THM]
          >> `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST]
          >> `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
          >> `(\n. c - (1 / 2) pow n) --> c`
             by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_SUB,REAL_SUB_RZERO]
          >> EQ_TAC
          >- (RW_TAC std_ss []
              >> `!e:real. 0 < e ==> ?N. !n. n >= N ==> abs ((1 / 2) pow n) < e`
                 by FULL_SIMP_TAC real_ss [Q.SPECL [`(\n. (1/2) pow n)`,`0`] SEQ,REAL_SUB_RZERO]
              >> `!n. abs ((1/2) pow n) = ((1/2) pow n):real` by FULL_SIMP_TAC real_ss [POW_POS,ABS_REFL]
              >> `!e:real. 0 < e ==> ?N. !n. n >= N ==> (1 / 2) pow n < e` by METIS_TAC []
              >> `f x <> PosInf` by METIS_TAC [lt_infty]
              >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
              >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
              >> `?N. !n. n >= N ==> (1 / 2) pow n < d - r` by METIS_TAC [REAL_SUB_LT]
              >> Q.EXISTS_TAC `N`
              >> `(1 / 2) pow N < d - r` by FULL_SIMP_TAC real_ss []
              >> FULL_SIMP_TAC real_ss [GSYM REAL_LT_ADD_SUB, REAL_ADD_COMM, REAL_LT_IMP_LE])
          >> RW_TAC std_ss [] >|
             [ METIS_TAC[],
               `!n. - ((1 / 2) pow n) < 0:real` by METIS_TAC [REAL_POW_LT, REAL_NEG_0, REAL_LT_NEG, EVAL ``0:real < 1/2``]
               >> `!n. d - (1 / 2) pow n < d` by METIS_TAC [REAL_LT_IADD, REAL_ADD_RID, real_sub]
               >> `f x <> PosInf` by METIS_TAC [le_infty,extreal_not_infty]
               >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
               >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
               >> METIS_TAC [REAL_LET_TRANS],
               METIS_TAC [] ])
  >> `BIGUNION (IMAGE (\n:num. {x | Normal c <= f x /\ f x <= Normal (d - ((1 / 2) pow n))} INTER space a) UNIV)
      IN subsets a`
      by (RW_TAC std_ss []
          >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
          >> RW_TAC std_ss []
          >> `(\n. {x | Normal c <= f x /\ f x <= Normal (d - ((1 / 2) pow n))} INTER space a) IN (UNIV -> subsets a)`
             by FULL_SIMP_TAC real_ss [IN_FUNSET, GSPECIFICATION, IN_INTER]
          >> `{x | Normal c <= f x /\ f x <= Normal (d - ((1/2) pow n))} INTER space a IN subsets a` by METIS_TAC []
          >> METIS_TAC [])
  >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7 = store_thm
  ("IN_MEASURABLE_BOREL_ALT7",
  ``!f a. (!x. f x <> NegInf) ==>
          (f IN measurable a Borel =
           sigma_algebra a /\ f IN (space a -> UNIV) /\
           !c d. ({x | Normal c < f x /\ f x < Normal d } INTER space a) IN subsets a)``,
  RW_TAC std_ss []
  >> EQ_TAC
  >- (RW_TAC std_ss [IN_FUNSET,IN_UNIV]
      >- METIS_TAC [IN_MEASURABLE_BOREL]
      >> `(!d. {x | f x < Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL]
      >> `(!c. {x | Normal c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
      >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
      >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) IN subsets a` by METIS_TAC [sigma_algebra_def,ALGEBRA_INTER]
      >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) =
                 ({x | Normal c < f x} INTER {x | f x < Normal d} INTER space a)`
            by METIS_TAC [INTER_ASSOC,INTER_COMM,INTER_IDEMPOT]
      >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}` by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
      >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}` by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
      >> METIS_TAC [])
  >> RW_TAC std_ss [IN_MEASURABLE_BOREL]
  >> `!c. {x | f x < Normal c} INTER (space a) = BIGUNION (IMAGE (\n:num. {x | Normal (- &n) < f x /\ f x < Normal c } INTER space a) UNIV)`
        by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV,IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss [GSPECIFICATION]
                >> `f x <> PosInf` by METIS_TAC [lt_infty]
                >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
                >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
                >> (MP_TAC o Q.SPEC `r`) SIMP_REAL_ARCH_NEG
                     >> RW_TAC real_ss []
                     >> Q.EXISTS_TAC `n + 1`
                     >> ONCE_REWRITE_TAC [GSYM REAL_ADD]
                     >> RW_TAC real_ss [REAL_NEG_ADD, REAL_LT_ADD_SUB,REAL_LT_ADD1])
            >> RW_TAC std_ss [GSPECIFICATION] >> METIS_TAC [lt_infty])
  >> `BIGUNION (IMAGE (\n:num. {x | Normal (- &n) < f x /\ f x < Normal c } INTER space a) UNIV) IN subsets a`
        by (RW_TAC std_ss []
            >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
            >> RW_TAC std_ss []
            >> `(\n. {x | Normal (-&n) < f x /\ f x < Normal c} INTER space a) IN (UNIV -> subsets a)` by FULL_SIMP_TAC real_ss [IN_FUNSET,GSPECIFICATION,IN_INTER]
            >> `{x | Normal (-&n) < f x /\ f x < Normal c} INTER space a IN subsets a` by METIS_TAC []
            >> METIS_TAC [])
  >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT4_IMP_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | Normal c <= f x /\ f x < Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `!d. {x | f x < Normal d} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL]
 >> `!c. {x | Normal c <= f x} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) =
            ({x | Normal c <= f x} INTER {x | f x < Normal d} INTER space a)`
    by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 >> `{x | Normal c <= f x} INTER {x | f x < Normal d} = {x | Normal c <= f x /\ f x < Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT4_IMP_p = prove (
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | Normal c <= f x /\ f x < PosInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> Know `{x | f x < PosInf} INTER space a IN subsets a`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     METIS_TAC [IN_MEASURABLE_BOREL_NOT_POSINF]) >> DISCH_TAC
 >> `!c. {x | Normal c <= f x} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < PosInf} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!c. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < PosInf} INTER space a)) =
          ({x | Normal c <= f x} INTER {x | f x < PosInf} INTER space a)`
    by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 >> `{x | Normal c <= f x} INTER {x | f x < PosInf} = {x | Normal c <= f x /\ f x < PosInf}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT4_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT4_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | c <= f x /\ f x < d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP >> art [])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     SIMP_TAC std_ss [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     `!x. PosInf <= f x /\ f x < Normal r <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT4_IMP_p >> art [])
 (* goal 9 (of 9) *)
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT4_IMP_r >> art []);

val IN_MEASURABLE_BOREL_CO = save_thm
  ("IN_MEASURABLE_BOREL_CO", IN_MEASURABLE_BOREL_ALT4_IMP);

val IN_MEASURABLE_BOREL_ALT5_IMP_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | Normal c < f x /\ f x <= Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `(!d. {x | f x <= Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
 >> `(!c. {x | Normal c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) =
           ({x | Normal c < f x} INTER {x | f x <= Normal d} INTER space a)`
    by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
 >> `{x | Normal c < f x} INTER {x | f x <= Normal d} =
     {x | Normal c < f x /\ f x <= Normal d}` by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT5_IMP_n = prove (
  ``!f a. f IN measurable a Borel ==>
          !d. ({x | NegInf < f x /\ f x <= Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `!d. {x | f x <= Normal d} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
 >> Know `{x | NegInf < f x} INTER space a IN subsets a`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     METIS_TAC [IN_MEASURABLE_BOREL_NOT_NEGINF]) >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!d. (({x | NegInf < f x} INTER space a) INTER
          ({x | f x <= Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!d. (({x | NegInf < f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) =
          ({x | NegInf < f x} INTER {x | f x <= Normal d} INTER space a)`
    by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
 >> `{x | NegInf < f x} INTER {x | f x <= Normal d} =
     {x | NegInf < f x /\ f x <= Normal d}` by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT5_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT5_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | c < f x /\ f x <= d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     `!x. NegInf < f x /\ f x <= NegInf <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [])
 >- ((* goal 3 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT5_IMP_n >> art [])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     `!x. Normal r < f x /\ f x <= NegInf <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT3_IMP >> art [])
 (* goal 9 (of 9) *)
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT5_IMP_r >> art []);

val IN_MEASURABLE_BOREL_OC = save_thm
  ("IN_MEASURABLE_BOREL_OC", IN_MEASURABLE_BOREL_ALT5_IMP);

val IN_MEASURABLE_BOREL_ALT6_IMP_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x| Normal c <= f x /\ f x <= Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET,IN_UNIV]
 >> `(!d. {x | f x <= Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
 >> `(!c. {x | Normal c <= f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def,ALGEBRA_INTER]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) =
           ({x | Normal c <= f x} INTER {x | f x <= Normal d} INTER space a)`
    by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] >> METIS_TAC [])
  >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
    by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
  >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
    by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
  >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT6_IMP  = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT6_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x| c <= f x /\ f x <= d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [le_infty, GSPEC_T, INTER_UNIV] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_SPACE])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT2_IMP >> art [])
 >- ((* goal 4 (of 9) *)
     `!x. PosInf <= f x /\ f x <= NegInf <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, extreal_cases] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [])
 >- ((* goal 6 (of 9) *)
     `!x. PosInf <= f x /\ f x <= Normal r <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     `!x. Normal r <= f x /\ f x <= NegInf <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT1_IMP >> art [])
 (* goal 9 (of 9) *)
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT6_IMP_r >> art []);

val IN_MEASURABLE_BOREL_CC = save_thm
  ("IN_MEASURABLE_BOREL_CC", IN_MEASURABLE_BOREL_ALT6_IMP);

val IN_MEASURABLE_BOREL_ALT7_IMP_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | Normal c < f x /\ f x < Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `(!d. {x | f x < Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL]
 >> `(!c. {x | Normal c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!c d. ({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a) =
           ({x | Normal c < f x} INTER {x | f x < Normal d} INTER space a)`
    by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7_IMP_np = prove ((* new *)
  ``!f a. f IN measurable a Borel ==>
          ({x | NegInf < f x /\ f x < PosInf} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r
 >> fs [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> Know `{x | NegInf < f x /\ f x < PosInf} INTER space a =
          BIGUNION (IMAGE (\n. {x | -&n < f x /\ f x < &n} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n1. -&n1 <= f x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         `?n2. f x <= &n2` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC (MAX n1 n2)` \\
         CONJ_TAC >- (MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n1` >> art [] \\
                      SIMP_TAC std_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT] \\
                      MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC \\
                      REWRITE_TAC [MAX_LE] >> DISJ1_TAC >> REWRITE_TAC [LESS_EQ_REFL]) \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n2` >> art [] \\
         SIMP_TAC std_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT] \\
         MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC \\
         REWRITE_TAC [MAX_LE] >> DISJ2_TAC >> REWRITE_TAC [LESS_EQ_REFL]) \\
     RW_TAC std_ss [] >| (* 3 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       METIS_TAC [num_not_infty, lt_infty],
       ASM_REWRITE_TAC [] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7_IMP_n = prove ((* new *)
  ``!f a. f IN measurable a Borel ==>
          !d. ({x | NegInf < f x /\ f x < Normal d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r
 >> fs [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> Know `{x | NegInf < f x /\ f x < Normal d} INTER space a =
          BIGUNION (IMAGE (\n. {x | -&n < f x /\ f x < Normal d} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n. -&n <= f x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >| (* 3 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       ASM_REWRITE_TAC [],
       ASM_REWRITE_TAC [] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7_IMP_p = prove ((* new *)
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | Normal c < f x /\ f x < PosInf} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r
 >> fs [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> Know `{x | Normal c < f x /\ f x < PosInf} INTER space a =
          BIGUNION (IMAGE (\n. {x | Normal c < f x /\ f x < &n} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n. f x <= &n` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >| (* 3 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       METIS_TAC [num_not_infty, lt_infty],
       ASM_REWRITE_TAC [] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7_IMP = store_thm
  ("IN_MEASURABLE_BOREL_ALT7_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | c < f x /\ f x < d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT7_IMP_np >> art [])
 >- ((* goal 3 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT7_IMP_n >> art [])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT7_IMP_p >> art [])
 (* goal 9 (of 9) *)
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r >> art []);

val IN_MEASURABLE_BOREL_OO = save_thm (* not "00" *)
  ("IN_MEASURABLE_BOREL_OO", IN_MEASURABLE_BOREL_ALT7_IMP);

val IN_MEASURABLE_BOREL_ALT8_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | f x = Normal c} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> MP_TAC IN_MEASURABLE_BOREL_ALT4_IMP_r
 >> RW_TAC std_ss []
 >> `!c. {x | f x = Normal c} INTER (space a) =
         BIGINTER (IMAGE (\n. {x | Normal (c - ((1/2) pow n)) <= f x /\
                                   f x < Normal (c + ((1/2) pow n))} INTER space a) UNIV)`
 by (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV,IN_SING,IN_INTER] \\
     EQ_TAC >- RW_TAC real_ss [extreal_le_def, extreal_lt_eq, GSPECIFICATION, REAL_POW_LT,
                               REAL_LT_IMP_LE, REAL_LT_ADDR, REAL_LT_DIV, HALF_POS,
                               REAL_LT_ADDNEG2, real_sub, IN_INTER] \\
     RW_TAC std_ss [GSPECIFICATION] \\
    `f x <> PosInf` by METIS_TAC [lt_infty] \\
    `f x <> NegInf` by METIS_TAC [le_infty, extreal_not_infty] \\
    `?r. f x = Normal r` by METIS_TAC [extreal_cases] \\
     FULL_SIMP_TAC std_ss [extreal_le_def, extreal_lt_eq, extreal_11] \\
    `!n. c - (1 / 2) pow n <= r` by FULL_SIMP_TAC real_ss [real_sub] \\
    `!n. r <= c + (1 / 2) pow n` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_LE] \\
    `(\n. c - (1 / 2) pow n) = (\n. (\n. c) n - (\n. (1 / 2) pow n) n)`
        by RW_TAC real_ss [FUN_EQ_THM] \\
    `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n)`
        by RW_TAC real_ss [FUN_EQ_THM] \\
    `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST] \\
    `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER] \\
    `(\n. c - (1 / 2) pow n) --> c`
        by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_SUB, REAL_SUB_RZERO] \\
    `(\n. c + (1 / 2) pow n) --> c`
        by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD, REAL_ADD_RID] \\
    `c <= r` by METIS_TAC [Q.SPECL [`r`,`c`,`(\n. c - (1 / 2) pow n)`] SEQ_LE_IMP_LIM_LE] \\
    `r <= c` by METIS_TAC [Q.SPECL [`r`,`c`,`(\n. c + (1 / 2) pow n)`] LE_SEQ_IMP_LE_LIM] \\
     METIS_TAC [REAL_LE_ANTISYM])
 >> Know `BIGINTER (IMAGE (\n. {x | Normal (c - ((1/2) pow n)) <= f x /\
                               f x < Normal (c + ((1/2) pow n))} INTER space a)
                    UNIV) IN subsets a`
 >- (RW_TAC std_ss [] \\
     (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN_BIGINTER \\
     RW_TAC std_ss [] \\
    `(\n. {x | Normal (c - ((1/2) pow n)) <= f x /\
               f x < Normal (c + ((1/2) pow n))} INTER space a) IN (UNIV -> subsets a)`
        by (RW_TAC std_ss [IN_FUNSET]) \\
     METIS_TAC [IN_MEASURABLE_BOREL])
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT8 = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT8",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | f x = c} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      RW_TAC std_ss [IN_MEASURABLE_BOREL] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [IN_MEASURABLE_BOREL],
      (* goal 2 (of 3) *)
      RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT3] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [IN_MEASURABLE_BOREL_ALT3],
      (* goal 3 (of 3) *)
      IMP_RES_TAC IN_MEASURABLE_BOREL_ALT8_r >> art [] ]);

val IN_MEASURABLE_BOREL_SING = save_thm
  ("IN_MEASURABLE_BOREL_SING", IN_MEASURABLE_BOREL_ALT8);

val IN_MEASURABLE_BOREL_ALT9 = store_thm
  ("IN_MEASURABLE_BOREL_ALT9",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | f x <> c} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_SING
 >> Know `!c. {x | f x <> c} INTER (space a) =
              space a DIFF ({x | f x = c} INTER space a)`
 >- (RW_TAC std_ss [EXTENSION, IN_UNIV, IN_DIFF, IN_INTER, GSPECIFICATION] \\
     EQ_TAC >- (rpt STRIP_TAC >> art []) \\
     METIS_TAC []) >> Rewr
 >> fs [IN_MEASURABLE_BOREL]
 >> MATCH_MP_TAC ALGEBRA_COMPL
 >> CONJ_TAC
 >- IMP_RES_TAC SIGMA_ALGEBRA_ALGEBRA
 >> ASM_REWRITE_TAC []);

val IN_MEASURABLE_BOREL_NOT_SING = save_thm
  ("IN_MEASURABLE_BOREL_NOT_SING", IN_MEASURABLE_BOREL_ALT9);

(* all IMP versions of IN_MEASURABLE_BOREL_ALTs *)
val IN_MEASURABLE_BOREL_ALL = store_thm
  ("IN_MEASURABLE_BOREL_ALL",
  ``!f a.
        f IN measurable a Borel ==>
        (!c. {x | f x < c} INTER space a IN subsets a) /\
        (!c. {x | c <= f x} INTER space a IN subsets a) /\
        (!c. {x | f x <= c} INTER space a IN subsets a) /\
        (!c. {x | c < f x} INTER space a IN subsets a) /\
        (!c d. {x | c <= f x /\ f x < d} INTER space a IN subsets a) /\
        (!c d. {x | c < f x /\ f x <= d} INTER space a IN subsets a) /\
        (!c d. {x | c <= f x /\ f x <= d} INTER space a IN subsets a) /\
        (!c d. {x | c < f x /\ f x < d} INTER space a IN subsets a) /\
        (!c. {x | f x = c} INTER space a IN subsets a) /\
        (!c. {x | f x <> c} INTER space a IN subsets a)``,
    METIS_TAC [IN_MEASURABLE_BOREL_RO,         (* f x < c *)
               IN_MEASURABLE_BOREL_CR,         (* c <= f x *)
               IN_MEASURABLE_BOREL_RC,         (* f x <= c *)
               IN_MEASURABLE_BOREL_OR,         (* c < f x *)
               IN_MEASURABLE_BOREL_CO,         (* c <= f x /\ f x < d *)
               IN_MEASURABLE_BOREL_OC,         (* c < f x /\ f x <= d *)
               IN_MEASURABLE_BOREL_CC,         (* c <= f x /\ f x <= d *)
               IN_MEASURABLE_BOREL_OO,         (* c < f x /\ f x < d *)
               IN_MEASURABLE_BOREL_SING,       (* f x = c *)
               IN_MEASURABLE_BOREL_NOT_SING]); (* f x <> c *)

(* |- !f m.
         f IN measurable (m_space m,measurable_sets m) Borel ==>
         (!c. {x | f x < c} INTER m_space m IN measurable_sets m) /\
         (!c. {x | c <= f x} INTER m_space m IN measurable_sets m) /\
         (!c. {x | f x <= c} INTER m_space m IN measurable_sets m) /\
         (!c. {x | c < f x} INTER m_space m IN measurable_sets m) /\
         (!c d. {x | c <= f x /\ f x < d} INTER m_space m IN measurable_sets m) /\
         (!c d. {x | c < f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
         (!c d. {x | c <= f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
         (!c d. {x | c < f x /\ f x < d} INTER m_space m IN measurable_sets m) /\
         !c. {x | f x = c} INTER m_space m IN measurable_sets m /\
         !c. {x | f x <> c} INTER m_space m IN measurable_sets m
 *)
val IN_MEASURABLE_BOREL_ALL_MEASURE = save_thm
  ("IN_MEASURABLE_BOREL_ALL_MEASURE",
  ((Q.GENL [`f`, `m`]) o
   (REWRITE_RULE [space_def, subsets_def]) o
   (Q.SPECL [`f`, `(m_space m,measurable_sets m)`])) IN_MEASURABLE_BOREL_ALL);

val IN_MEASURABLE_BOREL_LT = store_thm
  ("IN_MEASURABLE_BOREL_LT",
  ``!f g a. f IN measurable a Borel /\ g IN measurable a Borel ==>
            ({x | f x < g x} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  >> `{x | f x < g x} INTER space a =
      BIGUNION (IMAGE (\r. {x | f x < r /\ r < g x} INTER space a) Q_set)`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_INTER]
            >> EQ_TAC
            >- RW_TAC std_ss [Q_DENSE_IN_R]
            >> METIS_TAC [lt_trans])
  >> POP_ORW
  >> MATCH_MP_TAC BIGUNION_IMAGE_Q
  >> CONJ_TAC
  >- FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
  >> RW_TAC std_ss [IN_FUNSET]
  >> `{x | f x < r /\ r < g x} INTER space a =
     ({x | f x < r} INTER space a) INTER ({x | r < g x} INTER space a)`
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
  >> POP_ORW
  >> MATCH_MP_TAC ALGEBRA_INTER
  >> CONJ_TAC
  >- FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL, sigma_algebra_def]
  >> `?c. r = Normal c` by METIS_TAC [rat_not_infty, extreal_cases]
  >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]);

val IN_MEASURABLE_BOREL_LE = store_thm
  ("IN_MEASURABLE_BOREL_LE",
  ``!f g a. f IN measurable a Borel /\ g IN measurable a Borel ==>
                 ({x | f x <= g x} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  >> `{x | f x <= g x} INTER space a = space a DIFF ({x | g x < f x} INTER space a)`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF]
          >> METIS_TAC [extreal_lt_def])
  >> `{x | g x < f x} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_LT]
  >> METIS_TAC [algebra_def, IN_MEASURABLE_BOREL, sigma_algebra_def]);

(*****************************************************)

val BOREL_MEASURABLE_SETS_RO_r = prove (
  ``!c. {x | x < Normal c} IN subsets Borel``,
    RW_TAC std_ss [Borel_def]
 >> MATCH_MP_TAC IN_SIGMA
 >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> METIS_TAC []);

val BOREL_MEASURABLE_SETS_NEGINF = prove ((* new *)
  ``{x | x = NegInf} IN subsets Borel``,
    Know `{x | x = NegInf} = BIGINTER (IMAGE (\n. {x | x < -(&n)}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC >- METIS_TAC [num_not_infty,lt_infty,extreal_ainv_def,extreal_of_num_def] \\
     RW_TAC std_ss [] \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     METIS_TAC [SIMP_EXTREAL_ARCH_NEG, extreal_lt_def, extreal_ainv_def, neg_neg, lt_neg])
 >> Rewr'
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (- &n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def] >> POP_ORW
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_RO_r]);

val BOREL_MEASURABLE_SETS_NEGINF' = prove ((* new *)
  ``{NegInf} IN subsets Borel``,
    Know `{NegInf} = {x | x = NegInf}`
 >- RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING]
 >> Rewr' >> REWRITE_TAC [BOREL_MEASURABLE_SETS_NEGINF]);

val BOREL_MEASURABLE_SETS_NOT_POSINF = prove ((* new *)
  ``{x | x <> PosInf} IN subsets Borel``,
    Know `{x | x <> PosInf} = BIGUNION (IMAGE (\n. {x | x < &n}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (DISCH_TAC \\
         `?n. x <= &n` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n` >> art [] \\
         SIMP_TAC arith_ss [extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >> METIS_TAC [num_not_infty, lt_infty])
 >> Rewr'
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def] >> POP_ORW
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_RO_r]);

val BOREL_MEASURABLE_SETS_RO = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_RO", ``!c. {x | x < c} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- (REWRITE_TAC [lt_infty, GSPEC_F, INTER_EMPTY] \\
     PROVE_TAC [SIGMA_ALGEBRA_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- REWRITE_TAC [GSYM lt_infty, BOREL_MEASURABLE_SETS_NOT_POSINF]
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_RO_r]);

val BOREL_MEASURABLE_SETS_CR_r = prove (
  ``!c. {x | Normal c <= x} IN subsets Borel``,
    RW_TAC std_ss []
 >> `{x | Normal c <= x} = UNIV DIFF {x | x < Normal c}`
      by RW_TAC std_ss [extreal_lt_def, EXTENSION, GSPECIFICATION, DIFF_DEF, IN_UNIV, real_lte]
 >> METIS_TAC [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, sigma_algebra_def, algebra_def,
               BOREL_MEASURABLE_SETS_RO]);

val BOREL_MEASURABLE_SETS_RC_r = prove (
  ``!c. {x | x <= Normal c} IN subsets Borel``,
    RW_TAC std_ss []
 >> `!c. {x | x <= Normal c} = BIGINTER (IMAGE (\n:num. {x | x < Normal (c + (1/2) pow n)}) UNIV)`
         by (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV,IN_INTER]
             >> EQ_TAC
             >- (RW_TAC std_ss [GSPECIFICATION]
                 >> `0:real < (1/2) pow n` by RW_TAC real_ss [REAL_POW_LT]
                 >> Cases_on `x = NegInf` >- METIS_TAC [lt_infty]
                 >> `x <> PosInf` by METIS_TAC [le_infty,extreal_not_infty]
                 >> `0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def]
                 >> RW_TAC std_ss [GSYM extreal_add_def]
                 >> METIS_TAC [extreal_of_num_def,extreal_not_infty,let_add2,add_rzero])
                    >> RW_TAC std_ss [GSPECIFICATION]
                    >> `!n. x < Normal (c + (1 / 2) pow n)` by METIS_TAC []
                    >> `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n)`
                  by RW_TAC real_ss [FUN_EQ_THM]
                    >> `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST]
                    >> `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
                    >> `(\n. c + (1 / 2) pow n) --> c`
                  by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD,REAL_ADD_RID]
             >> Cases_on `x = NegInf` >- RW_TAC std_ss [le_infty]
             >> `x <> PosInf` by METIS_TAC [lt_infty]
             >> `?r. x = Normal r` by METIS_TAC [extreal_cases]
             >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
             >> METIS_TAC [REAL_LT_IMP_LE,
                           Q.SPECL [`r`,`c`,`(\n. c + (1 / 2) pow n)`] LE_SEQ_IMP_LE_LIM])
 >> FULL_SIMP_TAC std_ss []
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> (MP_TAC o UNDISCH o Q.SPEC `Borel`)
        (INST_TYPE [alpha |-> ``:extreal``] SIGMA_ALGEBRA_FN_BIGINTER)
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!f. P f ==> Q f` (MP_TAC o Q.SPEC `(\n. {x | x < Normal (c + (1 / 2) pow n)})`)
 >> `(\n. {x | x < Normal (c + (1 / 2) pow n)}) IN (UNIV -> subsets Borel)`
        by RW_TAC std_ss [IN_FUNSET,BOREL_MEASURABLE_SETS_RO]
 >> METIS_TAC []);

val BOREL_MEASURABLE_SETS_RC = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_RC", ``!c. {x | x <= c} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- (REWRITE_TAC [le_infty, BOREL_MEASURABLE_SETS_NEGINF])
 >- (REWRITE_TAC [le_infty, GSPEC_T] \\
     PROVE_TAC [SIGMA_ALGEBRA_BOREL, sigma_algebra_def, ALGEBRA_SPACE, SPACE_BOREL])
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_RC_r]);

val BOREL_MEASURABLE_SETS_OR_r = prove (
  ``!c. {x | Normal c < x} IN subsets Borel``,
    GEN_TAC
 >> `{x | Normal c < x} = UNIV DIFF {x | x <= Normal c}`
        by RW_TAC std_ss [extreal_lt_def, EXTENSION, GSPECIFICATION, DIFF_DEF, IN_UNIV, real_lte]
 >> METIS_TAC [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, sigma_algebra_def, algebra_def,
               BOREL_MEASURABLE_SETS_RC]);

val BOREL_MEASURABLE_SETS_NOT_NEGINF = prove ((* new *)
  ``{x | x <> NegInf} IN subsets Borel``,
    Know `{x | x <> NegInf} = BIGUNION (IMAGE (\n. {x | -(&n) < x}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (DISCH_TAC \\
         `?n. -(&n) <= x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >> METIS_TAC [num_not_infty, lt_infty])
 >> Rewr'
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def] >> POP_ORW
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OR_r]);

val BOREL_MEASURABLE_SETS_OR = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_OR", ``!c. {x | c < x} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- (REWRITE_TAC [GSYM lt_infty, BOREL_MEASURABLE_SETS_NOT_NEGINF])
 >- (REWRITE_TAC [lt_infty, GSPEC_F] \\
     PROVE_TAC [SIGMA_ALGEBRA_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OR_r]);

val BOREL_MEASURABLE_SETS_POSINF = prove ((* new *)
  ``{x | x = PosInf} IN subsets Borel``,
    Know `{x | x = PosInf} = BIGINTER (IMAGE (\n. {x | &n < x}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC >- METIS_TAC [num_not_infty, lt_infty, extreal_ainv_def, extreal_of_num_def] \\
     RW_TAC std_ss [] \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     METIS_TAC [SIMP_EXTREAL_ARCH, extreal_lt_def])
 >> Rewr'
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def] >> POP_ORW
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OR]);

val BOREL_MEASURABLE_SETS_POSINF' = prove ((* new *)
  ``{PosInf} IN subsets Borel``,
    Know `{PosInf} = {x | x = PosInf}`
 >- RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING]
 >> Rewr' >> REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF]);

val BOREL_MEASURABLE_SETS_CR = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_CR",
  ``!c. {x | c <= x} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- (REWRITE_TAC [le_infty, GSPEC_T] \\
     PROVE_TAC [SIGMA_ALGEBRA_BOREL, sigma_algebra_def, ALGEBRA_SPACE, SPACE_BOREL])
 >- REWRITE_TAC [le_infty, BOREL_MEASURABLE_SETS_POSINF]
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_CR_r]);

val BOREL_MEASURABLE_SETS_CO_r = prove (
  ``!c d. {x | Normal c <= x /\ x < Normal d} IN subsets Borel``,
    rpt GEN_TAC
 >> `!d. {x | x < Normal d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_RO]
 >> `!c. {x | Normal c <= x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_CR]
 >> `{x | Normal c <= x /\ x < Normal d} = {x | Normal c <= x} INTER {x | x < Normal d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_CO_p = prove ((* new *)
  ``!c d. {x | Normal c <= x /\ x < PosInf} IN subsets Borel``,
    rpt GEN_TAC
 >> Know `{x | x < PosInf} IN subsets Borel`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NOT_POSINF]) >> DISCH_TAC
 >> `!c. {x | Normal c <= x} IN subsets Borel` by REWRITE_TAC [BOREL_MEASURABLE_SETS_CR]
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> `!c. {x | Normal c <= x} INTER {x | x < PosInf} IN subsets Borel`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `{x | Normal c <= x /\ x < PosInf} = {x | Normal c <= x} INTER {x | x < PosInf}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> POP_ORW
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val BOREL_MEASURABLE_SETS_CO = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_CO",
  ``!c d. {x | c <= x /\ x < d} IN subsets Borel``,
    rpt GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NOT_POSINF])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_RO])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     SIMP_TAC std_ss [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     `!x. PosInf <= x /\ x < Normal r <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_CO_p])
 (* goal 9 (of 9) *)
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_CO_r]);

val BOREL_MEASURABLE_SETS_OC_r = prove (
  ``!c d. {x | Normal c < x /\ x <= Normal d} IN subsets Borel``,
    rpt GEN_TAC
 >> `!d. {x | x <= Normal d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_RC]
 >> `!c. {x | Normal c < x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_OR]
 >> `{x | Normal c < x /\ x <= Normal d} = {x | Normal c < x} INTER {x | x <= Normal d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_OC_n = prove ((* new *)
  ``!d. {x | NegInf < x /\ x <= Normal d} IN subsets Borel``,
    GEN_TAC
 >> `!d. {x | x <= Normal d} IN subsets Borel` by REWRITE_TAC [BOREL_MEASURABLE_SETS_RC]
 >> Know `{x | NegInf < x} IN subsets Borel`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NOT_NEGINF]) >> DISCH_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> `!d. ({x | NegInf < x} INTER {x | x <= Normal d}) IN subsets Borel`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `{x | NegInf < x /\ x <= Normal d} = {x | NegInf < x} INTER {x | x <= Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> POP_ORW
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_OC = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_OC",
  ``!c d. {x | c < x /\ x <= d} IN subsets Borel``,
    rpt GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     `!x. NegInf < x /\ x <= NegInf <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NOT_NEGINF])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OC_n])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     `!x. Normal r < x /\ x <= NegInf <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OR])
 (* goal 9 (of 9) *)
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OC_r]);

val BOREL_MEASURABLE_SETS_CC_r = prove (
  ``!c d. {x | Normal c <= x /\ x <= Normal d} IN subsets Borel``,
    rpt GEN_TAC
 >> `!d. {x | x <= Normal d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_RC]
 >> `!c. {x | Normal c <= x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_CR]
 >> `{x | Normal c <= x /\ x <= Normal d} = {x | Normal c <= x} INTER {x | x <= Normal d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_CC = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_CC", ``!c d. {x | c <= x /\ x <= d} IN subsets Borel``,
    rpt GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NEGINF])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [le_infty, GSPEC_T] \\
     METIS_TAC [sigma_algebra_def, ALGEBRA_SPACE, SPACE_BOREL])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_RC])
 >- ((* goal 4 (of 9) *)
     `!x. PosInf <= x /\ x <= NegInf <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, extreal_cases] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF])
 >- ((* goal 6 (of 9) *)
     `!x. PosInf <= x /\ x <= Normal r <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     `!x. Normal r <= x /\ x <= NegInf <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_CR])
 (* goal 9 (of 9) *)
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_CC_r]);

val BOREL_MEASURABLE_SETS_OO_r = prove ((* not "00_r" *)
  ``!c d. {x | Normal c < x /\ x < Normal d} IN subsets Borel``,
    rpt GEN_TAC
 >> `!d. {x | x < Normal d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_RO]
 >> `!c. {x | Normal c < x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_OR]
 >> `{x | Normal c < x /\ x < Normal d} = {x | Normal c < x} INTER {x | x < Normal d}`
       by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_OO_np = prove ((* new, not "00_np" *)
  ``{x | NegInf < x /\ x < PosInf} IN subsets Borel``,
    ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Know `{x | NegInf < x /\ x < PosInf} =
          BIGUNION (IMAGE (\n. {x | -&n < x /\ x < &n}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n1. -&n1 <= x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         `?n2. x <= &n2` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC (MAX n1 n2)` \\
         CONJ_TAC >- (MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n1` >> art [] \\
                      SIMP_TAC std_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT] \\
                      MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC \\
                      REWRITE_TAC [MAX_LE] >> DISJ1_TAC >> REWRITE_TAC [LESS_EQ_REFL]) \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n2` >> art [] \\
         SIMP_TAC std_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT] \\
         MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC \\
         REWRITE_TAC [MAX_LE] >> DISJ2_TAC >> REWRITE_TAC [LESS_EQ_REFL]) \\
     RW_TAC std_ss [] >| (* 2 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       METIS_TAC [num_not_infty, lt_infty] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> ASM_REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_r]);

val BOREL_MEASURABLE_SETS_OO_n = prove ((* new, not "00_n" *)
  ``!d. {x | NegInf < x /\ x < Normal d} IN subsets Borel``,
    GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Know `{x | NegInf < x /\ x < Normal d} =
          BIGUNION (IMAGE (\n. {x | -&n < x /\ x < Normal d}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n. -&n <= x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >| (* 2 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       ASM_REWRITE_TAC [] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> ASM_REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_r]);

val BOREL_MEASURABLE_SETS_OO_p = prove ((* new, not "00_p" *)
  ``!c. {x | Normal c < x /\ x < PosInf} IN subsets Borel``,
    GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Know `{x | Normal c < x /\ x < PosInf} =
          BIGUNION (IMAGE (\n. {x | Normal c < x /\ x < &n}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n. x <= &n` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >| (* 3 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       METIS_TAC [num_not_infty, lt_infty] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> ASM_REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_r]);

val BOREL_MEASURABLE_SETS_OO = store_thm (* new, not "00" *)
  ("BOREL_MEASURABLE_SETS_OO", ``!c d. {x | c < x /\ x < d} IN subsets Borel``,
    rpt GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_np])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_n])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_p])
 (* goal 9 (of 9) *)
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_r]);

val BOREL_MEASURABLE_SETS_SING_r = prove (
  ``!c. {Normal c} IN subsets Borel``,
    RW_TAC std_ss []
 >> Know `!c. {Normal c} = BIGINTER (IMAGE (\n. {x | Normal (c - ((1/2) pow n)) <= x /\
                                                     x < Normal (c + ((1/2) pow n))}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, IN_SING, IN_INTER] \\
     EQ_TAC >- RW_TAC real_ss [extreal_lt_eq, extreal_le_def, GSPECIFICATION,
                               REAL_POW_LT, REAL_LT_IMP_LE, REAL_LT_ADDR, REAL_LT_DIV,
                               HALF_POS, REAL_LT_ADDNEG2, real_sub, IN_INTER] \\
     RW_TAC std_ss [GSPECIFICATION] \\
    `!n. Normal (c - (1/2) pow n) <= x` by FULL_SIMP_TAC real_ss [real_sub] \\
    `!n. x <= Normal (c + (1/2) pow n)` by FULL_SIMP_TAC real_ss [lt_imp_le] \\
    `(\n. c - (1/2) pow n) = (\n. (\n. c) n - (\n. (1/2) pow n) n)`
       by RW_TAC real_ss [FUN_EQ_THM] \\
    `(\n. c + (1/2) pow n) = (\n. (\n. c) n + (\n. (1/2) pow n) n)`
       by RW_TAC real_ss [FUN_EQ_THM] \\
    `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST] \\
    `(\n. (1/2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER] \\
    `(\n. c - (1/2) pow n) --> c`
       by METIS_TAC [Q.SPECL [`(\n. c)`, `c`, `(\n. (1/2) pow n)`, `0`] SEQ_SUB, REAL_SUB_RZERO] \\
    `(\n. c + (1/2) pow n) --> c`
       by METIS_TAC [Q.SPECL [`(\n. c)`, `c`, `(\n. (1/2) pow n)`, `0`] SEQ_ADD, REAL_ADD_RID] \\
    `x <> PosInf` by METIS_TAC [lt_infty] \\
    `x <> NegInf` by METIS_TAC [le_infty, extreal_not_infty] \\
    `?r. x = Normal r` by METIS_TAC [extreal_cases] \\
     FULL_SIMP_TAC std_ss [extreal_le_def, extreal_lt_eq, extreal_11] \\
    `c <= r` by METIS_TAC [Q.SPECL [`r`, `c`, `(\n. c - (1/2) pow n)`] SEQ_LE_IMP_LIM_LE] \\
    `r <= c` by METIS_TAC [Q.SPECL [`r`, `c`, `(\n. c + (1/2) pow n)`] LE_SEQ_IMP_LE_LIM] \\
     METIS_TAC [REAL_LE_ANTISYM]) >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> (MP_TAC o UNDISCH o Q.SPEC `Borel` o (INST_TYPE [alpha |-> ``:extreal``]))
      SIGMA_ALGEBRA_FN_BIGINTER
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!f. P f ==> Q f`
     (MP_TAC o
      Q.SPEC `(\n. {x | Normal (c - ((1/2) pow n)) <= x /\ x < Normal (c + ((1/2) pow n))})`)
 >> `(\n. {x | Normal (c - ((1/2) pow n)) <= x /\
               x < Normal (c + ((1/2) pow n))}) IN (UNIV -> subsets Borel)`
     by RW_TAC std_ss [IN_FUNSET, BOREL_MEASURABLE_SETS_CO]
 >> METIS_TAC []);

val BOREL_MEASURABLE_SETS_SING = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_SING", ``!c. {c} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_NEGINF']
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF']
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_SING_r]);

val BOREL_MEASURABLE_SETS_SING' = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_SING'", ``!c. {x | x = c} IN subsets Borel``,
    GEN_TAC
 >> `{x | x = c} = {c}` by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING]
 >> POP_ORW >> Cases_on `c`
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_NEGINF']
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF']
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_SING_r]);

val BOREL_MEASURABLE_SETS_NOT_SING = store_thm
  ("BOREL_MEASURABLE_SETS_NOT_SING", ``!c. {x | x <> c} IN subsets Borel``,
    RW_TAC std_ss []
 >> `{x | x <> c} = (space Borel) DIFF ({c})`
      by RW_TAC std_ss [SPACE_BOREL, EXTENSION, IN_DIFF, IN_SING, GSPECIFICATION, IN_UNIV]
 >> POP_ORW
 >> METIS_TAC [SIGMA_ALGEBRA_BOREL, BOREL_MEASURABLE_SETS_SING,
               sigma_algebra_def, algebra_def]);

(* For backwards compatibilities *)
val BOREL_MEASURABLE_SETS1 = save_thm
  ("BOREL_MEASURABLE_SETS1", BOREL_MEASURABLE_SETS_RO);
val BOREL_MEASURABLE_SETS2 = save_thm
  ("BOREL_MEASURABLE_SETS2", BOREL_MEASURABLE_SETS_CR);
val BOREL_MEASURABLE_SETS3 = save_thm
  ("BOREL_MEASURABLE_SETS3", BOREL_MEASURABLE_SETS_RC);
val BOREL_MEASURABLE_SETS4 = save_thm
  ("BOREL_MEASURABLE_SETS4", BOREL_MEASURABLE_SETS_OR);
val BOREL_MEASURABLE_SETS5 = save_thm
  ("BOREL_MEASURABLE_SETS5", BOREL_MEASURABLE_SETS_CO);
val BOREL_MEASURABLE_SETS6 = save_thm
  ("BOREL_MEASURABLE_SETS6", BOREL_MEASURABLE_SETS_OC);
val BOREL_MEASURABLE_SETS7 = save_thm
  ("BOREL_MEASURABLE_SETS7", BOREL_MEASURABLE_SETS_CC);
val BOREL_MEASURABLE_SETS8 = save_thm
  ("BOREL_MEASURABLE_SETS8", BOREL_MEASURABLE_SETS_OO);
val BOREL_MEASURABLE_SETS9 = save_thm
  ("BOREL_MEASURABLE_SETS9", BOREL_MEASURABLE_SETS_SING);
val BOREL_MEASURABLE_SETS10 = save_thm
  ("BOREL_MEASURABLE_SETS10", BOREL_MEASURABLE_SETS_NOT_SING);

(* A summary of all Borel-measurable sets *)
val BOREL_MEASURABLE_SETS = store_thm
  ("BOREL_MEASURABLE_SETS",
  ``(!c. {x | x < c} IN subsets Borel) /\
    (!c. {x | c < x} IN subsets Borel) /\
    (!c. {x | x <= c} IN subsets Borel) /\
    (!c. {x | c <= x} IN subsets Borel) /\
    (!c d. {x | c <= x /\ x < d} IN subsets Borel) /\
    (!c d. {x | c < x /\ x <= d} IN subsets Borel) /\
    (!c d. {x | c <= x /\ x <= d} IN subsets Borel) /\
    (!c d. {x | c < x /\ x < d} IN subsets Borel) /\
    (!c. {c} IN subsets Borel) /\
    (!c. {x | x <> c} IN subsets Borel)``,
 (* proof *)
    RW_TAC std_ss [BOREL_MEASURABLE_SETS_RO, (*         x < c *)
                   BOREL_MEASURABLE_SETS_OR, (* c < x         *)
                   BOREL_MEASURABLE_SETS_RC, (*         x <= c *)
                   BOREL_MEASURABLE_SETS_CR, (* c <= x         *)
                   BOREL_MEASURABLE_SETS_CO, (* c <= x /\ x < d *)
                   BOREL_MEASURABLE_SETS_OC, (* c < x /\ x <= d *)
                   BOREL_MEASURABLE_SETS_CC, (* c <= x /\ x <= d *)
                   BOREL_MEASURABLE_SETS_OO, (* c < x /\ x < d *)
                   BOREL_MEASURABLE_SETS_SING,       (* x = c *)
                   BOREL_MEASURABLE_SETS_NOT_SING]); (* x <> c *)


(* ******************************************* *)
(*        Borel measurable functions           *)
(* ******************************************* *)

val IN_MEASURABLE_BOREL_CONST = store_thm
  ("IN_MEASURABLE_BOREL_CONST",
  ``!a k f. sigma_algebra a /\ (!x. x IN space a ==> (f x = k)) ==> f IN measurable a Borel``,
 (* proof *)
    RW_TAC std_ss [IN_MEASURABLE_BOREL,IN_FUNSET, IN_UNIV]
 >> Cases_on `Normal c <= k`
 >- (`{x | f x < Normal c} INTER space a = {}`
         by  (RW_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER]
              >> METIS_TAC [extreal_lt_def])
      >> METIS_TAC [sigma_algebra_def,algebra_def])
 >> `{x | f x < Normal c} INTER space a = space a`
      by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
          >> METIS_TAC [extreal_lt_def])
 >> METIS_TAC [sigma_algebra_def,algebra_def,INTER_IDEMPOT,DIFF_EMPTY]);

val IN_MEASURABLE_BOREL_INDICATOR = store_thm
  ("IN_MEASURABLE_BOREL_INDICATOR",
  ``!a A f. sigma_algebra a /\ A IN subsets a /\
           (!x. x IN space a ==> (f x = (indicator_fn A x)))
        ==> f IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL]
 >- RW_TAC std_ss [IN_FUNSET,UNIV_DEF,indicator_fn_def,IN_DEF]
 >> `!x. x IN space a ==> 0 <= f x /\ f x <= 1` by RW_TAC real_ss [indicator_fn_def,le_01,le_refl]
 >> Cases_on `Normal c <= 0`
 >- (`{x | f x < Normal c} INTER space a = {}`
      by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER,extreal_lt_def]
          >> METIS_TAC [le_trans])
      >> METIS_TAC [sigma_algebra_def,algebra_def,DIFF_EMPTY])
 >> Cases_on `1 < Normal c`
 >- (`{x | f x < Normal c} INTER space a = space a`
        by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER]
            >> METIS_TAC [let_trans])
     >> METIS_TAC [sigma_algebra_def,algebra_def,DIFF_EMPTY])
 >> `{x | f x < Normal c} INTER space a = (space a) DIFF A`
        by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,IN_DIFF]
            >> FULL_SIMP_TAC std_ss [extreal_lt_def,indicator_fn_def]
            >> METIS_TAC [extreal_lt_def])
 >> METIS_TAC [sigma_algebra_def,algebra_def,DIFF_EMPTY]);

val IN_MEASURABLE_BOREL_CMUL = store_thm
  ("IN_MEASURABLE_BOREL_CMUL",
  ``!a f g z. sigma_algebra a /\ f IN measurable a Borel /\
             (!x. x IN space a ==> (g x = Normal (z) * f x))
          ==> g IN measurable a Borel``,
    RW_TAC std_ss []
 >> Cases_on `Normal z = 0`
 >- METIS_TAC [IN_MEASURABLE_BOREL_CONST, mul_lzero]
 >> Cases_on `0 < Normal z`
 >- (RW_TAC real_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV] \\
    `!c. {x | g x < Normal c} INTER space a = {x | f x < Normal (c) / Normal z} INTER space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
          METIS_TAC [lt_rdiv, mul_comm, extreal_of_num_def, extreal_lt_eq]) \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL, extreal_div_eq, extreal_of_num_def, extreal_11])
 >> `z < 0` by METIS_TAC [extreal_lt_def, extreal_le_def, extreal_of_num_def,
                          REAL_LT_LE, GSYM real_lte]
 >> RW_TAC real_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> `!c. {x | g x < Normal c} INTER space a = {x | Normal c / Normal z < f x} INTER space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
          METIS_TAC [lt_rdiv_neg, mul_comm])
 >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, extreal_div_eq, REAL_LT_IMP_NE]);

val IN_MEASURABLE_BOREL_ABS = store_thm
  ("IN_MEASURABLE_BOREL_ABS",
  ``!a f g. (sigma_algebra a) /\ f IN measurable a Borel /\
            (!x. x IN space a ==> (g x = abs (f x)))
         ==> g IN measurable a Borel``,
    RW_TAC real_ss [IN_MEASURABLE_BOREL,IN_UNIV,IN_FUNSET]
 >> Cases_on `c <= 0`
 >- (`{x | g x < Normal c} INTER space a = {}`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, NOT_IN_EMPTY, GSYM real_lte] \\
            METIS_TAC [abs_pos, le_trans, extreal_le_def, extreal_of_num_def, extreal_lt_def]) \\
     METIS_TAC [sigma_algebra_def, algebra_def])
 >> FULL_SIMP_TAC real_ss [GSYM real_lt]
 >> Suff `{x | g x < Normal c} INTER space a =
          ({x | f x < Normal c} INTER space a) INTER ({x | Normal (-c) < f x} INTER space a)`
 >- (Rewr' \\
     METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, IN_MEASURABLE_BOREL_ALL,
               IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV])
 >> RW_TAC real_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> EQ_TAC
 >- (RW_TAC std_ss []
     >- (`abs (f x) < Normal c` by METIS_TAC [] \\
         Cases_on `f x` >| (* 3 subgoals *)
         [ METIS_TAC [lt_infty],
           METIS_TAC [extreal_abs_def, lt_infty, extreal_not_infty],
          `g x = Normal (abs r)` by METIS_TAC [extreal_abs_def] \\
           FULL_SIMP_TAC std_ss [extreal_lt_eq] \\
           METIS_TAC [REAL_ADD_LID, REAL_SUB_RZERO, ABS_BETWEEN] ]) \\
     Cases_on `f x` >| (* 3 subgoals *)
     [ METIS_TAC [extreal_abs_def, lt_infty],
       METIS_TAC [lt_infty],
      `g x = Normal (abs r)` by METIS_TAC [extreal_abs_def] \\
       FULL_SIMP_TAC std_ss [extreal_lt_eq] \\
       METIS_TAC [REAL_ADD_LID, REAL_SUB_LZERO, REAL_SUB_RZERO, ABS_BETWEEN] ])
 >> RW_TAC std_ss []
 >> `f x <> NegInf` by METIS_TAC [lt_infty]
 >> `f x <> PosInf` by METIS_TAC [lt_infty]
 >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss [extreal_abs_def, extreal_lt_eq, extreal_le_def]
 >> `r = r - 0` by PROVE_TAC [REAL_SUB_RZERO] >> POP_ORW
 >> REWRITE_TAC [GSYM ABS_BETWEEN]
 >> ASM_REWRITE_TAC [REAL_ADD_LID, REAL_SUB_LZERO, REAL_SUB_RZERO]
 >> METIS_TAC [REAL_LET_ANTISYM, REAL_NOT_LE]);

val IN_MEASURABLE_BOREL_SQR = store_thm
  ("IN_MEASURABLE_BOREL_SQR",``!a f g. sigma_algebra a /\ f IN measurable a Borel /\
                                (!x. x IN space a ==> (g x = (f x) pow 2))
                                ==> g IN measurable a Borel``,
  RW_TAC real_ss []
  >> `!c. {x | f x <= Normal c} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
  >> `!c. {x | Normal c <= f x} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
  >> RW_TAC real_ss [IN_UNIV,IN_FUNSET,IN_MEASURABLE_BOREL_ALT2]
  >> Cases_on `Normal c < 0`
  >- (`{x | g x <= Normal c} INTER space a = {}`
          by ( RW_TAC real_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER,GSYM real_lt]
             >> METIS_TAC [le_pow2,lte_trans,extreal_lt_def])
      >> METIS_TAC [sigma_algebra_def,algebra_def])
  >> FULL_SIMP_TAC real_ss [extreal_lt_def]
  >> `{x | g x <= Normal c} INTER space a =
        ({x | f x <= sqrt (Normal c)} INTER space a) INTER
        ({x | - (sqrt (Normal c)) <= f x} INTER space a)`
        by (RW_TAC real_ss [EXTENSION,GSPECIFICATION,IN_INTER]
            >> EQ_TAC
            >- (RW_TAC real_ss []
                >- (Cases_on `f x < 0` >- METIS_TAC [lte_trans,lt_imp_le,sqrt_pos_le]
                         >> METIS_TAC [pow2_sqrt,sqrt_mono_le,le_pow2,extreal_lt_def])
                     >> Cases_on `0 <= f x` >- METIS_TAC [le_trans,le_neg,sqrt_pos_le,neg_0]
                >> SPOSE_NOT_THEN ASSUME_TAC
                >> FULL_SIMP_TAC real_ss [GSYM extreal_lt_def]
                >> `sqrt (Normal c) < - (f x)` by METIS_TAC [lt_neg,neg_neg]
                >> `(sqrt (Normal c)) pow 2 < (- (f x)) pow 2` by RW_TAC real_ss [pow_lt2,sqrt_pos_le]
                >> `(sqrt (Normal c)) pow 2 = Normal c` by METIS_TAC [sqrt_pow2]
                >> `(-1) pow 2 = 1` by METIS_TAC [pow_minus1,MULT_RIGHT_1]
                >> `(- (f x)) pow 2 = (f x) pow 2` by RW_TAC std_ss [Once neg_minus1,pow_mul,mul_lone]
                >> METIS_TAC [extreal_lt_def])
            >> RW_TAC std_ss []
            >> Cases_on `0 <= f x` >- METIS_TAC [pow_le,sqrt_pow2]
            >> FULL_SIMP_TAC real_ss [GSYM extreal_lt_def]
            >> `- (f x) <= sqrt (Normal c)` by METIS_TAC [le_neg,neg_neg]
            >> `(- (f x)) pow 2 <= (sqrt (Normal c)) pow 2`
               by METIS_TAC [pow_le, sqrt_pos_le, lt_neg, neg_neg, neg_0, lt_imp_le]
            >> `(sqrt (Normal c)) pow 2 = Normal c` by METIS_TAC [sqrt_pow2]
            >> `(-1) pow 2 = 1` by METIS_TAC [pow_minus1,MULT_RIGHT_1]
            >> `(- (f x)) pow 2 = (f x) pow 2` by RW_TAC std_ss [Once neg_minus1,pow_mul,mul_lone]
            >> METIS_TAC [])
  >> METIS_TAC [sigma_algebra_def,ALGEBRA_INTER,extreal_sqrt_def,extreal_ainv_def]);

val IN_MEASURABLE_BOREL_ADD = store_thm
  ("IN_MEASURABLE_BOREL_ADD",
  ``!a f g h. sigma_algebra a /\ f IN measurable a Borel /\
              g IN measurable a Borel /\
              (!x. x IN space a ==> f x <> NegInf /\ g x <> NegInf) /\
              (!x. x IN space a ==> (h x = f x + g x))
          ==> h IN measurable a Borel``,
    rpt STRIP_TAC
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL] >- RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `!c. {x | h x < Normal c} INTER (space a) =
         BIGUNION (IMAGE (\r. {x | f x < r /\ r < Normal c - g x} INTER space a) Q_set)`
     by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV,IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss []
                >> METIS_TAC [lt_sub_imp,Q_DENSE_IN_R])
            >> RW_TAC std_ss []
            >- METIS_TAC [lt_sub,lt_trans,extreal_not_infty]
            >> METIS_TAC [])
 >> FULL_SIMP_TAC std_ss []
 >> MATCH_MP_TAC BIGUNION_IMAGE_Q
 >> RW_TAC std_ss [IN_FUNSET]
 >> `?y. r = Normal y` by METIS_TAC [Q_not_infty, extreal_cases]
 >> `{x | f x < Normal y /\ Normal y < Normal c - g x} =
     {x | f x < Normal y} INTER {x | Normal y < Normal c - g x}`
     by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> `({x | f x < Normal y} INTER space a) IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
 >> `!x. x IN space a ==> ((Normal y < Normal c - g x) = (g x < Normal c - Normal y))`
     by METIS_TAC [lt_sub, extreal_not_infty, add_comm]
 >> `{x | Normal y < Normal c - g x} INTER space a = {x | g x < Normal c - Normal y} INTER space a`
     by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION] >> METIS_TAC [])
 >> `({x | Normal y < Normal c - g x} INTER space a) IN subsets a`
     by METIS_TAC [IN_MEASURABLE_BOREL_ALL, extreal_sub_def]
  >> `({x | f x < Normal y} INTER space a) INTER ({x | Normal y < Normal c - g x} INTER space a) =
      ({x | f x < Normal y} INTER {x | Normal y < Normal c - g x} INTER space a)`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
            >> EQ_TAC >- RW_TAC std_ss []
            >> RW_TAC std_ss [])
  >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val IN_MEASURABLE_BOREL_SUB = store_thm
  ("IN_MEASURABLE_BOREL_SUB",
  ``!a f g h. sigma_algebra a /\
              f IN measurable a Borel /\
              g IN measurable a Borel /\
             (!x. x IN space a ==> f x <> NegInf /\ g x <> PosInf) /\
             (!x. x IN space a ==> (h x = f x - g x))
          ==> h IN measurable a Borel``,
    RW_TAC std_ss []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
 >> Q.EXISTS_TAC `f`
 >> Q.EXISTS_TAC `(\x. - g x)`
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
      Q.EXISTS_TAC `g` \\
      Q.EXISTS_TAC `-1` \\
      RW_TAC std_ss [GSYM extreal_ainv_def, GSYM extreal_of_num_def, GSYM neg_minus1],
      (* goal 2 (of 3) *)
      METIS_TAC [extreal_ainv_def, neg_neg],
      (* goal 3 (of 3) *)
      Cases_on `f x` >> Cases_on `g x` \\
      METIS_TAC [le_infty, extreal_ainv_def, extreal_sub_def, extreal_add_def, real_sub] ]);

val IN_MEASURABLE_BOREL_MUL = store_thm
  ("IN_MEASURABLE_BOREL_MUL",
  ``!a f g h. sigma_algebra a /\ f IN measurable a Borel  /\
             (!x. x IN space a ==> f x <> NegInf /\ f x <> PosInf /\
                                   g x <> NegInf /\ g x <> PosInf) /\
              g IN measurable a Borel /\ (!x. x IN space a ==> (h x = f x * g x))
          ==> h IN measurable a Borel``,
    RW_TAC std_ss []
 >> `!x. x IN space a ==> (f x * g x = 1 / 2 * ((f x + g x) pow 2 - f x pow 2 - g x pow 2))`
 by (RW_TAC std_ss [] \\
     (MP_TAC o Q.SPECL [`f x`, `g x`]) add_pow2 \\
     RW_TAC std_ss [] \\
    `?r. f x = Normal r` by METIS_TAC [extreal_cases] \\
    `?r. g x = Normal r` by METIS_TAC [extreal_cases] \\
     FULL_SIMP_TAC real_ss [extreal_11, extreal_pow_def, extreal_add_def, extreal_sub_def,
                            extreal_of_num_def, extreal_mul_def, extreal_div_eq] \\
    `r pow 2 + r' pow 2 + 2 * r * r' - r pow 2 - r' pow 2 = 2 * r * r'` by REAL_ARITH_TAC \\
     RW_TAC real_ss [REAL_MUL_ASSOC])
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
 >> Q.EXISTS_TAC `(\x. (f x + g x) pow 2 - f x pow 2 - g x pow 2)`
 >> Q.EXISTS_TAC `1 / 2`
 >> RW_TAC real_ss [extreal_of_num_def,extreal_div_eq]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
 >> Q.EXISTS_TAC `(\x. (f x + g x) pow 2 - f x pow 2)`
 >> Q.EXISTS_TAC `(\x. g x pow 2)`
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 4) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
      Q.EXISTS_TAC `(\x. (f x + g x) pow 2)` \\
      Q.EXISTS_TAC `(\x. f x pow 2)` \\
      RW_TAC std_ss [] >|
      [ MATCH_MP_TAC IN_MEASURABLE_BOREL_SQR
        >> Q.EXISTS_TAC `(\x. (f x + g x))`
        >> RW_TAC std_ss []
        >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
        >> Q.EXISTS_TAC `f`
        >> Q.EXISTS_TAC `g`
        >> RW_TAC std_ss [],
        MATCH_MP_TAC IN_MEASURABLE_BOREL_SQR
        >> METIS_TAC [],
        METIS_TAC [add_not_infty,pow_not_infty],
        METIS_TAC [pow_not_infty] ],
      (* goal 2 (of 4) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_SQR >> METIS_TAC [],
      (* goal 3 (of 4) *)
      METIS_TAC [add_not_infty, pow_not_infty, sub_not_infty],
      (* goal 4 (of 4) *)
      METIS_TAC [pow_not_infty] ]);

val IN_MEASURABLE_BOREL_SUM = store_thm
  ("IN_MEASURABLE_BOREL_SUM", ``!a f g s. FINITE s /\ sigma_algebra a /\
                                (!i. i IN s ==> (f i) IN measurable a Borel) /\
                                (!i x. i IN s /\ x IN space a ==> f i x <> NegInf) /\
                                (!x. x IN space a ==> (g x = SIGMA (\i. (f i) x) s))
                                 ==> g IN measurable a Borel``,
  Suff `!s:'b -> bool. FINITE s ==> (\s:'b -> bool. !a f g. FINITE s /\ sigma_algebra a /\
                (!i. i IN s ==> f i IN measurable a Borel) /\
                (!i x. i IN s /\ x IN space a ==> f i x <> NegInf) /\
                (!x. x IN space a ==> (g x = SIGMA (\i. f i x) s)) ==>
                   g IN measurable a Borel) s`
  >- METIS_TAC []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,NOT_IN_EMPTY]
  >- METIS_TAC [IN_MEASURABLE_BOREL_CONST]
  >> `!x. x IN space a ==> (SIGMA (\i. f i x) (e INSERT s) = f e x + SIGMA (\i. f i x) (s DELETE e))`
        by (RW_TAC std_ss []
            >> (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i x)`,`s`] o
                INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
            >> RW_TAC std_ss [])

  >> FULL_SIMP_TAC std_ss []
  >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
  >> Q.EXISTS_TAC `f e`
  >> Q.EXISTS_TAC `(\x. SIGMA (\i. f i x) s)`
  >> FULL_SIMP_TAC std_ss [IN_INSERT,DELETE_NON_ELEMENT,EXTREAL_SUM_IMAGE_NOT_INFTY]
  >> Q.PAT_X_ASSUM `!a f g. P ==> g IN measurable a Borel` MATCH_MP_TAC
  >> Q.EXISTS_TAC `f`
  >> RW_TAC std_ss []);

val IN_MEASURABLE_BOREL_CMUL_INDICATOR = store_thm
  ("IN_MEASURABLE_BOREL_CMUL_INDICATOR",``!a z s. sigma_algebra a /\ s IN subsets a
      ==> (\x. Normal z * indicator_fn s x) IN measurable a Borel``,
  RW_TAC std_ss []
  >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
  >> Q.EXISTS_TAC `indicator_fn s`
  >> Q.EXISTS_TAC `z`
  >> RW_TAC std_ss []
  >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
  >> METIS_TAC []);

val IN_MEASURABLE_BOREL_MUL_INDICATOR = store_thm
  ("IN_MEASURABLE_BOREL_MUL_INDICATOR",
  ``!a f s. sigma_algebra a /\ f IN measurable a Borel /\ s IN subsets a ==>
            (\x. f x * indicator_fn s x) IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2,IN_FUNSET,IN_UNIV]
 >> Cases_on `0 <= Normal c`
 >- (`{x | f x * indicator_fn s x <= Normal c} INTER space a =
      (({x | f x <= Normal c} INTER space a) INTER s) UNION (space a DIFF s)`
         by (RW_TAC std_ss [indicator_fn_def, EXTENSION, GSPECIFICATION, IN_INTER,
                            IN_UNION, IN_DIFF]
             >> Cases_on `x IN s` >- RW_TAC std_ss [mul_rone, mul_rzero]
             >> RW_TAC std_ss [mul_rone,mul_rzero])
     >> POP_ORW
     >> MATCH_MP_TAC ALGEBRA_UNION
     >> CONJ_TAC >- FULL_SIMP_TAC std_ss [sigma_algebra_def]
     >> Reverse CONJ_TAC >- FULL_SIMP_TAC std_ss [sigma_algebra_def,algebra_def]
     >> MATCH_MP_TAC ALGEBRA_INTER
     >> FULL_SIMP_TAC std_ss [sigma_algebra_def])
 >> `{x | f x * indicator_fn s x <= Normal c} INTER space a =
     (({x | f x <= Normal c} INTER space a) INTER s)`
         by (RW_TAC std_ss [indicator_fn_def,EXTENSION,GSPECIFICATION,IN_INTER]
             >> Cases_on `x IN s` >- RW_TAC std_ss [mul_rone,mul_rzero]
             >> RW_TAC std_ss [mul_rone,mul_rzero])
 >> POP_ORW
 >> MATCH_MP_TAC ALGEBRA_INTER
 >> FULL_SIMP_TAC std_ss [sigma_algebra_def]);

val IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ = store_thm
  ("IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ",
  ``!a f. sigma_algebra a ==>
         (f IN measurable a Borel = (\x. f x * indicator_fn (space a) x) IN measurable a Borel)``,
    RW_TAC std_ss []
 >> EQ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, ALGEBRA_SPACE, sigma_algebra_def]
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_UNIV, IN_FUNSET]
 >> `{x | f x < Normal c} INTER space a =
     {x | f x * indicator_fn (space a) x < Normal c} INTER space a`
       by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION, indicator_fn_def,
                          mul_rzero, mul_rone]
           >> METIS_TAC [mul_rzero, mul_rone])
 >> POP_ORW >> art []);

val IN_MEASURABLE_BOREL_POW = store_thm
  ("IN_MEASURABLE_BOREL_POW",
  ``!n a f. sigma_algebra a /\ f IN measurable a Borel /\
            (!x. x IN space a ==> f x <> NegInf /\ f x <> PosInf)
        ==> (\x. (f x) pow n) IN measurable a Borel``,
  Induct >- (RW_TAC std_ss [pow_0]
             >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST
             >> METIS_TAC [])
  >> RW_TAC std_ss []
  >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL
  >> Q.EXISTS_TAC `f`
  >> Q.EXISTS_TAC `(\x. f x pow n)`
  >> RW_TAC std_ss [pow_not_infty]
  >> METIS_TAC [pow_add,ADD1,pow_1,mul_comm]);

val IN_MEASURABLE_BOREL_MAX = store_thm
  ("IN_MEASURABLE_BOREL_MAX",
  ``!a f g. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel
        ==> (\x. max (f x) (g x)) IN measurable a Borel``,
  RW_TAC std_ss [IN_MEASURABLE_BOREL,extreal_max_def,IN_FUNSET, IN_UNIV]
  >> `!c. {x | (if f x <= g x then g x else f x) < c} = {x | f x < c} INTER {x | g x < c}`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss []
                >- METIS_TAC [let_trans]
                >> METIS_TAC [extreal_lt_def, lt_trans])
             >> METIS_TAC [extreal_lt_def, lt_trans])
  >> `!c. {x | (if f x <= g x then g x else f x) < c} INTER space a =
          ({x | f x < c} INTER space a) INTER ({x | g x < c} INTER space a)`
          by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
  >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val IN_MEASURABLE_BOREL_MONO_SUP = store_thm
  ("IN_MEASURABLE_BOREL_MONO_SUP",
  ``!fn f a. sigma_algebra a /\ (!n:num. fn n IN measurable a Borel) /\
            (!n x. fn n x <= fn (SUC n) x) /\
            (!x. x IN space a ==> (f x = sup (IMAGE (\n. fn n x) UNIV)))
         ==> f IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2, IN_FUNSET, IN_UNIV]
 >> `{x | sup (IMAGE (\n. fn n x) UNIV) <= Normal c} INTER space a =
     BIGINTER (IMAGE (\n. {x | fn n x <= Normal c} INTER space a) UNIV)`
 by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGINTER_IMAGE, IN_UNIV, IN_INTER, sup_le]
     >> EQ_TAC
     >- (RW_TAC std_ss []
         >> Q.PAT_X_ASSUM `!y. P y ==> y <= Normal c` MATCH_MP_TAC
         >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
         >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
         >> METIS_TAC [])
     >> RW_TAC std_ss []
     >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
     >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
     >> METIS_TAC [])
 >> `{x | f x <= Normal c} INTER space a =
     {x | sup (IMAGE (\n. fn n x) UNIV) <= Normal c} INTER space a`
      by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] >> METIS_TAC [])
 >> `!c. BIGINTER (IMAGE (\n. {x | fn n x <= Normal c} INTER (space a)) UNIV) IN subsets a`
      by (RW_TAC std_ss []
          >> (MP_TAC o Q.SPEC `(space a,subsets a)`) SIGMA_ALGEBRA_FN_BIGINTER
          >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, space_def, subsets_def, SPACE])
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_FN_PLUS = store_thm
  ("IN_MEASURABLE_BOREL_FN_PLUS",
  ``!a f. f IN measurable a Borel ==> fn_plus f IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV, fn_plus_def]
 >> Cases_on `c <= 0`
 >- (`{x | (if 0 < f x then f x else 0) < Normal c} = {}`
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]
           >> `!x. 0 <= (if 0 < f x then f x else 0)` by RW_TAC real_ss [lt_imp_le, le_refl]
           >> METIS_TAC [le_trans, extreal_lt_def, extreal_of_num_def, extreal_le_def])
     >> METIS_TAC [sigma_algebra_def, algebra_def, INTER_EMPTY])
 >> `{x | (if 0 < f x then f x else 0) < Normal c} = {x | f x < Normal c}`
       by (RW_TAC real_ss [EXTENSION, GSPECIFICATION]
           >> EQ_TAC
           >- (RW_TAC real_ss []
               >> METIS_TAC [extreal_lt_def, let_trans])
           >> RW_TAC real_ss []
           >> METIS_TAC [extreal_lt_eq, extreal_of_num_def, real_lte])
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_FN_MINUS = store_thm
  ("IN_MEASURABLE_BOREL_FN_MINUS",
  ``!a f. f IN measurable a Borel ==> fn_minus f IN measurable a Borel``,
    RW_TAC std_ss [fn_minus_def]
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL,IN_FUNSET,IN_UNIV,fn_minus_def]
 >- METIS_TAC [IN_MEASURABLE_BOREL]
 >> Cases_on `c <= 0`
 >- (`{x | (if f x < 0 then -f x else 0) < Normal c} = {}`
        by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY]
            >> `!x. 0 <= (if f x < 0 then -f x else 0)`
                 by (RW_TAC real_ss [le_refl]
                     >> METIS_TAC [lt_neg, neg_0, lt_imp_le])
            >> METIS_TAC [extreal_of_num_def, extreal_le_def, le_trans, extreal_lt_def])
            >> METIS_TAC [sigma_algebra_def, algebra_def, INTER_EMPTY, IN_MEASURABLE_BOREL])
 >> `{x | (if f x < 0 then -f x else 0) < Normal c} = {x | Normal (-c) < f x}`
        by (RW_TAC real_ss [EXTENSION,GSPECIFICATION]
               >> EQ_TAC
            >- (RW_TAC std_ss []
                >- METIS_TAC [lt_neg, neg_neg, extreal_ainv_def]
                >> METIS_TAC [lt_neg, neg_neg, neg_0, extreal_lt_def, lte_trans, lt_imp_le,
                              extreal_ainv_def])
            >> RW_TAC std_ss []
            >- METIS_TAC [lt_neg, neg_neg, extreal_ainv_def]
            >> METIS_TAC [real_lte, extreal_lt_eq, extreal_of_num_def, extreal_ainv_def])
 >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]);

(* NOTE: added `!x. f x <> NegInf` due to the changes in IN_MEASURABLE_BOREL_SUB.
   Since `f = fn_plus f - fn_minus f`, to prevent `PosInf - PosInf`, fn_minus must not
   take PosInf at any point, thus f must not take NegInf at any point. *)
val IN_MEASURABLE_BOREL_PLUS_MINUS = store_thm
  ("IN_MEASURABLE_BOREL_PLUS_MINUS",
  ``!a f. (!x. f x <> NegInf) ==>
          (f IN measurable a Borel =
           fn_plus f IN measurable a Borel /\ fn_minus f IN measurable a Borel)``,
    RW_TAC std_ss []
 >> EQ_TAC >- RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, IN_MEASURABLE_BOREL_FN_MINUS]
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
 >> Q.EXISTS_TAC `fn_plus f`
 >> Q.EXISTS_TAC `fn_minus f`
 >> RW_TAC std_ss [fn_plus_def, fn_minus_def, sub_rzero,lt_antisym, sub_rzero, add_lzero]
 >- METIS_TAC [IN_MEASURABLE_BOREL]
 >- METIS_TAC [lt_antisym]
 >- METIS_TAC [extreal_not_infty, extreal_of_num_def]
 >- METIS_TAC [extreal_not_infty, extreal_of_num_def]
 >- METIS_TAC [neg_neg, extreal_ainv_def]
 >- METIS_TAC [extreal_not_infty, extreal_of_num_def]
 >- METIS_TAC [extreal_not_infty, extreal_of_num_def]
 >- METIS_TAC [lt_antisym]
 >- METIS_TAC [sub_rneg, add_lzero, extreal_of_num_def]
 >- METIS_TAC [le_antisym, extreal_lt_def]);


(* ------------------------------------------------------------------------- *)
(*  Construction of Lebesgue measure space by CARATHEODORY_SEMIRING          *)
(* ------------------------------------------------------------------------- *)

(* The line-segment (half open, half closed) from a to b, named after [6, p.389] *)
val line_segment_def = Define (* (a, b] *)
   `line_segment a b = {x | Normal a < x /\ x <= Normal b}`;

(* for {} is in Borel_generator *)
val line_segment_empty = store_thm
  ("line_segment_empty", ``!a b. (a = b) ==> (line_segment a b = {})``,
    RW_TAC std_ss [line_segment_def, Once EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]
 >> REWRITE_TAC [GSYM extreal_lt_def]
 >> METIS_TAC [lt_antisym]);

(* `lambda0` is the "length" of the line-segment from a to b *)
local
  val thm = prove (
    ``?l. !a b. a <= b ==> (l (line_segment a b) = Normal b - Normal a)``,
      Q.EXISTS_TAC `\s. if s = {} then 0 else sup s - inf s`
   >> RW_TAC std_ss []
   >- (Cases_on `a = b` >- METIS_TAC [sub_refl, extreal_not_infty] \\
       fs [REAL_LE_LT, line_segment_def] \\
       Q.PAT_X_ASSUM `P = {}` MP_TAC \\
       RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] \\
       STRIP_ASSUME_TAC (MATCH_MP (Q.SPECL [`a`, `b`] REAL_MEAN)
                                  (ASSUME ``a < b:real``)) \\
       METIS_TAC [extreal_lt_eq, lt_imp_le])
   >> Cases_on `a = b` >- PROVE_TAC [line_segment_empty]
   >> fs [REAL_LE_LT]
   >> Know `sup (line_segment a b) = Normal b`
   >- (RW_TAC std_ss [line_segment_def, sup_eq', GSPECIFICATION] \\
       POP_ASSUM MATCH_MP_TAC >> art [extreal_lt_eq, le_refl])
   >> Rewr'
   >> Know `inf (line_segment a b) = Normal a`
   >- (RW_TAC std_ss [line_segment_def, inf_eq', GSPECIFICATION]
       >- IMP_RES_TAC lt_imp_le \\
       MATCH_MP_TAC le_epsilon \\
       RW_TAC std_ss [] \\
       Cases_on `Normal a + e <= Normal b`
       >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
           ASSUME_TAC (REWRITE_RULE [extreal_not_infty, add_rzero]
                                    (Q.SPECL [`Normal a`, `0`, `e`] lt_ladd)) >> art []) \\
       fs [GSYM extreal_lt_def] \\
       MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `Normal b` \\
       Reverse CONJ_TAC >- IMP_RES_TAC lt_imp_le \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [extreal_lt_eq, le_refl])
   >> Rewr);
in
  (* |- !a b. a <= b ==> (lambda0 (line_segment a b) = Normal b - Normal a) *)
  val lambda0_def = new_specification      (* learnt from "examples/miller" *)
    ("lambda0_def", ["lambda0"], thm);
end;

val Borel_generator_def = Define (* {(a, b] | a < b} *)
   `Borel_generator = (univ(:extreal), {l | ?a b. a <= b /\ (l = line_segment a b)})`;

(* Borel_generator is a semiring *)
val SEMIRING_BOREL_GENERATOR = store_thm
  ("SEMIRING_BOREL_GENERATOR", ``semiring Borel_generator``,
    cheat);

(* The smallest sigma algebra generated from line segments is properly the Borel set *)
val SIGMA_BOREL_GENERATOR = store_thm
  ("SIGMA_BOREL_GENERATOR",
  ``sigma (space Borel_generator) (subsets Borel_generator) = Borel``,
    cheat);

(* lambda0 is a premeasure, whose countable-additivity comes from COMPACT_IMP_HEINE_BOREL *)
val PREMEASURE_LAMBDA0 = store_thm
  ("PREMEASURE_LAMBDA0",
  ``premeasure (space Borel_generator,subsets Borel_generator,lambda0)``,
    cheat);

local
  val thm = prove (
    ``?m. (!s. s IN measurable_sets m ==> (measure m s = lambda0 s)) /\
          ((m_space m, measurable_sets m) = Borel) /\ measure_space m``,
      cheat
  (*  MP_TAC (Q.ISPEC `(space generator,subsets generator,lambda0)` CARATHEODORY_SEMIRING) \\
      ASSUME_TAC SPACE_SUBSETS_GENERATOR \\
      RW_TAC std_ss [GENERATOR_ALGEBRA, PROB_MEASURE_POSITIVE,
                     PROB_MEASURE_COUNTABLY_ADDITIVE, measurable_sets_def,
                     measure_def, m_space_def] \\
      Q.EXISTS_TAC `m` \\
      RW_TAC std_ss [prob_space_def, prob_def, events_def, p_space_def] \\
      ONCE_REWRITE_TAC [GSYM PROB_MEASURE_BASIC] \\
      Know `m_space m = UNIV`
      >- (Q.PAT_X_ASSUM `(m_space m, measurable_sets m) = P` MP_TAC \\
          RW_TAC std_ss [sigma_def, prob_algebra_def, space_def, PAIR_EQ]) \\
      Rewr \\
      Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC \\
      REWRITE_TAC [PROB_ALGEBRA_UNIV]
   *));
in
  (* named after Henri Lebesgue (1875–1941), a French mathematician [5] *)
  val Lebesgue_def = new_specification (* method learnt from "examples/miller" *)
    ("Lebesgue_def", ["Lebesgue"], thm);
end;

val MEASURE_SPACE_LEBESGUE = store_thm
  ("MEASURE_SPACE_LEBESGUE", ``measure_space Lebesgue``,
    PROVE_TAC [Lebesgue_def]);

val SPACE_LEBESGUE = store_thm
  ("SPACE_LEBESGUE", ``m_space Lebesgue = univ(:extreal)``,
    PROVE_TAC [Lebesgue_def, GSYM SPACE, SPACE_BOREL, CLOSED_PAIR_EQ]);

val MEASURABLE_SETS_LEBESGUE = store_thm
  ("MEASURABLE_SETS_LEBESGUE", ``measurable_sets Lebesgue = subsets Borel``,
    PROVE_TAC [Lebesgue_def, GSYM SPACE, CLOSED_PAIR_EQ]);

val _ = overload_on ("lambda", ``measure Lebesgue``);

(* from now on, `lambda` is also the "length" of the line-segment from a to b *)
val lambda = store_thm
  ("lambda", ``!a b. a <= b ==> (lambda (line_segment a b) = Normal b - Normal a)``,
    cheat);

(* ------------------------------------------------------------------------- *)
(*  Almost everywhere (a.e) - basic binder definitions                       *)
(* ------------------------------------------------------------------------- *)

val almost_everywhere_def = Define
   `almost_everywhere m P = ?N. null_set m N /\ !x. x IN (m_space m DIFF N) ==> P x`;

(* This binder syntax is learnt from Thomas Tuerk. `Lebesgue` is a required
   household measure space for `AE x. P x` without `::m`, but it's never used.
 *)
val AE_def = new_definition ("AE_def",
  ``$AE = \P. almost_everywhere Lebesgue P``);

val _ = set_fixity "AE" Binder;
val _ = associate_restriction ("AE", "almost_everywhere");

val AE_THM = store_thm
  ("AE_THM", ``!m P. (AE x::m. P x) = almost_everywhere m P``,
    SIMP_TAC std_ss [almost_everywhere_def]);

val AE_ALT = store_thm (* [1, p.80] *)
  ("AE_ALT", ``!m P. (AE x::m. P x) =
                     ?N. null_set m N /\ {x | x IN m_space m /\ ~P x} SUBSET N``,
    RW_TAC std_ss [AE_THM, almost_everywhere_def, SUBSET_DEF, GSPECIFICATION, IN_DIFF]
 >> METIS_TAC []);

val FORALL_IMP_AE = store_thm
  ("FORALL_IMP_AE",
  ``!m P. measure_space m /\ (!x. x IN m_space m ==> P x) ==> AE x::m. P x``,
    RW_TAC std_ss [AE_THM, almost_everywhere_def]
 >> Q.EXISTS_TAC `{}`
 >> RW_TAC std_ss [NULL_SET_EMPTY, IN_DIFF, NOT_IN_EMPTY]);


(* ------------------------------------------------------------------------- *)
(*  Fatou's lemma for measures (limsup and liminf) [1, p.74]                 *)
(* ------------------------------------------------------------------------- *)

val set_limsup_def = Define
   `set_limsup (E :num -> 'a set) =
      BIGINTER (IMAGE (\m. BIGUNION {E n | m <= n}) UNIV)`;

val set_liminf_def = Define
   `set_liminf (E :num -> 'a set) =
      BIGUNION (IMAGE (\m. BIGINTER {E n | m <= n}) UNIV)`;

val _ = overload_on ("limsup", ``set_limsup``);
val _ = overload_on ("liminf", ``set_liminf``);

(* this lemma implicitly assume `events p = UNIV` *)
val liminf_limsup = store_thm
  ("liminf_limsup", ``!(E :num -> 'a set). COMPL (liminf E) = limsup (COMPL o E)``,
    RW_TAC std_ss [set_limsup_def, set_liminf_def]
 >> SIMP_TAC std_ss [COMPL_BIGUNION_IMAGE, o_DEF]
 >> Suff `!m. COMPL (BIGINTER {E n | m <= n}) = BIGUNION {COMPL (E n) | m <= n}` >- Rewr
 >> GEN_TAC >> REWRITE_TAC [COMPL_BIGINTER]
 >> Suff `IMAGE COMPL {E n | m <= n} = {COMPL (E n) | m <= n}` >- Rewr
 >> SIMP_TAC std_ss [IMAGE_DEF, IN_COMPL, Once GSPECIFICATION]
 >> RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, IN_COMPL]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (fs [COMPL_COMPL] >> Q.EXISTS_TAC `n` >> art [])
 >> fs []
 >> Q.EXISTS_TAC `E n` >> art []
 >> Q.EXISTS_TAC `n` >> art []);

val liminf_limsup_sp = store_thm (* more general form *)
  ("liminf_limsup_sp",
  ``!sp E. (!n. E n SUBSET sp) ==> (sp DIFF (liminf E) = limsup (\n. sp DIFF (E n)))``,
    RW_TAC std_ss [set_limsup_def, set_liminf_def]
 >> Q.ABBREV_TAC `f = (\m. BIGINTER {E n | m <= n})`
 >> Know `!m. f m SUBSET sp`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC \\
     RW_TAC std_ss [SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] \\
     fs [SUBSET_DEF] >> LAST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `SUC m` \\
     POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `E (SUC m)`)) \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `SUC m` >> RW_TAC arith_ss [])
 >> DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP GEN_COMPL_BIGUNION_IMAGE))
 >> Suff `!m. sp DIFF f m = BIGUNION {sp DIFF E n | m <= n}` >- Rewr
 >> GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC
 >> Know `!x. x IN {E n | m <= n} ==> x SUBSET sp`
 >- (RW_TAC std_ss [GSPECIFICATION] >> art [])
 >> DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP GEN_COMPL_BIGINTER))
 >> Suff `(IMAGE (\x. sp DIFF x) {E n | m <= n}) = {sp DIFF E n | m <= n}` >- Rewr
 >> RW_TAC std_ss [Once EXTENSION, IMAGE_DEF, IN_DIFF, GSPECIFICATION]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `n` >> METIS_TAC [])
 >> Q.EXISTS_TAC `E n` >> art []
 >> Q.EXISTS_TAC `n` >> art []);

(* TODO: migrate all limsup/liminf proofs from probabilityTheory here. *)

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales. Cambridge University Press (2005).
  [2] Mhamdi, T., Hasan, O., Tahar, S.: Formalization of Measure Theory and
      Lebesgue Integration for Probabilistic Analysis in HOL.
      ACM Trans. Embedded Comput. Syst. 12, 1--23 (2013).
  [3] Coble, A.R.: Anonymity, information, and machine-assisted proof, (2010).
  [4] Hurd, J.: Formal verification of probabilistic algorithms. (2001).
  [5] Wikipedia: https://en.wikipedia.org/wiki/Henri_Lebesgue
  [6] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
 *)
