(* ========================================================================= *)
(*        Lebesgue Measure Theory (lebesgue_measure_hvgScript.sml)           *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(* Note: This theory is inspired from isabelle                               *)
(* ------------------------------------------------------------------------- *)
(*  Equivalence of Lebesgue and Gauge (Henstock-Kurzweil) Integration        *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open prim_recTheory arithmeticTheory numTheory numLib pred_setTheory pred_setLib
     combinTheory hurdUtils jrhUtils cardinalTheory relationTheory whileTheory;

open realTheory realLib seqTheory transcTheory real_sigmaTheory iterateTheory
     topologyTheory metricTheory real_topologyTheory integrationTheory
     integerTheory intrealTheory;

open sigma_algebraTheory extrealTheory real_borelTheory measureTheory borelTheory
     lebesgueTheory martingaleTheory;

(* We only need very few theorems from these theories, which may be conflict
   with other opened theories.
 *)
local open integralTheory lift_ieeeTheory in end;
val integral_def = integrationTheory.integral_def;

val _ = new_theory "lebesgue_measure";

val ASM_ARITH_TAC = rpt (POP_ASSUM MP_TAC) >> ARITH_TAC; (* numLib *)
val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC;
fun METIS ths tm = prove(tm, METIS_TAC ths);

val _ = hide "top"; (* posetTheory *)
val _ = hide "nf";  (* relationTheory *)

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

(* Some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

(* ------------------------------------------------------------------------- *)
(*  Lebesgue sigma-algebra with the household Lebesgue measure (lebesgue)    *)
(* ------------------------------------------------------------------------- *)

Theorem absolutely_integrable_on_indicator :
    !A X. indicator A absolutely_integrable_on X <=>
          indicator A integrable_on X
Proof
    rpt GEN_TAC >> REWRITE_TAC [absolutely_integrable_on]
 >> EQ_TAC >> STRIP_TAC >> art []
 >> Suff ‘!x. abs(indicator A x) = indicator A x’
 >- (Rewr' >> METIS_TAC [ETA_AX])
 >> RW_TAC real_ss [indicator]
QED

Theorem has_integral_indicator_UNIV :
    !s A x. (indicator (s INTER A) has_integral x) UNIV =
            (indicator s has_integral x) A
Proof
    Know ‘!(s :real set) A. (\x. if x IN A then indicator s x else 0) =
                            indicator (s INTER A)’
 >- SET_TAC [indicator]
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> RW_TAC std_ss [HAS_INTEGRAL_RESTRICT_UNIV]
 >> METIS_TAC [ETA_AX]
QED

Theorem integral_indicator_UNIV :
    !s A. integral UNIV (indicator (s INTER A)) =
          integral A (indicator s)
Proof
  REWRITE_TAC [integral_def] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN METIS_TAC [has_integral_indicator_UNIV]
QED

Theorem integrable_indicator_UNIV :
    !s A. (indicator (s INTER A)) integrable_on UNIV <=>
          (indicator s) integrable_on A
Proof
  RW_TAC std_ss [integrable_on] THEN AP_TERM_TAC THEN
  ABS_TAC THEN METIS_TAC [has_integral_indicator_UNIV]
QED

Theorem integral_one : (* was: MEASURE_HOLLIGHT_EQ_ISABELLE *)
    !A. integral A (\x. 1) = integral univ(:real) (indicator A)
Proof
    ONCE_REWRITE_TAC [METIS [SET_RULE ``A = A INTER A``]
                          ``indicator A = indicator (A INTER A)``]
 >> SIMP_TAC std_ss [integral_indicator_UNIV]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC INTEGRAL_EQ >> SIMP_TAC std_ss [indicator]
QED

val indicator_fn_pos_le = INDICATOR_FN_POS;

Theorem has_integral_interval_cube :
    !a b n. (indicator (interval [a,b]) has_integral
               content (interval [a,b] INTER (line n))) (line n)
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM has_integral_indicator_UNIV] THEN
  SIMP_TAC std_ss [indicator, HAS_INTEGRAL_RESTRICT_UNIV] THEN
  SIMP_TAC std_ss [line, GSYM interval, INTER_INTERVAL] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``content (interval [(max a (-&n),min b (&n))]) =
                        content (interval [(max a (-&n),min b (&n))]) * 1``] THEN
  METIS_TAC [HAS_INTEGRAL_CONST]
QED

(* Lebesgue sigma-algebra with the household measure (lebesgue),
   constructed by Henstock-Kurzweil (gauge) Integration.

   Named after Henri Lebesgue (1875-1941), a French mathematician [5]

   NOTE: This definition of "Lebesgue measurable sets (and Lebesgue measure)"
   is aligned with Definition 18.1 [2, p.300] and 18.7 [2, p.304].
 *)
Definition lebesgue_def :
  lebesgue = (univ(:real),
              {A | !n. (indicator A) integrable_on (line n)},
              (\A. sup {Normal (integral (line n) (indicator A)) | n IN UNIV}))
End

Theorem space_lebesgue :
    m_space lebesgue = univ(:real)
Proof
    SIMP_TAC std_ss [lebesgue_def, m_space_def]
QED

Theorem in_sets_lebesgue : (* was: lebesgueI *)
    !A. (!n. indicator A integrable_on line n) ==> A IN measurable_sets lebesgue
Proof
    SIMP_TAC std_ss [lebesgue_def, measurable_sets_def] THEN SET_TAC []
QED

val lebesgueI = in_sets_lebesgue;

Theorem limseq_indicator_BIGUNION : (* was: LIMSEQ_indicator_UN *)
    !A x. ((\k. indicator (BIGUNION {(A:num->real->bool) i | i < k}) x) -->
           (indicator (BIGUNION {A i | i IN UNIV}) x)) sequentially
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``?i. x IN (A:num->real->bool) i`` THENL
  [ALL_TAC, FULL_SIMP_TAC std_ss [indicator, IN_BIGUNION] THEN
   SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] THEN
   KNOW_TAC ``~(?s. x IN s /\ ?i. s = (A:num->real->bool) i)`` THENL
   [METIS_TAC [], DISCH_TAC] THEN
   KNOW_TAC ``!k. ~(?s. x IN s /\ ?i. (s = (A:num->real->bool) i) /\ i < k)`` THENL
   [METIS_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC std_ss [LIM_CONST]] THEN
  FULL_SIMP_TAC std_ss [] THEN
  KNOW_TAC ``!k. indicator (BIGUNION {(A:num->real->bool) j | j < k + SUC i}) x = 1`` THENL
  [RW_TAC real_ss [indicator, GSPECIFICATION, IN_BIGUNION] THEN
   UNDISCH_TAC ``~?s. x IN s /\ ?j. (s = (A:num->real->bool) j) /\ j < k + SUC i`` THEN
   SIMP_TAC std_ss [] THEN EXISTS_TAC ``(A:num->real->bool) i`` THEN
   ASM_SIMP_TAC std_ss [] THEN EXISTS_TAC  ``i:num`` THEN ASM_SIMP_TAC std_ss [] THEN
   ARITH_TAC, DISCH_TAC] THEN
  KNOW_TAC ``indicator (BIGUNION {(A:num->real->bool) i | i IN univ(:num)}) x = 1`` THENL
  [RW_TAC real_ss [indicator, GSPECIFICATION, IN_BIGUNION] THEN
   POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [IN_UNIV] THEN METIS_TAC [], DISCH_TAC] THEN
  MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC ``SUC i`` THEN
  ASM_SIMP_TAC std_ss [LIM_CONST]
QED

val LIMSEQ_indicator_UN = limseq_indicator_BIGUNION;

Theorem sigma_algebra_lebesgue :
    sigma_algebra (UNIV, {A | !n. (indicator A) integrable_on (line n)})
Proof
    RW_TAC std_ss [sigma_algebra_alt_pow]
 >- (REWRITE_TAC [POW_DEF] >> SET_TAC [])
 >- (SIMP_TAC std_ss [GSPECIFICATION] \\
     Know `indicator {} = (\x:real. 0)` >- SET_TAC [indicator] \\
     Rewr' >> SIMP_TAC std_ss [INTEGRABLE_0])
 >- (FULL_SIMP_TAC std_ss [GSPECIFICATION] \\
     Know `indicator (univ(:real) DIFF s) = (\x. 1 - indicator s x)`
     >- (SIMP_TAC std_ss [indicator] >> ABS_TAC \\
         SIMP_TAC std_ss [IN_DIFF, IN_UNIV] >> COND_CASES_TAC \\
         FULL_SIMP_TAC real_ss []) >> Rewr' \\
     ONCE_REWRITE_TAC [METIS [] ``(\x. 1 - indicator s x) =
                        (\x. (\x. 1) x - (\x. indicator s x) x)``] \\
     GEN_TAC >> MATCH_MP_TAC INTEGRABLE_SUB >> CONJ_TAC >|
     [SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
      METIS_TAC [ETA_AX]])
 >> FULL_SIMP_TAC std_ss [GSPECIFICATION]
 >> KNOW_TAC ``!k n. indicator (BIGUNION {(A:num->real->bool) i | i < k})
              integrable_on (line n)``
 >- (Induct_on `k`
     >- (SIMP_TAC std_ss [LT] THEN REWRITE_TAC [SET_RULE ``BIGUNION {A i | i | F} = {}``] THEN
         KNOW_TAC ``indicator {} = (\x:real. 0)``
         THENL [SET_TAC [indicator], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
         SIMP_TAC std_ss [INTEGRABLE_0]) \\
     KNOW_TAC ``BIGUNION {A i | i < SUC k} =
              BIGUNION {(A:num->real->bool) i | i < k} UNION A k`` THENL
     [ SIMP_TAC std_ss [ADD1, ARITH_PROVE ``i < SUC k <=> (i < k \/ (i = k))``] THEN
       SET_TAC [], DISCH_TAC THEN ASM_REWRITE_TAC [] ] THEN
     KNOW_TAC ``indicator (BIGUNION {(A:num->real->bool) i | i < k} UNION A k) =
                (\x. max (indicator (BIGUNION {A i | i < k}) x) (indicator (A k) x))`` THENL
     [ SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
       SIMP_TAC std_ss [max_def, indicator] THEN
       REPEAT COND_CASES_TAC THEN FULL_SIMP_TAC std_ss [IN_UNION] THEN
       POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FULL_SIMP_TAC real_ss [],
       DISCH_TAC ] THEN
     REWRITE_TAC [GSYM absolutely_integrable_on_indicator] THEN GEN_TAC THEN
     ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX THEN
     ASM_SIMP_TAC std_ss [absolutely_integrable_on_indicator] THEN
     FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [])
 >> DISCH_TAC
 >> GEN_TAC
 >> MP_TAC (ISPECL [``(\k. indicator (BIGUNION {(A:num->real->bool) i | i < k}))``,
                  ``indicator (BIGUNION {(A:num->real->bool) i | i IN univ(:num)})``,
                  ``(\x:real. 1:real)``, ``line n``] DOMINATED_CONVERGENCE)
 >> KNOW_TAC ``(!k.
      (\k. indicator (BIGUNION {(A:num->real->bool) i | i < k})) k integrable_on line n) /\
      (\x. 1) integrable_on line n /\
      (!k x.
        x IN line n ==>
        abs ((\k. indicator (BIGUNION {A i | i < k})) k x) <= (\x. 1) x) /\
      (!x.
        x IN line n ==>
          ((\k. (\k. indicator (BIGUNION {A i | i < k})) k x) -->
          indicator (BIGUNION {A i | i IN univ(:num)}) x) sequentially)``
 >| [ALL_TAC, METIS_TAC []]
 >> REPEAT CONJ_TAC
 >| [ FULL_SIMP_TAC std_ss [],
      SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
      SIMP_TAC std_ss [DROP_INDICATOR_ABS_LE_1],
      METIS_TAC [LIMSEQ_indicator_UN] ]
QED

Theorem sets_lebesgue :
    measurable_sets lebesgue = {A | !n. (indicator A) integrable_on (line n)}
Proof
    SIMP_TAC std_ss [lebesgue_def, measurable_sets_def]
QED

Theorem in_sets_lebesgue_imp : (* was: lebesgueD *)
    !A n. A IN measurable_sets lebesgue ==> indicator A integrable_on line n
Proof
    SIMP_TAC std_ss [sets_lebesgue, GSPECIFICATION]
QED

val lebesgueD = in_sets_lebesgue_imp;

Theorem measure_lebesgue :
    measure lebesgue =
      (\A. sup {Normal (integral (line n) (indicator A)) | n IN UNIV})
Proof
    SIMP_TAC std_ss [measure_def, lebesgue_def]
QED

Theorem positive_lebesgue :
    positive lebesgue
Proof
  SIMP_TAC std_ss [lebesgue_def, positive_def, sets_lebesgue, measure_lebesgue] THEN
  SIMP_TAC std_ss [INDICATOR_EMPTY, IN_UNIV, INTEGRAL_0, extreal_of_num_def] THEN
   REWRITE_TAC [SET_RULE ``{Normal 0 | n | T} = {Normal 0}``, sup_sing] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC le_sup_imp THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
  EXISTS_TAC ``0:num`` THEN SIMP_TAC std_ss [extreal_11, line, GSYM interval] THEN
  SIMP_TAC std_ss [REAL_NEG_0, INTEGRAL_REFL]
QED

Theorem countably_additive_lebesgue :
    countably_additive lebesgue
Proof
    RW_TAC std_ss [countably_additive_def]
 >> Know `!A. IMAGE A univ(:num) SUBSET measurable_sets lebesgue ==>
              !i n. indicator (A i) integrable_on line n`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC lebesgueD \\
     FULL_SIMP_TAC std_ss [SUBSET_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> METIS_TAC [IN_IMAGE, IN_UNIV])
 >> DISCH_TAC
 >> Know `!i n. 0 <= integral (line n) (indicator ((f:num->real->bool) i))`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC INTEGRAL_COMPONENT_POS \\
     SIMP_TAC std_ss [DROP_INDICATOR_POS_LE] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     FULL_SIMP_TAC std_ss [IN_FUNSET, SUBSET_DEF, IN_IMAGE] \\
     METIS_TAC []) >> DISCH_TAC
 >> Know `BIGUNION {f i | i IN UNIV} IN measurable_sets lebesgue ==>
          !i n. (indicator ((f:num->real->bool) i)) integrable_on line n`
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC lebesgueD \\
     FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV])
 >> FULL_SIMP_TAC std_ss [GSYM IMAGE_DEF] >> DISCH_TAC
 >> SIMP_TAC std_ss [o_DEF, measure_lebesgue]
 >> Know `suminf (\i. sup {(\n i. Normal (integral (line n) (indicator (f i)))) n i | n IN UNIV}) =
          sup {suminf (\i. (\n i. Normal (integral (line n) (indicator (f i)))) n i) | n IN UNIV}`
 >- (MATCH_MP_TAC ext_suminf_sup_eq \\
     SIMP_TAC std_ss [extreal_of_num_def] \\
     CONJ_TAC
     >- (SIMP_TAC std_ss [extreal_le_def] >> rpt STRIP_TAC \\
         MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE \\
         FULL_SIMP_TAC std_ss [LINE_MONO, DROP_INDICATOR_POS_LE]) \\
     SIMP_TAC std_ss [extreal_le_def] \\
     rpt GEN_TAC >> MATCH_MP_TAC INTEGRAL_COMPONENT_POS \\
     FULL_SIMP_TAC std_ss [DROP_INDICATOR_POS_LE])
 >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
 >> Suff `!n. Normal (integral (line n) (indicator (BIGUNION (IMAGE f univ(:num))))) =
              suminf (\x. Normal (integral (line n) (indicator ((f:num->real->bool) x))))`
 >- (DISCH_TAC >> ASM_SIMP_TAC std_ss [])
 >> GEN_TAC
 >> Know `suminf (\x. Normal (integral (line n) (indicator (f x)))) =
          sup (IMAGE (\n'. EXTREAL_SUM_IMAGE (\x. Normal (integral (line n) (indicator (f x))))
                                             (count n')) UNIV)`
 >- (MATCH_MP_TAC ext_suminf_def \\
     rw [extreal_of_num_def, extreal_le_eq]) >> Rewr'
 >> SIMP_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_NORMAL]
 >> Know `mono_increasing
          (\n'. SIGMA (\x. integral (line n) (indicator ((f:num->real->bool) x))) (count n'))`
 >- (SIMP_TAC std_ss [mono_increasing_def] THEN
     REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     SIMP_TAC std_ss [FINITE_COUNT, GSYM EXTREAL_SUM_IMAGE_NORMAL] THEN
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
     ASM_SIMP_TAC real_ss [count_def, GSPECIFICATION, FINITE_COUNT, SUBSET_DEF] THEN
     REPEAT STRIP_TAC THEN REWRITE_TAC [extreal_of_num_def, extreal_le_def] THEN
     MATCH_MP_TAC INTEGRAL_COMPONENT_POS THEN
     ASM_SIMP_TAC std_ss [DROP_INDICATOR_POS_LE]) >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [GSYM sup_seq', REAL_SUM_IMAGE_COUNT]
 >> Know `!n m. sum (0,m) (\x. integral (line n) (indicator ((f:num->real->bool) x))) =
                integral (line n) (indicator (BIGUNION {f i | i < m}))`
 THENL (* The rest (original proof) works fine *)
[GEN_TAC THEN Induct_on `m` THENL
  [REWRITE_TAC [realTheory.sum, LT] THEN
  REWRITE_TAC [SET_RULE ``{f i | i | F} = {}``, BIGUNION_EMPTY] THEN
  SIMP_TAC real_ss [INDICATOR_EMPTY, INTEGRAL_0], ALL_TAC] THEN
 KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} IN
                measurable_sets lebesgue`` THENL
 [GEN_TAC THEN MATCH_MP_TAC lebesgueI THEN GEN_TAC THEN
  ASSUME_TAC sigma_algebra_lebesgue THEN
  FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, GSPECIFICATION, subsets_def, space_def] THEN
  POP_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN CONJ_TAC THENL
  [REWRITE_TAC [pred_setTheory.COUNTABLE_ALT] THEN SET_TAC [], ALL_TAC] THEN METIS_TAC [],
  DISCH_TAC] THEN
 KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} INTER f m = {}`` THENL
 [GEN_TAC THEN SIMP_TAC std_ss [INTER_DEF, IN_BIGUNION, GSPECIFICATION] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
  GEN_TAC THEN ASM_CASES_TAC ``x NOTIN (f:num->real->bool) m'`` THEN
  ASM_REWRITE_TAC [] THEN GEN_TAC THEN
  ASM_CASES_TAC ``x IN (s:real->bool)`` THEN FULL_SIMP_TAC std_ss [] THEN
  GEN_TAC THEN ASM_CASES_TAC ``~(i < m':num)`` THEN FULL_SIMP_TAC std_ss [] THEN
  EXISTS_TAC ``x:real`` THEN FULL_SIMP_TAC std_ss [DISJOINT_DEF] THEN
  POP_ASSUM MP_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP LESS_NOT_EQ) THEN
  ASM_SET_TAC [], DISCH_TAC] THEN
 KNOW_TAC ``!x. indicator (BIGUNION {(f:num->real->bool) i | i < SUC m}) x =
                indicator (BIGUNION {f i | i < m}) x +
                indicator (f m) x`` THENL
 [GEN_TAC THEN SIMP_TAC std_ss [indicator] THEN
  ASM_CASES_TAC ``x IN ((f:num->real->bool) m)`` THEN ASM_SIMP_TAC std_ss [] THENL
  [KNOW_TAC ``x NOTIN BIGUNION {(f:num->real->bool) i | i < m}`` THENL
   [ASM_SET_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC real_ss [IN_BIGUNION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN
   KNOW_TAC ``?s. x IN s /\ ?i. (s = (f:num->real->bool) i) /\ i < SUC m`` THENL
   [ALL_TAC, METIS_TAC []] THEN EXISTS_TAC ``(f:num->real->bool) m`` THEN
   ASM_REWRITE_TAC [] THEN EXISTS_TAC ``m:num`` THEN SIMP_TAC arith_ss [], ALL_TAC] THEN
   FULL_SIMP_TAC real_ss [IN_BIGUNION, GSPECIFICATION] THEN COND_CASES_TAC THENL
   [ALL_TAC, COND_CASES_TAC THENL [ALL_TAC, SIMP_TAC real_ss []] THEN
    FULL_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o SPEC ``s:real->bool``) THEN
    ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o SPEC ``i:num``) THEN
    ASM_SIMP_TAC arith_ss []] THEN FULL_SIMP_TAC std_ss [] THEN
   COND_CASES_TAC THENL [SIMP_TAC std_ss [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o SPEC ``(f:num->real->bool) i``) THEN
   ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o SPEC ``i:num``) THEN
   RW_TAC std_ss [] THEN KNOW_TAC ``i = m:num`` THENL
   [ASM_SIMP_TAC arith_ss [], DISCH_TAC] THEN FULL_SIMP_TAC std_ss [],
   DISCH_TAC] THEN
  ONCE_REWRITE_TAC [realTheory.sum] THEN ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN REWRITE_TAC [ADD] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
               [METIS [] ``!f. indicator f = (\x. indicator f x)``] THEN
  SIMP_TAC std_ss [] THEN
  KNOW_TAC ``integral (line n') (indicator (BIGUNION {f i | i < SUC m})) =
             integral (line n') ((\x. (\x. indicator (BIGUNION {f i | i < m}) x) x +
                                 (\x. indicator ((f:num->real->bool) m) x) x))`` THENL
  [FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   ASM_SIMP_TAC std_ss [] THEN METIS_TAC [], DISC_RW_KILL] THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN METIS_TAC [lebesgueD], DISCH_TAC] THEN
  ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC (METIS [] ``!P. (P /\ Q) ==> Q``) THEN
  ONCE_REWRITE_TAC [METIS []
        ``(indicator (BIGUNION {(f:num->real->bool) i | i < n'})) =
     (\n'. indicator (BIGUNION {f i | i < n'})) n'``] THEN
  EXISTS_TAC ``(indicator (BIGUNION (IMAGE (f:num->real->bool) univ(:num))))
                integrable_on (line n)`` THEN
  MATCH_MP_TAC DOMINATED_CONVERGENCE THEN EXISTS_TAC ``\x:real. 1:real`` THEN
  REPEAT CONJ_TAC THENL
  [KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} IN
                measurable_sets lebesgue`` THENL
  [GEN_TAC THEN MATCH_MP_TAC lebesgueI THEN GEN_TAC THEN
   ASSUME_TAC sigma_algebra_lebesgue THEN
   FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, GSPECIFICATION, subsets_def, space_def] THEN
   POP_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC [pred_setTheory.COUNTABLE_ALT] THEN SET_TAC [], ALL_TAC] THEN
    METIS_TAC [],
    DISCH_TAC] THEN METIS_TAC [lebesgueD],
   SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
   FULL_SIMP_TAC std_ss [DROP_INDICATOR_ABS_LE_1], ALL_TAC] THEN
  METIS_TAC [LIMSEQ_indicator_UN, IMAGE_DEF]
QED

Theorem measure_space_lebesgue :
    measure_space lebesgue
Proof
    SIMP_TAC std_ss [measure_space_def, positive_lebesgue]
 >> SIMP_TAC std_ss [sets_lebesgue, space_lebesgue, sigma_algebra_lebesgue]
 >> SIMP_TAC std_ss [countably_additive_lebesgue]
QED

Theorem borel_imp_lebesgue_sets : (* was: lebesgueI_borel *)
    !s. s IN subsets borel ==> s IN measurable_sets lebesgue
Proof
    RW_TAC std_ss [borel_eq_ge_le]
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (‘s’, ‘s’)
 >> REWRITE_TAC [GSYM SUBSET_DEF]
 >> ‘measurable_sets lebesgue = subsets (m_space lebesgue,measurable_sets lebesgue)’
       by rw [subsets_def]
 >> POP_ORW
 >> ‘univ(:real) = space (m_space lebesgue,measurable_sets lebesgue)’
       by rw [space_def, space_lebesgue]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> CONJ_TAC >- rw [space_lebesgue, sets_lebesgue, sigma_algebra_lebesgue]
 >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV, subsets_def]
 >> rename1 ‘(\(a,b). {x | a <= x /\ x <= b}) y IN measurable_sets lebesgue’
 >> Cases_on ‘y’
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC lebesgueI
 >> REWRITE_TAC [integrable_on, GSYM interval]
 >> METIS_TAC [has_integral_interval_cube]
QED

val lebesgueI_borel = borel_imp_lebesgue_sets;

(* TODO: prove this theorem with PSUBSET, i.e. the existence of non-Borel
   Lebesgue-measurable sets.
 *)
Theorem lborel_subset_lebesgue :
    measurable_sets lborel SUBSET measurable_sets lebesgue
Proof
    RW_TAC std_ss [SUBSET_DEF, sets_lborel]
 >> MATCH_MP_TAC lebesgueI_borel >> art []
QED

Theorem borel_imp_lebesgue_measurable :
    !f. f IN borel_measurable (space borel, subsets borel) ==>
        f IN borel_measurable (m_space lebesgue, measurable_sets lebesgue)
Proof
    RW_TAC std_ss [measurable_def, GSPECIFICATION]
 >| [ FULL_SIMP_TAC std_ss [space_lebesgue, space_borel, space_def],
      FULL_SIMP_TAC std_ss [space_def, subsets_def] ]
 >> FULL_SIMP_TAC std_ss [space_borel, space_lebesgue, INTER_UNIV]
 >> MATCH_MP_TAC lebesgueI_borel >> ASM_SET_TAC []
QED

val borel_measurable_lebesgueI = borel_imp_lebesgue_measurable;

(* |- !f. f IN borel_measurable borel ==>
          f IN borel_measurable (m_space lebesgue,measurable_sets lebesgue)
 *)
Theorem borel_imp_lebesgue_measurable' =
    REWRITE_RULE [SPACE] borel_imp_lebesgue_measurable

Theorem negligible_in_lebesgue :
    !s. negligible s ==> s IN measurable_sets lebesgue
Proof
    RW_TAC std_ss [negligible]
 >> MATCH_MP_TAC lebesgueI
 >> METIS_TAC [integrable_on, line, GSYM interval]
QED

val lebesgueI_negligible = negligible_in_lebesgue;

Theorem lebesgue_of_negligible :
    !s. negligible s ==> (measure lebesgue s = 0)
Proof
    RW_TAC std_ss [measure_lebesgue]
 >> Know `!n. integral (line n) (indicator s) = 0`
 >- (FULL_SIMP_TAC std_ss [integral_def, negligible, line, GSYM interval] \\
     GEN_TAC >> MATCH_MP_TAC SELECT_UNIQUE \\
     GEN_TAC \\
     reverse EQ_TAC >- METIS_TAC [] \\
     METIS_TAC [HAS_INTEGRAL_UNIQUE]) >> Rewr
 >> SIMP_TAC std_ss [GSYM extreal_of_num_def]
 >> REWRITE_TAC [SET_RULE ``{(0 :extreal) | n IN UNIV} = {0}``]
 >> SIMP_TAC std_ss [sup_sing]
QED

val lmeasure_eq_0 = lebesgue_of_negligible;

Theorem lebesgue_measure_iff_LIMSEQ[local] :
    !A m. A IN measurable_sets lebesgue /\ 0 <= m ==>
         (measure lebesgue A = Normal m <=>
          ((\n. integral (line n) (indicator A)) --> m) sequentially)
Proof
    RW_TAC std_ss [Once EQ_SYM_EQ]
 >> `!n. Normal (integral (line n) (indicator A)) =
         Normal ((\n. integral (line n) (indicator A)) n)` by METIS_TAC []
 >> SIMP_TAC std_ss [measure_lebesgue, GSYM IMAGE_DEF]
 >> ONCE_ASM_REWRITE_TAC []
 >> MATCH_MP_TAC sup_seq'
 >> RW_TAC std_ss [mono_increasing_def]
 >> MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE
 >> ASM_SIMP_TAC std_ss [LINE_MONO, lebesgueD, DROP_INDICATOR_POS_LE]
QED

val lmeasure_iff_LIMSEQ = lebesgue_measure_iff_LIMSEQ;

(* It's hard to calculate `measure lebesgue` on intervals by "lebesgue_def",
   but once the following lemma is proven, by UNIQUENESS_OF_MEASURE we
   will have `lebesgue` and `lborel` coincide on `subsets borel`, and thus
  `measure lebesgue` of other intervals can be derived from lambda lemmas.

   Most steps are from "lborel_eqI" (HVG's lebesgue_measure_hvgScript.sml).
 *)
Theorem lebesgue_closed_interval :
    !a b. a <= b ==> measure lebesgue (interval [a,b]) = Normal (b - a)
Proof
    RW_TAC std_ss [lebesgue_def, measure_def, GSYM CONTENT_CLOSED_INTERVAL]
 >> SIMP_TAC std_ss [sup_eq']
 >> CONJ_TAC >> GEN_TAC
 >- (SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] \\
     STRIP_TAC >> POP_ORW \\
     ASM_SIMP_TAC std_ss [extreal_le_def] \\
     ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] \\
     ONCE_REWRITE_TAC [INTER_COMM] \\
     REWRITE_TAC [integral_indicator_UNIV] \\
     GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID] \\
     MATCH_MP_TAC INTEGRAL_COMPONENT_UBOUND \\
     SIMP_TAC std_ss [DROP_INDICATOR_LE_1] \\
     ONCE_REWRITE_TAC [GSYM integrable_indicator_UNIV] \\
     SIMP_TAC std_ss [INTER_INTERVAL, line, GSYM interval, indicator] \\
     ONCE_REWRITE_TAC [METIS [] ``1 = (\x:real. 1:real) x``] \\
     REWRITE_TAC [INTEGRABLE_RESTRICT_UNIV, INTEGRABLE_CONST])
 >> DISCH_THEN MATCH_MP_TAC
 >> SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV, extreal_11]
 >> MP_TAC (Q.SPECL [`abs a`, `abs b`] REAL_LE_TOTAL)
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `?n. abs b <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] \\
      Q.EXISTS_TAC `n` >> MATCH_MP_TAC INTEGRAL_UNIQUE \\
      Suff `{x | a <= x /\ x <= b} = {x | a <= x /\ x <= b} INTER line n`
      >- METIS_TAC [has_integral_interval_cube, GSYM interval] \\
      SIMP_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, line] \\
      GEN_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> REAL_ARITH_TAC,
      (* goal 2 (of 2) *)
     `?n. abs a <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] \\
      Q.EXISTS_TAC `n` THEN MATCH_MP_TAC INTEGRAL_UNIQUE \\
      Suff `{x | a <= x /\ x <= b} = {x | a <= x /\ x <= b} INTER line n`
      >- METIS_TAC [has_integral_interval_cube, GSYM interval] \\
      SIMP_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, line] \\
      GEN_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> REAL_ARITH_TAC ]
QED

(* |- !c. measure lebesgue {c} = 0 *)
Theorem lebesgue_sing =
   ((Q.GEN `c`) o
    (SIMP_RULE real_ss [REAL_LE_REFL, GSYM extreal_of_num_def, INTERVAL_SING]) o
    (Q.SPECL [`c`,`c`])) lebesgue_closed_interval;

Theorem lebesgue_empty :
    measure lebesgue {} = 0
Proof
    MATCH_MP_TAC lebesgue_of_negligible
 >> REWRITE_TAC [NEGLIGIBLE_EMPTY]
QED

Theorem lebesgue_closed_interval_content :
    !a b. measure lebesgue (interval [a,b]) = Normal (content (interval [a,b]))
Proof
    rpt STRIP_TAC
 >> `a <= b \/ b < a` by PROVE_TAC [REAL_LTE_TOTAL]
 >- ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL, lebesgue_closed_interval]
 >> IMP_RES_TAC REAL_LT_IMP_LE
 >> fs [GSYM CONTENT_EQ_0, GSYM extreal_of_num_def]
 >> fs [INTERVAL_EQ_EMPTY, lebesgue_empty]
QED

(* A direct application of the above theorem:
   |- measure_space (space borel,subsets borel,measure lebesgue) ==>
      !s. s IN subsets borel ==> lambda s = measure lebesgue s
 *)
val lemma =
    REWRITE_RULE [m_space_def, measurable_sets_def, measure_def,
                  lebesgue_closed_interval_content]
      (Q.SPEC `(space borel, subsets borel, measure lebesgue)` lambda_eq);

(* final theorem (in this section): lborel and lebesgue coincide on borel *)
Theorem lambda_eq_lebesgue :
    !s. s IN subsets borel ==> lambda s = measure lebesgue s
Proof
    MATCH_MP_TAC lemma
 >> ASSUME_TAC borel_imp_lebesgue_sets
 >> RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def,
                   SPACE, sigma_algebra_borel] (* 2 subgoals *)
 >| [ (* goal 1 (of 2): positive *)
      MP_TAC positive_lebesgue \\
      RW_TAC std_ss [positive_def, measure_def, measurable_sets_def],
      (* goal 2 (of 2): countably_additive *)
      MP_TAC countably_additive_lebesgue \\
      RW_TAC std_ss [countably_additive_def, measure_def, measurable_sets_def,
                     IN_FUNSET, IN_UNIV] ]
QED

(* |- !s. s IN subsets borel ==> measure lebesgue s = lambda s *)
Theorem lebesgue_eq_lambda = GSYM lambda_eq_lebesgue;

(* a sample application of "lebesgue_eq_lambda" *)
Theorem lebesgue_open_interval :
    !a b. a <= b ==> measure lebesgue (interval (a,b)) = Normal (b - a)
Proof
    rpt STRIP_TAC
 >> `interval (a,b) IN subsets borel`
       by METIS_TAC [borel_measurable_sets, interval]
 >> ASM_SIMP_TAC std_ss [lebesgue_eq_lambda, lambda_open_interval]
QED

Overload m_lebesgue = “measure lebesgue”

(* ------------------------------------------------------------------------- *)
(*  Equivalence of Lebesgue and Gauge (Henstock-Kurzweil) Integration        *)
(* ------------------------------------------------------------------------- *)

(* |- !k x.
        0 <= x /\ x < 1 /\ 0 < k ==>
        ?n. n < 2 ** k /\ &n / 2 pow k <= x /\ x < &SUC n / 2 pow k
 *)
val lemma1 = lift_ieeeTheory.error_bound_lemma1 |> Q.SPEC ‘k’ |> GEN_ALL

(* lemma1 also holds if “0 < k” is removed *)
Triviality lemma1a :
    !k x. 0 <= x /\ x < (1 :real) ==>
          ?n. n < 2 ** k /\ &n / 2 pow k <= x /\ x < &SUC n / 2 pow k
Proof
    rpt STRIP_TAC
 >> ‘k = 0 \/ 0 < k’ by simp [] >- rw []
 >> MATCH_MP_TAC lemma1 >> art []
QED

Triviality lemma1b :
    !k x. 0 <= x /\ x <= (1 :real) ==>
          ?n. n < 2 ** k /\ &n / 2 pow k <= x /\ x <= &SUC n / 2 pow k
Proof
    rpt STRIP_TAC
 >> ‘x < 1 \/ x = (1 :real)’ by PROVE_TAC [REAL_LE_LT]
 >- (MP_TAC (Q.SPECL [‘k’, ‘x’] lemma1a) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘n’ >> RW_TAC real_ss [REAL_LT_IMP_LE])
 >> POP_ORW
 >> Q.EXISTS_TAC ‘2 ** k - 1’ >> simp [REAL_POW]
QED

Theorem lemma1c[local] :
    !k x c. c <= x /\ x <= c + (1 :real) ==>
            ?n. n < 2 ** k /\ c + &n / 2 pow k <= x /\ x <= c + &SUC n / 2 pow k
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘k’, ‘x - c’] lemma1b)
 >> impl_tac >- REAL_ASM_ARITH_TAC
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘n’
 >> REAL_ASM_ARITH_TAC
QED

(* |- !k x.
        0 <= x /\ x < 1 /\ 0 < k ==>
        ?n. n <= 2 ** k /\ abs (x - &n / 2 pow k) <= 1 / 2 pow SUC k
 *)
val lemma2 = lift_ieeeTheory.error_bound_lemma2 |> Q.SPEC ‘k’ |> GEN_ALL
          |> SIMP_RULE real_ss [REAL_INV_1OVER, GSYM ADD1]

(* remove “0 < k”, use “_ <= 1 / 2 pow k” instead of “_ <= 1 / 2 pow SUC k” *)
Triviality lemma2a :
    !k x. 0 <= x /\ x < (1 :real) ==>
          ?n. n <= 2 ** k /\ abs (x - &n / 2 pow k) <= 1 / 2 pow k
Proof
    rpt STRIP_TAC
 >> ‘k = 0 \/ 0 < k’ by simp []
 >- (Q.EXISTS_TAC ‘0’ >> simp [ABS_BOUNDS, REAL_LT_IMP_LE] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘0’ >> simp [])
 >> MP_TAC (Q.SPECL [‘k’, ‘x’] lemma2)
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘n’ >> art []
 >> Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1 / 2 pow SUC k’ >> art []
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> simp [REAL_POW_MONO_LT]
QED

(* furthermore, use “n < 2 ** k” instead of “n <= 2 ** k”

   NOTE: It turns out that lemma2 (and all variants) are not needed. Only
   lemma1a is used in [dyadic_covering_lemma_01] below.
 *)
Triviality lemma2b :
    !k x. 0 <= x /\ x < (1 :real) ==>
          ?n. n < 2 ** k /\ abs (x - &n / 2 pow k) <= 1 / 2 pow k
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘k’, ‘x’] lemma2a)
 >> RW_TAC std_ss []
 >> ‘n < 2 ** k \/ n = 2 ** k’ by simp []
 >- (Q.EXISTS_TAC ‘n’ >> art [])
 >> Q.PAT_X_ASSUM ‘abs _ <= 1 / 2 pow k’ MP_TAC
 >> ASM_SIMP_TAC real_ss [GSYM REAL_POW]
 >> ‘2 pow k / 2 pow k = (1 :real)’ by simp [REAL_DIV_REFL] >> POP_ORW
 >> ‘x - 1 < 0 :real’ by simp [REAL_SUB_LT_NEG]
 >> ASM_SIMP_TAC real_ss [ABS_EQ_NEG]
 >> ‘1 - x <= 1 / 2 pow k <=> 1 - 1 / 2 pow k <= x’ by REAL_ARITH_TAC
 >> POP_ORW
 >> Know ‘(1 - 1 / 2 pow k) :real = &(2 ** k) / 2 pow k - 1 / 2 pow k’
 >- (ASM_SIMP_TAC real_ss [GSYM REAL_POW] \\
     Suff ‘2 pow k / 2 pow k = (1 :real)’ >- rw [] \\
     MATCH_MP_TAC REAL_DIV_REFL >> simp [])
 >> Rewr'
 >> REWRITE_TAC [REAL_DIV_SUB]
 >> ‘&(2 ** k) - (1 :real) = &(2 ** k - 1)’
      by simp [realaxTheory.REAL_OF_NUM_SUB] >> POP_ORW
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘2 ** k - 1’
 >> SIMP_TAC real_ss [EXP_POS]
 >> ‘(0 :real) <= x - &(2 ** k - 1) / 2 pow k’ by simp [REAL_SUB_LE]
 >> ASM_SIMP_TAC real_ss [ABS_EQ_POS]
 >> REWRITE_TAC [REAL_LE_SUB_RADD, REAL_DIV_ADD]
 >> SIMP_TAC real_ss [REAL_OF_NUM_ADD]
 >> SIMP_TAC arith_ss [GSYM LESS_EQ_ADD_SUB]
 >> SIMP_TAC real_ss [GSYM REAL_POW]
 >> Suff ‘2 pow k / 2 pow k = (1 :real)’ >- rw [REAL_LT_IMP_LE]
 >> MATCH_MP_TAC REAL_DIV_REFL >> simp []
QED

(* |- !k x.
        1 <= x /\ x < 2 /\ 0 < k ==>
        ?n. n <= 2 ** k /\ abs (1 + &n / 2 pow k - x) <= 1 / 2 pow SUC k
 *)
val lemma3 = lift_ieeeTheory.error_bound_lemma3 |> Q.SPEC ‘k’ |> GEN_ALL
          |> SIMP_RULE real_ss [REAL_INV_1OVER, GSYM ADD1]

(* |- !y. 0 < y ==> ?n. 1 / 2 pow n < y *)
val lemma4 = REAL_ARCH_POW_INV |> Q.SPEC ‘1 / 2’
          |> SIMP_RULE real_ss [pow_div, POW_ONE]

Triviality lemma5 :
    !n k. &n / 2 pow k < (&SUC n / 2 pow k) :real
Proof
    rpt GEN_TAC
 >> qmatch_abbrev_tac ‘x / z < y / (z :real)’
 >> Know ‘x / z < y / z <=> x < y’
 >- (MATCH_MP_TAC REAL_LT_RDIV >> simp [Abbr ‘z’])
 >> Rewr'
 >> simp [Abbr ‘x’, Abbr ‘y’]
QED

Triviality lemma5a :
    !n k c. c + &n / 2 pow k < (c + &SUC n / 2 pow k) :real
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC REAL_LT_IADD
 >> REWRITE_TAC [lemma5]
QED

Triviality lemma6 :
    !n k. &SUC n / 2 pow k - &n / 2 pow k = (1 / 2 pow k) :real
Proof
    RW_TAC real_ss [REAL_DIV_SUB]
 >> simp [GSYM realaxTheory.REAL_OF_NUM_SUB]
QED

Triviality lemma6a :
    !n k c. (c + &SUC n / 2 pow k) - (c + &n / 2 pow k) = (1 / 2 pow k) :real
Proof
    rw [REAL_ARITH “c + a - (c + b) = a - (b :real)”, lemma6]
QED

Definition nonoverlapping_def :
    nonoverlapping s t <=> DISJOINT (interior s) (interior t)
End

(* cf. right_open_interval_11 *)
Theorem closed_interval_11 :
    !a b c d. a < b /\ c < d ==>
             (interval [a,b] = interval [c,d] <=> a = c /\ b = d)
Proof
    rw [EQ_INTERVAL, GSYM INTERVAL_EQ_EMPTY]
 >> REAL_ASM_ARITH_TAC
QED

(* cf. right_open_interval_SUBSET_EQ, ordering: [c [a, b] d] *)
Theorem closed_interval_subset_eq :
    !a b c d. a < b /\ c < d ==>
             (interval [a,b] SUBSET interval [c,d] <=> c <= a /\ b <= d)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> rw [SUBSET_DEF, IN_INTERVAL] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      CCONTR_TAC >> fs [GSYM real_lt] \\
      (* a < z < b,c < d *)
      MP_TAC (Q.SPECL [‘a’, ‘min b c’] REAL_MEAN) \\
      ASM_REWRITE_TAC [REAL_LT_MIN] \\
      CCONTR_TAC >> fs [] \\
     ‘a <= z /\ z <= b’ by simp [REAL_LT_IMP_LE] \\
     ‘c <= z’ by PROVE_TAC [] \\
      METIS_TAC [REAL_LTE_ANTISYM],
      (* goal 2 (of 4) *)
      CCONTR_TAC >> fs [GSYM real_lt] \\
      (* c < d,a < z < b *)
      MP_TAC (Q.SPECL [‘max d a’, ‘b’] REAL_MEAN) \\
      ASM_REWRITE_TAC [REAL_MAX_LT] \\
      CCONTR_TAC >> fs [] \\
     ‘a <= z /\ z <= b’ by simp [REAL_LT_IMP_LE] \\
     ‘z <= d’ by PROVE_TAC [] \\
      METIS_TAC [REAL_LTE_ANTISYM],
      (* goal 3 (of 4) *)
      Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘a’ >> art [],
      (* goal 3 (of 3) *)
      Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘b’ >> art [] ]
QED

(* cf. right_open_interval_SUBSET *)
Theorem closed_interval_subset :
    !a b c d. a < b /\ c < d /\ interval [a,b] SUBSET interval [c,d] ==>
              b - a <= d - c
Proof
    rpt STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> simp [closed_interval_subset_eq]
 >> REAL_ASM_ARITH_TAC
QED

(* cf. right_open_interval_DISJOINT_EQ *)
Theorem closed_interval_nonoverlapping :
    !a b c d. a < b /\ c < d ==>
             (nonoverlapping (interval [a,b]) (interval [c,d]) <=>
              b <= c \/ d <= a)
Proof
    RW_TAC std_ss [nonoverlapping_def, INTERIOR_INTERVAL]
 >> EQ_TAC >> rw [DISJOINT_ALT, IN_INTERVAL, REAL_NOT_LT] (* 3 subgoals *)
 >| [ (* goal 1 (of 3): a < b <= c < d  or  c < d <= a < b *)
      CCONTR_TAC >> fs [REAL_NOT_LE] \\
      MP_TAC (Q.SPECL [‘max a c’, ‘min b d’] REAL_MEAN) \\
      ASM_REWRITE_TAC [REAL_MAX_LT, REAL_LT_MIN] \\
      CCONTR_TAC >> fs [] \\
     ‘z <= c \/ d <= z’ by PROVE_TAC [] >- METIS_TAC [REAL_LTE_ANTISYM] \\
      METIS_TAC [REAL_LTE_ANTISYM],
      (* goal 2 (of 3) *)
      CCONTR_TAC >> fs [REAL_NOT_LE] \\
      (* a < x < b <= c < x < d *)
     ‘x < c’ by PROVE_TAC [REAL_LTE_TRANS] \\
      METIS_TAC [REAL_LT_ANTISYM],
      (* goal 3 (of 3) *)
      CCONTR_TAC >> fs [REAL_NOT_LE] \\
      (* c < x < d <= a < x < b *)
     ‘x < a’ by PROVE_TAC [REAL_LTE_TRANS] \\
      METIS_TAC [REAL_LT_ANTISYM] ]
QED

Theorem nonoverlapping_comm :
    !s t. nonoverlapping s t <=> nonoverlapping t s
Proof
    RW_TAC std_ss [nonoverlapping_def, Once DISJOINT_SYM]
QED

(* cf. SUBSET_DISJOINT *)
Theorem subset_nonoverlapping :
    !s t u v. nonoverlapping s t /\ u SUBSET s /\ v SUBSET t ==>
              nonoverlapping u v
Proof
    rw [nonoverlapping_def]
 >> MATCH_MP_TAC SUBSET_DISJOINT
 >> qexistsl_tac [‘interior s’, ‘interior t’] >> art []
 >> rw [SUBSET_INTERIOR]
QED

(* cf. right_open_interval_DISJOINT_EQ *)
Theorem closed_interval_disjoint_eq :
    !a b c d. a < b /\ c < d ==>
             (DISJOINT (interval (a,b)) (interval (c,d)) <=> b <= c \/ d <= a)
Proof
    rw [DISJOINT_ALT, IN_INTERVAL]
 >> EQ_TAC >> rpt STRIP_TAC (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      CCONTR_TAC >> fs [REAL_NOT_LE, REAL_NOT_LT] \\
      (* a < c < b < d *)
      MP_TAC (Q.SPECL [‘max a c’, ‘min b d’] REAL_MEAN) \\
      rw [REAL_MAX_LT, REAL_LT_MIN] \\
      CCONTR_TAC >> fs [] (* a < c < z < b < d *) \\
      METIS_TAC [REAL_LET_ANTISYM],
      (* goal 2 (of 3) *)
      CCONTR_TAC >> fs [] \\
     ‘x < c’ by PROVE_TAC [REAL_LTE_TRANS] \\
      METIS_TAC [REAL_LT_ANTISYM],
      (* goal 3 (of 3) *)
      CCONTR_TAC >> fs [] \\
     ‘d < x’ by PROVE_TAC [REAL_LET_TRANS] \\
      METIS_TAC [REAL_LT_ANTISYM] ]
QED

(* NOTE: Here we use the “gauge” definition from the old integralTheory, as it
   avoids “open” sets and directly gives the radius g(x) as a positive real.

   The asserted ‘J’ may contain duplicated elements, i.e. J(i) is finite. This is
   why we used “J i <> J j” instead of “i <> j” in the disjointness conclusion.
 *)
Theorem dyadic_covering_lemma_unit[local] :
    !g E c. gauge UNIV g /\ E <> {} /\ E SUBSET interval [c,c + 1] ==>
            ?J t. (!i. J i SUBSET interval [c,c + 1] /\
                       compact (J i) /\ t i IN E INTER J (i :num) /\
                       E INTER J i SUBSET cball (t i,g (t i))) /\
                  (!i j. J i <> J j ==> nonoverlapping (J i) (J j)) /\
                   E SUBSET BIGUNION (IMAGE J UNIV)
Proof
    rw [integralTheory.gauge, SUBSET_DEF, IN_INTERVAL, IN_CBALL, IN_INTERVAL]
 >> qabbrev_tac ‘f = \k n. interval [c + &n / 2 pow k,c + &SUC n / 2 pow k]’
 >> ‘!x. ?n. 1 / 2 pow n < g x’ by METIS_TAC [lemma4]
 >> FULL_SIMP_TAC std_ss [SKOLEM_THM]
 >> rename1 ‘!x. 1 / 2 pow d x < g x’
 >> Know ‘!x. c <= x /\ x <= c + 1 ==>
              ?k n. n < 2 ** k /\ x IN f k n /\ f k n SUBSET cball (x,g x)’
 >- (RW_TAC std_ss [Abbr ‘f’, SUBSET_DEF, IN_INTERVAL, IN_CBALL] \\
     Q.PAT_X_ASSUM ‘!x. _ < g x’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     qabbrev_tac ‘k = d x’ \\
     MP_TAC (Q.SPECL [‘k’, ‘x’, ‘c’] lemma1c) >> RW_TAC std_ss [] \\
     qexistsl_tac [‘k’, ‘n’] >> art [] \\
     Q.X_GEN_TAC ‘y’ >> RW_TAC std_ss [dist] \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘1 / 2 pow k’ >> art [] \\
     Cases_on ‘0 <= x - y’
     >- (ASM_SIMP_TAC real_ss [ABS_EQ_POS] \\
         Suff ‘x <= 1 / 2 pow k + y’ >- REAL_ARITH_TAC \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘c + &SUC n / 2 pow k’ >> art [] \\
         Suff ‘c + (&SUC n / 2 pow k - 1 / 2 pow k) <= y’ >- REAL_ARITH_TAC \\
         ASM_SIMP_TAC real_ss [REAL_DIV_SUB, ADD1] \\
         simp [GSYM realaxTheory.REAL_OF_NUM_SUB]) \\
     FULL_SIMP_TAC real_ss [GSYM real_lt, ABS_EQ_NEG] \\
     Suff ‘y - 1 / 2 pow k <= x’ >- REAL_ARITH_TAC \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘c + &n / 2 pow k’ >> art [] \\
     Suff ‘y <= c + (&n / 2 pow k + 1 / 2 pow k)’ >- REAL_ARITH_TAC \\
     ASM_SIMP_TAC real_ss [REAL_DIV_ADD, GSYM ADD1])
 >> DISCH_TAC
 (* stage work *)
 >> qabbrev_tac ‘J0 = {s | ?n k. s = f k n /\ n < 2 ** k}’
 >> Know ‘!s1 s2. s1 IN J0 /\ s2 IN J0 /\ s1 <> s2 ==>
                  s1 SUBSET s2 \/ s2 SUBSET s1 \/ nonoverlapping s1 s2’
 >- (rw [Abbr ‘J0’, Abbr ‘f’] \\
     POP_ASSUM MP_TAC >> rename1 ‘m < 2 ** l’ \\
    ‘c + &n / 2 pow k < (c + &SUC n / 2 pow k) :real /\
     c + &m / 2 pow l < (c + &SUC m / 2 pow l) :real’ by simp [] \\
     ASM_SIMP_TAC std_ss [closed_interval_11] \\
     Cases_on ‘k = l’
     >- (simp [] >> DISCH_TAC (* n <> m *) \\
         simp [closed_interval_subset_eq, closed_interval_nonoverlapping]) \\
     NTAC 5 (POP_ASSUM MP_TAC) \\
  (* applying wlog_tac *)
     wlog_tac ‘k <= l’ []
     >- (rpt STRIP_TAC \\
        ‘l <= k /\ l < k’ by simp [] \\
         ONCE_REWRITE_TAC [nonoverlapping_comm] \\
         Q.PAT_X_ASSUM ‘!k l n m. P’ (MP_TAC o Q.SPECL [‘l’, ‘k’, ‘m’, ‘n’]) \\
         METIS_TAC []) \\
     rpt STRIP_TAC \\
    ‘k < l’ by simp [] >> Q.PAT_X_ASSUM ‘k <= l’ K_TAC \\
    ‘?p. p + k = l’ by METIS_TAC [LESS_ADD] \\
     POP_ASSUM (FULL_SIMP_TAC std_ss o wrap o SYM) \\
    ‘(&n / 2 pow k) :real = &(n * 2 ** p) / 2 pow (p + k)’
       by (simp [POW_ADD] >> simp [REAL_OF_NUM_MUL, REAL_POW]) \\
     POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
    ‘(&SUC n / 2 pow k) :real = &(SUC n * 2 ** p) / 2 pow (p + k)’
       by (simp [POW_ADD] >> simp [REAL_OF_NUM_MUL, REAL_POW]) \\
     POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
     qabbrev_tac ‘l = p + k’ \\
     simp [closed_interval_subset_eq, closed_interval_nonoverlapping])
 >> DISCH_TAC
 >> Know ‘countable J0’
 >- (qabbrev_tac ‘t = \k. count (2 ** k)’ \\
     Know ‘J0 = {f x y | x IN univ(:num) /\ y IN t x}’
     >- (rw [Once EXTENSION, Abbr ‘J0’, Abbr ‘t’, IN_COUNT] \\
         METIS_TAC []) >> Rewr' \\
     MATCH_MP_TAC COUNTABLE_PRODUCT_DEPENDENT >> rw [])
 >> DISCH_TAC
 >> Know ‘J0 <> {}’
 >- (rw [Abbr ‘J0’, Once EXTENSION, NOT_IN_EMPTY] \\
     qexistsl_tac [‘0’, ‘0’] >> simp [])
 >> DISCH_TAC
 >> qabbrev_tac ‘J1 = J0 DIFF {s | ~?x k n. x IN E INTER s /\ s = f k n /\
                                            f k n SUBSET cball (x,g x)}’
 >> ‘J1 SUBSET J0’ by rw [SUBSET_DEF, Abbr ‘J1’]
 >> ‘countable J1’ by PROVE_TAC [COUNTABLE_SUBSET]
 >> Know ‘!s. s IN J1 ==> ?x k n. x IN E /\ x IN s /\ s = f k n /\ n < 2 ** k /\
                                  f k n SUBSET cball (x,g x)’
 >- (rw [Abbr ‘J1’, Abbr ‘J0’] \\
     rename1 ‘y IN f l m’ \\
     qexistsl_tac [‘y’, ‘k’, ‘n’] >> rw [] >> gs [])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!x. x IN E ==>
              ?s k n. s IN J1 /\ s = f k n /\ n < 2 ** k /\ x IN f k n /\
                      f k n SUBSET cball (x,g x)’
 >- (rpt (Q.PAT_X_ASSUM ‘countable _’ K_TAC) \\
     rpt (Q.PAT_X_ASSUM ‘_ SUBSET _’  K_TAC) \\
     rw [Abbr ‘J1’, Abbr ‘J0’] \\
     Q.PAT_X_ASSUM ‘!x. c <= x /\ x <= c + 1 ==> ?k n. _’ (MP_TAC o Q.SPEC ‘x’) \\
     RW_TAC std_ss [] \\
     qexistsl_tac [‘k’, ‘n’] >> art [] \\
     CONJ_TAC >- (qexistsl_tac [‘n’, ‘k’] >> art []) \\
     qexistsl_tac [‘x’, ‘k’, ‘n’] >> art [])
 >> DISCH_TAC
 (* “E <> {}” is needed here *)
 >> Know ‘J1 <> {}’
 >- (rw [Once EXTENSION, NOT_IN_EMPTY] \\
    ‘?x. x IN E’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
     METIS_TAC [])
 >> DISCH_TAC
 (* J2 is done by removing smaller sets from J1 *)
 >> qabbrev_tac ‘J2 = J1 DIFF {s | s IN J1 /\ ?t. t IN J1 /\ s PSUBSET t}’
 >> ‘J2 SUBSET J1’ by rw [SUBSET_DEF, Abbr ‘J2’]
 >> ‘countable J2’ by PROVE_TAC [COUNTABLE_SUBSET]
 >> Know ‘J2 <> {}’
 >- (rpt (Q.PAT_X_ASSUM ‘countable _’ K_TAC) \\
     Q.PAT_X_ASSUM ‘J2 SUBSET J1’ K_TAC \\
     rw [Abbr ‘J2’, Once EXTENSION, NOT_IN_EMPTY, PSUBSET_DEF] \\
     SIMP_TAC (bool_ss ++ DNF_ss) [GSYM IMP_DISJ_THM] \\
     qabbrev_tac ‘P = \k. ?x n. n < 2 ** k /\ x IN E INTER f k n /\
                                f k n SUBSET cball (x,g x)’ \\
     MP_TAC (Q.SPEC ‘P’ LEAST_EXISTS_IMP) \\
     qabbrev_tac ‘l = $LEAST P’ (* here “l” means least *) \\
     impl_tac
     >- (simp [Abbr ‘P’] \\
        ‘?s. s IN J1’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
         Q.PAT_X_ASSUM ‘!s. s IN J1 ==> ?x k n. _’ (MP_TAC o Q.SPEC ‘s’) \\
         RW_TAC std_ss [] \\
         qexistsl_tac [‘k’, ‘x’, ‘n’] >> art []) \\
     rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘f l n’ \\
     CONJ_TAC
     >- (rw [Abbr ‘J1’, Abbr ‘J0’]
         >- (qexistsl_tac [‘n’, ‘l’] >> art []) \\
         qexistsl_tac [‘x’, ‘l’, ‘n’] >> art []) \\
     NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!s. s IN J1 ==> _’ (MP_TAC o Q.SPEC ‘t’) >> POP_ORW \\
     RW_TAC std_ss [] >> rename1 ‘y IN f k m’ \\
     Know ‘c + &SUC n / 2 pow l - (c + &n / 2 pow l) :real <=
           c + &SUC m / 2 pow k - (c + &m / 2 pow k)’
     >- (MATCH_MP_TAC closed_interval_subset \\
         REWRITE_TAC [lemma5a] \\
         POP_ASSUM MP_TAC >> simp [Abbr ‘f’]) \\
     simp [lemma6a] \\
     Know ‘2 pow k <= (2 pow l) :real <=> k <= l’
     >- (MATCH_MP_TAC REAL_POW_MONO_EQ >> simp []) >> Rewr' \\
     DISCH_TAC \\
    ‘k = l \/ k < l’ by simp [] (* 2 subgoals *)
     >- (Q.PAT_X_ASSUM ‘f l n SUBSET f k m’ MP_TAC \\
         simp [Abbr ‘f’, closed_interval_subset_eq, lemma5] \\
         simp [LE_ANTISYM]) \\
     METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘!x. x IN E ==> ?s. x IN s /\ s IN J2’
 >- (rpt STRIP_TAC \\
     qabbrev_tac ‘P = \k. ?y n. n < 2 ** k /\
                                x IN E INTER f k n /\
                                y IN E INTER f k n /\
                                f k n SUBSET cball (y,g y)’ \\
  (* NOTE: “$LEAST P” is biggest interval for any y IN E containing also x *)
     MP_TAC (Q.SPEC ‘P’ LEAST_EXISTS_IMP) \\
     qabbrev_tac ‘l = $LEAST P’ \\
     impl_tac
     >- (simp [Abbr ‘P’] \\
         Q.PAT_X_ASSUM ‘!x. x IN E ==> ?s k n. _’ drule >> rw [] \\
         qexistsl_tac [‘k’, ‘x’, ‘n’] >> art []) \\
     rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘f l n’ >> art [] \\
     Q.PAT_X_ASSUM ‘J2 SUBSET J1’ K_TAC \\
     Q.PAT_X_ASSUM ‘countable J2’ K_TAC \\
     Q.PAT_X_ASSUM ‘K2 <> {}’     K_TAC \\
     rw [Abbr ‘J2’]
     >- (rw [Abbr ‘J1’, Abbr ‘J0’]
         >- (qexistsl_tac [‘n’, ‘l’] >> art []) \\
         qexistsl_tac [‘y’, ‘l’, ‘n’] >> art []) \\
     STRONG_DISJ_TAC \\
     RW_TAC std_ss [PSUBSET_DEF, GSYM IMP_DISJ_THM] \\
     Q.PAT_X_ASSUM ‘!s. s IN J1 ==> _’ (MP_TAC o Q.SPEC ‘t’) \\
     RW_TAC std_ss [] >> rename1 ‘z IN f k m’ \\
     Know ‘c + &SUC n / 2 pow l - (c + &n / 2 pow l) :real <=
           c + &SUC m / 2 pow k - (c + &m / 2 pow k)’
     >- (MATCH_MP_TAC closed_interval_subset \\
         REWRITE_TAC [lemma5a] \\
         Q.PAT_X_ASSUM ‘f l n SUBSET f k m’ MP_TAC \\
         simp [Abbr ‘f’]) \\
     simp [lemma6a] \\
     Know ‘2 pow k <= (2 pow l) :real <=> k <= l’
     >- (MATCH_MP_TAC REAL_POW_MONO_EQ >> simp []) >> Rewr' \\
     DISCH_TAC \\
    ‘k = l \/ k < l’ by simp [] (* 2 subgoals *)
     >- (Q.PAT_X_ASSUM ‘f l n SUBSET f k m’ MP_TAC \\
         simp [Abbr ‘f’, closed_interval_subset_eq, lemma5] \\
         simp [LE_ANTISYM]) \\
    ‘x IN f k m’ by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘!s1 s2. s1 IN J2 /\ s2 IN J2 /\ s1 <> s2 ==> ~(s1 SUBSET s2)’
 >- (rw [Abbr ‘J2’, PSUBSET_DEF] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘?J. J2 = IMAGE J univ(:num)’ by METIS_TAC [COUNTABLE_AS_IMAGE]
 >> ‘!i. J i IN J2’ by rw []
 (* stage work *)
 >> Know ‘!i. ?xs. FST xs IN E /\
                   J i = f (FST (SND xs)) (SND (SND xs)) /\
                   SND (SND xs) < 2 ** FST (SND xs) /\ FST xs IN J i /\
                   J i SUBSET cball (FST xs,g (FST xs))’
 >- (Q.X_GEN_TAC ‘i’ \\
    ‘J i IN J1’ by PROVE_TAC [SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘!s. s IN J1 ==> ?x k n. _’ (MP_TAC o Q.SPEC ‘J (i :num)’) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘(x,k,n)’ >> simp [] >> fs [])
 >> simp [SKOLEM_THM]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘ts’ STRIP_ASSUME_TAC)
 >> qexistsl_tac [‘J’, ‘\i. FST (ts i)’]
 (* nonoverlapping *)
 >> Know ‘!i j. J i <> J j ==> nonoverlapping (J i) (J j)’
 >- (POP_ASSUM K_TAC >> rpt STRIP_TAC \\
    ‘J2 SUBSET J0’ by PROVE_TAC [SUBSET_TRANS] \\
    ‘!i. J i IN J0’ by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [])
 >> Rewr
 >> Know ‘!i. compact (J i)’
 >- simp [Abbr ‘f’, COMPACT_INTERVAL]
 >> Rewr
 (* !x. x IN E ==> ?s. x IN s /\ ?x. s = J x *)
 >> reverse CONJ_TAC
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!x. x IN E ==> ?s. x IN s /\ s IN J2’ drule >> rw [])
 (* stage work *)
 >> Q.X_GEN_TAC ‘i’ >> simp []
 >> POP_ASSUM (MP_TAC o Q.SPEC ‘i’)
 >> Cases_on ‘ts i’ >> simp []
 >> PairCases_on ‘r’ >> simp []
 >> rename1 ‘ts i = (y,k,n)’ >> simp []
 >> STRIP_TAC
 >> reverse CONJ_TAC
 >- (CONJ_TAC (* y IN f k n *)
     >- (Q.PAT_X_ASSUM ‘J i = f k n’ (REWRITE_TAC o wrap o SYM) >> art []) \\
     rpt STRIP_TAC \\
     Know ‘x IN cball (y,g y)’ >- METIS_TAC [SUBSET_DEF] \\
     simp [IN_CBALL])
 (* !x. x IN f k n ==> c <= x /\ x <= c + 1 *)
 >> RW_TAC real_ss [Abbr ‘f’, IN_INTERVAL]
 >| [ (* goal 1 (of 2) *)
      Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘c + &n / 2 pow k’ >> art [] \\
      simp [REAL_LE_ADDR],
      (* goal 2 (of 2) *)
      Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘c + &SUC n / 2 pow k’ >> art [] \\
      simp [ADD1, REAL_POW] ]
QED

Theorem UNIT_INTERVAL_PARTITION :
    BIGUNION (IMAGE (\i. interval [real_of_int i, real_of_int i + 1])
                    UNIV) = UNIV
Proof
    rw [Once EXTENSION, IN_BIGUNION_IMAGE, IN_INTERVAL]
 >> Q.EXISTS_TAC ‘INT_FLOOR x’
 >> MP_TAC (Q.SPEC ‘x’ INT_FLOOR_BOUNDS') (* intrealTheory *)
 >> qabbrev_tac ‘r = real_of_int (INT_FLOOR x)’
 >> REAL_ARITH_TAC
QED

(* cf. INFINITE_INT_UNIV *)
Theorem COUNTABLE_INT_UNIV :
    countable univ(:int)
Proof
    Suff ‘univ(:int) = IMAGE int_of_num UNIV UNION IMAGE (\n. -int_of_num n) UNIV’
 >- (Rewr' \\
     MATCH_MP_TAC COUNTABLE_UNION_IMP (* cardinalTheory *) \\
     CONJ_TAC >> MATCH_MP_TAC COUNTABLE_IMAGE >> simp [])
 >> rw [Once EXTENSION]
 >> STRIP_ASSUME_TAC (Q.SPEC ‘x’ int_cases)
 >| [ DISJ1_TAC >> Q.EXISTS_TAC ‘n’ >> art [],
      DISJ2_TAC >> Q.EXISTS_TAC ‘n’ >> art [] ]
QED

(* 18.15 Dyadic Covering Lemma [2, p.311] *)
Theorem dyadic_covering_lemma :
    !g E. gauge UNIV g /\ E <> {} ==>
          ?J t. (!i. compact (J i) /\ t i IN E INTER J (i :num) /\
                     E INTER J i SUBSET cball (t i,g (t i))) /\
                (!i j. J i <> J j ==> nonoverlapping (J i) (J j)) /\
                 E SUBSET BIGUNION (IMAGE J UNIV)
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘e = \i. E INTER interval [real_of_int i,real_of_int i + 1]’
 >> ‘!i. e i SUBSET interval [real_of_int i,real_of_int i + 1]’
      by rw [SUBSET_DEF, Abbr ‘e’, IN_INTERVAL]
 (* applying dyadic_covering_lemma_unit *)
 >> Know ‘!n. e n <> {} ==>
              ?J t. (!i. J i SUBSET interval [real_of_int n,real_of_int n + 1] /\
                         compact (J i) /\
                         t i IN e n INTER J (i :num) /\
                         e n INTER J i SUBSET cball (t i,g (t i))) /\
                    (!i j. J i <> J j ==> nonoverlapping (J i) (J j)) /\
                     e n SUBSET BIGUNION (IMAGE J UNIV)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC dyadic_covering_lemma_unit >> simp [])
 (* This asserts f and f' in place of J and t *)
 >> DISCH_THEN (STRIP_ASSUME_TAC o
                SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])
 >> Know ‘E = BIGUNION (IMAGE e UNIV)’
 >- (simp [Abbr ‘e’, GSYM BIGUNION_OVER_INTER_R] \\
     simp [UNIT_INTERVAL_PARTITION])
 >> DISCH_TAC
 >> Know ‘?n0. e n0 <> {}’
 >- (Suff ‘BIGUNION (IMAGE e univ(:int)) <> {}’
     >- (POP_ASSUM K_TAC \\
         rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         Cases_on ‘x = {}’ >> fs [] \\
         rename1 ‘x = e n0’ \\
         Q.EXISTS_TAC ‘n0’ >> rw []) \\
     POP_ASSUM (art o wrap o SYM))
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘E = _’ (REWRITE_TAC o wrap)
 (* NOTE: Here I want to construct an non-empty countable set holding pairs
    (a,b) which comes from all (f i,f' i) pairs of each non-empty (e' n).
    Then, by COUNTABLE_ENUM or COUNTABLE_AS_IMAGE, the final existence of J/t
    is derived from this countable set.
  *)
 >> qabbrev_tac ‘a = \i. IMAGE (\j. (f i j, f' i j)) UNIV’
 >> qabbrev_tac ‘s = \i. if e i <> {} then a i else {}’
 >> qabbrev_tac ‘c = BIGUNION (IMAGE s UNIV)’
 >> Know ‘c <> {}’
 >- (simp [Abbr ‘c’, Once EXTENSION, IN_BIGUNION_IMAGE, Abbr ‘s’, NOT_IN_EMPTY] \\
     Suff ‘?i. e i <> {}’
     >- (STRIP_TAC \\
         Q.EXISTS_TAC ‘a i’ \\
         Know ‘a i <> {}’ >- rw [Abbr ‘a’, Once EXTENSION, NOT_IN_EMPTY] \\
         rw [] >> Q.EXISTS_TAC ‘i’ >> art []) \\
     Q.EXISTS_TAC ‘n0’ \\
     rw [Abbr ‘e’, Once EXTENSION, NOT_IN_EMPTY] \\
     simp [MEMBER_NOT_EMPTY])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘e n0 <> {}’ K_TAC (* no more needed *)
 >> Know ‘countable c’
 >- (POP_ASSUM K_TAC (* c <> {} *) \\
     qunabbrev_tac ‘c’ \\
     MATCH_MP_TAC COUNTABLE_BIGUNION \\
     CONJ_TAC >- (MATCH_MP_TAC COUNTABLE_IMAGE \\
                  REWRITE_TAC [COUNTABLE_INT_UNIV]) \\
     rw [Abbr ‘s’] \\
     rename1 ‘countable (if e n <> {} then a n else {})’ \\
     Cases_on ‘e n = {}’ >> simp [COUNTABLE_EMPTY, Abbr ‘a’])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!z1 z2. z1 IN c /\ z2 IN c /\ FST z1 <> FST z2 ==>
                  nonoverlapping (FST z1) (FST z2)’
 >- (rw [Abbr ‘c’, Abbr ‘s’, IN_BIGUNION_IMAGE] \\
     rename1 ‘z2 IN if e j <> {} then a j else {}’ \\
     Cases_on ‘e i = {}’ >> fs [] \\
     Cases_on ‘e j = {}’ >> fs [] \\
     Q.PAT_X_ASSUM ‘z2 IN a j’ MP_TAC \\
     Q.PAT_X_ASSUM ‘z1 IN a i’ MP_TAC \\
     Q.PAT_X_ASSUM ‘FST z1 <> FST z2’ MP_TAC \\
     rw [Abbr ‘a’] >> fs [] >> rename1 ‘f i m <> f j n’ \\
     Cases_on ‘i = j’ >- rw [] \\
     Q.PAT_X_ASSUM ‘f i m <> f j n’ K_TAC \\
    ‘f i m SUBSET interval [real_of_int i,real_of_int i + 1] /\
     f j n SUBSET interval [real_of_int j,real_of_int j + 1]’ by rw [] \\
     MATCH_MP_TAC subset_nonoverlapping \\
     qexistsl_tac [‘interval [real_of_int i,real_of_int i + 1]’,
                   ‘interval [real_of_int j,real_of_int j + 1]’] \\
     simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
     simp [closed_interval_disjoint_eq] \\
     SIMP_TAC real_ss [GSYM real_of_int_add, GSYM real_of_int_num] \\
     simp [] \\
     Q.PAT_X_ASSUM ‘i <> j’ MP_TAC >> intLib.ARITH_TAC)
 >> DISCH_TAC
 (* stage work *)
 >> Suff ‘!z. z IN c ==> compact (FST z) /\
                         SND z IN BIGUNION (IMAGE e UNIV) INTER FST z /\
                         BIGUNION (IMAGE e UNIV) INTER FST z SUBSET
                         cball (SND z,g (SND z))’
 >- (DISCH_TAC \\
     MP_TAC (ISPEC “c :(real set # real) set” COUNTABLE_AS_IMAGE) \\
     simp [] >> DISCH_THEN (Q.X_CHOOSE_THEN ‘h’ STRIP_ASSUME_TAC) \\
    ‘!n. h n IN c’ by rw [] \\
     qexistsl_tac [‘FST o h’, ‘SND o h’] >> simp [o_DEF] \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘n’ \\
         Q.PAT_X_ASSUM ‘!z. z IN c ==> _’ (MP_TAC o Q.SPEC ‘h (n :num)’) >> rw []) \\
     simp [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     Q.X_GEN_TAC ‘x’ \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n’ STRIP_ASSUME_TAC) \\
     Cases_on ‘e n = {}’ >- fs [] \\
     Know ‘x IN BIGUNION (IMAGE (f n) UNIV)’ >- METIS_TAC [SUBSET_DEF] \\
     simp [IN_BIGUNION_IMAGE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j’ STRIP_ASSUME_TAC) \\
     Know ‘(f n j,f' n j) IN c’
     >- (Q.PAT_X_ASSUM ‘c = IMAGE h UNIV’ K_TAC \\
         rw [Abbr ‘c’] \\
         Q.EXISTS_TAC ‘s n’ \\
         reverse CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> simp []) \\
         rw [Abbr ‘s’] \\
         rw [Abbr ‘a’] \\
         Q.EXISTS_TAC ‘j’ >> simp []) \\
     Q.PAT_X_ASSUM ‘c = IMAGE h UNIV’ (REWRITE_TAC o wrap) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
     Q.EXISTS_TAC ‘i’ \\
     POP_ASSUM (simp o wrap o SYM))
 (* stage work *)
 >> NTAC 3 (POP_ASSUM K_TAC)
 >> Q.X_GEN_TAC ‘z’
 >> simp [Abbr ‘c’, Abbr ‘s’, IN_BIGUNION_IMAGE, SUBSET_DEF]
 >> STRIP_TAC
 >> Cases_on ‘e i = {}’ >> fs []
 >> Q.PAT_X_ASSUM ‘z IN a i’ MP_TAC
 >> simp [Abbr ‘a’]
 >> STRIP_TAC >> POP_ORW >> simp []
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘!n. e n <> {} ==> _’ (MP_TAC o Q.SPEC ‘i’) >> simp [] \\
     STRIP_TAC \\
     NTAC 2 (POP_ASSUM K_TAC) \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘j’) >> rw [Abbr ‘e’] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> rw [] >> rename1 ‘x IN e n’
 >> Q.PAT_X_ASSUM ‘!n. e n <> {} ==> _’ (MP_TAC o Q.SPEC ‘i’) >> simp []
 >> STRIP_TAC
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> POP_ASSUM (MP_TAC o Q.SPEC ‘j’)
 >> rw [Abbr ‘e’, IN_CBALL, SUBSET_DEF, IN_INTERVAL]
 >> POP_ASSUM MATCH_MP_TAC >> simp [] >> fs []
QED

(* 18.16 Approximation Theorem [2, p.312] *)
Theorem approximation_thm :
    !E e. indicator E integrable_on UNIV /\ 0 < e ==>
          ?J. (!i. compact (J i)) /\
              (!i j. J i <> J j ==> nonoverlapping (J i) (J j)) /\
               E SUBSET BIGUNION (IMAGE J UNIV) /\
               m_lebesgue E <= suminf (m_lebesgue o J) /\
               suminf (m_lebesgue o J) <= m_lebesgue E + e
Proof
    cheat
QED

Theorem pos_fn_integral_fn_seq :
    !m f n. measure_space m /\ f IN Borel_measurable (measurable_space m) ==>
            pos_fn_integral m (fn_seq m f n) = fn_seq_integral m f n
Proof
    RW_TAC std_ss [fn_seq_integral_def, fn_seq_def]
 >> qabbrev_tac ‘s = \n. count (4 ** n)’
 >> qabbrev_tac ‘a = \n k. {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                                f x < (&k + 1) / 2 pow n}’
 >> Know ‘!n i. a n i IN measurable_sets m’
 >- (rw [Abbr ‘a’] \\
    ‘{x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} =
     {x | &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} INTER m_space m’
       by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> DISCH_TAC
 >> qabbrev_tac ‘b = \n. {x | x IN m_space m /\ 2 pow n <= f x}’
 >> Know ‘!i. b i IN measurable_sets m’
 >- (Q.X_GEN_TAC ‘n’ >> simp [Abbr ‘b’] \\
    ‘{x | x IN m_space m /\ 2 pow n <= f x} =
     {x | 2 pow n <= f x} INTER m_space m’ by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> DISCH_TAC
 >> qabbrev_tac ‘c = \n k. (&k / 2 pow n) :extreal’
 >> Know ‘!i k. 0 <= c i k’
 >- (rw [Abbr ‘c’] \\
    ‘2 pow i = Normal (2 pow i)’
      by simp [extreal_of_num_def, extreal_pow_def] >> POP_ORW \\
     MATCH_MP_TAC le_div >> simp [REAL_POW_LT])
 >> DISCH_TAC
 >> qabbrev_tac ‘h = \x. SIGMA (\k. c n k * indicator_fn (a n k) x) (s n)’
 >> Know ‘!x. x IN m_space m ==> 0 <= h x’
 >- (rw [Abbr ‘h’] \\
     irule EXTREAL_SUM_IMAGE_POS >> simp [Abbr ‘s’] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC le_mul >> rw [Abbr ‘c’, INDICATOR_FN_POS])
 >> DISCH_TAC
 >> qabbrev_tac ‘g = \x. 2 pow n * indicator_fn (b n) x’ >> simp []
 >> Know ‘!x. x IN m_space m ==> 0 <= g x’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC le_mul >> simp [pow_pos_le, INDICATOR_FN_POS])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral m (\x. h x + g x) =
          pos_fn_integral m h + pos_fn_integral m g’
 >- (MATCH_MP_TAC pos_fn_integral_add >> art [] \\
     CONJ_TAC (* h IN Borel_measurable (measurable_space m) *)
     >- (MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
         simp [MEASURE_SPACE_SIGMA_ALGEBRA, Abbr ‘h’] \\
         qexistsl_tac [‘\k x. c n k * indicator_fn (a n k) x’, ‘s n’] \\
         simp [Abbr ‘s’] \\
         reverse CONJ_TAC
         >- (rpt GEN_TAC >> STRIP_TAC \\
             MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC le_mul >> simp [INDICATOR_FN_POS]) \\
         rw [Abbr ‘c’] \\
         simp [extreal_of_num_def, extreal_pow_def] \\
        ‘(0 :real) < 2 pow n’ by simp [REAL_POW_LT] \\
        ‘2 pow n <> 0 :real’ by PROVE_TAC [REAL_LT_IMP_NE] \\
         simp [extreal_div_eq] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR \\
         simp [MEASURE_SPACE_SIGMA_ALGEBRA]) \\
  (* g IN Borel_measurable (measurable_space m) *)
     rw [Abbr ‘g’, extreal_of_num_def, extreal_pow_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR \\
     simp [MEASURE_SPACE_SIGMA_ALGEBRA])
 >> Rewr'
 >> Know ‘pos_fn_integral m g = 2 pow n * measure m (b n)’
 >- (simp [Abbr ‘g’, extreal_of_num_def, extreal_pow_def] \\
     MATCH_MP_TAC pos_fn_integral_cmul_indicator \\
     simp [REAL_POW_LE])
 >> Rewr'
 >> qmatch_abbrev_tac ‘x1 + y = x2 + (y :extreal)’
 >> Know ‘y <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     qunabbrev_tac ‘y’ \\
     MATCH_MP_TAC le_mul >> simp [pow_pos_le] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [])
 >> DISCH_TAC
 >> Cases_on ‘y = PosInf’
 >- (POP_ORW \\
     Suff ‘x1 + PosInf = PosInf /\ x2 + PosInf = PosInf’ >- simp [] \\
     Suff ‘x1 <> NegInf /\ x2 <> NegInf’ >- PROVE_TAC [add_infty] \\
     CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       qunabbrev_tac ‘x1’ \\
       MATCH_MP_TAC pos_fn_integral_pos >> art [],
       (* goal 2 (of 2) *)
       qunabbrev_tac ‘x2’ \\
       irule EXTREAL_SUM_IMAGE_POS >> rw [Abbr ‘s’] \\
       MATCH_MP_TAC le_mul >> art [] \\
       MATCH_MP_TAC MEASURE_POSITIVE >> art [] ])
 >> Know ‘x1 + y = x2 + y <=> x1 = x2’
 >- (MATCH_MP_TAC EXTREAL_EQ_RADD >> art [])
 >> Rewr'
 >> qunabbrevl_tac [‘x1’, ‘x2’]
 (* cleanup y and y-assumptions *)
 >> NTAC 2 (POP_ASSUM K_TAC) >> qunabbrev_tac ‘y’
 (* cleanup g and g-assumptions *)
 >> POP_ASSUM K_TAC >> qunabbrev_tac ‘g’
 >> POP_ASSUM K_TAC (* h-assumption *)
 >> qunabbrev_tac ‘h’
 (* re-define another g *)
 >> qabbrev_tac ‘g = \k x. c n k * indicator_fn (a n k) x’ >> simp []
 >> Know ‘!i x. x IN m_space m ==> 0 <= g i x’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC le_mul >> simp [INDICATOR_FN_POS])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘m’, ‘g’, ‘s (n :num)’]
                    (INST_TYPE [beta |-> “:num”] pos_fn_integral_sum))
 >> impl_tac
 >- (simp [Abbr ‘s’] \\
     rw [Abbr ‘g’, Abbr ‘c’, extreal_of_num_def, extreal_pow_def] \\
    ‘(0 :real) < 2 pow n’ by simp [REAL_POW_LT] \\
    ‘2 pow n <> 0 :real’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     simp [extreal_div_eq] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR \\
     simp [MEASURE_SPACE_SIGMA_ALGEBRA])
 >> Rewr'
 >> irule EXTREAL_SUM_IMAGE_EQ
 >> simp [Abbr ‘s’]
 >> reverse CONJ_TAC
 >- (DISJ1_TAC \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     CONJ_TAC >> MATCH_MP_TAC pos_not_neginf
     >- (MATCH_MP_TAC pos_fn_integral_pos >> art []) \\
     MATCH_MP_TAC le_mul >> art [] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [])
 >> rw [Abbr ‘g’]
 >> simp [Abbr ‘c’, extreal_of_num_def, extreal_pow_def]
 >> ‘(0 :real) < 2 pow n’ by simp [REAL_POW_LT]
 >> ‘2 pow n <> 0 :real’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> simp [extreal_div_eq]
 >> MATCH_MP_TAC pos_fn_integral_cmul_indicator >> art []
 >> MATCH_MP_TAC REAL_LE_DIV >> simp [POW_POS]
QED

(* At first we prove it for bounded positive (non-negative) functions *)
Theorem lebesgue_eq_gauge_integral_lemma1[local] :
    !f. f IN borel_measurable borel /\
        pos_fn_integral lborel (Normal o f) <> PosInf /\
       (!x. 0 <= f x) /\ bounded (IMAGE f UNIV) ==>
        pos_fn_integral lborel (Normal o f) = Normal (integral UNIV f)
Proof
    rw [bounded_def]
 >> Know ‘0 <= a’
 >- (CCONTR_TAC >> fs [GSYM real_lt] \\
    ‘0 <= abs (f ARB)’ by simp [ABS_POS] \\
    ‘abs (f ARB) <= a’ by PROVE_TAC [] \\
    ‘0 <= a’ by PROVE_TAC [REAL_LE_TRANS] \\
     METIS_TAC [REAL_LET_ANTISYM])
 >> DISCH_TAC
 >> qabbrev_tac ‘nf = Normal o f’
 >> ‘!x. 0 <= nf x’ by rw [Abbr ‘nf’, o_DEF]
 >> Know ‘nf IN Borel_measurable borel’
 >- (qunabbrev_tac ‘nf’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> MP_TAC (ISPECL [“lborel”, “nf :real -> extreal”] integral_sequence)
 >> impl_tac >- simp [lborel_def, space_lborel]
 >> qabbrev_tac ‘fi = fn_seq lborel nf’
 >> Rewr'
 >> Know ‘f = \x. real (sup (IMAGE (\n. fi n x) UNIV))’
 >- (rw [FUN_EQ_THM, Abbr ‘fi’] \\
     MP_TAC (ISPECL [“lborel”, “nf :real -> extreal”] lemma_fn_seq_sup) \\
     rw [lborel_def, space_lborel] \\
     simp [Abbr ‘nf’, o_DEF, real_normal])
 >> Rewr'
 >> qunabbrev_tac ‘fi’
 >> Know ‘!i. pos_fn_integral lborel (fn_seq lborel nf i) =
              fn_seq_integral lborel nf i’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC pos_fn_integral_fn_seq >> rw [lborel_def])
 >> Rewr'
 >> qabbrev_tac ‘fn = \n x. real (fn_seq lborel nf n x)’
 (* applying sup_normal *)
 >> qabbrev_tac ‘s = \x. IMAGE (\n. fn_seq lborel nf n x) UNIV’ >> simp []
 >> Know ‘!x. sup (s x) = Normal (sup (s x o Normal))’
 >- (rw [Once EQ_SYM_EQ] \\
     MATCH_MP_TAC sup_normal \\
     Q.EXISTS_TAC ‘a’ >> rw [abs_bounds] (* 2 subgoals *)
     >- (rw [Abbr ‘s’, le_sup'] \\
         Q_TAC (TRANS_TAC le_trans) ‘0’ \\
         CONJ_TAC >- simp [extreal_of_num_def, extreal_ainv_def] \\
         Q_TAC (TRANS_TAC le_trans) ‘fn_seq lborel nf 0 x’ \\
         reverse CONJ_TAC
         >- (POP_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘0’ >> art []) \\
         MATCH_MP_TAC lemma_fn_seq_positive >> art []) \\
     rw [Abbr ‘s’, sup_le'] \\
     Q_TAC (TRANS_TAC le_trans) ‘nf x’ \\
     CONJ_TAC >- (MATCH_MP_TAC lemma_fn_seq_upper_bounded >> art []) \\
     rw [Abbr ‘nf’, o_DEF] \\
     Suff ‘abs (f x) <= a’ >- simp [ABS_BOUNDS] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> art [])
 >> Rewr'
 >> simp [real_normal, Abbr ‘s’]
 >> Know ‘!x. IMAGE (\n. fn_seq lborel nf n x) UNIV o Normal =
              IMAGE (\n. fn n x) UNIV’
 >- (Q.X_GEN_TAC ‘y’ >> rw [Once EXTENSION, o_DEF] \\
     EQ_TAC >> rw [Abbr ‘fn’]
     >- (Q.EXISTS_TAC ‘n’ \\
         POP_ASSUM (simp o wrap o SYM)) \\
     Q.EXISTS_TAC ‘n’ \\
     MATCH_MP_TAC normal_real \\
     CONJ_TAC
     >- (MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC lemma_fn_seq_positive >> art []) \\
     REWRITE_TAC [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘nf y’ \\
     CONJ_TAC >- (MATCH_MP_TAC lemma_fn_seq_upper_bounded >> art []) \\
     simp [Abbr ‘nf’, o_DEF])
 >> Rewr'
 (* applying BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING *)
 >> cheat
QED

(* ------------------------------------------------------------------------- *)
(* Non-measurable sets                                                       *)
(* ------------------------------------------------------------------------- *)

open ordinalTheory;

Definition Borel_pointclass_def :
   (additive_class (top :'a topology) (ord :'b ordinal) =
           if ord = 0o then {}
      else if ord = 1o then open_in top
      else COUNTABLE UNION_OF
             (BIGUNION (IMAGE (\i. multiplicative_class top i) (preds ord))))
    /\
   (multiplicative_class (top :'a topology) (ord :'b ordinal) =
           if ord = 0o then {}
      else if ord = 1o then closed_in top
      else COUNTABLE INTERSECTION_OF
             (BIGUNION (IMAGE (\i. additive_class top i) (preds ord)))
           relative_to (topspace top))
Termination
 (* val _ = Defn.tgoal (Hol_defn "Borel_pointclass" Borel_pointclass_def);
    The termination tactics are provided by Michael Norrish:
  *)
    WF_REL_TAC ‘inv_image ordlt (\s. case s of INL (x,a) => a | INR (y,a) => a)’
 >> rw [ordlt_WF]
End

Theorem additive_class_def :
    !(top :'a topology).
       (additive_class top (0o :'b ordinal) = {}) /\
       (additive_class top (1o :'b ordinal) = open_in top) /\
       !ord. 1o < (ord :'b ordinal) ==>
             additive_class top ord =
             COUNTABLE UNION_OF
               (BIGUNION (IMAGE (\i. multiplicative_class top i) (preds ord)))
Proof
    NTAC 2 (rw [Once Borel_pointclass_def])
QED

Theorem multiplicative_class_def :
    !(top :'a topology).
       (multiplicative_class top (0o :'b ordinal) = {}) /\
       (multiplicative_class top (1o :'b ordinal) = closed_in top) /\
       !ord. 1o < (ord :'b ordinal) ==>
             multiplicative_class top ord =
             COUNTABLE INTERSECTION_OF
               (BIGUNION (IMAGE (\i. additive_class top i) (preds ord)))
             relative_to (topspace top)
Proof
    NTAC 2 (rw [Once Borel_pointclass_def])
QED

Definition ambiguous_class_def :
    ambiguous_class (top :'a topology) (ord :'b ordinal) =
      (additive_class top ord) INTER (multiplicative_class top ord)
End

Theorem preds_2[local] :
    preds (2o :'b ordinal) = {0o; 1o}
Proof
    rw [preds_nat]
 >> ‘count 2 = {0; 1}’ by rw [Once EXTENSION]
 >> POP_ORW
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw [] (* 2 subgoals *)
 >| [ Q.EXISTS_TAC ‘0’ >> rw [],
      Q.EXISTS_TAC ‘1’ >> rw [] ]
QED

Theorem additive_class_2 :
    !(top :'a topology). additive_class top (2o :'b ordinal) = fsigma_in top
Proof
    rw [additive_class_def, multiplicative_class_def, fsigma_in, preds_2]
QED

Theorem multiplicative_class_2 :
    !(top :'a topology). multiplicative_class top (2o :'b ordinal) = gdelta_in top
Proof
    rw [additive_class_def, multiplicative_class_def, gdelta_in, preds_2]
QED

Overload gdelta_sigma_in =
  “\top. COUNTABLE UNION_OF (gdelta_in top)”
Overload fsigma_delta_in =
  “\top. COUNTABLE INTERSECTION_OF (fsigma_in top) relative_to (topspace top)”

Theorem preds_3[local] :
    preds (3o :'b ordinal) = {0o; 1o; 2o}
Proof
    rw [preds_nat]
 >> ‘count 3 = {0; 1; 2}’ by rw [Once EXTENSION]
 >> POP_ORW
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw [] (* 3 subgoals *)
 >| [ Q.EXISTS_TAC ‘0’ >> rw [],
      Q.EXISTS_TAC ‘1’ >> rw [],
      Q.EXISTS_TAC ‘2’ >> rw [] ]
QED

Theorem additive_class_3 :
    !(top :'a topology).
        metrizable_space top ==>
        additive_class top (3o :'b ordinal) = gdelta_sigma_in top
Proof
    rw [additive_class_def, multiplicative_class_def, gdelta_in, preds_2, preds_3]
 >> AP_TERM_TAC
 >> rw [GSYM gdelta_in]
 >> Suff ‘closed_in top SUBSET gdelta_in top’ >- SET_TAC []
 >> METIS_TAC [SUBSET_DEF, IN_APP, CLOSED_IMP_GDELTA_IN]
QED

Theorem multiplicative_class_3 :
    !(top :'a topology).
        metrizable_space top ==>
        multiplicative_class top (3o :'b ordinal) = fsigma_delta_in top
Proof
    rw [additive_class_def, multiplicative_class_def, fsigma_in, preds_2, preds_3]
 >> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
      [COUNTABLE_INTERSECTION_OF_RELATIVE_TO]
 >> Suff ‘open_in top UNION countable UNION_OF closed_in top =
          countable UNION_OF closed_in top relative_to topspace top’ >- Rewr
 >> rw [GSYM fsigma_in, FSIGMA_IN_RELATIVE_TO_TOPSPACE]
 >> Suff ‘open_in top SUBSET fsigma_in top’ >- SET_TAC []
 >> METIS_TAC [SUBSET_DEF, IN_APP, OPEN_IMP_FSIGMA_IN]
QED

Theorem additive_class_mono :
    !(top :'a topology). metrizable_space top ==>
        !o1 (o2 :'b ordinal). o1 <= o2 ==>
            additive_class top o1 SUBSET additive_class top o2
Proof
    NTAC 2 STRIP_TAC
 >> Q.X_GEN_TAC ‘o1’
 >> HO_MATCH_MP_TAC ord_induction
 >> rpt STRIP_TAC
 >> cheat
QED

(* ========================================================================= *)
(* Cantor's Ternary Set, see, e.g. [1, p.4,59] and [6]                       *)
(* ========================================================================= *)

(* Recursive construction Cantor Set C(n), a set of reals (C is the generator)

   C(0) = [0,1]

   For each closed interval in C(n), denoted by [a,b], we divide it into three
   parts:

   [a, a+1/3*(b-a)], (a+1/3*(b-a), a+2/3*(b-a)) and [a+2/3*(b-a), b]

   Then C(n+1) contains the 1st and 3rd (closed) intervals.
 *)
Definition Cantor_def :
    Cantor      0  = { interval[0,1] } /\
    Cantor (SUC n) = BIGUNION (IMAGE (\i. let a = interval_lowerbound i;
                                              b = interval_upperbound i in
                                          { interval[a, a + 1 / 3 * (b - a)];
                                            interval[a + 2 / 3 * (b - a), b] })
                              (Cantor n))
End

(* This merges the set of closed intervals in ‘Cantor n’ to single set of reals *)
Definition Cantor_set_def :
    Cantor_set n = BIGUNION (Cantor n)
End

(* The final "Cantor's ternary set" is a BIGINTER of all ‘Cantor_set n’ *)
Definition Cantor_ternary_set_def :
    Cantor_ternary_set = BIGINTER (IMAGE Cantor_set UNIV)
End

Theorem Cantor_interval_lemma[local] :
    a <= b ==> a + 2 / 3 * (b - a) <= (b :real)
Proof
    DISCH_TAC
 >> ONCE_REWRITE_TAC [REAL_ADD_COMM]
 >> REWRITE_TAC [GSYM REAL_LE_SUB_LADD]
 >> ‘0 <= b - a’ by PROVE_TAC [REAL_SUB_LE]
 >> Q.ABBREV_TAC ‘c = b - a’
 >> Suff ‘2 / 3 * c <= 1 * c’ >- rw []
 >> MATCH_MP_TAC REAL_LE_RMUL_IMP >> RW_TAC real_ss []
QED

Theorem Cantor_closed_intervals[local] :
    !n s. s IN Cantor n ==> ?a b. a <= b /\ s = interval[a,b]
Proof
    Induct_on ‘n’
 >- (rw [Cantor_def] \\
     qexistsl_tac [‘0’, ‘1’] >> RW_TAC real_ss [])
 >> rw [Cantor_def]
 >> Q.PAT_X_ASSUM ‘!s. s IN Cantor n ==> P’ (MP_TAC o (Q.SPEC ‘i’))
 >> RW_TAC std_ss [] (* this asserts a and b *)
 >> fs [INTERVAL_LOWERBOUND, INTERVAL_UPPERBOUND] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      qexistsl_tac [‘a’, ‘a + 1 / 3 * (b - a)’] \\
      simp [REAL_SUB_LE],
      (* goal 2 (of 2) *)
      qexistsl_tac [‘a + 2 / 3 * (b - a)’, ‘b’] >> simp [] \\
      MATCH_MP_TAC Cantor_interval_lemma >> art [] ]
QED

Theorem Cantor_itself_not_empty[local]:
    !n. Cantor n <> EMPTY
Proof
    Induct_on ‘n’
 >- rw [GSYM MEMBER_NOT_EMPTY, Cantor_def]
 >> fs [GSYM MEMBER_NOT_EMPTY, Cantor_def]
 >> rename1 ‘i IN Cantor n’
 >> Q.ABBREV_TAC
   ‘s = {interval [interval_lowerbound i,
                   interval_lowerbound i +
                   1 / 3 * (interval_upperbound i - interval_lowerbound i)];
         interval [interval_lowerbound i +
                   2 / 3 * (interval_upperbound i - interval_lowerbound i),
                   interval_upperbound i]}’
 >> qexistsl_tac [‘CHOICE s’, ‘s’]
 >> CONJ_TAC
 >- (MATCH_MP_TAC CHOICE_DEF \\
     rw [GSYM MEMBER_NOT_EMPTY, Abbr ‘s’] \\
     METIS_TAC [])
 >> Q.EXISTS_TAC ‘i’ >> METIS_TAC []
QED

Theorem Cantor_elements_not_empty[local] :
    !n s. s IN Cantor n ==> s <> EMPTY
Proof
    Induct_on ‘n’
 >- rw [Cantor_def, INTERVAL_NE_EMPTY]
 >> rw [Cantor_def, INTERVAL_NE_EMPTY]
 >> ‘?a b. a <= b /\ i = CLOSED_interval[a,b]’
      by METIS_TAC [Cantor_closed_intervals]
 >> fs [INTERVAL_LOWERBOUND, INTERVAL_UPPERBOUND, INTERVAL_NE_EMPTY, REAL_SUB_LE]
 >> MATCH_MP_TAC Cantor_interval_lemma >> art []
QED

Theorem Cantor_set_not_empty :
    !n. Cantor_set n <> EMPTY
Proof
    rw [Cantor_set_def, GSYM MEMBER_NOT_EMPTY]
 >> ‘?s. s IN Cantor n’ by METIS_TAC [Cantor_itself_not_empty, MEMBER_NOT_EMPTY]
 >> ‘?x. x IN s’ by METIS_TAC [Cantor_elements_not_empty, MEMBER_NOT_EMPTY]
 >> qexistsl_tac [‘x’, ‘s’] >> art []
QED

Theorem Cantor_set_decreasing :
    !i j. i <= j ==> Cantor_set j SUBSET Cantor_set i
Proof
    rpt GEN_TAC
 >> Suff ‘!i j. i < j ==> Cantor_set j SUBSET Cantor_set i’
 >- (rpt STRIP_TAC \\
    ‘i = j \/ i < j’ by rw [] >> rw [SUBSET_REFL])
 >> HO_MATCH_MP_TAC TRANSITIVE_STEPWISE_LT (* real_topologyTheory *)
 >> rpt STRIP_TAC >- METIS_TAC [SUBSET_TRANS]
 >> rename1 ‘Cantor_set (SUC n) SUBSET Cantor_set n’
 >> REWRITE_TAC [Cantor_set_def, Once Cantor_def]
 >> rw [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_BIGUNION]
 (* 2 subgoals, same initial tactics *)
 >> Q.EXISTS_TAC ‘i’ >> art []
 >> ‘?a b. a <= b /\ i = CLOSED_interval[a,b]’
      by METIS_TAC [Cantor_closed_intervals]
 >> fs [INTERVAL_LOWERBOUND, INTERVAL_UPPERBOUND, INTERVAL_NE_EMPTY, REAL_SUB_LE]
 >| [ (* goal 1 (of 2) *)
      Suff ‘interval[a,a + 1 / 3 * (b - a)] SUBSET interval[a,b]’
      >- rw [SUBSET_DEF] \\
      rw [SUBSET_INTERVAL] \\
      ONCE_REWRITE_TAC [REAL_ADD_COMM] \\
      REWRITE_TAC [GSYM REAL_LE_SUB_LADD] \\
      Q.ABBREV_TAC ‘c = b - a’ \\
      Suff ‘1 / 3 * c <= 1 * c’ >- rw [] \\
      MATCH_MP_TAC REAL_LE_RMUL_IMP >> RW_TAC real_ss [],
      (* goal 2 (of 2) *)
      Suff ‘interval[a + 2 / 3 * (b - a),b] SUBSET interval[a,b]’
      >- rw [SUBSET_DEF] \\
      rw [SUBSET_INTERVAL, REAL_SUB_LE] ]
QED

Theorem Cantor_set_bounded :
    !n. Cantor_set n SUBSET interval[0,1]
Proof
    Induct_on ‘n’
 >- rw [Cantor_set_def, Cantor_def]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘Cantor_set n’ >> art []
 >> MATCH_MP_TAC Cantor_set_decreasing >> rw []
QED

(* The explicit closed formulas for the Cantor set [6] *)
Theorem Cantor_ternary_set_explicit :
    Cantor_ternary_set =
    interval[0,1] DIFF
    BIGUNION (IMAGE (\n. BIGUNION (IMAGE (\k. interval((3 * &k + 1) / 3 pow SUC n,
                                                       (3 * &k + 2) / 3 pow SUC n))
                                         (count (3 ** n)))) UNIV)
Proof
 (* applying GEN_COMPL_BIGUNION_IMAGE *)
    Q.ABBREV_TAC ‘sp = interval [0,1]’
 >> Q.ABBREV_TAC
   ‘g = \n k. interval ((3 * &k + 1) / 3 pow SUC n,(3 * &k + 2) / 3 pow SUC n)’
 >> simp []
 >> Q.ABBREV_TAC ‘f = \n. BIGUNION (IMAGE (\k. g n k) (count (3 ** n)))’
 >> Know ‘sp DIFF BIGUNION (IMAGE f univ(:num)) =
          BIGINTER (IMAGE (\n. sp DIFF f n) univ(:num))’
 >- (MATCH_MP_TAC GEN_COMPL_BIGUNION_IMAGE \\
     rw [Abbr ‘f’, SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     POP_ASSUM MP_TAC \\
     Suff ‘g n k SUBSET sp’ >- rw [SUBSET_DEF] \\
     rw [SUBSET_INTERVAL, Abbr ‘sp’, Abbr ‘g’] \\
     REWRITE_TAC [pow, GSYM REAL_ADD, GSYM REAL_MUL] \\
    ‘3 * &k + (2 :real) = 3 * (&k + 2 / 3)’ by REAL_ARITH_TAC >> POP_ORW \\
     MATCH_MP_TAC REAL_LE_LMUL_IMP >> rw [] \\
    ‘k + 1 <= 3 ** n’ by rw [] \\
     MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC ‘&k + 1’ \\
     reverse CONJ_TAC >- rw [REAL_OF_NUM_POW] \\
     rw [REAL_LE_LADD])
 >> Rewr'
 (* applying GEN_COMPL_FINITE_UNION *)
 >> simp [Abbr ‘f’]
 >> Know ‘!n. sp DIFF BIGUNION (IMAGE (\k. g n k) (count (3 ** n))) =
              BIGINTER (IMAGE (\i. sp DIFF (\k. g n k) i) (count (3 ** n)))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC GEN_COMPL_FINITE_UNION >> rw [])
 >> Rewr'
 >> cheat
QED

val _ = export_theory ();
val _ = html_theory "lebesgue_measure";

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Bartle, R.G.: A Modern Theory of Integration. American Mathematical Soc. (2001).
  [3] Srivastava, S.M.: A Course on Borel Sets. Springer, Berlin, Heidelberg (1998).
  [4] Kechris, A.S.: Classical Descriptive Set Theory. Springer-Verlag, New York (1995).
  [5] Wikipedia: https://en.wikipedia.org/wiki/Henri_Lebesgue
  [6] Wikipedia: https://en.wikipedia.org/wiki/Cantor_set
  [7] Swartz, C.W., Kurtz, D.S.: Theories Of Integration: The Integrals Of Riemann,
      Lebesgue, Henstock-kurzweil, And Mcshane (2nd Edition).
      World Scientific Publishing Company (2011).
 *)
