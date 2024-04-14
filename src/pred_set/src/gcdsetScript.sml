open HolKernel Parse boolLib BasicProvers

open arithmeticTheory dividesTheory pred_setTheory
open gcdTheory simpLib metisLib

local open TotalDefn numSimps in end;

val ARITH_ss = numSimps.ARITH_ss
val zDefine =
   Lib.with_flag (computeLib.auto_import_definitions, false) TotalDefn.Define

fun DECIDE_TAC (g as (asl,_)) =
  ((MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith asl) THEN
    CONV_TAC Arith.ARITH_CONV)
   ORELSE tautLib.TAUT_TAC) g;

val decide_tac = DECIDE_TAC;
val metis_tac = METIS_TAC;
val rw = SRW_TAC [ARITH_ss];

val _ = new_theory "gcdset"

val gcdset_def = new_definition(
  "gcdset_def",
  ``gcdset s =
      if (s = {}) \/ (s = {0}) then 0
      else MAX_SET ({ n | n <= MIN_SET (s DELETE 0) } INTER
                    { d | !e. e IN s ==> divides d e })``);

val FINITE_LEQ_MIN_SET = prove(
  ``FINITE { n | n <= MIN_SET (s DELETE 0) }``,
  Q_TAC SUFF_TAC `
    { n | n <= MIN_SET (s DELETE 0) } = count (MIN_SET (s DELETE 0) + 1)
  ` THEN1 SRW_TAC [][] THEN
  SRW_TAC [ARITH_ss][EXTENSION]);

val NON_EMPTY_INTERSECTION = prove(
  ``s <> {} /\ s <> {0} ==>
    { n | n <= MIN_SET (s DELETE 0) } INTER
    { d | !e. e IN s ==> divides d e}  <> {}``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [EXTENSION] THEN Q.EXISTS_TAC `1` THEN
  SRW_TAC [][] THEN DEEP_INTRO_TAC MIN_SET_ELIM THEN
  SRW_TAC [ARITH_ss][EXTENSION] THEN
  FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []);

val gcdset_divides = store_thm(
  "gcdset_divides",
  ``!e. e IN s ==> divides (gcdset s) e``,
  SRW_TAC[][gcdset_def] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  DEEP_INTRO_TAC MAX_SET_ELIM THEN
  ASM_SIMP_TAC (srw_ss()) [FINITE_INTER, FINITE_LEQ_MIN_SET,
                           NON_EMPTY_INTERSECTION]);

val DECIDE = numLib.ARITH_PROVE
val gcdset_greatest = store_thm(
  "gcdset_greatest",
  ``(!e. e IN s ==> divides g e) ==> divides g (gcdset s)``,
  SRW_TAC [][gcdset_def] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  DEEP_INTRO_TAC MAX_SET_ELIM THEN
  ASM_SIMP_TAC (srw_ss()) [NON_EMPTY_INTERSECTION, FINITE_LEQ_MIN_SET] THEN
  Q.X_GEN_TAC `m` THEN REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `L = lcm g m` THEN
  `(!e. e IN s ==> divides L e) /\ divides m L /\ divides g L`
    by METIS_TAC [gcdTheory.LCM_IS_LEAST_COMMON_MULTIPLE] THEN
  `?x. x IN s /\ x <> 0`
    by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []) THEN
  `L <= MIN_SET (s DELETE 0)`
    by (DEEP_INTRO_TAC MIN_SET_ELIM THEN SRW_TAC [][EXTENSION]
          THEN1 METIS_TAC [] THEN
        METIS_TAC [DIVIDES_LE, DECIDE ``x <> 0 <=> 0 < x``]) THEN
  `L <= m` by METIS_TAC[] THEN
  Q_TAC SUFF_TAC `0 < m /\ 0 < g` THEN1
    METIS_TAC [LCM_LE, DECIDE ``x <= y /\ y <= x ==> (x = y)``] THEN
  METIS_TAC [ZERO_DIVIDES, DECIDE ``x <> 0 <=> 0 < x``]);

val gcdset_EMPTY = store_thm(
  "gcdset_EMPTY",
  ``gcdset {} = 0``,
  SRW_TAC [][gcdset_def]);
val _ = export_rewrites ["gcdset_EMPTY"]

val gcdset_INSERT = store_thm(
  "gcdset_INSERT",
  ``gcdset (x INSERT s) = gcd x (gcdset s)``,
  Q.MATCH_ABBREV_TAC `G1 = G2` THEN
  `(!e. e IN s ==> divides G1 e) /\ divides G1 x`
     by METIS_TAC [IN_INSERT, gcdset_divides] THEN
  `divides G2 x /\ divides G2 (gcdset s)`
     by METIS_TAC [GCD_IS_GCD, is_gcd_def] THEN
  MATCH_MP_TAC DIVIDES_ANTISYM THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `divides G1 (gcdset s)` THEN1
       METIS_TAC [GCD_IS_GCD, is_gcd_def] THEN
    SRW_TAC [][gcdset_greatest],
    Q_TAC SUFF_TAC `!e. e IN s ==> divides G2 e` THEN1
       METIS_TAC [IN_INSERT, gcdset_greatest] THEN
    METIS_TAC [gcdset_divides, DIVIDES_TRANS]
  ]);
val _ = export_rewrites ["gcdset_INSERT"]

(* ------------------------------------------------------------------------- *)
(* Naturals -- counting from 1 rather than 0, and inclusive.                 *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of natural numbers (like count) *)
val _ = overload_on("natural", ``\n. IMAGE SUC (count n)``);

(* Theorem: j IN (natural n) <=> 0 < j /\ j <= n *)
(* Proof:
   Note j <> 0                     by natural_not_0
       j IN (natural n)
   ==> j IN IMAGE SUC (count n)    by notation
   ==> ?x. x < n /\ (j = SUC x)    by IN_IMAGE
   Since SUC x <> 0                by numTheory.NOT_SUC
   Hence j <> 0,
     and x  < n ==> SUC x < SUC n  by LESS_MONO_EQ
      or j < SUC n                 by above, j = SUC x
    thus j <= n                    by prim_recTheory.LESS_THM
*)
val natural_element = store_thm(
  "natural_element",
  ``!n j. j IN (natural n) <=> 0 < j /\ j <= n``,
  rw[EQ_IMP_THM] >>
  `j <> 0` by decide_tac >>
  `?m. j = SUC m` by metis_tac[num_CASES] >>
  `m < n` by decide_tac >>
  metis_tac[]);

(* Theorem: natural n = {j| 0 < j /\ j <= n} *)
(* Proof: by natural_element, IN_IMAGE *)
val natural_property = store_thm(
  "natural_property",
  ``!n. natural n = {j| 0 < j /\ j <= n}``,
  rw[EXTENSION, natural_element]);

(* Theorem: FINITE (natural n) *)
(* Proof: FINITE_COUNT, IMAGE_FINITE *)
val natural_finite = store_thm(
  "natural_finite",
  ``!n. FINITE (natural n)``,
  rw[]);

(* Theorem: CARD (natural n) = n *)
(* Proof:
     CARD (natural n)
   = CARD (IMAGE SUC (count n))  by notation
   = CARD (count n)              by CARD_IMAGE_SUC
   = n                           by CARD_COUNT
*)
val natural_card = store_thm(
  "natural_card",
  ``!n. CARD (natural n) = n``,
  rw[CARD_IMAGE_SUC]);

(* Theorem: 0 NOTIN (natural n) *)
(* Proof: by NOT_SUC *)
val natural_not_0 = store_thm(
  "natural_not_0",
  ``!n. 0 NOTIN (natural n)``,
  rw[]);

(* Theorem: natural 0 = {} *)
(* Proof:
     natural 0
   = IMAGE SUC (count 0)    by notation
   = IMAGE SUC {}           by COUNT_ZERO
   = {}                     by IMAGE_EMPTY
*)
val natural_0 = store_thm(
  "natural_0",
  ``natural 0 = {}``,
  rw[]);

(* Theorem: natural 1 = {1} *)
(* Proof:
     natural 1
   = IMAGE SUC (count 1)    by notation
   = IMAGE SUC {0}          by count_add1
   = {SUC 0}                by IMAGE_DEF
   = {1}                    by ONE
*)
val natural_1 = store_thm(
  "natural_1",
  ``natural 1 = {1}``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: 0 < n ==> 1 IN (natural n) *)
(* Proof: by natural_element, LESS_OR, ONE *)
val natural_has_1 = store_thm(
  "natural_has_1",
  ``!n. 0 < n ==> 1 IN (natural n)``,
  rw[natural_element]);

(* Theorem: 0 < n ==> n IN (natural n) *)
(* Proof: by natural_element *)
val natural_has_last = store_thm(
  "natural_has_last",
  ``!n. 0 < n ==> n IN (natural n)``,
  rw[natural_element]);

(* Theorem: natural (SUC n) = (SUC n) INSERT (natural n) *)
(* Proof:
       natural (SUC n)
   <=> {j | 0 < j /\ j <= (SUC n)}              by natural_property
   <=> {j | 0 < j /\ (j <= n \/ (j = SUC n))}   by LE
   <=> {j | j IN (natural n) \/ (j = SUC n)}    by natural_property
   <=> (SUC n) INSERT (natural n)               by INSERT_DEF
*)
val natural_suc = store_thm(
  "natural_suc",
  ``!n. natural (SUC n) = (SUC n) INSERT (natural n)``,
  rw[EXTENSION, EQ_IMP_THM]);

val _ = export_theory()
