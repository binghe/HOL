(* ------------------------------------------------------------------------- *)
(* Elementary Number Theory - a collection of useful results for Numbers     *)
(*                                                                           *)
(* Author: Hing-Lun Chan (Australian National University, 2019)              *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib Parse bossLib;

open prim_recTheory arithmeticTheory dividesTheory gcdTheory gcdsetTheory
     pred_setTheory;

val _ = new_theory "number";

(* ------------------------------------------------------------------------- *)
(* Set of Proper Subsets (from examples/algebra)                             *)
(* ------------------------------------------------------------------------- *)

(* Define the set of all proper subsets of a set *)
val _ = overload_on ("PPOW", ``\s. (POW s) DIFF {s}``);

(* Theorem: !s e. e IN PPOW s ==> e PSUBSET s *)
(* Proof:
     e IN PPOW s
   = e IN ((POW s) DIFF {s})       by notation
   = (e IN POW s) /\ e NOTIN {s}   by IN_DIFF
   = (e SUBSET s) /\ e NOTIN {s}   by IN_POW
   = (e SUBSET s) /\ e <> s        by IN_SING
   = e PSUBSET s                   by PSUBSET_DEF
*)
val IN_PPOW = store_thm(
  "IN_PPOW",
  ``!s e. e IN PPOW s ==> e PSUBSET s``,
  rw[PSUBSET_DEF, IN_POW]);

(* Theorem: FINITE (PPOW s) *)
(* Proof:
   Since PPOW s = (POW s) DIFF {s},
       FINITE s
   ==> FINITE (POW s)     by FINITE_POW
   ==> FINITE ((POW s) DIFF {s})  by FINITE_DIFF
   ==> FINITE (PPOW s)            by above
*)
val FINITE_PPOW = store_thm(
  "FINITE_PPOW",
  ``!s. FINITE s ==> FINITE (PPOW s)``,
  rw[FINITE_POW]);

(* Theorem: FINITE s ==> CARD (PPOW s) = PRE (2 ** CARD s) *)
(* Proof:
     CARD (PPOW s)
   = CARD ((POW s) DIFF {s})      by notation
   = CARD (POW s) - CARD ((POW s) INTER {s})   by CARD_DIFF
   = CARD (POW s) - CARD {s}      by INTER_SING, since s IN POW s
   = 2 ** CARD s  - CARD {s}      by CARD_POW
   = 2 ** CARD s  - 1             by CARD_SING
   = PRE (2 ** CARD s)            by PRE_SUB1
*)
val CARD_PPOW = store_thm(
  "CARD_PPOW",
  ``!s. FINITE s ==> (CARD (PPOW s) = PRE (2 ** CARD s))``,
  rpt strip_tac >>
  `FINITE {s}` by rw[FINITE_SING] >>
  `FINITE (POW s)` by rw[FINITE_POW] >>
  `s IN (POW s)` by rw[IN_POW, SUBSET_REFL] >>
  `CARD (PPOW s) = CARD (POW s) - CARD ((POW s) INTER {s})` by rw[CARD_DIFF] >>
  `_ = CARD (POW s) - CARD {s}` by rw[INTER_SING] >>
  `_ = 2 ** CARD s  - CARD {s}` by rw[CARD_POW] >>
  `_ = 2 ** CARD s  - 1` by rw[CARD_SING] >>
  `_ = PRE (2 ** CARD s)` by rw[PRE_SUB1] >>
  rw[]);

(* Theorem: FINITE s ==> CARD (PPOW s) = PRE (2 ** CARD s) *)
(* Proof: by CARD_PPOW *)
val CARD_PPOW_EQN = store_thm(
  "CARD_PPOW_EQN",
  ``!s. FINITE s ==> (CARD (PPOW s) = (2 ** CARD s) - 1)``,
  rw[CARD_PPOW]);

(* ------------------------------------------------------------------------- *)
(* Arithmetic Theorems (from examples/algebra)                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 3 = SUC 2 *)
(* Proof: by arithmetic *)
val THREE = store_thm(
  "THREE",
  ``3 = SUC 2``,
  decide_tac);

(* Theorem: 4 = SUC 3 *)
(* Proof: by arithmetic *)
val FOUR = store_thm(
  "FOUR",
  ``4 = SUC 3``,
  decide_tac);

(* Theorem: 5 = SUC 4 *)
(* Proof: by arithmetic *)
val FIVE = store_thm(
  "FIVE",
  ``5 = SUC 4``,
  decide_tac);

(* Overload squaring *)
val _ = overload_on("SQ", ``\n. n * n``); (* not n ** 2 *)

(* Overload half of a number *)
val _ = overload_on("HALF", ``\n. n DIV 2``);

(* Overload twice of a number *)
val _ = overload_on("TWICE", ``\n. 2 * n``);

(* make divides infix *)
val _ = set_fixity "divides" (Infixl 480); (* relation is 450, +/- is 500, * is 600. *)

(* Theorem alias *)
Theorem ZERO_LE_ALL = arithmeticTheory.ZERO_LESS_EQ;
(* val ZERO_LE_ALL = |- !n. 0 <= n: thm *)

(* Extract theorem *)
Theorem ONE_NOT_0  = DECIDE``1 <> 0``;
(* val ONE_NOT_0 = |- 1 <> 0: thm *)

(* Theorem: !n. 1 < n ==> 0 < n *)
(* Proof: by arithmetic. *)
val ONE_LT_POS = store_thm(
  "ONE_LT_POS",
  ``!n. 1 < n ==> 0 < n``,
  decide_tac);

(* Theorem: !n. 1 < n ==> n <> 0 *)
(* Proof: by arithmetic. *)
val ONE_LT_NONZERO = store_thm(
  "ONE_LT_NONZERO",
  ``!n. 1 < n ==> n <> 0``,
  decide_tac);

(* Theorem: ~(1 < n) <=> (n = 0) \/ (n = 1) *)
(* Proof: by arithmetic. *)
val NOT_LT_ONE = store_thm(
  "NOT_LT_ONE",
  ``!n. ~(1 < n) <=> (n = 0) \/ (n = 1)``,
  decide_tac);

(* Theorem: n <> 0 <=> 1 <= n *)
(* Proof: by arithmetic. *)
val NOT_ZERO_GE_ONE = store_thm(
  "NOT_ZERO_GE_ONE",
  ``!n. n <> 0 <=> 1 <= n``,
  decide_tac);

(* Theorem: n <= 1 <=> (n = 0) \/ (n = 1) *)
(* Proof: by arithmetic *)
val LE_ONE = store_thm(
  "LE_ONE",
  ``!n. n <= 1 <=> (n = 0) \/ (n = 1)``,
  decide_tac);

(* arithmeticTheory.LESS_EQ_SUC_REFL |- !m. m <= SUC m *)

(* Theorem: n < SUC n *)
(* Proof: by arithmetic. *)
val LESS_SUC = store_thm(
  "LESS_SUC",
  ``!n. n < SUC n``,
  decide_tac);

(* Theorem: 0 < n ==> PRE n < n *)
(* Proof: by arithmetic. *)
val PRE_LESS = store_thm(
  "PRE_LESS",
  ``!n. 0 < n ==> PRE n < n``,
  decide_tac);

(* Theorem: 0 < n ==> ?m. n = SUC m *)
(* Proof: by NOT_ZERO_LT_ZERO, num_CASES. *)
val SUC_EXISTS = store_thm(
  "SUC_EXISTS",
  ``!n. 0 < n ==> ?m. n = SUC m``,
  metis_tac[NOT_ZERO_LT_ZERO, num_CASES]);


(* Theorem: 1 <> 0 *)
(* Proof: by ONE, SUC_ID *)
val ONE_NOT_ZERO = store_thm(
  "ONE_NOT_ZERO",
  ``1 <> 0``,
  decide_tac);

(* Theorem: (SUC m) + (SUC n) = m + n + 2 *)
(* Proof:
     (SUC m) + (SUC n)
   = (m + 1) + (n + 1)     by ADD1
   = m + n + 2             by arithmetic
*)
val SUC_ADD_SUC = store_thm(
  "SUC_ADD_SUC",
  ``!m n. (SUC m) + (SUC n) = m + n + 2``,
  decide_tac);

(* Theorem: (SUC m) * (SUC n) = m * n + m + n + 1 *)
(* Proof:
     (SUC m) * (SUC n)
   = SUC m + (SUC m) * n   by MULT_SUC
   = SUC m + n * (SUC m)   by MULT_COMM
   = SUC m + (n + n * m)   by MULT_SUC
   = m * n + m + n + 1     by arithmetic
*)
val SUC_MULT_SUC = store_thm(
  "SUC_MULT_SUC",
  ``!m n. (SUC m) * (SUC n) = m * n + m + n + 1``,
  rw[MULT_SUC]);

(* Theorem: (SUC m = SUC n) <=> (m = n) *)
(* Proof: by prim_recTheory.INV_SUC_EQ *)
val SUC_EQ = store_thm(
  "SUC_EQ",
  ``!m n. (SUC m = SUC n) <=> (m = n)``,
  rw[]);

(* Theorem: (TWICE n = 0) <=> (n = 0) *)
(* Proof: MULT_EQ_0 *)
val TWICE_EQ_0 = store_thm(
  "TWICE_EQ_0",
  ``!n. (TWICE n = 0) <=> (n = 0)``,
  rw[]);

(* Theorem: (SQ n = 0) <=> (n = 0) *)
(* Proof: MULT_EQ_0 *)
val SQ_EQ_0 = store_thm(
  "SQ_EQ_0",
  ``!n. (SQ n = 0) <=> (n = 0)``,
  rw[]);

(* Theorem: (SQ n = 1) <=> (n = 1) *)
(* Proof: MULT_EQ_1 *)
val SQ_EQ_1 = store_thm(
  "SQ_EQ_1",
  ``!n. (SQ n = 1) <=> (n = 1)``,
  rw[]);

(* Theorem: (x * y * z = 0) <=> ((x = 0) \/ (y = 0) \/ (z = 0)) *)
(* Proof: by MULT_EQ_0 *)
val MULT3_EQ_0 = store_thm(
  "MULT3_EQ_0",
  ``!x y z. (x * y * z = 0) <=> ((x = 0) \/ (y = 0) \/ (z = 0))``,
  metis_tac[MULT_EQ_0]);

(* Theorem: (x * y * z = 1) <=> ((x = 1) /\ (y = 1) /\ (z = 1)) *)
(* Proof: by MULT_EQ_1 *)
val MULT3_EQ_1 = store_thm(
  "MULT3_EQ_1",
  ``!x y z. (x * y * z = 1) <=> ((x = 1) /\ (y = 1) /\ (z = 1))``,
  metis_tac[MULT_EQ_1]);

(* Theorem: 0 ** 2 = 0 *)
(* Proof: by ZERO_EXP *)
Theorem SQ_0:
  0 ** 2 = 0
Proof
  simp[]
QED

(* Theorem: (n ** 2 = 0) <=> (n = 0) *)
(* Proof: by EXP_2, MULT_EQ_0 *)
Theorem EXP_2_EQ_0:
  !n. (n ** 2 = 0) <=> (n = 0)
Proof
  simp[]
QED

(* LE_MULT_LCANCEL |- !m n p. m * n <= m * p <=> m = 0 \/ n <= p *)

(* Theorem: n <= p ==> m * n <= m * p *)
(* Proof:
   If m = 0, this is trivial.
   If m <> 0, this is true by LE_MULT_LCANCEL.
*)
Theorem LE_MULT_LCANCEL_IMP:
  !m n p. n <= p ==> m * n <= m * p
Proof
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Maximum and minimum                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MAX m n = if m <= n then n else m *)
(* Proof: by MAX_DEF *)
val MAX_ALT = store_thm(
  "MAX_ALT",
  ``!m n. MAX m n = if m <= n then n else m``,
  rw[MAX_DEF]);

(* Theorem: MIN m n = if m <= n then m else n *)
(* Proof: by MIN_DEF *)
val MIN_ALT = store_thm(
  "MIN_ALT",
  ``!m n. MIN m n = if m <= n then m else n``,
  rw[MIN_DEF]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==> !x y. f (MAX x y) = MAX (f x) (f y) *)
(* Proof: by MAX_DEF *)
val MAX_SWAP = store_thm(
  "MAX_SWAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MAX x y) = MAX (f x) (f y)``,
  rw[MAX_DEF] >>
  Cases_on `x < y` >| [
    `f x <= f y` by rw[] >>
    Cases_on `f x = f y` >-
    rw[] >>
    rw[],
    `y <= x` by decide_tac >>
    `f y <= f x` by rw[] >>
    rw[]
  ]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==> !x y. f (MIN x y) = MIN (f x) (f y) *)
(* Proof: by MIN_DEF *)
val MIN_SWAP = store_thm(
  "MIN_SWAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MIN x y) = MIN (f x) (f y)``,
  rw[MIN_DEF] >>
  Cases_on `x < y` >| [
    `f x <= f y` by rw[] >>
    Cases_on `f x = f y` >-
    rw[] >>
    rw[],
    `y <= x` by decide_tac >>
    `f y <= f x` by rw[] >>
    rw[]
  ]);

(* Theorem: SUC (MAX m n) = MAX (SUC m) (SUC n) *)
(* Proof:
   If m < n, then SUC m < SUC n    by LESS_MONO_EQ
      hence true by MAX_DEF.
   If m = n, then true by MAX_IDEM.
   If n < m, true by MAX_COMM of the case m < n.
*)
val SUC_MAX = store_thm(
  "SUC_MAX",
  ``!m n. SUC (MAX m n) = MAX (SUC m) (SUC n)``,
  rw[MAX_DEF]);

(* Theorem: SUC (MIN m n) = MIN (SUC m) (SUC n) *)
(* Proof: by MIN_DEF *)
val SUC_MIN = store_thm(
  "SUC_MIN",
  ``!m n. SUC (MIN m n) = MIN (SUC m) (SUC n)``,
  rw[MIN_DEF]);

(* Reverse theorems *)
val MAX_SUC = save_thm("MAX_SUC", GSYM SUC_MAX);
(* val MAX_SUC = |- !m n. MAX (SUC m) (SUC n) = SUC (MAX m n): thm *)
val MIN_SUC = save_thm("MIN_SUC", GSYM SUC_MIN);
(* val MIN_SUC = |- !m n. MIN (SUC m) (SUC n) = SUC (MIN m n): thm *)

(* Theorem: x < n /\ y < n ==> MAX x y < n *)
(* Proof:
        MAX x y
      = if x < y then y else x    by MAX_DEF
      = either x or y
      < n                         for either case
*)
val MAX_LESS = store_thm(
  "MAX_LESS",
  ``!x y n. x < n /\ y < n ==> MAX x y < n``,
  rw[]);

(* Theorem: (MAX n m = n) \/ (MAX n m = m) *)
(* Proof: by MAX_DEF *)
val MAX_CASES = store_thm(
  "MAX_CASES",
  ``!m n. (MAX n m = n) \/ (MAX n m = m)``,
  rw[MAX_DEF]);

(* Theorem: (MIN n m = n) \/ (MIN n m = m) *)
(* Proof: by MIN_DEF *)
val MIN_CASES = store_thm(
  "MIN_CASES",
  ``!m n. (MIN n m = n) \/ (MIN n m = m)``,
  rw[MIN_DEF]);

(* Theorem: (MAX n m = 0) <=> ((n = 0) /\ (m = 0)) *)
(* Proof:
   If part: MAX n m = 0 ==> n = 0 /\ m = 0
      If n < m, 0 = MAX n m = m, hence m = 0     by MAX_DEF
                but n < 0 is F                   by NOT_LESS_0
      If ~(n < m), 0 = MAX n m = n, hence n = 0  by MAX_DEF
                and ~(0 < m) ==> m = 0           by NOT_LESS
   Only-if part: n = 0 /\ m = 0 ==> MAX n m = 0
      True since MAX 0 0 = 0                     by MAX_0
*)
val MAX_EQ_0 = store_thm(
  "MAX_EQ_0",
  ``!m n. (MAX n m = 0) <=> ((n = 0) /\ (m = 0))``,
  rw[MAX_DEF]);

(* Theorem: (MIN n m = 0) <=> ((n = 0) \/ (m = 0)) *)
(* Proof:
   If part: MIN n m = 0 ==> n = 0 \/ m = 0
      If n < m, 0 = MIN n m = n, hence n = 0     by MIN_DEF
      If ~(n < m), 0 = MAX n m = m, hence m = 0  by MIN_DEF
   Only-if part: n = 0 \/ m = 0 ==> MIN n m = 0
      True since MIN 0 0 = 0                     by MIN_0
*)
val MIN_EQ_0 = store_thm(
  "MIN_EQ_0",
  ``!m n. (MIN n m = 0) <=> ((n = 0) \/ (m = 0))``,
  rw[MIN_DEF]);

(* Theorem: m <= MAX m n /\ n <= MAX m n *)
(* Proof: by MAX_DEF *)
val MAX_IS_MAX = store_thm(
  "MAX_IS_MAX",
  ``!m n. m <= MAX m n /\ n <= MAX m n``,
  rw_tac std_ss[MAX_DEF]);

(* Theorem: MIN m n <= m /\ MIN m n <= n *)
(* Proof: by MIN_DEF *)
val MIN_IS_MIN = store_thm(
  "MIN_IS_MIN",
  ``!m n. MIN m n <= m /\ MIN m n <= n``,
  rw_tac std_ss[MIN_DEF]);

(* Theorem: (MAX (MAX m n) n = MAX m n) /\ (MAX m (MAX m n) = MAX m n) *)
(* Proof: by MAX_DEF *)
val MAX_ID = store_thm(
  "MAX_ID",
  ``!m n. (MAX (MAX m n) n = MAX m n) /\ (MAX m (MAX m n) = MAX m n)``,
  rw[MAX_DEF]);

(* Theorem: (MIN (MIN m n) n = MIN m n) /\ (MIN m (MIN m n) = MIN m n) *)
(* Proof: by MIN_DEF *)
val MIN_ID = store_thm(
  "MIN_ID",
  ``!m n. (MIN (MIN m n) n = MIN m n) /\ (MIN m (MIN m n) = MIN m n)``,
  rw[MIN_DEF]);

(* Theorem: a <= b /\ c <= d ==> MAX a c <= MAX b d *)
(* Proof: by MAX_DEF *)
val MAX_LE_PAIR = store_thm(
  "MAX_LE_PAIR",
  ``!a b c d. a <= b /\ c <= d ==> MAX a c <= MAX b d``,
  rw[]);

(* Theorem: a <= b /\ c <= d ==> MIN a c <= MIN b d *)
(* Proof: by MIN_DEF *)
val MIN_LE_PAIR = store_thm(
  "MIN_LE_PAIR",
  ``!a b c d. a <= b /\ c <= d ==> MIN a c <= MIN b d``,
  rw[]);

(* Theorem: MAX a (b + c) <= MAX a b + MAX a c *)
(* Proof: by MAX_DEF *)
val MAX_ADD = store_thm(
  "MAX_ADD",
  ``!a b c. MAX a (b + c) <= MAX a b + MAX a c``,
  rw[MAX_DEF]);

(* Theorem: MIN a (b + c) <= MIN a b + MIN a c *)
(* Proof: by MIN_DEF *)
val MIN_ADD = store_thm(
  "MIN_ADD",
  ``!a b c. MIN a (b + c) <= MIN a b + MIN a c``,
  rw[MIN_DEF]);

(* Theorem: 0 < n ==> (MAX 1 n = n) *)
(* Proof: by MAX_DEF *)
val MAX_1_POS = store_thm(
  "MAX_1_POS",
  ``!n. 0 < n ==> (MAX 1 n = n)``,
  rw[MAX_DEF]);

(* Theorem: 0 < n ==> (MIN 1 n = 1) *)
(* Proof: by MIN_DEF *)
val MIN_1_POS = store_thm(
  "MIN_1_POS",
  ``!n. 0 < n ==> (MIN 1 n = 1)``,
  rw[MIN_DEF]);

(* Theorem: MAX m n <= m + n *)
(* Proof:
   If m < n,  MAX m n = n <= m + n  by arithmetic
   Otherwise, MAX m n = m <= m + n  by arithmetic
*)
val MAX_LE_SUM = store_thm(
  "MAX_LE_SUM",
  ``!m n. MAX m n <= m + n``,
  rw[MAX_DEF]);

(* Theorem: MIN m n <= m + n *)
(* Proof:
   If m < n,  MIN m n = m <= m + n  by arithmetic
   Otherwise, MIN m n = n <= m + n  by arithmetic
*)
val MIN_LE_SUM = store_thm(
  "MIN_LE_SUM",
  ``!m n. MIN m n <= m + n``,
  rw[MIN_DEF]);

(* Theorem: MAX 1 (m ** n) = (MAX 1 m) ** n *)
(* Proof:
   If m = 0,
      Then 0 ** n = 0 or 1          by ZERO_EXP
      Thus MAX 1 (0 ** n) = 1       by MAX_DEF
       and (MAX 1 0) ** n = 1       by MAX_DEF, EXP_1
   If m <> 0,
      Then 0 < m ** n               by EXP_POS
        so MAX 1 (m ** n) = m ** n  by MAX_DEF
       and (MAX 1 m) ** n = m ** n  by MAX_DEF, 0 < m
*)
val MAX_1_EXP = store_thm(
  "MAX_1_EXP",
  ``!n m. MAX 1 (m ** n) = (MAX 1 m) ** n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[ZERO_EXP, MAX_DEF] >>
  `0 < m /\ 0 < m ** n` by rw[] >>
  `MAX 1 (m ** n) = m ** n` by rw[MAX_DEF] >>
  `MAX 1 m = m` by rw[MAX_DEF] >>
  fs[]);

(* Theorem: MIN 1 (m ** n) = (MIN 1 m) ** n *)
(* Proof:
   If m = 0,
      Then 0 ** n = 0 or 1          by ZERO_EXP
      Thus MIN 1 (0 ** n) = 0 when n <> 0 or 1 when n = 0  by MIN_DEF
       and (MIN 1 0) ** n = 0 ** n  by MIN_DEF
   If m <> 0,
      Then 0 < m ** n               by EXP_POS
        so MIN 1 (m ** n) = 1 ** n  by MIN_DEF
       and (MIN 1 m) ** n = 1 ** n  by MIN_DEF, 0 < m
*)
val MIN_1_EXP = store_thm(
  "MIN_1_EXP",
  ``!n m. MIN 1 (m ** n) = (MIN 1 m) ** n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[ZERO_EXP, MIN_DEF] >>
  `0 < m ** n` by rw[] >>
  `MIN 1 (m ** n) = 1` by rw[MIN_DEF] >>
  `MIN 1 m = 1` by rw[MIN_DEF] >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* Arithmetic Manipulations                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (n * n = n) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: n * n = n ==> (n = 0) \/ (n = 1)
      By contradiction, suppose n <> 0 /\ n <> 1.
      Since n * n = n = n * 1     by MULT_RIGHT_1
       then     n = 1             by MULT_LEFT_CANCEL, n <> 0
       This contradicts n <> 1.
   Only-if part: (n = 0) \/ (n = 1) ==> n * n = n
      That is, 0 * 0 = 0          by MULT
           and 1 * 1 = 1          by MULT_RIGHT_1
*)
val SQ_EQ_SELF = store_thm(
  "SQ_EQ_SELF",
  ``!n. (n * n = n) <=> ((n = 0) \/ (n = 1))``,
  rw_tac bool_ss[EQ_IMP_THM] >-
  metis_tac[MULT_RIGHT_1, MULT_LEFT_CANCEL] >-
  rw[] >>
  rw[]);

(* Theorem: m <= n /\ 0 < c ==> b ** c ** m <= b ** c ** n *)
(* Proof:
   If b = 0,
      Note 0 < c ** m /\ 0 < c ** n   by EXP_POS, by 0 < c
      Thus 0 ** c ** m = 0            by ZERO_EXP
       and 0 ** c ** n = 0            by ZERO_EXP
      Hence true.
   If b <> 0,
      Then c ** m <= c ** n           by EXP_BASE_LEQ_MONO_IMP, 0 < c
        so b ** c ** m <= b ** c ** n by EXP_BASE_LEQ_MONO_IMP, 0 < b
*)
val EXP_EXP_BASE_LE = store_thm(
  "EXP_EXP_BASE_LE",
  ``!b c m n. m <= n /\ 0 < c ==> b ** c ** m <= b ** c ** n``,
  rpt strip_tac >>
  Cases_on `b = 0` >-
  rw[ZERO_EXP] >>
  rw[EXP_BASE_LEQ_MONO_IMP]);

(* Theorem: a <= b ==> a ** n <= b ** n *)
(* Proof:
   Note a ** n <= b ** n                 by EXP_EXP_LE_MONO
   Thus size (a ** n) <= size (b ** n)   by size_monotone_le
*)
val EXP_EXP_LE_MONO_IMP = store_thm(
  "EXP_EXP_LE_MONO_IMP",
  ``!a b n. a <= b ==> a ** n <= b ** n``,
  rw[]);

(* Theorem: m <= n ==> !p. p ** n = p ** m * p ** (n - m) *)
(* Proof:
   Note n = (n - m) + m          by m <= n
        p ** n
      = p ** (n - m) * p ** m    by EXP_ADD
      = p ** m * p ** (n - m)    by MULT_COMM
*)
val EXP_BY_ADD_SUB_LE = store_thm(
  "EXP_BY_ADD_SUB_LE",
  ``!m n. m <= n ==> !p. p ** n = p ** m * p ** (n - m)``,
  rpt strip_tac >>
  `n = (n - m) + m` by decide_tac >>
  metis_tac[EXP_ADD, MULT_COMM]);

(* Theorem: m < n ==> (p ** n = p ** m * p ** (n - m)) *)
(* Proof: by EXP_BY_ADD_SUB_LE, LESS_IMP_LESS_OR_EQ *)
val EXP_BY_ADD_SUB_LT = store_thm(
  "EXP_BY_ADD_SUB_LT",
  ``!m n. m < n ==> !p. p ** n = p ** m * p ** (n - m)``,
  rw[EXP_BY_ADD_SUB_LE]);

(* Theorem: 0 < m ==> m ** (SUC n) DIV m = m ** n *)
(* Proof:
     m ** (SUC n) DIV m
   = (m * m ** n) DIV m    by EXP
   = m ** n                by MULT_TO_DIV, 0 < m
*)
val EXP_SUC_DIV = store_thm(
  "EXP_SUC_DIV",
  ``!m n. 0 < m ==> (m ** (SUC n) DIV m = m ** n)``,
  simp[EXP, MULT_TO_DIV]);

(* Theorem: n <= n ** 2 *)
(* Proof:
   If n = 0,
      Then n ** 2 = 0 >= 0       by ZERO_EXP
   If n <> 0, then 0 < n         by NOT_ZERO_LT_ZERO
      Hence n = n ** 1           by EXP_1
             <= n ** 2           by EXP_BASE_LEQ_MONO_IMP
*)
val SELF_LE_SQ = store_thm(
  "SELF_LE_SQ",
  ``!n. n <= n ** 2``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n /\ 1 <= 2` by decide_tac >>
  metis_tac[EXP_BASE_LEQ_MONO_IMP, EXP_1]);

(* Theorem: a <= b /\ c <= d ==> a + c <= b + d *)
(* Proof: by LESS_EQ_LESS_EQ_MONO, or
   Note a <= b ==>  a + c <= b + c    by LE_ADD_RCANCEL
    and c <= d ==>  b + c <= b + d    by LE_ADD_LCANCEL
   Thus             a + c <= b + d    by LESS_EQ_TRANS
*)
val LE_MONO_ADD2 = store_thm(
  "LE_MONO_ADD2",
  ``!a b c d. a <= b /\ c <= d ==> a + c <= b + d``,
  rw[LESS_EQ_LESS_EQ_MONO]);

(* Theorem: a < b /\ c < d ==> a + c < b + d *)
(* Proof:
   Note a < b ==>  a + c < b + c    by LT_ADD_RCANCEL
    and c < d ==>  b + c < b + d    by LT_ADD_LCANCEL
   Thus            a + c < b + d    by LESS_TRANS
*)
val LT_MONO_ADD2 = store_thm(
  "LT_MONO_ADD2",
  ``!a b c d. a < b /\ c < d ==> a + c < b + d``,
  rw[LT_ADD_RCANCEL, LT_ADD_LCANCEL]);

(* Theorem: a <= b /\ c <= d ==> a * c <= b * d *)
(* Proof: by LESS_MONO_MULT2, or
   Note a <= b ==> a * c <= b * c  by LE_MULT_RCANCEL
    and c <= d ==> b * c <= b * d  by LE_MULT_LCANCEL
   Thus            a * c <= b * d  by LESS_EQ_TRANS
*)
val LE_MONO_MULT2 = store_thm(
  "LE_MONO_MULT2",
  ``!a b c d. a <= b /\ c <= d ==> a * c <= b * d``,
  rw[LESS_MONO_MULT2]);

(* Theorem: a < b /\ c < d ==> a * c < b * d *)
(* Proof:
   Note 0 < b, by a < b.
    and 0 < d, by c < d.
   If c = 0,
      Then a * c = 0 < b * d   by MULT_EQ_0
   If c <> 0, then 0 < c       by NOT_ZERO_LT_ZERO
      a < b ==> a * c < b * c  by LT_MULT_RCANCEL, 0 < c
      c < d ==> b * c < b * d  by LT_MULT_LCANCEL, 0 < b
   Thus         a * c < b * d  by LESS_TRANS
*)
val LT_MONO_MULT2 = store_thm(
  "LT_MONO_MULT2",
  ``!a b c d. a < b /\ c < d ==> a * c < b * d``,
  rpt strip_tac >>
  `0 < b /\ 0 < d` by decide_tac >>
  Cases_on `c = 0` >-
  metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[LT_MULT_RCANCEL, LT_MULT_LCANCEL, LESS_TRANS, NOT_ZERO_LT_ZERO]);

(* Theorem: 1 < m /\ 1 < n ==> (m + n <= m * n) *)
(* Proof:
   Let m = m' + 1, n = n' + 1.
   Note m' <> 0 /\ n' <> 0.
   Thus m' * n' <> 0               by MULT_EQ_0
     or 1 <= m' * n'
       m * n
     = (m' + 1) * (n' + 1)
     = m' * n' + m' + n' + 1       by arithmetic
    >= 1 + m' + n' + 1             by 1 <= m' * n'
     = m + n
*)
val SUM_LE_PRODUCT = store_thm(
  "SUM_LE_PRODUCT",
  ``!m n. 1 < m /\ 1 < n ==> (m + n <= m * n)``,
  rpt strip_tac >>
  `m <> 0 /\ n <> 0` by decide_tac >>
  `?m' n'. (m = m' + 1) /\ (n = n' + 1)` by metis_tac[num_CASES, ADD1] >>
  `m * n = (m' + 1) * n' + (m' + 1)` by rw[LEFT_ADD_DISTRIB] >>
  `_ = m' * n' + n' + (m' + 1)` by rw[RIGHT_ADD_DISTRIB] >>
  `_ = m + (n' + m' * n')` by decide_tac >>
  `m' * n' <> 0` by fs[] >>
  decide_tac);

(* Theorem: 0 < n ==> k * n + 1 <= (k + 1) * n *)
(* Proof:
        k * n + 1
     <= k * n + n          by 1 <= n
     <= (k + 1) * n        by RIGHT_ADD_DISTRIB
*)
val MULTIPLE_SUC_LE = store_thm(
  "MULTIPLE_SUC_LE",
  ``!n k. 0 < n ==> k * n + 1 <= (k + 1) * n``,
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Simple Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m /\ 0 < n /\ (m + n = 2) ==> m = 1 /\ n = 1 *)
(* Proof: by arithmetic. *)
val ADD_EQ_2 = store_thm(
  "ADD_EQ_2",
  ``!m n. 0 < m /\ 0 < n /\ (m + n = 2) ==> (m = 1) /\ (n = 1)``,
  rw_tac arith_ss[]);

(* Theorem: EVEN 0 *)
(* Proof: by EVEN. *)
val EVEN_0 = store_thm(
  "EVEN_0",
  ``EVEN 0``,
  simp[]);

(* Theorem: ODD 1 *)
(* Proof: by ODD. *)
val ODD_1 = store_thm(
  "ODD_1",
  ``ODD 1``,
  simp[]);

(* Theorem: EVEN 2 *)
(* Proof: by EVEN_MOD2. *)
val EVEN_2 = store_thm(
  "EVEN_2",
  ``EVEN 2``,
  EVAL_TAC);

(*
EVEN_ADD  |- !m n. EVEN (m + n) <=> (EVEN m <=> EVEN n)
ODD_ADD   |- !m n. ODD (m + n) <=> (ODD m <=/=> ODD n)
EVEN_MULT |- !m n. EVEN (m * n) <=> EVEN m \/ EVEN n
ODD_MULT  |- !m n. ODD (m * n) <=> ODD m /\ ODD n
*)

(* Derive theorems. *)
val EVEN_SQ = save_thm("EVEN_SQ",
    EVEN_MULT |> SPEC ``n:num`` |> SPEC ``n:num`` |> SIMP_RULE arith_ss[] |> GEN_ALL);
(* val EVEN_SQ = |- !n. EVEN (n ** 2) <=> EVEN n: thm *)
val ODD_SQ = save_thm("ODD_SQ",
    ODD_MULT |> SPEC ``n:num`` |> SPEC ``n:num`` |> SIMP_RULE arith_ss[] |> GEN_ALL);
(* val ODD_SQ = |- !n. ODD (n ** 2) <=> ODD n: thm *)

(* Theorem: EVEN (2 * a + b) <=> EVEN b *)
(* Proof:
       EVEN (2 * a + b)
   <=> EVEN (2 * a) /\ EVEN b      by EVEN_ADD
   <=>            T /\ EVEN b      by EVEN_DOUBLE
   <=> EVEN b
*)
Theorem EQ_PARITY:
  !a b. EVEN (2 * a + b) <=> EVEN b
Proof
  rw[EVEN_ADD, EVEN_DOUBLE]
QED

(* Theorem: ODD x <=> (x MOD 2 = 1) *)
(* Proof:
   If part: ODD x ==> x MOD 2 = 1
      Since  ODD x
         <=> ~EVEN x          by ODD_EVEN
         <=> ~(x MOD 2 = 0)   by EVEN_MOD2
         But x MOD 2 < 2      by MOD_LESS, 0 < 2
          so x MOD 2 = 1      by arithmetic
   Only-if part: x MOD 2 = 1 ==> ODD x
      By contradiction, suppose ~ODD x.
      Then EVEN x             by ODD_EVEN
       and x MOD 2 = 0        by EVEN_MOD2
      This contradicts x MOD 2 = 1.
*)
val ODD_MOD2 = store_thm(
  "ODD_MOD2",
  ``!x. ODD x <=> (x MOD 2 = 1)``,
  metis_tac[EVEN_MOD2, ODD_EVEN, MOD_LESS,
             DECIDE``0 <> 1 /\ 0 < 2 /\ !n. n < 2 /\ n <> 1 ==> (n = 0)``]);

(* Theorem: (EVEN n <=> ODD (SUC n)) /\ (ODD n <=> EVEN (SUC n)) *)
(* Proof: by EVEN, ODD, EVEN_OR_ODD *)
val EVEN_ODD_SUC = store_thm(
  "EVEN_ODD_SUC",
  ``!n. (EVEN n <=> ODD (SUC n)) /\ (ODD n <=> EVEN (SUC n))``,
  metis_tac[EVEN, ODD, EVEN_OR_ODD]);

(* Theorem: 0 < n ==> (EVEN n <=> ODD (PRE n)) /\ (ODD n <=> EVEN (PRE n)) *)
(* Proof: by EVEN, ODD, EVEN_OR_ODD, PRE_SUC_EQ *)
val EVEN_ODD_PRE = store_thm(
  "EVEN_ODD_PRE",
  ``!n. 0 < n ==> (EVEN n <=> ODD (PRE n)) /\ (ODD n <=> EVEN (PRE n))``,
  metis_tac[EVEN, ODD, EVEN_OR_ODD, PRE_SUC_EQ]);

(* Theorem: EVEN (n * (n + 1)) *)
(* Proof:
   If EVEN n, true        by EVEN_MULT
   If ~(EVEN n),
      Then EVEN (SUC n)   by EVEN
        or EVEN (n + 1)   by ADD1
      Thus true           by EVEN_MULT
*)
val EVEN_PARTNERS = store_thm(
  "EVEN_PARTNERS",
  ``!n. EVEN (n * (n + 1))``,
  metis_tac[EVEN, EVEN_MULT, ADD1]);

(* Theorem: EVEN n ==> (n = 2 * HALF n) *)
(* Proof:
   Note EVEN n ==> ?m. n = 2 * m     by EVEN_EXISTS
    and HALF n = HALF (2 * m)        by above
               = m                   by MULT_TO_DIV, 0 < 2
   Thus n = 2 * m = 2 * HALF n       by above
*)
val EVEN_HALF = store_thm(
  "EVEN_HALF",
  ``!n. EVEN n ==> (n = 2 * HALF n)``,
  metis_tac[EVEN_EXISTS, MULT_TO_DIV, DECIDE``0 < 2``]);

(* Theorem: ODD n ==> (n = 2 * HALF n + 1 *)
(* Proof:
   Since n = HALF n * 2 + n MOD 2  by DIVISION, 0 < 2
           = 2 * HALF n + n MOD 2  by MULT_COMM
           = 2 * HALF n + 1        by ODD_MOD2
*)
val ODD_HALF = store_thm(
  "ODD_HALF",
  ``!n. ODD n ==> (n = 2 * HALF n + 1)``,
  metis_tac[DIVISION, MULT_COMM, ODD_MOD2, DECIDE``0 < 2``]);

(* Theorem: EVEN n ==> (HALF (SUC n) = HALF n) *)
(* Proof:
   Note n = (HALF n) * 2 + (n MOD 2)   by DIVISION, 0 < 2
          = (HALF n) * 2               by EVEN_MOD2
    Now SUC n
      = n + 1                          by ADD1
      = (HALF n) * 2 + 1               by above
   Thus HALF (SUC n)
      = ((HALF n) * 2 + 1) DIV 2       by above
      = HALF n                         by DIV_MULT, 1 < 2
*)
val EVEN_SUC_HALF = store_thm(
  "EVEN_SUC_HALF",
  ``!n. EVEN n ==> (HALF (SUC n) = HALF n)``,
  rpt strip_tac >>
  `n MOD 2 = 0` by rw[GSYM EVEN_MOD2] >>
  `n = HALF n * 2 + n MOD 2` by rw[DIVISION] >>
  `SUC n = HALF n * 2 + 1` by rw[] >>
  metis_tac[DIV_MULT, DECIDE``1 < 2``]);

(* Theorem: ODD n ==> (HALF (SUC n) = SUC (HALF n)) *)
(* Proof:
     SUC n
   = SUC (2 * HALF n + 1)              by ODD_HALF
   = 2 * HALF n + 1 + 1                by ADD1
   = 2 * HALF n + 2                    by arithmetic
   = 2 * (HALF n + 1)                  by LEFT_ADD_DISTRIB
   = 2 * SUC (HALF n)                  by ADD1
   = SUC (HALF n) * 2 + 0              by MULT_COMM, ADD_0
   Hence HALF (SUC n) = SUC (HALF n)   by DIV_UNIQUE, 0 < 2
*)
val ODD_SUC_HALF = store_thm(
  "ODD_SUC_HALF",
  ``!n. ODD n ==> (HALF (SUC n) = SUC (HALF n))``,
  rpt strip_tac >>
  `SUC n = SUC (2 * HALF n + 1)` by rw[ODD_HALF] >>
  `_ = SUC (HALF n) * 2 + 0` by rw[] >>
  metis_tac[DIV_UNIQUE, DECIDE``0 < 2``]);

(* Theorem: (HALF n = 0) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: (HALF n = 0) ==> ((n = 0) \/ (n = 1))
      Note n = (HALF n) * 2 + (n MOD 2)    by DIVISION, 0 < 2
             = n MOD 2                     by HALF n = 0
       and n MOD 2 < 2                     by MOD_LESS, 0 < 2
        so n < 2, or n = 0 or n = 1        by arithmetic
   Only-if part: HALF 0 = 0, HALF 1 = 0.
      True since both 0 or 1 < 2           by LESS_DIV_EQ_ZERO, 0 < 2
*)
val HALF_EQ_0 = store_thm(
  "HALF_EQ_0",
  ``!n. (HALF n = 0) <=> ((n = 0) \/ (n = 1))``,
  rw[LESS_DIV_EQ_ZERO, EQ_IMP_THM] >>
  `n = (HALF n) * 2 + (n MOD 2)` by rw[DIVISION] >>
  `n MOD 2 < 2` by rw[MOD_LESS] >>
  decide_tac);

(* Theorem: (HALF n = n) <=> (n = 0) *)
(* Proof:
   If part: HALF n = n ==> n = 0
      Note n = 2 * HALF n + (n MOD 2)    by DIVISION, MULT_COMM
        so n = 2 * n + (n MOD 2)         by HALF n = n
        or 0 = n + (n MOD 2)             by arithmetic
      Thus n  = 0  and (n MOD 2 = 0)     by ADD_EQ_0
   Only-if part: HALF 0 = 0, true        by ZERO_DIV, 0 < 2
*)
val HALF_EQ_SELF = store_thm(
  "HALF_EQ_SELF",
  ``!n. (HALF n = n) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  `n = 2 * HALF n + (n MOD 2)` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 2``] >>
  rw[ADD_EQ_0]);

(* Theorem: 0 < n ==> HALF n < n *)
(* Proof:
   Note HALF n <= n     by DIV_LESS_EQ, 0 < 2
    and HALF n <> n     by HALF_EQ_SELF, n <> 0
     so HALF n < n      by arithmetic
*)
val HALF_LT = store_thm(
  "HALF_LT",
  ``!n. 0 < n ==> HALF n < n``,
  rpt strip_tac >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n <> n` by rw[HALF_EQ_SELF] >>
  decide_tac);

(* Theorem: 2 < n ==> (1 + HALF n < n) *)
(* Proof:
   If EVEN n,
      then     2 * HALF n = n      by EVEN_HALF
        so 2 + 2 * HALF n < n + n  by 2 < n
        or     1 + HALF n < n      by arithmetic
   If ~EVEN n, then ODD n          by ODD_EVEN
      then 1 + 2 * HALF n = 2      by ODD_HALF
        so 1 + 2 * HALF n < n      by 2 < n
      also 2 + 2 * HALF n < n + n  by 1 < n
        or     1 + HALF n < n      by arithmetic
*)
Theorem HALF_ADD1_LT:
  !n. 2 < n ==> 1 + HALF n < n
Proof
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `2 * HALF n = n` by rw[EVEN_HALF] >>
    decide_tac,
    `1 + 2 * HALF n = n` by rw[ODD_HALF, ODD_EVEN] >>
    decide_tac
  ]
QED

(* Theorem alias *)
Theorem HALF_TWICE = arithmeticTheory.MULT_DIV_2;
(* val HALF_TWICE = |- !n. HALF (2 * n) = n: thm *)

(* Theorem: n * HALF m <= HALF (n * m) *)
(* Proof:
   Let k = HALF m.
   If EVEN m,
      Then m = 2 * k           by EVEN_HALF
        HALF (n * m)
      = HALF (n * (2 * k))     by above
      = HALF (2 * (n * k))     by arithmetic
      = n * k                  by HALF_TWICE
   If ~EVEN m, then ODD m      by ODD_EVEN
      Then m = 2 * k + 1       by ODD_HALF
      so   HALF (n * m)
         = HALF (n * (2 * k + 1))        by above
         = HALF (2 * (n * k) + n)        by LEFT_ADD_DISTRIB
         = HALF (2 * (n * k)) + HALF n   by ADD_DIV_ADD_DIV
         = n * k + HALF n                by HALF_TWICE
         >= n * k                        by arithmetic
*)
Theorem HALF_MULT: !m n. n * (m DIV 2) <= (n * m) DIV 2
Proof
  rpt strip_tac >>
  qabbrev_tac `k = m DIV 2` >>
  Cases_on `EVEN m`
  >- (`m = 2 * k` by rw[EVEN_HALF, Abbr`k`] >>
      simp[]) >>
  `ODD m` by rw[ODD_EVEN] >>
  `m = 2 * k + 1` by rw[ODD_HALF, Abbr`k`] >>
  simp[LEFT_ADD_DISTRIB]
QED

(* Theorem: 2 * HALF n <= n /\ n <= SUC (2 * HALF n) *)
(* Proof:
   If EVEN n,
      Then n = 2 * HALF n         by EVEN_HALF
       and n = n < SUC n          by LESS_SUC
        or n <= n <= SUC n,
      Giving 2 * HALF n <= n /\ n <= SUC (2 * HALF n)
   If ~(EVEN n), then ODD n       by EVEN_ODD
      Then n = 2 * HALF n + 1     by ODD_HALF
             = SUC (2 * HALF n)   by ADD1
        or n - 1 < n = n
        or n - 1 <= n <= n,
      Giving 2 * HALF n <= n /\ n <= SUC (2 * HALF n)
*)
val TWO_HALF_LE_THM = store_thm(
  "TWO_HALF_LE_THM",
  ``!n. 2 * HALF n <= n /\ n <= SUC (2 * HALF n)``,
  strip_tac >>
  Cases_on `EVEN n` >-
  rw[GSYM EVEN_HALF] >>
  `ODD n` by rw[ODD_EVEN] >>
  `n <> 0` by metis_tac[ODD] >>
  `n = SUC (2 * HALF n)` by rw[ODD_HALF, ADD1] >>
  `2 * HALF n = PRE n` by rw[] >>
  rw[]);

(* Theorem: 2 * ((HALF n) * m) <= n * m *)
(* Proof:
      2 * ((HALF n) * m)
    = 2 * (m * HALF n)      by MULT_COMM
   <= 2 * (HALF (m * n))    by HALF_MULT
   <= m * n                 by TWO_HALF_LE_THM
    = n * m                 by MULT_COMM
*)
val TWO_HALF_TIMES_LE = store_thm(
  "TWO_HALF_TIMES_LE",
  ``!m n. 2 * ((HALF n) * m) <= n * m``,
  rpt strip_tac >>
  `2 * (m * HALF n) <= 2 * (HALF (m * n))` by rw[HALF_MULT] >>
  `2 * (HALF (m * n)) <= m * n` by rw[TWO_HALF_LE_THM] >>
  fs[]);

(* Theorem: 0 < n ==> 1 + HALF n <= n *)
(* Proof:
   If n = 1,
      HALF 1 = 0, hence true.
   If n <> 1,
      Then HALF n <> 0       by HALF_EQ_0, n <> 0, n <> 1
      Thus 1 + HALF n
        <= HALF n + HALF n   by 1 <= HALF n
         = 2 * HALF n
        <= n                 by TWO_HALF_LE_THM
*)
val HALF_ADD1_LE = store_thm(
  "HALF_ADD1_LE",
  ``!n. 0 < n ==> 1 + HALF n <= n``,
  rpt strip_tac >>
  (Cases_on `n = 1` >> simp[]) >>
  `HALF n <> 0` by metis_tac[HALF_EQ_0, NOT_ZERO] >>
  `1 + HALF n <= 2 * HALF n` by decide_tac >>
  `2 * HALF n <= n` by rw[TWO_HALF_LE_THM] >>
  decide_tac);

(* Theorem: (HALF n) ** 2 <= (n ** 2) DIV 4 *)
(* Proof:
   Let k = HALF n.
   Then 2 * k <= n                by TWO_HALF_LE_THM
     so (2 * k) ** 2 <= n ** 2                by EXP_EXP_LE_MONO
    and (2 * k) ** 2 DIV 4 <= n ** 2 DIV 4    by DIV_LE_MONOTONE, 0 < 4
    But (2 * k) ** 2 DIV 4
      = 4 * k ** 2 DIV 4          by EXP_BASE_MULT
      = k ** 2                    by MULT_TO_DIV, 0 < 4
   Thus k ** 2 <= n ** 2 DIV 4.
*)
val HALF_SQ_LE = store_thm(
  "HALF_SQ_LE",
  ``!n. (HALF n) ** 2 <= (n ** 2) DIV 4``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `2 * k <= n` by rw[TWO_HALF_LE_THM, Abbr`k`] >>
  `(2 * k) ** 2 <= n ** 2` by rw[] >>
  `(2 * k) ** 2 DIV 4 <= n ** 2 DIV 4` by rw[DIV_LE_MONOTONE] >>
  `(2 * k) ** 2 DIV 4 = 4 * k ** 2 DIV 4` by rw[EXP_BASE_MULT] >>
  `_ = k ** 2` by rw[MULT_TO_DIV] >>
  decide_tac);

(* Obtain theorems *)
val HALF_LE = save_thm("HALF_LE",
    DIV_LESS_EQ |> SPEC ``2`` |> SIMP_RULE (arith_ss) [] |> SPEC ``n:num`` |> GEN_ALL);
(* val HALF_LE = |- !n. HALF n <= n: thm *)
val HALF_LE_MONO = save_thm("HALF_LE_MONO",
    DIV_LE_MONOTONE |> SPEC ``2`` |> SIMP_RULE (arith_ss) []);
(* val HALF_LE_MONO = |- !x y. x <= y ==> HALF x <= HALF y: thm *)

(* Theorem: HALF (SUC n) <= n *)
(* Proof:
   If EVEN n,
      Then ?k. n = 2 * k                       by EVEN_EXISTS
       and SUC n = 2 * k + 1
        so HALF (SUC n) = k <= k + k = n       by ineqaulities
   Otherwise ODD n,                            by ODD_EVEN
      Then ?k. n = 2 * k + 1                   by ODD_EXISTS
       and SUC n = 2 * k + 2
        so HALF (SUC n) = k + 1 <= k + k + 1 = n
*)
Theorem HALF_SUC:
  !n. HALF (SUC n) <= n
Proof
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `?k. n = 2 * k` by metis_tac[EVEN_EXISTS] >>
    `HALF (SUC n) = k` by simp[ADD1] >>
    decide_tac,
    `?k. n = 2 * k + 1` by metis_tac[ODD_EXISTS, ODD_EVEN, ADD1] >>
    `HALF (SUC n) = k + 1` by simp[ADD1] >>
    decide_tac
  ]
QED

(* Theorem: 0 < n ==> HALF (SUC (SUC n)) <= n *)
(* Proof:
   Note SUC (SUC n) = n + 2        by ADD1
   If EVEN n,
      then ?k. n = 2 * k           by EVEN_EXISTS
      Since n = 2 * k <> 0         by NOT_ZERO, 0 < n
        so k <> 0, or 1 <= k       by MULT_EQ_0
           HALF (n + 2)
         = k + 1                   by arithmetic
        <= k + k                   by above
         = n
   Otherwise ODD n,                by ODD_EVEN
      then ?k. n = 2 * k + 1       by ODD_EXISTS
           HALF (n + 2)
         = HALF (2 * k + 3)        by arithmetic
         = k + 1                   by arithmetic
        <= k + k + 1               by ineqaulities
         = n
*)
Theorem HALF_SUC_SUC:
  !n. 0 < n ==> HALF (SUC (SUC n)) <= n
Proof
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `?k. n = 2 * k` by metis_tac[EVEN_EXISTS] >>
    `0 < k` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    `1 <= k` by decide_tac >>
    `HALF (SUC (SUC n)) = k + 1` by simp[ADD1] >>
    fs[],
    `?k. n = 2 * k + 1` by metis_tac[ODD_EXISTS, ODD_EVEN, ADD1] >>
    `HALF (SUC (SUC n)) = k + 1` by simp[ADD1] >>
    fs[]
  ]
QED

(* Theorem: n < HALF (SUC m) ==> 2 * n + 1 <= m *)
(* Proof:
   If EVEN m,
      Then m = 2 * HALF m                      by EVEN_HALF
       and SUC m = 2 * HALF m + 1              by ADD1
        so     n < (2 * HALF m + 1) DIV 2      by given
        or     n < HALF m                      by arithmetic
           2 * n < 2 * HALF m                  by LT_MULT_LCANCEL
           2 * n < m                           by above
       2 * n + 1 <= m                          by arithmetic
    Otherwise, ODD m                           by ODD_EVEN
       Then m = 2 * HALF m + 1                 by ODD_HALF
        and SUC m = 2 * HALF m + 2             by ADD1
         so     n < (2 * HALF m + 2) DIV 2     by given
         or     n < HALF m + 1                 by arithmetic
        2 * n + 1 < 2 * HALF m + 1             by LT_MULT_LCANCEL, LT_ADD_RCANCEL
         or 2 * n + 1 < m                      by above
    Overall, 2 * n + 1 <= m.
*)
Theorem HALF_SUC_LE:
  !n m. n < HALF (SUC m) ==> 2 * n + 1 <= m
Proof
  rpt strip_tac >>
  Cases_on `EVEN m` >| [
    `m = 2 * HALF m` by simp[EVEN_HALF] >>
    `HALF (SUC m) =  HALF (2 * HALF m + 1)` by metis_tac[ADD1] >>
    `_ = HALF m` by simp[] >>
    simp[],
    `m = 2 * HALF m + 1` by simp[ODD_HALF, ODD_EVEN] >>
    `HALF (SUC m) =  HALF (2 * HALF m + 1 + 1)` by metis_tac[ADD1] >>
    `_ = HALF m + 1` by simp[] >>
    simp[]
  ]
QED

(* Theorem: 2 * n < m ==> n <= HALF m *)
(* Proof:
   If EVEN m,
      Then m = 2 * HALF m                      by EVEN_HALF
        so 2 * n < 2 * HALF m                  by above
        or     n < HALF m                      by LT_MULT_LCANCEL
    Otherwise, ODD m                           by ODD_EVEN
       Then m = 2 * HALF m + 1                 by ODD_HALF
         so 2 * n < 2 * HALF m + 1             by above
         so 2 * n <= 2 * HALF m                by removing 1
         or     n <= HALF m                    by LE_MULT_LCANCEL
    Overall, n <= HALF m.
*)
Theorem HALF_EVEN_LE:
  !n m. 2 * n < m ==> n <= HALF m
Proof
  rpt strip_tac >>
  Cases_on `EVEN m` >| [
    `2 * n < 2 * HALF m` by metis_tac[EVEN_HALF] >>
    simp[],
    `2 * n < 2 * HALF m + 1` by metis_tac[ODD_HALF, ODD_EVEN] >>
    simp[]
  ]
QED

(* Theorem: 2 * n + 1 < m ==> n < HALF m *)
(* Proof:
   If EVEN m,
      Then m = 2 * HALF m                      by EVEN_HALF
        so 2 * n + 1 < 2 * HALF m              by above
        or     2 * n < 2 * HALF m              by removing 1
        or     n < HALF m                      by LT_MULT_LCANCEL
    Otherwise, ODD m                           by ODD_EVEN
       Then m = 2 * HALF m + 1                 by ODD_HALF
         so 2 * n + 1 < 2 * HALF m + 1         by above
         or     2 * n < 2 * HALF m             by LT_ADD_RCANCEL
         or         n < HALF m                 by LT_MULT_LCANCEL
    Overall, n < HALF m.
*)
Theorem HALF_ODD_LT:
  !n m. 2 * n + 1 < m ==> n < HALF m
Proof
  rpt strip_tac >>
  Cases_on `EVEN m` >| [
    `2 * n + 1 < 2 * HALF m` by metis_tac[EVEN_HALF] >>
    simp[],
    `2 * n + 1 < 2 * HALF m + 1` by metis_tac[ODD_HALF, ODD_EVEN] >>
    simp[]
  ]
QED

(* Theorem: EVEN n ==> !m. m * n = (TWICE m) * (HALF n) *)
(* Proof:
     (TWICE m) * (HALF n)
   = (2 * m) * (HALF n)   by notation
   = m * TWICE (HALF n)   by MULT_COMM, MULT_ASSOC
   = m * n                by EVEN_HALF
*)
val MULT_EVEN = store_thm(
  "MULT_EVEN",
  ``!n. EVEN n ==> !m. m * n = (TWICE m) * (HALF n)``,
  metis_tac[MULT_COMM, MULT_ASSOC, EVEN_HALF]);

(* Theorem: ODD n ==> !m. m * n = m + (TWICE m) * (HALF n) *)
(* Proof:
     m + (TWICE m) * (HALF n)
   = m + (2 * m) * (HALF n)     by notation
   = m + m * (TWICE (HALF n))   by MULT_COMM, MULT_ASSOC
   = m * (SUC (TWICE (HALF n))) by MULT_SUC
   = m * (TWICE (HALF n) + 1)   by ADD1
   = m * n                      by ODD_HALF
*)
val MULT_ODD = store_thm(
  "MULT_ODD",
  ``!n. ODD n ==> !m. m * n = m + (TWICE m) * (HALF n)``,
  metis_tac[MULT_COMM, MULT_ASSOC, ODD_HALF, MULT_SUC, ADD1]);

(* Theorem: EVEN m /\ m <> 0 ==> !n. EVEN n <=> EVEN (n MOD m) *)
(* Proof:
   Note ?k. m = 2 * k                by EVEN_EXISTS, EVEN m
    and k <> 0                       by MULT_EQ_0, m <> 0
    ==> (n MOD m) MOD 2 = n MOD 2    by MOD_MULT_MOD
   The result follows                by EVEN_MOD2
*)
val EVEN_MOD_EVEN = store_thm(
  "EVEN_MOD_EVEN",
  ``!m. EVEN m /\ m <> 0 ==> !n. EVEN n <=> EVEN (n MOD m)``,
  rpt strip_tac >>
  `?k. m = 2 * k` by rw[GSYM EVEN_EXISTS] >>
  `(n MOD m) MOD 2 = n MOD 2` by rw[MOD_MULT_MOD] >>
  metis_tac[EVEN_MOD2]);

(* Theorem: EVEN m /\ m <> 0 ==> !n. ODD n <=> ODD (n MOD m) *)
(* Proof: by EVEN_MOD_EVEN, ODD_EVEN *)
val EVEN_MOD_ODD = store_thm(
  "EVEN_MOD_ODD",
  ``!m. EVEN m /\ m <> 0 ==> !n. ODD n <=> ODD (n MOD m)``,
  rw_tac std_ss[EVEN_MOD_EVEN, ODD_EVEN]);

(* Theorem: c <= a ==> ((a - b) - (a - c) = c - b) *)
(* Proof:
     a - b - (a - c)
   = a - (b + (a - c))     by SUB_RIGHT_SUB, no condition
   = a - ((a - c) + b)     by ADD_COMM, no condition
   = a - (a - c) - b       by SUB_RIGHT_SUB, no condition
   = a + c - a - b         by SUB_SUB, c <= a
   = c + a - a - b         by ADD_COMM, no condition
   = c + (a - a) - b       by LESS_EQ_ADD_SUB, a <= a
   = c + 0 - b             by SUB_EQUAL_0
   = c - b
*)
val SUB_SUB_SUB = store_thm(
  "SUB_SUB_SUB",
  ``!a b c. c <= a ==> ((a - b) - (a - c) = c - b)``,
  decide_tac);

(* Theorem: c <= a ==> (a + b - (a - c) = c + b) *)
(* Proof:
     a + b - (a - c)
   = a + b + c - a      by SUB_SUB, a <= c
   = a + (b + c) - a    by ADD_ASSOC
   = (b + c) + a - a    by ADD_COMM
   = b + c - (a - a)    by SUB_SUB, a <= a
   = b + c - 0          by SUB_EQUAL_0
   = b + c              by SUB_0
*)
val ADD_SUB_SUB = store_thm(
  "ADD_SUB_SUB",
  ``!a b c. c <= a ==> (a + b - (a - c) = c + b)``,
  decide_tac);

(* Theorem: 0 < p ==> !m n. (m - n = p) <=> (m = n + p) *)
(* Proof:
   If part: m - n = p ==> m = n + p
      Note 0 < m - n          by 0 < p
        so n < m              by LESS_MONO_ADD
        or m = m - n + n      by SUB_ADD, n <= m
             = p + n          by m - n = p
             = n + p          by ADD_COMM
   Only-if part: m = n + p ==> m - n = p
        m - n
      = (n + p) - n           by m = n + p
      = p + n - n             by ADD_COMM
      = p                     by ADD_SUB
*)
val SUB_EQ_ADD = store_thm(
  "SUB_EQ_ADD",
  ``!p. 0 < p ==> !m n. (m - n = p) <=> (m = n + p)``,
  decide_tac);

(* Note: ADD_EQ_SUB |- !m n p. n <= p ==> ((m + n = p) <=> (m = p - n)) *)

(* Theorem: 0 < a /\ 0 < b /\ a < c /\ (a * b = c * d) ==> (d < b) *)
(* Proof:
   By contradiction, suppose b <= d.
   Since a * b <> 0         by MULT_EQ_0, 0 < a, 0 < b
      so d <> 0, or 0 < d   by MULT_EQ_0, a * b <> 0
     Now a * b <= a * d     by LE_MULT_LCANCEL, b <= d, a <> 0
     and a * d < c * d      by LT_MULT_LCANCEL, a < c, d <> 0
      so a * b < c * d      by LESS_EQ_LESS_TRANS
    This contradicts a * b = c * d.
*)
val MULT_EQ_LESS_TO_MORE = store_thm(
  "MULT_EQ_LESS_TO_MORE",
  ``!a b c d. 0 < a /\ 0 < b /\ a < c /\ (a * b = c * d) ==> (d < b)``,
  spose_not_then strip_assume_tac >>
  `b <= d` by decide_tac >>
  `0 < d` by decide_tac >>
  `a * b <= a * d` by rw[LE_MULT_LCANCEL] >>
  `a * d < c * d` by rw[LT_MULT_LCANCEL] >>
  decide_tac);

(* Theorem: 0 < c /\ 0 < d /\ a * b <= c * d /\ d < b ==> a < c *)
(* Proof:
   By contradiction, suppose c <= a.
   With d < b, which gives d <= b    by LESS_IMP_LESS_OR_EQ
   Thus c * d <= a * b               by LE_MONO_MULT2
     or a * b = c * d                by a * b <= c * d
   Note 0 < c /\ 0 < d               by given
    ==> a < c                        by MULT_EQ_LESS_TO_MORE
   This contradicts c <= a.

MULT_EQ_LESS_TO_MORE
|- !a b c d. 0 < a /\ 0 < b /\ a < c /\ a * b = c * d ==> d < b
             0 < d /\ 0 < c /\ d < b /\ d * c = b * a ==> a < c
*)
val LE_IMP_REVERSE_LT = store_thm(
  "LE_IMP_REVERSE_LT",
  ``!a b c d. 0 < c /\ 0 < d /\ a * b <= c * d /\ d < b ==> a < c``,
  spose_not_then strip_assume_tac >>
  `c <= a` by decide_tac >>
  `c * d <= a * b` by rw[LE_MONO_MULT2] >>
  `a * b = c * d` by decide_tac >>
  `a < c` by metis_tac[MULT_EQ_LESS_TO_MORE, MULT_COMM]);

(* ------------------------------------------------------------------------- *)
(* Exponential Theorems                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: n ** 0 = 1 *)
(* Proof: by EXP *)
val EXP_0 = store_thm(
  "EXP_0",
  ``!n. n ** 0 = 1``,
  rw_tac std_ss[EXP]);

(* Theorem: n ** 2 = n * n *)
(* Proof:
   n ** 2 = n * (n ** 1) = n * (n * (n ** 0)) = n * (n * 1) = n * n
   or n ** 2 = n * (n ** 1) = n * n  by EXP_1:  !n. (1 ** n = 1) /\ (n ** 1 = n)
*)
val EXP_2 = store_thm(
  "EXP_2",
  ``!n. n ** 2 = n * n``,
  metis_tac[EXP, TWO, EXP_1]);

(* Theorem: m <> 0 ==> m ** n <> 0 *)
(* Proof: by EXP_EQ_0 *)
val EXP_NONZERO = store_thm(
  "EXP_NONZERO",
  ``!m n. m <> 0 ==> m ** n <> 0``,
  metis_tac[EXP_EQ_0]);

(* Theorem: 0 < m ==> 0 < m ** n *)
(* Proof: by EXP_NONZERO *)
val EXP_POS = store_thm(
  "EXP_POS",
  ``!m n. 0 < m ==> 0 < m ** n``,
  rw[EXP_NONZERO]);

(* Theorem: 0 < m ==> ((n ** m = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1))) *)
(* Proof:
   If part: n ** m = n ==> n = 0 \/ n = 1
      By contradiction, assume n <> 0 /\ n <> 1.
      Then ?k. m = SUC k            by num_CASES, 0 < m
        so  n ** SUC k = n          by n ** m = n
        or  n * n ** k = n          by EXP
       ==>      n ** k = 1          by MULT_EQ_SELF, 0 < n
       ==>      n = 1 or k = 0      by EXP_EQ_1
       ==>      n = 1 or m = 1,
      These contradict n <> 1 and m <> 1.
   Only-if part: n ** 1 = n /\ 0 ** m = 0 /\ 1 ** m = 1
      These are true   by EXP_1, ZERO_EXP.
*)
val EXP_EQ_SELF = store_thm(
  "EXP_EQ_SELF",
  ``!n m. 0 < m ==> ((n ** m = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1)))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `m <> 0` by decide_tac >>
    `?k. m = SUC k` by metis_tac[num_CASES] >>
    `n * n ** k = n` by fs[EXP] >>
    `n ** k = 1` by metis_tac[MULT_EQ_SELF, NOT_ZERO_LT_ZERO] >>
    fs[EXP_EQ_1],
    rw[],
    rw[],
    rw[]
  ]);

(* Obtain a theorem *)
val EXP_LE = save_thm("EXP_LE", X_LE_X_EXP |> GEN ``x:num`` |> SPEC ``b:num`` |> GEN_ALL);
(* val EXP_LE = |- !n b. 0 < n ==> b <= b ** n: thm *)

(* Theorem: 1 < b /\ 1 < n ==> b < b ** n *)
(* Proof:
   By contradiction, assume ~(b < b ** n).
   Then b ** n <= b       by arithmetic
    But b <= b ** n       by EXP_LE, 0 < n
    ==> b ** n = b        by EQ_LESS_EQ
    ==> b = 1 or n = 0 or n = 1.
   All these contradict 1 < b and 1 < n.
*)
val EXP_LT = store_thm(
  "EXP_LT",
  ``!n b. 1 < b /\ 1 < n ==> b < b ** n``,
  spose_not_then strip_assume_tac >>
  `b <= b ** n` by rw[EXP_LE] >>
  `b ** n = b` by decide_tac >>
  rfs[EXP_EQ_SELF]);

(* Theorem: 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c) *)
(* Proof:
   Let d = m - n.
   Then 0 < d, and  m = n + d       by arithmetic
    and 0 < a ==> a ** n <> 0       by EXP_EQ_0
      a ** n * b
    = a ** (n + d) * c              by m = n + d
    = (a ** n * a ** d) * c         by EXP_ADD
    = a ** n * (a ** d * c)         by MULT_ASSOC
   The result follows               by MULT_LEFT_CANCEL
*)
val EXP_LCANCEL = store_thm(
  "EXP_LCANCEL",
  ``!a b c n m. 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c)``,
  rpt strip_tac >>
  `0 < m - n /\ (m = n + (m - n))` by decide_tac >>
  qabbrev_tac `d = m - n` >>
  `a ** n <> 0` by metis_tac[EXP_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[EXP_ADD, MULT_ASSOC, MULT_LEFT_CANCEL]);

(* Theorem: 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c) *)
(* Proof: by EXP_LCANCEL, MULT_COMM. *)
val EXP_RCANCEL = store_thm(
  "EXP_RCANCEL",
  ``!a b c n m. 0 < a /\ n < m /\ (b * a ** n = c * a ** m) ==> ?d. 0 < d /\ (b = c * a ** d)``,
  metis_tac[EXP_LCANCEL, MULT_COMM]);

(*
EXP_POS      |- !m n. 0 < m ==> 0 < m ** n
ONE_LT_EXP   |- !x y. 1 < x ** y <=> 1 < x /\ 0 < y
ZERO_LT_EXP  |- 0 < x ** y <=> 0 < x \/ (y = 0)
*)

(* Theorem: 0 < m ==> 1 <= m ** n *)
(* Proof:
   0 < m ==>  0 < m ** n      by EXP_POS
          or 1 <= m ** n      by arithmetic
*)
val ONE_LE_EXP = store_thm(
  "ONE_LE_EXP",
  ``!m n. 0 < m ==> 1 <= m ** n``,
  metis_tac[EXP_POS, DECIDE``!x. 0 < x <=> 1 <= x``]);

(* Theorem: EVEN n ==> !m. m ** n = (SQ m) ** (HALF n) *)
(* Proof:
     (SQ m) ** (HALF n)
   = (m ** 2) ** (HALF n)   by notation
   = m ** (2 * HALF n)      by EXP_EXP_MULT
   = m ** n                 by EVEN_HALF
*)
val EXP_EVEN = store_thm(
  "EXP_EVEN",
  ``!n. EVEN n ==> !m. m ** n = (SQ m) ** (HALF n)``,
  rpt strip_tac >>
  `(SQ m) ** (HALF n) = m ** (2 * HALF n)` by rw[EXP_EXP_MULT] >>
  `_ = m ** n` by rw[GSYM EVEN_HALF] >>
  rw[]);

(* Theorem: ODD n ==> !m. m ** n = m * (SQ m) ** (HALF n) *)
(* Proof:
     m * (SQ m) ** (HALF n)
   = m * (m ** 2) ** (HALF n)   by notation
   = m * m ** (2 * HALF n)      by EXP_EXP_MULT
   = m ** (SUC (2 * HALF n))    by EXP
   = m ** (2 * HALF n + 1)      by ADD1
   = m ** n                     by ODD_HALF
*)
val EXP_ODD = store_thm(
  "EXP_ODD",
  ``!n. ODD n ==> !m. m ** n = m * (SQ m) ** (HALF n)``,
  rpt strip_tac >>
  `m * (SQ m) ** (HALF n) = m * m ** (2 * HALF n)` by rw[EXP_EXP_MULT] >>
  `_ = m ** (2 * HALF n + 1)` by rw[GSYM EXP, ADD1] >>
  `_ = m ** n` by rw[GSYM ODD_HALF] >>
  rw[]);

(* An exponentiation identity *)
(* val EXP_THM = save_thm("EXP_THM", CONJ EXP_EVEN EXP_ODD); *)
(*
val EXP_THM = |- (!n. EVEN n ==> !m. m ** n = SQ m ** HALF n) /\
                  !n. ODD n ==> !m. m ** n = m * SQ m ** HALF n: thm
*)
(* Next is better *)

(* Theorem: m ** n = if n = 0 then 1 else if n = 1 then m else
            if EVEN n then (m * m) ** HALF n else m * ((m * m) ** (HALF n)) *)
(* Proof: mainly by EXP_EVEN, EXP_ODD. *)
Theorem EXP_THM:
  !m n. m ** n = if n = 0 then 1 else if n = 1 then m
                 else if EVEN n then (m * m) ** HALF n
                 else m * ((m * m) ** (HALF n))
Proof
  metis_tac[EXP_0, EXP_1, EXP_EVEN, EXP_ODD, EVEN_ODD]
QED

(* Theorem: m ** n =
            if n = 0 then 1
            else if EVEN n then (m * m) ** (HALF n) else m * (m * m) ** (HALF n) *)
(* Proof:
   If n = 0, to show:
      m ** 0 = 1, true                      by EXP_0
   If EVEN n, to show:
      m ** n = (m * m) ** (HALF n), true    by EXP_EVEN
   If ~EVEN n, ODD n, to show:              by EVEN_ODD
      m ** n = m * (m * m) ** HALF n, true  by EXP_ODD
*)
val EXP_EQN = store_thm(
  "EXP_EQN",
  ``!m n. m ** n =
         if n = 0 then 1
         else if EVEN n then (m * m) ** (HALF n) else m * (m * m) ** (HALF n)``,
  rw[] >-
  rw[Once EXP_EVEN] >>
  `ODD n` by metis_tac[EVEN_ODD] >>
  rw[Once EXP_ODD]);

(* Theorem: m ** n = if n = 0 then 1 else (if EVEN n then 1 else m) * (m * m) ** (HALF n) *)
(* Proof: by EXP_EQN *)
val EXP_EQN_ALT = store_thm(
  "EXP_EQN_ALT",
  ``!m n. m ** n =
         if n = 0 then 1
         else (if EVEN n then 1 else m) * (m * m) ** (HALF n)``,
  rw[Once EXP_EQN]);

(* Theorem: m ** n = (if n = 0 then 1 else (if EVEN n then 1 else m) * (m ** 2) ** HALF n) *)
(* Proof: by EXP_EQN_ALT, EXP_2 *)
val EXP_ALT_EQN = store_thm(
  "EXP_ALT_EQN",
  ``!m n. m ** n = (if n = 0 then 1 else (if EVEN n then 1 else m) * (m ** 2) ** HALF n)``,
  metis_tac[EXP_EQN_ALT, EXP_2]);

(* Theorem: 1 < m ==>
      (b ** n) MOD m = if (n = 0) then 1
                       else let result = (b * b) ** (HALF n) MOD m
                             in if EVEN n then result else (b * result) MOD m *)
(* Proof:
   This is to show:
   (1) 1 < m ==> b ** 0 MOD m = 1
         b ** 0 MOD m
       = 1 MOD m            by EXP_0
       = 1                  by ONE_MOD, 1 < m
   (2) EVEN n ==> b ** n MOD m = (b ** 2) ** HALF n MOD m
         b ** n MOD m
       = (b * b) ** HALF n MOD m    by EXP_EVEN
       = (b ** 2) ** HALF n MOD m   by EXP_2
   (3) ~EVEN n ==> b ** n MOD m = (b * (b ** 2) ** HALF n) MOD m
         b ** n MOD m
       = (b * (b * b) ** HALF n) MOD m      by EXP_ODD, EVEN_ODD
       = (b * (b ** 2) ** HALF n) MOD m     by EXP_2
*)
Theorem EXP_MOD_EQN:
  !b n m. 1 < m ==>
      ((b ** n) MOD m =
       if (n = 0) then 1
       else let result = (b * b) ** (HALF n) MOD m
             in if EVEN n then result else (b * result) MOD m)
Proof
  rw[]
  >- metis_tac[EXP_EVEN, EXP_2] >>
  metis_tac[EXP_ODD, EXP_2, EVEN_ODD]
QED

(* Pretty version of EXP_MOD_EQN, same pattern as EXP_EQN_ALT. *)

(* Theorem: 1 < m ==> b ** n MOD m =
           if n = 0 then 1 else
           ((if EVEN n then 1 else b) * ((SQ b ** HALF n) MOD m)) MOD m *)
(* Proof: by EXP_MOD_EQN *)
val EXP_MOD_ALT = store_thm(
  "EXP_MOD_ALT",
  ``!b n m. 1 < m ==> b ** n MOD m =
           if n = 0 then 1 else
           ((if EVEN n then 1 else b) * ((SQ b ** HALF n) MOD m)) MOD m``,
  rpt strip_tac >>
  imp_res_tac EXP_MOD_EQN >>
  last_x_assum (qspecl_then [`n`, `b`] strip_assume_tac) >>
  rw[]);

(* Theorem: x ** (y ** SUC n) = (x ** y) ** y ** n *)
(* Proof:
      x ** (y ** SUC n)
    = x ** (y * y ** n)     by EXP
    = (x ** y) ** (y ** n)  by EXP_EXP_MULT
*)
val EXP_EXP_SUC = store_thm(
  "EXP_EXP_SUC",
  ``!x y n. x ** (y ** SUC n) = (x ** y) ** y ** n``,
  rw[EXP, EXP_EXP_MULT]);

(* Theorem: 1 + n * m <= (1 + m) ** n *)
(* Proof:
   By induction on n.
   Base: 1 + 0 * m <= (1 + m) ** 0
        LHS = 1 + 0 * m = 1            by arithmetic
        RHS = (1 + m) ** 0 = 1         by EXP_0
        Hence true.
   Step: 1 + n * m <= (1 + m) ** n ==>
         1 + SUC n * m <= (1 + m) ** SUC n
          1 + SUC n * m
        = 1 + n * m + m                     by MULT
        <= (1 + m) ** n + m                 by induction hypothesis
        <= (1 + m) ** n + m * (1 + m) ** n  by EXP_POS
        <= (1 + m) * (1 + m) ** n           by RIGHT_ADD_DISTRIB
         = (1 + m) ** SUC n                 by EXP
*)
val EXP_LOWER_LE_LOW = store_thm(
  "EXP_LOWER_LE_LOW",
  ``!n m. 1 + n * m <= (1 + m) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[EXP_0] >>
  `0 < (1 + m) ** n` by rw[] >>
  `1 + SUC n * m = 1 + (n * m + m)` by rw[MULT] >>
  `_ = 1 + n * m + m` by decide_tac >>
  `m <= m * (1 + m) ** n` by rw[] >>
  `1 + SUC n * m <= (1 + m) ** n + m * (1 + m) ** n` by decide_tac >>
  `(1 + m) ** n + m * (1 + m) ** n = (1 + m) * (1 + m) ** n` by decide_tac >>
  `_ = (1 + m) ** SUC n` by rw[EXP] >>
  decide_tac);

(* Theorem: 0 < m /\ 1 < n ==> 1 + n * m < (1 + m) ** n *)
(* Proof:
   By induction on n.
   Base: 1 < 0 ==> 1 + 0 * m <= (1 + m) ** 0
        True since 1 < 0 = F.
   Step: 1 < n ==> 1 + n * m < (1 + m) ** n ==>
         1 < SUC n ==> 1 + SUC n * m < (1 + m) ** SUC n
      Note n <> 0, since SUC 0 = 1          by ONE
      If n = 1,
         Note m * m <> 0                    by MULT_EQ_0, m <> 0
           (1 + m) ** SUC 1
         = (1 + m) ** 2                     by TWO
         = 1 + 2 * m + m * m                by expansion
         > 1 + 2 * m                        by 0 < m * m
         = 1 + (SUC 1) * m
      If n <> 1, then 1 < n.
          1 + SUC n * m
        = 1 + n * m + m                     by MULT
         < (1 + m) ** n + m                 by induction hypothesis, 1 < n
        <= (1 + m) ** n + m * (1 + m) ** n  by EXP_POS
        <= (1 + m) * (1 + m) ** n           by RIGHT_ADD_DISTRIB
         = (1 + m) ** SUC n                 by EXP
*)
val EXP_LOWER_LT_LOW = store_thm(
  "EXP_LOWER_LT_LOW",
  ``!n m. 0 < m /\ 1 < n ==> 1 + n * m < (1 + m) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `n <> 0` by fs[] >>
  Cases_on `n = 1` >| [
    simp[] >>
    `(m + 1) ** 2 = (m + 1) * (m + 1)` by rw[GSYM EXP_2] >>
    `_ = m * m + 2 * m + 1` by decide_tac >>
    `0 < SQ m` by metis_tac[SQ_EQ_0, NOT_ZERO_LT_ZERO] >>
    decide_tac,
    `1 < n` by decide_tac >>
    `0 < (1 + m) ** n` by rw[] >>
    `1 + SUC n * m = 1 + (n * m + m)` by rw[MULT] >>
    `_ = 1 + n * m + m` by decide_tac >>
    `m <= m * (1 + m) ** n` by rw[] >>
    `1 + SUC n * m < (1 + m) ** n + m * (1 + m) ** n` by decide_tac >>
    `(1 + m) ** n + m * (1 + m) ** n = (1 + m) * (1 + m) ** n` by decide_tac >>
    `_ = (1 + m) ** SUC n` by rw[EXP] >>
    decide_tac
  ]);

(*
Note: EXP_LOWER_LE_LOW collects the first two terms of binomial expansion.
  but EXP_LOWER_LE_HIGH collects the last two terms of binomial expansion.
*)

(* Theorem: n * m ** (n - 1) + m ** n <= (1 + m) ** n *)
(* Proof:
   By induction on n.
   Base: 0 * m ** (0 - 1) + m ** 0 <= (1 + m) ** 0
        LHS = 0 * m ** (0 - 1) + m ** 0
            = 0 + 1                      by EXP_0
            = 1
           <= 1 = (1 + m) ** 0 = RHS     by EXP_0
   Step: n * m ** (n - 1) + m ** n <= (1 + m) ** n ==>
         SUC n * m ** (SUC n - 1) + m ** SUC n <= (1 + m) ** SUC n
        If n = 0,
           LHS = 1 * m ** 0 + m ** 1
               = 1 + m                   by EXP_0, EXP_1
               = (1 + m) ** 1 = RHS      by EXP_1
        If n <> 0,
           Then SUC (n - 1) = n          by n <> 0.
           LHS = SUC n * m ** (SUC n - 1) + m ** SUC n
               = (n + 1) * m ** n + m * m ** n     by EXP, ADD1
               = (n + 1 + m) * m ** n              by arithmetic
               = n * m ** n + (1 + m) * m ** n     by arithmetic
               = n * m ** SUC (n - 1) + (1 + m) * m ** n    by SUC (n - 1) = n
               = n * m * m ** (n - 1) + (1 + m) * m ** n    by EXP
               = m * (n * m ** (n - 1)) + (1 + m) * m ** n  by arithmetic
              <= (1 + m) * (n * m ** (n - 1)) + (1 + m) * m ** n   by m < 1 + m
               = (1 + m) * (n * m ** (n - 1) + m ** n)      by LEFT_ADD_DISTRIB
              <= (1 + m) * (1 + m) ** n                     by induction hypothesis
               = (1 + m) ** SUC n                           by EXP
*)
val EXP_LOWER_LE_HIGH = store_thm(
  "EXP_LOWER_LE_HIGH",
  ``!n m. n * m ** (n - 1) + m ** n <= (1 + m) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  Cases_on `n = 0` >-
  simp[EXP_0] >>
  `SUC (n - 1) = n` by decide_tac >>
  simp[EXP] >>
  simp[ADD1] >>
  `m * m ** n + (n + 1) * m ** n = (m + (n + 1)) * m ** n` by rw[LEFT_ADD_DISTRIB] >>
  `_ = (n + (m + 1)) * m ** n` by decide_tac >>
  `_ = n * m ** n + (m + 1) * m ** n` by rw[LEFT_ADD_DISTRIB] >>
  `_ = n * m ** SUC (n - 1) + (m + 1) * m ** n` by rw[] >>
  `_ = n * (m * m ** (n - 1)) + (m + 1) * m ** n` by rw[EXP] >>
  `_ = m * (n * m ** (n - 1)) + (m + 1) * m ** n` by decide_tac >>
  `m * (n * m ** (n - 1)) + (m + 1) * m ** n <= (m + 1) * (n * m ** (n - 1)) + (m + 1) * m ** n` by decide_tac >>
  qabbrev_tac `t = n * m ** (n - 1) + m ** n` >>
  `(m + 1) * (n * m ** (n - 1)) + (m + 1) * m ** n = (m + 1) * t` by rw[LEFT_ADD_DISTRIB, Abbr`t`] >>
  `t <= (m + 1) ** n` by metis_tac[ADD_COMM] >>
  `(m + 1) * t <= (m + 1) * (m + 1) ** n` by rw[] >>
  decide_tac);

(* Theorem: 1 < n ==> SUC n < 2 ** n *)
(* Proof:
   Note 1 + n < (1 + 1) ** n    by EXP_LOWER_LT_LOW, m = 1
     or SUC n < SUC 1 ** n      by ADD1
     or SUC n < 2 ** n          by TWO
*)
val SUC_X_LT_2_EXP_X = store_thm(
  "SUC_X_LT_2_EXP_X",
  ``!n. 1 < n ==> SUC n < 2 ** n``,
  rpt strip_tac >>
  `1 + n * 1 < (1 + 1) ** n` by rw[EXP_LOWER_LT_LOW] >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* DIVIDES Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m ==> m * (n DIV m) <= n /\ n < m * SUC (n DIV m) *)
(* Proof:
   Note n = n DIV m * m + n MOD m /\
        n MOD m < m                      by DIVISION
   Thus m * (n DIV m) <= n               by MULT_COMM
    and n < m * (n DIV m) + m
          = m * (n DIV m  + 1)           by LEFT_ADD_DISTRIB
          = m * SUC (n DIV m)            by ADD1
*)
val DIV_MULT_LESS_EQ = store_thm(
  "DIV_MULT_LESS_EQ",
  ``!m n. 0 < m ==> m * (n DIV m) <= n /\ n < m * SUC (n DIV m)``,
  ntac 3 strip_tac >>
  `(n = n DIV m * m + n MOD m) /\ n MOD m < m` by rw[DIVISION] >>
  `n < m * (n DIV m) + m` by decide_tac >>
  `m * (n DIV m) + m = m * (SUC (n DIV m))` by rw[ADD1] >>
  decide_tac);

(* Theorem: 0 < n ==> (m - n) DIV n = if m < n then 0 else (m DIV n - 1) *)
(* Proof:
   If m < n, then m - n = 0, so (m - n) DIV n = 0     by ZERO_DIV
   Otherwise, n <= m, and (m - n) DIV n = m DIV n - 1 by SUB_DIV
*)
val SUB_DIV_EQN = store_thm(
  "SUB_DIV_EQN",
  ``!m n. 0 < n ==> ((m - n) DIV n = if m < n then 0 else (m DIV n - 1))``,
  rw[SUB_DIV] >>
  `m - n = 0` by decide_tac >>
  rw[ZERO_DIV]);

(* Theorem: 0 < n ==> (m - n) MOD n = if m < n then 0 else m MOD n *)
(* Proof:
   If m < n, then m - n = 0, so (m - n) MOD n = 0     by ZERO_MOD
   Otherwise, n <= m, and (m - n) MOD n = m MOD n     by SUB_MOD
*)
val SUB_MOD_EQN = store_thm(
  "SUB_MOD_EQN",
  ``!m n. 0 < n ==> ((m - n) MOD n = if m < n then 0 else m MOD n)``,
  rw[SUB_MOD]);

(* Theorem: 0 < m /\ 0 < n /\ (n MOD m = 0) ==> n DIV (SUC m) < n DIV m *)
(* Proof:
   Note n = n DIV (SUC m) * (SUC m) + n MOD (SUC m)   by DIVISION
          = n DIV m * m + n MOD m                     by DIVISION
          = n DIV m * m                               by n MOD m = 0
   Thus n DIV SUC m * SUC m <= n DIV m * m            by arithmetic
   Note m < SUC m                                     by LESS_SUC
    and n DIV m <> 0, or 0 < n DIV m                  by DIV_MOD_EQ_0
   Thus n DIV (SUC m) < n DIV m                       by LE_IMP_REVERSE_LT
*)
val DIV_LT_SUC = store_thm(
  "DIV_LT_SUC",
  ``!m n. 0 < m /\ 0 < n /\ (n MOD m = 0) ==> n DIV (SUC m) < n DIV m``,
  rpt strip_tac >>
  `n DIV m * m = n` by metis_tac[DIVISION, ADD_0] >>
  `_ = n DIV (SUC m) * (SUC m) + n MOD (SUC m)` by metis_tac[DIVISION, SUC_POS] >>
  `n DIV SUC m * SUC m <= n DIV m * m` by decide_tac >>
  `m < SUC m` by decide_tac >>
  `0 < n DIV m` by metis_tac[DIV_MOD_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[LE_IMP_REVERSE_LT]);

(* Theorem: 0 < x /\ 0 < y /\ x < y ==> !n. 0 < n /\ (n MOD x = 0) ==> n DIV y < n DIV x *)
(* Proof:
   Note x < y ==> SUC x <= y                by arithmetic
   Thus n DIV y <= n DIV (SUC x)            by DIV_LE_MONOTONE_REVERSE
    But 0 < x /\ 0 < n /\ (n MOD x = 0)     by given
    ==> n DIV (SUC x) < n DIV x             by DIV_LT_SUC
   Hence n DIV y < n DIV x                  by inequalities
*)
val DIV_LT_MONOTONE_REVERSE = store_thm(
  "DIV_LT_MONOTONE_REVERSE",
  ``!x y. 0 < x /\ 0 < y /\ x < y ==> !n. 0 < n /\ (n MOD x = 0) ==> n DIV y < n DIV x``,
  rpt strip_tac >>
  `SUC x <= y` by decide_tac >>
  `n DIV y <= n DIV (SUC x)` by rw[DIV_LE_MONOTONE_REVERSE] >>
  `n DIV (SUC x) < n DIV x` by rw[DIV_LT_SUC] >>
  decide_tac);

(* Theorem: k <> 0 ==> (m divides n <=> (k * m) divides (k * n)) *)
(* Proof:
       m divides n
   <=> ?q. n = q * m             by divides_def
   <=> ?q. k * n = k * (q * m)   by EQ_MULT_LCANCEL, k <> 0
   <=> ?q. k * n = q * (k * m)   by MULT_ASSOC, MULT_COMM
   <=> (k * m) divides (k * n)   by divides_def
*)
val DIVIDES_MULTIPLE_IFF = store_thm(
  "DIVIDES_MULTIPLE_IFF",
  ``!m n k. k <> 0 ==> (m divides n <=> (k * m) divides (k * n))``,
  rpt strip_tac >>
  `m divides n <=> ?q. n = q * m` by rw[GSYM divides_def] >>
  `_ = ?q. (k * n = k * (q * m))` by rw[EQ_MULT_LCANCEL] >>
  metis_tac[divides_def, MULT_COMM, MULT_ASSOC]);

(* Theorem: 0 < n /\ n divides m ==> m = n * (m DIV n) *)
(* Proof:
   n divides m <=> m MOD n = 0    by DIVIDES_MOD_0
   m = (m DIV n) * n + (m MOD n)  by DIVISION
     = (m DIV n) * n              by above
     = n * (m DIV n)              by MULT_COMM
*)
val DIVIDES_FACTORS = store_thm(
  "DIVIDES_FACTORS",
  ``!m n. 0 < n /\ n divides m ==> (m = n * (m DIV n))``,
  metis_tac[DIVISION, DIVIDES_MOD_0, ADD_0, MULT_COMM]);

(* Theorem: 0 < n /\ n divides m ==> (m DIV n) divides m *)
(* Proof:
   By DIVIDES_FACTORS: m = (m DIV n) * n
   Hence (m DIV n) | m    by divides_def
*)
val DIVIDES_COFACTOR = store_thm(
  "DIVIDES_COFACTOR",
  ``!m n. 0 < n /\ n divides m ==> (m DIV n) divides m``,
  metis_tac[DIVIDES_FACTORS, divides_def]);

(* Theorem: n divides q ==> p * (q DIV n) = (p * q) DIV n *)
(* Proof:
   n divides q ==> q MOD n = 0               by DIVIDES_MOD_0
   p * q = p * ((q DIV n) * n + q MOD n)     by DIVISION
         = p * ((q DIV n) * n)               by ADD_0
         = p * (q DIV n) * n                 by MULT_ASSOC
         = p * (q DIV n) * n + 0             by ADD_0
   Hence (p * q) DIV n = p * (q DIV n)       by DIV_UNIQUE, 0 < n:
   |- !n k q. (?r. (k = q * n + r) /\ r < n) ==> (k DIV n = q)
*)
val MULTIPLY_DIV = store_thm(
  "MULTIPLY_DIV",
  ``!n p q. 0 < n /\ n divides q ==> (p * (q DIV n) = (p * q) DIV n)``,
  rpt strip_tac >>
  `q MOD n = 0` by rw[GSYM DIVIDES_MOD_0] >>
  `p * q = p * ((q DIV n) * n)` by metis_tac[DIVISION, ADD_0] >>
  `_ = p * (q DIV n) * n + 0` by rw[MULT_ASSOC] >>
  metis_tac[DIV_UNIQUE]);

(* Note: The condition: n divides q is important:
> EVAL ``5 * (10 DIV 3)``;
val it = |- 5 * (10 DIV 3) = 15: thm
> EVAL ``(5 * 10) DIV 3``;
val it = |- 5 * 10 DIV 3 = 16: thm
*)

(* Theorem: 0 < n /\ m divides n ==> !x. (x MOD n) MOD m = x MOD m *)
(* Proof:
   Note 0 < m                                   by ZERO_DIVIDES, 0 < n
   Given divides m n ==> ?q. n = q * m          by divides_def
   Since x = (x DIV n) * n + (x MOD n)          by DIVISION
           = (x DIV n) * (q * m) + (x MOD n)    by above
           = ((x DIV n) * q) * m + (x MOD n)    by MULT_ASSOC
   Hence     x MOD m
           = ((x DIV n) * q) * m + (x MOD n)) MOD m                by above
           = (((x DIV n) * q * m) MOD m + (x MOD n) MOD m) MOD m   by MOD_PLUS
           = (0 + (x MOD n) MOD m) MOD m                           by MOD_EQ_0
           = (x MOD n) MOD m                                       by ADD, MOD_MOD
*)
val DIVIDES_MOD_MOD = store_thm(
  "DIVIDES_MOD_MOD",
  ``!m n. 0 < n /\ m divides n ==> !x. (x MOD n) MOD m = x MOD m``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  `?q. n = q * m` by rw[GSYM divides_def] >>
  `x MOD m = ((x DIV n) * n + (x MOD n)) MOD m` by rw[GSYM DIVISION] >>
  `_ = (((x DIV n) * q) * m + (x MOD n)) MOD m` by rw[MULT_ASSOC] >>
  `_ = (((x DIV n) * q * m) MOD m + (x MOD n) MOD m) MOD m` by rw[MOD_PLUS] >>
  rw[MOD_EQ_0, MOD_MOD]);

(* Theorem: m divides n <=> (m * k) divides (n * k) *)
(* Proof: by divides_def and EQ_MULT_LCANCEL. *)
val DIVIDES_CANCEL = store_thm(
  "DIVIDES_CANCEL",
  ``!k. 0 < k ==> !m n. m divides n <=> (m * k) divides (n * k)``,
  rw[divides_def] >>
  `k <> 0` by decide_tac >>
  `!q. (q * m) * k = q * (m * k)` by rw_tac arith_ss[] >>
  metis_tac[EQ_MULT_LCANCEL, MULT_COMM]);

(* Theorem: m divides n ==> (k * m) divides (k * n) *)
(* Proof:
       m divides n
   ==> ?q. n = q * m              by divides_def
   So  k * n = k * (q * m)
             = (k * q) * m        by MULT_ASSOC
             = (q * k) * m        by MULT_COMM
             = q * (k * m)        by MULT_ASSOC
   Hence (k * m) divides (k * n)  by divides_def
*)
val DIVIDES_CANCEL_COMM = store_thm(
  "DIVIDES_CANCEL_COMM",
  ``!m n k. m divides n ==> (k * m) divides (k * n)``,
  metis_tac[MULT_ASSOC, MULT_COMM, divides_def]);

(* Theorem: 0 < n /\ 0 < m ==> !x. n divides x ==> ((m * x) DIV (m * n) = x DIV n) *)
(* Proof:
    n divides x ==> x = n * (x DIV n)              by DIVIDES_FACTORS
   or           m * x = (m * n) * (x DIV n)        by MULT_ASSOC
       n divides x
   ==> divides (m * n) (m * x)                     by DIVIDES_CANCEL_COMM
   ==> m * x = (m * n) * ((m * x) DIV (m * n))     by DIVIDES_FACTORS
   Equating expressions for m * x,
       (m * n) * (x DIV n) = (m * n) * ((m * x) DIV (m * n))
   or              x DIV n = (m * x) DIV (m * n)   by MULT_LEFT_CANCEL
*)
val DIV_COMMON_FACTOR = store_thm(
  "DIV_COMMON_FACTOR",
  ``!m n. 0 < n /\ 0 < m ==> !x. n divides x ==> ((m * x) DIV (m * n) = x DIV n)``,
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  `0 < m * n` by metis_tac[MULT_EQ_0] >>
  metis_tac[DIVIDES_CANCEL_COMM, DIVIDES_FACTORS, MULT_ASSOC, MULT_LEFT_CANCEL]);

(* Theorem: 0 < n /\ 0 < m /\ 0 < m DIV n /\
           n divides m /\ m divides x /\ (m DIV n) divides x ==>
           (x DIV (m DIV n) = n * (x DIV m)) *)
(* Proof:
     x DIV (m DIV n)
   = (n * x) DIV (n * (m DIV n))   by DIV_COMMON_FACTOR, (m DIV n) divides x, 0 < m DIV n.
   = (n * x) DIV m                 by DIVIDES_FACTORS, n divides m, 0 < n.
   = n * (x DIV m)                 by MULTIPLY_DIV, m divides x, 0 < m.
*)
val DIV_DIV_MULT = store_thm(
  "DIV_DIV_MULT",
  ``!m n x. 0 < n /\ 0 < m /\ 0 < m DIV n /\
           n divides m /\ m divides x /\ (m DIV n) divides x ==>
           (x DIV (m DIV n) = n * (x DIV m))``,
  metis_tac[DIV_COMMON_FACTOR, DIVIDES_FACTORS, MULTIPLY_DIV]);

(* ------------------------------------------------------------------------- *)
(* Basic Divisibility                                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: a little trick to make divisibility to mean equality. *)

(* Theorem: 0 < n /\ n < 2 * m ==> (m divides n <=> n = m) *)
(* Proof:
   If part: 0 < n /\ n < 2 * m /\ m divides n ==> n = m
      Note ?k. n = k * m           by divides_def
       Now k * m < 2 * m           by n < 2 * m
        so 0 < m /\ k < 2          by LT_MULT_LCANCEL
       and 0 < k                   by MULT
        so 1 <= k                  by LE_MULT_LCANCEL, 0 < m
      Thus k = 1, or n = m.
   Only-if part: true              by DIVIDES_REFL
*)
Theorem divides_iff_equal:
  !m n. 0 < n /\ n < 2 * m ==> (m divides n <=> n = m)
Proof
  rw[EQ_IMP_THM] >>
  `?k. n = k * m` by rw[GSYM divides_def] >>
  `0 < m /\ k < 2` by fs[LT_MULT_LCANCEL] >>
  `0 < k` by fs[] >>
  `k = 1` by decide_tac >>
  simp[]
QED

(* Theorem: 0 < m /\ n divides m ==> !t. m divides (t * n) <=> (m DIV n) divides t *)
(* Proof:
   Let k = m DIV n.
   Since m <> 0, n divides m ==> n <> 0       by ZERO_DIVIDES
    Thus m = k * n                            by DIVIDES_EQN, 0 < n
      so 0 < k                                by MULT, NOT_ZERO_LT_ZERO
   Hence k * n divides t * n <=> k divides t  by DIVIDES_CANCEL, 0 < k
*)
val dividend_divides_divisor_multiple = store_thm(
  "dividend_divides_divisor_multiple",
  ``!m n. 0 < m /\ n divides m ==> !t. m divides (t * n) <=> (m DIV n) divides t``,
  rpt strip_tac >>
  qabbrev_tac `k = m DIV n` >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `m = k * n` by rw[GSYM DIVIDES_EQN, Abbr`k`] >>
  `0 < k` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  metis_tac[DIVIDES_CANCEL]);

(* Theorem: 0 < n /\ m divides n ==> 0 < m *)
(* Proof:
   Since 0 < n means n <> 0,
    then m divides n ==> m <> 0     by ZERO_DIVIDES
      or 0 < m                      by NOT_ZERO_LT_ZERO
*)
val divisor_pos = store_thm(
  "divisor_pos",
  ``!m n. 0 < n /\ m divides n ==> 0 < m``,
  metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n /\ m divides n ==> 0 < m /\ m <= n *)
(* Proof:
   Since 0 < n /\ m divides n,
    then 0 < m           by divisor_pos
     and m <= n          by DIVIDES_LE
*)
val divides_pos = store_thm(
  "divides_pos",
  ``!m n. 0 < n /\ m divides n ==> 0 < m /\ m <= n``,
  metis_tac[divisor_pos, DIVIDES_LE]);

(* Theorem: 0 < n /\ m divides n ==> (n DIV (n DIV m) = m) *)
(* Proof:
   Since 0 < n /\ m divides n, 0 < m       by divisor_pos
   Hence n = (n DIV m) * m                 by DIVIDES_EQN, 0 < m
    Note 0 < n DIV m, otherwise contradicts 0 < n      by MULT
     Now n = m * (n DIV m)                 by MULT_COMM
           = m * (n DIV m) + 0             by ADD_0
   Therefore n DIV (n DIV m) = m           by DIV_UNIQUE
*)
val divide_by_cofactor = store_thm(
  "divide_by_cofactor",
  ``!m n. 0 < n /\ m divides n ==> (n DIV (n DIV m) = m)``,
  rpt strip_tac >>
  `0 < m` by metis_tac[divisor_pos] >>
  `n = (n DIV m) * m` by rw[GSYM DIVIDES_EQN] >>
  `0 < n DIV m` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  `n = m * (n DIV m) + 0` by metis_tac[MULT_COMM, ADD_0] >>
  metis_tac[DIV_UNIQUE]);

(* Theorem: 0 < n ==> !a b. a divides b ==> a divides b ** n *)
(* Proof:
   Since 0 < n, n = SUC m for some m.
    thus b ** n = b ** (SUC m)
                = b * b ** m    by EXP
   Now a divides b means
       ?k. b = k * a            by divides_def
    so b ** n
     = k * a * b ** m
     = (k * b ** m) * a         by MULT_COMM, MULT_ASSOC
   Hence a divides (b ** n)     by divides_def
*)
val divides_exp = store_thm(
  "divides_exp",
  ``!n. 0 < n ==> !a b. a divides b ==> a divides b ** n``,
  rw_tac std_ss[divides_def] >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `(q * a) ** n = q * a * (q * a) ** m` by rw[EXP] >>
  `_ = q * (q * a) ** m * a` by rw[MULT_COMM, MULT_ASSOC] >>
  metis_tac[]);

(* Note; converse need prime divisor:
DIVIDES_EXP_BASE |- !a b n. prime a /\ 0 < n ==> (a divides b <=> a divides b ** n)
Counter-example for a general base: 12 divides 36 = 6^2, but ~(12 divides 6)
*)

(* Better than: DIVIDES_ADD_1 |- !a b c. a divides b /\ a divides c ==> a divides b + c *)

(* Theorem: c divides a /\ c divides b ==> !h k. c divides (h * a + k * b) *)
(* Proof:
   Since c divides a, ?u. a = u * c     by divides_def
     and c divides b, ?v. b = v * c     by divides_def
      h * a + k * b
    = h * (u * c) + k * (v * c)         by above
    = h * u * c + k * v * c             by MULT_ASSOC
    = (h * u + k * v) * c               by RIGHT_ADD_DISTRIB
   Hence c divides (h * a + k * b)      by divides_def
*)
val divides_linear = store_thm(
  "divides_linear",
  ``!a b c. c divides a /\ c divides b ==> !h k. c divides (h * a + k * b)``,
  rw_tac std_ss[divides_def] >>
  metis_tac[RIGHT_ADD_DISTRIB, MULT_ASSOC]);

(* Theorem: c divides a /\ c divides b ==> !h k d. (h * a = k * b + d) ==> c divides d *)
(* Proof:
   If c = 0,
      0 divides a ==> a = 0     by ZERO_DIVIDES
      0 divides b ==> b = 0     by ZERO_DIVIDES
      Thus d = 0                by arithmetic
      and 0 divides 0           by ZERO_DIVIDES
   If c <> 0, 0 < c.
      c divides a ==> (a MOD c = 0)  by DIVIDES_MOD_0
      c divides b ==> (b MOD c = 0)  by DIVIDES_MOD_0
      Hence 0 = (h * a) MOD c        by MOD_TIMES2, ZERO_MOD
              = (0 + d MOD c) MOD c  by MOD_PLUS, MOD_TIMES2, ZERO_MOD
              = d MOD c              by MOD_MOD
      or c divides d                 by DIVIDES_MOD_0
*)
val divides_linear_sub = store_thm(
  "divides_linear_sub",
  ``!a b c. c divides a /\ c divides b ==> !h k d. (h * a = k * b + d) ==> c divides d``,
  rpt strip_tac >>
  Cases_on `c = 0` >| [
    `(a = 0) /\ (b = 0)` by metis_tac[ZERO_DIVIDES] >>
    `d = 0` by rw_tac arith_ss[] >>
    rw[],
    `0 < c` by decide_tac >>
    `(a MOD c = 0) /\ (b MOD c = 0)` by rw[GSYM DIVIDES_MOD_0] >>
    `0 = (h * a) MOD c` by metis_tac[MOD_TIMES2, ZERO_MOD, MULT_0] >>
    `_ = (0 + d MOD c) MOD c` by metis_tac[MOD_PLUS, MOD_TIMES2, ZERO_MOD, MULT_0] >>
    `_ = d MOD c` by rw[MOD_MOD] >>
    rw[DIVIDES_MOD_0]
  ]);

(* Theorem: 1 < p ==> !m n. p ** m divides p ** n <=> m <= n *)
(* Proof:
   Note p <> 0 /\ p <> 1                      by 1 < p

   If-part: p ** m divides p ** n ==> m <= n
      By contradiction, suppose n < m.
      Let d = m - n, then d <> 0              by n < m
      Note p ** m = p ** n * p ** d           by EXP_BY_ADD_SUB_LT
       and p ** n <> 0                        by EXP_EQ_0, p <> 0
       Now ?q. p ** n = q * p ** m            by divides_def
                      = q * p ** d * p ** n   by MULT_ASSOC_COMM
      Thus 1 * p ** n = q * p ** d * p ** n   by MULT_LEFT_1
        or          1 = q * p ** d            by MULT_RIGHT_CANCEL
       ==>     p ** d = 1                     by MULT_EQ_1
        or          d = 0                     by EXP_EQ_1, p <> 1
      This contradicts d <> 0.

  Only-if part: m <= n ==> p ** m divides p ** n
      Note p ** n = p ** m * p ** (n - m)     by EXP_BY_ADD_SUB_LE
      Thus p ** m divides p ** n              by divides_def, MULT_COMM
*)
val power_divides_iff = store_thm(
  "power_divides_iff",
  ``!p. 1 < p ==> !m n. p ** m divides p ** n <=> m <= n``,
  rpt strip_tac >>
  `p <> 0 /\ p <> 1` by decide_tac >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n < m /\ m - n <> 0` by decide_tac >>
    qabbrev_tac `d = m - n` >>
    `p ** m = p ** n * p ** d` by rw[EXP_BY_ADD_SUB_LT, Abbr`d`] >>
    `p ** n <> 0` by rw[EXP_EQ_0] >>
    `?q. p ** n = q * p ** m` by rw[GSYM divides_def] >>
    `_ = q * p ** d * p ** n` by metis_tac[MULT_ASSOC_COMM] >>
    `1 = q * p ** d` by metis_tac[MULT_RIGHT_CANCEL, MULT_LEFT_1] >>
    `p ** d = 1` by metis_tac[MULT_EQ_1] >>
    metis_tac[EXP_EQ_1],
    `p ** n = p ** m * p ** (n - m)` by rw[EXP_BY_ADD_SUB_LE] >>
    metis_tac[divides_def, MULT_COMM]
  ]);

(* Theorem: prime p ==> !m n. p ** m divides p ** n <=> m <= n *)
(* Proof: by power_divides_iff, ONE_LT_PRIME *)
val prime_power_divides_iff = store_thm(
  "prime_power_divides_iff",
  ``!p. prime p ==> !m n. p ** m divides p ** n <=> m <= n``,
  rw[power_divides_iff, ONE_LT_PRIME]);

(* Theorem: 0 < n /\ 1 < p ==> p divides p ** n *)
(* Proof:
   Note 0 < n <=> 1 <= n         by arithmetic
     so p ** 1 divides p ** n    by power_divides_iff
     or      p divides p ** n    by EXP_1
*)
val divides_self_power = store_thm(
  "divides_self_power",
  ``!n p. 0 < n /\ 1 < p ==> p divides p ** n``,
  metis_tac[power_divides_iff, EXP_1, DECIDE``0 < n <=> 1 <= n``]);

(* Theorem: a divides b /\ 0 < b /\ b < 2 * a ==> (b = a) *)
(* Proof:
   Note ?k. b = k * a      by divides_def
    and 0 < k              by MULT_EQ_0, 0 < b
    and k < 2              by LT_MULT_RCANCEL, k * a < 2 * a
   Thus k = 1              by 0 < k < 2
     or b = k * a = a      by arithmetic
*)
Theorem divides_eq_thm:
  !a b. a divides b /\ 0 < b /\ b < 2 * a ==> (b = a)
Proof
  rpt strip_tac >>
  `?k. b = k * a` by rw[GSYM divides_def] >>
  `0 < k` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
  `k < 2` by metis_tac[LT_MULT_RCANCEL] >>
  `k = 1` by decide_tac >>
  simp[]
QED

(* Idea: factor equals cofactor iff the number is a square of the factor. *)

(* Theorem: 0 < m /\ m divides n ==> (m = n DIV m <=> n = m ** 2) *)
(* Proof:
        n
      = n DIV m * m + n MOD m    by DIVISION, 0 < m
      = n DIV m * m + 0          by DIVIDES_MOD_0, m divides n
      = n DIV m * m              by ADD_0
   If m = n DIV m,
     then n = m * m = m ** 2     by EXP_2
   If n = m ** 2,
     then n = m * m              by EXP_2
       so m = n DIV m            by EQ_MULT_RCANCEL
*)
Theorem factor_eq_cofactor:
  !m n. 0 < m /\ m divides n ==> (m = n DIV m <=> n = m ** 2)
Proof
  rw[EQ_IMP_THM] >>
  `n = n DIV m * m + n MOD m` by rw[DIVISION] >>
  `_ = m * m + 0` by metis_tac[DIVIDES_MOD_0] >>
  simp[]
QED

(* Theorem alias *)
Theorem euclid_prime = gcdTheory.P_EUCLIDES;
(* |- !p a b. prime p /\ p divides a * b ==> p divides a \/ p divides b *)

(* Theorem alias *)
Theorem euclid_coprime = gcdTheory.L_EUCLIDES;
(* |- !a b c. coprime a b /\ b divides a * c ==> b divides c *)

(* ------------------------------------------------------------------------- *)
(* Modulo Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Idea: eliminate modulus n when a MOD n = b MOD n. *)

(* Theorem: 0 < n /\ b <= a ==> (a MOD n = b MOD n <=> ?c. a = b + c * n) *)
(* Proof:
   If part: a MOD n = b MOD n ==> ?c. a = b + c * n
      Note ?c. a = c * n + b MOD n       by MOD_EQN
       and b = (b DIV n) * n + b MOD n   by DIVISION
      Let q = b DIV n,
      Then q * n <= c * n                by LE_ADD_RCANCEL, b <= a
           a
         = c * n + (b - q * n)           by above
         = b + (c * n - q * n)           by arithmetic, q * n <= c * n
         = b + (c - q) * n               by RIGHT_SUB_DISTRIB
      Take (c - q) as c.
   Only-if part: (b + c * n) MOD n = b MOD n
      This is true                       by MOD_TIMES
*)
Theorem MOD_MOD_EQN:
  !n a b. 0 < n /\ b <= a ==> (a MOD n = b MOD n <=> ?c. a = b + c * n)
Proof
  rw[EQ_IMP_THM] >| [
    `?c. a = c * n + b MOD n` by metis_tac[MOD_EQN] >>
    `b = (b DIV n) * n + b MOD n` by rw[DIVISION] >>
    qabbrev_tac `q = b DIV n` >>
    `q * n <= c * n` by metis_tac[LE_ADD_RCANCEL] >>
    `a = b + (c * n - q * n)` by decide_tac >>
    `_ = b + (c - q) * n` by decide_tac >>
    metis_tac[],
    simp[]
  ]
QED

(* Idea: a convenient form of MOD_PLUS. *)

(* Theorem: 0 < n ==> (x + y) MOD n = (x + y MOD n) MOD n *)
(* Proof:
   Let q = y DIV n, r = y MOD n.
   Then y = q * n + r              by DIVISION, 0 < n
        (x + y) MOD n
      = (x + (q * n + r)) MOD n    by above
      = (q * n + (x + r)) MOD n    by arithmetic
      = (x + r) MOD n              by MOD_PLUS, MOD_EQ_0
*)
Theorem MOD_PLUS2:
  !n x y. 0 < n ==> (x + y) MOD n = (x + y MOD n) MOD n
Proof
  rpt strip_tac >>
  `y = (y DIV n) * n + y MOD n` by metis_tac[DIVISION] >>
  simp[]
QED

(* Theorem: If n > 0, a MOD n = b MOD n ==> (a - b) MOD n = 0 *)
(* Proof:
   a = (a DIV n)*n + (a MOD n)   by DIVISION
   b = (b DIV n)*n + (b MOD n)   by DIVISION
   Hence  a - b = ((a DIV n) - (b DIV n))* n
                = a multiple of n
   Therefore (a - b) MOD n = 0.
*)
val MOD_EQ_DIFF = store_thm(
  "MOD_EQ_DIFF",
  ``!n a b. 0 < n /\ (a MOD n = b MOD n) ==> ((a - b) MOD n = 0)``,
  rpt strip_tac >>
  `a = a DIV n * n + a MOD n` by metis_tac[DIVISION] >>
  `b = b DIV n * n + b MOD n` by metis_tac[DIVISION] >>
  `a - b = (a DIV n - b DIV n) * n` by rw_tac arith_ss[] >>
  metis_tac[MOD_EQ_0]);
(* Note: The reverse is true only when a >= b:
         (a-b) MOD n = 0 cannot imply a MOD n = b MOD n *)

(* Theorem: if n > 0, a >= b, then (a - b) MOD n = 0 <=> a MOD n = b MOD n *)
(* Proof:
         (a-b) MOD n = 0
   ==>   n divides (a-b)   by MOD_0_DIVIDES
   ==>   (a-b) = k*n       for some k by divides_def
   ==>       a = b + k*n   need b <= a to apply arithmeticTheory.SUB_ADD
   ==> a MOD n = b MOD n   by arithmeticTheory.MOD_TIMES

   The converse is given by MOD_EQ_DIFF.
*)
val MOD_EQ = store_thm(
  "MOD_EQ",
  ``!n a b. 0 < n /\ b <= a ==> (((a - b) MOD n = 0) <=> (a MOD n = b MOD n))``,
  rw[EQ_IMP_THM] >| [
    `?k. a - b = k * n` by metis_tac[DIVIDES_MOD_0, divides_def] >>
    `a = k*n + b` by rw_tac arith_ss[] >>
    metis_tac[MOD_TIMES],
    metis_tac[MOD_EQ_DIFF]
  ]);
(* Both MOD_EQ_DIFF and MOD_EQ are required in MOD_MULT_LCANCEL *)

(* Idea: equality exchange for MOD without negative. *)

(* Theorem: b < n /\ c < n ==>
              ((a + b) MOD n = (c + d) MOD n <=>
               (a + (n - c)) MOD n = (d + (n - b)) MOD n) *)
(* Proof:
   Note 0 < n                  by b < n or c < n
   Let x = n - b, y = n - c.
   The goal is: (a + b) MOD n = (c + d) MOD n <=>
                (a + y) MOD n = (d + x) MOD n
   Note n = b + x, n = c + y   by arithmetic
       (a + b) MOD n = (c + d) MOD n
   <=> (a + b + x + y) MOD n = (c + d + x + y) MOD n   by ADD_MOD
   <=> (a + y + n) MOD n = (d + x + n) MOD n           by above
   <=> (a + y) MOD n = (d + x) MOD n                   by ADD_MOD

   For integers, this is simply: a + b = c + d <=> a - c = b - d.
*)
Theorem mod_add_eq_sub:
  !n a b c d. b < n /\ c < n ==>
              ((a + b) MOD n = (c + d) MOD n <=>
               (a + (n - c)) MOD n = (d + (n - b)) MOD n)
Proof
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `n = b + (n - b)` by decide_tac >>
  `n = c + (n - c)` by decide_tac >>
  qabbrev_tac `x = n - b` >>
  qabbrev_tac `y = n - c` >>
  `a + b + x + y = a + y + n` by decide_tac >>
  `c + d + x + y = d + x + n` by decide_tac >>
  `(a + b) MOD n = (c + d) MOD n <=>
    (a + b + x + y) MOD n = (c + d + x + y) MOD n` by simp[ADD_MOD] >>
  fs[ADD_MOD]
QED

(* Idea: generalise above equality exchange for MOD. *)

(* Theorem: 0 < n ==>
            ((a + b) MOD n = (c + d) MOD n <=>
             (a + (n - c MOD n)) MOD n = (d + (n - b MOD n)) MOD n) *)
(* Proof:
   Let b' = b MOD n, c' = c MOD n.
   Note b' < n            by MOD_LESS, 0 < n
    and c' < n            by MOD_LESS, 0 < n
        (a + b) MOD n = (c + d) MOD n
    <=> (a + b') MOD n = (d + c') MOD n              by MOD_PLUS2
    <=> (a + (n - c')) MOD n = (d + (n - b')) MOD n  by mod_add_eq_sub
*)
Theorem mod_add_eq_sub_eq:
  !n a b c d. 0 < n ==>
              ((a + b) MOD n = (c + d) MOD n <=>
               (a + (n - c MOD n)) MOD n = (d + (n - b MOD n)) MOD n)
Proof
  rpt strip_tac >>
  `b MOD n < n /\ c MOD n < n` by rw[] >>
  `(a + b) MOD n = (a + b MOD n) MOD n` by simp[Once MOD_PLUS2] >>
  `(c + d) MOD n = (d + c MOD n) MOD n` by simp[Once MOD_PLUS2] >>
  prove_tac[mod_add_eq_sub]
QED

(*
MOD_EQN is a trick to eliminate MOD:
|- !n. 0 < n ==> !a b. a MOD n = b <=> ?c. a = c * n + b /\ b < n
*)

(* Idea: remove MOD for divides: need b divides (a MOD n) ==> b divides a. *)

(* Theorem: 0 < n /\ b divides n /\ b divides (a MOD n) ==> b divides a *)
(* Proof:
   Note ?k. n = k * b                    by divides_def, b divides n
    and ?h. a MOD n = h * b              by divides_def, b divides (a MOD n)
    and ?c. a = c * n + h * b            by MOD_EQN, 0 < n
              = c * (k * b) + h * b      by above
              = (c * k + h) * b          by RIGHT_ADD_DISTRIB
   Thus b divides a                      by divides_def
*)
Theorem mod_divides:
  !n a b. 0 < n /\ b divides n /\ b divides (a MOD n) ==> b divides a
Proof
  rpt strip_tac >>
  `?k. n = k * b` by rw[GSYM divides_def] >>
  `?h. a MOD n = h * b` by rw[GSYM divides_def] >>
  `?c. a = c * n + h * b` by metis_tac[MOD_EQN] >>
  `_ = (c * k + h) * b` by simp[] >>
  metis_tac[divides_def]
QED

(* Idea: include converse of mod_divides. *)

(* Theorem: 0 < n /\ b divides n ==> (b divides (a MOD n) <=> b divides a) *)
(* Proof:
   If part: b divides n /\ b divides a MOD n ==> b divides a
      This is true                       by mod_divides
   Only-if part: b divides n /\ b divides a ==> b divides a MOD n
   Note ?c. a = c * n + a MOD n          by MOD_EQN, 0 < n
              = c * n + 1 * a MOD n      by MULT_LEFT_1
   Thus b divides (a MOD n)              by divides_linear_sub
*)
Theorem mod_divides_iff:
  !n a b. 0 < n /\ b divides n ==> (b divides (a MOD n) <=> b divides a)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[mod_divides] >>
  `?c. a = c * n + a MOD n` by metis_tac[MOD_EQN] >>
  metis_tac[divides_linear_sub, MULT_LEFT_1]
QED

(* An application of
DIVIDES_MOD_MOD:
|- !m n. 0 < n /\ m divides n ==> !x. x MOD n MOD m = x MOD m
Let x = a linear combination.
(linear) MOD n MOD m = linear MOD m
change n to a product m * n, for z = linear MOD (m * n).
(linear) MOD (m * n) MOD g = linear MOD g
z MOD g = linear MOD g
requires: g divides (m * n)
*)

(* Idea: generalise for MOD equation: a MOD n = b. Need c divides a ==> c divides b. *)

(* Theorem: 0 < n /\ a MOD n = b /\ c divides n /\ c divides a ==> c divides b *)
(* Proof:
   Note 0 < c                      by ZERO_DIVIDES, c divides n, 0 < n.
       a MOD n = b
   ==> (a MOD n) MOD c = b MOD c
   ==>         a MOD c = b MOD c   by DIVIDES_MOD_MOD, 0 < n, c divides n
   But a MOD c = 0                 by DIVIDES_MOD_0, c divides a
    so b MOD c = 0, or c divides b by DIVIDES_MOD_0, 0 < c
*)
Theorem mod_divides_divides:
  !n a b c. 0 < n /\ a MOD n = b /\ c divides n /\ c divides a ==> c divides b
Proof
  simp[mod_divides_iff]
QED

(* Idea: include converse of mod_divides_divides. *)

(* Theorem: 0 < n /\ a MOD n = b /\ c divides n ==> (c divides a <=> c divides b) *)
(* Proof:
   If part: c divides a ==> c divides b, true  by mod_divides_divides
   Only-if part: c divides b ==> c divides a
      Note b = a MOD n, so this is true        by mod_divides
*)
Theorem mod_divides_divides_iff:
  !n a b c. 0 < n /\ a MOD n = b /\ c divides n ==> (c divides a <=> c divides b)
Proof
  simp[mod_divides_iff]
QED

(* Idea: divides across MOD: from a MOD n = b MOD n to c divides a ==> c divides b. *)

(* Theorem: 0 < n /\ a MOD n = b MOD n /\ c divides n /\ c divides a ==> c divides b *)
(* Proof:
   Note c divides (b MOD n)        by mod_divides_divides
     so c divides b                by mod_divides
   Or, simply have both            by mod_divides_iff
*)
Theorem mod_eq_divides:
  !n a b c. 0 < n /\ a MOD n = b MOD n /\ c divides n /\ c divides a ==> c divides b
Proof
  metis_tac[mod_divides_iff]
QED

(* Idea: include converse of mod_eq_divides. *)

(* Theorem: 0 < n /\ a MOD n = b MOD n /\ c divides n ==> (c divides a <=> c divides b) *)
(* Proof:
   If part: c divides a ==> c divides b, true  by mod_eq_divides, a MOD n = b MOD n
   Only-if: c divides b ==> c divides a, true  by mod_eq_divides, b MOD n = a MOD n
*)
Theorem mod_eq_divides_iff:
  !n a b c. 0 < n /\ a MOD n = b MOD n /\ c divides n ==> (c divides a <=> c divides b)
Proof
  metis_tac[mod_eq_divides]
QED

(* Idea: special cross-multiply equality of MOD (m * n) implies pair equality:
         from (m * a) MOD (m * n) = (n * b) MOD (m * n) to a = n /\ b = m. *)

(* Theorem: coprime m n /\ 0 < a /\ a < 2 * n /\ 0 < b /\ b < 2 * m /\
            (m * a) MOD (m * n) = (n * b) MOD (m * n) ==> (a = n /\ b = m) *)
(* Proof:
   Given (m * a) MOD (m * n) = (n * b) MOD (m * n)
   Note n divides (n * b)      by factor_divides
    and n divides (m * n)      by factor_divides
     so n divides (m * a)      by mod_eq_divides
    ==> n divides a            by euclid_coprime, MULT_COMM
   Thus a = n                  by divides_iff_equal
   Also m divides (m * a)      by factor_divides
    and m divides (m * n)      by factor_divides
     so m divides (n * b)      by mod_eq_divides
    ==> m divides b            by euclid_coprime, GCD_SYM
   Thus b = m                  by divides_iff_equal
*)
Theorem mod_mult_eq_mult:
  !m n a b. coprime m n /\ 0 < a /\ a < 2 * n /\ 0 < b /\ b < 2 * m /\
            (m * a) MOD (m * n) = (n * b) MOD (m * n) ==> (a = n /\ b = m)
Proof
  ntac 5 strip_tac >>
  `0 < m /\ 0 < n` by decide_tac >>
  `0 < m * n` by rw[] >>
  strip_tac >| [
    `n divides (n * b)` by rw[DIVIDES_MULTIPLE] >>
    `n divides (m * n)` by rw[DIVIDES_MULTIPLE] >>
    `n divides (m * a)` by metis_tac[mod_eq_divides] >>
    `n divides a` by metis_tac[euclid_coprime, MULT_COMM] >>
    metis_tac[divides_iff_equal],
    `m divides (m * a)` by rw[DIVIDES_MULTIPLE] >>
    `m divides (m * n)` by metis_tac[DIVIDES_REFL, DIVIDES_MULTIPLE, MULT_COMM] >>
    `m divides (n * b)` by metis_tac[mod_eq_divides] >>
    `m divides b` by metis_tac[euclid_coprime, GCD_SYM] >>
    metis_tac[divides_iff_equal]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Even and Odd Parity.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n /\ EVEN m ==> EVEN (m ** n) *)
(* Proof:
   Since EVEN m, m MOD 2 = 0       by EVEN_MOD2
       EVEN (m ** n)
   <=> (m ** n) MOD 2 = 0          by EVEN_MOD2
   <=> (m MOD 2) ** n MOD 2 = 0    by EXP_MOD, 0 < 2
   ==> 0 ** n MOD 2 = 0            by above
   <=> 0 MOD 2 = 0                 by ZERO_EXP, n <> 0
   <=> 0 = 0                       by ZERO_MOD
   <=> T
*)
(* Note: arithmeticTheory.EVEN_EXP  |- !m n. 0 < n /\ EVEN m ==> EVEN (m ** n) *)

(* Theorem: !m n. 0 < n /\ ODD m ==> ODD (m ** n) *)
(* Proof:
   Since ODD m, m MOD 2 = 1        by ODD_MOD2
       ODD (m ** n)
   <=> (m ** n) MOD 2 = 1          by ODD_MOD2
   <=> (m MOD 2) ** n MOD 2 = 1    by EXP_MOD, 0 < 2
   ==> 1 ** n MOD 2 = 1            by above
   <=> 1 MOD 2 = 1                 by EXP_1, n <> 0
   <=> 1 = 1                       by ONE_MOD, 1 < 2
   <=> T
*)
val ODD_EXP = store_thm(
  "ODD_EXP",
  ``!m n. 0 < n /\ ODD m ==> ODD (m ** n)``,
  rw[ODD_MOD2] >>
  `n <> 0 /\ 0 < 2` by decide_tac >>
  metis_tac[EXP_MOD, EXP_1, ONE_MOD]);

(* Theorem: 0 < n ==> !m. (EVEN m <=> EVEN (m ** n)) /\ (ODD m <=> ODD (m ** n)) *)
(* Proof:
   First goal: EVEN m <=> EVEN (m ** n)
     If part: EVEN m ==> EVEN (m ** n), true by EVEN_EXP
     Only-if part: EVEN (m ** n) ==> EVEN m.
        By contradiction, suppose ~EVEN m.
        Then ODD m                           by EVEN_ODD
         and ODD (m ** n)                    by ODD_EXP
          or ~EVEN (m ** n)                  by EVEN_ODD
        This contradicts EVEN (m ** n).
   Second goal: ODD m <=> ODD (m ** n)
     Just mirror the reasoning of first goal.
*)
val power_parity = store_thm(
  "power_parity",
  ``!n. 0 < n ==> !m. (EVEN m <=> EVEN (m ** n)) /\ (ODD m <=> ODD (m ** n))``,
  metis_tac[EVEN_EXP, ODD_EXP, ODD_EVEN]);

(* Theorem: 0 < n ==> EVEN (2 ** n) *)
(* Proof:
       EVEN (2 ** n)
   <=> (2 ** n) MOD 2 = 0          by EVEN_MOD2
   <=> (2 MOD 2) ** n MOD 2 = 0    by EXP_MOD
   <=> 0 ** n MOD 2 = 0            by DIVMOD_ID, 0 < 2
   <=> 0 MOD 2 = 0                 by ZERO_EXP, n <> 0
   <=> 0 = 0                       by ZERO_MOD
   <=> T
*)
Theorem EXP_2_EVEN:  !n. 0 < n ==> EVEN (2 ** n)
Proof rw[EVEN_MOD2, ZERO_EXP]
QED
(* Michael's proof by induction
val EXP_2_EVEN = store_thm(
  "EXP_2_EVEN",
  ``!n. 0 < n ==> EVEN (2 ** n)``,
  Induct >> rw[EXP, EVEN_DOUBLE]);
 *)

(* Theorem: 0 < n ==> ODD (2 ** n - 1) *)
(* Proof:
   Since 0 < 2 ** n                  by EXP_POS, 0 < 2
      so 1 <= 2 ** n                 by LESS_EQ
    thus SUC (2 ** n - 1)
       = 2 ** n - 1 + 1              by ADD1
       = 2 ** n                      by SUB_ADD, 1 <= 2 ** n
     and EVEN (2 ** n)               by EXP_2_EVEN
   Hence ODD (2 ** n - 1)            by EVEN_ODD_SUC
*)
val EXP_2_PRE_ODD = store_thm(
  "EXP_2_PRE_ODD",
  ``!n. 0 < n ==> ODD (2 ** n - 1)``,
  rpt strip_tac >>
  `0 < 2 ** n` by rw[EXP_POS] >>
  `SUC (2 ** n - 1) = 2 ** n` by decide_tac >>
  metis_tac[EXP_2_EVEN, EVEN_ODD_SUC]);

(* ------------------------------------------------------------------------- *)
(* Modulo Inverse                                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Euclid's Lemma] A prime a divides product iff the prime a divides factor.
            [in MOD notation] For prime p, x*y MOD p = 0 <=> x MOD p = 0 or y MOD p = 0 *)
(* Proof:
   The if part is already in P_EUCLIDES:
   !p a b. prime p /\ divides p (a * b) ==> p divides a \/ p divides b
   Convert the divides to MOD by DIVIDES_MOD_0.
   The only-if part is:
   (1) divides p x ==> divides p (x * y)
   (2) divides p y ==> divides p (x * y)
   Both are true by DIVIDES_MULT: !a b c. a divides b ==> a divides (b * c).
   The symmetry of x and y can be taken care of by MULT_COMM.
*)
val EUCLID_LEMMA = store_thm(
  "EUCLID_LEMMA",
  ``!p x y. prime p ==> (((x * y) MOD p = 0) <=> (x MOD p = 0) \/ (y MOD p = 0))``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  rw[GSYM DIVIDES_MOD_0, EQ_IMP_THM] >>
  metis_tac[P_EUCLIDES, DIVIDES_MULT, MULT_COMM]);

(* Theorem: [Cancellation Law for MOD p]
   For prime p, if x MOD p <> 0,
      (x*y) MOD p = (x*z) MOD p ==> y MOD p = z MOD p *)
(* Proof:
       (x*y) MOD p = (x*z) MOD p
   ==> ((x*y) - (x*z)) MOD p = 0   by MOD_EQ_DIFF
   ==>       (x*(y-z)) MOD p = 0   by arithmetic LEFT_SUB_DISTRIB
   ==>           (y-z) MOD p = 0   by EUCLID_LEMMA, x MOD p <> 0
   ==>               y MOD p = z MOD p    if z <= y

   Since this theorem is symmetric in y, z,
   First prove the theorem assuming z <= y,
   then use the same proof for y <= z.
*)
Theorem MOD_MULT_LCANCEL:
  !p x y z. prime p /\ (x * y) MOD p = (x * z) MOD p /\ x MOD p <> 0 ==> y MOD p = z MOD p
Proof
  rpt strip_tac >>
  `!a b c. c <= b /\ (a * b) MOD p = (a * c) MOD p /\ a MOD p <> 0 ==> b MOD p = c MOD p` by
  (rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `(a * b - a * c) MOD p = 0` by rw[MOD_EQ_DIFF] >>
  `(a * (b - c)) MOD p = 0` by rw[LEFT_SUB_DISTRIB] >>
  metis_tac[EUCLID_LEMMA, MOD_EQ]) >>
  Cases_on `z <= y` >-
  metis_tac[] >>
  `y <= z` by decide_tac >>
  metis_tac[]
QED

(* Theorem: prime p /\ (y * x) MOD p = (z * x) MOD p /\ x MOD p <> 0 ==>
            y MOD p = z MOD p *)
(* Proof: by MOD_MULT_LCANCEL, MULT_COMM *)
Theorem MOD_MULT_RCANCEL:
  !p x y z. prime p /\ (y * x) MOD p = (z * x) MOD p /\ x MOD p <> 0 ==>
            y MOD p = z MOD p
Proof
  metis_tac[MOD_MULT_LCANCEL, MULT_COMM]
QED

(* Theorem: For prime p, 0 < x < p ==> ?y. 0 < y /\ y < p /\ (y*x) MOD p = 1 *)
(* Proof:
       0 < x < p
   ==> ~ divides p x                    by NOT_LT_DIVIDES
   ==> gcd p x = 1                      by gcdTheory.PRIME_GCD
   ==> ?k q. k * x = q * p + 1          by gcdTheory.LINEAR_GCD
   ==> k*x MOD p = (q*p + 1) MOD p      by arithmetic
   ==> k*x MOD p = 1                    by MOD_MULT, 1 < p.
   ==> (k MOD p)*(x MOD p) MOD p = 1    by MOD_TIMES2
   ==> ((k MOD p) * x) MOD p = 1        by LESS_MOD, x < p.
   Now   k MOD p < p                    by MOD_LESS
   and   0 < k MOD p since (k*x) MOD p <> 0  (by 1 <> 0)
                       and x MOD p <> 0      (by ~ divides p x)
                                        by EUCLID_LEMMA
   Hence take y = k MOD p, then 0 < y < p.
*)
val MOD_MULT_INV_EXISTS = store_thm(
  "MOD_MULT_INV_EXISTS",
  ``!p x. prime p /\ 0 < x /\ x < p ==> ?y. 0 < y /\ y < p /\ ((y * x) MOD p = 1)``,
  rpt strip_tac >>
  `0 < p /\ 1 < p` by metis_tac[PRIME_POS, ONE_LT_PRIME] >>
  `gcd p x = 1` by metis_tac[PRIME_GCD, NOT_LT_DIVIDES] >>
  `?k q. k * x = q * p + 1` by metis_tac[LINEAR_GCD, NOT_ZERO_LT_ZERO] >>
  `1 = (k * x) MOD p` by metis_tac[MOD_MULT] >>
  `_ = ((k MOD p) * (x MOD p)) MOD p` by metis_tac[MOD_TIMES2] >>
  `0 < k MOD p` by
  (`1 <> 0` by decide_tac >>
  `x MOD p <> 0` by metis_tac[DIVIDES_MOD_0, NOT_LT_DIVIDES] >>
  `k MOD p <> 0` by metis_tac[EUCLID_LEMMA, MOD_MOD] >>
  decide_tac) >>
  metis_tac[MOD_LESS, LESS_MOD]);

(* Convert this theorem into MUL_INV_DEF *)

(* Step 1: move ?y forward by collecting quantifiers *)
val lemma = prove(
  ``!p x. ?y. prime p /\ 0 < x /\ x < p ==> 0 < y /\ y < p /\ ((y * x) MOD p = 1)``,
  metis_tac[MOD_MULT_INV_EXISTS]);

(* Step 2: apply SKOLEM_THM *)
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
val MOD_MULT_INV_DEF = new_specification(
  "MOD_MULT_INV_DEF",
  ["MOD_MULT_INV"], (* avoid MOD_MULT_INV_EXISTS: thm *)
  SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(*
> val MOD_MULT_INV_DEF =
    |- !p x.
         prime p /\ 0 < x /\ x < p ==>
         0 < MOD_MULT_INV p x /\ MOD_MULT_INV p x < p /\
         ((MOD_MULT_INV p x * x) MOD p = 1) : thm
*)

(* ------------------------------------------------------------------------- *)
(* FACTOR Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ~ prime n ==> n has a proper prime factor p *)
(* Proof: apply PRIME_FACTOR:
   !n. n <> 1 ==> ?p. prime p /\ p divides n : thm
*)
val PRIME_FACTOR_PROPER = store_thm(
  "PRIME_FACTOR_PROPER",
  ``!n. 1 < n /\ ~prime n ==> ?p. prime p /\ p < n /\ (p divides n)``,
  rpt strip_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  `?p. prime p /\ p divides n` by metis_tac[PRIME_FACTOR] >>
  `~(n < p)` by metis_tac[NOT_LT_DIVIDES] >>
  Cases_on `n = p` >-
  full_simp_tac std_ss[] >>
  `p < n` by decide_tac >>
  metis_tac[]);

(* Theorem: If p divides n, then there is a (p ** m) that maximally divides n. *)
(* Proof:
   Consider the set s = {k | p ** k divides n}
   Since p IN s, s <> {}           by MEMBER_NOT_EMPTY
   For k IN s, p ** k n divides ==> p ** k <= n    by DIVIDES_LE
   Since ?z. n <= p ** z           by EXP_ALWAYS_BIG_ENOUGH
   p ** k <= p ** z
        k <= z                     by EXP_BASE_LE_MONO
     or k < SUC z
   Hence s SUBSET count (SUC z)    by SUBSET_DEF
   and FINITE s                    by FINITE_COUNT, SUBSET_FINITE
   Let m = MAX_SET s
   Then p ** m n divides           by MAX_SET_DEF
   Let q = n DIV (p ** m)
   i.e.  n = q * (p ** m)
   If p divides q, then q = t * p
   or n = t * p * (p ** m)
        = t * (p * p ** m)         by MULT_ASSOC
        = t * p ** SUC m           by EXP
   i.e. p ** SUC m  divides n, or SUC m IN s.
   Since m < SUC m                 by LESS_SUC
   This contradicts the maximal property of m.
*)
val FACTOR_OUT_POWER = store_thm(
  "FACTOR_OUT_POWER",
  ``!n p. 0 < n /\ 1 < p /\ p divides n ==> ?m. (p ** m) divides n /\ ~(p divides (n DIV (p ** m)))``,
  rpt strip_tac >>
  `p <= n` by rw[DIVIDES_LE] >>
  `1 < n` by decide_tac >>
  qabbrev_tac `s = {k | (p ** k) divides n }` >>
  qexists_tac `MAX_SET s` >>
  qabbrev_tac `m = MAX_SET s` >>
  `!k. k IN s <=> (p ** k) divides n` by rw[Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY, EXP_1] >>
  `?z. n <= p ** z` by rw[EXP_ALWAYS_BIG_ENOUGH] >>
  `!k. k IN s ==> k <= z` by metis_tac[DIVIDES_LE, EXP_BASE_LE_MONO, LESS_EQ_TRANS] >>
  `!k. k <= z ==> k < SUC z` by decide_tac >>
  `s SUBSET (count (SUC z))` by metis_tac[IN_COUNT, SUBSET_DEF, LESS_EQ_TRANS] >>
  `FINITE s` by metis_tac[FINITE_COUNT, SUBSET_FINITE] >>
  `m IN s /\ !y. y IN s ==> y <= m` by metis_tac[MAX_SET_DEF] >>
  `(p ** m) divides n` by metis_tac[] >>
  rw[] >>
  spose_not_then strip_assume_tac >>
  `0 < p` by decide_tac >>
  `0 < p ** m` by rw[EXP_POS] >>
  `n = (p ** m) * (n DIV (p ** m))` by rw[DIVIDES_FACTORS] >>
  `?q. n DIV (p ** m) = q * p` by rw[GSYM divides_def] >>
  `n = q * p ** SUC m` by metis_tac[MULT_COMM, MULT_ASSOC, EXP] >>
  `SUC m <= m` by metis_tac[divides_def] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

(* binomial_add: same as SUM_SQUARED *)

(* Theorem: (a + b) ** 2 = a ** 2 + b ** 2 + 2 * a * b *)
(* Proof:
     (a + b) ** 2
   = (a + b) * (a + b)                   by EXP_2
   = a * (a + b) + b * (a + b)           by RIGHT_ADD_DISTRIB
   = (a * a + a * b) + (b * a + b * b)   by LEFT_ADD_DISTRIB
   = a * a + b * b + 2 * a * b           by arithmetic
   = a ** 2 + b ** 2 + 2 * a * b         by EXP_2
*)
Theorem binomial_add:
  !a b. (a + b) ** 2 = a ** 2 + b ** 2 + 2 * a * b
Proof
  rpt strip_tac >>
  `(a + b) ** 2 = (a + b) * (a + b)` by simp[] >>
  `_ = a * a + b * b + 2 * a * b` by decide_tac >>
  simp[]
QED

(* Theorem: b <= a ==> ((a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b) *)
(* Proof:
   If b = 0,
      RHS = a ** 2 + 0 ** 2 - 2 * a * 0
          = a ** 2 + 0 - 0
          = a ** 2
          = (a - 0) ** 2
          = LHS
   If b <> 0,
      Then b * b <= a * b                      by LE_MULT_RCANCEL, b <> 0
       and b * b <= 2 * a * b

      LHS = (a - b) ** 2
          = (a - b) * (a - b)                  by EXP_2
          = a * (a - b) - b * (a - b)          by RIGHT_SUB_DISTRIB
          = (a * a - a * b) - (b * a - b * b)  by LEFT_SUB_DISTRIB
          = a * a - (a * b + (a * b - b * b))  by SUB_PLUS
          = a * a - (a * b + a * b - b * b)    by LESS_EQ_ADD_SUB, b * b <= a * b
          = a * a - (2 * a * b - b * b)
          = a * a + b * b - 2 * a * b          by SUB_SUB, b * b <= 2 * a * b
          = a ** 2 + b ** 2 - 2 * a * b        by EXP_2
          = RHS
*)
Theorem binomial_sub:
  !a b. b <= a ==> ((a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b)
Proof
  rpt strip_tac >>
  Cases_on `b = 0` >-
  simp[] >>
  `b * b <= a * b` by rw[] >>
  `b * b <= 2 * a * b` by decide_tac >>
  `(a - b) ** 2 = (a - b) * (a - b)` by simp[] >>
  `_ = a * a + b * b - 2 * a * b` by decide_tac >>
  rw[]
QED

(* Theorem: 2 * a * b <= a ** 2 + b ** 2 *)
(* Proof:
   If a = b,
      LHS = 2 * a * a
          = a * a + a * a
          = a ** 2 + a ** 2        by EXP_2
          = RHS
   If a < b, then 0 < b - a.
      Thus 0 < (b - a) * (b - a)   by MULT_EQ_0
        or 0 < (b - a) ** 2        by EXP_2
        so 0 < b ** 2 + a ** 2 - 2 * b * a   by binomial_sub, a <= b
       ==> 2 * a * b < a ** 2 + b ** 2       due to 0 < RHS.
   If b < a, then 0 < a - b.
      Thus 0 < (a - b) * (a - b)   by MULT_EQ_0
        or 0 < (a - b) ** 2        by EXP_2
        so 0 < a ** 2 + b ** 2 - 2 * a * b   by binomial_sub, b <= a
       ==> 2 * a * b < a ** 2 + b ** 2       due to 0 < RHS.
*)
Theorem binomial_means:
  !a b. 2 * a * b <= a ** 2 + b ** 2
Proof
  rpt strip_tac >>
  Cases_on `a = b` >-
  simp[] >>
  Cases_on `a < b` >| [
    `b - a <> 0` by decide_tac >>
    `(b - a) * (b - a) <> 0` by metis_tac[MULT_EQ_0] >>
    `(b - a) * (b - a) = (b - a) ** 2` by simp[] >>
    `_ = b ** 2 + a ** 2 - 2 * b * a` by rw[binomial_sub] >>
    decide_tac,
    `a - b <> 0` by decide_tac >>
    `(a - b) * (a - b) <> 0` by metis_tac[MULT_EQ_0] >>
    `(a - b) * (a - b) = (a - b) ** 2` by simp[] >>
    `_ = a ** 2 + b ** 2 - 2 * a * b` by rw[binomial_sub] >>
    decide_tac
  ]
QED

(* Theorem: b <= a ==> (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2 *)
(* Proof:
   Note (a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b     by binomial_sub
    and 2 * a * b <= a ** 2 + b ** 2                   by binomial_means
   Thus (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2
*)
Theorem binomial_sub_sum:
  !a b. b <= a ==> (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2
Proof
  rpt strip_tac >>
  imp_res_tac binomial_sub >>
  assume_tac (binomial_means |> SPEC_ALL) >>
  decide_tac
QED

(* Theorem: b <= a ==> ((a - b) ** 2 + 4 * a * b = (a + b) ** 2) *)
(* Proof:
   Note: 2 * a * b <= a ** 2 + b ** 2          by binomial_means, as [1]
     (a - b) ** 2 + 4 * a * b
   = a ** 2 + b ** 2 - 2 * a * b + 4 * a * b   by binomial_sub, b <= a
   = a ** 2 + b ** 2 + 4 * a * b - 2 * a * b   by SUB_ADD, [1]
   = a ** 2 + b ** 2 + 2 * a * b
   = (a + b) ** 2                              by binomial_add
*)
Theorem binomial_sub_add:
  !a b. b <= a ==> ((a - b) ** 2 + 4 * a * b = (a + b) ** 2)
Proof
  rpt strip_tac >>
  `2 * a * b <= a ** 2 + b ** 2` by rw[binomial_means] >>
  `(a - b) ** 2 + 4 * a * b = a ** 2 + b ** 2 - 2 * a * b + 4 * a * b` by rw[binomial_sub] >>
  `_ = a ** 2 + b ** 2 + 4 * a * b - 2 * a * b` by decide_tac >>
  `_ = a ** 2 + b ** 2 + 2 * a * b` by decide_tac >>
  `_ = (a + b) ** 2` by rw[binomial_add] >>
  decide_tac
QED

(* Theorem: a ** 2 - b ** 2 = (a - b) * (a + b) *)
(* Proof:
     a ** 2 - b ** 2
   = a * a - b * b                       by EXP_2
   = a * a + a * b - a * b - b * b       by ADD_SUB
   = a * a + a * b - (b * a + b * b)     by SUB_PLUS
   = a * (a + b) - b * (a + b)           by LEFT_ADD_DISTRIB
   = (a - b) * (a + b)                   by RIGHT_SUB_DISTRIB
*)
Theorem difference_of_squares:
  !a b. a ** 2 - b ** 2 = (a - b) * (a + b)
Proof
  rpt strip_tac >>
  `a ** 2 - b ** 2 = a * a - b * b` by simp[] >>
  `_ = a * a + a * b - a * b - b * b` by decide_tac >>
  decide_tac
QED

(* Theorem: a * a - b * b = (a - b) * (a + b) *)
(* Proof:
     a * a - b * b
   = a ** 2 - b ** 2       by EXP_2
   = (a + b) * (a - b)     by difference_of_squares
*)
Theorem difference_of_squares_alt:
  !a b. a * a - b * b = (a - b) * (a + b)
Proof
  rw[difference_of_squares]
QED

(* binomial_2: same as binomial_add, or SUM_SQUARED *)

(* Theorem: (m + n) ** 2 = m ** 2 + n ** 2 + 2 * m * n *)
(* Proof:
     (m + n) ** 2
   = (m + n) * (m + n)                 by EXP_2
   = m * m + n * m + m * n + n * n     by LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB
   = m ** 2 + n ** 2 + 2 * m * n       by EXP_2
*)
val binomial_2 = store_thm(
  "binomial_2",
  ``!m n. (m + n) ** 2 = m ** 2 + n ** 2 + 2 * m * n``,
  rpt strip_tac >>
  `(m + n) ** 2 = (m + n) * (m + n)` by rw[] >>
  `_ = m * m + n * m + m * n + n * n` by decide_tac >>
  `_ = m ** 2 + n ** 2 + 2 * m * n` by rw[] >>
  decide_tac);

(* Obtain a corollary *)
val SUC_SQ = save_thm("SUC_SQ",
    binomial_2 |> SPEC ``1`` |> SIMP_RULE (srw_ss()) [GSYM SUC_ONE_ADD]);
(* val SUC_SQ = |- !n. SUC n ** 2 = SUC (n ** 2) + TWICE n: thm *)

(* Theorem: m <= n ==> SQ m <= SQ n *)
(* Proof:
   Since m * m <= n * n    by LE_MONO_MULT2
      so  SQ m <= SQ n     by notation
*)
val SQ_LE = store_thm(
  "SQ_LE",
  ``!m n. m <= n ==> SQ m <= SQ n``,
  rw[]);

(* Theorem: EVEN n /\ prime n <=> n = 2 *)
(* Proof:
   If part: EVEN n /\ prime n ==> n = 2
      EVEN n ==> n MOD 2 = 0       by EVEN_MOD2
             ==> 2 divides n       by DIVIDES_MOD_0, 0 < 2
             ==> n = 2             by prime_def, 2 <> 1
   Only-if part: n = 2 ==> EVEN n /\ prime n
      Note EVEN 2                  by EVEN_2
       and prime 2                 by prime_2
*)
(* Proof:
   EVEN n ==> n MOD 2 = 0    by EVEN_MOD2
          ==> 2 divides n    by DIVIDES_MOD_0, 0 < 2
          ==> n = 2          by prime_def, 2 <> 1
*)
Theorem EVEN_PRIME:
  !n. EVEN n /\ prime n <=> n = 2
Proof
  rw[EQ_IMP_THM] >>
  `0 < 2 /\ 2 <> 1` by decide_tac >>
  `2 divides n` by rw[DIVIDES_MOD_0, GSYM EVEN_MOD2] >>
  metis_tac[prime_def]
QED

(* Theorem: prime n /\ n <> 2 ==> ODD n *)
(* Proof:
   By contradiction, suppose ~ODD n.
   Then EVEN n                        by EVEN_ODD
    but EVEN n /\ prime n ==> n = 2   by EVEN_PRIME
   This contradicts n <> 2.
*)
val ODD_PRIME = store_thm(
  "ODD_PRIME",
  ``!n. prime n /\ n <> 2 ==> ODD n``,
  metis_tac[EVEN_PRIME, EVEN_ODD]);

(* Theorem: prime p ==> 2 <= p *)
(* Proof: by ONE_LT_PRIME *)
val TWO_LE_PRIME = store_thm(
  "TWO_LE_PRIME",
  ``!p. prime p ==> 2 <= p``,
  metis_tac[ONE_LT_PRIME, DECIDE``1 < n <=> 2 <= n``]);

(* Theorem: ~prime 4 *)
(* Proof:
   Note 4 = 2 * 2      by arithmetic
     so 2 divides 4    by divides_def
   thus ~prime 4       by primes_def
*)
Theorem NOT_PRIME_4:
  ~prime 4
Proof
  rpt strip_tac >>
  `4 = 2 * 2` by decide_tac >>
  `4 <> 2 /\ 4 <> 1 /\ 2 <> 1` by decide_tac >>
  metis_tac[prime_def, divides_def]
QED

(* Theorem: prime n /\ prime m ==> (n divides m <=> (n = m)) *)
(* Proof:
   If part: prime n /\ prime m /\ n divides m ==> (n = m)
      Note prime n
       ==> n <> 1           by NOT_PRIME_1
      With n divides m      by given
       and prime m          by given
      Thus n = m            by prime_def
   Only-if part; prime n /\ prime m /\ (n = m) ==> n divides m
      True as m divides m   by DIVIDES_REFL
*)
val prime_divides_prime = store_thm(
  "prime_divides_prime",
  ``!n m. prime n /\ prime m ==> (n divides m <=> (n = m))``,
  rw[EQ_IMP_THM] >>
  `n <> 1` by metis_tac[NOT_PRIME_1] >>
  metis_tac[prime_def]);
(* This is: dividesTheory.prime_divides_only_self;
|- !m n. prime m /\ prime n /\ m divides n ==> (m = n)
*)

(* Theorem: 0 < m /\ 1 < n /\ (!p. prime p /\ p divides m ==> (p MOD n = 1)) ==> (m MOD n = 1) *)
(* Proof:
   By complete induction on m.
   If m = 1, trivially true               by ONE_MOD
   If m <> 1,
      Then ?p. prime p /\ p divides m     by PRIME_FACTOR, m <> 1
       and ?q. m = q * p                  by divides_def
       and q divides m                    by divides_def, MULT_COMM
      In order to apply induction hypothesis,
      Show: q < m
            Note q <= m                   by DIVIDES_LE, 0 < m
             But p <> 1                   by NOT_PRIME_1
            Thus q <> m                   by MULT_RIGHT_1, EQ_MULT_LCANCEL, m <> 0
             ==> q < m
      Show: 0 < q
            Since m = q * p  and m <> 0   by above
            Thus q <> 0, or 0 < q         by MULT
      Show: !p. prime p /\ p divides q ==> (p MOD n = 1)
            If p divides q, and q divides m,
            Then p divides m              by DIVIDES_TRANS
             ==> p MOD n = 1              by implication

      Hence q MOD n = 1                   by induction hypothesis
        and p MOD n = 1                   by implication
        Now 0 < n                         by 1 < n
            m MDO n
          = (q * p) MOD n                 by m = q * p
          = (q MOD n * p MOD n) MOD n     by MOD_TIMES2, 0 < n
          = (1 * 1) MOD n                 by above
          = 1                             by MULT_RIGHT_1, ONE_MOD
*)
val ALL_PRIME_FACTORS_MOD_EQ_1 = store_thm(
  "ALL_PRIME_FACTORS_MOD_EQ_1",
  ``!m n. 0 < m /\ 1 < n /\ (!p. prime p /\ p divides m ==> (p MOD n = 1)) ==> (m MOD n = 1)``,
  completeInduct_on `m` >>
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[] >>
  `?p. prime p /\ p divides m` by rw[PRIME_FACTOR] >>
  `?q. m = q * p` by rw[GSYM divides_def] >>
  `q divides m` by metis_tac[divides_def, MULT_COMM] >>
  `p <> 1` by metis_tac[NOT_PRIME_1] >>
  `m <> 0` by decide_tac >>
  `q <> m` by metis_tac[MULT_RIGHT_1, EQ_MULT_LCANCEL] >>
  `q <= m` by metis_tac[DIVIDES_LE] >>
  `q < m` by decide_tac >>
  `q <> 0` by metis_tac[MULT] >>
  `0 < q` by decide_tac >>
  `!p. prime p /\ p divides q ==> (p MOD n = 1)` by metis_tac[DIVIDES_TRANS] >>
  `q MOD n = 1` by rw[] >>
  `p MOD n = 1` by rw[] >>
  `0 < n` by decide_tac >>
  metis_tac[MOD_TIMES2, MULT_RIGHT_1, ONE_MOD]);

(* Theorem: prime p /\ 0 < n ==> !b. p divides (b ** n) <=> p divides b *)
(* Proof:
   If part: p divides b ** n ==> p divides b
      By induction on n.
      Base: 0 < 0 ==> p divides b ** 0 ==> p divides b
         True by 0 < 0 = F.
      Step: 0 < n ==> p divides b ** n ==> p divides b ==>
            0 < SUC n ==> p divides b ** SUC n ==> p divides b
         If n = 0,
              b ** SUC 0
            = b ** 1                  by ONE
            = b                       by EXP_1
            so p divides b.
         If n <> 0, 0 < n.
              b ** SUC n
            = b * b ** n              by EXP
            Thus p divides b,
              or p divides (b ** n)   by P_EUCLIDES
            For the latter case,
                 p divides b          by induction hypothesis, 0 < n

   Only-if part: p divides b ==> p divides b ** n
      Since n <> 0, ?m. n = SUC m     by num_CASES
        and b ** n
          = b ** SUC m
          = b * b ** m                by EXP
       Thus p divides b ** n          by DIVIDES_MULTIPLE, MULT_COMM
*)
val prime_divides_power = store_thm(
  "prime_divides_power",
  ``!p n. prime p /\ 0 < n ==> !b. p divides (b ** n) <=> p divides b``,
  rw[EQ_IMP_THM] >| [
    Induct_on `n` >-
    rw[] >>
    rpt strip_tac >>
    Cases_on `n = 0` >-
    metis_tac[ONE, EXP_1] >>
    `0 < n` by decide_tac >>
    `b ** SUC n = b * b ** n` by rw[EXP] >>
    metis_tac[P_EUCLIDES],
    `n <> 0` by decide_tac >>
    `?m. n = SUC m` by metis_tac[num_CASES] >>
    `b ** SUC m = b * b ** m` by rw[EXP] >>
    metis_tac[DIVIDES_MULTIPLE, MULT_COMM]
  ]);

(* Theorem: prime p ==> !n. 0 < n ==> p divides p ** n *)
(* Proof:
   Since p divides p        by DIVIDES_REFL
      so p divides p ** n   by prime_divides_power, 0 < n
*)
val prime_divides_self_power = store_thm(
  "prime_divides_self_power",
  ``!p. prime p ==> !n. 0 < n ==> p divides p ** n``,
  rw[prime_divides_power, DIVIDES_REFL]);

(* Theorem: prime p ==> !b n m. 0 < m /\ (b ** n = p ** m) ==> ?k. (b = p ** k) /\ (k * n = m) *)
(* Proof:
   Note 1 < p                    by ONE_LT_PRIME
     so p <> 0, 0 < p, p <> 1    by arithmetic
   also m <> 0                   by 0 < m
   Thus p ** m <> 0              by EXP_EQ_0, p <> 0
    and p ** m <> 1              by EXP_EQ_1, p <> 1, m <> 0
    ==> n <> 0, 0 < n            by EXP, b ** n = p ** m <> 1
   also b <> 0, 0 < b            by EXP_EQ_0, b ** n = p ** m <> 0, 0 < n

   Step 1: show p divides b.
   Note p divides (p ** m)       by prime_divides_self_power, 0 < m
     so p divides (b ** n)       by given, b ** n = p ** m
     or p divides b              by prime_divides_power, 0 < b

   Step 2: express b = q * p ** u  where ~(p divides q).
   Note 1 < p /\ 0 < b /\ p divides b
    ==> ?u. p ** u divides b /\ ~(p divides b DIV p ** u)  by FACTOR_OUT_POWER
    Let q = b DIV p ** u, v = u * n.
   Since p ** u <> 0             by EXP_EQ_0, p <> 0
      so b = q * p ** u          by DIVIDES_EQN, 0 < p ** u
         p ** m
       = (q * p ** u) ** n       by b = q * p ** u
       = q ** n * (p ** u) ** n  by EXP_BASE_MULT
       = q ** n * p ** (u * n)   by EXP_EXP_MULT
       = q ** n * p ** v         by v = u * n

   Step 3: split cases
   If v = m,
      Then q ** n * p ** m = 1 * p ** m     by above
        or          q ** n = 1              by EQ_MULT_RCANCEL, p ** m <> 0
      giving             q = 1              by EXP_EQ_1, 0 < n
      Thus b = p ** u                       by b = q * p ** u
      Take k = u, the result follows.

   If v < m,
      Let d = m - v.
      Then 0 < d /\ (m = d + v)             by arithmetic
       and p ** m = p ** d * p ** v         by EXP_ADD
      Note p ** v <> 0                      by EXP_EQ_0, p <> 0
           q ** n * p ** v = p ** d * p ** v
       ==>          q ** n = p ** d         by EQ_MULT_RCANCEL, p ** v <> 0
      Now p divides p ** d                  by prime_divides_self_power, 0 < d
       so p divides q ** n                  by above, q ** n = p ** d
      ==> p divides q                       by prime_divides_power, 0 < n
      This contradicts ~(p divides q)

   If m < v,
      Let d = v - m.
      Then 0 < d /\ (v = d + m)             by arithmetic
       and q ** n * p ** v
         = q ** n * (p ** d * p ** m)       by EXP_ADD
         = q ** n * p ** d * p ** m         by MULT_ASSOC
         = 1 * p ** m                       by arithmetic, b ** n = p ** m
      Hence q ** n * p ** d = 1             by EQ_MULT_RCANCEL, p ** m <> 0
        ==> (q ** n = 1) /\ (p ** d = 1)    by MULT_EQ_1
        But p ** d <> 1                     by EXP_EQ_1, 0 < d
       This contradicts p ** d = 1.
*)
Theorem power_eq_prime_power:
  !p. prime p ==>
      !b n m. 0 < m /\ (b ** n = p ** m) ==> ?k. (b = p ** k) /\ (k * n = m)
Proof
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `m <> 0 /\ 0 < p /\ p <> 0 /\ p <> 1` by decide_tac >>
  `p ** m <> 0` by rw[EXP_EQ_0] >>
  `p ** m <> 1` by rw[EXP_EQ_1] >>
  `n <> 0` by metis_tac[EXP] >>
  `0 < n /\ 0 < p ** m` by decide_tac >>
  `b <> 0` by metis_tac[EXP_EQ_0] >>
  `0 < b` by decide_tac >>
  `p divides (p ** m)` by rw[prime_divides_self_power] >>
  `p divides b` by metis_tac[prime_divides_power] >>
  `?u. p ** u divides b /\ ~(p divides b DIV p ** u)` by metis_tac[FACTOR_OUT_POWER] >>
  qabbrev_tac `q = b DIV p ** u` >>
  `p ** u <> 0` by rw[EXP_EQ_0] >>
  `0 < p ** u` by decide_tac >>
  `b = q * p ** u` by rw[GSYM DIVIDES_EQN, Abbr`q`] >>
  `q ** n * p ** (u * n) = p ** m` by metis_tac[EXP_BASE_MULT, EXP_EXP_MULT] >>
  qabbrev_tac `v = u * n` >>
  Cases_on `v = m` >| [
    `p ** m = 1 * p ** m` by simp[] >>
    `q ** n = 1` by metis_tac[EQ_MULT_RCANCEL] >>
    `q = 1` by metis_tac[EXP_EQ_1] >>
    `b = p ** u` by simp[] >>
    metis_tac[],
    Cases_on `v < m` >| [
      `?d. d = m - v` by rw[] >>
      `0 < d /\ (m = d + v)` by rw[] >>
      `p ** m = p ** d * p ** v` by rw[EXP_ADD] >>
      `p ** v <> 0` by metis_tac[EXP_EQ_0] >>
      `q ** n = p ** d` by metis_tac[EQ_MULT_RCANCEL] >>
      `p divides p ** d` by metis_tac[prime_divides_self_power] >>
      metis_tac[prime_divides_power],
      `m < v` by decide_tac >>
      `?d. d = v - m` by rw[] >>
      `0 < d /\ (v = d + m)` by rw[] >>
      `d <> 0` by decide_tac >>
      `q ** n * p ** d * p ** m = p ** m` by metis_tac[EXP_ADD, MULT_ASSOC] >>
      `_ = 1 * p ** m` by rw[] >>
      `q ** n * p ** d = 1` by metis_tac[EQ_MULT_RCANCEL] >>
      `(q ** n = 1) /\ (p ** d = 1)` by metis_tac[MULT_EQ_1] >>
      metis_tac[EXP_EQ_1]
    ]
  ]
QED

(* Theorem: 1 < n ==> !m. (n ** m = n) <=> (m = 1) *)
(* Proof:
   If part: n ** m = n ==> m = 1
      Note n = n ** 1           by EXP_1
        so n ** m = n ** 1      by given
        or      m = 1           by EXP_BASE_INJECTIVE, 1 < n
   Only-if part: m = 1 ==> n ** m = n
      This is true              by EXP_1
*)
val POWER_EQ_SELF = store_thm(
  "POWER_EQ_SELF",
  ``!n. 1 < n ==> !m. (n ** m = n) <=> (m = 1)``,
  metis_tac[EXP_BASE_INJECTIVE, EXP_1]);

(* Theorem: k < HALF n <=> k + 1 < n - k *)
(* Proof:
   If part: k < HALF n ==> k + 1 < n - k
      Claim: 1 < n - 2 * k.
      Proof: If EVEN n,
                Claim: n - 2 * k <> 0
                Proof: By contradiction, assume n - 2 * k = 0.
                       Then 2 * k = n = 2 * HALF n      by EVEN_HALF
                         or     k = HALF n              by MULT_LEFT_CANCEL, 2 <> 0
                         but this contradicts k < HALF n.
                Claim: n - 2 * k <> 1
                Proof: By contradiction, assume n - 2 * k = 1.
                       Then n = 2 * k + 1               by SUB_EQ_ADD, 0 < 1
                         or ODD n                       by ODD_EXISTS, ADD1
                        but this contradicts EVEN n     by EVEN_ODD
                Thus n - 2 * k <> 1, or 1 < n - 2 * k   by above claims.
      Since 1 < n - 2 * k         by above
         so 2 * k + 1 < n         by arithmetic
         or k + k + 1 < n         by TIMES2
         or     k + 1 < n - k     by arithmetic

   Only-if part: k + 1 < n - k ==> k < HALF n
      Since     k + 1 < n - k
         so 2 * k + 1 < n                by arithmetic
        But n = 2 * HALF n + (n MOD 2)   by DIVISION, MULT_COMM, 0 < 2
        and n MOD 2 < 2                  by MOD_LESS, 0 < 2
         so n <= 2 * HALF n + 1          by arithmetic
       Thus 2 * k + 1 < 2 * HALF n + 1   by LESS_LESS_EQ_TRANS
         or         k < HALF             by LT_MULT_LCANCEL
*)
val LESS_HALF_IFF = store_thm(
  "LESS_HALF_IFF",
  ``!n k. k < HALF n <=> k + 1 < n - k``,
  rw[EQ_IMP_THM] >| [
    `1 < n - 2 * k` by
  (Cases_on `EVEN n` >| [
      `n - 2 * k <> 0` by
  (spose_not_then strip_assume_tac >>
      `2 * HALF n = n` by metis_tac[EVEN_HALF] >>
      decide_tac) >>
      `n - 2 * k <> 1` by
    (spose_not_then strip_assume_tac >>
      `n = 2 * k + 1` by decide_tac >>
      `ODD n` by metis_tac[ODD_EXISTS, ADD1] >>
      metis_tac[EVEN_ODD]) >>
      decide_tac,
      `n MOD 2 = 1` by metis_tac[EVEN_ODD, ODD_MOD2] >>
      `n = 2 * HALF n + (n MOD 2)` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 2``] >>
      decide_tac
    ]) >>
    decide_tac,
    `2 * k + 1 < n` by decide_tac >>
    `n = 2 * HALF n + (n MOD 2)` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 2``] >>
    `n MOD 2 < 2` by rw[] >>
    decide_tac
  ]);

(* Theorem: HALF n < k ==> n - k <= HALF n *)
(* Proof:
   If k < n,
      If EVEN n,
         Note HALF n + HALF n < k + HALF n   by HALF n < k
           or      2 * HALF n < k + HALF n   by TIMES2
           or               n < k + HALF n   by EVEN_HALF, EVEN n
           or           n - k < HALF n       by LESS_EQ_SUB_LESS, k <= n
         Hence true.
      If ~EVEN n, then ODD n                 by EVEN_ODD
         Note HALF n + HALF n + 1 < k + HALF n + 1   by HALF n < k
           or      2 * HALF n + 1 < k + HALF n + 1   by TIMES2
           or         n < k + HALF n + 1     by ODD_HALF
           or         n <= k + HALF n        by arithmetic
           so     n - k <= HALF n            by SUB_LESS_EQ_ADD, k <= n
   If ~(k < n), then n <= k.
      Thus n - k = 0, hence n - k <= HALF n  by arithmetic
*)
val MORE_HALF_IMP = store_thm(
  "MORE_HALF_IMP",
  ``!n k. HALF n < k ==> n - k <= HALF n``,
  rpt strip_tac >>
  Cases_on `k < n` >| [
    Cases_on `EVEN n` >| [
      `n = 2 * HALF n` by rw[EVEN_HALF] >>
      `n < k + HALF n` by decide_tac >>
      `n - k < HALF n` by decide_tac >>
      decide_tac,
      `ODD n` by rw[ODD_EVEN] >>
      `n = 2 * HALF n + 1` by rw[ODD_HALF] >>
      decide_tac
    ],
    decide_tac
  ]);

(* Theorem: (!k. k < m ==> f k < f (k + 1)) ==> !k. k < m ==> f k < f m *)
(* Proof:
   By induction on the difference (m - k):
   Base: 0 = m - k /\ k < m ==> f k < f m
      Note m = k and k < m contradicts, hence true.
   Step: !m k. (v = m - k) ==> k < m ==> f k < f m ==>
         SUC v = m - k /\ k < m ==> f k < f m
      Note v + 1 = m - k        by ADD1
        so v = m - (k + 1)      by arithmetic
      If v = 0,
         Then m = k + 1
           so f k < f (k + 1)   by implication
           or f k < f m         by m = k + 1
      If v <> 0, then 0 < v.
         Then 0 < m - (k + 1)   by v = m - (k + 1)
           or k + 1 < m         by arithmetic
          Now f k < f (k + 1)   by implication, k < m
          and f (k + 1) < f m   by induction hypothesis, put k = k + 1
           so f k < f m         by LESS_TRANS
*)
val MONOTONE_MAX = store_thm(
  "MONOTONE_MAX",
  ``!f m. (!k. k < m ==> f k < f (k + 1)) ==> !k. k < m ==> f k < f m``,
  rpt strip_tac >>
  Induct_on `m - k` >| [
    rpt strip_tac >>
    decide_tac,
    rpt strip_tac >>
    `v + 1 = m - k` by rw[] >>
    `v = m - (k + 1)` by decide_tac >>
    Cases_on `v = 0` >| [
      `m = k + 1` by decide_tac >>
      rw[],
      `k + 1 < m` by decide_tac >>
      `f k < f (k + 1)` by rw[] >>
      `f (k + 1) < f m` by rw[] >>
      decide_tac
    ]
  ]);

(* Theorem: (multiple gap)
   If n divides m, n cannot divide any x: m - n < x < m, or m < x < m + n
   n divides m ==> !x. m - n < x /\ x < m + n /\ n divides x ==> (x = m) *)
(* Proof:
   All these x, when divided by n, have non-zero remainders.
   Since n divides m and n divides x
     ==> ?h. m = h * n, and ?k. x = k * n  by divides_def
   Hence m - n < x
     ==> (h-1) * n < k * n                 by RIGHT_SUB_DISTRIB, MULT_LEFT_1
     and x < m + n
     ==>     k * n < (h+1) * n             by RIGHT_ADD_DISTRIB, MULT_LEFT_1
      so 0 < n, and h-1 < k, and k < h+1   by LT_MULT_RCANCEL
     that is, h <= k, and k <= h
   Therefore  h = k, or m = h * n = k * n = x.
*)
val MULTIPLE_INTERVAL = store_thm(
  "MULTIPLE_INTERVAL",
  ``!n m. n divides m ==> !x. m - n < x /\ x < m + n /\ n divides x ==> (x = m)``,
  rpt strip_tac >>
  `(?h. m = h*n) /\ (?k. x = k * n)` by metis_tac[divides_def] >>
  `(h-1) * n < k * n` by metis_tac[RIGHT_SUB_DISTRIB, MULT_LEFT_1] >>
  `k * n < (h+1) * n` by metis_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >>
  `0 < n /\ h-1 < k /\ k < h+1` by metis_tac[LT_MULT_RCANCEL] >>
  `h = k` by decide_tac >>
  metis_tac[]);

(* Theorem: 0 < m ==> (SUC (n MOD m) = SUC n MOD m + (SUC n DIV m - n DIV m) * m) *)
(* Proof:
   Let x = n DIV m, y = (SUC n) DIV m.
   Let a = SUC (n MOD m), b = (SUC n) MOD m.
   Note SUC n = y * m + b                 by DIVISION, 0 < m, for (SUC n), [1]
    and     n = x * m + (n MOD m)         by DIVISION, 0 < m, for n
     so SUC n = SUC (x * m + (n MOD m))   by above
              = x * m + a                 by ADD_SUC, [2]
   Equating, x * m + a = y * m + b        by [1], [2]
   Now n < SUC n                          by SUC_POS
    so n DIV m <= (SUC n) DIV m           by DIV_LE_MONOTONE, n <= SUC n
    or       x <= y
    so   x * m <= y * m                   by LE_MULT_RCANCEL, m <> 0

   Thus a = b + (y * m - x * m)           by arithmetic
          = b + (y - x) * m               by RIGHT_SUB_DISTRIB
*)
val MOD_SUC_EQN = store_thm(
  "MOD_SUC_EQN",
  ``!m n. 0 < m ==> (SUC (n MOD m) = SUC n MOD m + (SUC n DIV m - n DIV m) * m)``,
  rpt strip_tac >>
  qabbrev_tac `x = n DIV m` >>
  qabbrev_tac `y = (SUC n) DIV m` >>
  qabbrev_tac `a = SUC (n MOD m)` >>
  qabbrev_tac `b = (SUC n) MOD m` >>
  `SUC n = y * m + b` by rw[DIVISION, Abbr`y`, Abbr`b`] >>
  `n = x * m + (n MOD m)` by rw[DIVISION, Abbr`x`] >>
  `SUC n = x * m + a` by rw[Abbr`a`] >>
  `n < SUC n` by rw[] >>
  `x <= y` by rw[DIV_LE_MONOTONE, Abbr`x`, Abbr`y`] >>
  `x * m <= y * m` by rw[] >>
  `a = b + (y * m - x * m)` by decide_tac >>
  `_ = b + (y - x) * m` by rw[] >>
  rw[]);

(* Note: Compare this result with these in arithmeticTheory:
MOD_SUC      |- 0 < y /\ SUC x <> SUC (x DIV y) * y ==> (SUC x MOD y = SUC (x MOD y))
MOD_SUC_IFF  |- 0 < y ==> ((SUC x MOD y = SUC (x MOD y)) <=> SUC x <> SUC (x DIV y) * y)
*)

(* Theorem: 1 < n ==> 1 < HALF (n ** 2) *)
(* Proof:
       1 < n
   ==> 2 <= n                            by arithmetic
   ==> 2 ** 2 <= n ** 2                  by EXP_EXP_LE_MONO
   ==> (2 ** 2) DIV 2 <= (n ** 2) DIV 2  by DIV_LE_MONOTONE
   ==> 2 <= (n ** 2) DIV 2               by arithmetic
   ==> 1 < (n ** 2) DIV 2                by arithmetic
*)
val ONE_LT_HALF_SQ = store_thm(
  "ONE_LT_HALF_SQ",
  ``!n. 1 < n ==> 1 < HALF (n ** 2)``,
  rpt strip_tac >>
  `2 <= n` by decide_tac >>
  `2 ** 2 <= n ** 2` by rw[] >>
  `(2 ** 2) DIV 2 <= (n ** 2) DIV 2` by rw[DIV_LE_MONOTONE] >>
  `(2 ** 2) DIV 2 = 2` by EVAL_TAC >>
  decide_tac);

(* Theorem: 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1)) *)
(* Proof
   By induction on n.
   Base: 0 < 0 ==> 2 ** 0 DIV 2 = 2 ** (0 - 1)
      This is trivially true as 0 < 0 = F.
   Step:  0 < n ==> HALF (2 ** n) = 2 ** (n - 1)
      ==> 0 < SUC n ==> HALF (2 ** SUC n) = 2 ** (SUC n - 1)
        HALF (2 ** SUC n)
      = HALF (2 * 2 ** n)          by EXP
      = 2 ** n                     by MULT_TO_DIV
      = 2 ** (SUC n - 1)           by SUC_SUB1
*)
Theorem EXP_2_HALF:
  !n. 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1))
Proof
  Induct >> simp[EXP, MULT_TO_DIV]
QED

(*
There is EVEN_MULT    |- !m n. EVEN (m * n) <=> EVEN m \/ EVEN n
There is EVEN_DOUBLE  |- !n. EVEN (TWICE n)
*)

(* Theorem: EVEN n ==> (HALF (m * n) = m * HALF n) *)
(* Proof:
   Note n = TWICE (HALF n)  by EVEN_HALF
   Let k = HALF n.
     HALF (m * n)
   = HALF (m * (2 * k))  by above
   = HALF (2 * (m * k))  by MULT_COMM_ASSOC
   = m * k               by HALF_TWICE
   = m * HALF n          by notation
*)
val HALF_MULT_EVEN = store_thm(
  "HALF_MULT_EVEN",
  ``!m n. EVEN n ==> (HALF (m * n) = m * HALF n)``,
  metis_tac[EVEN_HALF, MULT_COMM_ASSOC, HALF_TWICE]);

(* Theorem: 0 < k /\ k * m < n ==> m < n *)
(* Proof:
   Note ?h. k = SUC h     by num_CASES, k <> 0
        k * m
      = SUC h * m         by above
      = (h + 1) * m       by ADD1
      = h * m + 1 * m     by LEFT_ADD_DISTRIB
      = h * m + m         by MULT_LEFT_1
   Since 0 <= h * m,
      so k * m < n ==> m < n.
*)
val MULT_LT_IMP_LT = store_thm(
  "MULT_LT_IMP_LT",
  ``!m n k. 0 < k /\ k * m < n ==> m < n``,
  rpt strip_tac >>
  `k <> 0` by decide_tac >>
  `?h. k = SUC h` by metis_tac[num_CASES] >>
  `k * m = h * m + m` by rw[ADD1] >>
  decide_tac);

(* Theorem: 0 < k /\ k * m <= n ==> m <= n *)
(* Proof:
   Note     1 <= k                 by 0 < k
     so 1 * m <= k * m             by LE_MULT_RCANCEL
     or     m <= k * m <= n        by inequalities
*)
Theorem MULT_LE_IMP_LE:
  !m n k. 0 < k /\ k * m <= n ==> m <= n
Proof
  rpt strip_tac >>
  `1 <= k` by decide_tac >>
  `1 * m <= k * m` by simp[] >>
  decide_tac
QED

(* Theorem: n * HALF ((SQ n) ** 2) <= HALF (n ** 5) *)
(* Proof:
      n * HALF ((SQ n) ** 2)
   <= HALF (n * (SQ n) ** 2)     by HALF_MULT
    = HALF (n * (n ** 2) ** 2)   by EXP_2
    = HALF (n * n ** 4)          by EXP_EXP_MULT
    = HALF (n ** 5)              by EXP
*)
val HALF_EXP_5 = store_thm(
  "HALF_EXP_5",
  ``!n. n * HALF ((SQ n) ** 2) <= HALF (n ** 5)``,
  rpt strip_tac >>
  `n * ((SQ n) ** 2) = n * n ** 4` by rw[EXP_2, EXP_EXP_MULT] >>
  `_ = n ** 5` by rw[EXP] >>
  metis_tac[HALF_MULT]);

(* Theorem: n <= 2 * m <=> (n <> 0 ==> HALF (n - 1) < m) *)
(* Proof:
   Let k = n - 1, then n = SUC k.
   If part: n <= TWICE m /\ n <> 0 ==> HALF k < m
      Note HALF (SUC k) <= m                by DIV_LE_MONOTONE, HALF_TWICE
      If EVEN n,
         Then ODD k                         by EVEN_ODD_SUC
          ==> HALF (SUC k) = SUC (HALF k)   by ODD_SUC_HALF
         Thus SUC (HALF k) <= m             by above
           or        HALF k < m             by LESS_EQ
      If ~EVEN n, then ODD n                by EVEN_ODD
         Thus EVEN k                        by EVEN_ODD_SUC
          ==> HALF (SUC k) = HALF k         by EVEN_SUC_HALF
          But k <> TWICE m                  by k = n - 1, n <= TWICE m
          ==> HALF k <> m                   by EVEN_HALF
         Thus  HALF k < m                   by HALF k <= m, HALF k <> m

   Only-if part: n <> 0 ==> HALF k < m ==> n <= TWICE m
      If n = 0, trivially true.
      If n <> 0, has HALF k < m.
         If EVEN n,
            Then ODD k                        by EVEN_ODD_SUC
             ==> HALF (SUC k) = SUC (HALF k)  by ODD_SUC_HALF
             But SUC (HALF k) <= m            by HALF k < m
            Thus HALF n <= m                  by n = SUC k
             ==> TWICE (HALF n) <= TWICE m    by LE_MULT_LCANCEL
              or              n <= TWICE m    by EVEN_HALF
         If ~EVEN n, then ODD n               by EVEN_ODD
            Then EVEN k                       by EVEN_ODD_SUC
             ==> TWICE (HALF k) < TWICE m     by LT_MULT_LCANCEL
              or              k < TWICE m     by EVEN_HALF
              or             n <= TWICE m     by n = k + 1
*)
val LE_TWICE_ALT = store_thm(
  "LE_TWICE_ALT",
  ``!m n. n <= 2 * m <=> (n <> 0 ==> HALF (n - 1) < m)``,
  rw[EQ_IMP_THM] >| [
    `n = SUC (n - 1)` by decide_tac >>
    qabbrev_tac `k = n - 1` >>
    `HALF (SUC k) <= m` by metis_tac[DIV_LE_MONOTONE, HALF_TWICE, DECIDE``0 < 2``] >>
    Cases_on `EVEN n` >| [
      `ODD k` by rw[EVEN_ODD_SUC] >>
      `HALF (SUC k) = SUC (HALF k)` by rw[ODD_SUC_HALF] >>
      decide_tac,
      `ODD n` by metis_tac[EVEN_ODD] >>
      `EVEN k` by rw[EVEN_ODD_SUC] >>
      `HALF (SUC k) = HALF k` by rw[EVEN_SUC_HALF] >>
      `k <> TWICE m` by rw[Abbr`k`] >>
      `HALF k <> m` by metis_tac[EVEN_HALF] >>
      decide_tac
    ],
    Cases_on `n = 0` >-
    rw[] >>
    `n = SUC (n - 1)` by decide_tac >>
    qabbrev_tac `k = n - 1` >>
    Cases_on `EVEN n` >| [
      `ODD k` by rw[EVEN_ODD_SUC] >>
      `HALF (SUC k) = SUC (HALF k)` by rw[ODD_SUC_HALF] >>
      `HALF n <= m` by rw[] >>
      metis_tac[LE_MULT_LCANCEL, EVEN_HALF, DECIDE``2 <> 0``],
      `ODD n` by metis_tac[EVEN_ODD] >>
      `EVEN k` by rw[EVEN_ODD_SUC] >>
      `k < TWICE m` by metis_tac[LT_MULT_LCANCEL, EVEN_HALF, DECIDE``0 < 2``] >>
      rw[Abbr`k`]
    ]
  ]);

(* Theorem: (HALF n) DIV 2 ** m = n DIV (2 ** SUC m) *)
(* Proof:
     (HALF n) DIV 2 ** m
   = (n DIV 2) DIV (2 ** m)    by notation
   = n DIV (2 * 2 ** m)        by DIV_DIV_DIV_MULT, 0 < 2, 0 < 2 ** m
   = n DIV (2 ** (SUC m))      by EXP
*)
val HALF_DIV_TWO_POWER = store_thm(
  "HALF_DIV_TWO_POWER",
  ``!m n. (HALF n) DIV 2 ** m = n DIV (2 ** SUC m)``,
  rw[DIV_DIV_DIV_MULT, EXP]);

(* Theorem: 1 + 2 + 3 + 4 = 10 *)
(* Proof: by calculation. *)
Theorem fit_for_10:
  1 + 2 + 3 + 4 = 10
Proof
  decide_tac
QED

(* Theorem: 1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100 *)
(* Proof: by calculation. *)
Theorem fit_for_100:
  1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100
Proof
  decide_tac
QED

(* ------------------------------------------------------------------------- *)

(* Theorem: If prime p divides n, ?m. 0 < m /\ (p ** m) divides n /\ n DIV (p ** m) has no p *)
(* Proof:
   Let s = {j | (p ** j) divides n }
   Since p ** 1 = p, 1 IN s, so s <> {}.
       (p ** j) divides n
   ==> p ** j <= n                  by DIVIDES_LE
   ==> p ** j <= p ** z             by EXP_ALWAYS_BIG_ENOUGH
   ==>      j <= z                  by EXP_BASE_LE_MONO
   ==> s SUBSET count (SUC z),
   so FINITE s                      by FINITE_COUNT, SUBSET_FINITE
   Let m = MAX_SET s,
   m IN s, so (p ** m) divides n    by MAX_SET_DEF
   1 <= m, or 0 < m.
   ?q. n = q * (p ** m)             by divides_def
   To prove: !k. gcd (p ** k) (n DIV (p ** m)) = 1
   By contradiction, suppose there is a k such that
   gcd (p ** k) (n DIV (p ** m)) <> 1
   So there is a prime pp that divides this gcd, by PRIME_FACTOR
   but pp | p ** k, a pure prime, so pp = p      by DIVIDES_EXP_BASE, prime_divides_only_self
       pp | n DIV (p ** m)
   or  pp * p ** m | n
       p * SUC m | n, making m not MAX_SET s.
*)
val FACTOR_OUT_PRIME = store_thm(
  "FACTOR_OUT_PRIME",
  ``!n p. 0 < n /\ prime p /\ p divides n ==> ?m. 0 < m /\ (p ** m) divides n /\ !k. gcd (p ** k) (n DIV (p ** m)) = 1``,
  rpt strip_tac >>
  qabbrev_tac `s = {j | (p ** j) divides n }` >>
  `!j. j IN s <=> (p ** j) divides n` by rw[Abbr`s`] >>
  `p ** 1 = p` by rw[] >>
  `1 IN s` by metis_tac[] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `?z. n <= p ** z` by rw[EXP_ALWAYS_BIG_ENOUGH] >>
  `!j. j IN s ==> p ** j <= n` by metis_tac[DIVIDES_LE] >>
  `!j. j IN s ==> p ** j <= p ** z` by metis_tac[LESS_EQ_TRANS] >>
  `!j. j IN s ==> j <= z` by metis_tac[EXP_BASE_LE_MONO] >>
  `!j. j <= z <=> j < SUC z` by decide_tac >>
  `!j. j < SUC z <=> j IN count (SUC z)` by rw[] >>
  `s SUBSET count (SUC z)` by metis_tac[SUBSET_DEF] >>
  `FINITE s` by metis_tac[FINITE_COUNT, SUBSET_FINITE] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  qabbrev_tac `m = MAX_SET s` >>
  `m IN s /\ !y. y IN s ==> y <= m`by rw[MAX_SET_DEF, Abbr`m`] >>
  qexists_tac `m` >>
  CONJ_ASM1_TAC >| [
    `1 <= m` by metis_tac[] >>
    decide_tac,
    CONJ_ASM1_TAC >-
    metis_tac[] >>
    qabbrev_tac `pm = p ** m` >>
    `0 < p` by decide_tac >>
    `0 < pm` by rw[ZERO_LT_EXP, Abbr`pm`] >>
    `n MOD pm = 0` by metis_tac[DIVIDES_MOD_0] >>
    `n = n DIV pm * pm` by metis_tac[DIVISION, ADD_0] >>
    qabbrev_tac `qm = n DIV pm` >>
    spose_not_then strip_assume_tac >>
    `?q. prime q /\ q divides (gcd (p ** k) qm)` by rw[PRIME_FACTOR] >>
    `0 <> pm /\ n <> 0` by decide_tac >>
    `qm <> 0` by metis_tac[MULT] >>
    `0 < qm` by decide_tac >>
    qabbrev_tac `pk = p ** k` >>
    `0 < pk` by rw[ZERO_LT_EXP, Abbr`pk`] >>
    `(gcd pk qm) divides pk /\ (gcd pk qm) divides qm` by metis_tac[GCD_DIVIDES, DIVIDES_MOD_0] >>
    `q divides pk /\ q divides qm` by metis_tac[DIVIDES_TRANS] >>
    `k <> 0` by metis_tac[EXP, GCD_1] >>
    `0 < k` by decide_tac >>
    `q divides p` by metis_tac[DIVIDES_EXP_BASE] >>
    `q = p` by rw[prime_divides_only_self] >>
    `?x. qm = x * q` by rw[GSYM divides_def] >>
    `n = x * p * pm` by metis_tac[] >>
    `_ = x * (p * pm)` by rw_tac arith_ss[] >>
    `_ = x * (p ** SUC m)` by rw[EXP, Abbr`pm`] >>
    `(p ** SUC m) divides n` by metis_tac[divides_def] >>
    `SUC m <= m` by metis_tac[] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Consequences of Coprime.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If 1 < n, !x. coprime n x ==> 0 < x /\ 0 < x MOD n *)
(* Proof:
   If x = 0, gcd n x = n. But n <> 1, hence x <> 0, or 0 < x.
   x MOD n = 0 ==> x a multiple of n ==> gcd n x = n <> 1  if n <> 1.
   Hence if 1 < n, coprime n x ==> x MOD n <> 0, or 0 < x MOD n.
*)
val MOD_NONZERO_WHEN_GCD_ONE = store_thm(
  "MOD_NONZERO_WHEN_GCD_ONE",
  ``!n. 1 < n ==> !x. coprime n x ==> 0 < x /\ 0 < x MOD n``,
  ntac 4 strip_tac >>
  conj_asm1_tac >| [
    `1 <> n` by decide_tac >>
    `x <> 0` by metis_tac[GCD_0R] >>
    decide_tac,
    `1 <> n /\ x <> 0` by decide_tac >>
    `?k q. k * x = q * n + 1` by metis_tac[LINEAR_GCD] >>
    `(k*x) MOD n = 1` by rw_tac std_ss[MOD_MULT] >>
    spose_not_then strip_assume_tac >>
    `(x MOD n = 0) /\ 0 < n /\ 1 <> 0` by decide_tac >>
    metis_tac[MOD_MULTIPLE_ZERO, MULT_COMM]
  ]);

(* Theorem: If 1 < n, coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k *)
(* Proof:
       gcd n x = 1 ==> x <> 0               by GCD_0R
   Also,
       gcd n x = 1
   ==> ?k q. k * x = q * n + 1              by LINEAR_GCD
   ==> (k * x) MOD n = (q * n + 1) MOD n    by arithmetic
   ==> (k * x) MOD n = 1                    by MOD_MULT, 1 < n.

   Let g = gcd n k.
   Since 1 < n, 0 < n.
   Since q * n+1 <> 0, x <> 0, k <> 0, hence 0 < k.
   Hence 0 < g /\ (n MOD g = 0) /\ (k MOD g = 0)    by GCD_DIVIDES.
   Or  n = a * g /\ k = b * g    for some a, b.
   Therefore:
        (b * g) * x = q * (a * g) + 1
        (b * x) * g = (q * a) * g + 1      by arithmetic
   Hence g divides 1, or g = 1     since 0 < g.
*)
val GCD_ONE_PROPERTY = store_thm(
  "GCD_ONE_PROPERTY",
  ``!n x. 1 < n /\ coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k``,
  rpt strip_tac >>
  `n <> 1` by decide_tac >>
  `x <> 0` by metis_tac[GCD_0R] >>
  `?k q. k * x = q * n + 1` by metis_tac[LINEAR_GCD] >>
  `(k * x) MOD n = 1` by rw_tac std_ss[MOD_MULT] >>
  `?g. g = gcd n k` by rw[] >>
  `n <> 0 /\ q*n + 1 <> 0` by decide_tac >>
  `k <> 0` by metis_tac[MULT_EQ_0] >>
  `0 < g /\ (n MOD g = 0) /\ (k MOD g = 0)` by metis_tac[GCD_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `g divides n /\ g divides k` by rw[DIVIDES_MOD_0] >>
  `g divides (n * q) /\ g divides (k*x)` by rw[DIVIDES_MULT] >>
  `g divides (n * q + 1)` by metis_tac [MULT_COMM] >>
  `g divides 1` by metis_tac[DIVIDES_ADD_2] >>
  metis_tac[DIVIDES_ONE]);

(* Theorem: For 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
            ?y. 0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1) *)
(* Proof:
       gcd n x = 1
   ==> ?k. (k * x) MOD n = 1 /\ coprime n k   by GCD_ONE_PROPERTY
       (k * x) MOD n = 1
   ==> (k MOD n * x MOD n) MOD n = 1          by MOD_TIMES2
   ==> ((k MOD n) * x) MOD n = 1              by LESS_MOD, x < n.

   Now   k MOD n < n                          by MOD_LESS
   and   0 < k MOD n                          by MOD_MULTIPLE_ZERO and 1 <> 0.

   Hence take y = k MOD n, then 0 < y < n.
   and gcd n k = 1 ==> gcd n (k MOD n) = 1    by MOD_WITH_GCD_ONE.
*)
val GCD_MOD_MULT_INV = store_thm(
  "GCD_MOD_MULT_INV",
  ``!n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
      ?y. 0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1)``,
  rpt strip_tac >>
  `?k. ((k * x) MOD n = 1) /\ coprime n k` by rw_tac std_ss[GCD_ONE_PROPERTY] >>
  `0 < n` by decide_tac >>
  `(k MOD n * x MOD n) MOD n = 1` by rw_tac std_ss[MOD_TIMES2] >>
  `((k MOD n) * x) MOD n = 1` by metis_tac[LESS_MOD] >>
  `k MOD n < n` by rw_tac std_ss[MOD_LESS] >>
  `1 <> 0` by decide_tac >>
  `0 <> k MOD n` by metis_tac[MOD_MULTIPLE_ZERO] >>
  `0 < k MOD n` by decide_tac >>
  metis_tac[MOD_WITH_GCD_ONE]);

(* Convert this into an existence definition *)
val lemma = prove(
  ``!n x. ?y. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
              0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1)``,
  metis_tac[GCD_MOD_MULT_INV]);

val GEN_MULT_INV_DEF = new_specification(
  "GEN_MULT_INV_DEF",
  ["GCD_MOD_MUL_INV"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(* > val GEN_MULT_INV_DEF =
    |- !n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
       0 < GCD_MOD_MUL_INV n x /\ GCD_MOD_MUL_INV n x < n /\ coprime n (GCD_MOD_MUL_INV n x) /\
       ((GCD_MOD_MUL_INV n x * x) MOD n = 1) : thm *)

(* Theorem: If 1/c = 1/b - 1/a, then lcm a b = lcm a c.
            a * b = c * (a - b) ==> lcm a b = lcm a c *)
(* Proof:
   Idea:
     lcm a c
   = (a * c) DIV (gcd a c)              by lcm_def
   = (a * b * c) DIV (gcd a c) DIV b    by MULT_DIV
   = (a * b * c) DIV b * (gcd a c)      by DIV_DIV_DIV_MULT
   = (a * b * c) DIV gcd b*a b*c        by GCD_COMMON_FACTOR
   = (a * b * c) DIV gcd c*(a-b) c*b    by given
   = (a * b * c) DIV c * gcd (a-b) b    by GCD_COMMON_FACTOR
   = (a * b * c) DIV c * gcd a b        by GCD_SUB_L
   = (a * b * c) DIV c DIV gcd a b      by DIV_DIV_DIV_MULT
   = a * b DIV gcd a b                  by MULT_DIV
   = lcm a b                            by lcm_def

   Details:
   If a = 0,
      lcm 0 b = 0 = lcm 0 c          by LCM_0
   If a <> 0,
      If b = 0, a * b = 0 = c * a    by MULT_0, SUB_0
      Hence c = 0, hence true        by MULT_EQ_0
      If b <> 0, c <> 0.             by MULT_EQ_0
      So 0 < gcd a c, 0 < gcd a b    by GCD_EQ_0
      and  (gcd a c) divides a       by GCD_IS_GREATEST_COMMON_DIVISOR
      thus (gcd a c) divides (a * c) by DIVIDES_MULT
      Note (a - b) <> 0              by MULT_EQ_0
       so  ~(a <= b)                 by SUB_EQ_0
       or  b < a, or b <= a          for GCD_SUB_L later.
   Now,
      lcm a c
    = (a * c) DIV (gcd a c)                      by lcm_def
    = (b * ((a * c) DIV (gcd a c))) DIV b        by MULT_COMM, MULT_DIV
    = ((b * (a * c)) DIV (gcd a c)) DIV b        by MULTIPLY_DIV
    = (b * (a * c)) DIV ((gcd a c) * b)          by DIV_DIV_DIV_MULT
    = (b * a * c) DIV ((gcd a c) * b)            by MULT_ASSOC
    = c * (a * b) DIV (b * (gcd a c))            by MULT_COMM
    = c * (a * b) DIV (gcd (b * a) (b * c))      by GCD_COMMON_FACTOR
    = c * (a * b) DIV (gcd (a * b) (c * b))      by MULT_COMM
    = c * (a * b) DIV (gcd (c * (a-b)) (c * b))  by a * b = c * (a - b)
    = c * (a * b) DIV (c * gcd (a-b) b)          by GCD_COMMON_FACTOR
    = c * (a * b) DIV (c * gcd a b)              by GCD_SUB_L
    = c * (a * b) DIV c DIV (gcd a b)            by DIV_DIV_DIV_MULT
    = a * b DIV gcd a b                          by MULT_COMM, MULT_DIV
    = lcm a b                                    by lcm_def
*)
val LCM_EXCHANGE = store_thm(
  "LCM_EXCHANGE",
  ``!a b c. (a * b = c * (a - b)) ==> (lcm a b = lcm a c)``,
  rpt strip_tac >>
  Cases_on `a = 0` >-
  rw[] >>
  Cases_on `b = 0` >| [
    `c = 0` by metis_tac[MULT_EQ_0, SUB_0] >>
    rw[],
    `c <> 0` by metis_tac[MULT_EQ_0] >>
    `0 < b /\ 0 < c` by decide_tac >>
    `(gcd a c) divides a` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
    `(gcd a c) divides (a * c)` by rw[DIVIDES_MULT] >>
    `0 < gcd a c /\ 0 < gcd a b` by metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO] >>
    `~(a <= b)` by metis_tac[SUB_EQ_0, MULT_EQ_0] >>
    `b <= a` by decide_tac >>
    `lcm a c = (a * c) DIV (gcd a c)` by rw[lcm_def] >>
    `_ = (b * ((a * c) DIV (gcd a c))) DIV b` by metis_tac[MULT_COMM, MULT_DIV] >>
    `_ = ((b * (a * c)) DIV (gcd a c)) DIV b` by rw[MULTIPLY_DIV] >>
    `_ = (b * (a * c)) DIV ((gcd a c) * b)` by rw[DIV_DIV_DIV_MULT] >>
    `_ = (b * a * c) DIV ((gcd a c) * b)` by rw[MULT_ASSOC] >>
    `_ = c * (a * b) DIV (b * (gcd a c))` by rw_tac std_ss[MULT_COMM] >>
    `_ = c * (a * b) DIV (gcd (b * a) (b * c))` by rw[GCD_COMMON_FACTOR] >>
    `_ = c * (a * b) DIV (gcd (a * b) (c * b))` by rw_tac std_ss[MULT_COMM] >>
    `_ = c * (a * b) DIV (gcd (c * (a-b)) (c * b))` by rw[] >>
    `_ = c * (a * b) DIV (c * gcd (a-b) b)` by rw[GCD_COMMON_FACTOR] >>
    `_ = c * (a * b) DIV (c * gcd a b)` by rw[GCD_SUB_L] >>
    `_ = c * (a * b) DIV c DIV (gcd a b)` by rw[DIV_DIV_DIV_MULT] >>
    `_ = a * b DIV gcd a b` by metis_tac[MULT_COMM, MULT_DIV] >>
    `_ = lcm a b` by rw[lcm_def] >>
    decide_tac
  ]);

(* Theorem: LCM (k * m) (k * n) = k * LCM m n *)
(* Proof:
   If m = 0 or n = 0, LHS = 0 = RHS.
   If m <> 0 and n <> 0,
     lcm (k * m) (k * n)
   = (k * m) * (k * n) / gcd (k * m) (k * n)    by GCD_LCM
   = (k * m) * (k * n) / k * (gcd m n)          by GCD_COMMON_FACTOR
   = k * m * n / (gcd m n)
   = k * LCM m n                                by GCD_LCM
*)
val LCM_COMMON_FACTOR = store_thm(
  "LCM_COMMON_FACTOR",
  ``!m n k. lcm (k * m) (k * n) = k * lcm m n``,
  rpt strip_tac >>
  `k * (k * (m * n)) = (k * m) * (k * n)` by rw_tac arith_ss[] >>
  `_ = gcd (k * m) (k * n) * lcm (k * m) (k * n) ` by rw[GCD_LCM] >>
  `_ = k * (gcd m n) * lcm (k * m) (k * n)` by rw[GCD_COMMON_FACTOR] >>
  `_ = k * ((gcd m n) * lcm (k * m) (k * n))` by rw_tac arith_ss[] >>
  Cases_on `k = 0` >-
  rw[] >>
  `(gcd m n) * lcm (k * m) (k * n) = k * (m * n)` by metis_tac[MULT_LEFT_CANCEL] >>
  `_ = k * ((gcd m n) * (lcm m n))` by rw_tac std_ss[GCD_LCM] >>
  `_ = (gcd m n) * (k * (lcm m n))` by rw_tac arith_ss[] >>
  Cases_on `n = 0` >-
  rw[] >>
  metis_tac[MULT_LEFT_CANCEL, GCD_EQ_0]);

(* Theorem: coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c *)
(* Proof:
     lcm (a * c) (b * c)
   = lcm (c * a) (c * b)     by MULT_COMM
   = c * (lcm a b)           by LCM_COMMON_FACTOR
   = (lcm a b) * c           by MULT_COMM
   = a * b * c               by LCM_COPRIME
*)
val LCM_COMMON_COPRIME = store_thm(
  "LCM_COMMON_COPRIME",
  ``!a b. coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c``,
  metis_tac[LCM_COMMON_FACTOR, LCM_COPRIME, MULT_COMM]);

(* Theorem: 0 < n /\ m MOD n = 0 ==> gcd m n = n *)
(* Proof:
   Since m MOD n = 0
         ==> n divides m     by DIVIDES_MOD_0
   Hence gcd m n = gcd n m   by GCD_SYM
                 = n         by divides_iff_gcd_fix
*)
val GCD_MULTIPLE = store_thm(
  "GCD_MULTIPLE",
  ``!m n. 0 < n /\ (m MOD n = 0) ==> (gcd m n = n)``,
  metis_tac[DIVIDES_MOD_0, divides_iff_gcd_fix, GCD_SYM]);

(* Theorem: gcd (m * n) n = n *)
(* Proof:
     gcd (m * n) n
   = gcd (n * m) n          by MULT_COMM
   = gcd (n * m) (n * 1)    by MULT_RIGHT_1
   = n * (gcd m 1)          by GCD_COMMON_FACTOR
   = n * 1                  by GCD_1
   = n                      by MULT_RIGHT_1
*)
val GCD_MULTIPLE_ALT = store_thm(
  "GCD_MULTIPLE_ALT",
  ``!m n. gcd (m * n) n = n``,
  rpt strip_tac >>
  `gcd (m * n) n = gcd (n * m) n` by rw[MULT_COMM] >>
  `_ = gcd (n * m) (n * 1)` by rw[] >>
  rw[GCD_COMMON_FACTOR]);


(* Theorem: k * a <= b ==> gcd a b = gcd a (b - k * a) *)
(* Proof:
   By induction on k.
   Base case: 0 * a <= b ==> gcd a b = gcd a (b - 0 * a)
     True since b - 0 * a = b       by MULT, SUB_0
   Step case: k * a <= b ==> (gcd a b = gcd a (b - k * a)) ==>
              SUC k * a <= b ==> (gcd a b = gcd a (b - SUC k * a))
         SUC k * a <= b
     ==> k * a + a <= b             by MULT
        so       a <= b - k * a     by arithmetic [1]
       and   k * a <= b             by 0 <= b - k * a, [2]
       gcd a (b - SUC k * a)
     = gcd a (b - (k * a + a))      by MULT
     = gcd a (b - k * a - a)        by arithmetic
     = gcd a (b - k * a - a + a)    by GCD_ADD_L, ADD_COMM
     = gcd a (b - k * a)            by SUB_ADD, a <= b - k * a [1]
     = gcd a b                      by induction hypothesis, k * a <= b [2]
*)
val GCD_SUB_MULTIPLE = store_thm(
  "GCD_SUB_MULTIPLE",
  ``!a b k. k * a <= b ==> (gcd a b = gcd a (b - k * a))``,
  rpt strip_tac >>
  Induct_on `k` >-
  rw[] >>
  rw_tac std_ss[] >>
  `k * a + a <= b` by metis_tac[MULT] >>
  `a <= b - k * a` by decide_tac >>
  `k * a <= b` by decide_tac >>
  `gcd a (b - SUC k * a) = gcd a (b - (k * a + a))` by rw[MULT] >>
  `_ = gcd a (b - k * a - a)` by rw_tac arith_ss[] >>
  `_ = gcd a (b - k * a - a + a)` by rw[GCD_ADD_L, ADD_COMM] >>
  rw_tac std_ss[SUB_ADD]);

(* Theorem: k * a <= b ==> (gcd b a = gcd a (b - k * a)) *)
(* Proof: by GCD_SUB_MULTIPLE, GCD_SYM *)
val GCD_SUB_MULTIPLE_COMM = store_thm(
  "GCD_SUB_MULTIPLE_COMM",
  ``!a b k. k * a <= b ==> (gcd b a = gcd a (b - k * a))``,
  metis_tac[GCD_SUB_MULTIPLE, GCD_SYM]);

(* Idea: a crude upper bound for greatest common divisor.
         A better upper bound is: gcd m n <= MIN m n, by MIN_LE *)

(* Theorem: 0 < m /\ 0 < n ==> gcd m n <= m /\ gcd m n <= n *)
(* Proof:
   Let g = gcd m n.
   Then g divides m /\ g divides n   by GCD_PROPERTY
     so g <= m /\ g <= n             by DIVIDES_LE,  0 < m, 0 < n
*)
Theorem gcd_le:
  !m n. 0 < m /\ 0 < n ==> gcd m n <= m /\ gcd m n <= n
Proof
  ntac 3 strip_tac >>
  qabbrev_tac `g = gcd m n` >>
  `g divides m /\ g divides n` by metis_tac[GCD_PROPERTY] >>
  simp[DIVIDES_LE]
QED

(* Idea: a generalisation of GCD_LINEAR:
|- !j k. 0 < j ==> ?p q. p * j = q * k + gcd j k
   This imposes a condition for (gcd a b) divides c.
*)

(* Theorem: 0 < a ==> ((gcd a b) divides c <=> ?p q. p * a = q * b + c) *)
(* Proof:
   Let d = gcd a b.
   If part: d divides c ==> ?p q. p * a = q * b + c
      Note ?k. c = k * d                 by divides_def
       and ?u v. u * a = v * b + d       by GCD_LINEAR, 0 < a
        so (k * u) * a = (k * v) * b + (k * d)
      Take p = k * u, q = k * v,
      Then p * q = q * b + c
   Only-if part: p * a = q * b + c ==> d divides c
      Note d divides a /\ d divides b    by GCD_PROPERTY
        so d divides c                   by divides_linear_sub
*)
Theorem gcd_divides_iff:
  !a b c. 0 < a ==> ((gcd a b) divides c <=> ?p q. p * a = q * b + c)
Proof
  rpt strip_tac >>
  qabbrev_tac `d = gcd a b` >>
  rw_tac bool_ss[EQ_IMP_THM] >| [
    `?k. c = k * d` by rw[GSYM divides_def] >>
    `?p q. p * a = q * b + d` by rw[GCD_LINEAR, Abbr`d`] >>
    `k * (p * a) = k * (q * b + d)` by fs[] >>
    `_ = k * (q * b) + k * d` by decide_tac >>
    metis_tac[MULT_ASSOC],
    `d divides a /\ d divides b` by metis_tac[GCD_PROPERTY] >>
    metis_tac[divides_linear_sub]
  ]
QED

(* Theorem alias *)
Theorem gcd_linear_thm = gcd_divides_iff;
(* val gcd_linear_thm =
|- !a b c. 0 < a ==> (gcd a b divides c <=> ?p q. p * a = q * b + c): thm *)

(* Idea: a version of GCD_LINEAR for MOD, without negatives.
   That is: in MOD n. gcd (a b) can be expressed as a linear combination of a b. *)

(* Theorem: 0 < n /\ 0 < a ==> ?p q. (p * a + q * b) MOD n = gcd a b MOD n *)
(* Proof:
   Let d = gcd a b.
   Then ?h k. h * a = k * b + d                by GCD_LINEAR, 0 < a
   Let p = h, q = k * n - k.
   Then q + k = k * n.
          (p * a) MOD n = (k * b + d) MOD n
   <=>    (p * a + q * b) MOD n = (q * b + k * b + d) MOD n    by ADD_MOD
   <=>    (p * a + q * b) MOD n = (k * b * n + d) MOD n        by above
   <=>    (p * a + q * b) MOD n = d MOD n                      by MOD_TIMES
*)
Theorem gcd_linear_mod_thm:
  !n a b. 0 < n /\ 0 < a ==> ?p q. (p * a + q * b) MOD n = gcd a b MOD n
Proof
  rpt strip_tac >>
  qabbrev_tac `d = gcd a b` >>
  `?p k. p * a = k * b + d` by rw[GCD_LINEAR, Abbr`d`] >>
  `k <= k * n` by fs[] >>
  `k * n - k + k = k * n` by decide_tac >>
  qabbrev_tac `q = k * n - k` >>
  qexists_tac `p` >>
  qexists_tac `q` >>
  `(p * a + q * b) MOD n = (q * b + k * b + d) MOD n` by rw[ADD_MOD] >>
  `_ = ((q + k) * b + d) MOD n` by decide_tac >>
  `_ = (k * b * n + d) MOD n` by rfs[] >>
  simp[MOD_TIMES]
QED

(* Idea: a simplification of gcd_linear_mod_thm when n = a. *)

(* Theorem: 0 < a ==> ?q. (q * b) MOD a = (gcd a b) MOD a *)
(* Proof:
   Let g = gcd a b.
   Then ?p q. (p * a + q * b) MOD a = g MOD a  by gcd_linear_mod_thm, n = a
     so               (q * b) MOD a = g MOD a  by MOD_TIMES
*)
Theorem gcd_linear_mod_1:
  !a b. 0 < a ==> ?q. (q * b) MOD a = (gcd a b) MOD a
Proof
  metis_tac[gcd_linear_mod_thm, MOD_TIMES]
QED

(* Idea: symmetric version of of gcd_linear_mod_1. *)

(* Theorem: 0 < b ==> ?p. (p * a) MOD b = (gcd a b) MOD b *)
(* Proof:
   Note ?p. (p * a) MOD b = (gcd b a) MOD b    by gcd_linear_mod_1
     or                   = (gcd a b) MOD b    by GCD_SYM
*)
Theorem gcd_linear_mod_2:
  !a b. 0 < b ==> ?p. (p * a) MOD b = (gcd a b) MOD b
Proof
  metis_tac[gcd_linear_mod_1, GCD_SYM]
QED

(* Idea: replacing n = a * b in gcd_linear_mod_thm. *)

(* Theorem: 0 < a /\ 0 < b ==> ?p q. (p * a + q * b) MOD (a * b) = (gcd a b) MOD (a * b) *)
(* Proof: by gcd_linear_mod_thm, n = a * b. *)
Theorem gcd_linear_mod_prod:
  !a b. 0 < a /\ 0 < b ==> ?p q. (p * a + q * b) MOD (a * b) = (gcd a b) MOD (a * b)
Proof
  simp[gcd_linear_mod_thm]
QED

(* Idea: specialise gcd_linear_mod_prod for coprime a b. *)

(* Theorem: 0 < a /\ 0 < b /\ coprime a b ==>
            ?p q. (p * a + q * b) MOD (a * b) = 1 MOD (a * b) *)
(* Proof: by gcd_linear_mod_prod. *)
Theorem coprime_linear_mod_prod:
  !a b. 0 < a /\ 0 < b /\ coprime a b ==>
  ?p q. (p * a + q * b) MOD (a * b) = 1 MOD (a * b)
Proof
  metis_tac[gcd_linear_mod_prod]
QED

(* Idea: generalise gcd_linear_mod_thm for multiple of gcd a b. *)

(* Theorem: 0 < n /\ 0 < a /\ gcd a b divides c ==>
            ?p q. (p * a + q * b) MOD n = c MOD n *)
(* Proof:
   Let d = gcd a b.
   Note k. c = k * d                           by divides_def
    and ?p q. (p * a + q * b) MOD n = d MOD n  by gcd_linear_mod_thm
   Thus (k * d) MOD n
      = (k * (p * a + q * b)) MOD n            by MOD_TIMES2, 0 < n
      = (k * p * a + k * q * b) MOD n          by LEFT_ADD_DISTRIB
   Take (k * p) and (k * q) for the eventual p and q.
*)
Theorem gcd_multiple_linear_mod_thm:
  !n a b c. 0 < n /\ 0 < a /\ gcd a b divides c ==>
            ?p q. (p * a + q * b) MOD n = c MOD n
Proof
  rpt strip_tac >>
  qabbrev_tac `d = gcd a b` >>
  `?k. c = k * d` by rw[GSYM divides_def] >>
  `?p q. (p * a + q * b) MOD n = d MOD n` by metis_tac[gcd_linear_mod_thm] >>
  `(k * (p * a + q * b)) MOD n = (k * d) MOD n` by metis_tac[MOD_TIMES2] >>
  `k * (p * a + q * b) = k * p * a + k * q * b` by decide_tac >>
  metis_tac[]
QED

(* Idea: specialise gcd_multiple_linear_mod_thm for n = a * b. *)

(* Theorem: 0 < a /\ 0 < b /\ gcd a b divides c ==>
            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)) *)
(* Proof: by gcd_multiple_linear_mod_thm. *)
Theorem gcd_multiple_linear_mod_prod:
  !a b c. 0 < a /\ 0 < b /\ gcd a b divides c ==>
          ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)
Proof
  simp[gcd_multiple_linear_mod_thm]
QED

(* Idea: specialise gcd_multiple_linear_mod_prod for coprime a b. *)

(* Theorem: 0 < a /\ 0 < b /\ coprime a b ==>
            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b) *)
(* Proof:
   Note coprime a b means gcd a b = 1    by notation
    and 1 divides c                      by ONE_DIVIDES_ALL
     so the result follows               by gcd_multiple_linear_mod_prod
*)
Theorem coprime_multiple_linear_mod_prod:
  !a b c. 0 < a /\ 0 < b /\ coprime a b ==>
          ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)
Proof
  metis_tac[gcd_multiple_linear_mod_prod, ONE_DIVIDES_ALL]
QED

(* ------------------------------------------------------------------------- *)
(* Coprime Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> !a b. coprime a b <=> coprime a (b ** n) *)
(* Proof:
   If part: coprime a b ==> coprime a (b ** n)
      True by coprime_exp_comm.
   Only-if part: coprime a (b ** n) ==> coprime a b
      If a = 0,
         then b ** n = 1        by GCD_0L
          and b = 1             by EXP_EQ_1, n <> 0
         Hence coprime 0 1      by GCD_0L
      If a <> 0,
      Since coprime a (b ** n) means
            ?h k. h * a = k * b ** n + 1   by LINEAR_GCD, GCD_SYM
   Let d = gcd a b.
   Since d divides a and d divides b       by GCD_IS_GREATEST_COMMON_DIVISOR
     and d divides b ** n                  by divides_exp, 0 < n
      so d divides 1                       by divides_linear_sub
    Thus d = 1                             by DIVIDES_ONE
      or coprime a b                       by notation
*)
val coprime_iff_coprime_exp = store_thm(
  "coprime_iff_coprime_exp",
  ``!n. 0 < n ==> !a b. coprime a b <=> coprime a (b ** n)``,
  rw[EQ_IMP_THM] >-
  rw[coprime_exp_comm] >>
  `n <> 0` by decide_tac >>
  Cases_on `a = 0` >-
  metis_tac[GCD_0L, EXP_EQ_1] >>
  `?h k. h * a = k * b ** n + 1` by metis_tac[LINEAR_GCD, GCD_SYM] >>
  qabbrev_tac `d = gcd a b` >>
  `d divides a /\ d divides b` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides (b ** n)` by rw[divides_exp] >>
  `d divides 1` by metis_tac[divides_linear_sub] >>
  rw[GSYM DIVIDES_ONE]);

(* Theorem: 1 < n /\ coprime n m ==> ~(n divides m) *)
(* Proof:
       coprime n m
   ==> gcd n m = 1       by notation
   ==> n MOD m <> 0      by MOD_NONZERO_WHEN_GCD_ONE, with 1 < n
   ==> ~(n divides m)    by DIVIDES_MOD_0, with 0 < n
*)
val coprime_not_divides = store_thm(
  "coprime_not_divides",
  ``!m n. 1 < n /\ coprime n m ==> ~(n divides m)``,
  metis_tac[MOD_NONZERO_WHEN_GCD_ONE, DIVIDES_MOD_0, ONE_LT_POS, NOT_ZERO_LT_ZERO]);

(* Theorem: 1 < n ==> (!j. 0 < j /\ j <= m ==> coprime n j) ==> m < n *)
(* Proof:
   By contradiction. Suppose n <= m.
   Since 1 < n means 0 < n and n <> 1,
   The implication shows
       coprime n n, or n = 1   by notation
   But gcd n n = n             by GCD_REF
   This contradicts n <> 1.
*)
val coprime_all_le_imp_lt = store_thm(
  "coprime_all_le_imp_lt",
  ``!n. 1 < n ==> !m. (!j. 0 < j /\ j <= m ==> coprime n j) ==> m < n``,
  spose_not_then strip_assume_tac >>
  `n <= m` by decide_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  metis_tac[GCD_REF]);

(* Theorem: (!j. 1 < j /\ j <= m ==> ~(j divides n)) <=> (!j. 1 < j /\ j <= m ==> coprime j n) *)
(* Proof:
   If part: (!j. 1 < j /\ j <= m ==> ~(j divides n)) /\ 1 < j /\ j <= m ==> coprime j n
      Let d = gcd j n.
      Then d divides j /\ d divides n         by GCD_IS_GREATEST_COMMON_DIVISOR
       Now 1 < j ==> 0 < j /\ j <> 0
        so d <= j                             by DIVIDES_LE, 0 < j
       and d <> 0                             by GCD_EQ_0, j <> 0
      By contradiction, suppose d <> 1.
      Then 1 < d /\ d <= m                    by d <> 1, d <= j /\ j <= m
        so ~(d divides n), a contradiction    by implication

   Only-if part: (!j. 1 < j /\ j <= m ==> coprime j n) /\ 1 < j /\ j <= m ==> ~(j divides n)
      Since coprime j n                       by implication
         so ~(j divides n)                    by coprime_not_divides
*)
val coprime_condition = store_thm(
  "coprime_condition",
  ``!m n. (!j. 1 < j /\ j <= m ==> ~(j divides n)) <=> (!j. 1 < j /\ j <= m ==> coprime j n)``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `d = gcd j n` >>
    `d divides j /\ d divides n` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
    `0 < j /\ j <> 0` by decide_tac >>
    `d <= j` by rw[DIVIDES_LE] >>
    `d <> 0` by metis_tac[GCD_EQ_0] >>
    `1 < d /\ d <= m` by decide_tac >>
    metis_tac[],
    metis_tac[coprime_not_divides]
  ]);

(* Note:
The above is the generalization of this observation:
- a prime n  has all 1 < j < n coprime to n. Therefore,
- a number n has all 1 < j < m coprime to n, where m is the first non-trivial factor of n.
  Of course, the first non-trivial factor of n must be a prime.
*)

(* Theorem: 1 < m /\ (!j. 1 < j /\ j <= m ==> ~(j divides n)) ==> coprime m n *)
(* Proof: by coprime_condition, taking j = m. *)
val coprime_by_le_not_divides = store_thm(
  "coprime_by_le_not_divides",
  ``!m n. 1 < m /\ (!j. 1 < j /\ j <= m ==> ~(j divides n)) ==> coprime m n``,
  rw[coprime_condition]);

(* Idea: establish coprime (p * a + q * b) (a * b). *)
(* Note: the key is to apply coprime_by_prime_factor. *)

(* Theorem: coprime a b /\ coprime p b /\ coprime q a ==> coprime (p * a + q * b) (a * b) *)
(* Proof:
   Let z = p * a + q * b, c = a * b, d = gcd z c.
   Then d divides z /\ d divides c       by GCD_PROPERTY
   By coprime_by_prime_factor, we need to show:
      !t. prime t ==> ~(t divides z /\ t divides c)
   By contradiction, suppose t divides z /\ t divides c.
   Then t divides d                      by GCD_PROPERTY
     or t divides c where c = a * b      by DIVIDES_TRANS
     so t divides a or p divides b       by P_EUCLIDES

   If t divides a,
      Then t divides (q * b)             by divides_linear_sub
       and ~(t divides b)                by coprime_common_factor, NOT_PRIME_1
        so t divides q                   by P_EUCLIDES
       ==> t = 1                         by coprime_common_factor
       This contradicts prime t          by NOT_PRIME_1
   If t divides b,
      Then t divides (p * a)             by divides_linear_sub
       and ~(t divides a)                by coprime_common_factor, NOT_PRIME_1
        so t divides p                   by P_EUCLIDES
       ==> t = 1                         by coprime_common_factor
       This contradicts prime t          by NOT_PRIME_1
   Since all lead to contradiction, we have shown:
     !t. prime t ==> ~(t divides z /\ t divides c)
   Thus coprime z c                      by coprime_by_prime_factor
*)
Theorem coprime_linear_mult:
  !a b p q. coprime a b /\ coprime p b /\ coprime q a ==> coprime (p * a + q * b) (a * b)
Proof
  rpt strip_tac >>
  qabbrev_tac `z = p * a + q * b` >>
  qabbrev_tac `c = a * b` >>
  irule (coprime_by_prime_factor |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >>
  `p' divides a \/ p' divides b` by metis_tac[P_EUCLIDES] >| [
    `p' divides (q * b)` by metis_tac[divides_linear_sub, MULT_LEFT_1] >>
    `~(p' divides b)` by metis_tac[coprime_common_factor, NOT_PRIME_1] >>
    `p' divides q` by metis_tac[P_EUCLIDES] >>
    metis_tac[coprime_common_factor, NOT_PRIME_1],
    `p' divides (p * a)` by metis_tac[divides_linear_sub, MULT_LEFT_1, ADD_COMM] >>
    `~(p' divides a)` by metis_tac[coprime_common_factor, NOT_PRIME_1, MULT_COMM] >>
    `p' divides p` by metis_tac[P_EUCLIDES] >>
    metis_tac[coprime_common_factor, NOT_PRIME_1]
  ]
QED

(* Idea: include converse of coprime_linear_mult. *)

(* Theorem: coprime a b ==>
            ((coprime p b /\ coprime q a) <=> coprime (p * a + q * b) (a * b)) *)
(* Proof:
   If part: coprime p b /\ coprime q a ==> coprime (p * a + q * b) (a * b)
      This is true by coprime_linear_mult.
   Only-if: coprime (p * a + q * b) (a * b) ==> coprime p b /\ coprime q a
      Let z = p * a + q * b. Consider a prime t.
      For coprime p b.
          If t divides p /\ t divides b,
          Then t divides z         by divides_linear
           and t divides (a * b)   by DIVIDES_MULTIPLE
            so t = 1               by coprime_common_factor
          This contradicts prime t by NOT_PRIME_1
          Thus coprime p b         by coprime_by_prime_factor
      For coprime q a.
          If t divides q /\ t divides a,
          Then t divides z         by divides_linear
           and t divides (a * b)   by DIVIDES_MULTIPLE
            so t = 1               by coprime_common_factor
          This contradicts prime t by NOT_PRIME_1
          Thus coprime q a         by coprime_by_prime_factor
*)
Theorem coprime_linear_mult_iff:
  !a b p q. coprime a b ==>
            ((coprime p b /\ coprime q a) <=> coprime (p * a + q * b) (a * b))
Proof
  rw_tac std_ss[EQ_IMP_THM] >-
  simp[coprime_linear_mult] >-
 (irule (coprime_by_prime_factor |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >>
  `p' divides (p * a + q * b)` by metis_tac[divides_linear, MULT_COMM] >>
  `p' divides (a * b)` by rw[DIVIDES_MULTIPLE] >>
  metis_tac[coprime_common_factor, NOT_PRIME_1]) >>
  irule (coprime_by_prime_factor |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >>
  `p' divides (p * a + q * b)` by metis_tac[divides_linear, MULT_COMM] >>
  `p' divides (a * b)` by metis_tac[DIVIDES_MULTIPLE, MULT_COMM] >>
  metis_tac[coprime_common_factor, NOT_PRIME_1]
QED

(* Idea: condition for a number to be coprime with prime power. *)

(* Theorem: prime p /\ 0 < n ==> !q. coprime q (p ** n) <=> ~(p divides q) *)
(* Proof:
   If part: prime p /\ 0 < n /\ coprime q (p ** n) ==> ~(p divides q)
      By contradiction, suppose p divides q.
      Note p divides (p ** n)  by prime_divides_self_power, 0 < n
      Thus p = 1               by coprime_common_factor
      This contradicts p <> 1  by NOT_PRIME_1
   Only-if part: prime p /\ 0 < n /\ ~(p divides q) ==> coprime q (p ** n)
      Note coprime q p         by prime_not_divides_coprime, GCD_SYM
      Thus coprime q (p ** n)  by coprime_iff_coprime_exp, 0 < n
*)
Theorem coprime_prime_power:
  !p n. prime p /\ 0 < n ==> !q. coprime q (p ** n) <=> ~(p divides q)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[prime_divides_self_power, coprime_common_factor, NOT_PRIME_1] >>
  metis_tac[prime_not_divides_coprime, coprime_iff_coprime_exp, GCD_SYM]
QED

(* Theorem: prime n ==> !m. 0 < m /\ m < n ==> coprime n m *)
(* Proof:
   By contradiction. Let d = gcd n m, and d <> 1.
   Since prime n, 0 < n       by PRIME_POS
   Thus d divides n, and d m divides    by GCD_IS_GREATEST_COMMON_DIVISOR, n <> 0, m <> 0.
   ==>  d = n                           by prime_def, d <> 1.
   ==>  n divides m                     by d divides m
   ==>  n <= m                          by DIVIDES_LE
   which contradicts m < n.
*)
val prime_coprime_all_lt = store_thm(
  "prime_coprime_all_lt",
  ``!n. prime n ==> !m. 0 < m /\ m < n ==> coprime n m``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd n m` >>
  `0 < n` by rw[PRIME_POS] >>
  `n <> 0 /\ m <> 0` by decide_tac >>
  `d divides n /\ d divides m` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d = n` by metis_tac[prime_def] >>
  `n <= m` by rw[DIVIDES_LE] >>
  decide_tac);

(* Theorem: prime n /\ m < n ==> (!j. 0 < j /\ j <= m ==> coprime n j) *)
(* Proof:
   Since m < n, all j < n.
   Hence true by prime_coprime_all_lt
*)
val prime_coprime_all_less = store_thm(
  "prime_coprime_all_less",
  ``!m n. prime n /\ m < n ==> (!j. 0 < j /\ j <= m ==> coprime n j)``,
  rpt strip_tac >>
  `j < n` by decide_tac >>
  rw[prime_coprime_all_lt]);

(* Theorem: prime n <=> 1 < n /\ (!j. 0 < j /\ j < n ==> coprime n j)) *)
(* Proof:
   If part: prime n ==> 1 < n /\ !j. 0 < j /\ j < n ==> coprime n j
      (1) prime n ==> 1 < n                          by ONE_LT_PRIME
      (2) prime n /\ 0 < j /\ j < n ==> coprime n j  by prime_coprime_all_lt
   Only-if part: !j. 0 < j /\ j < n ==> coprime n j ==> prime n
      By contradiction, assume ~prime n.
      Now, 1 < n /\ ~prime n
      ==> ?p. prime p /\ p < n /\ p divides n   by PRIME_FACTOR_PROPER
      and prime p ==> 0 < p and 1 < p           by PRIME_POS, ONE_LT_PRIME
      Hence ~coprime p n                        by coprime_not_divides, 1 < p
      But 0 < p < n ==> coprime n p             by given implication
      This is a contradiction                   by coprime_sym
*)
val prime_iff_coprime_all_lt = store_thm(
  "prime_iff_coprime_all_lt",
  ``!n. prime n <=> 1 < n /\ (!j. 0 < j /\ j < n ==> coprime n j)``,
  rw[EQ_IMP_THM, ONE_LT_PRIME] >-
  rw[prime_coprime_all_lt] >>
  spose_not_then strip_assume_tac >>
  `?p. prime p /\ p < n /\ p divides n` by rw[PRIME_FACTOR_PROPER] >>
  `0 < p` by rw[PRIME_POS] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  metis_tac[coprime_not_divides, coprime_sym]);

(* Theorem: prime n <=> (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n))) *)
(* Proof:
   If part: prime n ==> (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n)))
      Note 1 < n                 by ONE_LT_PRIME
      By contradiction, suppose j divides n.
      Then j = 1 or j = n        by prime_def
      This contradicts 1 < j /\ j < n.
   Only-if part: (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n))) ==> prime n
      This is to show:
      !b. b divides n ==> b = 1 or b = n    by prime_def
      Since 1 < n, so n <> 0     by arithmetic
      Thus b <= n                by DIVIDES_LE
       and b <> 0                by ZERO_DIVIDES
      By contradiction, suppose b <> 1 and b <> n, but b divides n.
      Then 1 < b /\ b < n        by above
      giving ~(b divides n)      by implication
      This contradicts with b divides n.
*)
val prime_iff_no_proper_factor = store_thm(
  "prime_iff_no_proper_factor",
  ``!n. prime n <=> (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n)))``,
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[ONE_LT_PRIME] >-
  metis_tac[prime_def, LESS_NOT_EQ] >>
  rw[prime_def] >>
  `b <= n` by rw[DIVIDES_LE] >>
  `n <> 0` by decide_tac >>
  `b <> 0` by metis_tac[ZERO_DIVIDES] >>
  spose_not_then strip_assume_tac >>
  `1 < b /\ b < n` by decide_tac >>
  metis_tac[]);

(* Theorem: FINITE s ==> !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s) *)
(* Proof:
   By finite induction on s.
   Base: coprime x (PROD_SET {})
      Note PROD_SET {} = 1         by PROD_SET_EMPTY
       and coprime x 1 = T         by GCD_1
   Step: !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s) ==>
        e NOTIN s /\ x NOTIN e INSERT s /\ !z. z IN e INSERT s ==> coprime x z ==>
        coprime x (PROD_SET (e INSERT s))
      Note coprime x e                               by IN_INSERT
       and coprime x (PROD_SET s)                    by induction hypothesis
      Thus coprime x (e * PROD_SET s)                by coprime_product_coprime_sym
        or coprime x PROD_SET (e INSERT s)           by PROD_SET_INSERT
*)
val every_coprime_prod_set_coprime = store_thm(
  "every_coprime_prod_set_coprime",
  ``!s. FINITE s ==> !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY] >>
  fs[] >>
  rw[PROD_SET_INSERT, coprime_product_coprime_sym]);

(* ------------------------------------------------------------------------- *)
(* GCD divisibility condition of Power Predecessors                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < t /\ m <= n ==>
           (t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1)) *)
(* Proof:
   Note !n. 1 <= t ** n                  by ONE_LE_EXP, 0 < t, [1]

   Claim: t ** (n - m) - 1 <= t ** n - 1, because:
   Proof: Note n - m <= n                always
            so t ** (n - m) <= t ** n    by EXP_BASE_LEQ_MONO_IMP, 0 < t
           Now 1 <= t ** (n - m) and
               1 <= t ** n               by [1]
           Hence t ** (n - m) - 1 <= t ** n - 1.

        t ** (n - m) * (t ** m - 1) + t ** (n - m) - 1
      = (t ** (n - m) * t ** m - t ** (n - m)) + t ** (n - m) - 1   by LEFT_SUB_DISTRIB
      = (t ** (n - m + m) - t ** (n - m)) + t ** (n - m) - 1        by EXP_ADD
      = (t ** n - t ** (n - m)) + t ** (n - m) - 1                  by SUB_ADD, m <= n
      = (t ** n - (t ** (n - m) - 1 + 1)) + t ** (n - m) - 1        by SUB_ADD, 1 <= t ** (n - m)
      = (t ** n - (1 + (t ** (n - m) - 1))) + t ** (n - m) - 1      by ADD_COMM
      = (t ** n - 1 - (t ** (n - m) - 1)) + t ** (n - m) - 1        by SUB_PLUS, no condition
      = t ** n - 1                                 by SUB_ADD, t ** (n - m) - 1 <= t ** n - 1
*)
val power_predecessor_division_eqn = store_thm(
  "power_predecessor_division_eqn",
  ``!t m n. 0 < t /\ m <= n ==>
           (t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1))``,
  rpt strip_tac >>
  `1 <= t ** n /\ 1 <= t ** (n - m)` by rw[ONE_LE_EXP] >>
  `n - m <= n` by decide_tac >>
  `t ** (n - m) <= t ** n` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  `t ** (n - m) - 1 <= t ** n - 1` by decide_tac >>
  qabbrev_tac `z = t ** (n - m) - 1` >>
  `t ** (n - m) * (t ** m - 1) + z =
    t ** (n - m) * t ** m - t ** (n - m) + z` by decide_tac >>
  `_ = t ** (n - m + m) - t ** (n - m) + z` by rw_tac std_ss[EXP_ADD] >>
  `_ = t ** n - t ** (n - m) + z` by rw_tac std_ss[SUB_ADD] >>
  `_ = t ** n - (z + 1) + z` by rw_tac std_ss[SUB_ADD, Abbr`z`] >>
  `_ = t ** n + z - (z + 1)` by decide_tac >>
  `_ = t ** n - 1` by decide_tac >>
  decide_tac);

(* This shows the pattern:
                    1000000    so 9999999999 = 1000000 * 9999 + 999999
               ------------    or (b ** 10 - 1) = b ** 6 * (b ** 4 - 1) + (b ** 6 - 1)
          9999 | 9999999999    where b = 10.
                 9999
                 ----------
                     999999
*)

(* Theorem: 0 < t /\ m <= n ==>
           (t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1) *)
(* Proof: by power_predecessor_division_eqn *)
val power_predecessor_division_alt = store_thm(
  "power_predecessor_division_alt",
  ``!t m n. 0 < t /\ m <= n ==>
           (t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1)``,
  rpt strip_tac >>
  imp_res_tac power_predecessor_division_eqn >>
  fs[]);

(* Theorem: m < n ==> (gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** m - 1)) (t ** (n - m) - 1)) *)
(* Proof:
   Case t = 0,
      If n = 0, t ** 0 = 1             by ZERO_EXP
      LHS = gcd 0 x = 0                by GCD_0L
          = gcd 0 y = RHS              by ZERO_EXP
      If n <> 0, 0 ** n = 0            by ZERO_EXP
      LHS = gcd (0 - 1) x
          = gcd 0 x = 0                by GCD_0L
          = gcd 0 y = RHS              by ZERO_EXP
   Case t <> 0,
      Note t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1)
                                       by power_predecessor_division_eqn
        so t ** (n - m) * (t ** m - 1) <= t ** n - 1    by above, [1]
       and t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1, [2]
        gcd (t ** n - 1) (t ** m - 1)
      = gcd (t ** m - 1) (t ** n - 1)                by GCD_SYM
      = gcd (t ** m - 1) ((t ** n - 1) - t ** (n - m) * (t ** m - 1))
                                                     by GCD_SUB_MULTIPLE, [1]
      = gcd (t ** m - 1)) (t ** (n - m) - 1)         by [2]
*)
val power_predecessor_gcd_reduction = store_thm(
  "power_predecessor_gcd_reduction",
  ``!t n m. m <= n ==> (gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** m - 1)) (t ** (n - m) - 1))``,
  rpt strip_tac >>
  Cases_on `t = 0` >-
  rw[ZERO_EXP] >>
  `t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1)` by rw[power_predecessor_division_eqn] >>
  `t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1` by fs[] >>
  `gcd (t ** n - 1) (t ** m - 1) = gcd (t ** m - 1) (t ** n - 1)` by rw_tac std_ss[GCD_SYM] >>
  `_ = gcd (t ** m - 1) ((t ** n - 1) - t ** (n - m) * (t ** m - 1))` by rw_tac std_ss[GCD_SUB_MULTIPLE] >>
  rw_tac std_ss[]);

(* Theorem: gcd (t ** n - 1) (t ** m - 1) = t ** (gcd n m) - 1 *)
(* Proof:
   By complete induction on (n + m):
   Induction hypothesis: !m'. m' < n + m ==>
                         !n m. (m' = n + m) ==> (gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1)
   Idea: if 0 < m, n < n + m. Put last n = m, m = n - m. That is m' = m + (n - m) = n.
   Also  if 0 < n, m < n + m. Put last n = n, m = m - n. That is m' = n + (m - n) = m.

   Thus to apply induction hypothesis, need 0 < n or 0 < m.
   So take care of these special cases first.

   Case: n = 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         LHS = gcd (t ** 0 - 1) (t ** m - 1)
             = gcd 0 (t ** m - 1)                 by EXP
             = t ** m - 1                         by GCD_0L
             = t ** (gcd 0 m) - 1 = RHS           by GCD_0L
   Case: m = 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         LHS = gcd (t ** n - 1) (t ** 0 - 1)
             = gcd (t ** n - 1) 0                 by EXP
             = t ** n - 1                         by GCD_0R
             = t ** (gcd n 0) - 1 = RHS           by GCD_0R

   Case: m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
      That is, 0 < n, and 0 < m
          also n < n + m, and m < n + m           by arithmetic

      Use trichotomy of numbers:                  by LESS_LESS_CASES
      Case: n = m /\ m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         LHS = gcd (t ** m - 1) (t ** m - 1)
             = t ** m - 1                         by GCD_REF
             = t ** (gcd m m) - 1 = RHS           by GCD_REF

      Case: m < n /\ m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         Since n < n + m                          by 0 < m
           and m + (n - m) = (n - m) + m          by ADD_COMM
                           = n                    by SUB_ADD, m <= n
           gcd (t ** n - 1) (t ** m - 1)
         = gcd ((t ** m - 1)) (t ** (n - m) - 1)  by power_predecessor_gcd_reduction
         = t ** gcd m (n - m) - 1                 by induction hypothesis, m + (n - m) = n
         = t ** gcd m n - 1                       by GCD_SUB_R, m <= n
         = t ** gcd n m - 1                       by GCD_SYM

      Case: n < m /\ m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         Since m < n + m                          by 0 < n
           and n + (m - n) = (m - n) + n          by ADD_COMM
                           = m                    by SUB_ADD, n <= m
          gcd (t ** n - 1) (t ** m - 1)
        = gcd (t ** m - 1) (t ** n - 1)           by GCD_SYM
        = gcd ((t ** n - 1)) (t ** (m - n) - 1)   by power_predecessor_gcd_reduction
        = t ** gcd n (m - n) - 1                  by induction hypothesis, n + (m - n) = m
        = t ** gcd n m                            by GCD_SUB_R, n <= m
*)
val power_predecessor_gcd_identity = store_thm(
  "power_predecessor_gcd_identity",
  ``!t n m. gcd (t ** n - 1) (t ** m - 1) = t ** (gcd n m) - 1``,
  rpt strip_tac >>
  completeInduct_on `n + m` >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[EXP] >>
  Cases_on `m = 0` >-
  rw[EXP] >>
  `(n = m) \/ (m < n) \/ (n < m)` by metis_tac[LESS_LESS_CASES] >-
  rw[GCD_REF] >-
 (`0 < m /\ n < n + m` by decide_tac >>
  `m <= n` by decide_tac >>
  `m + (n - m) = n` by metis_tac[SUB_ADD, ADD_COMM] >>
  `gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** m - 1)) (t ** (n - m) - 1)` by rw[power_predecessor_gcd_reduction] >>
  `_ = t ** gcd m (n - m) - 1` by metis_tac[] >>
  metis_tac[GCD_SUB_R, GCD_SYM]) >>
  `0 < n /\ m < n + m` by decide_tac >>
  `n <= m` by decide_tac >>
  `n + (m - n) = m` by metis_tac[SUB_ADD, ADD_COMM] >>
  `gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** n - 1)) (t ** (m - n) - 1)` by rw[power_predecessor_gcd_reduction, GCD_SYM] >>
  `_ = t ** gcd n (m - n) - 1` by metis_tac[] >>
  metis_tac[GCD_SUB_R]);

(* Above is the formal proof of the following pattern:
   For any base
         gcd(999999,9999) = gcd(6 9s, 4 9s) = gcd(6,4) 9s = 2 9s = 99
   or        999999 MOD 9999 = (6 9s) MOD (4 9s) = 2 9s = 99
   Thus in general,
             (m 9s) MOD (n 9s) = (m MOD n) 9s
   Repeating the use of Euclidean algorithm then gives:
             gcd (m 9s, n 9s) = (gcd m n) 9s

Reference: A Mathematical Tapestry (by Jean Pedersen and Peter Hilton)
Chapter 4: A number-theory thread -- Folding numbers, a number trick, and some tidbits.
*)

(* Theorem: 1 < t ==> ((t ** n - 1) divides (t ** m - 1) <=> n divides m) *)
(* Proof:
       (t ** n - 1) divides (t ** m - 1)
   <=> gcd (t ** n - 1) (t ** m - 1) = t ** n - 1   by divides_iff_gcd_fix
   <=> t ** (gcd n m) - 1 = t ** n - 1              by power_predecessor_gcd_identity
   <=> t ** (gcd n m) = t ** n                      by PRE_SUB1, INV_PRE_EQ, EXP_POS, 0 < t
   <=>       gcd n m = n                            by EXP_BASE_INJECTIVE, 1 < t
   <=>       n divides m                            by divides_iff_gcd_fix
*)
val power_predecessor_divisibility = store_thm(
  "power_predecessor_divisibility",
  ``!t n m. 1 < t ==> ((t ** n - 1) divides (t ** m - 1) <=> n divides m)``,
  rpt strip_tac >>
  `0 < t` by decide_tac >>
  `!n. 0 < t ** n` by rw[EXP_POS] >>
  `!x y. 0 < x /\ 0 < y ==> ((x - 1 = y - 1) <=> (x = y))` by decide_tac >>
  `(t ** n - 1) divides (t ** m - 1) <=> ((gcd (t ** n - 1) (t ** m - 1) = t ** n - 1))` by rw[divides_iff_gcd_fix] >>
  `_ = (t ** (gcd n m) - 1 = t ** n - 1)` by rw[power_predecessor_gcd_identity] >>
  `_ = (t ** (gcd n m) = t ** n)` by rw[] >>
  `_ = (gcd n m = n)` by rw[EXP_BASE_INJECTIVE] >>
  rw[divides_iff_gcd_fix]);

(* Theorem: t - 1 divides t ** n - 1 *)
(* Proof:
   If t = 0,
      Then t - 1 = 0        by integer subtraction
       and t ** n - 1 = 0   by ZERO_EXP, either case of n.
      Thus 0 divides 0      by ZERO_DIVIDES
   If t = 1,
      Then t - 1 = 0        by arithmetic
       and t ** n - 1 = 0   by EXP_1
      Thus 0 divides 0      by ZERO_DIVIDES
   Otherwise, 1 < t
       and 1 divides n      by ONE_DIVIDES_ALL
       ==> t ** 1 - 1 divides t ** n - 1   by power_predecessor_divisibility
        or      t - 1 divides t ** n - 1   by EXP_1
*)
Theorem power_predecessor_divisor:
  !t n. t - 1 divides t ** n - 1
Proof
  rpt strip_tac >>
  Cases_on `t = 0` >-
  simp[ZERO_EXP] >>
  Cases_on `t = 1` >-
  simp[] >>
  `1 < t` by decide_tac >>
  metis_tac[power_predecessor_divisibility, EXP_1, ONE_DIVIDES_ALL]
QED

(* Overload power predecessor *)
Overload tops = “\b:num n. b ** n - 1”

(*
   power_predecessor_division_eqn
     |- !t m n. 0 < t /\ m <= n ==> tops t n = t ** (n - m) * tops t m + tops t (n - m)
   power_predecessor_division_alt
     |- !t m n. 0 < t /\ m <= n ==> tops t n - t ** (n - m) * tops t m = tops t (n - m)
   power_predecessor_gcd_reduction
     |- !t n m. m <= n ==> (gcd (tops t n) (tops t m) = gcd (tops t m) (tops t (n - m)))
   power_predecessor_gcd_identity
     |- !t n m. gcd (tops t n) (tops t m) = tops t (gcd n m)
   power_predecessor_divisibility
     |- !t n m. 1 < t ==> (tops t n divides tops t m <=> n divides m)
   power_predecessor_divisor
     |- !t n. t - 1 divides tops t n
*)

(* Overload power predecessor base 10 *)
val _ = overload_on("nines", ``\n. tops 10 n``);

(* Obtain corollaries *)

val nines_division_eqn = save_thm("nines_division_eqn",
    power_predecessor_division_eqn |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
val nines_division_alt = save_thm("nines_division_alt",
    power_predecessor_division_alt |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
val nines_gcd_reduction = save_thm("nines_gcd_reduction",
    power_predecessor_gcd_reduction |> ISPEC ``10``);
val nines_gcd_identity = save_thm("nines_gcd_identity",
    power_predecessor_gcd_identity |> ISPEC ``10``);
val nines_divisibility = save_thm("nines_divisibility",
    power_predecessor_divisibility |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
val nines_divisor = save_thm("nines_divisor",
    power_predecessor_divisor |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
(*
val nines_division_eqn =
   |- !m n. m <= n ==> nines n = 10 ** (n - m) * nines m + nines (n - m): thm
val nines_division_alt =
   |- !m n. m <= n ==> nines n - 10 ** (n - m) * nines m = nines (n - m): thm
val nines_gcd_reduction =
   |- !n m. m <= n ==> gcd (nines n) (nines m) = gcd (nines m) (nines (n - m)): thm
val nines_gcd_identity = |- !n m. gcd (nines n) (nines m) = nines (gcd n m): thm
val nines_divisibility = |- !n m. nines n divides nines m <=> n divides m: thm
val nines_divisor = |- !n. 9 divides nines n: thm
*)

(* ------------------------------------------------------------------------- *)
(* GCD involving Powers                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime m /\ prime n /\ m divides (n ** k) ==> (m = n) *)
(* Proof:
   By induction on k.
   Base: m divides n ** 0 ==> (m = n)
      Since n ** 0 = 1              by EXP
        and m divides 1 ==> m = 1   by DIVIDES_ONE
       This contradicts 1 < m       by ONE_LT_PRIME
   Step: m divides n ** k ==> (m = n) ==> m divides n ** SUC k ==> (m = n)
      Since n ** SUC k = n * n ** k           by EXP
       Also m divides n \/ m divides n ** k   by P_EUCLIDES
         If m divides n, then m = n           by prime_divides_only_self
         If m divides n ** k, then m = n      by induction hypothesis
*)
val prime_divides_prime_power = store_thm(
  "prime_divides_prime_power",
  ``!m n k. prime m /\ prime n /\ m divides (n ** k) ==> (m = n)``,
  rpt strip_tac >>
  Induct_on `k` >| [
    rpt strip_tac >>
    `1 < m` by rw[ONE_LT_PRIME] >>
    `m = 1` by metis_tac[EXP, DIVIDES_ONE] >>
    decide_tac,
    metis_tac[EXP, P_EUCLIDES, prime_divides_only_self]
  ]);

(* This is better than FACTOR_OUT_PRIME *)

(* Theorem: 0 < n /\ prime p ==> ?q m. (n = (p ** m) * q) /\ coprime p q *)
(* Proof:
   If p divides n,
      Then ?m. 0 < m /\ p ** m divides n /\
           !k. coprime (p ** k) (n DIV p ** m)   by FACTOR_OUT_PRIME
      Let q = n DIV (p ** m).
      Note 0 < p                                 by PRIME_POS
        so 0 < p ** m                            by EXP_POS, 0 < p
      Take this q and m,
      Then n = (p ** m) * q                      by DIVIDES_EQN_COMM
       and coprime p q                           by taking k = 1, EXP_1

   If ~(p divides n),
      Then coprime p n                           by prime_not_divides_coprime
      Let q = n, m = 0.
      Then n = 1 * q                             by EXP, MULT_LEFT_1
       and coprime p q.
*)
val prime_power_factor = store_thm(
  "prime_power_factor",
  ``!n p. 0 < n /\ prime p ==> ?q m. (n = (p ** m) * q) /\ coprime p q``,
  rpt strip_tac >>
  Cases_on `p divides n` >| [
    `?m. 0 < m /\ p ** m divides n /\ !k. coprime (p ** k) (n DIV p ** m)` by rw[FACTOR_OUT_PRIME] >>
    qabbrev_tac `q = n DIV (p ** m)` >>
    `0 < p` by rw[PRIME_POS] >>
    `0 < p ** m` by rw[EXP_POS] >>
    metis_tac[DIVIDES_EQN_COMM, EXP_1],
    `coprime p n` by rw[prime_not_divides_coprime] >>
    metis_tac[EXP, MULT_LEFT_1]
  ]);

(* Even this simple theorem is quite difficult to prove, why? *)
(* Because this needs a typical detective-style proof! *)

(* Theorem: prime p /\ a divides (p ** n) ==> ?j. j <= n /\ (a = p ** j) *)
(* Proof:
   Note 0 < p                by PRIME_POS
     so 0 < p ** n           by EXP_POS
   Thus 0 < a                by ZERO_DIVIDES
    ==> ?q m. (a = (p ** m) * q) /\ coprime p q    by prime_power_factor

   Claim: q = 1
   Proof: By contradiction, suppose q <> 1.
          Then ?t. prime t /\ t divides q          by PRIME_FACTOR, q <> 1
           Now q divides a           by divides_def
            so t divides (p ** n)    by DIVIDES_TRANS
           ==> t = p                 by prime_divides_prime_power
           But gcd t q = t           by divides_iff_gcd_fix
            or gcd p q = p           by t = p
           Yet p <> 1                by NOT_PRIME_1
            so this contradicts coprime p q.

   Thus a = p ** m                   by q = 1, Claim.
   Note p ** m <= p ** n             by DIVIDES_LE, 0 < p
    and 1 < p                        by ONE_LT_PRIME
    ==>      m <= n                  by EXP_BASE_LE_MONO, 1 < p
   Take j = m, and the result follows.
*)
val prime_power_divisor = store_thm(
  "prime_power_divisor",
  ``!p n a. prime p /\ a divides (p ** n) ==> ?j. j <= n /\ (a = p ** j)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `0 < p ** n` by rw[EXP_POS] >>
  `0 < a` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `?q m. (a = (p ** m) * q) /\ coprime p q` by rw[prime_power_factor] >>
  `q = 1` by
  (spose_not_then strip_assume_tac >>
  `?t. prime t /\ t divides q` by rw[PRIME_FACTOR] >>
  `q divides a` by metis_tac[divides_def] >>
  `t divides (p ** n)` by metis_tac[DIVIDES_TRANS] >>
  `t = p` by metis_tac[prime_divides_prime_power] >>
  `gcd t q = t` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[NOT_PRIME_1]) >>
  `a = p ** m` by rw[] >>
  metis_tac[DIVIDES_LE, EXP_BASE_LE_MONO, ONE_LT_PRIME]);

(* Theorem: prime p /\ prime q ==>
            !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n) *)
(* Proof:
   First goal: p = q.
      Since p divides p        by DIVIDES_REFL
        ==> p divides p ** m   by divides_exp, 0 < m.
         so p divides q ** n   by given, p ** m = q ** n
      Hence p = q              by prime_divides_prime_power
   Second goal: m = n.
      Note p = q               by first goal.
      Since 1 < p              by ONE_LT_PRIME
      Hence m = n              by EXP_BASE_INJECTIVE, 1 < p
*)
val prime_powers_eq = store_thm(
  "prime_powers_eq",
  ``!p q. prime p /\ prime q ==>
   !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n)``,
  ntac 6 strip_tac >>
  conj_asm1_tac >-
  metis_tac[divides_exp, prime_divides_prime_power, DIVIDES_REFL] >>
  metis_tac[EXP_BASE_INJECTIVE, ONE_LT_PRIME]);

(* Theorem: prime p /\ prime q /\ p <> q ==> !m n. coprime (p ** m) (q ** n) *)
(* Proof:
   Let d = gcd (p ** m) (q ** n).
   By contradiction, d <> 1.
   Then d divides (p ** m) /\ d divides (q ** n)   by GCD_PROPERTY
    ==> ?j. j <= m /\ (d = p ** j)                 by prime_power_divisor, prime p
    and ?k. k <= n /\ (d = q ** k)                 by prime_power_divisor, prime q
   Note j <> 0 /\ k <> 0                           by EXP_0
     or 0 < j /\ 0 < k                             by arithmetic
    ==> p = q, which contradicts p <> q            by prime_powers_eq
*)
val prime_powers_coprime = store_thm(
  "prime_powers_coprime",
  ``!p q. prime p /\ prime q /\ p <> q ==> !m n. coprime (p ** m) (q ** n)``,
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd (p ** m) (q ** n)` >>
  `d divides (p ** m) /\ d divides (q ** n)` by metis_tac[GCD_PROPERTY] >>
  metis_tac[prime_power_divisor, prime_powers_eq, EXP_0, NOT_ZERO_LT_ZERO]);

(*
val prime_powers_eq = |- !p q. prime p /\ prime q ==> !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n): thm
*)

(* Theorem: prime p /\ prime q ==> !m n. 0 < m ==> ((p ** m divides q ** n) <=> (p = q) /\ (m <= n)) *)
(* Proof:
   If part: p ** m divides q ** n ==> (p = q) /\ m <= n
      Note p divides (p ** m)         by prime_divides_self_power, 0 < m
        so p divides (q ** n)         by DIVIDES_TRANS
      Thus p = q                      by prime_divides_prime_power
      Note 1 < p                      by ONE_LT_PRIME
      Thus m <= n                     by power_divides_iff
   Only-if part: (p = q) /\ m <= n ==> p ** m divides q ** n
      Note 1 < p                      by ONE_LT_PRIME
      Thus p ** m divides q ** n      by power_divides_iff
*)
val prime_powers_divide = store_thm(
  "prime_powers_divide",
  ``!p q. prime p /\ prime q ==> !m n. 0 < m ==> ((p ** m divides q ** n) <=> (p = q) /\ (m <= n))``,
  metis_tac[ONE_LT_PRIME, divides_self_power, prime_divides_prime_power, power_divides_iff, DIVIDES_TRANS]);

(* Theorem: gcd (b ** m) (b ** n) = b ** (MIN m n) *)
(* Proof:
   If m = n,
      LHS = gcd (b ** n) (b ** n)
          = b ** n                     by GCD_REF
      RHS = b ** (MIN n n)
          = b ** n                     by MIN_IDEM
   If m < n,
      b ** n = b ** (n - m + m)        by arithmetic
             = b ** (n - m) * b ** m   by EXP_ADD
      so (b ** m) divides (b ** n)     by divides_def
      or gcd (b ** m) (b ** n)
       = b ** m                        by divides_iff_gcd_fix
       = b ** (MIN m n)                by MIN_DEF
   If ~(m < n), n < m.
      Similar argument as m < n, with m n exchanged, use GCD_SYM.
*)
val gcd_powers = store_thm(
  "gcd_powers",
  ``!b m n. gcd (b ** m) (b ** n) = b ** (MIN m n)``,
  rpt strip_tac >>
  Cases_on `m = n` >-
  rw[] >>
  Cases_on `m < n` >| [
    `b ** n = b ** (n - m + m)` by rw[] >>
    `_ = b ** (n - m) * b ** m` by rw[EXP_ADD] >>
    `(b ** m) divides (b ** n)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_gcd_fix, MIN_DEF],
    `n < m` by decide_tac >>
    `b ** m = b ** (m - n + n)` by rw[] >>
    `_ = b ** (m - n) * b ** n` by rw[EXP_ADD] >>
    `(b ** n) divides (b ** m)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_gcd_fix, GCD_SYM, MIN_DEF]
  ]);

(* Theorem: lcm (b ** m) (b ** n) = b ** (MAX m n) *)
(* Proof:
   If m = n,
      LHS = lcm (b ** n) (b ** n)
          = b ** n                     by LCM_REF
      RHS = b ** (MAX n n)
          = b ** n                     by MAX_IDEM
   If m < n,
      b ** n = b ** (n - m + m)        by arithmetic
             = b ** (n - m) * b ** m   by EXP_ADD
      so (b ** m) divides (b ** n)     by divides_def
      or lcm (b ** m) (b ** n)
       = b ** n                        by divides_iff_lcm_fix
       = b ** (MAX m n)                by MAX_DEF
   If ~(m < n), n < m.
      Similar argument as m < n, with m n exchanged, use LCM_COMM.
*)
val lcm_powers = store_thm(
  "lcm_powers",
  ``!b m n. lcm (b ** m) (b ** n) = b ** (MAX m n)``,
  rpt strip_tac >>
  Cases_on `m = n` >-
  rw[LCM_REF] >>
  Cases_on `m < n` >| [
    `b ** n = b ** (n - m + m)` by rw[] >>
    `_ = b ** (n - m) * b ** m` by rw[EXP_ADD] >>
    `(b ** m) divides (b ** n)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_lcm_fix, MAX_DEF],
    `n < m` by decide_tac >>
    `b ** m = b ** (m - n + n)` by rw[] >>
    `_ = b ** (m - n) * b ** n` by rw[EXP_ADD] >>
    `(b ** n) divides (b ** m)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_lcm_fix, LCM_COMM, MAX_DEF]
  ]);

(* Theorem: 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m - 1) *)
(* Proof:
   If m = n,
          coprime (b ** n) (b ** n - 1)
      <=> T                                by coprime_PRE

   Claim: !j. j < m ==> coprime (b ** j) (b ** m - 1)
   Proof: b ** m
        = b ** (m - j + j)                 by SUB_ADD
        = b ** (m - j) * b ** j            by EXP_ADD
     Thus (b ** j) divides (b ** m)        by divides_def
      Now 0 < b ** m                       by EXP_POS
       so coprime (b ** j) (PRE (b ** m))  by divides_imp_coprime_with_predecessor
       or coprime (b ** j) (b ** m - 1)    by PRE_SUB1

   Given 0 < m,
          b ** n
        = b ** ((n DIV m) * m + n MOD m)          by DIVISION
        = b ** (m * (n DIV m) + n MOD m)          by MULT_COMM
        = b ** (m * (n DIV m)) * b ** (n MOD m)   by EXP_ADD
        = (b ** m) ** (n DIV m) * b ** (n MOD m)  by EXP_EXP_MULT
   Let z = b ** m,
   Then b ** n = z ** (n DIV m) * b ** (n MOD m)
    and 0 < z                                     by EXP_POS
   Since coprime z (z - 1)                        by coprime_PRE
     ==> coprime (z ** (n DIV m)) (z - 1)         by coprime_exp
          gcd (b ** n) (b ** m - 1)
        = gcd (z ** (n DIV m) * b ** (n MOD m)) (z - 1)
        = gcd (b ** (n MOD m)) (z - 1)            by GCD_SYM, GCD_CANCEL_MULT
    Now (n MOD m) < m                             by MOD_LESS
    so apply the claim to deduce the result.
*)
val coprime_power_and_power_predecessor = store_thm(
  "coprime_power_and_power_predecessor",
  ``!b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m - 1)``,
  rpt strip_tac >>
  `0 < b ** n /\ 0 < b ** m` by rw[EXP_POS] >>
  Cases_on `m = n` >-
  rw[coprime_PRE] >>
  `!j. j < m ==> coprime (b ** j) (b ** m - 1)` by
  (rpt strip_tac >>
  `b ** m = b ** (m - j + j)` by rw[] >>
  `_ = b ** (m - j) * b ** j` by rw[EXP_ADD] >>
  `(b ** j) divides (b ** m)` by metis_tac[divides_def] >>
  metis_tac[divides_imp_coprime_with_predecessor, PRE_SUB1]) >>
  `b ** n = b ** ((n DIV m) * m + n MOD m)` by rw[GSYM DIVISION] >>
  `_ = b ** (m * (n DIV m) + n MOD m)` by rw[MULT_COMM] >>
  `_ = b ** (m * (n DIV m)) * b ** (n MOD m)` by rw[EXP_ADD] >>
  `_ = (b ** m) ** (n DIV m) * b ** (n MOD m)` by rw[EXP_EXP_MULT] >>
  qabbrev_tac `z = b ** m` >>
  `coprime z (z - 1)` by rw[coprime_PRE] >>
  `coprime (z ** (n DIV m)) (z - 1)` by rw[coprime_exp] >>
  metis_tac[GCD_SYM, GCD_CANCEL_MULT, MOD_LESS]);

(* Any counter-example? Theorem proved, no counter-example! *)
(* This is a most unexpected theorem.
   At first I thought it only holds for prime base b,
   but in HOL4 using the EVAL function shows it seems to hold for any base b.
   As for the proof, I don't have a clue initially.
   I try this idea:
   For a prime base b, most likely ODD b, then ODD (b ** n) and ODD (b ** m).
   But then EVEN (b ** m - 1), maybe ODD and EVEN will give coprime.
   If base b is EVEN, then EVEN (b ** n) but ODD (b ** m - 1), so this can work.
   However, in general ODD and EVEN do not give coprime:  gcd 6 9 = 3.
   Of course, if ODD and EVEN arise from powers of same base, like this theorem, then true!
   Actually this follows from divides_imp_coprime_with_predecessor, sort of.
   This success inspires the following theorem.
*)

(* Theorem: 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m + 1) *)
(* Proof:
   If m = n,
          coprime (b ** n) (b ** n + 1)
      <=> T                                by coprime_SUC

   Claim: !j. j < m ==> coprime (b ** j) (b ** m + 1)
   Proof: b ** m
        = b ** (m - j + j)                 by SUB_ADD
        = b ** (m - j) * b ** j            by EXP_ADD
     Thus (b ** j) divides (b ** m)        by divides_def
      Now 0 < b ** m                       by EXP_POS
       so coprime (b ** j) (SUC (b ** m))  by divides_imp_coprime_with_successor
       or coprime (b ** j) (b ** m + 1)    by ADD1

   Given 0 < m,
          b ** n
        = b ** ((n DIV m) * m + n MOD m)          by DIVISION
        = b ** (m * (n DIV m) + n MOD m)          by MULT_COMM
        = b ** (m * (n DIV m)) * b ** (n MOD m)   by EXP_ADD
        = (b ** m) ** (n DIV m) * b ** (n MOD m)  by EXP_EXP_MULT
   Let z = b ** m,
   Then b ** n = z ** (n DIV m) * b ** (n MOD m)
    and 0 < z                                     by EXP_POS
   Since coprime z (z + 1)                        by coprime_SUC
     ==> coprime (z ** (n DIV m)) (z + 1)         by coprime_exp
          gcd (b ** n) (b ** m + 1)
        = gcd (z ** (n DIV m) * b ** (n MOD m)) (z + 1)
        = gcd (b ** (n MOD m)) (z + 1)            by GCD_SYM, GCD_CANCEL_MULT
    Now (n MOD m) < m                             by MOD_LESS
    so apply the claim to deduce the result.
*)
val coprime_power_and_power_successor = store_thm(
  "coprime_power_and_power_successor",
  ``!b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m + 1)``,
  rpt strip_tac >>
  `0 < b ** n /\ 0 < b ** m` by rw[EXP_POS] >>
  Cases_on `m = n` >-
  rw[coprime_SUC] >>
  `!j. j < m ==> coprime (b ** j) (b ** m + 1)` by
  (rpt strip_tac >>
  `b ** m = b ** (m - j + j)` by rw[] >>
  `_ = b ** (m - j) * b ** j` by rw[EXP_ADD] >>
  `(b ** j) divides (b ** m)` by metis_tac[divides_def] >>
  metis_tac[divides_imp_coprime_with_successor, ADD1]) >>
  `b ** n = b ** ((n DIV m) * m + n MOD m)` by rw[GSYM DIVISION] >>
  `_ = b ** (m * (n DIV m) + n MOD m)` by rw[MULT_COMM] >>
  `_ = b ** (m * (n DIV m)) * b ** (n MOD m)` by rw[EXP_ADD] >>
  `_ = (b ** m) ** (n DIV m) * b ** (n MOD m)` by rw[EXP_EXP_MULT] >>
  qabbrev_tac `z = b ** m` >>
  `coprime z (z + 1)` by rw[coprime_SUC] >>
  `coprime (z ** (n DIV m)) (z + 1)` by rw[coprime_exp] >>
  metis_tac[GCD_SYM, GCD_CANCEL_MULT, MOD_LESS]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Note:
> type_of ``prime``;
val it = ":num -> bool": hol_type

Thus prime is also a set, or prime = {p | prime p}
*)

(* Theorem: p IN prime <=> prime p *)
(* Proof: by IN_DEF *)
val in_prime = store_thm(
  "in_prime",
  ``!p. p IN prime <=> prime p``,
  rw[IN_DEF]);

(* Theorem: (Generalized Euclid's Lemma)
            If prime p divides a PROD_SET, it divides a member of the PROD_SET.
            FINITE s ==> !p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b *)
(* Proof: by induction of the PROD_SET, apply Euclid's Lemma.
- P_EUCLIDES;
> val it =
    |- !p a b. prime p /\ p divides (a * b) ==> p divides a \/ p divides b : thm
   By finite induction on s.
   Base case: prime p /\ p divides (PROD_SET {}) ==> F
     Since PROD_SET {} = 1        by PROD_SET_THM
       and p divides 1 <=> p = 1  by DIVIDES_ONE
       but prime p ==> p <> 1     by NOT_PRIME_1
       This gives the contradiction.
   Step case: FINITE s /\ (!p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b) /\
              e NOTIN s /\ prime p /\ p divides (PROD_SET (e INSERT s)) ==>
              ?b. ((b = e) \/ b IN s) /\ p divides b
     Note PROD_SET (e INSERT s) = e * PROD_SET s   by PROD_SET_THM, DELETE_NON_ELEMENT, e NOTIN s.
     So prime p /\ p divides (PROD_SET (e INSERT s))
     ==> p divides e, or p divides (PROD_SET s)    by P_EUCLIDES
     If p divides e, just take b = e.
     If p divides (PROD_SET s), there is such b    by induction hypothesis
*)
val PROD_SET_EUCLID = store_thm(
  "PROD_SET_EUCLID",
  ``!s. FINITE s ==> !p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b``,
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >-
  metis_tac[PROD_SET_EMPTY, DIVIDES_ONE, NOT_PRIME_1] >>
  `PROD_SET (e INSERT s) = e * PROD_SET s`
    by metis_tac[PROD_SET_THM, DELETE_NON_ELEMENT] >>
  Cases_on `p divides e` >-
  metis_tac[] >>
  metis_tac[P_EUCLIDES]);



(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
