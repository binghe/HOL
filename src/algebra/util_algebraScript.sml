(* ------------------------------------------------------------------------- *)
(* Helper Theorems - a collection of useful results                          *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "util_algebra";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory rich_listTheory listRangeTheory;
open arithmeticTheory dividesTheory gcdTheory;

(* ------------------------------------------------------------------------- *)
(* HelperNum Documentation                                                   *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   SQ n           = n * n
   HALF n         = n DIV 2
   TWICE n        = 2 * n
   n divides m    = divides n m
*)
(* Definitions and Theorems (# are exported):

   Arithmetic Theorems:
   THREE             |- 3 = SUC 2
   FOUR              |- 4 = SUC 3
   FIVE              |- 5 = SUC 4
   ZERO_LE_ALL       |- !n. 0 <= n
   NOT_ZERO          |- !n. n <> 0 <=> 0 < n
   ONE_LT_POS        |- !n. 1 < n ==> 0 < n
   ONE_LT_NONZERO    |- !n. 1 < n ==> n <> 0
   NOT_LT_ONE        |- !n. ~(1 < n) <=> (n = 0) \/ (n = 1)
   NOT_ZERO_GE_ONE   |- !n. n <> 0 <=> 1 <= n
   ONE_LE_NONZERO    |- !n. 1 <= n <=> n <> 0
   LE_ONE            |- !n. n <= 1 <=> (n = 0) \/ (n = 1)
   LT_ONE            |- !n. n < 1 <=> (n = 0)
   LT_TWO            |- !n. n < 2 <=> (n = 0) \/ (n = 1)
   LESS_TWICE        |- !m n. m < TWICE n ==> m - n < n
   LESS_NOT_EQ       |- !m n. m < n ==> m <> n
   LESS_SELF         |- !n. ~(n < n)
   LESS_SUC          |- !n. n < SUC n
   PRE_LESS          |- !n. 0 < n ==> PRE n < n
   LESS_EQ_SUC       |- !n. 0 < n ==> ?m. n = SUC m
   SUC_POS           |- !n. 0 < SUC n
   SUC_NOT_ZERO      |- !n. SUC n <> 0
   ONE_NOT_ZERO      |- 1 <> 0
   SUC_ADD_SUC       |- !m n. SUC m + SUC n = m + n + 2
   SUC_MULT_SUC      |- !m n. SUC m * SUC n = m * n + m + n + 1
   SUC_EQ            |- !m n. (SUC m = SUC n) <=> (m = n)
   TWICE_EQ_0        |- !n. (TWICE n = 0) <=> (n = 0)
   SQ_EQ_0           |- !n. (SQ n = 0) <=> (n = 0)
   SQ_EQ_1           |- !n. (SQ n = 1) <=> (n = 1)
   MULT3_EQ_0        |- !x y z. (x * y * z = 0) <=> ((x = 0) \/ (y = 0) \/ (z = 0))
   MULT3_EQ_1        |- !x y z. (x * y * z = 1) <=> ((x = 1) /\ (y = 1) /\ (z = 1))
   SQ_0              |- 0 ** 2 = 0
   EXP_2_EQ_0        |- !n. (n ** 2 = 0) <=> (n = 0)

   Maximum and minimum:
   MAX_ALT           |- !m n. MAX m n = if m <= n then n else m
   MIN_ALT           |- !m n. MIN m n = if m <= n then m else n
   MAX_SWAP          |- !f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MAX x y) = MAX (f x) (f y)
   MIN_SWAP          |- !f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MIN x y) = MIN (f x) (f y)
   SUC_MAX           |- !m n. SUC (MAX m n) = MAX (SUC m) (SUC n)
   SUC_MIN           |- !m n. SUC (MIN m n) = MIN (SUC m) (SUC n)
   MAX_SUC           |- !m n. MAX (SUC m) (SUC n) = SUC (MAX m n)
   MIN_SUC           |- !m n. MIN (SUC m) (SUC n) = SUC (MIN m n)
   MAX_LESS          |- !x y n. x < n /\ y < n ==> MAX x y < n
   MAX_CASES         |- !m n. (MAX n m = n) \/ (MAX n m = m)
   MIN_CASES         |- !m n. (MIN n m = n) \/ (MIN n m = m)
   MAX_EQ_0          |- !m n. (MAX n m = 0) <=> (n = 0) /\ (m = 0)
   MIN_EQ_0          |- !m n. (MIN n m = 0) <=> (n = 0) \/ (m = 0)
   MAX_IS_MAX        |- !m n. m <= MAX m n /\ n <= MAX m n
   MIN_IS_MIN        |- !m n. MIN m n <= m /\ MIN m n <= n
   MAX_ID            |- !m n. MAX (MAX m n) n = MAX m n /\ MAX m (MAX m n) = MAX m n
   MIN_ID            |- !m n. MIN (MIN m n) n = MIN m n /\ MIN m (MIN m n) = MIN m n
   MAX_LE_PAIR       |- !a b c d. a <= b /\ c <= d ==> MAX a c <= MAX b d
   MIN_LE_PAIR       |- !a b c d. a <= b /\ c <= d ==> MIN a c <= MIN b d
   MAX_ADD           |- !a b c. MAX a (b + c) <= MAX a b + MAX a c
   MIN_ADD           |- !a b c. MIN a (b + c) <= MIN a b + MIN a c
   MAX_1_POS         |- !n. 0 < n ==> MAX 1 n = n
   MIN_1_POS         |- !n. 0 < n ==> MIN 1 n = 1
   MAX_LE_SUM        |- !m n. MAX m n <= m + n
   MIN_LE_SUM        |- !m n. MIN m n <= m + n
   MAX_1_EXP         |- !n m. MAX 1 (m ** n) = MAX 1 m ** n
   MIN_1_EXP         |- !n m. MIN 1 (m ** n) = MIN 1 m ** n

   Arithmetic Manipulations:
   MULT_POS          |- !m n. 0 < m /\ 0 < n ==> 0 < m * n
   MULT_COMM_ASSOC   |- !m n p. m * (n * p) = n * (m * p)
   EQ_MULT_RCANCEL   |- !m n p. (n * m = p * m) <=> (m = 0) \/ (n = p)
   MULT_RIGHT_CANCEL |- !m n p. (n * p = m * p) <=> (p = 0) \/ (n = m)
   MULT_LEFT_CANCEL  |- !m n p. (p * n = p * m) <=> (p = 0) \/ (n = m)
   MULT_TO_DIV       |- !m n. 0 < n ==> (n * m DIV n = m)
   MULT_ASSOC_COMM   |- !m n p. m * (n * p) = m * p * n
   MULT_LEFT_ID      |- !n. 0 < n ==> !m. (m * n = n) <=> (m = 1)
   MULT_RIGHT_ID     |- !n. 0 < n ==> !m. (n * m = n) <=> (m = 1)
   MULT_EQ_SELF      |- !n. 0 < n ==> !m. (n * m = n) <=> (m = 1)
   SQ_EQ_SELF        |- !n. (n * n = n) <=> (n = 0) \/ (n = 1)
   EXP_EXP_BASE_LE   |- !b c m n. m <= n /\ 0 < c ==> b ** c ** m <= b ** c ** n
   EXP_EXP_LE_MONO_IMP|- !a b n. a <= b ==> a ** n <= b ** n
   EXP_BY_ADD_SUB_LE |- !m n. m <= n ==> !p. p ** n = p ** m * p ** (n - m)
   EXP_BY_ADD_SUB_LT |- !m n. m < n ==> !p. p ** n = p ** m * p ** (n - m)
   EXP_SUC_DIV       |- !m n. 0 < m ==> m ** SUC n DIV m = m ** n
   SELF_LE_SQ        |- !n. n <= n ** 2
   LE_MONO_ADD2      |- !a b c d. a <= b /\ c <= d ==> a + c <= b + d
   LT_MONO_ADD2      |- !a b c d. a < b /\ c < d ==> a + c < b + d
   LE_MONO_MULT2     |- !a b c d. a <= b /\ c <= d ==> a * c <= b * d
   LT_MONO_MULT2     |- !a b c d. a < b /\ c < d ==> a * c < b * d
   SUM_LE_PRODUCT    |- !m n. 1 < m /\ 1 < n ==> m + n <= m * n
   MULTIPLE_SUC_LE   |- !n k. 0 < n ==> k * n + 1 <= (k + 1) * n

   Simple Theorems:
   ADD_EQ_2          |- !m n. 0 < m /\ 0 < n /\ (m + n = 2) ==> (m = 1) /\ (n = 1)
   EVEN_0            |- EVEN 0
   ODD_1             |- ODD 1
   EVEN_2            |- EVEN 2
   EVEN_SQ           |- !n. EVEN (n ** 2) <=> EVEN n
   ODD_SQ            |- !n. ODD (n ** 2) <=> ODD n
   EQ_PARITY         |- !a b. EVEN (2 * a + b) <=> EVEN b
   ODD_MOD2          |- !x. ODD x <=> (x MOD 2 = 1)
   EVEN_ODD_SUC      |- !n. (EVEN n <=> ODD (SUC n)) /\ (ODD n <=> EVEN (SUC n))
   EVEN_ODD_PRE      |- !n. 0 < n ==> (EVEN n <=> ODD (PRE n)) /\ (ODD n <=> EVEN (PRE n))
   EVEN_PARTNERS     |- !n. EVEN (n * (n + 1))
   EVEN_HALF         |- !n. EVEN n ==> (n = 2 * HALF n)
   ODD_HALF          |- !n. ODD n ==> (n = 2 * HALF n + 1)
   EVEN_SUC_HALF     |- !n. EVEN n ==> (HALF (SUC n) = HALF n)
   ODD_SUC_HALF      |- !n. ODD n ==> (HALF (SUC n) = SUC (HALF n))
   HALF_EQ_0         |- !n. (HALF n = 0) <=> (n = 0) \/ (n = 1)
   HALF_EQ_SELF      |- !n. (HALF n = n) <=> (n = 0)
   HALF_LESS         |- !n. 0 < n ==> HALF n < n
   HALF_TWICE        |- !n. HALF (TWICE n) = n
   HALF_MULT         |- !m n. n * HALF m <= HALF (n * m)
   TWO_HALF_LESS_EQ  |- !n. 2 * HALF n <= n /\ n <= SUC (2 * HALF n)
   TWO_HALF_TIMES_LE |- !m n. TWICE (HALF n * m) <= n * m
   SUC_HALF_LE       |- !n. 0 < n ==> 1 + HALF n <= n
   HALF_SQ_LE        |- !n. HALF n ** 2 <= n ** 2 DIV 4
   HALF_LE                |- !n. HALF n <= n
   HALF_LE_MONO           |- !x y. x <= y ==> HALF x <= HALF y
   MULT_EVEN         |- !n. EVEN n ==> !m. m * n = TWICE m * HALF n
   MULT_ODD          |- !n. ODD n ==> !m. m * n = m + TWICE m * HALF n
   EVEN_MOD_EVEN     |- !m. EVEN m /\ m <> 0 ==> !n. EVEN n <=> EVEN (n MOD m)
   EVEN_MOD_ODD      |- !m. EVEN m /\ m <> 0 ==> !n. ODD n <=> ODD (n MOD m)

   SUB_SUB_SUB           |- !a b c. c <= a ==> (a - b - (a - c) = c - b)
   ADD_SUB_SUB           |- !a b c. c <= a ==> (a + b - (a - c) = c + b)
   SUB_EQ_ADD            |- !p. 0 < p ==> !m n. (m - n = p) <=> (m = n + p)
   MULT_EQ_LESS_TO_MORE  |- !a b c d. 0 < a /\ 0 < b /\ a < c /\ (a * b = c * d) ==> d < b
   LE_IMP_REVERSE_LT     |- !a b c d. 0 < c /\ 0 < d /\ a * b <= c * d /\ d < b ==> a < c

   Exponential Theorems:
   EXP_0             |- !n. n ** 0 = 1
   EXP_2             |- !n. n ** 2 = n * n
   EXP_NONZERO       |- !m n. m <> 0 ==> m ** n <> 0
   EXP_POS           |- !m n. 0 < m ==> 0 < m ** n
   EXP_EQ_SELF       |- !n m. 0 < m ==> (n ** m = n) <=> (m = 1) \/ (n = 0) \/ (n = 1)
   EXP_LE            |- !n b. 0 < n ==> b <= b ** n
   EXP_LT            |- !n b. 1 < b /\ 1 < n ==> b < b ** n
   EXP_LCANCEL       |- !a b c n m. 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c)
   EXP_RCANCEL       |- !a b c n m. 0 < a /\ n < m /\ (b * a ** n = c * a ** m) ==> ?d. 0 < d /\ (b = c * a ** d)
   ONE_LE_EXP        |- !m n. 0 < m ==> 1 <= m ** n
   EXP_EVEN          |- !n. EVEN n ==> !m. m ** n = SQ m ** HALF n
   EXP_ODD           |- !n. ODD n ==> !m. m ** n = m * SQ m ** HALF n
   EXP_THM           |- !m n. m ** n =
                              if n = 0 then 1 else if n = 1 then m
                              else if EVEN n then SQ m ** HALF n
                                   else m * SQ m ** HALF n
   EXP_EQN           |- !m n. m ** n =
                              if n = 0 then 1
                              else if EVEN n then SQ m ** HALF n
                              else m * SQ m ** HALF n
   EXP_EQN_ALT       |- !m n. m ** n =
                              if n = 0 then 1 else (if EVEN n then 1 else m) * SQ m ** HALF n
   EXP_ALT_EQN       |- !m n. m ** n =
                              if n = 0 then 1 else (if EVEN n then 1 else m) * (m ** 2) ** HALF n
   EXP_MOD_EQN       |- !b n m. 1 < m ==>
                                (b ** n MOD m =
                                 if n = 0 then 1
                                 else (let result = SQ b ** HALF n MOD m
                                        in if EVEN n then result else (b * result) MOD m))
   EXP_MOD_ALT       |- !b n m. 1 < m ==>
                                (b ** n MOD m =
                                 if n = 0 then 1
                                 else ((if EVEN n then 1 else b) * SQ b ** HALF n MOD m) MOD m)
   EXP_EXP_SUC       |- !x y n. x ** y ** SUC n = (x ** y) ** y ** n
   EXP_LOWER_LE_LOW  |- !n m. 1 + n * m <= (1 + m) ** n
   EXP_LOWER_LT_LOW  |- !n m. 0 < m /\ 1 < n ==> 1 + n * m < (1 + m) ** n
   EXP_LOWER_LE_HIGH |- !n m. n * m ** (n - 1) + m ** n <= (1 + m) ** n
   SUC_X_LT_2_EXP_X  |- !n. 1 < n ==> SUC n < 2 ** n

   DIVIDES Theorems:
   DIV_EQ_0          |- !m n. 0 < n ==> ((m DIV n = 0) <=> m < n)
   DIV_POS           |- !m n. 0 < n /\ m divides n ==> 0 < n DIV m
   DIV_LE            |- !x y z. 0 < y /\ x <= y * z ==> x DIV y <= z
   DIV_SOLVE         |- !n. 0 < n ==> !x y. (x * n = y) ==> (x = y DIV n)
   DIV_SOLVE_COMM    |- !n. 0 < n ==> !x y. (n * x = y) ==> (x = y DIV n)
   ONE_DIV           |- !n. 1 < n ==> (1 DIV n = 0)
   DIVIDES_ODD       |- !n. ODD n ==> !m. m divides n ==> ODD m
   DIVIDES_EVEN      |- !m. EVEN m ==> !n. m divides n ==> EVEN n
   DIVIDES_MOD_0     |- !n. 0 < n ==> !m. n divides m <=> (m MOD n = 0)
   EVEN_ALT          |- !n. EVEN n <=> 2 divides n
   ODD_ALT           |- !n. ODD n <=> ~(2 divides n)

   DIV_MULT_LE       |- !n. 0 < n ==> !q. q DIV n * n <= q
   DIV_MULT_EQ       |- !n. 0 < n ==> !q. n divides q <=> (q DIV n * n = q)
   DIV_MULT_LESS_EQ  |- !m n. 0 < m ==> m * (n DIV m) <= n /\ n < m * SUC (n DIV m)
   DIV_LE_MONOTONE_REVERSE  |- !x y. 0 < x /\ 0 < y /\ x <= y ==> !n. n DIV y <= n DIV x
   DIVIDES_EQN       |- !n. 0 < n ==> !m. n divides m <=> (m = m DIV n * n)
   DIVIDES_EQN_COMM  |- !n. 0 < n ==> !m. n divides m <=> (m = n * (m DIV n))
   SUB_DIV           |- !m n. 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1)
   SUB_DIV_EQN       |- !m n. 0 < n ==> ((m - n) DIV n = if m < n then 0 else m DIV n - 1)
   SUB_MOD_EQN       |- !m n. 0 < n ==> ((m - n) MOD n = if m < n then 0 else m MOD n)
   DIV_EQ_MULT       |- !n. 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n))
   MULT_LT_DIV       |- !n. 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n)
   LE_MULT_LE_DIV    |- !n. 0 < n ==> !k m. (m MOD n = 0) ==> (m <= n * k <=> m DIV n <= k)
   DIV_MOD_EQ_0      |- !m n. 0 < m ==> (n DIV m = 0 /\ n MOD m = 0 <=> n = 0)
   DIV_LT_SUC        |- !m n. 0 < m /\ 0 < n /\ n MOD m = 0 ==> n DIV SUC m < n DIV m
   DIV_LT_MONOTONE_REVERSE  |- !x y. 0 < x /\ 0 < y /\ x < y ==>
                               !n. 0 < n /\ n MOD x = 0 ==> n DIV y < n DIV x

   EXP_DIVIDES            |- !a b n. 0 < n /\ a ** n divides b ==> a divides b
   DIVIDES_EXP_BASE       |- !a b n. prime a /\ 0 < n ==> (a divides b <=> a divides (b ** n))
   DIVIDES_MULTIPLE       |- !m n. n divides m ==> !k. n divides (k * m)
   DIVIDES_MULTIPLE_IFF   |- !m n k. k <> 0 ==> (m divides n <=> k * m divides k * n)
   DIVIDES_FACTORS        |- !m n. 0 < n /\ n divides m ==> (m = n * (m DIV n))
   DIVIDES_COFACTOR       |- !m n. 0 < n /\ n divides m ==> (m DIV n) divides m
   MULTIPLY_DIV           |- !n p q. 0 < n /\ n divides q ==> (p * (q DIV n) = p * q DIV n)
   DIVIDES_MOD_MOD        |- !m n. 0 < n /\ m divides n ==> !x. x MOD n MOD m = x MOD m
   DIVIDES_CANCEL         |- !k. 0 < k ==> !m n. m divides n <=> (m * k) divides (n * k)
   DIVIDES_CANCEL_COMM    |- !a b k. a divides b ==> (k * a) divides (k * b)
   DIV_COMMON_FACTOR      |- !m n. 0 < n /\ 0 < m ==> !x. n divides x ==> (m * x DIV (m * n) = x DIV n)
   DIV_DIV_MULT           |- !m n x. 0 < n /\ 0 < m /\ 0 < m DIV n /\ n divides m /\ m divides x /\
                                     (m DIV n) divides x ==> (x DIV (m DIV n) = n * (x DIV m))

   Basic Divisibility:
   dividend_divides_divisor_multiple  |- !m n. 0 < m /\ n divides m ==>
                                         !t. m divides t * n <=> m DIV n divides t
   divisor_pos         |- !m n. 0 < n /\ m divides n ==> 0 < m
   divides_pos         |- !m n. 0 < n /\ m divides n ==> 0 < m /\ m <= n
   divide_by_cofactor  |- !m n. 0 < n /\ m divides n ==> (n DIV (n DIV m) = m)
   divides_exp         |- !n. 0 < n ==> !a b. a divides b ==> a divides b ** n
   divides_linear      |- !a b c. c divides a /\ c divides b ==> !h k. c divides h * a + k * b
   divides_linear_sub  |- !a b c. c divides a /\ c divides b ==>
                          !h k d. (h * a = k * b + d) ==> c divides d
   power_divides_iff        |- !p. 1 < p ==> !m n. p ** m divides p ** n <=> m <= n
   prime_power_divides_iff  |- !p. prime p ==> !m n. p ** m divides p ** n <=> m <= n
   divides_self_power       |- !n p. 0 < n /\ 1 < p ==> p divides p ** n
   divides_eq_thm      |- !a b. a divides b /\ 0 < b /\ b < 2 * a ==> (b = a)
   factor_eq_cofactor  |- !m n. 0 < m /\ m divides n ==> (m = n DIV m <=> n = m ** 2)
   euclid_prime        |- !p a b. prime p /\ p divides a * b ==> p divides a \/ p divides b
   euclid_coprime      |- !a b c. (gcd a b = 1) /\ b divides a * c ==> b divides c

   Modulo Theorems:
   MOD_EQN             |- !n. 0 < n ==> !a b. (a MOD n = b) <=> ?c. (a = c * n + b) /\ b < n
   MOD_PLUS3           |- !n. 0 < n ==> !x y z. (x + y + z) MOD n = (x MOD n + y MOD n + z MOD n) MOD n
   MOD_ADD_ASSOC       |- !n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==>
                          (((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n)
   MOD_MULT_ASSOC      |- !n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==>
                          (((x * y) MOD n * z) MOD n = (x * (y * z) MOD n) MOD n)
   MOD_ADD_INV         |- !n x. 0 < n /\ x < n ==> (((n - x) MOD n + x) MOD n = 0)
   MOD_MULITPLE_ZERO   |- !n k. 0 < n /\ (k MOD n = 0) ==> !x. (k * x) MOD n = 0
   MOD_EQ_DIFF         |- !n a b. 0 < n /\ (a MOD n = b MOD n) ==> ((a - b) MOD n = 0)
   MOD_EQ              |- !n a b. 0 < n /\ b <= a ==> (((a - b) MOD n = 0) <=> (a MOD n = b MOD n))
   MOD_EQ_0_IFF        |- !m n. n < m ==> ((n MOD m = 0) <=> (n = 0))
   MOD_EXP             |- !n. 0 < n ==> !a m. (a MOD n) ** m MOD n = a ** m MOD n
   ODD_EXP             |- !m n. 0 < n /\ ODD m ==> ODD (m ** n)
   power_parity        |- !n. 0 < n ==> !m. (EVEN m <=> EVEN (m ** n)) /\ (ODD m <=> ODD (m ** n))
   EXP_2_EVEN          |- !n. 0 < n ==> EVEN (2 ** n)
   EXP_2_PRE_ODD       |- !n. 0 < n ==> ODD (2 ** n - 1)

   Modulo Inverse:
   GCD_LINEAR          |- !j k. 0 < j ==> ?p q. p * j = q * k + gcd j k
   EUCLID_LEMMA        |- !p x y. prime p ==> (((x * y) MOD p = 0) <=> (x MOD p = 0) \/ (y MOD p = 0))
   MOD_MULT_LCANCEL    |- !p x y z. prime p /\ (x * y) MOD p = (x * z) MOD p /\ x MOD p <> 0 ==>
                                    y MOD p = z MOD p
   MOD_MULT_RCANCEL    |- !p x y z. prime p /\ (y * x) MOD p = (z * x) MOD p /\ x MOD p <> 0 ==>
                                    y MOD p = z MOD p
   MOD_MULT_INV_EXISTS |- !p x. prime p /\ 0 < x /\ x < p ==> ?y. 0 < y /\ y < p /\ ((y * x) MOD p = 1)
   MOD_MULT_INV_DEF    |- !p x. prime p /\ 0 < x /\ x < p ==>
                           0 < MOD_MULT_INV p x /\ MOD_MULT_INV p x < p /\ ((MOD_MULT_INV p x * x) MOD p = 1)

   FACTOR Theorems:
   PRIME_FACTOR_PROPER    |- !n. 1 < n /\ ~prime n ==> ?p. prime p /\ p < n /\ (p divides n)
   FACTOR_OUT_POWER       |- !n p. 0 < n /\ 1 < p /\ p divides n ==>
                             ?m. (p ** m) divides n /\ ~(p divides (n DIV p ** m))

   Useful Theorems:
   binomial_add         |- !a b. (a + b) ** 2 = a ** 2 + b ** 2 + 2 * a * b
   binomial_sub         |- !a b. b <= a ==> ((a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b)
   binomial_means       |- !a b. 2 * a * b <= a ** 2 + b ** 2
   binomial_sub_add     |- !a b. b <= a ==> ((a - b) ** 2 + 4 * a * b = (a + b) ** 2)
   difference_of_squares|- !a b. a ** 2 - b ** 2 = (a - b) * (a + b)
   difference_of_squares_alt
                        |- !a b. a * a - b * b = (a - b) * (a + b)
   binomial_2           |- !m n. (m + n) ** 2 = m ** 2 + n ** 2 + TWICE m * n
   SUC_SQ               |- !n. SUC n ** 2 = SUC (n ** 2) + TWICE n
   SQ_LE                |- !m n. m <= n ==> SQ m <= SQ n
   EVEN_PRIME           |- !n. EVEN n /\ prime n ==> (n = 2)
   ODD_PRIME            |- !n. prime n /\ n <> 2 ==> ODD n
   TWO_LE_PRIME         |- !p. prime p ==> 2 <= p
   NOT_PRIME_4          |- ~prime 4
   prime_divides_prime  |- !n m. prime n /\ prime m ==> (n divides m <=> (n = m))
   ALL_PRIME_FACTORS_MOD_EQ_1  |- !m n. 0 < m /\ 1 < n /\
                                   (!p. prime p /\ p divides m ==> (p MOD n = 1)) ==> (m MOD n = 1)
   prime_divides_power         |- !p n. prime p /\ 0 < n ==> !b. p divides b ** n <=> p divides b
   prime_divides_self_power    |- !p. prime p ==> !n. 0 < n ==> p divides p ** n
   power_eq_prime_power        |- !p. prime p ==> !b n m. 0 < m /\ (b ** n = p ** m) ==>
                                  ?k. (b = p ** k) /\ (k * n = m)
   POWER_EQ_SELF        |- !n. 1 < n ==> !m. (n ** m = n) <=> (m = 1)

   LESS_HALF_IFF        |- !n k. k < HALF n <=> k + 1 < n - k
   MORE_HALF_IMP        |- !n k. HALF n < k ==> n - k <= HALF n
   MONOTONE_MAX         |- !f m. (!k. k < m ==> f k < f (k + 1)) ==> !k. k < m ==> f k < f m
   MULTIPLE_INTERVAL    |- !n m. n divides m ==> !x. m - n < x /\ x < m + n /\ n divides x ==> (x = m)
   MOD_SUC_EQN          |- !m n. 0 < m ==> (SUC (n MOD m) = SUC n MOD m + (SUC n DIV m - n DIV m) * m)
   ONE_LT_HALF_SQ       |- !n. 1 < n ==> 1 < HALF (n ** 2)
   EXP_2_HALF           |- !n. 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1))
   HALF_MULT_EVEN       |- !m n. EVEN n ==> (HALF (m * n) = m * HALF n)
   MULT_LESS_IMP_LESS   |- !m n k. 0 < k /\ k * m < n ==> m < n
   HALF_EXP_5           |- !n. n * HALF (SQ n ** 2) <= HALF (n ** 5)
   LE_TWICE_ALT         |- !m n. n <= TWICE m <=> n <> 0 ==> HALF (n - 1) < m
   HALF_DIV_TWO_POWER   |- !m n. HALF n DIV 2 ** m = n DIV 2 ** SUC m
   fit_for_100          |- 1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100
*)

(* ------------------------------------------------------------------------- *)
(* Arithmetic Theorems                                                       *)
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
val ZERO_LE_ALL = save_thm("ZERO_LE_ALL", ZERO_LESS_EQ);
(* val ZERO_LE_ALL = |- !n. 0 <= n: thm *)

(* Theorem alias *)
val NOT_ZERO = save_thm("NOT_ZERO", NOT_ZERO_LT_ZERO);

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

(* Theorem: 1 <= n <=> n <> 0 *)
(* Proof: by arithmetic *)
val ONE_LE_NONZERO = store_thm(
  "ONE_LE_NONZERO",
  ``!n. 1 <= n <=> n <> 0``,
  decide_tac);
(* This is the reverse of: NOT_ZERO_GE_ONE *)

(* Theorem: n <= 1 <=> (n = 0) \/ (n = 1) *)
(* Proof: by arithmetic *)
val LE_ONE = store_thm(
  "LE_ONE",
  ``!n. n <= 1 <=> (n = 0) \/ (n = 1)``,
  decide_tac);

(* Theorem: n < 1 <=> (n = 0) *)
(* Proof: by arithmetic *)
val LT_ONE = store_thm(
  "LT_ONE",
  ``!n. n < 1 <=> (n = 0)``,
  decide_tac);

(* Theorem: n < 2 <=> (n = 0) \/ (n = 1) *)
(* Proof: by arithmetic *)
val LT_TWO = store_thm(
  "LT_TWO",
  ``!n. n < 2 <=> (n = 0) \/ (n = 1)``,
  decide_tac);

(* Theorem: m < 2 * n ==> m - n < n *)
(* Proof: by arithmetic *)
val LESS_TWICE = store_thm(
  "LESS_TWICE",
  ``!m n. m < 2 * n ==> m - n < n``,
  decide_tac);

(* Theorem: m < n ==> m <> n *)
(* Proof: by arithmetic. *)
val LESS_NOT_EQ = store_thm(
  "LESS_NOT_EQ",
  ``!m n. m < n ==> m <> n``,
  decide_tac);

(* Theorem alias *)
val LESS_SELF = save_thm("LESS_SELF", prim_recTheory.LESS_REFL);
(* val LESS_SELF = |- !n. ~(n < n): thm *)

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
(* Proof: by NOT_ZERO_LT_ZERO. *)
val LESS_EQ_SUC = store_thm(
  "LESS_EQ_SUC",
  ``!n. 0 < n ==> ?m. n = SUC m``,
  metis_tac[NOT_ZERO_LT_ZERO, num_CASES]);

(* prim_recTheory.LESS_0 |- !n. 0 < SUC n  *)
(* Theorem: 0 < SUC n *)
(* Proof: by arithmetic. *)
val SUC_POS = store_thm(
  "SUC_POS",
  ``!n. 0 < SUC n``,
  decide_tac);

(* numTheory.NOT_SUC  |- !n. SUC n <> 0 *)
(* Theorem: 0 < SUC n *)
(* Proof: by arithmetic. *)
val SUC_NOT_ZERO = store_thm(
  "SUC_NOT_ZERO",
  ``!n. SUC n <> 0``,
  decide_tac);

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

(* Rename theorem *)
val MULT_POS = save_thm("MULT_POS", LESS_MULT2);
(* val MULT_POS = |- !m n. 0 < m /\ 0 < n ==> 0 < m * n: thm *)

(* Theorem: m * (n * p) = n * (m * p) *)
(* Proof:
     m * (n * p)
   = (m * n) * p       by MULT_ASSOC
   = (n * m) * p       by MULT_COMM
   = n * (m * p)       by MULT_ASSOC
*)
val MULT_COMM_ASSOC = store_thm(
  "MULT_COMM_ASSOC",
  ``!m n p. m * (n * p) = n * (m * p)``,
  metis_tac[MULT_COMM, MULT_ASSOC]);

(* The missing theorem in arithmeticTheory. Only has EQ_MULT_LCANCEL:
   |- !m n p. (m * n = m * p) <=> (m = 0) \/ (n = p): thm
*)
(* Theorem: (n * m = p * m) <=> (m = 0) \/ (n = p) *)
(* Proof: by EQ_MULT_LCANCEL, MULT_COMM *)
val EQ_MULT_RCANCEL = store_thm(
  "EQ_MULT_RCANCEL",
  ``!m n p. (n * m = p * m) <=> (m = 0) \/ (n = p)``,
  rw[EQ_MULT_LCANCEL, MULT_COMM]);

(* Theorem: n * p = m * p <=> p = 0 \/ n = m *)
(* Proof:
       n * p = m * p
   <=> n * p - m * p = 0      by SUB_EQUAL_0
   <=>   (n - m) * p = 0      by RIGHT_SUB_DISTRIB
   <=>   n - m = 0  or p = 0  by MULT_EQ_0
   <=>    n = m  or p = 0     by SUB_EQUAL_0
*)
val MULT_RIGHT_CANCEL = store_thm(
  "MULT_RIGHT_CANCEL",
  ``!m n p. (n * p = m * p) <=> (p = 0) \/ (n = m)``,
  rw[]);

(* Theorem: p * n = p * m <=> p = 0 \/ n = m *)
(* Proof: by MULT_RIGHT_CANCEL and MULT_COMM. *)
val MULT_LEFT_CANCEL = store_thm(
  "MULT_LEFT_CANCEL",
  ``!m n p. (p * n = p * m) <=> (p = 0) \/ (n = m)``,
  rw[MULT_RIGHT_CANCEL, MULT_COMM]);

(* Theorem: 0 < n ==> ((n * m) DIV n = m) *)
(* Proof:
   Since n * m = m * n        by MULT_COMM
               = m * n + 0    by ADD_0
     and 0 < n                by given
   Hence (n * m) DIV n = m    by DIV_UNIQUE:
   |- !n k q. (?r. (k = q * n + r) /\ r < n) ==> (k DIV n = q)
*)
val MULT_TO_DIV = store_thm(
  "MULT_TO_DIV",
  ``!m n. 0 < n ==> ((n * m) DIV n = m)``,
  metis_tac[MULT_COMM, ADD_0, DIV_UNIQUE]);
(* This is commutative version of:
arithmeticTheory.MULT_DIV |- !n q. 0 < n ==> (q * n DIV n = q)
*)

(* Theorem: m * (n * p) = m * p * n *)
(* Proof: by MULT_ASSOC, MULT_COMM *)
val MULT_ASSOC_COMM = store_thm(
  "MULT_ASSOC_COMM",
  ``!m n p. m * (n * p) = m * p * n``,
  metis_tac[MULT_ASSOC, MULT_COMM]);

(* Theorem: 0 < n ==> !m. (m * n = n) <=> (m = 1) *)
(* Proof: by MULT_EQ_ID *)
val MULT_LEFT_ID = store_thm(
  "MULT_LEFT_ID",
  ``!n. 0 < n ==> !m. (m * n = n) <=> (m = 1)``,
  metis_tac[MULT_EQ_ID, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n ==> !m. (n * m = n) <=> (m = 1) *)
(* Proof: by MULT_EQ_ID *)
val MULT_RIGHT_ID = store_thm(
  "MULT_RIGHT_ID",
  ``!n. 0 < n ==> !m. (n * m = n) <=> (m = 1)``,
  metis_tac[MULT_EQ_ID, MULT_COMM, NOT_ZERO_LT_ZERO]);

(* Theorem alias *)
val MULT_EQ_SELF = save_thm("MULT_EQ_SELF", MULT_RIGHT_ID);
(* val MULT_EQ_SELF = |- !n. 0 < n ==> !m. (n * m = n) <=> (m = 1): thm *)

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
val HALF_LESS = store_thm(
  "HALF_LESS",
  ``!n. 0 < n ==> HALF n < n``,
  rpt strip_tac >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n <> n` by rw[HALF_EQ_SELF] >>
  decide_tac);

(* Theorem: HALF (2 * n) = n *)
(* Proof:
   Let m = 2 * n.
   Then EVEN m                 by EVEN_DOUBLE
     so 2 * HALF m = m = 2 * n by EVEN_HALF
     or     HALF m = n         by MULT_LEFT_CANCEL
*)
val HALF_TWICE = store_thm(
  "HALF_TWICE",
  ``!n. HALF (2 * n) = n``,
  metis_tac[EVEN_DOUBLE, EVEN_HALF, MULT_LEFT_CANCEL, DECIDE``2 <> 0``]);

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
val HALF_MULT = store_thm(
  "HALF_MULT",
  ``!m n. n * HALF m <= HALF (n * m)``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF m` >>
  Cases_on `EVEN m` >| [
    `m = 2 * k` by rw[EVEN_HALF, Abbr`k`] >>
    `HALF (n * m) = HALF (2 * (n * k))` by rw[] >>
    `_ = n * k` by rw[GSYM HALF_TWICE] >>
    decide_tac,
    `ODD m` by rw[ODD_EVEN] >>
    `m = 2 * k + 1` by rw[ODD_HALF, Abbr`k`] >>
    `HALF (n * m) = HALF (2 * (n * k) + n)` by rw[LEFT_ADD_DISTRIB] >>
    `_ = (n * k) + HALF n` by rw[HALF_TWICE, GSYM ADD_DIV_ADD_DIV] >>
    decide_tac
  ]);

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
val TWO_HALF_LESS_EQ = store_thm(
  "TWO_HALF_LESS_EQ",
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
   <= m * n                 by TWO_HALF_LESS_EQ
    = n * m                 by MULT_COMM
*)
val TWO_HALF_TIMES_LE = store_thm(
  "TWO_HALF_TIMES_LE",
  ``!m n. 2 * ((HALF n) * m) <= n * m``,
  rpt strip_tac >>
  `2 * (m * HALF n) <= 2 * (HALF (m * n))` by rw[HALF_MULT] >>
  `2 * (HALF (m * n)) <= m * n` by rw[TWO_HALF_LESS_EQ] >>
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
        <= n                 by TWO_HALF_LESS_EQ
*)
val SUC_HALF_LE = store_thm(
  "SUC_HALF_LE",
  ``!n. 0 < n ==> 1 + HALF n <= n``,
  rpt strip_tac >>
  (Cases_on `n = 1` >> simp[]) >>
  `HALF n <> 0` by metis_tac[HALF_EQ_0, NOT_ZERO] >>
  `1 + HALF n <= 2 * HALF n` by decide_tac >>
  `2 * HALF n <= n` by rw[TWO_HALF_LESS_EQ] >>
  decide_tac);

(* Theorem: (HALF n) ** 2 <= (n ** 2) DIV 4 *)
(* Proof:
   Let k = HALF n.
   Then 2 * k <= n                by TWO_HALF_LESS_EQ
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
  `2 * k <= n` by rw[TWO_HALF_LESS_EQ, Abbr`k`] >>
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
val EXP_THM = save_thm("EXP_THM", CONJ EXP_EVEN EXP_ODD);
(*
val EXP_THM = |- (!n. EVEN n ==> !m. m ** n = SQ m ** HALF n) /\
                  !n. ODD n ==> !m. m ** n = m * SQ m ** HALF n: thm
*)
(* Next is better *)

(* Theorem: m ** n = if n = 0 then 1 else if n = 1 then m else
            if EVEN n then (m * m) ** HALF n else m * ((m * m) ** (HALF n)) *)
(* Proof: mainly by EXP_EVEN, EXP_ODD. *)
val EXP_THM = store_thm(
  "EXP_THM",
  ``!m n. m ** n = if n = 0 then 1 else if n = 1 then m else
      if EVEN n then (m * m) ** HALF n else m * ((m * m) ** (HALF n))``,
  metis_tac[EXP_0, EXP_1, EXP_EVEN, EXP_ODD, EVEN_ODD]);

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
val EXP_MOD_EQN = store_thm(
  "EXP_MOD_EQN",
  ``!b n m. 1 < m ==>
      ((b ** n) MOD m =
       if (n = 0) then 1
       else let result = (b * b) ** (HALF n) MOD m
             in if EVEN n then result else (b * result) MOD m)``,
  rw[] >-
  rw[EXP_0, ONE_MOD] >-
  metis_tac[EXP_EVEN, EXP_2] >>
  metis_tac[EXP_ODD, EXP_2, EVEN_ODD]);

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

(* arithmeticTheory.LESS_DIV_EQ_ZERO = |- !r n. r < n ==> (r DIV n = 0) *)

(* Theorem: 0 < n ==> ((m DIV n = 0) <=> m < n) *)
(* Proof:
   If part: 0 < n /\ m DIV n = 0 ==> m < n
      Since m = m DIV n * n + m MOD n) /\ (m MOD n < n)   by DIVISION, 0 < n
         so m = 0 * n + m MOD n            by m DIV n = 0
              = 0 + m MOD n                by MULT
              = m MOD n                    by ADD
      Since m MOD n < n, m < n.
   Only-if part: 0 < n /\ m < n ==> m DIV n = 0
      True by LESS_DIV_EQ_ZERO.
*)
Theorem DIV_EQ_0 : (* TODO: name conflict with arithmeticTheory.DIV_EQ_0 *)
    !m n. 0 < n ==> ((m DIV n = 0) <=> m < n)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[DIVISION, MULT, ADD] >>
  rw[LESS_DIV_EQ_ZERO]
QED

(* Theorem: 0 < n /\ m divides n ==> 0 < (n DIV m) *)
(* Proof:
   Given 0 < n /\ m divides n,
     ==> 0 < m              by ZERO_DIVIDES, n <> 0, so m <> 0
     and m <= n             by DIVIDES_LE
   By contradiction, suppose ~(0 < n DIV m).
   That means n DIV m = 0   by arithmetic
   Thus n < m               by DIV_EQ_0
   This contradicts m <= n.
*)
val DIV_POS = store_thm(
  "DIV_POS",
  ``!m n. 0 < n /\ m divides n ==> 0 < (n DIV m)``,
  rpt strip_tac >>
  `0 < m /\ m <= n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO, DIVIDES_LE] >>
  spose_not_then strip_assume_tac >>
  `n DIV m = 0` by decide_tac >>
  `n < m` by rw[GSYM DIV_EQ_0] >>
  decide_tac);

(*
DIV_LE_MONOTONE  |- !n x y. 0 < n /\ x <= y ==> x DIV n <= y DIV n
DIV_LE_X         |- !x y z. 0 < z ==> (y DIV z <= x <=> y < (x + 1) * z)
*)

(* Theorem: 0 < y /\ x <= y * z ==> x DIV y <= z *)
(* Proof:
             x <= y * z
   ==> x DIV y <= (y * z) DIV y      by DIV_LE_MONOTONE, 0 < y
                = z                  by MULT_TO_DIV
*)
val DIV_LE = store_thm(
  "DIV_LE",
  ``!x y z. 0 < y /\ x <= y * z ==> x DIV y <= z``,
  metis_tac[DIV_LE_MONOTONE, MULT_TO_DIV]);

(* Theorem: 0 < n ==> !x y. (x * n = y) ==> (x = y DIV n) *)
(* Proof:
     x = (x * n + 0) DIV n     by DIV_MULT, 0 < n
       = (x * n) DIV n         by ADD_0
*)
val DIV_SOLVE = store_thm(
  "DIV_SOLVE",
  ``!n. 0 < n ==> !x y. (x * n = y) ==> (x = y DIV n)``,
  metis_tac[DIV_MULT, ADD_0]);

(* Theorem: 0 < n ==> !x y. (n * x = y) ==> (x = y DIV n) *)
(* Proof: by DIV_SOLVE, MULT_COMM *)
val DIV_SOLVE_COMM = store_thm(
  "DIV_SOLVE_COMM",
  ``!n. 0 < n ==> !x y. (n * x = y) ==> (x = y DIV n)``,
  rw[DIV_SOLVE]);

(* Theorem: 1 < n ==> (1 DIV n = 0) *)
(* Proof:
   Since  1 = (1 DIV n) * n + (1 MOD n)   by DIVISION, 0 < n.
     and  1 MOD n = 1                     by ONE_MOD, 1 < n.
    thus  (1 DIV n) * n = 0               by arithmetic
      or  1 DIV n = 0  since n <> 0       by MULT_EQ_0
*)
val ONE_DIV = store_thm(
  "ONE_DIV",
  ``!n. 1 < n ==> (1 DIV n = 0)``,
  rpt strip_tac >>
  `0 < n /\ n <> 0` by decide_tac >>
  `1 = (1 DIV n) * n + (1 MOD n)` by rw[DIVISION] >>
  `_ = (1 DIV n) * n + 1` by rw[ONE_MOD] >>
  `(1 DIV n) * n = 0` by decide_tac >>
  metis_tac[MULT_EQ_0]);

(* Theorem: ODD n ==> !m. m divides n ==> ODD m *)
(* Proof:
   Since m divides n
     ==> ?q. n = q * m      by divides_def
   By contradiction, suppose ~ODD m.
   Then EVEN m              by ODD_EVEN
    and EVEN (q * m) = EVEN n    by EVEN_MULT
     or ~ODD n                   by ODD_EVEN
   This contradicts with ODD n.
*)
val DIVIDES_ODD = store_thm(
  "DIVIDES_ODD",
  ``!n. ODD n ==> !m. m divides n ==> ODD m``,
  metis_tac[divides_def, EVEN_MULT, EVEN_ODD]);

(* Note: For EVEN n, m divides n cannot conclude EVEN m.
Example: EVEN 2 or ODD 3 both divides EVEN 6.
*)

(* Theorem: EVEN m ==> !n. m divides n ==> EVEN n*)
(* Proof:
   Since m divides n
     ==> ?q. n = q * m      by divides_def
   Given EVEN m
    Then EVEN (q * m) = n   by EVEN_MULT
*)
val DIVIDES_EVEN = store_thm(
  "DIVIDES_EVEN",
  ``!m. EVEN m ==> !n. m divides n ==> EVEN n``,
  metis_tac[divides_def, EVEN_MULT]);

(* Theorem: n divides m <=> m MOD n = 0 *)
(* Proof:
   if part: n divides m ==> m MOD n = 0
       n divides m
   ==> ?q. m = q * n               by divides_def
   ==>   m MOD n
       = (q * n) MOD n             by substitution
       = 0                         by MOD_EQ_0
   only-if part: m MOD n = 0 ==> n divides m
   m = (m DIV n) * n + (m MOD n)   by DIVISION
     = (m DIV n) * n               by ADD_0 and given
   Hence  n divides m              by divides_def
   Or,
       m MOD n = 0
   <=> ?d. m = d * n    by MOD_EQ_0_DIVISOR, 0 < n
   <=> n divides m      by divides_def
*)
val DIVIDES_MOD_0 = store_thm(
  "DIVIDES_MOD_0",
  ``!n. 0 < n ==> !m. n divides m <=> (m MOD n = 0)``,
  metis_tac[MOD_EQ_0_DIVISOR, divides_def]);

(* Theorem: EVEN n = 2 divides n *)
(* Proof:
       EVEN n
   <=> n MOD 2 = 0     by EVEN_MOD2
   <=> 2 divides n     by DIVIDES_MOD_0, 0 < 2
*)
val EVEN_ALT = store_thm(
  "EVEN_ALT",
  ``!n. EVEN n = 2 divides n``,
  rw[EVEN_MOD2, DIVIDES_MOD_0]);

(* Theorem: ODD n = ~(2 divides n) *)
(* Proof:
   Note n MOD 2 < 2    by MOD_LESS
    and !x. x < 2 <=> (x = 0) \/ (x = 1)   by arithmetic
       ODD n
   <=> n MOD 2 = 1     by ODD_MOD2
   <=> ~(2 divides n)  by DIVIDES_MOD_0, 0 < 2
   Or,
   ODD n = ~(EVEN n)        by ODD_EVEN
         = ~(2 divides n)   by EVEN_ALT
*)
val ODD_ALT = store_thm(
  "ODD_ALT",
  ``!n. ODD n = ~(2 divides n)``,
  metis_tac[EVEN_ODD, EVEN_ALT]);

(* Theorem: 0 < n ==> !q. (q DIV n) * n <= q *)
(* Proof:
   Since q = (q DIV n) * n + q MOD n  by DIVISION
    Thus     (q DIV n) * n <= q       by discarding remainder
*)
val DIV_MULT_LE = store_thm(
  "DIV_MULT_LE",
  ``!n. 0 < n ==> !q. (q DIV n) * n <= q``,
  rpt strip_tac >>
  `q = (q DIV n) * n + q MOD n` by rw[DIVISION] >>
  decide_tac);

(* Theorem: 0 < n ==> !q. n divides q <=> ((q DIV n) * n = q) *)
(* Proof:
   If part: n divides q ==> q DIV n * n = q
     q = (q DIV n) * n + q MOD n  by DIVISION
       = (q DIV n) * n + 0        by MOD_EQ_0_DIVISOR, divides_def
       = (q DIV n) * n            by ADD_0
   Only-if part: q DIV n * n = q ==> n divides q
     True by divides_def
*)
val DIV_MULT_EQ = store_thm(
  "DIV_MULT_EQ",
  ``!n. 0 < n ==> !q. n divides q <=> ((q DIV n) * n = q)``,
  metis_tac[divides_def, DIVISION, MOD_EQ_0_DIVISOR, ADD_0]);
(* same as DIVIDES_EQN below *)

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

(* Theorem: 0 < x /\ 0 < y /\ x <= y ==> !n. n DIV y <= n DIV x *)
(* Proof:
   If n DIV y = 0,
      Then 0 <= n DIV x is trivially true.
   If n DIV y <> 0,
     (n DIV y) * x <= (n DIV y) * y        by LE_MULT_LCANCEL, x <= y, n DIV y <> 0
                   <= n                    by DIV_MULT_LE
  Hence        (n DIV y) * x <= n          by LESS_EQ_TRANS
  Then ((n DIV y) * x) DIV x <= n DIV x    by DIV_LE_MONOTONE
  or                 n DIV y <= n DIV x    by MULT_DIV
*)
val DIV_LE_MONOTONE_REVERSE = store_thm(
  "DIV_LE_MONOTONE_REVERSE",
  ``!x y. 0 < x /\ 0 < y /\ x <= y ==> !n. n DIV y <= n DIV x``,
  rpt strip_tac >>
  Cases_on `n DIV y = 0` >-
  decide_tac >>
  `(n DIV y) * x <= (n DIV y) * y` by rw[LE_MULT_LCANCEL] >>
  `(n DIV y) * y <= n` by rw[DIV_MULT_LE] >>
  `(n DIV y) * x <= n` by decide_tac >>
  `((n DIV y) * x) DIV x <= n DIV x` by rw[DIV_LE_MONOTONE] >>
  metis_tac[MULT_DIV]);

(* Theorem: n divides m <=> (m = (m DIV n) * n) *)
(* Proof:
   Since n divides m <=> m MOD n = 0     by DIVIDES_MOD_0
     and m = (m DIV n) * n + (m MOD n)   by DIVISION
   If part: n divides m ==> m = m DIV n * n
      This is true                       by ADD_0
   Only-if part: m = m DIV n * n ==> n divides m
      Since !x y. x + y = x <=> y = 0    by ADD_INV_0
   The result follows.
*)
val DIVIDES_EQN = store_thm(
  "DIVIDES_EQN",
  ``!n. 0 < n ==> !m. n divides m <=> (m = (m DIV n) * n)``,
  metis_tac[DIVISION, DIVIDES_MOD_0, ADD_0, ADD_INV_0]);

(* Theorem: 0 < n ==> !m. n divides m <=> (m = n * (m DIV n)) *)
(* Proof: vy DIVIDES_EQN, MULT_COMM *)
val DIVIDES_EQN_COMM = store_thm(
  "DIVIDES_EQN_COMM",
  ``!n. 0 < n ==> !m. n divides m <=> (m = n * (m DIV n))``,
  rw_tac std_ss[DIVIDES_EQN, MULT_COMM]);

(* Theorem: 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1) *)
(* Proof:
   Apply DIV_SUB |> GEN_ALL |> SPEC ``1`` |> REWRITE_RULE[MULT_RIGHT_1];
   val it = |- !n m. 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1): thm
*)
val SUB_DIV = save_thm("SUB_DIV",
    DIV_SUB |> GEN ``n:num`` |> GEN ``m:num`` |> GEN ``q:num`` |> SPEC ``1`` |> REWRITE_RULE[MULT_RIGHT_1]);
(* val SUB_DIV = |- !m n. 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1): thm *)


(* Note:
SUB_DIV    |- !m n. 0 < n /\ n <= m ==> (m - n) DIV n = m DIV n - 1
SUB_MOD    |- !m n. 0 < n /\ n <= m ==> (m - n) MOD n = m MOD n
*)

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

(*
Note: !n. 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n))    is almost MULT_EQ_DIV,
                                  but actually DIVIDES_EQN, DIVIDES_MOD_0, EQ_MULT_RCANCEL. See below.
Note: !n. 0 < n ==> !k m. (m MOD n = 0) ==> (k * n <= m <=> k <= m DIV n)      is X_LE_DIV, no m MOD n = 0.
Note: !n. 0 < n ==> !k m. (m MOD n = 0) ==> ((k + 1) * n <= m <=> k < m DIV n) is X_LT_DIV, no m MOD n = 0.
Note: !n. 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n)        is below next.
*)

(* Theorem: 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n)) *)
(* Proof:
   Note m MOD n = 0
    ==> n divides m            by DIVIDES_MOD_0, 0 < n
    ==> m = (m DIV n) * n      by DIVIDES_EQN, 0 < n
       k * n = m
   <=> k * n = (m DIV n) * n   by above
   <=>     k = (m DIV n)       by EQ_MULT_RCANCEL, n <> 0.
*)
val DIV_EQ_MULT = store_thm(
  "DIV_EQ_MULT",
  ``!n. 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n))``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `m = (m DIV n) * n` by rw[GSYM DIVIDES_EQN, DIVIDES_MOD_0] >>
  metis_tac[EQ_MULT_RCANCEL]);

(* Theorem: 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n) *)
(* Proof:
       k * n < m
   <=> k * n < (m DIV n) * n    by DIVIDES_EQN, DIVIDES_MOD_0, 0 < n
   <=>     k < m DIV n          by LT_MULT_RCANCEL, n <> 0
*)
val MULT_LT_DIV = store_thm(
  "MULT_LT_DIV",
  ``!n. 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n)``,
  metis_tac[DIVIDES_EQN, DIVIDES_MOD_0, LT_MULT_RCANCEL, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n ==> !k m. (m MOD n = 0) ==> (m <= n * k <=> m DIV n <= k) *)
(* Proof:
       m <= n * k
   <=> (m DIV n) * n <= n * k   by DIVIDES_EQN, DIVIDES_MOD_0, 0 < n
   <=> (m DIV n) * n <= k * n   by MULT_COMM
   <=>       m DIV n <= k       by LE_MULT_RCANCEL, n <> 0
*)
val LE_MULT_LE_DIV = store_thm(
  "LE_MULT_LE_DIV",
  ``!n. 0 < n ==> !k m. (m MOD n = 0) ==> (m <= n * k <=> m DIV n <= k)``,
  metis_tac[DIVIDES_EQN, DIVIDES_MOD_0, MULT_COMM, LE_MULT_RCANCEL, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < m ==> ((n DIV m = 0) /\ (n MOD m = 0) <=> (n = 0)) *)
(* Proof:
   If part: (n DIV m = 0) /\ (n MOD m = 0) ==> (n = 0)
      Note n DIV m = 0 ==> n < m        by DIV_EQ_0
      Thus n MOD m = n                  by LESS_MOD
        or n = 0
   Only-if part: 0 DIV m = 0            by ZERO_DIV
                 0 MOD m = 0            by ZERO_MOD
*)
val DIV_MOD_EQ_0 = store_thm(
  "DIV_MOD_EQ_0",
  ``!m n. 0 < m ==> ((n DIV m = 0) /\ (n MOD m = 0) <=> (n = 0))``,
  rpt strip_tac >>
  rw[EQ_IMP_THM] >-
  metis_tac[DIV_EQ_0, LESS_MOD] >>
  rw[ZERO_DIV]);

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

(* Theorem: 0 < n /\ a ** n divides b ==> a divides b *)
(* Proof:
   Note ?k. n = SUC k              by num_CASES, n <> 0
    and ?q. b = q * (a ** n)       by divides_def
              = q * (a * a ** k)   by EXP
              = (q * a ** k) * a   by arithmetic
   Thus a divides b                by divides_def
*)
val EXP_DIVIDES = store_thm(
  "EXP_DIVIDES",
  ``!a b n. 0 < n /\ a ** n divides b ==> a divides b``,
  rpt strip_tac >>
  `?k. n = SUC k` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  `?q. b = q * a ** n` by rw[GSYM divides_def] >>
  `_ = q * (a * a ** k)` by rw[EXP] >>
  `_ = (q * a ** k) * a` by decide_tac >>
  metis_tac[divides_def]);

(* Theorem: prime a ==> a divides b iff a divides b ** n for any n *)
(* Proof:
   by induction on n.
   Base case: 0 < 0 ==> (a divides b <=> a divides (b ** 0))
     True since 0 < 0 is False.
   Step case: 0 < n ==> (a divides b <=> a divides (b ** n)) ==>
              0 < SUC n ==> (a divides b <=> a divides (b ** SUC n))
     i.e. 0 < n ==> (a divides b <=> a divides (b ** n))==>
                    a divides b <=> a divides (b * b ** n)    by EXP
     If n = 0, b ** 0 = 1   by EXP
     Hence true.
     If n <> 0, 0 < n,
     If part: a divides b /\ 0 < n ==> (a divides b <=> a divides (b ** n)) ==> a divides (b ** n)
       True by DIVIDES_MULT.
     Only-if part: a divides (b * b ** n) /\ 0 < n ==> (a divides b <=> a divides (b ** n)) ==> a divides (b ** n)
       Since prime a, a divides b, or a divides (b ** n)  by P_EUCLIDES
       Either case is true.
*)
val DIVIDES_EXP_BASE = store_thm(
  "DIVIDES_EXP_BASE",
  ``!a b n. prime a /\ 0 < n ==> (a divides b <=> a divides (b ** n))``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[EXP] >>
  Cases_on `n = 0` >-
  rw[EXP] >>
  `0 < n` by decide_tac >>
  rw[EQ_IMP_THM] >-
  metis_tac[DIVIDES_MULT] >>
  `a divides b \/ a divides (b ** n)` by rw[P_EUCLIDES] >>
  metis_tac[]);

(* Theorem: n divides m ==> !k. n divides (k * m) *)
(* Proof:
   n divides m ==> ?q. m = q * n   by divides_def
   Hence k * m = k * (q * n)
               = (k * q) * n       by MULT_ASSOC
   or n divides (k * m)            by divides_def
*)
val DIVIDES_MULTIPLE = store_thm(
  "DIVIDES_MULTIPLE",
  ``!m n. n divides m ==> !k. n divides (k * m)``,
  metis_tac[divides_def, MULT_ASSOC]);

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
val euclid_prime = save_thm("euclid_prime", P_EUCLIDES);
(* |- !p a b. prime p /\ p divides a * b ==> p divides a \/ p divides b *)

(* Theorem alias *)
val euclid_coprime = save_thm("euclid_coprime", L_EUCLIDES);
(* |- !a b c. (gcd a b = 1) /\ b divides a * c ==> b divides c *)

(* ------------------------------------------------------------------------- *)
(* Modulo Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> !a b. (a MOD n = b) <=> ?c. (a = c * n + b) /\ (b < n) *)
(* Proof:
   If part: (a MOD n = b) ==> ?c. (a = c * n + b) /\ (b < n)
      Or to show: ?c. (a = c * n + a MOD n) /\ a MOD n < n
      Taking c = a DIV n, this is true     by DIVISION
   Only-if part: (a = c * n + b) /\ (b < n) ==> (a MOD n = b)
      Or to show: b < n ==> (c * n + b) MOD n = b
        (c * n + b) MOD n
      = ((c * n) MOD n + b MOD n) MOD n    by MOD_PLUS
      = (0 + b MOD n) MOD n                by MOD_EQ_0
      = b MOD n                            by MOD_MOD
      = b                                  by LESS_MOD, b < n
*)
val MOD_EQN = store_thm(
  "MOD_EQN",
  ``!n. 0 < n ==> !a b. (a MOD n = b) <=> ?c. (a = c * n + b) /\ (b < n)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[DIVISION] >>
  metis_tac[MOD_PLUS, MOD_EQ_0, ADD, MOD_MOD, LESS_MOD]);

(* Theorem: (x + y + z) MOD n = (x MOD n + y MOD n + z MOD n) MOD n *)
(* Proof:
     (x + y + z) MOD n
   = ((x + y) MOD n + z MOD n) MOD n               by MOD_PLUS
   = ((x MOD n + y MOD n) MOD n + z MOD n) MOD n   by MOD_PLUS
   = (x MOD n + y MOD n + z MOD n) MOD n           by MOD_MOD
*)
val MOD_PLUS3 = store_thm(
  "MOD_PLUS3",
  ``!n. 0 < n ==> !x y z. (x + y + z) MOD n = (x MOD n + y MOD n + z MOD n) MOD n``,
  metis_tac[MOD_PLUS, MOD_MOD]);

(* Theorem: Addition is associative in MOD: if x, y, z all < n,
            ((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n. *)
(* Proof:
     ((x * y) MOD n * z) MOD n
   = (((x * y) MOD n) MOD n * z MOD n) MOD n     by MOD_TIMES2
   = ((x * y) MOD n * z MOD n) MOD n             by MOD_MOD
   = (x * y * z) MOD n                           by MOD_TIMES2
   = (x * (y * z)) MOD n                         by MULT_ASSOC
   = (x MOD n * (y * z) MOD n) MOD n             by MOD_TIMES2
   = (x MOD n * ((y * z) MOD n) MOD n) MOD n     by MOD_MOD
   = (x * (y * z) MOD n) MOD n                   by MOD_TIMES2
   or
     ((x + y) MOD n + z) MOD n
   = ((x + y) MOD n + z MOD n) MOD n     by LESS_MOD, z < n
   = (x + y + z) MOD n                   by MOD_PLUS
   = (x + (y + z)) MOD n                 by ADD_ASSOC
   = (x MOD n + (y + z) MOD n) MOD n     by MOD_PLUS
   = (x + (y + z) MOD n) MOD n           by LESS_MOD, x < n
*)
val MOD_ADD_ASSOC = store_thm(
  "MOD_ADD_ASSOC",
  ``!n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==> (((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n)``,
  metis_tac[LESS_MOD, MOD_PLUS, ADD_ASSOC]);

(* Theorem: mutliplication is associative in MOD:
            (x*y MOD n * z) MOD n = (x * y*Z MOD n) MOD n  *)
(* Proof:
     ((x * y) MOD n * z) MOD n
   = (((x * y) MOD n) MOD n * z MOD n) MOD n     by MOD_TIMES2
   = ((x * y) MOD n * z MOD n) MOD n             by MOD_MOD
   = (x * y * z) MOD n                           by MOD_TIMES2
   = (x * (y * z)) MOD n                         by MULT_ASSOC
   = (x MOD n * (y * z) MOD n) MOD n             by MOD_TIMES2
   = (x MOD n * ((y * z) MOD n) MOD n) MOD n     by MOD_MOD
   = (x * (y * z) MOD n) MOD n                   by MOD_TIMES2
   or
     ((x * y) MOD n * z) MOD n
   = ((x * y) MOD n * z MOD n) MOD n    by LESS_MOD, z < n
   = (((x * y) * z) MOD n) MOD n        by MOD_TIMES2
   = ((x * (y * z)) MOD n) MOD n        by MULT_ASSOC
   = (x MOD n * (y * z) MOD n) MOD n    by MOD_TIMES2
   = (x * (y * z) MOD n) MOD n          by LESS_MOD, x < n
*)
val MOD_MULT_ASSOC = store_thm(
  "MOD_MULT_ASSOC",
  ``!n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==> (((x * y) MOD n * z) MOD n = (x * (y * z) MOD n) MOD n)``,
  metis_tac[LESS_MOD, MOD_TIMES2, MULT_ASSOC]);

(* Theorem: If n > 0, ((n - x) MOD n + x) MOD n = 0  for x < n. *)
(* Proof:
     ((n - x) MOD n + x) MOD n
   = ((n - x) MOD n + x MOD n) MOD n    by LESS_MOD
   = (n - x + x) MOD n                  by MOD_PLUS
   = n MOD n                            by SUB_ADD and 0 <= n
   = (1*n) MOD n                        by MULT_LEFT_1
   = 0                                  by MOD_EQ_0
*)
val MOD_ADD_INV = store_thm(
  "MOD_ADD_INV",
  ``!n x. 0 < n /\ x < n ==> (((n - x) MOD n + x) MOD n = 0)``,
  metis_tac[LESS_MOD, MOD_PLUS, SUB_ADD, LESS_IMP_LESS_OR_EQ, MOD_EQ_0, MULT_LEFT_1]);

(* Theorem: If n > 0, k MOD n = 0 ==> !x. (k*x) MOD n = 0 *)
(* Proof:
   (k*x) MOD n = (k MOD n * x MOD n) MOD n    by MOD_TIMES2
               = (0 * x MOD n) MOD n          by given
               = 0 MOD n                      by MULT_0 and MULT_COMM
               = 0                            by ZERO_MOD
*)
val MOD_MULITPLE_ZERO = store_thm(
  "MOD_MULITPLE_ZERO",
  ``!n k. 0 < n /\ (k MOD n = 0) ==> !x. ((k*x) MOD n = 0)``,
  metis_tac[MOD_TIMES2, MULT_0, MULT_COMM, ZERO_MOD]);

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

(* Theorem: n < m ==> ((n MOD m = 0) <=> (n = 0)) *)
(* Proof:
   Note n < m ==> (n MOD m = n)    by LESS_MOD
   Thus (n MOD m = 0) <=> (n = 0)  by above
*)
val MOD_EQ_0_IFF = store_thm(
  "MOD_EQ_0_IFF",
  ``!m n. n < m ==> ((n MOD m = 0) <=> (n = 0))``,
  rw_tac bool_ss[LESS_MOD]);

(* Theorem: ((a MOD n) ** m) MOD n = (a ** m) MOD n  *)
(* Proof: by induction on m.
   Base case: (a MOD n) ** 0 MOD n = a ** 0 MOD n
       (a MOD n) ** 0 MOD n
     = 1 MOD n              by EXP
     = a ** 0 MOD n         by EXP
   Step case: (a MOD n) ** m MOD n = a ** m MOD n ==> (a MOD n) ** SUC m MOD n = a ** SUC m MOD n
       (a MOD n) ** SUC m MOD n
     = ((a MOD n) * (a MOD n) ** m) MOD n             by EXP
     = ((a MOD n) * (((a MOD n) ** m) MOD n)) MOD n   by MOD_TIMES2, MOD_MOD
     = ((a MOD n) * (a ** m MOD n)) MOD n             by induction hypothesis
     = (a * a ** m) MOD n                             by MOD_TIMES2
     = a ** SUC m MOD n                               by EXP
*)
val MOD_EXP = store_thm(
  "MOD_EXP",
  ``!n. 0 < n ==> !a m. ((a MOD n) ** m) MOD n = (a ** m) MOD n``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[EXP] >>
  `(a MOD n) ** SUC m MOD n = ((a MOD n) * (a MOD n) ** m) MOD n` by rw[EXP] >>
  `_ = ((a MOD n) * (((a MOD n) ** m) MOD n)) MOD n` by metis_tac[MOD_TIMES2, MOD_MOD] >>
  `_ = ((a MOD n) * (a ** m MOD n)) MOD n` by rw[] >>
  `_ = (a * a ** m) MOD n` by rw[MOD_TIMES2] >>
  rw[EXP]);


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
val EXP_2_EVEN = store_thm(
  "EXP_2_EVEN",
  ``!n. 0 < n ==> EVEN (2 ** n)``,
  rw[EVEN_MOD2, ZERO_EXP]);
(* Michael's proof by induction *)
val EXP_2_EVEN = store_thm(
  "EXP_2_EVEN",
  ``!n. 0 < n ==> EVEN (2 ** n)``,
  Induct >> rw[EXP, EVEN_DOUBLE]);

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

(*
> LINEAR_GCD |> SPEC ``j:num`` |> SPEC ``k:num``;
val it = |- j <> 0 ==> ?p q. p * j = q * k + gcd k j: thm
*)

(* Theorem: 0 < j ==> ?p q. p * j = q * k + gcd j k *)
(* Proof: by LINEAR_GCD, GCD_SYM *)
val GCD_LINEAR = store_thm(
  "GCD_LINEAR",
  ``!j k. 0 < j ==> ?p q. p * j = q * k + gcd j k``,
  metis_tac[LINEAR_GCD, GCD_SYM, NOT_ZERO]);

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

(* Theorem: EVEN n /\ prime n ==> (n = 2) *)
(* Proof:
   EVEN n ==> n MOD 2 = 0    by EVEN_MOD2
          ==> 2 divides n    by DIVIDES_MOD_0, 0 < 2
          ==> n = 2          by prime_def, 2 <> 1
*)
val EVEN_PRIME = store_thm(
  "EVEN_PRIME",
  ``!n. EVEN n /\ prime n ==> (n = 2)``,
  rpt strip_tac >>
  `0 < 2 /\ 2 <> 1` by decide_tac >>
  `2 divides n` by rw[DIVIDES_MOD_0, GSYM EVEN_MOD2] >>
  metis_tac[prime_def]);

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
(* Proof:
   Since 2 ** n = (2 ** n) DIV 2 * 2 + (2 ** n) MOD 2   by DIVISION
   But  (2 ** n) MOD 2
      = ((2 MOD 2) ** n) MOD 2     by EXP_MOD
      = (0 ** n) MOD 2             by DIVMOD_ID
      = 0 MOD 2                    by ZERO_EXP, n <> 0
      = 0                          by ZERO_MOD, 0 < n
   Now  2 ** n
      = 2 ** SUC (n - 1)
      = 2 * 2 ** (n - 1)                by EXP
      = 2 * (2 ** n DIV 2)              by MULT_COMM, above
   Hence 2 ** (n - 1) = (2 ** n) DIV 2  by MULT_LEFT_CANCEL
*)
val EXP_2_HALF = store_thm(
  "EXP_2_HALF",
  ``!n. 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1))``,
  rpt strip_tac >>
  `2 ** n = (2 ** n) DIV 2 * 2 + (2 ** n) MOD 2` by rw[DIVISION] >>
  `(2 ** n) MOD 2 = ((2 MOD 2) ** n) MOD 2` by rw[] >>
  `2 MOD 2 = 0` by rw[] >>
  `n <> 0` by decide_tac >>
  `0 ** n = 0` by rw[] >>
  `(2 ** n) MOD 2 = 0` by rw[] >>
  `2 ** n = 2 ** n DIV 2 * 2` by decide_tac >>
  `n = SUC (n - 1)` by decide_tac >>
  `2 * 2 ** (n - 1) = 2 * (2 ** n DIV 2)` by metis_tac[EXP, MULT_COMM] >>
  decide_tac);
(* Michael's proof by induction *)
val EXP_2_HALF = store_thm(
  "EXP_2_HALF",
  ``!n. 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1))``,
  Induct >>
  simp[EXP, MULT_TO_DIV]);

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
val MULT_LESS_IMP_LESS = store_thm(
  "MULT_LESS_IMP_LESS",
  ``!m n k. 0 < k /\ k * m < n ==> m < n``,
  rpt strip_tac >>
  `k <> 0` by decide_tac >>
  `?h. k = SUC h` by metis_tac[num_CASES] >>
  `k * m = h * m + m` by rw[ADD1] >>
  decide_tac);

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

(* Theorem: 1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100 *)
(* Proof: by calculation. *)
val fit_for_100 = store_thm(
  "fit_for_100",
  ``1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100``,
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* HelperSet Documentation                                                   *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   countFrom m n        = IMAGE ($+ m) (count n)
   s =|= u # v          = split s u v
   equiv_class R s x    = {y | y IN s /\ R x y}
   EVERY_FINITE  P      = !s. s IN P ==> FINITE s
   PAIR_DISJOINT P      = !s t. s IN P /\ t IN P /\ ~(s = t) ==> DISJOINT s t
   SET_ADDITIVE f       = (f {} = 0) /\
                          (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) + f (s INTER t) = f s + f t))
   SET_MULTIPLICATIVE f = (f {} = 1) /\
                          (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) * f (s INTER t) = f s * f t))
   f PERMUTES s         = BIJ f s s
   PPOW s               = (POW s) DIFF {s}
*)
(* Definitions and Theorems (# are exported):

   Logic Theorems:
   EQ_IMP2_THM         |- !A B. (A <=> B) <=> (A ==> B) /\ ((A ==> B) ==> B ==> A)
   BOOL_EQ             |- !b1 b2 f. (b1 <=> b2) ==> (f b1 = f b2)
   IMP_IMP             |- !b c d. b /\ (c ==> d) ==> (b ==> c) ==> d
   AND_IMP_OR_NEG      |- !p q. p /\ q ==> p \/ ~q
   OR_IMP_IMP          |- !p q r. (p \/ q ==> r) ==> p /\ ~q ==> r
   PUSH_IN_INTO_IF     |- !b x s t. x IN (if b then s else t) <=> if b then x IN s else x IN t

   Set Theorems:
   IN_SUBSET           |- !s t. s SUBSET t <=> !x. x IN s ==> x IN t
   DISJOINT_DIFF       |- !s t. DISJOINT (s DIFF t) t /\ DISJOINT t (s DIFF t)
   DISJOINT_DIFF_IFF   |- !s t. DISJOINT s t <=> (s DIFF t = s)
   UNION_DIFF_EQ_UNION |- !s t. s UNION (t DIFF s) = s UNION t
   INTER_DIFF          |- !s t. (s INTER (t DIFF s) = {}) /\ ((t DIFF s) INTER s = {})
   BIGINTER_SUBSET     |- !P X. P <> {} /\ (!Y. Y IN P ==> Y SUBSET X) ==> BIGINTER P SUBSET X
   SUBSET_SING         |- !s x. {x} SUBSET s /\ SING s <=> (s = {x})
   INTER_SING          |- !s x. x IN s ==> (s INTER {x} = {x})
   ONE_ELEMENT_SING    |- !s a. s <> {} /\ (!k. k IN s ==> (k = a)) ==> (s = {a})
   SING_ONE_ELEMENT    |- !s. s <> {} ==> (SING s <=> !x y. x IN s /\ y IN s ==> (x = y))
   SING_ELEMENT        |- !s. SING s ==> !x y. x IN s /\ y IN s ==> (x = y)
   SING_TEST           |- !s. SING s <=> s <> {} /\ !x y. x IN s /\ y IN s ==> (x = y)
   SING_INTER          |- !s x. {x} INTER s = if x IN s then {x} else {}
   IN_SING_OR_EMPTY    |- !b x y. x IN (if b then {y} else {}) ==> (x = y)
   SING_CARD_1         |- !s. SING s ==> (CARD s = 1)
   CARD_EQ_1           |- !s. FINITE s ==> ((CARD s = 1) <=> SING s)
   INSERT_DELETE_COMM  |- !s x y. x <> y ==> ((x INSERT s) DELETE y = x INSERT s DELETE y)
   SUBSET_INTER_SUBSET |- !s t u. s SUBSET u ==> s INTER t SUBSET u
   DIFF_DIFF_EQ_INTER  |- !s t. s DIFF (s DIFF t) = s INTER t
   SET_EQ_BY_DIFF      |- !s t. (s = t) <=> s SUBSET t /\ (t DIFF s = {})
   SUBSET_INSERT_SUBSET|- !s t. s SUBSET t ==> !x. x INSERT s SUBSET x INSERT t
   INSERT_SUBSET_SUBSET|- !s t x. x NOTIN s /\ x INSERT s SUBSET t ==> s SUBSET t DELETE x
   DIFF_DELETE         |- !s t x. s DIFF t DELETE x = s DIFF (x INSERT t)
   SUBSET_DIFF_CARD    |- !a b. FINITE a /\ b SUBSET a ==> (CARD (a DIFF b) = CARD a - CARD b)
   SUBSET_SING_IFF     |- !s x. s SUBSET {x} <=> (s = {}) \/ (s = {x})

   Image and Bijection:
   INJ_CONG            |- !f g s t. (!x. x IN s ==> (f x = g x)) ==> (INJ f s t <=> INJ g s t)
   SURJ_CONG           |- !f g s t. (!x. x IN s ==> (f x = g x)) ==> (SURJ f s t <=> SURJ g s t)
   BIJ_CONG            |- !f g s t. (!x. x IN s ==> (f x = g x)) ==> (BIJ f s t <=> BIJ g s t)
   INJ_ELEMENT         |- !f s t x. INJ f s t /\ x IN s ==> f x IN t
   SURJ_ELEMENT        |- !f s t x. SURJ f s t /\ x IN s ==> f x IN t
   BIJ_ELEMENT         |- !f s t x. BIJ f s t /\ x IN s ==> f x IN t
   INJ_UNIV            |- !f s t. INJ f s t ==> INJ f s univ(:'b)
   INJ_SUBSET_UNIV     |- !f s. INJ f univ(:'a) univ(:'b) ==> INJ f s univ(:'b)
   INJ_IMAGE_BIJ       |- !f s. INJ f s univ(:'b) ==> BIJ f s (IMAGE f s)
   INJ_IMAGE_EQ        |- !P f. INJ f P univ(:'b) ==> !s t. s SUBSET P /\ t SUBSET P ==>
                                ((IMAGE f s = IMAGE f t) <=> (s = t))
   INJ_IMAGE_INTER     |- !P f. INJ f P univ(:'b) ==> !s t. s SUBSET P /\ t SUBSET P ==>
                                (IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t)
   INJ_IMAGE_DISJOINT  |- !P f. INJ f P univ(:'b) ==> !s t. s SUBSET P /\ t SUBSET P ==>
                                (DISJOINT s t <=> DISJOINT (IMAGE f s) (IMAGE f t))
   INJ_I               |- !s. INJ I s univ(:'a)
   INJ_I_IMAGE         |- !s f. INJ I (IMAGE f s) univ(:'b)
   BIJ_ALT             |- !f s t. BIJ f s t <=>
                          (!x. x IN s ==> f x IN t) /\ !y. y IN t ==> ?!x. x IN s /\ (f x = y)
   BIJ_IS_INJ          |- !f s t. BIJ f s t ==>
                          !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)
   INJ_EQ_11           |- !f s x y. INJ f s s /\ x IN s /\ y IN s ==> ((f x = f y) <=> (x = y))
   BIJ_I_SAME          |- !s. BIJ I s s
 # IMAGE_I             |- !s. IMAGE I s = s
   IMAGE_K             |- !s. s <> {} ==> !e. IMAGE (K e) s = {e}
   IMAGE_SING          |- !f x. IMAGE f {x} = {f x}
   IMAGE_SUBSET_TARGET |- !f s t. (!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t
   IMAGE_ELEMENT_CONDITION  |- !f. (!x y. (f x = f y) ==> (x = y)) ==> !s e. e IN s <=> f e IN IMAGE f s
   BIGUNION_ELEMENTS_SING   |- !s. BIGUNION (IMAGE (\x. {x}) s) = s
   IMAGE_INJ_SUBSET_DIFF    |- !s t f. s SUBSET t /\ INJ f t univ(:'b) ==>
                                         (IMAGE f (t DIFF s) = IMAGE f t DIFF IMAGE f s)

   More Theorems and Sets for Counting:
   COUNT_0             |- count 0 = {}
   COUNT_1             |- count 1 = {0}
   COUNT_NOT_SELF      |- !n. n NOTIN count n
   COUNT_EQ_EMPTY      |- !n. (count n = {}) <=> (n = 0)
   COUNT_SUBSET        |- !m n. m <= n ==> count m SUBSET count n
   COUNT_SUC_SUBSET    |- !n t. count (SUC n) SUBSET t <=> count n SUBSET t /\ n IN t
   DIFF_COUNT_SUC      |- !n t. t DIFF count (SUC n) = t DIFF count n DELETE n
   COUNT_SUC_BY_SUC    |- !n. count (SUC n) = 0 INSERT IMAGE SUC (count n)
   IMAGE_COUNT_SUC     |- !f n. IMAGE f (count (SUC n)) = f n INSERT IMAGE f (count n)
   IMAGE_COUNT_SUC_BY_SUC
                       |- !f n. IMAGE f (count (SUC n)) = f 0 INSERT IMAGE (f o SUC) (count n)
   countFrom_0         |- !m. countFrom m 0 = {}
   countFrom_SUC       |- !m n m n. countFrom m (SUC n) = m INSERT countFrom (m + 1) n
   countFrom_first     |- !m n. 0 < n ==> m IN countFrom m n
   countFrom_less      |- !m n x. x < m ==> x NOTIN countFrom m n
   count_by_countFrom     |- !n. count n = countFrom 0 n
   count_SUC_by_countFrom |- !n. count (SUC n) = 0 INSERT countFrom 1 n

   CARD_UNION_3_EQN    |- !a b c. FINITE a /\ FINITE b /\ FINITE c ==>
                                  (CARD (a UNION b UNION c) =
                                   CARD a + CARD b + CARD c + CARD (a INTER b INTER c) -
                                   CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c))
   CARD_UNION_3_DISJOINT
                       |- !a b c. FINITE a /\ FINITE b /\ FINITE c /\
                                  DISJOINT a b /\ DISJOINT b c /\ DISJOINT a c ==>
                                  (CARD (a UNION b UNION c) = CARD a + CARD b + CARD c)

   Maximum and Minimum of a Set:
   MAX_SET_LESS        |- !s n. FINITE s /\ MAX_SET s < n ==> !x. x IN s ==> x < n
   MAX_SET_TEST        |- !s. FINITE s /\ s <> {} ==>
                          !x. x IN s /\ (!y. y IN s ==> y <= x) ==> (x = MAX_SET s)
   MIN_SET_TEST        |- !s. s <> {} ==>
                          !x. x IN s /\ (!y. y IN s ==> x <= y) ==> (x = MIN_SET s)
   MAX_SET_TEST_IFF    |- !s. FINITE s /\ s <> {} ==> !x. x IN s ==>
                              ((MAX_SET s = x) <=> !y. y IN s ==> y <= x)
   MIN_SET_TEST_IFF    |- !s. s <> {} ==> !x. x IN s ==>
                              ((MIN_SET s = x) <=> !y. y IN s ==> x <= y)
   MAX_SET_EMPTY       |- MAX_SET {} = 0
   MAX_SET_SING        |- !e. MAX_SET {e} = e
   MAX_SET_IN_SET      |- !s. FINITE s /\ s <> {} ==> MAX_SET s IN s
   MAX_SET_PROPERTY    |- !s. FINITE s ==> !x. x IN s ==> x <= MAX_SET s
   MIN_SET_SING        |- !e. MIN_SET {e} = e
   MIN_SET_IN_SET      |- !s. s <> {} ==> MIN_SET s IN s
   MIN_SET_PROPERTY    |- !s. s <> {} ==> !x. x IN s ==> MIN_SET s <= x
   MAX_SET_DELETE      |- !s. FINITE s /\ s <> {} /\ s <> {MIN_SET s} ==>
                              (MAX_SET (s DELETE MIN_SET s) = MAX_SET s)
   MAX_SET_EQ_0        |- !s. FINITE s ==> ((MAX_SET s = 0) <=> (s = {}) \/ (s = {0}))
   MIN_SET_EQ_0        |- !s. s <> {} ==> ((MIN_SET s = 0) <=> 0 IN s)
   MAX_SET_IMAGE_SUC_COUNT  |- !n. MAX_SET (IMAGE SUC (count n)) = n
   MAX_SET_IMAGE_with_HALF  |- !f c x. HALF x <= c ==> f x <= MAX_SET {f x | HALF x <= c}
   MAX_SET_IMAGE_with_DIV   |- !f b c x. 0 < b /\ x DIV b <= c ==> f x <= MAX_SET {f x | x DIV b <= c}
   MAX_SET_IMAGE_with_DEC   |- !f b c x. x - b <= c ==> f x <= MAX_SET {f x | x - b <= c}

   Finite and Cardinality Theorems:
   INJ_CARD_IMAGE_EQN  |- !f s. INJ f s univ(:'b) /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)
   FINITE_INJ_AS_SURJ  |- !f s t. INJ f s t /\ FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> SURJ f s t
   FINITE_COUNT_IMAGE  |- !P n. FINITE {P x | x < n}
   FINITE_BIJ_PROPERTY |- !f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ (CARD s = CARD t)
   FINITE_CARD_IMAGE   |- !s f. (!x y. (f x = f y) <=> (x = y)) /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)
   CARD_IMAGE_SUC      |- !s. FINITE s ==> (CARD (IMAGE SUC s) = CARD s)
   CARD_UNION_DISJOINT |- !s t. FINITE s /\ FINITE t /\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t)
   image_mod_subset_count   |- !s n. 0 < n ==> IMAGE (\x. x MOD n) s SUBSET count n
   card_mod_image           |- !s n. 0 < n ==> CARD (IMAGE (\x. x MOD n) s) <= n
   card_mod_image_nonzero   |- !s n. 0 < n /\ 0 NOTIN IMAGE (\x. x MOD n) s ==>
                                               CARD (IMAGE (\x. x MOD n) s) < n

   Partition Property:
   finite_partition_property      |- !s. FINITE s ==> !u v. s =|= u # v ==> ((u = {}) <=> (v = s))
   finite_partition_by_predicate  |- !s. FINITE s ==> !P. (let u = {x | x IN s /\ P x} in
                                           let v = {x | x IN s /\ ~P x} in
                                           FINITE u /\ FINITE v /\ s =|= u # v)
   partition_by_subset    |- !s u. u SUBSET s ==> (let v = s DIFF u in s =|= u # v)
   partition_by_element   |- !s x. x IN s ==> s =|= {x} # s DELETE x

   Splitting of a set:
   SPLIT_EMPTY       |- !s t. s =|= {} # t <=> s = t
   SPLIT_UNION       |- !s u v a b. s =|= u # v /\ v =|= a # b ==> s =|= u UNION a # b /\ u UNION a =|= u # a
   SPLIT_EQ          |- !s u v. s =|= u # v <=> u SUBSET s /\ v = s DIFF u
   SPLIT_SYM         |- !s u v. s =|= u # v <=> s =|= v # u
   SPLIT_SYM_IMP     |- !s u v. s =|= u # v ==> s =|= v # u
   SPLIT_SING        |- !s v x. s =|= {x} # v <=> x IN s /\ v = s DELETE x
   SPLIT_SUBSETS     |- !s u v. s =|= u # v ==> u SUBSET s /\ v SUBSET s
   SPLIT_FINITE      |- !s u v. FINITE s /\ s =|= u # v ==> FINITE u /\ FINITE v
   SPLIT_CARD        |- !s u v. FINITE s /\ s =|= u # v ==> (CARD s = CARD u + CARD v)
   SPLIT_EQ_DIFF     |- !s u v. s =|= u # v <=> (u = s DIFF v) /\ (v = s DIFF u)
   SPLIT_BY_SUBSET   |- !s u. u SUBSET s ==> (let v = s DIFF u in s =|= u # v)
   SUBSET_DIFF_DIFF  |- !s t. t SUBSET s ==> (s DIFF (s DIFF t) = t)
   SUBSET_DIFF_EQ    |- !s1 s2 t. s1 SUBSET t /\ s2 SUBSET t /\ (t DIFF s1 = t DIFF s2) ==> (s1 = s2)

   Bijective Inverses:
   BIJ_LINV_ELEMENT  |- !f s t. BIJ f s t ==> !x. x IN t ==> LINV f s x IN s
   BIJ_LINV_THM      |- !f s t. BIJ f s t ==>
                                (!x. x IN s ==> (LINV f s (f x) = x)) /\ !x. x IN t ==> (f (LINV f s x) = x)
   BIJ_RINV_INV      |- !f s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==>
                                             !x. x IN s ==> (RINV f s (f x) = x)
   BIJ_RINV_BIJ      |- !f s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==> BIJ (RINV f s) t s
   LINV_SUBSET       |- !f s t. INJ f t t /\ s SUBSET t ==> !x. x IN s ==> (LINV f t (f x) = x)

   Iteration, Summation and Product:
   ITSET_SING           |- !f x b. ITSET f {x} b = f x b
   ITSET_PROPERTY       |- !s f b. FINITE s /\ s <> {} ==>
                                   (ITSET f s b = ITSET f (REST s) (f (CHOICE s) b))
   ITSET_CONG           |- !f g. (f = g) ==> (ITSET f = ITSET g)
   ITSET_REDUCTION      |- !f. (!x y z. f x (f y z) = f y (f x z)) ==>
                           !s x b. FINITE s /\ x NOTIN s ==> (ITSET f (x INSERT s) b = f x (ITSET f s b))

   Rework of ITSET Theorems:
   closure_comm_assoc_fun_def        |- !f s. closure_comm_assoc_fun f s <=>
                                        (!x y. x IN s /\ y IN s ==> f x y IN s) /\
                                         !x y z. x IN s /\ y IN s /\ z IN s ==> (f x (f y z) = f y (f x z))
   SUBSET_COMMUTING_ITSET_INSERT     |- !f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
                                        !x b::t. ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b)
   SUBSET_COMMUTING_ITSET_REDUCTION  |- !f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
                                        !x b::t. ITSET f s (f x b) = f x (ITSET f s b)
   SUBSET_COMMUTING_ITSET_RECURSES   |- !f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
                                        !x b::t. ITSET f (x INSERT s) b = f x (ITSET f (s DELETE x) b)

   SUM_IMAGE and PROD_IMAGE Theorems:
   SUM_IMAGE_EMPTY      |- !f. SIGMA f {} = 0
   SUM_IMAGE_INSERT     |- !f s. FINITE s ==> !e. e NOTIN s ==> (SIGMA f (e INSERT s) = f e + SIGMA f s)
   SUM_IMAGE_AS_SUM_SET |- !s. FINITE s ==> !f. (!x y. (f x = f y) ==> (x = y)) ==>
                               (SIGMA f s = SUM_SET (IMAGE f s))
   SIGMA_CONSTANT       |- !s. FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (SIGMA f s = k * CARD s)
   SUM_IMAGE_CONSTANT   |- !s. FINITE s ==> !c. SIGMA (K c) s = c * CARD s
   SIGMA_CARD_CONSTANT  |- !n s. FINITE s ==> (!e. e IN s ==> (CARD e = n)) ==> (SIGMA CARD s = n * CARD s)
   SIGMA_CARD_FACTOR    |- !n s. FINITE s ==> (!e. e IN s ==> n divides CARD e) ==> n divides SIGMA CARD s
   SIGMA_CONG           |- !s f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (SIGMA f1 s = SIGMA f2 s)
   CARD_AS_SIGMA        |- !s. FINITE s ==> (CARD s = SIGMA (\x. 1) s)
   CARD_EQ_SIGMA        |- !s. FINITE s ==> (CARD s = SIGMA (K 1) s)
   SIGMA_LE_SIGMA       |- !s. FINITE s ==> !f g. (!x. x IN s ==> f x <= g x) ==> SIGMA f s <= SIGMA g s
   SUM_IMAGE_UNION_EQN  |- !s t. FINITE s /\ FINITE t ==>
                           !f. SIGMA f (s UNION t) + SIGMA f (s INTER t) = SIGMA f s + SIGMA f t
   SUM_IMAGE_DISJOINT   |- !s t. FINITE s /\ FINITE t /\ DISJOINT s t ==>
                           !f. SIGMA f (s UNION t) = SIGMA f s + SIGMA f t
   SUM_IMAGE_MONO_LT    |- !s. FINITE s /\ s <> {} ==>
                           !f g. (!x. x IN s ==> f x < g x) ==> SIGMA f s < SIGMA g s
   SUM_IMAGE_PSUBSET_LT |- !f s t. FINITE s /\ t PSUBSET s /\ (!x. x IN s ==> f x <> 0) ==>
                                   SIGMA f t < SIGMA f s

   PROD_IMAGE_EMPTY     |- !f. PI f {} = 1
   PROD_IMAGE_INSERT    |- !s. FINITE s ==> !f e. e NOTIN s ==> (PI f (e INSERT s) = f e * PI f s)
   PROD_IMAGE_DELETE    |- !s. FINITE s ==> !f e. 0 < f e ==>
                               (PI f (s DELETE e) = if e IN s then PI f s DIV f e else PI f s)
   PROD_IMAGE_CONG      |- !s f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s)
   PI_CONSTANT          |- !s. FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (PI f s = k ** CARD s)
   PROD_IMAGE_CONSTANT  |- !s. FINITE s ==> !c. PI (K c) s = c ** CARD s

   SUM_SET and PROD_SET Theorems:
   SUM_SET_INSERT       |- !s x. FINITE s /\ x NOTIN s ==> (SUM_SET (x INSERT s) = x + SUM_SET s)
   SUM_SET_IMAGE_EQN    |- !s. FINITE s ==> !f. INJ f s univ(:num) ==> (SUM_SET (IMAGE f s) = SIGMA f s)
   SUM_SET_COUNT        |- !n. SUM_SET (count n) = n * (n - 1) DIV 2

   PROD_SET_SING        |- !x. PROD_SET {x} = x
   PROD_SET_NONZERO     |- !s. FINITE s /\ 0 NOTIN s ==> 0 < PROD_SET s
   PROD_SET_LESS        |- !s. FINITE s /\ s <> {} /\ 0 NOTIN s ==>
                           !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s)
   PROD_SET_LESS_SUC    |- !s. FINITE s /\ s <> {} /\ 0 NOTIN s ==> PROD_SET s < PROD_SET (IMAGE SUC s)
   PROD_SET_DIVISORS    |- !s. FINITE s ==> !n x. x IN s /\ n divides x ==> n divides (PROD_SET s)
   PROD_SET_INSERT      |- !x s. FINITE s /\ x NOTIN s ==> (PROD_SET (x INSERT s) = x * PROD_SET s)
   PROD_SET_IMAGE_EQN   |- !s. FINITE s ==> !f. INJ f s univ(:num) ==> (PROD_SET (IMAGE f s) = PI f s)
   PROD_SET_IMAGE_EXP   |- !n. 1 < n ==> !m. PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** SUM_SET (count m)
   PROD_SET_ELEMENT_DIVIDES     |- !s x. FINITE s /\ x IN s ==> x divides PROD_SET s
   PROD_SET_LESS_EQ             |- !s. FINITE s ==> !f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
                                       (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s)
   PROD_SET_LE_CONSTANT         |- !s. FINITE s ==> !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s
   PROD_SET_PRODUCT_GE_CONSTANT |- !s. FINITE s ==> !n f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
                                       (!x. x IN s ==> n <= f x * g x) ==>
                                       n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s)
   PROD_SET_PRODUCT_BY_PARTITION |- !s. FINITE s ==>
                                    !u v. s =|= u # v ==> (PROD_SET s = PROD_SET u * PROD_SET v)

   Partition and Equivalent Class:
   equiv_class_element    |- !R s x y. y IN equiv_class R s x <=> y IN s /\ R x y
   equiv_class_eq         |- !R s x y. R equiv_on s /\ x IN s /\ y IN s ==>
                                       ((equiv_class R s x = equiv_class R s y) <=> R x y)
   equiv_on_subset        |- !R s t. R equiv_on s /\ t SUBSET s ==> R equiv_on t
   partition_on_empty     |- !R. partition R {} = {}
   partition_element      |- !R s t. t IN partition R s <=> ?x. x IN s /\ (t = equiv_class R s x)
   partition_elements     |- !R s. partition R s = IMAGE (\x. equiv_class R s x) s
   partition_as_image     |- !R s. partition R s = IMAGE (\x. equiv_class R s x) s
   partition_cong         |- !R1 R2 s1 s2. (R1 = R2) /\ (s1 = s2) ==> (partition R1 s1 = partition R2 s2)
   equal_partition_card   |- !R s n. FINITE s /\ R equiv_on s /\
                             (!e. e IN partition R s ==> (CARD e = n)) ==> (CARD s = n * CARD (partition R s))
   equal_partition_factor |- !R s n. FINITE s /\ R equiv_on s /\
                             (!e. e IN partition R s ==> CARD e = n) ==> n divides CARD s
   factor_partition_card  |- !R s n. FINITE s /\ R equiv_on s /\
                             (!e. e IN partition R s ==> n divides CARD e) ==> n divides CARD s

   pair_disjoint_subset        |- !s t. t SUBSET s /\ PAIR_DISJOINT s ==> PAIR_DISJOINT t
   disjoint_bigunion_add_fun   |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                  !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P)
   set_additive_card           |- SET_ADDITIVE CARD
   disjoint_bigunion_card      |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                  (CARD (BIGUNION P) = SIGMA CARD P)
   set_additive_sigma          |- !f. SET_ADDITIVE (SIGMA f)
   disjoint_bigunion_sigma     |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                  !f. SIGMA f (BIGUNION P) = SIGMA (SIGMA f) P
   set_add_fun_by_partition    |- !R s. R equiv_on s /\ FINITE s ==>
                                  !f. SET_ADDITIVE f ==> (f s = SIGMA f (partition R s))
   set_card_by_partition       |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
   set_sigma_by_partition      |- !R s. R equiv_on s /\ FINITE s ==>
                                  !f. SIGMA f s = SIGMA (SIGMA f) (partition R s)
   disjoint_bigunion_mult_fun  |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                  !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P)
   set_mult_fun_by_partition   |- !R s. R equiv_on s /\ FINITE s ==>
                                  !f. SET_MULTIPLICATIVE f ==> (f s = PI f (partition R s))
   sum_image_by_composition    |- !s. FINITE s ==> !g. INJ g s univ(:'a) ==>
                                  !f. SIGMA f (IMAGE g s) = SIGMA (f o g) s
   sum_image_by_permutation    |- !s. FINITE s ==> !g. g PERMUTES s ==> !f. SIGMA (f o g) s = SIGMA f s
   sum_image_by_composition_with_partial_inj
                               |- !s. FINITE s ==> !f. (f {} = 0) ==>
                     !g. (!t. FINITE t /\ (!x. x IN t ==> g x <> {}) ==> INJ g t univ(:'b -> bool)) ==>
                                    (SIGMA f (IMAGE g s) = SIGMA (f o g) s)
   sum_image_by_composition_without_inj
                               |- !s. FINITE s ==>
                         !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
                                    (SIGMA f (IMAGE g s) = SIGMA (f o g) s)

   Pre-image Theorems:
   preimage_def               |- !f s y. preimage f s y = {x | x IN s /\ (f x = y)}
   preimage_element           |- !f s x y. x IN preimage f s y <=> x IN s /\ (f x = y)
   in_preimage                |- !f s x y. x IN preimage f s y <=> x IN s /\ (f x = y)
   preimage_subset_of_domain  |- !f s y. preimage f s y SUBSET s
   preimage_property          |- !f s y x. x IN preimage f s y ==> (f x = y)
   preimage_of_image          |- !f s x. x IN s ==> x IN preimage f s (f x)
   preimage_choice_property   |- !f s y. y IN IMAGE f s ==>
                                 CHOICE (preimage f s y) IN s /\ (f (CHOICE (preimage f s y)) = y)
   preimage_inj               |- !f s. INJ f s univ(:'b) ==> !x. x IN s ==> (preimage f s (f x) = {x})
   preimage_inj_choice        |- !f s. INJ f s univ(:'b) ==> !x. x IN s ==> (CHOICE (preimage f s (f x)) = x)

   Set of Proper Subsets:
   IN_PPOW         |- !s e. e IN PPOW s ==> e PSUBSET s
   FINITE_PPOW     |- !s. FINITE s ==> FINITE (PPOW s)
   CARD_PPOW       |- !s. FINITE s ==> (CARD (PPOW s) = PRE (2 ** CARD s)
   CARD_PPOW_EQN   |- !s. FINITE s ==> (CARD (PPOW s) = 2 ** CARD s - 1)

   Useful Theorems:
   in_prime        |- !p. p IN prime <=> prime p
   PROD_SET_EUCLID |- !s. FINITE s ==> !p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b

*)

(* ------------------------------------------------------------------------- *)
(* Logic Theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (A <=> B) <=> (A ==> B) /\ ((A ==> B) ==> (B ==> A)) *)
(* Proof: by logic. *)
val EQ_IMP2_THM = store_thm(
  "EQ_IMP2_THM",
  ``!A B. (A <=> B) <=> (A ==> B) /\ ((A ==> B) ==> (B ==> A))``,
  metis_tac[]);

(* Theorem: (b1 = b2) ==> (f b1 = f b2) *)
(* Proof: by substitution. *)
val BOOL_EQ = store_thm(
  "BOOL_EQ",
  ``!b1:bool b2:bool f. (b1 = b2) ==> (f b1 = f b2)``,
  simp[]);

(* Theorem: b /\ (c ==> d) ==> ((b ==> c) ==> d) *)
(* Proof: by logical implication. *)
val IMP_IMP = store_thm(
  "IMP_IMP",
  ``!b c d. b /\ (c ==> d) ==> ((b ==> c) ==> d)``,
  metis_tac[]);

(* Theorem: p /\ q ==> p \/ ~q *)
(* Proof:
   Note p /\ q ==> p          by AND1_THM
    and p ==> p \/ ~q         by OR_INTRO_THM1
   Thus p /\ q ==> p \/ ~q
*)
val AND_IMP_OR_NEG = store_thm(
  "AND_IMP_OR_NEG",
  ``!p q. p /\ q ==> p \/ ~q``,
  metis_tac[]);

(* Theorem: (p \/ q ==> r) ==> (p /\ ~q ==> r) *)
(* Proof:
       (p \/ q) ==> r
     = ~(p \/ q) \/ r      by IMP_DISJ_THM
     = (~p /\ ~q) \/ r     by DE_MORGAN_THM
   ==> (~p \/ q) \/ r      by AND_IMP_OR_NEG
     = ~(p /\ ~q) \/ r     by DE_MORGAN_THM
     = (p /\ ~q) ==> r     by IMP_DISJ_THM
*)
val OR_IMP_IMP = store_thm(
  "OR_IMP_IMP",
  ``!p q r. ((p \/ q) ==> r) ==> ((p /\ ~q) ==> r)``,
  metis_tac[]);

(* Theorem: x IN (if b then s else t) <=> if b then x IN s else x IN t *)
(* Proof: by boolTheory.COND_RAND:
   |- !f b x y. f (if b then x else y) = if b then f x else f y
*)
val PUSH_IN_INTO_IF = store_thm(
  "PUSH_IN_INTO_IF",
  ``!b x s t. x IN (if b then s else t) <=> if b then x IN s else x IN t``,
  rw_tac std_ss[]);

(* ------------------------------------------------------------------------- *)
(* Set Theorems.                                                             *)
(* ------------------------------------------------------------------------- *)

(* use of IN_SUBSET *)
val IN_SUBSET = save_thm("IN_SUBSET", SUBSET_DEF);
(*
val IN_SUBSET = |- !s t. s SUBSET t <=> !x. x IN s ==> x IN t: thm
*)

(* Theorem: DISJOINT (s DIFF t) t /\ DISJOINT t (s DIFF t) *)
(* Proof:
       DISJOINT (s DIFF t) t
   <=> (s DIFF t) INTER t = {}              by DISJOINT_DEF
   <=> !x. x IN (s DIFF t) INTER t <=> F    by MEMBER_NOT_EMPTY
       x IN (s DIFF t) INTER t
   <=> x IN (s DIFF t) /\ x IN t            by IN_INTER
   <=> (x IN s /\ x NOTIN t) /\ x IN t      by IN_DIFF
   <=> x IN s /\ (x NOTIN t /\ x IN t)
   <=> x IN s /\ F
   <=> F
   Similarly for DISJOINT t (s DIFF t)
*)
val DISJOINT_DIFF = store_thm(
  "DISJOINT_DIFF",
  ``!s t. (DISJOINT (s DIFF t) t) /\ (DISJOINT t (s DIFF t))``,
  (rw[DISJOINT_DEF, EXTENSION] >> metis_tac[]));

(* Theorem: DISJOINT s t <=> ((s DIFF t) = s) *)
(* Proof: by DISJOINT_DEF, DIFF_DEF, EXTENSION *)
val DISJOINT_DIFF_IFF = store_thm(
  "DISJOINT_DIFF_IFF",
  ``!s t. DISJOINT s t <=> ((s DIFF t) = s)``,
  rw[DISJOINT_DEF, DIFF_DEF, EXTENSION] >>
  metis_tac[]);

(* Theorem: s UNION (t DIFF s) = s UNION t *)
(* Proof:
   By EXTENSION,
     x IN (s UNION (t DIFF s))
   = x IN s \/ x IN (t DIFF s)                    by IN_UNION
   = x IN s \/ (x IN t /\ x NOTIN s)              by IN_DIFF
   = (x IN s \/ x IN t) /\ (x IN s \/ x NOTIN s)  by LEFT_OR_OVER_AND
   = (x IN s \/ x IN t) /\ T                      by EXCLUDED_MIDDLE
   = x IN (s UNION t)                             by IN_UNION
*)
val UNION_DIFF_EQ_UNION = store_thm(
  "UNION_DIFF_EQ_UNION",
  ``!s t. s UNION (t DIFF s) = s UNION t``,
  rw_tac std_ss[EXTENSION, IN_UNION, IN_DIFF] >>
  metis_tac[]);

(* Theorem: (s INTER (t DIFF s) = {}) /\ ((t DIFF s) INTER s = {}) *)
(* Proof: by DISJOINT_DIFF, GSYM DISJOINT_DEF *)
val INTER_DIFF = store_thm(
  "INTER_DIFF",
  ``!s t. (s INTER (t DIFF s) = {}) /\ ((t DIFF s) INTER s = {})``,
  rw[DISJOINT_DIFF, GSYM DISJOINT_DEF]);

(* Theorem: P <> {} /\ (!Y. Y IN P ==> Y SUBSET X) ==> (BIGINTER P) SUBSET X *)
(* Proof:
   Since P <> {}, let s IN P           by MEMBER_NOT_EMPTY
   Since s IN P, s SUBSET X            by given
   Now, x IN BIGINTER P
    <=> !Y. Y IN P ==> x IN Y          by IN_BIGINTER
   Since s IN P, x IN s
   Since s SUBSET X, x IN X            by IN_SUBSET
   Therefore (BIGINTER P) SUBSET X     by IN_SUBSET
*)
val BIGINTER_SUBSET = store_thm(
  "BIGINTER_SUBSET",
  ``!P X. P <> {} /\ (!Y. Y IN P ==> Y SUBSET X) ==> (BIGINTER P) SUBSET X``,
  rw[SUBSET_DEF] >>
  metis_tac[MEMBER_NOT_EMPTY]);

(* Theorem: {x} SUBSET s /\ SING s <=> (s = {x}) *)
(* Proof:
   Note {x} SUBSET s ==> x IN s           by SUBSET_DEF
    and SING s ==> ?y. s = {y}            by SING_DEF
   Thus x IN {y} ==> x = y                by IN_SING
*)
val SUBSET_SING = store_thm(
  "SUBSET_SING",
  ``!s x. {x} SUBSET s /\ SING s <=> (s = {x})``,
  metis_tac[SING_DEF, IN_SING, SUBSET_DEF]);

(* Theorem: !x. x IN s ==> s INTER {x} = {x} *)
(* Proof:
     s INTER {x}
   = {x | x IN s /\ x IN {x}}   by INTER_DEF
   = {x' | x' IN s /\ x' = x}   by IN_SING
   = {x}                        by EXTENSION
*)
val INTER_SING = store_thm(
  "INTER_SING",
  ``!s x. x IN s ==> (s INTER {x} = {x})``,
  rw[INTER_DEF, EXTENSION, EQ_IMP_THM]);

(* Theorem: A non-empty set with all elements equal to a is the singleton {a} *)
(* Proof: by singleton definition. *)
val ONE_ELEMENT_SING = store_thm(
  "ONE_ELEMENT_SING",
  ``!s a. s <> {} /\ (!k. k IN s ==> (k = a)) ==> (s = {a})``,
  rw[EXTENSION, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: s <> {} ==> (SING s <=> !x y. x IN s /\ y IN s ==> (x = y)) *)
(* Proof:
   If part: SING s ==> !x y. x IN s /\ y IN s ==> (x = y))
      SING s ==> ?t. s = {t}    by SING_DEF
      x IN s ==> x = t          by IN_SING
      y IN s ==> y = t          by IN_SING
      Hence x = y
   Only-if part: !x y. x IN s /\ y IN s ==> (x = y)) ==> SING s
     True by ONE_ELEMENT_SING
*)
val SING_ONE_ELEMENT = store_thm(
  "SING_ONE_ELEMENT",
  ``!s. s <> {} ==> (SING s <=> !x y. x IN s /\ y IN s ==> (x = y))``,
  metis_tac[SING_DEF, IN_SING, ONE_ELEMENT_SING]);

(* Theorem: SING s ==> (!x y. x IN s /\ y IN s ==> (x = y)) *)
(* Proof:
   Note SING s <=> ?z. s = {z}       by SING_DEF
    and x IN {z} <=> x = z           by IN_SING
    and y IN {z} <=> y = z           by IN_SING
   Thus x = y
*)
val SING_ELEMENT = store_thm(
  "SING_ELEMENT",
  ``!s. SING s ==> (!x y. x IN s /\ y IN s ==> (x = y))``,
  metis_tac[SING_DEF, IN_SING]);
(* Note: the converse really needs s <> {} *)

(* Theorem: SING s <=> s <> {} /\ (!x y. x IN s /\ y IN s ==> (x = y)) *)
(* Proof:
   If part: SING s ==> s <> {} /\ (!x y. x IN s /\ y IN s ==> (x = y))
      True by SING_EMPTY, SING_ELEMENT.
   Only-if part:  s <> {} /\ (!x y. x IN s /\ y IN s ==> (x = y)) ==> SING s
      True by SING_ONE_ELEMENT.
*)
val SING_TEST = store_thm(
  "SING_TEST",
  ``!s. SING s <=> s <> {} /\ (!x y. x IN s /\ y IN s ==> (x = y))``,
  metis_tac[SING_EMPTY, SING_ELEMENT, SING_ONE_ELEMENT]);

(* Theorem: x IN (if b then {y} else {}) ==> (x = y) *)
(* Proof: by IN_SING, MEMBER_NOT_EMPTY *)
val IN_SING_OR_EMPTY = store_thm(
  "IN_SING_OR_EMPTY",
  ``!b x y. x IN (if b then {y} else {}) ==> (x = y)``,
  rw[]);

(* Theorem: {x} INTER s = if x IN s then {x} else {} *)
(* Proof: by EXTENSION *)
val SING_INTER = store_thm(
  "SING_INTER",
  ``!s x. {x} INTER s = if x IN s then {x} else {}``,
  rw[EXTENSION] >>
  metis_tac[]);

(* Theorem: SING s ==> (CARD s = 1) *)
(* Proof:
   Note s = {x} for some x   by SING_DEF
     so CARD s = 1           by CARD_SING
*)
Theorem SING_CARD_1:
  !s. SING s ==> (CARD s = 1)
Proof
  metis_tac[SING_DEF, CARD_SING]
QED

(* Note: SING s <=> (CARD s = 1) cannot be proved.
Only SING_IFF_CARD1  |- !s. SING s <=> (CARD s = 1) /\ FINITE s
That is: FINITE s /\ (CARD s = 1) ==> SING s
*)

(* Theorem: FINITE s ==> ((CARD s = 1) <=> SING s) *)
(* Proof:
   If part: CARD s = 1 ==> SING s
      Since CARD s = 1
        ==> s <> {}        by CARD_EMPTY
        ==> ?x. x IN s     by MEMBER_NOT_EMPTY
      Claim: !y . y IN s ==> y = x
      Proof: By contradiction, suppose y <> x.
             Then y NOTIN {x}             by EXTENSION
               so CARD {y; x} = 2         by CARD_DEF
              and {y; x} SUBSET s         by SUBSET_DEF
             thus CARD {y; x} <= CARD s   by CARD_SUBSET
             This contradicts CARD s = 1.
      Hence SING s         by SING_ONE_ELEMENT (or EXTENSION, SING_DEF)
      Or,
      With x IN s, {x} SUBSET s         by SUBSET_DEF
      If s <> {x}, then {x} PSUBSET s   by PSUBSET_DEF
      so CARD {x} < CARD s              by CARD_PSUBSET
      But CARD {x} = 1                  by CARD_SING
      and this contradicts CARD s = 1.

   Only-if part: SING s ==> CARD s = 1
      Since SING s
        <=> ?x. s = {x}    by SING_DEF
        ==> CARD {x} = 1   by CARD_SING
*)
val CARD_EQ_1 = store_thm(
  "CARD_EQ_1",
  ``!s. FINITE s ==> ((CARD s = 1) <=> SING s)``,
  rw[SING_DEF, EQ_IMP_THM] >| [
    `1 <> 0` by decide_tac >>
    `s <> {} /\ ?x. x IN s` by metis_tac[CARD_EMPTY, MEMBER_NOT_EMPTY] >>
    qexists_tac `x` >>
    spose_not_then strip_assume_tac >>
    `{x} PSUBSET s` by rw[PSUBSET_DEF] >>
    `CARD {x} < CARD s` by rw[CARD_PSUBSET] >>
    `CARD {x} = 1` by rw[CARD_SING] >>
    decide_tac,
    rw[CARD_SING]
  ]);

(* Theorem: x <> y ==> ((x INSERT s) DELETE y = x INSERT (s DELETE y)) *)
(* Proof:
       z IN (x INSERT s) DELETE y
   <=> z IN (x INSERT s) /\ z <> y                by IN_DELETE
   <=> (z = x \/ z IN s) /\ z <> y                by IN_INSERT
   <=> (z = x /\ z <> y) \/ (z IN s /\ z <> y)    by RIGHT_AND_OVER_OR
   <=> (z = x) \/ (z IN s /\ z <> y)              by x <> y
   <=> (z = x) \/ (z IN DELETE y)                 by IN_DELETE
   <=> z IN  x INSERT (s DELETE y)                by IN_INSERT
*)
val INSERT_DELETE_COMM = store_thm(
  "INSERT_DELETE_COMM",
  ``!s x y. x <> y ==> ((x INSERT s) DELETE y = x INSERT (s DELETE y))``,
  (rw[EXTENSION] >> metis_tac[]));

(* Theorem: s SUBSET u ==> (s INTER t) SUBSET u *)
(* Proof:
   Note (s INTER t) SUBSET s     by INTER_SUBSET
    ==> (s INTER t) SUBSET u     by SUBSET_TRANS
*)
val SUBSET_INTER_SUBSET = store_thm(
  "SUBSET_INTER_SUBSET",
  ``!s t u. s SUBSET u ==> (s INTER t) SUBSET u``,
  metis_tac[INTER_SUBSET, SUBSET_TRANS]);

(* Theorem: s DIFF (s DIFF t) = s INTER t *)
(* Proof: by IN_DIFF, IN_INTER *)
val DIFF_DIFF_EQ_INTER = store_thm(
  "DIFF_DIFF_EQ_INTER",
  ``!s t. s DIFF (s DIFF t) = s INTER t``,
  rw[EXTENSION] >>
  metis_tac[]);

(* Theorem: (s = t) <=> (s SUBSET t /\ (t DIFF s = {})) *)
(* Proof:
       s = t
   <=> s SUBSET t /\ t SUBSET s       by SET_EQ_SUBSET
   <=> s SUBSET t /\ (t DIFF s = {})  by SUBSET_DIFF_EMPTY
*)
val SET_EQ_BY_DIFF = store_thm(
  "SET_EQ_BY_DIFF",
  ``!s t. (s = t) <=> (s SUBSET t /\ (t DIFF s = {}))``,
  rw[SET_EQ_SUBSET, SUBSET_DIFF_EMPTY]);

(* Theorem: s SUBSET t ==> !x. (x INSERT s) SUBSET (x INSERT t) *)
(* Proof: by SUBSET_DEF *)
val SUBSET_INSERT_SUBSET = store_thm(
  "SUBSET_INSERT_SUBSET",
  ``!s t. s SUBSET t ==> !x. (x INSERT s) SUBSET (x INSERT t)``,
  rw[SUBSET_DEF]);

(* Theorem: x NOTIN s /\ (x INSERT s) SUBSET t ==> s SUBSET (t DELETE x) *)
(* Proof: by SUBSET_DEF *)
val INSERT_SUBSET_SUBSET = store_thm(
  "INSERT_SUBSET_SUBSET",
  ``!s t x. x NOTIN s /\ (x INSERT s) SUBSET t ==> s SUBSET (t DELETE x)``,
  rw[SUBSET_DEF]);

(* DIFF_INSERT  |- !s t x. s DIFF (x INSERT t) = s DELETE x DIFF t *)

(* Theorem: (s DIFF t) DELETE x = s DIFF (x INSERT t) *)
(* Proof: by EXTENSION *)
val DIFF_DELETE = store_thm(
  "DIFF_DELETE",
  ``!s t x. (s DIFF t) DELETE x = s DIFF (x INSERT t)``,
  (rw[EXTENSION] >> metis_tac[]));

(* Theorem: FINITE a /\ b SUBSET a ==> (CARD (a DIFF b) = CARD a - CARD b) *)
(* Proof:
   Note FINITE b                   by SUBSET_FINITE
     so a INTER b = b              by SUBSET_INTER2
        CARD (a DIFF b)
      = CARD a - CARD (a INTER b)  by CARD_DIFF
      = CARD a - CARD b            by above
*)
Theorem SUBSET_DIFF_CARD:
  !a b. FINITE a /\ b SUBSET a ==> (CARD (a DIFF b) = CARD a - CARD b)
Proof
  metis_tac[CARD_DIFF, SUBSET_FINITE, SUBSET_INTER2]
QED

(* Theorem: s SUBSET {x} <=> ((s = {}) \/ (s = {x})) *)
(* Proof:
   Note !y. y IN s ==> y = x   by SUBSET_DEF, IN_SING
   If s = {}, then trivially true.
   If s <> {},
     then ?y. y IN s           by MEMBER_NOT_EMPTY, s <> {}
       so y = x                by above
      ==> s = {x}              by EXTENSION
*)
Theorem SUBSET_SING_IFF:
  !s x. s SUBSET {x} <=> ((s = {}) \/ (s = {x}))
Proof
  rw[SUBSET_DEF, EXTENSION] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Image and Bijection                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x. x IN s ==> (f x = g x)) ==> (INJ f s t <=> INJ g s t) *)
(* Proof: by INJ_DEF *)
val INJ_CONG = store_thm(
  "INJ_CONG",
  ``!f g s t. (!x. x IN s ==> (f x = g x)) ==> (INJ f s t <=> INJ g s t)``,
  rw[INJ_DEF]);

(* Theorem: (!x. x IN s ==> (f x = g x)) ==> (SURJ f s t <=> SURJ g s t) *)
(* Proof: by SURJ_DEF *)
val SURJ_CONG = store_thm(
  "SURJ_CONG",
  ``!f g s t. (!x. x IN s ==> (f x = g x)) ==> (SURJ f s t <=> SURJ g s t)``,
  rw[SURJ_DEF] >>
  metis_tac[]);

(* Theorem: (!x. x IN s ==> (f x = g x)) ==> (BIJ f s t <=> BIJ g s t) *)
(* Proof: by BIJ_DEF, INJ_CONG, SURJ_CONG *)
val BIJ_CONG = store_thm(
  "BIJ_CONG",
  ``!f g s t. (!x. x IN s ==> (f x = g x)) ==> (BIJ f s t <=> BIJ g s t)``,
  rw[BIJ_DEF] >>
  metis_tac[INJ_CONG, SURJ_CONG]);

(*
BIJ_LINV_BIJ |- !f s t. BIJ f s t ==> BIJ (LINV f s) t s
Cannot prove |- !f s t. BIJ f s t <=> BIJ (LINV f s) t s
because LINV f s depends on f!
*)

(* Theorem: INJ f s t /\ x IN s ==> f x IN t *)
(* Proof: by INJ_DEF *)
val INJ_ELEMENT = store_thm(
  "INJ_ELEMENT",
  ``!f s t x. INJ f s t /\ x IN s ==> f x IN t``,
  rw_tac std_ss[INJ_DEF]);

(* Theorem: SURJ f s t /\ x IN s ==> f x IN t *)
(* Proof: by SURJ_DEF *)
val SURJ_ELEMENT = store_thm(
  "SURJ_ELEMENT",
  ``!f s t x. SURJ f s t /\ x IN s ==> f x IN t``,
  rw_tac std_ss[SURJ_DEF]);

(* Theorem: BIJ f s t /\ x IN s ==> f x IN t *)
(* Proof: by BIJ_DEF *)
val BIJ_ELEMENT = store_thm(
  "BIJ_ELEMENT",
  ``!f s t x. BIJ f s t /\ x IN s ==> f x IN t``,
  rw_tac std_ss[BIJ_DEF, INJ_DEF]);

(* Theorem: INJ f s t ==> INJ f s UNIV *)
(* Proof:
   Note s SUBSET s                        by SUBSET_REFL
    and t SUBSET univ(:'b)                by SUBSET_UNIV
     so INJ f s t ==> INJ f s univ(:'b)   by INJ_SUBSET
*)
val INJ_UNIV = store_thm(
  "INJ_UNIV",
  ``!f s t. INJ f s t ==> INJ f s UNIV``,
  metis_tac[INJ_SUBSET, SUBSET_REFL, SUBSET_UNIV]);

(* Theorem: INJ f UNIV UNIV ==> INJ f s UNIV *)
(* Proof:
   Note s SUBSET univ(:'a)                               by SUBSET_UNIV
   and univ(:'b) SUBSET univ('b)                         by SUBSET_REFL
     so INJ f univ(:'a) univ(:'b) ==> INJ f s univ(:'b)  by INJ_SUBSET
*)
val INJ_SUBSET_UNIV = store_thm(
  "INJ_SUBSET_UNIV",
  ``!(f:'a -> 'b) (s:'a -> bool). INJ f UNIV UNIV ==> INJ f s UNIV``,
  metis_tac[INJ_SUBSET, SUBSET_UNIV, SUBSET_REFL]);

(* Theorem: INJ f s UNIV ==> BIJ f s (IMAGE f s) *)
(* Proof: by definitions. *)
val INJ_IMAGE_BIJ = store_thm(
  "INJ_IMAGE_BIJ",
  ``!f s. INJ f s UNIV ==> BIJ f s (IMAGE f s)``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: INJ f P univ(:'b) ==>
            !s t. s SUBSET P /\ t SUBSET P ==> ((IMAGE f s = IMAGE f t) <=> (s = t)) *)
(* Proof:
   If part: IMAGE f s = IMAGE f t ==> s = t
      Claim: s SUBSET t
      Proof: by SUBSET_DEF, this is to show: x IN s ==> x IN t
             x IN s
         ==> f x IN (IMAGE f s)            by INJ_DEF, IN_IMAGE
          or f x IN (IMAGE f t)            by given
         ==> ?x'. x' IN t /\ (f x' = f x)  by IN_IMAGE
         But x IN P /\ x' IN P             by SUBSET_DEF
        Thus f x' = f x ==> x' = x         by INJ_DEF

      Claim: t SUBSET s
      Proof: similar to above              by INJ_DEF, IN_IMAGE, SUBSET_DEF

       Hence s = t                         by SUBSET_ANTISYM

   Only-if part: s = t ==> IMAGE f s = IMAGE f t
      This is trivially true.
*)
val INJ_IMAGE_EQ = store_thm(
  "INJ_IMAGE_EQ",
  ``!P f. INJ f P univ(:'b) ==>
   !s t. s SUBSET P /\ t SUBSET P ==> ((IMAGE f s = IMAGE f t) <=> (s = t))``,
  rw[EQ_IMP_THM] >>
  (irule SUBSET_ANTISYM >> rpt conj_tac) >| [
    rw[SUBSET_DEF] >>
    `?x'. x' IN t /\ (f x' = f x)` by metis_tac[IMAGE_IN, IN_IMAGE] >>
    metis_tac[INJ_DEF, SUBSET_DEF],
    rw[SUBSET_DEF] >>
    `?x'. x' IN s /\ (f x' = f x)` by metis_tac[IMAGE_IN, IN_IMAGE] >>
    metis_tac[INJ_DEF, SUBSET_DEF]
  ]);

(* Note: pred_setTheory.IMAGE_INTER
|- !f s t. IMAGE f (s INTER t) SUBSET IMAGE f s INTER IMAGE f t
*)

(* Theorem: INJ f P univ(:'b) ==>
            !s t. s SUBSET P /\ t SUBSET P ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t)) *)
(* Proof: by EXTENSION, INJ_DEF, SUBSET_DEF *)
val INJ_IMAGE_INTER = store_thm(
  "INJ_IMAGE_INTER",
  ``!P f. INJ f P univ(:'b) ==>
   !s t. s SUBSET P /\ t SUBSET P ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))``,
  rw[EXTENSION] >>
  metis_tac[INJ_DEF, SUBSET_DEF]);

(* tobe: helperSet, change P to P *)

(* Theorem: INJ f P univ(:'b) ==>
            !s t. s SUBSET P /\ t SUBSET P ==> (DISJOINT s t <=> DISJOINT (IMAGE f s) (IMAGE f t)) *)
(* Proof:
       DISJOINT (IMAGE f s) (IMAGE f t)
   <=> (IMAGE f s) INTER (IMAGE f t) = {}     by DISJOINT_DEF
   <=>           IMAGE f (s INTER t) = {}     by INJ_IMAGE_INTER, INJ f P univ(:'b)
   <=>                    s INTER t  = {}     by IMAGE_EQ_EMPTY
   <=> DISJOINT s t                           by DISJOINT_DEF
*)
val INJ_IMAGE_DISJOINT = store_thm(
  "INJ_IMAGE_DISJOINT",
  ``!P f. INJ f P univ(:'b) ==>
   !s t. s SUBSET P /\ t SUBSET P ==> (DISJOINT s t <=> DISJOINT (IMAGE f s) (IMAGE f t))``,
  metis_tac[DISJOINT_DEF, INJ_IMAGE_INTER, IMAGE_EQ_EMPTY]);

(* Theorem: INJ I s univ(:'a) *)
(* Proof:
   Note !x. I x = x                                           by I_THM
     so !x. x IN s ==> I x IN univ(:'a)                       by IN_UNIV
    and !x y. x IN s /\ y IN s ==> (I x = I y) ==> (x = y)    by above
  Hence INJ I s univ(:'b)                                     by INJ_DEF
*)
val INJ_I = store_thm(
  "INJ_I",
  ``!s:'a -> bool. INJ I s univ(:'a)``,
  rw[INJ_DEF]);

(* Theorem: INJ I (IMAGE f s) univ(:'b) *)
(* Proof:
  Since !x. x IN (IMAGE f s) ==> x IN univ(:'b)          by IN_UNIV
    and !x y. x IN (IMAGE f s) /\ y IN (IMAGE f s) ==>
              (I x = I y) ==> (x = y)                    by I_THM
  Hence INJ I (IMAGE f s) univ(:'b)                      by INJ_DEF
*)
val INJ_I_IMAGE = store_thm(
  "INJ_I_IMAGE",
  ``!s f. INJ I (IMAGE f s) univ(:'b)``,
  rw[INJ_DEF]);

(* Theorem: BIJ f s t <=> (!x. x IN s ==> f x IN t) /\ (!y. y IN t ==> ?!x. x IN s /\ (f x = y)) *)
(* Proof:
   This is to prove:
   (1) y IN t ==> ?!x. x IN s /\ (f x = y)
       x exists by SURJ_DEF, and x is unique by INJ_DEF.
   (2) x IN s /\ y IN s /\ f x = f y ==> x = y
       true by INJ_DEF.
   (3) x IN t ==> ?y. y IN s /\ (f y = x)
       true by SURJ_DEF.
*)
val BIJ_ALT = store_thm(
  "BIJ_ALT",
  ``!f s t. BIJ f s t <=> (!x. x IN s ==> f x IN t) /\ (!y. y IN t ==> ?!x. x IN s /\ (f x = y))``,
  rw_tac std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >> metis_tac[]);

(* Theorem: BIJ f s t ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y) *)
(* Proof: by BIJ_DEF, INJ_DEF *)
Theorem BIJ_IS_INJ:
  !f s t. BIJ f s t ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)
Proof
  rw[BIJ_DEF, INJ_DEF]
QED

(* Theorem: INJ f s s /\ x IN s /\ y IN s ==> ((f x = f y) <=> (x = y)) *)
(* Proof: by INJ_DEF *)
Theorem INJ_EQ_11:
  !f s x y. INJ f s s /\ x IN s /\ y IN s ==> ((f x = f y) <=> (x = y))
Proof
  metis_tac[INJ_DEF]
QED

(* Theorem: BIJ I s s *)
(* Proof: by definitions. *)
val BIJ_I_SAME = store_thm(
  "BIJ_I_SAME",
  ``!s. BIJ I s s``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: IMAGE I s = s *)
(* Proof:
     IMAGE I s
   = {f x | x IN s}    by IMAGE_DEF
   = { x | x IN s}     by I_THM
   = s                 by EXTENSION
*)
val IMAGE_I = store_thm(
  "IMAGE_I",
  ``!s. IMAGE I s = s``,
  rw[IMAGE_DEF]);

(* export simple result *)
val _ = export_rewrites ["IMAGE_I"];

(* Theorem: s <> {} ==> !e. IMAGE (K e) s = {e} *)
(* Proof:
       IMAGE (K e) s
   <=> {(K e) x | x IN s}    by IMAGE_DEF
   <=> {e | x IN s}          by K_THM
   <=> {e}                   by EXTENSION, if s <> {}
*)
val IMAGE_K = store_thm(
  "IMAGE_K",
  ``!s. s <> {} ==> !e. IMAGE (K e) s = {e}``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: IMAGE f {x} = {f x} *)
(* Proof: by IN_IMAGE, IN_SING *)
val IMAGE_SING = store_thm(
  "IMAGE_SING",
  ``!f x. IMAGE f {x} = {f x}``,
  rw[]);

(* Theorem: (!x. x IN s ==> f x IN t) <=> (IMAGE f s) SUBSET t *)
(* Proof:
   If part: (!x. x IN s ==> f x IN t) ==> (IMAGE f s) SUBSET t
       y IN (IMAGE f s)
   ==> ?x. (y = f x) /\ x IN s   by IN_IMAGE
   ==> f x = y IN t              by given
   hence (IMAGE f s) SUBSET t    by SUBSET_DEF
   Only-if part: (IMAGE f s) SUBSET t ==>  (!x. x IN s ==> f x IN t)
       x IN s
   ==> f x IN (IMAGE f s)        by IN_IMAGE
   ==> f x IN t                  by SUBSET_DEF
*)
val IMAGE_SUBSET_TARGET = store_thm(
  "IMAGE_SUBSET_TARGET",
  ``!f s t. (!x. x IN s ==> f x IN t) <=> (IMAGE f s) SUBSET t``,
  metis_tac[IN_IMAGE, SUBSET_DEF]);

(* Theorem: (!x y. (f x = f y) ==> (x = y)) ==> (!s e. e IN s <=> f e IN IMAGE f s) *)
(* Proof:
   If part: e IN s ==> f e IN IMAGE f s
     True by IMAGE_IN.
   Only-if part: f e IN IMAGE f s ==> e IN s
     ?x. (f e = f x) /\ x IN s   by IN_IMAGE
     f e = f x ==> e = x         by given implication
     Hence x IN s
*)
val IMAGE_ELEMENT_CONDITION = store_thm(
  "IMAGE_ELEMENT_CONDITION",
  ``!f:'a -> 'b. (!x y. (f x = f y) ==> (x = y)) ==> (!s e. e IN s <=> f e IN IMAGE f s)``,
  rw[EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: BIGUNION (IMAGE (\x. {x}) s) = s *)
(* Proof:
       z IN BIGUNION (IMAGE (\x. {x}) s)
   <=> ?t. z IN t /\ t IN (IMAGE (\x. {x}) s)   by IN_BIGUNION
   <=> ?t. z IN t /\ (?y. y IN s /\ (t = {y}))  by IN_IMAGE
   <=> z IN {z} /\ (?y. y IN s /\ {z} = {y})    by picking t = {z}
   <=> T /\ z IN s                              by picking y = z, IN_SING
   Hence  BIGUNION (IMAGE (\x. {x}) s) = s      by EXTENSION
*)
val BIGUNION_ELEMENTS_SING = store_thm(
  "BIGUNION_ELEMENTS_SING",
  ``!s. BIGUNION (IMAGE (\x. {x}) s) = s``,
  rw[EXTENSION, EQ_IMP_THM] >-
  metis_tac[] >>
  qexists_tac `{x}` >>
  metis_tac[IN_SING]);

(* Theorem: s SUBSET t /\ INJ f t UNIV ==> (IMAGE f (t DIFF s) = (IMAGE f t) DIFF (IMAGE f s)) *)
(* Proof: by SUBSET_DEF, INJ_DEF, EXTENSION, IN_IMAGE, IN_DIFF *)
val IMAGE_INJ_SUBSET_DIFF = store_thm(
  "IMAGE_INJ_SUBSET_DIFF",
  ``!s t f. s SUBSET t /\ INJ f t UNIV ==> (IMAGE f (t DIFF s) = (IMAGE f t) DIFF (IMAGE f s))``,
  rw[SUBSET_DEF, INJ_DEF, EXTENSION] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* More Theorems and Sets for Counting                                       *)
(* ------------------------------------------------------------------------- *)

(* Have simple (count n) *)

(* Theorem: count 1 = {0} *)
(* Proof: rename COUNT_ZERO *)
val COUNT_0 = save_thm("COUNT_0", COUNT_ZERO);
(* val COUNT_0 = |- count 0 = {}: thm *)

(* Theorem: count 1 = {0} *)
(* Proof: by count_def, EXTENSION *)
val COUNT_1 = store_thm(
  "COUNT_1",
  ``count 1 = {0}``,
  rw[count_def, EXTENSION]);

(* Theorem: n NOTIN (count n) *)
(* Proof: by IN_COUNT *)
val COUNT_NOT_SELF = store_thm(
  "COUNT_NOT_SELF",
  ``!n. n NOTIN (count n)``,
  rw[]);

(* Theorem: (count n = {}) <=> (n = 0) *)
(* Proof:
   Since FINITE (count n)         by FINITE_COUNT
     and CARD (count n) = n       by CARD_COUNT
      so count n = {} <=> n = 0   by CARD_EQ_0
*)
val COUNT_EQ_EMPTY = store_thm(
  "COUNT_EQ_EMPTY",
  ``!n. (count n = {}) <=> (n = 0)``,
  metis_tac[FINITE_COUNT, CARD_COUNT, CARD_EQ_0]);

(* Theorem: m <= n ==> count m SUBSET count n *)
(* Proof: by LENGTH_TAKE_EQ *)
val COUNT_SUBSET = store_thm(
  "COUNT_SUBSET",
  ``!m n. m <= n ==> count m SUBSET count n``,
  rw[SUBSET_DEF]);

(* Theorem: count (SUC n) SUBSET t <=> count n SUBSET t /\ n IN t *)
(* Proof:
       count (SUC n) SUBSET t
   <=> (n INSERT count n) SUBSET t     by COUNT_SUC
   <=> n IN t /\ (count n) SUBSET t    by INSERT_SUBSET
   <=> (count n) SUBSET t /\ n IN t    by CONJ_COMM
*)
val COUNT_SUC_SUBSET = store_thm(
  "COUNT_SUC_SUBSET",
  ``!n t. count (SUC n) SUBSET t <=> count n SUBSET t /\ n IN t``,
  metis_tac[COUNT_SUC, INSERT_SUBSET]);

(* Theorem: t DIFF (count (SUC n)) = t DIFF (count n) DELETE n *)
(* Proof:
     t DIFF (count (SUC n))
   = t DIFF (n INSERT count n)    by COUNT_SUC
   = t DIFF (count n) DELETE n    by EXTENSION
*)
val DIFF_COUNT_SUC = store_thm(
  "DIFF_COUNT_SUC",
  ``!n t. t DIFF (count (SUC n)) = t DIFF (count n) DELETE n``,
  rw[EXTENSION, EQ_IMP_THM]);

(* COUNT_SUC  |- !n. count (SUC n) = n INSERT count n *)

(* Theorem: count (SUC n) = 0 INSERT (IMAGE SUC (count n)) *)
(* Proof: by EXTENSION *)
val COUNT_SUC_BY_SUC = store_thm(
  "COUNT_SUC_BY_SUC",
  ``!n. count (SUC n) = 0 INSERT (IMAGE SUC (count n))``,
  rw[EXTENSION, EQ_IMP_THM] >>
  (Cases_on `x` >> simp[]));

(* Theorem: IMAGE f (count (SUC n)) = (f n) INSERT IMAGE f (count n) *)
(* Proof:
     IMAGE f (count (SUC n))
   = IMAGE f (n INSERT (count n))    by COUNT_SUC
   = f n INSERT IMAGE f (count n)    by IMAGE_INSERT
*)
val IMAGE_COUNT_SUC = store_thm(
  "IMAGE_COUNT_SUC",
  ``!f n. IMAGE f (count (SUC n)) = (f n) INSERT IMAGE f (count n)``,
  rw[COUNT_SUC]);

(* Theorem: IMAGE f (count (SUC n)) = (f 0) INSERT IMAGE (f o SUC) (count n) *)
(* Proof:
     IMAGE f (count (SUC n))
   = IMAGE f (0 INSERT (IMAGE SUC (count n)))    by COUNT_SUC_BY_SUC
   = f 0 INSERT IMAGE f (IMAGE SUC (count n))    by IMAGE_INSERT
   = f 0 INSERT IMAGE (f o SUC) (count n)        by IMAGE_COMPOSE
*)
val IMAGE_COUNT_SUC_BY_SUC = store_thm(
  "IMAGE_COUNT_SUC_BY_SUC",
  ``!f n. IMAGE f (count (SUC n)) = (f 0) INSERT IMAGE (f o SUC) (count n)``,
  rw[COUNT_SUC_BY_SUC, IMAGE_COMPOSE]);

(* Introduce countFrom m n, the set {m, m + 1, m + 2, ...., m + n - 1} *)
val _ = overload_on("countFrom", ``\m n. IMAGE ($+ m) (count n)``);

(* Theorem: countFrom m 0 = {} *)
(* Proof:
     countFrom m 0
   = IMAGE ($+ m) (count 0)     by notation
   = IMAGE ($+ m) {}            by COUNT_0
   = {}                         by IMAGE_EMPTY
*)
val countFrom_0 = store_thm(
  "countFrom_0",
  ``!m. countFrom m 0 = {}``,
  rw[]);

(* Theorem: countFrom m (SUC n) = m INSERT countFrom (m + 1) n *)
(* Proof: by IMAGE_COUNT_SUC_BY_SUC *)
val countFrom_SUC = store_thm(
  "countFrom_SUC",
  ``!m n. !m n. countFrom m (SUC n) = m INSERT countFrom (m + 1) n``,
  rpt strip_tac >>
  `$+ m o SUC = $+ (m + 1)` by rw[FUN_EQ_THM] >>
  rw[IMAGE_COUNT_SUC_BY_SUC]);

(* Theorem: 0 < n ==> m IN countFrom m n *)
(* Proof: by IN_COUNT *)
val countFrom_first = store_thm(
  "countFrom_first",
  ``!m n. 0 < n ==> m IN countFrom m n``,
  rw[] >>
  metis_tac[ADD_0]);

(* Theorem: x < m ==> x NOTIN countFrom m n *)
(* Proof: by IN_COUNT *)
val countFrom_less = store_thm(
  "countFrom_less",
  ``!m n x. x < m ==> x NOTIN countFrom m n``,
  rw[]);

(* Theorem: count n = countFrom 0 n *)
(* Proof: by EXTENSION *)
val count_by_countFrom = store_thm(
  "count_by_countFrom",
  ``!n. count n = countFrom 0 n``,
  rw[EXTENSION]);

(* Theorem: count (SUC n) = 0 INSERT countFrom 1 n *)
(* Proof:
      count (SUC n)
   = 0 INSERT IMAGE SUC (count n)     by COUNT_SUC_BY_SUC
   = 0 INSERT IMAGE ($+ 1) (count n)  by FUN_EQ_THM
   = 0 INSERT countFrom 1 n           by notation
*)
val count_SUC_by_countFrom = store_thm(
  "count_SUC_by_countFrom",
  ``!n. count (SUC n) = 0 INSERT countFrom 1 n``,
  rpt strip_tac >>
  `SUC = $+ 1` by rw[FUN_EQ_THM] >>
  rw[COUNT_SUC_BY_SUC]);

(* Inclusion-Exclusion for two sets:

CARD_UNION
|- !s. FINITE s ==> !t. FINITE t ==>
       (CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t)
CARD_UNION_EQN
|- !s t. FINITE s /\ FINITE t ==>
         (CARD (s UNION t) = CARD s + CARD t - CARD (s INTER t))
CARD_UNION_DISJOINT
|- !s t. FINITE s /\ FINITE t /\ DISJOINT s t ==>
         (CARD (s UNION t) = CARD s + CARD t)
*)

(* Inclusion-Exclusion for three sets. *)

(* Theorem: FINITE a /\ FINITE b /\ FINITE c ==>
            (CARD (a UNION b UNION c) =
             CARD a + CARD b + CARD c + CARD (a INTER b INTER c) -
             CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c)) *)
(* Proof:
   Note FINITE (a UNION b)                            by FINITE_UNION
    and FINITE (a INTER c)                            by FINITE_INTER
    and FINITE (b INTER c)                            by FINITE_INTER
   Also (a INTER c) INTER (b INTER c)
       = a INTER b INTER c                            by EXTENSION
    and CARD (a INTER b) <= CARD a                    by CARD_INTER_LESS_EQ
    and CARD (a INTER b INTER c) <= CARD (b INTER c)  by CARD_INTER_LESS_EQ, INTER_COMM

        CARD (a UNION b UNION c)
      = CARD (a UNION b) + CARD c - CARD ((a UNION b) INTER c)
                                                      by CARD_UNION_EQN
      = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a UNION b) INTER c)          by CARD_UNION_EQN
      = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a INTER c) UNION (b INTER c))
                                                      by UNION_OVER_INTER
      = (CARD a + CARD b - CARD (a INTER b)) + CARD c -
        (CARD (a INTER c) + CARD (b INTER c) - CARD ((a INTER c) INTER (b INTER c)))
                                                      by CARD_UNION_EQN
      = CARD a + CARD b + CARD c - CARD (a INTER b) -
        (CARD (a INTER c) + CARD (b INTER c) - CARD (a INTER b INTER c))
                                                      by CARD (a INTER b) <= CARD a
      = CARD a + CARD b + CARD c - CARD (a INTER b) -
        (CARD (b INTER c) + CARD (a INTER c) - CARD (a INTER b INTER c))
                                                      by ADD_COMM
      = CARD a + CARD b + CARD c - CARD (a INTER b)
        + CARD (a INTER b INTER c) - CARD (b INTER c) - CARD (a INTER c)
                                                      by CARD (a INTER b INTER c) <= CARD (b INTER c)
      = CARD a + CARD b + CARD c + CARD (a INTER b INTER c)
        - CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c)
                                                      by arithmetic
*)
Theorem CARD_UNION_3_EQN:
  !a b c. FINITE a /\ FINITE b /\ FINITE c ==>
          (CARD (a UNION b UNION c) =
           CARD a + CARD b + CARD c + CARD (a INTER b INTER c) -
           CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c))
Proof
  rpt strip_tac >>
  `FINITE (a UNION b) /\ FINITE (a INTER c) /\ FINITE (b INTER c)` by rw[] >>
  (`(a INTER c) INTER (b INTER c) = a INTER b INTER c` by (rw[EXTENSION] >> metis_tac[])) >>
  `CARD (a INTER b) <= CARD a` by rw[CARD_INTER_LESS_EQ] >>
  `CARD (a INTER b INTER c) <= CARD (b INTER c)` by metis_tac[INTER_COMM, CARD_INTER_LESS_EQ] >>
  `CARD (a UNION b UNION c)
      = CARD (a UNION b) + CARD c - CARD ((a UNION b) INTER c)` by rw[CARD_UNION_EQN] >>
  `_ = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a UNION b) INTER c)` by rw[CARD_UNION_EQN] >>
  `_ = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a INTER c) UNION (b INTER c))` by fs[UNION_OVER_INTER, INTER_COMM] >>
  `_ = (CARD a + CARD b - CARD (a INTER b)) + CARD c -
        (CARD (a INTER c) + CARD (b INTER c) - CARD (a INTER b INTER c))` by metis_tac[CARD_UNION_EQN] >>
  decide_tac
QED

(* Simplification of the above result for 3 disjoint sets. *)

(* Theorem: FINITE a /\ FINITE b /\ FINITE c /\
            DISJOINT a b /\ DISJOINT b c /\ DISJOINT a c ==>
            (CARD (a UNION b UNION c) = CARD a + CARD b + CARD c) *)
(* Proof: by DISJOINT_DEF, CARD_UNION_3_EQN *)
Theorem CARD_UNION_3_DISJOINT:
  !a b c. FINITE a /\ FINITE b /\ FINITE c /\
           DISJOINT a b /\ DISJOINT b c /\ DISJOINT a c ==>
           (CARD (a UNION b UNION c) = CARD a + CARD b + CARD c)
Proof
  rw[DISJOINT_DEF] >>
  rw[CARD_UNION_3_EQN]
QED

(* ------------------------------------------------------------------------- *)
(* Maximum and Minimum of a Set                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s /\ MAX_SET s < n ==> !x. x IN s ==> x < n *)
(* Proof:
   Since x IN s, s <> {}     by MEMBER_NOT_EMPTY
   Hence x <= MAX_SET s      by MAX_SET_DEF
    Thus x < n               by LESS_EQ_LESS_TRANS
*)
val MAX_SET_LESS = store_thm(
  "MAX_SET_LESS",
  ``!s n. FINITE s /\ MAX_SET s < n ==> !x. x IN s ==> x < n``,
  metis_tac[MEMBER_NOT_EMPTY, MAX_SET_DEF, LESS_EQ_LESS_TRANS]);

(* Theorem: FINITE s /\ s <> {} ==> !x. x IN s /\ (!y. y IN s ==> y <= x) ==> (x = MAX_SET s) *)
(* Proof:
   Let m = MAX_SET s.
   Since m IN s /\ x <= m       by MAX_SET_DEF
     and m IN s ==> m <= x      by implication
   Hence x = m.
*)
val MAX_SET_TEST = store_thm(
  "MAX_SET_TEST",
  ``!s. FINITE s /\ s <> {} ==> !x. x IN s /\ (!y. y IN s ==> y <= x) ==> (x = MAX_SET s)``,
  rpt strip_tac >>
  qabbrev_tac `m = MAX_SET s` >>
  `m IN s /\ x <= m` by rw[MAX_SET_DEF, Abbr`m`] >>
  `m <= x` by rw[] >>
  decide_tac);

(* Theorem: s <> {} ==> !x. x IN s /\ (!y. y IN s ==> x <= y) ==> (x = MIN_SET s) *)
(* Proof:
   Let m = MIN_SET s.
   Since m IN s /\ m <= x     by MIN_SET_LEM
     and m IN s ==> x <= m    by implication
   Hence x = m.
*)
val MIN_SET_TEST = store_thm(
  "MIN_SET_TEST",
  ``!s. s <> {} ==> !x. x IN s /\ (!y. y IN s ==> x <= y) ==> (x = MIN_SET s)``,
  rpt strip_tac >>
  qabbrev_tac `m = MIN_SET s` >>
  `m IN s /\ m <= x` by rw[MIN_SET_LEM, Abbr`m`] >>
  `x <= m` by rw[] >>
  decide_tac);

(* Theorem: FINITE s /\ s <> {} ==> !x. x IN s ==> ((MAX_SET s = x) <=> (!y. y IN s ==> y <= x)) *)
(* Proof:
   Let m = MAX_SET s.
   If part: y IN s ==> y <= m, true  by MAX_SET_DEF
   Only-if part: !y. y IN s ==> y <= x ==> m = x
      Note m IN s /\ x <= m          by MAX_SET_DEF
       and m IN s ==> m <= x         by implication
   Hence x = m.
*)
Theorem MAX_SET_TEST_IFF:
  !s. FINITE s /\ s <> {} ==>
      !x. x IN s ==> ((MAX_SET s = x) <=> (!y. y IN s ==> y <= x))
Proof
  rpt strip_tac >>
  qabbrev_tac `m = MAX_SET s` >>
  rw[EQ_IMP_THM] >- rw[MAX_SET_DEF, Abbr‘m’] >>
  `m IN s /\ x <= m` by rw[MAX_SET_DEF, Abbr`m`] >>
  `m <= x` by rw[] >>
  decide_tac
QED

(* Theorem: s <> {} ==> !x. x IN s ==> ((MIN_SET s = x) <=> (!y. y IN s ==> x <= y)) *)
(* Proof:
   Let m = MIN_SET s.
   If part: y IN s ==> m <= y, true by  MIN_SET_LEM
   Only-if part: !y. y IN s ==> x <= y ==> m = x
      Note m IN s /\ m <= x     by MIN_SET_LEM
       and m IN s ==> x <= m    by implication
   Hence x = m.
*)
Theorem MIN_SET_TEST_IFF:
  !s. s <> {} ==> !x. x IN s ==> ((MIN_SET s = x) <=> (!y. y IN s ==> x <= y))
Proof
  rpt strip_tac >>
  qabbrev_tac `m = MIN_SET s` >>
  rw[EQ_IMP_THM] >- rw[MIN_SET_LEM, Abbr‘m’] >>
  `m IN s /\ m <= x` by rw[MIN_SET_LEM, Abbr`m`] >>
  `x <= m` by rw[] >> decide_tac
QED

(* Theorem: MAX_SET {} = 0 *)
(* Proof: by MAX_SET_REWRITES *)
val MAX_SET_EMPTY = save_thm("MAX_SET_EMPTY", MAX_SET_REWRITES |> CONJUNCT1);
(* val MAX_SET_EMPTY = |- MAX_SET {} = 0: thm *)

(* Theorem: MAX_SET {e} = e *)
(* Proof: by MAX_SET_REWRITES *)
val MAX_SET_SING = save_thm("MAX_SET_SING", MAX_SET_REWRITES |> CONJUNCT2 |> GEN_ALL);
(* val MAX_SET_SING = |- !e. MAX_SET {e} = e: thm *)

(* Theorem: FINITE s /\ s <> {} ==> MAX_SET s IN s *)
(* Proof: by MAX_SET_DEF *)
val MAX_SET_IN_SET = store_thm(
  "MAX_SET_IN_SET",
  ``!s. FINITE s /\ s <> {} ==> MAX_SET s IN s``,
  rw[MAX_SET_DEF]);

(* Theorem: FINITE s ==> !x. x IN s ==> x <= MAX_SET s *)
(* Proof: by in_max_set *)
val MAX_SET_PROPERTY = save_thm("MAX_SET_PROPERTY", in_max_set);
(* val MAX_SET_PROPERTY = |- !s. FINITE s ==> !x. x IN s ==> x <= MAX_SET s: thm *)

(* Note: MIN_SET {} is undefined. *)

(* Theorem: MIN_SET {e} = e *)
(* Proof: by MIN_SET_THM *)
val MIN_SET_SING = save_thm("MIN_SET_SING", MIN_SET_THM |> CONJUNCT1);
(* val MIN_SET_SING = |- !e. MIN_SET {e} = e: thm *)

(* Theorem: s <> {} ==> MIN_SET s IN s *)
(* Proof: by MIN_SET_LEM *)
val MIN_SET_IN_SET = save_thm("MIN_SET_IN_SET",
    MIN_SET_LEM |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* val MIN_SET_IN_SET = |- !s. s <> {} ==> MIN_SET s IN s: thm *)

(* Theorem: s <> {} ==> !x. x IN s ==> MIN_SET s <= x *)
(* Proof: by MIN_SET_LEM *)
val MIN_SET_PROPERTY = save_thm("MIN_SET_PROPERTY",
    MIN_SET_LEM |> SPEC_ALL |> UNDISCH |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* val MIN_SET_PROPERTY =|- !s. s <> {} ==> !x. x IN s ==> MIN_SET s <= x: thm *)


(* Theorem: FINITE s /\ s <> {} /\ s <> {MIN_SET s} ==> (MAX_SET (s DELETE (MIN_SET s)) = MAX_SET s) *)
(* Proof:
   Let m = MIN_SET s, t = s DELETE m.
    Then t SUBSET s              by DELETE_SUBSET
      so FINITE t                by SUBSET_FINITE]);
   Since m IN s                  by MIN_SET_IN_SET
      so t <> {}                 by DELETE_EQ_SING, s <> {m}
     ==> ?x. x IN t              by MEMBER_NOT_EMPTY
     and x IN s /\ x <> m        by IN_DELETE
    From x IN s ==> m <= x       by MIN_SET_PROPERTY
    With x <> m ==> m < x        by LESS_OR_EQ
    Also x <= MAX_SET s          by MAX_SET_PROPERTY
    Thus MAX_SET s <> m          since m < x <= MAX_SET s
     But MAX_SET s IN s          by MAX_SET_IN_SET
    Thus MAX_SET s IN t          by IN_DELETE
     Now !y. y IN t ==>
             y IN s              by SUBSET_DEF
          or y <= MAX_SET s      by MAX_SET_PROPERTY
   Hence MAX_SET s = MAX_SET t   by MAX_SET_TEST
*)
val MAX_SET_DELETE = store_thm(
  "MAX_SET_DELETE",
  ``!s. FINITE s /\ s <> {} /\ s <> {MIN_SET s} ==> (MAX_SET (s DELETE (MIN_SET s)) = MAX_SET s)``,
  rpt strip_tac >>
  qabbrev_tac `m = MIN_SET s` >>
  qabbrev_tac `t = s DELETE m` >>
  `t SUBSET s` by rw[Abbr`t`] >>
  `FINITE t` by metis_tac[SUBSET_FINITE] >>
  `t <> {}` by metis_tac[MIN_SET_IN_SET, DELETE_EQ_SING] >>
  `?x. x IN t /\ x IN s /\ x <> m` by metis_tac[IN_DELETE, MEMBER_NOT_EMPTY] >>
  `m <= x` by rw[MIN_SET_PROPERTY, Abbr`m`] >>
  `m < x` by decide_tac >>
  `x <= MAX_SET s` by rw[MAX_SET_PROPERTY] >>
  `MAX_SET s <> m` by decide_tac >>
  `MAX_SET s IN t` by rw[MAX_SET_IN_SET, Abbr`t`] >>
  metis_tac[SUBSET_DEF, MAX_SET_PROPERTY, MAX_SET_TEST]);

(* Theorem: FINITE s ==> ((MAX_SET s = 0) <=> (s = {}) \/ (s = {0})) *)
(* Proof:
   If part: MAX_SET s = 0 ==> (s = {}) \/ (s = {0})
      By contradiction, suppose s <> {} /\ s <> {0}.
      Then ?x. x IN s /\ x <> 0      by ONE_ELEMENT_SING
      Thus x <= MAX_SET s            by in_max_set
        so MAX_SET s <> 0            by x <> 0
      This contradicts MAX_SET s = 0.
   Only-if part: (s = {}) \/ (s = {0}) ==> MAX_SET s = 0
      If s = {}, MAX_SET s = 0       by MAX_SET_EMPTY
      If s = {0}, MAX_SET s = 0      by MAX_SET_SING
*)
val MAX_SET_EQ_0 = store_thm(
  "MAX_SET_EQ_0",
  ``!s. FINITE s ==> ((MAX_SET s = 0) <=> (s = {}) \/ (s = {0}))``,
  (rw[EQ_IMP_THM] >> simp[]) >>
  CCONTR_TAC >>
  `s <> {} /\ s <> {0}` by metis_tac[] >>
  `?x. x IN s /\ x <> 0` by metis_tac[ONE_ELEMENT_SING] >>
  `x <= MAX_SET s` by rw[in_max_set] >>
  decide_tac);

(* Theorem: s <> {} ==> ((MIN_SET s = 0) <=> 0 IN s) *)
(* Proof:
   If part: MIN_SET s = 0 ==> 0 IN s
      This is true by MIN_SET_IN_SET.
   Only-if part: 0 IN s ==> MIN_SET s = 0
      Note MIN_SET s <= 0   by MIN_SET_LEM, 0 IN s
      Thus MIN_SET s = 0    by arithmetic
*)
val MIN_SET_EQ_0 = store_thm(
  "MIN_SET_EQ_0",
  ``!s. s <> {} ==> ((MIN_SET s = 0) <=> 0 IN s)``,
  rw[EQ_IMP_THM] >-
  metis_tac[MIN_SET_IN_SET] >>
  `MIN_SET s <= 0` by rw[MIN_SET_LEM] >>
  decide_tac);

(* Theorem: MAX_SET (IMAGE SUC (count n)) = n *)
(* Proof:
   By induction on n.
   Base case: MAX_SET (IMAGE SUC (count 0)) = 0
      LHS = MAX_SET (IMAGE SUC (count 0))
          = MAX_SET (IMAGE SUC {})       by COUNT_ZERO
          = MAX_SET {}                   by IMAGE_EMPTY
          = 0                            by MAX_SET_THM
          = RHS
   Step case: MAX_SET (IMAGE SUC (count n)) = n ==>
              MAX_SET (IMAGE SUC (count (SUC n))) = SUC n
      LHS = MAX_SET (IMAGE SUC (count (SUC n)))
          = MAX_SET (IMAGE SUC (n INSERT count n))           by COUNT_SUC
          = MAX_SET ((SUC n) INSERT (IMAGE SUC (count n)))   by IMAGE_INSERT
          = MAX (SUC n) (MAX_SET (IMAGE SUC (count n)))      by MAX_SET_THM
          = MAX (SUC n) n                                    by induction hypothesis
          = SUC n                                            by LESS_SUC, MAX_DEF
          = RHS
*)
val MAX_SET_IMAGE_SUC_COUNT = store_thm(
  "MAX_SET_IMAGE_SUC_COUNT",
  ``!n. MAX_SET (IMAGE SUC (count n)) = n``,
  Induct_on `n` >-
  rw[] >>
  `MAX_SET (IMAGE SUC (count (SUC n))) = MAX_SET (IMAGE SUC (n INSERT count n))` by rw[COUNT_SUC] >>
  `_ = MAX_SET ((SUC n) INSERT (IMAGE SUC (count n)))` by rw[] >>
  `_ = MAX (SUC n) (MAX_SET (IMAGE SUC (count n)))` by rw[MAX_SET_THM] >>
  `_ = MAX (SUC n) n` by rw[] >>
  `_ = SUC n` by metis_tac[LESS_SUC, MAX_DEF, MAX_COMM] >>
  rw[]);

(* Another Proof: *)
(* Theorem: MAX_SET (IMAGE SUC (count n)) = n *)
(* Proof:
   By induction on n.
   Base case: MAX_SET (IMAGE SUC (count 0)) = 0
      LHS = MAX_SET (IMAGE SUC (count 0))
          = MAX_SET (IMAGE SUC {})         by COUNT_ZERO
          = MAX_SET {}                     by IMAGE_EMPTY
          = 0                              by MAX_SET_DEF
          = RHS
   Step case: MAX_SET (IMAGE SUC (count n)) = n ==>
              MAX_SET (IMAGE SUC (count (SUC n))) = SUC n
      Note: FINITE (IMAGE SUC (count n))                    by FINITE_COUNT, IMAGE_FINITE
      LHS = MAX_SET (IMAGE SUC (count (SUC n)))
          = MAX_SET (IMAGE SUC (n INSERT (count n)))        by COUNT_SUC
          = MAX_SET ((SUC n) INSERT (IMAGE SUC (count n)))  by IMAGE_INSERT
          = MAX (SUC n) (MAX_SET (IMAGE SUC (count n)))     by MAX_SET_THM
          = MAX (SUC n) n                                   by induction hypothesis
          = SUC n                                           by LESS_SUC, MAX_DEF
          = RHS
*)
val MAX_SET_IMAGE_SUC_COUNT = store_thm(
  "MAX_SET_IMAGE_SUC_COUNT",
  ``!n. MAX_SET (IMAGE SUC (count n)) = n``,
  Induct_on `n` >-
  rw[MAX_SET_DEF] >>
  `MAX_SET (IMAGE SUC (count (SUC n))) = MAX (SUC n) (MAX_SET (IMAGE SUC (count n)))` by rw[COUNT_SUC, MAX_SET_THM] >>
  metis_tac[MAX_SET_THM, LESS_SUC, MAX_DEF, MAX_COMM, FINITE_COUNT, IMAGE_FINITE]);

(* Theorem: HALF x <= c ==> f x <= MAX_SET {f x | HALF x <= c} *)
(* Proof:
   Let s = {f x | HALF x <= c}
   Note !x. HALF x <= c
    ==> SUC (2 * HALF x) <= SUC (2 * c)         by arithmetic
    and x <= SUC (2 * HALF x)                   by TWO_HALF_LESS_EQ
     so x <= SUC (2 * c) < 2 * c + 2            by arithmetic
   Thus s SUBSET (IMAGE f (count (2 * c + 2)))  by SUBSET_DEF
   Note FINITE (count (2 * c + 2))              by FINITE_COUNT
     so FINITE s                                by IMAGE_FINITE, SUBSET_FINITE
    and f x IN s                                by HALF x <= c
   Thus f x <= MAX_SET s                        by MAX_SET_PROPERTY
*)
val MAX_SET_IMAGE_with_HALF = store_thm(
  "MAX_SET_IMAGE_with_HALF",
  ``!f c x. HALF x <= c ==> f x <= MAX_SET {f x | HALF x <= c}``,
  rpt strip_tac >>
  qabbrev_tac `s = {f x | HALF x <= c}` >>
  `s SUBSET (IMAGE f (count (2 * c + 2)))` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `SUC (2 * HALF x'') <= SUC (2 * c)` by rw[] >>
  `x'' <= SUC (2 * HALF x'')` by rw[TWO_HALF_LESS_EQ] >>
  `x'' < 2 * c + 2` by decide_tac >>
  metis_tac[]) >>
  `FINITE s` by metis_tac[FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  (`f x IN s` by (rw[Abbr`s`] >> metis_tac[])) >>
  rw[MAX_SET_PROPERTY]);

(*
Note: A more general version, replacing HALF x by g x, would be desirable.
However, there is no way to show FINITE s for arbitrary g x.
*)

(* Theorem: 0 < b /\ x DIV b <= c ==> f x <= MAX_SET {f x | x DIV b <= c} *)
(* Proof:
   Let s = {f x | x DIV b <= c}.
   Note !x. x DIV b <= c
    ==> b * SUC (x DIV b) <= b * SUC c          by arithmetic
    and x < b * SUC (x DIV b)                   by DIV_MULT_LESS_EQ, 0 < b
     so x < b * SUC c                           by arithmetic
   Thus s SUBSET (IMAGE f (count (b * SUC c)))  by SUBSET_DEF
   Note FINITE (count (b * SUC c))              by FINITE_COUNT
     so FINITE s                                by IMAGE_FINITE, SUBSET_FINITE
    and f x IN s                                by HALF x <= c
   Thus f x <= MAX_SET s                        by MAX_SET_PROPERTY
*)
val MAX_SET_IMAGE_with_DIV = store_thm(
  "MAX_SET_IMAGE_with_DIV",
  ``!f b c x. 0 < b /\ x DIV b <= c ==> f x <= MAX_SET {f x | x DIV b <= c}``,
  rpt strip_tac >>
  qabbrev_tac `s = {f x | x DIV b <= c}` >>
  `s SUBSET (IMAGE f (count (b * SUC c)))` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `b * SUC (x'' DIV b) <= b * SUC c` by rw[] >>
  `x'' < b * SUC (x'' DIV b)` by rw[DIV_MULT_LESS_EQ] >>
  `x'' < b * SUC c` by decide_tac >>
  metis_tac[]) >>
  `FINITE s` by metis_tac[FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  (`f x IN s` by (rw[Abbr`s`] >> metis_tac[])) >>
  rw[MAX_SET_PROPERTY]);

(* Theorem: x - b <= c ==> f x <= MAX_SET {f x | x - b <= c} *)
(* Proof:
   Let s = {f x | x - b <= c}
   Note !x. x - b <= c ==> x <= b + c           by arithmetic
     so x <= 1 + b + c                          by arithmetic
   Thus s SUBSET (IMAGE f (count (1 + b + c)))  by SUBSET_DEF
   Note FINITE (count (1 + b + c))              by FINITE_COUNT
     so FINITE s                                by IMAGE_FINITE, SUBSET_FINITE
    and f x IN s                                by x - b <= c
   Thus f x <= MAX_SET s                        by MAX_SET_PROPERTY
*)
val MAX_SET_IMAGE_with_DEC = store_thm(
  "MAX_SET_IMAGE_with_DEC",
  ``!f b c x. x - b <= c ==> f x <= MAX_SET {f x | x - b <= c}``,
  rpt strip_tac >>
  qabbrev_tac `s = {f x | x - b <= c}` >>
  `s SUBSET (IMAGE f (count (1 + b + c)))` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `x'' < b + (c + 1)` by decide_tac >>
  metis_tac[]) >>
  `FINITE s` by metis_tac[FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  `f x IN s` by
    (rw[Abbr`s`] >>
  `x <= b + c` by decide_tac >>
  metis_tac[]) >>
  rw[MAX_SET_PROPERTY]);

(* ------------------------------------------------------------------------- *)
(* Finite and Cardinality Theorems                                           *)
(* ------------------------------------------------------------------------- *)


(* Theorem: INJ f s UNIV /\ FINITE s ==> CARD (IMAGE f s) = CARD s *)
(* Proof:
   !x y. x IN s /\ y IN s /\ f x = f y == x = y   by INJ_DEF
   FINITE s ==> FINITE (IMAGE f s)                by IMAGE_FINITE
   Therefore   BIJ f s (IMAGE f s)                by BIJ_DEF, INJ_DEF, SURJ_DEF
   Hence       CARD (IMAGE f s) = CARD s          by FINITE_BIJ_CARD_EQ
*)
val INJ_CARD_IMAGE_EQN = store_thm(
  "INJ_CARD_IMAGE_EQN",
  ``!f s. INJ f s UNIV /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)``,
  rw[INJ_DEF] >>
  `FINITE (IMAGE f s)` by rw[IMAGE_FINITE] >>
  `BIJ f s (IMAGE f s)` by rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  metis_tac[FINITE_BIJ_CARD_EQ]);


(* Theorem: FINTIE s /\ FINITE t /\ CARD s = CARD t /\ INJ f s t ==> SURJ f s t *)
(* Proof:
   For any map f from s to t,
   (IMAGE f s) SUBSET t            by IMAGE_SUBSET_TARGET
   FINITE s ==> FINITE (IMAGE f s) by IMAGE_FINITE
   CARD (IMAGE f s) = CARD s       by INJ_CARD_IMAGE
                    = CARD t       by given
   Hence (IMAGE f s) = t           by SUBSET_EQ_CARD, FINITE t
   or SURJ f s t                   by IMAGE_SURJ
*)
val FINITE_INJ_AS_SURJ = store_thm(
  "FINITE_INJ_AS_SURJ",
  ``!f s t. INJ f s t /\ FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> SURJ f s t``,
  rw[INJ_DEF] >>
  `(IMAGE f s) SUBSET t` by rw[GSYM IMAGE_SUBSET_TARGET] >>
  `FINITE (IMAGE f s)` by rw[IMAGE_FINITE] >>
  `CARD (IMAGE f s) = CARD t` by metis_tac[INJ_DEF, INJ_CARD_IMAGE, INJ_SUBSET, SUBSET_REFL, SUBSET_UNIV] >>
  rw[SUBSET_EQ_CARD, IMAGE_SURJ]);

(* Theorem: FINITE {P x | x < n}  *)
(* Proof:
   Since IMAGE (\i. P i) (count n) = {P x | x < n},
   this follows by
   IMAGE_FINITE  |- !s. FINITE s ==> !f. FINITE (IMAGE f s) : thm
   FINITE_COUNT  |- !n. FINITE (count n) : thm
*)
val FINITE_COUNT_IMAGE = store_thm(
  "FINITE_COUNT_IMAGE",
  ``!P n. FINITE {P x | x < n }``,
  rpt strip_tac >>
  `IMAGE (\i. P i) (count n) = {P x | x < n}` by rw[IMAGE_DEF] >>
  metis_tac[IMAGE_FINITE, FINITE_COUNT]);

(* Note: no need for CARD_IMAGE:

CARD_INJ_IMAGE      |- !f s. (!x y. (f x = f y) <=> (x = y)) /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)
FINITE_BIJ_CARD_EQ  |- !S. FINITE S ==> !t f. BIJ f S t /\ FINITE t ==> (CARD S = CARD t)
BIJ_LINV_BIJ        |- !f s t. BIJ f s t ==> BIJ (LINV f s) t s
*)

(* Theorem: FINITE s /\ BIJ f s t ==> FINITE t /\ (CARD s = CARD t) *)
(* Proof:
   First, FINITE s /\ BIJ f s t ==> FINITE t
     BIJ f s t ==> SURJ f s t          by BIJ_DEF
               ==> IMAGE f s = t       by IMAGE_SURJ
     FINITE s  ==> FINITE (IMAGE f s)  by IMAGE_FINITE
     Hence FINITE t.
   Next, FINITE s /\ FINITE t /\ BIJ f s t ==> CARD s = CARD t
     by FINITE_BIJ_CARD_EQ.
*)
val FINITE_BIJ_PROPERTY = store_thm(
  "FINITE_BIJ_PROPERTY",
  ``!f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ (CARD s = CARD t)``,
  ntac 4 strip_tac >>
  CONJ_ASM1_TAC >| [
    `SURJ f s t` by metis_tac[BIJ_DEF] >>
    `IMAGE f s = t` by rw[GSYM IMAGE_SURJ] >>
    rw[],
    metis_tac[FINITE_BIJ_CARD_EQ]
  ]);

(* Note:
> pred_setTheory.CARD_IMAGE;
val it = |- !s. FINITE s ==> CARD (IMAGE f s) <= CARD s: thm
*)

(* Theorem: For a 1-1 map f: s -> s, s and (IMAGE f s) are of the same size. *)
(* Proof:
   By finite induction on the set s:
   Base case: CARD (IMAGE f {}) = CARD {}
     True by IMAGE f {} = {}     by IMAGE_EMPTY
   Step case: !s. FINITE s /\ (CARD (IMAGE f s) = CARD s) ==> !e. e NOTIN s ==> (CARD (IMAGE f (e INSERT s)) = CARD (e INSERT s))
       CARD (IMAGE f (e INSERT s))
     = CARD (f e INSERT IMAGE f s)      by IMAGE_INSERT
     = SUC (CARD (IMAGE f s))           by CARD_INSERT: e NOTIN s, f e NOTIN s, for 1-1 map
     = SUC (CARD s)                     by induction hypothesis
     = CARD (e INSERT s)                by CARD_INSERT: e NOTIN s.
*)
val FINITE_CARD_IMAGE = store_thm(
  "FINITE_CARD_IMAGE",
  ``!s f. (!x y. (f x = f y) <=> (x = y)) /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)``,
  `!f. (!x y. (f x = f y) <=> (x = y)) ==> !s. FINITE s ==> (CARD (IMAGE f s) = CARD s)` suffices_by rw[] >>
  gen_tac >>
  strip_tac >>
  ho_match_mp_tac FINITE_INDUCT >>
  rw[]);
(* Michael's proof *)
val FINITE_CARD_IMAGE = store_thm(
  "FINITE_CARD_IMAGE",
  ``!s f. (!x y. (f x = f y) <=> (x = y)) /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)``,
  qsuff_tac `!f. (!x y. (f x = f y) = (x = y)) ==> !s. FINITE s ==> (CARD (IMAGE f s) = CARD s)` >-
  metis_tac[] >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac FINITE_INDUCT >> rw[]);

(* Theorem: !s. FINITE s ==> CARD (IMAGE SUC s)) = CARD s *)
(* Proof:
   Since !n m. SUC n = SUC m <=> n = m    by numTheory.INV_SUC
   This is true by FINITE_CARD_IMAGE.
*)
val CARD_IMAGE_SUC = store_thm(
  "CARD_IMAGE_SUC",
  ``!s. FINITE s ==> (CARD (IMAGE SUC s) = CARD s)``,
  rw[FINITE_CARD_IMAGE]);

(* Theorem: FINITE s /\ FINITE t /\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t) *)
(* Proof: by CARD_UNION_EQN, DISJOINT_DEF, CARD_EMPTY *)
val CARD_UNION_DISJOINT = store_thm(
  "CARD_UNION_DISJOINT",
  ``!s t. FINITE s /\ FINITE t /\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t)``,
  rw_tac std_ss[CARD_UNION_EQN, DISJOINT_DEF, CARD_EMPTY]);

(* Theorem: !n. 0 < n ==> IMAGE (\x. x MOD n) s SUBSET (count n) *)
(* Proof: by SUBSET_DEF, MOD_LESS. *)
val image_mod_subset_count = store_thm(
  "image_mod_subset_count",
  ``!s n. 0 < n ==> IMAGE (\x. x MOD n) s SUBSET (count n)``,
  rw[SUBSET_DEF] >>
  rw[MOD_LESS]);

(* Theorem: !n. 0 < n ==> CARD (IMAGE (\x. x MOD n) s) <= n *)
(* Proof:
   Let t = IMAGE (\x. x MOD n) s
   Since   t SUBSET count n          by SUBSET_DEF, MOD_LESS
     Now   FINITE (count n)          by FINITE_COUNT
     and   CARD (count n) = n        by CARD_COUNT
      So   CARD t <= n               by CARD_SUBSET
*)
val card_mod_image = store_thm(
  "card_mod_image",
  ``!s n. 0 < n ==> CARD (IMAGE (\x. x MOD n) s) <= n``,
  rpt strip_tac >>
  qabbrev_tac `t = IMAGE (\x. x MOD n) s` >>
  (`t SUBSET count n` by (rw[SUBSET_DEF, Abbr`t`] >> metis_tac[MOD_LESS])) >>
  metis_tac[CARD_SUBSET, FINITE_COUNT, CARD_COUNT]);
(* not used *)

(* Theorem: !n. 0 < n /\ 0 NOTIN (IMAGE (\x. x MOD n) s) ==> CARD (IMAGE (\x. x MOD n) s) < n *)
(* Proof:
   Let t = IMAGE (\x. x MOD n) s
   Since   t SUBSET count n          by SUBSET_DEF, MOD_LESS
     Now   FINITE (count n)          by FINITE_COUNT
     and   CARD (count n) = n        by CARD_COUNT
      So   CARD t <= n               by CARD_SUBSET
     and   FINITE t                  by SUBSET_FINITE
     But   0 IN (count n)            by IN_COUNT
     yet   0 NOTIN t                 by given
   Hence   t <> (count n)            by NOT_EQUAL_SETS
      So   CARD t <> n               by SUBSET_EQ_CARD
     Thus  CARD t < n
*)
val card_mod_image_nonzero = store_thm(
  "card_mod_image_nonzero",
  ``!s n. 0 < n /\ 0 NOTIN (IMAGE (\x. x MOD n) s) ==> CARD (IMAGE (\x. x MOD n) s) < n``,
  rpt strip_tac >>
  qabbrev_tac `t = IMAGE (\x. x MOD n) s` >>
  (`t SUBSET count n` by (rw[SUBSET_DEF, Abbr`t`] >> metis_tac[MOD_LESS])) >>
  `FINITE (count n) /\ (CARD (count n) = n) ` by rw[] >>
  `CARD t <= n` by metis_tac[CARD_SUBSET] >>
  `0 IN (count n)` by rw[] >>
  `t <> (count n)` by metis_tac[NOT_EQUAL_SETS] >>
  `CARD t <> n` by metis_tac[SUBSET_EQ_CARD, SUBSET_FINITE] >>
  decide_tac);
(* not used *)

(* ------------------------------------------------------------------------- *)
(* Partition Property                                                        *)
(* ------------------------------------------------------------------------- *)

(* Overload partition by split *)
val _ = overload_on("split", ``\s u v. (s = u UNION v) /\ (DISJOINT u v)``);

(* Pretty printing of partition by split *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 2)),
                       fixity = Infix(NONASSOC, 450),
                  paren_style = OnlyIfNecessary,
                    term_name = "split",
                  pp_elements = [HardSpace 1, TOK "=|=", HardSpace 1, TM,
                                 BreakSpace(1,1), TOK "#", BreakSpace(1,1)]};

(* Theorem: FINITE s ==> !u v. s =|= u # v ==> ((u = {}) <=> (v = s)) *)
(* Proof:
   If part: u = {} ==> v = s
      Note  s = {} UNION v        by given, u = {}
              = v                 by UNION_EMPTY
   Only-if part: v = s ==> u = {}
      Note FINITE u /\ FINITE v       by FINITE_UNION
       ==> CARD v = CARD u + CARD v   by CARD_UNION_DISJOINT
       ==>      0 = CARD u            by arithmetic
      Thus u = {}                     by CARD_EQ_0
*)
val finite_partition_property = store_thm(
  "finite_partition_property",
  ``!s. FINITE s ==> !u v. s =|= u # v ==> ((u = {}) <=> (v = s))``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `FINITE u /\ FINITE v` by metis_tac[FINITE_UNION] >>
  `CARD v = CARD u + CARD v` by metis_tac[CARD_UNION_DISJOINT] >>
  `CARD u <> 0` by rw[CARD_EQ_0] >>
  decide_tac);

(* Theorem: FINITE s ==> !P. let u = {x | x IN s /\ P x} in let v = {x | x IN s /\ ~P x} in
            FINITE u /\ FINITE v /\ s =|= u # v *)
(* Proof:
   This is to show:
   (1) FINITE u, true      by SUBSET_DEF, SUBSET_FINITE
   (2) FINITE v, true      by SUBSET_DEF, SUBSET_FINITE
   (3) u UNION v = s       by IN_UNION
   (4) DISJOINT u v, true  by IN_DISJOINT, MEMBER_NOT_EMPTY
*)
Theorem finite_partition_by_predicate:
  !s. FINITE s ==>
      !P. let u = {x | x IN s /\ P x} ;
              v = {x | x IN s /\ ~P x}
          in
              FINITE u /\ FINITE v /\ s =|= u # v
Proof
  rw_tac std_ss[] >| [
    `u SUBSET s` by rw[SUBSET_DEF, Abbr`u`] >>
    metis_tac[SUBSET_FINITE],
    `v SUBSET s` by rw[SUBSET_DEF, Abbr`v`] >>
    metis_tac[SUBSET_FINITE],
    simp[EXTENSION, Abbr‘u’, Abbr‘v’] >>
    metis_tac[],
    simp[Abbr‘u’, Abbr‘v’, DISJOINT_DEF, EXTENSION] >> metis_tac[]
  ]
QED

(* Theorem: u SUBSET s ==> let v = s DIFF u in s =|= u # v *)
(* Proof:
   This is to show:
   (1) u SUBSET s ==> s = u UNION (s DIFF u), true   by UNION_DIFF
   (2) u SUBSET s ==> DISJOINT u (s DIFF u), true    by DISJOINT_DIFF
*)
val partition_by_subset = store_thm(
  "partition_by_subset",
  ``!s u. u SUBSET s ==> let v = s DIFF u in s =|= u # v``,
  rw[UNION_DIFF, DISJOINT_DIFF]);

(* Theorem: x IN s ==> s =|= {x} # (s DELETE x) *)
(* Proof:
   Note x IN s ==> {x} SUBSET s    by SUBSET_DEF, IN_SING
    and s DELETE x = s DIFF {x}    by DELETE_DEF
   Thus s =|= {x} # (s DELETE x)   by partition_by_subset
*)
val partition_by_element = store_thm(
  "partition_by_element",
  ``!s x. x IN s ==> s =|= {x} # (s DELETE x)``,
  metis_tac[partition_by_subset, DELETE_DEF, SUBSET_DEF, IN_SING]);

(* ------------------------------------------------------------------------- *)
(* Splitting of a set                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: s =|= {} # t <=> (s = t) *)
(* Proof:
       s =|= {} # t
   <=> (s = {} UNION t) /\ (DISJOINT {} t)     by notation
   <=> (s = {} UNION t) /\ T                   by DISJOINT_EMPTY
   <=> s = t                                   by UNION_EMPTY
*)
val SPLIT_EMPTY = store_thm(
  "SPLIT_EMPTY",
  ``!s t. s =|= {} # t <=> (s = t)``,
  rw[]);

(* Theorem: s =|= u # v /\ v =|= a # b ==> s =|= u UNION a # b /\ u UNION a =|= u # a *)
(* Proof:
   Note s =|= u # v <=> (s = u UNION v) /\ (DISJOINT u v)   by notation
    and v =|= a # b <=> (v = a UNION b) /\ (DISJOINT a b)   by notation
   Let c = u UNION a.
   Then s = u UNION v                   by above
          = u UNION (a UNION b)         by above
          = (u UNION a) UNION b         by UNION_ASSOC
          = c UNION b
   Note  DISJOINT u v
     <=> DISJOINT u (a UNION b)
     <=> DISJOINT (a UNION b) u         by DISJOINT_SYM
     <=> DISJOINT a u /\ DISJOINT b u   by DISJOINT_UNION
     <=> DISJOINT u a /\ DISJOINT u b   by DISJOINT_SYM

   Thus  DISJOINT c b
     <=> DISJOINT (u UNION a) b         by above
     <=> DISJOINT u b /\ DISJOINT a b   by DISJOINT_UNION
     <=> T /\ T                         by above
     <=> T
   Therefore,
         s =|= c # b       by s = c UNION b /\ DISJOINT c b
     and c =|= u # a       by c = u UNION a /\ DISJOINT u a
*)
val SPLIT_UNION = store_thm(
  "SPLIT_UNION",
  ``!s u v a b. s =|= u # v /\ v =|= a # b ==> s =|= u UNION a # b /\ u UNION a =|= u # a``,
  metis_tac[DISJOINT_UNION, DISJOINT_SYM, UNION_ASSOC]);

(* Theorem: s =|= u # v <=> u SUBSET s /\ (v = s DIFF u) *)
(* Proof:
   Note s =|= u # v <=> (s = u UNION v) /\ (DISJOINT u v)   by notation
   If part: s =|= u # v ==> u SUBSET s /\ (v = s DIFF u)
      Note u SUBSET (u UNION v)         by SUBSET_UNION
           s DIFF u
         = (u UNION v) DIFF u           by s = u UNION v
         = v DIFF u                     by DIFF_SAME_UNION
         = v                            by DISJOINT_DIFF_IFF, DISJOINT_SYM

   Only-if part: u SUBSET s /\ (v = s DIFF u) ==> s =|= u # v
      Note s = u UNION (s DIFF u)       by UNION_DIFF, u SUBSET s
       and DISJOINT u (s DIFF u)        by DISJOINT_DIFF
      Thus s =|= u # v                  by notation
*)
val SPLIT_EQ = store_thm(
  "SPLIT_EQ",
  ``!s u v. s =|= u # v <=> u SUBSET s /\ (v = s DIFF u)``,
  rw[DISJOINT_DEF, SUBSET_DEF, EXTENSION] >>
  metis_tac[]);

(* Theorem: (s =|= u # v) = (s =|= v # u) *)
(* Proof:
     s =|= u # v
   = (s = u UNION v) /\ DISJOINT u v    by notation
   = (s = v UNION u) /\ DISJOINT u v    by UNION_COMM
   = (s = v UNION u) /\ DISJOINT v u    by DISJOINT_SYM
   = s =|= v # u                        by notation
*)
val SPLIT_SYM = store_thm(
  "SPLIT_SYM",
  ``!s u v. (s =|= u # v) = (s =|= v # u)``,
  rw_tac std_ss[UNION_COMM, DISJOINT_SYM]);

(* Theorem: (s =|= u # v) ==> (s =|= v # u) *)
(* Proof: by SPLIT_SYM *)
val SPLIT_SYM_IMP = store_thm(
  "SPLIT_SYM_IMP",
  ``!s u v. (s =|= u # v) ==> (s =|= v # u)``,
  rw_tac std_ss[SPLIT_SYM]);

(* Theorem: s =|= {x} # v <=> (x IN s /\ (v = s DELETE x)) *)
(* Proof:
       s =|= {x} # v
   <=> {x} SUBSET s /\ (v = s DIFF {x})   by SPLIT_EQ
   <=> x IN s       /\ (v = s DIFF {x})   by SUBSET_DEF
   <=> x IN s       /\ (v = s DELETE x)   by DELETE_DEF
*)
val SPLIT_SING = store_thm(
  "SPLIT_SING",
  ``!s v x. s =|= {x} # v <=> (x IN s /\ (v = s DELETE x))``,
  rw[SPLIT_EQ, SUBSET_DEF, DELETE_DEF]);

(* Theorem: s =|= u # v ==> u SUBSET s /\ v SUBSET s *)
(* Proof: by SUBSET_UNION *)
Theorem SPLIT_SUBSETS:
  !s u v. s =|= u # v ==> u SUBSET s /\ v SUBSET s
Proof
  rw[]
QED

(* Theorem: FINITE s /\ s =|= u # v ==> FINITE u /\ FINITE v *)
(* Proof: by SPLIT_SUBSETS, SUBSET_FINITE *)
Theorem SPLIT_FINITE:
  !s u v. FINITE s /\ s =|= u # v ==> FINITE u /\ FINITE v
Proof
  simp[SPLIT_SUBSETS, SUBSET_FINITE]
QED

(* Theorem: FINITE s /\ s =|= u # v ==> (CARD s = CARD u + CARD v) *)
(* Proof:
   Note FINITE u /\ FINITE v   by SPLIT_FINITE
     CARD s
   = CARD (u UNION v)          by notation
   = CARD u + CARD v           by CARD_UNION_DISJOINT
*)
Theorem SPLIT_CARD:
  !s u v. FINITE s /\ s =|= u # v ==> (CARD s = CARD u + CARD v)
Proof
  metis_tac[CARD_UNION_DISJOINT, SPLIT_FINITE]
QED

(* Theorem: s =|= u # v <=> (u = s DIFF v) /\ (v = s DIFF u) *)
(* Proof:
   If part: s =|= u # v ==> (u = s DIFF v) /\ (v = s DIFF u)
      True by EXTENSION, IN_UNION, IN_DISJOINT, IN_DIFF.
   Only-if part: (u = s DIFF v) /\ (v = s DIFF u) ==> s =|= u # v
      True by EXTENSION, IN_UNION, IN_DISJOINT, IN_DIFF.
*)
val SPLIT_EQ_DIFF = store_thm(
  "SPLIT_EQ_DIFF",
  ``!s u v. s =|= u # v <=> (u = s DIFF v) /\ (v = s DIFF u)``,
  rpt strip_tac >>
  eq_tac >| [
    rpt strip_tac >| [
      rw[EXTENSION] >>
      metis_tac[IN_UNION, IN_DISJOINT, IN_DIFF],
      rw[EXTENSION] >>
      metis_tac[IN_UNION, IN_DISJOINT, IN_DIFF]
    ],
    rpt strip_tac >| [
      rw[EXTENSION] >>
      metis_tac[IN_UNION, IN_DIFF],
      metis_tac[IN_DISJOINT, IN_DIFF]
    ]
  ]);

(* Theorem alias *)
val SPLIT_BY_SUBSET = save_thm("SPLIT_BY_SUBSET", partition_by_subset);
(* val SPLIT_BY_SUBSET = |- !s u. u SUBSET s ==> (let v = s DIFF u in s =|= u # v): thm *)

(* Theorem alias *)
val SUBSET_DIFF_DIFF = save_thm("SUBSET_DIFF_DIFF", DIFF_DIFF_SUBSET);
(* val SUBSET_DIFF_DIFF = |- !s t. t SUBSET s ==> (s DIFF (s DIFF t) = t) *)

(* Theorem: s1 SUBSET t /\ s2 SUBSET t /\ (t DIFF s1 = t DIFF s2) ==> (s1 = s2) *)
(* Proof:
   Let u = t DIFF s2.
   Then u = t DIFF s1             by given
    ==> t =|= u # s1              by SPLIT_BY_SUBSET, s1 SUBSET t
   Thus s1 = t DIFF u             by SPLIT_EQ
           = t DIFF (t DIFF s2)   by notation
           = s2                   by SUBSET_DIFF_DIFF, s2 SUBSET t
*)
val SUBSET_DIFF_EQ = store_thm(
  "SUBSET_DIFF_EQ",
  ``!s1 s2 t. s1 SUBSET t /\ s2 SUBSET t /\ (t DIFF s1 = t DIFF s2) ==> (s1 = s2)``,
  metis_tac[SPLIT_BY_SUBSET, SPLIT_EQ, SUBSET_DIFF_DIFF]);

(* ------------------------------------------------------------------------- *)
(* Bijective Inverses.                                                       *)
(* ------------------------------------------------------------------------- *)

(* In pred_setTheory:
LINV_DEF        |- !f s t. INJ f s t ==> !x. x IN s ==> (LINV f s (f x) = x)
BIJ_LINV_INV    |- !f s t. BIJ f s t ==> !x. x IN t ==> (f (LINV f s x) = x)
BIJ_LINV_BIJ    |- !f s t. BIJ f s t ==> BIJ (LINV f s) t s
RINV_DEF        |- !f s t. SURJ f s t ==> !x. x IN t ==> (f (RINV f s x) = x)

That's it, must be missing some!
Must assume: !y. y IN t ==> RINV f s y IN s
*)

(* Theorem: BIJ f s t ==> !x. x IN t ==> (LINV f s x) IN s *)
(* Proof:
   Since BIJ f s t ==> BIJ (LINV f s) t s   by BIJ_LINV_BIJ
      so x IN t ==> (LINV f s x) IN s       by BIJ_DEF, INJ_DEF
*)
val BIJ_LINV_ELEMENT = store_thm(
  "BIJ_LINV_ELEMENT",
  ``!f s t. BIJ f s t ==> !x. x IN t ==> (LINV f s x) IN s``,
  metis_tac[BIJ_LINV_BIJ, BIJ_DEF, INJ_DEF]);

(* Theorem: (!x. x IN s ==> (LINV f s (f x) = x)) /\ (!x. x IN t ==> (f (LINV f s x) = x)) *)
(* Proof:
   Since BIJ f s t ==> INJ f s t      by BIJ_DEF
     and INJ f s t ==> !x. x IN s ==> (LINV f s (f x) = x)    by LINV_DEF
    also BIJ f s t ==> !x. x IN t ==> (f (LINV f s x) = x)    by BIJ_LINV_INV
*)
val BIJ_LINV_THM = store_thm(
  "BIJ_LINV_THM",
  ``!(f:'a -> 'b) s t. BIJ f s t ==>
    (!x. x IN s ==> (LINV f s (f x) = x)) /\ (!x. x IN t ==> (f (LINV f s x) = x))``,
  metis_tac[BIJ_DEF, LINV_DEF, BIJ_LINV_INV]);

(* Theorem: BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==>
            !x. x IN s ==> (RINV f s (f x) = x) *)
(* Proof:
   BIJ f s t means INJ f s t /\ SURJ f s t     by BIJ_DEF
   Hence x IN s ==> f x IN t                   by INJ_DEF or SURJ_DEF
                ==> f (RINV f s (f x)) = f x   by RINV_DEF, SURJ f s t
                ==> RINV f s (f x) = x         by INJ_DEF
*)
val BIJ_RINV_INV = store_thm(
  "BIJ_RINV_INV",
  ``!(f:'a -> 'b) s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==>
   !x. x IN s ==> (RINV f s (f x) = x)``,
  rw[BIJ_DEF] >>
  `f x IN t` by metis_tac[INJ_DEF] >>
  `f (RINV f s (f x)) = f x` by metis_tac[RINV_DEF] >>
  metis_tac[INJ_DEF]);

(* Theorem: BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==> BIJ (RINV f s) t s *)
(* Proof:
   By BIJ_DEF, this is to show:
   (1) INJ (RINV f s) t s
       By INJ_DEF, this is to show:
       x IN t /\ y IN t /\ RINV f s x = RINV f s y ==> x = y
       But  SURJ f s t           by BIJ_DEF
        so  f (RINV f s x) = x   by RINV_DEF, SURJ f s t
       and  f (RINV f s y) = y   by RINV_DEF, SURJ f s t
       Thus x = y.
   (2) SURJ (RINV f s) t s
       By SURJ_DEF, this is to show:
       x IN s ==> ?y. y IN t /\ (RINV f s y = x)
       But  INJ f s t            by BIJ_DEF
        so  f x IN t             by INJ_DEF
       and  RINV f s (f x) = x   by BIJ_RINV_INV
       Take y = f x to meet the criteria.
*)
val BIJ_RINV_BIJ = store_thm(
  "BIJ_RINV_BIJ",
  ``!(f:'a -> 'b) s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==> BIJ (RINV f s) t s``,
  rpt strip_tac >>
  rw[BIJ_DEF] >-
  metis_tac[INJ_DEF, BIJ_DEF, RINV_DEF] >>
  rw[SURJ_DEF] >>
  metis_tac[INJ_DEF, BIJ_DEF, BIJ_RINV_INV]);

(* Theorem: INJ f t t /\ s SUBSET t ==> !x. x IN s ==> (LINV f t (f x) = x) *)
(* Proof: by LINV_DEF, SUBSET_DEF *)
val LINV_SUBSET = store_thm(
  "LINV_SUBSET",
  ``!(f:'a -> 'a) s t. INJ f t t /\ s SUBSET t ==> !x. x IN s ==> (LINV f t (f x) = x)``,
  metis_tac[LINV_DEF, SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* Iteration, Summation and Product                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ITSET f {x} b = f x b *)
(* Proof:
   Since FINITE {x}           by FINITE_SING
     ITSET f {x} b
   = ITSET f (REST {x}) (f (CHOICE {x} b)   by ITSET_THM
   = ITSET f {} (f x b)       by CHOICE_SING, REST_SING
   = f x b                    by ITSET_EMPTY
*)
val ITSET_SING = store_thm(
  "ITSET_SING",
  ``!f x b. ITSET f {x} b = f x b``,
  rw[ITSET_THM]);

(* Theorem: FINITE s /\ s <> {} ==> (ITSET f s b = ITSET f (REST s) (f (CHOICE s) b)) *)
(* Proof: by ITSET_THM. *)
val ITSET_PROPERTY = store_thm(
  "ITSET_PROPERTY",
  ``!s f b. FINITE s /\ s <> {} ==> (ITSET f s b = ITSET f (REST s) (f (CHOICE s) b))``,
  rw[ITSET_THM]);

(* Theorem: (f = g) ==> (ITSET f = ITSET g) *)
(* Proof: by congruence rule *)
val ITSET_CONG = store_thm(
  "ITSET_CONG",
  ``!f g. (f = g) ==> (ITSET f = ITSET g)``,
  rw[]);

(* Reduction of ITSET *)

(* Theorem: (!x y z. f x (f y z) = f y (f x z)) ==>
             !s x b. FINITE s /\ x NOTIN s ==> (ITSET f (x INSERT s) b = f x (ITSET f s b)) *)
(* Proof:
   Since x NOTIN s ==> s DELETE x = s   by DELETE_NON_ELEMENT
   The result is true                   by COMMUTING_ITSET_RECURSES
*)
val ITSET_REDUCTION = store_thm(
  "ITSET_REDUCTION",
  ``!f. (!x y z. f x (f y z) = f y (f x z)) ==>
   !s x b. FINITE s /\ x NOTIN s ==> (ITSET f (x INSERT s) b = f x (ITSET f s b))``,
  rw[COMMUTING_ITSET_RECURSES, DELETE_NON_ELEMENT]);

(* ------------------------------------------------------------------------- *)
(* Rework of ITSET Theorems                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define a function that gives closure and is commute_associative *)
val closure_comm_assoc_fun_def = Define`
    closure_comm_assoc_fun f s <=>
       (!x y. x IN s /\ y IN s ==> f x y IN s) /\ (* closure *)
       (!x y z. x IN s /\ y IN s /\ z IN s ==> (f x (f y z) = f y (f x z))) (* comm_assoc *)
`;

(* Theorem: FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
            !(x b):: t. ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b) *)
(* Proof:
   By complete induction on CARD s.
   The goal is to show:
   ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b)  [1]
   Applying ITSET_INSERT to LHS, this is to prove:
   ITSET f z (f y b) = ITSET f (s DELETE x) (f x b)
           |    |
           |    y = CHOICE (x INSERT s)
           +--- z = REST (x INSERT s)
   Note y NOTIN z   by CHOICE_NOT_IN_REST
   If x IN s,
       then x INSERT s = s                      by ABSORPTION
       thus y = CHOICE s, z = REST s            by x INSERT s = s

       If x = y,
       Since s = CHOICE s INSERT REST s         by CHOICE_INSERT_REST
               = y INSERT z                     by above y, z
       Hence z = s DELETE y                     by DELETE_INSERT
       Since CARD z < CARD s, apply induction:
       ITSET f (y INSERT z) b = ITSET f (z DELETE y) (f y b)  [2a]
       For the original goal [1],
       LHS = ITSET f (x INSERT s) b
           = ITSET f s b                        by x INSERT s = s
           = ITSET f (y INSERT z) b             by s = y INSERT z
           = ITSET f (z DELETE y) (f y b)       by induction hypothesis [2a]
           = ITSET f z (f y b)                  by DELETE_NON_ELEMENT, y NOTIN z
           = ITSET f (s DELETE y) (f y b)       by z = s DELETE y
           = ITSET f (s DELETE x) (f x b)       by x = y
           = RHS

       If x <> y, let u = z DELETE x.
       Note REST s = z = x INSERT u             by INSERT_DELETE
       Now s = x INSERT (y INSERT u)
             = x INSERT v, where v = y INSERT u, and x NOTIN z.
       Therefore (s DELETE x) = v               by DELETE_INSERT
       Since CARD v < CARD s, apply induction:
       ITSET f (x INSERT v) b = ITSET f (v DELETE x) (f x b)    [2b]
       For the original goal [1],
       LHS = ITSET f (x INSERT s) b
           = ITSET f s b                        by x INSERT s = s
           = ITSET f (x INSERT v) b             by s = x INSERT v
           = ITSET f (v DELETE x) (f x b)       by induction hypothesis [2b]
           = ITSET f v (f x b)                  by x NOTIN v
           = ITSET f (s DELETE x) (f x b)       by v = s DELETE x
           = RHS

   If x NOTIN s,
       then s DELETE x = x                      by DELETE_NON_ELEMENT
       To prove: ITSET f (x INSERT s) b = ITSET f s (f x b)    by [1]
       The CHOICE/REST of (x INSERT s) cannot be simplified, but can be replaced by:
       Note (x INSERT s) <> {}                  by NOT_EMPTY_INSERT
         y INSERT z
       = CHOICE (x INSERT s) INSERT (REST (x INSERT s))  by y = CHOICE (x INSERT s), z = REST (x INSERT s)
       = x INSERT s                                      by CHOICE_INSERT_REST

       If y = x,
          Then z = s                            by DELETE_INSERT, y INSERT z = x INSERT s, y = x.
          because s = s DELETE x                by DELETE_NON_ELEMENT, x NOTIN s.
                    = (x INSERT s) DELETE x     by DELETE_INSERT
                    = (y INSERT z) DELETE x     by above
                    = (y INSERT z) DELETE y     by y = x
                    = z DELETE y                by DELETE_INSERT
                    = z                         by DELETE_NON_ELEMENT, y NOTIN z.
       For the modified goal [1],
       LHS = ITSET f (x INSERT s) b
           = ITSET f (REST (x INSERT s)) (f (CHOICE (x INSERT s)) b)  by ITSET_PROPERTY
           = ITSET f z (f y b)                           by y = CHOICE (x INSERT s), z = REST (x INSERT s)
           = ITSET f s (f x b)                           by z = s, y = x
           = RHS

       If y <> x,
       Then x IN z and y IN s                   by IN_INSERT, x INSERT s = y INSERT z and x <> y.
        and s = y INSERT (s DELETE y)           by INSERT_DELETE, y IN s
              = y INSERT u  where u = s DELETE y
       Then y NOTIN u                           by IN_DELETE
        and z = x INSERT u,
       because  x INSERT u
              = x INSERT (s DELETE y)           by u = s DELETE y
              = (x INSERT s) DELETE y           by DELETE_INSERT, x <> y
              = (y INSERT z) DELETE y           by x INSERT s = y INSERT z
              = z                               by INSERT_DELETE
        and x NOTIN u                           by IN_DELETE, u = s DELETE y, but x NOTIN s.
       Thus CARD u < CARD s                     by CARD_INSERT, s = y INSERT u.
       Apply induction:
       !x b. ITSET f (x INSERT u) b = ITSET f (u DELETE x) (f x b)  [2c]

       For the modified goal [1],
       LHS = ITSET f (x INSERT s) b
           = ITSET f (REST (x INSERT s)) (f (CHOICE (x INSERT s)) b)  by ITSET_PROPERTY
           = ITSET f z (f y b)                  by z = REST (x INSERT s), y = CHOICE (x INSERT s)
           = ITSET f (x INSERT u) (f y b)       by z = x INSERT u
           = ITSET f (u DELETE x) (f x (f y b)) by induction hypothesis, [2c]
           = ITSET f u (f x (f y b))            by x NOTIN u
       RHS = ITSET f s (f x b)
           = ITSET f (y INSERT u) (f x b)       by s = y INSERT u
           = ITSET f (u DELETE y) (f y (f x b)) by induction hypothesis, [2c]
           = ITSET f u (f y (f x b))            by y NOTIN u
       Applying the commute_associativity of f, LHS = RHS.
*)
Theorem SUBSET_COMMUTING_ITSET_INSERT:
  !f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
          !(x b)::t. ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b)
Proof
  completeInduct_on `CARD s` >>
  rule_assum_tac(SIMP_RULE bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw[RES_FORALL_THM] >>
  rw[ITSET_INSERT] >>
  qabbrev_tac `y = CHOICE (x INSERT s)` >>
  qabbrev_tac `z = REST (x INSERT s)` >>
  `y NOTIN z` by metis_tac[CHOICE_NOT_IN_REST] >>
  `!x s. x IN s ==> (x INSERT s = s)` by rw[ABSORPTION] >>
  `!x s. x NOTIN s ==> (s DELETE x = s)` by rw[DELETE_NON_ELEMENT] >>
  Cases_on `x IN s` >| [
    `s = y INSERT z` by metis_tac[NOT_IN_EMPTY, CHOICE_INSERT_REST] >>
    `FINITE z` by metis_tac[REST_SUBSET, SUBSET_FINITE] >>
    `CARD s = SUC (CARD z)` by rw[] >>
    `CARD z < CARD s` by decide_tac >>
    `z = s DELETE y` by metis_tac[DELETE_INSERT] >>
    `z SUBSET t` by metis_tac[DELETE_SUBSET, SUBSET_TRANS] >>
    Cases_on `x = y` >- metis_tac[] >>
    `x IN z` by metis_tac[IN_INSERT] >>
    qabbrev_tac `u = z DELETE x` >>
    `z = x INSERT u` by rw[INSERT_DELETE, Abbr`u`] >>
    `x NOTIN u` by metis_tac[IN_DELETE] >>
    qabbrev_tac `v = y INSERT u` >>
    `s = x INSERT v` by simp[INSERT_COMM, Abbr `v`] >>
    `x NOTIN v` by rw[Abbr `v`] >>
    `FINITE v` by metis_tac[FINITE_INSERT] >>
    `CARD s = SUC (CARD v)` by metis_tac[CARD_INSERT] >>
    `CARD v < CARD s` by decide_tac >>
    `v SUBSET t` by metis_tac[INSERT_SUBSET, SUBSET_TRANS] >>
    `s DELETE x = v` by rw[DELETE_INSERT, Abbr `v`] >>
    `v = s DELETE x` by rw[] >>
    `y IN t` by metis_tac[NOT_INSERT_EMPTY, CHOICE_DEF, SUBSET_DEF] >>
    metis_tac[],
    `x INSERT s <> {}` by rw[] >>
    `y INSERT z = x INSERT s` by rw[CHOICE_INSERT_REST, Abbr`y`, Abbr`z`] >>
    Cases_on `x = y` >- metis_tac[DELETE_INSERT, ITSET_PROPERTY] >>
    `x IN z /\ y IN s` by metis_tac[IN_INSERT] >>
    qabbrev_tac `u = s DELETE y` >>
    `s = y INSERT u` by rw[INSERT_DELETE, Abbr`u`] >>
    `y NOTIN u` by metis_tac[IN_DELETE] >>
    `z = x INSERT u` by metis_tac[DELETE_INSERT, INSERT_DELETE] >>
    `x NOTIN u` by metis_tac[IN_DELETE] >>
    `FINITE u` by metis_tac[FINITE_DELETE, SUBSET_FINITE] >>
    `CARD u < CARD s` by rw[] >>
    `u SUBSET t` by metis_tac[DELETE_SUBSET, SUBSET_TRANS] >>
    `y IN t` by metis_tac[CHOICE_DEF, SUBSET_DEF] >>
    `f y b IN t /\ f x b IN t` by prove_tac[closure_comm_assoc_fun_def] >>
    `ITSET f z (f y b) = ITSET f (x INSERT u) (f y b)` by rw[] >>
    `_ = ITSET f (u DELETE x) (f x (f y b))` by metis_tac[] >>
    `_ = ITSET f u (f x (f y b))` by rw[] >>
    `ITSET f s (f x b) = ITSET f (y INSERT u) (f x b)` by rw[] >>
    `_ = ITSET f (u DELETE y) (f y (f x b))` by metis_tac[] >>
    `_ = ITSET f u (f y (f x b))` by rw[] >>
    `f x (f y b) = f y (f x b)` by prove_tac[closure_comm_assoc_fun_def] >>
    metis_tac[]
  ]
QED

(* This is a generalisation of COMMUTING_ITSET_INSERT, removing the requirement of commuting everywhere. *)

(* Theorem: FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
            !(x b)::t. ITSET f s (f x b) = f x (ITSET f s b) *)
(* Proof:
   By complete induction on CARD s.
   The goal is to show: ITSET f s (f x b) = f x (ITSET f s b)
   Base: s = {},
      LHS = ITSET f {} (f x b)
          = f x b                          by ITSET_EMPTY
          = f x (ITSET f {} b)             by ITSET_EMPTY
          = RHS
   Step: s <> {},
   Let s = y INSERT z, where y = CHOICE s, z = REST s.
   Then y NOTIN z                          by CHOICE_NOT_IN_REST
    But y IN t                             by CHOICE_DEF, SUBSET_DEF
    and z SUBSET t                         by REST_SUBSET, SUBSET_TRANS
   Also FINITE z                           by REST_SUBSET, SUBSET_FINITE
   Thus CARD s = SUC (CARD z)              by CARD_INSERT
     or CARD z < CARD s
   Note f x b IN t /\ f y b IN t           by closure_comm_assoc_fun_def

     LHS = ITSET f s (f x b)
         = ITSET f (y INSERT z) (f x b)        by s = y INSERT z
         = ITSET f (z DELETE y) (f y (f x b))  by SUBSET_COMMUTING_ITSET_INSERT, y, f x b IN t
         = ITSET f z (f y (f x b))             by DELETE_NON_ELEMENT, y NOTIN z
         = ITSET f z (f x (f y b))             by closure_comm_assoc_fun_def, x, y, b IN t
         = f x (ITSET f z (f y b))             by inductive hypothesis, CARD z < CARD s, x, f y b IN t
         = f x (ITSET f (z DELETE y) (f y b))  by DELETE_NON_ELEMENT, y NOTIN z
         = f x (ITSET f (y INSERT z) b)        by SUBSET_COMMUTING_ITSET_INSERT, y, f y b IN t
         = f x (ITSET f s b)                   by s = y INSERT z
         = RHS
*)
val SUBSET_COMMUTING_ITSET_REDUCTION = store_thm(
  "SUBSET_COMMUTING_ITSET_REDUCTION",
  ``!f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
     !(x b)::t. ITSET f s (f x b) = f x (ITSET f s b)``,
  completeInduct_on `CARD s` >>
  rule_assum_tac(SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw[RES_FORALL_THM] >>
  Cases_on `s = {}` >-
  rw[ITSET_EMPTY] >>
  `?y z. (y = CHOICE s) /\ (z = REST s) /\ (s = y INSERT z)` by rw[CHOICE_INSERT_REST] >>
  `y NOTIN z` by metis_tac[CHOICE_NOT_IN_REST] >>
  `y IN t` by metis_tac[CHOICE_DEF, SUBSET_DEF] >>
  `z SUBSET t` by metis_tac[REST_SUBSET, SUBSET_TRANS] >>
  `FINITE z` by metis_tac[REST_SUBSET, SUBSET_FINITE] >>
  `CARD s = SUC (CARD z)` by rw[] >>
  `CARD z < CARD s` by decide_tac >>
  `f x b IN t /\ f y b IN t /\ (f y (f x b) = f x (f y b))` by prove_tac[closure_comm_assoc_fun_def] >>
  metis_tac[SUBSET_COMMUTING_ITSET_INSERT, DELETE_NON_ELEMENT]);

(* This helps to prove the next generalisation. *)

(* Theorem: FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
            !(x b):: t. ITSET f (x INSERT s) b = f x (ITSET f (s DELETE x) b) *)
(* Proof:
   Note (s DELETE x) SUBSET t       by DELETE_SUBSET, SUBSET_TRANS
    and FINITE (s DELETE x)         by FINITE_DELETE, FINITE s
     ITSET f (x INSERT s) b
   = ITSET f (s DELETE x) (f x b)   by SUBSET_COMMUTING_ITSET_INSERT
   = f x (ITSET f (s DELETE x) b)   by SUBSET_COMMUTING_ITSET_REDUCTION, (s DELETE x) SUBSET t
*)
val SUBSET_COMMUTING_ITSET_RECURSES = store_thm(
  "SUBSET_COMMUTING_ITSET_RECURSES",
  ``!f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
     !(x b):: t. ITSET f (x INSERT s) b = f x (ITSET f (s DELETE x) b)``,
  rw[RES_FORALL_THM] >>
  `(s DELETE x) SUBSET t` by metis_tac[DELETE_SUBSET, SUBSET_TRANS] >>
  `FINITE (s DELETE x)` by rw[] >>
  metis_tac[SUBSET_COMMUTING_ITSET_INSERT, SUBSET_COMMUTING_ITSET_REDUCTION]);

(* ------------------------------------------------------------------------- *)
(* SUM_IMAGE and PROD_IMAGE Theorems                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: SIGMA f {} = 0 *)
(* Proof: by SUM_IMAGE_THM *)
val SUM_IMAGE_EMPTY = store_thm(
  "SUM_IMAGE_EMPTY",
  ``!f. SIGMA f {} = 0``,
  rw[SUM_IMAGE_THM]);

(* Theorem: FINITE s ==> !e. e NOTIN s ==> (SIGMA f (e INSERT s) = f e + (SIGMA f s)) *)
(* Proof:
     SIGMA f (e INSERT s)
   = f e + SIGMA f (s DELETE e)    by SUM_IMAGE_THM
   = f e + SIGMA f s               by DELETE_NON_ELEMENT
*)
val SUM_IMAGE_INSERT = store_thm(
  "SUM_IMAGE_INSERT",
  ``!f s. FINITE s ==> !e. e NOTIN s ==> (SIGMA f (e INSERT s) = f e + (SIGMA f s))``,
  rw[SUM_IMAGE_THM, DELETE_NON_ELEMENT]);

(* Theorem: FINITE s ==> !f. (!x y. (f x = f y) ==> (x = y)) ==> (SIGMA f s = SIGMA I (IMAGE f s)) *)
(* Proof:
   By finite induction on s.
   Base case: SIGMA f {} = SIGMA I {}
        SIGMA f {}
      = 0              by SUM_IMAGE_THM
      = SIGMA I {}     by SUM_IMAGE_THM
      = SUM_SET {}     by SUM_SET_DEF
   Step case: !f. (!x y. (f x = f y) ==> (x = y)) ==> (SIGMA f s = SUM_SET (IMAGE f s)) ==>
              e NOTIN s ==> SIGMA f (e INSERT s) = SUM_SET (f e INSERT IMAGE f s)
      Note FINITE s ==> FINITE (IMAGE f s)   by IMAGE_FINITE
       and e NOTIN s ==> f e NOTIN f s       by the injective property
        SIGMA f (e INSERT s)
      = f e + SIGMA f (s DELETE e))    by SUM_IMAGE_THM
      = f e + SIGMA f s                by DELETE_NON_ELEMENT
      = f e + SUM_SET (IMAGE f s))     by induction hypothesis
      = f e + SUM_SET ((IMAGE f s) DELETE (f e))   by DELETE_NON_ELEMENT, f e NOTIN f s
      = SUM_SET (f e INSERT IMAGE f s)             by SUM_SET_THM
*)
val SUM_IMAGE_AS_SUM_SET = store_thm(
  "SUM_IMAGE_AS_SUM_SET",
  ``!s. FINITE s ==> !f. (!x y. (f x = f y) ==> (x = y)) ==> (SIGMA f s = SUM_SET (IMAGE f s))``,
  HO_MATCH_MP_TAC FINITE_INDUCT >>
  rw[SUM_SET_DEF] >-
  rw[SUM_IMAGE_THM] >>
  rw[SUM_IMAGE_THM, SUM_IMAGE_DELETE] >>
  metis_tac[]);

(* Theorem: FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (SIGMA f s = k * CARD s) *)
(* Proof:
   By finite induction on s.
   Base: SIGMA f {} = k * CARD {}
        SIGMA f {}
      = 0              by SUM_IMAGE_EMPTY
      = k * 0          by MULT_0
      = k * CARD {}    by CARD_EMPTY
   Step: SIGMA f s = k * CARD s /\ e NOTIN s /\ !x. x IN e INSERT s /\ f x = k ==>
         SIGMA f (e INSERT s) = k * CARD (e INSERT s)
      Note f e = k /\ !x. x IN s ==> f x = k   by IN_INSERT
        SIGMA f (e INSERT s)
      = f e + SIGMA f (s DELETE e)     by SUM_IMAGE_THM
      = k + SIGMA f s                  by DELETE_NON_ELEMENT, f e = k
      = k + k * CARD s                 by induction hypothesis
      = k * (1 + CARD s)               by LEFT_ADD_DISTRIB
      = k * SUC (CARD s)               by SUC_ONE_ADD
      = k * CARD (e INSERT s)          by CARD_INSERT
*)
val SIGMA_CONSTANT = store_thm(
  "SIGMA_CONSTANT",
  ``!s. FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (SIGMA f s = k * CARD s)``,
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[SUM_IMAGE_EMPTY] >>
  `(f e = k) /\ !x. x IN s ==> (f x = k)` by rw[] >>
  `SIGMA f (e INSERT s) = f e + SIGMA f (s DELETE e)` by rw[SUM_IMAGE_THM] >>
  `_ = k + SIGMA f s` by metis_tac[DELETE_NON_ELEMENT] >>
  `_ = k + k * CARD s` by rw[] >>
  `_ = k * (1 + CARD s)` by rw[] >>
  `_ = k * SUC (CARD s)` by rw[ADD1] >>
  `_ = k * CARD (e INSERT s)` by rw[CARD_INSERT] >>
  rw[]);

(* Theorem: FINITE s ==> !c. SIGMA (K c) s = c * CARD s *)
(* Proof: by SIGMA_CONSTANT. *)
val SUM_IMAGE_CONSTANT = store_thm(
  "SUM_IMAGE_CONSTANT",
  ``!s. FINITE s ==> !c. SIGMA (K c) s = c * CARD s``,
  rw[SIGMA_CONSTANT]);

(* Theorem: If !e. e IN s, CARD e = n, SIGMA CARD s = n * CARD s. *)
(* Proof:
   By finite induction on set s.
   Base: SIGMA CARD {} = 0
     True by SUM_IMAGE_THM.
   Step: (!e. e IN s ==> (CARD e = n)) ==> (SIGMA CARD s = n * CARD s) ==>
         e NOTIN s /\ !e'. (e' = e) \/ e' IN s ==> (CARD e' = n) ==> SIGMA CARD (e INSERT s) = n * SUC (CARD s)
     Note CARD e = n.
        SIGMA CARD (e INSERT s)
      = CARD e + SIGMA CARD (s DELETE e)    by SUM_IMAGE_THM
      = CARD e + SIGMA CARD s               by DELETE_NON_ELEMENT
      = CARD e + n * CARD s                 by induction hypothesis
      = n + n * CARD s                      by above, CARD e = n
      = n * (1 + CARD s)                    by RIGHT_ADD_DISTRIB
      = n * SUC (CARD s)                    by arithmetic
   Or,
   directly by SIGMA_CONSTANT.
*)
val SIGMA_CARD_CONSTANT = store_thm(
  "SIGMA_CARD_CONSTANT",
  ``!n s. FINITE s ==> (!e. e IN s ==> (CARD e = n)) ==> (SIGMA CARD s = n * (CARD s))``,
  rw[SIGMA_CONSTANT]);

(* Theorem: If n divides CARD e for all e in s, then n divides SIGMA CARD s.
            FINITE s ==> (!e. e IN s ==> n divides (CARD e)) ==> n divides (SIGMA CARD s) *)
(* Proof:
   Use finite induction and SUM_IMAGE_THM.
   Base: n divides SIGMA CARD {}
         Note SIGMA CARD {} = 0        by SUM_IMAGE_THM
          and n divides 0              by ALL_DIVIDES_0
   Step: e NOTIN s /\ n divides (CARD e) ==> n divides SIGMA CARD (e INSERT s)
           SIGMA CARD (e INSERT s)
         = CARD e + SIGMA CARD (s DELETE e)      by SUM_IMAGE_THM
         = CARD e + SIGMA CARD s                 by DELETE_NON_ELEMENT
         Note n divides (CARD e)                 by given
          and n divides SIGMA CARD s             by induction hypothesis
         Thus n divides SIGMA CARD (e INSERT s)  by DIVIDES_ADD_1
*)
val SIGMA_CARD_FACTOR = store_thm(
  "SIGMA_CARD_FACTOR",
  ``!n s. FINITE s ==> (!e. e IN s ==> n divides (CARD e)) ==> n divides (SIGMA CARD s)``,
  strip_tac >>
  Induct_on `FINITE` >>
  rw[] >-
  rw[SUM_IMAGE_THM] >>
  metis_tac[SUM_IMAGE_THM, DELETE_NON_ELEMENT, DIVIDES_ADD_1]);

(* Theorem: (!x. x IN s ==> (f1 x = f2 x)) ==> (SIGMA f1 s = SIGMA f2 s) *)
val SIGMA_CONG = store_thm(
  "SIGMA_CONG",
  ``!s f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (SIGMA f1 s = SIGMA f2 s)``,
  rw[SUM_IMAGE_CONG]);

(* Theorem: FINITE s ==> (CARD s = SIGMA (\x. 1) s) *)
(* Proof:
   By finite induction:
   Base case: CARD {} = SIGMA (\x. 1) {}
     LHS = CARD {}
         = 0                 by CARD_EMPTY
     RHS = SIGMA (\x. 1) {}
         = 0 = LHS           by SUM_IMAGE_THM
   Step case: (CARD s = SIGMA (\x. 1) s) ==>
              !e. e NOTIN s ==> (CARD (e INSERT s) = SIGMA (\x. 1) (e INSERT s))
     CARD (e INSERT s)
   = SUC (CARD s)                             by CARD_DEF
   = SUC (SIGMA (\x. 1) s)                    by induction hypothesis
   = 1 + SIGMA (\x. 1) s                      by ADD1, ADD_COMM
   = (\x. 1) e + SIGMA (\x. 1) s              by function application
   = (\x. 1) e + SIGMA (\x. 1) (s DELETE e)   by DELETE_NON_ELEMENT
   = SIGMA (\x. 1) (e INSERT s)               by SUM_IMAGE_THM
*)
val CARD_AS_SIGMA = store_thm(
  "CARD_AS_SIGMA",
  ``!s. FINITE s ==> (CARD s = SIGMA (\x. 1) s)``,
  ho_match_mp_tac FINITE_INDUCT >>
  conj_tac >-
  rw[SUM_IMAGE_THM] >>
  rpt strip_tac >>
  `CARD (e INSERT s) = SUC (SIGMA (\x. 1) s)` by rw[] >>
  `_ = 1 + SIGMA (\x. 1) s` by rw_tac std_ss[ADD1, ADD_COMM] >>
  `_ = (\x. 1) e + SIGMA (\x. 1) s` by rw[] >>
  `_ = (\x. 1) e + SIGMA (\x. 1) (s DELETE e)` by metis_tac[DELETE_NON_ELEMENT] >>
  `_ = SIGMA (\x. 1) (e INSERT s)` by rw[SUM_IMAGE_THM] >>
  decide_tac);

(* Theorem: FINITE s ==> (CARD s = SIGMA (K 1) s) *)
(* Proof: by CARD_AS_SIGMA, SIGMA_CONG *)
val CARD_EQ_SIGMA = store_thm(
  "CARD_EQ_SIGMA",
  ``!s. FINITE s ==> (CARD s = SIGMA (K 1) s)``,
  rw[CARD_AS_SIGMA, SIGMA_CONG]);

(* Theorem: FINITE s ==> !f g. (!x. x IN s ==> f x <= g x) ==> (SIGMA f s <= SIGMA g s) *)
(* Proof:
   By finite induction:
   Base case: !f g. (!x. x IN {} ==> f x <= g x) ==> SIGMA f {} <= SIGMA g {}
      True since SIGMA f {} = 0      by SUM_IMAGE_THM
   Step case: !f g. (!x. x IN s ==> f x <= g x) ==> SIGMA f s <= SIGMA g s ==>
    e NOTIN s ==>
    !x. x IN e INSERT s ==> f x <= g x ==> !f g. SIGMA f (e INSERT s) <= SIGMA g (e INSERT s)
           SIGMA f (e INSERT s) <= SIGMA g (e INSERT s)
    means  f e + SIGMA f (s DELETE e) <= g e + SIGMA g (s DELETE e)    by SUM_IMAGE_THM
       or  f e + SIGMA f s <= g e + SIGMA g s                          by DELETE_NON_ELEMENT
    Now, x IN e INSERT s ==> (x = e) or (x IN s)         by IN_INSERT
    Therefore  f e <= g e, and !x IN s, f x <= g x       by x IN (e INSERT s) implication
    or         f e <= g e, and SIGMA f s <= SIGMA g s    by induction hypothesis
    Hence      f e + SIGMA f s <= g e + SIGMA g s        by arithmetic
*)
val SIGMA_LE_SIGMA = store_thm(
  "SIGMA_LE_SIGMA",
  ``!s. FINITE s ==> !f g. (!x. x IN s ==> f x <= g x) ==> (SIGMA f s <= SIGMA g s)``,
  ho_match_mp_tac FINITE_INDUCT >>
  conj_tac >-
  rw[SUM_IMAGE_THM] >>
  rw[SUM_IMAGE_THM, DELETE_NON_ELEMENT] >>
  `f e <= g e /\ SIGMA f s <= SIGMA g s` by rw[] >>
  decide_tac);

(* Theorem: FINITE s /\ FINITE t ==> !f. SIGMA f (s UNION t) + SIGMA f (s INTER t) = SIGMA f s + SIGMA f t *)
(* Proof:
   Note SIGMA f (s UNION t)
      = SIGMA f s + SIGMA f t - SIGMA f (s INTER t)    by SUM_IMAGE_UNION
    now s INTER t SUBSET s /\ s INTER t SUBSET t       by INTER_SUBSET
     so SIGMA f (s INTER t) <= SIGMA f s               by SUM_IMAGE_SUBSET_LE
    and SIGMA f (s INTER t) <= SIGMA f t               by SUM_IMAGE_SUBSET_LE
   thus SIGMA f (s INTER t) <= SIGMA f s + SIGMA f t   by arithmetic
   The result follows                                  by ADD_EQ_SUB
*)
val SUM_IMAGE_UNION_EQN = store_thm(
  "SUM_IMAGE_UNION_EQN",
  ``!s t. FINITE s /\ FINITE t ==> !f. SIGMA f (s UNION t) + SIGMA f (s INTER t) = SIGMA f s + SIGMA f t``,
  rpt strip_tac >>
  `SIGMA f (s UNION t) = SIGMA f s + SIGMA f t - SIGMA f (s INTER t)` by rw[SUM_IMAGE_UNION] >>
  `SIGMA f (s INTER t) <= SIGMA f s` by rw[SUM_IMAGE_SUBSET_LE, INTER_SUBSET] >>
  `SIGMA f (s INTER t) <= SIGMA f t` by rw[SUM_IMAGE_SUBSET_LE, INTER_SUBSET] >>
  `SIGMA f (s INTER t) <= SIGMA f s + SIGMA f t` by decide_tac >>
  rw[ADD_EQ_SUB]);

(* Theorem: FINITE s /\ FINITE t /\ DISJOINT s t ==> !f. SIGMA f (s UNION t) = SIGMA f s + SIGMA f t *)
(* Proof:
     SIGMA f (s UNION t)
   = SIGMA f s + SIGMA f t - SIGMA f (s INTER t)    by SUM_IMAGE_UNION
   = SIGMA f s + SIGMA f t - SIGMA f {}             by DISJOINT_DEF
   = SIGMA f s + SIGMA f t - 0                      by SUM_IMAGE_EMPTY
   = SIGMA f s + SIGMA f t                          by arithmetic
*)
val SUM_IMAGE_DISJOINT = store_thm(
  "SUM_IMAGE_DISJOINT",
  ``!s t. FINITE s /\ FINITE t /\ DISJOINT s t ==> !f. SIGMA f (s UNION t) = SIGMA f s + SIGMA f t``,
  rw_tac std_ss[SUM_IMAGE_UNION, DISJOINT_DEF, SUM_IMAGE_EMPTY]);

(* Theorem: FINITE s /\ s <> {} ==> !f g. (!x. x IN s ==> f x < g x) ==> SIGMA f s < SIGMA g s *)
(* Proof:
   Note s <> {} ==> ?x. x IN s       by MEMBER_NOT_EMPTY
   Thus ?x. x IN s /\ f x < g x      by implication
    and !x. x IN s ==> f x <= g x    by LESS_IMP_LESS_OR_EQ
    ==> SIGMA f s < SIGMA g s        by SUM_IMAGE_MONO_LESS
*)
val SUM_IMAGE_MONO_LT = store_thm(
  "SUM_IMAGE_MONO_LT",
  ``!s. FINITE s /\ s <> {} ==> !f g. (!x. x IN s ==> f x < g x) ==> SIGMA f s < SIGMA g s``,
  metis_tac[SUM_IMAGE_MONO_LESS, LESS_IMP_LESS_OR_EQ, MEMBER_NOT_EMPTY]);

(* Theorem: FINITE s /\ t PSUBSET s /\ (!x. x IN s ==> f x <> 0) ==> SIGMA f t < SIGMA f s *)
(* Proof:
   Note t SUBSET s /\ t <> s      by PSUBSET_DEF
   Thus SIGMA f t <= SIGMA f s    by SUM_IMAGE_SUBSET_LE
   By contradiction, suppose ~(SIGMA f t < SIGMA f s).
   Then SIGMA f t = SIGMA f s     by arithmetic [1]

   Let u = s DIFF t.
   Then DISJOINT u t                        by DISJOINT_DIFF
    and u UNION t = s                       by UNION_DIFF
   Note FINITE u /\ FINITE t                by FINITE_UNION
    ==> SIGMA f s = SIGMA f u + SIGMA f t   by SUM_IMAGE_DISJOINT
   Thus SIGMA f u = 0                       by arithmetic, [1]

    Now u SUBSET s                          by SUBSET_UNION
    and u <> {}                             by finite_partition_property, t <> s
   Thus ?x. x IN u                          by MEMBER_NOT_EMPTY
    and f x <> 0                            by SUBSET_DEF, implication
   This contradicts f x = 0                 by SUM_IMAGE_ZERO
*)
val SUM_IMAGE_PSUBSET_LT = store_thm(
  "SUM_IMAGE_PSUBSET_LT",
  ``!f s t. FINITE s /\ t PSUBSET s /\ (!x. x IN s ==> f x <> 0) ==> SIGMA f t < SIGMA f s``,
  rw[PSUBSET_DEF] >>
  `SIGMA f t <= SIGMA f s` by rw[SUM_IMAGE_SUBSET_LE] >>
  spose_not_then strip_assume_tac >>
  `SIGMA f t = SIGMA f s` by decide_tac >>
  qabbrev_tac `u = s DIFF t` >>
  `DISJOINT u t` by rw[DISJOINT_DIFF, Abbr`u`] >>
  `u UNION t = s` by rw[UNION_DIFF, Abbr`u`] >>
  `FINITE u /\ FINITE t` by metis_tac[FINITE_UNION] >>
  `SIGMA f s = SIGMA f u + SIGMA f t` by rw[GSYM SUM_IMAGE_DISJOINT] >>
  `SIGMA f u = 0` by decide_tac >>
  `u SUBSET s` by rw[] >>
  `u <> {}` by metis_tac[finite_partition_property] >>
  metis_tac[SUM_IMAGE_ZERO, SUBSET_DEF, MEMBER_NOT_EMPTY]);


(* Theorem: PI f {} = 1 *)
(* Proof: by PROD_IMAGE_THM *)
val PROD_IMAGE_EMPTY = store_thm(
  "PROD_IMAGE_EMPTY",
  ``!f. PI f {} = 1``,
  rw[PROD_IMAGE_THM]);

(* Theorem: FINITE s ==> !f e. e NOTIN s ==> (PI f (e INSERT s) = (f e) * PI f s) *)
(* Proof: by PROD_IMAGE_THM, DELETE_NON_ELEMENT *)
val PROD_IMAGE_INSERT = store_thm(
  "PROD_IMAGE_INSERT",
  ``!s. FINITE s ==> !f e. e NOTIN s ==> (PI f (e INSERT s) = (f e) * PI f s)``,
  rw[PROD_IMAGE_THM, DELETE_NON_ELEMENT]);

(* Theorem: FINITE s ==> !f e. 0 < f e ==>
            (PI f (s DELETE e) = if e IN s then ((PI f s) DIV (f e)) else PI f s) *)
(* Proof:
   If e IN s,
     Note PI f (e INSERT s) = (f e) *  PI f (s DELETE e)   by PROD_IMAGE_THM
     Thus PI f (s DELETE e) = PI f (e INSERT s) DIV (f e)  by DIV_SOLVE_COMM, 0 < f e
                            = (PI f s) DIV (f e)           by ABSORPTION, e IN s.
   If e NOTIN s,
      PI f (s DELETE e) = PI f e                           by DELETE_NON_ELEMENT
*)
val PROD_IMAGE_DELETE = store_thm(
  "PROD_IMAGE_DELETE",
  ``!s. FINITE s ==> !f e. 0 < f e ==>
       (PI f (s DELETE e) = if e IN s then ((PI f s) DIV (f e)) else PI f s)``,
  rpt strip_tac >>
  rw_tac std_ss[] >-
  metis_tac[PROD_IMAGE_THM, DIV_SOLVE_COMM, ABSORPTION] >>
  metis_tac[DELETE_NON_ELEMENT]);
(* The original proof of SUM_IMAGE_DELETE is clumsy. *)

(* Theorem: (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s) *)
(* Proof:
   If INFINITE s,
        PI f1 s
      = ITSET (\e acc. f e * acc) s 1    by PROD_IMAGE_DEF
      = ARB                              by ITSET_def
      Similarly, PI f2 s = ARB = PI f1 s.
   If FINITE s,
      Apply finite induction on s.
      Base: PI f1 {} = PI f2 {}, true     by PROD_IMAGE_EMPTY
      Step: !f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s) ==>
            e NOTIN s /\ !x. x IN e INSERT s ==> (f1 x = f2 x) ==> PI f1 (e INSERT s) = PI f2 (e INSERT s)
            Note !x. x IN e INSERT s ==> (f1 x = f2 x)
             ==> (f1 e = f2 e) \/ !x. s IN s ==> (f1 x = f2 x)   by IN_INSERT
              PI f1 (e INSERT s)
            = (f1 e) * (PI f1 s)    by PROD_IMAGE_INSERT, e NOTIN s
            = (f1 e) * (PI f2 s)    by induction hypothesis
            = (f2 e) * (PI f2 s)    by f1 e = f2 e
            = PI f2 (e INSERT s)    by PROD_IMAGE_INSERT, e NOTIN s
*)
val PROD_IMAGE_CONG = store_thm(
  "PROD_IMAGE_CONG",
  ``!s f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s)``,
  rpt strip_tac >>
  reverse (Cases_on `FINITE s`) >| [
    rw[PROD_IMAGE_DEF, Once ITSET_def] >>
    rw[Once ITSET_def],
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    qid_spec_tac `s` >>
    `!s. FINITE s ==> !f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s)` suffices_by rw[] >>
    Induct_on `FINITE` >>
    rpt strip_tac >-
    rw[PROD_IMAGE_EMPTY] >>
    metis_tac[PROD_IMAGE_INSERT, IN_INSERT]
  ]);
(* proof like SUM_IMAGE_CONG *)
val PROD_IMAGE_CONG = Q.store_thm(
   "PROD_IMAGE_CONG",
   `!s f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s)`,
   SRW_TAC [][] THEN
   REVERSE (Cases_on `FINITE s`) THEN1 (
       SRW_TAC [][PROD_IMAGE_DEF, Once ITSET_def] THEN
       SRW_TAC [][Once ITSET_def]
   ) THEN
   Q.PAT_ASSUM `!x. P` MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   Q.ID_SPEC_TAC `s` THEN
   HO_MATCH_MP_TAC FINITE_INDUCT THEN
   METIS_TAC [PROD_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT]
);

(* Theorem: FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (PI f s = k ** CARD s) *)
(* Proof:
   By finite induction on s.
   Base: PI f {} = k ** CARD {}
         PI f {}
       = 1               by PROD_IMAGE_THM
       = c ** 0          by EXP
       = c ** CARD {}    by CARD_DEF
   Step: !f k. (!x. x IN s ==> (f x = k)) ==> (PI f s = k ** CARD s) ==>
         e NOTIN s ==> PI f (e INSERT s) = k ** CARD (e INSERT s)
         PI f (e INSERT s)
       = ((f e) * PI (K c) (s DELETE e)    by PROD_IMAGE_THM
       = c * PI (K c) (s DELETE e)         by function application
       = c * PI (K c) s                    by DELETE_NON_ELEMENT
       = c * c ** CARD s                   by induction hypothesis
       = c ** (SUC (CARD s))               by EXP
       = c ** CARD (e INSERT s)            by CARD_INSERT, e NOTIN s
*)
val PI_CONSTANT = store_thm(
  "PI_CONSTANT",
  ``!s. FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (PI f s = k ** CARD s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_IMAGE_THM] >>
  rw[PROD_IMAGE_THM, CARD_INSERT] >>
  fs[] >>
  metis_tac[DELETE_NON_ELEMENT, EXP]);

(* Theorem: FINITE s ==> !c. PI (K c) s = c ** (CARD s) *)
(* Proof: by PI_CONSTANT. *)
val PROD_IMAGE_CONSTANT = store_thm(
  "PROD_IMAGE_CONSTANT",
  ``!s. FINITE s ==> !c. PI (K c) s = c ** (CARD s)``,
  rw[PI_CONSTANT]);

(* ------------------------------------------------------------------------- *)
(* SUM_SET and PROD_SET Theorems                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s /\ x NOTIN s ==> (SUM_SET (x INSERT s) = x + SUM_SET s) *)
(* Proof:
     SUM_SET (x INSERT s)
   = x + SUM_SET (s DELETE x)  by SUM_SET_THM
   = x + SUM_SET s             by DELETE_NON_ELEMENT
*)
val SUM_SET_INSERT = store_thm(
  "SUM_SET_INSERT",
  ``!s x. FINITE s /\ x NOTIN s ==> (SUM_SET (x INSERT s) = x + SUM_SET s)``,
  rw[SUM_SET_THM, DELETE_NON_ELEMENT]);

(* Theorem: FINITE s ==> !f. INJ f s UNIV ==> (SUM_SET (IMAGE f s) = SIGMA f s) *)
(* Proof:
   By finite induction on s.
   Base: SUM_SET (IMAGE f {}) = SIGMA f {}
         SUM_SET (IMAGE f {})
       = SUM_SET {}                  by IMAGE_EMPTY
       = 1                           by SUM_SET_EMPTY
       = SIGMA f {}                  by SUM_IMAGE_EMPTY
   Step: !f. INJ f s univ(:num) ==> (SUM_SET (IMAGE f s) = SIGMA f s) ==>
         e NOTIN s /\ INJ f (e INSERT s) univ(:num) ==> SUM_SET (IMAGE f (e INSERT s)) = SIGMA f (e INSERT s)
       Note INJ f s univ(:num)               by INJ_INSERT
        and f e NOTIN (IMAGE f s)            by IN_IMAGE
         SUM_SET (IMAGE f (e INSERT s))
       = SUM_SET (f e INSERT (IMAGE f s))    by IMAGE_INSERT
       = f e * SUM_SET (IMAGE f s)           by SUM_SET_INSERT
       = f e * SIGMA f s                     by induction hypothesis
       = SIGMA f (e INSERT s)                by SUM_IMAGE_INSERT
*)
val SUM_SET_IMAGE_EQN = store_thm(
  "SUM_SET_IMAGE_EQN",
  ``!s. FINITE s ==> !f. INJ f s UNIV ==> (SUM_SET (IMAGE f s) = SIGMA f s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[SUM_SET_EMPTY, SUM_IMAGE_EMPTY] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  rw[SUM_SET_INSERT, SUM_IMAGE_INSERT]);

(* Theorem: SUM_SET (count n) = (n * (n - 1)) DIV 2*)
(* Proof:
   By induction on n.
   Base case: SUM_SET (count 0) = 0 * (0 - 1) DIV 2
     LHS = SUM_SET (count 0)
         = SUM_SET {}           by COUNT_ZERO
         = 0                    by SUM_SET_THM
         = 0 DIV 2              by ZERO_DIV
         = 0 * (0 - 1) DIV 2    by MULT
         = RHS
   Step case: SUM_SET (count n) = n * (n - 1) DIV 2 ==>
              SUM_SET (count (SUC n)) = SUC n * (SUC n - 1) DIV 2
     If n = 0, to show: SUM_SET (count 1) = 0
        SUM_SET (count 1) = SUM_SET {0} = 0  by SUM_SET_SING
     If n <> 0, 0 < n.
     First, FINITE (count n)               by FINITE_COUNT
            n NOTIN (count n)              by IN_COUNT
     LHS = SUM_SET (count (SUC n))
         = SUM_SET (n INSERT count n)      by COUNT_SUC
         = n + SUM_SET (count n DELETE n)  by SUM_SET_THM
         = n + SUM_SET (count n)           by DELETE_NON_ELEMENT
         = n + n * (n - 1) DIV 2           by induction hypothesis
         = (n * 2 + n * (n - 1)) DIV 2     by ADD_DIV_ADD_DIV
         = (n * (2 + (n - 1))) DIV 2       by LEFT_ADD_DISTRIB
         = n * (n + 1) DIV 2               by arithmetic, 0 < n
         = (SUC n - 1) * (SUC n) DIV 2     by ADD1, SUC_SUB1
         = SUC n * (SUC n - 1) DIV 2       by MULT_COMM
         = RHS
*)
val SUM_SET_COUNT = store_thm(
  "SUM_SET_COUNT",
  ``!n. SUM_SET (count n) = (n * (n - 1)) DIV 2``,
  Induct_on `n` >-
  rw[] >>
  Cases_on `n = 0` >| [
    rw[] >>
    EVAL_TAC,
    `0 < n` by decide_tac >>
    `FINITE (count n)` by rw[] >>
    `n NOTIN (count n)` by rw[] >>
    `SUM_SET (count (SUC n)) = SUM_SET (n INSERT count n)` by rw[COUNT_SUC] >>
    `_ = n + SUM_SET (count n DELETE n)` by rw[SUM_SET_THM] >>
    `_ = n + SUM_SET (count n)` by metis_tac[DELETE_NON_ELEMENT] >>
    `_ = n + n * (n - 1) DIV 2` by rw[] >>
    `_ = (n * 2 + n * (n - 1)) DIV 2` by rw[ADD_DIV_ADD_DIV] >>
    `_ = (n * (2 + (n - 1))) DIV 2` by rw[LEFT_ADD_DISTRIB] >>
    `_ = n * (n + 1) DIV 2` by rw_tac arith_ss[] >>
    `_ = (SUC n - 1) * SUC n DIV 2` by rw[ADD1, SUC_SUB1] >>
    `_ = SUC n * (SUC n - 1) DIV 2 ` by rw[MULT_COMM] >>
    decide_tac
  ]);

(* Theorem: PROD_SET {x} = x *)
(* Proof:
   Since FINITE {x}           by FINITE_SING
     PROD_SET {x}
   = PROD_SET (x INSERT {})   by SING_INSERT
   = x * PROD_SET {}          by PROD_SET_THM
   = x                        by PROD_SET_EMPTY
*)
val PROD_SET_SING = store_thm(
  "PROD_SET_SING",
  ``!x. PROD_SET {x} = x``,
  rw[PROD_SET_THM, FINITE_SING]);

(* Theorem: FINITE s /\ 0 NOTIN s ==> 0 < PROD_SET s *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: 0 NOTIN {} ==> 0 < PROD_SET {}
     Since PROD_SET {} = 1        by PROD_SET_THM
     Hence true.
   Step case: 0 NOTIN s ==> 0 < PROD_SET s ==>
              e NOTIN s /\ 0 NOTIN e INSERT s ==> 0 < PROD_SET (e INSERT s)
       PROD_SET (e INSERT s)
     = e * PROD_SET (s DELETE e)          by PROD_SET_THM
     = e * PROD_SET s                     by DELETE_NON_ELEMENT
     But e IN e INSERT s                  by COMPONENT
     Hence e <> 0, or 0 < e               by implication
     and !x. x IN s ==> x IN (e INSERT s) by IN_INSERT
     Thus 0 < PROD_SET s                  by induction hypothesis
     Henec 0 < e * PROD_SET s             by ZERO_LESS_MULT
*)
val PROD_SET_NONZERO = store_thm(
  "PROD_SET_NONZERO",
  ``!s. FINITE s /\ 0 NOTIN s ==> 0 < PROD_SET s``,
  `!s. FINITE s ==> 0 NOTIN s ==> 0 < PROD_SET s` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[PROD_SET_THM] >>
  fs[] >>
  `0 < e` by decide_tac >>
  `PROD_SET (e INSERT s) = e * PROD_SET (s DELETE e)` by rw[PROD_SET_THM] >>
  `_ = e * PROD_SET s` by metis_tac[DELETE_NON_ELEMENT] >>
  rw[ZERO_LESS_MULT]);

(* Theorem: FINITE s /\ s <> {} /\ 0 NOTIN s ==>
            !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s) *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: {} <> {} ==> PROD_SET {} < PROD_SET (IMAGE f {})
     True since {} <> {} is false.
   Step case: s <> {} /\ 0 NOTIN s ==> !f. INJ f s univ(:num) ==> PROD_SET s < PROD_SET (IMAGE f s) ==>
              e NOTIN s /\ e INSERT s <> {} /\ 0 NOTIN e INSERT s /\ INJ f (e INSERT s) univ(:num) ==>
              PROD_SET (e INSERT s) < PROD_SET (IMAGE f (e INSERT s))
     Note INJ f (e INSERT s) univ(:num)
      ==> INJ f s univ(:num) /\
          !y. y IN s /\ (f e = f y) ==> (e = y)   by INJ_INSERT
     First,
       PROD_SET (e INSERT s)
     = e * PROD_SET (s DELETE e)           by PROD_SET_THM
     = e * PROD_SET s                      by DELETE_NON_ELEMENT
     Next,
       FINITE (IMAGE f s)                  by IMAGE_FINITE
       f e NOTIN IMAGE f s                 by IN_IMAGE, e NOTIN s
       PROD_SET (IMAGE f (e INSERT s))
     = f e * PROD_SET (IMAGE f s)          by PROD_SET_IMAGE_REDUCTION

     If s = {},
        to show: e * PROD_SET {} < f e * PROD_SET {}    by IMAGE_EMPTY
        which is true since PROD_SET {} = 1             by PROD_SET_THM
             and e < f e                                by given
     If s <> {},
     Since e IN e INSERT s                              by COMPONENT
     Hence 0 < e                                        by e <> 0
     and !x. x IN s ==> x IN (e INSERT s)               by IN_INSERT
     Thus PROD_SET s < PROD_SET (IMAGE f s)             by induction hypothesis
       or e * PROD_SET s < e * PROD_SET (IMAGE f s)     by LT_MULT_LCANCEL, 0 < e
     Note 0 < PROD_SET (IMAGE f s)                      by IN_IMAGE, !x. x < f x /\ x <> 0
       so e * PROD_SET (IMAGE f s) < f e * PROD_SET (IMAGE f s) by LT_MULT_LCANCEL, e < f e
     Hence PROD_SET (e INSERT s) < PROD_SET (IMAGE f (e INSERT s))
*)
val PROD_SET_LESS = store_thm(
  "PROD_SET_LESS",
  ``!s. FINITE s /\ s <> {} /\ 0 NOTIN s ==>
   !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s)``,
  `!s. FINITE s ==> s <> {} /\ 0 NOTIN s ==>
    !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  `PROD_SET (e INSERT s) = e * PROD_SET (s DELETE e)` by rw[PROD_SET_THM] >>
  `_ = e * PROD_SET s` by metis_tac[DELETE_NON_ELEMENT] >>
  fs[INJ_INSERT] >>
  `FINITE (IMAGE f s)` by rw[] >>
  `f e NOTIN IMAGE f s` by metis_tac[IN_IMAGE] >>
  `PROD_SET (IMAGE f (e INSERT s)) = f e * PROD_SET (IMAGE f s)` by rw[PROD_SET_IMAGE_REDUCTION] >>
  Cases_on `s = {}` >-
  rw[PROD_SET_SING, PROD_SET_THM] >>
  `0 < e` by decide_tac >>
  `PROD_SET s < PROD_SET (IMAGE f s)` by rw[] >>
  `e * PROD_SET s < e * PROD_SET (IMAGE f s)` by rw[] >>
  `e * PROD_SET (IMAGE f s) < (f e) * PROD_SET (IMAGE f s)` by rw[] >>
  `(IMAGE f (e INSERT s)) = (f e INSERT IMAGE f s)` by rw[] >>
  metis_tac[LESS_TRANS]);

(* Theorem: FINITE s /\ s <> {} /\ 0 NOTIN s ==> PROD_SET s < PROD_SET (IMAGE SUC s) *)
(* Proof:
   Since !m n. SUC m = SUC n <=> m = n      by INV_SUC
    thus INJ INJ SUC s univ(:num)           by INJ_DEF
   Hence the result follows                 by PROD_SET_LESS
*)
val PROD_SET_LESS_SUC = store_thm(
  "PROD_SET_LESS_SUC",
  ``!s. FINITE s /\ s <> {} /\ 0 NOTIN s ==> PROD_SET s < PROD_SET (IMAGE SUC s)``,
  rpt strip_tac >>
  (irule PROD_SET_LESS >> simp[]) >>
  rw[INJ_DEF]);

(* Theorem: FINITE s ==> !n x. x IN s /\ n divides x ==> n divides (PROD_SET s) *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: x IN {} /\ n divides x ==> n divides (PROD_SET {})
     True since x IN {} is false   by NOT_IN_EMPTY
   Step case: !n x. x IN s /\ n divides x ==> n divides (PROD_SET s) ==>
              e NOTIN s /\ x IN e INSERT s /\ n divides x ==> n divides (PROD_SET (e INSERT s))
       PROD_SET (e INSERT s)
     = e * PROD_SET (s DELETE e)   by PROD_SET_THM
     = e * PROD_SET s              by DELETE_NON_ELEMENT
     If x = e,
        n divides x
        means n divides e
        hence n divides PROD_SET (e INSERT s)   by DIVIDES_MULTIPLE, MULT_COMM
     If x <> e, x IN s             by IN_INSERT
        n divides (PROD_SET s)     by induction hypothesis
        hence n divides PROD_SET (e INSERT s)   by DIVIDES_MULTIPLE
*)
val PROD_SET_DIVISORS = store_thm(
  "PROD_SET_DIVISORS",
  ``!s. FINITE s ==> !n x. x IN s /\ n divides x ==> n divides (PROD_SET s)``,
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  metis_tac[NOT_IN_EMPTY] >>
  `PROD_SET (e INSERT s) = e * PROD_SET (s DELETE e)` by rw[PROD_SET_THM] >>
  `_ = e * PROD_SET s` by metis_tac[DELETE_NON_ELEMENT] >>
  `(x = e) \/ (x IN s)` by rw[GSYM IN_INSERT] >-
  metis_tac[DIVIDES_MULTIPLE, MULT_COMM] >>
  metis_tac[DIVIDES_MULTIPLE]);

(* PROD_SET_IMAGE_REDUCTION |> ISPEC ``I:num -> num``; *)

(* Theorem: FINITE s /\ x NOTIN s ==> (PROD_SET (x INSERT s) = x * PROD_SET s) *)
(* Proof:
   Since !x. I x = x         by I_THM
     and !s. IMAGE I s = s   by IMAGE_I
    thus the result follows  by PROD_SET_IMAGE_REDUCTION
*)
val PROD_SET_INSERT = store_thm(
  "PROD_SET_INSERT",
  ``!x s. FINITE s /\ x NOTIN s ==> (PROD_SET (x INSERT s) = x * PROD_SET s)``,
  metis_tac[PROD_SET_IMAGE_REDUCTION, combinTheory.I_THM, IMAGE_I]);

(* Theorem: FINITE s ==> !f. INJ f s UNIV ==> (PROD_SET (IMAGE f s) = PI f s) *)
(* Proof:
   By finite induction on s.
   Base: PROD_SET (IMAGE f {}) = PI f {}
         PROD_SET (IMAGE f {})
       = PROD_SET {}              by IMAGE_EMPTY
       = 1                        by PROD_SET_EMPTY
       = PI f {}                  by PROD_IMAGE_EMPTY
   Step: !f. INJ f s univ(:num) ==> (PROD_SET (IMAGE f s) = PI f s) ==>
         e NOTIN s /\ INJ f (e INSERT s) univ(:num) ==> PROD_SET (IMAGE f (e INSERT s)) = PI f (e INSERT s)
       Note INJ f s univ(:num)               by INJ_INSERT
        and f e NOTIN (IMAGE f s)            by IN_IMAGE
         PROD_SET (IMAGE f (e INSERT s))
       = PROD_SET (f e INSERT (IMAGE f s))   by IMAGE_INSERT
       = f e * PROD_SET (IMAGE f s)          by PROD_SET_INSERT
       = f e * PI f s                        by induction hypothesis
       = PI f (e INSERT s)                   by PROD_IMAGE_INSERT
*)
val PROD_SET_IMAGE_EQN = store_thm(
  "PROD_SET_IMAGE_EQN",
  ``!s. FINITE s ==> !f. INJ f s UNIV ==> (PROD_SET (IMAGE f s) = PI f s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY, PROD_IMAGE_EMPTY] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  rw[PROD_SET_INSERT, PROD_IMAGE_INSERT]);

(* Theorem: PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** (SUM_SET (count m)) *)
(* Proof:
   By induction on m.
   Base case: PROD_SET (IMAGE (\j. n ** j) (count 0)) = n ** SUM_SET (count 0)
     LHS = PROD_SET (IMAGE (\j. n ** j) (count 0))
         = PROD_SET (IMAGE (\j. n ** j) {})          by COUNT_ZERO
         = PROD_SET {}                               by IMAGE_EMPTY
         = 1                                         by PROD_SET_THM
     RHS = n ** SUM_SET (count 0)
         = n ** SUM_SET {}                           by COUNT_ZERO
         = n ** 0                                    by SUM_SET_THM
         = 1                                         by EXP
         = LHS
   Step case: PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** SUM_SET (count m) ==>
              PROD_SET (IMAGE (\j. n ** j) (count (SUC m))) = n ** SUM_SET (count (SUC m))
     First,
          FINITE (count m)                                   by FINITE_COUNT
          FINITE (IMAGE (\j. n ** j) (count m))              by IMAGE_FINITE
          m NOTIN count m                                    by IN_COUNT
     and  (\j. n ** j) m NOTIN IMAGE (\j. n ** j) (count m)  by EXP_BASE_INJECTIVE, 1 < n

     LHS = PROD_SET (IMAGE (\j. n ** j) (count (SUC m)))
         = PROD_SET (IMAGE (\j. n ** j) (m INSERT count m))  by COUNT_SUC
         = n ** m * PROD_SET (IMAGE (\j. n ** j) (count m))  by PROD_SET_IMAGE_REDUCTION
         = n ** m * n ** SUM_SET (count m)                   by induction hypothesis
         = n ** (m + SUM_SET (count m))                      by EXP_ADD
         = n ** SUM_SET (m INSERT count m)                   by SUM_SET_INSERT
         = n ** SUM_SET (count (SUC m))                      by COUNT_SUC
         = RHS
*)
val PROD_SET_IMAGE_EXP = store_thm(
  "PROD_SET_IMAGE_EXP",
  ``!n. 1 < n ==> !m. PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** (SUM_SET (count m))``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[PROD_SET_THM] >>
  `FINITE (IMAGE (\j. n ** j) (count m))` by rw[] >>
  `(\j. n ** j) m NOTIN IMAGE (\j. n ** j) (count m)` by rw[] >>
  `m NOTIN count m` by rw[] >>
  `PROD_SET (IMAGE (\j. n ** j) (count (SUC m))) =
    PROD_SET (IMAGE (\j. n ** j) (m INSERT count m))` by rw[COUNT_SUC] >>
  `_ = n ** m * PROD_SET (IMAGE (\j. n ** j) (count m))` by rw[PROD_SET_IMAGE_REDUCTION] >>
  `_ = n ** m * n ** SUM_SET (count m)` by rw[] >>
  `_ = n ** (m + SUM_SET (count m))` by rw[EXP_ADD] >>
  `_ = n ** SUM_SET (m INSERT count m)` by rw[SUM_SET_INSERT] >>
  `_ = n ** SUM_SET (count (SUC m))` by rw[COUNT_SUC] >>
  decide_tac);

(* Theorem: FINITE s /\ x IN s ==> x divides PROD_SET s *)
(* Proof:
   Note !n x. x IN s /\ n divides x
    ==> n divides PROD_SET s           by PROD_SET_DIVISORS
    Put n = x, and x divides x = T     by DIVIDES_REFL
    and the result follows.
*)
val PROD_SET_ELEMENT_DIVIDES = store_thm(
  "PROD_SET_ELEMENT_DIVIDES",
  ``!s x. FINITE s /\ x IN s ==> x divides PROD_SET s``,
  metis_tac[PROD_SET_DIVISORS, DIVIDES_REFL]);

(* Theorem: FINITE s ==> !f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
            (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s) *)
(* Proof:
   By finite induction on s.
   Base: PROD_SET (IMAGE f {}) <= PROD_SET (IMAGE g {})
      Note PROD_SET (IMAGE f {})
         = PROD_SET {}              by IMAGE_EMPTY
         = 1                        by PROD_SET_EMPTY
      Thus true.
   Step: !f g. (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s) ==>
        e NOTIN s /\ !x. x IN e INSERT s ==> f x <= g x ==>
        PROD_SET (IMAGE f (e INSERT s)) <= PROD_SET (IMAGE g (e INSERT s))
        Note INJ f s univ(:num)     by INJ_INSERT
         and INJ g s univ(:num)     by INJ_INSERT
         and f e NOTIN (IMAGE f s)  by IN_IMAGE
         and g e NOTIN (IMAGE g s)  by IN_IMAGE
       Applying LE_MONO_MULT2,
          PROD_SET (IMAGE f (e INSERT s))
        = PROD_SET (f e INSERT IMAGE f s)  by INSERT_IMAGE
        = f e * PROD_SET (IMAGE f s)       by PROD_SET_INSERT
       <= g e * PROD_SET (IMAGE f s)       by f e <= g e
       <= g e * PROD_SET (IMAGE g s)       by induction hypothesis
        = PROD_SET (g e INSERT IMAGE g s)  by PROD_SET_INSERT
        = PROD_SET (IMAGE g (e INSERT s))  by INSERT_IMAGE
*)
val PROD_SET_LESS_EQ = store_thm(
  "PROD_SET_LESS_EQ",
  ``!s. FINITE s ==> !f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
       (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  `g e NOTIN (IMAGE g s)` by metis_tac[IN_IMAGE] >>
  `f e <= g e` by rw[] >>
  `PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s)` by rw[] >>
  rw[PROD_SET_INSERT, LE_MONO_MULT2]);

(* Theorem: FINITE s ==> !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s *)
(* Proof:
   By finite induction on s.
   Base: PROD_SET {} <= n ** CARD {}
      Note PROD_SET {}
         = 1             by PROD_SET_EMPTY
         = n ** 0        by EXP_0
         = n ** CARD {}  by CARD_EMPTY
   Step: !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> x <= n ==> PROD_SET (e INSERT s) <= n ** CARD (e INSERT s)
      Note !x. (x = e) \/ x IN s ==> x <= n   by IN_INSERT
         PROD_SET (e INSERT s)
       = e * PROD_SET s          by PROD_SET_INSERT
      <= n * PROD_SET s          by e <= n
      <= n * (n ** CARD s)       by induction hypothesis
       = n ** (SUC (CARD s))     by EXP
       = n ** CARD (e INSERT s)  by CARD_INSERT, e NOTIN s
*)
val PROD_SET_LE_CONSTANT = store_thm(
  "PROD_SET_LE_CONSTANT",
  ``!s. FINITE s ==> !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY, EXP_0] >>
  fs[] >>
  `e <= n /\ PROD_SET s <= n ** CARD s` by rw[] >>
  rw[PROD_SET_INSERT, EXP, CARD_INSERT, LE_MONO_MULT2]);

(* Theorem: FINITE s ==> !n f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\ (!x. x IN s ==> n <= f x * g x) ==>
            n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s) *)
(* Proof:
   By finite induction on s.
   Base: n ** CARD {} <= PROD_SET (IMAGE f {}) * PROD_SET (IMAGE g {})
      Note n ** CARD {}
         = n ** 0           by CARD_EMPTY
         = 1                by EXP_0
       and PROD_SET (IMAGE f {})
         = PROD_SET {}      by IMAGE_EMPTY
         = 1                by PROD_SET_EMPTY
   Step: !n f. INJ f s univ(:num) /\ INJ g s univ(:num) /\
               (!x. x IN s ==> n <= f x * g x) ==>
               n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s) ==>
         e NOTIN s /\ INJ f (e INSERT s) univ(:num) /\ INJ g (e INSERT s) univ(:num) /\
         !x. x IN e INSERT s ==> n <= f x * g x ==>
         n ** CARD (e INSERT s) <= PROD_SET (IMAGE f (e INSERT s)) * PROD_SET (IMAGE g (e INSERT s))
      Note INJ f s univ(:num) /\ INJ g s univ(:num)         by INJ_INSERT
       and f e NOTIN (IMAGE f s) /\ g e NOTIN (IMAGE g s)   by IN_IMAGE
         PROD_SET (IMAGE f (e INSERT s)) * PROD_SET (IMAGE g (e INSERT s))
       = PROD_SET (f e INSERT (IMAGE f s)) * PROD_SET (g e INSERT (IMAGE g s))   by INSERT_IMAGE
       = (f e * PROD_SET (IMAGE f s)) * (g e * PROD_SET (IMAGE g s))    by PROD_SET_INSERT
       = (f e * g e) * (PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s))    by MULT_ASSOC, MULT_COMM
       >= n        * (PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s))      by n <= f e * g e
       >= n        * n ** CARD s                                        by induction hypothesis
        = n ** (SUC (CARD s))                               by EXP
        = n ** (CARD (e INSERT s))                          by CARD_INSERT
*)
val PROD_SET_PRODUCT_GE_CONSTANT = store_thm(
  "PROD_SET_PRODUCT_GE_CONSTANT",
  ``!s. FINITE s ==> !n f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\ (!x. x IN s ==> n <= f x * g x) ==>
       n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY, EXP_0] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s) /\ g e NOTIN (IMAGE g s)` by metis_tac[IN_IMAGE] >>
  `n <= f e * g e /\ n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s)` by rw[] >>
  `PROD_SET (f e INSERT IMAGE f s) * PROD_SET (g e INSERT IMAGE g s) =
    (f e * PROD_SET (IMAGE f s)) * (g e * PROD_SET (IMAGE g s))` by rw[PROD_SET_INSERT] >>
  `_ = (f e * g e) * (PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[EXP, CARD_INSERT, LE_MONO_MULT2]);

(* Theorem: FINITE s ==> !u v. s =|= u # v ==> (PROD_SET s = PROD_SET u * PROD_SET v) *)
(* Proof:
   By finite induction on s.
   Base: {} = u UNION v ==> PROD_SET {} = PROD_SET u * PROD_SET v
      Note u = {} and v = {}       by EMPTY_UNION
       and PROD_SET {} = 1         by PROD_SET_EMPTY
      Hence true.
   Step: !u v. (s = u UNION v) /\ DISJOINT u v ==> (PROD_SET s = PROD_SET u * PROD_SET v) ==>
         e NOTIN s /\ e INSERT s = u UNION v ==> PROD_SET (e INSERT s) = PROD_SET u * PROD_SET v
      Note e IN u \/ e IN v        by IN_INSERT, IN_UNION
      If e IN u,
         Then e NOTIN v            by IN_DISJOINT
         Let w = u DELETE e.
         Then e NOTIN w            by IN_DELETE
          and u = e INSERT w       by INSERT_DELETE
         Note s = w UNION v        by EXTENSION, IN_INSERT, IN_UNION
          ==> FINITE w             by FINITE_UNION
          and DISJOINT w v         by DISJOINT_INSERT
        PROD_SET (e INSERT s)
      = e * PROD_SET s                       by PROD_SET_INSERT, FINITE s
      = e * (PROD_SET w * PROD_SET v)        by induction hypothesis
      = (e * PROD_SET w) * PROD_SET v        by MULT_ASSOC
      = PROD_SET (e INSERT w) * PROD_SET v   by PROD_SET_INSERT, FINITE w
      = PROD_SET u * PROD_SET v

      Similarly for e IN v.
*)
val PROD_SET_PRODUCT_BY_PARTITION = store_thm(
  "PROD_SET_PRODUCT_BY_PARTITION",
  ``!s. FINITE s ==> !u v. s =|= u # v ==> (PROD_SET s = PROD_SET u * PROD_SET v)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  fs[PROD_SET_EMPTY] >>
  `e IN u \/ e IN v` by metis_tac[IN_INSERT, IN_UNION] >| [
    qabbrev_tac `w = u DELETE e` >>
    `u = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN v` by metis_tac[IN_DISJOINT] >>
    `s = w UNION v` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT w v` by metis_tac[DISJOINT_INSERT] >>
    `PROD_SET (e INSERT s) = e * PROD_SET s` by rw[PROD_SET_INSERT] >>
    `_ = e * (PROD_SET w * PROD_SET v)` by rw[] >>
    `_ = (e * PROD_SET w) * PROD_SET v` by rw[] >>
    `_ = PROD_SET u * PROD_SET v` by rw[PROD_SET_INSERT] >>
    rw[],
    qabbrev_tac `w = v DELETE e` >>
    `v = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN u` by metis_tac[IN_DISJOINT] >>
    `s = u UNION w` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT u w` by metis_tac[DISJOINT_INSERT, DISJOINT_SYM] >>
    `PROD_SET (e INSERT s) = e * PROD_SET s` by rw[PROD_SET_INSERT] >>
    `_ = e * (PROD_SET u * PROD_SET w)` by rw[] >>
    `_ = PROD_SET u * (e * PROD_SET w)` by rw[] >>
    `_ = PROD_SET u * PROD_SET v` by rw[PROD_SET_INSERT] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Partition and Equivalent Class                                            *)
(* ------------------------------------------------------------------------- *)

(* Overload equivalence class of a relation *)
val _ = overload_on("equiv_class", ``\R s x. {y | y IN s /\ R x y}``);

(* Theorem: y IN equiv_class R s x <=> y IN s /\ R x y *)
(* Proof: by GSPECIFICATION *)
val equiv_class_element = store_thm(
  "equiv_class_element",
  ``!R s x y. y IN equiv_class R s x <=> y IN s /\ R x y``,
  rw[]);

(* Theorem: R equiv_on s /\ x IN s /\ y IN s ==>
            ((equiv_class R s x = equiv_class R s y) <=> R x y) *)
(* Proof: by equiv_on_def, EXTENSION. *)
Theorem equiv_class_eq:
  !R s x y. R equiv_on s /\ x IN s /\ y IN s ==>
             ((equiv_class R s x = equiv_class R s y) <=> R x y)
Proof
  rw[equiv_on_def, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: R equiv_on s /\ t SUBSET s ==> R equiv_on t *)
(* Proof: by equiv_on_def, SUBSET_DEF *)
val equiv_on_subset = store_thm(
  "equiv_on_subset",
  ``!R s t. R equiv_on s /\ t SUBSET s ==> R equiv_on t``,
  rw_tac std_ss[equiv_on_def, SUBSET_DEF] >>
  metis_tac[]);

(* Theorem: partition R {} = {} *)
(* Proof: by partition_def *)
val partition_on_empty = store_thm(
  "partition_on_empty",
  ``!R. partition R {} = {}``,
  rw[partition_def]);

(*
> partition_def;
val it = |- !R s. partition R s = {t | ?x. x IN s /\ (t = equiv_class R s x)}: thm
*)

(* Theorem: t IN partition R s <=> ?x. x IN s /\ (t = equiv_class R s x) *)
(* Proof: by partition_def *)
Theorem partition_element:
  !R s t. t IN partition R s <=> ?x. x IN s /\ (t = equiv_class R s x)
Proof
  rw[partition_def]
QED

(* Theorem: partition R s = IMAGE (equiv_class R s) s *)
(* Proof:
     partition R s
   = {t | ?x. x IN s /\ (t = {y | y IN s /\ R x y})}   by partition_def
   = {t | ?x. x IN s /\ (t = equiv_class R s x)}       by notation
   = IMAGE (equiv_class R s) s                         by IN_IMAGE
*)
val partition_elements = store_thm(
  "partition_elements",
  ``!R s. partition R s = IMAGE (equiv_class R s) s``,
  rw[partition_def, EXTENSION] >>
  metis_tac[]);

(* Theorem alias *)
val partition_as_image = save_thm("partition_as_image", partition_elements);
(* val partition_as_image =
   |- !R s. partition R s = IMAGE (\x. equiv_class R s x) s: thm *)

(* Theorem: (R1 = R2) /\ (s1 = s2) ==> (partition R1 s1 = partition R2 s2) *)
(* Proof: by identity *)
val partition_cong = store_thm(
  "partition_cong",
  ``!R1 R2 s1 s2. (R1 = R2) /\ (s1 = s2) ==> (partition R1 s1 = partition R2 s2)``,
  rw[]);
(* Just in case this is needed. *)

(* Theorem: When the partitions are equal size of n, CARD s = n * CARD (partition of s).
           FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
           (CARD s = n * CARD (partition R s)) *)
(* Proof:
   Note FINITE (partition R s)               by FINITE_partition
     so CARD s = SIGMA CARD (partition R s)  by partition_CARD
               = n * CARD (partition R s)    by SIGMA_CARD_CONSTANT
*)
val equal_partition_card = store_thm(
  "equal_partition_card",
  ``!R s n. FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
           (CARD s = n * CARD (partition R s))``,
  rw_tac std_ss[partition_CARD, FINITE_partition, GSYM SIGMA_CARD_CONSTANT]);

(* Theorem: When the partitions are equal size of n, CARD s = n * CARD (partition of s).
           FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
           n divides (CARD s) *)
(* Proof: by equal_partition_card, divides_def. *)
Theorem equal_partition_factor:
  !R s n. FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
          n divides (CARD s)
Proof
  metis_tac[equal_partition_card, divides_def, MULT_COMM]
QED

(* Theorem: When the partition size has a factor n, then n divides CARD s.
            FINITE s /\ R equiv_on s /\
            (!e. e IN partition R s ==> n divides (CARD e)) ==> n divides (CARD s)  *)
(* Proof:
   Note FINITE (partition R s)                by FINITE_partition
   Thus CARD s = SIGMA CARD (partition R s)   by partition_CARD
    But !e. e IN partition R s ==> n divides (CARD e)
    ==> n divides SIGMA CARD (partition R s)  by SIGMA_CARD_FACTOR
   Hence n divdes CARD s                      by above
*)
val factor_partition_card = store_thm(
  "factor_partition_card",
  ``!R s n. FINITE s /\ R equiv_on s /\
   (!e. e IN partition R s ==> n divides (CARD e)) ==> n divides (CARD s)``,
  metis_tac[FINITE_partition, partition_CARD, SIGMA_CARD_FACTOR]);

(* Note:
When a set s is partitioned by an equivalence relation R,
partition_CARD  |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
Can this be generalized to:   f s = SIGMA f (partition R s)  ?
If so, we can have         (SIGMA f) s = SIGMA (SIGMA f) (partition R s)
Sort of yes, but have to use BIGUNION, and for a set_additive function f.
*)

(* Overload every element finite of a superset *)
val _ = overload_on("EVERY_FINITE", ``\P. (!s. s IN P ==> FINITE s)``);

(*
> FINITE_BIGUNION;
val it = |- !P. FINITE P /\ EVERY_FINITE P ==> FINITE (BIGUNION P): thm
*)

(* Overload pairwise disjoint of a superset *)
val _ = overload_on("PAIR_DISJOINT", ``\P. (!s t. s IN P /\ t IN P /\ ~(s = t) ==> DISJOINT s t)``);

(*
> partition_elements_disjoint;
val it = |- R equiv_on s ==> PAIR_DISJOINT (partition R s): thm
*)

(* Theorem: t SUBSET s /\ PAIR_DISJOINT s ==> PAIR_DISJOINT t *)
(* Proof: by SUBSET_DEF *)
Theorem pair_disjoint_subset:
  !s t. t SUBSET s /\ PAIR_DISJOINT s ==> PAIR_DISJOINT t
Proof
  rw[SUBSET_DEF]
QED

(* Overload an additive set function *)
val _ = overload_on("SET_ADDITIVE",
   ``\f. (f {} = 0) /\ (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) + f (s INTER t) = f s + f t))``);

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
            !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P) *)
(* Proof:
   By finite induction on P.
   Base: f (BIGUNION {}) = SIGMA f {}
         f (BIGUNION {})
       = f {}                by BIGUNION_EMPTY
       = 0                   by SET_ADDITIVE f
       = SIGMA f {} = RHS    by SUM_IMAGE_EMPTY
   Step: e NOTIN P ==> f (BIGUNION (e INSERT P)) = SIGMA f (e INSERT P)
       Given !s. s IN e INSERT P ==> FINITE s
        thus !s. (s = e) \/ s IN P ==> FINITE s   by IN_INSERT
       hence FINITE e              by implication
         and EVERY_FINITE P        by IN_INSERT
         and FINITE (BIGUNION P)   by FINITE_BIGUNION
       Given PAIR_DISJOINT (e INSERT P)
          so PAIR_DISJOINT P               by IN_INSERT
         and !s. s IN P ==> DISJOINT e s   by IN_INSERT
       hence DISJOINT e (BIGUNION P)       by DISJOINT_BIGUNION
          so e INTER (BIGUNION P) = {}     by DISJOINT_DEF
         and f (e INTER (BIGUNION P)) = 0  by SET_ADDITIVE f
         f (BIGUNION (e INSERT P)
       = f (BIGUNION (e INSERT P)) + f (e INTER (BIGUNION P))     by ADD_0
       = f e + f (BIGUNION P)                                     by SET_ADDITIVE f
       = f e + SIGMA f P                   by induction hypothesis
       = f e + SIGMA f (P DELETE e)        by DELETE_NON_ELEMENT
       = SIGMA f (e INSERT P)              by SUM_IMAGE_THM
*)
val disjoint_bigunion_add_fun = store_thm(
  "disjoint_bigunion_add_fun",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P)``,
  `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw_tac std_ss[BIGUNION_EMPTY, SUM_IMAGE_EMPTY] >>
  rw_tac std_ss[BIGUNION_INSERT, SUM_IMAGE_THM] >>
  `FINITE e /\ FINITE (BIGUNION P)` by rw[FINITE_BIGUNION] >>
  `EVERY_FINITE P /\ PAIR_DISJOINT P` by rw[] >>
  `!s. s IN P ==> DISJOINT e s` by metis_tac[IN_INSERT] >>
  `f (e INTER (BIGUNION P)) = 0` by metis_tac[DISJOINT_DEF, DISJOINT_BIGUNION] >>
  `f (e UNION BIGUNION P) = f (e UNION BIGUNION P) + f (e INTER (BIGUNION P))` by decide_tac >>
  `_ = f e + f (BIGUNION P)` by metis_tac[] >>
  `_ = f e + SIGMA f P` by prove_tac[] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem: SET_ADDITIVE CARD *)
(* Proof:
   Since CARD {} = 0                    by CARD_EMPTY
     and !s t. FINITE s /\ FINITE t
     ==> CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t   by CARD_UNION
   Hence SET_ADDITIVE CARD              by notation
*)
val set_additive_card = store_thm(
  "set_additive_card",
  ``SET_ADDITIVE CARD``,
  rw[FUN_EQ_THM, CARD_UNION]);

(* Note: DISJ_BIGUNION_CARD is only a prove_thm in pred_setTheoryScript.sml *)
(*
g `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P)`
e (PSet_ind.SET_INDUCT_TAC FINITE_INDUCT);
Q. use of this changes P to s, s to s', how?
*)

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P) *)
(* Proof: by disjoint_bigunion_add_fun, set_additive_card *)
val disjoint_bigunion_card = store_thm(
  "disjoint_bigunion_card",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P)``,
  rw[disjoint_bigunion_add_fun, set_additive_card]);

(* Theorem: SET_ADDITIVE (SIGMA f) *)
(* Proof:
   Since SIGMA f {} = 0         by SUM_IMAGE_EMPTY
     and !s t. FINITE s /\ FINITE t
     ==> SIGMA f (s UNION t) + SIGMA f (s INTER t) = SIGMA f s + SIGMA f t   by SUM_IMAGE_UNION_EQN
   Hence SET_ADDITIVE (SIGMA f)
*)
val set_additive_sigma = store_thm(
  "set_additive_sigma",
  ``!f. SET_ADDITIVE (SIGMA f)``,
  rw[SUM_IMAGE_EMPTY, SUM_IMAGE_UNION_EQN]);

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> !f. SIGMA f (BIGUNION P) = SIGMA (SIGMA f) P *)
(* Proof: by disjoint_bigunion_add_fun, set_additive_sigma *)
val disjoint_bigunion_sigma = store_thm(
  "disjoint_bigunion_sigma",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> !f. SIGMA f (BIGUNION P) = SIGMA (SIGMA f) P``,
  rw[disjoint_bigunion_add_fun, set_additive_sigma]);

(* Theorem: R equiv_on s /\ FINITE s ==> !f. SET_ADDITIVE f ==> (f s = SIGMA f (partition R s)) *)
(* Proof:
   Let P = partition R s.
    Then FINITE s
     ==> FINITE P /\ !t. t IN P ==> FINITE t    by FINITE_partition
     and R equiv_on s
     ==> BIGUNION P = s               by BIGUNION_partition
     ==> PAIR_DISJOINT P              by partition_elements_disjoint
   Hence f (BIGUNION P) = SIGMA f P   by disjoint_bigunion_add_fun
      or f s = SIGMA f P              by above, BIGUNION_partition
*)
val set_add_fun_by_partition = store_thm(
  "set_add_fun_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> !f. SET_ADDITIVE f ==> (f s = SIGMA f (partition R s))``,
  rpt strip_tac >>
  qabbrev_tac `P = partition R s` >>
  `FINITE P /\ !t. t IN P ==> FINITE t` by metis_tac[FINITE_partition] >>
  `BIGUNION P = s` by rw[BIGUNION_partition, Abbr`P`] >>
  `PAIR_DISJOINT P` by metis_tac[partition_elements_disjoint] >>
  rw[disjoint_bigunion_add_fun]);

(* Theorem: R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s)) *)
(* Proof: by set_add_fun_by_partition, set_additive_card *)
val set_card_by_partition = store_thm(
  "set_card_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))``,
  rw[set_add_fun_by_partition, set_additive_card]);

(* This is pred_setTheory.partition_CARD *)

(* Theorem: R equiv_on s /\ FINITE s ==> !f. SIGMA f s = SIGMA (SIGMA f) (partition R s) *)
(* Proof: by set_add_fun_by_partition, set_additive_sigma *)
val set_sigma_by_partition = store_thm(
  "set_sigma_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> !f. SIGMA f s = SIGMA (SIGMA f) (partition R s)``,
  rw[set_add_fun_by_partition, set_additive_sigma]);

(* Overload a multiplicative set function *)
val _ = overload_on("SET_MULTIPLICATIVE",
   ``\f. (f {} = 1) /\ (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) * f (s INTER t) = f s * f t))``);

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
            !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P) *)
(* Proof:
   By finite induction on P.
   Base: f (BIGUNION {}) = PI f {}
         f (BIGUNION {})
       = f {}                by BIGUNION_EMPTY
       = 1                   by SET_MULTIPLICATIVE f
       = PI f {} = RHS       by PROD_IMAGE_EMPTY
   Step: e NOTIN P ==> f (BIGUNION (e INSERT P)) = PI f (e INSERT P)
       Given !s. s IN e INSERT P ==> FINITE s
        thus !s. (s = e) \/ s IN P ==> FINITE s   by IN_INSERT
       hence FINITE e              by implication
         and EVERY_FINITE P        by IN_INSERT
         and FINITE (BIGUNION P)   by FINITE_BIGUNION
       Given PAIR_DISJOINT (e INSERT P)
          so PAIR_DISJOINT P               by IN_INSERT
         and !s. s IN P ==> DISJOINT e s   by IN_INSERT
       hence DISJOINT e (BIGUNION P)       by DISJOINT_BIGUNION
          so e INTER (BIGUNION P) = {}     by DISJOINT_DEF
         and f (e INTER (BIGUNION P)) = 1  by SET_MULTIPLICATIVE f
         f (BIGUNION (e INSERT P)
       = f (BIGUNION (e INSERT P)) * f (e INTER (BIGUNION P))     by MULT_RIGHT_1
       = f e * f (BIGUNION P)                                     by SET_MULTIPLICATIVE f
       = f e * PI f P                      by induction hypothesis
       = f e * PI f (P DELETE e)           by DELETE_NON_ELEMENT
       = PI f (e INSERT P)                 by PROD_IMAGE_THM
*)
val disjoint_bigunion_mult_fun = store_thm(
  "disjoint_bigunion_mult_fun",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P)``,
  `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw_tac std_ss[BIGUNION_EMPTY, PROD_IMAGE_EMPTY] >>
  rw_tac std_ss[BIGUNION_INSERT, PROD_IMAGE_THM] >>
  `FINITE e /\ FINITE (BIGUNION P)` by rw[FINITE_BIGUNION] >>
  `EVERY_FINITE P /\ PAIR_DISJOINT P` by rw[] >>
  `!s. s IN P ==> DISJOINT e s` by metis_tac[IN_INSERT] >>
  `f (e INTER (BIGUNION P)) = 1` by metis_tac[DISJOINT_DEF, DISJOINT_BIGUNION] >>
  `f (e UNION BIGUNION P) = f (e UNION BIGUNION P) * f (e INTER (BIGUNION P))` by metis_tac[MULT_RIGHT_1] >>
  `_ = f e * f (BIGUNION P)` by metis_tac[] >>
  `_ = f e * PI f P` by prove_tac[] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem: R equiv_on s /\ FINITE s ==> !f. SET_MULTIPLICATIVE f ==> (f s = PI f (partition R s)) *)
(* Proof:
   Let P = partition R s.
    Then FINITE s
     ==> FINITE P /\ EVERY_FINITE P   by FINITE_partition
     and R equiv_on s
     ==> BIGUNION P = s               by BIGUNION_partition
     ==> PAIR_DISJOINT P              by partition_elements_disjoint
   Hence f (BIGUNION P) = PI f P      by disjoint_bigunion_mult_fun
      or f s = PI f P                 by above, BIGUNION_partition
*)
val set_mult_fun_by_partition = store_thm(
  "set_mult_fun_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> !f. SET_MULTIPLICATIVE f ==> (f s = PI f (partition R s))``,
  rpt strip_tac >>
  qabbrev_tac `P = partition R s` >>
  `FINITE P /\ !t. t IN P ==> FINITE t` by metis_tac[FINITE_partition] >>
  `BIGUNION P = s` by rw[BIGUNION_partition, Abbr`P`] >>
  `PAIR_DISJOINT P` by metis_tac[partition_elements_disjoint] >>
  rw[disjoint_bigunion_mult_fun]);

(* Theorem: FINITE s ==> !g. INJ g s univ(:'a) ==> !f. SIGMA f (IMAGE g s) = SIGMA (f o g) s *)
(* Proof:
   By finite induction on s.
   Base: SIGMA f (IMAGE g {}) = SIGMA (f o g) {}
      LHS = SIGMA f (IMAGE g {})
          = SIGMA f {}                    by IMAGE_EMPTY
          = 0                             by SUM_IMAGE_EMPTY
          = SIGMA (f o g) {} = RHS        by SUM_IMAGE_EMPTY
   Step: e NOTIN s ==> SIGMA f (IMAGE g (e INSERT s)) = SIGMA (f o g) (e INSERT s)
      Note INJ g (e INSERT s) univ(:'a)
       ==> INJ g s univ(:'a) /\ g e IN univ(:'a) /\
           !y. y IN s /\ (g e = g y) ==> (e = y)       by INJ_INSERT
      Thus g e NOTIN (IMAGE g s)                       by IN_IMAGE
        SIGMA f (IMAGE g (e INSERT s))
      = SIGMA f (g e INSERT IMAGE g s)    by IMAGE_INSERT
      = f (g e) + SIGMA f (IMAGE g s)     by SUM_IMAGE_THM, g e NOTIN (IMAGE g s)
      = f (g e) + SIGMA (f o g) s         by induction hypothesis
      = (f o g) e + SIGMA (f o g) s       by composition
      = SIGMA (f o g) (e INSERT s)        by SUM_IMAGE_THM, e NOTIN s
*)
val sum_image_by_composition = store_thm(
  "sum_image_by_composition",
  ``!s. FINITE s ==> !g. INJ g s univ(:'a) ==> !f. SIGMA f (IMAGE g s) = SIGMA (f o g) s``,
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[SUM_IMAGE_EMPTY] >>
  `INJ g s univ(:'a) /\ g e IN univ(:'a) /\ !y. y IN s /\ (g e = g y) ==> (e = y)` by metis_tac[INJ_INSERT] >>
  `g e NOTIN (IMAGE g s)` by metis_tac[IN_IMAGE] >>
  `(s DELETE e = s) /\ (IMAGE g s DELETE g e = IMAGE g s)` by metis_tac[DELETE_NON_ELEMENT] >>
  rw[SUM_IMAGE_THM]);

(* Overload on permutation *)
val _ = overload_on("PERMUTES", ``\f s. BIJ f s s``);
val _ = set_fixity "PERMUTES" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: FINITE s ==> !g. g PERMUTES s ==> !f. SIGMA (f o g) s = SIGMA f s *)
(* Proof:
   Given permutate g s = BIJ g s s       by notation
     ==> INJ g s s /\ SURJ g s s         by BIJ_DEF
     Now SURJ g s s ==> IMAGE g s = s    by IMAGE_SURJ
    Also s SUBSET univ(:'a)              by SUBSET_UNIV
     and s SUBSET s                      by SUBSET_REFL
   Hence INJ g s univ(:'a)               by INJ_SUBSET
    With FINITE s,
      SIGMA (f o g) s
    = SIGMA f (IMAGE g s)                by sum_image_by_composition
    = SIGMA f s                          by above
*)
val sum_image_by_permutation = store_thm(
  "sum_image_by_permutation",
  ``!s. FINITE s ==> !g. g PERMUTES s ==> !f. SIGMA (f o g) s = SIGMA f s``,
  rpt strip_tac >>
  `INJ g s s /\ SURJ g s s` by metis_tac[BIJ_DEF] >>
  `IMAGE g s = s` by rw[GSYM IMAGE_SURJ] >>
  `s SUBSET univ(:'a)` by rw[SUBSET_UNIV] >>
  `INJ g s univ(:'a)` by metis_tac[INJ_SUBSET, SUBSET_REFL] >>
  `SIGMA (f o g) s = SIGMA f (IMAGE g s)` by rw[sum_image_by_composition] >>
  rw[]);

(* Theorem: FINITE s ==> !f:('b -> bool) -> num. (f {} = 0) ==>
            !g. (!t. FINITE t /\ (!x. x IN t ==> g x <> {}) ==> INJ g t univ(:num -> bool)) ==>
            (SIGMA f (IMAGE g s) = SIGMA (f o g) s) *)
(* Proof:
   Let s1 = {x | x IN s /\ (g x = {})},
       s2 = {x | x IN s /\ (g x <> {})}.
    Then s = s1 UNION s2                             by EXTENSION
     and DISJOINT s1 s2                              by EXTENSION, DISJOINT_DEF
     and DISJOINT (IMAGE g s1) (IMAGE g s2)          by EXTENSION, DISJOINT_DEF
     Now s1 SUBSET s /\ s1 SUBSET s                  by SUBSET_DEF
   Since FINITE s                                    by given
    thus FINITE s1 /\ FINITE s2                      by SUBSET_FINITE
     and FINITE (IMAGE g s1) /\ FINITE (IMAGE g s2)  by IMAGE_FINITE

   Step 1: decompose left summation
         SIGMA f (IMAGE g s)
       = SIGMA f (IMAGE g (s1 UNION s2))             by above, s = s1 UNION s2
       = SIGMA f ((IMAGE g s1) UNION (IMAGE g s2))   by IMAGE_UNION
       = SIGMA f (IMAGE g s1) + SIGMA f (IMAGE g s2) by SUM_IMAGE_DISJOINT

   Claim: SIGMA f (IMAGE g s1) = 0
   Proof: If s1 = {},
            SIGMA f (IMAGE g {})
          = SIGMA f {}                               by IMAGE_EMPTY
          = 0                                        by SUM_IMAGE_EMPTY
          If s1 <> {},
            Note !x. x IN s1 ==> (g x = {})          by definition of s1
            Thus !y. y IN (IMAGE g s1) ==> (y = {})  by IN_IMAGE, IMAGE_EMPTY
           Since s1 <> {}, IMAGE g s1 = {{}}         by SING_DEF, IN_SING, SING_ONE_ELEMENT
            SIGMA f (IMAGE g {})
          = SIGMA f {{}}                             by above
          = f {}                                     by SUM_IMAGE_SING
          = 0                                        by given

   Step 2: decompose right summation
    Also SIGMA (f o g) s
       = SIGMA (f o g) (s1 UNION s2)                 by above, s = s1 UNION s2
       = SIGMA (f o g) s1 + SIGMA (f o g) s2         by SUM_IMAGE_DISJOINT

   Claim: SIGMA (f o g) s1 = 0
   Proof: Note !x. x IN s1 ==> (g x = {})            by definition of s1
             (f o g) x
            = f (g x)                                by function application
            = f {}                                   by above
            = 0                                      by given
          Hence SIGMA (f o g) s1
              = 0 * CARD s1                          by SIGMA_CONSTANT
              = 0                                    by MULT

   Claim: SIGMA f (IMAGE g s2) = SIGMA (f o g) s2
   Proof: Note !x. x IN s2 ==> g x <> {}             by definition of s2
          Thus INJ g s2 univ(:'b -> bool)            by given
          Hence SIGMA f (IMAGE g s2)
              = SIGMA (f o g) (s2)                   by sum_image_by_composition

   Result follows by combining all the claims and arithmetic.
*)
val sum_image_by_composition_with_partial_inj = store_thm(
  "sum_image_by_composition_with_partial_inj",
  ``!s. FINITE s ==> !f:('b -> bool) -> num. (f {} = 0) ==>
   !g. (!t. FINITE t /\ (!x. x IN t ==> g x <> {}) ==> INJ g t univ(:'b -> bool)) ==>
   (SIGMA f (IMAGE g s) = SIGMA (f o g) s)``,
  rpt strip_tac >>
  qabbrev_tac `s1 = {x | x IN s /\ (g x = {})}` >>
  qabbrev_tac `s2 = {x | x IN s /\ (g x <> {})}` >>
  (`s = s1 UNION s2` by (rw[Abbr`s1`, Abbr`s2`, EXTENSION] >> metis_tac[])) >>
  (`DISJOINT s1 s2` by (rw[Abbr`s1`, Abbr`s2`, EXTENSION, DISJOINT_DEF] >> metis_tac[])) >>
  (`DISJOINT (IMAGE g s1) (IMAGE g s2)` by (rw[Abbr`s1`, Abbr`s2`, EXTENSION, DISJOINT_DEF] >> metis_tac[])) >>
  `s1 SUBSET s /\ s2 SUBSET s` by rw[Abbr`s1`, Abbr`s2`, SUBSET_DEF] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[SUBSET_FINITE] >>
  `FINITE (IMAGE g s1) /\ FINITE (IMAGE g s2)` by rw[] >>
  `SIGMA f (IMAGE g s) = SIGMA f ((IMAGE g s1) UNION (IMAGE g s2))` by rw[] >>
  `_ = SIGMA f (IMAGE g s1) + SIGMA f (IMAGE g s2)` by rw[SUM_IMAGE_DISJOINT] >>
  `SIGMA f (IMAGE g s1) = 0` by
  (Cases_on `s1 = {}` >-
  rw[SUM_IMAGE_EMPTY] >>
  `!x. x IN s1 ==> (g x = {})` by rw[Abbr`s1`] >>
  `!y. y IN (IMAGE g s1) ==> (y = {})` by metis_tac[IN_IMAGE, IMAGE_EMPTY] >>
  `{} IN {{}} /\ IMAGE g s1 <> {}` by rw[] >>
  `IMAGE g s1 = {{}}` by metis_tac[SING_DEF, IN_SING, SING_ONE_ELEMENT] >>
  `SIGMA f (IMAGE g s1) = f {}` by rw[SUM_IMAGE_SING] >>
  rw[]
  ) >>
  `SIGMA (f o g) s = SIGMA (f o g) s1 + SIGMA (f o g) s2` by rw[SUM_IMAGE_DISJOINT] >>
  `SIGMA (f o g) s1 = 0` by
    (`!x. x IN s1 ==> (g x = {})` by rw[Abbr`s1`] >>
  `!x. x IN s1 ==> ((f o g) x = 0)` by rw[] >>
  metis_tac[SIGMA_CONSTANT, MULT]) >>
  `SIGMA f (IMAGE g s2) = SIGMA (f o g) s2` by
      (`!x. x IN s2 ==> g x <> {}` by rw[Abbr`s2`] >>
  `INJ g s2 univ(:'b -> bool)` by rw[] >>
  rw[sum_image_by_composition]) >>
  decide_tac);

(* Theorem: FINITE s ==> !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
            (SIGMA f (IMAGE g s) = SIGMA (f o g) s) *)
(* Proof:
   By finite induction on s.
   Base: SIGMA f (IMAGE g {}) = SIGMA (f o g) {}
        SIGMA f (IMAGE g {})
      = SIGMA f {}                 by IMAGE_EMPTY
      = 0                          by SUM_IMAGE_EMPTY
      = SIGMA (f o g) {}           by SUM_IMAGE_EMPTY
   Step: !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
         (SIGMA f (IMAGE g s) = SIGMA (f o g) s) ==>
         e NOTIN s /\ !x y. x IN e INSERT s /\ y IN e INSERT s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)
         ==> SIGMA f (IMAGE g (e INSERT s)) = SIGMA (f o g) (e INSERT s)
      Note !x y. ((x = e) \/ x IN s) /\ ((y = e) \/ y IN s) /\ (g x = g y) ==>
                 (x = y) \/ (f (g y) = 0)       by IN_INSERT
      If g e IN IMAGE g s,
         Then ?x. x IN s /\ (g x = g e)         by IN_IMAGE
          and x <> e /\ (f (g e) = 0)           by implication
           SIGMA f (g e INSERT IMAGE g s)
         = SIGMA f (IMAGE g s)                  by ABSORPTION, g e IN IMAGE g s
         = SIGMA (f o g) s                      by induction hypothesis
         = f (g x) + SIGMA (f o g) s            by ADD
         = (f o g) e + SIGMA (f o g) s          by o_THM
         = SIGMA (f o g) (e INSERT s)           by SUM_IMAGE_INSERT, e NOTIN s
      If g e NOTIN IMAGE g s,
           SIGMA f (g e INSERT IMAGE g s)
         = f (g e) + SIGMA f (IMAGE g s)        by SUM_IMAGE_INSERT, g e NOTIN IMAGE g s
         = f (g e) + SIGMA (f o g) s            by induction hypothesis
         = (f o g) e + SIGMA (f o g) s          by o_THM
         = SIGMA (f o g) (e INSERT s)           by SUM_IMAGE_INSERT, e NOTIN s
*)
val sum_image_by_composition_without_inj = store_thm(
  "sum_image_by_composition_without_inj",
  ``!s. FINITE s ==> !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
       (SIGMA f (IMAGE g s) = SIGMA (f o g) s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[SUM_IMAGE_EMPTY] >>
  fs[] >>
  Cases_on `g e IN IMAGE g s` >| [
    `?x. x IN s /\ (g x = g e)` by metis_tac[IN_IMAGE] >>
    `x <> e /\ (f (g e) = 0)` by metis_tac[] >>
    `SIGMA f (g e INSERT IMAGE g s) = SIGMA f (IMAGE g s)` by metis_tac[ABSORPTION] >>
    `_ = SIGMA (f o g) s` by rw[] >>
    `_ = (f o g) e + SIGMA (f o g) s` by rw[] >>
    `_ = SIGMA (f o g) (e INSERT s)` by rw[SUM_IMAGE_INSERT] >>
    rw[],
    `SIGMA f (g e INSERT IMAGE g s) = f (g e) + SIGMA f (IMAGE g s)` by rw[SUM_IMAGE_INSERT] >>
    `_ = f (g e) + SIGMA (f o g) s` by rw[] >>
    `_ = (f o g) e + SIGMA (f o g) s` by rw[] >>
    `_ = SIGMA (f o g) (e INSERT s)` by rw[SUM_IMAGE_INSERT] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Pre-image Theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

(*
- IN_IMAGE;
> val it = |- !y s f. y IN IMAGE f s <=> ?x. (y = f x) /\ x IN s : thm
*)

(* Define preimage *)
val preimage_def = Define `preimage f s y = { x | x IN s /\ (f x = y) }`;

(* Theorem: x IN (preimage f s y) <=> x IN s /\ (f x = y) *)
(* Proof: by preimage_def *)
val preimage_element = store_thm(
  "preimage_element",
  ``!f s x y. x IN (preimage f s y) <=> x IN s /\ (f x = y)``,
  rw[preimage_def]);

(* Theorem: x IN preimage f s y <=> (x IN s /\ (f x = y)) *)
(* Proof: by preimage_def *)
val in_preimage = store_thm(
  "in_preimage",
  ``!f s x y. x IN preimage f s y <=> (x IN s /\ (f x = y))``,
  rw[preimage_def]);
(* same as theorem above. *)

(* Theorem: preimage f s y SUBSET s *)
(* Proof: by definition. *)
val preimage_subset_of_domain = store_thm(
  "preimage_subset_of_domain",
  ``!f s y. preimage f s y SUBSET s``,
  rw[preimage_def, SUBSET_DEF]);

(* export trivial truth -- but not frequently used. *)
(* val _ = export_rewrites ["preimage_subset_of_domain"]; *)

(* Theorem: !x. x IN preimage f s y ==> f x = y *)
(* Proof: by definition. *)
val preimage_property = store_thm(
  "preimage_property",
  ``!f s y. !x. x IN preimage f s y ==> (f x = y)``,
  rw[preimage_def]);

(* This is bad: every pattern of f x = y (i.e. practically every equality!) will invoke the check: x IN preimage f s y! *)
(* val _ = export_rewrites ["preimage_property"]; *)

(* Theorem: x IN s ==> x IN preimage f s (f x) *)
(* Proof: by IN_IMAGE. preimage_def. *)
val preimage_of_image = store_thm(
  "preimage_of_image",
  ``!f s x. x IN s ==> x IN preimage f s (f x)``,
  rw[preimage_def]);

(* Theorem: y IN (IMAGE f s) ==> CHOICE (preimage f s y) IN s /\ f (CHOICE (preimage f s y)) = y *)
(* Proof:
   (1) prove: y IN IMAGE f s ==> CHOICE (preimage f s y) IN s
   By IN_IMAGE, this is to show:
   x IN s ==> CHOICE (preimage f s (f x)) IN s
   Now, preimage f s (f x) <> {}   since x is a pre-image.
   hence CHOICE (preimage f s (f x)) IN preimage f s (f x) by CHOICE_DEF
   hence CHOICE (preimage f s (f x)) IN s                  by preimage_def
   (2) prove: y IN IMAGE f s /\ CHOICE (preimage f s y) IN s ==> f (CHOICE (preimage f s y)) = y
   By IN_IMAGE, this is to show: x IN s ==> f (CHOICE (preimage f s (f x))) = f x
   Now, x IN preimage f s (f x)   by preimage_of_image
   hence preimage f s (f x) <> {}  by MEMBER_NOT_EMPTY
   thus  CHOICE (preimage f s (f x)) IN (preimage f s (f x))  by CHOICE_DEF
   hence f (CHOICE (preimage f s (f x))) = f x  by preimage_def
*)
val preimage_choice_property = store_thm(
  "preimage_choice_property",
  ``!f s y. y IN (IMAGE f s) ==> CHOICE (preimage f s y) IN s /\ (f (CHOICE (preimage f s y)) = y)``,
  rpt gen_tac >>
  strip_tac >>
  conj_asm1_tac >| [
    full_simp_tac std_ss [IN_IMAGE] >>
    `CHOICE (preimage f s (f x)) IN preimage f s (f x)` suffices_by rw[preimage_def] >>
    metis_tac[CHOICE_DEF, preimage_of_image, MEMBER_NOT_EMPTY],
    full_simp_tac std_ss [IN_IMAGE] >>
    `x IN preimage f s (f x)` by rw_tac std_ss[preimage_of_image] >>
    `CHOICE (preimage f s (f x)) IN (preimage f s (f x))` by metis_tac[CHOICE_DEF, MEMBER_NOT_EMPTY] >>
    full_simp_tac std_ss [preimage_def, GSPECIFICATION]
  ]);

(* Theorem: INJ f s univ(:'b) ==> !x. x IN s ==> (preimage f s (f x) = {x}) *)
(* Proof:
     preimage f s (f x)
   = {x' | x' IN s /\ (f x' = f x)}    by preimage_def
   = {x' | x' IN s /\ (x' = x)}        by INJ_DEF
   = {x}                               by EXTENSION
*)
val preimage_inj = store_thm(
  "preimage_inj",
  ``!f s. INJ f s univ(:'b) ==> !x. x IN s ==> (preimage f s (f x) = {x})``,
  rw[preimage_def, EXTENSION] >>
  metis_tac[INJ_DEF]);

(* Theorem: INJ f s univ(:'b) ==> !x. x IN s ==> (CHOICE (preimage f s (f x)) = x) *)
(* Proof:
     CHOICE (preimage f s (f x))
   = CHOICE {x}                     by preimage_inj, INJ f s univ(:'b)
   = x                              by CHOICE_SING
*)
val preimage_inj_choice = store_thm(
  "preimage_inj_choice",
  ``!f s. INJ f s univ(:'b) ==> !x. x IN s ==> (CHOICE (preimage f s (f x)) = x)``,
  rw[preimage_inj]);

(* ------------------------------------------------------------------------- *)
(* Set of Proper Subsets                                                     *)
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

(* ------------------------------------------------------------------------- *)
(* HelperList Documentation                                                  *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   m downto n        = REVERSE [m .. n]
   turn_exp l n      = FUNPOW turn n l
   POSITIVE l        = !x. MEM x l ==> 0 < x
   EVERY_POSITIVE l  = EVERY (\k. 0 < k) l
   MONO f            = !x y. x <= y ==> f x <= f y
   MONO2 f           = !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x1 y1 <= f x2 y2
   MONO3 f           = !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==> f x1 y1 z1 <= f x2 y2 z2
   RMONO f           = !x y. x <= y ==> f y <= f x
   RMONO2 f          = !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x2 y2 <= f x1 y1
   RMONO3 f          = !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==> f x2 y2 z2 <= f x1 y1 z1
   MONO_INC ls       = !m n. m <= n /\ n < LENGTH ls ==> EL m ls <= EL n ls
   MONO_DEC ls       = !m n. m <= n /\ n < LENGTH ls ==> EL n ls <= EL m ls
*)

(* Definitions and Theorems (# are exported):

   List Theorems:
   LIST_NOT_NIL     |- !ls. ls <> [] <=> (ls = HD ls::TL ls)
   LIST_HEAD_TAIL   |- !ls. 0 < LENGTH ls <=> (ls = HD ls::TL ls)
   LIST_EQ_HEAD_TAIL|- !p q. p <> [] /\ q <> [] ==> ((p = q) <=> (HD p = HD q) /\ (TL p = TL q))
   LIST_SING_EQ     |- !x y. ([x] = [y]) <=> (x = y)
   LENGTH_NON_NIL   |- !l. 0 < LENGTH l <=> l <> []
   LENGTH_EQ_0      |- !l. (LENGTH l = 0) <=> (l = [])
   LENGTH_EQ_1      |- !l. (LENGTH l = 1) <=> ?x. l = [x]
   LENGTH_SING      |- !x. LENGTH [x] = 1
   LENGTH_TL_LT     |- !ls. ls <> [] ==> LENGTH (TL ls) < LENGTH ls
   SNOC_NIL         |- !x. SNOC x [] = [x]
   SNOC_CONS        |- !x x' l. SNOC x (x'::l) = x'::SNOC x l
   SNOC_LAST_FRONT  |- !l. l <> [] ==> (l = SNOC (LAST l) (FRONT l))
   MAP_COMPOSE      |- !f g l. MAP f (MAP g l) = MAP (f o g) l
   MAP_SING         |- !f x. MAP f [x] = [f x]
   LAST_EL_CONS     |- !h t. t <> [] ==> LAST t = EL (LENGTH t) (h::t)
   FRONT_LENGTH     |- !l. l <> [] ==> (LENGTH (FRONT l) = PRE (LENGTH l))
   FRONT_EL         |- !l n. l <> [] /\ n < LENGTH (FRONT l) ==> (EL n (FRONT l) = EL n l)
   FRONT_EQ_NIL     |- !l. LENGTH l = 1 ==> FRONT l = []
   FRONT_NON_NIL    |- !l. 1 < LENGTH l ==> FRONT l <> []
   HEAD_MEM         |- !ls. ls <> [] ==> MEM (HD ls) ls
   LAST_MEM         |- !ls. ls <> [] ==> MEM (LAST ls) ls
   DROP_1           |- !h t. DROP 1 (h::t) = t
   FRONT_SING       |- !x. FRONT [x] = []
   TAIL_BY_DROP     |- !ls. ls <> [] ==> TL ls = DROP 1 ls
   FRONT_BY_TAKE    |- !ls. ls <> [] ==> FRONT ls = TAKE (LENGTH ls - 1) ls
   HD_APPEND        |- !h t ls. HD (h::t ++ ls) = h
   EL_TAIL          |- !h t n. 0 <> n ==> (EL (n - 1) t = EL n (h::t))
   MONOLIST_SET_SING|- !c ls. ls <> [] /\ EVERY ($= c) ls ==> SING (set ls)

   List Reversal:
   REVERSE_SING      |- !x. REVERSE [x] = [x]
   REVERSE_HD        |- !ls. ls <> [] ==> (HD (REVERSE ls) = LAST ls)
   REVERSE_TL        |- !ls. ls <> [] ==> (TL (REVERSE ls) = REVERSE (FRONT ls))


   Extra List Theorems:
   EVERY_ELEMENT_PROPERTY  |- !p R. EVERY (\c. c IN R) p ==> !k. k < LENGTH p ==> EL k p IN R
   EVERY_MONOTONIC_MAP     |- !l f P Q. (!x. P x ==> (Q o f) x) /\ EVERY P l ==> EVERY Q (MAP f l)
   EVERY_LT_IMP_EVERY_LE   |- !ls n. EVERY (\j. j < n) ls ==> EVERY (\j. j <= n) ls
   ZIP_SNOC         |- !x1 x2 l1 l2. (LENGTH l1 = LENGTH l2) ==>
                                     (ZIP (SNOC x1 l1,SNOC x2 l2) = SNOC (x1,x2) (ZIP (l1,l2)))
   ZIP_MAP_MAP      |- !ls f g. ZIP (MAP f ls,MAP g ls) = MAP (\x. (f x,g x)) ls
   MAP2_MAP_MAP     |- !ls f g1 g2. MAP2 f (MAP g1 ls) (MAP g2 ls) = MAP (\x. f (g1 x) (g2 x)) ls
   EL_APPEND        |- !n l1 l2. EL n (l1 ++ l2) = if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2
   EL_ALL_PROPERTY  |- !h1 t1 h2 t2 P. (LENGTH (h1::t1) = LENGTH (h2::t2)) /\
                         (!k. k < LENGTH (h1::t1) ==> P (EL k (h1::t1)) (EL k (h2::t2))) ==>
                         P h1 h2 /\ !k. k < LENGTH t1 ==> P (EL k t1) (EL k t2)
   APPEND_EQ_APPEND_EQ   |- !l1 l2 m1 m2.
                            (l1 ++ l2 = m1 ++ m2) /\ (LENGTH l1 = LENGTH m1) <=> (l1 = m1) /\ (l2 = m2)
   LUPDATE_LEN           |- !e n l. LENGTH (LUPDATE e n l) = LENGTH l
   LUPDATE_EL            |- !e n l p. p < LENGTH l ==> EL p (LUPDATE e n l) = if p = n then e else EL p l
   LUPDATE_SAME_SPOT     |- !ls n p q. LUPDATE q n (LUPDATE p n ls) = LUPDATE q n ls
   LUPDATE_DIFF_SPOT     |- !ls m n p q. m <> n ==>
                            LUPDATE q n (LUPDATE p m ls) = LUPDATE p m (LUPDATE q n ls)
   EL_LENGTH_APPEND_0    |- !ls h t. EL (LENGTH ls) (ls ++ h::t) = h
   EL_LENGTH_APPEND_1    |- !ls h k t. EL (LENGTH ls + 1) (ls ++ h::k::t) = k
   LUPDATE_APPEND_0      |- !ls a h t. LUPDATE a (LENGTH ls) (ls ++ h::t) = ls ++ a::t
   LUPDATE_APPEND_1      |- !ls b h k t. LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) = ls ++ h::b::t
   LUPDATE_APPEND_0_1    |- !ls a b h k t. LUPDATE b (LENGTH ls + 1)
                                          (LUPDATE a (LENGTH ls) (ls ++ h::k::t)) = ls ++ a::b::t

   DROP and TAKE:
   DROP_LENGTH_NIL       |- !l. DROP (LENGTH l) l = []
   HD_DROP               |- !ls n. n < LENGTH ls ==> HD (DROP n ls) = EL n ls
   TAKE_1_APPEND         |- !x y. x <> [] ==> (TAKE 1 (x ++ y) = TAKE 1 x)
   DROP_1_APPEND         |- !x y. x <> [] ==> (DROP 1 (x ++ y) = DROP 1 x ++ y)
   DROP_SUC              |- !n x. DROP (SUC n) x = DROP 1 (DROP n x)
   TAKE_SUC              |- !n x. TAKE (SUC n) x = TAKE n x ++ TAKE 1 (DROP n x)
   TAKE_SUC_BY_TAKE      |- !k x. k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x))
   DROP_BY_DROP_SUC      |- !k x. k < LENGTH x ==> (DROP k x = EL k x::DROP (SUC k) x)
   DROP_HEAD_ELEMENT     |- !ls n. n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u
   DROP_TAKE_EQ_NIL      |- !ls n. DROP n (TAKE n ls) = []
   TAKE_DROP_SWAP        |- !ls m n. TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls)
   TAKE_LENGTH_APPEND2   |- !l1 l2 x k. TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2)) = l1
   LENGTH_TAKE_LE        |- !n l. LENGTH (TAKE n l) <= LENGTH l

   List Rotation:
   rotate_def              |- !n l. rotate n l = DROP n l ++ TAKE n l
   rotate_shift_element    |- !l n. n < LENGTH l ==> (rotate n l = EL n l::(DROP (SUC n) l ++ TAKE n l))
   rotate_0                |- !l. rotate 0 l = l
   rotate_nil              |- !n. rotate n [] = []
   rotate_full             |- !l. rotate (LENGTH l) l = l
   rotate_suc              |- !l n. n < LENGTH l ==> (rotate (SUC n) l = rotate 1 (rotate n l))
   rotate_same_length      |- !l n. LENGTH (rotate n l) = LENGTH l
   rotate_same_set         |- !l n. set (rotate n l) = set l
   rotate_add              |- !n m l. n + m <= LENGTH l ==> (rotate n (rotate m l) = rotate (n + m) l)
   rotate_lcancel          |- !k l. k < LENGTH l ==> (rotate (LENGTH l - k) (rotate k l) = l)
   rotate_rcancel          |- !k l. k < LENGTH l ==> (rotate k (rotate (LENGTH l - k) l) = l)

   List Turn:
   turn_def         |- !l. turn l = if l = [] then [] else LAST l::FRONT l
   turn_nil         |- turn [] = []
   turn_not_nil     |- !l. l <> [] ==> (turn l = LAST l::FRONT l)
   turn_length      |- !l. LENGTH (turn l) = LENGTH l
   turn_eq_nil      |- !p. (turn p = []) <=> (p = [])
   head_turn        |- !ls. ls <> [] ==> HD (turn ls) = LAST ls
   tail_turn        |- !ls. ls <> [] ==> (TL (turn ls) = FRONT ls)
   turn_snoc        |- !ls x. turn (SNOC x ls) = x::ls
   turn_exp_0       |- !l. turn_exp l 0 = l
   turn_exp_1       |- !l. turn_exp l 1 = turn l
   turn_exp_2       |- !l. turn_exp l 2 = turn (turn l)
   turn_exp_SUC     |- !l n. turn_exp l (SUC n) = turn_exp (turn l) n
   turn_exp_suc     |- !l n. turn_exp l (SUC n) = turn (turn_exp l n)
   turn_exp_length  |- !l n. LENGTH (turn_exp l n) = LENGTH l
   head_turn_exp    |- !ls n. n < LENGTH ls ==>
                              HD (turn_exp ls n) = EL (if n = 0 then 0 else (LENGTH ls - n)) ls

   Unit-List and Mono-List:
   LIST_TO_SET_SING |- !l. (LENGTH l = 1) ==> SING (set l)
   MONOLIST_EQ      |- !l1 l2. SING (set l1) /\ SING (set l2) ==>
                        ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2))
   NON_MONO_TAIL_PROPERTY |- !l. ~SING (set (h::t)) ==> ?h'. MEM h' t /\ h' <> h

   GENLIST Theorems:
   GENLIST_0           |- !f. GENLIST f 0 = []
   GENLIST_1           |- !f. GENLIST f 1 = [f 0]
   GENLIST_EQ          |- !f1 f2 n. (!m. m < n ==> f1 m = f2 m) ==> GENLIST f1 n = GENLIST f2 n
   GENLIST_EQ_NIL      |- !f n. (GENLIST f n = []) <=> (n = 0)
   GENLIST_LAST        |- !f n. LAST (GENLIST f (SUC n)) = f n
   GENLIST_CONSTANT    |- !f n c. (!k. k < n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f n)
   GENLIST_K_CONS      |- !e n. GENLIST (K e) (SUC n) = e::GENLIST (K e) n
   GENLIST_K_ADD       |- !e n m. GENLIST (K e) (n + m) = GENLIST (K e) m ++ GENLIST (K e) n
   GENLIST_K_LESS      |- !f e n. (!k. k < n ==> (f k = e)) ==> (GENLIST f n = GENLIST (K e) n)
   GENLIST_K_RANGE     |- !f e n. (!k. 0 < k /\ k <= n ==> (f k = e)) ==> (GENLIST (f o SUC) n = GENLIST (K e) n)
   GENLIST_K_APPEND    |- !a b c. GENLIST (K c) a ++ GENLIST (K c) b = GENLIST (K c) (a + b)
   GENLIST_K_APPEND_K  |- !c n. GENLIST (K c) n ++ [c] = [c] ++ GENLIST (K c) n
   GENLIST_K_MEM       |- !x c n. 0 < n ==> (MEM x (GENLIST (K c) n) <=> (x = c))
   GENLIST_K_SET       |- !c n. 0 < n ==> (set (GENLIST (K c) n) = {c})
   LIST_TO_SET_SING_IFF|- !ls. ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls))

   SUM Theorems:
   SUM_NIL                |- SUM [] = 0
   SUM_CONS               |- !h t. SUM (h::t) = h + SUM t
   SUM_SING               |- !n. SUM [n] = n
   SUM_MULT               |- !s k. k * SUM s = SUM (MAP ($* k) s)
   SUM_RIGHT_ADD_DISTRIB  |- !s m n. (m + n) * SUM s = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)
   SUM_LEFT_ADD_DISTRIB   |- !s m n. SUM s * (m + n) = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)

   SUM_GENLIST            |- !f n. SUM (GENLIST f n) = SIGMA f (count n)
   SUM_DECOMPOSE_FIRST    |- !f n. SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) n)
   SUM_DECOMPOSE_LAST     |- !f n. SUM (GENLIST f (SUC n)) = SUM (GENLIST f n) + f n
   SUM_ADD_GENLIST        |- !a b n. SUM (GENLIST a n) + SUM (GENLIST b n) =
                                     SUM (GENLIST (\k. a k + b k) n)
   SUM_GENLIST_APPEND     |- !a b n. SUM (GENLIST a n ++ GENLIST b n) = SUM (GENLIST (\k. a k + b k) n)
   SUM_DECOMPOSE_FIRST_LAST  |- !f n. 0 < n ==>
                                (SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n)
   SUM_MOD           |- !n. 0 < n ==> !l. (SUM l) MOD n = (SUM (MAP (\x. x MOD n) l)) MOD n
   SUM_EQ_0          |- !l. (SUM l = 0) <=> EVERY (\x. x = 0) l
   SUM_GENLIST_MOD   |- !n. 0 < n ==> !f. SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n =
                                          SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n
   SUM_CONSTANT      |- !n x. SUM (GENLIST (\j. x) n) = n * x
   SUM_GENLIST_K     |- !m n. SUM (GENLIST (K m) n) = m * n
   SUM_LE            |- !l1 l2. (LENGTH l1 = LENGTH l2) /\
                                (!k. k < LENGTH l1 ==> EL k l1 <= EL k l2) ==> SUM l1 <= SUM l2
   SUM_LE_MEM        |- !l x. MEM x l ==> x <= SUM l:
   SUM_LE_EL         |- !l n. n < LENGTH l ==> EL n l <= SUM l
   SUM_LE_SUM_EL     |- !l m n. m < n /\ n < LENGTH l ==> EL m l + EL n l <= SUM l
   SUM_DOUBLING_LIST |- !m n. SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1)

   Maximum of a List:
   MAX_LIST_def        |- (MAX_LIST [] = 0) /\ !h t. MAX_LIST (h::t) = MAX h (MAX_LIST t)
#  MAX_LIST_NIL        |- MAX_LIST [] = 0
#  MAX_LIST_CONS       |- !h t. MAX_LIST (h::t) = MAX h (MAX_LIST t)
   MAX_LIST_SING       |- !x. MAX_LIST [x] = x
   MAX_LIST_EQ_0       |- !l. (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l
   MAX_LIST_MEM        |- !l. l <> [] ==> MEM (MAX_LIST l) l
   MAX_LIST_PROPERTY   |- !l x. MEM x l ==> x <= MAX_LIST l
   MAX_LIST_TEST       |- !l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> y <= x) ==> (x = MAX_LIST l)
   MAX_LIST_LE         |- !h t. MAX_LIST t <= MAX_LIST (h::t)
   MAX_LIST_MONO_MAP   |- !f. (!x y. x <= y ==> f x <= f y) ==>
                              !ls. ls <> [] ==> MAX_LIST (MAP f ls) = f (MAX_LIST ls)

   Minimum of a List:
   MIN_LIST_def          |- !h t. MIN_LIST (h::t) = if t = [] then h else MIN h (MIN_LIST t)
#  MIN_LIST_SING         |- !x. MIN_LIST [x] = x
#  MIN_LIST_CONS         |- !h t. t <> [] ==> (MIN_LIST (h::t) = MIN h (MIN_LIST t))
   MIN_LIST_MEM          |- !l. l <> [] ==> MEM (MIN_LIST l) l
   MIN_LIST_PROPERTY     |- !l. l <> [] ==> !x. MEM x l ==> MIN_LIST l <= x
   MIN_LIST_TEST         |- !l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> x <= y) ==> (x = MIN_LIST l)
   MIN_LIST_LE_MAX_LIST  |- !l. l <> [] ==> MIN_LIST l <= MAX_LIST l
   MIN_LIST_LE           |- !h t. t <> [] ==> MIN_LIST (h::t) <= MIN_LIST t
   MIN_LIST_MONO_MAP     |- !f. (!x y. x <= y ==> f x <= f y) ==>
                                !ls. ls <> [] ==> MIN_LIST (MAP f ls) = f (MIN_LIST ls)

   List Nub and Set:
   nub_nil             |- nub [] = []
   nub_cons            |- !x l. nub (x::l) = if MEM x l then nub l else x::nub l
   nub_sing            |- !x. nub [x] = [x]
   nub_all_distinct    |- !l. ALL_DISTINCT (nub l)
   CARD_LIST_TO_SET_EQ           |- !l. CARD (set l) = LENGTH (nub l)
   MONO_LIST_TO_SET              |- !x. set [x] = {x}
   DISTINCT_LIST_TO_SET_EQ_SING  |- !l x. ALL_DISTINCT l /\ (set l = {x}) <=> (l = [x])
   MEM_SPLIT_APPEND_distinct     |- !l. ALL_DISTINCT l ==>
                                    !x. MEM x l <=> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2
   LIST_TO_SET_REDUCTION         |- !l1 l2 h. ~MEM h l1 /\ (set (h::l1) = set l2) ==>
                  ?p1 p2. ~MEM h p1 /\ ~MEM h p2 /\ (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2))

   Constant List and Padding:
   PAD_LEFT_NIL      |- !n c. PAD_LEFT c n [] = GENLIST (K c) n
   PAD_RIGHT_NIL     |- !n c. PAD_RIGHT c n [] = GENLIST (K c) n
   PAD_LEFT_LENGTH   |- !n c s. LENGTH (PAD_LEFT c n s) = MAX n (LENGTH s)
   PAD_RIGHT_LENGTH  |- !n c s. LENGTH (PAD_RIGHT c n s) = MAX n (LENGTH s)
   PAD_LEFT_ID       |- !l c n. n <= LENGTH l ==> (PAD_LEFT c n l = l)
   PAD_RIGHT_ID      |- !l c n. n <= LENGTH l ==> (PAD_RIGHT c n l = l)
   PAD_LEFT_0        |- !l c. PAD_LEFT c 0 l = l
   PAD_RIGHT_0       |- !l c. PAD_RIGHT c 0 l = l
   PAD_LEFT_CONS     |- !l n. LENGTH l <= n ==> !c. PAD_LEFT c (SUC n) l = c::PAD_LEFT c n l
   PAD_RIGHT_SNOC    |- !l n. LENGTH l <= n ==> !c. PAD_RIGHT c (SUC n) l = SNOC c (PAD_RIGHT c n l)
   PAD_RIGHT_CONS    |- !h t c n. h::PAD_RIGHT c n t = PAD_RIGHT c (SUC n) (h::t)
   PAD_LEFT_LAST     |- !l c n. l <> [] ==> (LAST (PAD_LEFT c n l) = LAST l)
   PAD_LEFT_EQ_NIL   |- !l c n. (PAD_LEFT c n l = []) <=> (l = []) /\ (n = 0)
   PAD_RIGHT_EQ_NIL  |- !l c n. (PAD_RIGHT c n l = []) <=> (l = []) /\ (n = 0)
   PAD_LEFT_NIL_EQ   |- !n c. 0 < n ==> (PAD_LEFT c n [] = PAD_LEFT c n [c])
   PAD_RIGHT_NIL_EQ  |- !n c. 0 < n ==> (PAD_RIGHT c n [] = PAD_RIGHT c n [c])
   PAD_RIGHT_BY_RIGHT|- !ls c n. PAD_RIGHT c n ls = ls ++ PAD_RIGHT c (n - LENGTH ls) []
   PAD_RIGHT_BY_LEFT |- !ls c n. PAD_RIGHT c n ls = ls ++ PAD_LEFT c (n - LENGTH ls) []
   PAD_LEFT_BY_RIGHT |- !ls c n. PAD_LEFT c n ls = PAD_RIGHT c (n - LENGTH ls) [] ++ ls
   PAD_LEFT_BY_LEFT  |- !ls c n. PAD_LEFT c n ls = PAD_LEFT c (n - LENGTH ls) [] ++ ls

   PROD for List, similar to SUM for List:
   POSITIVE_THM      |- !ls. EVERY_POSITIVE ls <=> POSITIVE ls
#  PROD              |- (PROD [] = 1) /\ !h t. PROD (h::t) = h * PROD t
   PROD_NIL          |- PROD [] = 1
   PROD_CONS         |- !h t. PROD (h::t) = h * PROD t
   PROD_SING         |- !n. PROD [n] = n
   PROD_eval         |- !ls. PROD ls = if ls = [] then 1 else HD ls * PROD (TL ls)
   PROD_eq_1         |- !ls. (PROD ls = 1) <=> !x. MEM x ls ==> (x = 1)
   PROD_SNOC         |- !x l. PROD (SNOC x l) = PROD l * x
   PROD_APPEND       |- !l1 l2. PROD (l1 ++ l2) = PROD l1 * PROD l2
   PROD_MAP_FOLDL    |- !ls f. PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls
   PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST  |- !s. FINITE s ==> !f. PI f s = PROD (MAP f (SET_TO_LIST s))
   PROD_ACC_DEF      |- (!acc. PROD_ACC [] acc = acc) /\
                         !h t acc. PROD_ACC (h::t) acc = PROD_ACC t (h * acc)
   PROD_ACC_PROD_LEM |- !L n. PROD_ACC L n = PROD L * n
   PROD_PROD_ACC     |- !L. PROD L = PROD_ACC L 1
   PROD_GENLIST_K    |- !m n. PROD (GENLIST (K m) n) = m ** n
   PROD_CONSTANT     |- !n x. PROD (GENLIST (\j. x) n) = x ** n
   PROD_EQ_0         |- !l. (PROD l = 0) <=> MEM 0 l
   PROD_POS          |- !l. EVERY_POSITIVE l ==> 0 < PROD l
   PROD_POS_ALT      |- !l. POSITIVE l ==> 0 < PROD l
   PROD_SQUARING_LIST|- !m n. PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1)

   List Range:
   listRangeINC_LEN          |- !m n. LENGTH [m .. n] = n + 1 - m
   listRangeINC_NIL          |- !m n. ([m .. n] = []) <=> n + 1 <= m
   listRangeINC_MEM          |- !m n x. MEM x [m .. n] <=> m <= x /\ x <= n
   listRangeINC_EL           |- !m n i. m + i <= n ==> EL i [m .. n] = m + i
   listRangeINC_EVERY        |- !P m n. EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x
   listRangeINC_EXISTS       |- !P m n. EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x
   listRangeINC_EVERY_EXISTS |- !P m n. EVERY P [m .. n] <=> ~EXISTS ($~ o P) [m .. n]
   listRangeINC_EXISTS_EVERY |- !P m n. EXISTS P [m .. n] <=> ~EVERY ($~ o P) [m .. n]
   listRangeINC_SNOC         |- !m n. m <= n + 1 ==> ([m .. n + 1] = SNOC (n + 1) [m .. n])
   listRangeINC_FRONT        |- !m n. m <= n + 1 ==> (FRONT [m .. n + 1] = [m .. n])
   listRangeINC_LAST         |- !m n. m <= n ==> (LAST [m .. n] = n)
   listRangeINC_REVERSE      |- !m n. REVERSE [m .. n] = MAP (\x. n - x + m) [m .. n]
   listRangeINC_REVERSE_MAP  |- !f m n. REVERSE (MAP f [m .. n]) = MAP (f o (\x. n - x + m)) [m .. n]
   listRangeINC_MAP_SUC      |- !f m n. MAP f [m + 1 .. n + 1] = MAP (f o SUC) [m .. n]
   listRangeINC_APPEND       |- !a b c. a <= b /\ b <= c ==> ([a .. b] ++ [b + 1 .. c] = [a .. c])
   listRangeINC_SUM          |- !m n. SUM [m .. n] = SUM [1 .. n] - SUM [1 .. m - 1]
   listRangeINC_PROD_pos     |- !m n. 0 < m ==> 0 < PROD [m .. n]
   listRangeINC_PROD         |- !m n. 0 < m /\ m <= n ==> (PROD [m .. n] = PROD [1 .. n] DIV PROD [1 .. m - 1])
   listRangeINC_has_divisors |- !m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m .. n]
   listRangeINC_1_n          |- !n. [1 .. n] = GENLIST SUC n
   listRangeINC_MAP          |- !f n. MAP f [1 .. n] = GENLIST (f o SUC) n
   listRangeINC_SUM_MAP      |- !f n. SUM (MAP f [1 .. SUC n]) = f (SUC n) + SUM (MAP f [1 .. n])

   listRangeLHI_to_listRangeINC  |- !m n. [m ..< n + 1] = [m .. n]
   listRangeLHI_LEN          |- !m n. LENGTH [m ..< n] = n - m
   listRangeLHI_NIL          |- !m n. [m ..< n] = [] <=> n <= m
   listRangeLHI_MEM          |- !m n x. MEM x [m ..< n] <=> m <= x /\ x < n
   listRangeLHI_EL           |- !m n i. m + i < n ==> EL i [m ..< n] = m + i
   listRangeLHI_EVERY        |- !P m n. EVERY P [m ..< n] <=> !x. m <= x /\ x < n ==> P x
   listRangeLHI_SNOC         |- !m n. m <= n ==> [m ..< n + 1] = SNOC n [m ..< n]
   listRangeLHI_FRONT        |- !m n. m <= n ==> (FRONT [m ..< n + 1] = [m ..< n])
   listRangeLHI_LAST         |- !m n. m <= n ==> (LAST [m ..< n + 1] = n)
   listRangeLHI_REVERSE      |- !m n. REVERSE [m ..< n] = MAP (\x. n - 1 - x + m) [m ..< n]
   listRangeLHI_REVERSE_MAP  |- !f m n. REVERSE (MAP f [m ..< n]) = MAP (f o (\x. n - 1 - x + m)) [m ..< n]
   listRangeLHI_MAP_SUC      |- !f m n. MAP f [m + 1 ..< n + 1] = MAP (f o SUC) [m ..< n]
   listRangeLHI_APPEND       |- !a b c. a <= b /\ b <= c ==> [a ..< b] ++ [b ..< c] = [a ..< c]
   listRangeLHI_SUM          |- !m n. SUM [m ..< n] = SUM [1 ..< n] - SUM [1 ..< m]
   listRangeLHI_PROD_pos     |- !m n. 0 < m ==> 0 < PROD [m ..< n]
   listRangeLHI_PROD         |- !m n. 0 < m /\ m <= n ==> PROD [m ..< n] = PROD [1 ..< n] DIV PROD [1 ..< m]
   listRangeLHI_has_divisors |- !m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m ..< n + 1]
   listRangeLHI_0_n          |- !n. [0 ..< n] = GENLIST I n
   listRangeLHI_MAP          |- !f n. MAP f [0 ..< n] = GENLIST f n
   listRangeLHI_SUM_MAP      |- !f n. SUM (MAP f [0 ..< SUC n]) = f n + SUM (MAP f [0 ..< n])

   List Summation and Product:
   sum_1_to_n_eq_tri_n       |- !n. SUM [1 .. n] = tri n
   sum_1_to_n_eqn            |- !n. SUM [1 .. n] = HALF (n * (n + 1))
   sum_1_to_n_double         |- !n. TWICE (SUM [1 .. n]) = n * (n + 1)
   prod_1_to_n_eq_fact_n     |- !n. PROD [1 .. n] = FACT n
   power_predecessor_eqn     |- !t n. t ** n - 1 = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n])
   geometric_sum_eqn         |- !t n. 1 < t ==> SUM (MAP (\j. t ** j) [0 ..< n]) = (t ** n - 1) DIV (t - 1)
   geometric_sum_eqn_alt     |- !t n. 1 < t ==> SUM (MAP (\j. t ** j) [0 .. n]) = (t ** (n + 1) - 1) DIV (t - 1)
   arithmetic_sum_eqn        |- !n. SUM [1 ..< n] = HALF (n * (n - 1))
   arithmetic_sum_eqn_alt    |- !n. SUM [1 .. n] = HALF (n * (n + 1))
   SUM_GENLIST_REVERSE       |- !f n. SUM (GENLIST (\j. f (n - j)) n) = SUM (MAP f [1 .. n])

   MAP of function with 3 list arguments:
   MAP3_DEF    |- (!t3 t2 t1 h3 h2 h1 f.
                    MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3) /\
                  (!z y f. MAP3 f [] y z = []) /\
                  (!z v5 v4 f. MAP3 f (v4::v5) [] z = []) /\
                   !v5 v4 v13 v12 f. MAP3 f (v4::v5) (v12::v13) [] = []
   MAP3        |- (!f. MAP3 f [] [] [] = []) /\
                   !f h1 t1 h2 t2 h3 t3.
                    MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3
   LENGTH_MAP3 |- !lx ly lz f. LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz)
   EL_MAP3     |- !lx ly lz n. n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
                  !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz)
   MEM_MAP2    |- !f x l1 l2. MEM x (MAP2 f l1 l2) ==>
                  ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2
   MEM_MAP3    |- !f x l1 l2 l3. MEM x (MAP3 f l1 l2 l3) ==>
                  ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3
   SUM_MAP_K   |- !ls c. SUM (MAP (K c) ls) = c * LENGTH ls
   SUM_MAP_K_LE|- !ls a b. a <= b ==> SUM (MAP (K a) ls) <= SUM (MAP (K b) ls)
   SUM_MAP2_K  |- !lx ly c. SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)
   SUM_MAP3_K  |- !lx ly lz c. SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)

   Bounds on Lists:
   SUM_UPPER        |- !ls. SUM ls <= MAX_LIST ls * LENGTH ls
   SUM_LOWER        |- !ls. MIN_LIST ls * LENGTH ls <= SUM ls
   SUM_MAP_LE       |- !f g ls. EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls)
   SUM_MAP_LT       |- !f g ls. EVERY (\x. f x < g x) ls /\ ls <> [] ==> SUM (MAP f ls) < SUM (MAP g ls)
   MEM_MAP_UPPER    |- !f. MONO f ==> !ls e. MEM e (MAP f ls) ==> e <= f (MAX_LIST ls)
   MEM_MAP2_UPPER   |- !f. MONO2 f ==>!lx ly e. MEM e (MAP2 f lx ly) ==> e <= f (MAX_LIST lx) (MAX_LIST ly)
   MEM_MAP3_UPPER   |- !f. MONO3 f ==>
                           !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz)
   MEM_MAP_LOWER    |- !f. MONO f ==> !ls e. MEM e (MAP f ls) ==> f (MIN_LIST ls) <= e
   MEM_MAP2_LOWER   |- !f. MONO2 f ==> !lx ly e. MEM e (MAP2 f lx ly) ==> f (MIN_LIST lx) (MIN_LIST ly) <= e
   MEM_MAP3_LOWER   |- !f. MONO3 f ==>
                           !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> f (MIN_LIST lx) (MIN_LIST ly) (MIN_LIST lz) <= e
   MAX_LIST_MAP_LE  |- !f g. (!x. f x <= g x) ==>
                       !ls. MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls)
   MIN_LIST_MAP_LE  |- !f g. (!x. f x <= g x) ==>
                       !ls. MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls)
   MAP_LE           |- !f g. (!x. f x <= g x) ==> !ls n. EL n (MAP f ls) <= EL n (MAP g ls)
   MAP2_LE          |- !f g. (!x y. f x y <= g x y) ==>
                       !lx ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly)
   MAP3_LE          |- !f g. (!x y z. f x y z <= g x y z) ==>
                       !lx ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz)
   SUM_MONO_MAP     |- !f1 f2. (!x. f1 x <= f2 x) ==> !ls. SUM (MAP f1 ls) <= SUM (MAP f2 ls)
   SUM_MONO_MAP2    |- !f1 f2. (!x y. f1 x y <= f2 x y) ==>
                               !lx ly. SUM (MAP2 f1 lx ly) <= SUM (MAP2 f2 lx ly)
   SUM_MONO_MAP3    |- !f1 f2. (!x y z. f1 x y z <= f2 x y z) ==>
                               !lx ly lz. SUM (MAP3 f1 lx ly lz) <= SUM (MAP3 f2 lx ly lz)
   SUM_MAP_UPPER    |- !f. MONO f ==> !ls. SUM (MAP f ls) <= f (MAX_LIST ls) * LENGTH ls
   SUM_MAP2_UPPER   |- !f. MONO2 f ==>
                       !lx ly. SUM (MAP2 f lx ly) <= f (MAX_LIST lx) (MAX_LIST ly) * LENGTH (MAP2 f lx ly)
   SUM_MAP3_UPPER   |- !f. MONO3 f ==>
                       !lx ly lz. SUM (MAP3 f lx ly lz) <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) * LENGTH (MAP3 f lx ly lz)

   Increasing and decreasing list bounds:
   GENLIST_MONO_INC   |- !f n. MONO f ==> MONO_INC (GENLIST f n)
   GENLIST_MONO_DEC   |- !f n. RMONO f ==> MONO_DEC (GENLIST f n)
   MAX_LIST_MONO_INC  |- !ls. ls <> [] /\ MONO_INC ls ==> MAX_LIST ls = LAST ls
   MAX_LIST_MONO_DEC  |- !ls. ls <> [] /\ MONO_DEC ls ==> MAX_LIST ls = HD ls
   MIN_LIST_MONO_INC  |- !ls. ls <> [] /\ MONO_INC ls ==> MIN_LIST ls = HD ls
   MIN_LIST_MONO_DEC  |- !ls. ls <> [] /\ MONO_DEC ls ==> MIN_LIST ls = LAST ls

   List Dilation:

   List Dilation (Multiplicative):
   MDILATE_def    |- (!e n. MDILATE e n [] = []) /\
        !e n h t. MDILATE e n (h::t) = if t = [] then [h] else h::GENLIST (K e) (PRE n) ++ MDILATE e n t
#  MDILATE_NIL    |- !e n. MDILATE e n [] = []
#  MDILATE_SING   |- !e n x. MDILATE e n [x] = [x]
   MDILATE_CONS   |- !e n h t. MDILATE e n (h::t) =
                               if t = [] then [h] else h::GENLIST (K e) (PRE n) ++ MDILATE e n t
   MDILATE_1      |- !l e. MDILATE e 1 l = l
   MDILATE_0      |- !l e. MDILATE e 0 l = l
   MDILATE_LENGTH        |- !l e n. LENGTH (MDILATE e n l) =
                              if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l))
   MDILATE_LENGTH_LOWER  |- !l e n. LENGTH l <= LENGTH (MDILATE e n l)
   MDILATE_LENGTH_UPPER  |- !l e n. 0 < n ==> LENGTH (MDILATE e n l) <= SUC (n * PRE (LENGTH l))
   MDILATE_EL     |- !l e n k. k < LENGTH (MDILATE e n l) ==>
              (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e)
   MDILATE_EQ_NIL |- !l e n. (MDILATE e n l = []) <=> (l = [])
   MDILATE_LAST   |- !l e n. LAST (MDILATE e n l) = LAST l

   List Dilation (Additive):
   DILATE_def       |- (!n m e. DILATE e n m [] = []) /\
                       (!n m h e. DILATE e n m [h] = [h]) /\
                       !v9 v8 n m h e. DILATE e n m (h::v8::v9) =
                        h:: (TAKE n (v8::v9) ++ GENLIST (K e) m ++ DILATE e n m (DROP n (v8::v9)))
#  DILATE_NIL       |- !n m e. DILATE e n m [] = []
#  DILATE_SING      |- !n m h e. DILATE e n m [h] = [h]
   DILATE_CONS      |- !n m h t e. DILATE e n m (h::t) =
                        if t = [] then [h] else h::(TAKE n t ++ GENLIST (K e) m ++ DILATE e n m (DROP n t))
   DILATE_0_CONS    |- !n h t e. DILATE e 0 n (h::t) =
                        if t = [] then [h] else h::(GENLIST (K e) n ++ DILATE e 0 n t)
   DILATE_0_0       |- !l e. DILATE e 0 0 l = l
   DILATE_0_SUC     |- !l e n. DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l)
   DILATE_0_LENGTH  |- !l e n. LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l))
   DILATE_0_LENGTH_LOWER  |- !l e n. LENGTH l <= LENGTH (DILATE e 0 n l)
   DILATE_0_LENGTH_UPPER   |- !l e n. LENGTH (DILATE e 0 n l) <= SUC (SUC n * PRE (LENGTH l))
   DILATE_0_EL      |- !l e n k. k < LENGTH (DILATE e 0 n l) ==>
                        (EL k (DILATE e 0 n l) = if k MOD SUC n = 0 then EL (k DIV SUC n) l else e)
   DILATE_0_EQ_NIL  |- !l e n. (DILATE e 0 n l = []) <=> (l = [])
   DILATE_0_LAST    |- !l e n. LAST (DILATE e 0 n l) = LAST l

   Range Conjunction and Disjunction:
   every_range_sing    |- !a j. a <= j /\ j <= a <=> (j = a)
   every_range_cons    |- !f a b. a <= b ==>
                                    ((!j. a <= j /\ j <= b ==> f j) <=>
                                      f a /\ !j. a + 1 <= j /\ j <= b ==> f j)
   exists_range_sing   |- !a. ?j. a <= j /\ j <= a <=> (j = a)
   exists_range_cons   |- !f a b. a <= b ==>
                                    ((?j. a <= j /\ j <= b /\ f j) <=>
                                     f a \/ ?j. a + 1 <= j /\ j <= b /\ f j)
*)

(* ------------------------------------------------------------------------- *)
(* List Theorems                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ls <> [] <=> (ls = HD ls::TL ls) *)
(* Proof:
   If part: ls <> [] ==> (ls = HD ls::TL ls)
       ls <> []
   ==> ?h t. ls = h::t         by list_CASES
   ==> ls = (HD ls)::(TL ls)   by HD, TL
   Only-if part: (ls = HD ls::TL ls) ==> ls <> []
   This is true                by NOT_NIL_CONS
*)
val LIST_NOT_NIL = store_thm(
  "LIST_NOT_NIL",
  ``!ls. ls <> [] <=> (ls = HD ls::TL ls)``,
  metis_tac[list_CASES, HD, TL, NOT_NIL_CONS]);

(* NOT_NIL_EQ_LENGTH_NOT_0  |- x <> [] <=> 0 < LENGTH x *)

(* Theorem: 0 < LENGTH ls <=> (ls = HD ls::TL ls) *)
(* Proof:
   If part: 0 < LENGTH ls ==> (ls = HD ls::TL ls)
      Note LENGTH ls <> 0                       by arithmetic
        so ~(NULL l)                            by NULL_LENGTH
        or ls = HD ls :: TL ls                  by CONS
   Only-if part: (ls = HD ls::TL ls) ==> 0 < LENGTH ls
      Note LENGTH ls = SUC (LENGTH (TL ls))     by LENGTH
       but 0 < SUC (LENGTH (TL ls))             by SUC_POS
*)
val LIST_HEAD_TAIL = store_thm(
  "LIST_HEAD_TAIL",
  ``!ls. 0 < LENGTH ls <=> (ls = HD ls::TL ls)``,
  metis_tac[LIST_NOT_NIL, NOT_NIL_EQ_LENGTH_NOT_0]);

(* Theorem: p <> [] /\ q <> [] ==> ((p = q) <=> ((HD p = HD q) /\ (TL p = TL q))) *)
(* Proof: by cases on p and cases on q, CONS_11 *)
val LIST_EQ_HEAD_TAIL = store_thm(
  "LIST_EQ_HEAD_TAIL",
  ``!p q. p <> [] /\ q <> [] ==>
         ((p = q) <=> ((HD p = HD q) /\ (TL p = TL q)))``,
  (Cases_on `p` >> Cases_on `q` >> fs[]));

(* Theorem: [x] = [y] <=> x = y *)
(* Proof: by EQ_LIST and notation. *)
val LIST_SING_EQ = store_thm(
  "LIST_SING_EQ",
  ``!x y. ([x] = [y]) <=> (x = y)``,
  rw_tac bool_ss[]);

(* Note: There is LENGTH_NIL, but no LENGTH_NON_NIL *)

(* Theorem: 0 < LENGTH l <=> l <> [] *)
(* Proof:
   Since  (LENGTH l = 0) <=> (l = [])   by LENGTH_NIL
   l <> [] <=> LENGTH l <> 0,
            or 0 < LENGTH l             by NOT_ZERO_LT_ZERO
*)
val LENGTH_NON_NIL = store_thm(
  "LENGTH_NON_NIL",
  ``!l. 0 < LENGTH l <=> l <> []``,
  metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO]);

(* val LENGTH_EQ_0 = save_thm("LENGTH_EQ_0", LENGTH_EQ_NUM |> CONJUNCT1); *)
val LENGTH_EQ_0 = save_thm("LENGTH_EQ_0", LENGTH_NIL);
(* > val LENGTH_EQ_0 = |- !l. (LENGTH l = 0) <=> (l = []): thm *)

(* Theorem: (LENGTH l = 1) <=> ?x. l = [x] *)
(* Proof:
   If part: (LENGTH l = 1) ==> ?x. l = [x]
     Since LENGTH l <> 0, l <> []  by LENGTH_NIL
        or ?h t. l = h::t          by list_CASES
       and LENGTH t = 0            by LENGTH
        so t = []                  by LENGTH_NIL
     Hence l = [x]
   Only-if part: (l = [x]) ==> (LENGTH l = 1)
     True by LENGTH.
*)
val LENGTH_EQ_1 = store_thm(
  "LENGTH_EQ_1",
  ``!l. (LENGTH l = 1) <=> ?x. l = [x]``,
  rw[EQ_IMP_THM] >| [
    `LENGTH l <> 0` by decide_tac >>
    `?h t. l = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `SUC (LENGTH t) = 1` by metis_tac[LENGTH] >>
    `LENGTH t = 0` by decide_tac >>
    metis_tac[LENGTH_NIL],
    rw[]
  ]);

(* Theorem: LENGTH [x] = 1 *)
(* Proof: by LENGTH, ONE. *)
val LENGTH_SING = store_thm(
  "LENGTH_SING",
  ``!x. LENGTH [x] = 1``,
  rw_tac bool_ss[LENGTH, ONE]);

(* Theorem: ls <> [] ==> LENGTH (TL ls) < LENGTH ls *)
(* Proof: by LENGTH_TL, LENGTH_EQ_0 *)
val LENGTH_TL_LT = store_thm(
  "LENGTH_TL_LT",
  ``!ls. ls <> [] ==> LENGTH (TL ls) < LENGTH ls``,
  metis_tac[LENGTH_TL, LENGTH_EQ_0, NOT_ZERO_LT_ZERO, DECIDE``n <> 0 ==> n - 1 < n``]);

val SNOC_NIL = save_thm("SNOC_NIL", SNOC |> CONJUNCT1);
(* > val SNOC_NIL = |- !x. SNOC x [] = [x]: thm *)
val SNOC_CONS = save_thm("SNOC_CONS", SNOC |> CONJUNCT2);
(* > val SNOC_CONS = |- !x x' l. SNOC x (x'::l) = x'::SNOC x l: thm *)

(* Theorem: l <> [] ==> (l = SNOC (LAST l) (FRONT l)) *)
(* Proof:
     l
   = FRONT l ++ [LAST l]      by APPEND_FRONT_LAST, l <> []
   = SNOC (LAST l) (FRONT l)  by SNOC_APPEND
*)
val SNOC_LAST_FRONT = store_thm(
  "SNOC_LAST_FRONT",
  ``!l. l <> [] ==> (l = SNOC (LAST l) (FRONT l))``,
  rw[APPEND_FRONT_LAST]);

(* Theorem alias *)
val MAP_COMPOSE = save_thm("MAP_COMPOSE", MAP_MAP_o);
(* val MAP_COMPOSE = |- !f g l. MAP f (MAP g l) = MAP (f o g) l: thm *)

(* Theorem: MAP f [x] = [f x] *)
(* Proof: by MAP *)
val MAP_SING = store_thm(
  "MAP_SING",
  ``!f x. MAP f [x] = [f x]``,
  rw[]);


(*
LAST_EL  |- !ls. ls <> [] ==> LAST ls = EL (PRE (LENGTH ls)) ls
*)

(* Theorem: t <> [] ==> (LAST t = EL (LENGTH t) (h::t)) *)
(* Proof:
   Note LENGTH t <> 0                      by LENGTH_EQ_0
     or 0 < LENGTH t
        LAST t
      = EL (PRE (LENGTH t)) t              by LAST_EL
      = EL (SUC (PRE (LENGTH t))) (h::t)   by EL
      = EL (LENGTH t) (h::t)               bu SUC_PRE, 0 < LENGTH t
*)
val LAST_EL_CONS = store_thm(
  "LAST_EL_CONS",
  ``!h t. t <> [] ==> (LAST t = EL (LENGTH t) (h::t))``,
  rpt strip_tac >>
  `0 < LENGTH t` by metis_tac[LENGTH_EQ_0, NOT_ZERO_LT_ZERO] >>
  `LAST t = EL (PRE (LENGTH t)) t` by rw[LAST_EL] >>
  `_ = EL (SUC (PRE (LENGTH t))) (h::t)` by rw[] >>
  metis_tac[SUC_PRE]);

(* Theorem alias *)
val FRONT_LENGTH = save_thm ("FRONT_LENGTH", LENGTH_FRONT);
(* val FRONT_LENGTH = |- !l. l <> [] ==> (LENGTH (FRONT l) = PRE (LENGTH l)): thm *)

val FRONT_EL = save_thm ("FRONT_EL", EL_FRONT);
(* val FRONT_EL = |- !l n. n < LENGTH (FRONT l) /\ ~NULL l ==> (EL n (FRONT l) = EL n l) *)
(* This is not convenient. *)

(* Theorem: l <> [] /\ n < LENGTH (FRONT l) ==> (EL n (FRONT l) = EL n l) *)
(* Proof: by EL_FRONT, NULL *)
val FRONT_EL = store_thm(
  "FRONT_EL",
  ``!l n. l <> [] /\ n < LENGTH (FRONT l) ==> (EL n (FRONT l) = EL n l)``,
  metis_tac[EL_FRONT, NULL, list_CASES]);

(* Theorem: (LENGTH l = 1) ==> (FRONT l = []) *)
(* Proof:
   Note ?x. l = [x]     by LENGTH_EQ_1
     FRONT l
   = FRONT [x]          by above
   = []                 by FRONT_DEF
*)
val FRONT_EQ_NIL = store_thm(
  "FRONT_EQ_NIL",
  ``!l. (LENGTH l = 1) ==> (FRONT l = [])``,
  rw[LENGTH_EQ_1] >>
  rw[FRONT_DEF]);

(* Theorem: 1 < LENGTH l ==> FRONT l <> [] *)
(* Proof:
   Note LENGTH l <> 0          by 1 < LENGTH l
   Thus ?h s. l = h::s         by list_CASES
     or 1 < 1 + LENGTH s
     so 0 < LENGTH s           by arithmetic
   Thus ?k t. s = k::t         by list_CASES
      FRONT l
    = FRONT (h::k::t)
    = h::FRONT (k::t)          by FRONT_CONS
    <> []                      by list_CASES
*)
val FRONT_NON_NIL = store_thm(
  "FRONT_NON_NIL",
  ``!l. 1 < LENGTH l ==> FRONT l <> []``,
  rpt strip_tac >>
  `LENGTH l <> 0` by decide_tac >>
  `?h s. l = h::s` by metis_tac[list_CASES, LENGTH_EQ_0] >>
  `LENGTH l = 1 + LENGTH s` by rw[] >>
  `LENGTH s <> 0` by decide_tac >>
  `?k t. s = k::t` by metis_tac[list_CASES, LENGTH_EQ_0] >>
  `FRONT l = h::FRONT (k::t)` by fs[FRONT_CONS] >>
  fs[]);

(* Theorem: ls <> [] ==> MEM (HD ls) ls *)
(* Proof:
   Note ls = h::t      by list_CASES
        MEM (HD (h::t)) (h::t)
    <=> MEM h (h::t)   by HD
    <=> T              by MEM
*)
val HEAD_MEM = store_thm(
  "HEAD_MEM",
  ``!ls. ls <> [] ==> MEM (HD ls) ls``,
  (Cases_on `ls` >> simp[]));

(* Theorem: ls <> [] ==> MEM (LAST ls) ls *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> MEM (LAST []) []
      True by [] <> [] = F.
   Step: ls <> [] ==> MEM (LAST ls) ls ==>
         !h. h::ls <> [] ==> MEM (LAST (h::ls)) (h::ls)
      If ls = [],
             MEM (LAST [h]) [h]
         <=> MEM h [h]          by LAST_DEF
         <=> T                  by MEM
      If ls <> [],
             MEM (LAST [h::ls]) (h::ls)
         <=> MEM (LAST ls) (h::ls)             by LAST_DEF
         <=> LAST ls = h \/ MEM (LAST ls) ls   by MEM
         <=> LAST ls = h \/ T                  by induction hypothesis
         <=> T                                 by logical or
*)
val LAST_MEM = store_thm(
  "LAST_MEM",
  ``!ls. ls <> [] ==> MEM (LAST ls) ls``,
  Induct >-
  decide_tac >>
  (Cases_on `ls = []` >> rw[LAST_DEF]));

(* Theorem: DROP 1 (h::t) = t *)
(* Proof: DROP_def *)
val DROP_1 = store_thm(
  "DROP_1",
  ``!h t. DROP 1 (h::t) = t``,
  rw[]);

(* Theorem: FRONT [x] = [] *)
(* Proof: FRONT_def *)
val FRONT_SING = store_thm(
  "FRONT_SING",
  ``!x. FRONT [x] = []``,
  rw[]);

(* Theorem: ls <> [] ==> (TL ls = DROP 1 ls) *)
(* Proof:
   Note ls = h::t        by list_CASES
     so TL (h::t)
      = t                by TL
      = DROP 1 (h::t)    by DROP_def
*)
val TAIL_BY_DROP = store_thm(
  "TAIL_BY_DROP",
  ``!ls. ls <> [] ==> (TL ls = DROP 1 ls)``,
  Cases_on `ls` >-
  decide_tac >>
  rw[]);

(* Theorem: ls <> [] ==> (FRONT ls = TAKE (LENGTH ls - 1) ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> FRONT [] = TAKE (LENGTH [] - 1) []
      True by [] <> [] = F.
   Step: ls <> [] ==> FRONT ls = TAKE (LENGTH ls - 1) ls ==>
         !h. h::ls <> [] ==> FRONT (h::ls) = TAKE (LENGTH (h::ls) - 1) (h::ls)
      If ls = [],
           FRONT [h]
         = []                          by FRONT_SING
         = TAKE 0 [h]                  by TAKE_0
         = TAKE (LENGTH [h] - 1) [h]   by LENGTH_SING
      If ls <> [],
           FRONT (h::ls)
         = h::FRONT ls                        by FRONT_DEF
         = h::TAKE (LENGTH ls - 1) ls         by induction hypothesis
         = TAKE (LENGTH (h::ls) - 1) (h::ls)  by TAKE_def
*)
val FRONT_BY_TAKE = store_thm(
  "FRONT_BY_TAKE",
  ``!ls. ls <> [] ==> (FRONT ls = TAKE (LENGTH ls - 1) ls)``,
  Induct >-
  decide_tac >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `LENGTH ls <> 0` by rw[] >>
  rw[FRONT_DEF]);

(* Theorem: HD (h::t ++ ls) = h *)
(* Proof:
     HD (h::t ++ ls)
   = HD (h::(t ++ ls))     by APPEND
   = h                     by HD
*)
Theorem HD_APPEND:
  !h t ls. HD (h::t ++ ls) = h
Proof
  simp[]
QED

(* Theorem: 0 <> n ==> (EL (n-1) t = EL n (h::t)) *)
(* Proof:
   Note n = SUC k for some k         by num_CASES
     so EL k t = EL (SUC k) (h::t)   by EL_restricted
*)
Theorem EL_TAIL:
  !h t n. 0 <> n ==> (EL (n-1) t = EL n (h::t))
Proof
  rpt strip_tac >>
  `n = SUC (n - 1)` by decide_tac >>
  metis_tac[EL_restricted]
QED

(* Idea: If all elements are the same, the set is SING. *)

(* Theorem: ls <> [] /\ EVERY ($= c) ls ==> SING (set ls) *)
(* Proof:
   Note set ls = {c}       by LIST_TO_SET_EQ_SING
   thus SING (set ls)      by SING_DEF
*)
Theorem MONOLIST_SET_SING:
  !c ls. ls <> [] /\ EVERY ($= c) ls ==> SING (set ls)
Proof
  metis_tac[LIST_TO_SET_EQ_SING, SING_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* List Reversal.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Overload for REVERSE [m .. n] *)
val _ = overload_on ("downto", ``\n m. REVERSE [m .. n]``);
val _ = set_fixity "downto" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: REVERSE [x] = [x] *)
(* Proof:
      REVERSE [x]
    = [] ++ [x]       by REVERSE_DEF
    = [x]             by APPEND
*)
val REVERSE_SING = store_thm(
  "REVERSE_SING",
  ``!x. REVERSE [x] = [x]``,
  rw[]);

(* Theorem: ls <> [] ==> (HD (REVERSE ls) = LAST ls) *)
(* Proof:
      HD (REVERSE ls)
    = HD (REVERSE (SNOC (LAST ls) (FRONT ls)))   by SNOC_LAST_FRONT
    = HD (LAST ls :: (REVERSE (FRONT ls))        by REVERSE_SNOC
    = LAST ls                                    by HD
*)
Theorem REVERSE_HD:
  !ls. ls <> [] ==> (HD (REVERSE ls) = LAST ls)
Proof
  metis_tac[SNOC_LAST_FRONT, REVERSE_SNOC, HD]
QED

(* Theorem: ls <> [] ==> (TL (REVERSE ls) = REVERSE (FRONT ls)) *)
(* Proof:
      TL (REVERSE ls)
    = TL (REVERSE (SNOC (LAST ls) (FRONT ls)))   by SNOC_LAST_FRONT
    = TL (LAST ls :: (REVERSE (FRONT ls))        by REVERSE_SNOC
    = REVERSE (FRONT ls)                         by TL
*)
Theorem REVERSE_TL:
  !ls. ls <> [] ==> (TL (REVERSE ls) = REVERSE (FRONT ls))
Proof
  metis_tac[SNOC_LAST_FRONT, REVERSE_SNOC, TL]
QED

(* ------------------------------------------------------------------------- *)
(* Extra List Theorems                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: EVERY (\c. c IN R) p ==> !k. k < LENGTH p ==> EL k p IN R *)
(* Proof: by EVERY_EL. *)
val EVERY_ELEMENT_PROPERTY = store_thm(
  "EVERY_ELEMENT_PROPERTY",
  ``!p R. EVERY (\c. c IN R) p ==> !k. k < LENGTH p ==> EL k p IN R``,
  rw[EVERY_EL]);

(* Theorem: (!x. P x ==> (Q o f) x) /\ EVERY P l ==> EVERY Q (MAP f l) *)
(* Proof:
   Since !x. P x ==> (Q o f) x,
         EVERY P l
     ==> EVERY Q o f l         by EVERY_MONOTONIC
     ==> EVERY Q (MAP f l)     by EVERY_MAP
*)
val EVERY_MONOTONIC_MAP = store_thm(
  "EVERY_MONOTONIC_MAP",
  ``!l f P Q. (!x. P x ==> (Q o f) x) /\ EVERY P l ==> EVERY Q (MAP f l)``,
  metis_tac[EVERY_MONOTONIC, EVERY_MAP]);

(* Theorem: EVERY (\j. j < n) ls ==> EVERY (\j. j <= n) ls *)
(* Proof: by EVERY_EL, arithmetic. *)
val EVERY_LT_IMP_EVERY_LE = store_thm(
  "EVERY_LT_IMP_EVERY_LE",
  ``!ls n. EVERY (\j. j < n) ls ==> EVERY (\j. j <= n) ls``,
  simp[EVERY_EL, LESS_IMP_LESS_OR_EQ]);

(* Theorem: LENGTH l1 = LENGTH l2 ==> ZIP (SNOC x1 l1, SNOC x2 l2) = SNOC (x1, x2) ZIP (l1, l2) *)
(* Proof:
   By induction on l1,
   Base case: !l2. (LENGTH [] = LENGTH l2) ==> (ZIP (SNOC x1 [],SNOC x2 l2) = SNOC (x1,x2) (ZIP ([],l2)))
     Since LENGTH l2 = LENGTH [] = 0, l2 = []      by LENGTH_NIL
       ZIP (SNOC x1 [],SNOC x2 [])
     = ZIP ([x1], [x2])              by SNOC
     = ([x1], [x2])                  by ZIP
     = SNOC ([x1], [x2]) []          by SNOC
     = SNOC ([x1], [x2]) ZIP ([][])  by ZIP
   Step case: !h l2. (LENGTH (h::l1) = LENGTH l2) ==> (ZIP (SNOC x1 (h::l1),SNOC x2 l2) = SNOC (x1,x2) (ZIP (h::l1,l2)))
     Expand by LENGTH_CONS, this is to show:
       ZIP (h::(l1 ++ [x1]),h'::l' ++ [x2]) = ZIP (h::l1,h'::l') ++ [(x1,x2)]
       ZIP (h::(l1 ++ [x1]),h'::l' ++ [x2])
     = (h, h') :: ZIP (l1 ++ [x1],l' ++ [x2])       by ZIP
     = (h, h') :: ZIP (SNOC x1 l1, SNOC x2 l')      by SNOC
     = (h, h') :: SNOC (x1, x2) (ZIP (l1, l'))      by induction hypothesis
     = (h, h') :: ZIP (l1, l') ++ [(x1, x2)]        by SNOC
     = ZIP (h::l1, h'::l') ++ [(x1, x2)]            by ZIP
*)
val ZIP_SNOC = store_thm(
  "ZIP_SNOC",
  ``!x1 x2 l1 l2. (LENGTH l1 = LENGTH l2) ==> (ZIP (SNOC x1 l1, SNOC x2 l2) = SNOC (x1, x2) (ZIP (l1, l2)))``,
  ntac 2 strip_tac >>
  Induct_on `l1` >-
  rw[] >>
  rw[LENGTH_CONS] >>
  `ZIP (h::(l1 ++ [x1]),h'::l' ++ [x2]) = (h, h') :: ZIP (l1 ++ [x1],l' ++ [x2])` by rw[] >>
  `_ = (h, h') :: ZIP (SNOC x1 l1, SNOC x2 l')` by rw[] >>
  `_ = (h, h') :: SNOC (x1, x2) (ZIP (l1, l'))` by metis_tac[] >>
  `_ = (h, h') :: ZIP (l1, l') ++ [(x1, x2)]` by rw[] >>
  `_ = ZIP (h::l1, h'::l') ++ [(x1, x2)]` by rw[] >>
  metis_tac[]);

(* MAP_ZIP_SAME  |- !ls f. MAP f (ZIP (ls,ls)) = MAP (\x. f (x,x)) ls *)

(* Theorem: ZIP ((MAP f ls), (MAP g ls)) = MAP (\x. (f x, g x)) ls *)
(* Proof:
     ZIP ((MAP f ls), (MAP g ls))
   = MAP (\(x, y). (f x, y)) (ZIP (ls, (MAP g ls)))                    by ZIP_MAP
   = MAP (\(x, y). (f x, y)) (MAP (\(x, y). (x, g y)) (ZIP (ls, ls)))  by ZIP_MAP
   = MAP (\(x, y). (f x, y)) (MAP (\j. (\(x, y). (x, g y)) (j,j)) ls)  by MAP_ZIP_SAME
   = MAP (\(x, y). (f x, y)) o (\j. (\(x, y). (x, g y)) (j,j)) ls      by MAP_COMPOSE
   = MAP (\x. (f x, g x)) ls                                           by FUN_EQ_THM
*)
val ZIP_MAP_MAP = store_thm(
  "ZIP_MAP_MAP",
  ``!ls f g. ZIP ((MAP f ls), (MAP g ls)) = MAP (\x. (f x, g x)) ls``,
  rw[ZIP_MAP, MAP_COMPOSE] >>
  qabbrev_tac `f1 = \p. (f (FST p),SND p)` >>
  qabbrev_tac `f2 = \x. (x,g x)` >>
  qabbrev_tac `f3 = \x. (f x,g x)` >>
  `f1 o f2 = f3` by rw[FUN_EQ_THM, Abbr`f1`, Abbr`f2`, Abbr`f3`] >>
  rw[]);

(* Theorem: MAP2 f (MAP g1 ls) (MAP g2 ls) = MAP (\x. f (g1 x) (g2 x)) ls *)
(* Proof:
   Let k = LENGTH ls.
     Note LENGTH (MAP g1 ls) = k      by LENGTH_MAP
      and LENGTH (MAP g2 ls) = k      by LENGTH_MAP
     MAP2 f (MAP g1 ls) (MAP g2 ls)
   = MAP (UNCURRY f) (ZIP ((MAP g1 ls), (MAP g2 ls)))      by MAP2_MAP
   = MAP (UNCURRY f) (MAP (\x. (g1 x, g2 x)) ls)           by ZIP_MAP_MAP
   = MAP ((UNCURRY f) o (\x. (g1 x, g2 x))) ls             by MAP_COMPOSE
   = MAP (\x. f (g1 x) (g2 y)) ls                          by FUN_EQ_THM
*)
val MAP2_MAP_MAP = store_thm(
  "MAP2_MAP_MAP",
  ``!ls f g1 g2. MAP2 f (MAP g1 ls) (MAP g2 ls) = MAP (\x. f (g1 x) (g2 x)) ls``,
  rw[MAP2_MAP, ZIP_MAP_MAP, MAP_COMPOSE] >>
  qabbrev_tac `f1 = UNCURRY f o (\x. (g1 x,g2 x))` >>
  qabbrev_tac `f2 = \x. f (g1 x) (g2 x)` >>
  `f1 = f2` by rw[FUN_EQ_THM, Abbr`f1`, Abbr`f2`] >>
  rw[]);

(* Theorem: EL n (l1 ++ l2) = if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2 *)
(* Proof: by EL_APPEND1, EL_APPEND2 *)
val EL_APPEND = store_thm(
  "EL_APPEND",
  ``!n l1 l2. EL n (l1 ++ l2) = if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2``,
  rw[EL_APPEND1, EL_APPEND2]);

(* Theorem: (LENGTH (h1::t1) = LENGTH (h2::t2)) /\
            (!k. k < LENGTH (h1::t1) ==> P (EL k (h1::t1)) (EL k (h2::t2))) ==>
           (P h1 h2) /\ (!k. k < LENGTH t1 ==> P (EL k t1) (EL k t2)) *)
(* Proof:
   Put k = 0,
   Then LENGTH (h1::t1) = SUC (LENGTH t1)     by LENGTH
                        > 0                   by SUC_POS
    and P (EL 0 (h1::t1)) (EL 0 (h2::t2))     by implication, 0 < LENGTH (h1::t1)
     or P HD (h1::t1) HD (h2::t2)             by EL
     or P h1 h2                               by HD
   Note k < LENGTH t1
    ==> k + 1 < SUC (LENGTH t1)                           by ADD1
              = LENGTH (h1::t1)                           by LENGTH
   Thus P (EL (k + 1) (h1::t1)) (EL (k + 1) (h2::t2))     by implication
     or P (EL (PRE (k + 1) t1)) (EL (PRE (k + 1)) t2)     by EL_CONS
     or P (EL k t1) (EL k t2)                             by PRE, ADD1
*)
val EL_ALL_PROPERTY = store_thm(
  "EL_ALL_PROPERTY",
  ``!h1 t1 h2 t2 P. (LENGTH (h1::t1) = LENGTH (h2::t2)) /\
     (!k. k < LENGTH (h1::t1) ==> P (EL k (h1::t1)) (EL k (h2::t2))) ==>
     (P h1 h2) /\ (!k. k < LENGTH t1 ==> P (EL k t1) (EL k t2))``,
  rpt strip_tac >| [
    `0 < LENGTH (h1::t1)` by metis_tac[LENGTH, SUC_POS] >>
    metis_tac[EL, HD],
    `k + 1 < SUC (LENGTH t1)` by decide_tac >>
    `k + 1 < LENGTH (h1::t1)` by metis_tac[LENGTH] >>
    `0 < k + 1 /\ (PRE (k + 1) = k)` by decide_tac >>
    metis_tac[EL_CONS]
  ]);

(* Theorem: (l1 ++ l2 = m1 ++ m2) /\ (LENGTH l1 = LENGTH m1) <=> (l1 = m1) /\ (l2 = m2) *)
(* Proof:
   By APPEND_EQ_APPEND,
   ?l. (l1 = m1 ++ l) /\ (m2 = l ++ l2) \/ ?l. (m1 = l1 ++ l) /\ (l2 = l ++ m2).
   Thus this is to show:
   (1) LENGTH (m1 ++ l) = LENGTH m1 ==> m1 ++ l = m1, true since l = [] by LENGTH_APPEND, LENGTH_NIL
   (2) LENGTH (m1 ++ l) = LENGTH m1 ==> l2 = l ++ l2, true since l = [] by LENGTH_APPEND, LENGTH_NIL
   (3) LENGTH l1 = LENGTH (l1 ++ l) ==> l1 = l1 ++ l, true since l = [] by LENGTH_APPEND, LENGTH_NIL
   (4) LENGTH l1 = LENGTH (l1 ++ l) ==> l ++ m2 = m2, true since l = [] by LENGTH_APPEND, LENGTH_NIL
*)
val APPEND_EQ_APPEND_EQ = store_thm(
  "APPEND_EQ_APPEND_EQ",
  ``!l1 l2 m1 m2. (l1 ++ l2 = m1 ++ m2) /\ (LENGTH l1 = LENGTH m1) <=> (l1 = m1) /\ (l2 = m2)``,
  rw[APPEND_EQ_APPEND] >>
  rw[EQ_IMP_THM] >-
  fs[] >-
  fs[] >-
 (fs[] >>
  `LENGTH l = 0` by decide_tac >>
  fs[]) >>
  fs[] >>
  `LENGTH l = 0` by decide_tac >>
  fs[]);

(*
LUPDATE_SEM     |- (!e n l. LENGTH (LUPDATE e n l) = LENGTH l) /\
                    !e n l p. p < LENGTH l ==> EL p (LUPDATE e n l) = if p = n then e else EL p l
EL_LUPDATE      |- !ys x i k. EL i (LUPDATE x k ys) = if i = k /\ k < LENGTH ys then x else EL i ys
LENGTH_LUPDATE  |- !x n ys. LENGTH (LUPDATE x n ys) = LENGTH ys
*)

(* Extract useful theorem from LUPDATE semantics *)
val LUPDATE_LEN = save_thm("LUPDATE_LEN", LUPDATE_SEM |> CONJUNCT1);
(* val LUPDATE_LEN = |- !e n l. LENGTH (LUPDATE e n l) = LENGTH l: thm *)
val LUPDATE_EL = save_thm("LUPDATE_EL", LUPDATE_SEM |> CONJUNCT2);
(* val LUPDATE_EL = |- !e n l p. p < LENGTH l ==> EL p (LUPDATE e n l) = if p = n then e else EL p l: thm *)

(* Theorem: LUPDATE q n (LUPDATE p n ls) = LUPDATE q n ls *)
(* Proof:
   Let l1 = LUPDATE q n (LUPDATE p n ls), l2 = LUPDATE q n ls.
   By LIST_EQ, this is to show:
   (1) LENGTH l1 = LENGTH l2
         LENGTH l1
       = LENGTH (LUPDATE q n (LUPDATE p n ls))  by notation
       = LENGTH (LUPDATE p n ls)                by LUPDATE_LEN
       = ls                                     by LUPDATE_LEN
       = LENGTH (LUPDATE q n ls)                by LUPDATE_LEN
       = LENGTH l2                              by notation
   (2) !x. x < LENGTH l1 ==> EL x l1 = EL x l2
         EL x l1
       = EL x (LUPDATE q n (LUPDATE p n ls))    by notation
       = if x = n then q else EL x (LUPDATE p n ls)            by LUPDATE_EL
       = if x = n then q else (if x = n then p else EL x ls)   by LUPDATE_EL
       = if x = n then q else EL x ls           by simplification
       = EL x (LUPDATE q n ls)                  by LUPDATE_EL
       = EL x l2                                by notation
*)
val LUPDATE_SAME_SPOT = store_thm(
  "LUPDATE_SAME_SPOT",
  ``!ls n p q. LUPDATE q n (LUPDATE p n ls) = LUPDATE q n ls``,
  rpt strip_tac >>
  qabbrev_tac `l1 = LUPDATE q n (LUPDATE p n ls)` >>
  qabbrev_tac `l2 = LUPDATE q n ls` >>
  `LENGTH l1 = LENGTH l2` by rw[LUPDATE_LEN, Abbr`l1`, Abbr`l2`] >>
  `!x. x < LENGTH l1 ==> (EL x l1 = EL x l2)` by fs[LUPDATE_EL, Abbr`l1`, Abbr`l2`] >>
  rw[LIST_EQ]);

(* Theorem: m <> n ==>
     (LUPDATE q n (LUPDATE p m ls) = LUPDATE p m (LUPDATE q n ls)) *)
(* Proof:
   Let l1 = LUPDATE q n (LUPDATE p m ls),
       l2 = LUPDATE p m (LUPDATE q n ls).
       LENGTH l1
     = LENGTH (LUPDATE q n (LUPDATE p m ls))  by notation
     = LENGTH (LUPDATE p m ls)                by LUPDATE_LEN
     = LENGTH ls                              by LUPDATE_LEN
     = LENGTH (LUPDATE q n ls)                by LUPDATE_LEN
     = LENGTH (LUPDATE p m (LUPDATE q n ls))  by LUPDATE_LEN
     = LENGTH l2                              by notation
      !x. x < LENGTH l1 ==>
      EL x l1
    = EL x ((LUPDATE q n (LUPDATE p m ls))    by notation
    = EL x ls  if x <> n, x <> m, or p if x = m, q if x = n
                                              by LUPDATE_EL
      EL x l2
    = EL x ((LUPDATE p m (LUPDATE q n ls))    by notation
    = EL x ls  if x <> m, x <> n, or q if x = n, p if x = m
                                              by LUPDATE_EL
    = EL x l1
   Hence l1 = l2                              by LIST_EQ
*)
val LUPDATE_DIFF_SPOT = store_thm(
  "LUPDATE_DIFF_SPOT",
  `` !ls m n p q. m <> n ==>
     (LUPDATE q n (LUPDATE p m ls) = LUPDATE p m (LUPDATE q n ls))``,
  rpt strip_tac >>
  qabbrev_tac `l1 = LUPDATE q n (LUPDATE p m ls)` >>
  qabbrev_tac `l2 = LUPDATE p m (LUPDATE q n ls)` >>
  irule LIST_EQ >>
  rw[LUPDATE_EL, Abbr`l1`, Abbr`l2`]);

(* Theorem: EL (LENGTH ls) (ls ++ h::t) = h *)
(* Proof:
   Let l2 = h::t.
   Note ~NULL l2                      by NULL
     so EL (LENGTH ls) (ls ++ h::t)
      = EL (LENGTH ls) (ls ++ l2)     by notation
      = HD l2                         by EL_LENGTH_APPEND
      = HD (h::t) = h                 by notation
*)
val EL_LENGTH_APPEND_0 = store_thm(
  "EL_LENGTH_APPEND_0",
  ``!ls h t. EL (LENGTH ls) (ls ++ h::t) = h``,
  rw[EL_LENGTH_APPEND]);

(* Theorem: EL (LENGTH ls + 1) (ls ++ h::k::t) = k *)
(* Proof:
   Let l1 = ls ++ [h].
   Then LENGTH l1 = LENGTH ls + 1    by LENGTH
   Note ls ++ h::k::t = l1 ++ k::t   by APPEND
        EL (LENGTH ls + 1) (ls ++ h::k::t)
      = EL (LENGTH l1) (l1 ++ k::t)  by above
      = k                            by EL_LENGTH_APPEND_0
*)
val EL_LENGTH_APPEND_1 = store_thm(
  "EL_LENGTH_APPEND_1",
  ``!ls h k t. EL (LENGTH ls + 1) (ls ++ h::k::t) = k``,
  rpt strip_tac >>
  qabbrev_tac `l1 = ls ++ [h]` >>
  `LENGTH l1 = LENGTH ls + 1` by rw[Abbr`l1`] >>
  `ls ++ h::k::t = l1 ++ k::t` by rw[Abbr`l1`] >>
  metis_tac[EL_LENGTH_APPEND_0]);

(* Theorem: LUPDATE a (LENGTH ls) (ls ++ (h::t)) = ls ++ (a::t) *)
(* Proof:
     LUPDATE a (LENGTH ls) (ls ++ h::t)
   = ls ++ LUPDATE a (LENGTH ls - LENGTH ls) (h::t)   by LUPDATE_APPEND2
   = ls ++ LUPDATE a 0 (h::t)                         by arithmetic
   = ls ++ (a::t)                                     by LUPDATE_def
*)
val LUPDATE_APPEND_0 = store_thm(
  "LUPDATE_APPEND_0",
  ``!ls a h t. LUPDATE a (LENGTH ls) (ls ++ (h::t)) = ls ++ (a::t)``,
  rw_tac std_ss[LUPDATE_APPEND2, LUPDATE_def]);

(* Theorem: LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) = ls ++ h::b::t *)
(* Proof:
     LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t)
   = ls ++ LUPDATE b (LENGTH ls + 1 - LENGTH ls) (h::k::t)   by LUPDATE_APPEND2
   = ls ++ LUPDATE b 1 (h::k::t)                      by arithmetic
   = ls ++ (h::b::t)                                  by LUPDATE_def
*)
val LUPDATE_APPEND_1 = store_thm(
  "LUPDATE_APPEND_1",
  ``!ls b h k t. LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) = ls ++ h::b::t``,
  rpt strip_tac >>
  `LUPDATE b 1 (h::k::t) = h::LUPDATE b 0 (k::t)` by rw[GSYM LUPDATE_def] >>
  `_ = h::b::t` by rw[LUPDATE_def] >>
  `LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) =
    ls ++ LUPDATE b (LENGTH ls + 1 - LENGTH ls) (h::k::t)` by metis_tac[LUPDATE_APPEND2, DECIDE``n <= n + 1``] >>
  fs[]);

(* Theorem: LUPDATE b (LENGTH ls + 1)
              (LUPDATE a (LENGTH ls) (ls ++ h::k::t)) = ls ++ a::b::t *)
(* Proof:
   Let l1 = LUPDATE a (LENGTH ls) (ls ++ h::k::t)
          = ls ++ a::k::t       by LUPDATE_APPEND_0
     LUPDATE b (LENGTH ls + 1) l1
   = LUPDATE b (LENGTH ls + 1) (ls ++ a::k::t)
   = ls ++ a::b::t              by LUPDATE_APPEND2_1
*)
val LUPDATE_APPEND_0_1 = store_thm(
  "LUPDATE_APPEND_0_1",
  ``!ls a b h k t.
    LUPDATE b (LENGTH ls + 1)
      (LUPDATE a (LENGTH ls) (ls ++ h::k::t)) = ls ++ a::b::t``,
  rw_tac std_ss[LUPDATE_APPEND_0, LUPDATE_APPEND_1]);

(* ------------------------------------------------------------------------- *)
(* DROP and TAKE                                                             *)
(* ------------------------------------------------------------------------- *)

(* Note: There is TAKE_LENGTH_ID, but no DROP_LENGTH_NIL, now have DROP_LENGTH_TOO_LONG *)

(* Theorem: DROP (LENGTH l) l = [] *)
(* Proof:
   By induction on l.
   Base case: DROP (LENGTH []) [] = []
      True by DROP_def: DROP n [] = [].
   Step case: DROP (LENGTH l) l = [] ==>
              !h. DROP (LENGTH (h::l)) (h::l) = []
    Since LENGTH (h::l) = SUC (LENGTH l)  by LENGTH
       so LENGTH (h::l) <> 0              by NOT_SUC
      and SUC (LENGTH l) - 1 = LENGTH l   by SUC_SUB1
      DROP (LENGTH (h::l) (h::l)
    = DROP (LENGTH l) l                   by DROP_def
    = []                                  by induction hypothesis
*)
val DROP_LENGTH_NIL = store_thm(
  "DROP_LENGTH_NIL",
  ``!l. DROP (LENGTH l) l = []``,
  Induct >> rw[]);

(* Theorem: n < LENGTH ls ==> (HD (DROP n ls) = EL n ls) *)
(* Proof:
     HD (DROP n ls)
   = HD (EL n ls :: DROP (n + 1) ls)    by DROP_EL_CONS, n < LENGTH ls
   = EL n ls
*)
val HD_DROP = store_thm(
  "HD_DROP",
  ``!ls n. n < LENGTH ls ==> (HD (DROP n ls) = EL n ls)``,
  rw[DROP_EL_CONS]);

(* Theorem: x <> [] ==> (TAKE 1 (x ++ y) = TAKE 1 x) *)
(* Proof:
   x <> [] means ?h t. x = h::t    by list_CASES
     TAKE 1 (x ++ y)
   = TAKE 1 ((h::t) ++ y)
   = TAKE 1 (h:: t ++ y)      by APPEND
   = h::TAKE 0 (t ++ y)       by TAKE_def
   = h::TAKE 0 t              by TAKE_0
   = TAKE 1 (h::t)            by TAKE_def
*)
val TAKE_1_APPEND = store_thm(
  "TAKE_1_APPEND",
  ``!x y. x <> [] ==> (TAKE 1 (x ++ y) = TAKE 1 x)``,
  Cases_on `x`>> rw[]);

(* Theorem: x <> [] ==> (DROP 1 (x ++ y) = (DROP 1 x) ++ y) *)
(* Proof:
   x <> [] means ?h t. x = h::t    by list_CASES
     DROP 1 (x ++ y)
   = DROP 1 ((h::t) ++ y)
   = DROP 1 (h:: t ++ y)      by APPEND
   = DROP 0 (t ++ y)          by DROP_def
   = t ++ y                   by DROP_0
   = (DROP 1 (h::t)) ++ y     by DROP_def
*)
val DROP_1_APPEND = store_thm(
  "DROP_1_APPEND",
  ``!x y. x <> [] ==> (DROP 1 (x ++ y) = (DROP 1 x) ++ y)``,
  Cases_on `x` >> rw[]);

(* Theorem: DROP (SUC n) x = DROP 1 (DROP n x) *)
(* Proof:
   By induction on x.
   Base case: !n. DROP (SUC n) [] = DROP 1 (DROP n [])
     LHS = DROP (SUC n) []  = []  by DROP_def
     RHS = DROP 1 (DROP n [])
         = DROP 1 []              by DROP_def
         = [] = LHS               by DROP_def
   Step case: !n. DROP (SUC n) x = DROP 1 (DROP n x) ==>
              !h n. DROP (SUC n) (h::x) = DROP 1 (DROP n (h::x))
     If n = 0,
     LHS = DROP (SUC 0) (h::x)
         = DROP 1 (h::x)          by ONE
     RHS = DROP 1 (DROP 0 (h::x))
         = DROP 1 (h::x) = LHS    by DROP_0
     If n <> 0,
     LHS = DROP (SUC n) (h::x)
         = DROP n x               by DROP_def
     RHS = DROP 1 (DROP n (h::x)
         = DROP 1 (DROP (n-1) x)  by DROP_def
         = DROP (SUC (n-1)) x     by induction hypothesis
         = DROP n x = LHS         by SUC (n-1) = n, n <> 0.
*)
val DROP_SUC = store_thm(
  "DROP_SUC",
  ``!n x. DROP (SUC n) x = DROP 1 (DROP n x)``,
  Induct_on `x` >>
  rw[DROP_def] >>
  `n = SUC (n-1)` by decide_tac >>
  metis_tac[]);

(* Theorem: TAKE (SUC n) x = (TAKE n x) ++ (TAKE 1 (DROP n x)) *)
(* Proof:
   By induction on x.
   Base case: !n. TAKE (SUC n) [] = TAKE n [] ++ TAKE 1 (DROP n [])
     LHS = TAKE (SUC n) [] = []    by TAKE_def
     RHS = TAKE n [] ++ TAKE 1 (DROP n [])
         = [] ++ TAKE 1 []         by TAKE_def, DROP_def
         = TAKE 1 []               by APPEND
         = [] = LHS                by TAKE_def
   Step case: !n. TAKE (SUC n) x = TAKE n x ++ TAKE 1 (DROP n x) ==>
              !h n. TAKE (SUC n) (h::x) = TAKE n (h::x) ++ TAKE 1 (DROP n (h::x))
     If n = 0,
     LHS = TAKE (SUC 0) (h::x)
         = TAKE 1 (h::x)           by ONE
     RHS = TAKE 0 (h::x) ++ TAKE 1 (DROP 0 (h::x))
         = [] ++ TAKE 1 (h::x)     by TAKE_def, DROP_def
         = TAKE 1 (h::x) = LHS     by APPEND
     If n <> 0,
     LHS = TAKE (SUC n) (h::x)
         = h :: TAKE n x           by TAKE_def
     RHS = TAKE n (h::x) ++ TAKE 1 (DROP n (h::x))
         = (h:: TAKE (n-1) x) ++ TAKE 1 (DROP (n-1) x)   by TAKE_def, DROP_def, n <> 0.
         = h :: (TAKE (n-1) x ++ TAKE 1 (DROP (n-1) x))  by APPEND
         = h :: TAKE (SUC (n-1)) x  by induction hypothesis
         = h :: TAKE n x            by SUC (n-1) = n, n <> 0.
*)
val TAKE_SUC = store_thm(
  "TAKE_SUC",
  ``!n x. TAKE (SUC n) x = (TAKE n x) ++ (TAKE 1 (DROP n x))``,
  Induct_on `x` >>
  rw[TAKE_def, DROP_def] >>
  `n = SUC (n-1)` by decide_tac >>
  metis_tac[]);

(* Theorem: k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x)) *)
(* Proof:
   By induction on k.
   Base case: !x. 0 < LENGTH x ==> (TAKE (SUC 0) x = SNOC (EL 0 x) (TAKE 0 x))
         0 < LENGTH x
     ==> ?h t. x = h::t   by LENGTH_NIL, list_CASES
     LHS = TAKE (SUC 0) x
         = TAKE 1 (h::t)   by ONE
         = h::TAKE 0 t     by TAKE_def
         = h::[]           by TAKE_0
         = [h]
         = SNOC h []       by SNOC
         = SNOC h (TAKE 0 (h::t))             by TAKE_0
         = SNOC (EL 0 (h::t)) (TAKE 0 (h::t)) by EL
         = RHS
   Step case: !x. k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x)) ==>
     !x. SUC k < LENGTH x ==> (TAKE (SUC (SUC k)) x = SNOC (EL (SUC k) x) (TAKE (SUC k) x))
     Since 0 < SUC k                        by prim_recTheory.LESS_0
           0 < LENGTH x                     by LESS_TRANS
       ==> ?h t. x = h::t                   by LENGTH_NIL, list_CASES
       and LENGTH (h::t) = SUC (LENGTH t)   by LENGTH
     hence k < LENGTH t                     by LESS_MONO_EQ
     LHS = TAKE (SUC (SUC k)) (h::t)
         = h :: TAKE (SUC k) t              by TAKE_def
         = h :: SNOC (EL k t) (TAKE k t)    by induction hypothesis, k < LENGTH t.
         = SNOC (EL k t) (h :: TAKE k t)    by SNOC
         = SNOC (EL (SUC k) (h::t)) (h :: TAKE k t)         by EL_restricted
         = SNOC (EL (SUC k) (h::t)) (TAKE (SUC k) (h::t))   by TAKE_def
         = RHS
*)
val TAKE_SUC_BY_TAKE = store_thm(
  "TAKE_SUC_BY_TAKE",
  ``!k x. k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x))``,
  Induct_on `k` >| [
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    rw[],
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `k < LENGTH t` by metis_tac[LENGTH, LESS_MONO_EQ] >>
    rw_tac std_ss[TAKE_def, SNOC, EL_restricted]
  ]);

(* Theorem: k < LENGTH x ==> (DROP k x = (EL k x) :: (DROP (SUC k) x)) *)
(* Proof:
   By induction on k.
   Base case: !x. 0 < LENGTH x ==> (DROP 0 x = EL 0 x::DROP (SUC 0) x)
         0 < LENGTH x
     ==> ?h t. x = h::t   by LENGTH_NIL, list_CASES
     LHS = DROP 0 (h::t)
         = h::t                            by DROP_0
         = (EL 0 (h::t))::t                by EL
         = (EL 0 (h::t))::(DROP 1 (h::t))  by DROP_def
         = EL 0 x::DROP (SUC 0) x          by ONE
         = RHS
   Step case: !x. k < LENGTH x ==> (DROP k x = EL k x::DROP (SUC k) x) ==>
              !x. SUC k < LENGTH x ==> (DROP (SUC k) x = EL (SUC k) x::DROP (SUC (SUC k)) x)
     Since 0 < SUC k                        by prim_recTheory.LESS_0
           0 < LENGTH x                     by LESS_TRANS
       ==> ?h t. x = h::t                   by LENGTH_NIL, list_CASES
       and LENGTH (h::t) = SUC (LENGTH t)   by LENGTH
     hence k < LENGTH t                     by LESS_MONO_EQ
     LHS = DROP (SUC k) (h::t)
         = DROP k t                         by DROP_def
         = EL k x::DROP (SUC k) x           by induction hypothesis
         = EL k t :: DROP (SUC (SUC k)) (h::t)           by DROP_def
         = EL (SUC k) (h::t)::DROP (SUC (SUC k)) (h::t)  by EL
         = RHS
*)
val DROP_BY_DROP_SUC = store_thm(
  "DROP_BY_DROP_SUC",
  ``!k x. k < LENGTH x ==> (DROP k x = (EL k x) :: (DROP (SUC k) x))``,
  Induct_on `k` >| [
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    rw[],
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `k < LENGTH t` by metis_tac[LENGTH, LESS_MONO_EQ] >>
    rw[]
  ]);

(* Theorem: n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u *)
(* Proof:
   By induction on n.
   Base: !ls. 0 < LENGTH ls ==> ?u. DROP 0 ls = [EL 0 ls] ++ u
       Note LENGTH ls <> 0        by 0 < LENGTH ls
        ==> ls <> []              by LENGTH_NIL
        ==> ?h t. ls = h::t       by list_CASES
         DROP 0 ls
       = ls                       by DROP_0
       = [h] ++ t                 by ls = h::t, CONS_APPEND
       = [EL 0 ls] ++ t           by EL
       Take u = t.
   Step: !ls. n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u ==>
         !ls. SUC n < LENGTH ls ==> ?u. DROP (SUC n) ls = [EL (SUC n) ls] ++ u
       Note LENGTH ls <> 0                  by SUC n < LENGTH ls
        ==> ?h t. ls = h::t                 by list_CASES, LENGTH_NIL
        Now LENGTH ls = SUC (LENGTH t)      by LENGTH
        ==> n < LENGTH t                    by SUC n < SUC (LENGTH t)
       Thus ?u. DROP n t = [EL n t] ++ u    by induction hypothesis

         DROP (SUC n) ls
       = DROP (SUC n) (h::t)                by ls = h::t
       = DROP n t                           by DROP_def
       = [EL n t] ++ u                      by above
       = [EL (SUC n) (h::t)] ++ u           by EL_restricted
       Take this u.
*)
val DROP_HEAD_ELEMENT = store_thm(
  "DROP_HEAD_ELEMENT",
  ``!ls n. n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u``,
  Induct_on `n` >| [
    rpt strip_tac >>
    `LENGTH ls <> 0` by decide_tac >>
    `?h t. ls = h::t` by metis_tac[list_CASES, LENGTH_NIL] >>
    rw[],
    rw[] >>
    `LENGTH ls <> 0` by decide_tac >>
    `?h t. ls = h::t` by metis_tac[list_CASES, LENGTH_NIL] >>
    `LENGTH ls = SUC (LENGTH t)` by rw[] >>
    `n < LENGTH t` by decide_tac >>
    `?u. DROP n t = [EL n t] ++ u` by rw[] >>
    rw[]
  ]);

(* Theorem: DROP n (TAKE n ls) = [] *)
(* Proof:
   If n <= LENGTH ls,
      Then LENGTH (TAKE n ls) = n           by LENGTH_TAKE_EQ
      Thus DROP n (TAKE n ls) = []          by DROP_LENGTH_TOO_LONG
   If LENGTH ls < n
      Then LENGTH (TAKE n ls) = LENGTH ls   by LENGTH_TAKE_EQ
      Thus DROP n (TAKE n ls) = []          by DROP_LENGTH_TOO_LONG
*)
val DROP_TAKE_EQ_NIL = store_thm(
  "DROP_TAKE_EQ_NIL",
  ``!ls n. DROP n (TAKE n ls) = []``,
  rw[LENGTH_TAKE_EQ, DROP_LENGTH_TOO_LONG]);

(* Theorem: TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls) *)
(* Proof:
   If n <= LENGTH ls,
      Then LENGTH (TAKE n ls) = n                       by LENGTH_TAKE_EQ, n <= LENGTH ls
        DROP n (TAKE (n + m) ls)
      = DROP n (TAKE n ls ++ TAKE m (DROP n ls))        by TAKE_SUM
      = DROP n (TAKE n ls) ++ DROP (n - LENGTH (TAKE n ls)) (TAKE m (DROP n ls))  by DROP_APPEND
      = [] ++ DROP (n - LENGTH (TAKE n ls)) (TAKE m (DROP n ls))     by DROP_TAKE_EQ_NIL
      = DROP (n - LENGTH (TAKE n ls)) (TAKE m (DROP n ls))           by APPEND
      = DROP 0 (TAKE m (DROP n ls))                                  by above
      = TAKE m (DROP n ls)                                           by DROP_0
   If LENGTH ls < n,
      Then DROP n ls = []         by DROP_LENGTH_TOO_LONG
       and TAKE (n + m) ls = ls   by TAKE_LENGTH_TOO_LONG
        DROP n (TAKE (n + m) ls)
      = DROP n ls                 by TAKE_LENGTH_TOO_LONG
      = []                        by DROP_LENGTH_TOO_LONG
      = TAKE m []                 by TAKE_nil
      = TAKE m (DROP n ls)        by DROP_LENGTH_TOO_LONG
*)
val TAKE_DROP_SWAP = store_thm(
  "TAKE_DROP_SWAP",
  ``!ls m n. TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls)``,
  rpt strip_tac >>
  Cases_on `n <= LENGTH ls` >| [
    qabbrev_tac `x = TAKE m (DROP n ls)` >>
    `DROP n (TAKE (n + m) ls) = DROP n (TAKE n ls ++ x)` by rw[TAKE_SUM, Abbr`x`] >>
    `_ = DROP n (TAKE n ls) ++ DROP (n - LENGTH (TAKE n ls)) x` by rw[DROP_APPEND] >>
    `_ = DROP (n - LENGTH (TAKE n ls)) x` by rw[DROP_TAKE_EQ_NIL] >>
    `_ = DROP 0 x` by rw[LENGTH_TAKE_EQ] >>
    rw[],
    `DROP n ls = []` by rw[DROP_LENGTH_TOO_LONG] >>
    `TAKE (n + m) ls = ls` by rw[TAKE_LENGTH_TOO_LONG] >>
    rw[]
  ]);

(* Theorem: TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2)) = l1 *)
(* Proof:
      TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2))
    = TAKE (LENGTH l1) (l1 ++ LUPDATE x k l2)      by LUPDATE_APPEND2
    = l1                                           by TAKE_LENGTH_APPEND
*)
val TAKE_LENGTH_APPEND2 = store_thm(
  "TAKE_LENGTH_APPEND2",
  ``!l1 l2 x k. TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2)) = l1``,
  rw_tac std_ss[LUPDATE_APPEND2, TAKE_LENGTH_APPEND]);

(* Theorem: LENGTH (TAKE n l) <= LENGTH l *)
(* Proof: by LENGTH_TAKE_EQ *)
val LENGTH_TAKE_LE = store_thm(
  "LENGTH_TAKE_LE",
  ``!n l. LENGTH (TAKE n l) <= LENGTH l``,
  rw[LENGTH_TAKE_EQ]);

(* ------------------------------------------------------------------------- *)
(* List Rotation.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define rotation of a list *)
val rotate_def = Define `
  rotate n l = DROP n l ++ TAKE n l
`;

(* Theorem: Rotate shifts element
            rotate n l = EL n l::(DROP (SUC n) l ++ TAKE n l) *)
(* Proof:
   h h t t t t t t  --> t t t t t h h
       k                k
   TAKE 2 x = h h
   DROP 2 x = t t t t t t
              k
   DROP 2 x ++ TAKE 2 x   has element k at front.

   Proof: by induction on l.
   Base case: !n. n < LENGTH [] ==> (DROP n [] = EL n []::DROP (SUC n) [])
     Since n < LENGTH [] = 0 is F, this is true.
   Step case: !h n. n < LENGTH (h::l) ==> (DROP n (h::l) = EL n (h::l)::DROP (SUC n) (h::l))
     i.e. n <> 0 /\ n < SUC (LENGTH l) ==> DROP (n - 1) l = EL n (h::l)::DROP n l  by DROP_def
     n <> 0 means ?j. n = SUC j < SUC (LENGTH l), so j < LENGTH l.
     LHS = DROP (SUC j - 1) l
         = DROP j l                    by SUC j - 1 = j
         = EL j l :: DROP (SUC j) l    by induction hypothesis
     RHS = EL (SUC j) (h::l) :: DROP (SUC (SUC j)) (h::l)
         = EL j l :: DROP (SUC j) l    by EL, DROP_def
         = LHS
*)
val rotate_shift_element = store_thm(
  "rotate_shift_element",
  ``!l n. n < LENGTH l ==> (rotate n l = EL n l::(DROP (SUC n) l ++ TAKE n l))``,
  rw[rotate_def] >>
  pop_assum mp_tac >>
  qid_spec_tac `n` >>
  Induct_on `l` >-
  rw[] >>
  rw[DROP_def] >-
  rw[EL_CONS, PRE_SUB1] >>
  `?j. n = SUC j` by metis_tac[num_CASES] >>
  `j < LENGTH l` by decide_tac >>
  `SUC j - 1 = j` by decide_tac >>
  rw[DROP_def, TAKE_def]);
(* Michael's proof *)
val rotate_shift_element = store_thm(
  "rotate_shift_element",
  ``!l n. n < LENGTH l ==> (rotate n l = EL n l::(DROP (SUC n) l ++ TAKE n l))``,
  rw[rotate_def] >>
  pop_assum mp_tac >>
  qid_spec_tac `n` >>
  Induct_on `l` >-
  rw[] >>
  rw[DROP_def] >> Cases_on `n` >> fs[]);

(* Theorem: rotate 0 l = l *)
(* Proof:
     rotate 0 l
   = DROP 0 l ++ TAKE 0 l   by rotate_def
   = l ++ []                by DROP_def, TAKE_def
   = l                      by APPEND
*)
val rotate_0 = store_thm(
  "rotate_0",
  ``!l. rotate 0 l = l``,
  rw[rotate_def]);

(* Theorem: rotate n [] = [] *)
(* Proof:
     rotate n []
   = DROP n [] ++ TAKE n []   by rotate_def
   = [] ++ []                 by DROP_def, TAKE_def
   = []                       by APPEND
*)
val rotate_nil = store_thm(
  "rotate_nil",
  ``!n. rotate n [] = []``,
  rw[rotate_def]);

(* Theorem: rotate (LENGTH l) l = l *)
(* Proof:
     rotate (LENGTH l) l
   = DROP (LENGTH l) l ++ TAKE (LENGTH l) l   by rotate_def
   = [] ++ TAKE (LENGTH l) l                  by DROP_LENGTH_NIL
   = [] ++ l                                  by TAKE_LENGTH_ID
   = l
*)
val rotate_full = store_thm(
  "rotate_full",
  ``!l. rotate (LENGTH l) l = l``,
  rw[rotate_def, DROP_LENGTH_NIL]);

(* Theorem: n < LENGTH l ==> rotate (SUC n) l = rotate 1 (rotate n l) *)
(* Proof:
   Since n < LENGTH l, l <> [] by LENGTH_NIL.
   Thus  DROP n l <> []  by DROP_EQ_NIL  (need n < LENGTH l)
   Expand by rotate_def, this is to show:
   DROP (SUC n) l ++ TAKE (SUC n) l = DROP 1 (DROP n l ++ TAKE n l) ++ TAKE 1 (DROP n l ++ TAKE n l)
   LHS = DROP (SUC n) l ++ TAKE (SUC n) l
       = DROP 1 (DROP n l) ++ (TAKE n l ++ TAKE 1 (DROP n l))             by DROP_SUC, TAKE_SUC
   Since DROP n l <> []  from above,
   RHS = DROP 1 (DROP n l ++ TAKE n l) ++ TAKE 1 (DROP n l ++ TAKE n l)
       = DROP 1 (DROP n l) ++ (TAKE n l ++ TAKE 1 (DROP n l))             by DROP_1_APPEND, TAKE_1_APPEND
       = LHS
*)
val rotate_suc = store_thm(
  "rotate_suc",
  ``!l n. n < LENGTH l ==> (rotate (SUC n) l = rotate 1 (rotate n l))``,
  rpt strip_tac >>
  `LENGTH l <> 0` by decide_tac >>
  `l <> []` by metis_tac[LENGTH_NIL] >>
  `DROP n l <> []` by simp[DROP_EQ_NIL] >>
  rw[rotate_def, DROP_1_APPEND, TAKE_1_APPEND, DROP_SUC, TAKE_SUC]);

(* Theorem: Rotate keeps LENGTH (of necklace): LENGTH (rotate n l) = LENGTH l *)
(* Proof:
     LENGTH (rotate n l)
   = LENGTH (DROP n l ++ TAKE n l)           by rotate_def
   = LENGTH (DROP n l) + LENGTH (TAKE n l)   by LENGTH_APPEND
   = LENGTH (TAKE n l) + LENGTH (DROP n l)   by arithmetic
   = LENGTH (TAKE n l ++ DROP n l)           by LENGTH_APPEND
   = LENGTH l                                by TAKE_DROP
*)
val rotate_same_length = store_thm(
  "rotate_same_length",
  ``!l n. LENGTH (rotate n l) = LENGTH l``,
  rpt strip_tac >>
  `LENGTH (rotate n l) = LENGTH (DROP n l ++ TAKE n l)` by rw[rotate_def] >>
  `_ = LENGTH (DROP n l) + LENGTH (TAKE n l)` by rw[] >>
  `_ = LENGTH (TAKE n l) + LENGTH (DROP n l)` by rw[ADD_COMM] >>
  `_ = LENGTH (TAKE n l ++ DROP n l)` by rw[] >>
  rw_tac std_ss[TAKE_DROP]);

(* Theorem: Rotate keeps SET (of elements): set (rotate n l) = set l *)
(* Proof:
     set (rotate n l)
   = set (DROP n l ++ TAKE n l)            by rotate_def
   = set (DROP n l) UNION set (TAKE n l)   by LIST_TO_SET_APPEND
   = set (TAKE n l) UNION set (DROP n l)   by UNION_COMM
   = set (TAKE n l ++ DROP n l)            by LIST_TO_SET_APPEND
   = set l                                 by TAKE_DROP
*)
val rotate_same_set = store_thm(
  "rotate_same_set",
  ``!l n. set (rotate n l) = set l``,
  rpt strip_tac >>
  `set (rotate n l) = set (DROP n l ++ TAKE n l)` by rw[rotate_def] >>
  `_ = set (DROP n l) UNION set (TAKE n l)` by rw[] >>
  `_ = set (TAKE n l) UNION set (DROP n l)` by rw[UNION_COMM] >>
  `_ = set (TAKE n l ++ DROP n l)` by rw[] >>
  rw_tac std_ss[TAKE_DROP]);

(* Theorem: n + m <= LENGTH l ==> rotate n (rotate m l) = rotate (n + m) l *)
(* Proof:
   By induction on n.
   Base case: !m l. 0 + m <= LENGTH l ==> (rotate 0 (rotate m l) = rotate (0 + m) l)
       rotate 0 (rotate m l)
     = rotate m l                by rotate_0
     = rotate (0 + m) l          by ADD
   Step case: !m l. SUC n + m <= LENGTH l ==> (rotate (SUC n) (rotate m l) = rotate (SUC n + m) l)
       rotate (SUC n) (rotate m l)
     = rotate 1 (rotate n (rotate m l))    by rotate_suc
     = rotate 1 (rotate (n + m) l)         by induction hypothesis
     = rotate (SUC (n + m)) l              by rotate_suc
     = rotate (SUC n + m) l                by ADD_CLAUSES
*)
val rotate_add = store_thm(
  "rotate_add",
  ``!n m l. n + m <= LENGTH l ==> (rotate n (rotate m l) = rotate (n + m) l)``,
  Induct >-
  rw[rotate_0] >>
  rw[] >>
  `LENGTH (rotate m l) = LENGTH l` by rw[rotate_same_length] >>
  `LENGTH (rotate (n + m) l) = LENGTH l` by rw[rotate_same_length] >>
  `n < LENGTH l /\ n + m < LENGTH l /\ n + m <= LENGTH l` by decide_tac >>
  rw[rotate_suc, ADD_CLAUSES]);

(* Theorem: !k. k < LENGTH l ==> rotate (LENGTH l - k) (rotate k l) = l *)
(* Proof:
   Since k < LENGTH l
     LENGTH 1 - k + k = LENGTH l <= LENGTH l   by EQ_LESS_EQ
     rotate (LENGTH l - k) (rotate k l)
   = rotate (LENGTH l - k + k) l        by rotate_add
   = rotate (LENGTH l) l                by arithmetic
   = l                                  by rotate_full
*)
val rotate_lcancel = store_thm(
  "rotate_lcancel",
  ``!k l. k < LENGTH l ==> (rotate (LENGTH l - k) (rotate k l) = l)``,
  rpt strip_tac >>
  `LENGTH l - k + k = LENGTH l` by decide_tac >>
  `LENGTH l <= LENGTH l` by rw[] >>
  rw[rotate_add, rotate_full]);

(* Theorem: !k. k < LENGTH l ==> rotate k (rotate (LENGTH l - k) l) = l *)
(* Proof:
   Since k < LENGTH l
     k + (LENGTH 1 - k) = LENGTH l <= LENGTH l   by EQ_LESS_EQ
     rotate k  (rotate (LENGTH l - k) l)
   = rotate (k + (LENGTH l - k)) l      by rotate_add
   = rotate (LENGTH l) l                by arithmetic
   = l                                  by rotate_full
*)
val rotate_rcancel = store_thm(
  "rotate_rcancel",
  ``!k l. k < LENGTH l ==> (rotate k (rotate (LENGTH l - k) l) = l)``,
  rpt strip_tac >>
  `k + (LENGTH l - k) = LENGTH l` by decide_tac >>
  `LENGTH l <= LENGTH l` by rw[] >>
  rw[rotate_add, rotate_full]);

(* ------------------------------------------------------------------------- *)
(* List Turn                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Define a rotation turn of a list (like a turnstile) *)
val turn_def = Define`
    turn l = if l = [] then [] else ((LAST l) :: (FRONT l))
`;

(* Theorem: turn [] = [] *)
(* Proof: by turn_def *)
val turn_nil = store_thm(
  "turn_nil",
  ``turn [] = []``,
  rw[turn_def]);

(* Theorem: l <> [] ==> (turn l = (LAST l) :: (FRONT l)) *)
(* Proof: by turn_def *)
val turn_not_nil = store_thm(
  "turn_not_nil",
  ``!l. l <> [] ==> (turn l = (LAST l) :: (FRONT l))``,
  rw[turn_def]);

(* Theorem: LENGTH (turn l) = LENGTH l *)
(* Proof:
   If l = [],
        LENGTH (turn []) = LENGTH []     by turn_def
   If l <> [],
      Then LENGTH l <> 0                 by LENGTH_NIL
        LENGTH (turn l)
      = LENGTH ((LAST l) :: (FRONT l))   by turn_def
      = SUC (LENGTH (FRONT l))           by LENGTH
      = SUC (PRE (LENGTH l))             by LENGTH_FRONT
      = LENGTH l                         by SUC_PRE, 0 < LENGTH l
*)
val turn_length = store_thm(
  "turn_length",
  ``!l. LENGTH (turn l) = LENGTH l``,
  metis_tac[turn_def, list_CASES, LENGTH, LENGTH_FRONT_CONS, SUC_PRE, NOT_ZERO_LT_ZERO]);

(* Theorem: (turn p = []) <=> (p = []) *)
(* Proof:
       turn p = []
   <=> LENGTH (turn p) = 0     by LENGTH_NIL
   <=> LENGTH p = 0            by turn_length
   <=> p = []                  by LENGTH_NIL
*)
val turn_eq_nil = store_thm(
  "turn_eq_nil",
  ``!p. (turn p = []) <=> (p = [])``,
  metis_tac[turn_length, LENGTH_NIL]);

(* Theorem: ls <> [] ==> (HD (turn ls) = LAST ls) *)
(* Proof:
     HD (turn ls)
   = HD (LAST ls :: FRONT ls)    by turn_def, ls <> []
   = LAST ls                     by HD
*)
val head_turn = store_thm(
  "head_turn",
  ``!ls. ls <> [] ==> (HD (turn ls) = LAST ls)``,
  rw[turn_def]);

(* Theorem: ls <> [] ==> (TL (turn ls) = FRONT ls) *)
(* Proof:
     TL (turn ls)
   = TL (LAST ls :: FRONT ls)  by turn_def, ls <> []
   = FRONT ls                  by TL
*)
Theorem tail_turn:
  !ls. ls <> [] ==> (TL (turn ls) = FRONT ls)
Proof
  rw[turn_def]
QED

(* Theorem: turn (SNOC x ls) = x :: ls *)
(* Proof:
   Note (SNOC x ls) <> []                    by NOT_SNOC_NIL
     turn (SNOC x ls)
   = LAST (SNOC x ls) :: FRONT (SNOC x ls)   by turn_def
   = x :: FRONT (SNOC x ls)                  by LAST_SNOC
   = x :: ls                                 by FRONT_SNOC
*)
Theorem turn_snoc:
  !ls x. turn (SNOC x ls) = x :: ls
Proof
  metis_tac[NOT_SNOC_NIL, turn_def, LAST_SNOC, FRONT_SNOC]
QED

(* Overload repeated turns *)
val _ = overload_on("turn_exp", ``\l n. FUNPOW turn n l``);

(* Theorem: turn_exp l 0 = l *)
(* Proof:
     turn_exp l 0
   = FUNPOW turn 0 l    by notation
   = l                  by FUNPOW
*)
val turn_exp_0 = store_thm(
  "turn_exp_0",
  ``!l. turn_exp l 0 = l``,
  rw[]);

(* Theorem: turn_exp l 1 = turn l *)
(* Proof:
     turn_exp l 1
   = FUNPOW turn 1 l    by notation
   = turn l             by FUNPOW
*)
val turn_exp_1 = store_thm(
  "turn_exp_1",
  ``!l. turn_exp l 1 = turn l``,
  rw[]);

(* Theorem: turn_exp l 2 = turn (turn l) *)
(* Proof:
     turn_exp l 2
   = FUNPOW turn 2 l         by notation
   = turn (FUNPOW turn 1 l)  by FUNPOW_SUC
   = turn (turn_exp l 1)     by notation
   = turn (turn l)           by turn_exp_1
*)
val turn_exp_2 = store_thm(
  "turn_exp_2",
  ``!l. turn_exp l 2 = turn (turn l)``,
  metis_tac[FUNPOW_SUC, turn_exp_1, TWO]);

(* Theorem: turn_exp l (SUC n) = turn_exp (turn l) n *)
(* Proof:
     turn_exp l (SUC n)
   = FUNPOW turn (SUC n) l    by notation
   = FUNPOW turn n (turn l)   by FUNPOW
   = turn_exp (turn l) n      by notation
*)
val turn_exp_SUC = store_thm(
  "turn_exp_SUC",
  ``!l n. turn_exp l (SUC n) = turn_exp (turn l) n``,
  rw[FUNPOW]);

(* Theorem: turn_exp l (SUC n) = turn (turn_exp l n) *)
(* Proof:
     turn_exp l (SUC n)
   = FUNPOW turn (SUC n) l    by notation
   = turn (FUNPOW turn n l)   by FUNPOW_SUC
   = turn (turn_exp l n)      by notation
*)
val turn_exp_suc = store_thm(
  "turn_exp_suc",
  ``!l n. turn_exp l (SUC n) = turn (turn_exp l n)``,
  rw[FUNPOW_SUC]);

(* Theorem: LENGTH (turn_exp l n) = LENGTH l *)
(* Proof:
   By induction on n.
   Base: LENGTH (turn_exp l 0) = LENGTH l
      True by turn_exp l 0 = l         by turn_exp_0
   Step: LENGTH (turn_exp l n) = LENGTH l ==> LENGTH (turn_exp l (SUC n)) = LENGTH l
        LENGTH (turn_exp l (SUC n))
      = LENGTH (turn (turn_exp l n))   by turn_exp_suc
      = LENGTH (turn_exp l n)          by turn_length
      = LENGTH l                       by induction hypothesis
*)
val turn_exp_length = store_thm(
  "turn_exp_length",
  ``!l n. LENGTH (turn_exp l n) = LENGTH l``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[turn_exp_suc, turn_length]);

(* Theorem: n < LENGTH ls ==>
            (HD (turn_exp ls n) = EL (if n = 0 then 0 else LENGTH ls - n) ls) *)
(* Proof:
   By induction on n.
   Base: !ls. 0 < LENGTH ls ==>
              HD (turn_exp ls 0) = EL 0 ls
           HD (turn_exp ls 0)
         = HD ls                 by FUNPOW_0
         = EL 0 ls               by EL
   Step: !ls. n < LENGTH ls ==> HD (turn_exp ls n) = EL (if n = 0 then 0 else (LENGTH ls - n)) ls ==>
         !ls. SUC n < LENGTH ls ==> HD (turn_exp ls (SUC n)) = EL (LENGTH ls - SUC n) ls
         Let k = LENGTH ls, then SUC n < k
         Note LENGTH (FRONT ls) = PRE k     by FRONT_LENGTH
          and n < PRE k                     by SUC n < k
         Also LENGTH (turn ls) = k          by turn_length
           so n < k                         by n < SUC n, SUC n < k
         Note ls <> []                      by k <> 0

           HD (turn_exp ls (SUC n))
         = HD (turn_exp (turn ls) n)                    by turn_exp_SUC
         = EL (if n = 0 then 0 else (LENGTH (turn ls) - n)) (turn ls)
                                                        by induction hypothesis, apply to (turn ls)
         = EL (if n = 0 then 0 else (k - n) (turn ls))  by above

         If n = 0,
         = EL 0 (turn ls)
         = LAST ls                           by turn_def
         = EL (PRE k) ls                     by LAST_EL
         = EL (k - SUC 0) ls                 by ONE
         If n <> 0
         = EL (k - n) (turn ls)
         = EL (k - n) (LAST ls :: FRONT ls)  by turn_def
         = EL (k - n - 1) (FRONT ls)         by EL
         = EL (k - n - 1) ls                 by FRONT_EL, k - n - 1 < PRE k, n <> 0
         = EL (k - SUC n) ls                 by arithmetic
*)
val head_turn_exp = store_thm(
  "head_turn_exp",
  ``!ls n. n < LENGTH ls ==>
         (HD (turn_exp ls n) = EL (if n = 0 then 0 else LENGTH ls - n) ls)``,
  (Induct_on `n` >> simp[]) >>
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH ls` >>
  `n < k` by rw[Abbr`k`] >>
  `LENGTH (turn ls) = k` by rw[turn_length, Abbr`k`] >>
  `HD (turn_exp ls (SUC n)) = HD (turn_exp (turn ls) n)` by rw[turn_exp_SUC] >>
  `_ = EL (if n = 0 then 0 else (k - n)) (turn ls)` by rw[] >>
  `k <> 0` by decide_tac >>
  `ls <> []` by metis_tac[LENGTH_NIL] >>
  (Cases_on `n = 0` >> fs[]) >| [
    `PRE k = k - 1` by decide_tac >>
    rw[head_turn, LAST_EL],
    `k - n = SUC (k - SUC n)` by decide_tac >>
    rw[turn_def, Abbr`k`] >>
    `LENGTH (FRONT ls) = PRE (LENGTH ls)` by rw[FRONT_LENGTH] >>
    `n < PRE (LENGTH ls)` by decide_tac >>
    rw[FRONT_EL]
  ]);

(* ------------------------------------------------------------------------- *)
(* Unit-List and Mono-List                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (LENGTH l = 1) ==> SING (set l) *)
(* Proof:
   Since ?x. l = [x]   by LENGTH_EQ_1
         set l = {x}   by LIST_TO_SET_DEF
      or SING (set l)  by SING_DEF
*)
val LIST_TO_SET_SING = store_thm(
  "LIST_TO_SET_SING",
  ``!l. (LENGTH l = 1) ==> SING (set l)``,
  rw[LENGTH_EQ_1, SING_DEF] >>
  `set [x] = {x}` by rw[] >>
  metis_tac[]);

(* Mono-list Theory: a mono-list is a list l with SING (set l) *)

(* Theorem: Two mono-lists are equal if their lengths and sets are equal.
            SING (set l1) /\ SING (set l2) ==>
            ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2)) *)
(* Proof:
   By induction on l1.
   Base case: !l2. SING (set []) /\ SING (set l2) ==>
              (([] = l2) <=> (LENGTH [] = LENGTH l2) /\ (set [] = set l2))
     True by SING (set []) is False, by SING_EMPTY.
   Step case: !l2. SING (set l1) /\ SING (set l2) ==>
              ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2)) ==>
              !h l2. SING (set (h::l1)) /\ SING (set l2) ==>
              ((h::l1 = l2) <=> (LENGTH (h::l1) = LENGTH l2) /\ (set (h::l1) = set l2))
     This is to show:
     (1) 1 = LENGTH l2 /\ {h} = set l2 ==>
         ([h] = l2) <=> (SUC (LENGTH []) = LENGTH l2) /\ (h INSERT set [] = set l2)
         If-part, l2 = [h],
              LENGTH l2 = 1 = SUC 0 = SUC (LENGTH [])   by LENGTH, ONE
          and set l2 = set [h] = {h} = h INSERT set []  by LIST_TO_SET
         Only-if part, LENGTH l2 = SUC 0 = 1            by ONE
            Then ?x. l2 = [x]                           by LENGTH_EQ_1
              so set l2 = {x} = {h}                     by LIST_TO_SET
              or x = h, hence l2 = [h]                  by EQUAL_SING
     (2) set l1 = {h} /\ SING (set l2) ==>
         (h::l1 = l2) <=> (SUC (LENGTH l1) = LENGTH l2) /\ (h INSERT set l1 = set l2)
         If part, h::l1 = l2.
            Then LENGTH l2 = LENGTH (h::l1) = SUC (LENGTH l1)  by LENGTH
             and set l2 = set (h::l1) = h INSERT set l1        by LIST_TO_SET
         Only-if part, SUC (LENGTH l1) = LENGTH l2.
            Since 0 < SUC (LENGTH l1)   by prim_recTheory.LESS_0
                  0 < LENGTH l2         by LESS_TRANS
               so ?k t. l2 = k::t       by LENGTH_NON_NIL, list_CASES
            Since LENGTH l2 = SUC (LENGTH t)   by LENGTH
                  LENGTH l1 = LENGTH t         by prim_recTheory.INV_SUC_EQ
              and set l2 = k INSERT set t      by LIST_TO_SET
            Given SING (set l2),
            either (set t = {}), or (set t = {k})  by SING_INSERT
            If set t = {},
               then t = []              by LIST_TO_SET_EQ_EMPTY
                and l1 = []             by LENGTH_NIL, LENGTH l1 = LENGTH t.
                 so set l1 = {}         by LIST_TO_SET_EQ_EMPTY
            contradicting set l1 = {h}  by NOT_SING_EMPTY
            If set t = {k},
               then set l2 = set t      by ABSORPTION, set l2 = k INSERT set {k}.
                 or k = h               by IN_SING
                 so l1 = t              by induction hypothesis
             giving l2 = h::l1
*)
val MONOLIST_EQ = store_thm(
  "MONOLIST_EQ",
  ``!l1 l2. SING (set l1) /\ SING (set l2) ==>
    ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2))``,
  Induct >-
  rw[] >>
  rw[] >| [
    rw[EQ_IMP_THM] >-
    rw[] >-
    rw[] >>
    `?x. l2 = [x]` by rw[GSYM LENGTH_EQ_1] >>
    `set l2 = {x}` by rw[] >>
    metis_tac[EQUAL_SING],
    rw[EQ_IMP_THM] >-
    rw[] >-
    rw[] >>
    `0 < LENGTH l2` by decide_tac >>
    `?k t. l2 = k::t` by metis_tac[LENGTH_NON_NIL, list_CASES] >>
    `LENGTH l2 = SUC (LENGTH t)` by rw[] >>
    `LENGTH l1 = LENGTH t` by decide_tac >>
    `set l2 = k INSERT set t` by rw[] >>
    `(set t = {}) \/ (set t = {k})` by metis_tac[SING_INSERT] >-
    metis_tac[LIST_TO_SET_EQ_EMPTY, LENGTH_NIL, NOT_SING_EMPTY] >>
    `set l2 = set t` by rw[] >>
    metis_tac[IN_SING]
  ]);
(* Michael's Proof *)
val MONOLIST_EQ = store_thm(
  "MONOLIST_EQ",
  ``!l1 l2. SING (set l1) /\ SING (set l2) ==>
              ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2))``,
  Induct >> rw[NOT_SING_EMPTY, SING_INSERT] >| [
    Cases_on `l2` >> rw[] >>
    full_simp_tac (srw_ss()) [SING_INSERT, EQUAL_SING] >>
    rw[LENGTH_NIL, NOT_SING_EMPTY, EQUAL_SING] >> metis_tac[],
    Cases_on `l2` >> rw[] >>
    full_simp_tac (srw_ss()) [SING_INSERT, LENGTH_NIL, NOT_SING_EMPTY, EQUAL_SING] >>
    metis_tac[]
  ]);

(* Theorem: A non-mono-list has at least one element in tail that is distinct from its head.
           ~SING (set (h::t)) ==> ?h'. h' IN set t /\ h' <> h *)
(* Proof:
   By SING_INSERT, this is to show:
      t <> [] /\ set t <> {h} ==> ?h'. MEM h' t /\ h' <> h
   Now, t <> [] ==> set t <> {}   by LIST_TO_SET_EQ_EMPTY
     so ?e. e IN set t            by MEMBER_NOT_EMPTY
     hence MEM e t,
       and MEM x t <=/=> (x = h)  by EXTENSION
   Therefore, e <> h, so take h' = e.
*)
val NON_MONO_TAIL_PROPERTY = store_thm(
  "NON_MONO_TAIL_PROPERTY",
  ``!l. ~SING (set (h::t)) ==> ?h'. h' IN set t /\ h' <> h``,
  rw[SING_INSERT] >>
  `set t <> {}` by metis_tac[LIST_TO_SET_EQ_EMPTY] >>
  `?e. e IN set t` by metis_tac[MEMBER_NOT_EMPTY] >>
  full_simp_tac (srw_ss())[EXTENSION] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* GENLIST Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: GENLIST f 0 = [] *)
(* Proof: by GENLIST *)
val GENLIST_0 = store_thm(
  "GENLIST_0",
  ``!f. GENLIST f 0 = []``,
  rw[]);

(* Theorem: GENLIST f 1 = [f 0] *)
(* Proof:
      GENLIST f 1
    = GENLIST f (SUC 0)          by ONE
    = SNOC (f 0) (GENLIST f 0)   by GENLIST
    = SNOC (f 0) []              by GENLIST
    = [f 0]                      by SNOC
*)
val GENLIST_1 = store_thm(
  "GENLIST_1",
  ``!f. GENLIST f 1 = [f 0]``,
  rw[]);

(* Theorem alias *)
Theorem GENLIST_EQ =
   listTheory.GENLIST_CONG |> GEN ``n:num`` |> GEN ``f2:num -> 'a``
                           |> GEN ``f1:num -> 'a``;
(*
val GENLIST_EQ = |- !f1 f2 n. (!m. m < n ==> f1 m = f2 m) ==> GENLIST f1 n = GENLIST f2 n: thm
*)

(* Theorem: (GENLIST f n = []) <=> (n = 0) *)
(* Proof:
   If part: GENLIST f n = [] ==> n = 0
      By contradiction, suppose n <> 0.
      Then LENGTH (GENLIST f n) = n <> 0  by LENGTH_GENLIST
      This contradicts LENGTH [] = 0.
   Only-if part: GENLIST f 0 = [], true   by GENLIST_0
*)
val GENLIST_EQ_NIL = store_thm(
  "GENLIST_EQ_NIL",
  ``!f n. (GENLIST f n = []) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  metis_tac[LENGTH_GENLIST, LENGTH_NIL]);

(* Theorem: LAST (GENLIST f (SUC n)) = f n *)
(* Proof:
     LAST (GENLIST f (SUC n))
   = LAST (SNOC (f n) (GENLIST f n))  by GENLIST
   = f n                              by LAST_SNOC
*)
val GENLIST_LAST = store_thm(
  "GENLIST_LAST",
  ``!f n. LAST (GENLIST f (SUC n)) = f n``,
  rw[GENLIST]);

(* Note:

- EVERY_MAP;
> val it = |- !P f l. EVERY P (MAP f l) <=> EVERY (\x. P (f x)) l : thm
- EVERY_GENLIST;
> val it = |- !n. EVERY P (GENLIST f n) <=> !i. i < n ==> P (f i) : thm
- MAP_GENLIST;
> val it = |- !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n : thm
*)

(* Note: the following can use EVERY_GENLIST. *)

(* Theorem: !k. (k < n ==> f k = c) <=> EVERY (\x. x = c) (GENLIST f n) *)
(* Proof: by induction on n.
   Base case: !c. (!k. k < 0 ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f 0)
     Since GENLIST f 0 = [], this is true as no k < 0.
   Step case: (!k. k < n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f n) ==>
              (!k. k < SUC n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f (SUC n))
         EVERY (\x. x = c) (GENLIST f (SUC n))
     <=> EVERY (\x. x = c) (SNOC (f n) (GENLIST f n))  by GENLIST
     <=> EVERY (\x. x = c) (GENLIST f n) /\ (f n = c)  by EVERY_SNOC
     <=> (!k. k < n ==> (f k = c)) /\ (f n = c)        by induction hypothesis
     <=> !k. k < SUC n ==> (f k = c)
*)
val GENLIST_CONSTANT = store_thm(
  "GENLIST_CONSTANT",
  ``!f n c. (!k. k < n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f n)``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[EVERY_DEF, GENLIST, EVERY_SNOC, EQ_IMP_THM] >-
  metis_tac[prim_recTheory.LESS_SUC] >>
  Cases_on `k = n` >-
  rw_tac std_ss[] >>
  metis_tac[prim_recTheory.LESS_THM]);

(* Theorem: GENLIST (K e) (SUC n) = e :: GENLIST (K e) n *)
(* Proof:
     GENLIST (K e) (SUC n)
   = (K e) 0::GENLIST ((K e) o SUC) n   by GENLIST_CONS
   = e :: GENLIST ((K e) o SUC) n       by K_THM
   = e :: GENLIST (K e) n               by K_o_THM
*)
val GENLIST_K_CONS = save_thm("GENLIST_K_CONS",
    SIMP_CONV (srw_ss()) [GENLIST_CONS] ``GENLIST (K e) (SUC n)`` |> GEN ``n:num`` |> GEN ``e``);
(* val GENLIST_K_CONS = |- !e n. GENLIST (K e) (SUC n) = e::GENLIST (K e) n: thm  *)

(* Theorem: GENLIST (K e) (n + m) = GENLIST (K e) m ++ GENLIST (K e) n *)
(* Proof:
   Note (\t. e) = K e    by FUN_EQ_THM
     GENLIST (K e) (n + m)
   = GENLIST (K e) m ++ GENLIST (\t. (K e) (t + m)) n    by GENLIST_APPEND
   = GENLIST (K e) m ++ GENLIST (\t. e) n                by K_THM
   = GENLIST (K e) m ++ GENLIST (K e) n                  by above
*)
val GENLIST_K_ADD = store_thm(
  "GENLIST_K_ADD",
  ``!e n m. GENLIST (K e) (n + m) = GENLIST (K e) m ++ GENLIST (K e) n``,
  rpt strip_tac >>
  `(\t. e) = K e` by rw[FUN_EQ_THM] >>
  rw[GENLIST_APPEND] >>
  metis_tac[]);

(* Theorem: (!k. k < n ==> (f k = e)) ==> (GENLIST f n = GENLIST (K e) n) *)
(* Proof:
   By induction on n.
   Base: GENLIST f 0 = GENLIST (K e) 0
        GENLIST f 0
      = []                          by GENLIST_0
      = GENLIST (K e) 0             by GENLIST_0
   Step: GENLIST f n = GENLIST (K e) n ==>
         GENLIST f (SUC n) = GENLIST (K e) (SUC n)
        GENLIST f (SUC n)
      = SNOC (f n) (GENLIST f n)    by GENLIST
      = SNOC e (GENLIST f n)        by applying f to n
      = SNOC e (GENLIST (K e) n)    by induction hypothesis
      = GENLIST (K e) (SUC n)       by GENLIST
*)
val GENLIST_K_LESS = store_thm(
  "GENLIST_K_LESS",
  ``!f e n. (!k. k < n ==> (f k = e)) ==> (GENLIST f n = GENLIST (K e) n)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[GENLIST]);

(* Theorem: (!k. 0 < k /\ k <= n ==> (f k = e)) ==> (GENLIST (f o SUC) n = GENLIST (K e) n) *)
(* Proof:
   Base: GENLIST (f o SUC) 0 = GENLIST (K e) 0
         GENLIST (f o SUC) 0
       = []                                by GENLIST_0
       = GENLIST (K e) 0                   by GENLIST_0
   Step: GENLIST (f o SUC) n = GENLIST (K e) n ==>
         GENLIST (f o SUC) (SUC n) = GENLIST (K e) (SUC n)
         GENLIST (f o SUC) (SUC n)
       = SNOC (f n) (GENLIST (f o SUC) n)  by GENLIST
       = SNOC e (GENLIST (f o SUC) n)      by applying f to n
       = SNOC e GENLIST (K e) n            by induction hypothesis
       = GENLIST (K e) (SUC n)             by GENLIST
*)
val GENLIST_K_RANGE = store_thm(
  "GENLIST_K_RANGE",
  ``!f e n. (!k. 0 < k /\ k <= n ==> (f k = e)) ==> (GENLIST (f o SUC) n = GENLIST (K e) n)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[GENLIST]);

(* Theorem: GENLIST (K c) a ++ GENLIST (K c) b = GENLIST (K c) (a + b) *)
(* Proof:
   Note (\t. c) = K c           by FUN_EQ_THM
     GENLIST (K c) (a + b)
   = GENLIST (K c) (b + a)                              by ADD_COMM
   = GENLIST (K c) a ++ GENLIST (\t. (K c) (t + a)) b   by GENLIST_APPEND
   = GENLIST (K c) a ++ GENLIST (\t. c) b               by applying constant function
   = GENLIST (K c) a ++ GENLIST (K c) b                 by GENLIST_FUN_EQ
*)
val GENLIST_K_APPEND = store_thm(
  "GENLIST_K_APPEND",
  ``!a b c. GENLIST (K c) a ++ GENLIST (K c) b = GENLIST (K c) (a + b)``,
  rpt strip_tac >>
  `(\t. c) = K c` by rw[FUN_EQ_THM] >>
  `GENLIST (K c) (a + b) = GENLIST (K c) (b + a)` by rw[] >>
  `_ = GENLIST (K c) a ++ GENLIST (\t. (K c) (t + a)) b` by rw[GENLIST_APPEND] >>
  rw[GENLIST_FUN_EQ]);

(* Theorem: GENLIST (K c) n ++ [c] = [c] ++ GENLIST (K c) n *)
(* Proof:
     GENLIST (K c) n ++ [c]
   = GENLIST (K c) n ++ GENLIST (K c) 1      by GENLIST_1
   = GENLIST (K c) (n + 1)                   by GENLIST_K_APPEND
   = GENLIST (K c) (1 + n)                   by ADD_COMM
   = GENLIST (K c) 1 ++ GENLIST (K c) n      by GENLIST_K_APPEND
   = [c] ++ GENLIST (K c) n                  by GENLIST_1
*)
val GENLIST_K_APPEND_K = store_thm(
  "GENLIST_K_APPEND_K",
  ``!c n. GENLIST (K c) n ++ [c] = [c] ++ GENLIST (K c) n``,
  metis_tac[GENLIST_K_APPEND, GENLIST_1, ADD_COMM, combinTheory.K_THM]);

(* Theorem: 0 < n ==> (MEM x (GENLIST (K c) n) <=> (x = c)) *)
(* Proof:
       MEM x (GENLIST (K c) n
   <=> ?m. m < n /\ (x = (K c) m)    by MEM_GENLIST
   <=> ?m. m < n /\ (x = c)          by K_THM
   <=> (x = c)                       by taking m = 0, 0 < n
*)
Theorem GENLIST_K_MEM:
  !x c n. 0 < n ==> (MEM x (GENLIST (K c) n) <=> (x = c))
Proof
  metis_tac[MEM_GENLIST, combinTheory.K_THM]
QED

(* Theorem: 0 < n ==> (set (GENLIST (K c) n) = {c}) *)
(* Proof:
   By induction on n.
   Base: 0 < 0 ==> (set (GENLIST (K c) 0) = {c})
      Since 0 < 0 = F, hence true.
   Step: 0 < n ==> (set (GENLIST (K c) n) = {c}) ==>
         0 < SUC n ==> (set (GENLIST (K c) (SUC n)) = {c})
      If n = 0,
        set (GENLIST (K c) (SUC 0)
      = set (GENLIST (K c) 1          by ONE
      = set [(K c) 0]                 by GENLIST_1
      = set [c]                       by K_THM
      = {c}                           by LIST_TO_SET
      If n <> 0, 0 < n.
        set (GENLIST (K c) (SUC n)
      = set (SNOC ((K c) n) (GENLIST (K c) n))     by GENLIST
      = set (SNOC c (GENLIST (K c) n)              by K_THM
      = c INSERT set (GENLIST (K c) n)             by LIST_TO_SET_SNOC
      = c INSERT {c}                               by induction hypothesis
      = {c}                                        by IN_INSERT
 *)
Theorem GENLIST_K_SET:
  !c n. 0 < n ==> (set (GENLIST (K c) n) = {c})
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  (Cases_on `n = 0` >> simp[]) >>
  `0 < n` by decide_tac >>
  simp[GENLIST, LIST_TO_SET_SNOC]
QED

(* Theorem: ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls)) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> (SING (set []) <=> ?c. [] = GENLIST (K c) (LENGTH []))
     Since [] <> [] = F, hence true.
   Step: ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls)) ==>
         !h. h::ls <> [] ==>
             (SING (set (h::ls)) <=> ?c. h::ls = GENLIST (K c) (LENGTH (h::ls)))
     Note h::ls <> [] = T.
     If part: SING (set (h::ls)) ==> ?c. h::ls = GENLIST (K c) (LENGTH (h::ls))
        Note SING (set (h::ls)) means
             set ls = {h}                by LIST_TO_SET_DEF, IN_SING
         Let n = LENGTH ls, 0 < n        by LENGTH_NON_NIL
        Note ls <> []                    by LIST_TO_SET, IN_SING, MEMBER_NOT_EMPTY
         and SING (set ls)               by SING_DEF
         ==> ?c. ls = GENLIST (K c) n    by induction hypothesis
          so set ls = {c}                by GENLIST_K_SET, 0 < n
         ==> h = c                       by IN_SING
           GENLIST (K c) (LENGTH (h::ls)
         = (K c) h :: ls                 by GENLIST_K_CONS
         = c :: ls                       by K_THM
         = h::ls                         by h = c
     Only-if part: ?c. h::ls = GENLIST (K c) (LENGTH (h::ls)) ==> SING (set (h::ls))
           set (h::ls)
         = set (GENLIST (K c) (LENGTH (h::ls)))        by given
         = set ((K c) h :: GENLIST (K c) (LENGTH ls))  by GENLIST_K_CONS
         = set (c :: GENLIST (K c) (LENGTH ls))        by K_THM
         = c INSERT set (GENLIST (K c) (LENGTH ls))    by LIST_TO_SET
         = c INSERT {c}                                by GENLIST_K_SET
         = {c}                                         by IN_INSERT
         Hence SING (set (h::ls))                      by SING_DEF
*)
Theorem LIST_TO_SET_SING_IFF:
  !ls. ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls))
Proof
  Induct >-
  simp[] >>
  (rw[EQ_IMP_THM] >> simp[]) >| [
    qexists_tac `h` >>
    qabbrev_tac `n = LENGTH ls` >>
    `ls <> []` by metis_tac[LIST_TO_SET, IN_SING, MEMBER_NOT_EMPTY] >>
    `SING (set ls)` by fs[SING_DEF] >>
    fs[] >>
    `0 < n` by metis_tac[LENGTH_NON_NIL] >>
    `h = c` by metis_tac[GENLIST_K_SET, IN_SING] >>
    simp[GENLIST_K_CONS],
    spose_not_then strip_assume_tac >>
    fs[GENLIST_K_CONS] >>
    `0 < LENGTH ls` by metis_tac[LENGTH_NON_NIL] >>
    metis_tac[GENLIST_K_SET]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* SUM Theorems                                                              *)
(* ------------------------------------------------------------------------- *)

(* Defined: SUM for summation of list = sequence *)

(* Theorem: SUM [] = 0 *)
(* Proof: by definition. *)
val SUM_NIL = save_thm("SUM_NIL", SUM |> CONJUNCT1);
(* > val SUM_NIL = |- SUM [] = 0 : thm *)

(* Theorem: SUM h::t = h + SUM t *)
(* Proof: by definition. *)
val SUM_CONS = save_thm("SUM_CONS", SUM |> CONJUNCT2);
(* val SUM_CONS = |- !h t. SUM (h::t) = h + SUM t: thm *)

(* Theorem: SUM [n] = n *)
(* Proof: by SUM *)
val SUM_SING = store_thm(
  "SUM_SING",
  ``!n. SUM [n] = n``,
  rw[]);

(* Theorem: SUM (s ++ t) = SUM s + SUM t *)
(* Proof: by induction on s *)
(*
val SUM_APPEND = store_thm(
  "SUM_APPEND",
  ``!s t. SUM (s ++ t) = SUM s + SUM t``,
  Induct_on `s` >-
  rw[] >>
  rw[ADD_ASSOC]);
*)
(* There is already a SUM_APPEND in up-to-date listTheory *)

(* Theorem: constant multiplication: k * SUM s = SUM (k * s)  *)
(* Proof: by induction on s.
   Base case: !k. k * SUM [] = SUM (MAP ($* k) [])
     LHS = k * SUM [] = k * 0 = 0         by SUM_NIL, MULT_0
         = SUM []                         by SUM_NIL
         = SUM (MAP ($* k) []) = RHS      by MAP
   Step case: !k. k * SUM s = SUM (MAP ($* k) s) ==>
              !h k. k * SUM (h::s) = SUM (MAP ($* k) (h::s))
     LHS = k * SUM (h::s)
         = k * (h + SUM s)                by SUM_CONS
         = k * h + k * SUM s              by LEFT_ADD_DISTRIB
         = k * h + SUM (MAP ($* k) s)     by induction hypothesis
         = SUM (k * h :: (MAP ($* k) s))  by SUM_CONS
         = SUM (MAP ($* k) (h::s))        by MAP
         = RHS
*)
val SUM_MULT = store_thm(
  "SUM_MULT",
  ``!s k. k * SUM s = SUM (MAP ($* k) s)``,
  Induct_on `s` >-
  metis_tac[SUM, MAP, MULT_0] >>
  metis_tac[SUM, MAP, LEFT_ADD_DISTRIB]);

(* Theorem: (m + n) * SUM s = SUM (m * s) + SUM (n * s)  *)
(* Proof: generalization of
- RIGHT_ADD_DISTRIB;
> val it = |- !m n p. (m + n) * p = m * p + n * p : thm
     (m + n) * SUM s
   = m * SUM s + n * SUM s                               by RIGHT_ADD_DISTRIB
   = SUM (MAP (\x. m * x) s) + SUM (MAP (\x. n * x) s)   by SUM_MULT
*)
val SUM_RIGHT_ADD_DISTRIB = store_thm(
  "SUM_RIGHT_ADD_DISTRIB",
  ``!s m n. (m + n) * SUM s = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)``,
  metis_tac[RIGHT_ADD_DISTRIB, SUM_MULT]);

(* Theorem: (SUM s) * (m + n) = SUM (m * s) + SUM (n * s)  *)
(* Proof: generalization of
- LEFT_ADD_DISTRIB;
> val it = |- !m n p. p * (m + n) = p * m + p * n : thm
     (SUM s) * (m + n)
   = (m + n) * SUM s                           by MULT_COMM
   = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)   by SUM_RIGHT_ADD_DISTRIB
*)
val SUM_LEFT_ADD_DISTRIB = store_thm(
  "SUM_LEFT_ADD_DISTRIB",
  ``!s m n. (SUM s) * (m + n) = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)``,
  metis_tac[SUM_RIGHT_ADD_DISTRIB, MULT_COMM]);


(*
- EVAL ``GENLIST I 4``;
> val it = |- GENLIST I 4 = [0; 1; 2; 3] : thm
- EVAL ``GENLIST SUC 4``;
> val it = |- GENLIST SUC 4 = [1; 2; 3; 4] : thm
- EVAL ``GENLIST (\k. binomial 4 k) 5``;
> val it = |- GENLIST (\k. binomial 4 k) 5 = [1; 4; 6; 4; 1] : thm
- EVAL ``GENLIST (\k. binomial 5 k) 6``;
> val it = |- GENLIST (\k. binomial 5 k) 6 = [1; 5; 10; 10; 5; 1] : thm
- EVAL ``GENLIST (\k. binomial 10 k) 11``;
> val it = |- GENLIST (\k. binomial 10 k) 11 = [1; 10; 45; 120; 210; 252; 210; 120; 45; 10; 1] : thm
*)

(* Theorems on GENLIST:

- GENLIST;
> val it = |- (!f. GENLIST f 0 = []) /\
               !f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n) : thm
- NULL_GENLIST;
> val it = |- !n f. NULL (GENLIST f n) <=> (n = 0) : thm
- GENLIST_CONS;
> val it = |- GENLIST f (SUC n) = f 0::GENLIST (f o SUC) n : thm
- EL_GENLIST;
> val it = |- !f n x. x < n ==> (EL x (GENLIST f n) = f x) : thm
- EXISTS_GENLIST;
> val it = |- !n. EXISTS P (GENLIST f n) <=> ?i. i < n /\ P (f i) : thm
- EVERY_GENLIST;
> val it = |- !n. EVERY P (GENLIST f n) <=> !i. i < n ==> P (f i) : thm
- MAP_GENLIST;
> val it = |- !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n : thm
- GENLIST_APPEND;
> val it = |- !f a b. GENLIST f (a + b) = GENLIST f b ++ GENLIST (\t. f (t + b)) a : thm
- HD_GENLIST;
> val it = |- HD (GENLIST f (SUC n)) = f 0 : thm
- TL_GENLIST;
> val it = |- !f n. TL (GENLIST f (SUC n)) = GENLIST (f o SUC) n : thm
- HD_GENLIST_COR;
> val it = |- !n f. 0 < n ==> (HD (GENLIST f n) = f 0) : thm
- GENLIST_FUN_EQ;
> val it = |- !n f g. (GENLIST f n = GENLIST g n) <=> !x. x < n ==> (f x = g x) : thm

*)

(* Theorem: SUM (GENLIST f n) = SIGMA f (count n) *)
(* Proof:
   By induction on n.
   Base: SUM (GENLIST f 0) = SIGMA f (count 0)

         SUM (GENLIST f 0)
       = SUM []                by GENLIST_0
       = 0                     by SUM_NIL
       = SIGMA f {}            by SUM_IMAGE_THM
       = SIGMA f (count 0)     by COUNT_0

   Step: SUM (GENLIST f n) = SIGMA f (count n) ==>
         SUM (GENLIST f (SUC n)) = SIGMA f (count (SUC n))

         SUM (GENLIST f (SUC n))
       = SUM (SNOC (f n) (GENLIST f n))   by GENLIST
       = f n + SUM (GENLIST f n)          by SUM_SNOC
       = f n + SIGMA f (count n)          by induction hypothesis
       = f n + SIGMA f (count n DELETE n) by IN_COUNT, DELETE_NON_ELEMENT
       = SIGMA f (n INSERT count n)       by SUM_IMAGE_THM, FINITE_COUNT
       = SIGMA f (count (SUC n))          by COUNT_SUC
*)
val SUM_GENLIST = store_thm(
  "SUM_GENLIST",
  ``!f n. SUM (GENLIST f n) = SIGMA f (count n)``,
  strip_tac >>
  Induct >-
  rw[SUM_IMAGE_THM] >>
  `SUM (GENLIST f (SUC n)) = SUM (SNOC (f n) (GENLIST f n))` by rw[GENLIST] >>
  `_ = f n + SUM (GENLIST f n)` by rw[SUM_SNOC] >>
  `_ = f n + SIGMA f (count n)` by rw[] >>
  `_ = f n + SIGMA f (count n DELETE n)` by metis_tac[IN_COUNT, LESS_SELF, DELETE_NON_ELEMENT] >>
  `_ = SIGMA f (n INSERT count n)` by rw[SUM_IMAGE_THM] >>
  `_ = SIGMA f (count (SUC n))` by rw[COUNT_SUC] >>
  decide_tac);

(* Theorem: SUM (k=0..n) f(k) = f(0) + SUM (k=1..n) f(k)  *)
(* Proof:
     SUM (GENLIST f (SUC n))
   = SUM (f 0 :: GENLIST (f o SUC) n)   by GENLIST_CONS
   = f 0 + SUM (GENLIST (f o SUC) n)    by SUM definition.
*)
val SUM_DECOMPOSE_FIRST = store_thm(
  "SUM_DECOMPOSE_FIRST",
  ``!f n. SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) n)``,
  metis_tac[GENLIST_CONS, SUM]);

(* Theorem: SUM (k=0..n) f(k) = SUM (k=0..(n-1)) f(k) + f n *)
(* Proof:
     SUM (GENLIST f (SUC n))
   = SUM (SNOC (f n) (GENLIST f n))  by GENLIST definition
   = SUM ((GENLIST f n) ++ [f n])    by SNOC_APPEND
   = SUM (GENLIST f n) + SUM [f n]   by SUM_APPEND
   = SUM (GENLIST f n) + f n         by SUM definition: SUM (h::t) = h + SUM t, and SUM [] = 0.
*)
val SUM_DECOMPOSE_LAST = store_thm(
  "SUM_DECOMPOSE_LAST",
  ``!f n. SUM (GENLIST f (SUC n)) = SUM (GENLIST f n) + f n``,
  rpt strip_tac >>
  `SUM (GENLIST f (SUC n)) = SUM (SNOC (f n) (GENLIST f n))` by metis_tac[GENLIST] >>
  `_ = SUM ((GENLIST f n) ++ [f n])` by metis_tac[SNOC_APPEND] >>
  `_ = SUM (GENLIST f n) + SUM [f n]` by metis_tac[SUM_APPEND] >>
  rw[SUM]);

(* Theorem: SUM (GENLIST a n) + SUM (GENLIST b n) = SUM (GENLIST (\k. a k + b k) n) *)
(* Proof: by induction on n.
   Base case: !a b. SUM (GENLIST a 0) + SUM (GENLIST b 0) = SUM (GENLIST (\k. a k + b k) 0)
     Since GENLIST f 0 = []    by GENLIST
       and SUM [] = 0          by SUM_NIL
     This is just 0 + 0 = 0, true by arithmetic.
   Step case: !a b. SUM (GENLIST a n) + SUM (GENLIST b n) =
                    SUM (GENLIST (\k. a k + b k) n) ==>
              !a b. SUM (GENLIST a (SUC n)) + SUM (GENLIST b (SUC n)) =
                    SUM (GENLIST (\k. a k + b k) (SUC n))
       SUM (GENLIST a (SUC n)) + SUM (GENLIST b (SUC n)
     = (SUM (GENLIST a n) + a n) + (SUM (GENLIST b n) + b n)  by SUM_DECOMPOSE_LAST
     = SUM (GENLIST a n) + SUM (GENLIST b n) + (a n + b n)    by arithmetic
     = SUM (GENLIST (\k. a k + b k) n) + (a n + b n)          by induction hypothesis
     = SUM (GENLIST (\k. a k + b k) (SUC n))                  by SUM_DECOMPOSE_LAST
*)
val SUM_ADD_GENLIST = store_thm(
  "SUM_ADD_GENLIST",
  ``!a b n. SUM (GENLIST a n) + SUM (GENLIST b n) = SUM (GENLIST (\k. a k + b k) n)``,
  Induct_on `n` >-
  rw[] >>
  rw[SUM_DECOMPOSE_LAST]);

(* Theorem: SUM (GENLIST a n ++ GENLIST b n) = SUM (GENLIST (\k. a k + b k) n) *)
(* Proof:
     SUM (GENLIST a n ++ GENLIST b n)
   = SUM (GENLIST a n) + SUM (GENLIST b n)  by SUM_APPEND
   = SUM (GENLIST (\k. a k + b k) n)        by SUM_ADD_GENLIST
*)
val SUM_GENLIST_APPEND = store_thm(
  "SUM_GENLIST_APPEND",
  ``!a b n. SUM (GENLIST a n ++ GENLIST b n) = SUM (GENLIST (\k. a k + b k) n)``,
  metis_tac[SUM_APPEND, SUM_ADD_GENLIST]);

(* Theorem: 0 < n ==> SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n *)
(* Proof:
     SUM (GENLIST f (SUC n))
   = SUM (GENLIST f n) + f n                       by SUM_DECOMPOSE_LAST
   = SUM (GENLIST f (SUC m)) + f n                 by n = SUC m, 0 < n
   = f 0 + SUM (GENLIST (f o SUC) m) + f n         by SUM_DECOMPOSE_FIRST
   = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n   by PRE_SUC_EQ
*)
val SUM_DECOMPOSE_FIRST_LAST = store_thm(
  "SUM_DECOMPOSE_FIRST_LAST",
  ``!f n. 0 < n ==> (SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n)``,
  metis_tac[SUM_DECOMPOSE_LAST, SUM_DECOMPOSE_FIRST, LESS_EQ_SUC, PRE_SUC_EQ]);

(* Theorem: (SUM l) MOD n = (SUM (MAP (\x. x MOD n) l)) MOD n *)
(* Proof: by list induction.
   Base case: SUM [] MOD n = SUM (MAP (\x. x MOD n) []) MOD n
      true by SUM [] = 0, MAP f [] = 0, and 0 MOD n = 0.
   Step case: SUM l MOD n = SUM (MAP (\x. x MOD n) l) MOD n ==>
              !h. SUM (h::l) MOD n = SUM (MAP (\x. x MOD n) (h::l)) MOD n
      SUM (h::l) MOD n
    = (h + SUM l) MOD n                                           by SUM
    = (h MOD n + (SUM l) MOD n) MOD n                             by MOD_PLUS
    = (h MOD n + SUM (MAP (\x. x MOD n) l) MOD n) MOD n           by induction hypothesis
    = ((h MOD n) MOD n + SUM (MAP (\x. x MOD n) l) MOD n) MOD n   by MOD_MOD
    = ((h MOD n + SUM (MAP (\x. x MOD n) l)) MOD n) MOD n         by MOD_PLUS
    = (h MOD n + SUM (MAP (\x. x MOD n) l)) MOD n                 by MOD_MOD
    = (SUM (h MOD n ::(MAP (\x. x MOD n) l))) MOD n               by SUM
    = (SUM (MAP (\x. x MOD n) (h::l))) MOD n                      by MAP
*)
val SUM_MOD = store_thm(
  "SUM_MOD",
  ``!n. 0 < n ==> !l. (SUM l) MOD n = (SUM (MAP (\x. x MOD n) l)) MOD n``,
  rpt strip_tac >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  `SUM (h::l) MOD n = (h MOD n + (SUM l) MOD n) MOD n` by rw_tac std_ss[SUM, MOD_PLUS] >>
  `_ = ((h MOD n) MOD n + SUM (MAP (\x. x MOD n) l) MOD n) MOD n` by rw_tac std_ss[MOD_MOD] >>
  rw[MOD_PLUS]);

(* Theorem: SUM l = 0 <=> l = EVERY (\x. x = 0) l *)
(* Proof: by induction on l.
   Base case: (SUM [] = 0) <=> EVERY (\x. x = 0) []
      true by SUM [] = 0 and GENLIST f 0 = [].
   Step case: (SUM l = 0) <=> EVERY (\x. x = 0) l ==>
              !h. (SUM (h::l) = 0) <=> EVERY (\x. x = 0) (h::l)
       SUM (h::l) = 0
   <=> h + SUM l = 0                  by SUM
   <=> h = 0 /\ SUM l = 0             by ADD_EQ_0
   <=> h = 0 /\ EVERY (\x. x = 0) l   by induction hypothesis
   <=> EVERY (\x. x = 0) (h::l)       by EVERY_DEF
*)
val SUM_EQ_0 = store_thm(
  "SUM_EQ_0",
  ``!l. (SUM l = 0) <=> EVERY (\x. x = 0) l``,
  Induct >>
  rw[]);

(* Theorem: SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n =
            SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n *)
(* Proof:
     SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n
   = SUM (MAP (\x. x MOD n) (GENLIST ((\k. f k) o SUC) (PRE n))) MOD n  by SUM_MOD
   = SUM (GENLIST ((\x. x MOD n) o ((\k. f k) o SUC)) (PRE n)) MOD n    by MAP_GENLIST
   = SUM (GENLIST ((\x. x MOD n) o (\k. f k) o SUC) (PRE n)) MOD n      by composition associative
   = SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n                by composition
*)
val SUM_GENLIST_MOD = store_thm(
  "SUM_GENLIST_MOD",
  ``!n. 0 < n ==> !f. SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n = SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n``,
  rpt strip_tac >>
  `SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n =
    SUM (MAP (\x. x MOD n) (GENLIST ((\k. f k) o SUC) (PRE n))) MOD n` by metis_tac[SUM_MOD] >>
  rw_tac std_ss[MAP_GENLIST, combinTheory.o_ASSOC, combinTheory.o_ABS_L]);

(* Theorem: SUM (GENLIST (\j. x) n) = n * x *)
(* Proof:
   By induction on n.
   Base case: !x. SUM (GENLIST (\j. x) 0) = 0 * x
       SUM (GENLIST (\j. x) 0)
     = SUM []                   by GENLIST
     = 0                        by SUM
     = 0 * x                    by MULT
   Step case: !x. SUM (GENLIST (\j. x) n) = n * x ==>
              !x. SUM (GENLIST (\j. x) (SUC n)) = SUC n * x
       SUM (GENLIST (\j. x) (SUC n))
     = SUM (SNOC x (GENLIST (\j. x) n))   by GENLIST
     = SUM (GENLIST (\j. x) n) + x        by SUM_SNOC
     = n * x + x                          by induction hypothesis
     = SUC n * x                          by MULT
*)
val SUM_CONSTANT = store_thm(
  "SUM_CONSTANT",
  ``!n x. SUM (GENLIST (\j. x) n) = n * x``,
  Induct >-
  rw[] >>
  rw_tac std_ss[GENLIST, SUM_SNOC, MULT]);

(* Theorem: SUM (GENLIST (K m) n) = m * n *)
(* Proof:
   By induction on n.
   Base: SUM (GENLIST (K m) 0) = m * 0
        SUM (GENLIST (K m) 0)
      = SUM []                 by GENLIST
      = 0                      by SUM
      = m * 0                  by MULT_0
   Step: SUM (GENLIST (K m) n) = m * n ==> SUM (GENLIST (K m) (SUC n)) = m * SUC n
        SUM (GENLIST (K m) (SUC n))
      = SUM (SNOC m (GENLIST (K m) n))    by GENLIST
      = SUM (GENLIST (K m) n) + m         by SUM_SNOC
      = m * n + m                         by induction hypothesis
      = m + m * n                         by ADD_COMM
      = m * SUC n                         by MULT_SUC
*)
val SUM_GENLIST_K = store_thm(
  "SUM_GENLIST_K",
  ``!m n. SUM (GENLIST (K m) n) = m * n``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[GENLIST, SUM_SNOC, MULT_SUC]);

(* Theorem: (LENGTH l1 = LENGTH l2) /\ (!k. k <= LENGTH l1 ==> EL k l1 <= EL k l2) ==> SUM l1 <= SUM l2 *)
(* Proof:
   By induction on l1.
   Base: LENGTH [] = LENGTH l2 ==> SUM [] <= SUM l2
       Note l2 = []               by LENGTH_EQ_0
         so SUM [] = SUM []
         or SUM [] <= SUM l2      by EQ_LESS_EQ
   Step: !l2. (LENGTH l1 = LENGTH l2) /\ ... ==> SUM l1 <= SUM l2 ==>
         (LENGTH (h::l1) = LENGTH l2) /\ ... ==> SUM h::l1 <= SUM l2
       Note l2 <> []              by LENGTH_EQ_0
         so ?h1 t2. l2 = h1::t1   by list_CASES
        and LENGTH l1 = LENGTH t1 by LENGTH
            SUM (h::l1)
          = h + SUM l1            by SUM_CONS
          <= h1 + SUM t1          by EL_ALL_PROPERTY, induction hypothesis
           = SUM l2               by SUM_CONS
*)
val SUM_LE = store_thm(
  "SUM_LE",
  ``!l1 l2. (LENGTH l1 = LENGTH l2) /\ (!k. k < LENGTH l1 ==> EL k l1 <= EL k l2) ==>
           SUM l1 <= SUM l2``,
  Induct >-
  metis_tac[LENGTH_EQ_0, EQ_LESS_EQ] >>
  rpt strip_tac >>
  `?h1 t1. l2 = h1::t1` by metis_tac[LENGTH_EQ_0, list_CASES] >>
  `LENGTH l1 = LENGTH t1` by metis_tac[LENGTH, SUC_EQ] >>
  `SUM (h::l1) = h + SUM l1` by rw[SUM_CONS] >>
  `SUM l2 = h1 + SUM t1` by rw[SUM_CONS] >>
  `(h <= h1) /\ SUM l1 <= SUM t1` by metis_tac[EL_ALL_PROPERTY] >>
  decide_tac);

(* Theorem: MEM x l ==> x <= SUM l *)
(* Proof:
   By induction on l.
   Base: !x. MEM x [] ==> x <= SUM []
      True since MEM x [] = F              by MEM
   Step: !x. MEM x l ==> x <= SUM l ==> !h x. MEM x (h::l) ==> x <= SUM (h::l)
      If x = h,
         Then h <= h + SUM l = SUM (h::l)  by SUM
      If x <> h,
         Then MEM x l                      by MEM
          ==> x <= SUM l                   by induction hypothesis
           or x <= h + SUM l = SUM (h::l)  by SUM
*)
val SUM_LE_MEM = store_thm(
  "SUM_LE_MEM",
  ``!l x. MEM x l ==> x <= SUM l``,
  Induct >-
  rw[] >>
  rw[] >-
  decide_tac >>
  `x <= SUM l` by rw[] >>
  decide_tac);

(* Theorem: n < LENGTH l ==> (EL n l) <= SUM l *)
(* Proof: by SUM_LE_MEM, MEM_EL *)
val SUM_LE_EL = store_thm(
  "SUM_LE_EL",
  ``!l n. n < LENGTH l ==> (EL n l) <= SUM l``,
  metis_tac[SUM_LE_MEM, MEM_EL]);

(* Theorem: m < n /\ n < LENGTH l ==> (EL m l) + (EL n l) <= SUM l *)
(* Proof:
   By induction on l.
   Base: !m n. m < n /\ n < LENGTH [] ==> EL m [] + EL n [] <= SUM []
      True since n < LENGTH [] = F              by LENGTH
   Step: !m n. m < LENGTH l /\ n < LENGTH l ==> EL m l + EL n l <= SUM l ==>
         !h m n. m < LENGTH (h::l) /\ n < LENGTH (h::l) ==> EL m (h::l) + EL n (h::l) <= SUM (h::l)
      Note 0 < n, or n <> 0             by m < n
        so ?k. n = SUC k            by num_CASES
       and k < LENGTH l             by SUC k < SUC (LENGTH l)
       and EL n (h::l) = EL k l     by EL_restricted
      If m = 0,
         Then EL m (h::l) = h       by EL_restricted
          and EL k l <= SUM l       by SUM_LE_EL
         Thus EL m (h::l) + EL n (h::l)
            = h + SUM l
            = SUM (h::l)            by SUM
      If m <> 0,
         Then ?j. m = SUC j         by num_CASES
          and j < k                 by SUC j < SUC k
          and EL m (h::l) = EL j l  by EL_restricted
         Thus EL m (h::l) + EL n (h::l)
            = EL j l + EL k l       by above
           <= SUM l                 by induction hypothesis
           <= h + SUM l             by arithmetic
            = SUM (h::l)            by SUM
*)
val SUM_LE_SUM_EL = store_thm(
  "SUM_LE_SUM_EL",
  ``!l m n. m < n /\ n < LENGTH l ==> (EL m l) + (EL n l) <= SUM l``,
  Induct >-
  rw[] >>
  rw[] >>
  `n <> 0` by decide_tac >>
  `?k. n = SUC k` by metis_tac[num_CASES] >>
  `k < LENGTH l` by decide_tac >>
  `EL n (h::l) = EL k l` by rw[] >>
  Cases_on `m = 0` >| [
    `EL m (h::l) = h` by rw[] >>
    `EL k l <= SUM l` by rw[SUM_LE_EL] >>
    decide_tac,
    `?j. m = SUC j` by metis_tac[num_CASES] >>
    `j < k` by decide_tac >>
    `EL m (h::l) = EL j l` by rw[] >>
    `EL j l + EL k l <= SUM l` by rw[] >>
    decide_tac
  ]);

(* Theorem: SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1) *)
(* Proof:
   The computation is:
       n + (n * 2) + (n * 4) + ... + (n * (2 ** (m - 1)))
     = n * (1 + 2 + 4 + ... + 2 ** (m - 1))
     = n * (2 ** m - 1)

   By induction on m.
   Base: SUM (GENLIST (\j. n * 2 ** j) 0) = n * (2 ** 0 - 1)
      LHS = SUM (GENLIST (\j. n * 2 ** j) 0)
          = SUM []                by GENLIST_0
          = 0                     by PROD
      RHS = n * (1 - 1)           by EXP_0
          = n * 0 = 0 = LHS       by MULT_0
   Step: SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1) ==>
         SUM (GENLIST (\j. n * 2 ** j) (SUC m)) = n * (2 ** SUC m - 1)
         SUM (GENLIST (\j. n * 2 ** j) (SUC m))
       = SUM (SNOC (n * 2 ** m) (GENLIST (\j. n * 2 ** j) m))   by GENLIST
       = SUM (GENLIST (\j. n * 2 ** j) m) + (n * 2 ** m)        by SUM_SNOC
       = n * (2 ** m - 1) + n * 2 ** m                          by induction hypothesis
       = n * (2 ** m - 1 + 2 ** m)                              by LEFT_ADD_DISTRIB
       = n * (2 * 2 ** m - 1)                                   by arithmetic
       = n * (2 ** SUC m - 1)                                   by EXP
*)
val SUM_DOUBLING_LIST = store_thm(
  "SUM_DOUBLING_LIST",
  ``!m n. SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1)``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[] >>
  qabbrev_tac `f = \j. n * 2 ** j` >>
  `SUM (GENLIST f (SUC m)) = SUM (SNOC (n * 2 ** m) (GENLIST f m))` by rw[GENLIST, Abbr`f`] >>
  `_ = SUM (GENLIST f m) + (n * 2 ** m)` by rw[SUM_SNOC] >>
  `_ = n * (2 ** m - 1) + n * 2 ** m` by rw[] >>
  `_ = n * (2 ** m - 1 + 2 ** m)` by rw[LEFT_ADD_DISTRIB] >>
  rw[EXP]);

(* ------------------------------------------------------------------------- *)
(* Maximum of a List                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define MAX of a list *)
val MAX_LIST_def = Define`
    (MAX_LIST [] = 0) /\
    (MAX_LIST (h::t) = MAX h (MAX_LIST t))
`;

(* export simple recursive definition *)
(* val _ = export_rewrites["MAX_LIST_def"]; *)

(* Theorem: MAX_LIST [] = 0 *)
(* Proof: by MAX_LIST_def *)
val MAX_LIST_NIL = save_thm("MAX_LIST_NIL", MAX_LIST_def |> CONJUNCT1);
(* val MAX_LIST_NIL = |- MAX_LIST [] = 0: thm *)

(* Theorem: MAX_LIST (h::t) = MAX h (MAX_LIST t) *)
(* Proof: by MAX_LIST_def *)
val MAX_LIST_CONS = save_thm("MAX_LIST_CONS", MAX_LIST_def |> CONJUNCT2);
(* val MAX_LIST_CONS = |- !h t. MAX_LIST (h::t) = MAX h (MAX_LIST t): thm *)

(* export simple results *)
val _ = export_rewrites["MAX_LIST_NIL", "MAX_LIST_CONS"];

(* Theorem: MAX_LIST [x] = x *)
(* Proof:
     MAX_LIST [x]
   = MAX x (MAX_LIST [])   by MAX_LIST_CONS
   = MAX x 0               by MAX_LIST_NIL
   = x                     by MAX_0
*)
val MAX_LIST_SING = store_thm(
  "MAX_LIST_SING",
  ``!x. MAX_LIST [x] = x``,
  rw[]);

(* Theorem: (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l *)
(* Proof:
   By induction on l.
   Base: (MAX_LIST [] = 0) <=> EVERY (\x. x = 0) []
      LHS: MAX_LIST [] = 0, true           by MAX_LIST_NIL
      RHS: EVERY (\x. x = 0) [], true      by EVERY_DEF
   Step: (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l ==>
         !h. (MAX_LIST (h::l) = 0) <=> EVERY (\x. x = 0) (h::l)
          MAX_LIST (h::l) = 0
      <=> MAX h (MAX_LIST l) = 0           by MAX_LIST_CONS
      <=> (h = 0) /\ (MAX_LIST l = 0)      by MAX_EQ_0
      <=> (h = 0) /\ EVERY (\x. x = 0) l   by induction hypothesis
      <=> EVERY (\x. x = 0) (h::l)         by EVERY_DEF
*)
val MAX_LIST_EQ_0 = store_thm(
  "MAX_LIST_EQ_0",
  ``!l. (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l``,
  Induct >>
  rw[MAX_EQ_0]);

(* Theorem: l <> [] ==> MEM (MAX_LIST l) l *)
(* Proof:
   By induction on l.
   Base: [] <> [] ==> MEM (MAX_LIST []) []
      Trivially true by [] <> [] = F.
   Step: l <> [] ==> MEM (MAX_LIST l) l ==>
         !h. h::l <> [] ==> MEM (MAX_LIST (h::l)) (h::l)
      If l = [],
         Note MAX_LIST [h] = h         by MAX_LIST_SING
          and MEM h [h]                by MEM
         Hence true.
      If l <> [],
         Let x = MAX_LIST (h::l)
               = MAX h (MAX_LIST l)    by MAX_LIST_CONS
         ==> x = h \/ x = MAX_LIST l   by MAX_CASES
         If x = h, MEM x (h::l)        by MEM
         If x = MAX_LIST l, MEM x l    by induction hypothesis
*)
val MAX_LIST_MEM = store_thm(
  "MAX_LIST_MEM",
  ``!l. l <> [] ==> MEM (MAX_LIST l) l``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  rw[] >>
  metis_tac[MAX_CASES]);

(* Theorem: MEM x l ==> x <= MAX_LIST l *)
(* Proof:
   By induction on l.
   Base: !x. MEM x [] ==> x <= MAX_LIST []
     Trivially true since MEM x [] = F             by MEM
   Step: !x. MEM x l ==> x <= MAX_LIST l ==> !h x. MEM x (h::l) ==> x <= MAX_LIST (h::l)
     Note MEM x (h::l) means (x = h) \/ MEM x l    by MEM
      and MAX_LIST (h::l) = MAX h (MAX_LIST l)     by MAX_LIST_CONS
     If x = h, x <= MAX h (MAX_LIST l)             by MAX_LE
     If MEM x l, x <= MAX_LIST l                   by induction hypothesis
     or          x <= MAX h (MAX_LIST l)           by MAX_LE, LESS_EQ_TRANS
*)
val MAX_LIST_PROPERTY = store_thm(
  "MAX_LIST_PROPERTY",
  ``!l x. MEM x l ==> x <= MAX_LIST l``,
  Induct >-
  rw[] >>
  rw[MAX_LIST_CONS] >-
  decide_tac >>
  rw[]);

(* Theorem: l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> y <= x) ==> (x = MAX_LIST l) *)
(* Proof:
   Let m = MAX_LIST l.
   Since MEM x l /\ x <= m     by MAX_LIST_PROPERTY
     and MEM m l ==> m <= x    by MAX_LIST_MEM, implication, l <> []
   Hence x = m                 by EQ_LESS_EQ
*)
val MAX_LIST_TEST = store_thm(
  "MAX_LIST_TEST",
  ``!l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> y <= x) ==> (x = MAX_LIST l)``,
  metis_tac[MAX_LIST_MEM, MAX_LIST_PROPERTY, EQ_LESS_EQ]);

(* Theorem: MAX_LIST t <= MAX_LIST (h::t) *)
(* Proof:
   Note MAX_LIST (h::t) = MAX h (MAX_LIST t)   by MAX_LIST_def
    and MAX_LIST t <= MAX h (MAX_LIST t)       by MAX_IS_MAX
   Thus MAX_LIST t <= MAX_LIST (h::t)
*)
val MAX_LIST_LE = store_thm(
  "MAX_LIST_LE",
  ``!h t. MAX_LIST t <= MAX_LIST (h::t)``,
  rw_tac std_ss[MAX_LIST_def]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==>
           !ls. ls <> [] ==> (MAX_LIST (MAP f ls) = f (MAX_LIST ls)) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> MAX_LIST (MAP f []) = f (MAX_LIST [])
      True by [] <> [] = F.
   Step: ls <> [] ==> MAX_LIST (MAP f ls) = f (MAX_LIST ls) ==>
         !h. h::ls <> [] ==> MAX_LIST (MAP f (h::ls)) = f (MAX_LIST (h::ls))
      If ls = [],
         MAX_LIST (MAP f [h])
       = MAX_LIST [f h]             by MAP
       = f h                        by MAX_LIST_def
       = f (MAX_LIST [h])           by MAX_LIST_def
      If ls <> [],
         MAX_LIST (MAP f (h::ls))
       = MAX_LIST (f h::MAP f ls)        by MAP
       = MAX (f h) MAX_LIST (MAP f ls)   by MAX_LIST_def
       = MAX (f h) (f (MAX_LIST ls))     by induction hypothesis
       = f (MAX h (MAX_LIST ls))         by MAX_SWAP
       = f (MAX_LIST (h::ls))            by MAX_LIST_def
*)
val MAX_LIST_MONO_MAP = store_thm(
  "MAX_LIST_MONO_MAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==>
   !ls. ls <> [] ==> (MAX_LIST (MAP f ls) = f (MAX_LIST ls))``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  rw[MAX_SWAP]);

(* ------------------------------------------------------------------------- *)
(* Minimum of a List                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define MIN of a list *)
val MIN_LIST_def = Define`
    MIN_LIST (h::t) = if t = [] then h else MIN h (MIN_LIST t)
`;

(* Theorem: MIN_LIST [x] = x *)
(* Proof: by MIN_LIST_def *)
val MIN_LIST_SING = store_thm(
  "MIN_LIST_SING",
  ``!x. MIN_LIST [x] = x``,
  rw[MIN_LIST_def]);

(* Theorem: t <> [] ==> (MIN_LIST (h::t) = MIN h (MIN_LIST t)) *)
(* Proof: by MIN_LIST_def *)
val MIN_LIST_CONS = store_thm(
  "MIN_LIST_CONS",
  ``!h t. t <> [] ==> (MIN_LIST (h::t) = MIN h (MIN_LIST t))``,
  rw[MIN_LIST_def]);

(* export simple results *)
val _ = export_rewrites["MIN_LIST_SING", "MIN_LIST_CONS"];

(* Theorem: l <> [] ==> MEM (MIN_LIST l) l *)
(* Proof:
   By induction on l.
   Base: [] <> [] ==> MEM (MIN_LIST []) []
      Trivially true by [] <> [] = F.
   Step: l <> [] ==> MEM (MIN_LIST l) l ==>
         !h. h::l <> [] ==> MEM (MIN_LIST (h::l)) (h::l)
      If l = [],
         Note MIN_LIST [h] = h         by MIN_LIST_SING
          and MEM h [h]                by MEM
         Hence true.
      If l <> [],
         Let x = MIN_LIST (h::l)
               = MIN h (MIN_LIST l)    by MIN_LIST_CONS
         ==> x = h \/ x = MIN_LIST l   by MIN_CASES
         If x = h, MEM x (h::l)        by MEM
         If x = MIN_LIST l, MEM x l    by induction hypothesis
*)
val MIN_LIST_MEM = store_thm(
  "MIN_LIST_MEM",
  ``!l. l <> [] ==> MEM (MIN_LIST l) l``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  rw[] >>
  metis_tac[MIN_CASES]);

(* Theorem: l <> [] ==> !x. MEM x l ==> (MIN_LIST l) <= x *)
(* Proof:
   By induction on l.
   Base: [] <> [] ==> ...
     Trivially true since [] <> [] = F
   Step: l <> [] ==> !x. MEM x l ==> MIN_LIST l <= x ==>
         !h. h::l <> [] ==> !x. MEM x (h::l) ==> MIN_LIST (h::l) <= x
     Note MEM x (h::l) means (x = h) \/ MEM x l    by MEM
     If l = [],
        MEM x [h] means x = h                      by MEM
        and MIN_LIST [h] = h, hence true           by MIN_LIST_SING
     If l <> [],
        MIN_LIST (h::l) = MIN h (MIN_LIST l)       by MIN_LIST_CONS
        If x = h, MIN h (MIN_LIST l) <= x          by MIN_LE
        If MEM x l, MIN_LIST l <= x                by induction hypothesis
        or          MIN h (MIN_LIST l) <= x        by MIN_LE, LESS_EQ_TRANS
*)
val MIN_LIST_PROPERTY = store_thm(
  "MIN_LIST_PROPERTY",
  ``!l. l <> [] ==> !x. MEM x l ==> (MIN_LIST l) <= x``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  fs[MIN_LIST_SING, MEM] >>
  fs[MIN_LIST_CONS, MEM]);

(* Theorem: l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> x <= y) ==> (x = MIN_LIST l) *)
(* Proof:
   Let m = MIN_LIST l.
   Since MEM x l /\ m <= x     by MIN_LIST_PROPERTY
     and MEM m l ==> x <= m    by MIN_LIST_MEM, implication, l <> []
   Hence x = m                 by EQ_LESS_EQ
*)
val MIN_LIST_TEST = store_thm(
  "MIN_LIST_TEST",
  ``!l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> x <= y) ==> (x = MIN_LIST l)``,
  metis_tac[MIN_LIST_MEM, MIN_LIST_PROPERTY, EQ_LESS_EQ]);

(* Theorem: l <> [] ==> MIN_LIST l <= MAX_LIST l *)
(* Proof:
   Since MEM (MIN_LIST l) l          by MIN_LIST_MEM
      so MIN_LIST l <= MAX_LIST l    by MAX_LIST_PROPERTY
*)
val MIN_LIST_LE_MAX_LIST = store_thm(
  "MIN_LIST_LE_MAX_LIST",
  ``!l. l <> [] ==> MIN_LIST l <= MAX_LIST l``,
  rw[MIN_LIST_MEM, MAX_LIST_PROPERTY]);

(* Theorem: t <> [] ==> MIN_LIST (h::t) <= MIN_LIST t *)
(* Proof:
   Note MIN_LIST (h::t) = MIN h (MIN_LIST t)   by MIN_LIST_def, t <> []
    and MIN h (MIN_LIST t) <= MIN_LIST t       by MIN_IS_MIN
   Thus MIN_LIST (h::t) <= MIN_LIST t
*)
val MIN_LIST_LE = store_thm(
  "MIN_LIST_LE",
  ``!h t. t <> [] ==> MIN_LIST (h::t) <= MIN_LIST t``,
  rw_tac std_ss[MIN_LIST_def]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==>
           !ls. ls <> [] ==> (MIN_LIST (MAP f ls) = f (MIN_LIST ls)) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> MIN_LIST (MAP f []) = f (MIN_LIST [])
      True by [] <> [] = F.
   Step: ls <> [] ==> MIN_LIST (MAP f ls) = f (MIN_LIST ls) ==>
         !h. h::ls <> [] ==> MIN_LIST (MAP f (h::ls)) = f (MIN_LIST (h::ls))
      If ls = [],
         MIN_LIST (MAP f [h])
       = MIN_LIST [f h]             by MAP
       = f h                        by MIN_LIST_def
       = f (MIN_LIST [h])           by MIN_LIST_def
      If ls <> [],
         MIN_LIST (MAP f (h::ls))
       = MIN_LIST (f h::MAP f ls)        by MAP
       = MIN (f h) MIN_LIST (MAP f ls)   by MIN_LIST_def
       = MIN (f h) (f (MIN_LIST ls))     by induction hypothesis
       = f (MIN h (MIN_LIST ls))         by MIN_SWAP
       = f (MIN_LIST (h::ls))            by MIN_LIST_def
*)
val MIN_LIST_MONO_MAP = store_thm(
  "MIN_LIST_MONO_MAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==>
   !ls. ls <> [] ==> (MIN_LIST (MAP f ls) = f (MIN_LIST ls))``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  rw[MIN_SWAP]);

(* ------------------------------------------------------------------------- *)
(* List Nub and Set                                                          *)
(* ------------------------------------------------------------------------- *)

(* Note:
> nub_def;
|- (nub [] = []) /\ !x l. nub (x::l) = if MEM x l then nub l else x::nub l
*)

(* Theorem: nub [] = [] *)
(* Proof: by nub_def *)
val nub_nil = save_thm("nub_nil", nub_def |> CONJUNCT1);
(* val nub_nil = |- nub [] = []: thm *)

(* Theorem: nub (x::l) = if MEM x l then nub l else x::nub l *)
(* Proof: by nub_def *)
val nub_cons = save_thm("nub_cons", nub_def |> CONJUNCT2);
(* val nub_cons = |- !x l. nub (x::l) = if MEM x l then nub l else x::nub l: thm *)

(* Theorem: nub [x] = [x] *)
(* Proof:
     nub [x]
   = nub (x::[])   by notation
   = x :: nub []   by nub_cons, MEM x [] = F
   = x ::[]        by nub_nil
   = [x]           by notation
*)
val nub_sing = store_thm(
  "nub_sing",
  ``!x. nub [x] = [x]``,
  rw[nub_def]);

(* Theorem: ALL_DISTINCT (nub l) *)
(* Proof:
   By induction on l.
   Base: ALL_DISTINCT (nub [])
         ALL_DISTINCT (nub [])
     <=> ALL_DISTINCT []               by nub_nil
     <=> T                             by ALL_DISTINCT
   Step: ALL_DISTINCT (nub l) ==> !h. ALL_DISTINCT (nub (h::l))
     If MEM h l,
        Then nub (h::l) = nub l        by nub_cons
        Thus ALL_DISTINCT (nub l)      by induction hypothesis
         ==> ALL_DISTINCT (nub (h::l))
     If ~(MEM h l),
        Then nub (h::l) = h:nub l      by nub_cons
        With ALL_DISTINCT (nub l)      by induction hypothesis
         ==> ALL_DISTINCT (h::nub l)   by ALL_DISTINCT, ~(MEM h l)
          or ALL_DISTINCT (nub (h::l))
*)
val nub_all_distinct = store_thm(
  "nub_all_distinct",
  ``!l. ALL_DISTINCT (nub l)``,
  Induct >-
  rw[nub_nil] >>
  rw[nub_cons]);

(* Theorem: CARD (set l) = LENGTH (nub l) *)
(* Proof:
   Note set (nub l) = set l    by nub_set
    and ALL_DISTINCT (nub l)   by nub_all_distinct
        CARD (set l)
      = CARD (set (nub l))     by above
      = LENGTH (nub l)         by ALL_DISTINCT_CARD_LIST_TO_SET, ALL_DISTINCT (nub l)
*)
val CARD_LIST_TO_SET_EQ = store_thm(
  "CARD_LIST_TO_SET_EQ",
  ``!l. CARD (set l) = LENGTH (nub l)``,
  rpt strip_tac >>
  `set (nub l) = set l` by rw[nub_set] >>
  `ALL_DISTINCT (nub l)` by rw[nub_all_distinct] >>
  rw[GSYM ALL_DISTINCT_CARD_LIST_TO_SET]);

(* Theorem: set [x] = {x} *)
(* Proof:
     set [x]
   = x INSERT set []              by LIST_TO_SET
   = x INSERT {}                  by LIST_TO_SET
   = {x}                          by INSERT_DEF
*)
val MONO_LIST_TO_SET = store_thm(
  "MONO_LIST_TO_SET",
  ``!x. set [x] = {x}``,
  rw[]);

(* Theorem: ALL_DISTINCT l /\ (set l = {x}) <=> (l = [x]) *)
(* Proof:
   If part: ALL_DISTINCT l /\ set l = {x} ==> l = [x]
      Note set l = {x}
       ==> l <> [] /\ EVERY ($= x) l   by LIST_TO_SET_EQ_SING
      Let P = (S= x).
      Note l <> [] ==> ?h t. l = h::t  by list_CASES
        so h = x /\ EVERY P t             by EVERY_DEF
       and ~(MEM h t) /\ ALL_DISTINCT t   by ALL_DISTINCT
      By contradiction, suppose l <> [x].
      Then t <> [] ==> ?u v. t = u::v     by list_CASES
       and MEM u t                        by MEM
       but u = h                          by EVERY_DEF
       ==> MEM h t, which contradicts ~(MEM h t).

   Only-if part: l = [x] ==> ALL_DISTINCT l /\ set l = {x}
       Note ALL_DISTINCT [x] = T     by ALL_DISTINCT_SING
        and set [x] = {x}            by MONO_LIST_TO_SET
*)
val DISTINCT_LIST_TO_SET_EQ_SING = store_thm(
  "DISTINCT_LIST_TO_SET_EQ_SING",
  ``!l x. ALL_DISTINCT l /\ (set l = {x}) <=> (l = [x])``,
  rw[EQ_IMP_THM] >>
  qabbrev_tac `P = ($= x)` >>
  `!y. P y ==> (y = x)` by rw[Abbr`P`] >>
  `l <> [] /\ EVERY P l` by metis_tac[LIST_TO_SET_EQ_SING, Abbr`P`] >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  `(h = x) /\ (EVERY P t)` by metis_tac[EVERY_DEF] >>
  `~(MEM h t) /\ ALL_DISTINCT t` by metis_tac[ALL_DISTINCT] >>
  spose_not_then strip_assume_tac >>
  `t <> []` by rw[] >>
  `?u v. t = u::v` by metis_tac[list_CASES] >>
  `MEM u t` by rw[] >>
  metis_tac[EVERY_DEF]);

(* Theorem: ALL_DISTINCT l ==> !x. MEM x l <=> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2 *)
(* Proof:
   If part: MEM x l ==> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2
      Note ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p2    by MEM_SPLIT_APPEND_last
       Now ALL_DISTINCT (p1 ++ [x])              by ALL_DISTINCT_APPEND, ALL_DISTINCT l
       But MEM x [x]                             by MEM
        so ~MEM x p1                             by ALL_DISTINCT_APPEND

   Only-if part: MEM x (p1 ++ [x] ++ p2), true   by MEM_APPEND
*)
val MEM_SPLIT_APPEND_distinct = store_thm(
  "MEM_SPLIT_APPEND_distinct",
  ``!l. ALL_DISTINCT l ==> !x. MEM x l <=> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2``,
  rw[EQ_IMP_THM] >-
  metis_tac[MEM_SPLIT_APPEND_last, ALL_DISTINCT_APPEND, MEM] >>
  rw[]);

(* Theorem: ~(MEM h l1) /\ (set (h::l1) = set l2) ==>
            ?p1 p2. ~(MEM h p1) /\ ~(MEM h p2) /\ (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2)) *)
(* Proof:
   Note MEM h (h::l1)          by MEM
     or h IN set (h::l1)       by notation
     so h IN set l2            by given
     or h IN set (nub l2)      by nub_set
     so MEM h (nub l2)         by notation
     or ?p1 p2. nub l2 = p1 ++ [h] ++ h2
     and  ~(MEM h p1) /\ ~(MEM h p2)           by MEM_SPLIT_APPEND_distinct
   Remaining goal: set l1 = set (p1 ++ p2)

   Step 1: show set l1 SUBSET set (p1 ++ p2)
       Let x IN set l1.
       Then MEM x l1 ==> MEM x (h::l1)   by MEM
         so x IN set (h::l1)
         or x IN set l2                  by given
         or x IN set (nub l2)            by nub_set
         or MEM x (nub l2)               by notation
        But h <> x  since MEM x l1 but ~MEM h l1
         so MEM x (p1 ++ p2)             by MEM, MEM_APPEND
         or x IN set (p1 ++ p2)          by notation
        Thus l1 SUBSET set (p1 ++ p2)    by SUBSET_DEF

   Step 2: show set (p1 ++ p2) SUBSET set l1
       Let x IN set (p1 ++ p2)
        or MEM x (p1 ++ p2)              by notation
        so MEM x (nub l2)                by MEM, MEM_APPEND
        or x IN set (nub l2)             by notation
       ==> x IN set l2                   by nub_set
        or x IN set (h::l1)              by given
        or MEM x (h::l1)                 by notation
       But x <> h                        by MEM_APPEND, MEM x (p1 ++ p2) but ~(MEM h p1) /\ ~(MEM h p2)
       ==> MEM x l1                      by MEM
        or x IN set l1                   by notation
      Thus set (p1 ++ p2) SUBSET set l1  by SUBSET_DEF

  Thus set l1 = set (p1 ++ p2)           by SUBSET_ANTISYM
*)
val LIST_TO_SET_REDUCTION = store_thm(
  "LIST_TO_SET_REDUCTION",
  ``!l1 l2 h. ~(MEM h l1) /\ (set (h::l1) = set l2) ==>
   ?p1 p2. ~(MEM h p1) /\ ~(MEM h p2) /\ (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2))``,
  rpt strip_tac >>
  `MEM h (nub l2)` by metis_tac[MEM, nub_set] >>
  qabbrev_tac `l = nub l2` >>
  `?n. n < LENGTH l /\ (h = EL n l)` by rw[GSYM MEM_EL] >>
  `ALL_DISTINCT l` by rw[nub_all_distinct, Abbr`l`] >>
  `?p1 p2. (l = p1 ++ [h] ++ p2) /\ ~MEM h p1 /\ ~MEM h p2` by rw[GSYM MEM_SPLIT_APPEND_distinct] >>
  qexists_tac `p1` >>
  qexists_tac `p2` >>
  rpt strip_tac >-
  rw[] >>
  `set l1 SUBSET set (p1 ++ p2) /\ set (p1 ++ p2) SUBSET set l1` suffices_by metis_tac[SUBSET_ANTISYM] >>
  rewrite_tac[SUBSET_DEF] >>
  rpt strip_tac >-
  metis_tac[MEM_APPEND, MEM, nub_set] >>
  metis_tac[MEM_APPEND, MEM, nub_set]);

(* ------------------------------------------------------------------------- *)
(* List Padding                                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: PAD_LEFT c n [] = GENLIST (K c) n *)
(* Proof: by PAD_LEFT *)
val PAD_LEFT_NIL = store_thm(
  "PAD_LEFT_NIL",
  ``!n c. PAD_LEFT c n [] = GENLIST (K c) n``,
  rw[PAD_LEFT]);

(* Theorem: PAD_RIGHT c n [] = GENLIST (K c) n *)
(* Proof: by PAD_RIGHT *)
val PAD_RIGHT_NIL = store_thm(
  "PAD_RIGHT_NIL",
  ``!n c. PAD_RIGHT c n [] = GENLIST (K c) n``,
  rw[PAD_RIGHT]);

(* Theorem: LENGTH (PAD_LEFT c n s) = MAX n (LENGTH s) *)
(* Proof:
     LENGTH (PAD_LEFT c n s)
   = LENGTH (GENLIST (K c) (n - LENGTH s) ++ s)           by PAD_LEFT
   = LENGTH (GENLIST (K c) (n - LENGTH s)) + LENGTH s     by LENGTH_APPEND
   = n - LENGTH s + LENGTH s                              by LENGTH_GENLIST
   = MAX n (LENGTH s)                                     by MAX_DEF
*)
val PAD_LEFT_LENGTH = store_thm(
  "PAD_LEFT_LENGTH",
  ``!n c s. LENGTH (PAD_LEFT c n s) = MAX n (LENGTH s)``,
  rw[PAD_LEFT, MAX_DEF]);

(* Theorem: LENGTH (PAD_RIGHT c n s) = MAX n (LENGTH s) *)
(* Proof:
     LENGTH (PAD_LEFT c n s)
   = LENGTH (s ++ GENLIST (K c) (n - LENGTH s))           by PAD_RIGHT
   = LENGTH s + LENGTH (GENLIST (K c) (n - LENGTH s))     by LENGTH_APPEND
   = LENGTH s + (n - LENGTH s)                            by LENGTH_GENLIST
   = MAX n (LENGTH s)                                     by MAX_DEF
*)
val PAD_RIGHT_LENGTH = store_thm(
  "PAD_RIGHT_LENGTH",
  ``!n c s. LENGTH (PAD_RIGHT c n s) = MAX n (LENGTH s)``,
  rw[PAD_RIGHT, MAX_DEF]);

(* Theorem: n <= LENGTH l ==> (PAD_LEFT c n l = l) *)
(* Proof:
   Note n - LENGTH l = 0       by n <= LENGTH l
     PAD_LEFT c (LENGTH l) l
   = GENLIST (K c) 0 ++ l      by PAD_LEFT
   = [] ++ l                   by GENLIST
   = l                         by APPEND
*)
val PAD_LEFT_ID = store_thm(
  "PAD_LEFT_ID",
  ``!l c n. n <= LENGTH l ==> (PAD_LEFT c n l = l)``,
  rpt strip_tac >>
  `n - LENGTH l = 0` by decide_tac >>
  rw[PAD_LEFT]);

(* Theorem: n <= LENGTH l ==> (PAD_RIGHT c n l = l) *)
(* Proof:
   Note n - LENGTH l = 0       by n <= LENGTH l
     PAD_RIGHT c (LENGTH l) l
   = ll ++ GENLIST (K c) 0     by PAD_RIGHT
   = [] ++ l                   by GENLIST
   = l                         by APPEND_NIL
*)
val PAD_RIGHT_ID = store_thm(
  "PAD_RIGHT_ID",
  ``!l c n. n <= LENGTH l ==> (PAD_RIGHT c n l = l)``,
  rpt strip_tac >>
  `n - LENGTH l = 0` by decide_tac >>
  rw[PAD_RIGHT]);

(* Theorem: PAD_LEFT c 0 l = l *)
(* Proof: by PAD_LEFT_ID *)
val PAD_LEFT_0 = store_thm(
  "PAD_LEFT_0",
  ``!l c. PAD_LEFT c 0 l = l``,
  rw_tac std_ss[PAD_LEFT_ID]);

(* Theorem: PAD_RIGHT c 0 l = l *)
(* Proof: by PAD_RIGHT_ID *)
val PAD_RIGHT_0 = store_thm(
  "PAD_RIGHT_0",
  ``!l c. PAD_RIGHT c 0 l = l``,
  rw_tac std_ss[PAD_RIGHT_ID]);

(* Theorem: LENGTH l <= n ==> !c. PAD_LEFT c (SUC n) l = c:: PAD_LEFT c n l *)
(* Proof:
     PAD_LEFT c (SUC n) l
   = GENLIST (K c) (SUC n - LENGTH l) ++ l         by PAD_LEFT
   = GENLIST (K c) (SUC (n - LENGTH l)) ++ l       by LENGTH l <= n
   = SNOC c (GENLIST (K c) (n - LENGTH l)) ++ l    by GENLIST
   = (GENLIST (K c) (n - LENGTH l)) ++ [c] ++ l    by SNOC_APPEND
   = [c] ++ (GENLIST (K c) (n - LENGTH l)) ++ l    by GENLIST_K_APPEND_K
   = [c] ++ ((GENLIST (K c) (n - LENGTH l)) ++ l)  by APPEND_ASSOC
   = [c] ++ PAD_LEFT c n l                         by PAD_LEFT
   = c :: PAD_LEFT c n l                           by CONS_APPEND
*)
val PAD_LEFT_CONS = store_thm(
  "PAD_LEFT_CONS",
  ``!l n. LENGTH l <= n ==> !c. PAD_LEFT c (SUC n) l = c:: PAD_LEFT c n l``,
  rpt strip_tac >>
  qabbrev_tac `m = LENGTH l` >>
  `SUC n - m = SUC (n - m)` by decide_tac >>
  `PAD_LEFT c (SUC n) l = GENLIST (K c) (SUC n - m) ++ l` by rw[PAD_LEFT, Abbr`m`] >>
  `_ = SNOC c (GENLIST (K c) (n - m)) ++ l` by rw[GENLIST] >>
  `_ = (GENLIST (K c) (n - m)) ++ [c] ++ l` by rw[SNOC_APPEND] >>
  `_ = [c] ++ (GENLIST (K c) (n - m)) ++ l` by rw[GENLIST_K_APPEND_K] >>
  `_ = [c] ++ ((GENLIST (K c) (n - m)) ++ l)` by rw[APPEND_ASSOC] >>
  `_ = [c] ++ PAD_LEFT c n l` by rw[PAD_LEFT] >>
  `_ = c :: PAD_LEFT c n l` by rw[] >>
  rw[]);

(* Theorem: LENGTH l <= n ==> !c. PAD_RIGHT c (SUC n) l = SNOC c (PAD_RIGHT c n l) *)
(* Proof:
     PAD_RIGHT c (SUC n) l
   = l ++ GENLIST (K c) (SUC n - LENGTH l)         by PAD_RIGHT
   = l ++ GENLIST (K c) (SUC (n - LENGTH l))       by LENGTH l <= n
   = l ++ SNOC c (GENLIST (K c) (n - LENGTH l))    by GENLIST
   = SNOC c (l ++ (GENLIST (K c) (n - LENGTH l)))  by APPEND_SNOC
   = SNOC c (PAD_RIGHT c n l)                      by PAD_RIGHT
*)
val PAD_RIGHT_SNOC = store_thm(
  "PAD_RIGHT_SNOC",
  ``!l n. LENGTH l <= n ==> !c. PAD_RIGHT c (SUC n) l = SNOC c (PAD_RIGHT c n l)``,
  rpt strip_tac >>
  qabbrev_tac `m = LENGTH l` >>
  `SUC n - m = SUC (n - m)` by decide_tac >>
  rw[PAD_RIGHT, GENLIST, APPEND_SNOC]);

(* Theorem: h :: PAD_RIGHT c n t = PAD_RIGHT c (SUC n) (h::t) *)
(* Proof:
     h :: PAD_RIGHT c n t
   = h :: (t ++ GENLIST (K c) (n - LENGTH t))          by PAD_RIGHT
   = (h::t) ++ GENLIST (K c) (n - LENGTH t)            by APPEND
   = (h::t) ++ GENLIST (K c) (SUC n - LENGTH (h::t))   by LENGTH
   = PAD_RIGHT c (SUC n) (h::t)                        by PAD_RIGHT
*)
val PAD_RIGHT_CONS = store_thm(
  "PAD_RIGHT_CONS",
  ``!h t c n. h :: PAD_RIGHT c n t = PAD_RIGHT c (SUC n) (h::t)``,
  rw[PAD_RIGHT]);

(* Theorem: l <> [] ==> (LAST (PAD_LEFT c n l) = LAST l) *)
(* Proof:
   Note ?h t. l = h::t     by list_CASES
     LAST (PAD_LEFT c n l)
   = LAST (GENLIST (K c) (n - LENGTH (h::t)) ++ (h::t))   by PAD_LEFT
   = LAST (h::t)           by LAST_APPEND_CONS
   = LAST l                by notation
*)
val PAD_LEFT_LAST = store_thm(
  "PAD_LEFT_LAST",
  ``!l c n. l <> [] ==> (LAST (PAD_LEFT c n l) = LAST l)``,
  rpt strip_tac >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  rw[PAD_LEFT, LAST_APPEND_CONS]);

(* Theorem: (PAD_LEFT c n l = []) <=> ((l = []) /\ (n = 0)) *)
(* Proof:
       PAD_LEFT c n l = []
   <=> GENLIST (K c) (n - LENGTH l) ++ l = []        by PAD_LEFT
   <=> GENLIST (K c) (n - LENGTH l) = [] /\ l = []   by APPEND_eq_NIL
   <=> GENLIST (K c) n = [] /\ l = []                by LENGTH l = 0
   <=> n = 0 /\ l = []                               by GENLIST_EQ_NIL
*)
val PAD_LEFT_EQ_NIL = store_thm(
  "PAD_LEFT_EQ_NIL",
  ``!l c n. (PAD_LEFT c n l = []) <=> ((l = []) /\ (n = 0))``,
  rw[PAD_LEFT, EQ_IMP_THM] >>
  fs[GENLIST_EQ_NIL]);

(* Theorem: (PAD_RIGHT c n l = []) <=> ((l = []) /\ (n = 0)) *)
(* Proof:
       PAD_RIGHT c n l = []
   <=> l ++ GENLIST (K c) (n - LENGTH l) = []        by PAD_RIGHT
   <=> l = [] /\ GENLIST (K c) (n - LENGTH l) = []   by APPEND_eq_NIL
   <=> l = [] /\ GENLIST (K c) n = []                by LENGTH l = 0
   <=> l = [] /\ n = 0                               by GENLIST_EQ_NIL
*)
val PAD_RIGHT_EQ_NIL = store_thm(
  "PAD_RIGHT_EQ_NIL",
  ``!l c n. (PAD_RIGHT c n l = []) <=> ((l = []) /\ (n = 0))``,
  rw[PAD_RIGHT, EQ_IMP_THM] >>
  fs[GENLIST_EQ_NIL]);

(* Theorem: 0 < n ==> (PAD_LEFT c n [] = PAD_LEFT c n [c]) *)
(* Proof:
      PAD_LEFT c n []
    = GENLIST (K c) n          by PAD_LEFT, APPEND_NIL
    = GENLIST (K c) (SUC k)    by n = SUC k, 0 < n
    = SNOC c (GENLIST (K c) k) by GENLIST, (K c) k = c
    = GENLIST (K c) k ++ [c]   by SNOC_APPEND
    = PAD_LEFT c n [c]         by PAD_LEFT
*)
val PAD_LEFT_NIL_EQ = store_thm(
  "PAD_LEFT_NIL_EQ",
  ``!n c. 0 < n ==> (PAD_LEFT c n [] = PAD_LEFT c n [c])``,
  rw[PAD_LEFT] >>
  `SUC (n - 1) = n` by decide_tac >>
  qabbrev_tac `f = (K c):num -> 'a` >>
  `f (n - 1) = c` by rw[Abbr`f`] >>
  metis_tac[SNOC_APPEND, GENLIST]);

(* Theorem: 0 < n ==> (PAD_RIGHT c n [] = PAD_RIGHT c n [c]) *)
(* Proof:
      PAD_RIGHT c n []
    = GENLIST (K c) n                by PAD_RIGHT
    = GENLIST (K c) (SUC (n - 1))    by 0 < n
    = c :: GENLIST (K c) (n - 1)     by GENLIST_K_CONS
    = [c] ++ GENLIST (K c) (n - 1)   by CONS_APPEND
    = PAD_RIGHT c (SUC (n - 1)) [c]  by PAD_RIGHT
    = PAD_RIGHT c n [c]              by 0 < n
*)
val PAD_RIGHT_NIL_EQ = store_thm(
  "PAD_RIGHT_NIL_EQ",
  ``!n c. 0 < n ==> (PAD_RIGHT c n [] = PAD_RIGHT c n [c])``,
  rw[PAD_RIGHT] >>
  `SUC (n - 1) = n` by decide_tac >>
  metis_tac[GENLIST_K_CONS]);

(* Theorem: PAD_RIGHT c n ls = ls ++ PAD_RIGHT c (n - LENGTH ls) [] *)
(* Proof:
     PAD_RIGHT c n ls
   = ls ++ GENLIST (K c) (n - LENGTH ls)                by PAD_RIGHT
   = ls ++ ([] ++ GENLIST (K c) ((n - LENGTH ls) - 0)   by APPEND_NIL, LENGTH
   = ls ++ PAD_RIGHT c (n - LENGTH ls) []               by PAD_RIGHT
*)
val PAD_RIGHT_BY_RIGHT = store_thm(
  "PAD_RIGHT_BY_RIGHT",
  ``!ls c n. PAD_RIGHT c n ls = ls ++ PAD_RIGHT c (n - LENGTH ls) []``,
  rw[PAD_RIGHT]);

(* Theorem: PAD_RIGHT c n ls = ls ++ PAD_LEFT c (n - LENGTH ls) [] *)
(* Proof:
     PAD_RIGHT c n ls
   = ls ++ GENLIST (K c) (n - LENGTH ls)                by PAD_RIGHT
   = ls ++ (GENLIST (K c) ((n - LENGTH ls) - 0) ++ [])  by APPEND_NIL, LENGTH
   = ls ++ PAD_LEFT c (n - LENGTH ls) []               by PAD_LEFT
*)
val PAD_RIGHT_BY_LEFT = store_thm(
  "PAD_RIGHT_BY_LEFT",
  ``!ls c n. PAD_RIGHT c n ls = ls ++ PAD_LEFT c (n - LENGTH ls) []``,
  rw[PAD_RIGHT, PAD_LEFT]);

(* Theorem: PAD_LEFT c n ls = (PAD_RIGHT c (n - LENGTH ls) []) ++ ls *)
(* Proof:
     PAD_LEFT c n ls
   = GENLIST (K c) (n - LENGTH ls) ++ ls               by PAD_LEFT
   = ([] ++ GENLIST (K c) ((n - LENGTH ls) - 0) ++ ls  by APPEND_NIL, LENGTH
   = (PAD_RIGHT c (n - LENGTH ls) []) ++ ls            by PAD_RIGHT
*)
val PAD_LEFT_BY_RIGHT = store_thm(
  "PAD_LEFT_BY_RIGHT",
  ``!ls c n. PAD_LEFT c n ls = (PAD_RIGHT c (n - LENGTH ls) []) ++ ls``,
  rw[PAD_RIGHT, PAD_LEFT]);

(* Theorem: PAD_LEFT c n ls = (PAD_LEFT c (n - LENGTH ls) []) ++ ls *)
(* Proof:
     PAD_LEFT c n ls
   = GENLIST (K c) (n - LENGTH ls) ++ ls                 by PAD_LEFT
   = ((GENLIST (K c) ((n - LENGTH ls) - 0) ++ []) ++ ls  by APPEND_NIL, LENGTH
   = (PAD_LEFT c (n - LENGTH ls) []) ++ ls               by PAD_LEFT
*)
val PAD_LEFT_BY_LEFT = store_thm(
  "PAD_LEFT_BY_LEFT",
  ``!ls c n. PAD_LEFT c n ls = (PAD_LEFT c (n - LENGTH ls) []) ++ ls``,
  rw[PAD_LEFT]);

(* ------------------------------------------------------------------------- *)
(* PROD for List, similar to SUM for List                                    *)
(* ------------------------------------------------------------------------- *)

(* Overload a positive list *)
val _ = overload_on("POSITIVE", ``\l. !x. MEM x l ==> 0 < x``);
val _ = overload_on("EVERY_POSITIVE", ``\l. EVERY (\k. 0 < k) l``);

(* Theorem: EVERY_POSITIVE ls <=> POSITIVE ls *)
(* Proof: by EVERY_MEM *)
val POSITIVE_THM = store_thm(
  "POSITIVE_THM",
  ``!ls. EVERY_POSITIVE ls <=> POSITIVE ls``,
  rw[EVERY_MEM]);

(* Note: For product of a number list, any zero element will make the product 0. *)

(* Define PROD, similar to SUM *)
val PROD = new_recursive_definition
      {name = "PROD",
       rec_axiom = list_Axiom,
       def = ``(PROD [] = 1) /\
          (!h t. PROD (h::t) = h * PROD t)``};

(* export simple definition *)
val _ = export_rewrites["PROD"];

(* Extract theorems from definition *)
val PROD_NIL = save_thm("PROD_NIL", PROD |> CONJUNCT1);
(* val PROD_NIL = |- PROD [] = 1: thm *)

val PROD_CONS = save_thm("PROD_CONS", PROD |> CONJUNCT2);
(* val PROD_CONS = |- !h t. PROD (h::t) = h * PROD t: thm *)

(* Theorem: PROD [n] = n *)
(* Proof: by PROD *)
val PROD_SING = store_thm(
  "PROD_SING",
  ``!n. PROD [n] = n``,
  rw[]);

(* Theorem: PROD ls = if ls = [] then 1 else (HD ls) * PROD (TL ls) *)
(* Proof: by PROD *)
val PROD_eval = store_thm(
  "PROD_eval[compute]", (* put in computeLib *)
  ``!ls. PROD ls = if ls = [] then 1 else (HD ls) * PROD (TL ls)``,
  metis_tac[PROD, list_CASES, HD, TL]);

(* enable PROD computation -- use [compute] above. *)
(* val _ = computeLib.add_persistent_funs ["PROD_eval"]; *)

(* Theorem: (PROD ls = 1) = !x. MEM x ls ==> (x = 1) *)
(* Proof:
   By induction on ls.
   Base: (PROD [] = 1) <=> !x. MEM x [] ==> (x = 1)
      LHS: PROD [] = 1 is true          by PROD
      RHS: is true since MEM x [] = F   by MEM
   Step: (PROD ls = 1) <=> !x. MEM x ls ==> (x = 1) ==>
         !h. (PROD (h::ls) = 1) <=> !x. MEM x (h::ls) ==> (x = 1)
      Note 1 = PROD (h::ls)                     by given
             = h * PROD ls                      by PROD
      Thus h = 1 /\ PROD ls = 1                 by MULT_EQ_1
        or h = 1 /\ !x. MEM x ls ==> (x = 1)    by induction hypothesis
        or !x. MEM x (h::ls) ==> (x = 1)        by MEM
*)
val PROD_eq_1 = store_thm(
  "PROD_eq_1",
  ``!ls. (PROD ls = 1) = !x. MEM x ls ==> (x = 1)``,
  Induct >>
  rw[] >>
  metis_tac[]);
(* proof like SUM_eq_0 *)
val PROD_eq_1 = store_thm("PROD_eq_1",
  ``!ls. (PROD ls = 1) = !x. MEM x ls ==> (x = 1)``,
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN SRW_TAC[] [PROD, MEM] THEN METIS_TAC[]);

(* Theorem: PROD (SNOC x l) = (PROD l) * x *)
(* Proof:
   By induction on l.
   Base: PROD (SNOC x []) = PROD [] * x
        PROD (SNOC x [])
      = PROD [x]                by SNOC
      = x                       by PROD
      = 1 * x                   by MULT_LEFT_1
      = PROD [] * x             by PROD
   Step: PROD (SNOC x l) = PROD l * x ==> !h. PROD (SNOC x (h::l)) = PROD (h::l) * x
        PROD (SNOC x (h::l))
      = PROD (h:: SNOC x l)     by SNOC
      = h * PROD (SNOC x l)     by PROD
      = h * (PROD l * x)        by induction hypothesis
      = (h * PROD l) * x        by MULT_ASSOC
      = PROD (h::l) * x         by PROD
*)
val PROD_SNOC = store_thm(
  "PROD_SNOC",
  ``!x l. PROD (SNOC x l) = (PROD l) * x``,
  strip_tac >>
  Induct >>
  rw[]);
(* proof like SUM_SNOC *)
val PROD_SNOC = store_thm("PROD_SNOC",
    (``!x l. PROD (SNOC x l) = (PROD l) * x``),
    GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN REWRITE_TAC[PROD, SNOC, MULT, MULT_CLAUSES]
    THEN GEN_TAC THEN ASM_REWRITE_TAC[MULT_ASSOC]);

(* Theorem: PROD (APPEND l1 l2) = PROD l1 * PROD l2 *)
(* Proof:
   By induction on l1.
   Base: PROD ([] ++ l2) = PROD [] * PROD l2
         PROD ([] ++ l2)
       = PROD l2                   by APPEND
       = 1 * PROD l2               by MULT_LEFT_1
       = PROD [] * PROD l2         by PROD
   Step: !l2. PROD (l1 ++ l2) = PROD l1 * PROD l2 ==> !h l2. PROD (h::l1 ++ l2) = PROD (h::l1) * PROD l2
         PROD (h::l1 ++ l2)
       = PROD (h::(l1 ++ l2))      by APPEND
       = h * PROD (l1 ++ l2)       by PROD
       = h * (PROD l1 * PROD l2)   by induction hypothesis
       = (h * PROD l1) * PROD l2   by MULT_ASSOC
       = PROD (h::l1) * PROD l2    by PROD
*)
val PROD_APPEND = store_thm(
  "PROD_APPEND",
  ``!l1 l2. PROD (APPEND l1 l2) = PROD l1 * PROD l2``,
  Induct >>
  rw[]);
(* proof like SUM_APPEND *)
val PROD_APPEND = store_thm("PROD_APPEND",
    (``!l1 l2. PROD (APPEND l1 l2) = PROD l1 * PROD l2``),
    INDUCT_THEN list_INDUCT ASSUME_TAC THEN ASM_REWRITE_TAC[PROD, APPEND, MULT_LEFT_1, MULT_ASSOC]);

(* Theorem: PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls *)
(* Proof:
   By SNOC_INDUCT |- !P. P [] /\ (!l. P l ==> !x. P (SNOC x l)) ==> !l. P l
   Base: PROD (MAP f []) = FOLDL (\a e. a * f e) 1 []
         PROD (MAP f [])
       = PROD []                     by MAP
       = 1                           by PROD
       = FOLDL (\a e. a * f e) 1 []  by FOLDL
   Step: !f. PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls ==>
         PROD (MAP f (SNOC x ls)) = FOLDL (\a e. a * f e) 1 (SNOC x ls)
         PROD (MAP f (SNOC x ls))
       = PROD (SNOC (f x) (MAP f ls))                      by MAP_SNOC
       = PROD (MAP f ls) * (f x)                           by PROD_SNOC
       = (FOLDL (\a e. a * f e) 1 ls) * (f x)              by induction hypothesis
       = (\a e. a * f e) (FOLDL (\a e. a * f e) 1 ls) x    by function application
       = FOLDL (\a e. a * f e) 1 (SNOC x ls)               by FOLDL_SNOC
*)
val PROD_MAP_FOLDL = store_thm(
  "PROD_MAP_FOLDL",
  ``!ls f. PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls``,
  HO_MATCH_MP_TAC SNOC_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  rw[MAP_SNOC, PROD_SNOC, FOLDL_SNOC]);
(* proof like SUM_MAP_FOLDL *)
val PROD_MAP_FOLDL = Q.store_thm("PROD_MAP_FOLDL",
    `!ls f. PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls`,
    HO_MATCH_MP_TAC SNOC_INDUCT THEN
    SRW_TAC [] [FOLDL_SNOC, MAP_SNOC, PROD_SNOC, MAP, PROD, FOLDL]);

(* Theorem: FINITE s ==> !f. PI f s = PROD (MAP f (SET_TO_LIST s)) *)
(* Proof:
     PI f s
   = ITSET (\e acc. f e * acc) s 1                            by PROD_IMAGE_DEF
   = FOLDL (combin$C (\e acc. f e * acc)) 1 (SET_TO_LIST s)   by ITSET_eq_FOLDL_SET_TO_LIST, FINITE s
   = FOLDL (\a e. a * f e) 1 (SET_TO_LIST s)                  by FUN_EQ_THM
   = PROD (MAP f (SET_TO_LIST s))                             by PROD_MAP_FOLDL
*)
val PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST = store_thm(
  "PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST",
  ``!s. FINITE s ==> !f. PI f s = PROD (MAP f (SET_TO_LIST s))``,
  rw[PROD_IMAGE_DEF] >>
  rw[ITSET_eq_FOLDL_SET_TO_LIST, PROD_MAP_FOLDL] >>
  rpt AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM]);
(* proof like SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST *)
val PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST = Q.store_thm(
   "PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST",
   `!s. FINITE s ==> !f. PI f s = PROD (MAP f (SET_TO_LIST s))`,
    SRW_TAC [] [PROD_IMAGE_DEF] THEN
    SRW_TAC [] [ITSET_eq_FOLDL_SET_TO_LIST, PROD_MAP_FOLDL] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SRW_TAC [] [FUN_EQ_THM, arithmeticTheory.MULT_COMM]);

(* Define PROD using accumulator *)
val PROD_ACC_DEF = Lib.with_flag (Defn.def_suffix, "_DEF") Define
  `(PROD_ACC [] acc = acc) /\
   (PROD_ACC (h::t) acc = PROD_ACC t (h * acc))`;

(* Theorem: PROD_ACC L n = PROD L * n *)
(* Proof:
   By induction on L.
   Base: !n. PROD_ACC [] n = PROD [] * n
        PROD_ACC [] n
      = n                 by PROD_ACC_DEF
      = 1 * n             by MULT_LEFT_1
      = PROD [] * n       by PROD
   Step: !n. PROD_ACC L n = PROD L * n ==> !h n. PROD_ACC (h::L) n = PROD (h::L) * n
        PROD_ACC (h::L) n
      = PROD_ACC L (h * n)   by PROD_ACC_DEF
      = PROD L * (h * n)     by induction hypothesis
      = (PROD L * h) * n     by MULT_ASSOC
      = (h * PROD L) * n     by MULT_COMM
      = PROD (h::L) * n      by PROD
*)
val PROD_ACC_PROD_LEM = store_thm(
  "PROD_ACC_PROD_LEM",
  ``!L n. PROD_ACC L n = PROD L * n``,
  Induct >>
  rw[PROD_ACC_DEF]);
(* proof SUM_ACC_SUM_LEM *)
val PROD_ACC_PROD_LEM = store_thm
("PROD_ACC_SUM_LEM",
 ``!L n. PROD_ACC L n = PROD L * n``,
 Induct THEN RW_TAC arith_ss [PROD_ACC_DEF, PROD]);

(* Theorem: PROD L = PROD_ACC L 1 *)
(* Proof: Put n = 1 in PROD_ACC_PROD_LEM *)
val PROD_PROD_ACC = store_thm(
  "PROD_PROD_ACC",
  ``!L. PROD L = PROD_ACC L 1``,
  rw[PROD_ACC_PROD_LEM]);
(* proof like SUM_SUM_ACC *)
val PROD_PROD_ACC = store_thm
("PROD_PROD_ACC",
  ``!L. PROD L = PROD_ACC L 1``,
  PROVE_TAC [PROD_ACC_PROD_LEM, MULT_RIGHT_1]);

(* Put in computeLib *)
val _ = computeLib.add_funs [PROD_PROD_ACC];

(* EVAL ``PROD [1; 2; 3; 4]``; --> 24 *)

(* Theorem: PROD (GENLIST (K m) n) = m ** n *)
(* Proof:
   By induction on n.
   Base: PROD (GENLIST (K m) 0) = m ** 0
        PROD (GENLIST (K m) 0)
      = PROD []                by GENLIST
      = 1                      by PROD
      = m ** 0                 by EXP
   Step: PROD (GENLIST (K m) n) = m ** n ==> PROD (GENLIST (K m) (SUC n)) = m ** SUC n
        PROD (GENLIST (K m) (SUC n))
      = PROD (SNOC m (GENLIST (K m) n))    by GENLIST
      = PROD (GENLIST (K m) n) * m         by PROD_SNOC
      = m ** n * m                         by induction hypothesis
      = m * m ** n                         by MULT_COMM
      = m * SUC n                          by EXP
*)
val PROD_GENLIST_K = store_thm(
  "PROD_GENLIST_K",
  ``!m n. PROD (GENLIST (K m) n) = m ** n``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[GENLIST, PROD_SNOC, EXP]);

(* Same as PROD_GENLIST_K, formulated slightly different. *)

(* Theorem: PPROD (GENLIST (\j. x) n) = x ** n *)
(* Proof:
   Note (\j. x) = K x             by FUN_EQ_THM
        PROD (GENLIST (\j. x) n)
      = PROD (GENLIST (K x) n)    by GENLIST_FUN_EQ
      = x ** n                    by PROD_GENLIST_K
*)
val PROD_CONSTANT = store_thm(
  "PROD_CONSTANT",
  ``!n x. PROD (GENLIST (\j. x) n) = x ** n``,
  rpt strip_tac >>
  `(\j. x) = K x` by rw[FUN_EQ_THM] >>
  metis_tac[PROD_GENLIST_K, GENLIST_FUN_EQ]);

(* Theorem: (PROD l = 0) <=> MEM 0 l *)
(* Proof:
   By induction on l.
   Base: (PROD [] = 0) <=> MEM 0 []
      LHS = F    by PROD_NIL, 1 <> 0
      RHS = F    by MEM
   Step: (PROD l = 0) <=> MEM 0 l ==> !h. (PROD (h::l) = 0) <=> MEM 0 (h::l)
      Note PROD (h::l) = h * PROD l     by PROD_CONS
      Thus PROD (h::l) = 0
       ==> h = 0 \/ PROD l = 0          by MULT_EQ_0
      If h = 0, then MEM 0 (h::l)       by MEM
      If PROD l = 0, then MEM 0 l       by induction hypothesis
                       or MEM 0 (h::l)  by MEM
*)
val PROD_EQ_0 = store_thm(
  "PROD_EQ_0",
  ``!l. (PROD l = 0) <=> MEM 0 l``,
  Induct >-
  rw[] >>
  metis_tac[PROD_CONS, MULT_EQ_0, MEM]);

(* Theorem: EVERY (\x. 0 < x) l ==> 0 < PROD l *)
(* Proof:
   By contradiction, suppose PROD l = 0.
   Then MEM 0 l              by PROD_EQ_0
     or 0 < 0 = F            by EVERY_MEM
*)
val PROD_POS = store_thm(
  "PROD_POS",
  ``!l. EVERY (\x. 0 < x) l ==> 0 < PROD l``,
  metis_tac[EVERY_MEM, PROD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: POSITIVE l ==> 0 < PROD l *)
(* Proof: PROD_POS, EVERY_MEM *)
val PROD_POS_ALT = store_thm(
  "PROD_POS_ALT",
  ``!l. POSITIVE l ==> 0 < PROD l``,
  rw[PROD_POS, EVERY_MEM]);

(* Theorem: PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1) *)
(* Proof:
   The computation is:
       n * (n ** 2) * (n ** 4) * ... * (n ** (2 ** (m - 1)))
     = n ** (1 + 2 + 4 + ... + 2 ** (m - 1))
     = n ** (2 ** m - 1)

   By induction on m.
   Base: PROD (GENLIST (\j. n ** 2 ** j) 0) = n ** (2 ** 0 - 1)
      LHS = PROD (GENLIST (\j. n ** 2 ** j) 0)
          = PROD []                by GENLIST_0
          = 1                      by PROD
      RHS = n ** (1 - 1)           by EXP_0
          = n ** 0 = 1 = LHS       by EXP_0
   Step: PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1) ==>
         PROD (GENLIST (\j. n ** 2 ** j) (SUC m)) = n ** (2 ** SUC m - 1)
         PROD (GENLIST (\j. n ** 2 ** j) (SUC m))
       = PROD (SNOC (n ** 2 ** m) (GENLIST (\j. n ** 2 ** j) m))   by GENLIST
       = PROD (GENLIST (\j. n ** 2 ** j) m) * (n ** 2 ** m)        by PROD_SNOC
       = n ** (2 ** m - 1) * n ** 2 ** m                           by induction hypothesis
       = n ** (2 ** m - 1 + 2 ** m)                                by EXP_ADD
       = n ** (2 * 2 ** m - 1)                                     by arithmetic
       = n ** (2 ** SUC m - 1)                                     by EXP
*)
val PROD_SQUARING_LIST = store_thm(
  "PROD_SQUARING_LIST",
  ``!m n. PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1)``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[] >>
  qabbrev_tac `f = \j. n ** 2 ** j` >>
  `PROD (GENLIST f (SUC m)) = PROD (SNOC (n ** 2 ** m) (GENLIST f m))` by rw[GENLIST, Abbr`f`] >>
  `_ = PROD (GENLIST f m) * (n ** 2 ** m)` by rw[PROD_SNOC] >>
  `_ = n ** (2 ** m - 1) * n ** 2 ** m` by rw[] >>
  `_ = n ** (2 ** m - 1 + 2 ** m)` by rw[EXP_ADD] >>
  rw[EXP]);

(* ------------------------------------------------------------------------- *)
(* List Range                                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: LENGTH [m .. n] = n + 1 - m *)
(* Proof:
     LENGTH [m .. n]
   = LENGTH (GENLIST (\i. m + i) (n + 1 - m))  by listRangeINC_def
   = n + 1 - m                                 by LENGTH_GENLIST
*)
val listRangeINC_LEN = store_thm(
  "listRangeINC_LEN",
  ``!m n. LENGTH [m .. n] = n + 1 - m``,
  rw[listRangeINC_def]);

(* Theorem: ([m .. n] = []) <=> (n + 1 <= m) *)
(* Proof:
              [m .. n] = []
   <=> LENGTH [m .. n] = 0         by LENGTH_NIL
   <=>       n + 1 - m = 0         by listRangeINC_LEN
   <=>          n + 1 <= m         by arithmetic
*)
val listRangeINC_NIL = store_thm(
  "listRangeINC_NIL",
  ``!m n. ([m .. n] = []) <=> (n + 1 <= m)``,
  metis_tac[listRangeINC_LEN, LENGTH_NIL, DECIDE``(n + 1 - m = 0) <=> (n + 1 <= m)``]);

(* Rename a theorem *)
val listRangeINC_MEM = save_thm("listRangeINC_MEM",
    MEM_listRangeINC |> GEN ``x:num`` |> GEN ``n:num`` |> GEN ``m:num``);
(*
val listRangeINC_MEM = |- !m n x. MEM x [m .. n] <=> m <= x /\ x <= n: thm
*)

(*
EL_listRangeLHI
|- lo + i < hi ==> EL i [lo ..< hi] = lo + i
*)

(* Theorem: m + i <= n ==> (EL i [m .. n] = m + i) *)
(* Proof: by listRangeINC_def *)
val listRangeINC_EL = store_thm(
  "listRangeINC_EL",
  ``!m n i. m + i <= n ==> (EL i [m .. n] = m + i)``,
  rw[listRangeINC_def]);

(* Theorem: EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. MEM x [m .. n] ==> P x      by EVERY_MEM
   <=> !x. m <= x /\ x <= n ==> P x    by MEM_listRangeINC
*)
val listRangeINC_EVERY = store_thm(
  "listRangeINC_EVERY",
  ``!P m n. EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x``,
  rw[EVERY_MEM, MEM_listRangeINC]);

(* Theorem: EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x *)
(* Proof:
       EXISTS P [m .. n]
   <=> ?x. MEM x [m .. n] /\ P x      by EXISTS_MEM
   <=> ?x. m <= x /\ x <= n /\ P e    by MEM_listRangeINC
*)
val listRangeINC_EXISTS = store_thm(
  "listRangeINC_EXISTS",
  ``!P m n. EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x``,
  metis_tac[EXISTS_MEM, MEM_listRangeINC]);

(* Theorem: EVERY P [m .. n] <=> ~(EXISTS ($~ o P) [m .. n]) *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. m <= x /\ x <= n ==> P x        by listRangeINC_EVERY
   <=> ~(?x. m <= x /\ x <= n /\ ~(P x))   by negation
   <=> ~(EXISTS ($~ o P) [m .. m])         by listRangeINC_EXISTS
*)
val listRangeINC_EVERY_EXISTS = store_thm(
  "listRangeINC_EVERY_EXISTS",
  ``!P m n. EVERY P [m .. n] <=> ~(EXISTS ($~ o P) [m .. n])``,
  rw[listRangeINC_EVERY, listRangeINC_EXISTS]);

(* Theorem: EXISTS P [m .. n] <=> ~(EVERY ($~ o P) [m .. n]) *)
(* Proof:
       EXISTS P [m .. n]
   <=> ?x. m <= x /\ x <= m /\ P x           by listRangeINC_EXISTS
   <=> ~(!x. m <= x /\ x <= n ==> ~(P x))    by negation
   <=> ~(EVERY ($~ o P) [m .. n])            by listRangeINC_EVERY
*)
val listRangeINC_EXISTS_EVERY = store_thm(
  "listRangeINC_EXISTS_EVERY",
  ``!P m n. EXISTS P [m .. n] <=> ~(EVERY ($~ o P) [m .. n])``,
  rw[listRangeINC_EXISTS, listRangeINC_EVERY]);

(* Theorem: m <= n + 1 ==> ([m .. (n + 1)] = SNOC (n + 1) [m .. n]) *)
(* Proof:
     [m .. (n + 1)]
   = GENLIST (\i. m + i) ((n + 1) + 1 - m)                      by listRangeINC_def
   = GENLIST (\i. m + i) (1 + (n + 1 - m))                      by arithmetic
   = GENLIST (\i. m + i) (n + 1 - m) ++ GENLIST (\t. (\i. m + i) (t + n + 1 - m)) 1  by GENLIST_APPEND
   = [m .. n] ++ GENLIST (\t. (\i. m + i) (t + n + 1 - m)) 1    by listRangeINC_def
   = [m .. n] ++ [(\t. (\i. m + i) (t + n + 1 - m)) 0]          by GENLIST_1
   = [m .. n] ++ [m + n + 1 - m]                                by function evaluation
   = [m .. n] ++ [n + 1]                                        by arithmetic
   = SNOC (n + 1) [m .. n]                                      by SNOC_APPEND
*)
val listRangeINC_SNOC = store_thm(
  "listRangeINC_SNOC",
  ``!m n. m <= n + 1 ==> ([m .. (n + 1)] = SNOC (n + 1) [m .. n])``,
  rw[listRangeINC_def] >>
  `(n + 2 - m = 1 + (n + 1 - m)) /\ (n + 1 - m + m = n + 1)` by decide_tac >>
  rw_tac std_ss[GENLIST_APPEND, GENLIST_1]);

(* Theorem: m <= n + 1 ==> (FRONT [m .. (n + 1)] = [m .. n]) *)
(* Proof:
     FRONT [m .. (n + 1)]
   = FRONT (SNOC (n + 1) [m .. n]))    by listRangeINC_SNOC
   = [m .. n]                          by FRONT_SNOC
*)
Theorem listRangeINC_FRONT:
  !m n. m <= n + 1 ==> (FRONT [m .. (n + 1)] = [m .. n])
Proof
  simp[listRangeINC_SNOC, FRONT_SNOC]
QED

(* Theorem: m <= n ==> (LAST [m .. n] = n) *)
(* Proof:
   Let ls = [m .. n]
   Note ls <> []                   by listRangeINC_NIL
     so LAST ls
      = EL (PRE (LENGTH ls)) ls    by LAST_EL
      = EL (PRE (n + 1 - m)) ls    by listRangeINC_LEN
      = EL (n - m) ls              by arithmetic
      = n                          by listRangeINC_EL
   Or
      LAST [m .. n]
    = LAST (GENLIST (\i. m + i) (n + 1 - m))   by listRangeINC_def
    = LAST (GENLIST (\i. m + i) (SUC (n - m))  by arithmetic, m <= n
    = (\i. m + i) (n - m)                      by GENLIST_LAST
    = m + (n - m)                              by function application
    = n                                        by m <= n
   Or
    If n = 0, then m <= 0 means m = 0.
      LAST [0 .. 0] = LAST [0] = 0 = n   by LAST_DEF
    Otherwise n = SUC k.
      LAST [m .. n]
    = LAST (SNOC n [m .. k])             by listRangeINC_SNOC, ADD1
    = n                                  by LAST_SNOC
*)
Theorem listRangeINC_LAST:
  !m n. m <= n ==> (LAST [m .. n] = n)
Proof
  rpt strip_tac >>
  Cases_on `n` >-
  fs[] >>
  metis_tac[listRangeINC_SNOC, LAST_SNOC, ADD1]
QED

(* Theorem: REVERSE [m .. n] = MAP (\x. n - x + m) [m .. n] *)
(* Proof:
     REVERSE [m .. n]
   = REVERSE (GENLIST (\i. m + i) (n + 1 - m))              by listRangeINC_def
   = GENLIST (\x. (\i. m + i) (PRE (n + 1 - m) - x)) (n + 1 - m)   by REVERSE_GENLIST
   = GENLIST (\x. (\i. m + i) (n - m - x)) (n + 1 - m)      by PRE
   = GENLIST (\x. (m + n - m - x) (n + 1 - m)               by function application
   = GENLIST (\x. n - x) (n + 1 - m)                        by arithmetic

     MAP (\x. n - x + m) [m .. n]
   = MAP (\x. n - x + m) (GENLIST (\i. m + i) (n + 1 - m))  by listRangeINC_def
   = GENLIST ((\x. n - x + m) o (\i. m + i)) (n + 1 - m)    by MAP_GENLIST
   = GENLIST (\i. n - (m + i) + m) (n + 1 - m)              by function composition
   = GENLIST (\i. n - i) (n + 1 - m)                        by arithmetic
*)
val listRangeINC_REVERSE = store_thm(
  "listRangeINC_REVERSE",
  ``!m n. REVERSE [m .. n] = MAP (\x. n - x + m) [m .. n]``,
  rpt strip_tac >>
  `(\m'. PRE (n + 1 - m) - m' + m) = ((\x. n - x + m) o (\i. i + m))` by rw[FUN_EQ_THM, combinTheory.o_THM] >>
  rw[listRangeINC_def, REVERSE_GENLIST, MAP_GENLIST]);

(* Theorem: REVERSE (MAP f [m .. n]) = MAP (f o (\x. n - x + m)) [m .. n] *)
(* Proof:
    REVERSE (MAP f [m .. n])
  = MAP f (REVERSE [m .. n])                by MAP_REVERSE
  = MAP f (MAP (\x. n - x + m) [m .. n])    by listRangeINC_REVERSE
  = MAP (f o (\x. n - x + m)) [m .. n]      by MAP_MAP_o
*)
val listRangeINC_REVERSE_MAP = store_thm(
  "listRangeINC_REVERSE_MAP",
  ``!f m n. REVERSE (MAP f [m .. n]) = MAP (f o (\x. n - x + m)) [m .. n]``,
  metis_tac[MAP_REVERSE, listRangeINC_REVERSE, MAP_MAP_o]);

(* Theorem: MAP f [(m + 1) .. (n + 1)] = MAP (f o SUC) [m .. n] *)
(* Proof:
   Note (\i. (m + 1) + i) = SUC o (\i. (m + i))                 by FUN_EQ_THM
     MAP f [(m + 1) .. (n + 1)]
   = MAP f (GENLIST (\i. (m + 1) + i) ((n + 1) + 1 - (m + 1)))  by listRangeINC_def
   = MAP f (GENLIST (\i. (m + 1) + i) (n + 1 - m))              by arithmetic
   = MAP f (GENLIST (SUC o (\i. (m + i))) (n + 1 - m))          by above
   = MAP (f o SUC) (GENLIST (\i. (m + i)) (n + 1 - m))          by MAP_GENLIST
   = MAP (f o SUC) [m .. n]                                     by listRangeINC_def
*)
val listRangeINC_MAP_SUC = store_thm(
  "listRangeINC_MAP_SUC",
  ``!f m n. MAP f [(m + 1) .. (n + 1)] = MAP (f o SUC) [m .. n]``,
  rpt strip_tac >>
  `(\i. (m + 1) + i) = SUC o (\i. (m + i))` by rw[FUN_EQ_THM] >>
  rw[listRangeINC_def, MAP_GENLIST]);

(* Theorem: a <= b /\ b <= c ==> ([a .. b] ++ [(b + 1) .. c] = [a .. c]) *)
(* Proof:
   By listRangeINC_def, this is to show:
      GENLIST (\i. a + i) (b + 1 - a) ++ GENLIST (\i. b + (i + 1)) (c - b) = GENLIST (\i. a + i) (c + 1 - a)
   Let f = \i. a + i.
   Note (\t. f (t + (b + 1 - a))) = (\i. b + (i + 1))     by FUN_EQ_THM
   Thus GENLIST (\i. b + (i + 1)) (c - b) = GENLIST (\t. f (t + (b + 1 - a))) (c - b)  by GENLIST_FUN_EQ
   Now (c - b) + (b + 1 - a) = c + 1 - a                   by a <= b /\ b <= c
   The result follows                                      by GENLIST_APPEND
*)
val listRangeINC_APPEND = store_thm(
  "listRangeINC_APPEND",
  ``!a b c. a <= b /\ b <= c ==> ([a .. b] ++ [(b + 1) .. c] = [a .. c])``,
  rw[listRangeINC_def] >>
  qabbrev_tac `f = \i. a + i` >>
  `(\t. f (t + (b + 1 - a))) = (\i. b + (i + 1))` by rw[FUN_EQ_THM, Abbr`f`] >>
  `GENLIST (\i. b + (i + 1)) (c - b) = GENLIST (\t. f (t + (b + 1 - a))) (c - b)` by rw[GSYM GENLIST_FUN_EQ] >>
  `(c - b) + (b + 1 - a) = c + 1 - a` by decide_tac >>
  metis_tac[GENLIST_APPEND]);

(* Theorem: SUM [m .. n] = SUM [1 .. n] - SUM [1 .. (m - 1)] *)
(* Proof:
   If m = 0,
      Then [1 .. (m-1)] = [1 .. 0] = []   by listRangeINC_EMPTY
           SUM [0 .. n]
         = SUM (0::[1 .. n])              by listRangeINC_CONS
         = 0 + SUM [1 .. n]               by SUM_CONS
         = SUM [1 .. n] - 0               by arithmetic
         = SUM [1 .. n] - SUM []          by SUM_NIL
   If m = 1,
      Then [1 .. (m-1)] = [1 .. 0] = []   by listRangeINC_EMPTY
           SUM [1 .. n]
         = SUM [1 .. n] - 0               by arithmetic
         = SUM [1 .. n] - SUM []          by SUM_NIL
   Otherwise 1 < m, or 1 <= m - 1.
   If n < m,
      Then SUM [m .. n] = 0               by listRangeINC_EMPTY
      If n = 0,
         Then SUM [1 .. 0] = 0            by listRangeINC_EMPTY
          and 0 - SUM [1 .. (m - 1)] = 0  by integer subtraction
      If n <> 0,
         Then 1 <= n /\ n <= m - 1        by arithmetic
          ==> [1 .. m - 1] =
              [1 .. n] ++ [(n + 1) .. (m - 1)]         by listRangeINC_APPEND
           or SUM [1 .. m - 1]
            = SUM [1 .. n] + SUM [(n + 1) .. (m - 1)]  by SUM_APPEND
         Thus SUM [1 .. n] - SUM [1 .. m - 1] = 0      by subtraction
   If ~(n < m), then m <= n.
      Note m - 1 < n /\ (m - 1 + 1 = m)                by arithmetic
      Thus [1 .. n] = [1 .. (m - 1)] ++ [m .. n]       by listRangeINC_APPEND
        or SUM [1 .. n]
         = SUM [1 .. (m - 1)] + SUM [m .. n]           by SUM_APPEND
      The result follows                               by subtraction
*)
val listRangeINC_SUM = store_thm(
  "listRangeINC_SUM",
  ``!m n. SUM [m .. n] = SUM [1 .. n] - SUM [1 .. (m - 1)]``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[listRangeINC_EMPTY, listRangeINC_CONS] >>
  Cases_on `m = 1` >-
  rw[listRangeINC_EMPTY] >>
  Cases_on `n < m` >| [
    Cases_on `n = 0` >-
    rw[listRangeINC_EMPTY] >>
    `1 <= n /\ n <= m - 1` by decide_tac >>
    `[1 .. m - 1] = [1 .. n] ++ [(n + 1) .. (m - 1)]` by rw[listRangeINC_APPEND] >>
    `SUM [1 .. m - 1] = SUM [1 .. n] + SUM [(n + 1) .. (m - 1)]` by rw[GSYM SUM_APPEND] >>
    `SUM [m .. n] = 0` by rw[listRangeINC_EMPTY] >>
    decide_tac,
    `1 <= m - 1 /\ m - 1 <= n /\ (m - 1 + 1 = m)` by decide_tac >>
    `[1 .. n] = [1 .. (m - 1)] ++ [m .. n]` by metis_tac[listRangeINC_APPEND] >>
    `SUM [1 .. n] = SUM [1 .. (m - 1)] + SUM [m .. n]` by rw[GSYM SUM_APPEND] >>
    decide_tac
  ]);

(* Theorem: 0 < m ==> 0 < PROD [m .. n] *)
(* Proof:
   Note MEM 0 [m .. n] = F        by MEM_listRangeINC
   Thus PROD [m .. n] <> 0        by PROD_EQ_0
   The result follows.
   or
   Note EVERY_POSITIVE [m .. n]   by listRangeINC_EVERY
   Thus 0 < PROD [m .. n]         by PROD_POS
*)
val listRangeINC_PROD_pos = store_thm(
  "listRangeINC_PROD_pos",
  ``!m n. 0 < m ==> 0 < PROD [m .. n]``,
  rw[PROD_POS, listRangeINC_EVERY]);

(* Theorem: 0 < m /\ m <= n ==> (PROD [m .. n] = PROD [1 .. n] DIV PROD [1 .. (m - 1)]) *)
(* Proof:
   If m = 1,
      Then [1 .. (m-1)] = [1 .. 0] = []   by listRangeINC_EMPTY
           PROD [1 .. n]
         = PROD [1 .. n] DIV 1            by DIV_ONE
         = PROD [1 .. n] DIV PROD []      by PROD_NIL
   If m <> 1, then 1 <= m                 by m <> 0, m <> 1
   Note 1 <= m - 1 /\ m - 1 < n /\ (m - 1 + 1 = m)            by arithmetic
   Thus [1 .. n] = [1 .. (m - 1)] ++ [m .. n]                 by listRangeINC_APPEND
     or PROD [1 .. n] = PROD [1 .. (m - 1)] * PROD [m .. n]   by PROD_POS
    Now 0 < PROD [1 .. (m - 1)]                               by listRangeINC_PROD_pos
   The result follows                                         by MULT_TO_DIV
*)
val listRangeINC_PROD = store_thm(
  "listRangeINC_PROD",
  ``!m n. 0 < m /\ m <= n ==> (PROD [m .. n] = PROD [1 .. n] DIV PROD [1 .. (m - 1)])``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[listRangeINC_EMPTY] >>
  `1 <= m - 1 /\ m - 1 <= n /\ (m - 1 + 1 = m)` by decide_tac >>
  `[1 .. n] = [1 .. (m - 1)] ++ [m .. n]` by metis_tac[listRangeINC_APPEND] >>
  `PROD [1 .. n] = PROD [1 .. (m - 1)] * PROD [m .. n]` by rw[GSYM PROD_APPEND] >>
  `0 < PROD [1 .. (m - 1)]` by rw[listRangeINC_PROD_pos] >>
  metis_tac[MULT_TO_DIV]);

(* Theorem: 0 < n /\ m <= x /\ x divides n ==> MEM x [m .. n] *)
(* Proof:
   Note x divdes n ==> x <= n     by DIVIDES_LE, 0 < n
     so MEM x [m .. n]            by listRangeINC_MEM
*)
val listRangeINC_has_divisors = store_thm(
  "listRangeINC_has_divisors",
  ``!m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m .. n]``,
  rw[listRangeINC_MEM, DIVIDES_LE]);

(* Theorem: [1 .. n] = GENLIST SUC n *)
(* Proof: by listRangeINC_def *)
val listRangeINC_1_n = store_thm(
  "listRangeINC_1_n",
  ``!n. [1 .. n] = GENLIST SUC n``,
  rpt strip_tac >>
  `(\i. i + 1) = SUC` by rw[FUN_EQ_THM] >>
  rw[listRangeINC_def]);

(* Theorem: MAP f [1 .. n] = GENLIST (f o SUC) n *)
(* Proof:
     MAP f [1 .. n]
   = MAP f (GENLIST SUC n)     by listRangeINC_1_n
   = GENLIST (f o SUC) n       by MAP_GENLIST
*)
val listRangeINC_MAP = store_thm(
  "listRangeINC_MAP",
  ``!f n. MAP f [1 .. n] = GENLIST (f o SUC) n``,
  rw[listRangeINC_1_n, MAP_GENLIST]);

(* Theorem: SUM (MAP f [1 .. (SUC n)]) = f (SUC n) + SUM (MAP f [1 .. n]) *)
(* Proof:
      SUM (MAP f [1 .. (SUC n)])
    = SUM (MAP f (SNOC (SUC n) [1 .. n]))       by listRangeINC_SNOC
    = SUM (SNOC (f (SUC n)) (MAP f [1 .. n]))   by MAP_SNOC
    = f (SUC n) + SUM (MAP f [1 .. n])          by SUM_SNOC
*)
val listRangeINC_SUM_MAP = store_thm(
  "listRangeINC_SUM_MAP",
  ``!f n. SUM (MAP f [1 .. (SUC n)]) = f (SUC n) + SUM (MAP f [1 .. n])``,
  rw[listRangeINC_SNOC, MAP_SNOC, SUM_SNOC, ADD1]);

(* Theorem: [m ..< (n + 1)] = [m .. n] *)
(* Proof:
     [m ..< (n + 1)]
   =  GENLIST (\i. m + i) (n + 1 - m)    by listRangeLHI_def
   = [m .. n]                            by listRangeINC_def
*)
val listRangeLHI_to_listRangeINC = store_thm(
  "listRangeLHI_to_listRangeINC",
  ``!m n. [m ..< (n + 1)] = [m .. n]``,
  rw[listRangeLHI_def, listRangeINC_def]);

(* Theorem alias *)
val listRangeLHI_LEN = save_thm("listRangeLHI_LEN",  LENGTH_listRangeLHI |> GEN_ALL);
(* val listRangeLHI_LEN = |- !lo hi. LENGTH [lo ..< hi] = hi - lo: thm *)

(* Theorem: LENGTH [m ..< n] = n - m *)
(* Proof: by LENGTH_listRangeLHI *)
val listRangeLHI_LEN = store_thm(
  "listRangeLHI_LEN",
  ``!m n. LENGTH [m ..< n] = n - m``,
  rw[LENGTH_listRangeLHI]);

(* Theorem: ([m ..< n] = []) <=> n <= m *)
(* Proof:
   If n = 0, LHS = T, RHS = T    hence true.
   If n <> 0, then n = SUC k     by num_CASES
       [m ..< n] = []
   <=> [m ..< SUC k] = []        by n = SUC k
   <=> [m .. k] = []             by listRangeLHI_to_listRangeINC
   <=> k + 1 <= m                by listRangeINC_NIL
   <=>     n <= m                by ADD1
*)
val listRangeLHI_NIL = store_thm(
  "listRangeLHI_NIL",
  ``!m n. ([m ..< n] = []) <=> n <= m``,
  rpt strip_tac >>
  Cases_on `n` >-
  rw[listRangeLHI_def] >>
  rw[listRangeLHI_to_listRangeINC, listRangeINC_NIL, ADD1]);

(* Theorem: MEM x [m ..< n] <=> m <= x /\ x < n *)
(* Proof: by MEM_listRangeLHI *)
val listRangeLHI_MEM = store_thm(
  "listRangeLHI_MEM",
  ``!m n x. MEM x [m ..< n] <=> m <= x /\ x < n``,
  rw[MEM_listRangeLHI]);

(* Theorem: m + i < n ==> EL i [m ..< n] = m + i *)
(* Proof: EL_listRangeLHI *)
val listRangeLHI_EL = store_thm(
  "listRangeLHI_EL",
  ``!m n i. m + i < n ==> (EL i [m ..< n] = m + i)``,
  rw[EL_listRangeLHI]);

(* Theorem: EVERY P [m ..< n] <=> !x. m <= x /\ x < n ==> P x *)
(* Proof:
       EVERY P [m ..< n]
   <=> !x. MEM x [m ..< n] ==> P e      by EVERY_MEM
   <=> !x. m <= x /\ x < n ==> P e    by MEM_listRangeLHI
*)
val listRangeLHI_EVERY = store_thm(
  "listRangeLHI_EVERY",
  ``!P m n. EVERY P [m ..< n] <=> !x. m <= x /\ x < n ==> P x``,
  rw[EVERY_MEM, MEM_listRangeLHI]);

(* Theorem: m <= n ==> ([m ..< n + 1] = SNOC n [m ..< n]) *)
(* Proof:
   If n = 0,
      Then m = 0               by m <= n
      LHS = [0 ..< 1] = [0]
      RHS = SNOC 0 [0 ..< 0]
          = SNOC 0 []          by listRangeLHI_def
          = [0] = LHS          by SNOC
   If n <> 0,
      Then n = (n - 1) + 1     by arithmetic
       [m ..< n + 1]
     = [m .. n]                by listRangeLHI_to_listRangeINC
     = SNOC n [m .. n - 1]     by listRangeINC_SNOC, m <= (n - 1) + 1
     = SNOC n [m ..< n]        by listRangeLHI_to_listRangeINC
*)
val listRangeLHI_SNOC = store_thm(
  "listRangeLHI_SNOC",
  ``!m n. m <= n ==> ([m ..< n + 1] = SNOC n [m ..< n])``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `m = 0` by decide_tac >>
    rw[listRangeLHI_def],
    `n = (n - 1) + 1` by decide_tac >>
    `[m ..< n + 1] = [m .. n]` by rw[listRangeLHI_to_listRangeINC] >>
    `_ = SNOC n [m .. n - 1]` by metis_tac[listRangeINC_SNOC] >>
    `_ = SNOC n [m ..< n]` by rw[GSYM listRangeLHI_to_listRangeINC] >>
    rw[]
  ]);

(* Theorem: m <= n ==> (FRONT [m .. < n + 1] = [m .. <n]) *)
(* Proof:
     FRONT [m ..< n + 1]
   = FRONT (SNOC n [m ..< n]))     by listRangeLHI_SNOC
   = [m ..< n]                     by FRONT_SNOC
*)
Theorem listRangeLHI_FRONT:
  !m n. m <= n ==> (FRONT [m ..< n + 1] = [m ..< n])
Proof
  simp[listRangeLHI_SNOC, FRONT_SNOC]
QED

(* Theorem: m <= n ==> (LAST [m ..< n + 1] = n) *)
(* Proof:
      LAST [m ..< n + 1]
    = LAST (SNOC n [m ..< n])      by listRangeLHI_SNOC
    = n                            by LAST_SNOC
*)
Theorem listRangeLHI_LAST:
  !m n. m <= n ==> (LAST [m ..< n + 1] = n)
Proof
  simp[listRangeLHI_SNOC, LAST_SNOC]
QED

(* Theorem: REVERSE [m ..< n] = MAP (\x. n - 1 - x + m) [m ..< n] *)
(* Proof:
   If n = 0,
      LHS = REVERSE []            by listRangeLHI_def
          = []                    by REVERSE_DEF
          = MAP f [] = RHS        by MAP
   If n <> 0,
      Then n = k + 1 for some k   by num_CASES, ADD1
        REVERSE [m ..< n]
      = REVERSE [m .. k]                   by listRangeLHI_to_listRangeINC
      = MAP (\x. k - x + m) [m .. k]       by listRangeINC_REVERSE
      = MAP (\x. n - 1 - x + m) [m ..< n]  by listRangeLHI_to_listRangeINC
*)
val listRangeLHI_REVERSE = store_thm(
  "listRangeLHI_REVERSE",
  ``!m n. REVERSE [m ..< n] = MAP (\x. n - 1 - x + m) [m ..< n]``,
  rpt strip_tac >>
  Cases_on `n` >-
  rw[listRangeLHI_def] >>
  `REVERSE [m ..< SUC n'] = REVERSE [m .. n']` by rw[listRangeLHI_to_listRangeINC, ADD1] >>
  `_ = MAP (\x. n' - x + m) [m .. n']` by rw[listRangeINC_REVERSE] >>
  `_ = MAP (\x. n' - x + m) [m ..< (SUC n')]` by rw[GSYM listRangeLHI_to_listRangeINC, ADD1] >>
  rw[]);

(* Theorem: REVERSE (MAP f [m ..< n]) = MAP (f o (\x. n - 1 - x + m)) [m ..< n] *)
(* Proof:
    REVERSE (MAP f [m ..< n])
  = MAP f (REVERSE [m ..< n])                    by MAP_REVERSE
  = MAP f (MAP (\x. n - 1 - x + m) [m ..< n])    by listRangeLHI_REVERSE
  = MAP (f o (\x. n - 1 - x + m)) [m ..< n]      by MAP_MAP_o
*)
val listRangeLHI_REVERSE_MAP = store_thm(
  "listRangeLHI_REVERSE_MAP",
  ``!f m n. REVERSE (MAP f [m ..< n]) = MAP (f o (\x. n - 1 - x + m)) [m ..< n]``,
  metis_tac[MAP_REVERSE, listRangeLHI_REVERSE, MAP_MAP_o]);

(* Theorem: MAP f [(m + 1) ..< (n + 1)] = MAP (f o SUC) [m ..< n] *)
(* Proof:
   Note (\i. (m + 1) + i) = SUC o (\i. (m + i))             by FUN_EQ_THM
     MAP f [(m + 1) ..< (n + 1)]
   = MAP f (GENLIST (\i. (m + 1) + i) ((n + 1) - (m + 1)))  by listRangeLHI_def
   = MAP f (GENLIST (\i. (m + 1) + i) (n - m))              by arithmetic
   = MAP f (GENLIST (SUC o (\i. (m + i))) (n - m))          by above
   = MAP (f o SUC) (GENLIST (\i. (m + i)) (n - m))          by MAP_GENLIST
   = MAP (f o SUC) [m ..< n]                                by listRangeLHI_def
*)
val listRangeLHI_MAP_SUC = store_thm(
  "listRangeLHI_MAP_SUC",
  ``!f m n. MAP f [(m + 1) ..< (n + 1)] = MAP (f o SUC) [m ..< n]``,
  rpt strip_tac >>
  `(\i. (m + 1) + i) = SUC o (\i. (m + i))` by rw[FUN_EQ_THM] >>
  rw[listRangeLHI_def, MAP_GENLIST]);


(* Theorem: a <= b /\ b <= c ==> [a ..< b] ++ [b ..< c] = [a ..< c] *)
(* Proof:
   If a = b,
       LHS = [a ..< a] ++ [a ..< c]
           = [] ++ [a ..< c]        by listRangeLHI_def
           = [a ..< c] = RHS        by APPEND
   If a <> b,
      Then a < b,                   by a <= b
        so b <> 0, and c <> 0       by b <= c
      Let b = b' + 1, c = c' + 1    by num_CASES, ADD1
      Then a <= b' /\ b' <= c.
        [a ..< b] ++ [b ..< c]
      = [a .. b'] ++ [b' + 1 .. c']   by listRangeLHI_to_listRangeINC
      = [a .. c']                     by listRangeINC_APPEND
      = [a ..< c]                     by listRangeLHI_to_listRangeINC
*)
val listRangeLHI_APPEND = store_thm(
  "listRangeLHI_APPEND",
  ``!a b c. a <= b /\ b <= c ==> ([a ..< b] ++ [b ..< c] = [a ..< c])``,
  rpt strip_tac >>
  `(a = b) \/ (a < b)` by decide_tac >-
  rw[listRangeLHI_def] >>
  `b <> 0 /\ c <> 0` by decide_tac >>
  `?b' c'. (b = b' + 1) /\ (c = c' + 1)` by metis_tac[num_CASES, ADD1] >>
  `a <= b' /\ b' <= c` by decide_tac >>
  `[a ..< b] ++ [b ..< c] = [a .. b'] ++ [b' + 1 .. c']` by rw[listRangeLHI_to_listRangeINC] >>
  `_ = [a .. c']` by rw[listRangeINC_APPEND] >>
  `_ = [a ..< c]` by rw[GSYM listRangeLHI_to_listRangeINC] >>
  rw[]);

(* Theorem: SUM [m ..< n] = SUM [1 ..< n] - SUM [1 ..< m] *)
(* Proof:
   If n = 0,
      LHS = SUM [m ..< 0] = SUM [] = 0        by listRangeLHI_EMPTY
      RHS = SUM [1 ..< 0] - SUM [1 ..< m]
          = SUM [] - SUM [1 ..< m]            by listRangeLHI_EMPTY
          = 0 - SUM [1 ..< m] = 0 = LHS       by integer subtraction
   If m = 0,
      LHS = SUM [0 ..< n]
          = SUM (0 :: [1 ..< n])              by listRangeLHI_CONS
          = 0 + SUM [1 ..< n]                 by SUM
          = SUM [1 ..< n]                     by arithmetic
      RHS = SUM [1 ..< n] - SUM [1 ..< 0]     by integer subtraction
          = SUM [1 ..< n] - SUM []            by listRangeLHI_EMPTY
          = SUM [1 ..< n] - 0                 by SUM
          = LHS
   Otherwise,
      n <> 0, and m <> 0.
      Let n = n' + 1, m = m' + 1              by num_CASES, ADD1
         SUM [m ..< n]
       = SUM [m .. n']                        by listRangeLHI_to_listRangeINC
       = SUM [1 .. n'] - SUM [1 .. m - 1]     by listRangeINC_SUM
       = SUM [1 .. n'] - SUM [1 .. m']        by m' = m - 1
       = SUM [1 ..< n] - SUM [1 ..< m]        by listRangeLHI_to_listRangeINC
*)
val listRangeLHI_SUM = store_thm(
  "listRangeLHI_SUM",
  ``!m n. SUM [m ..< n] = SUM [1 ..< n] - SUM [1 ..< m]``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[listRangeLHI_EMPTY] >>
  Cases_on `m = 0` >-
  rw[listRangeLHI_EMPTY, listRangeLHI_CONS] >>
  `?n' m'. (n = n' + 1) /\ (m = m' + 1)` by metis_tac[num_CASES, ADD1] >>
  `SUM [m ..< n] = SUM [m .. n']` by rw[listRangeLHI_to_listRangeINC] >>
  `_ = SUM [1 .. n'] - SUM [1 .. m - 1]` by rw[GSYM listRangeINC_SUM] >>
  `_ = SUM [1 .. n'] - SUM [1 .. m']` by rw[] >>
  `_ = SUM [1 ..< n] - SUM [1 ..< m]` by rw[GSYM listRangeLHI_to_listRangeINC] >>
  rw[]);

(* Theorem: 0 < m ==> 0 < PROD [m ..< n] *)
(* Proof:
   Note MEM 0 [m ..< n] = F        by MEM_listRangeLHI
   Thus PROD [m ..< n] <> 0        by PROD_EQ_0
   The result follows.
   or,
   Note EVERY_POSITIVE [m ..< n]   by listRangeLHI_EVERY
   Thus 0 < PROD [m ..< n]         by PROD_POS
*)
val listRangeLHI_PROD_pos = store_thm(
  "listRangeLHI_PROD_pos",
  ``!m n. 0 < m ==> 0 < PROD [m ..< n]``,
  rw[PROD_POS, listRangeLHI_EVERY]);

(* Theorem: 0 < m /\ m <= n ==> (PROD [m ..< n] = PROD [1 ..< n] DIV PROD [1 ..< m]) *)
(* Proof:
   Note n <> 0                    by 0 < m /\ m <= n
   Let m = m' + 1, n = n' + 1     by num_CASES, ADD1
   If m = n,
      Note 0 < PROD [1 ..< n]     by listRangeLHI_PROD_pos
      LHS = PROD [n ..< n]
          = PROD [] = 1           by listRangeLHI_EMPTY
      RHS = PROD [1 ..< n] DIV PROD [1 ..< n]
          = 1                     by DIVMOD_ID, 0 < PROD [1 ..< n]
   If m <> n,
      Then m < n, or m <= n'      by arithmetic
        PROD [m ..< n]
      = PROD [m .. n']                          by listRangeLHI_to_listRangeINC
      = PROD [1 .. n'] DIV PROD [1 .. m - 1]    by listRangeINC_PROD, m <= n'
      = PROD [1 .. n'] DIV PROD [1 .. m']       by m' = m - 1
      = PROD [1 ..< n] DIV PROD [1 ..< m]       by listRangeLHI_to_listRangeINC
*)
val listRangeLHI_PROD = store_thm(
  "listRangeLHI_PROD",
  ``!m n. 0 < m /\ m <= n ==> (PROD [m ..< n] = PROD [1 ..< n] DIV PROD [1 ..< m])``,
  rpt strip_tac >>
  `m <> 0 /\ n <> 0` by decide_tac >>
  `?n' m'. (n = n' + 1) /\ (m = m' + 1)` by metis_tac[num_CASES, ADD1] >>
  Cases_on `m = n` >| [
    `0 < PROD [1 ..< n]` by rw[listRangeLHI_PROD_pos] >>
    rfs[listRangeLHI_EMPTY, DIVMOD_ID],
    `m <= n'` by decide_tac >>
    `PROD [m ..< n] = PROD [m .. n']` by rw[listRangeLHI_to_listRangeINC] >>
    `_ = PROD [1 .. n'] DIV PROD [1 .. m - 1]` by rw[GSYM listRangeINC_PROD] >>
    `_ = PROD [1 .. n'] DIV PROD [1 .. m']` by rw[] >>
    `_ = PROD [1 ..< n] DIV PROD [1 ..< m]` by rw[GSYM listRangeLHI_to_listRangeINC] >>
    rw[]
  ]);

(* Theorem: 0 < n /\ m <= x /\ x divides n ==> MEM x [m ..< n + 1] *)
(* Proof:
   Note the condition implies:
        MEM x [m .. n]         by listRangeINC_has_divisors
      = MEM x [m ..< n + 1]    by listRangeLHI_to_listRangeINC
*)
val listRangeLHI_has_divisors = store_thm(
  "listRangeLHI_has_divisors",
  ``!m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m ..< n + 1]``,
  metis_tac[listRangeINC_has_divisors, listRangeLHI_to_listRangeINC]);

(* Theorem: [0 ..< n] = GENLIST I n *)
(* Proof: by listRangeINC_def *)
val listRangeLHI_0_n = store_thm(
  "listRangeLHI_0_n",
  ``!n. [0 ..< n] = GENLIST I n``,
  rpt strip_tac >>
  `(\i:num. i) = I` by rw[FUN_EQ_THM] >>
  rw[listRangeLHI_def]);

(* Theorem: MAP f [0 ..< n] = GENLIST f n *)
(* Proof:
     MAP f [0 ..< n]
   = MAP f (GENLIST I n)     by listRangeLHI_0_n
   = GENLIST (f o I) n       by MAP_GENLIST
   = GENLIST f n             by I_THM
*)
val listRangeLHI_MAP = store_thm(
  "listRangeLHI_MAP",
  ``!f n. MAP f [0 ..< n] = GENLIST f n``,
  rw[listRangeLHI_0_n, MAP_GENLIST]);

(* Theorem: SUM (MAP f [0 ..< (SUC n)]) = f n + SUM (MAP f [0 ..< n]) *)
(* Proof:
      SUM (MAP f [0 ..< (SUC n)])
    = SUM (MAP f (SNOC n [0 ..< n]))       by listRangeLHI_SNOC
    = SUM (SNOC (f n) (MAP f [0 ..< n]))   by MAP_SNOC
    = f n + SUM (MAP f [0 ..< n])          by SUM_SNOC
*)
val listRangeLHI_SUM_MAP = store_thm(
  "listRangeLHI_SUM_MAP",
  ``!f n. SUM (MAP f [0 ..< (SUC n)]) = f n + SUM (MAP f [0 ..< n])``,
  rw[listRangeLHI_SNOC, MAP_SNOC, SUM_SNOC, ADD1]);

(* ------------------------------------------------------------------------- *)
(* List Summation and Product                                                *)
(* ------------------------------------------------------------------------- *)

(*
> numpairTheory.tri_def;
val it = |- tri 0 = 0 /\ !n. tri (SUC n) = SUC n + tri n: thm
*)

(* Theorem: SUM [1 .. n] = tri n *)
(* Proof:
   By induction on n,
   Base: SUM [1 .. 0] = tri 0
         SUM [1 .. 0]
       = SUM []          by listRangeINC_EMPTY
       = 0               by SUM_NIL
       = tri 0           by tri_def
   Step: SUM [1 .. n] = tri n ==> SUM [1 .. SUC n] = tri (SUC n)
         SUM [1 .. SUC n]
       = SUM (SNOC (SUC n) [1 .. n])     by listRangeINC_SNOC, 1 < n
       = SUM [1 .. n] + (SUC n)          by SUM_SNOC
       = tri n + (SUC n)                 by induction hypothesis
       = tri (SUC n)                     by tri_def
*)
val sum_1_to_n_eq_tri_n = store_thm(
  "sum_1_to_n_eq_tri_n",
  ``!n. SUM [1 .. n] = tri n``,
  Induct >-
  rw[listRangeINC_EMPTY, SUM_NIL, numpairTheory.tri_def] >>
  rw[listRangeINC_SNOC, ADD1, SUM_SNOC, numpairTheory.tri_def]);

(* Theorem: SUM [1 .. n] = HALF (n * (n + 1)) *)
(* Proof:
     SUM [1 .. n]
   = tri n                by sum_1_to_n_eq_tri_n
   = HALF (n * (n + 1))   by tri_formula
*)
val sum_1_to_n_eqn = store_thm(
  "sum_1_to_n_eqn",
  ``!n. SUM [1 .. n] = HALF (n * (n + 1))``,
  rw[sum_1_to_n_eq_tri_n, numpairTheory.tri_formula]);

(* Theorem: 2 * SUM [1 .. n] = n * (n + 1) *)
(* Proof:
   Note EVEN (n * (n + 1))         by EVEN_PARTNERS
     or 2 divides (n * (n + 1))    by EVEN_ALT
   Thus n * (n + 1)
      = ((n * (n + 1)) DIV 2) * 2  by DIV_MULT_EQ
      = (SUM [1 .. n]) * 2         by sum_1_to_n_eqn
      = 2 * SUM [1 .. n]           by MULT_COMM
*)
val sum_1_to_n_double = store_thm(
  "sum_1_to_n_double",
  ``!n. 2 * SUM [1 .. n] = n * (n + 1)``,
  rpt strip_tac >>
  `2 divides (n * (n + 1))` by rw[EVEN_PARTNERS, GSYM EVEN_ALT] >>
  metis_tac[sum_1_to_n_eqn, DIV_MULT_EQ, MULT_COMM, DECIDE``0 < 2``]);

(* Theorem: PROD [1 .. n] = FACT n *)
(* Proof:
   By induction on n,
   Base: PROD [1 .. 0] = FACT 0
         PROD [1 .. 0]
       = PROD []          by listRangeINC_EMPTY
       = 1                by PROD_NIL
       = FACT 0           by FACT
   Step: PROD [1 .. n] = FACT n ==> PROD [1 .. SUC n] = FACT (SUC n)
         PROD [1 .. SUC n] = FACT (SUC n)
       = PROD (SNOC (SUC n) [1 .. n])     by listRangeINC_SNOC, 1 < n
       = PROD [1 .. n] * (SUC n)          by PROD_SNOC
       = (FACT n) * (SUC n)               by induction hypothesis
       = FACT (SUC n)                     by FACT
*)
val prod_1_to_n_eq_fact_n = store_thm(
  "prod_1_to_n_eq_fact_n",
  ``!n. PROD [1 .. n] = FACT n``,
  Induct >-
  rw[listRangeINC_EMPTY, PROD_NIL, FACT] >>
  rw[listRangeINC_SNOC, ADD1, PROD_SNOC, FACT]);

(* This is numerical version of:
poly_cyclic_cofactor  |- !r. Ring r /\ #1 <> #0 ==> !n. unity n = unity 1 * cyclic n
*)
(* Theorem: (t ** n - 1 = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n])) *)
(* Proof:
   Let f = (\j. t ** j).
   By induction on n.
   Base: t ** 0 - 1 = (t - 1) * SUM (MAP f [0 ..< 0])
         LHS = t ** 0 - 1 = 0           by EXP_0
         RHS = (t - 1) * SUM (MAP f [0 ..< 0])
             = (t - 1) * SUM []         by listRangeLHI_EMPTY
             = (t - 1) * 0 = 0          by SUM
   Step: t ** n - 1 = (t - 1) * SUM (MAP f [0 ..< n]) ==>
         t ** SUC n - 1 = (t - 1) * SUM (MAP f [0 ..< SUC n])
       If t = 0,
          LHS = 0 ** SUC n - 1 = 0              by EXP_0
          RHS = (0 - 1) * SUM (MAP f [0 ..< SUC n])
              = 0 * SUM (MAP f [0 ..< SUC n])   by integer subtraction
              = 0 = LHS
       If t <> 0,
          Then 0 < t ** n                       by EXP_POS
            or 1 <= t ** n                      by arithmetic
            so (t ** n - 1) + (t * t ** n - t ** n) = t * t ** n - 1
            (t - 1) * SUM (MAP (\j. t ** j) [0 ..< (SUC n)])
          = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n + 1])        by ADD1
          = (t - 1) * SUM (MAP (\j. t ** j) (SNOC n [0 ..< n]))   by listRangeLHI_SNOC
          = (t - 1) * SUM (SNOC (t ** n) (MAP f [0 ..< n]))       by MAP_SNOC
          = (t - 1) * (SUM (MAP f [0 ..< n]) + t ** n)            by SUM_SNOC
          = (t - 1) * SUM (MAP f [0 ..< n]) + (t - 1) * t ** n    by RIGHT_ADD_DISTRIB
          = (t ** n - 1) + (t - 1) * t ** n                       by induction hypothesis
          = t ** SUC n - 1                                        by EXP
*)
val power_predecessor_eqn = store_thm(
  "power_predecessor_eqn",
  ``!t n. t ** n - 1 = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n])``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. t ** j` >>
  Induct_on `n` >-
  rw[EXP_0, Abbr`f`] >>
  Cases_on `t = 0` >-
  rw[ZERO_EXP, Abbr`f`] >>
  `(t ** n - 1) + (t * t ** n - t ** n) = t * t ** n - 1` by
  (`0 < t` by decide_tac >>
  `0 < t ** n` by rw[EXP_POS] >>
  `1 <= t ** n` by decide_tac >>
  `t ** n <= t * t ** n` by rw[] >>
  decide_tac) >>
  `(t - 1) * SUM (MAP f [0 ..< (SUC n)]) = (t - 1) * SUM (MAP f [0 ..< n + 1])` by rw[ADD1] >>
  `_ = (t - 1) * SUM (MAP f (SNOC n [0 ..< n]))` by rw[listRangeLHI_SNOC] >>
  `_ = (t - 1) * SUM (SNOC (t ** n) (MAP f [0 ..< n]))` by rw[MAP_SNOC, Abbr`f`] >>
  `_ = (t - 1) * (SUM (MAP f [0 ..< n]) + t ** n)` by rw[SUM_SNOC] >>
  `_ = (t - 1) * SUM (MAP f [0 ..< n]) + (t - 1) * t ** n` by rw[RIGHT_ADD_DISTRIB] >>
  `_ = (t ** n - 1) + (t - 1) * t ** n` by rw[] >>
  `_ = (t ** n - 1) + (t * t ** n - t ** n)` by rw[LEFT_SUB_DISTRIB] >>
  `_ = t * t ** n - 1` by rw[] >>
  `_ =  t ** SUC n - 1 ` by rw[GSYM EXP] >>
  rw[]);

(* Above is the formal proof of the following observation for any base:
        9 = 9 * 1
       99 = 9 * 11
      999 = 9 * 111
     9999 = 9 * 1111
    99999 = 8 * 11111
   etc.

  This asserts:
     (t ** n - 1) = (t - 1) * (1 + t + t ** 2 + ... + t ** (n-1))
  or  1 + t + t ** 2 + ... + t ** (n - 1) = (t ** n - 1) DIV (t - 1),
  which is the sum of the geometric series.
*)

(* Theorem: 1 < t ==> (SUM (MAP (\j. t ** j) [0 ..< n]) = (t ** n - 1) DIV (t - 1)) *)
(* Proof:
   Note 0 < t - 1                     by 1 < t
    Let s = SUM (MAP (\j. t ** j) [0 ..< n]).
   Then (t ** n - 1) = (t - 1) * s    by power_predecessor_eqn
   Thus s = (t ** n - 1) DIV (t - 1)  by MULT_TO_DIV, 0 < t - 1
*)
val geometric_sum_eqn = store_thm(
  "geometric_sum_eqn",
  ``!t n. 1 < t ==> (SUM (MAP (\j. t ** j) [0 ..< n]) = (t ** n - 1) DIV (t - 1))``,
  rpt strip_tac >>
  `0 < t - 1` by decide_tac >>
  rw_tac std_ss[power_predecessor_eqn, MULT_TO_DIV]);

(* Theorem: 1 < t ==> (SUM (MAP (\j. t ** j) [0 .. n]) = (t ** (n + 1) - 1) DIV (t - 1)) *)
(* Proof:
     SUM (MAP (\j. t ** j) [0 .. n])
   = SUM (MAP (\j. t ** j) [0 ..< n + 1])   by listRangeLHI_to_listRangeINC
   = (t ** (n + 1) - 1) DIV (t - 1)         by geometric_sum_eqn
*)
val geometric_sum_eqn_alt = store_thm(
  "geometric_sum_eqn_alt",
  ``!t n. 1 < t ==> (SUM (MAP (\j. t ** j) [0 .. n]) = (t ** (n + 1) - 1) DIV (t - 1))``,
  rw_tac std_ss[GSYM listRangeLHI_to_listRangeINC, geometric_sum_eqn]);

(* Theorem: SUM [1 ..< n] = HALF (n * (n - 1)) *)
(* Proof:
   If n = 0,
      LHS = SUM [1 ..< 0]
          = SUM [] = 0                by listRangeLHI_EMPTY
      RHS = HALF (0 * (0 - 1))
          = 0 = LHS                   by arithmetic
   If n <> 0,
      Then n = (n - 1) + 1            by arithmetic, n <> 0
        SUM [1 ..< n]
      = SUM [1 .. n - 1]              by listRangeLHI_to_listRangeINC
      = HALF ((n - 1) * (n - 1 + 1))  by sum_1_to_n_eqn
      = HALF (n * (n - 1))            by arithmetic
*)
val arithmetic_sum_eqn = store_thm(
  "arithmetic_sum_eqn",
  ``!n. SUM [1 ..< n] = HALF (n * (n - 1))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[listRangeLHI_EMPTY] >>
  `n = (n - 1) + 1` by decide_tac >>
  `SUM [1 ..< n] = SUM [1 .. n - 1]` by rw[GSYM listRangeLHI_to_listRangeINC] >>
  `_ = HALF ((n - 1) * (n - 1 + 1))` by rw[sum_1_to_n_eqn] >>
  `_ = HALF (n * (n - 1))` by rw[] >>
  rw[]);

(* Theorem alias *)
val arithmetic_sum_eqn_alt = save_thm("arithmetic_sum_eqn_alt", sum_1_to_n_eqn);
(* val arithmetic_sum_eqn_alt = |- !n. SUM [1 .. n] = HALF (n * (n + 1)): thm *)

(* Theorem: SUM (GENLIST (\j. f (n - j)) n) = SUM (MAP f [1 .. n]) *)
(* Proof:
     SUM (GENLIST (\j. f (n - j)) n)
   = SUM (REVERSE (GENLIST (\j. f (n - j)) n))     by SUM_REVERSE
   = SUM (GENLIST (\j. f (n - (PRE n - j))) n)     by REVERSE_GENLIST
   = SUM (GENLIST (\j. f (1 + j)) n)               by LIST_EQ, SUB_SUB
   = SUM (GENLIST (f o SUC) n)                     by FUN_EQ_THM
   = SUM (MAP f [1 .. n])                          by listRangeINC_MAP
*)
val SUM_GENLIST_REVERSE = store_thm(
  "SUM_GENLIST_REVERSE",
  ``!f n. SUM (GENLIST (\j. f (n - j)) n) = SUM (MAP f [1 .. n])``,
  rpt strip_tac >>
  `GENLIST (\j. f (n - (PRE n - j))) n = GENLIST (f o SUC) n` by
  (irule LIST_EQ >>
  rw[] >>
  `n + x - PRE n = SUC x` by decide_tac >>
  simp[]) >>
  qabbrev_tac `g = \j. f (n - j)` >>
  `SUM (GENLIST g n) = SUM (REVERSE (GENLIST g n))` by rw[SUM_REVERSE] >>
  `_ = SUM (GENLIST (\j. g (PRE n - j)) n)` by rw[REVERSE_GENLIST] >>
  `_ = SUM (GENLIST (f o SUC) n)` by rw[Abbr`g`] >>
  `_ = SUM (MAP f [1 .. n])` by rw[listRangeINC_MAP] >>
  decide_tac);
(* Note: locate here due to use of listRangeINC_MAP *)

(* ------------------------------------------------------------------------- *)
(* MAP of function with 3 list arguments                                     *)
(* ------------------------------------------------------------------------- *)

(* Define MAP3 similar to MAP2 in listTheory. *)
val dDefine = Lib.with_flag (Defn.def_suffix, "_DEF") Define;
val MAP3_DEF = dDefine`
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3) /\
  (MAP3 f x y z = [])`;
val _ = export_rewrites["MAP3_DEF"];
val MAP3 = store_thm ("MAP3",
``(!f. MAP3 f [] [] [] = []) /\
  (!f h1 t1 h2 t2 h3 t3. MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)``,
  METIS_TAC[MAP3_DEF]);

(*
LENGTH_MAP   |- !l f. LENGTH (MAP f l) = LENGTH l
LENGTH_MAP2  |- !xs ys. LENGTH (MAP2 f xs ys) = MIN (LENGTH xs) (LENGTH ys)
*)

(* Theorem: LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) *)
(* Proof:
   By induction on lx.
   Base: !ly lz f. LENGTH (MAP3 f [] ly lz) = MIN (MIN (LENGTH []) (LENGTH ly)) (LENGTH lz)
      LHS = LENGTH [] = 0                         by MAP3, LENGTH
      RHS = MIN (MIN 0 (LENGTH ly)) (LENGTH lz)   by LENGTH
          = MIN 0 (LENGTH lz) = 0 = LHS           by MIN_DEF
   Step: !ly lz f. LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
         !h ly lz f. LENGTH (MAP3 f (h::lx) ly lz) = MIN (MIN (LENGTH (h::lx)) (LENGTH ly)) (LENGTH lz)
      If ly = [],
         LHS = LENGTH (MAP3 f (h::lx) [] lz) = 0  by MAP3, LENGTH
         RHS = MIN (MIN (LENGTH (h::lx)) (LENGTH [])) (LENGTH lz)
             = MIN 0 (LENGTH lz) = 0 = LHS        by MIN_DEF
      Otherwise, ly = h'::t.
      If lz = [],
         LHS = LENGTH (MAP3 f (h::lx) (h'::t) []) = 0  by MAP3, LENGTH
         RHS = MIN (MIN (LENGTH (h::lx)) (LENGTH (h'::t))) (LENGTH [])
             = 0 = LHS                                 by MIN_DEF
      Otherwise, lz = h''::t'.
         LHS = LENGTH (MAP3 f (h::lx) (h'::t) (h''::t'))
             = LENGTH (f h' h''::MAP3 lx t t'')        by MAP3
             = SUC (LENGTH MAP3 lx t t'')              by LENGTH
             = SUC (MIN (MIN (LENGTH lx) (LENGTH t)) (LENGTH t''))   by induction hypothesis
         RHS = MIN (MIN (LENGTH (h::lx)) (LENGTH (h'::t))) (LENGTH (h''::t'))
             = MIN (MIN (SUC (LENGTH lx)) (SUC (LENGTH t))) (SUC (LENGTH t'))  by LENGTH
             = MIN (SUC (MIN (LENGTH lx) (LENGTH t))) (SUC (LESS_TWICE t'))    by MIN_DEF
             = SUC (MIN (MIN (LENGTH lx) (LENGTH t)) (LENGTH t'')) = LHS       by MIN_DEF
*)
val LENGTH_MAP3 = store_thm(
  "LENGTH_MAP3",
  ``!lx ly lz f. LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz)``,
  Induct_on `lx` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `lz` >-
  rw[] >>
  rw[MIN_DEF]);

(*
EL_MAP   |- !n l. n < LENGTH l ==> !f. EL n (MAP f l) = f (EL n l)
EL_MAP2  |- !ts tt n. n < MIN (LENGTH ts) (LENGTH tt) ==> (EL n (MAP2 f ts tt) = f (EL n ts) (EL n tt))
*)

(* Theorem: n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
           !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz) *)
(* Proof:
   By induction on n.
   Base: !lx ly lz. 0 < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
         !f. EL 0 (MAP3 f lx ly lz) = f (EL 0 lx) (EL 0 ly) (EL 0 lz)
      Note ?x tx. lx = x::tx             by LENGTH_EQ_0, list_CASES
       and ?y ty. ly = y::ty             by LENGTH_EQ_0, list_CASES
       and ?z tz. lz = z::tz             by LENGTH_EQ_0, list_CASES
          EL 0 (MAP3 f lx ly lz)
        = EL 0 (MAP3 f (x::lx) (y::ty) (z::tz))
        = EL 0 (f x y z::MAP3 f tx ty tz)    by MAP3
        = f x y z                            by EL
        = f (EL 0 lx) (EL 0 ly) (EL 0 lz)    by EL
   Step: !lx ly lz. n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
             !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz) ==>
         !lx ly lz. SUC n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
             !f. EL (SUC n) (MAP3 f lx ly lz) = f (EL (SUC n) lx) (EL (SUC n) ly) (EL (SUC n) lz)
      Note ?x tx. lx = x::tx             by LENGTH_EQ_0, list_CASES
       and ?y ty. ly = y::ty             by LENGTH_EQ_0, list_CASES
       and ?z tz. lz = z::tz             by LENGTH_EQ_0, list_CASES
      Also n < LENGTH tx /\ n < LENGTH ty /\ n < LENGTH tz    by LENGTH
      Thus n < MIN (MIN (LENGTH tx) (LENGTH ty)) (LENGTH tz)  by MIN_DEF
          EL (SUC n) (MAP3 f lx ly lz)
        = EL (SUC n) (MAP3 f (x::lx) (y::ty) (z::tz))
        = EL (SUC n) (f x y z::MAP3 f tx ty tz)    by MAP3
        = EL n (MAP3 f tx ty tz)                   by EL
        = f (EL n tx) (EL n ty) (EL n tz)          by induction hypothesis
        = f (EL (SUC n) lx) (EL (SUC n) ly) (EL (SUC n) lz)
                                                   by EL
*)
val EL_MAP3 = store_thm(
  "EL_MAP3",
  ``!lx ly lz n. n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
   !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz)``,
  Induct_on `n` >| [
    rw[] >>
    `?x tx. lx = x::tx` by metis_tac[LENGTH_EQ_0, list_CASES, NOT_ZERO_LT_ZERO] >>
    `?y ty. ly = y::ty` by metis_tac[LENGTH_EQ_0, list_CASES, NOT_ZERO_LT_ZERO] >>
    `?z tz. lz = z::tz` by metis_tac[LENGTH_EQ_0, list_CASES, NOT_ZERO_LT_ZERO] >>
    rw[],
    rw[] >>
    `!a. SUC n < a ==> a <> 0` by decide_tac >>
    `?x tx. lx = x::tx` by metis_tac[LENGTH_EQ_0, list_CASES] >>
    `?y ty. ly = y::ty` by metis_tac[LENGTH_EQ_0, list_CASES] >>
    `?z tz. lz = z::tz` by metis_tac[LENGTH_EQ_0, list_CASES] >>
    `n < LENGTH tx /\ n < LENGTH ty /\ n < LENGTH tz` by fs[] >>
    rw[]
  ]);

(*
MEM_MAP  |- !l f x. MEM x (MAP f l) <=> ?y. x = f y /\ MEM y l
*)

(* Theorem: MEM x (MAP2 f l1 l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2 *)
(* Proof:
   By induction on l1.
   Base: !l2. MEM x (MAP2 f [] l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 [] /\ MEM y2 l2
      Note MAP2 f [] l2 = []         by MAP2_DEF
       and MEM x [] = F, hence true  by MEM
   Step: !l2. MEM x (MAP2 f l1 l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2 ==>
         !h l2. MEM x (MAP2 f (h::l1) l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 (h::l1) /\ MEM y2 l2
      If l2 = [],
         Then MEM x (MAP2 f (h::l1) []) = F, hence true    by MEM
      Otherwise, l2 = h'::t,
         to show: MEM x (MAP2 f (h::l1) (h'::t)) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 (h::l1) /\ MEM y2 (h'::t)
         Note MAP2 f (h::l1) (h'::t)
            = (f h h')::MAP2 f l1 t                      by MAP2
         Thus x = f h h'  or MEM x (MAP2 f l1 t)         by MEM
         If x = f h h',
            Take y1 = h, y2 = h', and the result follows by MEM
         If MEM x (MAP2 f l1 t)
            Then ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 t   by induction hypothesis
            Take this y1 and y2, the result follows      by MEM
*)
val MEM_MAP2 = store_thm(
  "MEM_MAP2",
  ``!f x l1 l2. MEM x (MAP2 f l1 l2) ==> ?y1 y2. (x = f y1 y2) /\ MEM y1 l1 /\ MEM y2 l2``,
  ntac 2 strip_tac >>
  Induct_on `l1` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l2` >-
  fs[] >>
  fs[] >-
  metis_tac[] >>
  metis_tac[MEM]);

(* Theorem: MEM x (MAP3 f l1 l2 l3) ==> ?y1 y2 y3. (x = f y1 y2 y3) /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3 *)
(* Proof:
   By induction on l1.
   Base: !l2 l3. MEM x (MAP3 f [] l2 l3) ==> ...
      Note MAP3 f [] l2 l3 = [], and MEM x [] = F, hence true.
   Step: !l2 l3. MEM x (MAP3 f l1 l2 l3) ==>
                 ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3 ==>
         !h l2 l3. MEM x (MAP3 f (h::l1) l2 l3) ==>
                 ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 (h::l1) /\ MEM y2 l2 /\ MEM y3 l3
      If l2 = [],
         Then MEM x (MAP3 f (h::l1) [] l3) = MEM x [] = F, hence true   by MAP3_DEF
      Otherwise, l2 = h'::t,
         to show: MEM x (MAP3 f (h::l1) (h'::t) l3) ==>
                  ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 (h::l1) /\ MEM y2 (h'::t) /\ MEM y3 l3
         If l3 = [],
            Then MEM x (MAP3 f (h::l1) l2 []) = MEM x [] = F, hence true   by MAP3_DEF
         Otherwise, l3 = h''::t',
            to show: MEM x (MAP3 f (h::l1) (h'::t) (h''::t')) ==>
                     ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 (h::l1) /\ MEM y2 (h'::t) /\ MEM y3 (h''::t')

         Note MAP3 f (h::l1) (h'::t) (h''::t')
            = (f h h' h'')::MAP3 f l1 t t'              by MAP3
         Thus x = f h h' h''  or MEM x (MAP3 f l1 t t') by MEM
         If x = f h h' h'',
            Take y1 = h, y2 = h', y3 = h'' and the result follows by MEM
         If MEM x (MAP3 f l1 t t')
            Then ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 t /\ MEM y2 l2 /\ MEM y3 t'
                                                         by induction hypothesis
            Take this y1, y2 and y3, the result follows  by MEM
*)
val MEM_MAP3 = store_thm(
  "MEM_MAP3",
  ``!f x l1 l2 l3. MEM x (MAP3 f l1 l2 l3) ==>
   ?y1 y2 y3. (x = f y1 y2 y3) /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3``,
  ntac 2 strip_tac >>
  Induct_on `l1` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l2` >-
  fs[] >>
  Cases_on `l3` >-
  fs[] >>
  fs[] >-
  metis_tac[] >>
  metis_tac[MEM]);

(* Theorem: SUM (MAP (K c) ls) = c * LENGTH ls *)
(* Proof:
   By induction on ls.
   Base: !c. SUM (MAP (K c) []) = c * LENGTH []
      LHS = SUM (MAP (K c) [])
          = SUM [] = 0             by MAP, SUM
      RHS = c * LENGTH []
          = c * 0 = 0 = LHS        by LENGTH
   Step: !c. SUM (MAP (K c) ls) = c * LENGTH ls ==>
         !h c. SUM (MAP (K c) (h::ls)) = c * LENGTH (h::ls)
        SUM (MAP (K c) (h::ls))
      = SUM (c :: MAP (K c) ls)    by MAP
      = c + SUM (MAP (K c) ls)     by SUM
      = c + c * LENGTH ls          by induction hypothesis
      = c * (1 + LENGTH ls)        by RIGHT_ADD_DISTRIB
      = c * (SUC (LENGTH ls))      by ADD1
      = c * LENGTH (h::ls)         by LENGTH
*)
val SUM_MAP_K = store_thm(
  "SUM_MAP_K",
  ``!ls c. SUM (MAP (K c) ls) = c * LENGTH ls``,
  Induct >-
  rw[] >>
  rw[ADD1]);

(* Theorem: a <= b ==> SUM (MAP (K a) ls) <= SUM (MAP (K b) ls) *)
(* Proof:
      SUM (MAP (K a) ls)
    = a * LENGTH ls             by SUM_MAP_K
   <= b * LENGTH ls             by a <= b
    = SUM (MAP (K b) ls)        by SUM_MAP_K
*)
val SUM_MAP_K_LE = store_thm(
  "SUM_MAP_K_LE",
  ``!ls a b. a <= b ==> SUM (MAP (K a) ls) <= SUM (MAP (K b) ls)``,
  rw[SUM_MAP_K]);

(* Theorem: SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly) *)
(* Proof:
   By induction on lx.
   Base: !ly c. SUM (MAP2 (\x y. c) [] ly) = c * LENGTH (MAP2 (\x y. c) [] ly)
      LHS = SUM (MAP2 (\x y. c) [] ly)
          = SUM [] = 0             by MAP2_DEF, SUM
      RHS = c * LENGTH (MAP2 (\x y. c) [] ly)
          = c * 0 = 0 = LHS        by MAP2_DEF, LENGTH
   Step: !ly c. SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly) ==>
         !h ly c. SUM (MAP2 (\x y. c) (h::lx) ly) = c * LENGTH (MAP2 (\x y. c) (h::lx) ly)
      If ly = [],
         to show: SUM (MAP2 (\x y. c) (h::lx) []) = c * LENGTH (MAP2 (\x y. c) (h::lx) [])
         LHS = SUM (MAP2 (\x y. c) (h::lx) [])
             = SUM [] = 0          by MAP2_DEF, SUM
         RHS = c * LENGTH (MAP2 (\x y. c) (h::lx) [])
             = c * 0 = 0 = LHS     by MAP2_DEF, LENGTH
      Otherwise, ly = h'::t,
        to show: SUM (MAP2 (\x y. c) (h::lx) (h'::t)) = c * LENGTH (MAP2 (\x y. c) (h::lx) (h'::t))

           SUM (MAP2 (\x y. c) (h::lx) (h'::t))
         = SUM (c :: MAP2 (\x y. c) lx t)               by MAP2_DEF
         = c + SUM (MAP2 (\x y. c) lx t)                by SUM
         = c + c * LENGTH (MAP2 (\x y. c) lx t)         by induction hypothesis
         = c * (1 + LENGTH (MAP2 (\x y. c) lx t)        by RIGHT_ADD_DISTRIB
         = c * (SUC (LENGTH (MAP2 (\x y. c) lx t))      by ADD1
         = c * LENGTH (MAP2 (\x y. c) (h::lx) (h'::t))  by LENGTH
*)
val SUM_MAP2_K = store_thm(
  "SUM_MAP2_K",
  ``!lx ly c. SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  rw[ADD1, MIN_DEF]);

(* Theorem: SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz) *)
(* Proof:
   By induction on lx.
   Base: !ly lz c. SUM (MAP3 (\x y z. c) [] ly lz) = c * LENGTH (MAP3 (\x y z. c) [] ly lz)
      LHS = SUM (MAP3 (\x y z. c) [] ly lz)
          = SUM [] = 0             by MAP3_DEF, SUM
      RHS = c * LENGTH (MAP3 (\x y z. c) [] ly lz)
          = c * 0 = 0 = LHS        by MAP3_DEF, LENGTH
   Step: !ly lz c. SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz) ==>
         !h ly lz c. SUM (MAP3 (\x y z. c) (h::lx) ly lz) = c * LENGTH (MAP3 (\x y z. c) (h::lx) ly lz)
      If ly = [],
         to show: SUM (MAP3 (\x y z. c) (h::lx) [] lz) = c * LENGTH (MAP3 (\x y z. c) (h::lx) [] lz)
         LHS = SUM (MAP3 (\x y z. c) (h::lx) [] lz)
             = SUM [] = 0          by MAP3_DEF, SUM
         RHS = c * LENGTH (MAP3 (\x y z. c) (h::lx) [] lz)
             = c * 0 = 0 = LHS     by MAP3_DEF, LENGTH
      Otherwise, ly = h'::t,
        to show: SUM (MAP3 (\x y z. c) (h::lx) (h'::t) lz) = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) lz)
        If lz = [],
           to show: SUM (MAP3 (\x y z. c) (h::lx) (h'::t) []) = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) [])
           LHS = SUM (MAP3 (\x y z. c) (h::lx) (h'::t) [])
               = SUM [] = 0                  by MAP3_DEF, SUM
           RHS = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) [])
               = c * 0 = 0                   by MAP3_DEF, LENGTH
        Otherwise, lz = h''::t',
           to show: SUM (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t')) = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t'))
              SUM (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t'))
            = SUM (c :: MAP3 (\x y z. c) lx t t')                      by MAP3_DEF
            = c + SUM (MAP3 (\x y z. c) lx t t')                       by SUM
            = c + c * LENGTH (MAP3 (\x y z. c) lx t t')                by induction hypothesis
            = c * (1 + LENGTH (MAP3 (\x y z. c) lx t t')               by RIGHT_ADD_DISTRIB
            = c * (SUC (LENGTH (MAP3 (\x y z. c) lx t t'))             by ADD1
            = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t'))  by LENGTH
*)
val SUM_MAP3_K = store_thm(
  "SUM_MAP3_K",
  ``!lx ly lz c. SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `lz` >-
  rw[] >>
  rw[ADD1]);

(* ------------------------------------------------------------------------- *)
(* Bounds on Lists                                                           *)
(* ------------------------------------------------------------------------- *)

(* Overload non-decreasing functions with different arity. *)
val _ = overload_on("MONO", ``\f:num -> num. !x y. x <= y ==> f x <= f y``);
val _ = overload_on("MONO2", ``\f:num -> num -> num. !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x1 y1 <= f x2 y2``);
val _ = overload_on("MONO3", ``\f:num -> num -> num -> num. !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==> f x1 y1 z1 <= f x2 y2 z2``);

(* Overload non-increasing functions with different arity. *)
val _ = overload_on("RMONO", ``\f:num -> num. !x y. x <= y ==> f y <= f x``);
val _ = overload_on("RMONO2", ``\f:num -> num -> num. !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x2 y2 <= f x1 y1``);
val _ = overload_on("RMONO3", ``\f:num -> num -> num -> num. !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==> f x2 y2 z2 <= f x1 y1 z1``);


(* Theorem: SUM ls <= (MAX_LIST ls) * LENGTH ls *)
(* Proof:
   By induction on ls.
   Base: SUM [] <= MAX_LIST [] * LENGTH []
      LHS = SUM [] = 0          by SUM
      RHS = MAX_LIST [] * LENGTH []
          = 0 * 0 = 0           by MAX_LIST, LENGTH
      Hence true.
   Step: SUM ls <= MAX_LIST ls * LENGTH ls ==>
         !h. SUM (h::ls) <= MAX_LIST (h::ls) * LENGTH (h::ls)
        SUM (h::ls)
      = h + SUM ls                                       by SUM
     <= h + MAX_LIST ls * LENGTH ls                      by induction hypothesis
     <= MAX_LIST (h::ls) + MAX_LIST ls * LENGTH ls       by MAX_LIST_PROPERTY
     <= MAX_LIST (h::ls) + MAX_LIST (h::ls) * LENGTH ls  by MAX_LIST_LE
      = MAX_LIST (h::ls) * (1 + LENGTH ls)               by LEFT_ADD_DISTRIB
      = MAX_LIST (h::ls) * LENGTH (h::ls)                by LENGTH
*)
val SUM_UPPER = store_thm(
  "SUM_UPPER",
  ``!ls. SUM ls <= (MAX_LIST ls) * LENGTH ls``,
  Induct_on `ls` >-
  rw[] >>
  strip_tac >>
  `SUM (h::ls) <= h + MAX_LIST ls * LENGTH ls` by rw[] >>
  `h + MAX_LIST ls * LENGTH ls <= MAX_LIST (h::ls) + MAX_LIST ls * LENGTH ls` by rw[] >>
  `MAX_LIST (h::ls) + MAX_LIST ls * LENGTH ls <= MAX_LIST (h::ls) + MAX_LIST (h::ls) * LENGTH ls` by rw[] >>
  `MAX_LIST (h::ls) + MAX_LIST (h::ls) * LENGTH ls = MAX_LIST (h::ls) * (1 + LENGTH ls)` by rw[] >>
  `_ = MAX_LIST (h::ls) * LENGTH (h::ls)` by rw[] >>
  decide_tac);

(* Theorem: (MIN_LIST ls) * LENGTH ls <= SUM ls *)
(* Proof:
   By induction on ls.
   Base: MIN_LIST [] * LENGTH [] <= SUM []
      LHS = (MIN_LIST []) * LENGTH [] = 0     by LENGTH
      RHS = SUM [] = 0                        by SUM
      Hence true.
   Step: MIN_LIST ls * LENGTH ls <= SUM ls ==>
         !h. MIN_LIST (h::ls) * LENGTH (h::ls) <= SUM (h::ls)
      If ls = [],
         LHS = (MIN_LIST [h]) * LENGTH [h]
             = h * 1 = h             by MIN_LIST_def, LENGTH
         RHS = SUM [h] = h           by SUM
         Hence true.
      If ls <> [],
          MIN_LIST (h::ls) * LENGTH (h::ls)
        = (MIN h (MIN_LIST ls)) * (1 + LENGTH ls)   by MIN_LIST_def, LENGTH
        = (MIN h (MIN_LIST ls)) + (MIN h (MIN_LIST ls)) * LENGTH ls
                                                    by RIGHT_ADD_DISTRIB
       <= h + (MIN_LIST ls) * LENGTH ls             by MIN_IS_MIN
       <= h + SUM ls                                by induction hypothesis
        = SUM (h::ls)                               by SUM
*)
val SUM_LOWER = store_thm(
  "SUM_LOWER",
  ``!ls. (MIN_LIST ls) * LENGTH ls <= SUM ls``,
  Induct_on `ls` >-
  rw[] >>
  strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `MIN_LIST (h::ls) * LENGTH (h::ls) = (MIN h (MIN_LIST ls)) * (1 + LENGTH ls)` by rw[] >>
  `_ = (MIN h (MIN_LIST ls)) + (MIN h (MIN_LIST ls)) * LENGTH ls` by rw[] >>
  `(MIN h (MIN_LIST ls)) <= h` by rw[] >>
  `(MIN h (MIN_LIST ls)) * LENGTH ls <= (MIN_LIST ls) * LENGTH ls` by rw[] >>
  rw[]);

(* Theorem: EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: EVERY (\x. f x <= g x) [] ==> SUM (MAP f []) <= SUM (MAP g [])
         EVERY (\x. f x <= g x) [] = T    by EVERY_DEF
           SUM (MAP f [])
         = SUM []                         by MAP
         = SUM (MAP g [])                 by MAP
   Step: EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls) ==>
         !h. EVERY (\x. f x <= g x) (h::ls) ==> SUM (MAP f (h::ls)) <= SUM (MAP g (h::ls))
         Note f h <= g h /\
              EVERY (\x. f x <= g x) ls   by EVERY_DEF
           SUM (MAP f (h::ls))
         = SUM (f h :: MAP f ls)          by MAP
         = f h + SUM (MAP f ls)           by SUM
        <= g h + SUM (MAP g ls)           by above, induction hypothesis
         = SUM (g h :: MAP g ls)          by SUM
         = SUM (MAP g (h::ls))            by MAP
*)
val SUM_MAP_LE = store_thm(
  "SUM_MAP_LE",
  ``!f g ls. EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >>
  rw[] >>
  rw[] >>
  fs[]);

(* Theorem: EVERY (\x. f x < g x) ls /\ ls <> [] ==> SUM (MAP f ls) < SUM (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: EVERY (\x. f x <= g x) [] /\ [] <> [] ==> SUM (MAP f []) <= SUM (MAP g [])
         True since [] <> [] = F.
   Step: EVERY (\x. f x <= g x) ls ==> ls <> [] ==> SUM (MAP f ls) <= SUM (MAP g ls) ==>
         !h. EVERY (\x. f x <= g x) (h::ls) ==> h::ls <> [] ==> SUM (MAP f (h::ls)) <= SUM (MAP g (h::ls))
         Note f h < g h /\
              EVERY (\x. f x < g x) ls    by EVERY_DEF

         If ls = [],
           SUM (MAP f [h])
         = SUM (f h)          by MAP
         = f h                by SUM
         < g h                by above
         = SUM (g h)          by SUM
         = SUM (MAP g [h])    by MAP

         If ls <> [],
           SUM (MAP f (h::ls))
         = SUM (f h :: MAP f ls)          by MAP
         = f h + SUM (MAP f ls)           by SUM
         < g h + SUM (MAP g ls)           by induction hypothesis
         = SUM (g h :: MAP g ls)          by SUM
         = SUM (MAP g (h::ls))            by MAP
*)
val SUM_MAP_LT = store_thm(
  "SUM_MAP_LT",
  ``!f g ls. EVERY (\x. f x < g x) ls /\ ls <> [] ==> SUM (MAP f ls) < SUM (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >>
  rw[] >>
  rw[] >>
  (Cases_on `ls = []` >> fs[]));

(*
MAX_LIST_PROPERTY  |- !l x. MEM x l ==> x <= MAX_LIST l
MIN_LIST_PROPERTY  |- !l. l <> [] ==> !x. MEM x l ==> MIN_LIST l <= x
*)

(* Theorem: MONO f  ==> !ls e. MEM e (MAP f ls) ==> e <= f (MAX_LIST ls) *)
(* Proof:
   Note ?y. (e = f y) /\ MEM y ls    by MEM_MAP
    and   y <= MAX_LIST ls           by MAX_LIST_PROPERTY
   Thus f y <= f (MAX_LIST ls)       by given
     or   e <= f (MAX_LIST ls)       by e = f y
*)
val MEM_MAP_UPPER = store_thm(
  "MEM_MAP_UPPER",
  ``!f. MONO f ==> !ls e. MEM e (MAP f ls) ==> e <= f (MAX_LIST ls)``,
  rpt strip_tac >>
  `?y. (e = f y) /\ MEM y ls` by rw[GSYM MEM_MAP] >>
  `y <= MAX_LIST ls` by rw[MAX_LIST_PROPERTY] >>
  rw[]);

(* Theorem: MONO2 f ==> !lx ly e. MEM e (MAP2 f lx ly) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) *)
(* Proof:
   Note ?ex ey. (e = f ex ey) /\
                MEM ex lx /\ MEM ey ly    by MEM_MAP2
    and ex <= MAX_LIST lx                 by MAX_LIST_PROPERTY
    and ey <= MAX_LIST ly                 by MAX_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP2_UPPER = store_thm(
  "MEM_MAP2_UPPER",
  ``!f. MONO2 f ==> !lx ly e. MEM e (MAP2 f lx ly) ==> e <= f (MAX_LIST lx) (MAX_LIST ly)``,
  metis_tac[MEM_MAP2, MAX_LIST_PROPERTY]);

(* Theorem: MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) *)
(* Proof:
   Note ?ex ey ez. (e = f ex ey ez) /\
                   MEM ex lx /\ MEM ey ly /\ MEM ez lz  by MEM_MAP3
    and ex <= MAX_LIST lx                 by MAX_LIST_PROPERTY
    and ey <= MAX_LIST ly                 by MAX_LIST_PROPERTY
    and ez <= MAX_LIST lz                 by MAX_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP3_UPPER = store_thm(
  "MEM_MAP3_UPPER",
  ``!f. MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz)``,
  metis_tac[MEM_MAP3, MAX_LIST_PROPERTY]);

(* Theorem: MONO f ==> !ls e. MEM e (MAP f ls) ==> f (MIN_LIST ls) <= e *)
(* Proof:
   Note ?y. (e = f y) /\ MEM y ls    by MEM_MAP
    and ls <> []                     by MEM, MEM y ls
   then     MIN_LIST ls <= y         by MIN_LIST_PROPERTY, ls <> []
   Thus f (MIN_LIST ls) <= f y       by given
     or f (MIN_LIST ls) <= e         by e = f y
*)
val MEM_MAP_LOWER = store_thm(
  "MEM_MAP_LOWER",
  ``!f. MONO f ==> !ls e. MEM e (MAP f ls) ==> f (MIN_LIST ls) <= e``,
  rpt strip_tac >>
  `?y. (e = f y) /\ MEM y ls` by rw[GSYM MEM_MAP] >>
  `ls <> []` by metis_tac[MEM] >>
  `MIN_LIST ls <= y` by rw[MIN_LIST_PROPERTY] >>
  rw[]);

(* Theorem: MONO2 f ==>
            !lx ly e. MEM e (MAP2 f lx ly) ==> f (MIN_LIST lx) (MIN_LIST ly) <= e *)
(* Proof:
   Note ?ex ey. (e = f ex ey) /\
                MEM ex lx /\ MEM ey ly   by MEM_MAP2
    and lx <> [] /\ ly <> []             by MEM
    and MIN_LIST lx <= ex                by MIN_LIST_PROPERTY
    and MIN_LIST ly <= ey                by MIN_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP2_LOWER = store_thm(
  "MEM_MAP2_LOWER",
  ``!f. MONO2 f ==>
   !lx ly e. MEM e (MAP2 f lx ly) ==> f (MIN_LIST lx) (MIN_LIST ly) <= e``,
  metis_tac[MEM_MAP2, MEM, MIN_LIST_PROPERTY]);

(* Theorem: MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> f (MIN_LIST lx) (MIN_LIST ly) (MIN_LIST lz) <= e *)
(* Proof:
   Note ?ex ey ez. (e = f ex ey ez) /\
                MEM ex lx /\ MEM ey ly /\ MEM ez lz  by MEM_MAP3
    and lx <> [] /\ ly <> [] /\ lz <> [] by MEM
    and MIN_LIST lx <= ex                by MIN_LIST_PROPERTY
    and MIN_LIST ly <= ey                by MIN_LIST_PROPERTY
    and MIN_LIST lz <= ez                by MIN_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP3_LOWER = store_thm(
  "MEM_MAP3_LOWER",
  ``!f. MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> f (MIN_LIST lx) (MIN_LIST ly) (MIN_LIST lz) <= e``,
  rpt strip_tac >>
  `?ex ey ez. (e = f ex ey ez) /\ MEM ex lx /\ MEM ey ly /\ MEM ez lz` by rw[MEM_MAP3] >>
  `lx <> [] /\ ly <> [] /\ lz <> []` by metis_tac[MEM] >>
  rw[MIN_LIST_PROPERTY]);

(* Theorem: (!x. f x <= g x) ==> !ls. MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: MAX_LIST (MAP f []) <= MAX_LIST (MAP g [])
      LHS = MAX_LIST (MAP f []) = MAX_LIST []    by MAP
      RHS = MAX_LIST (MAP g []) = MAX_LIST []    by MAP
      Hence true.
   Step: MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls) ==>
         !h. MAX_LIST (MAP f (h::ls)) <= MAX_LIST (MAP g (h::ls))
        MAX_LIST (MAP f (h::ls))
      = MAX_LIST (f h::MAP f ls)                 by MAP
      = MAX (f h) (MAX_LIST (MAP f ls))          by MAX_LIST_def
     <= MAX (f h) (MAX_LIST (MAP g ls))          by induction hypothesis
     <= MAX (g h) (MAX_LIST (MAP g ls))          by properties of f, g
      = MAX_LIST (g h::MAP g ls)                 by MAX_LIST_def
      = MAX_LIST (MAP g (h::ls))                 by MAP
*)
val MAX_LIST_MAP_LE = store_thm(
  "MAX_LIST_MAP_LE",
  ``!f g. (!x. f x <= g x) ==> !ls. MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rw[]);

(* Theorem: (!x. f x <= g x) ==> !ls. MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: MIN_LIST (MAP f []) <= MIN_LIST (MAP g [])
      LHS = MIN_LIST (MAP f []) = MIN_LIST []    by MAP
      RHS = MIN_LIST (MAP g []) = MIN_LIST []    by MAP
      Hence true.
   Step: MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls) ==>
         !h. MIN_LIST (MAP f (h::ls)) <= MIN_LIST (MAP g (h::ls))
      If ls = [],
        MIN_LIST (MAP f [h])
      = MIN_LIST [f h]                           by MAP
      = f h                                      by MIN_LIST_def
     <= g h                                      by properties of f, g
      = MIN_LIST [g h]                           by MIN_LIST_def
      = MIN_LIST (MAP g [h])                     by MAP
      Otherwise ls <> [],
        MIN_LIST (MAP f (h::ls))
      = MIN_LIST (f h::MAP f ls)                 by MAP
      = MIN (f h) (MIN_LIST (MAP f ls))          by MIN_LIST_def
     <= MIN (g h) (MIN_LIST (MAP g ls))          by MIN_LE_PAIR, induction hypothesis
      = MIN_LIST (g h::MAP g ls)                 by MIN_LIST_def
      = MIN_LIST (MAP g (h::ls))                 by MAP
*)
val MIN_LIST_MAP_LE = store_thm(
  "MIN_LIST_MAP_LE",
  ``!f g. (!x. f x <= g x) ==> !ls. MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[MIN_LIST_def] >>
  rw[MIN_LIST_def, MIN_LE_PAIR]);

(* Theorem: (!x. f x <= g x) ==> !ls n. EL n (MAP f ls) <= EL n (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: !n. EL n (MAP f []) <= EL n (MAP g [])
      LHS = EL n [] = RHS             by MAP
   Step: !n. EL n (MAP f ls) <= EL n (MAP g ls) ==>
         !h n. EL n (MAP f (h::ls)) <= EL n (MAP g (h::ls))
      If n = 0,
          EL 0 (MAP f (h::ls))
        = EL 0 (f h::MAP f ls)        by MAP
        = f h                         by EL
       <= g h                         by given
        = EL 0 (g h::MAP g ls)        by EL
        = EL 0 (MAP g (h::ls))        by MAP
      If n <> 0, then n = SUC k       by num_CASES
         EL n (MAP f (h::ls))
       = EL (SUC k) (f h::MAP f ls)   by MAP
       = EL k (MAP f ls)              by EL
      <= EL k (MAP g ls)              by induction hypothesis
       = EL (SUC k) (g h::MAP g ls)   by EL
       = EL n (MAP g (h::ls))         by MAP
*)
val MAP_LE = store_thm(
  "MAP_LE",
  ``!(f:num -> num) g. (!x. f x <= g x) ==> !ls n. EL n (MAP f ls) <= EL n (MAP g ls)``,
  ntac 3 strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  Cases_on `n` >-
  rw[] >>
  rw[]);

(* Theorem: (!x y. f x y <= g x y) ==> !lx ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly) *)
(* Proof:
   By induction on lx.
   Base: !ly n. EL n (MAP2 f [] ly) <= EL n (MAP2 g [] ly)
      LHS = EL n [] = RHS             by MAP2_DEF
   Step: !ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly) ==>
         !h ly n. EL n (MAP2 f (h::lx) ly) <= EL n (MAP2 g (h::lx) ly)
      If ly = [],
         to show: EL n (MAP2 f (h::lx) []) <= EL n (MAP2 g (h::lx) [])
         True since LHS = EL n [] = RHS         by MAP2_DEF
      Otherwise, ly = h'::t.
         to show: EL n (MAP2 f (h::lx) (h'::t)) <= EL n (MAP2 g (h::lx) (h'::t))
         If n = 0,
             EL 0 (MAP2 f (h::lx) (h'::t))
           = EL 0 (f h h'::MAP2 f lx t)        by MAP2
           = f h h'                            by EL
          <= g h h'                            by given
           = EL 0 (g h h'::MAP2 g lx t)        by EL
           = EL 0 (MAP2 g (h::lx) (h'::t))     by MAP2
         If n <> 0, then n = SUC k             by num_CASES
            EL n (MAP2 f (h::lx) (h'::t))
          = EL (SUC k) (f h h'::MAP2 f lx t)   by MAP2
          = EL k (MAP2 f lx t)                 by EL
         <= EL k (MAP2 g lx t)                 by induction hypothesis
          = EL (SUC k) (g h h'::MAP2 g lx t)   by EL
          = EL n (MAP2 g (h::lx) (h'::t))      by MAP2
*)
val MAP2_LE = store_thm(
  "MAP2_LE",
  ``!(f:num -> num -> num) g. (!x y. f x y <= g x y) ==>
   !lx ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly)``,
  ntac 3 strip_tac >>
  Induct_on `lx` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `n` >-
  rw[] >>
  rw[]);

(* Theorem: (!x y z. f x y z <= g x y z) ==>
            !lx ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz) *)
(* Proof:
   By induction on lx.
   Base: !ly lz n. EL n (MAP3 f [] ly lz) <= EL n (MAP3 g [] ly lz)
      LHS = EL n [] = RHS             by MAP3_DEF
   Step: !ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz) ==>
         !h ly lz n. EL n (MAP3 f (h::lx) ly lz) <= EL n (MAP3 g (h::lx) ly lz)
      If ly = [],
         to show: EL n (MAP3 f (h::lx) [] lz) <= EL n (MAP3 g (h::lx) [] lz)
         True since LHS = EL n [] = RHS          by MAP3_DEF
      Otherwise, ly = h'::t.
         to show: EL n (MAP3 f (h::lx) (h'::t) lz) <= EL n (MAP3 g (h::lx) (h'::t) lz)
         If lz = [],
            to show: EL n (MAP3 f (h::lx) (h'::t) []) <= EL n (MAP3 g (h::lx) (h'::t) [])
            True since LHS = EL n [] = RHS       by MAP3_DEF
         Otherwise, lz = h''::t'.
            to show: EL n (MAP3 f (h::lx) (h'::t) (h''::t')) <= EL n (MAP3 g (h::lx) (h'::t) (h''::t'))
            If n = 0,
                EL 0 (MAP3 f (h::lx) (h'::t) (h''::t'))
              = EL 0 (f h h' h''::MAP3 f lx t t')        by MAP3
              = f h h' h''                               by EL
             <= g h h' h''                               by given
              = EL 0 (g h h' h''::MAP3 g lx t t')        by EL
              = EL 0 (MAP3 g (h::lx) (h'::t) (h''::t'))  by MAP3
            If n <> 0, then n = SUC k                    by num_CASES
               EL n (MAP3 f (h::lx) (h'::t) (h''::t'))
             = EL (SUC k) (f h h' h''::MAP3 f lx t t')   by MAP3
             = EL k (MAP3 f lx t t')                     by EL
            <= EL k (MAP3 g lx t t')                     by induction hypothesis
             = EL (SUC k) (g h h' h''::MAP3 g lx t t')   by EL
             = EL n (MAP3 g (h::lx) (h'::t) (h''::t'))   by MAP3
*)
val MAP3_LE = store_thm(
  "MAP3_LE",
  ``!(f:num -> num -> num -> num) g. (!x y z. f x y z <= g x y z) ==>
   !lx ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz)``,
  ntac 3 strip_tac >>
  Induct_on `lx` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `lz` >-
  rw[] >>
  Cases_on `n` >-
  rw[] >>
  rw[]);

(*
SUM_MAP_PLUS       |- !f g ls. SUM (MAP (\x. f x + g x) ls) = SUM (MAP f ls) + SUM (MAP g ls)
SUM_MAP_PLUS_ZIP   |- !ls1 ls2. LENGTH ls1 = LENGTH ls2 /\ (!x y. f (x,y) = g x + h y) ==>
                                SUM (MAP f (ZIP (ls1,ls2))) = SUM (MAP g ls1) + SUM (MAP h ls2)
*)

(* Theorem: (!x. f1 x <= f2 x) ==> !ls. SUM (MAP f1 ls) <= SUM (MAP f2 ls) *)
(* Proof:
   By SUM_LE, this is to show:
   (1) !k. k < LENGTH (MAP f1 ls) ==> EL k (MAP f1 ls) <= EL k (MAP f2 ls)
       This is true                by EL_MAP
   (2) LENGTH (MAP f1 ls) = LENGTH (MAP f2 ls)
       This is true                by LENGTH_MAP
*)
val SUM_MONO_MAP = store_thm(
  "SUM_MONO_MAP",
  ``!f1 f2. (!x. f1 x <= f2 x) ==> !ls. SUM (MAP f1 ls) <= SUM (MAP f2 ls)``,
  rpt strip_tac >>
  irule SUM_LE >>
  rw[EL_MAP]);

(* Theorem: (!x y. f1 x y <= f2 x y) ==> !lx ly. SUM (MAP2 f1 lx ly) <= SUM (MAP2 f2 lx ly) *)
(* Proof:
   By SUM_LE, this is to show:
   (1) !k. k < LENGTH (MAP2 f1 lx ly) ==> EL k (MAP2 f1 lx ly) <= EL k (MAP2 f2 lx ly)
       This is true                by EL_MAP2, LENGTH_MAP2
   (2) LENGTH (MAP2 f1 lx ly) = LENGTH (MAP2 f2 lx ly)
       This is true                by LENGTH_MAP2
*)
val SUM_MONO_MAP2 = store_thm(
  "SUM_MONO_MAP2",
  ``!f1 f2. (!x y. f1 x y <= f2 x y) ==> !lx ly. SUM (MAP2 f1 lx ly) <= SUM (MAP2 f2 lx ly)``,
  rpt strip_tac >>
  irule SUM_LE >>
  rw[EL_MAP2]);

(* Theorem: (!x y z. f1 x y z <= f2 x y z) ==> !lx ly lz. SUM (MAP3 f1 lx ly lz) <= SUM (MAP3 f2 lx ly lz) *)
(* Proof:
   By SUM_LE, this is to show:
   (1) !k. k < LENGTH (MAP3 f1 lx ly lz) ==> EL k (MAP3 f1 lx ly lz) <= EL k (MAP3 f2 lx ly lz)
       This is true                by EL_MAP3, LENGTH_MAP3
   (2)LENGTH (MAP3 f1 lx ly lz) = LENGTH (MAP3 f2 lx ly lz)
       This is true                by LENGTH_MAP3
*)
val SUM_MONO_MAP3 = store_thm(
  "SUM_MONO_MAP3",
  ``!f1 f2. (!x y z. f1 x y z <= f2 x y z) ==>
   !lx ly lz. SUM (MAP3 f1 lx ly lz) <= SUM (MAP3 f2 lx ly lz)``,
  rpt strip_tac >>
  irule SUM_LE >>
  rw[EL_MAP3, LENGTH_MAP3]);

(* Theorem: MONO f ==> !ls. SUM (MAP f ls) <= f (MAX_LIST ls) * LENGTH ls *)
(* Proof:
   Let c = f (MAX_LIST ls).

   Claim: SUM (MAP f ls) <= SUM (MAP (K c) ls)
   Proof: By SUM_LE, this is to show:
          (1) LENGTH (MAP f ls) = LENGTH (MAP (K c) ls)
              This is true                           by LENGTH_MAP
          (2) !k. k < LENGTH (MAP f ls) ==> EL k (MAP f ls) <= EL k (MAP (K c) ls)
              Note EL k (MAP f ls) = f (EL k ls)     by EL_MAP
               and EL k (MAP (K c) ls)
                 = (K c) (EL k ls)                   by EL_MAP
                 = c                                 by K_THM
               Now MEM (EL k ls) ls                  by EL_MEM
                so EL k ls <= MAX_LIST ls            by MAX_LIST_PROPERTY
              Thus f (EL k ls) <= c                  by property of f

   Note SUM (MAP (K c) ls) = c * LENGTH ls           by SUM_MAP_K
   Thus SUM (MAP f ls) <= c * LENGTH ls              by Claim
*)
val SUM_MAP_UPPER = store_thm(
  "SUM_MAP_UPPER",
  ``!f. MONO f ==> !ls. SUM (MAP f ls) <= f (MAX_LIST ls) * LENGTH ls``,
  rpt strip_tac >>
  qabbrev_tac `c = f (MAX_LIST ls)` >>
  `SUM (MAP f ls) <= SUM (MAP (K c) ls)` by
  ((irule SUM_LE >> rw[]) >>
  rw[EL_MAP, EL_MEM, MAX_LIST_PROPERTY, Abbr`c`]) >>
  `SUM (MAP (K c) ls) = c * LENGTH ls` by rw[SUM_MAP_K] >>
  decide_tac);

(* Theorem: MONO2 f ==>
            !lx ly. SUM (MAP2 f lx ly) <= (f (MAX_LIST lx) (MAX_LIST ly)) * LENGTH (MAP2 f lx ly) *)
(* Proof:
   Let c = f (MAX_LIST lx) (MAX_LIST ly).

   Claim: SUM (MAP2 f lx ly) <= SUM (MAP2 (\x y. c) lx ly)
   Proof: By SUM_LE, this is to show:
          (1) LENGTH (MAP2 f lx ly) = LENGTH (MAP2 (\x y. c) lx ly)
              This is true                           by LENGTH_MAP2
          (2) !k. k < LENGTH (MAP2 f lx ly) ==> EL k (MAP2 f lx ly) <= EL k (MAP2 (\x y. c) lx ly)
              Note EL k (MAP2 f lx ly)
                 = f (EL k lx) (EL k ly)             by EL_MAP2
               and EL k (MAP2 (\x y. c) lx ly)
                 = (\x y. c) (EL k lx) (EL k ly)     by EL_MAP2
                 = c                                 by function application
              Note k < LENGTH lx, k < LENGTH ly      by LENGTH_MAP2
               Now MEM (EL k lx) lx                  by EL_MEM
               and MEM (EL k ly) ly                  by EL_MEM
                so EL k lx <= MAX_LIST lx            by MAX_LIST_PROPERTY
               and EL k ly <= MAX_LIST ly            by MAX_LIST_PROPERTY
              Thus f (EL k lx) (EL k ly) <= c        by property of f

   Note SUM (MAP (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)  by SUM_MAP2_K
    and LENGTH (MAP2 (\x y. c) lx ly) = LENGTH (MAP2 f lx ly)          by LENGTH_MAP2
   Thus SUM (MAP f lx ly) <= c * LENGTH (MAP2 f lx ly)                 by Claim
*)
val SUM_MAP2_UPPER = store_thm(
  "SUM_MAP2_UPPER",
  ``!f. MONO2 f ==>
   !lx ly. SUM (MAP2 f lx ly) <= (f (MAX_LIST lx) (MAX_LIST ly)) * LENGTH (MAP2 f lx ly)``,
  rpt strip_tac >>
  qabbrev_tac `c = f (MAX_LIST lx) (MAX_LIST ly)` >>
  `SUM (MAP2 f lx ly) <= SUM (MAP2 (\x y. c) lx ly)` by
  ((irule SUM_LE >> rw[]) >>
  rw[EL_MAP2, EL_MEM, MAX_LIST_PROPERTY, Abbr`c`]) >>
  `SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)` by rw[SUM_MAP2_K, Abbr`c`] >>
  `c * LENGTH (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 f lx ly)` by rw[] >>
  decide_tac);

(* Theorem: MONO3 f ==>
           !lx ly lz. SUM (MAP3 f lx ly lz) <=
                      f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) * LENGTH (MAP3 f lx ly lz) *)
(* Proof:
   Let c = f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz).

   Claim: SUM (MAP3 f lx ly lz) <= SUM (MAP3 (\x y z. c) lx ly lz)
   Proof: By SUM_LE, this is to show:
          (1) LENGTH (MAP3 f lx ly lz) = LENGTH (MAP3 (\x y z. c) lx ly lz)
              This is true                           by LENGTH_MAP3
          (2) !k. k < LENGTH (MAP3 f lx ly lz) ==> EL k (MAP3 f lx ly lz) <= EL k (MAP3 (\x y z. c) lx ly lz)
              Note EL k (MAP3 f lx ly lz)
                 = f (EL k lx) (EL k ly) (EL k lz)   by EL_MAP3
               and EL k (MAP3 (\x y z. c) lx ly lz)
                 = (\x y z. c) (EL k lx) (EL k ly) (EL k lz)  by EL_MAP3
                 = c                                 by function application
              Note k < LENGTH lx, k < LENGTH ly, k < LENGTH lz
                                                     by LENGTH_MAP3
               Now MEM (EL k lx) lx                  by EL_MEM
               and MEM (EL k ly) ly                  by EL_MEM
               and MEM (EL k lz) lz                  by EL_MEM
                so EL k lx <= MAX_LIST lx            by MAX_LIST_PROPERTY
               and EL k ly <= MAX_LIST ly            by MAX_LIST_PROPERTY
               and EL k lz <= MAX_LIST lz            by MAX_LIST_PROPERTY
              Thus f (EL k lx) (EL k ly) (EL k lz) <= c  by property of f

   Note SUM (MAP (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)   by SUM_MAP3_K
    and LENGTH (MAP3 (\x y z. c) lx ly lz) = LENGTH (MAP3 f lx ly lz)             by LENGTH_MAP3
   Thus SUM (MAP f lx ly lz) <= c * LENGTH (MAP3 f lx ly lz)                      by Claim
*)
val SUM_MAP3_UPPER = store_thm(
  "SUM_MAP3_UPPER",
  ``!f. MONO3 f ==>
   !lx ly lz. SUM (MAP3 f lx ly lz) <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) * LENGTH (MAP3 f lx ly lz)``,
  rpt strip_tac >>
  qabbrev_tac `c = f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz)` >>
  `SUM (MAP3 f lx ly lz) <= SUM (MAP3 (\x y z. c) lx ly lz)` by
  (`LENGTH (MAP3 f lx ly lz) = LENGTH (MAP3 (\x y z. c) lx ly lz)` by rw[LENGTH_MAP3] >>
  (irule SUM_LE >> rw[]) >>
  fs[LENGTH_MAP3] >>
  rw[EL_MAP3, EL_MEM, MAX_LIST_PROPERTY, Abbr`c`]) >>
  `SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)` by rw[SUM_MAP3_K] >>
  `c * LENGTH (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 f lx ly lz)` by rw[LENGTH_MAP3] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Increasing and decreasing list bounds                                     *)
(* ------------------------------------------------------------------------- *)

(* Overload increasing list and decreasing list *)
val _ = overload_on("MONO_INC",
          ``\ls:num list. !m n. m <= n /\ n < LENGTH ls ==> EL m ls <= EL n ls``);
val _ = overload_on("MONO_DEC",
          ``\ls:num list. !m n. m <= n /\ n < LENGTH ls ==> EL n ls <= EL m ls``);

(* Theorem: MONO f ==> MONO_INC (GENLIST f n) *)
(* Proof:
   Let ls = GENLIST f n.
   Then LENGTH ls = n                 by LENGTH_GENLIST
    and !k. k < n ==> EL k ls = f k   by EL_GENLIST
   Thus MONO_INC ls
*)
val GENLIST_MONO_INC = store_thm(
  "GENLIST_MONO_INC",
  ``!f:num -> num n. MONO f ==> MONO_INC (GENLIST f n)``,
  rw[]);

(* Theorem: RMONO f ==> MONO_DEC (GENLIST f n) *)
(* Proof:
   Let ls = GENLIST f n.
   Then LENGTH ls = n                 by LENGTH_GENLIST
    and !k. k < n ==> EL k ls = f k   by EL_GENLIST
   Thus MONO_DEC ls
*)
val GENLIST_MONO_DEC = store_thm(
  "GENLIST_MONO_DEC",
  ``!f:num -> num n. RMONO f ==> MONO_DEC (GENLIST f n)``,
  rw[]);

(* Theorem: ls <> [] /\ (!m n. m <= n ==> EL m ls <= EL n ls) ==> (MAX_LIST ls = LAST ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_INC [] ==> MAX_LIST [] = LAST []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_INC ls ==> MAX_LIST ls = LAST ls ==>
         !h. h::ls <> [] /\ MONO_INC (h::ls) ==> MAX_LIST (h::ls) = LAST (h::ls)
       If ls = [],
         LHS = MAX_LIST [h] = h        by MAX_LIST_def
         RHS = LAST [h] = h = LHS      by LAST_DEF
       If ls <> [],
         Note h <= LAST ls             by LAST_EL_CONS, increasing property
          and MONO_INC ls            by EL, m <= n ==> SUC m <= SUC n
         MAX_LIST (h::ls)
       = MAX h (MAX_LIST ls)           by MAX_LIST_def
       = MAX h (LAST ls)               by induction hypothesis
       = LAST ls                       by MAX_DEF, h <= LAST ls
       = LAST (h::ls)                  by LAST_DEF
*)
val MAX_LIST_MONO_INC = store_thm(
  "MAX_LIST_MONO_INC",
  ``!ls. ls <> [] /\ MONO_INC ls ==> (MAX_LIST ls = LAST ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `h <= LAST ls` by
  (`LAST ls = EL (LENGTH ls) (h::ls)` by rw[LAST_EL_CONS] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `LENGTH ls < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= n``]) >>
  `MONO_INC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC m) (h::ls) <= EL (SUC n) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MAX_DEF, LAST_DEF]);

(* Theorem: ls <> [] /\ MONO_DEC ls ==> (MAX_LIST ls = HD ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_DEC [] ==> MAX_LIST [] = HD []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_DEC ls ==> MAX_LIST ls = HD ls ==>
         !h. h::ls <> [] /\ MONO_DEC (h::ls) ==> MAX_LIST (h::ls) = HD (h::ls)
       If ls = [],
         LHS = MAX_LIST [h] = h        by MAX_LIST_def
         RHS = HD [h] = h = LHS        by HD
       If ls <> [],
         Note HD ls <= h               by HD, decreasing property
          and MONO_DEC ls            by EL, m <= n ==> SUC m <= SUC n
         MAX_LIST (h::ls)
       = MAX h (MAX_LIST ls)           by MAX_LIST_def
       = MAX h (HD ls)                 by induction hypothesis
       = h                             by MAX_DEF, HD ls <= h
       = HD (h::ls)                    by HD
*)
val MAX_LIST_MONO_DEC = store_thm(
  "MAX_LIST_MONO_DEC",
  ``!ls. ls <> [] /\ MONO_DEC ls ==> (MAX_LIST ls = HD ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `HD ls <= h` by
  (`HD ls = EL 1 (h::ls)` by rw[] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `0 < LENGTH ls` by metis_tac[LENGTH_EQ_0, NOT_ZERO_LT_ZERO] >>
  `1 < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= 1``]) >>
  `MONO_DEC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC n) (h::ls) <= EL (SUC m) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MAX_DEF]);

(* Theorem: ls <> [] /\ MONO_INC ls ==> (MIN_LIST ls = HD ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_INC [] ==> MIN_LIST [] = HD []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_INC ls ==> MIN_LIST ls = HD ls ==>
         !h. h::ls <> [] /\ MONO_INC (h::ls) ==> MIN_LIST (h::ls) = HD (h::ls)
       If ls = [],
         LHS = MIN_LIST [h] = h        by MIN_LIST_def
         RHS = HD [h] = h = LHS        by HD
       If ls <> [],
         Note h <= HD ls               by HD, increasing property
          and MONO_INC ls            by EL, m <= n ==> SUC m <= SUC n
         MIN_LIST (h::ls)
       = MIN h (MIN_LIST ls)           by MIN_LIST_def
       = MIN h (HD ls)                 by induction hypothesis
       = h                             by MIN_DEF, h <= HD ls
       = HD (h::ls)                    by HD
*)
val MIN_LIST_MONO_INC = store_thm(
  "MIN_LIST_MONO_INC",
  ``!ls. ls <> [] /\ MONO_INC ls ==> (MIN_LIST ls = HD ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `h <= HD ls` by
  (`HD ls = EL 1 (h::ls)` by rw[] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `0 < LENGTH ls` by metis_tac[LENGTH_EQ_0, NOT_ZERO_LT_ZERO] >>
  `1 < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= 1``]) >>
  `MONO_INC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC m) (h::ls) <= EL (SUC n) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MIN_DEF]);

(* Theorem: ls <> [] /\ MONO_DEC ls ==> (MIN_LIST ls = LAST ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_DEC [] ==> MIN_LIST [] = LAST []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_DEC ls ==> MIN_LIST ls = LAST ls ==>
         !h. h::ls <> [] /\ MONO_DEC (h::ls) ==> MAX_LIST (h::ls) = LAST (h::ls)
       If ls = [],
         LHS = MIN_LIST [h] = h        by MIN_LIST_def
         RHS = LAST [h] = h = LHS      by LAST_DEF
       If ls <> [],
         Note LAST ls <= h             by LAST_EL_CONS, decreasing property
          and MONO_DEC ls            by EL, m <= n ==> SUC m <= SUC n
         MIN_LIST (h::ls)
       = MIN h (MIN_LIST ls)           by MIN_LIST_def
       = MIN h (LAST ls)               by induction hypothesis
       = LAST ls                       by MIN_DEF, LAST ls <= h
       = LAST (h::ls)                  by LAST_DEF
*)
val MIN_LIST_MONO_DEC = store_thm(
  "MIN_LIST_MONO_DEC",
  ``!ls. ls <> [] /\ MONO_DEC ls ==> (MIN_LIST ls = LAST ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `LAST ls <= h` by
  (`LAST ls = EL (LENGTH ls) (h::ls)` by rw[LAST_EL_CONS] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `LENGTH ls < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= n``]) >>
  `MONO_DEC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC n) (h::ls) <= EL (SUC m) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MIN_DEF, LAST_DEF]);

(* ------------------------------------------------------------------------- *)
(* List Dilation                                                             *)
(* ------------------------------------------------------------------------- *)

(*
Use the concept of dilating a list.

Let p = [1;2;3], that is, p = 1 + 2x + 3x^2.
Then q = peval p (x^3) is just q = 1 + 2(x^3) + 3(x^3)^2 = [1;0;0;2;0;0;3]

DILATE 3 [] = []
DILATE 3 (h::t) = [h;0;0] ++ MDILATE 3 t

val DILATE_3_DEF = Define`
   (DILATE_3 [] = []) /\
   (DILATE_3 (h::t) = [h;0;0] ++ (MDILATE_3 t))
`;
> EVAL ``DILATE_3 [1;2;3]``;
val it = |- MDILATE_3 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3; 0; 0]: thm

val DILATE_3_DEF = Define`
   (DILATE_3 [] = []) /\
   (DILATE_3 [h] = [h]) /\
   (DILATE_3 (h::t) = [h;0;0] ++ (MDILATE_3 t))
`;
> EVAL ``DILATE_3 [1;2;3]``;
val it = |- MDILATE_3 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3]: thm
*)

(* ------------------------------------------------------------------------- *)
(* List Dilation (Multiplicative)                                            *)
(* ------------------------------------------------------------------------- *)

(* Note:
   It would be better to define:  MDILATE e n l = inserting n (e)'s,
   that is, using GENLIST (K e) n, so that only MDILATE e 0 l = l.
   However, the intention is to have later, for polynomials:
       peval p (X ** n) = pdilate n p
   and since X ** 1 = X, and peval p X = p,
   it is desirable to have MDILATE e 1 l = l, with the definition below.

   However, the multiplicative feature at the end destroys such an application.
*)

(* Dilate a list with an element e, for a factor n (n <> 0) *)
val MDILATE_def = Define`
   (MDILATE e n [] = []) /\
   (MDILATE e n (h::t) = if t = [] then [h] else (h:: GENLIST (K e) (PRE n)) ++ (MDILATE e n t))
`;
(*
> EVAL ``MDILATE 0 2 [1;2;3]``;
val it = |- MDILATE 0 2 [1; 2; 3] = [1; 0; 2; 0; 3]: thm
> EVAL ``MDILATE 0 3 [1;2;3]``;
val it = |- MDILATE 0 3 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3]: thm
> EVAL ``MDILATE #0 3 [a;b;#1]``;
val it = |- MDILATE #0 3 [a; b; #1] = [a; #0; #0; b; #0; #0; #1]: thm
*)

(* Theorem: MDILATE e n [] = [] *)
(* Proof: by MDILATE_def *)
val MDILATE_NIL = store_thm(
  "MDILATE_NIL",
  ``!e n. MDILATE e n [] = []``,
  rw[MDILATE_def]);

(* export simple result *)
val _ = export_rewrites["MDILATE_NIL"];

(* Theorem: MDILATE e n [x] = [x] *)
(* Proof: by MDILATE_def *)
val MDILATE_SING = store_thm(
  "MDILATE_SING",
  ``!e n x. MDILATE e n [x] = [x]``,
  rw[MDILATE_def]);

(* export simple result *)
val _ = export_rewrites["MDILATE_SING"];

(* Theorem: MDILATE e n (h::t) =
            if t = [] then [h] else (h:: GENLIST (K e) (PRE n)) ++ (MDILATE e n t) *)
(* Proof: by MDILATE_def *)
val MDILATE_CONS = store_thm(
  "MDILATE_CONS",
  ``!e n h t. MDILATE e n (h::t) =
    if t = [] then [h] else (h:: GENLIST (K e) (PRE n)) ++ (MDILATE e n t)``,
  rw[MDILATE_def]);

(* Theorem: MDILATE e 1 l = l *)
(* Proof:
   By induction on l.
   Base: !e. MDILATE e 1 [] = [], true     by MDILATE_NIL
   Step: !e. MDILATE e 1 l = l ==> !h e. MDILATE e 1 (h::l) = h::l
      If l = [],
        MDILATE e 1 [h]
      = [h]                                by MDILATE_SING
      If l <> [],
        MDILATE e 1 (h::l)
      = (h:: GENLIST (K e) (PRE 1)) ++ (MDILATE e n l)   by MDILATE_CONS
      = (h:: GENLIST (K e) (PRE 1)) ++ l   by induction hypothesis
      = (h:: GENLIST (K e) 0) ++ l         by PRE
      = [h] ++ l                           by GENLIST_0
      = h::l                               by CONS_APPEND
*)
val MDILATE_1 = store_thm(
  "MDILATE_1",
  ``!l e. MDILATE e 1 l = l``,
  Induct_on `l` >>
  rw[MDILATE_def]);

(* Theorem: MDILATE e 0 l = l *)
(* Proof:
   By induction on l, and note GENLIST (K e) (PRE 0) = GENLIST (K e) 0 = [].
*)
val MDILATE_0 = store_thm(
  "MDILATE_0",
  ``!l e. MDILATE e 0 l = l``,
  Induct_on `l` >> rw[MDILATE_def]);

(* Theorem: LENGTH (MDILATE e n l) =
            if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l)) *)
(* Proof:
   If n = 0,
      Then MDILATE e 0 l = l       by MDILATE_0
      Hence true.
   If n <> 0,
      Then 0 < n                   by NOT_ZERO_LT_ZERO
   By induction on l.
   Base: LENGTH (MDILATE e n []) = if n = 0 then LENGTH [] else if [] = [] then 0 else SUC (n * PRE (LENGTH []))
       LENGTH (MDILATE e n [])
     = LENGTH []                   by MDILATE_NIL
     = 0                           by LENGTH_NIL
   Step: LENGTH (MDILATE e n l) = if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l)) ==>
         !h. LENGTH (MDILATE e n (h::l)) = if n = 0 then LENGTH (h::l) else if h::l = [] then 0 else SUC (n * PRE (LENGTH (h::l)))
       Note h::l = [] <=> F           by NOT_CONS_NIL
       If l = [],
         LENGTH (MDILATE e n [h])
       = LENGTH [h]                   by MDILATE_SING
       = 1                            by LENGTH_EQ_1
       = SUC 0                        by ONE
       = SUC (n * 0)                  by MULT_0
       = SUC (n * (PRE (LENGTH [h]))) by LENGTH_EQ_1, PRE_SUC_EQ
       If l <> [],
         Then LENGTH l <> 0           by LENGTH_NIL
         LENGTH (MDILATE e n (h::l))
       = LENGTH (h:: GENLIST (K e) (PRE n) ++ MDILATE e n l)          by MDILATE_CONS
       = LENGTH (h:: GENLIST (K e) (PRE n)) + LENGTH (MDILATE e n l)  by LENGTH_APPEND
       = n + LENGTH (MDILATE e n l)       by LENGTH_GENLIST
       = n + SUC (n * PRE (LENGTH l))     by induction hypothesis
       = SUC (n + n * PRE (LENGTH l))     by ADD_SUC
       = SUC (n * SUC (PRE (LENGTH l)))   by MULT_SUC
       = SUC (n * LENGTH l)               by SUC_PRE, 0 < LENGTH l
       = SUC (n * PRE (LENGTH (h::l)))    by LENGTH, PRE_SUC_EQ
*)
val MDILATE_LENGTH = store_thm(
  "MDILATE_LENGTH",
  ``!l e n. LENGTH (MDILATE e n l) =
   if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[MDILATE_0] >>
  `0 < n` by decide_tac >>
  Induct_on `l` >-
  rw[] >>
  rw[MDILATE_def] >>
  `LENGTH l <> 0` by metis_tac[LENGTH_NIL] >>
  `0 < LENGTH l` by decide_tac >>
  `PRE n + SUC (n * PRE (LENGTH l)) = SUC (PRE n) + n * PRE (LENGTH l)` by rw[] >>
  `_ = n + n * PRE (LENGTH l)` by decide_tac >>
  `_ = n * SUC (PRE (LENGTH l))` by rw[MULT_SUC] >>
  `_ = n * LENGTH l` by metis_tac[SUC_PRE] >>
  decide_tac);

(* Theorem: LENGTH l <= LENGTH (MDILATE e n l) *)
(* Proof:
   If n = 0,
        LENGTH (MDILATE e 0 l)
      = LENGTH l                       by MDILATE_LENGTH
      >= LENGTH l
   If l = [],
        LENGTH (MDILATE e n [])
      = LENGTH []                      by MDILATE_NIL
      >= LENGTH []
   If l <> [],
      Then ?h t. l = h::t              by list_CASES
        LENGTH (MDILATE e n (h::t))
      = SUC (n * PRE (LENGTH (h::t)))  by MDILATE_LENGTH
      = SUC (n * PRE (SUC (LENGTH t))) by LENGTH
      = SUC (n * LENGTH t)             by PRE
      = n * LENGTH t + 1               by ADD1
      >= LENGTH t + 1                  by LE_MULT_CANCEL_LBARE, 0 < n
      = SUC (LENGTH t)                 by ADD1
      = LENGTH (h::t)                  by LENGTH
*)
val MDILATE_LENGTH_LOWER = store_thm(
  "MDILATE_LENGTH_LOWER",
  ``!l e n. LENGTH l <= LENGTH (MDILATE e n l)``,
  rw[MDILATE_LENGTH] >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  rw[]);

(* Theorem: 0 < n ==> LENGTH (MDILATE e n l) <= SUC (n * PRE (LENGTH l)) *)
(* Proof:
   Since n <> 0,
   If l = [],
        LENGTH (MDILATE e n [])
      = LENGTH []                  by MDILATE_NIL
      = 0                          by LENGTH_NIL
        SUC (n * PRE (LENGTH []))
      = SUC (n * PRE 0)            by LENGTH_NIL
      = SUC 0                      by PRE, MULT_0
      > 0                          by LESS_SUC
   If l <> [],
        LENGTH (MDILATE e n l)
      = SUC (n * PRE (LENGTH l))   by MDILATE_LENGTH, n <> 0
*)
val MDILATE_LENGTH_UPPER = store_thm(
  "MDILATE_LENGTH_UPPER",
  ``!l e n. 0 < n ==> LENGTH (MDILATE e n l) <= SUC (n * PRE (LENGTH l))``,
  rw[MDILATE_LENGTH]);

(* Theorem: k < LENGTH (MDILATE e n l) ==>
            (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e) *)
(* Proof:
   If n = 0,
      Then MDILATE e 0 l = l     by MDILATE_0
      Hence true trivially.
   If n <> 0,
      Then 0 < n                 by NOT_ZERO_LT_ZERO
   By induction on l.
   Base: !k. k < LENGTH (MDILATE e n []) ==>
         (EL k (MDILATE e n []) = if n = 0 then EL k [] else if k MOD n = 0 then EL (k DIV n) [] else e)
      Note LENGTH (MDILATE e n [])
         = LENGTH []         by MDILATE_NIL
         = 0                 by LENGTH_NIL
      Thus k < 0 <=> F       by NOT_ZERO_LT_ZERO
   Step: !k. k < LENGTH (MDILATE e n l) ==> (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e) ==>
         !h k. k < LENGTH (MDILATE e n (h::l)) ==> (EL k (MDILATE e n (h::l)) = if n = 0 then EL k (h::l) else if k MOD n = 0 then EL (k DIV n) (h::l) else e)
      Note LENGTH (MDILATE e n [h]) = 1    by MDILATE_SING
       and LENGTH (MDILATE e n (h::l))
         = SUC (n * PRE (LENGTH (h::l)))   by MDILATE_LENGTH, n <> 0
         = SUC (n * PRE (SUC (LENGTH l)))  by LENGTH
         = SUC (n * LENGTH l)              by PRE

      If l = [],
        Then MDILATE e n [h] = [h]         by MDILATE_SING
         and LENGTH (MDILATE e n [h]) = 1  by LENGTH
          so k < 1 means k = 0.
         and 0 DIV n = 0                   by ZERO_DIV, 0 < n
         and 0 MOD n = 0                   by ZERO_MOD, 0 < n
        Thus EL k [h] = EL (k DIV n) [h].

      If l <> [],
        Let t = h::GENLIST (K e) (PRE n)
        Note LENGTH t = n                  by LENGTH_GENLIST
        If k < n,
           Then k MOD n = k                by LESS_MOD, k < n
             EL k (MDILATE e n (h::l))
           = EL k (t ++ MDILATE e n l)     by MDILATE_CONS
           = EL k t                        by EL_APPEND, k < LENGTH t
           If k = 0,
              EL 0 t
            = EL 0 (h:: GENLIST (K e) (PRE n))  by notation of t
            = h
            = EL (0 DIV n) (h::l)          by EL, HD
           If k <> 0,
              EL k t
            = EL k (h:: GENLIST (K e) (PRE n))    by notation of t
            = EL (PRE k) (GENLIST (K e) (PRE n))  by EL_CONS
            = (K e) (PRE k)                by EL_GENLIST, PRE k < PRE n
            = e                            by application of K
        If ~(k < n), n <= k.
           Given k < LENGTH (MDILATE e n (h::l))
              or k < SUC (n * LENGTH l)    by above
             ==> k - n < SUC (n * LENGTH l) - n      by n <= k
                       = SUC (n * LENGTH l - n)      by SUB
                       = SUC (n * (LENGTH l - 1))    by LEFT_SUB_DISTRIB
                       = SUC (n * PRE (LENGTH l))    by PRE_SUB1
              or k - n < LENGTH (MDILATE e n l)      by MDILATE_LENGTH
            Thus (k - n) MOD n = k MOD n             by SUB_MOD
             and (k - n) DIV n = k DIV n - 1         by SUB_DIV
          If k MOD n = 0,
             Note 0 < k DIV n                        by DIVIDES_MOD_0, DIV_POS
             EL k (t ++ MDILATE e n l)
           = EL (k - n) (MDILATE e n l)              by EL_APPEND, n <= k
           = EL (k DIV n - 1) l                      by induction hypothesis, (k - n) MOD n = 0
           = EL (PRE (k DIV n)) l                    by PRE_SUB1
           = EL (k DIV n) (h::l)                     by EL_CONS, 0 < k DIV n
          If k MOD n <> 0,
             EL k (t ++ MDILATE e n l)
           = EL (k - n) (MDILATE e n l)              by EL_APPEND, n <= k
           = e                                       by induction hypothesis, (k - n) MOD n <> 0
*)
val MDILATE_EL = store_thm(
  "MDILATE_EL",
  ``!l e n k. k < LENGTH (MDILATE e n l) ==>
      (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e)``,
  ntac 3 strip_tac >>
  Cases_on `n = 0` >-
  rw[MDILATE_0] >>
  `0 < n` by decide_tac >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  `LENGTH (MDILATE e n [h]) = 1` by rw[MDILATE_SING] >>
  `LENGTH (MDILATE e n (h::l)) = SUC (n * LENGTH l)` by rw[MDILATE_LENGTH] >>
  qabbrev_tac `t = h:: GENLIST (K e) (PRE n)` >>
  `!k. k < 1 <=> (k = 0)` by decide_tac >>
  rw_tac std_ss[MDILATE_def] >-
  metis_tac[ZERO_DIV] >-
  metis_tac[ZERO_MOD] >-
 (rw_tac std_ss[EL_APPEND] >| [
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k MOD n = k` by rw[LESS_MOD] >>
    `!x. EL 0 (h::x) = h` by rw[] >>
    metis_tac[ZERO_DIV],
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k - n < LENGTH (MDILATE e n l)` by rw[MDILATE_LENGTH] >>
    `(k - n) MOD n = k MOD n` by rw[SUB_MOD] >>
    `(k - n) DIV n = k DIV n - 1` by rw[GSYM SUB_DIV] >>
    `0 < k DIV n` by rw[DIVIDES_MOD_0, DIV_POS] >>
    `EL (k - n) (MDILATE e n l) = EL (k DIV n - 1) l` by rw[] >>
    `_ = EL (PRE (k DIV n)) l` by rw[PRE_SUB1] >>
    `_ = EL (k DIV n) (h::l)` by rw[EL_CONS] >>
    rw[]
  ]) >>
  rw_tac std_ss[EL_APPEND] >| [
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k MOD n = k` by rw[LESS_MOD] >>
    `0 < k /\ PRE k < PRE n` by decide_tac >>
    `EL k t = EL (PRE k) (GENLIST (K e) (PRE n))` by rw[EL_CONS, Abbr`t`] >>
    `_ = e` by rw[] >>
    rw[],
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k - n < LENGTH (MDILATE e n l)` by rw[MDILATE_LENGTH] >>
    `n <= k` by decide_tac >>
    `(k - n) MOD n = k MOD n` by rw[SUB_MOD] >>
    `EL (k - n) (MDILATE e n l) = e` by rw[] >>
    rw[]
  ]);

(* This is a milestone theorem. *)

(* Theorem: (MDILATE e n l = []) <=> (l = []) *)
(* Proof:
   If part: MDILATE e n l = [] ==> l = []
      By contradiction, suppose l <> [].
      If n = 0,
         Then MDILATE e 0 l = l     by MDILATE_0
         This contradicts MDILATE e 0 l = [].
      If n <> 0,
         Then LENGTH (MDILATE e n l)
            = SUC (n * PRE (LENGTH l))  by MDILATE_LENGTH
            <> 0                    by SUC_NOT
         So (MDILATE e n l) <> []   by LENGTH_NIL
         This contradicts MDILATE e n l = []
   Only-if part: l = [] ==> MDILATE e n l = []
      True by MDILATE_NIL
*)
val MDILATE_EQ_NIL = store_thm(
  "MDILATE_EQ_NIL",
  ``!l e n. (MDILATE e n l = []) <=> (l = [])``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  Cases_on `n = 0` >| [
    `MDILATE e 0 l = l` by rw[GSYM MDILATE_0] >>
    metis_tac[],
    `LENGTH (MDILATE e n l) = SUC (n * PRE (LENGTH l))` by rw[MDILATE_LENGTH] >>
    `LENGTH (MDILATE e n l) <> 0` by decide_tac >>
    metis_tac[LENGTH_EQ_0]
  ]);

(* Theorem: LAST (MDILATE e n l) = LAST l *)
(* Proof:
   If l = [],
        LAST (MDILATE e n [])
      = LAST []                by MDILATE_NIL
   If l <> [],
      If n = 0,
        LAST (MDILATE e 0 l)
      = LAST l                 by MDILATE_0
      If n <> 0, then 0 < m    by LESS_0
        Then MDILATE e n l <> []             by MDILATE_EQ_NIL
          or LENGTH (MDILATE e n l) <> 0     by LENGTH_NIL
        Note PRE (LENGTH (MDILATE e n l))
           = PRE (SUC (n * PRE (LENGTH l)))  by MDILATE_LENGTH
           = n * PRE (LENGTH l)              by PRE
        Let k = PRE (LENGTH (MDILATE e n l)).
        Then k < LENGTH (MDILATE e n l)      by PRE x < x
         and k MOD n = 0                     by MOD_EQ_0, MULT_COMM, 0 < n
         and k DIV n = PRE (LENGTH l)        by MULT_DIV, MULT_COMM

        LAST (MDILATE e n l)
      = EL k (MDILATE e n l)                 by LAST_EL
      = EL (k DIV n) l                       by MDILATE_EL
      = EL (PRE (LENGTH l)) l                by above
      = LAST l                               by LAST_EL
*)
val MDILATE_LAST = store_thm(
  "MDILATE_LAST",
  ``!l e n. LAST (MDILATE e n l) = LAST l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  Cases_on `n = 0` >-
  rw[MDILATE_0] >>
  `0 < n` by decide_tac >>
  `MDILATE e n l <> []` by rw[MDILATE_EQ_NIL] >>
  `LENGTH (MDILATE e n l) <> 0` by metis_tac[LENGTH_NIL] >>
  qabbrev_tac `k = PRE (LENGTH (MDILATE e n l))` >>
  rw[LAST_EL] >>
  `k = n * PRE (LENGTH l)` by rw[MDILATE_LENGTH, Abbr`k`] >>
  `k MOD n = 0` by metis_tac[MOD_EQ_0, MULT_COMM] >>
  `k DIV n = PRE (LENGTH l)` by metis_tac[MULT_DIV, MULT_COMM] >>
  `k < LENGTH (MDILATE e n l)` by rw[Abbr`k`] >>
  rw[MDILATE_EL]);

(*
Succesive dilation:

> EVAL ``MDILATE #0 3 [a; b; c]``;
val it = |- MDILATE #0 3 [a; b; c] = [a; #0; #0; b; #0; #0; c]: thm
> EVAL ``MDILATE #0 4 [a; b; c]``;
val it = |- MDILATE #0 4 [a; b; c] = [a; #0; #0; #0; b; #0; #0; #0; c]: thm
> EVAL ``MDILATE #0 1 (MDILATE #0 3 [a; b; c])``;
val it = |- MDILATE #0 1 (MDILATE #0 3 [a; b; c]) = [a; #0; #0; b; #0; #0; c]: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 3 [a; b; c])``;
val it = |- MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = [a; #0; #0; #0; #0; #0; b; #0; #0; #0; #0; #0; c]: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 2 [a; b; c])``;
val it = |- MDILATE #0 2 (MDILATE #0 2 [a; b; c]) = [a; #0; #0; #0; b; #0; #0; #0; c]: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 2 [a; b; c]) = MDILATE #0 4 [a; b; c]``;
val it = |- (MDILATE #0 2 (MDILATE #0 2 [a; b; c]) = MDILATE #0 4 [a; b; c]) <=> T: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 5 [a; b; c]``;
val it = |- (MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 5 [a; b; c]) <=> F: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 6 [a; b; c]``;
val it = |- (MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 6 [a; b; c]) <=> T: thm

So successive dilation is related to product, or factorisation, or primes:
MDILATE e m (MDILATE e n l) = MDILATE e (m * n) l, for 0 < m, 0 < n.

*)

(* ------------------------------------------------------------------------- *)
(* List Dilation (Additive)                                                  *)
(* ------------------------------------------------------------------------- *)

(* Dilate by inserting m zeroes, at position n of tail *)
val DILATE_def = tDefine "DILATE" `
  (DILATE e n m [] = []) /\
  (DILATE e n m [h] = [h]) /\
  (DILATE e n m (h::t) = h:: (TAKE n t ++ (GENLIST (K e) m) ++ DILATE e n m (DROP n t)))
`(
  WF_REL_TAC `measure (\(a,b,c,d). LENGTH d)` >>
  rw[LENGTH_DROP]);

(*
> EVAL ``DILATE 0 0 1 [1;2;3]``;
val it = |- DILATE 0 0 1 [1; 2; 3] = [1; 0; 2; 0; 3]: thm
> EVAL ``DILATE 0 0 2 [1;2;3]``;
val it = |- DILATE 0 0 2 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3]: thm
> EVAL ``DILATE 0 1 1 [1;2;3]``;
val it = |- DILATE 0 1 1 [1; 2; 3] = [1; 2; 0; 3]: thm
> EVAL ``DILATE 0 1 1 (DILATE 0 0 1 [1;2;3])``;
val it = |- DILATE 0 1 1 (DILATE 0 0 1 [1; 2; 3]) = [1; 0; 0; 2; 0; 0; 3]: thm
>  EVAL ``DILATE 0 0 3 [1;2;3]``;
val it = |- DILATE 0 0 3 [1; 2; 3] = [1; 0; 0; 0; 2; 0; 0; 0; 3]: thm
> EVAL ``DILATE 0 1 1 (DILATE 0 0 2 [1;2;3])``;
val it = |- DILATE 0 1 1 (DILATE 0 0 2 [1; 2; 3]) = [1; 0; 0; 0; 2; 0; 0; 0; 0; 3]: thm
> EVAL ``DILATE 0 0 3 [1;2;3] = DILATE 0 2 1 (DILATE 0 0 2 [1;2;3])``;
val it = |- (DILATE 0 0 3 [1; 2; 3] = DILATE 0 2 1 (DILATE 0 0 2 [1; 2; 3])) <=> T: thm

> EVAL ``DILATE 0 0 0 [1;2;3]``;
val it = |- DILATE 0 0 0 [1; 2; 3] = [1; 2; 3]: thm
> EVAL ``DILATE 1 0 0 [1;2;3]``;
val it = |- DILATE 1 0 0 [1; 2; 3] = [1; 2; 3]: thm
> EVAL ``DILATE 1 0 1 [1;2;3]``;
val it = |- DILATE 1 0 1 [1; 2; 3] = [1; 1; 2; 1; 3]: thm
> EVAL ``DILATE 1 1 1 [1;2;3]``;
val it = |- DILATE 1 1 1 [1; 2; 3] = [1; 2; 1; 3]: thm
> EVAL ``DILATE 1 1 2 [1;2;3]``;
val it = |- DILATE 1 1 2 [1; 2; 3] = [1; 2; 1; 1; 3]: thm
> EVAL ``DILATE 1 1 3 [1;2;3]``;
val it = |- DILATE 1 1 3 [1; 2; 3] = [1; 2; 1; 1; 1; 3]: thm
*)

(* Theorem: DILATE e n m [] = [] *)
(* Proof: by DILATE_def *)
val DILATE_NIL = save_thm("DILATE_NIL", DILATE_def |> CONJUNCT1);
(* val DILATE_NIL = |- !n m e. DILATE e n m [] = []: thm *)

(* export simple result *)
val _ = export_rewrites["DILATE_NIL"];

(* Theorem: DILATE e n m [h] = [h] *)
(* Proof: by DILATE_def *)
val DILATE_SING = save_thm("DILATE_SING", DILATE_def |> CONJUNCT2 |> CONJUNCT1);
(* val DILATE_SING = |- !n m h e. DILATE e n m [h] = [h]: thm *)

(* export simple result *)
val _ = export_rewrites["DILATE_SING"];

(* Theorem: DILATE e n m (h::t) =
            if t = [] then [h] else h:: (TAKE n t ++ (GENLIST (K e) m) ++ DILATE e n m (DROP n t)) *)
(* Proof: by DILATE_def, list_CASES *)
val DILATE_CONS = store_thm(
  "DILATE_CONS",
  ``!n m h t e. DILATE e n m (h::t) =
    if t = [] then [h] else h:: (TAKE n t ++ (GENLIST (K e) m) ++ DILATE e n m (DROP n t))``,
  metis_tac[DILATE_def, list_CASES]);

(* Theorem: DILATE e 0 n (h::t) = if t = [] then [h] else h::(GENLIST (K e) n ++ DILATE e 0 n t) *)
(* Proof:
   If t = [],
     DILATE e 0 n (h::t) = [h]    by DILATE_CONS
   If t <> [],
     DILATE e 0 n (h::t)
   = h:: (TAKE 0 t ++ (GENLIST (K e) n) ++ DILATE e 0 n (DROP 0 t))  by DILATE_CONS
   = h:: ([] ++ (GENLIST (K e) n) ++ DILATE e 0 n t)                 by TAKE_0, DROP_0
   = h:: (GENLIST (K e) n ++ DILATE e 0 n t)                         by APPEND
*)
val DILATE_0_CONS = store_thm(
  "DILATE_0_CONS",
  ``!n h t e. DILATE e 0 n (h::t) = if t = [] then [h] else h::(GENLIST (K e) n ++ DILATE e 0 n t)``,
  rw[DILATE_CONS]);

(* Theorem: DILATE e 0 0 l = l *)
(* Proof:
   By induction on l.
   Base: DILATE e 0 0 [] = [], true         by DILATE_NIL
   Step: DILATE e 0 0 l = l ==> !h. DILATE e 0 0 (h::l) = h::l
      If l = [],
         DILATE e 0 0 [h] = [h]             by DILATE_SING
      If l <> [],
         DILATE e 0 0 (h::l)
       = h::(GENLIST (K e) 0 ++ DILATE e 0 0 l)   by DILATE_0_CONS
       = h::([] ++ DILATE e 0 0 l)                by GENLIST_0
       = h:: DILATE e 0 0 l                       by APPEND
       = h::l                                     by induction hypothesis
*)
val DILATE_0_0 = store_thm(
  "DILATE_0_0",
  ``!l e. DILATE e 0 0 l = l``,
  Induct >>
  rw[DILATE_0_CONS]);

(* Theorem: DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l) *)
(* Proof:
   If n = 0,
      DILATE e 0 1 l = DILATE e 0 1 (DILATE e 0 0 l)   by DILATE_0_0
   If n <> 0,
      GENLIST (K e) n <> []       by LENGTH_GENLIST, LENGTH_NIL
   By induction on l.
   Base: DILATE e 0 (SUC n) [] = DILATE e n 1 (DILATE e 0 n [])
      DILATE e 0 (SUC n) [] = []                  by DILATE_NIL
        DILATE e n 1 (DILATE e 0 n [])
      = DILATE e n 1 [] = []                      by DILATE_NIL
   Step: DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l) ==>
         !h. DILATE e 0 (SUC n) (h::l) = DILATE e n 1 (DILATE e 0 n (h::l))
      If l = [],
        DILATE e 0 (SUC n) [h] = [h]       by DILATE_SING
          DILATE e n 1 (DILATE e 0 n [h])
        = DILATE e n 1 [h] = [h]           by DILATE_SING
      If l <> [],
          DILATE e 0 (SUC n) (h::l)
        = h::(GENLIST (K e) (SUC n) ++ DILATE e 0 (SUC n) l)                by DILATE_0_CONS
        = h::(GENLIST (K e) (SUC n) ++ DILATE e n 1 (DILATE e 0 n l))       by induction hypothesis

        Note LENGTH (GENLIST (K e) n) = n                 by LENGTH_GENLIST
          so (GENLIST (K e) n ++ DILATE e 0 n l) <> []    by APPEND_eq_NIL, LENGTH_NIL [1]
         and TAKE n (GENLIST (K e) n ++ DILATE e 0 n l) = GENLIST (K e) n   by TAKE_LENGTH_APPEND [2]
         and DROP n (GENLIST (K e) n ++ DILATE e 0 n l) = DILATE e 0 n l    by DROP_LENGTH_APPEND [3]
         and GENLIST (K e) (SUC n)
           = GENLIST (K e) (1 + n)                        by SUC_ONE_ADD
           = GENLIST (K e) n ++ GENLIST (K e) 1           by GENLIST_K_ADD [4]

          DILATE e n 1 (DILATE e 0 n (h::l))
        = DILATE e n 1 (h::(GENLIST (K e) n ++ DILATE e 0 n l))             by DILATE_0_CONS
        = h::(TAKE n (GENLIST (K e) n ++ DILATE e 0 n l) ++ GENLIST (K e) 1 ++
               DILATE e n 1 (DROP n (GENLIST (K e) n ++ DILATE e 0 n l)))   by DILATE_CONS, [1]
        = h::(GENLIST (K e) n ++ GENLIST (K e) 1 ++ DILATE e n 1 (DILATE e 0 n l))   by above [2], [3]
        = h::(GENLIST (K e) (SUC n) ++ DILATE e n 1 (DILATE e 0 n l))       by above [4]
*)
val DILATE_0_SUC = store_thm(
  "DILATE_0_SUC",
  ``!l e n. DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[DILATE_0_0] >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[DILATE_SING] >>
  qabbrev_tac `a = GENLIST (K e) n ++ DILATE e 0 n l` >>
  `LENGTH (GENLIST (K e) n) = n` by rw[] >>
  `a <> []` by metis_tac[APPEND_eq_NIL, LENGTH_NIL] >>
  `TAKE n a = GENLIST (K e) n` by metis_tac[TAKE_LENGTH_APPEND] >>
  `DROP n a = DILATE e 0 n l` by metis_tac[DROP_LENGTH_APPEND] >>
  `GENLIST (K e) (SUC n) = GENLIST (K e) n ++ GENLIST (K e) 1` by rw_tac std_ss[SUC_ONE_ADD, GENLIST_K_ADD] >>
  metis_tac[DILATE_0_CONS, DILATE_CONS]);

(* Theorem: LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l)) *)
(* Proof:
   By induction on l.
   Base: LENGTH (DILATE e 0 n []) = 0
         LENGTH (DILATE e 0 n [])
       = LENGTH []                       by DILATE_NIL
       = 0                               by LENGTH_NIL
   Step: LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l)) ==>
         !h. LENGTH (DILATE e 0 n (h::l)) = SUC (SUC n * PRE (LENGTH (h::l)))
       If l = [],
          LENGTH (DILATE e 0 n [h])
        = LENGTH [h]                     by DILATE_SING
        = 1                              by LENGTH
          SUC (SUC n * PRE (LENGTH [h])
        = SUC (SUC n * PRE 1)            by LENGTH
        = SUC (SUC n * 0)                by PRE_SUB1
        = SUC 0                          by MULT_0
        = 1                              by ONE
       If l <> [],
          Note LENGTH l <> 0             by LENGTH_NIL
          LENGTH (DILATE e 0 n (h::l))
        = LENGTH (h::(GENLIST (K e) n ++ DILATE e 0 n l))           by DILATE_0_CONS
        = SUC (LENGTH (GENLIST (K e) n ++ DILATE e 0 n l))          by LENGTH
        = SUC (LENGTH (GENLIST (K e) n) + LENGTH (DILATE e 0 n l))  by LENGTH_APPEND
        = SUC (n + LENGTH (DILATE e 0 n l))        by LENGTH_GENLIST
        = SUC (n + SUC (SUC n * PRE (LENGTH l)))   by induction hypothesis
        = SUC (SUC (n + SUC n * PRE (LENGTH l)))   by ADD_SUC
        = SUC (SUC n  + SUC n * PRE (LENGTH l))    by ADD_COMM, ADD_SUC
        = SUC (SUC n * SUC (PRE (LENGTH l)))       by MULT_SUC
        = SUC (SUC n * LENGTH l)                   by SUC_PRE, 0 < LENGTH l
        = SUC (SUC n * PRE (LENGTH (h::l)))        by LENGTH, PRE_SUC_EQ
*)
val DILATE_0_LENGTH = store_thm(
  "DILATE_0_LENGTH",
  ``!l e n. LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l))``,
  Induct >-
  rw[] >>
  rw_tac std_ss[LENGTH] >>
  Cases_on `l = []` >-
  rw[] >>
  `0 < LENGTH l` by metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO] >>
  `LENGTH (DILATE e 0 n (h::l)) = LENGTH (h::(GENLIST (K e) n ++ DILATE e 0 n l))` by rw[DILATE_0_CONS] >>
  `_ = SUC (LENGTH (GENLIST (K e) n ++ DILATE e 0 n l))` by rw[] >>
  `_ = SUC (n + LENGTH (DILATE e 0 n l))` by rw[] >>
  `_ = SUC (n + SUC (SUC n * PRE (LENGTH l)))` by rw[] >>
  `_ = SUC (SUC (n + SUC n * PRE (LENGTH l)))` by rw[] >>
  `_ = SUC (SUC n + SUC n * PRE (LENGTH l))` by rw[] >>
  `_ = SUC (SUC n * SUC (PRE (LENGTH l)))` by rw[MULT_SUC] >>
  `_ = SUC (SUC n * LENGTH l)` by rw[SUC_PRE] >>
  rw[]);

(* Theorem: LENGTH l <= LENGTH (DILATE e 0 n l) *)
(* Proof:
   If l = [],
        LENGTH (DILATE e 0 n [])
      = LENGTH []                      by DILATE_NIL
      >= LENGTH []
   If l <> [],
      Then ?h t. l = h::t              by list_CASES
        LENGTH (DILATE e 0 n (h::t))
      = SUC (SUC n * PRE (LENGTH (h::t)))  by DILATE_0_LENGTH
      = SUC (SUC n * PRE (SUC (LENGTH t))) by LENGTH
      = SUC (SUC n * LENGTH t)             by PRE
      = SUC n * LENGTH t + 1               by ADD1
      >= LENGTH t + 1                  by LE_MULT_CANCEL_LBARE, 0 < SUC n
      = SUC (LENGTH t)                 by ADD1
      = LENGTH (h::t)                  by LENGTH
*)
val DILATE_0_LENGTH_LOWER = store_thm(
  "DILATE_0_LENGTH_LOWER",
  ``!l e n. LENGTH l <= LENGTH (DILATE e 0 n l)``,
  rw[DILATE_0_LENGTH] >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  rw[]);

(* Theorem: LENGTH (DILATE e 0 n l) <= SUC (SUC n * PRE (LENGTH l)) *)
(* Proof:
   If l = [],
        LENGTH (DILATE e 0 n [])
      = LENGTH []                      by DILATE_NIL
      = 0                              by LENGTH_NIL
        SUC (SUC n * PRE (LENGTH []))
      = SUC (SUC n * PRE 0)            by LENGTH_NIL
      = SUC 0                          by PRE, MULT_0
      > 0                              by LESS_SUC
   If l <> [],
        LENGTH (DILATE e 0 n l)
      = SUC (SUC n * PRE (LENGTH l))   by DILATE_0_LENGTH
*)
val DILATE_0_LENGTH_UPPER = store_thm(
  "DILATE_0_LENGTH_UPPER",
  ``!l e n. LENGTH (DILATE e 0 n l) <= SUC (SUC n * PRE (LENGTH l))``,
  rw[DILATE_0_LENGTH]);

(* Theorem: k < LENGTH (DILATE e 0 n l) ==>
            (EL k (DILATE e 0 n l) = if k MOD (SUC n) = 0 then EL (k DIV (SUC n)) l else e) *)
(* Proof:
   Let m = SUC n, then 0 < m.
   By induction on l.
   Base: !k. k < LENGTH (DILATE e 0 n []) ==> (EL k (DILATE e 0 n []) = if k MOD m = 0 then EL (k DIV m) [] else e)
      Note LENGTH (DILATE e 0 n [])
         = LENGTH []         by DILATE_NIL
         = 0                 by LENGTH_NIL
      Thus k < 0 <=> F       by NOT_ZERO_LT_ZERO
   Step: !k. k < LENGTH (DILATE e 0 n l) ==> (EL k (DILATE e 0 n l) = if k MOD m = 0 then EL (k DIV m) l else e) ==>
         !h k. k < LENGTH (DILATE e 0 n (h::l)) ==> (EL k (DILATE e 0 n (h::l)) = if k MOD m = 0 then EL (k DIV m) (h::l) else e)
      Note LENGTH (DILATE e 0 n [h]) = 1    by DILATE_SING
       and LENGTH (DILATE e 0 n (h::l))
         = SUC (m * PRE (LENGTH (h::l)))    by DILATE_0_LENGTH, n <> 0
         = SUC (m * PRE (SUC (LENGTH l)))   by LENGTH
         = SUC (m * LENGTH l)               by PRE

      If l = [],
        Then DILATE e 0 n [h] = [h]         by DILATE_SING
         and LENGTH (DILATE e 0 n [h]) = 1  by LENGTH
          so k < 1 means k = 0.
         and 0 DIV m = 0                    by ZERO_DIV, 0 < m
         and 0 MOD m = 0                    by ZERO_MOD, 0 < m
        Thus EL k [h] = EL (k DIV m) [h].

      If l <> [],
        Let t = h:: GENLIST (K e) n.
        Note LENGTH t = SUC n = m           by LENGTH_GENLIST
        If k < m,
           Then k MOD m = k                 by LESS_MOD, k < m
             EL k (DILATE e 0 n (h::l))
           = EL k (t ++ DILATE e 0 n l)     by DILATE_0_CONS
           = EL k t                         by EL_APPEND, k < LENGTH t
           If k = 0, i.e. k MOD m = 0.
              EL 0 t
            = EL 0 (h:: GENLIST (K e) (PRE n))  by notation of t
            = h
            = EL (0 DIV m) (h::l)           by EL, HD
           If k <> 0, i.e. k MOD m <> 0.
              EL k t
            = EL k (h:: GENLIST (K e) n)    by notation of t
            = EL (PRE k) (GENLIST (K e) n)  by EL_CONS
            = (K e) (PRE k)                 by EL_GENLIST, PRE k < PRE m = n
            = e                             by application of K
        If ~(k < m), then m <= k.
           Given k < LENGTH (DILATE e 0 n (h::l))
              or k < SUC (m * LENGTH l)              by above
             ==> k - m < SUC (m * LENGTH l) - m      by m <= k
                       = SUC (m * LENGTH l - m)      by SUB
                       = SUC (m * (LENGTH l - 1))    by LEFT_SUB_DISTRIB
                       = SUC (m * PRE (LENGTH l))    by PRE_SUB1
              or k - m < LENGTH (MDILATE e n l)      by MDILATE_LENGTH
            Thus (k - m) MOD m = k MOD m             by SUB_MOD
             and (k - m) DIV m = k DIV m - 1         by SUB_DIV
          If k MOD m = 0,
             Note 0 < k DIV m                        by DIVIDES_MOD_0, DIV_POS
             EL k (t ++ DILATE e 0 n l)
           = EL (k - m) (DILATE e 0 n l)             by EL_APPEND, m <= k
           = EL (k DIV m - 1) l                      by induction hypothesis, (k - m) MOD m = 0
           = EL (PRE (k DIV m)) l                    by PRE_SUB1
           = EL (k DIV m) (h::l)                     by EL_CONS, 0 < k DIV m
          If k MOD m <> 0,
             EL k (t ++ DILATE e 0 n l)
           = EL (k - m) (DILATE e 0 n l)             by EL_APPEND, n <= k
           = e                                       by induction hypothesis, (k - m) MOD n <> 0
*)
Theorem DILATE_0_EL:
  !l e n k.
     k < LENGTH (DILATE e 0 n l) ==>
     EL k (DILATE e 0 n l) = if k MOD (SUC n) = 0 then EL (k DIV (SUC n)) l
                             else e
Proof
  ntac 3 strip_tac >>
  `0 < SUC n` by decide_tac >>
  qabbrev_tac `m = SUC n` >>
  Induct_on `l` >- rw[] >>
  rpt strip_tac >>
  `LENGTH (DILATE e 0 n [h]) = 1` by rw[DILATE_SING] >>
  `LENGTH (DILATE e 0 n (h::l)) = SUC (m * LENGTH l)` by rw[DILATE_0_LENGTH, Abbr`m`] >>
  Cases_on `l = []` >| [
    `k = 0` by rw[] >>
    `k MOD m = 0` by rw[] >>
    `k DIV m = 0` by rw[ZERO_DIV] >>
    rw_tac std_ss[DILATE_SING],
    qabbrev_tac `t = h::GENLIST (K e) n` >>
    `DILATE e 0 n (h::l) = t ++ DILATE e 0 n l` by rw[DILATE_0_CONS, Abbr`t`] >>
    `m = LENGTH t` by rw[Abbr`t`] >>
    Cases_on `k < m` >| [
      `k MOD m = k` by rw[] >>
      `EL k (DILATE e 0 n (h::l)) = EL k t` by rw[EL_APPEND] >>
      Cases_on `k = 0` >| [
        `EL 0 t = h` by rw[Abbr`t`] >>
        rw[ZERO_DIV],
        `PRE m = n` by rw[Abbr`m`] >>
        `PRE k < n` by decide_tac >>
        `EL k t = EL (PRE k) (GENLIST (K e) n)` by rw[EL_CONS, Abbr`t`] >>
        `_ = (K e) (PRE k)` by rw[EL_GENLIST] >>
        rw[]
      ],
      `m <= k` by decide_tac >>
      `EL k (t ++ DILATE e 0 n l) = EL (k - m) (DILATE e 0 n l)`
        by simp[EL_APPEND] >>
      `k - m < LENGTH (DILATE e 0 n l)`
        by (trace ("BasicProvers.var_eq_old", 1)(rw[DILATE_0_LENGTH])) >>
      `(k - m) MOD m = k MOD m` by simp[SUB_MOD] >>
      `(k - m) DIV m = k DIV m - 1` by simp[SUB_DIV] >>
      Cases_on `k MOD m = 0` >| [
        `0 < k DIV m` by rw[DIVIDES_MOD_0, DIV_POS] >>
        `EL (k - m) (DILATE e 0 n l) = EL (k DIV m - 1) l` by rw[] >>
        `_ = EL (PRE (k DIV m)) l` by rw[PRE_SUB1] >>
        `_ = EL (k DIV m) (h::l)` by rw[EL_CONS] >>
        rw[],
        `EL (k - m) (DILATE e 0 n l)  = e`
          by trace ("BasicProvers.var_eq_old", 1)(rw[]) >>
        rw[]
      ]
    ]
  ]
QED

(* This is a milestone theorem. *)

(* Theorem: (DILATE e 0 n l = []) <=> (l = []) *)
(* Proof:
   If part: DILATE e 0 n l = [] ==> l = []
      By contradiction, suppose l <> [].
      If n = 0,
         Then DILATE e n 0 l = l     by DILATE_0_0
         This contradicts DILATE e n 0 l = [].
      If n <> 0,
         Then LENGTH (DILATE e 0 n l)
            = SUC (SUC n * PRE (LENGTH l))  by DILATE_0_LENGTH
            <> 0                     by SUC_NOT
         So (DILATE e 0 n l) <> []   by LENGTH_NIL
         This contradicts DILATE e 0 n l = []
   Only-if part: l = [] ==> DILATE e 0 n l = []
      True by DILATE_NIL
*)
val DILATE_0_EQ_NIL = store_thm(
  "DILATE_0_EQ_NIL",
  ``!l e n. (DILATE e 0 n l = []) <=> (l = [])``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  Cases_on `n = 0` >| [
    `DILATE e 0 0 l = l` by rw[GSYM DILATE_0_0] >>
    metis_tac[],
    `LENGTH (DILATE e 0 n l) = SUC (SUC n * PRE (LENGTH l))` by rw[DILATE_0_LENGTH] >>
    `LENGTH (DILATE e 0 n l) <> 0` by decide_tac >>
    metis_tac[LENGTH_EQ_0]
  ]);

(* Theorem: LAST (DILATE e 0 n l) = LAST l *)
(* Proof:
   If l = [],
        LAST (DILATE e 0 n [])
      = LAST []                by DILATE_NIL
   If l <> [],
      If n = 0,
        LAST (DILATE e 0 0 l)
      = LAST l                 by DILATE_0_0
      If n <> 0,
        Then DILATE e 0 n l <> []            by DILATE_0_EQ_NIL
          or LENGTH (DILATE e 0 n l) <> 0    by LENGTH_NIL
        Let m = SUC n, then 0 < m            by LESS_0
        Note PRE (LENGTH (DILATE e 0 n l))
           = PRE (SUC (m * PRE (LENGTH l)))  by DILATE_0_LENGTH
           = m * PRE (LENGTH l)              by PRE
        Let k = PRE (LENGTH (DILATE e 0 n l)).
        Then k < LENGTH (DILATE e 0 n l)     by PRE x < x
         and k MOD m = 0                     by MOD_EQ_0, MULT_COMM, 0 < m
         and k DIV m = PRE (LENGTH l)        by MULT_DIV, MULT_COMM

        LAST (DILATE e 0 n l)
      = EL k (DILATE e 0 n l)                by LAST_EL
      = EL (k DIV m) l                       by DILATE_0_EL
      = EL (PRE (LENGTH l)) l                by above
      = LAST l                               by LAST_EL
*)
val DILATE_0_LAST = store_thm(
  "DILATE_0_LAST",
  ``!l e n. LAST (DILATE e 0 n l) = LAST l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  Cases_on `n = 0` >-
  rw[DILATE_0_0] >>
  `0 < n` by decide_tac >>
  `DILATE e 0 n l <> []` by rw[DILATE_0_EQ_NIL] >>
  `LENGTH (DILATE e 0 n l) <> 0` by metis_tac[LENGTH_NIL] >>
  qabbrev_tac `k = PRE (LENGTH (DILATE e 0 n l))` >>
  rw[LAST_EL] >>
  `0 < SUC n` by decide_tac >>
  qabbrev_tac `m = SUC n` >>
  `k = m * PRE (LENGTH l)` by rw[DILATE_0_LENGTH, Abbr`k`, Abbr`m`] >>
  `k MOD m = 0` by metis_tac[MOD_EQ_0, MULT_COMM] >>
  `k DIV m = PRE (LENGTH l)` by metis_tac[MULT_DIV, MULT_COMM] >>
  `k < LENGTH (DILATE e 0 n l)` by simp[Abbr`k`] >>
  Q.RM_ABBREV_TAC ‘k’ >>
  rw[DILATE_0_EL]);

(* ------------------------------------------------------------------------- *)
(* Range Conjunction and Disjunction                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: a <= j /\ j <= a <=> (j = a) *)
(* Proof: trivial by arithmetic. *)
val every_range_sing = store_thm(
  "every_range_sing",
  ``!a j. a <= j /\ j <= a <=> (j = a)``,
  decide_tac);

(* Theorem: a <= b ==>
    ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ !j. a + 1 <= j /\ j <= b ==> f j)) *)
(* Proof:
   If part: !j. a <= j /\ j <= b ==> f j ==>
              f a /\ !j. a + 1 <= j /\ j <= b ==> f j
      This is trivial since a + 1 = SUC a.
   Only-if part: f a /\ !j. a + 1 <= j /\ j <= b ==> f j ==>
                 !j. a <= j /\ j <= b ==> f j
      Note a <= j <=> a = j or a < j      by arithmetic
      If a = j, this is trivial.
      If a < j, then a + 1 <= j, also trivial.
*)
val every_range_cons = store_thm(
  "every_range_cons",
  ``!f a b. a <= b ==>
    ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ !j. a + 1 <= j /\ j <= b ==> f j))``,
  rw[EQ_IMP_THM] >>
  `(a = j) \/ (a < j)` by decide_tac >-
  fs[] >>
  fs[]);

(* Theorem: ?j. a <= j /\ j <= a <=> (j = a) *)
(* Proof: trivial by arithmetic. *)
val exists_range_sing = store_thm(
  "exists_range_sing",
  ``!a. ?j. a <= j /\ j <= a <=> (j = a)``,
  metis_tac[LESS_EQ_REFL]);

(* Theorem: a <= b ==>
    ((?j. a <= j /\ j <= b /\ f j) <=> (f a \/ ?j. a + 1 <= j /\ j <= b /\ f j)) *)
(* Proof:
   If part: ?j. a <= j /\ j <= b /\ f j ==>
              f a \/ ?j. a + 1 <= j /\ j <= b /\ f j
      This is trivial since a + 1 = SUC a.
   Only-if part: f a /\ ?j. a + 1 <= j /\ j <= b /\ f j ==>
                 ?j. a <= j /\ j <= b /\ f j
      Note a <= j <=> a = j or a < j      by arithmetic
      If a = j, this is trivial.
      If a < j, then a + 1 <= j, also trivial.
*)
val exists_range_cons = store_thm(
  "exists_range_cons",
  ``!f a b. a <= b ==>
    ((?j. a <= j /\ j <= b /\ f j) <=> (f a \/ ?j. a + 1 <= j /\ j <= b /\ f j))``,
  rw[EQ_IMP_THM] >| [
    `(a = j) \/ (a < j)` by decide_tac >-
    fs[] >>
    `a + 1 <= j` by decide_tac >>
    metis_tac[],
    metis_tac[LESS_EQ_REFL],
    `a <= j` by decide_tac >>
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Helper Function Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   x == y (f)          = fequiv x y f
   RISING f            = !x:num. x <= f x
   FALLING f           = !x:num. f x <= x
   SQRT n              = ROOT 2 n
   LOG2 n              = LOG 2 n
   coprime x y         = gcd x y = 1
   PAIRWISE_COPRIME s  = !x y. x IN s /\ y IN s /\ x <> y ==> coprime x y
   tops b n            = b ** n - 1
   nines n             = tops 10 n
*)
(* Definitions and Theorems (# are exported):

   Function Equivalence as Relation:
   fequiv_def         |- !x y f. fequiv x y f <=> (f x = f y)
#  fequiv_refl        |- !f x. (x == x) f
   fequiv_sym         |- !f x y. (x == y) f ==> (y == x) f
   fequiv_trans       |- !f x y z. (x == y) f /\ (y == z) f ==> (x == z) f
   fequiv_equiv_class |- !f. (\x y. (x == y) f) equiv_on univ(:'a)

   Function-based Equivalence:
   feq_def             |- !f x y. feq f x y <=> (f x = f y)
   feq_class_def       |- !s f n. feq_class f s n = {x | x IN s /\ (f x = n)}
   feq_class_element   |- !f s n x. x IN feq_class f s n <=> x IN s /\ (f x = n)
   feq_class_property  |- !f s x. feq_class f s (f x) = {y | y IN s /\ feq f x y}
   feq_class_fun       |- !f s. feq_class f s o f = (\x. {y | y IN s /\ feq f x y})


   feq_equiv                  |- !s f. feq f equiv_on s
   feq_partition              |- !s f. partition (feq f) s = IMAGE (feq_class f s o f) s
   feq_partition_element      |- !s f t. t IN partition (feq f) s <=>
                                 ?z. z IN s /\ !x. x IN t <=> x IN s /\ (f x = f z)
   feq_class_eq_preimage      |- !f s. feq_class f s = preimage f s
   feq_partition_by_preimage  |- !f s. partition (feq f) s = IMAGE (preimage f s o f) s
   feq_sum_over_partition     |- !s. FINITE s ==> !f g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s)

   finite_card_by_feq_partition   |- !s. FINITE s ==> !f. CARD s = SIGMA CARD (partition (feq f) s)
   finite_card_by_image_preimage  |- !s. FINITE s ==> !f. CARD s = SIGMA CARD (IMAGE (preimage f s o f) s)

   Function Iteration:
   FUNPOW_2            |- !f x. FUNPOW f 2 x = f (f x)
   FUNPOW_K            |- !n x c. FUNPOW (K c) n x = if n = 0 then x else c
   FUNPOW_MULTIPLE     |- !f k e. 0 < k /\ (FUNPOW f k e = e) ==> !n. FUNPOW f (n * k) e = e
   FUNPOW_MOD          |- !f k e. 0 < k /\ (FUNPOW f k e = e) ==> !n. FUNPOW f n e = FUNPOW f (n MOD k) e
   FUNPOW_COMM         |- !f m n x. FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x)
   FUNPOW_LE_RISING    |- !f m n. RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x
   FUNPOW_LE_FALLING   |- !f m n. FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x
   FUNPOW_LE_MONO      |- !f g. (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x
   FUNPOW_GE_MONO      |- !f g. (!x. f x <= g x) /\ MONO f ==> !n x. FUNPOW f n x <= FUNPOW g n x
   FUNPOW_SQ           |- !m n. FUNPOW (\n. SQ n) n m = m ** 2 ** n
   FUNPOW_SQ_MOD       |- !m n k. 0 < m /\ 0 < n ==> (FUNPOW (\n. SQ n MOD m) n k = k ** 2 ** n MOD m)
   FUNPOW_ADD1         |- !m n. FUNPOW SUC n m = m + n
   FUNPOW_SUB1         |- !m n. FUNPOW PRE n m = m - n
   FUNPOW_MUL          |- !b m n. FUNPOW ($* b) n m = m * b ** n
   FUNPOW_DIV          |- !b m n. 0 < b ==> FUNPOW (combin$C $DIV b) n m = m DIV b ** n
   FUNPOW_MAX          |- !m n k. 0 < n ==> (FUNPOW (\x. MAX x m) n k = MAX k m)
   FUNPOW_MIN          |- !m n k. 0 < n ==> (FUNPOW (\x. MIN x m) n k = MIN k m)
   FUNPOW_PAIR         |- !f g n x y. FUNPOW (\(x,y). (f x,g y)) n (x,y) = (FUNPOW f n x,FUNPOW g n y)
   FUNPOW_TRIPLE       |- !f g h n x y z. FUNPOW (\(x,y,z). (f x,g y,h z)) n (x,y,z) =
                                          (FUNPOW f n x,FUNPOW g n y,FUNPOW h n z)
   FUNPOW_closure      |- !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s

   Factorial:
   FACT_0              |- FACT 0 = 1
   FACT_1              |- FACT 1 = 1
   FACT_2              |- FACT 2 = 2
   FACT_EQ_1           |- !n. (FACT n = 1) <=> n <= 1
   FACT_GE_1           |- !n. 1 <= FACT n
   FACT_EQ_SELF        |- !n. (FACT n = n) <=> (n = 1) \/ (n = 2)
   FACT_GE_SELF        |- !n. 0 < n ==> n <= FACT n
   FACT_DIV            |- !n. 0 < n ==> (FACT (n - 1) = FACT n DIV n)
   FACT_EQ_PROD        |- !n. FACT n = PROD_SET (IMAGE SUC (count n))
   FACT_REDUCTION      |- !n m. m < n ==> (FACT n = PROD_SET (IMAGE SUC ((count n) DIFF (count m))) * (FACT m))
   PRIME_BIG_NOT_DIVIDES_FACT  |- !p k. prime p /\ k < p ==> ~(p divides (FACT k))

   Basic GCD, LCM Theorems:
   GCD_COMM            |- !a b. gcd a b = gcd b a
   LCM_SYM             |- !a b. lcm a b = lcm b a
   GCD_0               |- !x. (gcd 0 x = x) /\ (gcd x 0 = x)
   GCD_DIVIDES         |- !m n. 0 < n /\ 0 < m ==> 0 < gcd n m /\ (n MOD gcd n m = 0) /\ (m MOD gcd n m = 0)
   GCD_GCD             |- !m n. gcd n (gcd n m) = gcd n m
   GCD_LCM             |- !m n. gcd m n * lcm m n = m * n
   LCM_DIVISORS        |- !m n. m divides lcm m n /\ n divides lcm m n
   LCM_IS_LCM          |- !m n p. m divides p /\ n divides p ==> lcm m n divides p
   LCM_EQ_0            |- !m n. (lcm m n = 0) <=> (m = 0) \/ (n = 0)
   LCM_REF             |- !a. lcm a a = a
   LCM_DIVIDES         |- !n a b. a divides n /\ b divides n ==> lcm a b divides n
   GCD_POS             |- !m n. 0 < m \/ 0 < n ==> 0 < gcd m n
   LCM_POS             |- !m n. 0 < m /\ 0 < n ==> 0 < lcm m n
   divides_iff_gcd_fix |- !m n. n divides m <=> (gcd n m = n)
   divides_iff_lcm_fix |- !m n. n divides m <=> (lcm n m = m)
   FACTOR_OUT_PRIME    |- !n p. 0 < n /\ prime p /\ p divides n ==>
                          ?m. 0 < m /\ (p ** m) divides n /\ !k. coprime (p ** k) (n DIV p ** m)

   Consequences of Coprime:
   MOD_NONZERO_WHEN_GCD_ONE |- !n. 1 < n ==> !x. coprime n x ==> 0 < x /\ 0 < x MOD n
   PRODUCT_WITH_GCD_ONE     |- !n x y. coprime n x /\ coprime n y ==> coprime n (x * y)
   MOD_WITH_GCD_ONE         |- !n x. 0 < n /\ coprime n x ==> coprime n (x MOD n)
   GCD_ONE_PROPERTY         |- !n x. 1 < n /\ coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k
   GCD_MOD_MULT_INV         |- !n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
                                 ?y. 0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1)
   GEN_MULT_INV_DEF         |- !n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
                                     0 < GCD_MOD_MUL_INV n x /\ GCD_MOD_MUL_INV n x < n /\
                                     coprime n (GCD_MOD_MUL_INV n x) /\
                                     ((GCD_MOD_MUL_INV n x * x) MOD n = 1)

   More GCD and LCM Theorems:
   GCD_PROPERTY        |- !a b c. (c = gcd a b) <=> c divides a /\ c divides b /\
                               !x. x divides a /\ x divides b ==> x divides c
   GCD_ASSOC           |- !a b c. gcd a (gcd b c) = gcd (gcd a b) c
   GCD_ASSOC_COMM      |- !a b c. gcd a (gcd b c) = gcd b (gcd a c)
   LCM_PROPERTY        |- !a b c. (c = lcm a b) <=> a divides c /\ b divides c /\
                          !x. a divides x /\ b divides x ==> c divides x
   LCM_ASSOC           |- !a b c. lcm a (lcm b c) = lcm (lcm a b)
   LCM_ASSOC_COMM      |- !a b c. lcm a (lcm b c) = lcm b (lcm a c)
   GCD_SUB_L           |- !a b. b <= a ==> (gcd (a - b) b = gcd a b)
   GCD_SUB_R           |- !a b. a <= b ==> (gcd a (b - a) = gcd a b)
   LCM_EXCHANGE        |- !a b c. (a * b = c * (a - b)) ==> (lcm a b = lcm a c)
   LCM_COPRIME         |- !m n. coprime m n ==> (lcm m n = m * n)
   LCM_COMMON_FACTOR   |- !m n k. lcm (k * m) (k * n) = k * lcm m n
   LCM_COMMON_COPRIME  |- !a b. coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c
   GCD_MULTIPLE        |- !m n. 0 < n /\ (m MOD n = 0) ==> (gcd m n = n)
   GCD_MULTIPLE_ALT    |- !m n. gcd (m * n) n = n
   GCD_SUB_MULTIPLE    |- !a b k. k * a <= b ==> (gcd a b = gcd a (b - k * a))
   GCD_SUB_MULTIPLE_COMM
                       |- !a b k. k * a <= b ==> (gcd b a = gcd a (b - k * a))
   GCD_MOD             |- !m n. 0 < m ==> (gcd m n = gcd m (n MOD m))
   GCD_MOD_COMM        |- !m n. 0 < m ==> (gcd n m = gcd (n MOD m) m)
   GCD_EUCLID          |- !a b c. gcd a (b * a + c) = gcd a c
   GCD_REDUCE          |- !a b c. gcd (b * a + c) a = gcd a c

   Coprime Theorems:
   coprime_SUC         |- !n. coprime n (n + 1)
   coprime_PRE         |- !n. 0 < n ==> coprime (n - 1) n
   coprime_0L          |- !n. coprime 0 n <=> (n = 1)
   coprime_0R          |- !n. coprime n 0 <=> (n = 1)
   coprime_sym         |- !x y. coprime x y <=> coprime y x
   coprime_neq_1       |- !n k. coprime k n /\ n <> 1 ==> k <> 0
   coprime_gt_1        |- !n k. coprime k n /\ 1 < n ==> 0 < k
   coprime_exp                  |- !c m. coprime c m ==> !n. coprime (c ** n) m
   coprime_exp_comm             |- !a b. coprime a b ==> !n. coprime a (b ** n)
   coprime_iff_coprime_exp      |- !n. 0 < n ==> !a b. coprime a b <=> coprime a (b ** n)
   coprime_product_coprime      |- !x y z. coprime x z /\ coprime y z ==> coprime (x * y) z
   coprime_product_coprime_sym  |- !x y z. coprime z x /\ coprime z y ==> coprime z (x * y)
   coprime_product_coprime_iff  |- !x y z. coprime x z ==> (coprime y z <=> coprime (x * y) z)
   coprime_product_divides      |- !n a b. a divides n /\ b divides n /\ coprime a b ==> a * b divides n
   coprime_mod                  |- !m n. 0 < m /\ coprime m n ==> coprime m (n MOD m)
   coprime_mod_iff              |- !m n. 0 < m ==> (coprime m n <=> coprime m (n MOD m))
   coprime_not_divides          |- !m n. 1 < n /\ coprime n m ==> ~(n divides m)
   coprime_factor_not_divides   |- !n k. 1 < n /\ coprime n k ==>
                                   !p. 1 < p /\ p divides n ==> ~(p divides k)
   coprime_factor_coprime       |- !m n. m divides n ==> !k. coprime n k ==> coprime m k
   prime_not_divides_is_coprime |- !n p. prime p /\ ~(p divides n) ==> coprime p n
   prime_not_coprime_divides    |- !n p. prime p /\ ~(coprime p n) ==> p divides n
   coprime_prime_factor_coprime |- !n p. 1 < n /\ prime p /\ p divides n ==>
                                   !k. coprime n k ==> coprime p k
   coprime_all_le_imp_lt     |- !n. 1 < n ==> !m. (!j. 0 < j /\ j <= m ==> coprime n j) ==> m < n
   coprime_condition         |- !m n. (!j. 1 < j /\ j <= m ==> ~(j divides n)) <=>
                                      !j. 1 < j /\ j <= m ==> coprime j n
   coprime_by_le_not_divides |- !m n. 1 < m /\ (!j. 1 < j /\ j <= m ==> ~(j divides n)) ==> coprime m n
   prime_coprime_all_lt      |- !n. prime n ==> !m. 0 < m /\ m < n ==> coprime n m
   prime_coprime_all_less    |- !m n. prime n /\ m < n ==> !j. 0 < j /\ j <= m ==> coprime n j
   prime_iff_coprime_all_lt  |- !n. prime n <=> 1 < n /\ !j. 0 < j /\ j < n ==> coprime n j
   prime_iff_no_proper_factor|- !n. prime n <=> 1 < n /\ !j. 1 < j /\ j < n ==> ~(j divides n)
   prime_always_bigger       |- !n. ?p. prime p /\ n < p
   divides_imp_coprime_with_successor   |- !m n. n divides m ==> coprime n (SUC m)
   divides_imp_coprime_with_predecessor |- !m n. 0 < m /\ n divides m ==> coprime n (PRE m)
   gcd_coprime_cancel        |- !m n p. coprime p n ==> (gcd (p * m) n = gcd m n)
   primes_coprime            |- !p q. prime p /\ prime q /\ p <> q ==> coprime p q
   every_coprime_prod_set_coprime       |- !s. FINITE s ==>
                                !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s)

   Pairwise Coprime Property:
   pairwise_coprime_insert   |- !s e. e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==>
                                      (!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s
   pairwise_coprime_prod_set_subset_divides
                             |- !s. FINITE s /\ PAIRWISE_COPRIME s ==>
                                !t. t SUBSET s ==> PROD_SET t divides PROD_SET s
   pairwise_coprime_partition_coprime    |- !s. FINITE s /\ PAIRWISE_COPRIME s ==>
                             !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v)
   pairwise_coprime_prod_set_partition  |- !s. FINITE s /\ PAIRWISE_COPRIME s ==>
                                           !u v. (s = u UNION v) /\ DISJOINT u v ==>
                             (PROD_SET s = PROD_SET u * PROD_SET v) /\ coprime (PROD_SET u) (PROD_SET v)

   GCD divisibility condition of Power Predecessors:
   power_predecessor_division_eqn  |- !t m n. 0 < t /\ m <= n ==>
                                       tops t n = t ** (n - m) * tops t m + tops t (n - m)
   power_predecessor_division_alt  |- !t m n. 0 < t /\ m <= n ==>
                                       tops t n - t ** (n - m) * tops t m = tops t (n - m)
   power_predecessor_gcd_reduction |- !t n m. m <= n ==>
                                      (gcd (tops t n) (tops t m) = gcd (tops t m) (tops t (n - m)))
   power_predecessor_gcd_identity  |- !t n m. gcd (tops t n) (tops t m) = tops t (gcd n m)
   power_predecessor_divisibility  |- !t n m. 1 < t ==> (tops t n divides tops t m <=> n divides m)
   power_predecessor_divisor       |- !t n. t - 1 divides tops t n

   nines_division_eqn  |- !m n. m <= n ==> nines n = 10 ** (n - m) * nines m + nines (n - m): thm
   nines_division_alt  |- !m n. m <= n ==> nines n - 10 ** (n - m) * nines m = nines (n - m): thm
   nines_gcd_reduction |- !n m. m <= n ==> gcd (nines n) (nines m) = gcd (nines m) (nines (n - m)): thm
   nines_gcd_identity  |- !n m. gcd (nines n) (nines m) = nines (gcd n m): thm
   nines_divisibility  |- !n m. nines n divides nines m <=> n divides m: thm
   nines_divisor       |- !n. 9 divides nines n: thm

   GCD involving Powers:
   prime_divides_prime_power  |- !m n k. prime m /\ prime n /\ m divides n ** k ==> (m = n)
   prime_power_factor         |- !n p. 0 < n /\ prime p ==> ?q m. (n = p ** m * q) /\ coprime p q
   prime_power_divisor        |- !p n a. prime p /\ a divides p ** n ==> ?j. j <= n /\ (a = p ** j)
   prime_powers_eq      |- !p q. prime p /\ prime q ==> !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n)
   prime_powers_coprime |- !p q. prime p /\ prime q /\ p <> q ==> !m n. coprime (p ** m) (q ** n)
   prime_powers_divide  |- !p q. prime p /\ prime q ==>
                           !m n. 0 < m ==> (p ** m divides q ** n <=> (p = q) /\ m <= n)
   gcd_powers           |- !b m n. gcd (b ** m) (b ** n) = b ** MIN m n
   lcm_powers           |- !b m n. lcm (b ** m) (b ** n) = b ** MAX m n
   coprime_power_and_power_predecessor   |- !b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m - 1)
   coprime_power_and_power_successor     |- !b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m + 1)

   Useful Theorems:
   PRIME_EXP_FACTOR    |- !p q n. prime p /\ q divides p ** n ==> (q = 1) \/ p divides q
   FACT_MOD_PRIME      |- !p n. prime p /\ n < p ==> FACT n MOD p <> 0:
*)

(* ------------------------------------------------------------------------- *)
(* Function Equivalence as Relation                                          *)
(* ------------------------------------------------------------------------- *)

(* For function f on a domain D, x, y in D are "equal" if f x = f y. *)
val fequiv_def = Define`
  fequiv x y f <=> (f x = f y)
`;

val _ = overload_on ("==", ``fequiv``);
val _ = set_fixity "==" (Infix(NONASSOC, 450));

(* Theorem: [Reflexive] (x == x) f *)
(* Proof: by definition,
   and f x = f x.
*)
val fequiv_refl = store_thm(
  "fequiv_refl",
  ``!f x. (x == x) f``,
  rw_tac std_ss[fequiv_def]);

(* export simple definition *)
val _ = export_rewrites ["fequiv_refl"];

(* Theorem: [Symmetric] (x == y) f ==> (y == x) f *)
(* Proof: by defintion,
   and f x = f y means the same as f y = f x.
*)
val fequiv_sym = store_thm(
  "fequiv_sym",
  ``!f x y. (x == y) f ==> (y == x) f``,
  rw_tac std_ss[fequiv_def]);

(* no export of commutativity *)

(* Theorem: [Transitive] (x == y) f /\ (y == z) f ==> (x == z) f *)
(* Proof: by defintion,
   and f x = f y
   and f y = f z
   implies f x = f z.
*)
val fequiv_trans = store_thm(
  "fequiv_trans",
  ``!f x y z. (x == y) f /\ (y == z) f ==> (x == z) f``,
  rw_tac std_ss[fequiv_def]);

(* Theorem: fequiv (==) is an equivalence relation on the domain. *)
(* Proof: by reflexive, symmetric and transitive. *)
val fequiv_equiv_class = store_thm(
  "fequiv_equiv_class",
  ``!f. (\x y. (x == y) f) equiv_on univ(:'a)``,
  rw_tac std_ss[equiv_on_def, fequiv_def, EQ_IMP_THM]);

(* ------------------------------------------------------------------------- *)
(* Function-based Equivalence                                                *)
(* ------------------------------------------------------------------------- *)

(* Define an equivalence relation based on a function *)
val feq_def = Define `
   feq f x y = (f x = f y)
`;

(* Define equivalence class based on a function *)
val feq_class_def = Define `
   feq_class f s n = {x | x IN s /\ (f x = n)}
`;

(* Theorem: x IN feq_class f s n <=> x IN s /\ (f x = n) *)
(* Proof: by feq_class_def *)
val feq_class_element = store_thm(
  "feq_class_element",
  ``!f s n x. x IN feq_class f s n <=> x IN s /\ (f x = n)``,
  rw[feq_class_def]);

(* Note:
    y IN equiv_class (feq f) s x
<=> y IN s /\ (feq f x y)      by equiv_class_element
<=> y IN s /\ (f x = f y)      by feq_def
*)

(* Theorem: feq_class f s (f x) = equiv_class (feq f) s x *)
(* Proof:
     feq_class f s (f x)
   = {y | y IN s /\ (f y = f x)}    by feq_class_def
   = {y | y IN s /\ (f x = f y)}
   = {y | y IN s /\ (feq f x y)}    by feq_def
   = equiv_class (feq f) s x        by notation
*)
val feq_class_property = store_thm(
  "feq_class_property",
  ``!f s x. feq_class f s (f x) = equiv_class (feq f) s x``,
  (rw[feq_class_def, feq_def, EXTENSION] >> metis_tac[]));

(* Theorem: (feq_class f s) o f = equiv_class (feq f) s *)
(* Proof: by FUN_EQ_THM, feq_class_property *)
val feq_class_fun = store_thm(
  "feq_class_fun",
  ``!f s. (feq_class f s) o f = equiv_class (feq f) s``,
  rw[FUN_EQ_THM, feq_class_property]);

(* Theorem: feq f equiv_on s *)
(* Proof: by equiv_on_def, feq_def *)
val feq_equiv = store_thm(
  "feq_equiv",
  ``!s f. feq f equiv_on s``,
  rw[equiv_on_def, feq_def] >>
  metis_tac[]);

(* Theorem: partition (feq f) s = IMAGE ((feq_class f s) o f) s *)
(* Proof:
   Use partition_def |> ISPEC ``feq f`` |> ISPEC ``(s:'a -> bool)``;

    partition (feq f) s
  = {t | ?x. x IN s /\ (t = {y | y IN s /\ feq f x y})}     by partition_def
  = {t | ?x. x IN s /\ (t = {y | y IN s /\ (f x = f y)})}   by feq_def
  = {t | ?x. x IN s /\ (t = feq_class f s (f x))}           by feq_class_def
  = {feq_class f s (f x) | x | x IN s }                     by rewriting
  = IMAGE (feq_class f s) (IMAGE f s)                       by IN_IMAGE
  = IMAGE ((feq_class f s) o f) s                           by IMAGE_COMPOSE
*)
val feq_partition = store_thm(
  "feq_partition",
  ``!s f. partition (feq f) s = IMAGE ((feq_class f s) o f) s``,
  (rw[partition_def, feq_def, feq_class_def, EXTENSION, EQ_IMP_THM] >> metis_tac[]));

(* Theorem: t IN partition (feq f) s <=> ?z. z IN s /\ (!x. x IN t <=> x IN s /\ (f x = f z)) *)
(* Proof: by feq_partition, feq_class_def, EXTENSION *)
val feq_partition_element = store_thm(
  "feq_partition_element",
  ``!s f t. t IN partition (feq f) s <=> ?z. z IN s /\ (!x. x IN t <=> x IN s /\ (f x = f z))``,
  (rw[feq_partition, feq_class_def, EXTENSION] >> metis_tac[]));

(* Theorem: feq_class f s = preimage f s *)
(* Proof:
     feq_class f s n
   = {x | x IN s /\ (f x = n)}          by feq_class_def
   = preimage f s n                     by preimage_def
   Hence feq_class f s = preimage f s   by FUN_EQ_THM
*)
val feq_class_eq_preimage = store_thm(
  "feq_class_eq_preimage",
  ``!f s. feq_class f s = preimage f s``,
  rw[feq_class_def, preimage_def, FUN_EQ_THM]);

(* Theorem: partition (feq f) s = IMAGE (preimage f s o f) s *)
(* Proof:
       x IN partition (feq f) s
   <=> ?z. z IN s /\ !j. j IN x <=> j IN s /\ (f j = f z)      by feq_partition_element
   <=> ?z. z IN s /\ !j. j IN x <=> j IN (preimage f s (f z))  by preimage_element
   <=> ?z. z IN s /\ (x = preimage f s (f z))                  by EXTENSION
   <=> ?z. z IN s /\ (x = (preimage f s o f) z)                by composition (o_THM)
   <=> x IN IMAGE (preimage f s o f) s                         by IN_IMAGE
   Hence partition (feq f) s = IMAGE (preimage f s o f) s      by EXTENSION

   or,
     partition (feq f) s
   = IMAGE (feq_class f s o f) s     by feq_partition
   = IMAGE (preiamge f s o f) s      by feq_class_eq_preimage
*)
val feq_partition_by_preimage = store_thm(
  "feq_partition_by_preimage",
  ``!f s. partition (feq f) s = IMAGE (preimage f s o f) s``,
  rw[feq_partition, feq_class_eq_preimage]);

(* Theorem: FINITE s ==> !f g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s) *)
(* Proof:
   Since (feq f) equiv_on s   by feq_equiv
   Hence !g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s)  by set_sigma_by_partition
*)
val feq_sum_over_partition = store_thm(
  "feq_sum_over_partition",
  ``!s. FINITE s ==> !f g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s)``,
  rw[feq_equiv, set_sigma_by_partition]);

(* Theorem: FINITE s ==> !f. CARD s = SIGMA CARD (partition (feq f) s) *)
(* Proof:
   Note feq equiv_on s   by feq_equiv
   The result follows    by partition_CARD
*)
val finite_card_by_feq_partition = store_thm(
  "finite_card_by_feq_partition",
  ``!s. FINITE s ==> !f. CARD s = SIGMA CARD (partition (feq f) s)``,
  rw[feq_equiv, partition_CARD]);

(* Theorem: FINITE s ==> !f. CARD s = SIGMA CARD (IMAGE ((preimage f s) o f) s) *)
(* Proof:
   Note (feq f) equiv_on s                       by feq_equiv
        CARD s
      = SIGMA CARD (partition (feq f) s)         by partition_CARD
      = SIGMA CARD (IMAGE (preimage f s o f) s)  by feq_partition_by_preimage
*)
val finite_card_by_image_preimage = store_thm(
  "finite_card_by_image_preimage",
  ``!s. FINITE s ==> !f. CARD s = SIGMA CARD (IMAGE ((preimage f s) o f) s)``,
  rw[feq_equiv, partition_CARD, GSYM feq_partition_by_preimage]);

(* ------------------------------------------------------------------------- *)
(* Function Iteration                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FUNPOW f 2 x = f (f x) *)
(* Proof: by definition. *)
val FUNPOW_2 = store_thm(
  "FUNPOW_2",
  ``!f x. FUNPOW f 2 x = f (f x)``,
  simp_tac bool_ss [FUNPOW, TWO, ONE]);

(* Theorem: FUNPOW (K c) n x = if n = 0 then x else c *)
(* Proof:
   By induction on n.
   Base: !x c. FUNPOW (K c) 0 x = if 0 = 0 then x else c
           FUNPOW (K c) 0 x
         = x                         by FUNPOW
         = if 0 = 0 then x else c    by 0 = 0 is true
   Step: !x c. FUNPOW (K c) n x = if n = 0 then x else c ==>
         !x c. FUNPOW (K c) (SUC n) x = if SUC n = 0 then x else c
           FUNPOW (K c) (SUC n) x
         = FUNPOW (K c) n ((K c) x)         by FUNPOW
         = if n = 0 then ((K c) c) else c   by induction hypothesis
         = if n = 0 then c else c           by K_THM
         = c                                by either case
         = if SUC n = 0 then x else c       by SUC n = 0 is false
*)
val FUNPOW_K = store_thm(
  "FUNPOW_K",
  ``!n x c. FUNPOW (K c) n x = if n = 0 then x else c``,
  Induct >-
  rw[] >>
  metis_tac[FUNPOW, combinTheory.K_THM, SUC_NOT_ZERO]);

(* Theorem: 0 < k /\ FUNPOW f k e = e  ==> !n. FUNPOW f (n*k) e = e *)
(* Proof:
   By induction on n:
   Base case: FUNPOW f (0 * k) e = e
     FUNPOW f (0 * k) e
   = FUNPOW f 0 e          by arithmetic
   = e                     by FUNPOW_0
   Step case: FUNPOW f (n * k) e = e ==> FUNPOW f (SUC n * k) e = e
     FUNPOW f (SUC n * k) e
   = FUNPOW f (k + n * k) e         by arithmetic
   = FUNPOW f k (FUNPOW (n * k) e)  by FUNPOW_ADD.
   = FUNPOW f k e                   by induction hypothesis
   = e                              by given
*)
val FUNPOW_MULTIPLE = store_thm(
  "FUNPOW_MULTIPLE",
  ``!f k e. 0 < k /\ (FUNPOW f k e = e)  ==> !n. FUNPOW f (n*k) e = e``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[MULT_COMM, MULT_SUC, FUNPOW_ADD]);

(* Theorem: 0 < k /\ FUNPOW f k e = e  ==> !n. FUNPOW f n e = FUNPOW f (n MOD k) e *)
(* Proof:
     FUNPOW f n e
   = FUNPOW f ((n DIV k) * k + (n MOD k)) e       by division algorithm
   = FUNPOW f ((n MOD k) + (n DIV k) * k) e       by arithmetic
   = FUNPOW f (n MOD k) (FUNPOW (n DIV k) * k e)  by FUNPOW_ADD
   = FUNPOW f (n MOD k) e                         by FUNPOW_MULTIPLE
*)
val FUNPOW_MOD = store_thm(
  "FUNPOW_MOD",
  ``!f k e. 0 < k /\ (FUNPOW f k e = e)  ==> !n. FUNPOW f n e = FUNPOW f (n MOD k) e``,
  rpt strip_tac >>
  `n = (n MOD k) + (n DIV k) * k` by metis_tac[DIVISION, ADD_COMM] >>
  metis_tac[FUNPOW_ADD, FUNPOW_MULTIPLE]);

(* Theorem: FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x) *)
(* Proof: by FUNPOW_ADD, ADD_COMM *)
Theorem FUNPOW_COMM:
  !f m n x. FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x)
Proof
  metis_tac[FUNPOW_ADD, ADD_COMM]
QED

(* Overload a RISING function *)
val _ = overload_on ("RISING", ``\f. !x:num. x <= f x``);

(* Overload a FALLING function *)
val _ = overload_on ("FALLING", ``\f. !x:num. f x <= x``);

(* Theorem: RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x *)
(* Proof:
   By induction on n.
   Base: !m. m <= 0 ==> !x. FUNPOW f m x <= FUNPOW f 0 x
      Note m = 0, and FUNPOW f 0 x <= FUNPOW f 0 x.
   Step:  !m. RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x ==>
          !m. m <= SUC n ==> FUNPOW f m x <= FUNPOW f (SUC n) x
      Note m <= n or m = SUC n.
      If m = SUC n, this is trivial.
      If m <= n,
             FUNPOW f m x
          <= FUNPOW f n x            by induction hypothesis
          <= f (FUNPOW f n x)        by RISING f
           = FUNPOW f (SUC n) x      by FUNPOW_SUC
*)
val FUNPOW_LE_RISING = store_thm(
  "FUNPOW_LE_RISING",
  ``!f m n. RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `(m <= n) \/ (m = SUC n)` by decide_tac >| [
    `FUNPOW f m x <= FUNPOW f n x` by rw[] >>
    `FUNPOW f n x <= f (FUNPOW f n x)` by rw[] >>
    `f (FUNPOW f n x) = FUNPOW f (SUC n) x` by rw[FUNPOW_SUC] >>
    decide_tac,
    rw[]
  ]);

(* Theorem: FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x *)
(* Proof:
   By induction on n.
   Base: !m. m <= 0 ==> !x. FUNPOW f 0 x <= FUNPOW f m x
      Note m = 0, and FUNPOW f 0 x <= FUNPOW f 0 x.
   Step:  !m. FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x ==>
          !m. m <= SUC n ==> FUNPOW f (SUC n) x <= FUNPOW f m x
      Note m <= n or m = SUC n.
      If m = SUC n, this is trivial.
      If m <= n,
            FUNPOW f (SUC n) x
          = f (FUNPOW f n x)         by FUNPOW_SUC
         <= FUNPOW f n x             by FALLING f
         <= FUNPOW f m x             by induction hypothesis
*)
val FUNPOW_LE_FALLING = store_thm(
  "FUNPOW_LE_FALLING",
  ``!f m n. FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `(m <= n) \/ (m = SUC n)` by decide_tac >| [
    `FUNPOW f (SUC n) x = f (FUNPOW f n x)` by rw[FUNPOW_SUC] >>
    `f (FUNPOW f n x) <= FUNPOW f n x` by rw[] >>
    `FUNPOW f n x <= FUNPOW f m x` by rw[] >>
    decide_tac,
    rw[]
  ]);

(* Theorem: (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 x <= FUNPOW g 0 x
         FUNPOW f 0 x          by FUNPOW_0
       = x
       <= x = FUNPOW g 0 x     by FUNPOW_0
   Step: FUNPOW f n x <= FUNPOW g n x ==> FUNPOW f (SUC n) x <= FUNPOW g (SUC n) x
         FUNPOW f (SUC n) x
       = f (FUNPOW f n x)      by FUNPOW_SUC
      <= g (FUNPOW f n x)      by !x. f x <= g x
      <= g (FUNPOW g n x)      by induction hypothesis, MONO g
       = FUNPOW g (SUC n) x    by FUNPOW_SUC
*)
val FUNPOW_LE_MONO = store_thm(
  "FUNPOW_LE_MONO",
  ``!f g. (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `f (FUNPOW f n x) <= g (FUNPOW f n x)` by rw[] >>
  `g (FUNPOW f n x) <= g (FUNPOW g n x)` by rw[] >>
  decide_tac);

(* Note:
There is no FUNPOW_LE_RMONO. FUNPOW_LE_MONO says:
|- !f g. (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x
To compare the terms in these two sequences:
     x, f x, f (f x), f (f (f x)), ......
     x, g x, g (g x), g (g (g x)), ......
For the first pair:       x <= x.
For the second pair:    f x <= g x,      as g is cover.
For the third pair: f (f x) <= g (f x)   by g is cover,
                            <= g (g x)   by MONO g, and will not work if RMONO g.
*)

(* Theorem: (!x. f x <= g x) /\ MONO f ==> !n x. FUNPOW f n x <= FUNPOW g n x *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 x <= FUNPOW g 0 x
         FUNPOW f 0 x          by FUNPOW_0
       = x
       <= x = FUNPOW g 0 x     by FUNPOW_0
   Step: FUNPOW f n x <= FUNPOW g n x ==> FUNPOW f (SUC n) x <= FUNPOW g (SUC n) x
         FUNPOW f (SUC n) x
       = f (FUNPOW f n x)      by FUNPOW_SUC
      <= f (FUNPOW g n x)      by induction hypothesis, MONO f
      <= g (FUNPOW g n x)      by !x. f x <= g x
       = FUNPOW g (SUC n) x    by FUNPOW_SUC
*)
val FUNPOW_GE_MONO = store_thm(
  "FUNPOW_GE_MONO",
  ``!f g. (!x. f x <= g x) /\ MONO f ==> !n x. FUNPOW f n x <= FUNPOW g n x``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `f (FUNPOW f n x) <= f (FUNPOW g n x)` by rw[] >>
  `f (FUNPOW g n x) <= g (FUNPOW g n x)` by rw[] >>
  decide_tac);

(* Note: the name FUNPOW_SUC is taken:
FUNPOW_SUC  |- !f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)
*)

(* Theorem: FUNPOW SUC n m = m + n *)
(* Proof:
   By induction on n.
   Base: !m. FUNPOW SUC 0 m = m + 0
      LHS = FUNPOW SUC 0 m
          = m                  by FUNPOW_0
          = m + 0 = RHS        by ADD_0
   Step: !m. FUNPOW SUC n m = m + n ==>
         !m. FUNPOW SUC (SUC n) m = m + SUC n
       FUNPOW SUC (SUC n) m
     = FUNPOW SUC n (SUC m)    by FUNPOW
     = (SUC m) + n             by induction hypothesis
     = m + SUC n               by arithmetic
*)
val FUNPOW_ADD1 = store_thm(
  "FUNPOW_ADD1",
  ``!m n. FUNPOW SUC n m = m + n``,
  Induct_on `n` >>
  rw[FUNPOW]);

(* Theorem: FUNPOW PRE n m = m - n *)
(* Proof:
   By induction on n.
   Base: !m. FUNPOW PRE 0 m = m - 0
      LHS = FUNPOW PRE 0 m
          = m                  by FUNPOW_0
          = m + 0 = RHS        by ADD_0
   Step: !m. FUNPOW PRE n m = m - n ==>
         !m. FUNPOW PRE (SUC n) m = m - SUC n
       FUNPOW PRE (SUC n) m
     = FUNPOW PRE n (PRE m)    by FUNPOW
     = (PRE m) - n             by induction hypothesis
     = m - PRE n               by arithmetic
*)
val FUNPOW_SUB1 = store_thm(
  "FUNPOW_SUB1",
  ``!m n. FUNPOW PRE n m = m - n``,
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW]);

(* Theorem: FUNPOW ($* b) n m = m * b ** n *)
(* Proof:
   By induction on n.
   Base: !m. !m. FUNPOW ($* b) 0 m = m * b ** 0
      LHS = FUNPOW ($* b) 0 m
          = m                  by FUNPOW_0
          = m * 1              by MULT_RIGHT_1
          = m * b ** 0 = RHS   by EXP_0
   Step: !m. FUNPOW ($* b) n m = m * b ** n ==>
         !m. FUNPOW ($* b) (SUC n) m = m * b ** SUC n
       FUNPOW ($* b) (SUC n) m
     = FUNPOW ($* b) n (b * m)    by FUNPOW
     = b * m * b ** n             by induction hypothesis
     = m * (b * b ** n)           by arithmetic
     = m * b ** SUC n             by EXP
*)
val FUNPOW_MUL = store_thm(
  "FUNPOW_MUL",
  ``!b m n. FUNPOW ($* b) n m = m * b ** n``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW, EXP]);

(* Theorem: 0 < b ==> (FUNPOW (combin$C $DIV b) n m = m DIV (b ** n)) *)
(* Proof:
   By induction on n.
   Let f = combin$C $DIV b.
   Base: !m. FUNPOW f 0 m = m DIV b ** 0
      LHS = FUNPOW f 0 m
          = m                     by FUNPOW_0
          = m DIV 1               by DIV_1
          = m DIV (b ** 0) = RHS  by EXP_0
   Step: !m. FUNPOW f n m = m DIV b ** n ==>
         !m. FUNPOW f (SUC n) m = m DIV b ** SUC n
       FUNPOW f (SUC n) m
     = FUNPOW f n (f m)           by FUNPOW
     = FUNPOW f n (m DIV b)       by C_THM
     = (m DIV b) DIV (b ** n)     by induction hypothesis
     = m DIV (b * b ** n)         by DIV_DIV_DIV_MULT, 0 < b, 0 < b ** n
     = m DIV b ** SUC n           by EXP
*)
val FUNPOW_DIV = store_thm(
  "FUNPOW_DIV",
  ``!b m n. 0 < b ==> (FUNPOW (combin$C $DIV b) n m = m DIV (b ** n))``,
  strip_tac >>
  qabbrev_tac `f = combin$C $DIV b` >>
  Induct_on `n` >-
  rw[EXP_0] >>
  rpt strip_tac >>
  `FUNPOW f (SUC n) m = FUNPOW f n (m DIV b)` by rw[FUNPOW, Abbr`f`] >>
  `_ = (m DIV b) DIV (b ** n)` by rw[] >>
  `_ = m DIV (b * b ** n)` by rw[DIV_DIV_DIV_MULT] >>
  `_ = m DIV b ** SUC n` by rw[EXP] >>
  decide_tac);

(* Theorem: FUNPOW SQ n m = m ** (2 ** n) *)
(* Proof:
   By induction on n.
   Base: !m. FUNPOW (\n. SQ n) 0 m = m ** 2 ** 0
        FUNPOW SQ 0 m
      = m               by FUNPOW_0
      = m ** 1          by EXP_1
      = m ** 2 ** 0     by EXP_0
   Step: !m. FUNPOW (\n. SQ n) n m = m ** 2 ** n ==>
         !m. FUNPOW (\n. SQ n) (SUC n) m = m ** 2 ** SUC n
        FUNPOW (\n. SQ n) (SUC n) m
      = SQ (FUNPOW (\n. SQ n) n m)    by FUNPOW_SUC
      = SQ (m ** 2 ** n)              by induction hypothesis
      = (m ** 2 ** n) ** 2            by EXP_2
      = m ** (2 * 2 ** n)             by EXP_EXP_MULT
      = m ** 2 ** SUC n               by EXP
*)
val FUNPOW_SQ = store_thm(
  "FUNPOW_SQ",
  ``!m n. FUNPOW SQ n m = m ** (2 ** n)``,
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW_SUC, GSYM EXP_EXP_MULT, EXP]);

(* Theorem: 0 < m /\ 0 < n ==> (FUNPOW (\n. (n * n) MOD m) n k = (k ** 2 ** n) MOD m) *)
(* Proof:
   Lef f = (\n. SQ n MOD m).
   By induction on n.
   Base: !k. 0 < m /\ 0 < 0 ==> FUNPOW f 0 k = k ** 2 ** 0 MOD m
      True since 0 < 0 = F.
   Step: !k. 0 < m /\ 0 < n ==> FUNPOW f n k = k ** 2 ** n MOD m ==>
         !k. 0 < m /\ 0 < SUC n ==> FUNPOW f (SUC n) k = k ** 2 ** SUC n MOD m
     If n = 1,
       FUNPOW f (SUC 0) k
     = FUNPOW f 1 k             by ONE
     = f k                      by FUNPOW_1
     = SQ k MOD m               by notation
     = (k ** 2) MOD m           by EXP_2
     = (k ** (2 ** 1)) MOD m    by EXP_1
     If n <> 0,
       FUNPOW f (SUC n) k
     = f (FUNPOW f n k)         by FUNPOW_SUC
     = f (k ** 2 ** n MOD m)    by induction hypothesis
     = (k ** 2 ** n MOD m) * (k ** 2 ** n MOD m) MOD m     by notation
     = (k ** 2 ** n * k ** 2 ** n) MOD m                   by MOD_TIMES2
     = (k ** (2 ** n + 2 ** n)) MOD m          by EXP_BASE_MULT
     = (k ** (2 * 2 ** n)) MOD m               by arithmetic
     = (k ** 2 ** SUC n) MOD m                 by EXP
*)
val FUNPOW_SQ_MOD = store_thm(
  "FUNPOW_SQ_MOD",
  ``!m n k. 0 < m /\ 0 < n ==> (FUNPOW (\n. (n * n) MOD m) n k = (k ** 2 ** n) MOD m)``,
  strip_tac >>
  qabbrev_tac `f = \n. SQ n MOD m` >>
  Induct >>
  simp[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[Abbr`f`] >>
  rw[FUNPOW_SUC, Abbr`f`] >>
  `(k ** 2 ** n) ** 2 = k ** (2 * 2 ** n)` by rw[GSYM EXP_EXP_MULT] >>
  `_ = k ** 2 ** SUC n` by rw[EXP] >>
  rw[]);

(* Theorem: 0 < n ==> (FUNPOW (\x. MAX x m) n k = MAX k m) *)
(* Proof:
   By induction on n.
   Base: !m k. 0 < 0 ==> FUNPOW (\x. MAX x m) 0 k = MAX k m
      True by 0 < 0 = F.
   Step: !m k. 0 < n ==> FUNPOW (\x. MAX x m) n k = MAX k m ==>
         !m k. 0 < SUC n ==> FUNPOW (\x. MAX x m) (SUC n) k = MAX k m
      If n = 0,
           FUNPOW (\x. MAX x m) (SUC 0) k
         = FUNPOW (\x. MAX x m) 1 k          by ONE
         = (\x. MAX x m) k                   by FUNPOW_1
         = MAX k m                           by function application
      If n <> 0,
           FUNPOW (\x. MAX x m) (SUC n) k
         = f (FUNPOW (\x. MAX x m) n k)      by FUNPOW_SUC
         = (\x. MAX x m) (MAX k m)           by induction hypothesis
         = MAX (MAX k m) m                   by function application
         = MAX k m                           by MAX_IS_MAX, m <= MAX k m
*)
val FUNPOW_MAX = store_thm(
  "FUNPOW_MAX",
  ``!m n k. 0 < n ==> (FUNPOW (\x. MAX x m) n k = MAX k m)``,
  Induct_on `n` >-
  simp[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `m <= MAX k m` by rw[] >>
  rw[MAX_DEF]);

(* Theorem: 0 < n ==> (FUNPOW (\x. MIN x m) n k = MIN k m) *)
(* Proof:
   By induction on n.
   Base: !m k. 0 < 0 ==> FUNPOW (\x. MIN x m) 0 k = MIN k m
      True by 0 < 0 = F.
   Step: !m k. 0 < n ==> FUNPOW (\x. MIN x m) n k = MIN k m ==>
         !m k. 0 < SUC n ==> FUNPOW (\x. MIN x m) (SUC n) k = MIN k m
      If n = 0,
           FUNPOW (\x. MIN x m) (SUC 0) k
         = FUNPOW (\x. MIN x m) 1 k          by ONE
         = (\x. MIN x m) k                   by FUNPOW_1
         = MIN k m                           by function application
      If n <> 0,
           FUNPOW (\x. MIN x m) (SUC n) k
         = f (FUNPOW (\x. MIN x m) n k)      by FUNPOW_SUC
         = (\x. MIN x m) (MIN k m)           by induction hypothesis
         = MIN (MIN k m) m                   by function application
         = MIN k m                           by MIN_IS_MIN, MIN k m <= m
*)
val FUNPOW_MIN = store_thm(
  "FUNPOW_MIN",
  ``!m n k. 0 < n ==> (FUNPOW (\x. MIN x m) n k = MIN k m)``,
  Induct_on `n` >-
  simp[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `MIN k m <= m` by rw[] >>
  rw[MIN_DEF]);

(* Theorem: FUNPOW (\(x,y). (f x, g y)) n (x,y) = (FUNPOW f n x, FUNPOW g n y) *)
(* Proof:
   By induction on n.
   Base: FUNPOW (\(x,y). (f x,g y)) 0 (x,y) = (FUNPOW f 0 x,FUNPOW g 0 y)
          FUNPOW (\(x,y). (f x,g y)) 0 (x,y)
        = (x,y)                           by FUNPOW_0
        = (FUNPOW f 0 x, FUNPOW g 0 y)    by FUNPOW_0
   Step: FUNPOW (\(x,y). (f x,g y)) n (x,y) = (FUNPOW f n x,FUNPOW g n y) ==>
         FUNPOW (\(x,y). (f x,g y)) (SUC n) (x,y) = (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y)
         FUNPOW (\(x,y). (f x,g y)) (SUC n) (x,y)
       = (\(x,y). (f x,g y)) (FUNPOW (\(x,y). (f x,g y)) n (x,y)) by FUNPOW_SUC
       = (\(x,y). (f x,g y)) (FUNPOW f n x,FUNPOW g n y)          by induction hypothesis
       = (f (FUNPOW f n x),g (FUNPOW g n y))                      by function application
       = (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y)                  by FUNPOW_SUC
*)
val FUNPOW_PAIR = store_thm(
  "FUNPOW_PAIR",
  ``!f g n x y. FUNPOW (\(x,y). (f x, g y)) n (x,y) = (FUNPOW f n x, FUNPOW g n y)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[FUNPOW_SUC]);

(* Theorem: FUNPOW (\(x,y,z). (f x, g y, h z)) n (x,y,z) = (FUNPOW f n x, FUNPOW g n y, FUNPOW h n z) *)
(* Proof:
   By induction on n.
   Base: FUNPOW (\(x,y,z). (f x,g y,h z)) 0 (x,y,z) = (FUNPOW f 0 x,FUNPOW g 0 y,FUNPOW h 0 z)
          FUNPOW (\(x,y,z). (f x,g y,h z)) 0 (x,y,z)
        = (x,y)                                         by FUNPOW_0
        = (FUNPOW f 0 x, FUNPOW g 0 y, FUNPOW h 0 z)    by FUNPOW_0
   Step: FUNPOW (\(x,y,z). (f x,g y,h z)) n (x,y,z) =
                (FUNPOW f n x,FUNPOW g n y,FUNPOW h n z) ==>
         FUNPOW (\(x,y,z). (f x,g y,h z)) (SUC n) (x,y,z) =
                (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y,FUNPOW h (SUC n) z)
       Let fun = (\(x,y,z). (f x,g y,h z)).
         FUNPOW fun (SUC n) (x,y, z)
       = fun (FUNPOW fun n (x,y,z))                                   by FUNPOW_SUC
       = fun (FUNPOW f n x,FUNPOW g n y, FUNPOW h n z)                by induction hypothesis
       = (f (FUNPOW f n x),g (FUNPOW g n y), h (FUNPOW h n z))        by function application
       = (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y, FUNPOW h (SUC n) z)  by FUNPOW_SUC
*)
val FUNPOW_TRIPLE = store_thm(
  "FUNPOW_TRIPLE",
  ``!f g h n x y z. FUNPOW (\(x,y,z). (f x, g y, h z)) n (x,y,z) =
                  (FUNPOW f n x, FUNPOW g n y, FUNPOW h n z)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[FUNPOW_SUC]);

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 x IN s
         Since FUNPOW f 0 x = x      by FUNPOW_0
         This is trivially true.
   Step: FUNPOW f n x IN s ==> FUNPOW f (SUC n) x IN s
           FUNPOW f (SUC n) x
         = f (FUNPOW f n x)          by FUNPOW_SUC
         But FUNPOW f n x IN s       by induction hypothesis
          so f (FUNPOW f n x) IN s   by BIJ_ELEMENT, f PERMUTES s
*)
Theorem FUNPOW_closure:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[FUNPOW_SUC, BIJ_ELEMENT]
QED

(* ------------------------------------------------------------------------- *)
(* Integer Functions.                                                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Factorial                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FACT 0 = 1 *)
(* Proof: by FACT *)
val FACT_0 = store_thm(
  "FACT_0",
  ``FACT 0 = 1``,
  EVAL_TAC);

(* Theorem: FACT 1 = 1 *)
(* Proof:
     FACT 1
   = FACT (SUC 0)      by ONE
   = (SUC 0) * FACT 0  by FACT
   = (SUC 0) * 1       by FACT
   = 1                 by ONE
*)
val FACT_1 = store_thm(
  "FACT_1",
  ``FACT 1 = 1``,
  EVAL_TAC);

(* Theorem: FACT 2 = 2 *)
(* Proof:
     FACT 2
   = FACT (SUC 1)      by TWO
   = (SUC 1) * FACT 1  by FACT
   = (SUC 1) * 1       by FACT_1
   = 2                 by TWO
*)
val FACT_2 = store_thm(
  "FACT_2",
  ``FACT 2 = 2``,
  EVAL_TAC);

(* Theorem: (FACT n = 1) <=> n <= 1 *)
(* Proof:
   If n = 0,
      LHS = (FACT 0 = 1) = T         by FACT_0
      RHS = 0 <= 1 = T               by arithmetic
   If n <> 0, n = SUC m              by num_CASES
      LHS = FACT (SUC m) = 1
        <=> (SUC m) * FACT m = 1     by FACT
        <=> SUC m = 1 /\ FACT m = 1  by  MULT_EQ_1
        <=> m = 0  /\ FACT m = 1     by m = PRE 1 = 0
        <=> m = 0                    by FACT_0
      RHS = SUC m <= 1
        <=> ~(1 <= m)                by NOT_LEQ
        <=> m < 1                    by NOT_LESS_EQUAL
        <=> m = 0                    by arithmetic
*)
val FACT_EQ_1 = store_thm(
  "FACT_EQ_1",
  ``!n. (FACT n = 1) <=> n <= 1``,
  rpt strip_tac >>
  Cases_on `n` >>
  rw[FACT_0] >>
  rw[FACT] >>
  `!m. SUC m <= 1 <=> (m = 0)` by decide_tac >>
  metis_tac[FACT_0]);

(* Theorem: 1 <= FACT n *)
(* Proof:
   Note 0 < FACT n    by FACT_LESS
     so 1 <= FACT n   by arithmetic
*)
val FACT_GE_1 = store_thm(
  "FACT_GE_1",
  ``!n. 1 <= FACT n``,
  metis_tac[FACT_LESS, LESS_OR, ONE]);

(* Theorem: (FACT n = n) <=> (n = 1) \/ (n = 2) *)
(* Proof:
   If part: (FACT n = n) ==> (n = 1) \/ (n = 2)
      Note n <> 0           by FACT_0: FACT 0 = 1
       ==> ?m. n = SUC m    by num_CASES
      Thus SUC m * FACT m = SUC m       by FACT
                          = SUC m * 1   by MULT_RIGHT_1
       ==> FACT m = 1                   by EQ_MULT_LCANCEL, SUC_NOT
        or m <= 1           by FACT_EQ_1
      Thus m = 0 or 1       by arithmetic
        or n = 1 or 2       by ONE, TWO

   Only-if part: (FACT 1 = 1) /\ (FACT 2 = 2)
      Note FACT 1 = 1       by FACT_1
       and FACT 2 = 2       by FACT_2
*)
val FACT_EQ_SELF = store_thm(
  "FACT_EQ_SELF",
  ``!n. (FACT n = n) <=> (n = 1) \/ (n = 2)``,
  rw[EQ_IMP_THM] >| [
    `n <> 0` by metis_tac[FACT_0, DECIDE``1 <> 0``] >>
    `?m. n = SUC m` by metis_tac[num_CASES] >>
    fs[FACT] >>
    `FACT m = 1` by metis_tac[MULT_LEFT_1, EQ_MULT_RCANCEL, SUC_NOT] >>
    `m <= 1` by rw[GSYM FACT_EQ_1] >>
    decide_tac,
    rw[FACT_1],
    rw[FACT_2]
  ]);

(* Theorem: 0 < n ==> n <= FACT n *)
(* Proof:
   Note n <> 0             by 0 < n
    ==> ?m. n = SUC m      by num_CASES
   Thus FACT n
      = FACT (SUC m)       by n = SUC m
      = (SUC m) * FACT m   by FACT_LESS: 0 < FACT m
      >= (SUC m)           by LE_MULT_CANCEL_LBARE
      >= n                 by n = SUC m
*)
val FACT_GE_SELF = store_thm(
  "FACT_GE_SELF",
  ``!n. 0 < n ==> n <= FACT n``,
  rpt strip_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  rw[FACT] >>
  rw[FACT_LESS]);

(* Theorem: 0 < n ==> (FACT (n-1) = FACT n DIV n) *)
(* Proof:
   Since  n = SUC(n-1)                 by SUC_PRE, 0 < n.
     and  FACT n = n * FACT (n-1)      by FACT
                 = FACT (n-1) * n      by MULT_COMM
                 = FACT (n-1) * n + 0  by ADD_0
   Hence  FACT (n-1) = FACT n DIV n    by DIV_UNIQUE, 0 < n.
*)
val FACT_DIV = store_thm(
  "FACT_DIV",
  ``!n. 0 < n ==> (FACT (n-1) = FACT n DIV n)``,
  rpt strip_tac >>
  `n = SUC(n-1)` by decide_tac >>
  `FACT n = n * FACT (n-1)` by metis_tac[FACT] >>
  `_ = FACT (n-1) * n + 0` by rw[MULT_COMM] >>
  metis_tac[DIV_UNIQUE]);

(* Theorem: n! = PROD_SET (count (n+1))  *)
(* Proof: by induction on n.
   Base case: FACT 0 = PROD_SET (IMAGE SUC (count 0))
     LHS = FACT 0
         = 1                               by FACT
         = PROD_SET {}                     by PROD_SET_THM
         = PROD_SET (IMAGE SUC {})         by IMAGE_EMPTY
         = PROD_SET (IMAGE SUC (count 0))  by COUNT_ZERO
         = RHS
   Step case: FACT n = PROD_SET (IMAGE SUC (count n)) ==>
              FACT (SUC n) = PROD_SET (IMAGE SUC (count (SUC n)))
     Note: (SUC n) NOTIN (IMAGE SUC (count n))  by IN_IMAGE, IN_COUNT [1]
     LHS = FACT (SUC n)
         = (SUC n) * (FACT n)                            by FACT
         = (SUC n) * (PROD_SET (IMAGE SUC (count n)))    by induction hypothesis
         = (SUC n) * (PROD_SET (IMAGE SUC (count n)) DELETE (SUC n))         by DELETE_NON_ELEMENT, [1]
         = PROD_SET ((SUC n) INSERT ((IMAGE SUC (count n)) DELETE (SUC n)))  by PROD_SET_THM
         = PROD_SET (IMAGE SUC (n INSERT (count n)))     by IMAGE_INSERT
         = PROD_SET (IMAGE SUC (count (SUC n)))          by COUNT_SUC
         = RHS
*)
val FACT_EQ_PROD = store_thm(
  "FACT_EQ_PROD",
  ``!n. FACT n = PROD_SET (IMAGE SUC (count n))``,
  Induct_on `n` >-
  rw[PROD_SET_THM, FACT] >>
  rw[PROD_SET_THM, FACT, COUNT_SUC] >>
  `(SUC n) NOTIN (IMAGE SUC (count n))` by rw[] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem: n!/m! = product of (m+1) to n.
            m < n ==> (FACT n = PROD_SET (IMAGE SUC ((count n) DIFF (count m))) * (FACT m)) *)
(* Proof: by factorial formula.
   By induction on n.
   Base case: m < 0 ==> ...
     True since m < 0 = F.
   Step case: !m. m < n ==>
              (FACT n = PROD_SET (IMAGE SUC (count n DIFF count m)) * FACT m) ==>
              !m. m < SUC n ==>
              (FACT (SUC n) = PROD_SET (IMAGE SUC (count (SUC n) DIFF count m)) * FACT m)
     Note that m < SUC n ==> m <= n.
      and FACT (SUC n) = (SUC n) * FACT n     by FACT
     If m = n,
        PROD_SET (IMAGE SUC (count (SUC n) DIFF count n)) * FACT n
      = PROD_SET (IMAGE SUC {n}) * FACT n     by IN_DIFF, IN_COUNT
      = PROD_SET {SUC n} * FACT n             by IN_IMAGE
      = (SUC n) * FACT n                      by PROD_SET_THM
     If m < n,
        n NOTIN (count m)                     by IN_COUNT
     so n INSERT ((count n) DIFF (count m))
      = (n INSERT (count n)) DIFF (count m)   by INSERT_DIFF
      = count (SUC n) DIFF (count m)          by EXTENSION
     Since (SUC n) NOTIN (IMAGE SUC ((count n) DIFF (count m)))  by IN_IMAGE, IN_DIFF, IN_COUNT
       and FINITE (IMAGE SUC ((count n) DIFF (count m)))         by IMAGE_FINITE, FINITE_DIFF, FINITE_COUNT
     Hence PROD_SET (IMAGE SUC (count (SUC n) DIFF count m)) * FACT m
         = ((SUC n) * PROD_SET (IMAGE SUC (count n DIFF count m))) * FACT m   by PROD_SET_IMAGE_REDUCTION
         = (SUC n) * (PROD_SET (IMAGE SUC (count n DIFF count m))) * FACT m)  by MULT_ASSOC
         = (SUC n) * FACT n                                      by induction hypothesis
         = FACT (SUC n)                                          by FACT
*)
val FACT_REDUCTION = store_thm(
  "FACT_REDUCTION",
  ``!n m. m < n ==> (FACT n = PROD_SET (IMAGE SUC ((count n) DIFF (count m))) * (FACT m))``,
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[FACT] >>
  `m <= n` by decide_tac >>
  Cases_on `m = n` >| [
    rw_tac std_ss[] >>
    `count (SUC m) DIFF count m = {m}` by
  (rw[DIFF_DEF] >>
    rw[EXTENSION, EQ_IMP_THM]) >>
    `PROD_SET (IMAGE SUC {m}) = SUC m` by rw[PROD_SET_THM] >>
    metis_tac[],
    `m < n` by decide_tac >>
    `n NOTIN (count m)` by srw_tac[ARITH_ss][] >>
    `n INSERT ((count n) DIFF (count m)) = (n INSERT (count n)) DIFF (count m)` by rw[] >>
    `_ = count (SUC n) DIFF (count m)` by srw_tac[ARITH_ss][EXTENSION] >>
    `(SUC n) NOTIN (IMAGE SUC ((count n) DIFF (count m)))` by rw[] >>
    `FINITE (IMAGE SUC ((count n) DIFF (count m)))` by rw[] >>
    metis_tac[PROD_SET_IMAGE_REDUCTION, MULT_ASSOC]
  ]);

(* Theorem: prime p ==> p cannot divide k! for p > k.
            prime p /\ k < p ==> ~(p divides (FACT k)) *)
(* Proof:
   Since all terms of k! are less than p, and p has only 1 and p as factor.
   By contradiction, and induction on k.
   Base case: prime p ==> 0 < p ==> p divides (FACT 0) ==> F
     Since FACT 0 = 1              by FACT
       and p divides 1 <=> p = 1   by DIVIDES_ONE
       but prime p ==> 1 < p       by ONE_LT_PRIME
       so this is a contradiction.
   Step case: prime p /\ k < p ==> p divides (FACT k) ==> F ==>
              SUC k < p ==> p divides (FACT (SUC k)) ==> F
     Since FACT (SUC k) = SUC k * FACT k    by FACT
       and prime p /\ p divides (FACT (SUC k))
       ==> p divides (SUC k),
        or p divides (FACT k)               by P_EUCLIDES
     But SUC k < p, so ~(p divides (SUC k)) by NOT_LT_DIVIDES
     Hence p divides (FACT k) ==> F         by induction hypothesis
*)
val PRIME_BIG_NOT_DIVIDES_FACT = store_thm(
  "PRIME_BIG_NOT_DIVIDES_FACT",
  ``!p k. prime p /\ k < p ==> ~(p divides (FACT k))``,
  (spose_not_then strip_assume_tac) >>
  Induct_on `k` >| [
    rw[FACT] >>
    metis_tac[ONE_LT_PRIME, LESS_NOT_EQ],
    rw[FACT] >>
    (spose_not_then strip_assume_tac) >>
    `k < p /\ 0 < SUC k` by decide_tac >>
    metis_tac[P_EUCLIDES, NOT_LT_DIVIDES]
  ]);

(* ------------------------------------------------------------------------- *)
(* Basic GCD, LCM Theorems                                                   *)
(* ------------------------------------------------------------------------- *)

(* Note: gcd Theory has: GCD_SYM   |- !a b. gcd a b = gcd b a
                    but: LCM_COMM  |- lcm a b = lcm b a
*)
val GCD_COMM = save_thm("GCD_COMM", GCD_SYM);
(* val GCD_COMM = |- !a b. gcd a b = gcd b a: thm *)
val LCM_SYM = save_thm("LCM_SYM", LCM_COMM |> GEN ``b:num`` |> GEN ``a:num``);
(* val val LCM_SYM = |- !a b. lcm a b = lcm b a: thm *)

(* Note:
gcdTheory.LCM_0  |- (lcm 0 x = 0) /\ (lcm x 0 = 0)
gcdTheory.LCM_1  |- (lcm 1 x = x) /\ (lcm x 1 = x)
gcdTheory.GCD_1  |- coprime 1 x /\ coprime x 1
but only GCD_0L, GCD_0R
gcdTheory.GCD_EQ_0 |- !n m. (gcd n m = 0) <=> (n = 0) /\ (m = 0)
*)

(* Theorem: (gcd 0 x = x) /\ (gcd x 0 = x) *)
(* Proof: by GCD_0L, GCD_0R *)
val GCD_0 = store_thm(
  "GCD_0",
  ``!x. (gcd 0 x = x) /\ (gcd x 0 = x)``,
  rw_tac std_ss[GCD_0L, GCD_0R]);

(* Theorem: gcd(n, m) = 1 ==> n divides (c * m) ==> n divides c *)
(* Proof:
   This is L_EUCLIDES:  (Euclid's Lemma)
> val it = |- !a b c. coprime a b /\ divides b (a * c) ==> b divides c : thm
*)

(* Theorem: If 0 < n, 0 < m, let g = gcd n m, then 0 < g and n MOD g = 0 and m MOD g = 0 *)
(* Proof:
   0 < n ==> n <> 0, 0 < m ==> m <> 0,              by NOT_ZERO_LT_ZERO
   hence  g = gcd n m <> 0, or 0 < g.               by GCD_EQ_0
   g = gcd n m ==> (g divides n) /\ (g divides m)   by GCD_IS_GCD, is_gcd_def
               ==> (n MOD g = 0) /\ (m MOD g = 0)   by DIVIDES_MOD_0
*)
val GCD_DIVIDES = store_thm(
  "GCD_DIVIDES",
  ``!m n. 0 < n /\ 0 < m ==> 0 < (gcd n m) /\ (n MOD (gcd n m) = 0) /\ (m MOD (gcd n m) = 0)``,
  ntac 3 strip_tac >>
  conj_asm1_tac >-
  metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[GCD_IS_GCD, is_gcd_def, DIVIDES_MOD_0]);

(* Theorem: gcd n (gcd n m) = gcd n m *)
(* Proof:
   If n = 0,
      gcd 0 (gcd n m) = gcd n m   by GCD_0L
   If m = 0,
      gcd n (gcd n 0)
    = gcd n n                     by GCD_0R
    = n = gcd n 0                 by GCD_REF
   If n <> 0, m <> 0, d <> 0      by GCD_EQ_0
   Since d divides n, n MOD d = 0
     gcd n d
   = gcd d n             by GCD_SYM
   = gcd (n MOD d) d     by GCD_EFFICIENTLY, d <> 0
   = gcd 0 d             by GCD_DIVIDES
   = d                   by GCD_0L
*)
val GCD_GCD = store_thm(
  "GCD_GCD",
  ``!m n. gcd n (gcd n m) = gcd n m``,
  rpt strip_tac >>
  Cases_on `n = 0` >- rw[] >>
  Cases_on `m = 0` >- rw[] >>
  `0 < n /\ 0 < m` by decide_tac >>
  metis_tac[GCD_SYM, GCD_EFFICIENTLY, GCD_DIVIDES, GCD_EQ_0, GCD_0L]);

(* Theorem: GCD m n * LCM m n = m * n *)
(* Proof:
   By lcm_def:
   lcm m n = if (m = 0) \/ (n = 0) then 0 else m * n DIV gcd m n
   If m = 0,
   gcd 0 n * lcm 0 n = n * 0 = 0 = 0 * n, hence true.
   If n = 0,
   gcd m 0 * lcm m 0 = m * 0 = 0 = m * 0, hence true.
   If m <> 0, n <> 0,
   gcd m n * lcm m n = gcd m n * (m * n DIV gcd m n) = m * n.
*)
val GCD_LCM = store_thm(
  "GCD_LCM",
  ``!m n. gcd m n * lcm m n = m * n``,
  rw[lcm_def] >>
  `0 < m /\ 0 < n` by decide_tac >>
  `0 < gcd m n /\ (n MOD gcd m n = 0)` by rw[GCD_DIVIDES] >>
  qabbrev_tac `d = gcd m n` >>
  `m * n = (m * n) DIV d * d + (m * n) MOD d` by rw[DIVISION] >>
  `(m * n) MOD d = 0` by metis_tac[MOD_TIMES2, ZERO_MOD, MULT_0] >>
  metis_tac[ADD_0, MULT_COMM]);

(* Theorem: m divides (lcm m n) /\ n divides (lcm m n) *)
(* Proof: by LCM_IS_LEAST_COMMON_MULTIPLE *)
val LCM_DIVISORS = store_thm(
  "LCM_DIVISORS",
  ``!m n. m divides (lcm m n) /\ n divides (lcm m n)``,
  rw[LCM_IS_LEAST_COMMON_MULTIPLE]);

(* Theorem: m divides p /\ n divides p ==> (lcm m n) divides p *)
(* Proof: by LCM_IS_LEAST_COMMON_MULTIPLE *)
val LCM_IS_LCM = store_thm(
  "LCM_IS_LCM",
  ``!m n p. m divides p /\ n divides p ==> (lcm m n) divides p``,
  rw[LCM_IS_LEAST_COMMON_MULTIPLE]);

(* Theorem: (lcm m n = 0) <=> ((m = 0) \/ (n = 0)) *)
(* Proof:
   If part: lcm m n = 0 ==> m = 0 \/ n = 0
      By contradiction, suppse m = 0 /\ n = 0.
      Then gcd m n = 0                     by GCD_EQ_0
       and m * n = 0                       by MULT_EQ_0
       but (gcd m n) * (lcm m n) = m * n   by GCD_LCM
        so RHS <> 0, but LHS = 0           by MULT_0
       This is a contradiction.
   Only-if part: m = 0 \/ n = 0 ==> lcm m n = 0
      True by LCM_0
*)
val LCM_EQ_0 = store_thm(
  "LCM_EQ_0",
  ``!m n. (lcm m n = 0) <=> ((m = 0) \/ (n = 0))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `(gcd m n) * (lcm m n) = m * n` by rw[GCD_LCM] >>
    `gcd m n <> 0` by rw[GCD_EQ_0] >>
    `m * n <> 0` by rw[MULT_EQ_0] >>
    metis_tac[MULT_0],
    rw[LCM_0],
    rw[LCM_0]
  ]);

(* Note: gcdTheory.GCD_REF |- !a. gcd a a = a *)

(* Theorem: lcm a a = a *)
(* Proof:
  If a = 0,
     lcm 0 0 = 0                      by LCM_0
  If a <> 0,
     (gcd a a) * (lcm a a) = a * a    by GCD_LCM
             a * (lcm a a) = a * a    by GCD_REF
                   lcm a a = a        by MULT_LEFT_CANCEL, a <> 0
*)
val LCM_REF = store_thm(
  "LCM_REF",
  ``!a. lcm a a = a``,
  metis_tac[num_CASES, LCM_0, GCD_LCM, GCD_REF, MULT_LEFT_CANCEL]);

(* Theorem: a divides n /\ b divides n ==> (lcm a b) divides n *)
(* Proof: same as LCM_IS_LCM *)
val LCM_DIVIDES = store_thm(
  "LCM_DIVIDES",
  ``!n a b. a divides n /\ b divides n ==> (lcm a b) divides n``,
  rw[LCM_IS_LCM]);
(*
> LCM_IS_LCM |> ISPEC ``a:num`` |> ISPEC ``b:num`` |> ISPEC ``n:num`` |> GEN_ALL;
val it = |- !n b a. a divides n /\ b divides n ==> lcm a b divides n: thm
*)

(* Theorem: 0 < m \/ 0 < n ==> 0 < gcd m n *)
(* Proof: by GCD_EQ_0, NOT_ZERO_LT_ZERO *)
val GCD_POS = store_thm(
  "GCD_POS",
  ``!m n. 0 < m \/ 0 < n ==> 0 < gcd m n``,
  metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < m /\ 0 < n ==> 0 < lcm m n *)
(* Proof: by LCM_EQ_0, NOT_ZERO_LT_ZERO *)
val LCM_POS = store_thm(
  "LCM_POS",
  ``!m n. 0 < m /\ 0 < n ==> 0 < lcm m n``,
  metis_tac[LCM_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: n divides m <=> gcd n m = n *)
(* Proof:
   If part:
     n divides m ==> ?k. m = k * n   by divides_def
       gcd n m
     = gcd n (k * n)
     = gcd (n * 1) (n * k)      by MULT_RIGHT_1, MULT_COMM
     = n * gcd 1 k              by GCD_COMMON_FACTOR
     = n * 1                    by GCD_1
     = n                        by MULT_RIGHT_1
   Only-if part: gcd n m = n ==> n divides m
     If n = 0, gcd 0 m = m      by GCD_0L
     But gcd n m = n = 0        by givien
     hence m = 0,
     and 0 divides 0 is true    by DIVIDES_REFL
     If n <> 0,
       If m = 0, LHS true       by GCD_0R
                 RHS true       by ALL_DIVIDES_0
       If m <> 0,
       then 0 < n and 0 < m,
       gcd n m = gcd (m MOD n) n       by GCD_EFFICIENTLY
       if (m MOD n) = 0
          then n divides m             by DIVIDES_MOD_0
       If (m MOD n) <> 0,
       so (m MOD n) MOD (gcd n m) = 0  by GCD_DIVIDES
       or (m MOD n) MOD n = 0          by gcd n m = n, given
       or  m MOD n = 0                 by MOD_MOD
       contradicting (m MOD n) <> 0, hence true.
*)
val divides_iff_gcd_fix = store_thm(
  "divides_iff_gcd_fix",
  ``!m n. n divides m <=> (gcd n m = n)``,
  rw[EQ_IMP_THM] >| [
    `?k. m = k * n` by rw[GSYM divides_def] >>
    `gcd n m = gcd (n * 1) (n * k)` by rw[MULT_COMM] >>
    rw[GCD_COMMON_FACTOR, GCD_1],
    Cases_on `n = 0` >-
    metis_tac[GCD_0L, DIVIDES_REFL] >>
    Cases_on `m = 0` >-
    metis_tac[GCD_0R, ALL_DIVIDES_0] >>
    `0 < n /\ 0 < m` by decide_tac >>
    Cases_on `m MOD n = 0` >-
    metis_tac[DIVIDES_MOD_0] >>
    `0 < m MOD n` by decide_tac >>
    metis_tac[GCD_EFFICIENTLY, GCD_DIVIDES, MOD_MOD]
  ]);

(* Theorem: !m n. n divides m <=> (lcm n m = m) *)
(* Proof:
   If n = 0,
      n divides m <=> m = 0         by ZERO_DIVIDES
      and lcm 0 0 = 0 = m           by LCM_0
   If n <> 0,
     gcd n m * lcm n m = n * m      by GCD_LCM
     If part: n divides m ==> (lcm n m = m)
        Then gcd n m = n            by divides_iff_gcd_fix
        so   n * lcm n m = n * m    by above
                 lcm n m = m        by MULT_LEFT_CANCEL, n <> 0
     Only-if part: lcm n m = m ==> n divides m
        If m = 0, n divdes 0 = true by ALL_DIVIDES_0
        If m <> 0,
        Then gcd n m * m = n * m    by above
          or     gcd n m = n        by MULT_RIGHT_CANCEL, m <> 0
          so     n divides m        by divides_iff_gcd_fix
*)
val divides_iff_lcm_fix = store_thm(
  "divides_iff_lcm_fix",
  ``!m n. n divides m <=> (lcm n m = m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[ZERO_DIVIDES, LCM_0] >>
  metis_tac[GCD_LCM, MULT_LEFT_CANCEL, MULT_RIGHT_CANCEL, divides_iff_gcd_fix, ALL_DIVIDES_0]);

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

(* Overload on coprime for GCD equals 1 *)
val _ = overload_on ("coprime", ``\x y. gcd x y = 1``);

(* Theorem: If 1 < n, !x. gcd n x = 1  ==> 0 < x /\ 0 < x MOD n *)
(* Proof:
   If x = 0, gcd n x = n. But n <> 1, hence x <> 0, or 0 < x.
   x MOD n = 0 ==> x a multiple of n ==> gcd n x = n <> 1  if n <> 1.
   Hence if 1 < n, gcd x n = 1 ==> x MOD n <> 0, or 0 < x MOD n.
*)
val MOD_NONZERO_WHEN_GCD_ONE = store_thm(
  "MOD_NONZERO_WHEN_GCD_ONE",
  ``!n. 1 < n ==> !x. (gcd n x = 1) ==> 0 < x /\ 0 < x MOD n``,
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
    metis_tac[MOD_MULITPLE_ZERO, MULT_COMM]
  ]);

(* Theorem: (gcd n x = 1) /\ (gcd n y = 1) ==> (gcd n (x*y) = 1) *)
(* Proof:
   gcd n x = 1 ==> no common factor between x and n
   gcd n y = 1 ==> no common factor between y and n
   Hence there is no common factor between (x*y) and n
   or gcd n (x*y) = 1

   gcd n (x * y) = gcd n y    by GCD_CANCEL_MULT, since gcd n x = 1.
                 = 1          by given
*)
val PRODUCT_WITH_GCD_ONE = store_thm(
  "PRODUCT_WITH_GCD_ONE",
  ``!n x y. (gcd n x = 1) /\ (gcd n y = 1) ==> (gcd n (x*y) = 1)``,
  metis_tac[GCD_CANCEL_MULT]);

(* Theorem: For 0 < n, (gcd n x = 1) ==> (gcd n (x MOD n) = 1) *)
(* Proof:
   Since n <> 0,
   1 = gcd n x            by given
     = gcd (x MOD n) n    by GCD_EFFICIENTLY
     = gcd n (x MOD n)    by GCD_SYM
*)
val MOD_WITH_GCD_ONE = store_thm(
  "MOD_WITH_GCD_ONE",
  ``!n x. 0 < n /\ (gcd n x = 1) ==> (gcd n (x MOD n) = 1)``,
  rpt strip_tac >>
  `0 <> n` by decide_tac >>
  metis_tac[GCD_EFFICIENTLY, GCD_SYM]);

(* Theorem: If 1 < n, gcd n x = 1 ==> ?k q. (k * x) MOD n = 1 /\ gcd n k = 1 *)
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
  ``!n x. 1 < n /\ (gcd n x = 1) ==> ?k. ((k * x) MOD n = 1) /\ (gcd n k = 1)``,
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

(* Theorem: For n > 1, 0 < x < n /\ (gcd n x = 1) ==>
            ?y. 0 < y /\ y < n /\ gcd n y = 1 /\ y*x MOD n = 1 *)
(* Proof:
       gcd n x = 1
   ==> ?k. (k*x) MOD n = 1 /\ gcd n k = 1     by GCD_ONE_PROPERTY
       (k*x) MOD n = 1
   ==> (k MOD n * x MOD n) MOD n = 1          by MOD_TIMES2
   ==> ((k MOD n) * x) MOD n = 1              by LESS_MOD, x < n.

   Now   k MOD n < n                          by MOD_LESS
   and   0 < k MOD n                          by MOD_MULITPLE_ZERO and 1 <> 0.

   Hence take y = k MOD n, then 0 < y < n.
   and gcd n k = 1 ==> gcd n (k MOD n) = 1    by MOD_WITH_GCD_ONE.
*)
val GCD_MOD_MULT_INV = store_thm(
  "GCD_MOD_MULT_INV",
  ``!n x. 1 < n /\ 0 < x /\ x < n /\ (gcd n x = 1) ==> ?y. 0 < y /\ y < n /\ (gcd n y = 1) /\ ((y*x) MOD n = 1)``,
  rpt strip_tac >>
  `?k. ((k*x) MOD n = 1) /\ (gcd n k = 1)` by rw_tac std_ss[GCD_ONE_PROPERTY] >>
  `0 < n` by decide_tac >>
  `(k MOD n * x MOD n) MOD n = 1` by rw_tac std_ss[MOD_TIMES2] >>
  `((k MOD n) * x) MOD n = 1` by metis_tac[LESS_MOD] >>
  `k MOD n < n` by rw_tac std_ss[MOD_LESS] >>
  `1 <> 0` by decide_tac >>
  `0 <> k MOD n` by metis_tac[MOD_MULITPLE_ZERO] >>
  `0 < k MOD n` by decide_tac >>
  metis_tac[MOD_WITH_GCD_ONE]);

(* Convert this into an existence definition *)
val lemma = prove(
  ``!n x. ?y. 1 < n /\ 0 < x /\ x < n /\ (gcd n x = 1) ==>
              0 < y /\ y < n /\ (gcd n y = 1) /\ ((y*x) MOD n = 1)``,
  metis_tac[GCD_MOD_MULT_INV]);

val GEN_MULT_INV_DEF = new_specification(
  "GEN_MULT_INV_DEF",
  ["GCD_MOD_MUL_INV"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(* > val GEN_MULT_INV_DEF =
    |- !n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
       0 < GCD_MOD_MUL_INV n x /\ GCD_MOD_MUL_INV n x < n /\ coprime n (GCD_MOD_MUL_INV n x) /\
       ((GCD_MOD_MUL_INV n x * x) MOD n = 1) : thm *)

(* ------------------------------------------------------------------------- *)
(* More GCD and LCM Theorems                                                 *)
(* ------------------------------------------------------------------------- *)

(* Note:
gcdTheory.LCM_IS_LEAST_COMMON_MULTIPLE
|- m divides lcm m n /\ n divides lcm m n /\ !p. m divides p /\ n divides p ==> lcm m n divides p
gcdTheory.GCD_IS_GREATEST_COMMON_DIVISOR
|- !a b. gcd a b divides a /\ gcd a b divides b /\ !d. d divides a /\ d divides b ==> d divides gcd a b
*)

(* Theorem: (c = gcd a b) <=>
            c divides a /\ c divides b /\ !x. x divides a /\ x divides b ==> x divides c *)
(* Proof:
   By GCD_IS_GREATEST_COMMON_DIVISOR
       (gcd a b) divides a     [1]
   and (gcd a b) divides b     [2]
   and !p. p divides a /\ p divides b ==> p divides (gcd a b)   [3]
   Hence if part is true, and for the only-if part,
   We have c divides (gcd a b)   by [3] above,
       and (gcd a b) divides c   by [1], [2] and the given implication
   Therefore c = gcd a b         by DIVIDES_ANTISYM
*)
val GCD_PROPERTY = store_thm(
  "GCD_PROPERTY",
  ``!a b c. (c = gcd a b) <=>
   c divides a /\ c divides b /\ !x. x divides a /\ x divides b ==> x divides c``,
  rw[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_ANTISYM, EQ_IMP_THM]);

(* Theorem: gcd a (gcd b c) = gcd (gcd a b) c *)
(* Proof:
   Since (gcd a (gcd b c)) divides a    by GCD_PROPERTY
         (gcd a (gcd b c)) divides b    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd a (gcd b c)) divides c    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd (gcd a b) c) divides a    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd (gcd a b) c) divides b    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd (gcd a b) c) divides c    by GCD_PROPERTY
   We have
         (gcd (gcd a b) c) divides (gcd b c)           by GCD_PROPERTY
     and (gcd (gcd a b) c) divides (gcd a (gcd b c))   by GCD_PROPERTY
    Also (gcd a (gcd b c)) divides (gcd a b)           by GCD_PROPERTY
     and (gcd a (gcd b c)) divides (gcd (gcd a b) c)   by GCD_PROPERTY
   Therefore gcd a (gcd b c) = gcd (gcd a b) c         by DIVIDES_ANTISYM
*)
val GCD_ASSOC = store_thm(
  "GCD_ASSOC",
  ``!a b c. gcd a (gcd b c) = gcd (gcd a b) c``,
  rpt strip_tac >>
  `(gcd a (gcd b c)) divides a` by metis_tac[GCD_PROPERTY] >>
  `(gcd a (gcd b c)) divides b` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd a (gcd b c)) divides c` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd (gcd a b) c) divides a` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd (gcd a b) c) divides b` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd (gcd a b) c) divides c` by metis_tac[GCD_PROPERTY] >>
  `(gcd (gcd a b) c) divides (gcd a (gcd b c))` by metis_tac[GCD_PROPERTY] >>
  `(gcd a (gcd b c)) divides (gcd (gcd a b) c)` by metis_tac[GCD_PROPERTY] >>
  rw[DIVIDES_ANTISYM]);

(* Note:
   With identity by GCD_1: (gcd 1 x = 1) /\ (gcd x 1 = 1)
   GCD forms a monoid in numbers.
*)

(* Theorem: gcd a (gcd b c) = gcd b (gcd a c) *)
(* Proof:
     gcd a (gcd b c)
   = gcd (gcd a b) c    by GCD_ASSOC
   = gcd (gcd b a) c    by GCD_SYM
   = gcd b (gcd a c)    by GCD_ASSOC
*)
val GCD_ASSOC_COMM = store_thm(
  "GCD_ASSOC_COMM",
  ``!a b c. gcd a (gcd b c) = gcd b (gcd a c)``,
  metis_tac[GCD_ASSOC, GCD_SYM]);

(* Theorem: (c = lcm a b) <=>
            a divides c /\ b divides c /\ !x. a divides x /\ b divides x ==> c divides x *)
(* Proof:
   By LCM_IS_LEAST_COMMON_MULTIPLE
       a divides (lcm a b)    [1]
   and b divides (lcm a b)    [2]
   and !p. a divides p /\ divides b p ==> divides (lcm a b) p  [3]
   Hence if part is true, and for the only-if part,
   We have c divides (lcm a b)   by implication and [1], [2]
       and (lcm a b) divides c   by [3]
   Therefore c = lcm a b         by DIVIDES_ANTISYM
*)
val LCM_PROPERTY = store_thm(
  "LCM_PROPERTY",
  ``!a b c. (c = lcm a b) <=>
   a divides c /\ b divides c /\ !x. a divides x /\ b divides x ==> c divides x``,
  rw[LCM_IS_LEAST_COMMON_MULTIPLE, DIVIDES_ANTISYM, EQ_IMP_THM]);

(* Theorem: lcm a (lcm b c) = lcm (lcm a b) c *)
(* Proof:
   Since a divides (lcm a (lcm b c))   by LCM_PROPERTY
         b divides (lcm a (lcm b c))   by LCM_PROPERTY, DIVIDES_TRANS
         c divides (lcm a (lcm b c))   by LCM_PROPERTY, DIVIDES_TRANS
         a divides (lcm (lcm a b) c)   by LCM_PROPERTY, DIVIDES_TRANS
         b divides (lcm (lcm a b) c)   by LCM_PROPERTY, DIVIDES_TRANS
         c divides (lcm (lcm a b) c)   by LCM_PROPERTY
   We have
         (lcm b c) divides (lcm (lcm a b) c)           by LCM_PROPERTY
     and (lcm a (lcm b c)) divides (lcm (lcm a b) c)   by LCM_PROPERTY
    Also (lcm a b) divides (lcm a (lcm b c))           by LCM_PROPERTY
     and (lcm (lcm a b) c) divides (lcm a (lcm b c))   by LCM_PROPERTY
    Therefore lcm a (lcm b c) = lcm (lcm a b) c        by DIVIDES_ANTISYM
*)
val LCM_ASSOC = store_thm(
  "LCM_ASSOC",
  ``!a b c. lcm a (lcm b c) = lcm (lcm a b) c``,
  rpt strip_tac >>
  `a divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY] >>
  `b divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `c divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `a divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `b divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `c divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY] >>
  `(lcm a (lcm b c)) divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY] >>
  `(lcm (lcm a b) c) divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY] >>
  rw[DIVIDES_ANTISYM]);

(* Note:
   With the identity by LCM_0: (lcm 0 x = 0) /\ (lcm x 0 = 0)
   LCM forms a monoid in numbers.
*)

(* Theorem: lcm a (lcm b c) = lcm b (lcm a c) *)
(* Proof:
     lcm a (lcm b c)
   = lcm (lcm a b) c   by LCM_ASSOC
   = lcm (lcm b a) c   by LCM_COMM
   = lcm b (lcm a c)   by LCM_ASSOC
*)
val LCM_ASSOC_COMM = store_thm(
  "LCM_ASSOC_COMM",
  ``!a b c. lcm a (lcm b c) = lcm b (lcm a c)``,
  metis_tac[LCM_ASSOC, LCM_COMM]);

(* Theorem: b <= a ==> gcd (a - b) b = gcd a b *)
(* Proof:
     gcd (a - b) b
   = gcd b (a - b)         by GCD_SYM
   = gcd (b + (a - b)) b   by GCD_ADD_L
   = gcd (a - b + b) b     by ADD_COMM
   = gcd a b               by SUB_ADD, b <= a.

Note: If a < b, a - b = 0  for num, hence gcd (a - b) b = gcd 0 b = b.
*)
val GCD_SUB_L = store_thm(
  "GCD_SUB_L",
  ``!a b. b <= a ==> (gcd (a - b) b = gcd a b)``,
  metis_tac[GCD_SYM, GCD_ADD_L, ADD_COMM, SUB_ADD]);

(* Theorem: a <= b ==> gcd a (b - a) = gcd a b *)
(* Proof:
     gcd a (b - a)
   = gcd (b - a) a         by GCD_SYM
   = gcd b a               by GCD_SUB_L
   = gcd a b               by GCD_SYM
*)
val GCD_SUB_R = store_thm(
  "GCD_SUB_R",
  ``!a b. a <= b ==> (gcd a (b - a) = gcd a b)``,
  metis_tac[GCD_SYM, GCD_SUB_L]);

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

(* Theorem: coprime m n ==> LCM m n = m * n *)
(* Proof:
   By GCD_LCM, with gcd m n = 1.
*)
val LCM_COPRIME = store_thm(
  "LCM_COPRIME",
  ``!m n. coprime m n ==> (lcm m n = m * n)``,
  metis_tac[GCD_LCM, MULT_LEFT_1]);

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

(* Theorem: 0 < m ==> (gcd m n = gcd m (n MOD m)) *)
(* Proof:
     gcd m n
   = gcd (n MOD m) m       by GCD_EFFICIENTLY, m <> 0
   = gcd m (n MOD m)       by GCD_SYM
*)
val GCD_MOD = store_thm(
  "GCD_MOD",
  ``!m n. 0 < m ==> (gcd m n = gcd m (n MOD m))``,
  rw[Once GCD_EFFICIENTLY, GCD_SYM]);

(* Theorem: 0 < m ==> (gcd n m = gcd (n MOD m) m) *)
(* Proof: by GCD_MOD, GCD_COMM *)
val GCD_MOD_COMM = store_thm(
  "GCD_MOD_COMM",
  ``!m n. 0 < m ==> (gcd n m = gcd (n MOD m) m)``,
  metis_tac[GCD_MOD, GCD_COMM]);

(* Theorem: gcd a (b * a + c) = gcd a c *)
(* Proof:
   If a = 0,
      Then b * 0 + c = c             by arithmetic
      Hence trivially true.
   If a <> 0,
      gcd a (b * a + c)
    = gcd ((b * a + c) MOD a) a      by GCD_EFFICIENTLY, 0 < a
    = gcd (c MOD a) a                by MOD_TIMES, 0 < a
    = gcd a c                        by GCD_EFFICIENTLY, 0 < a
*)
val GCD_EUCLID = store_thm(
  "GCD_EUCLID",
  ``!a b c. gcd a (b * a + c) = gcd a c``,
  rpt strip_tac >>
  Cases_on `a = 0` >-
  rw[] >>
  metis_tac[GCD_EFFICIENTLY, MOD_TIMES, NOT_ZERO_LT_ZERO]);

(* Theorem: gcd (b * a + c) a = gcd a c *)
(* Proof: by GCD_EUCLID, GCD_SYM *)
val GCD_REDUCE = store_thm(
  "GCD_REDUCE",
  ``!a b c. gcd (b * a + c) a = gcd a c``,
  rw[GCD_EUCLID, GCD_SYM]);

(* ------------------------------------------------------------------------- *)
(* Coprime Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: coprime n (n + 1) *)
(* Proof:
   Since n < n + 1 ==> n <= n + 1,
     gcd n (n + 1)
   = gcd n (n + 1 - n)      by GCD_SUB_R
   = gcd n 1                by arithmetic
   = 1                      by GCD_1
*)
val coprime_SUC = store_thm(
  "coprime_SUC",
  ``!n. coprime n (n + 1)``,
  rw[GCD_SUB_R]);

(* Theorem: 0 < n ==> coprime n (n - 1) *)
(* Proof:
     gcd n (n - 1)
   = gcd (n - 1) n             by GCD_SYM
   = gcd (n - 1) (n - 1 + 1)   by SUB_ADD, 0 <= n
   = 1                         by coprime_SUC
*)
val coprime_PRE = store_thm(
  "coprime_PRE",
  ``!n. 0 < n ==> coprime n (n - 1)``,
  metis_tac[GCD_SYM, coprime_SUC, DECIDE``!n. 0 < n ==> (n - 1 + 1 = n)``]);

(* Theorem: coprime 0 n ==> n = 1 *)
(* Proof:
   gcd 0 n = n    by GCD_0L
           = 1    by coprime 0 n
*)
val coprime_0L = store_thm(
  "coprime_0L",
  ``!n. coprime 0 n <=> (n = 1)``,
  rw[GCD_0L]);

(* Theorem: coprime n 0 ==> n = 1 *)
(* Proof:
   gcd n 0 = n    by GCD_0L
           = 1    by coprime n 0
*)
val coprime_0R = store_thm(
  "coprime_0R",
  ``!n. coprime n 0 <=> (n = 1)``,
  rw[GCD_0R]);

(* Theorem: coprime x y = coprime y x *)
(* Proof:
         coprime x y
   means gcd x y = 1
      so gcd y x = 1   by GCD_SYM
    thus coprime y x
*)
val coprime_sym = store_thm(
  "coprime_sym",
  ``!x y. coprime x y = coprime y x``,
  rw[GCD_SYM]);

(* Theorem: coprime k n /\ n <> 1 ==> k <> 0 *)
(* Proof: by coprime_0L *)
val coprime_neq_1 = store_thm(
  "coprime_neq_1",
  ``!n k. coprime k n /\ n <> 1 ==> k <> 0``,
  fs[coprime_0L]);

(* Theorem: coprime k n /\ 1 < n ==> 0 < k *)
(* Proof: by coprime_neq_1 *)
val coprime_gt_1 = store_thm(
  "coprime_gt_1",
  ``!n k. coprime k n /\ 1 < n ==> 0 < k``,
  metis_tac[coprime_neq_1, NOT_ZERO_LT_ZERO, DECIDE``~(1 < 1)``]);

(* Note:  gcd (c ** n) m = gcd c m  is false when n = 0, where c ** 0 = 1. *)

(* Theorem: coprime c m ==> !n. coprime (c ** n) m *)
(* Proof: by induction on n.
   Base case: coprime (c ** 0) m
     Since c ** 0 = 1         by EXP
     and coprime 1 m is true  by GCD_1
   Step case: coprime c m /\ coprime (c ** n) m ==> coprime (c ** SUC n) m
     coprime c m means
     coprime m c              by GCD_SYM

       gcd m (c ** SUC n)
     = gcd m (c * c ** n)     by EXP
     = gcd m (c ** n)         by GCD_CANCEL_MULT, coprime m c
     = 1                      by induction hypothesis
     Hence coprime m (c ** SUC n)
     or coprime (c ** SUC n) m  by GCD_SYM
*)
val coprime_exp = store_thm(
  "coprime_exp",
  ``!c m. coprime c m ==> !n. coprime (c ** n) m``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[EXP, GCD_1] >>
  metis_tac[EXP, GCD_CANCEL_MULT, GCD_SYM]);

(* Theorem: coprime a b ==> !n. coprime a (b ** n) *)
(* Proof: by coprime_exp, GCD_SYM *)
val coprime_exp_comm = store_thm(
  "coprime_exp_comm",
  ``!a b. coprime a b ==> !n. coprime a (b ** n)``,
  metis_tac[coprime_exp, GCD_SYM]);

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

(* Theorem: coprime x z /\ coprime y z ==> coprime (x * y) z *)
(* Proof:
   By GCD_CANCEL_MULT:
   |- !m n k. coprime m k ==> (gcd m (k * n) = gcd m n)
   Hence follows by coprime_sym.
*)
val coprime_product_coprime = store_thm(
  "coprime_product_coprime",
  ``!x y z. coprime x z /\ coprime y z ==> coprime (x * y) z``,
  metis_tac[GCD_CANCEL_MULT, GCD_SYM]);

(* Theorem: coprime z x /\ coprime z y ==> coprime z (x * y) *)
(* Proof:
   Note gcd z x = 1         by given
    ==> gcd z (x * y)
      = gcd z y             by GCD_CANCEL_MULT
      = 1                   by given
*)
val coprime_product_coprime_sym = store_thm(
  "coprime_product_coprime_sym",
  ``!x y z. coprime z x /\ coprime z y ==> coprime z (x * y)``,
  rw[GCD_CANCEL_MULT]);
(* This is the same as PRODUCT_WITH_GCD_ONE *)

(* Theorem: coprime x z ==> (coprime y z <=> coprime (x * y) z) *)
(* Proof:
   If part: coprime x z /\ coprime y z ==> coprime (x * y) z
      True by coprime_product_coprime
   Only-if part: coprime x z /\ coprime (x * y) z ==> coprime y z
      Let d = gcd y z.
      Then d divides z /\ d divides y     by GCD_PROPERTY
        so d divides (x * y)              by DIVIDES_MULT, MULT_COMM
        or d divides (gcd (x * y) z)      by GCD_PROPERTY
           d divides 1                    by coprime (x * y) z
       ==> d = 1                          by DIVIDES_ONE
        or coprime y z                    by notation
*)
val coprime_product_coprime_iff = store_thm(
  "coprime_product_coprime_iff",
  ``!x y z. coprime x z ==> (coprime y z <=> coprime (x * y) z)``,
  rw[EQ_IMP_THM] >-
  rw[coprime_product_coprime] >>
  qabbrev_tac `d = gcd y z` >>
  metis_tac[GCD_PROPERTY, DIVIDES_MULT, MULT_COMM, DIVIDES_ONE]);

(* Theorem: a divides n /\ b divides n /\ coprime a b ==> (a * b) divides n *)
(* Proof: by LCM_COPRIME, LCM_DIVIDES *)
val coprime_product_divides = store_thm(
  "coprime_product_divides",
  ``!n a b. a divides n /\ b divides n /\ coprime a b ==> (a * b) divides n``,
  metis_tac[LCM_COPRIME, LCM_DIVIDES]);

(* Theorem: 0 < m /\ coprime m n ==> coprime m (n MOD m) *)
(* Proof:
     gcd m n
   = if m = 0 then n else gcd (n MOD m) m    by GCD_EFFICIENTLY
   = gcd (n MOD m) m                         by decide_tac, m <> 0
   = gcd m (n MOD m)                         by GCD_SYM
   Hence true since coprime m n <=> gcd m n = 1.
*)
val coprime_mod = store_thm(
  "coprime_mod",
  ``!m n. 0 < m /\ coprime m n ==> coprime m (n MOD m)``,
  metis_tac[GCD_EFFICIENTLY, GCD_SYM, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < m ==> (coprime m n = coprime m (n MOD m)) *)
(* Proof: by GCD_MOD *)
val coprime_mod_iff = store_thm(
  "coprime_mod_iff",
  ``!m n. 0 < m ==> (coprime m n = coprime m (n MOD m))``,
  rw[Once GCD_MOD]);

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

(* Theorem: 1 < n /\ coprime n k /\ 1 < p /\ p divides n ==> ~(p divides k) *)
(* Proof:
   First, 1 < n ==> n <> 0 and n <> 1
   If k = 0, gcd n k = n        by GCD_0R
   But coprime n k means gcd n k = 1, so k <> 0.
   By contradiction.
   If p divides k, and given p divides n,
   then p divides gcd n k = 1   by GCD_IS_GREATEST_COMMON_DIVISOR, n <> 0 and k <> 0
   or   p = 1                   by DIVIDES_ONE
   which contradicts 1 < p.
*)
val coprime_factor_not_divides = store_thm(
  "coprime_factor_not_divides",
  ``!n k. 1 < n /\ coprime n k ==> !p. 1 < p /\ p divides n ==> ~(p divides k)``,
  rpt strip_tac >>
  `n <> 0 /\ n <> 1 /\ p <> 1` by decide_tac >>
  metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_ONE, GCD_0R]);

(* Theorem: m divides n ==> !k. coprime n k ==> coprime m k *)
(* Proof:
   Let d = gcd m k.
   Then d divides m /\ d divides k    by GCD_IS_GREATEST_COMMON_DIVISOR
    ==> d divides n                   by DIVIDES_TRANS
     so d divides 1                   by GCD_IS_GREATEST_COMMON_DIVISOR, coprime n k
    ==> d = 1                         by DIVIDES_ONE
*)
val coprime_factor_coprime = store_thm(
  "coprime_factor_coprime",
  ``!m n. m divides n ==> !k. coprime n k ==> coprime m k``,
  rpt strip_tac >>
  qabbrev_tac `d = gcd m k` >>
  `d divides m /\ d divides k` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides n` by metis_tac[DIVIDES_TRANS] >>
  `d divides 1` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR] >>
  rw[GSYM DIVIDES_ONE]);

(* Theorem: prime p /\ ~(p divides n) ==> coprime p n *)
(* Proof:
   Since divides p 0, so n <> 0.    by ALL_DIVIDES_0
   If n = 1, certainly coprime p n  by GCD_1
   If n <> 1,
   Let gcd p n = d.
   Since d divides p                by GCD_IS_GREATEST_COMMON_DIVISOR
     and prime p                    by given
      so d = 1 or d = p             by prime_def
     but d <> p                     by divides_iff_gcd_fix
   Hence d = 1, or coprime p n.
*)
val prime_not_divides_is_coprime = store_thm(
  "prime_not_divides_is_coprime",
  ``!n p. prime p /\ ~(p divides n) ==> coprime p n``,
  rpt strip_tac >>
  `n <> 0` by metis_tac[ALL_DIVIDES_0] >>
  Cases_on `n = 1` >-
  rw[] >>
  `0 < p` by rw[PRIME_POS] >>
  `p <> 0` by decide_tac >>
  metis_tac[prime_def, divides_iff_gcd_fix, GCD_IS_GREATEST_COMMON_DIVISOR]);

(* Theorem: prime p /\ ~(coprime p n) ==> p divides n *)
(* Proof:
   Let d = gcd p n.
   Then d divides p        by GCD_IS_GREATEST_COMMON_DIVISOR
    ==> d = p              by prime_def
   Thus p divides n        by divides_iff_gcd_fix
*)
val prime_not_coprime_divides = store_thm(
  "prime_not_coprime_divides",
  ``!n p. prime p /\ ~(coprime p n) ==> p divides n``,
  rpt strip_tac >>
  qabbrev_tac `d = gcd p n` >>
  `d divides p` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d = p` by metis_tac[prime_def] >>
  rw[divides_iff_gcd_fix]);

(* This is just the inverse of prime_not_divides_is_coprime *)
val prime_not_coprime_divides = store_thm(
  "prime_not_coprime_divides",
  ``!n p. prime p /\ ~(coprime p n) ==> p divides n``,
  metis_tac[prime_not_divides_is_coprime]);

(* Theorem: 1 < n /\ prime p /\ p divides n ==> !k. coprime n k ==> coprime p k *)
(* Proof:
   Since coprime n k /\ p divides n
     ==> ~(p divides k)               by coprime_factor_not_divides
    Then prime p /\ ~(p divides k)
     ==> coprime p k                  by prime_not_divides_is_coprime
*)
val coprime_prime_factor_coprime = store_thm(
  "coprime_prime_factor_coprime",
  ``!n p. 1 < n /\ prime p /\ p divides n ==> !k. coprime n k ==> coprime p k``,
  metis_tac[coprime_factor_not_divides, prime_not_divides_is_coprime, ONE_LT_PRIME]);

(* This is better:
coprime_factor_coprime
|- !m n. m divides n ==> !k. coprime n k ==> coprime m k
*)

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

(* Theorem: !n. ?p. prime p /\ n < p *)
(* Proof:
   Since ?i. n < PRIMES i   by NEXT_LARGER_PRIME
     and prime (PRIMES i)   by primePRIMES
   Take p = PRIMES i.
*)
val prime_always_bigger = store_thm(
  "prime_always_bigger",
  ``!n. ?p. prime p /\ n < p``,
  metis_tac[NEXT_LARGER_PRIME, primePRIMES]);

(* Theorem: n divides m ==> coprime n (SUC m) *)
(* Proof:
   If n = 0,
     then m = 0      by ZERO_DIVIDES
     gcd 0 (SUC 0)
   = SUC 0           by GCD_0L
   = 1               by ONE
   If n = 1,
      gcd 1 (SUC m) = 1      by GCD_1
   If n <> 0,
     gcd n (SUC m)
   = gcd ((SUC m) MOD n) n   by GCD_EFFICIENTLY
   = gcd 1 n                 by n divides m
   = 1                       by GCD_1
*)
val divides_imp_coprime_with_successor = store_thm(
  "divides_imp_coprime_with_successor",
  ``!m n. n divides m ==> coprime n (SUC m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[GSYM ZERO_DIVIDES] >>
  Cases_on `n = 1` >-
  rw[] >>
  `0 < n /\ 1 < n` by decide_tac >>
  `m MOD n = 0` by rw[GSYM DIVIDES_MOD_0] >>
  `(SUC m) MOD n = (m + 1) MOD n` by rw[ADD1] >>
  `_ = (m MOD n + 1 MOD n) MOD n` by rw[MOD_PLUS] >>
  `_ = (0 + 1) MOD n` by rw[ONE_MOD] >>
  `_ = 1` by rw[ONE_MOD] >>
  metis_tac[GCD_EFFICIENTLY, GCD_1]);

(* Note: counter-example for converse: gcd 3 11 = 1, but ~(3 divides 10). *)

(* Theorem: 0 < m /\ n divides m ==> coprime n (PRE m) *)
(* Proof:
   Since n divides m
     ==> ?q. m = q * n      by divides_def
    Also 0 < m means m <> 0,
     ==> ?k. m = SUC k      by num_CASES
               = k + 1      by ADD1
      so m - k = 1, k = PRE m.
    Let d = gcd n k.
    Then d divides n /\ d divides k     by GCD_IS_GREATEST_COMMON_DIVISOR
     and d divides n ==> d divides m    by DIVIDES_MULTIPLE, m = q * n
      so d divides (m - k)              by DIVIDES_SUB
      or d divides 1                    by m - k = 1
     ==> d = 1                          by DIVIDES_ONE
*)
val divides_imp_coprime_with_predecessor = store_thm(
  "divides_imp_coprime_with_predecessor",
  ``!m n. 0 < m /\ n divides m ==> coprime n (PRE m)``,
  rpt strip_tac >>
  `?q. m = q * n` by rw[GSYM divides_def] >>
  `m <> 0` by decide_tac >>
  `?k. m = k + 1` by metis_tac[num_CASES, ADD1] >>
  `(k = PRE m) /\ (m - k = 1)` by decide_tac >>
  qabbrev_tac `d = gcd n k` >>
  `d divides n /\ d divides k` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides m` by rw[DIVIDES_MULTIPLE] >>
  `d divides (m - k)` by rw[DIVIDES_SUB] >>
  metis_tac[DIVIDES_ONE]);

(* Theorem: coprime p n ==> (gcd (p * m) n = gcd m n) *)
(* Proof:
   Note coprime p n means coprime n p     by GCD_SYM
     gcd (p * m) n
   = gcd n (p * m)                        by GCD_SYM
   = gcd n p                              by GCD_CANCEL_MULT
*)
val gcd_coprime_cancel = store_thm(
  "gcd_coprime_cancel",
  ``!m n p. coprime p n ==> (gcd (p * m) n = gcd m n)``,
  rw[GCD_CANCEL_MULT, GCD_SYM]);

(* The following is a direct, but tricky, proof of the above result *)

(* Theorem: coprime p n ==> (gcd (p * m) n = gcd m n) *)
(* Proof:
     gcd (p * m) n
   = gcd (p * m) (n * 1)            by MULT_RIGHT_1
   = gcd (p * m) (n * (gcd m 1))    by GCD_1
   = gcd (p * m) (gcd (n * m) n)    by GCD_COMMON_FACTOR
   = gcd (gcd (p * m) (n * m)) n    by GCD_ASSOC
   = gcd (m * (gcd p n)) n          by GCD_COMMON_FACTOR, MULT_COMM
   = gcd (m * 1) n                  by coprime p n
   = gcd m n                        by MULT_RIGHT_1

   Simple proof of GCD_CANCEL_MULT:
   (a*c, b) = (a*c , b*1) = (a * c, b * (c, 1)) = (a * c, b * c, b) = ((a, b) * c, b) = (c, b) since (a,b) = 1.
*)
val gcd_coprime_cancel = store_thm(
  "gcd_coprime_cancel",
  ``!m n p. coprime p n ==> (gcd (p * m) n = gcd m n)``,
  rpt strip_tac >>
  `gcd (p * m) n = gcd (p * m) (n * (gcd m 1))` by rw[GCD_1] >>
  `_ = gcd (p * m) (gcd (n * m) n)` by rw[GSYM GCD_COMMON_FACTOR] >>
  `_ = gcd (gcd (p * m) (n * m)) n` by rw[GCD_ASSOC] >>
  `_ = gcd m n` by rw[GCD_COMMON_FACTOR, MULT_COMM] >>
  rw[]);

(* Theorem: prime p /\ prime q /\ p <> q ==> coprime p q *)
(* Proof:
   Let d = gcd p q.
   By contradiction, suppose d <> 1.
   Then d divides p /\ d divides q   by GCD_PROPERTY
     so d = 1 or d = p               by prime_def
    and d = 1 or d = q               by prime_def
    But p <> q                       by given
     so d = 1, contradicts d <> 1.
*)
val primes_coprime = store_thm(
  "primes_coprime",
  ``!p q. prime p /\ prime q /\ p <> q ==> coprime p q``,
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd p q` >>
  `d divides p /\ d divides q` by metis_tac[GCD_PROPERTY] >>
  metis_tac[prime_def]);

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
(* Pairwise Coprime Property                                                 *)
(* ------------------------------------------------------------------------- *)

(* Overload pairwise coprime set *)
val _ = overload_on("PAIRWISE_COPRIME", ``\s. !x y. x IN s /\ y IN s /\ x <> y ==> coprime x y``);

(* Theorem: e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==>
            (!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s *)
(* Proof: by IN_INSERT *)
val pairwise_coprime_insert = store_thm(
  "pairwise_coprime_insert",
  ``!s e. e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==>
        (!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s``,
  metis_tac[IN_INSERT]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==>
            !t. t SUBSET s ==> (PROD_SET t) divides (PROD_SET s) *)
(* Proof:
   Note FINITE t    by SUBSET_FINITE
   By finite induction on t.
   Base case: PROD_SET {} divides PROD_SET s
      Note PROD_SET {} = 1           by PROD_SET_EMPTY
       and 1 divides (PROD_SET s)    by ONE_DIVIDES_ALL
   Step case: t SUBSET s ==> PROD_SET t divides PROD_SET s ==>
              e NOTIN t /\ e INSERT t SUBSET s ==> PROD_SET (e INSERT t) divides PROD_SET s
      Let m = PROD_SET s.
      Note e IN s /\ t SUBSET s                      by INSERT_SUBSET
      Thus e divides m                               by PROD_SET_ELEMENT_DIVIDES
       and (PROD_SET t) divides m                    by induction hypothesis
      Also coprime e (PROD_SET t)                    by every_coprime_prod_set_coprime, SUBSET_DEF
      Note PROD_SET (e INSERT t) = e * PROD_SET t    by PROD_SET_INSERT
       ==> e * PROD_SET t divides m                  by coprime_product_divides
*)
val pairwise_coprime_prod_set_subset_divides = store_thm(
  "pairwise_coprime_prod_set_subset_divides",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==>
   !t. t SUBSET s ==> (PROD_SET t) divides (PROD_SET s)``,
  rpt strip_tac >>
  `FINITE t` by metis_tac[SUBSET_FINITE] >>
  qpat_x_assum `t SUBSET s` mp_tac >>
  qpat_x_assum `FINITE t` mp_tac >>
  qid_spec_tac `t` >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY] >>
  fs[] >>
  `e divides PROD_SET s` by rw[PROD_SET_ELEMENT_DIVIDES] >>
  `coprime e (PROD_SET t)` by prove_tac[every_coprime_prod_set_coprime, SUBSET_DEF] >>
  rw[PROD_SET_INSERT, coprime_product_divides]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==>
            !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v) *)
(* Proof:
   By finite induction on s.
   Base: {} = u UNION v ==> coprime (PROD_SET u) (PROD_SET v)
      Note u = {} and v = {}       by EMPTY_UNION
       and PROD_SET {} = 1         by PROD_SET_EMPTY
      Hence true                   by GCD_1
   Step: PAIRWISE_COPRIME s ==>
         !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v) ==>
         e NOTIN s /\ e INSERT s = u UNION v ==> coprime (PROD_SET u) (PROD_SET v)
      Note (!x. x IN s ==> coprime e x) /\
           PAIRWISE_COPRIME s      by IN_INSERT
      Note e IN u \/ e IN v        by IN_INSERT, IN_UNION
      If e IN u,
         Then e NOTIN v            by IN_DISJOINT
         Let w = u DELETE e.
         Then e NOTIN w            by IN_DELETE
          and u = e INSERT w       by INSERT_DELETE
         Note s = w UNION v        by EXTENSION, IN_INSERT, IN_UNION
          ==> FINITE w             by FINITE_UNION
          and DISJOINT w v         by DISJOINT_INSERT

         Note coprime (PROD_SET w) (PROD_SET v)   by induction hypothesis
          and !x. x IN v ==> coprime e x          by v SUBSET s
         Also FINITE v                            by FINITE_UNION
           so coprime e (PROD_SET v)              by every_coprime_prod_set_coprime, FINITE v
          ==> coprime (e * PROD_SET w) PROD_SET v         by coprime_product_coprime
           or coprime PROD_SET (e INSERT w) PROD_SET v    by PROD_SET_INSERT
            = coprime PROD_SET u PROD_SET v               by above

      Similarly for e IN v.
*)
val pairwise_coprime_partition_coprime = store_thm(
  "pairwise_coprime_partition_coprime",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==>
   !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v)``,
  ntac 2 strip_tac >>
  qpat_x_assum `PAIRWISE_COPRIME s` mp_tac >>
  qpat_x_assum `FINITE s` mp_tac >>
  qid_spec_tac `s` >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  fs[PROD_SET_EMPTY] >>
  `(!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s` by metis_tac[IN_INSERT] >>
  `e IN u \/ e IN v` by metis_tac[IN_INSERT, IN_UNION] >| [
    qabbrev_tac `w = u DELETE e` >>
    `u = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN v` by metis_tac[IN_DISJOINT] >>
    `s = w UNION v` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT w v` by metis_tac[DISJOINT_INSERT] >>
    `coprime (PROD_SET w) (PROD_SET v)` by rw[] >>
    `(!x. x IN v ==> coprime e x)` by rw[] >>
    `FINITE v` by metis_tac[FINITE_UNION] >>
    `coprime e (PROD_SET v)` by rw[every_coprime_prod_set_coprime] >>
    metis_tac[coprime_product_coprime, PROD_SET_INSERT],
    qabbrev_tac `w = v DELETE e` >>
    `v = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN u` by metis_tac[IN_DISJOINT] >>
    `s = u UNION w` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT u w` by metis_tac[DISJOINT_INSERT, DISJOINT_SYM] >>
    `coprime (PROD_SET u) (PROD_SET w)` by rw[] >>
    `(!x. x IN u ==> coprime e x)` by rw[] >>
    `FINITE u` by metis_tac[FINITE_UNION] >>
    `coprime (PROD_SET u) e` by rw[every_coprime_prod_set_coprime, coprime_sym] >>
    metis_tac[coprime_product_coprime_sym, PROD_SET_INSERT]
  ]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==> !u v. (s = u UNION v) /\ DISJOINT u v ==>
            (PROD_SET s = PROD_SET u * PROD_SET v) /\ (coprime (PROD_SET u) (PROD_SET v)) *)
(* Proof: by PROD_SET_PRODUCT_BY_PARTITION, pairwise_coprime_partition_coprime *)
val pairwise_coprime_prod_set_partition = store_thm(
  "pairwise_coprime_prod_set_partition",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==> !u v. (s = u UNION v) /\ DISJOINT u v ==>
       (PROD_SET s = PROD_SET u * PROD_SET v) /\ (coprime (PROD_SET u) (PROD_SET v))``,
  metis_tac[PROD_SET_PRODUCT_BY_PARTITION, pairwise_coprime_partition_coprime]);

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

(* This is numerical version of:
poly_unity_1_divides  |- !r. Ring r /\ #1 <> #0 ==> !n. X - |1| pdivides unity n
*)
val power_predecessor_divisor = save_thm("power_predecessor_divisor",
    power_predecessor_divisibility
       |> SPEC ``t:num`` |> SPEC ``1:num`` |> SPEC ``n:num``
       |> SIMP_RULE (srw_ss()) [] |> GEN_ALL);
(* val power_predecessor_divisor = |- !t n. 1 < t ==> t - 1 divides t ** n - 1: thm *)
(* However, this is too restrictive. *)

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
val power_predecessor_divisor = store_thm(
  "power_predecessor_divisor",
  ``!t n. t - 1 divides t ** n - 1``,
  rpt strip_tac >>
  Cases_on `t = 0` >-
  simp[ZERO_EXP] >>
  Cases_on `t = 1` >-
  simp[] >>
  `1 < t` by decide_tac >>
  metis_tac[power_predecessor_divisibility, EXP_1, ONE_DIVIDES_ALL]);

(* Overload power predecessor *)
val _ = overload_on("tops", ``\b:num n. b ** n - 1``);

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
      Then coprime p n                           by prime_not_divides_is_coprime
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
    `coprime p n` by rw[prime_not_divides_is_coprime] >>
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

(* Theorem: prime p /\ q divides (p ** n) ==> (q = 1) \/ (p divides q) *)
(* Proof:
   By contradiction, suppose q <> 1 /\ ~(p divides q).
   Note ?j. j <= n /\ (q = p ** j)   by prime_power_divisor
    and 0 < j                        by EXP_0, q <> 1
   then p divides q                  by prime_divides_self_power, 0 < j
   This contradicts ~(p divides q).
*)
Theorem PRIME_EXP_FACTOR:
  !p q n. prime p /\ q divides (p ** n) ==> (q = 1) \/ (p divides q)
Proof
  spose_not_then strip_assume_tac >>
  `?j. j <= n /\ (q = p ** j)` by rw[prime_power_divisor] >>
  `0 < j` by fs[] >>
  metis_tac[prime_divides_self_power]
QED

(* Idea: For prime p, FACT (p-1) MOD p <> 0 *)

(* Theorem: prime p /\ n < p ==> FACT n MOD p <> 0 *)
(* Proof:
   Note 1 < p                  by ONE_LT_PRIME
   By induction on n.
   Base: 0 < p ==> (FACT 0 MOD p = 0) ==> F
      Note FACT 0 = 1          by FACT_0
       and 1 MOD p = 1         by LESS_MOD, 1 < p
       and 1 = 0 is F.
   Step: n < p ==> (FACT n MOD p = 0) ==> F ==>
         SUC n < p ==> (FACT (SUC n) MOD p = 0) ==> F
      If n = 0, SUC 0 = 1      by ONE
         Note FACT 1 = 1       by FACT_1
          and 1 MOD p = 1      by LESS_MOD, 1 < p
          and 1 = 0 is F.
      If n <> 0, 0 < n.
             (FACT (SUC n)) MOD p = 0
         <=> (SUC n * FACT n) MOD p = 0      by FACT
         Note (SUC n) MOD p <> 0             by MOD_LESS, SUC n < p
          and (FACT n) MOD p <> 0            by induction hypothesis
           so (SUC n * FACT n) MOD p <> 0    by EUCLID_LEMMA
         This is a contradiction.
*)
Theorem FACT_MOD_PRIME:
  !p n. prime p /\ n < p ==> FACT n MOD p <> 0
Proof
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  Induct_on `n` >-
  simp[FACT_0] >>
  Cases_on `n = 0` >-
  simp[FACT_1] >>
  rw[FACT] >>
  `n < p` by decide_tac >>
  `(SUC n) MOD p <> 0` by fs[] >>
  metis_tac[EUCLID_LEMMA]
QED

(* ------------------------------------------------------------------------- *)
(* Sublist Theory Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Datatypes and overloads:
   l1 <= l2  = sublist l1 l2
*)
(* Definitions and Theorems (# are exported):

   Sublist:
   sublist_def           |- (!x. [] <= x <=> T) /\ (!t1 h1. h1::t1 <= [] <=> F) /\
                             !t2 t1 h2 h1. h1::t1 <= h2::t2 <=>
                              (h1 = h2) /\ t1 <= t2 \/ h1 <> h2 /\ h1::t1 <= t2
   sublist_nil           |- !p. [] <= p
   sublist_cons          |- !h p q. p <= q <=> h::p <= h::q
   sublist_of_nil        |- !p. p <= [] <=> (p = [])
   sublist_cons_eq       |- !h. (!p q. h::p <= q ==> p <= q) <=> !p q. p <= q ==> p <= h::q
   sublist_cons_remove   |- !h p q. h::p <= q ==> p <= q
   sublist_cons_include  |- !h p q. p <= q ==> p <= h::q
   sublist_length        |- !p q. p <= q ==> LENGTH p <= LENGTH q
   sublist_refl          |- !p. p <= p
   sublist_antisym       |- !p q. p <= q /\ q <= p ==> (p = q)
   sublist_trans         |- !p q r. p <= q /\ q <= r ==> p <= r
   sublist_snoc          |- !h p q. p <= q ==> SNOC h p <= SNOC h q
   sublist_member_sing   |- !ls x. MEM x ls ==> [x] <= ls
   sublist_take          |- !ls n. TAKE n ls <= ls
   sublist_drop          |- !ls n. DROP n ls <= ls
   sublist_tail          |- !ls. ls <> [] ==> TL ls <= ls
   sublist_front         |- !ls. ls <> [] ==> FRONT ls <= ls
   sublist_head_sing     |- !ls. ls <> [] ==> [HD ls] <= ls
   sublist_last_sing     |- !ls. ls <> [] ==> [LAST ls] <= ls
   sublist_every         |- !l ls. l <= ls ==> !P. EVERY P ls ==> EVERY P l

   More sublists:
   sublist_induct          |- !P. (!y. P [] y) /\
                                  (!h x y. P x y /\ x <= y ==> P (h::x) (h::y)) /\
                                  (!h x y. P x y /\ x <= y ==> P x (h::y)) ==> !x y. x <= y ==> P x y
   sublist_append_remove   |- !p q x. x ++ p <= q ==> p <= q
   sublist_append_include  |- !p q x. p <= q ==> p <= x ++ q
   sublist_append_suffix   |- !p q. p <= p ++ q
   sublist_append_prefix   |- !p q. p <= q ++ p
   sublist_prefix          |- !x p q. p <= q <=> x ++ p <= x ++ q
   sublist_prefix_nil      |- !p q. p ++ q <= q ==> (p = [])
   sublist_append_if       |- !p q. p <= q ==> !h. p ++ [h] <= q ++ [h]
   sublist_append_only_if  |- !p q h. p ++ [h] <= q ++ [h] ==> p <= q
   sublist_append_iff      |- !p q h. p <= q <=> p ++ [h] <= q ++ [h]
   sublist_suffix          |- !x p q. p <= q <=> p ++ x <= q ++ x
   sublist_append_pair     |- !a b c d. a <= b /\ c <= d ==> a ++ c <= b ++ d
   sublist_append_extend   |- !h t q. h::t <= q <=> ?x y. (q = x ++ h::y) /\ t <= y

   Applications of sublist:
   MAP_SUBLIST           |- !f p q. p <= q ==> MAP f p <= MAP f q
   SUM_SUBLIST           |- !p q. p <= q ==> SUM p <= SUM q
   listRangeINC_sublist  |- !m n. m < n ==> [m; n] <= [m .. n]
   listRangeLHI_sublist  |- !m n. m + 1 < n ==> [m; n - 1] <= [m ..< n]
*)

(* ------------------------------------------------------------------------- *)
(* Sublist: an order-preserving portion of a list                            *)
(* ------------------------------------------------------------------------- *)

(* Definition of sublist *)
val sublist_def = Define`
    (sublist [] x = T) /\
    (sublist (h1::t1) [] = F) /\
    (sublist (h1::t1) (h2::t2) <=>
       ((h1 = h2) /\ sublist t1 t2 \/ ~(h1 = h2) /\ sublist (h1::t1) t2))
`;

(* Overload sublist by infix operator *)
val _ = overload_on ("<=", ``sublist``);
(*
> sublist_def;
val it = |- (!x. [] <= x <=> T) /\ (!t1 h1. h1::t1 <= [] <=> F) /\
             !t2 t1 h2 h1. h1::t1 <= h2::t2 <=>
                (h1 = h2) /\ t1 <= t2 \/ h1 <> h2 /\ h1::t1 <= t2: thm
*)

(* Theorem: [] <= p *)
(* Proof: by sublist_def *)
val sublist_nil = store_thm(
  "sublist_nil",
  ``!p. [] <= p``,
  rw[sublist_def]);

(* Theorem: p <= q <=> h::p <= h::q *)
(* Proof: by sublist_def *)
val sublist_cons = store_thm(
  "sublist_cons",
  ``!h p q. p <= q <=> h::p <= h::q``,
  rw[sublist_def]);

(* Theorem: p <= [] <=> (p = []) *)
(* Proof:
   If p = [], then [] <= []           by sublist_nil
   If p = h::t, then h::t <= [] = F   by sublist_def
*)
val sublist_of_nil = store_thm(
  "sublist_of_nil",
  ``!p. p <= [] <=> (p = [])``,
  (Cases_on `p` >> rw[sublist_def]));

(* Theorem: (!p q. (h::p) <= q ==> p <= q) = (!p q. p <= q ==> p <= (h::q)) *)
(* Proof:
   If part: (!p q. (h::p) <= q ==> p <= q) ==> (!p q. p <= q ==> p <= (h::q))
               p <= q
        ==> h::p <= h::q     by sublist_cons
        ==>    p <= h::q     by implication
   Only-if part: (!p q. p <= q ==> p <= (h::q)) ==> (!p q. (h::p) <= q ==> p <= q)
            (h::p) <= q
        ==> (h::p) <= (h::q) by implication
        ==>      p <= q      by sublist_cons
*)
val sublist_cons_eq = store_thm(
  "sublist_cons_eq",
  ``!h. (!p q. (h::p) <= q ==> p <= q) = (!p q. p <= q ==> p <= (h::q))``,
  rw[EQ_IMP_THM] >>
  metis_tac[sublist_cons]);

(* Theorem: h::p <= q ==> p <= q *)
(* Proof:
   By induction on q.
   Base: !h p. h::p <= [] ==> p <= []
        True since h::p <= [] = F    by sublist_def

   Step: !h p. h::p <= q ==> p <= q ==>
         !h h' p. h'::p <= h::q ==> p <= h::q
        If p = [], true        by sublist_nil
        If p = h''::t,
            p <= h::q
        <=> (h'' = h) /\ t <= q \/ h'' <> h /\ h''::t <= q   by sublist_def
        If h'' = h, then t <= q        by sublist_def, induction hypothesis
        If h'' <> h, then h''::t <= q  by sublist_def, induction hypothesis
*)
val sublist_cons_remove = store_thm(
  "sublist_cons_remove",
  ``!h p q. h::p <= q ==> p <= q``,
  Induct_on `q` >-
  rw[sublist_def] >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[sublist_def]) >>
  (Cases_on `h'' = h` >> metis_tac[sublist_def]));

(* Theorem: p <= q ==> p <= h::q *)
(* Proof: by sublist_cons_eq, sublist_cons_remove *)
val sublist_cons_include = store_thm(
  "sublist_cons_include",
  ``!h p q. p <= q ==> p <= h::q``,
  metis_tac[sublist_cons_eq, sublist_cons_remove]);

(* Theorem: p <= q ==> LENGTH p <= LENGTH q *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ==> LENGTH p <= LENGTH []
        Note p = []      by sublist_of_nil
        Thus true        by arithemtic
   Step: !p. p <= q ==> LENGTH p <= LENGTH q ==>
         !h p. p <= h::q ==> LENGTH p <= LENGTH (h::q)
         If p = [], LENGTH p = 0          by LENGTH
            and 0 <= LENGTH (h::q).
         If p = h'::t,
            If h = h',
               (h::t) <= (h::q)
            <=>    t <= q                 by sublist_def, same heads
            ==> LENGTH t <= LENGTH q      by inductive hypothesis
            ==> SUC(LENGTH t) <= SUC(LENGTH q)
              = LENGTH (h::t) <= LENGTH (h::q)
            If ~(h = h'),
                (h'::t) <= (h::q)
            <=> (h'::t) <= q                      by sublist_def, different heads
            ==> LENGTH (h'::t) <= LENGTH q        by inductive hypothesis
            ==> LENGTH (h'::t) <= SUC(LENGTH q)   by arithemtic
              = LENGTH (h'::t) <= LENGTH (h::q)
*)
val sublist_length = store_thm(
  "sublist_length",
  ``!p q. p <= q ==> LENGTH p <= LENGTH q``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[]) >>
  (Cases_on `h = h'` >> fs[sublist_def]) >>
  `LENGTH (h'::t) <= LENGTH q` by rw[] >>
  `LENGTH t < LENGTH (h'::t)` by rw[LENGTH_TL_LT] >>
  decide_tac);

(* Theorem: [Reflexive] p <= p *)
(* Proof:
   By induction on p.
   Base: [] <= [], true                      by sublist_nil
   Step: p <= p ==> !h. h::p <= h::p, true   by sublist_cons
*)
val sublist_refl = store_thm(
  "sublist_refl",
  ``!p:'a list. p <= p``,
  Induct >-
  rw[sublist_nil] >>
  rw[GSYM sublist_cons]);
(* Faster just by definition *)
val sublist_refl = store_thm(
  "sublist_refl",
  ``!p:'a list. p <= p``,
  Induct >> rw[sublist_def]);

(* Theorem: [Anti-symmetric] !p q. (p <= q) /\ (q <= p) ==> (p = q) *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] /\ [] <= p ==> (p = [])
       Note p <= [] already gives p = []   by sublist_of_nil
   Step: !p. p <= q /\ q <= p ==> (p = q) ==>
         !h p. p <= h::q /\ h::q <= p ==> (p = h::q)
       If p = [], h::q <= [] = F           by sublist_def
       If p = (h'::t),
          If h = h',
              ((h::t) <= (h::q)) /\ ((h::q) <= (h::t))
          <=> (t <= q) and (q <= t)        by sublist_def, same heads
          ==> t = q                        by inductive hypothesis
          <=> (h::t) = (h::q)              by list equality
          If ~(h = h'),
              ((h'::t) <= (h::q)) /\ ((h::q) <= (h'::t))
          <=> ((h'::t) <= q) /\ ((h::q) <= t)      by sublist_def, different heads
          ==> (LENGTH (h'::t) <= LENGTH q) /\
              (LENGTH (h::q) <= LENGTH t)          by sublist_length
          ==> (LENGTh t < LENGTH q) /\
              (LENGTH q < LENGTH t)                by LENGTH_TL_LT
            = F                                    by arithmetic
          Hence the implication is T.
*)
val sublist_antisym = store_thm(
  "sublist_antisym",
  ``!p q:'a list. p <= q /\ q <= p ==> (p = q)``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  Cases_on `p` >-
  fs[sublist_def] >>
  (Cases_on `h' = h` >> fs[sublist_def]) >>
  `LENGTH (h'::t) <= LENGTH q /\ LENGTH (h::q) <= LENGTH t` by rw[sublist_length] >>
  fs[LENGTH_TL_LT]);

(* Theorem [Transitive]: for all lists p, q, r; (p <= q) /\ (q <= r) ==> (p <= r) *)
(* Proof:
   By induction on list r and taking note of cases.
   By induction on r.
   Base: !p q. p <= q /\ q <= [] ==> p <= []
      Note q = []         by sublist_of_nil
        so p = []         by sublist_of_nil
   Step: !p q. p <= q /\ q <= r ==> p <= r ==>
         !h p q. p <= q /\ q <= h::r ==> p <= h::r
      If p = [], true     by sublist_nil
      If p = h'::t, to show:
         h'::t <= q /\ q <= h::r ==>
         (h' = h) /\ t <= r \/
         h' <> h /\ h'::t <= r    by sublist_def
      If q = [], [] <= h::r = F   by sublist_def
      If q = h''::t', this reduces to:
      (1) h' = h'' /\ t <= t' /\ h'' = h /\ t' <= r ==> t <= r
          Note t <= t' /\ t' <= r ==> t <= r     by induction hypothesis
      (2) h' = h'' /\ t <= t' /\ h'' <> h /\ h''::t' <= r ==> h''::t <= r
          Note t <= t' ==> h''::t <= h''::t'     by sublist_cons
          With h''::t' <= r ==> h''::t <= r      by induction hypothesis
      (3) h' <> h'' /\ h'::t <= t' /\ h'' = h /\ t' <= r ==>
          (h' = h) /\ t <= r \/ h' <> h /\ h'::t <= r
          Note h'::t <= t' ==> t <= t'           by sublist_cons_remove
          With t' <= r ==> t <= r                by induction hypothesis
          Or simply h'::t <= t' /\ t' <= r
                    ==> h'::t <= r               by induction hypothesis
          Hence this is true.
      (4) h' <> h'' /\ h'::t <= t' /\ h'' <> h /\ h''::t' <= r ==>
          (h' = h) /\ t <= r \/ h' <> h /\ h'::t <= r
          Same reasoning as (3).
*)
val sublist_trans = store_thm(
  "sublist_trans",
  ``!p q r:'a list. p <= q /\ q <= r ==> p <= r``,
  Induct_on `r` >-
  fs[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >>
  (Cases_on `q` >> fs[sublist_def]) >-
  metis_tac[] >-
  metis_tac[sublist_cons] >-
  metis_tac[sublist_cons_remove] >>
  metis_tac[sublist_cons_remove]);

(* The above theorems show that sublist is a partial ordering. *)

(* Theorem: p <= q ==> SNOC h p <= SNOC h q *)
(* Proof:
   By induction on q.
   Base: !h p. p <= [] ==> SNOC h p <= SNOC h []
       Note p = []                    by sublist_of_nil
       Thus SNOC h [] <= SNOC h []    by sublist_refl
   Step: !h p. p <= q ==> SNOC h p <= SNOC h q ==>
         !h h' p. p <= h::q ==> SNOC h' p <= SNOC h' (h::q)
       If p = [],
          Note [] <= q                by sublist_nil
          Thus SNOC h' []
            <= SNOC h' q              by induction hypothesis
            <= h::SNOC h' q           by sublist_cons_include
             = SNOC h' (h::q)         by SNOC
       If p = h''::t,
          If h = h'',
          Then t <= q                 by sublist_def, same heads
           ==>      SNOC h' t <= SNOC h' q        by induction hypothesis
           ==>   h::SNOC h' t <= h::SNOC h' q     by rw[sublist_cons
            or SNOC h' (h::t) <= SNOC h' (h::q)   by SNOC
            or      SNOC h' p <= SNOC h' (h::q)   by p = h::t
          If h <> h'',
          Then         p <= q              by sublist_def, different heads
           ==> SNOC h' p <= SNOC h' q      by induction hypothesis
           ==> SNOC h' p <= h::SNOC h' q   by sublist_cons_include
*)
val sublist_snoc = store_thm(
  "sublist_snoc",
  ``!h p q. p <= q ==> SNOC h p <= SNOC h q``,
  Induct_on `q` >-
  rw[sublist_of_nil, sublist_refl] >>
  rw[sublist_def] >>
  Cases_on `p` >-
  rw[sublist_nil, sublist_cons_include] >>
  metis_tac[sublist_def, sublist_cons, SNOC]);

(* Theorem: MEM x ls ==> [x] <= ls *)
(* Proof:
   By induction on ls.
   Base: !x. MEM x [] ==> [x] <= []
      True since MEM x [] = F.
   Step: !x. MEM x ls ==> [x] <= ls ==>
         !h x. MEM x (h::ls) ==> [x] <= h::ls
      If x = h,
         Then [h] <= h::ls     by sublist_nil, sublist_cons
      If x <> h,
         Then MEM h ls         by MEM x (h::ls)
          ==> [x] <= ls        by induction hypothesis
          ==> [x] <= h::ls     by sublist_cons_include
*)
val sublist_member_sing = store_thm(
  "sublist_member_sing",
  ``!ls x. MEM x ls ==> [x] <= ls``,
  Induct >-
  rw[] >>
  rw[] >-
  rw[sublist_nil, GSYM sublist_cons] >>
  rw[sublist_cons_include]);

(* Theorem: TAKE n ls <= ls *)
(* Proof:
   By induction on ls.
   Base: !n. TAKE n [] <= []
      LHS = TAKE n [] = []   by TAKE_def
          <= [] = RHS        by sublist_nil
   Step: !n. TAKE n ls <= ls ==> !h n. TAKE n (h::ls) <= h::ls
      If n = 0,
         TAKE 0 (h::ls)
       = []                  by TAKE_def
      <= h::ls               by sublist_nil
      If n <> 0,
         TAKE n (h::ls)
       = h::TAKE (n - 1) ls             by TAKE_def
       Now    TAKE (n - 1) ls <= ls     by induction hypothesis
      Thus h::TAKE (n - 1) ls <= h::ls  by sublist_cons
*)
val sublist_take = store_thm(
  "sublist_take",
  ``!ls n. TAKE n ls <= ls``,
  Induct >-
  rw[sublist_nil] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[sublist_nil] >>
  rw[GSYM sublist_cons]);

(* Theorem: DROP n ls <= ls *)
(* Proof:
   By induction on ls.
   Base: !n. DROP n [] <= []
      LHS = DROP n [] = []   by DROP_def
          <= [] = RHS        by sublist_nil
   Step: !n. DROP n ls <= ls ==> !h n. DROP n (h::ls) <= h::ls
      If n = 0,
         DROP 0 (h::ls)
       = h::ls               by DROP_def
      <= h::ls               by sublist_refl
      If n <> 0,
         DROP n (h::ls)
       = DROP n ls           by DROP_def
      <= ls                  by induction hypothesis
      <= h::ls               by sublist_cons_include
*)
val sublist_drop = store_thm(
  "sublist_drop",
  ``!ls n. DROP n ls <= ls``,
  Induct >-
  rw[sublist_nil] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[sublist_refl] >>
  rw[sublist_cons_include]);

(* Theorem: ls <> [] ==> TL ls <= ls *)
(* Proof:
   Note TL ls = DROP 1 ls    by TAIL_BY_DROP, ls <> []
   Thus TL ls <= ls          by sublist_drop
*)
val sublist_tail = store_thm(
  "sublist_tail",
  ``!ls. ls <> [] ==> TL ls <= ls``,
  rw[TAIL_BY_DROP, sublist_drop]);

(* Theorem: ls <> [] ==> FRONT ls <= ls *)
(* Proof:
   Note FRONT ls = TAKE (LENGTH ls - 1) ls   by FRONT_BY_TAKE
     so FRONT ls <= ls                       by sublist_take
*)
val sublist_front = store_thm(
  "sublist_front",
  ``!ls. ls <> [] ==> FRONT ls <= ls``,
  rw[FRONT_BY_TAKE, sublist_take]);

(* Theorem: ls <> [] ==> [HD ls] <= ls *)
(* Proof: HEAD_MEM, sublist_member_sing *)
val sublist_head_sing = store_thm(
  "sublist_head_sing",
  ``!ls. ls <> [] ==> [HD ls] <= ls``,
  rw[HEAD_MEM, sublist_member_sing]);

(* Theorem: ls <> [] ==> [LAST ls] <= ls *)
(* Proof: LAST_MEM, sublist_member_sing *)
val sublist_last_sing = store_thm(
  "sublist_last_sing",
  ``!ls. ls <> [] ==> [LAST ls] <= ls``,
  rw[LAST_MEM, sublist_member_sing]);

(* Theorem: l <= ls ==> !P. EVERY P ls ==> EVERY P l` *)
(* Proof:
   By induction on ls.
   Base: !l. l <= [] ==> !P. EVERY P [] ==> EVERY P l
        Note l <= [] ==> l = []        by sublist_of_nil
         and EVERY P [] = T            by implication, or EVERY_DEF
   Step:  !l. l <= ls ==> !P. EVERY P ls ==> EVERY P l ==>
          !h l. l <= h::ls ==> !P. EVERY P (h::ls) ==> EVERY P l
         l <= h::ls
        If l = [], then EVERY P [] = T    by EVERY_DEF
        Otherwise, let l = k::t           by list_CASES
        Note EVERY P (h::ls)
         ==> P h /\ EVERY P ls            by EVERY_DEF
        Then k::t <= h::ls
         ==> k = h /\ t <= ls
          or k <> h /\ k::t <= ls         by sublist_def
        For the first case, h = k,
            P k /\ EVERY P t              by induction hypothesis
        ==> EVERY P (k::t) = EVERY P l    by EVERY_DEF
        For the second case, h <> k,
            EVERY P (k::t) = EVERY P l    by induction hypothesis
*)
val sublist_every = store_thm(
  "sublist_every",
  ``!l ls. l <= ls ==> !P. EVERY P ls ==> EVERY P l``,
  Induct_on `ls` >-
  rw[sublist_of_nil] >>
  (Cases_on `l` >> simp[]) >>
  metis_tac[sublist_def, EVERY_DEF]);

(* ------------------------------------------------------------------------- *)
(* More sublists, applying partial order properties                          *)
(* ------------------------------------------------------------------------- *)

(* Observation:
When doing induction proofs on sublists about p <= q,
Always induct on q, then take cases on p.
*)

(* The following induction theorem is already present during definition:
> theorem "sublist_ind";
val it = |- !P. (!x. P [] x) /\ (!h1 t1. P (h1::t1) []) /\
                (!h1 t1 h2 t2. P t1 t2 /\ P (h1::t1) t2 ==> P (h1::t1) (h2::t2)) ==>
            !v v1. P v v1: thm

Just prove it as an exercise.
*)

(* Theorem: [Induction] For any property P satisfying,
   (a) !y. P [] y = T
   (b) !h x y. P x y /\ sublist x y ==> P (h::x) (h::y)
   (c) !h x y. P x y /\ sublist x y ==> P x (h::y)
   then  !x y. sublist x y ==> P x y.
*)
(* Proof:
   By induction on y.
   Base: !x. x <= [] ==> P x []
      Note x = []            by sublist_of_nil
       and P [] [] = T       by given
   Step: !x. x <= y ==> P x y ==>
         !h x. x <= h::y ==> P x (h::y)
      If x = [], then [] <= h::y = F      by sublist_def
      If x = h'::t,
         If h' = h, t <= y                by sublist_def, same heads
            Thus P t y                    by induction hypothesis
             and P t y /\ t <= y ==> P (h::t) (h::y) = P x (h::y)
         If h' <> h, x <= y               by sublist_def, different heads
            Thus P x y                    by induction hypothesis
             and P x y /\ x <= y ==> P x (h::y).
*)
val sublist_induct = store_thm(
  "sublist_induct",
  ``!P. (!y. P [] y) /\
       (!h x y. P x y /\ x <= y ==> P (h::x) (h::y)) /\
       (!h x y. P x y /\ x <= y ==> P x (h::y)) ==>
        !x y. x <= y ==> P x y``,
  ntac 2 strip_tac >>
  Induct_on `y` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `x` >> fs[sublist_def]));

(* Theorem: [Eliminate append from left]: (x ++ p) <= q ==> sublist p <= q *)
(* Proof:
   By induction on the extra list x.
   The induction step follows from sublist_cons_remove.

   By induction on x.
   Base: !p q. [] ++ p <= q ==> p <= q
       True since [] ++ p = p     by APPEND
   Step: !p q. x ++ p <= q ==> p <= q ==>
         !h p q. h::x ++ p <= q ==> p <= q
            h::x ++ p <= q
        = h::(x ++ p) <= q        by APPEND
       ==>   (x ++ p) <= q        by sublist_cons_remove
       ==>          p <= q        by induction hypothesis
*)
val sublist_append_remove = store_thm(
  "sublist_append_remove",
  ``!p q x. x ++ p <= q ==> p <= q``,
  Induct_on `x` >> metis_tac[sublist_cons_remove, APPEND]);

(* Theorem: [Include append to right] p <= q ==> p <= (x ++ q) *)
(* Proof:
   By induction on list x.
   The induction step follows by sublist_cons_include.

   By induction on x.
   Base: !p q. p <= q ==> p <= [] ++ q
       True since [] ++ q = q     by APPEND
   Step: !p q. p <= q ==> p <= x ++ q ==>
         !h p q. p <= q ==> p <= h::x ++ q
             p <= q
       ==>   p <= x ++ q          by induction hypothesis
       ==>   p <= h::(x ++ q)     by sublist_cons_include
         =   p <= h::x ++ q       by APPEND
*)
val sublist_append_include = store_thm(
  "sublist_append_include",
  ``!p q x. p <= q ==> p <= x ++ q``,
  Induct_on `x` >> metis_tac[sublist_cons_include, APPEND]);

(* Theorem: [append after] p <= (p ++ q) *)
(* Proof:
   By induction on list p, and note that p and (p ++ q) have the same head.
   Base: !q. [] <= [] ++ q, true    by sublist_nil
   Step: !q. p <= p ++ q ==> !h q. h::p <= h::p ++ q
               p <= p ++ q          by induction hypothesis
        ==> h::p <= h::(p ++ q)     by sublist_cons
        ==> h::p <= h::p ++ q       by APPEND
*)
val sublist_append_suffix = store_thm(
  "sublist_append_suffix",
  ``!p q. p <= p ++ q``,
  Induct_on `p` >> rw[sublist_def]);

(* Theorem: [append before] p <= (q ++ p) *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ++ p
      Note [] ++ p = p       by APPEND
       and p <= p            by sublist_refl
   Step: !p. p <= q ++ p ==> !h p. p <= h::q ++ p
           p <= q ++ p       by induction hypothesis
       ==> p <= h::(q ++ p)  by sublist_cons_include
        =  p <= h::q ++ p    by APPEND
*)
val sublist_append_prefix = store_thm(
  "sublist_append_prefix",
  ``!p q. p <= q ++ p``,
  Induct_on `q` >-
  rw[sublist_refl] >>
  rw[sublist_cons_include]);

(* Theorem: [prefix append] p <= q <=> (x ++ p) <= (x ++ q) *)
(* Proof:
   By induction on x.
   Base: !p q. p <= q <=> [] ++ p <= [] ++ q
      Since [] ++ p = p /\ [] ++ q = q           by APPEND
      This is trivially true.
   Step: !p q. p <= q <=> x ++ p <= x ++ q ==>
         !h p q. p <= q <=> h::x ++ p <= h::x ++ q
         p <= q <=>      x ++ p <= x ++ q        by induction hypothesis
                <=> h::(x ++ p) <= h::(x ++ q)   by sublist_cons
                <=>   h::x ++ p <= h::x ++ q     by APPEND
*)
val sublist_prefix = store_thm(
  "sublist_prefix",
  ``!x p q. p <= q <=> (x ++ p) <= (x ++ q)``,
  Induct_on `x` >> metis_tac[sublist_cons, APPEND]);

(* Theorem: [no append to left] !p q. (p ++ q) <= q ==> p = [] *)
(* Proof:
   By induction on q.
   Base: !p. p ++ [] <= [] ==> (p = [])
      Note p ++ [] = p         by APPEND
       and p <= [] ==> p = []  by sublist_of_nil
   Step: !p. p ++ q <= q ==> (p = []) ==>
         !h p. p ++ h::q <= h::q ==> (p = [])
      If p = [], true trivially.
      If p = h'::t,
          (h'::t) ++ (h::q) <= h::q
         =  h'::(t ++ h::q) <= h::q       by APPEND
         If h' = h,
            Then       t ++ h::q <= q     by sublist_def, same heads
              or (t ++ [h]) ++ q <= q     by APPEND
             ==>     t ++ [h] = []        by induction hypothesis
            which is F, hence h' <> h.
         If h' <> h,
            Then       p ++ h::q <= q     by sublist_def, different heads
              or (p ++ [h]) ++ q <= q     by APPEND
             ==> (p ++ [h]) = []          by induction hypothesis
             which is F, hence neither h' <> h.
         All these shows that p = h'::t is impossible.
*)
val sublist_prefix_nil = store_thm(
  "sublist_prefix_nil",
  ``!p q. (p ++ q) <= q ==> (p = [])``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >| [
    `t ++ h::q = (t ++ [h])++ q` by rw[] >>
    `t ++ [h] <> []` by rw[] >>
    metis_tac[],
    `(t ++ h::q) <= q` by metis_tac[sublist_cons_remove] >>
    `t ++ h::q = (t ++ [h])++ q` by rw[] >>
    `t ++ [h] <> []` by rw[] >>
    metis_tac[]
  ]);

(* Theorem: [tail append - if] p <= q ==> (p ++ [h]) <= (q ++ [h]) *)
(* Proof:
   By sublist induction, this is to show:
   (1) [h] <= q ++ [h]
       Note [h] <= [h]         by sublist_refl
        ==> [h] <= q ++ [h]    by sublist_append_prefix
   (2) h::(p ++ [h']) <= h::(q ++ [h'])
       Note      p ++ [h'] <= q ++ [h']        by induction hypothesis
        ==> h::(p ++ [h']) <= h::(q ++ [h'])   by sublist_cons
   (3) p ++ [h'] <= h::(q ++ [h'])
       Note   p ++ [h'] <= q ++ [h']           by induction hypothesis
        ==>   p ++ [h'] <= h::(q + [h'])       by sublist_cons_include
*)
(* First method *)
val sublist_append_if = store_thm(
  "sublist_append_if",
  ``!p q h. p <= q ==> (p ++ [h]) <= (q ++ [h])``,
  Induct_on `q` >-
  rw[sublist_of_nil, sublist_refl] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >-
  (Cases_on `h' = h` >> rw[sublist_append_prefix]) >>
  metis_tac[APPEND]);
(* Second method -- change goal to match *)
val sublist_append_if = store_thm(
  "sublist_append_if",
  ``!p q. p <= q ==> !h. (p ++ [h]) <= (q ++ [h])``,
  ho_match_mp_tac sublist_induct >>
  rw[] >-
  rw[sublist_refl, sublist_append_prefix] >-
  metis_tac[sublist_cons] >>
  rw[sublist_cons_include]);
(* Third method *)
val sublist_append_if = store_thm(
  "sublist_append_if",
  ``!p q h. p <= q ==> (p ++ [h]) <= (q ++ [h])``,
  rw[sublist_snoc, GSYM SNOC_APPEND]);

(* Theorem: [tail append - only if] p ++ [h] <= q ++ [h] ==> p <= q *)
(* Proof:
   By induction on q.
   Base: !p h. p ++ [h] <= [] ++ [h] ==> p <= []
       Note [] ++ [h] = [h]                  by APPEND
        and p ++ [h] <= [h] ==> p = []       by sublist_prefix_nil
        and [] <= []                         by sublist_nil
   Step: !p h. p ++ [h] <= q ++ [h] ==> p <= q ==>
         !h p h'. p ++ [h'] <= h::q ++ [h'] ==> p <= h::q
       If p = [], [h'] <= h::q ++ [h'] = F    by sublist_def
       If p = h''::t,
          h''::t ++ [h'] = h''::(t ++ [h'])   by APPEND
          If h'' = h',
             Then t ++ [h'] <= q ++ [h']      by sublist_def, same heads
              ==>         t <= q              by induction hypothesis
          If h'' <> h',
             Then h''::t ++ [h'] <= q ++ [h'] by sublist_def, different heads
              ==>         h''::t <= q         by induction hypothesis
*)
val sublist_append_only_if = store_thm(
  "sublist_append_only_if",
  ``!p q h. (p ++ [h]) <= (q ++ [h]) ==> p <= q``,
  Induct_on `q` >-
  metis_tac[sublist_prefix_nil, sublist_nil, APPEND] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >-
  metis_tac[] >>
  `h''::(t ++ [h']) = (h''::t) ++ [h']` by rw[] >>
  metis_tac[]);

(* Theorem: [tail append] p <= q <=> p ++ [h] <= q ++ [h] *)
(* Proof: by sublist_append_if, sublist_append_only_if *)
val sublist_append_iff = store_thm(
  "sublist_append_iff",
  ``!p q h. p <= q <=> (p ++ [h]) <= (q ++ [h])``,
  metis_tac[sublist_append_if, sublist_append_only_if]);

(* Theorem: [suffix append] sublist p q ==> sublist (p ++ x) (q ++ x) *)
(* Proof:
   By induction on x.
   Base: !p q. p <= q <=> p ++ [] <= q ++ []
      True by p ++ [] = p, q ++ [] = q           by APPEND
   Step: !p q. p <= q <=> p ++ x <= q ++ x ==>
         !h p q. p <= q <=> p ++ h::x <= q ++ h::x
                         p <= q
       <=>      (p ++ [h]) <= (q ++ [h])         by sublist_append_iff
       <=> (p ++ [h]) ++ x <= (q ++ [h]) ++ x    by induction hypothesis
       <=>     p ++ (h::x) <= q ++ (h::x)        by APPEND
*)
val sublist_suffix = store_thm(
  "sublist_suffix",
  ``!x p q. p <= q <=> (p ++ x) <= (q ++ x)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  `!z. z ++ h::x = (z ++ [h]) ++ x` by rw[] >>
  metis_tac[sublist_append_iff]);

(* Theorem : (a <= b) /\ (c <= d) ==> (a ++ c) <= (b ++ d) *)
(* Proof:
   Note a ++ c <= a ++ d    by sublist_prefix
    and a ++ d <= b ++ d    by sublist_suffix
    ==> a ++ c <= b ++ d    by sublist_trans
*)
val sublist_append_pair = store_thm(
  "sublist_append_pair",
  ``!a b c d. (a <= b) /\ (c <= d) ==> (a ++ c) <= (b ++ d)``,
  metis_tac[sublist_prefix, sublist_suffix, sublist_trans]);

(* Theorem: [Extended Append, or Decomposition] (h::t) <= q <=> ?x y. (q = x ++ (h::y)) /\ (t <= y) *)
(* Proof:
   By induction on list q.
   Base case is to prove:
     sublist (h::t) []  <=> ?x y. ([] = x ++ (h::y)) /\ (sublist t y)
     Hypothesis sublist (h::t) [] is F by SUBLIST_NIL.
     In the conclusion, [] cannot be decomposed, hence implication is valid.
   Step case is to prove:
     (sublist (h::t) q  <=> ?x y. (q = x ++ (h::y)) /\ (sublist t y)) ==>
     (sublist (h::t) (h'::q)  <=> ?x y. (h'::q = x ++ (h::y)) /\ (sublist t y))
     Applying SUBLIST definition and split the if-and-only-if parts, there are 4 cases:
     When h = h', if part:
       sublist (h::t) (h::q) ==> ?x y. (h::q = x ++ (h::y)) /\ (sublist t y)
       For this case, choose x=[], y=q, and sublist (h::t) (h::q) = sublist t q, by SUBLIST same head.
     When h = h', only-if part:
       ?x y. (h::q = x ++ (h::y)) /\ (sublist t y) ==> sublist (h::t) (h::q)
       Take cases on x.
       When x = [],
         h::q = h::y ==> q = y,
         hence sublist t y = sublist t q ==> sublist (h::t) (h::q) by SUBLIST same head.
       When x = h''::t',
         h::q = (h''::t') ++ (h::y) = h''::(t' ++ (h::y)) ==>
         q = t' ++ (h::y),
         hence sublist t y ==> sublist t q (by SUBLIST_APPENDR_I) ==> sublist (h::t) (h::q).
     When ~(h=h'), if part:
       sublist (h::t) (h'::q) ==> ?x y. (h'::q = x ++ (h::y)) /\ (sublist t y)
       From hypothesis,
             sublist (h::t) (h'::q)
           = sublist (h::t) q           when ~(h=h'), by SUBLIST definition
         ==> ?x1 y1. (q = x1 ++ (h::y1)) /\ (sublist t y1))  by inductive hypothesis
         Now (h'::q) = (h'::(x1 ++ (h::y1)) = (h'::x1) ++ (h::y1) by APPEND associativity
         So taking x = h'::x1, y = y1, this gives the conclusion.
     When ~(h=h'), only-if part:
       ?x y. (h'::q = x ++ (h::y)) /\ (sublist t y) ==> sublist (h::t) (h'::q)
       The case x = [] is impossible by list equality, since ~(h=h').
       Hence x = h'::t', giving:
            q = t'++(h::y) /\ (sublist t y)
          = sublist (h::t) q              by inductive hypothesis (only-if)
        ==> sublist (h::t) (h'::q)        by SUBLIST, different head.
*)
val sublist_append_extend = store_thm(
  "sublist_append_extend",
  ``!h t q. h::t <= q  <=> ?x y. (q = x ++ (h::y)) /\ (t <= y)``,
  ntac 2 strip_tac >>
  Induct >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `h = h'` >> rw[EQ_IMP_THM]) >| [
    `h::q = [] ++ [h] ++ q` by rw[] >>
    metis_tac[sublist_cons],
    `h::t <= h::y` by rw[GSYM sublist_cons] >>
    `x ++ [h] ++ y = x ++ (h::y)` by rw[] >>
    metis_tac[sublist_append_include],
    `h::t <= q` by metis_tac[sublist_def] >>
    metis_tac[APPEND, APPEND_ASSOC],
    `h::t <= h::y` by rw[GSYM sublist_cons] >>
    `x ++ [h] ++ y = x ++ (h::y)` by rw[] >>
    metis_tac[sublist_append_include]
  ]);


(* ------------------------------------------------------------------------- *)
(* Application of sublist.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p <= q ==> (MAP f p) <= (MAP f q) *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ==> MAP f p <= MAP f []
         Note p = []       by sublist_of_nil
          and MAP f []     by MAP
           so [] <= []     by sublist_nil
   Step: !p. p <= q ==> MAP f p <= MAP f q ==>
         !h p. p <= h::q ==> MAP f p <= MAP f (h::q)
         If p = [], [] <= h::q = F          by sublist_def
         If p = h'::t,
            If h' = h,
               Then             t <= q             by sublist_def, same heads
                ==>       MAP f t <= MAP f q       by induction hypothesis
                ==>    h::MAP f t <= h::MAP f q    by sublist_cons
                ==>  MAP f (h::t) <= MAP f (h::q)  by MAP
                 or       MAP f p <= MAP f (h::q)  by p = h::t
            If h' <> h,
               Then          p <= q                by sublist_def, different heads
               ==>     MAP f p <= MAP f q          by induction hypothesis
               ==>     MAP f p <= h::MAP f q       by sublist_cons_include
                or     MAP f p <= MAP f (h::q)     by MAP
*)
val MAP_SUBLIST = store_thm(
  "MAP_SUBLIST",
  ``!f p q. p <= q ==> (MAP f p) <= (MAP f q)``,
  strip_tac >>
  Induct_on `q` >-
  rw[sublist_of_nil, sublist_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[sublist_def]) >>
  metis_tac[sublist_def, sublist_cons_include, MAP]);

(* Theorem: l1 <= l2 ==> SUM l1 <= SUM l2 *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ==> SUM p <= SUM []
      Note p = []        by sublist_of_nil
       and SUM [] = 0    by SUM
      Hence true.
   Step: !p. p <= q ==> SUM p <= SUM q ==>
         !h p. p <= h::q ==> SUM p <= SUM (h::q)
      If p = [], [] <= h::q = F         by sublist_def
      If p = h'::t,
         If h' = h,
         Then          t <= q           by sublist_def, same heads
          ==>      SUM t <= SUM q       by induction hypothesis
          ==>  h + SUM t <= h + SUM q   by arithmetic
          ==> SUM (h::t) <= SUM (h::q)  by SUM
           or      SUM p <= SUM (h::q)  by p = h::t
         If h' <> h,
         Then          p <= q           by sublist_def, different heads
          ==>      SUM p <= SUM q       by induction hypothesis
          ==>      SUM p <= h + SUM q   by arithmetic
          ==>      SUM p <= SUM (h::q)  by SUM
*)
val SUM_SUBLIST = store_thm(
  "SUM_SUBLIST",
  ``!p q. p <= q ==> SUM p <= SUM q``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >>
  `h' + SUM t <= SUM q` by metis_tac[SUM] >>
  decide_tac);

(* Theorem: m < n ==> [m; n] <= [m .. n] *)
(* Proof:
   By induction on n.
   Base: !m. m < 0 ==> [m; 0] <= [m .. 0], true       by m < 0 = F.
   Step: !m. m < n ==> [m; n] <= [m .. n] ==>
         !m. m < SUC n ==> [m; SUC n] <= [m .. SUC n]
        Note m < SUC n means m <= n.
        If m = n, LHS = [n; SUC n]
                  RHS = [n .. (n + 1)] = [n; SUC n]   by ADD1
                      = LHS, thus true                by sublist_refl
        If m < n,              [m; n] <= [m .. n]     by induction hypothesis
                  SNOC (SUC n) [m; n] <= SNOC (SUC n) [m .. n] by sublist_snoc
                        [m; n; SUC n] <= [m .. SUC n]          by SNOC, listRangeINC_SNOC
           But [m; SUC n] <= [m; n; SUC n]            by sublist_def
           Thus [m; SUC n] <= [m .. SUC n]            by sublist_trans
*)
val listRangeINC_sublist = store_thm(
  "listRangeINC_sublist",
  ``!m n. m < n ==> [m; n] <= [m .. n]``,
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `(m = n) \/ m < n` by decide_tac >| [
    rw[listRangeINC_def, ADD1] >>
    rw[sublist_refl],
    `[m; n] <= [m .. n]` by rw[] >>
    `SNOC (SUC n) [m; n] <= SNOC (SUC n) [m .. n]` by rw[sublist_snoc] >>
    `SNOC (SUC n) [m; n] = [m; n; SUC n]` by rw[] >>
    `SNOC (SUC n) [m .. n] = [m .. SUC n]` by rw[listRangeINC_SNOC, ADD1] >>
    `[m; SUC n] <= [m; n; SUC n]` by rw[sublist_def] >>
    metis_tac[sublist_trans]
  ]);

(* Theorem: m + 1 < n ==> [m; (n - 1)] <= [m ..< n] *)
(* Proof:
   By induction on n.
   Base: !m. m + 1 < 0 ==> [m; 0 - 1] <= [m ..< 0], true  by m + 1 < 0 = F.
   Step: !m. m + 1 < n ==> [m; n - 1] <= [m ..< n] ==>
         !m. m + 1 < SUC n ==> [m; SUC n - 1] <= [m ..< SUC n]
        Note m + 1 < SUC n means m + 1 <= n.
        If m + 1 = n, LHS = [m; SUC n - 1] = [m; n]
                  RHS = [m ..< (n + 1)] = [m; n]          by ADD1
                      = LHS, thus true                    by sublist_refl
        If m + 1 < n,    [m; n - 1] <= [m ..< n]          by induction hypothesis
                  SNOC n [m; n - 1] <= SNOC n [m ..< n]   by sublist_snoc
                      [m; n - 1; n] <= [m ..< SUC n]      by SNOC, listRangeLHI_SNOC, ADD1
           But [m; SUC n - 1] <= [m; n] <= [m; n - 1; n]  by sublist_def
           Thus [m; SUC n - 1] <= [m ..< SUC n]           by sublist_trans
*)
val listRangeLHI_sublist = store_thm(
  "listRangeLHI_sublist",
  ``!m n. m + 1 < n ==> [m; (n - 1)] <= [m ..< n]``,
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `SUC n - 1 = n` by decide_tac >>
  `(m + 1 = n) \/ m + 1 < n` by decide_tac >| [
    rw[listRangeLHI_def, ADD1] >>
    rw[sublist_refl],
    `[m; n - 1] <= [m ..< n]` by rw[] >>
    `SNOC n [m; n - 1] <= SNOC n [m ..< n]` by rw[sublist_snoc] >>
    `SNOC n [m; n - 1] = [m; n - 1; n]` by rw[] >>
    `SNOC n [m ..< n] = [m ..< SUC n]` by rw[listRangeLHI_SNOC, ADD1] >>
    `[m; SUC n - 1] <= [m; n - 1; n]` by rw[sublist_def] >>
    metis_tac[sublist_trans]
  ]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
