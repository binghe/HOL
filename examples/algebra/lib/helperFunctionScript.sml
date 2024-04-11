(* ------------------------------------------------------------------------- *)
(* Helper Theorems - a collection of useful results -- for Functions.        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperFunction";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory prim_recTheory arithmeticTheory;
open listTheory rich_listTheory listRangeTheory;
open dividesTheory gcdTheory gcdsetTheory;

open numberTheory helperListTheory helperSetTheory;

(* ------------------------------------------------------------------------- *)
(* Helper Function Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading/syntax:
   (x == y) f          = fequiv x y f
   feq                 = flip (flip o fequiv)
   RISING f            = !x:num. x <= f x
   FALLING f           = !x:num. f x <= x
   SQRT n              = ROOT 2 n
   LOG2 n              = LOG 2 n
   PAIRWISE_COPRIME s  = !x y. x IN s /\ y IN s /\ x <> y ==> coprime x y
   tops b n            = b ** n - 1
   nines n             = tops 10 n
*)
(* Definitions and Theorems (# are exported):

   Function Equivalence as Relation:
   fequiv_def         |- !x y f. fequiv x y f <=> (f x = f y)
   fequiv_refl        |- !f x. (x == x) f
   fequiv_sym         |- !f x y. (x == y) f ==> (y == x) f
   fequiv_trans       |- !f x y z. (x == y) f /\ (y == z) f ==> (x == z) f
   fequiv_equiv_class |- !f. (\x y. (x == y) f) equiv_on univ(:'a)

   Function-based Equivalence:
   feq_class_def       |- !s f n. feq_class f s n = {x | x IN s /\ (f x = n)}
   feq_class_element   |- !f s n x. x IN feq_class f s n <=> x IN s /\ (f x = n)
   feq_class_property  |- !f s x. feq_class f s (f x) = {y | y IN s /\ feq f x y}
   feq_class_fun       |- !f s. feq_class f s o f = (\x. {y | y IN s /\ feq f x y})


   feq_equiv                  |- !s f. feq f equiv_on s
   feq_partition              |- !s f. partition (feq f) s = IMAGE (feq_class f s o f) s
   feq_partition_element      |- !s f t. t IN partition (feq f) s <=>
                                 ?z. z IN s /\ !x. x IN t <=> x IN s /\ (f x = f z)
   feq_partition_element_exists
                              |- !f s x. x IN s <=> ?e. e IN partition (feq f) s /\ x IN e
   feq_partition_element_not_empty
                              |- !f s e. e IN partition (feq f) s ==> e <> {}
   feq_class_eq_preimage      |- !f s. feq_class f s = preimage f s
   feq_partition_by_preimage  |- !f s. partition (feq f) s = IMAGE (preimage f s o f) s
   feq_sum_over_partition     |- !s. FINITE s ==> !f g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s)

   finite_card_by_feq_partition   |- !s. FINITE s ==> !f. CARD s = SIGMA CARD (partition (feq f) s)
   finite_card_by_image_preimage  |- !s. FINITE s ==> !f. CARD s = SIGMA CARD (IMAGE (preimage f s o f) s)
   finite_card_surj_by_image_preimage
                       |- !f s t. FINITE s /\ SURJ f s t ==>
                                  CARD s = SIGMA CARD (IMAGE (preimage f s) t)
   preimage_image_bij  |- !f s. BIJ (preimage f s) (IMAGE f s) (partition (feq f) s):

   Condition for surjection to be a bijection:
   inj_iff_partition_element_sing
                       |- !f s. INJ f s (IMAGE f s) <=>
                                !e. e IN partition (feq f) s ==> SING e
   inj_iff_partition_element_card_1
                       |- !f s. FINITE s ==>
                                (INJ f s (IMAGE f s) <=>
                                 !e. e IN partition (feq f) s ==> CARD e = 1)
   FINITE_SURJ_IS_INJ  |- !f s t. FINITE s /\
                                  CARD s = CARD t /\ SURJ f s t ==> INJ f s t
   FINITE_SURJ_IS_BIJ  |- !f s t. FINITE s /\
                                  CARD s = CARD t /\ SURJ f s t ==> BIJ f s t

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

   More FUNPOW Theorems:
   LINV_permutes       |- !f s. f PERMUTES s ==> LINV f s PERMUTES s
   FUNPOW_permutes     |- !f s n. f PERMUTES s ==> FUNPOW f n PERMUTES s
   FUNPOW_closure      |- !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s
   FUNPOW_LINV_permutes|- !f s n. f PERMUTES s ==> FUNPOW (LINV f s) n PERMUTES s
   FUNPOW_LINV_closure |- !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n x IN s
   FUNPOW_LINV_EQ      |- !f s x n. f PERMUTES s /\ x IN s ==>
                                    FUNPOW f n (FUNPOW (LINV f s) n x) = x
   FUNPOW_EQ_LINV      |- !f s x n. f PERMUTES s /\ x IN s ==>
                                    FUNPOW (LINV f s) n (FUNPOW f n x) = x
   FUNPOW_SUB_LINV1    |- !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
                          FUNPOW f (n - m) x = FUNPOW f n (FUNPOW (LINV f s) m x)
   FUNPOW_SUB_LINV2    |- !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
                          FUNPOW f (n - m) x = FUNPOW (LINV f s) m (FUNPOW f n x)
   FUNPOW_LINV_SUB1    |- !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
                          FUNPOW (LINV f s) (n - m) x = FUNPOW (LINV f s) n (FUNPOW f m x)
   FUNPOW_LINV_SUB2    |- !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
                          FUNPOW (LINV f s) (n - m) x = FUNPOW f m (FUNPOW (LINV f s) n x)
   FUNPOW_LINV_INV     |- !f s x y n. f PERMUTES s /\ x IN s /\ y IN s ==>
                          (x = FUNPOW f n y <=> y = FUNPOW (LINV f s) n x)

   FUNPOW with incremental cons:
   FUNPOW_cons_head    |- !f n ls. HD (FUNPOW (\ls. f (HD ls)::ls) n ls) = FUNPOW f n (HD ls)
   FUNPOW_cons_eq_map_0|- !f u n. FUNPOW (\ls. f (HD ls)::ls) n [u] =
                                  MAP (\j. FUNPOW f j u) (n downto 0)
   FUNPOW_cons_eq_map_1|- !f u n. 0 < n ==>
                                  FUNPOW (\ls. f (HD ls)::ls) (n - 1) [f u] =
                                  MAP (\j. FUNPOW f j u) (n downto 1)

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
   FACT_iff            |- !f. f = FACT <=> f 0 = 1 /\ !n. f (SUC n) = SUC n * f n

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
   GCD_REDUCE_BY_COPRIME
                       |- !m n k. coprime m k ==> gcd m (k * n) = gcd m n
   gcd_le              |- !m n. 0 < m /\ 0 < n ==> gcd m n <= m /\ gcd m n <= n
   gcd_divides_iff     |- !a b c. 0 < a ==> (gcd a b divides c <=> ?p q. p * a = q * b + c)
   gcd_linear_thm      |- !a b c. 0 < a ==> (gcd a b divides c <=> ?p q. p * a = q * b + c)
   gcd_linear_mod_thm  |- !n a b. 0 < n /\ 0 < a ==> ?p q. (p * a + q * b) MOD n = gcd a b MOD n
   gcd_linear_mod_1    |- !a b. 0 < a ==> ?q. (q * b) MOD a = gcd a b MOD a
   gcd_linear_mod_2    |- !a b. 0 < b ==> ?p. (p * a) MOD b = gcd a b MOD b
   gcd_linear_mod_prod |- !a b. 0 < a /\ 0 < b ==>
                          ?p q. (p * a + q * b) MOD (a * b) = gcd a b MOD (a * b)
   coprime_linear_mod_prod
                       |- !a b. 0 < a /\ 0 < b /\ coprime a b ==>
                          ?p q. (p * a + q * b) MOD (a * b) = 1 MOD (a * b)
   gcd_multiple_linear_mod_thm
                       |- !n a b c. 0 < n /\ 0 < a /\ gcd a b divides c ==>
                              ?p q. (p * a + q * b) MOD n = c MOD n
   gcd_multiple_linear_mod_prod
                       |- !a b c. 0 < a /\ 0 < b /\ gcd a b divides c ==>
                            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)
   coprime_multiple_linear_mod_prod
                       |- !a b c. 0 < a /\ 0 < b /\ coprime a b ==>
                            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)

   Coprime Theorems:
   coprime_SUC         |- !n. coprime n (n + 1)
   coprime_PRE         |- !n. 0 < n ==> coprime (n - 1) n
   coprime_0L          |- !n. coprime 0 n <=> (n = 1)
   coprime_0R          |- !n. coprime n 0 <=> (n = 1)
   coprime_0           |- !n. (coprime 0 n <=> n = 1) /\ (coprime n 0 <=> n = 1)
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
   coprime_common_factor        |- !a b c. coprime a b /\ c divides a /\ c divides b ==> c = 1
   prime_not_divides_coprime    |- !n p. prime p /\ ~(p divides n) ==> coprime p n
   prime_not_coprime_divides    |- !n p. prime p /\ ~(coprime p n) ==> p divides n
   coprime_prime_factor_coprime |- !n p. 1 < n /\ prime p /\ p divides n ==>
                                   !k. coprime n k ==> coprime p k
   coprime_all_le_imp_lt     |- !n. 1 < n ==> !m. (!j. 0 < j /\ j <= m ==> coprime n j) ==> m < n
   coprime_condition         |- !m n. (!j. 1 < j /\ j <= m ==> ~(j divides n)) <=>
                                      !j. 1 < j /\ j <= m ==> coprime j n
   coprime_by_le_not_divides |- !m n. 1 < m /\ (!j. 1 < j /\ j <= m ==> ~(j divides n)) ==> coprime m n
   coprime_by_prime_factor   |- !m n. coprime m n <=> !p. prime p ==> ~(p divides m /\ p divides n)
   coprime_by_prime_factor_le|- !m n. 0 < m /\ 0 < n ==>
                                     (coprime m n <=>
                                  !p. prime p /\ p <= m /\ p <= n ==> ~(p divides m /\ p divides n))
   coprime_linear_mult       |- !a b p q. coprime a b /\ coprime p b /\ coprime q a ==>
                                          coprime (p * a + q * b) (a * b)
   coprime_linear_mult_iff   |- !a b p q. coprime a b ==>
                                         (coprime p b /\ coprime q a <=> coprime (p * a + q * b) (a * b))
   coprime_prime_power       |- !p n. prime p /\ 0 < n ==> !q. coprime q (p ** n) <=> ~(p divides q)
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
Definition fequiv_def:
  fequiv x y f <=> (f x = f y)
End
Overload "==" = ``fequiv``
val _ = set_fixity "==" (Infix(NONASSOC, 450));

(* Theorem: [Reflexive] (x == x) f *)
(* Proof: by definition,
   and f x = f x.
*)
Theorem fequiv_refl[simp]:  !f x. (x == x) f
Proof rw_tac std_ss[fequiv_def]
QED

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

Overload feq = “flip (flip o fequiv)”
Overload feq_class[inferior] = “preimage”

(* Theorem: x IN feq_class f s n <=> x IN s /\ (f x = n) *)
(* Proof: by feq_class_def *)
Theorem feq_class_element = in_preimage

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
  rw[in_preimage, EXTENSION, fequiv_def] >> metis_tac[]);

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
  rw[equiv_on_def, fequiv_def] >>
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
  rw[partition_def, fequiv_def, in_preimage, EXTENSION, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: t IN partition (feq f) s <=> ?z. z IN s /\ (!x. x IN t <=> x IN s /\ (f x = f z)) *)
(* Proof: by feq_partition, feq_class_def, EXTENSION *)
Theorem feq_partition_element:
  !s f t. t IN partition (feq f) s <=>
          ?z. z IN s /\ (!x. x IN t <=> x IN s /\ (f x = f z))
Proof
  rw[feq_partition, in_preimage, EXTENSION] >> metis_tac[]
QED

(* Theorem: x IN s <=> ?e. e IN partition (feq f) s /\ x IN e *)
(* Proof:
   Note (feq f) equiv_on s         by feq_equiv
   This result follows             by partition_element_exists
*)
Theorem feq_partition_element_exists:
  !f s x. x IN s <=> ?e. e IN partition (feq f) s /\ x IN e
Proof
  simp[feq_equiv, partition_element_exists]
QED

(* Theorem: e IN partition (feq f) s ==> e <> {} *)
(* Proof:
   Note (feq f) equiv_on s     by feq_equiv
     so e <> {}                by partition_element_not_empty
*)
Theorem feq_partition_element_not_empty:
  !f s e. e IN partition (feq f) s ==> e <> {}
Proof
  metis_tac[feq_equiv, partition_element_not_empty]
QED

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
val feq_partition_by_preimage = feq_partition

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
  rw[feq_equiv, partition_CARD, GSYM feq_partition]);

(* Theorem: FINITE s /\ SURJ f s t ==>
            CARD s = SIGMA CARD (IMAGE (preimage f s) t) *)
(* Proof:
     CARD s
   = SIGMA CARD (IMAGE (preimage f s o f) s)           by finite_card_by_image_preimage
   = SIGMA CARD (IMAGE (preimage f s) (IMAGE f s))     by IMAGE_COMPOSE
   = SIGMA CARD (IMAGE (preimage f s) t)               by IMAGE_SURJ
*)
Theorem finite_card_surj_by_image_preimage:
  !f s t. FINITE s /\ SURJ f s t ==>
          CARD s = SIGMA CARD (IMAGE (preimage f s) t)
Proof
  rpt strip_tac >>
  `CARD s = SIGMA CARD (IMAGE (preimage f s o f) s)` by rw[finite_card_by_image_preimage] >>
  `_ = SIGMA CARD (IMAGE (preimage f s) (IMAGE f s))` by rw[IMAGE_COMPOSE] >>
  `_ = SIGMA CARD (IMAGE (preimage f s) t)` by fs[IMAGE_SURJ] >>
  simp[]
QED

(* Theorem: BIJ (preimage f s) (IMAGE f s) (partition (feq f) s) *)
(* Proof:
   Let g = preimage f s, t = IMAGE f s.
   Note INJ g t (POW s)                        by preimage_image_inj
     so BIJ g t (IMAGE g t)                    by INJ_IMAGE_BIJ
    But IMAGE g t
      = IMAGE (preimage f s) (IMAGE f s)       by notation
      = IMAGE (preimage f s o f) s             by IMAGE_COMPOSE
      = partition (feq f) s                    by feq_partition_by_preimage
   Thus BIJ g t (partition (feq f) s)          by above
*)
Theorem preimage_image_bij:
  !f s. BIJ (preimage f s) (IMAGE f s) (partition (feq f) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `g = preimage f s` >>
  qabbrev_tac `t = IMAGE f s` >>
  `BIJ g t (IMAGE g t)` by metis_tac[preimage_image_inj, INJ_IMAGE_BIJ] >>
  simp[IMAGE_COMPOSE, feq_partition, Abbr`g`, Abbr`t`]
QED

(* ------------------------------------------------------------------------- *)
(* Condition for surjection to be a bijection.                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> SING e *)
(* Proof:
   If part: e IN partition (feq f) s ==> SING e
          e IN partition (feq f) s
      <=> ?z. z IN s /\ !x. x IN e <=> x IN s /\ f x = f z
                                               by feq_partition_element
      Thus z IN e, so e <> {}                  by MEMBER_NOT_EMPTY
       and !x. x IN e ==> x = z                by INJ_DEF
        so SING e                              by SING_ONE_ELEMENT
   Only-if part: !e. e IN partition (feq f) s ==> SING e ==> INJ f s (IMAGE f s)
      By INJ_DEF, IN_IMAGE, this is to show:
         !x y. x IN s /\ y IN s /\ f x = f y ==> x = y
      Note ?e. e IN (partition (feq f) s) /\ x IN e
                                               by feq_partition_element_exists
       and y IN e                              by feq_partition_element
      then SING e                              by implication
        so x = y                               by IN_SING
*)
Theorem inj_iff_partition_element_sing:
  !f s. INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> SING e
Proof
  rw[EQ_IMP_THM] >| [
    fs[feq_partition_element, INJ_DEF] >>
    `e <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
    simp[SING_ONE_ELEMENT],
    rw[INJ_DEF] >>
    `?e. e IN (partition (feq f) s) /\ x IN e` by fs[GSYM feq_partition_element_exists] >>
    `y IN e` by metis_tac[feq_partition_element] >>
    metis_tac[SING_DEF, IN_SING]
  ]
QED

(* Theorem: FINITE s ==>
            (INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> CARD e = 1) *)
(* Proof:
       INJ f s (IMAGE f s)
   <=> !e. e IN (partition (feq f) s) ==> SING e       by inj_iff_partition_element_sing
   <=> !e. e IN (partition (feq f) s) ==> CARD e = 1   by FINITE_partition, CARD_EQ_1
*)
Theorem inj_iff_partition_element_card_1:
  !f s. FINITE s ==>
        (INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> CARD e = 1)
Proof
  metis_tac[inj_iff_partition_element_sing, FINITE_partition, CARD_EQ_1]
QED

(* Idea: for a finite domain, with target same size, surjection means injection. *)

(* Theorem: FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> INJ f s t *)
(* Proof:
   Let p = partition (feq f) s.
   Note IMAGE f s = t              by IMAGE_SURJ
     so FINITE t                   by IMAGE_FINITE
    and CARD s = SIGMA CARD p      by finite_card_by_feq_partition
    and CARD t = CARD p            by preimage_image_bij, bij_eq_card
   Thus CARD p = SIGMA CARD p      by given CARD s = CARD t
    Now FINITE p                   by FINITE_partition
    and !e. e IN p ==> FINITE e    by FINITE_partition
    and !e. e IN p ==> e <> {}     by feq_partition_element_not_empty
     so !e. e IN p ==> CARD e <> 0 by CARD_EQ_0
   Thus !e. e IN p ==> CARD e = 1  by card_eq_sigma_card
     or INJ f s (IMAGE f s)        by inj_iff_partition_element_card_1
     so INJ f s t                  by IMAGE f s = t
*)
Theorem FINITE_SURJ_IS_INJ:
  !f s t. FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> INJ f s t
Proof
  rpt strip_tac >>
  imp_res_tac finite_card_by_feq_partition >>
  first_x_assum (qspec_then `f` strip_assume_tac) >>
  qabbrev_tac `p = partition (feq f) s` >>
  `IMAGE f s = t` by fs[IMAGE_SURJ] >>
  `FINITE t` by rw[] >>
  `CARD t = CARD p` by metis_tac[preimage_image_bij, FINITE_BIJ_CARD] >>
  `FINITE p /\ !e. e IN p ==> FINITE e` by metis_tac[FINITE_partition] >>
  `!e. e IN p ==> CARD e <> 0` by metis_tac[feq_partition_element_not_empty, CARD_EQ_0] >>
  `!e. e IN p ==> CARD e = 1` by metis_tac[card_eq_sigma_card] >>
  metis_tac[inj_iff_partition_element_card_1]
QED

(* Finally! show that SURJ can imply BIJ. *)

(* Theorem: FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> BIJ f s t *)
(* Proof:
   Note INJ f s t              by FINITE_SURJ_IS_INJ
     so BIJ f s t              by BIJ_DEF, SURJ f s t
*)
Theorem FINITE_SURJ_IS_BIJ:
  !f s t. FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> BIJ f s t
Proof
  simp[FINITE_SURJ_IS_INJ, BIJ_DEF]
QED

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

(* ------------------------------------------------------------------------- *)
(* More FUNPOW Theorems                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f PERMUTES s ==> (LINV f s) PERMUTES s *)
(* Proof: by BIJ_LINV_BIJ *)
Theorem LINV_permutes:
  !f s. f PERMUTES s ==> (LINV f s) PERMUTES s
Proof
  rw[BIJ_LINV_BIJ]
QED

(* Theorem: f PERMUTES s ==> (FUNPOW f n) PERMUTES s *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 PERMUTES s
      Note FUNPOW f 0 = I         by FUN_EQ_THM, FUNPOW_0
       and I PERMUTES s           by BIJ_I_SAME
      thus true.
   Step: f PERMUTES s /\ FUNPOW f n PERMUTES s ==>
         FUNPOW f (SUC n) PERMUTES s
      Note FUNPOW f (SUC n)
         = f o (FUNPOW f n)       by FUN_EQ_THM, FUNPOW_SUC
      Thus true                   by BIJ_COMPOSE
*)
Theorem FUNPOW_permutes:
  !f s n. f PERMUTES s ==> (FUNPOW f n) PERMUTES s
Proof
  rpt strip_tac >>
  Induct_on `n` >| [
    `FUNPOW f 0 = I` by rw[FUN_EQ_THM] >>
    simp[BIJ_I_SAME],
    `FUNPOW f (SUC n) = f o (FUNPOW f n)` by rw[FUN_EQ_THM, FUNPOW_SUC] >>
    metis_tac[BIJ_COMPOSE]
  ]
QED

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

(* Theorem: f PERMUTES s ==> FUNPOW (LINV f s) n PERMUTES s *)
(* Proof: by LINV_permutes, FUNPOW_permutes *)
Theorem FUNPOW_LINV_permutes:
  !f s n. f PERMUTES s ==> FUNPOW (LINV f s) n PERMUTES s
Proof
  simp[LINV_permutes, FUNPOW_permutes]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s *)
(* Proof:
   By induction on n.
   Base: FUNPOW (LINV f s) 0 x IN s
         Since FUNPOW (LINV f s) 0 x = x   by FUNPOW_0
         This is trivially true.
   Step: FUNPOW (LINV f s) n x IN s ==> FUNPOW (LINV f s) (SUC n) x IN s
           FUNPOW (LINV f s) (SUC n) x
         = (LINV f s) (FUNPOW (LINV f s) n x)   by FUNPOW_SUC
         But FUNPOW (LINV f s) n x IN s         by induction hypothesis
         and (LINV f s) PERMUTES s              by LINV_permutes
          so (LINV f s) (FUNPOW (LINV f s) n x) IN s
                                                by BIJ_ELEMENT
*)
Theorem FUNPOW_LINV_closure:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n x IN s
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `(LINV f s) PERMUTES s` by rw[LINV_permutes] >>
  prove_tac[FUNPOW_SUC, BIJ_ELEMENT]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW f n (FUNPOW (LINV f s) n x) = x *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 (FUNPOW (LINV f s) 0 x) = x
           FUNPOW f 0 (FUNPOW (LINV f s) 0 x)
         = FUNPOW f 0 x              by FUNPOW_0
         = x                         by FUNPOW_0
   Step: FUNPOW f n (FUNPOW (LINV f s) n x) = x ==>
         FUNPOW f (SUC n) (FUNPOW (LINV f s) (SUC n) x) = x
         Note (FUNPOW (LINV f s) n x) IN s        by FUNPOW_LINV_closure
           FUNPOW f (SUC n) (FUNPOW (LINV f s) (SUC n) x)
         = FUNPOW f (SUC n) ((LINV f s) (FUNPOW (LINV f s) n x))  by FUNPOW_SUC
         = FUNPOW f n (f ((LINV f s) (FUNPOW (LINV f s) n x)))    by FUNPOW
         = FUNPOW f n (FUNPOW (LINV f s) n x)                     by BIJ_LINV_THM
         = x                                      by induction hypothesis
*)
Theorem FUNPOW_LINV_EQ:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW f n (FUNPOW (LINV f s) n x) = x
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `FUNPOW f (SUC n) (FUNPOW (LINV f s) (SUC n) x)
    = FUNPOW f (SUC n) ((LINV f s) (FUNPOW (LINV f s) n x))` by rw[FUNPOW_SUC] >>
  `_ = FUNPOW f n (f ((LINV f s) (FUNPOW (LINV f s) n x)))` by rw[FUNPOW] >>
  `_ = FUNPOW f n (FUNPOW (LINV f s) n x)` by metis_tac[BIJ_LINV_THM, FUNPOW_LINV_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n (FUNPOW f n x) = x *)
(* Proof:
   By induction on n.
   Base: FUNPOW (LINV f s) 0 (FUNPOW f 0 x) = x
           FUNPOW (LINV f s) 0 (FUNPOW f 0 x)
         = FUNPOW (LINV f s) 0 x     by FUNPOW_0
         = x                         by FUNPOW_0
   Step: FUNPOW (LINV f s) n (FUNPOW f n x) = x ==>
         FUNPOW (LINV f s) (SUC n) (FUNPOW f (SUC n) x) = x
         Note (FUNPOW f n x) IN s                 by FUNPOW_closure
           FUNPOW (LINV f s) (SUC n) (FUNPOW f (SUC n) x)
         = FUNPOW (LINV f s) (SUC n) (f (FUNPOW f n x))           by FUNPOW_SUC
         = FUNPOW (LINV f s) n ((LINV f s) (f (FUNPOW f n x)))    by FUNPOW
         = FUNPOW (LINV f s) n (FUNPOW f n x)                     by BIJ_LINV_THM
         = x                                      by induction hypothesis
*)
Theorem FUNPOW_EQ_LINV:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n (FUNPOW f n x) = x
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `FUNPOW (LINV f s) (SUC n) (FUNPOW f (SUC n) x)
    = FUNPOW (LINV f s) (SUC n) (f (FUNPOW f n x))` by rw[FUNPOW_SUC] >>
  `_ = FUNPOW (LINV f s) n ((LINV f s) (f (FUNPOW f n x)))` by rw[FUNPOW] >>
  `_ = FUNPOW (LINV f s) n (FUNPOW f n x)` by metis_tac[BIJ_LINV_THM, FUNPOW_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW f (n - m) x = FUNPOW f n (FUNPOW (LINV f s) m x) *)
(* Proof:
     FUNPOW f n (FUNPOW (LINV f s) m x)
   = FUNPOW f (n - m + m) (FUNPOW (LINV f s) m x)   by SUB_ADD, m <= n
   = FUNPOW f (n - m) (FUNPOW f m (FUNPOW (LINV f s) m x))  by FUNPOW_ADD
   = FUNPOW f (n - m) x                             by FUNPOW_LINV_EQ
*)
Theorem FUNPOW_SUB_LINV1:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW f (n - m) x = FUNPOW f n (FUNPOW (LINV f s) m x)
Proof
  rpt strip_tac >>
  `FUNPOW f n (FUNPOW (LINV f s) m x)
  = FUNPOW f (n - m + m) (FUNPOW (LINV f s) m x)` by simp[] >>
  `_ = FUNPOW f (n - m) (FUNPOW f m (FUNPOW (LINV f s) m x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW f (n - m) x` by rw[FUNPOW_LINV_EQ] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW f (n - m) x = FUNPOW (LINV f s) m (FUNPOW f n x) *)
(* Proof:
   Note FUNPOW f (n - m) x IN s                      by FUNPOW_closure
     FUNPOW (LINV f s) m (FUNPOW f n x)
   = FUNPOW (LINV f s) m (FUNPOW f (n - m + m) x)    by SUB_ADD, m <= n
   = FUNPOW (LINV f s) m (FUNPOW f (m + (n - m)) x)  by ADD_COMM
   = FUNPOW (LINV f s) m (FUNPOW f m (FUNPOW f (n - m) x))  by FUNPOW_ADD
   = FUNPOW f (n - m) x                              by FUNPOW_EQ_LINV
*)
Theorem FUNPOW_SUB_LINV2:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW f (n - m) x = FUNPOW (LINV f s) m (FUNPOW f n x)
Proof
  rpt strip_tac >>
  `FUNPOW (LINV f s) m (FUNPOW f n x)
  = FUNPOW (LINV f s) m (FUNPOW f (n - m + m) x)` by simp[] >>
  `_ = FUNPOW (LINV f s) m (FUNPOW f (m + (n - m)) x)` by metis_tac[ADD_COMM] >>
  `_ = FUNPOW (LINV f s) m (FUNPOW f m (FUNPOW f (n - m) x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW f (n - m) x` by rw[FUNPOW_EQ_LINV, FUNPOW_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW (LINV f s) (n - m) x = FUNPOW (LINV f s) n (FUNPOW f m x) *)
(* Proof:
     FUNPOW (LINV f s) n (FUNPOW f m x)
   = FUNPOW (LINV f s) (n - m + m) (FUNPOW f m x)    by SUB_ADD, m <= n
   = FUNPOW (LINV f s) (n - m) (FUNPOW (LINV f s) m (FUNPOW f m x))  by FUNPOW_ADD
   = FUNPOW (LINV f s) (n - m) x                     by FUNPOW_EQ_LINV
*)
Theorem FUNPOW_LINV_SUB1:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW (LINV f s) (n - m) x = FUNPOW (LINV f s) n (FUNPOW f m x)
Proof
  rpt strip_tac >>
  `FUNPOW (LINV f s) n (FUNPOW f m x)
  = FUNPOW (LINV f s) (n - m + m) (FUNPOW f m x)` by simp[] >>
  `_ = FUNPOW (LINV f s) (n - m) (FUNPOW (LINV f s) m (FUNPOW f m x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW (LINV f s) (n - m) x` by rw[FUNPOW_EQ_LINV] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW (LINV f s) (n - m) x = FUNPOW f m (FUNPOW (LINV f s) n x) *)
(* Proof:
   Note FUNPOW (LINV f s) (n - m) x IN s             by FUNPOW_LINV_closure
     FUNPOW f m (FUNPOW (LINV f s) n x)
   = FUNPOW f m (FUNPOW (LINV f s) (n - m + m) x)    by SUB_ADD, m <= n
   = FUNPOW f m (FUNPOW (LINV f s) (m + (n - m)) x)  by ADD_COMM
   = FUNPOW f m (FUNPOW (LINV f s) m (FUNPOW (LINV f s) (n - m) x))  by FUNPOW_ADD
   = FUNPOW (LINV f s) (n - m) x                     by FUNPOW_LINV_EQ
*)
Theorem FUNPOW_LINV_SUB2:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW (LINV f s) (n - m) x = FUNPOW f m (FUNPOW (LINV f s) n x)
Proof
  rpt strip_tac >>
  `FUNPOW f m (FUNPOW (LINV f s) n x)
  = FUNPOW f m (FUNPOW (LINV f s) (n - m + m) x)` by simp[] >>
  `_ = FUNPOW f m (FUNPOW (LINV f s) (m + (n - m)) x)` by metis_tac[ADD_COMM] >>
  `_ = FUNPOW f m (FUNPOW (LINV f s) m (FUNPOW (LINV f s) (n - m) x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW (LINV f s) (n - m) x` by rw[FUNPOW_LINV_EQ, FUNPOW_LINV_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ y IN s ==>
            (x = FUNPOW f n y <=> y = FUNPOW (LINV f s) n x) *)
(* Proof:
   If part: x = FUNPOW f n y ==> y = FUNPOW (LINV f s) n x)
        FUNPOW (LINV f s) n x)
      = FUNPOW (LINV f s) n (FUNPOW f n y))   by x = FUNPOW f n y
      = y                                     by FUNPOW_EQ_LINV
   Only-if part: y = FUNPOW (LINV f s) n x) ==> x = FUNPOW f n y
        FUNPOW f n y
      = FUNPOW f n (FUNPOW (LINV f s) n x))   by y = FUNPOW (LINV f s) n x)
      = x                                     by FUNPOW_LINV_EQ
*)
Theorem FUNPOW_LINV_INV:
  !f s x y n. f PERMUTES s /\ x IN s /\ y IN s ==>
              (x = FUNPOW f n y <=> y = FUNPOW (LINV f s) n x)
Proof
  rw[EQ_IMP_THM] >-
  rw[FUNPOW_EQ_LINV] >>
  rw[FUNPOW_LINV_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* FUNPOW with incremental cons.                                             *)
(* ------------------------------------------------------------------------- *)

(* Note from HelperList: m downto n = REVERSE [m .. n] *)

(* Idea: when applying incremental cons (f head) to a list for n times,
         head of the result is f^n (head of list). *)

(* Theorem: HD (FUNPOW (\ls. f (HD ls)::ls) n ls) = FUNPOW f n (HD ls) *)
(* Proof:
   Let h = (\ls. f (HD ls)::ls).
   By induction on n.
   Base: !ls. HD (FUNPOW h 0 ls) = FUNPOW f 0 (HD ls)
           HD (FUNPOW h 0 ls)
         = HD ls                by FUNPOW_0
         = FUNPOW f 0 (HD ls)   by FUNPOW_0
   Step: !ls. HD (FUNPOW h n ls) = FUNPOW f n (HD ls) ==>
         !ls. HD (FUNPOW h (SUC n) ls) = FUNPOW f (SUC n) (HD ls)
           HD (FUNPOW h (SUC n) ls)
         = HD (FUNPOW h n (h ls))    by FUNPOW
         = FUNPOW f n (HD (h ls))    by induction hypothesis
         = FUNPOW f n (f (HD ls))    by definition of h
         = FUNPOW f (SUC n) (HD ls)  by FUNPOW
*)
Theorem FUNPOW_cons_head:
  !f n ls. HD (FUNPOW (\ls. f (HD ls)::ls) n ls) = FUNPOW f n (HD ls)
Proof
  strip_tac >>
  qabbrev_tac `h = \ls. f (HD ls)::ls` >>
  Induct >-
  simp[] >>
  rw[FUNPOW, Abbr`h`]
QED

(* Idea: when applying incremental cons (f head) to a singleton [u] for n times,
         the result is the list [f^n(u), .... f(u), u]. *)

(* Theorem: FUNPOW (\ls. f (HD ls)::ls) n [u] =
            MAP (\j. FUNPOW f j u) (n downto 0) *)
(* Proof:
   Let g = (\ls. f (HD ls)::ls),
       h = (\j. FUNPOW f j u).
   By induction on n.
   Base: FUNPOW g 0 [u] = MAP h (0 downto 0)
           FUNPOW g 0 [u]
         = [u]                       by FUNPOW_0
         = [FUNPOW f 0 u]            by FUNPOW_0
         = MAP h [0]                 by MAP
         = MAP h (0 downto 0)  by REVERSE
   Step: FUNPOW g n [u] = MAP h (n downto 0) ==>
         FUNPOW g (SUC n) [u] = MAP h (SUC n downto 0)
           FUNPOW g (SUC n) [u]
         = g (FUNPOW g n [u])             by FUNPOW_SUC
         = g (MAP h (n downto 0))   by induction hypothesis
         = f (HD (MAP h (n downto 0))) ::
             MAP h (n downto 0)     by definition of g
         Now f (HD (MAP h (n downto 0)))
           = f (HD (MAP h (MAP (\x. n - x) [0 .. n])))    by listRangeINC_REVERSE
           = f (HD (MAP h o (\x. n - x) [0 .. n]))        by MAP_COMPOSE
           = f ((h o (\x. n - x)) 0)                      by MAP
           = f (h n)
           = f (FUNPOW f n u)             by definition of h
           = FUNPOW (n + 1) u             by FUNPOW_SUC
           = h (n + 1)                    by definition of h
          so h (n + 1) :: MAP h (n downto 0)
           = MAP h ((n + 1) :: (n downto 0))         by MAP
           = MAP h (REVERSE (SNOC (n+1) [0 .. n]))   by REVERSE_SNOC
           = MAP h (SUC n downto 0)                  by listRangeINC_SNOC
*)
Theorem FUNPOW_cons_eq_map_0:
  !f u n. FUNPOW (\ls. f (HD ls)::ls) n [u] =
          MAP (\j. FUNPOW f j u) (n downto 0)
Proof
  ntac 2 strip_tac >>
  Induct >-
  rw[] >>
  qabbrev_tac `g = \ls. f (HD ls)::ls` >>
  qabbrev_tac `h = \j. FUNPOW f j u` >>
  rw[] >>
  `f (HD (MAP h (n downto 0))) = h (n + 1)` by
  (`[0 .. n] = 0 :: [1 .. n]` by rw[listRangeINC_CONS] >>
  fs[listRangeINC_REVERSE, MAP_COMPOSE, GSYM FUNPOW_SUC, ADD1, Abbr`h`]) >>
  `FUNPOW g (SUC n) [u] = g (FUNPOW g n [u])` by rw[FUNPOW_SUC] >>
  `_ = g (MAP h (n downto 0))` by fs[] >>
  `_ = h (n + 1) :: MAP h (n downto 0)` by rw[Abbr`g`] >>
  `_ = MAP h ((n + 1) :: (n downto 0))` by rw[] >>
  `_ = MAP h (REVERSE (SNOC (n+1) [0 .. n]))` by rw[REVERSE_SNOC] >>
  rw[listRangeINC_SNOC, ADD1]
QED

(* Idea: when applying incremental cons (f head) to a singleton [f(u)] for (n-1) times,
         the result is the list [f^n(u), .... f(u)]. *)

(* Theorem: 0 < n ==> (FUNPOW (\ls. f (HD ls)::ls) (n - 1) [f u] =
            MAP (\j. FUNPOW f j u) (n downto 1)) *)
(* Proof:
   Let g = (\ls. f (HD ls)::ls),
       h = (\j. FUNPOW f j u).
   By induction on n.
   Base: FUNPOW g 0 [f u] = MAP h (REVERSE [1 .. 1])
           FUNPOW g 0 [f u]
         = [f u]                     by FUNPOW_0
         = [FUNPOW f 1 u]            by FUNPOW_1
         = MAP h [1]                 by MAP
         = MAP h (REVERSE [1 .. 1])  by REVERSE
   Step: 0 < n ==> FUNPOW g (n-1) [f u] = MAP h (n downto 1) ==>
         FUNPOW g n [f u] = MAP h (REVERSE [1 .. SUC n])
         The case n = 0 is the base case. For n <> 0,
           FUNPOW g n [f u]
         = g (FUNPOW g (n-1) [f u])       by FUNPOW_SUC
         = g (MAP h (n downto 1))         by induction hypothesis
         = f (HD (MAP h (n downto 1))) ::
             MAP h (n downto 1)           by definition of g
         Now f (HD (MAP h (n downto 1)))
           = f (HD (MAP h (MAP (\x. n + 1 - x) [1 .. n])))  by listRangeINC_REVERSE
           = f (HD (MAP h o (\x. n + 1 - x) [1 .. n]))      by MAP_COMPOSE
           = f ((h o (\x. n + 1 - x)) 1)                    by MAP
           = f (h n)
           = f (FUNPOW f n u)             by definition of h
           = FUNPOW (n + 1) u             by FUNPOW_SUC
           = h (n + 1)                    by definition of h
          so h (n + 1) :: MAP h (n downto 1)
           = MAP h ((n + 1) :: (n downto 1))         by MAP
           = MAP h (REVERSE (SNOC (n+1) [1 .. n]))   by REVERSE_SNOC
           = MAP h (REVERSE [1 .. SUC n])            by listRangeINC_SNOC
*)
Theorem FUNPOW_cons_eq_map_1:
  !f u n. 0 < n ==> (FUNPOW (\ls. f (HD ls)::ls) (n - 1) [f u] =
          MAP (\j. FUNPOW f j u) (n downto 1))
Proof
  ntac 2 strip_tac >>
  Induct >-
  simp[] >>
  rw[] >>
  qabbrev_tac `g = \ls. f (HD ls)::ls` >>
  qabbrev_tac `h = \j. FUNPOW f j u` >>
  Cases_on `n = 0` >-
  rw[Abbr`g`, Abbr`h`] >>
  `f (HD (MAP h (n downto 1))) = h (n + 1)` by
  (`[1 .. n] = 1 :: [2 .. n]` by rw[listRangeINC_CONS] >>
  fs[listRangeINC_REVERSE, MAP_COMPOSE, GSYM FUNPOW_SUC, ADD1, Abbr`h`]) >>
  `n = SUC (n-1)` by decide_tac >>
  `FUNPOW g n [f u] = g (FUNPOW g (n - 1) [f u])` by metis_tac[FUNPOW_SUC] >>
  `_ = g (MAP h (n downto 1))` by fs[] >>
  `_ = h (n + 1) :: MAP h (n downto 1)` by rw[Abbr`g`] >>
  `_ = MAP h ((n + 1) :: (n downto 1))` by rw[] >>
  `_ = MAP h (REVERSE (SNOC (n+1) [1 .. n]))` by rw[REVERSE_SNOC] >>
  rw[listRangeINC_SNOC, ADD1]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
