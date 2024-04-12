(* ------------------------------------------------------------------------- *)
(* Helper Theorems - a collection of useful results -- for Sets.             *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperSet";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open arithmeticTheory dividesTheory gcdTheory logrootTheory;
open pred_setTheory gcdsetTheory numberTheory;

(* ------------------------------------------------------------------------- *)
(* HelperSet Documentation                                                   *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   countFrom m n        = IMAGE ($+ m) (count n)
   s =|= u # v          = split s u v
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
   INSERT_DELETE_NON_ELEMENT
                       |- !x s. x NOTIN s ==> (x INSERT s) DELETE x = s
   SUBSET_INTER_SUBSET |- !s t u. s SUBSET u ==> s INTER t SUBSET u
   DIFF_DIFF_EQ_INTER  |- !s t. s DIFF (s DIFF t) = s INTER t
   SET_EQ_BY_DIFF      |- !s t. (s = t) <=> s SUBSET t /\ (t DIFF s = {})
   SUBSET_INSERT_BOTH  |- !s1 s2 x. s1 SUBSET s2 ==> x INSERT s1 SUBSET x INSERT s2
   INSERT_SUBSET_SUBSET|- !s t x. x NOTIN s /\ x INSERT s SUBSET t ==> s SUBSET t DELETE x
   DIFF_DELETE         |- !s t x. s DIFF t DELETE x = s DIFF (x INSERT t)
   SUBSET_DIFF_CARD    |- !a b. FINITE a /\ b SUBSET a ==> (CARD (a DIFF b) = CARD a - CARD b)
   SUBSET_SING_IFF     |- !s x. s SUBSET {x} <=> (s = {}) \/ (s = {x})
   SUBSET_CARD_EQ      |- !s t. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)
   IMAGE_SUBSET_TARGET |- !f s t. (!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t
   SURJ_CARD_IMAGE     |- !f s t. SURJ f s t ==> CARD (IMAGE f s) = CARD t

   Image and Bijection:
   INJ_CONG            |- !f g s t. (!x. x IN s ==> (f x = g x)) ==> (INJ f s t <=> INJ g s t)
   SURJ_CONG           |- !f g s t. (!x. x IN s ==> (f x = g x)) ==> (SURJ f s t <=> SURJ g s t)
   BIJ_CONG            |- !f g s t. (!x. x IN s ==> (f x = g x)) ==> (BIJ f s t <=> BIJ g s t)
   INJ_ELEMENT         |- !f s t x. INJ f s t /\ x IN s ==> f x IN t
   SURJ_ELEMENT        |- !f s t x. SURJ f s t /\ x IN s ==> f x IN t
   BIJ_ELEMENT         |- !f s t x. BIJ f s t /\ x IN s ==> f x IN t
   INJ_UNIV            |- !f s t. INJ f s t ==> INJ f s univ(:'b)
   INJ_SUBSET_UNIV     |- !f s. INJ f univ(:'a) univ(:'b) ==> INJ f s univ(:'b)
   INJ_IMAGE_BIJ_ALT   |- !f s. INJ f s univ(:'b) ==> BIJ f s (IMAGE f s)
   INJ_IMAGE_EQ        |- !P f. INJ f P univ(:'b) ==> !s t. s SUBSET P /\ t SUBSET P ==>
                                ((IMAGE f s = IMAGE f t) <=> (s = t))
   INJ_IMAGE_INTER     |- !P f. INJ f P univ(:'b) ==> !s t. s SUBSET P /\ t SUBSET P ==>
                                (IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t)
   INJ_IMAGE_DISJOINT  |- !P f. INJ f P univ(:'b) ==> !s t. s SUBSET P /\ t SUBSET P ==>
                                (DISJOINT s t <=> DISJOINT (IMAGE f s) (IMAGE f t))
   INJ_I               |- !s. INJ I s univ(:'a)
   INJ_I_IMAGE         |- !s f. INJ I (IMAGE f s) univ(:'b)
   BIJ_THM             |- !f s t. BIJ f s t <=>
                          (!x. x IN s ==> f x IN t) /\ !y. y IN t ==> ?!x. x IN s /\ (f x = y)
   BIJ_IS_INJ          |- !f s t. BIJ f s t ==>
                          !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)
   BIJ_IS_SURJ         |- !f s t. BIJ f s t ==> !x. x IN t ==> ?y. y IN s /\ f y = x
   BIJ_FINITE_IFF      |- !f s t. BIJ f s t ==> (FINITE s <=> FINITE t)
   INJ_EQ_11           |- !f s x y. INJ f s s /\ x IN s /\ y IN s ==> ((f x = f y) <=> (x = y))
   INJ_IMP_11          |- !f. INJ f univ(:'a) univ(:'b) ==> !x y. f x = f y <=> x = y
   BIJ_I_SAME          |- !s. BIJ I s s
   IMAGE_K             |- !s. s <> {} ==> !e. IMAGE (K e) s = {e}
   IMAGE_ELEMENT_CONDITION  |- !f. (!x y. (f x = f y) ==> (x = y)) ==> !s e. e IN s <=> f e IN IMAGE f s
   BIGUNION_ELEMENTS_SING   |- !s. BIGUNION (IMAGE (\x. {x}) s) = s
   IMAGE_DIFF          |- !s t f. s SUBSET t /\ INJ f t univ(:'b) ==>
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
   FINITE_INJ_IS_SURJ  |- !f s t. FINITE s /\ FINITE t /\
                                  CARD s = CARD t /\ INJ f s t ==> SURJ f s t
   FINITE_INJ_IS_BIJ   |- !f s t. FINITE s /\ FINITE t /\
                                  CARD s = CARD t /\ INJ f s t ==> BIJ f s t
   FINITE_COUNT_IMAGE  |- !P n. FINITE {P x | x < n}
   FINITE_BIJ_PROPERTY |- !f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ (CARD s = CARD t)
   FINITE_CARD_IMAGE   |- !s f. (!x y. (f x = f y) <=> (x = y)) /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)
   CARD_IMAGE_SUC      |- !s. FINITE s ==> (CARD (IMAGE SUC s) = CARD s)
   CARD_UNION_DISJOINT |- !s t. FINITE s /\ FINITE t /\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t)
   FINITE_BIJ_COUNT_CARD    |- !s. FINITE s ==> ?f. BIJ f (count (CARD s)) s
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
   LINV_SUBSET       |- !f s t. INJ f t univ(:'b) /\ s SUBSET t ==> !x. x IN s ==> (LINV f t (f x) = x)

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
   SUM_IMAGE_DOUBLET    |- !f x y. x <> y ==> SIGMA f {x; y} = f x + f y
   SUM_IMAGE_TRIPLET    |- !f x y z. x <> y /\ y <> z /\ z <> x ==> SIGMA f {x; y; z} = f x + f y + f z
   SIGMA_CONSTANT       |- !s. FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (SIGMA f s = k * CARD s)
   SUM_IMAGE_CONSTANT   |- !s. FINITE s ==> !c. SIGMA (K c) s = c * CARD s
   SIGMA_CARD_CONSTANT  |- !n s. FINITE s /\ (!e. e IN s ==> CARD e = n) ==> SIGMA CARD s = n * CARD s
   SIGMA_CARD_SAME_SIZE_SETS
                        |- !n s. FINITE s /\ (!e. e IN s ==> CARD e = n) ==> SIGMA CARD s = n * CARD s
   SIGMA_CARD_FACTOR    |- !n s. FINITE s /\ (!e. e IN s ==> n divides CARD e) ==> n divides SIGMA CARD s
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
   card_le_sigma_card   |- !s. FINITE s /\ (!e. e IN s ==> CARD e <> 0) ==>
                               CARD s <= SIGMA CARD s
   card_eq_sigma_card   |- !s. FINITE s /\ (!e. e IN s ==> CARD e <> 0) /\
                               CARD s = SIGMA CARD s ==> !e. e IN s ==> CARD e = 1

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
   partition_on_empty     |- !R. partition R {} = {}
   partition_element      |- !R s t. t IN partition R s <=> ?x. x IN s /\ (t = equiv_class R s x)
   partition_elements     |- !R s. partition R s = IMAGE (\x. equiv_class R s x) s
   partition_as_image     |- !R s. partition R s = IMAGE (\x. equiv_class R s x) s
   partition_cong         |- !R1 R2 s1 s2. (R1 = R2) /\ (s1 = s2) ==> (partition R1 s1 = partition R2 s2)
   partition_element_not_empty
                          |- !R s e. R equiv_on s /\ e IN partition R s ==> e <> {}
   equiv_class_not_empty  |- !R s x. R equiv_on s /\ x IN s ==> equiv_class R s x <> {}
   partition_element_exists
                          |- !R s x. R equiv_on s ==> (x IN s <=> ?e. e IN partition R s /\ x IN e)
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
   CARD_BIGUNION_PAIR_DISJOINT |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                      CARD (BIGUNION P) = SIGMA CARD P
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
   preimage_subset            |- !f s y. preimage f s y SUBSET s
   preimage_finite            |- !f s y. FINITE s ==> FINITE (preimage f s y)
   preimage_property          |- !f s y x. x IN preimage f s y ==> (f x = y)
   preimage_of_image          |- !f s x. x IN s ==> x IN preimage f s (f x)
   preimage_choice_property   |- !f s y. y IN IMAGE f s ==>
                                 CHOICE (preimage f s y) IN s /\ (f (CHOICE (preimage f s y)) = y)
   preimage_inj               |- !f s. INJ f s univ(:'b) ==> !x. x IN s ==> (preimage f s (f x) = {x})
   preimage_inj_choice        |- !f s. INJ f s univ(:'b) ==> !x. x IN s ==> (CHOICE (preimage f s (f x)) = x)
   preimage_image_inj         |- !f s. INJ (preimage f s) (IMAGE f s) (POW s)

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

(* export theory at end *)
val _ = export_theory();
val _ = html_theory "helperSet";

(*===========================================================================*)
