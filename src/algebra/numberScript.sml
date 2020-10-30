(* ------------------------------------------------------------------------- *)
(*  Number Theory                                                            *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "number";

(* ------------------------------------------------------------------------- *)

(* open dependent theories *)
open pred_setTheory relationTheory listTheory rich_listTheory listRangeTheory;
open arithmeticTheory dividesTheory gcdTheory logrootTheory optionTheory;

(* local theories *)
open jcLib util_algebraTheory;

(* ------------------------------------------------------------------------- *)
(* Euler Set and Totient Function Documentation                              *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   natural n    = IMAGE SUC (count n)
   upto n       = count (SUC n)
*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   Residues:
   residue_def       |- !n. residue n = {i | 0 < i /\ i < n}
   residue_element   |- !n j. j IN residue n ==> 0 < j /\ j < n
   residue_0         |- residue 0 = {}
   residue_1         |- residue 1 = {}
   residue_nonempty  |- !n. 1 < n ==> residue n <> {}
   residue_no_zero   |- !n. 0 NOTIN residue n
   residue_no_self   |- !n. n NOTIN residue n
!  residue_thm       |- !n. residue n = count n DIFF {0}
   residue_insert    |- !n. 0 < n ==> (residue (SUC n) = n INSERT residue n)
   residue_delete    |- !n. 0 < n ==> (residue n DELETE n = residue n)
   residue_suc       |- !n. 0 < n ==> (residue (SUC n) = n INSERT residue n)
   residue_count     |- !n. 0 < n ==> (count n = 0 INSERT residue n)
   residue_finite    |- !n. FINITE (residue n)
   residue_card      |- !n. 0 < n ==> (CARD (residue n) = n - 1)
   residue_prime_neq |- !p a n. prime p /\ a IN residue p /\ n <= p ==>
                        !x. x IN residue n ==> (a * n) MOD p <> (a * x) MOD p
   prod_set_residue  |- !n. PROD_SET (residue n) = FACT (n - 1)

   Naturals:
   natural_element  |- !n j. j IN natural n <=> 0 < j /\ j <= n
   natural_property |- !n. natural n = {j | 0 < j /\ j <= n}
   natural_finite   |- !n. FINITE (natural n)
   natural_card     |- !n. CARD (natural n) = n
   natural_not_0    |- !n. 0 NOTIN natural n
   natural_0        |- natural 0 = {}
   natural_1        |- natural 1 = {1}
   natural_has_1    |- !n. 0 < n ==> 1 IN natural n
   natural_has_last |- !n. 0 < n ==> n IN natural n
   natural_suc      |- !n. natural (SUC n) = SUC n INSERT natural n
   natural_thm      |- !n. natural n = set (GENLIST SUC n)
   natural_divisor_natural   |- !n a b. 0 < n /\ a IN natural n /\ b divides a ==> b IN natural n
   natural_cofactor_natural  |- !n a b. 0 < n /\ 0 < a /\ b IN natural n /\ a divides b ==>
                                        b DIV a IN natural n
   natural_cofactor_natural_reduced
                             |- !n a b. 0 < n /\ a divides n /\ b IN natural n /\ a divides b ==>
                                        b DIV a IN natural (n DIV a)

   Uptos:
   upto_finite      |- !n. FINITE (upto n)
   upto_card        |- !n. CARD (upto n) = SUC n
   upto_has_last    |- !n. n IN upto n
   upto_split_first |- !n. upto n = {0} UNION natural n
   upto_split_last  |- !n. upto n = count n UNION {n}
   upto_by_count    |- !n. upto n = n INSERT count n
   upto_by_natural  |- !n. upto n = 0 INSERT natural n
   natural_by_upto  |- !n. natural n = upto n DELETE 0

   Euler Set and Totient Function:
   Euler_def            |- !n. Euler n = {i | 0 < i /\ i < n /\ coprime n i}
   totient_def          |- !n. totient n = CARD (Euler n)
   Euler_element        |- !n x. x IN Euler n <=> 0 < x /\ x < n /\ coprime n x
!  Euler_thm            |- !n. Euler n = residue n INTER {j | coprime j n}
   Euler_finite         |- !n. FINITE (Euler n)
   Euler_0              |- Euler 0 = {}
   Euler_1              |- Euler 1 = {}
   Euler_has_1          |- !n. 1 < n ==> 1 IN Euler n
   Euler_nonempty       |- !n. 1 < n ==> Euler n <> {}
   Euler_empty          |- !n. (Euler n = {}) <=> (n = 0 \/ n = 1)
   Euler_card_upper_le  |- !n. totient n <= n
   Euler_card_upper_lt  |- !n. 1 < n ==> totient n < n
   Euler_card_bounds    |- !n. totient n <= n /\ (1 < n ==> 0 < totient n /\ totient n < n)
   Euler_prime          |- !p. prime p ==> (Euler p = residue p)
   Euler_card_prime     |- !p. prime p ==> (totient p = p - 1)

   Summation of Geometric Sequence:
   sigma_geometric_natural_eqn   |- !p. 0 < p ==>
                                    !n. (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1)
   sigma_geometric_natural       |- !p. 1 < p ==>
                                    !n. SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1) DIV (p - 1)

   Useful Theorems:
   PROD_SET_IMAGE_EXP_NONZERO    |- !n m. 1 < n /\ 0 < m ==>
                                         (PROD_SET (IMAGE (\j. n ** j) (count m)) =
                                          PROD_SET (IMAGE (\j. n ** j) (residue m)))
*)

(* ------------------------------------------------------------------------- *)
(* Count-based Sets                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Residues -- close-relative of COUNT                                       *)
(* ------------------------------------------------------------------------- *)

(* Define the set of residues = nonzero remainders *)
val residue_def = zDefine `residue n = { i | (0 < i) /\ (i < n) }`;
(* use zDefine as this is not computationally effective. *)

(* Theorem: j IN residue n ==> 0 < j /\ j < n *)
(* Proof: by residue_def. *)
val residue_element = store_thm(
  "residue_element",
  ``!n j. j IN residue n ==> 0 < j /\ j < n``,
  rw[residue_def]);

(* Theorem: residue 0 = EMPTY *)
(* Proof: by residue_def *)
val residue_0 = store_thm(
  "residue_0",
  ``residue 0 = {}``,
  simp[residue_def]);

(* Theorem: residue 1 = EMPTY *)
(* Proof: by definition. *)
val residue_1 = store_thm(
  "residue_1",
  ``residue 1 = {}``,
  simp[residue_def]);

(* Theorem: 1 < n ==> residue n <> {} *)
(* Proof:
   By residue_def, this is to show: 1 < n ==> ?x. x <> 0 /\ x < n
   Take x = 1, this is true.
*)
val residue_nonempty = store_thm(
  "residue_nonempty",
  ``!n. 1 < n ==> residue n <> {}``,
  rw[residue_def, EXTENSION] >>
  metis_tac[DECIDE``1 <> 0``]);

(* Theorem: 0 NOTIN residue n *)
(* Proof: by residue_def *)
val residue_no_zero = store_thm(
  "residue_no_zero",
  ``!n. 0 NOTIN residue n``,
  simp[residue_def]);

(* Theorem: n NOTIN residue n *)
(* Proof: by residue_def *)
val residue_no_self = store_thm(
  "residue_no_self",
  ``!n. n NOTIN residue n``,
  simp[residue_def]);

(* Theorem: residue n = (count n) DIFF {0} *)
(* Proof:
     residue n
   = {i | 0 < i /\ i < n}   by residue_def
   = {i | i < n /\ i <> 0}  by NOT_ZERO_LT_ZERO
   = {i | i < n} DIFF {0}   by IN_DIFF
   = (count n) DIFF {0}     by count_def
*)
val residue_thm = store_thm(
  "residue_thm[compute]",
  ``!n. residue n = (count n) DIFF {0}``,
  rw[residue_def, EXTENSION]);
(* This is effective, put in computeLib. *)

(*
> EVAL ``residue 10``;
val it = |- residue 10 = {9; 8; 7; 6; 5; 4; 3; 2; 1}: thm
*)

(* Theorem: For n > 0, residue (SUC n) = n INSERT residue n *)
(* Proof:
     residue (SUC n)
   = {1, 2, ..., n}
   = n INSERT {1, 2, ..., (n-1) }
   = n INSERT residue n
*)
val residue_insert = store_thm(
  "residue_insert",
  ``!n. 0 < n ==> (residue (SUC n) = n INSERT residue n)``,
  srw_tac[ARITH_ss][residue_def, EXTENSION]);

(* Theorem: (residue n) DELETE n = residue n *)
(* Proof: Because n is not in (residue n). *)
val residue_delete = store_thm(
  "residue_delete",
  ``!n. 0 < n ==> ((residue n) DELETE n = residue n)``,
  rpt strip_tac >>
  `n NOTIN (residue n)` by rw[residue_def] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem alias: rename *)
val residue_suc = save_thm("residue_suc", residue_insert);
(* val residue_suc = |- !n. 0 < n ==> (residue (SUC n) = n INSERT residue n): thm *)

(* Theorem: count n = 0 INSERT (residue n) *)
(* Proof: by definition. *)
val residue_count = store_thm(
  "residue_count",
  ``!n. 0 < n ==> (count n = 0 INSERT (residue n))``,
  srw_tac[ARITH_ss][residue_def, EXTENSION]);

(* Theorem: FINITE (residue n) *)
(* Proof: by FINITE_COUNT.
   If n = 0, residue 0 = {}, hence FINITE.
   If n > 0, count n = 0 INSERT (residue n)  by residue_count
   hence true by FINITE_COUNT and FINITE_INSERT.
*)
val residue_finite = store_thm(
  "residue_finite",
  ``!n. FINITE (residue n)``,
  Cases >-
  rw[residue_def] >>
  metis_tac[residue_count, FINITE_INSERT, count_def, FINITE_COUNT, DECIDE ``0 < SUC n``]);

(* Theorem: For n > 0, CARD (residue n) = n-1 *)
(* Proof:
   Since 0 INSERT (residue n) = count n by residue_count
   the result follows by CARD_COUNT.
*)
val residue_card = store_thm(
  "residue_card",
  ``!n. 0 < n ==> (CARD (residue n) = n-1)``,
  rpt strip_tac >>
  `0 NOTIN (residue n)` by rw[residue_def] >>
  `0 INSERT (residue n) = count n` by rw[residue_count] >>
  `SUC (CARD (residue n)) = n` by metis_tac[residue_finite, CARD_INSERT, CARD_COUNT] >>
  decide_tac);

(* Theorem: For prime m, a in residue m, n <= m, a*n MOD m <> a*x MOD m  for all x in residue n *)
(* Proof:
   Assume the contrary, that a*n MOD m = a*x MOD m
   Since a in residue m and m is prime, MOD_MULT_LCANCEL gives: n MOD m = x MOD m
   If n = m, n MOD m = 0, but x MOD m <> 0, hence contradiction.
   If n < m, then since x < n <= m, n = x, contradicting x < n.
*)
val residue_prime_neq = store_thm(
  "residue_prime_neq",
  ``!p a n. prime p /\ a IN (residue p) /\ n <= p ==> !x. x IN (residue n) ==> (a*n) MOD p <> (a*x) MOD p``,
  rw[residue_def] >>
  spose_not_then strip_assume_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `(a MOD p <> 0) /\ (x MOD p <> 0)` by rw_tac arith_ss[] >>
  `n MOD p = x MOD p` by metis_tac[MOD_MULT_LCANCEL] >>
  Cases_on `n = p` >-
  metis_tac [DIVMOD_ID] >>
  `n < p` by decide_tac >>
  `(n MOD p = n) /\ (x MOD p = x)` by rw_tac arith_ss[] >>
  decide_tac);

(* Idea: the product of residues is a factorial. *)

(* Theorem: PROD_SET (residue n) = FACT (n - 1) *)
(* Proof:
   By induction on n.
   Base: PROD_SET (residue 0) = FACT (0 - 1)
        PROD_SET (residue 0)
      = PROD_SET {}           by residue_0
      = 1                     by PROD_SET_EMPTY
      = FACT 0                by FACT_0
      = FACT (0 - 1)          by arithmetic
   Step: PROD_SET (residue n) = FACT (n - 1) ==>
         PROD_SET (residue (SUC n)) = FACT (SUC n - 1)
      If n = 0,
        PROD_SET (residue (SUC 0))
      = PROD_SET (residue 1)  by ONE
      = PROD_SET {}           by residue_1
      = 1                     by PROD_SET_EMPTY
      = FACT 0                by FACT_0

      If n <> 0, then 0 < n.
      Note FINITE (residue n)                by residue_finite
        PROD_SET (residue (SUC n))
      = PROD_SET (n INSERT residue n)        by residue_insert
      = n * PROD_SET ((residue n) DELETE n)  by PROD_SET_THM
      = n * PROD_SET (residue n)             by residue_delete
      = n * FACT (n - 1)                     by induction hypothesis
      = FACT (SUC (n - 1))                   by FACT
      = FACT (SUC n - 1)                     by arithmetic
*)
val prod_set_residue = store_thm(
  "prod_set_residue",
  ``!n. PROD_SET (residue n) = FACT (n - 1)``,
  Induct >-
  simp[residue_0, PROD_SET_EMPTY, FACT_0] >>
  Cases_on `n = 0` >-
  simp[residue_1, PROD_SET_EMPTY, FACT_0] >>
  `FINITE (residue n)` by rw[residue_finite] >>
  `n = SUC (n - 1)` by decide_tac >>
  `SUC (n - 1) = SUC n - 1` by decide_tac >>
  `PROD_SET (residue (SUC n)) = PROD_SET (n INSERT residue n)` by rw[residue_insert] >>
  `_ = n * PROD_SET ((residue n) DELETE n)` by rw[PROD_SET_THM] >>
  `_ = n * PROD_SET (residue n)` by rw[residue_delete] >>
  `_ = n * FACT (n - 1)` by rw[] >>
  metis_tac[FACT]);

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

(* Theorem: natural n = set (GENLIST SUC n) *)
(* Proof:
   By induction on n.
   Base: natural 0 = set (GENLIST SUC 0)
      LHS = natural 0 = {}         by natural_0
      RHS = set (GENLIST SUC 0)
          = set []                 by GENLIST_0
          = {}                     by LIST_TO_SET
   Step: natural n = set (GENLIST SUC n) ==>
         natural (SUC n) = set (GENLIST SUC (SUC n))
         natural (SUC n)
       = SUC n INSERT natural n                 by natural_suc
       = SUC n INSERT (set (GENLIST SUC n))     by induction hypothesis
       = set (SNOC (SUC n) (GENLIST SUC n))     by LIST_TO_SET_SNOC
       = set (GENLIST SUC (SUC n))              by GENLIST
*)
val natural_thm = store_thm(
  "natural_thm",
  ``!n. natural n = set (GENLIST SUC n)``,
  Induct >-
  rw[] >>
  rw[natural_suc, LIST_TO_SET_SNOC, GENLIST]);

(* Theorem: 0 < n /\ a IN (natural n) /\ b divides a ==> b IN (natural n) *)
(* Proof:
   By natural_element, this is to show:
   (1) 0 < a /\ b divides a ==> 0 < b
       True by divisor_pos
   (2) 0 < a /\ b divides a ==> b <= n
       Since b divides a
         ==> b <= a                     by DIVIDES_LE, 0 < a
         ==> b <= n                     by LESS_EQ_TRANS
*)
val natural_divisor_natural = store_thm(
  "natural_divisor_natural",
  ``!n a b. 0 < n /\ a IN (natural n) /\ b divides a ==> b IN (natural n)``,
  rw[natural_element] >-
  metis_tac[divisor_pos] >>
  metis_tac[DIVIDES_LE, LESS_EQ_TRANS]);

(* Theorem: 0 < n /\ 0 < a /\ b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural n) *)
(* Proof:
   Let c = b DIV a.
   By natural_element, this is to show:
      0 < a /\ 0 < b /\ b <= n /\ a divides b ==> 0 < c /\ c <= n
   Since a divides b ==> b = c * a               by DIVIDES_EQN, 0 < a
      so b = a * c                               by MULT_COMM
      or c divides b                             by divides_def
    Thus 0 < c /\ c <= b                         by divides_pos
      or c <= n                                  by LESS_EQ_TRANS
*)
val natural_cofactor_natural = store_thm(
  "natural_cofactor_natural",
  ``!n a b. 0 < n /\ 0 < a /\ b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural n)``,
  rewrite_tac[natural_element] >>
  ntac 4 strip_tac >>
  qabbrev_tac `c = b DIV a` >>
  `b = c * a` by rw[GSYM DIVIDES_EQN, Abbr`c`] >>
  `c divides b` by metis_tac[divides_def, MULT_COMM] >>
  `0 < c /\ c <= b` by metis_tac[divides_pos] >>
  decide_tac);

(* Theorem: 0 < n /\ a divides n /\ b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural (n DIV a)) *)
(* Proof:
   Let c = b DIV a.
   By natural_element, this is to show:
      0 < n /\ a divides b /\ 0 < b /\ b <= n /\ a divides b ==> 0 < c /\ c <= n DIV a
   Note 0 < a                                    by ZERO_DIVIES, 0 < n
   Since a divides b ==> b = c * a               by DIVIDES_EQN, 0 < a [1]
      or c divides b                             by divides_def, MULT_COMM
    Thus 0 < c, since 0 divides b means b = 0.   by ZERO_DIVIDES, b <> 0
     Now n = (n DIV a) * a                       by DIVIDES_EQN, 0 < a [2]
    With b <= n, c * a <= (n DIV a) * a          by [1], [2]
   Hence c <= n DIV a                            by LE_MULT_RCANCEL, a <> 0
*)
val natural_cofactor_natural_reduced = store_thm(
  "natural_cofactor_natural_reduced",
  ``!n a b. 0 < n /\ a divides n /\
           b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural (n DIV a))``,
  rewrite_tac[natural_element] >>
  ntac 4 strip_tac >>
  qabbrev_tac `c = b DIV a` >>
  `a <> 0` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  `(b = c * a) /\ (n = (n DIV a) * a)` by rw[GSYM DIVIDES_EQN, Abbr`c`] >>
  `c divides b` by metis_tac[divides_def, MULT_COMM] >>
  `0 < c` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  metis_tac[LE_MULT_RCANCEL]);

(* ------------------------------------------------------------------------- *)
(* Uptos -- counting from 0 and inclusive.                                   *)
(* ------------------------------------------------------------------------- *)

(* Overload on another count-related set *)
val _ = overload_on("upto", ``\n. count (SUC n)``);

(* Theorem: FINITE (upto n) *)
(* Proof: by FINITE_COUNT *)
val upto_finite = store_thm(
  "upto_finite",
  ``!n. FINITE (upto n)``,
  rw[]);

(* Theorem: CARD (upto n) = SUC n *)
(* Proof: by CARD_COUNT *)
val upto_card = store_thm(
  "upto_card",
  ``!n. CARD (upto n) = SUC n``,
  rw[]);

(* Theorem: n IN (upto n) *)
(* Proof: byLESS_SUC_REFL *)
val upto_has_last = store_thm(
  "upto_has_last",
  ``!n. n IN (upto n)``,
  rw[]);

(* Theorem: upto n = {0} UNION (natural n) *)
(* Proof:
   By UNION_DEF, EXTENSION, this is to show:
   (1) x < SUC n ==> (x = 0) \/ ?x'. (x = SUC x') /\ x' < n
       If x = 0, trivially true.
       If x <> 0, x = SUC m.
          Take x' = m,
          then SUC m = x < SUC n ==> m < n   by LESS_MONO_EQ
   (2) (x = 0) \/ ?x'. (x = SUC x') /\ x' < n ==> x < SUC n
       If x = 0, 0 < SUC n                   by SUC_POS
       If ?x'. (x = SUC x') /\ x' < n,
          x' < n ==> SUC x' = x < SUC n      by LESS_MONO_EQ
*)
val upto_split_first = store_thm(
  "upto_split_first",
  ``!n. upto n = {0} UNION (natural n)``,
  rw[EXTENSION, EQ_IMP_THM] >>
  Cases_on `x` >-
  rw[] >>
  metis_tac[LESS_MONO_EQ]);

(* Theorem: upto n = (count n) UNION {n} *)
(* Proof:
   By UNION_DEF, EXTENSION, this is to show:
   (1) x < SUC n ==> x < n \/ (x = n)
       True by LESS_THM.
   (2) x < n \/ (x = n) ==> x < SUC n
       True by LESS_THM.
*)
val upto_split_last = store_thm(
  "upto_split_last",
  ``!n. upto n = (count n) UNION {n}``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: upto n = n INSERT (count n) *)
(* Proof:
     upto n
   = count (SUC n)             by notation
   = {x | x < SUC n}           by count_def
   = {x | (x = n) \/ (x < n)}  by prim_recTheory.LESS_THM
   = x INSERT {x| x < n}       by INSERT_DEF
   = x INSERT (count n)        by count_def
*)
val upto_by_count = store_thm(
  "upto_by_count",
  ``!n. upto n = n INSERT (count n)``,
  rw[EXTENSION]);

(* Theorem: upto n = 0 INSERT (natural n) *)
(* Proof:
     upto n
   = count (SUC n)             by notation
   = {x | x < SUC n}           by count_def
   = {x | ((x = 0) \/ (?m. x = SUC m)) /\ x < SUC n)}            by num_CASES
   = {x | (x = 0 /\ x < SUC n) \/ (?m. x = SUC m /\ x < SUC n)}  by SUC_POS
   = 0 INSERT {SUC m | SUC m < SUC n}   by INSERT_DEF
   = 0 INSERT {SUC m | m < n}           by LESS_MONO_EQ
   = 0 INSERT (IMAGE SUC (count n))     by IMAGE_DEF
   = 0 INSERT (natural n)               by notation
*)
val upto_by_natural = store_thm(
  "upto_by_natural",
  ``!n. upto n = 0 INSERT (natural n)``,
  rw[EXTENSION] >>
  metis_tac[num_CASES, LESS_MONO_EQ, SUC_POS]);

(* Theorem: natural n = count (SUC n) DELETE 0 *)
(* Proof:
     count (SUC n) DELETE 0
   = {x | x < SUC n} DELETE 0    by count_def
   = {x | x < SUC n} DIFF {0}    by DELETE_DEF
   = {x | x < SUC n /\ x <> 0}   by DIFF_DEF
   = {SUC m | SUC m < SUC n}     by num_CASES
   = {SUC m | m < n}             by LESS_MONO_EQ
   = IMAGE SUC (count n)         by IMAGE_DEF
   = natural n                   by notation
*)
val natural_by_upto = store_thm(
  "natural_by_upto",
  ``!n. natural n = count (SUC n) DELETE 0``,
  (rw[EXTENSION, EQ_IMP_THM] >> metis_tac[num_CASES, LESS_MONO_EQ]));

(* ------------------------------------------------------------------------- *)
(* Euler Set and Totient Function                                            *)
(* ------------------------------------------------------------------------- *)

(* Euler's totient function *)
val Euler_def = zDefine`
  Euler n = { i | 0 < i /\ i < n /\ (gcd n i = 1) }
`;
(* that is, Euler n = { i | i in (residue n) /\ (gcd n i = 1) }`; *)
(* use zDefine as this is not computationally effective. *)

val totient_def = Define`
  totient n = CARD (Euler n)
`;

(* Theorem: x IN (Euler n) <=> 0 < x /\ x < n /\ coprime n x *)
(* Proof: by Euler_def. *)
val Euler_element = store_thm(
  "Euler_element",
  ``!n x. x IN (Euler n) <=> 0 < x /\ x < n /\ coprime n x``,
  rw[Euler_def]);

(* Theorem: Euler n = (residue n) INTER {j | coprime j n} *)
(* Proof: by Euler_def, residue_def, EXTENSION, IN_INTER *)
val Euler_thm = store_thm(
  "Euler_thm[compute]",
  ``!n. Euler n = (residue n) INTER {j | coprime j n}``,
  rw[Euler_def, residue_def, GCD_SYM, EXTENSION]);
(* This is effective, put in computeLib. *)

(*
> EVAL ``Euler 10``;
val it = |- Euler 10 = {9; 7; 3; 1}: thm
> EVAL ``totient 10``;
val it = |- totient 10 = 4: thm
*)

(* Theorem: FINITE (Euler n) *)
(* Proof:
   Since (Euler n) SUBSET count n  by Euler_def, SUBSET_DEF
     and FINITE (count n)          by FINITE_COUNT
     ==> FINITE (Euler n)          by SUBSET_FINITE
*)
val Euler_finite = store_thm(
  "Euler_finite",
  ``!n. FINITE (Euler n)``,
  rpt strip_tac >>
  `(Euler n) SUBSET count n` by rw[Euler_def, SUBSET_DEF] >>
  metis_tac[FINITE_COUNT, SUBSET_FINITE]);

(* Theorem: Euler 0 = {} *)
(* Proof: by Euler_def *)
val Euler_0 = store_thm(
  "Euler_0",
  ``Euler 0 = {}``,
  rw[Euler_def]);

(* Theorem: Euler 1 = {} *)
(* Proof: by Euler_def *)
val Euler_1 = store_thm(
  "Euler_1",
  ``Euler 1 = {}``,
  rw[Euler_def]);

(* Theorem: 1 < n ==> 1 IN (Euler n) *)
(* Proof: by Euler_def *)
val Euler_has_1 = store_thm(
  "Euler_has_1",
  ``!n. 1 < n ==> 1 IN (Euler n)``,
  rw[Euler_def]);

(* Theorem: 1 < n ==> (Euler n) <> {} *)
(* Proof: by Euler_has_1, MEMBER_NOT_EMPTY *)
val Euler_nonempty = store_thm(
  "Euler_nonempty",
  ``!n. 1 < n ==> (Euler n) <> {}``,
  metis_tac[Euler_has_1, MEMBER_NOT_EMPTY]);

(* Theorem: (Euler n = {}) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: Euler n = {} ==> n = 0 \/ n = 1
      By contradiction, suppose ~(n = 0 \/ n = 1).
      Then 1 < n, but Euler n <> {}   by Euler_nonempty
      This contradicts Euler n = {}.
   Only-if part: n = 0 \/ n = 1 ==> Euler n = {}
      Note Euler 0 = {}               by Euler_0
       and Euler 1 = {}               by Euler_1
*)
val Euler_empty = store_thm(
  "Euler_empty",
  ``!n. (Euler n = {}) <=> ((n = 0) \/ (n = 1))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `1 < n` by decide_tac >>
    metis_tac[Euler_nonempty],
    rw[Euler_0],
    rw[Euler_1]
  ]);

(* Theorem: totient n <= n *)
(* Proof:
   Since (Euler n) SUBSET count n  by Euler_def, SUBSET_DEF
     and FINITE (count n)          by FINITE_COUNT
     and (CARD (count n) = n       by CARD_COUNT
   Hence CARD (Euler n) <= n       by CARD_SUBSET
      or totient n <= n            by totient_def
*)
val Euler_card_upper_le = store_thm(
  "Euler_card_upper_le",
  ``!n. totient n <= n``,
  rpt strip_tac >>
  `(Euler n) SUBSET count n` by rw[Euler_def, SUBSET_DEF] >>
  metis_tac[totient_def, CARD_SUBSET, FINITE_COUNT, CARD_COUNT]);

(* Theorem: 1 < n ==> totient n < n *)
(* Proof:
   First, (Euler n) SUBSET count n     by Euler_def, SUBSET_DEF
     Now, ~(coprime 0 n)               by coprime_0L, n <> 1
      so  0 NOTIN (Euler n)            by Euler_def
     but  0 IN (count n)               by IN_COUNT, 0 < n
    Thus  (Euler n) <> (count n)       by EXTENSION
     and  (Euler n) PSUBSET (count n)  by PSUBSET_DEF
   Since  FINITE (count n)             by FINITE_COUNT
     and  (CARD (count n) = n          by CARD_COUNT
   Hence  CARD (Euler n) < n           by CARD_PSUBSET
      or  totient n < n                by totient_def
*)
val Euler_card_upper_lt = store_thm(
  "Euler_card_upper_lt",
  ``!n. 1 < n ==> totient n < n``,
  rpt strip_tac >>
  `(Euler n) SUBSET count n` by rw[Euler_def, SUBSET_DEF] >>
  `0 < n /\ n <> 1` by decide_tac >>
  `~(coprime 0 n)` by metis_tac[coprime_0L] >>
  `0 NOTIN (Euler n)` by rw[Euler_def] >>
  `0 IN (count n)` by rw[] >>
  `(Euler n) <> (count n)` by metis_tac[EXTENSION] >>
  `(Euler n) PSUBSET (count n)` by rw[PSUBSET_DEF] >>
  metis_tac[totient_def, CARD_PSUBSET, FINITE_COUNT, CARD_COUNT]);

(* Theorem: (totient n <= n) /\ (1 < n ==> 0 < totient n /\ totient n < n) *)
(* Proof:
   This is to show:
   (1) totient n <= n,
       True by Euler_card_upper_le.
   (2) 1 < n ==> 0 < totient n
       Since (Euler n) <> {}      by Euler_nonempty
        Also FINITE (Euler n)     by Euler_finite
       Hence CARD (Euler n) <> 0  by CARD_EQ_0
          or 0 < totient n        by totient_def
   (3) 1 < n ==> totient n < n
       True by Euler_card_upper_lt.
*)
val Euler_card_bounds = store_thm(
  "Euler_card_bounds",
  ``!n. (totient n <= n) /\ (1 < n ==> 0 < totient n /\ totient n < n)``,
  rw[] >-
  rw[Euler_card_upper_le] >-
 (`(Euler n) <> {}` by rw[Euler_nonempty] >>
  `FINITE (Euler n)` by rw[Euler_finite] >>
  `totient n <> 0` by metis_tac[totient_def, CARD_EQ_0] >>
  decide_tac) >>
  rw[Euler_card_upper_lt]);

(* Theorem: For prime p, (Euler p = residue p) *)
(* Proof:
   By Euler_def, residue_def, this is to show:
   For prime p, gcd p x = 1   for 0 < x < p.
   Since x < p, x does not divide p, result follows by PRIME_GCD.
   or, this is true by prime_coprime_all_lt
*)
val Euler_prime = store_thm(
  "Euler_prime",
  ``!p. prime p ==> (Euler p = residue p)``,
  rw[Euler_def, residue_def, EXTENSION, EQ_IMP_THM] >>
  rw[prime_coprime_all_lt]);

(* Theorem: For prime p, totient p = p - 1 *)
(* Proof:
      totient p
    = CARD (Euler p)    by totient_def
    = CARD (residue p)  by Euler_prime
    = p - 1             by residue_card, and prime p > 0.
*)
val Euler_card_prime = store_thm(
  "Euler_card_prime",
  ``!p. prime p ==> (totient p = p - 1)``,
  rw[totient_def, Euler_prime, residue_card, PRIME_POS]);

(* ------------------------------------------------------------------------- *)
(* Summation of Geometric Sequence                                           *)
(* ------------------------------------------------------------------------- *)

(* Geometric Series:
   Let s = p + p ** 2 + p ** 3
   p * s = p ** 2 + p ** 3 + p ** 4
   p * s - s = p ** 4 - p
   (p - 1) * s = p * (p ** 3 - 1)
*)

(* Theorem: 0 < p ==> !n. (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1) *)
(* Proof:
   By induction on n.
   Base: (p - 1) * SIGMA (\j. p ** j) (natural 0) = p * (p ** 0 - 1)
      LHS = (p - 1) * SIGMA (\j. p ** j) (natural 0)
          = (p - 1) * SIGMA (\j. p ** j) {}          by natural_0
          = (p - 1) * 0                              by SUM_IMAGE_EMPTY
          = 0                                        by MULT_0
      RHS = p * (p ** 0 - 1)
          = p * (1 - 1)                              by EXP
          = p * 0                                    by SUB_EQUAL_0
          = 0 = LHS                                  by MULT_0
   Step: (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1) ==>
         (p - 1) * SIGMA (\j. p ** j) (natural (SUC n)) = p * (p ** SUC n - 1)
      Note FINITE (natural n)                        by natural_finite
       and (SUC n) NOTIN (natural n)                 by natural_element
      Also p <= p ** (SUC n)                         by X_LE_X_EXP, SUC_POS
       and 1 <= p                                    by 0 < p
      thus p ** (SUC n) <> 0                         by EXP_POS, 0 < p
        so p ** (SUC n) <= p * p ** (SUC n)          by LE_MULT_LCANCEL, p ** (SUC n) <> 0
        (p - 1) * SIGMA (\j. p ** j) (natural (SUC n))
      = (p - 1) * SIGMA (\j. p ** j) ((SUC n) INSERT (natural n))                   by natural_suc
      = (p - 1) * ((p ** SUC n) + SIGMA (\j. p ** j) ((natural n) DELETE (SUC n)))  by SUM_IMAGE_THM
      = (p - 1) * ((p ** SUC n) + SIGMA (\j. p ** j) (natural n))                   by DELETE_NON_ELEMENT
      = (p - 1) * (p ** SUC n) + (p - 1) * SIGMA (\j. p ** j) (natural n)           by LEFT_ADD_DISTRIB
      = (p - 1) * (p ** SUC n) + p * (p ** n - 1)        by induction hypothesis
      = (p - 1) * (p ** SUC n) + (p * p ** n - p)        by LEFT_SUB_DISTRIB
      = (p - 1) * (p ** SUC n) + (p ** (SUC n) - p)      by EXP
      = (p * p ** SUC n - p ** SUC n) + (p ** SUC n - p) by RIGHT_SUB_DISTRIB
      = (p * p ** SUC n - p ** SUC n + p ** SUC n - p    by LESS_EQ_ADD_SUB, p <= p ** (SUC n)
      = p ** p ** SUC n - p                              by SUB_ADD, p ** (SUC n) <= p * p ** (SUC n)
      = p * (p ** SUC n - 1)                             by LEFT_SUB_DISTRIB
 *)
val sigma_geometric_natural_eqn = store_thm(
  "sigma_geometric_natural_eqn",
  ``!p. 0 < p ==> !n. (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw_tac std_ss[natural_0, SUM_IMAGE_EMPTY, EXP, MULT_0] >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `(SUC n) NOTIN (natural n)` by rw[natural_element] >>
  qabbrev_tac `q = p ** SUC n` >>
  `p <= q` by rw[X_LE_X_EXP, Abbr`q`] >>
  `1 <= p` by decide_tac >>
  `q <> 0` by rw[EXP_POS, Abbr`q`] >>
  `q <= p * q` by rw[LE_MULT_LCANCEL] >>
  `(p - 1) * SIGMA (\j. p ** j) (natural (SUC n))
  = (p - 1) * SIGMA (\j. p ** j) ((SUC n) INSERT (natural n))` by rw[natural_suc] >>
  `_ = (p - 1) * (q + SIGMA (\j. p ** j) ((natural n) DELETE (SUC n)))` by rw[SUM_IMAGE_THM, Abbr`q`] >>
  `_ = (p - 1) * (q + SIGMA (\j. p ** j) (natural n))` by metis_tac[DELETE_NON_ELEMENT] >>
  `_ = (p - 1) * q + (p - 1) * SIGMA (\j. p ** j) (natural n)` by rw[LEFT_ADD_DISTRIB] >>
  `_ = (p - 1) * q + p * (p ** n - 1)` by rw[] >>
  `_ = (p - 1) * q + (p * p ** n - p)` by rw[LEFT_SUB_DISTRIB] >>
  `_ = (p - 1) * q + (q - p)` by rw[EXP, Abbr`q`] >>
  `_ = (p * q - q) + (q - p)` by rw[RIGHT_SUB_DISTRIB] >>
  `_ = (p * q - q + q) - p` by rw[LESS_EQ_ADD_SUB] >>
  `_ = p * q - p` by rw[SUB_ADD] >>
  `_ = p * (q - 1)` by rw[LEFT_SUB_DISTRIB] >>
  rw[]);

(* Theorem: 1 < p ==> !n. SIGMA (\j. p ** j) (natural n) = (p * (p ** n - 1)) DIV (p - 1) *)
(* Proof:
   Since 1 < p,
     ==> 0 < p - 1, and 0 < p                          by arithmetic
   Let t = SIGMA (\j. p ** j) (natural n)
    With 0 < p,
         (p - 1) * t = p * (p ** n - 1)                by sigma_geometric_natural_eqn, 0 < p
   Hence           t = (p * (p ** n - 1)) DIV (p - 1)  by DIV_SOLVE, 0 < (p - 1)
*)
val sigma_geometric_natural = store_thm(
  "sigma_geometric_natural",
  ``!p. 1 < p ==> !n. SIGMA (\j. p ** j) (natural n) = (p * (p ** n - 1)) DIV (p - 1)``,
  rpt strip_tac >>
  `0 < p - 1 /\ 0 < p` by decide_tac >>
  rw[sigma_geometric_natural_eqn, DIV_SOLVE]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Note:
   count m = {i | i < m}                  defined in pred_set
   residue m = {i | 0 < i /\ i < m}       defined in Euler
   The difference i = 0 gives n ** 0 = 1, which does not make a difference for PROD_SET.
*)

(* Theorem: 1 < n /\ 0 < m ==>
    (PROD_SET (IMAGE (\j. n ** j) (count m)) = PROD_SET (IMAGE (\j. n ** j) (residue m))) *)
(* Proof:
   Since 0 IN count m  by IN_COUNT, 0 < m
     and (IMAGE (\j. n ** j) (count m)) DELETE 1 = IMAGE (\j. n ** j) (residue m)
                                                            by IMAGE_DEF, EXP_EQ_1, EXP
     PROD_SET (IMAGE (\j. n ** j) (count m))
   = PROD_SET (IMAGE (\j. n ** j) (0 INSERT count m))       by ABSORPTION
   = PROD_SET ((\j. n ** j) 0 INSERT IMAGE (\j. n ** j) (count m))     by IMAGE_INSERT
   = n ** 0 * PROD_SET ((IMAGE (\j. n ** j) (count m)) DELETE n ** 0)  by PROD_SET_THM
   = PROD_SET ((IMAGE (\j. n ** j) (count m)) DELETE 1)     by EXP
   = PROD_SET ((IMAGE (\j. n ** j) (residue m)))            by above
*)
val PROD_SET_IMAGE_EXP_NONZERO = store_thm(
  "PROD_SET_IMAGE_EXP_NONZERO",
  ``!n m. 1 < n /\ 0 < m ==>
    (PROD_SET (IMAGE (\j. n ** j) (count m)) = PROD_SET (IMAGE (\j. n ** j) (residue m)))``,
  rpt strip_tac >>
  `0 IN count m` by rw[] >>
  `FINITE (IMAGE (\j. n ** j) (count m))` by rw[] >>
  `(IMAGE (\j. n ** j) (count m)) DELETE 1 = IMAGE (\j. n ** j) (residue m)` by
  (rw[residue_def, IMAGE_DEF, EXTENSION, EQ_IMP_THM] >-
  metis_tac[EXP, NOT_ZERO_LT_ZERO] >-
  metis_tac[] >>
  `j <> 0 /\ n <> 1` by decide_tac >>
  metis_tac[EXP_EQ_1]
  ) >>
  `PROD_SET (IMAGE (\j. n ** j) (count m)) = PROD_SET (IMAGE (\j. n ** j) (0 INSERT count m))` by metis_tac[ABSORPTION] >>
  `_ = PROD_SET ((\j. n ** j) 0 INSERT IMAGE (\j. n ** j) (count m))` by rw[] >>
  `_ = n ** 0 * PROD_SET ((IMAGE (\j. n ** j) (count m)) DELETE n ** 0)` by rw[PROD_SET_THM] >>
  `_ = PROD_SET ((IMAGE (\j. n ** j) (count m)) DELETE 1)` by rw[EXP] >>
  `_ = PROD_SET ((IMAGE (\j. n ** j) (residue m)))` by rw[] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem                                                     *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   Helper Theorems:

   Coprimes:
   coprimes_def      |- !n. coprimes n = {j | j IN natural n /\ coprime j n}
   coprimes_element  |- !n j. j IN coprimes n <=> 0 < j /\ j <= n /\ coprime j n
!  coprimes_alt      |- !n. coprimes n = natural n INTER {j | coprime j n}
   coprimes_thm      |- !n. coprimes n = set (FILTER (\j. coprime j n) (GENLIST SUC n))
   coprimes_subset   |- !n. coprimes n SUBSET natural n
   coprimes_finite   |- !n. FINITE (coprimes n)
   coprimes_0        |- coprimes 0 = {}
   coprimes_1        |- coprimes 1 = {1}
   coprimes_has_1    |- !n. 0 < n ==> 1 IN coprimes n
   coprimes_eq_empty |- !n. (coprimes n = {}) <=> (n = 0)
   coprimes_no_0     |- !n. 0 NOTIN coprimes n
   coprimes_without_last |- !n. 1 < n ==> n NOTIN coprimes n
   coprimes_with_last    |- !n. n IN coprimes n <=> (n = 1)
   coprimes_has_last_but_1  |- !n. 1 < n ==> n - 1 IN coprimes n
   coprimes_element_less    |- !n. 1 < n ==> !j. j IN coprimes n ==> j < n
   coprimes_element_alt     |- !n. 1 < n ==> !j. j IN coprimes n <=> j < n /\ coprime j n
   coprimes_max      |- !n. 1 < n ==> (MAX_SET (coprimes n) = n - 1)
   coprimes_eq_Euler |- !n. 1 < n ==> (coprimes n = Euler n)
   coprimes_prime    |- !n. prime n ==> (coprimes n = residue n)

   Coprimes by a divisor:
   coprimes_by_def     |- !n d. coprimes_by n d = if 0 < n /\ d divides n then coprimes (n DIV d) else {}
   coprimes_by_element |- !n d j. j IN coprimes_by n d <=> 0 < n /\ d divides n /\ j IN coprimes (n DIV d)
   coprimes_by_finite  |- !n d. FINITE (coprimes_by n d)
   coprimes_by_0       |- !d. coprimes_by 0 d = {}
   coprimes_by_by_0    |- !n. coprimes_by n 0 = {}
   coprimes_by_by_1    |- !n. 0 < n ==> (coprimes_by n 1 = coprimes n)
   coprimes_by_by_last |- !n. 0 < n ==> (coprimes_by n n = {1})
   coprimes_by_by_divisor  |- !n d. 0 < n /\ d divides n ==> (coprimes_by n d = coprimes (n DIV d))
   coprimes_by_eq_empty    |- !n d. 0 < n ==> ((coprimes_by n d = {}) <=> ~(d divides n))

   GCD Equivalence Class:
   gcd_matches_def       |- !n d. gcd_matches n d = {j | j IN natural n /\ (gcd j n = d)}
!  gcd_matches_alt       |- !n d. gcd_matches n d = natural n INTER {j | gcd j n = d}
   gcd_matches_element   |- !n d j. j IN gcd_matches n d <=> 0 < j /\ j <= n /\ (gcd j n = d)
   gcd_matches_subset    |- !n d. gcd_matches n d SUBSET natural n
   gcd_matches_finite    |- !n d. FINITE (gcd_matches n d)
   gcd_matches_0         |- !d. gcd_matches 0 d = {}
   gcd_matches_with_0    |- !n. gcd_matches n 0 = {}
   gcd_matches_1         |- !d. gcd_matches 1 d = if d = 1 then {1} else {}
   gcd_matches_has_divisor     |- !n d. 0 < n /\ d divides n ==> d IN gcd_matches n d
   gcd_matches_element_divides |- !n d j. j IN gcd_matches n d ==> d divides j /\ d divides n
   gcd_matches_eq_empty        |- !n d. 0 < n ==> ((gcd_matches n d = {}) <=> ~(d divides n))

   Phi Function:
   phi_def           |- !n. phi n = CARD (coprimes n)
   phi_thm           |- !n. phi n = LENGTH (FILTER (\j. coprime j n) (GENLIST SUC n))
   phi_fun           |- phi = CARD o coprimes
   phi_pos           |- !n. 0 < n ==> 0 < phi n
   phi_0             |- phi 0 = 0
   phi_eq_0          |- !n. (phi n = 0) <=> (n = 0)
   phi_1             |- phi 1 = 1
   phi_eq_totient    |- !n. 1 < n ==> (phi n = totient n)
   phi_prime         |- !n. prime n ==> (phi n = n - 1)
   phi_2             |- phi 2 = 1
   phi_gt_1          |- !n. 2 < n ==> 1 < phi n
   phi_le            |- !n. phi n <= n
   phi_lt            |- !n. 1 < n ==> phi n < n

   Divisors:
   divisors_def            |- !n. divisors n = {d | d <= n /\ d divides n}
   divisors_element        |- !n d. d IN divisors n <=> d <= n /\ d divides n
   divisors_element_alt    |- !n. 0 < n ==> !d. d IN divisors n <=> d divides n
   divisors_has_one        |- !n. 0 < n ==> 1 IN divisors n
   divisors_has_last       |- !n. n IN divisors n
   divisors_not_empty      |- !n. divisors n <> {}
!  divisors_eqn            |- !n. divisors n =
                                  if n = 0 then {0}
                                  else IMAGE (\j. if j + 1 divides n then j + 1 else 1) (count n)
   divisors_cofactor       |- !n d. 0 < n /\ d IN divisors n ==> n DIV d IN divisors n
   divisors_delete_last    |- !n. 0 < n ==> (divisors n DELETE n = {m | m < n /\ m divides n})
   divisors_nonzero        |- !n. 0 < n ==> !d. d IN divisors n ==> 0 < d
   divisors_has_cofactor   |- !n. 0 < n ==> !d. d IN divisors n ==> n DIV d IN divisors n
   divisors_subset_upto    |- !n. divisors n SUBSET upto n
   divisors_subset_natural |- !n. 0 < n ==> divisors n SUBSET natural n
   divisors_finite         |- !n. FINITE (divisors n)
   divisors_0              |- divisors 0 = {0}
   divisors_1              |- divisors 1 = {1}
   divisors_has_0          |- !n. 0 IN divisors n <=> (n = 0)
   divisors_divisors_bij   |- !n. 0 < n ==> (\d. n DIV d) PERMUTES divisors n

   Gauss' Little Theorem:
   gcd_matches_divisor_element  |- !n d. d divides n ==>
                                   !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d
   gcd_matches_bij_coprimes_by  |- !n d. d divides n ==>
                                   BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d)
   gcd_matches_bij_coprimes     |- !n d. 0 < n /\ d divides n ==>
                                   BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d))
   divisors_eq_gcd_image    |- !n. 0 < n ==> (divisors n = IMAGE (gcd n) (natural n))
   gcd_eq_equiv_class       |- !n d. feq_class (gcd n) (natural n) d = gcd_matches n d
   gcd_eq_equiv_class_fun   |- !n. feq_class (gcd n) (natural n) = gcd_matches n
   gcd_eq_partition_by_divisors |- !n. 0 < n ==> (partition (feq (gcd n)) (natural n) =
                                   IMAGE (gcd_matches n) (divisors n))
   gcd_eq_equiv_on_natural        |- !n. feq (gcd n) equiv_on natural n
   sum_over_natural_by_gcd_partition
                                  |- !f n. SIGMA f (natural n) =
                                           SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))
   sum_over_natural_by_divisors   |- !f n. SIGMA f (natural n) =
                                              SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))
   gcd_matches_from_divisors_inj  |- !n. INJ (gcd_matches n) (divisors n) univ(:num -> bool)
   gcd_matches_and_coprimes_by_same_size |- !n. CARD o gcd_matches n = CARD o coprimes_by n
   coprimes_by_with_card      |- !n. 0 < n ==> (CARD o coprimes_by n =
                                               (\d. phi (if d IN divisors n then n DIV d else 0)))
   coprimes_by_divisors_card  |- !n. 0 < n ==> !x. x IN divisors n ==>
                                               ((CARD o coprimes_by n) x = (\d. phi (n DIV d)) x)
   Gauss_little_thm           |- !n. n = SIGMA phi (divisors n)

   Recursive definition of phi:
   rec_phi_def      |- !n. rec_phi n = if n = 0 then 0
                                  else if n = 1 then 1
                                  else n - SIGMA (\a. rec_phi a) {m | m < n /\ m divides n}
   rec_phi_0        |- rec_phi 0 = 0
   rec_phi_1        |- rec_phi 1 = 1
   rec_phi_eq_phi   |- !n. rec_phi n = phi n

   Not Used:
   coprimes_from_notone_inj       |- INJ coprimes (univ(:num) DIFF {1}) univ(:num -> bool)
   divisors_eq_image_gcd_upto     |- !n. divisors n = IMAGE (gcd n) (upto n)
   gcd_eq_equiv_on_upto           |- !n. feq (gcd n) equiv_on upto n
   gcd_eq_upto_partition_by_divisors   |- !n. partition (feq (gcd n)) (upto n) =
                                          IMAGE (preimage (gcd n) (upto n)) (divisors n)
   sum_over_upto_by_gcd_partition |- !f n. SIGMA f (upto n) =
                                           SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))
   sum_over_upto_by_divisors      |- !f n. SIGMA f (upto n) =
                                           SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))

   divisors_eq_image_gcd_count    |- !n. 0 < n ==> (divisors n = IMAGE (gcd n) (count n))
   gcd_eq_equiv_on_count          |- !n. feq (gcd n) equiv_on count n
   gcd_eq_count_partition_by_divisors  |- !n. 0 < n ==> (partition (feq (gcd n)) (count n) =
                                          IMAGE (preimage (gcd n) (count n)) (divisors n))
   sum_over_count_by_gcd_partition     |- !f n. SIGMA f (count n) =
                                          SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))
   sum_over_count_by_divisors     |- !f n. 0 < n ==> (SIGMA f (count n) =
                                     SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n)))

   divisors_eq_image_gcd_natural  |- !n. 0 < n ==> (divisors n = IMAGE (gcd n) (natural n))
   gcd_eq_natural_partition_by_divisors   |- !n. 0 < n ==> (partition (feq (gcd n)) (natural n) =
                                             IMAGE (preimage (gcd n) (natural n)) (divisors n))
   sum_over_natural_by_preimage_divisors  |- !f n. 0 < n ==> (SIGMA f (natural n) =
                                     SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n)))
   sum_image_divisors_cong        |- !f g. (f 1 = g 1) /\
                                           (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> (f = g)
*)

(* Theory:

Given the set natural 6 = {1, 2, 3, 4, 5, 6}
Every element has a gcd with 6: IMAGE (gcd 6) (natural 6) = {1, 2, 3, 2, 1, 6} = {1, 2, 3, 6}.
Thus the original set is partitioned by gcd: {{1, 5}, {2, 4}, {3}, {6}}
Since (gcd 6) j is a divisor of 6, and they run through all possible divisors of 6,
  SIGMA f (natural 6)
= f 1 + f 2 + f 3 + f 4 + f 5 + f 6
= (f 1 + f 5) + (f 2 + f 4) + f 3 + f 6
= (SIGMA f {1, 5}) + (SIGMA f {2, 4}) + (SIGMA f {3}) + (SIGMA f {6})
= SIGMA (SIGMA f) {{1, 5}, {2, 4}, {3}, {6}}
= SIGMA (SIGMA f) (partition (feq (natural 6) (gcd 6)) (natural 6))

SIGMA:('a -> num) -> ('a -> bool) -> num
SIGMA (f:num -> num):(num -> bool) -> num
SIGMA (SIGMA (f:num -> num)) (s:(num -> bool) -> bool):num

How to relate this to (divisors n) ?
First, observe   IMAGE (gcd 6) (natural 6) = divisors 6
and partition {{1, 5}, {2, 4}, {3}, {6}} = IMAGE (preimage (gcd 6) (natural 6)) (divisors 6)

  SIGMA f (natural 6)
= SIGMA (SIGMA f) (partition (feq (natural 6) (gcd 6)) (natural 6))
= SIGMA (SIGMA f) (IMAGE (preimage (gcd 6) (natural 6)) (divisors 6))

divisors n:num -> bool
preimage (gcd n):(num -> bool) -> num -> num -> bool
preimage (gcd n) (natural n):num -> num -> bool
IMAGE (preimage (gcd n) (natural n)) (divisors n):(num -> bool) -> bool

How to relate this to (coprimes d), where d divides n ?
Note {1, 5} with (gcd 6) j = 1, equals to (coprimes (6 DIV 1)) = coprimes 6
     {2, 4} with (gcd 6) j = 2, BIJ to {2/2, 4/2} with gcd (6/2) (j/2) = 1, i.e {1, 2} = coprimes 3
     {3} with (gcd 6) j = 3, BIJ to {3/3} with gcd (6/3) (j/3) = 1, i.e. {1} = coprimes 2
     {6} with (gcd 6) j = 6, BIJ to {6/6} with gcd (6/6) (j/6) = 1, i.e. {1} = coprimes 1
Hence CARD {{1, 5}, {2, 4}, {3}, {6}} = CARD (partition)
    = CARD {{1, 5}/1, {2,4}/2, {3}/3, {6}/6} = CARD (reduced-partition)
    = CARD {(coprimes 6/1) (coprimes 6/2) (coprimes 6/3) (coprimes 6/6)}
    = CARD {(coprimes 6) (coprimes 3) (coprimes 2) (coprimes 1)}
    = SIGMA (CARD (coprimes d)), over d divides 6)
    = SIGMA (phi d), over d divides 6.
*)


(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Coprimes                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define the coprimes set: integers from 1 to n that are coprime to n *)
(*
val coprimes_def = zDefine `
   coprimes n = {j | 0 < j /\ j <= n /\ coprime j n}
`;
*)
(* Note: j <= n ensures that coprimes n is finite. *)
(* Note: 0 < j is only to ensure  coprimes 1 = {1} *)
val coprimes_def = zDefine `
   coprimes n = {j | j IN (natural n) /\ coprime j n}
`;
(* use zDefine as this is not computationally effective. *)

(* Theorem: j IN coprimes n <=> 0 < j /\ j <= n /\ coprime j n *)
(* Proof: by coprimes_def, natural_element *)
val coprimes_element = store_thm(
  "coprimes_element",
  ``!n j. j IN coprimes n <=> 0 < j /\ j <= n /\ coprime j n``,
  (rw[coprimes_def, natural_element] >> metis_tac[]));

(* Theorem: coprimes n = (natural n) INTER {j | coprime j n} *)
(* Proof: by coprimes_def, EXTENSION, IN_INTER *)
val coprimes_alt = store_thm(
  "coprimes_alt[compute]",
  ``!n. coprimes n = (natural n) INTER {j | coprime j n}``,
  rw[coprimes_def, EXTENSION]);
(* This is effective, put in computeLib. *)

(*
> EVAL ``coprimes 10``;
val it = |- coprimes 10 = {9; 7; 3; 1}: thm
*)

(* Theorem: coprimes n = set (FILTER (\j. coprime j n) (GENLIST SUC n)) *)
(* Proof:
     coprimes n
   = (natural n) INTER {j | coprime j n}             by coprimes_alt
   = (set (GENLIST SUC n)) INTER {j | coprime j n}   by natural_thm
   = {j | coprime j n} INTER (set (GENLIST SUC n))   by INTER_COMM
   = set (FILTER (\j. coprime j n) (GENLIST SUC n))  by LIST_TO_SET_FILTER
*)
val coprimes_thm = store_thm(
  "coprimes_thm",
  ``!n. coprimes n = set (FILTER (\j. coprime j n) (GENLIST SUC n))``,
  rw[coprimes_alt, natural_thm, INTER_COMM, LIST_TO_SET_FILTER]);

(* Theorem: coprimes n SUBSET natural n *)
(* Proof: by coprimes_def, SUBSET_DEF *)
val coprimes_subset = store_thm(
  "coprimes_subset",
  ``!n. coprimes n SUBSET natural n``,
  rw[coprimes_def, SUBSET_DEF]);

(* Theorem: FINITE (coprimes n) *)
(* Proof:
   Since (coprimes n) SUBSET (natural n)   by coprimes_subset
     and !n. FINITE (natural n)            by natural_finite
      so FINITE (coprimes n)               by SUBSET_FINITE
*)
val coprimes_finite = store_thm(
  "coprimes_finite",
  ``!n. FINITE (coprimes n)``,
  metis_tac[coprimes_subset, natural_finite, SUBSET_FINITE]);

(* Theorem: coprimes 0 = {} *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= 0,
   which is impossible, hence empty.
*)
val coprimes_0 = store_thm(
  "coprimes_0",
  ``coprimes 0 = {}``,
  rw[coprimes_element, EXTENSION]);

(* Theorem: coprimes 1 = {1} *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= 1,
   Only possible j is 1, and gcd 1 1 = 1.
 *)
val coprimes_1 = store_thm(
  "coprimes_1",
  ``coprimes 1 = {1}``,
  rw[coprimes_element, EXTENSION]);

(* Theorem: 0 < n ==> 1 IN (coprimes n) *)
(* Proof: by coprimes_element, GCD_1 *)
val coprimes_has_1 = store_thm(
  "coprimes_has_1",
  ``!n. 0 < n ==> 1 IN (coprimes n)``,
  rw[coprimes_element]);

(* Theorem: (coprimes n = {}) <=> (n = 0) *)
(* Proof:
   If part: coprimes n = {} ==> n = 0
      By contradiction.
      Suppose n <> 0, then 0 < n.
      Then 1 IN (coprimes n)    by coprimes_has_1
      hence (coprimes n) <> {}  by MEMBER_NOT_EMPTY
      This contradicts (coprimes n) = {}.
   Only-if part: n = 0 ==> coprimes n = {}
      True by coprimes_0
*)
val coprimes_eq_empty = store_thm(
  "coprimes_eq_empty",
  ``!n. (coprimes n = {}) <=> (n = 0)``,
  rw[EQ_IMP_THM] >-
  metis_tac[coprimes_has_1, MEMBER_NOT_EMPTY, NOT_ZERO_LT_ZERO] >>
  rw[coprimes_0]);

(* Theorem: 0 NOTIN (coprimes n) *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= n,
   Hence j <> 0, or 0 NOTIN (coprimes n)
*)
val coprimes_no_0 = store_thm(
  "coprimes_no_0",
  ``!n. 0 NOTIN (coprimes n)``,
  rw[coprimes_element]);

(* Theorem: 1 < n ==> n NOTIN coprimes n *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= n /\ gcd j n = 1
   If j = n,  1 = gcd j n = gcd n n = n     by GCD_REF
   which is excluded by 1 < n, so j <> n.
*)
val coprimes_without_last = store_thm(
  "coprimes_without_last",
  ``!n. 1 < n ==> n NOTIN coprimes n``,
  rw[coprimes_element]);

(* Theorem: n IN coprimes n <=> (n = 1) *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= n /\ gcd j n = 1
   If n IN coprimes n, 1 = gcd j n = gcd n n = n     by GCD_REF
   If n = 1, 0 < n, n <= n, and gcd n n = n = 1      by GCD_REF
*)
val coprimes_with_last = store_thm(
  "coprimes_with_last",
  ``!n. n IN coprimes n <=> (n = 1)``,
  rw[coprimes_element]);

(* Theorem: 1 < n ==> (n - 1) IN (coprimes n) *)
(* Proof: by coprimes_element, coprime_PRE, GCD_SYM *)
val coprimes_has_last_but_1 = store_thm(
  "coprimes_has_last_but_1",
  ``!n. 1 < n ==> (n - 1) IN (coprimes n)``,
  rpt strip_tac >>
  `0 < n /\ 0 < n - 1` by decide_tac >>
  rw[coprimes_element, coprime_PRE, GCD_SYM]);

(* Theorem: 1 < n ==> !j. j IN coprimes n ==> j < n *)
(* Proof:
   Since j IN coprimes n ==> j <= n    by coprimes_element
   If j = n, then gcd n n = n <> 1     by GCD_REF
   Thus j <> n, or j < n.              or by coprimes_without_last
*)
val coprimes_element_less = store_thm(
  "coprimes_element_less",
  ``!n. 1 < n ==> !j. j IN coprimes n ==> j < n``,
  metis_tac[coprimes_element, coprimes_without_last, LESS_OR_EQ]);

(* Theorem: 1 < n ==> !j. j IN coprimes n <=> j < n /\ coprime j n *)
(* Proof:
   If part: j IN coprimes n ==> j < n /\ coprime j n
      Note 0 < j /\ j <= n /\ coprime j n      by coprimes_element
      By contradiction, suppose n <= j.
      Then j = n, but gcd n n = n <> 1         by GCD_REF
   Only-if part: j < n /\ coprime j n ==> j IN coprimes n
      This is to show:
           0 < j /\ j <= n /\ coprime j n      by coprimes_element
      By contradiction, suppose ~(0 < j).
      Then j = 0, but gcd 0 n = n <> 1         by GCD_0L
*)
val coprimes_element_alt = store_thm(
  "coprimes_element_alt",
  ``!n. 1 < n ==> !j. j IN coprimes n <=> j < n /\ coprime j n``,
  rw[coprimes_element] >>
  `n <> 1` by decide_tac >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `j = n` by decide_tac >>
    metis_tac[GCD_REF],
    spose_not_then strip_assume_tac >>
    `j = 0` by decide_tac >>
    metis_tac[GCD_0L]
  ]);

(* Theorem: 1 < n ==> (MAX_SET (coprimes n) = n - 1) *)
(* Proof:
   Let s = coprimes n, m = MAX_SET s.
    Note (n - 1) IN s     by coprimes_has_last_but_1, 1 < n
   Hence s <> {}          by MEMBER_NOT_EMPTY
     and FINITE s         by coprimes_finite
   Since !x. x IN s ==> x < n         by coprimes_element_less, 1 < n
    also !x. x < n ==> x <= (n - 1)   by SUB_LESS_OR
   Therefore MAX_SET s = n - 1        by MAX_SET_TEST
*)
val coprimes_max = store_thm(
  "coprimes_max",
  ``!n. 1 < n ==> (MAX_SET (coprimes n) = n - 1)``,
  rpt strip_tac >>
  qabbrev_tac `s = coprimes n` >>
  `(n - 1) IN s` by rw[coprimes_has_last_but_1, Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `FINITE s` by rw[coprimes_finite, Abbr`s`] >>
  `!x. x IN s ==> x < n` by rw[coprimes_element_less, Abbr`s`] >>
  `!x. x < n ==> x <= (n - 1)` by decide_tac >>
  metis_tac[MAX_SET_TEST]);

(* Relate coprimes to Euler totient *)

(* Theorem: 1 < n ==> (coprimes n = Euler n) *)
(* Proof:
   By Euler_def, this is to show:
   (1) x IN coprimes n ==> 0 < x, true by coprimes_element
   (2) x IN coprimes n ==> x < n, true by coprimes_element_less
   (3) x IN coprimes n ==> coprime n x, true by coprimes_element, GCD_SYM
   (4) 0 < x /\ x < n /\ coprime n x ==> x IN coprimes n
       That is, to show: 0 < x /\ x <= n /\ coprime x n.
       Since x < n ==> x <= n   by LESS_IMP_LESS_OR_EQ
       Hence true by GCD_SYM
*)
val coprimes_eq_Euler = store_thm(
  "coprimes_eq_Euler",
  ``!n. 1 < n ==> (coprimes n = Euler n)``,
  rw[Euler_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[coprimes_element] >-
  rw[coprimes_element_less] >-
  metis_tac[coprimes_element, GCD_SYM] >>
  metis_tac[coprimes_element, GCD_SYM, LESS_IMP_LESS_OR_EQ]);

(* Theorem: prime n ==> (coprimes n = residue n) *)
(* Proof:
   Since prime n ==> 1 < n     by ONE_LT_PRIME
   Hence   coprimes n
         = Euler n             by coprimes_eq_Euler
         = residue n           by Euler_prime
*)
val coprimes_prime = store_thm(
  "coprimes_prime",
  ``!n. prime n ==> (coprimes n = residue n)``,
  rw[ONE_LT_PRIME, coprimes_eq_Euler, Euler_prime]);

(* ------------------------------------------------------------------------- *)
(* Coprimes by a divisor                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the set of coprimes by a divisor of n *)
val coprimes_by_def = Define `
    coprimes_by n d = if (0 < n /\ d divides n) then coprimes (n DIV d) else {}
`;

(*
EVAL ``coprimes_by 10 2``; = {4; 3; 2; 1}
EVAL ``coprimes_by 10 5``; = {1}
*)

(* Theorem: j IN (coprimes_by n d) <=> (0 < n /\ d divides n /\ j IN coprimes (n DIV d)) *)
(* Proof: by coprimes_by_def, MEMBER_NOT_EMPTY *)
val coprimes_by_element = store_thm(
  "coprimes_by_element",
  ``!n d j. j IN (coprimes_by n d) <=> (0 < n /\ d divides n /\ j IN coprimes (n DIV d))``,
  metis_tac[coprimes_by_def, MEMBER_NOT_EMPTY]);

(* Theorem: FINITE (coprimes_by n d) *)
(* Proof:
   From coprimes_by_def, this follows by:
   (1) !k. FINITE (coprimes k)  by coprimes_finite
   (2) FINITE {}                by FINITE_EMPTY
*)
val coprimes_by_finite = store_thm(
  "coprimes_by_finite",
  ``!n d. FINITE (coprimes_by n d)``,
  rw[coprimes_by_def, coprimes_finite]);

(* Theorem: coprimes_by 0 d = {} *)
(* Proof: by coprimes_by_def *)
val coprimes_by_0 = store_thm(
  "coprimes_by_0",
  ``!d. coprimes_by 0 d = {}``,
  rw[coprimes_by_def]);

(* Theorem: coprimes_by n 0 = {} *)
(* Proof:
     coprimes_by n 0
   = if 0 < n /\ 0 divides n then coprimes (n DIV 0) else {}
   = 0 < 0 then coprimes (n DIV 0) else {}    by ZERO_DIVIDES
   = {}                                       by prim_recTheory.LESS_REFL
*)
val coprimes_by_by_0 = store_thm(
  "coprimes_by_by_0",
  ``!n. coprimes_by n 0 = {}``,
  rw[coprimes_by_def]);

(* Theorem: 0 < n ==> (coprimes_by n 1 = coprimes n) *)
(* Proof:
   Since 1 divides n       by ONE_DIVIDES_ALL
       coprimes_by n 1
     = coprimes (n DIV 1)  by coprimes_by_def
     = coprimes n          by DIV_ONE, ONE
*)
val coprimes_by_by_1 = store_thm(
  "coprimes_by_by_1",
  ``!n. 0 < n ==> (coprimes_by n 1 = coprimes n)``,
  rw[coprimes_by_def]);

(* Theorem: 0 < n ==> (coprimes_by n n = {1}) *)
(* Proof:
   Since n divides n       by DIVIDES_REFL
       coprimes_by n n
     = coprimes (n DIV n)  by coprimes_by_def
     = coprimes 1          by DIVMOD_ID, 0 < n
     = {1}                 by coprimes_1
*)
val coprimes_by_by_last = store_thm(
  "coprimes_by_by_last",
  ``!n. 0 < n ==> (coprimes_by n n = {1})``,
  rw[coprimes_by_def, coprimes_1]);

(* Theorem: 0 < n /\ d divides n ==> (coprimes_by n d = coprimes (n DIV d)) *)
(* Proof: by coprimes_by_def *)
val coprimes_by_by_divisor = store_thm(
  "coprimes_by_by_divisor",
  ``!n d. 0 < n /\ d divides n ==> (coprimes_by n d = coprimes (n DIV d))``,
  rw[coprimes_by_def]);

(* Theorem: 0 < n ==> ((coprimes_by n d = {}) <=> ~(d divides n)) *)
(* Proof:
   If part: 0 < n /\ coprimes_by n d = {} ==> ~(d divides n)
      By contradiction. Suppose d divides n.
      Then d divides n and 0 < n means
           0 < d /\ d <= n                           by divides_pos, 0 < n
      Also coprimes_by n d = coprimes (n DIV d)      by coprimes_by_def
        so coprimes (n DIV d) = {} <=> n DIV d = 0   by coprimes_eq_empty
      Thus n < d         by DIV_EQ_0
      which contradicts d <= n.
   Only-if part: 0 < n /\ ~(d divides n) ==> coprimes n d = {}
      This follows by coprimes_by_def
*)
Theorem coprimes_by_eq_empty :
    !n d. 0 < n ==> ((coprimes_by n d = {}) <=> ~(d divides n))
Proof
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `0 < d /\ d <= n` by metis_tac[divides_pos] >>
    `n DIV d = 0` by metis_tac[coprimes_by_def, coprimes_eq_empty] >>
    `n < d` by rw[GSYM DIV_EQ_0] >>
    decide_tac,
    rw[coprimes_by_def]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* GCD Equivalence Class                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the set of values with the same gcd *)
val gcd_matches_def = zDefine `
    gcd_matches n d = {j| j IN (natural n) /\ (gcd j n = d)}
`;
(* use zDefine as this is not computationally effective. *)

(* Theorem: gcd_matches n d = (natural n) INTER {j | gcd j n = d} *)
(* Proof: by gcd_matches_def *)
Theorem gcd_matches_alt[compute]:
  !n d. gcd_matches n d = (natural n) INTER {j | gcd j n = d}
Proof
  simp[gcd_matches_def, EXTENSION]
QED

(*
EVAL ``gcd_matches 10 2``; = {8; 6; 4; 2}
EVAL ``gcd_matches 10 5``; = {5}
*)

(* Theorem: j IN gcd_matches n d <=> 0 < j /\ j <= n /\ (gcd j n = d) *)
(* Proof: by gcd_matches_def *)
val gcd_matches_element = store_thm(
  "gcd_matches_element",
  ``!n d j. j IN gcd_matches n d <=> 0 < j /\ j <= n /\ (gcd j n = d)``,
  rw[gcd_matches_def, natural_element]);

(* Theorem: (gcd_matches n d) SUBSET (natural n) *)
(* Proof: by gcd_matches_def, SUBSET_DEF *)
val gcd_matches_subset = store_thm(
  "gcd_matches_subset",
  ``!n d. (gcd_matches n d) SUBSET (natural n)``,
  rw[gcd_matches_def, SUBSET_DEF]);

(* Theorem: FINITE (gcd_matches n d) *)
(* Proof:
   Since (gcd_matches n d) SUBSET (natural n)   by coprimes_subset
     and !n. FINITE (natural n)                 by natural_finite
      so FINITE (gcd_matches n d)               by SUBSET_FINITE
*)
val gcd_matches_finite = store_thm(
  "gcd_matches_finite",
  ``!n d. FINITE (gcd_matches n d)``,
  metis_tac[gcd_matches_subset, natural_finite, SUBSET_FINITE]);

(* Theorem: gcd_matches 0 d = {} *)
(* Proof:
       j IN gcd_matches 0 d
   <=> 0 < j /\ j <= 0 /\ (gcd j 0 = d)   by gcd_matches_element
   Since no j can satisfy this, the set is empty.
*)
val gcd_matches_0 = store_thm(
  "gcd_matches_0",
  ``!d. gcd_matches 0 d = {}``,
  rw[gcd_matches_element, EXTENSION]);

(* Theorem: gcd_matches n 0 = {} *)
(* Proof:
       x IN gcd_matches n 0
   <=> 0 < x /\ x <= n /\ (gcd x n = 0)        by gcd_matches_element
   <=> 0 < x /\ x <= n /\ (x = 0) /\ (n = 0)   by GCD_EQ_0
   <=> F                                       by 0 < x, x = 0
   Hence gcd_matches n 0 = {}                  by EXTENSION
*)
val gcd_matches_with_0 = store_thm(
  "gcd_matches_with_0",
  ``!n. gcd_matches n 0 = {}``,
  rw[EXTENSION, gcd_matches_element]);

(* Theorem: gcd_matches 1 d = if d = 1 then {1} else {} *)
(* Proof:
       j IN gcd_matches 1 d
   <=> 0 < j /\ j <= 1 /\ (gcd j 1 = d)   by gcd_matches_element
   Only j to satisfy this is j = 1.
   and d = gcd 1 1 = 1                    by GCD_REF
   If d = 1, j = 1 is the only element.
   If d <> 1, the only element is taken out, set is empty.
*)
val gcd_matches_1 = store_thm(
  "gcd_matches_1",
  ``!d. gcd_matches 1 d = if d = 1 then {1} else {}``,
  rw[gcd_matches_element, EXTENSION]);

(* Theorem: 0 < n /\ d divides n ==> d IN (gcd_matches n d) *)
(* Proof:
   Note  0 < n /\ d divides n
     ==> 0 < d, and d <= n           by divides_pos
     and gcd d n = d                 by divides_iff_gcd_fix
   Hence d IN (gcd_matches n d)      by gcd_matches_element
*)
val gcd_matches_has_divisor = store_thm(
  "gcd_matches_has_divisor",
  ``!n d. 0 < n /\ d divides n ==> d IN (gcd_matches n d)``,
  rw[gcd_matches_element] >-
  metis_tac[divisor_pos] >-
  rw[DIVIDES_LE] >>
  rw[GSYM divides_iff_gcd_fix]);

(* Theorem: j IN (gcd_matches n d) ==> d divides j /\ d divides n *)
(* Proof:
   If j IN (gcd_matches n d), gcd j n = d    by gcd_matches_element
   This means d divides j /\ d divides n     by GCD_IS_GREATEST_COMMON_DIVISOR
*)
val gcd_matches_element_divides = store_thm(
  "gcd_matches_element_divides",
  ``!n d j. j IN (gcd_matches n d) ==> d divides j /\ d divides n``,
  metis_tac[gcd_matches_element, GCD_IS_GREATEST_COMMON_DIVISOR]);

(* Theorem: 0 < n ==> ((gcd_matches n d = {}) <=> ~(d divides n)) *)
(* Proof:
   If part: 0 < n /\ (gcd_matches n d = {}) ==> ~(d divides n)
      By contradiction, suppose d divides n.
      Then d IN gcd_matches n d               by gcd_matches_has_divisor
      This contradicts gcd_matches n d = {}   by MEMBER_NOT_EMPTY
   Only-if part: 0 < n /\ ~(d divides n) ==> (gcd_matches n d = {})
      By contradiction, suppose gcd_matches n d <> {}.
      Then ?j. j IN (gcd_matches n d)         by MEMBER_NOT_EMPTY
      Giving d divides j /\ d divides n       by gcd_matches_element_divides
      This contradicts ~(d divides n).
*)
val gcd_matches_eq_empty = store_thm(
  "gcd_matches_eq_empty",
  ``!n d. 0 < n ==> ((gcd_matches n d = {}) <=> ~(d divides n))``,
  rw[EQ_IMP_THM] >-
  metis_tac[gcd_matches_has_divisor, MEMBER_NOT_EMPTY] >>
  metis_tac[gcd_matches_element_divides, MEMBER_NOT_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Phi Function                                                              *)
(* ------------------------------------------------------------------------- *)

(* Define the Euler phi function from coprime set *)
val phi_def = Define `
   phi n = CARD (coprimes n)
`;
(* Since (coprimes n) is computable, phi n is now computable *)

(*
> EVAL ``phi 10``;
val it = |- phi 10 = 4: thm
*)

(* Theorem: phi n = LENGTH (FILTER (\j. coprime j n) (GENLIST SUC n)) *)
(* Proof:
   Let ls = FILTER (\j. coprime j n) (GENLIST SUC n).
   Note ALL_DISTINCT (GENLIST SUC n)       by ALL_DISTINCT_GENLIST, SUC_EQ
   Thus ALL_DISTINCT ls                    by FILTER_ALL_DISTINCT
     phi n = CARD (coprimes n)             by phi_def
           = CARD (set ls)                 by coprimes_thm
           = LENGTH ls                     by ALL_DISTINCT_CARD_LIST_TO_SET
*)
val phi_thm = store_thm(
  "phi_thm",
  ``!n. phi n = LENGTH (FILTER (\j. coprime j n) (GENLIST SUC n))``,
  rpt strip_tac >>
  qabbrev_tac `ls = FILTER (\j. coprime j n) (GENLIST SUC n)` >>
  `ALL_DISTINCT ls` by rw[ALL_DISTINCT_GENLIST, FILTER_ALL_DISTINCT, Abbr`ls`] >>
  `phi n = CARD (coprimes n)` by rw[phi_def] >>
  `_ = CARD (set ls)` by rw[coprimes_thm, Abbr`ls`] >>
  `_ = LENGTH ls` by rw[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  decide_tac);

(* Theorem: phi = CARD o coprimes *)
(* Proof: by phi_def, FUN_EQ_THM *)
val phi_fun = store_thm(
  "phi_fun",
  ``phi = CARD o coprimes``,
  rw[phi_def, FUN_EQ_THM]);

(* Theorem: 0 < n ==> 0 < phi n *)
(* Proof:
   Since 1 IN coprimes n       by coprimes_has_1
      so coprimes n <> {}      by MEMBER_NOT_EMPTY
     and FINITE (coprimes n)   by coprimes_finite
   hence phi n <> 0            by CARD_EQ_0
      or 0 < phi n
*)
val phi_pos = store_thm(
  "phi_pos",
  ``!n. 0 < n ==> 0 < phi n``,
  rpt strip_tac >>
  `coprimes n <> {}` by metis_tac[coprimes_has_1, MEMBER_NOT_EMPTY] >>
  `FINITE (coprimes n)` by rw[coprimes_finite] >>
  `phi n <> 0` by rw[phi_def, CARD_EQ_0] >>
  decide_tac);

(* Theorem: phi 0 = 0 *)
(* Proof:
     phi 0
   = CARD (coprimes 0)   by phi_def
   = CARD {}             by coprimes_0
   = 0                   by CARD_EMPTY
*)
val phi_0 = store_thm(
  "phi_0",
  ``phi 0 = 0``,
  rw[phi_def, coprimes_0]);

(* Theorem: (phi n = 0) <=> (n = 0) *)
(* Proof:
   If part: (phi n = 0) ==> (n = 0)    by phi_pos, NOT_ZERO_LT_ZERO
   Only-if part: phi 0 = 0             by phi_0
*)
val phi_eq_0 = store_thm(
  "phi_eq_0",
  ``!n. (phi n = 0) <=> (n = 0)``,
  metis_tac[phi_0, phi_pos, NOT_ZERO_LT_ZERO]);

(* Theorem: phi 1 = 1 *)
(* Proof:
     phi 1
   = CARD (coprimes 1)    by phi_def
   = CARD {1}             by coprimes_1
   = 1                    by CARD_SING
*)
val phi_1 = store_thm(
  "phi_1",
  ``phi 1 = 1``,
  rw[phi_def, coprimes_1]);

(* Theorem: 1 < n ==> (phi n = totient n) *)
(* Proof:
      phi n
    = CARD (coprimes n)     by phi_def
    = CARD (Euler n )       by coprimes_eq_Euler
    = totient n             by totient_def
*)
val phi_eq_totient = store_thm(
  "phi_eq_totient",
  ``!n. 1 < n ==> (phi n = totient n)``,
  rw[phi_def, totient_def, coprimes_eq_Euler]);

(* Theorem: prime n ==> (phi n = n - 1) *)
(* Proof:
   Since prime n ==> 1 < n   by ONE_LT_PRIME
   Hence   phi n
         = totient n         by phi_eq_totient
         = n - 1             by Euler_card_prime
*)
val phi_prime = store_thm(
  "phi_prime",
  ``!n. prime n ==> (phi n = n - 1)``,
  rw[ONE_LT_PRIME, phi_eq_totient, Euler_card_prime]);

(* Theorem: phi 2 = 1 *)
(* Proof:
   Since prime 2               by PRIME_2
      so phi 2 = 2 - 1 = 1     by phi_prime
*)
val phi_2 = store_thm(
  "phi_2",
  ``phi 2 = 1``,
  rw[phi_prime, PRIME_2]);

(* Theorem: 2 < n ==> 1 < phi n *)
(* Proof:
   Note 1 IN (coprimes n)        by coprimes_has_1, 0 < n
    and (n - 1) IN (coprimes n)  by coprimes_has_last_but_1, 1 < n
    and n - 1 <> 1               by 2 < n
    Now FINITE (coprimes n)      by coprimes_finite]
    and {1; (n-1)} SUBSET (coprimes n)   by SUBSET_DEF, above
   Note CARD {1; (n-1)} = 2      by CARD_INSERT, CARD_EMPTY, TWO
   thus 2 <= CARD (coprimes n)   by CARD_SUBSET
     or 1 < phi n                by phi_def
*)
val phi_gt_1 = store_thm(
  "phi_gt_1",
  ``!n. 2 < n ==> 1 < phi n``,
  rw[phi_def] >>
  `0 < n /\ 1 < n /\ n - 1 <> 1` by decide_tac >>
  `1 IN (coprimes n)` by rw[coprimes_has_1] >>
  `(n - 1) IN (coprimes n)` by rw[coprimes_has_last_but_1] >>
  `FINITE (coprimes n)` by rw[coprimes_finite] >>
  `{1; (n-1)} SUBSET (coprimes n)` by rw[SUBSET_DEF] >>
  `CARD {1; (n-1)} = 2` by rw[] >>
  `2 <= CARD (coprimes n)` by metis_tac[CARD_SUBSET] >>
  decide_tac);

(* Theorem: phi n <= n *)
(* Proof:
   Note phi n = CARD (coprimes n)    by phi_def
    and coprimes n SUBSET natural n  by coprimes_subset
    Now FINITE (natural n)           by natural_finite
    and CARD (natural n) = n         by natural_card
     so CARD (coprimes n) <= n       by CARD_SUBSET
*)
val phi_le = store_thm(
  "phi_le",
  ``!n. phi n <= n``,
  metis_tac[phi_def, coprimes_subset, natural_finite, natural_card, CARD_SUBSET]);

(* Theorem: 1 < n ==> phi n < n *)
(* Proof:
   Note phi n = CARD (coprimes n)    by phi_def
    and 1 < n ==> !j. j IN coprimes n ==> j < n     by coprimes_element_less
    but 0 NOTIN coprimes n           by coprimes_no_0
     or coprimes n SUBSET (count n) DIFF {0}  by SUBSET_DEF, IN_DIFF
    Let s = (count n) DIFF {0}.
   Note {0} SUBSET count n           by SUBSET_DEF]);
     so count n INTER {0} = {0}      by SUBSET_INTER_ABSORPTION
    Now FINITE s                     by FINITE_COUNT, FINITE_DIFF
    and CARD s = n - 1               by CARD_COUNT, CARD_DIFF, CARD_SING
     so CARD (coprimes n) <= n - 1   by CARD_SUBSET
     or phi n < n                    by arithmetic
*)
val phi_lt = store_thm(
  "phi_lt",
  ``!n. 1 < n ==> phi n < n``,
  rw[phi_def] >>
  `!j. j IN coprimes n ==> j < n` by rw[coprimes_element_less] >>
  `!j. j IN coprimes n ==> j <> 0` by metis_tac[coprimes_no_0] >>
  qabbrev_tac `s = (count n) DIFF {0}` >>
  `coprimes n SUBSET s` by rw[SUBSET_DEF, Abbr`s`] >>
  `{0} SUBSET count n` by rw[SUBSET_DEF] >>
  `count n INTER {0} = {0}` by metis_tac[SUBSET_INTER_ABSORPTION, INTER_COMM] >>
  `FINITE s` by rw[Abbr`s`] >>
  `CARD s = n - 1` by rw[Abbr`s`] >>
  `CARD (coprimes n) <= n - 1` by metis_tac[CARD_SUBSET] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Divisors                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define the set of divisors of a number. *)
val divisors_def = zDefine `
   divisors n = {d | d <= n /\ d divides n}
`;
(* use zDefine as this is not computationally effective. *)
(* Note: use of d <= n to give bounded divisors, so that divisors_0 = {0} only. *)
(* Note: for 0 < n, d <= n is redundant, as DIVIDES_LE implies it. *)

(* Theorem: d IN divisors n <=> d <= n /\ d divides n *)
(* Proof: by divisors_def *)
val divisors_element = store_thm(
  "divisors_element",
  ``!n d. d IN divisors n <=> d <= n /\ d divides n``,
  rw[divisors_def]);

(* Theorem: 0 < n ==> !d. d IN divisors n <=> d divides n *)
(* Proof:
   If part: d IN divisors n ==> d divides n
      True by divisors_element
   Only-if part: 0 < n /\ d divides n ==> d IN divisors n
      Since 0 < n /\ d divides n
        ==> 0 < d /\ d <= n      by divides_pos
       Hence d IN divisors n     by divisors_element
*)
val divisors_element_alt = store_thm(
  "divisors_element_alt",
  ``!n. 0 < n ==> !d. d IN divisors n <=> d divides n``,
  metis_tac[divisors_element, divides_pos]);

(* Theorem: 0 < n ==> 1 IN (divisors n) *)
(* Proof:
    Note 0 < n ==> 1 <= n    by arithmetic
     and 1 divides n         by ONE_DIVIDES_ALL
   Hence 1 IN (divisors n)   by divisors_element
*)
val divisors_has_one = store_thm(
  "divisors_has_one",
  ``!n. 0 < n ==> 1 IN (divisors n)``,
  rw[divisors_element]);

(* Theorem: n IN (divisors n) *)
(* Proof: by divisors_element *)
val divisors_has_last = store_thm(
  "divisors_has_last",
  ``!n. n IN (divisors n)``,
  rw[divisors_element]);

(* Theorem: divisors n <> {} *)
(* Proof: by divisors_has_last, MEMBER_NOT_EMPTY *)
val divisors_not_empty = store_thm(
  "divisors_not_empty",
  ``!n. divisors n <> {}``,
  metis_tac[divisors_has_last, MEMBER_NOT_EMPTY]);

(* Idea: a method to evaluate divisors. *)

(* Theorem: divisors n =
            if n = 0 then {0}
            else IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n) *)
(* Proof:
   If n = 0,
        divisors 0
      = {d | d <= 0 /\ d divides 0}      by divisors_def
      = {0}                              by d <= 0, and ALL_DIVIDES_0
   If n <> 0,
        divisors n
      = {d | d <= n /\ d divides n}      by divisors_def
      = {d | d <> 0 /\ d <= n /\ d divides n}
                                         by ZERO_DIVIDES
      = {k + 1 | (k + 1) <= n /\ (k + 1) divides n}
                                         by num_CASES, d <> 0
      = {k + 1 | k < n /\ (k + 1) divides n}
                                         by arithmetic
      = IMAGE (\j. if (j + 1) divides n then j + 1 else 1) {k | k < n}
                                         by IMAGE_DEF
      = IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n)
                                         by count_def
*)
Theorem divisors_eqn[compute]:
  !n. divisors n =
       if n = 0 then {0}
       else IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n)
Proof
  (rw[divisors_def, EXTENSION, EQ_IMP_THM] >> rw[]) >>
  `x <> 0` by metis_tac[ZERO_DIVIDES] >>
  `?k. x = SUC k` by metis_tac[num_CASES] >>
  qexists_tac `k` >>
  fs[ADD1]
QED

(*
> EVAL ``divisors 3``; = {3; 1}: thm
> EVAL ``divisors 4``; = {4; 2; 1}: thm
> EVAL ``divisors 5``; = {5; 1}: thm
> EVAL ``divisors 6``; = {6; 3; 2; 1}: thm
> EVAL ``divisors 7``; = {7; 1}: thm
> EVAL ``divisors 8``; = {8; 4; 2; 1}: thm
> EVAL ``divisors 9``; = {9; 3; 1}: thm
*)

(* Idea: when factor divides, its cofactor also divides. *)

(* Theorem: 0 < n /\ d IN divisors n ==> (n DIV d) IN divisors n *)
(* Proof:
   Note d <= n /\ d divides n      by divisors_def
     so 0 < d                      by ZERO_DIVIDES
    and n DIV d <= n               by DIV_LESS_EQ, 0 < d
    and n DIV d divides n          by DIVIDES_COFACTOR, 0 < d
*)
Theorem divisors_cofactor:
  !n d. 0 < n /\ d IN divisors n ==> (n DIV d) IN divisors n
Proof
  simp [divisors_def] >>
  ntac 3 strip_tac >>
  `0 < d` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  rw[DIV_LESS_EQ, DIVIDES_COFACTOR]
QED

(* Theorem: 0 < n ==> ((divisors n) DELETE n = {m | m < n /\ m divides n}) *)
(* Proof:
     (divisors n) DELETE n
   = {m | m <= n /\ m divides n} DELETE n     by divisors_def
   = {m | m <= n /\ m divides n} DIFF {n}     by DELETE_DEF
   = {m | m <> n /\ m <= n /\ m divides n}    by IN_DIFF
   = {m | m < n /\ m divides n}               by LESS_OR_EQ
*)
val divisors_delete_last = store_thm(
  "divisors_delete_last",
  ``!n. 0 < n ==> ((divisors n) DELETE n = {m | m < n /\ m divides n})``,
  rw[divisors_def, EXTENSION, EQ_IMP_THM]);

(* Theorem: 0 < n ==> !d. d IN (divisors n) ==> 0 < d *)
(* Proof:
   Since d IN (divisors n), d divides n      by divisors_element
   By contradiction, if d = 0, then n = 0    by ZERO_DIVIDES
   This contradicts 0 < n.
*)
val divisors_nonzero = store_thm(
  "divisors_nonzero",
  ``!n. 0 < n ==> !d. d IN (divisors n) ==> 0 < d``,
  metis_tac[divisors_element, ZERO_DIVIDES, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n ==> !d. d IN divisors n ==> n DIV d IN divisors n *)
(* Proof:
   By divisors_element, this is to show:
      0 < n /\ d <= n /\ d divides n ==> n DIV d <= n /\ n DIV d divides n
   Since 0 < n /\ d divides n ==> 0 < d   by divisor_pos
      so n = (n DIV d) * d                by DIVIDES_EQN, 0 < d
           = d * (n DIV d)                by MULT_COMM
   Hence (n DIV d) divides n              by divides_def
     and (n DIV d) <= n                   by DIVIDES_LE, 0 < n
*)
val divisors_has_cofactor = store_thm(
  "divisors_has_cofactor",
  ``!n. 0 < n ==> !d. d IN divisors n ==> n DIV d IN divisors n``,
  rewrite_tac[divisors_element] >>
  ntac 4 strip_tac >>
  `0 < d` by metis_tac[divisor_pos] >>
  `n = (n DIV d) * d` by rw[GSYM DIVIDES_EQN] >>
  `_ = d * (n DIV d)` by rw[MULT_COMM] >>
  metis_tac[divides_def, DIVIDES_LE]);

(* Theorem: divisors n SUBSET upto n *)
(* Proof: by divisors_def, SUBSET_DEF *)
val divisors_subset_upto = store_thm(
  "divisors_subset_upto",
  ``!n. divisors n SUBSET upto n``,
  rw[divisors_def, SUBSET_DEF]);

(* Theorem: 0 < n ==> (divisors n) SUBSET (natural n) *)
(* Proof:
   By SUBSET_DEF, this is to show:
      x IN (divisors n) ==> x IN (natural n)
   Since x IN (divisors n)
     ==> x <= n /\ x divides n    by divisors_element
     ==> x <= n /\ 0 < x          since n <> 0, so x <> 0 by ZERO_DIVIDES
     ==> x IN (natural n)         by natural_element
*)
val divisors_subset_natural = store_thm(
  "divisors_subset_natural",
  ``!n. 0 < n ==> (divisors n) SUBSET (natural n)``,
  rw[divisors_element, natural_element, SUBSET_DEF] >>
  metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO]);

(* Theorem: FINITE (divisors n) *)
(* Proof:
   Since (divisors n) SUBSET count (SUC n)   by divisors_subset_upto
     and FINITE (count (SUC n))              by FINITE_COUNT
      so FINITE (divisors n)                 by SUBSET_FINITE
*)
val divisors_finite = store_thm(
  "divisors_finite",
  ``!n. FINITE (divisors n)``,
  metis_tac[divisors_subset_upto, SUBSET_FINITE, FINITE_COUNT]);

(* Theorem: divisors 0 = {0} *)
(* Proof: divisors_def *)
val divisors_0 = store_thm(
  "divisors_0",
  ``divisors 0 = {0}``,
  rw[divisors_def]);

(* Theorem: divisors 1 = {1} *)
(* Proof: divisors_def *)
val divisors_1 = store_thm(
  "divisors_1",
  ``divisors 1 = {1}``,
  rw[divisors_def, EXTENSION]);

(* Theorem: 0 IN divisors n <=> (n = 0) *)
(* Proof:
       0 IN divisors n
   <=> 0 <= n /\ 0 divides n    by divisors_element
   <=> n = 0                    by ZERO_DIVIDES
*)
val divisors_has_0 = store_thm(
  "divisors_has_0",
  ``!n. 0 IN divisors n <=> (n = 0)``,
  rw[divisors_element]);

(* Theorem: 0 < n ==> BIJ (\d. n DIV d) (divisors n) (divisors n) *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) d IN divisors n ==> n DIV d IN divisors n
       True by divisors_has_cofactor.
   (2) d IN divisors n /\ d' IN divisors n /\ n DIV d = n DIV d' ==> d = d'
       d IN divisors n ==> d divides n /\ 0 < d           by divisors_element, divisor_pos
       d' IN divisors n ==> d' divides n /\ 0 < d'        by divisors_element, divisor_pos
       Hence n = (n DIV d) * d  and n = (n DIV d') * d'   by DIVIDES_EQN
       giving   (n DIV d) * d = (n DIV d') * d'
       Now (n DIV d) <> 0, otherwise contradicts 0 < n    by MULT
       Hence                d = d'                        by EQ_MULT_LCANCEL
   (3) same as (1), true by divisors_has_cofactor.
   (4) x IN divisors n ==> ?d. d IN divisors n /\ (n DIV d = x)
       x IN divisors n ==> x divides n                    by divisors_element
       Let d = n DIV x.
       Then d IN divisors n                               by divisors_has_cofactor
       and  n DIV d = n DIV (n DIV x) = x                 by divide_by_cofactor
*)
val divisors_divisors_bij = store_thm(
  "divisors_divisors_bij",
  ``!n. 0 < n ==> BIJ (\d. n DIV d) (divisors n) (divisors n)``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
  rw[divisors_has_cofactor] >-
 (`n = (n DIV d) * d` by metis_tac[DIVIDES_EQN, divisors_element, divisor_pos] >>
  `n = (n DIV d') * d'` by metis_tac[DIVIDES_EQN, divisors_element, divisor_pos] >>
  `n DIV d <> 0` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  metis_tac[EQ_MULT_LCANCEL]) >-
  rw[divisors_has_cofactor] >>
  metis_tac[divisors_element, divisors_has_cofactor, divide_by_cofactor]);

(*
> divisors_divisors_bij;
val it = |- !n. 0 < n ==> (\d. n DIV d) PERMUTES divisors n: thm
*)

(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem                                                     *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem: sum of phi over divisors                           *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem: A general theory on sum over divisors              *)
(* ------------------------------------------------------------------------- *)

(*
Let n = 6. (divisors 6) = {1, 2, 3, 6}
  IMAGE coprimes (divisors 6)
= {coprimes 1, coprimes 2, coprimes 3, coprimes 6}
= {{1}, {1}, {1, 2}, {1, 5}}   <-- will collapse
  IMAGE (preimage (gcd 6) (count 6)) (divisors 6)
= {{preimage in count 6 of those gcd 6 j = 1},
   {preimage in count 6 of those gcd 6 j = 2},
   {preimage in count 6 of those gcd 6 j = 3},
   {preimage in count 6 of those gcd 6 j = 6}}
= {{1, 5}, {2, 4}, {3}, {6}}
= {1x{1, 5}, 2x{1, 2}, 3x{1}, 6x{1}}
!s. s IN (IMAGE (preimage (gcd n) (count n)) (divisors n))
==> ?d. d divides n /\ d < n /\ s = preimage (gcd n) (count n) d
==> ?d. d divides n /\ d < n /\ s = IMAGE (TIMES d) (coprimes ((gcd n d) DIV d))

  IMAGE (feq_class (count 6) (gcd 6)) (divisors 6)
= {{feq_class in count 6 of those gcd 6 j = 1},
   {feq_class in count 6 of those gcd 6 j = 2},
   {feq_class in count 6 of those gcd 6 j = 3},
   {feq_class in count 6 of those gcd 6 j = 6}}
= {{1, 5}, {2, 4}, {3}, {6}}
= {1x{1, 5}, 2x{1, 2}, 3x{1}, 6x{1}}
That is:  CARD {1, 5} = CARD (coprime 6) = CARD (coprime (6 DIV 1))
          CARD {2, 4} = CARD (coprime 3) = CARD (coprime (6 DIV 2))
          CARD {3} = CARD (coprime 2) = CARD (coprime (6 DIV 3)))
          CARD {6} = CARD (coprime 1) = CARD (coprime (6 DIV 6)))

*)
(* Note:
   In general, what is the condition for:  SIGMA f s = SIGMA g t ?
   Conceptually,
       SIGMA f s = f s1 + f s2 + f s3 + ... + f sn
   and SIGMA g t = g t1 + g t2 + g t3 + ... + g tm

SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST

Use disjoint_bigunion_card
|- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P)
If a partition P = {s | condition on s} the element s = IMAGE g t
e.g.  P = {{1, 5} {2, 4} {3} {6}}
        = {IMAGE (TIMES 1) (coprimes 6/1),
           IMAGE (TIMES 2) (coprimes 6/2),
           IMAGE (TIMES 3) (coprimes 6/3),
           IMAGE (TIMES 6) (coprimes 6/6)}
        =  IMAGE (\d. TIMES d o coprimes (6/d)) {1, 2, 3, 6}

*)

(* Theorem: d divides n ==> !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d *)
(* Proof:
   When n = 0, gcd_matches 0 d = {}       by gcd_matches_0, hence trivially true.
   Otherwise,
   By coprimes_by_def, this is to show:
      0 < n /\ d divides n ==> !j. j IN gcd_matches n d ==> j DIV d IN coprimes (n DIV d)
   Note j IN gcd_matches n d
    ==> d divides j               by gcd_matches_element_divides
   Also d IN gcd_matches n d      by gcd_matches_has_divisor
     so 0 < d /\ (d = gcd j n)    by gcd_matches_element
     or d <> 0 /\ (d = gcd n j)   by GCD_SYM
   With the given d divides n,
        j = d * (j DIV d)         by DIVIDES_EQN, MULT_COMM, 0 < d
        n = d * (n DIV d)         by DIVIDES_EQN, MULT_COMM, 0 < d
  Hence d = d * gcd (n DIV d) (j DIV d)        by GCD_COMMON_FACTOR
     or d * 1 = d * gcd (n DIV d) (j DIV d)    by MULT_RIGHT_1
  giving    1 = gcd (n DIV d) (j DIV d)        by EQ_MULT_LCANCEL, d <> 0
      or    coprime (j DIV d) (n DIV d)        by GCD_SYM
   Also j IN natural n            by gcd_matches_subset, SUBSET_DEF
  Hence 0 < j DIV d /\ j DIV d <= n DIV d      by natural_cofactor_natural_reduced
     or j DIV d IN coprimes (n DIV d)          by coprimes_element
*)
val gcd_matches_divisor_element = store_thm(
  "gcd_matches_divisor_element",
  ``!n d. d divides n ==> !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[gcd_matches_0, NOT_IN_EMPTY] >>
  `0 < n` by decide_tac >>
  rw[coprimes_by_def] >>
  `d divides j` by metis_tac[gcd_matches_element_divides] >>
  `0 < d /\ 0 < j /\ j <= n /\ (d = gcd n j)` by metis_tac[gcd_matches_has_divisor, gcd_matches_element, GCD_SYM] >>
  `d <> 0` by decide_tac >>
  `(j = d * (j DIV d)) /\ (n = d * (n DIV d))` by metis_tac[DIVIDES_EQN, MULT_COMM] >>
  `coprime (n DIV d) (j DIV d)` by metis_tac[GCD_COMMON_FACTOR, MULT_RIGHT_1, EQ_MULT_LCANCEL] >>
  `0 < j DIV d /\ j DIV d <= n DIV d` by metis_tac[natural_cofactor_natural_reduced, natural_element] >>
  metis_tac[coprimes_element, GCD_SYM]);

(* Theorem: d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d) *)
(* Proof:
   When n = 0, gcd_matches 0 d = {}       by gcd_matches_0
           and coprimes_by 0 d = {}       by coprimes_by_0, hence trivially true.
   Otherwise,
   By definitions, this is to show:
   (1) j IN gcd_matches n d ==> j DIV d IN coprimes_by n d
       True by gcd_matches_divisor_element.
   (2) j IN gcd_matches n d /\ j' IN gcd_matches n d /\ j DIV d = j' DIV d ==> j = j'
      Note j IN gcd_matches n d /\ j' IN gcd_matches n d
       ==> d divides j /\ d divides j'             by gcd_matches_element_divides
      Also d IN (gcd_matches n d)                  by gcd_matches_has_divisor
        so 0 < d                                   by gcd_matches_element
      Thus j = (j DIV d) * d                       by DIVIDES_EQN, 0 < d
       and j' = (j' DIV d) * d                     by DIVIDES_EQN, 0 < d
      Since j DIV d = j' DIV d, j = j'.
   (3) same as (1), true by gcd_matches_divisor_element,
   (4) d divides n /\ x IN coprimes_by n d ==> ?j. j IN gcd_matches n d /\ (j DIV d = x)
       Note x IN coprimes (n DIV d)                by coprimes_by_def
        ==> 0 < x /\ x <= n DIV d /\ (coprime x (n DIV d))  by coprimes_element
        And d divides n /\ 0 < n
        ==> 0 < d /\ d <> 0                        by ZERO_DIVIDES, 0 < n
       Giving (x * d) DIV d = x                    by MULT_DIV, 0 < d
        Let j = x * d. so j DIV d = x              by above
       Then d divides j                            by divides_def
        ==> j = (j DIV d) * d                      by DIVIDES_EQN, 0 < d
       Note d divides n
        ==> n = (n DIV d) * d                      by DIVIDES_EQN, 0 < d
      Hence gcd j n
          = gcd (d * (j DIV d)) (d * (n DIV d))    by MULT_COMM
          = d * gcd (j DIV d) (n DIV d)            by GCD_COMMON_FACTOR
          = d * gcd x (n DIV d)                    by x = j DIV d
          = d * 1                                  by coprime x (n DIV d)
          = d                                      by MULT_RIGHT_1
      Since j = x * d, 0 < j                       by MULT_EQ_0, 0 < x, 0 < d
       Also x <= n DIV d
       means j DIV d <= n DIV d                    by x = j DIV d
          so (j DIV d) * d <= (n DIV d) * d        by LE_MULT_RCANCEL, d <> 0
          or             j <= n                    by above
      Hence j IN gcd_matches n d                   by gcd_matches_element
*)
val gcd_matches_bij_coprimes_by = store_thm(
  "gcd_matches_bij_coprimes_by",
  ``!n d. d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d)``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `gcd_matches n d = {}` by rw[gcd_matches_0] >>
    `coprimes_by n d = {}` by rw[coprimes_by_0] >>
    rw[],
    `0 < n` by decide_tac >>
    rw[BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >-
    rw[GSYM gcd_matches_divisor_element] >-
    metis_tac[gcd_matches_element_divides, gcd_matches_has_divisor, gcd_matches_element, DIVIDES_EQN] >-
    rw[GSYM gcd_matches_divisor_element] >>
    `0 < x /\ x <= n DIV d /\ (coprime x (n DIV d))` by metis_tac[coprimes_by_def, coprimes_element] >>
    `0 < d /\ d <> 0` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
    `(x * d) DIV d = x` by rw[MULT_DIV] >>
    qabbrev_tac `j = x * d` >>
    `d divides j` by metis_tac[divides_def] >>
    `(n = (n DIV d) * d) /\ (j = (j DIV d) * d)` by rw[GSYM DIVIDES_EQN] >>
    `gcd j n = d` by metis_tac[GCD_COMMON_FACTOR, MULT_COMM, MULT_RIGHT_1] >>
    `0 < j` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    `j <= n` by metis_tac[LE_MULT_RCANCEL] >>
    metis_tac[gcd_matches_element]
  ]);

(* Theorem: 0 < n /\ d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d)) *)
(* Proof: by gcd_matches_bij_coprimes_by, coprimes_by_by_divisor *)
val gcd_matches_bij_coprimes = store_thm(
  "gcd_matches_bij_coprimes",
  ``!n d. 0 < n /\ d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d))``,
  metis_tac[gcd_matches_bij_coprimes_by, coprimes_by_by_divisor]);

(* Note: it is not useful to show:
         CARD o (gcd_matches n) = CARD o coprimes,
   as FUN_EQ_THM will demand:  CARD (gcd_matches n x) = CARD (coprimes x),
   which is not possible.
*)

(* Theorem: 0 < n ==> (divisors n = IMAGE (gcd n) (natural n)) *)
(* Proof:
     divisors n
   = {d | d <= n /\ d divides n}                by divisors_def
   = {d | 0 < d /\ d <= n /\ d divides n}       by divisor_pos
   = {d | d IN (natural n) /\ d divides n}      by natural_element
   = {d | d IN (natural n) /\ (gcd d n = d)}    by divides_iff_gcd_fix
   = {d | d IN (natural n) /\ (gcd n d = d)}    by GCD_SYM
   = {gcd n d | d | d IN (natural n)}           by replacemnt
   = IMAGE (gcd n) (natural n)                  by IMAGE_DEF

   Or, by divisors_def, natuarl_elemnt, IN_IMAGE, this is to show:
   (1) 0 < n /\ x <= n /\ x divides n ==> ?x'. (x = gcd n x') /\ 0 < x' /\ x' <= n
       Note x divides n ==> 0 < x               by divisor_pos
       Also x divides n ==> gcd x n = x         by divides_iff_gcd_fix
         or                 gcd n x = x         by GCD_SYM
       Take this x, and the result follows.
   (2) 0 < n /\ 0 < x' /\ x' <= n ==> gcd n x' <= n /\ gcd n x' divides n
       Note gcd n x' divides n                  by GCD_IS_GREATEST_COMMON_DIVISOR
        and gcd n x' <= n                       by DIVIDES_LE, 0 < n.
*)
val divisors_eq_gcd_image = store_thm(
  "divisors_eq_gcd_image",
  ``!n. 0 < n ==> (divisors n = IMAGE (gcd n) (natural n))``,
  rw_tac std_ss[divisors_def, GSPECIFICATION, EXTENSION, IN_IMAGE, natural_element, EQ_IMP_THM] >-
  metis_tac[divisor_pos, divides_iff_gcd_fix, GCD_SYM] >-
  metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_LE] >>
  metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR]);

(* Theorem: feq_class (gcd n) (natural n) d = gcd_matches n d *)
(* Proof:
     feq_class (gcd n) (natural n) d
   = {x | x IN natural n /\ (gcd n x = d)}   by feq_class_def
   = {j | j IN natural n /\ (gcd j n = d)}   by GCD_SYM
   = gcd_matches n d                         by gcd_matches_def
*)
val gcd_eq_equiv_class = store_thm(
  "gcd_eq_equiv_class",
  ``!n d. feq_class (gcd n) (natural n) d = gcd_matches n d``,
  rewrite_tac[feq_class_def, gcd_matches_def] >>
  rw[EXTENSION, GCD_SYM]);

(* Theorem: feq_class (gcd n) (natural n) = gcd_matches n *)
(* Proof: by FUN_EQ_THM, gcd_eq_equiv_class *)
val gcd_eq_equiv_class_fun = store_thm(
  "gcd_eq_equiv_class_fun",
  ``!n. feq_class (gcd n) (natural n) = gcd_matches n``,
  rw[FUN_EQ_THM, gcd_eq_equiv_class]);

(* Theorem: 0 < n ==> (partition (feq (gcd n)) (natural n) = IMAGE (gcd_matches n) (divisors n)) *)
(* Proof:
     partition (feq (gcd n)) (natural n)
   = IMAGE (equiv_class (feq (gcd n)) (natural n)) (natural n)    by partition_elements
   = IMAGE ((feq_class (gcd n) (natural n)) o (gcd n)) (natural n)  by feq_class_fun
   = IMAGE ((gcd_matches n) o (gcd n)) (natural n)       by gcd_eq_equiv_class_fun
   = IMAGE (gcd_matches n) (IMAGE (gcd n) (natural n))   by IMAGE_COMPOSE
   = IMAGE (gcd_matches n) (divisors n)      by divisors_eq_gcd_image, 0 < n
*)
val gcd_eq_partition_by_divisors = store_thm(
  "gcd_eq_partition_by_divisors",
  ``!n. 0 < n ==> (partition (feq (gcd n)) (natural n) = IMAGE (gcd_matches n) (divisors n))``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = natural n` >>
  `partition (feq f) s = IMAGE (equiv_class (feq f) s) s` by rw[partition_elements] >>
  `_ = IMAGE ((feq_class f s) o f) s` by rw[feq_class_fun] >>
  `_ = IMAGE ((gcd_matches n) o f) s` by rw[gcd_eq_equiv_class_fun, Abbr`f`, Abbr`s`] >>
  `_ = IMAGE (gcd_matches n) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  `_ = IMAGE (gcd_matches n) (divisors n)` by rw[divisors_eq_gcd_image, Abbr`f`, Abbr`s`] >>
  rw[]);

(* Theorem: (feq (gcd n)) equiv_on (natural n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = natural n.
*)
val gcd_eq_equiv_on_natural = store_thm(
  "gcd_eq_equiv_on_natural",
  ``!n. (feq (gcd n)) equiv_on (natural n)``,
  rw[feq_equiv]);

(* Theorem: SIGMA f (natural n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n)) *)
(* Proof:
   Let g = gcd n, s = natural n.
   Since FINITE s               by natural_finite
     and (feq g) equiv_on s     by feq_equiv
   The result follows           by set_sigma_by_partition
*)
val sum_over_natural_by_gcd_partition = store_thm(
  "sum_over_natural_by_gcd_partition",
  ``!f n. SIGMA f (natural n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))``,
  rw[feq_equiv, natural_finite, set_sigma_by_partition]);

(* Theorem: SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n)) *)
(* Proof:
   If n = 0,
      LHS = SIGMA f (natural 0)
          = SIGMA f {}             by natural_0
          = 0                      by SUM_IMAGE_EMPTY
      RHS = SIGMA (SIGMA f) (IMAGE (gcd_matches 0) (divisors 0))
          = SIGMA (SIGMA f) (IMAGE (gcd_matches 0) {0})   by divisors_0
          = SIGMA (SIGMA f) {gcd_matches 0 0}             by IMAGE_SING
          = SIGMA (SIGMA f) {{}}                          by gcd_matches_0
          = SIGMA f {}                                    by SUM_IMAGE_SING
          = 0 = LHS                                       by SUM_IMAGE_EMPTY
   Otherwise 0 < n,
     SIGMA f (natural n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n)) by sum_over_natural_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))  by gcd_eq_partition_by_divisors, 0 < n
*)
val sum_over_natural_by_divisors = store_thm(
  "sum_over_natural_by_divisors",
  ``!f n. SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `natural n = {}` by rw_tac std_ss[natural_0] >>
    `divisors n = {0}` by rw_tac std_ss[divisors_0] >>
    `IMAGE (gcd_matches n) (divisors n) = {{}}` by rw[gcd_matches_0] >>
    rw[SUM_IMAGE_SING],
    rw[sum_over_natural_by_gcd_partition, gcd_eq_partition_by_divisors]
  ]);

(* Theorem: 0 < n ==> INJ (gcd_matches n) (divisors n) univ(num) *)
(* Proof:
   By INJ_DEF, this is to show:
      x IN divisors n /\ y IN divisors n /\ gcd_matches n x = gcd_matches n y ==> x = y
   If n = 0,
      then divisors n = {}                by divisors_0
      hence trivially true.
   Otherwise 0 < n,
    Note x IN divisors n
     ==> x <= n /\ x divides n            by divisors_element
    also y IN divisors n
     ==> y <= n /\ y divides n            by divisors_element
   Hence (gcd x n = x) /\ (gcd y n = y)   by divides_iff_gcd_fix
   Since x divides n,  0 < x              by divisor_pos, 0 < n
   Giving x IN gcd_matches n x            by gcd_matches_element
       so x IN gcd_matches n y            by gcd_matches n x = gcd_matches n y
     with gcd x n = y                     by gcd_matches_element
   Therefore y = gcd x n = x.
*)
val gcd_matches_from_divisors_inj = store_thm(
  "gcd_matches_from_divisors_inj",
  ``!n. INJ (gcd_matches n) (divisors n) univ(:num -> bool)``,
  rw[INJ_DEF] >>
  Cases_on `n = 0` >>
  fs[divisors_0] >>
  `0 < n` by decide_tac >>
  `x <= n /\ x divides n /\ y <= n /\ y divides n` by metis_tac[divisors_element] >>
  `(gcd x n = x) /\ (gcd y n = y)` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[divisor_pos, gcd_matches_element]);

(* Theorem: 0 < n ==> (CARD o (gcd_matches n) = CARD o (coprimes_by n)) *)
(* Proof:
   By composition and FUN_EQ_THM, this is to show:
      !x. CARD (gcd_matches n x) = CARD (coprimes_by n x)
   If x divides n,
      Then BIJ (\j. j DIV x) (gcd_matches n x) (coprimes_by n x)  by gcd_matches_bij_coprimes_by
      Also FINITE (gcd_matches n x)                               by gcd_matches_finite
       and FINITE (coprimes_by n x)                               by coprimes_by_finite
      Hence CARD (gcd_matches n x) = CARD (coprimes_by n x)       by FINITE_BIJ_CARD_EQ
   If ~(x divides n),
      If n = 0,
         then gcd_matches 0 x = {}      by gcd_matches_0
          and coprimes_by 0 x = {}      by coprimes_by_0
         Hence true.
      If n <> 0,
         then gcd_matches n x = {}      by gcd_matches_eq_empty, 0 < n
          and coprimes_by n x = {}      by coprimes_by_eq_empty, 0 < n
         Hence CARD {} = CARD {}.
*)
val gcd_matches_and_coprimes_by_same_size = store_thm(
  "gcd_matches_and_coprimes_by_same_size",
  ``!n. CARD o (gcd_matches n) = CARD o (coprimes_by n)``,
  rw[FUN_EQ_THM] >>
  Cases_on `x divides n` >| [
    `BIJ (\j. j DIV x) (gcd_matches n x) (coprimes_by n x)` by rw[gcd_matches_bij_coprimes_by] >>
    `FINITE (gcd_matches n x)` by rw[gcd_matches_finite] >>
    `FINITE (coprimes_by n x)` by rw[coprimes_by_finite] >>
    metis_tac[FINITE_BIJ_CARD_EQ],
    Cases_on `n = 0` >-
    rw[gcd_matches_0, coprimes_by_0] >>
    `gcd_matches n x = {}` by rw[gcd_matches_eq_empty] >>
    `coprimes_by n x = {}` by rw[coprimes_by_eq_empty] >>
    rw[]
  ]);

(* HERE; to fix! *)

(* Theorem: 0 < n ==> (CARD o (coprimes_by n) = \d. phi (if d IN (divisors n) then n DIV d else 0)) *)
(* Proof:
   By FUN_EQ_THM,
      CARD o (coprimes_by n) x
    = CARD (coprimes_by n x)       by composition, combinTheory.o_THM
    = CARD (if x divides n then coprimes (n DIV x) else {})    by coprimes_by_def, 0 < n
    If x divides n,
       x <= n                      by DIVIDES_LE
       so x IN (divisors n)        by divisors_element
       CARD o (coprimes_by n) x
     = CARD (coprimes (n DIV x))
     = phi (n DIV x)               by phi_def
    If ~(x divides n),
       x NOTIN (divisors n)        by divisors_element
       CARD o (coprimes_by n) x
     = CARD {}
     = 0                           by CARD_EMPTY
     = phi 0                       by phi_0
    Hence the same function as:
    \d. phi (if d IN (divisors n) then n DIV d else 0)
*)
val coprimes_by_with_card = store_thm(
  "coprimes_by_with_card",
  ``!n. 0 < n ==> (CARD o (coprimes_by n) = \d. phi (if d IN (divisors n) then n DIV d else 0))``,
  rw[coprimes_by_def, phi_def, divisors_def, FUN_EQ_THM] >>
  metis_tac[DIVIDES_LE, coprimes_0]);

(* Theorem: 0 < n ==> !x. x IN (divisors n) ==> ((CARD o (coprimes_by n)) x = (\d. phi (n DIV d)) x) *)
(* Proof:
   Since x IN (divisors n) ==> x divides n    by divisors_element
       CARD o (coprimes_by n) x
     = CARD (coprimes (n DIV x))   by coprimes_by_def
     = phi (n DIV x)               by phi_def
*)
val coprimes_by_divisors_card = store_thm(
  "coprimes_by_divisors_card",
  ``!n. 0 < n ==> !x. x IN (divisors n) ==> ((CARD o (coprimes_by n)) x = (\d. phi (n DIV d)) x)``,
  rw[coprimes_by_def, phi_def, divisors_def]);

(*
SUM_IMAGE_CONG |- (s1 = s2) /\ (!x. x IN s2 ==> (f1 x = f2 x)) ==> (SIGMA f1 s1 = SIGMA f2 s2)
*)

(* Theorem: n = SIGMA phi (divisors n) *)
(* Proof:
   If n = 0,
        SIGMA phi (divisors 0)
      = SIGMA phi {0}               by divisors_0
      = phi 0                       by SUM_IMAGE_SING
      = 0                           by phi_0
   If n <> 0, 0 < n.
   Note INJ (gcd_matches n) (divisors n) univ(:num -> bool)  by gcd_matches_from_divisors_inj
    and (\d. n DIV d) PERMUTES (divisors n)              by divisors_divisors_bij, 0 < n
   n = CARD (natural n)                                  by natural_card
     = SIGMA CARD (partition (feq (gcd n)) (natural n))  by partition_CARD
     = SIGMA CARD (IMAGE (gcd_matches n) (divisors n))   by gcd_eq_partition_by_divisors
     = SIGMA (CARD o (gcd_matches n)) (divisors n)       by sum_image_by_composition
     = SIGMA (CARD o (coprimes_by n)) (divisors n)       by gcd_matches_and_coprimes_by_same_size
     = SIGMA (\d. phi (n DIV d)) (divisors n)            by SUM_IMAGE_CONG, coprimes_by_divisors_card
     = SIGMA phi (divisors n)                            by sum_image_by_permutation
*)
val Gauss_little_thm = store_thm(
  "Gauss_little_thm",
  ``!n. n = SIGMA phi (divisors n)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[divisors_0, SUM_IMAGE_SING, phi_0] >>
  `0 < n` by decide_tac >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `(feq (gcd n)) equiv_on (natural n)` by rw[gcd_eq_equiv_on_natural] >>
  `INJ (gcd_matches n) (divisors n) univ(:num -> bool)` by rw[gcd_matches_from_divisors_inj] >>
  `(\d. n DIV d) PERMUTES (divisors n)` by rw[divisors_divisors_bij] >>
  `FINITE (divisors n)` by rw[divisors_finite] >>
  `n = CARD (natural n)` by rw[natural_card] >>
  `_ = SIGMA CARD (partition (feq (gcd n)) (natural n))` by rw[partition_CARD] >>
  `_ = SIGMA CARD (IMAGE (gcd_matches n) (divisors n))` by rw[gcd_eq_partition_by_divisors] >>
  `_ = SIGMA (CARD o (gcd_matches n)) (divisors n)` by prove_tac[sum_image_by_composition] >>
  `_ = SIGMA (CARD o (coprimes_by n)) (divisors n)` by rw[gcd_matches_and_coprimes_by_same_size] >>
  `_ = SIGMA (\d. phi (n DIV d)) (divisors n)` by rw[SUM_IMAGE_CONG, coprimes_by_divisors_card] >>
  `_ = SIGMA phi (divisors n)` by metis_tac[sum_image_by_permutation] >>
  rw[]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Recursive definition of phi                                               *)
(* ------------------------------------------------------------------------- *)

(* Define phi by recursion *)
val rec_phi_def = tDefine "rec_phi" `
  rec_phi n = if n = 0 then 0
         else if n = 1 then 1
         else n - SIGMA rec_phi { m | m < n /\ m divides n}`
  (WF_REL_TAC `$< : num -> num -> bool` >> srw_tac[][]);
(* This is the recursive form of Gauss' Little Theorem:  n = SUM phi m, m divides n *)

(* Just using Define without any condition will trigger:

Initial goal:

?R. WF R /\ !n a. n <> 0 /\ n <> 1 /\ a IN {m | m < n /\ m divides n} ==> R a n

Unable to prove termination!

Try using "TotalDefn.tDefine <name> <quotation> <tac>".

The termination goal has been set up using Defn.tgoal <defn>.

So one can set up:
g `?R. WF R /\ !n a. n <> 0 /\ n <> 1 /\ a IN {m | m < n /\ m divides n} ==> R a n`;
e (WF_REL_TAC `$< : num -> num -> bool`);
e (srw[][]);

which gives the tDefine solution.
*)

(* Theorem: rec_phi 0 = 0 *)
(* Proof: by rec_phi_def *)
val rec_phi_0 = store_thm(
  "rec_phi_0",
  ``rec_phi 0 = 0``,
  rw[rec_phi_def]);

(* Theorem: rec_phi 1 = 1 *)
(* Proof: by rec_phi_def *)
val rec_phi_1 = store_thm(
  "rec_phi_1",
  ``rec_phi 1 = 1``,
  rw[Once rec_phi_def]);

(* Theorem: rec_phi n = phi n *)
(* Proof:
   By complete induction on n.
   If n = 0,
      rec_phi 0 = 0      by rec_phi_0
                = phi 0  by phi_0
   If n = 1,
      rec_phi 1 = 1      by rec_phi_1
                = phi 1  by phi_1
   Othewise,
      Let s = {m | m < n /\ m divides n}.
      Note s SUBSET (count n)       by SUBSET_DEF
      thus FINITE s                 by SUBSET_FINITE, FINITE_COUNT
     Hence !m. m IN s
       ==> (rec_phi m = phi m)      by induction hypothesis
      Also n NOTIN s                by EXTENSION
       and n INSERT s
         = {m | m <= n /\ m divides n}
         = divisors n               by divisors_def, EXTENSION, LESS_OR_EQ

        rec_phi n
      = n - (SIGMA rec_phi s)       by rec_phi_def
      = n - (SIGMA phi s)           by SUM_IMAGE_CONG, rec_phi m = phi m
      = (SIGMA phi (divisors n)) - (SIGMA phi s)           by Gauss' Little Theorem
      = (SIGMA phi (n INSERT s)) - (SIGMA phi s)           by divisors n = n INSERT s
      = (phi n + SIGMA phi (s DELETE n)) - (SIGMA phi s)   by SUM_IMAGE_THM
      = (phi n + SIGMA phi s) - (SIGMA phi s)              by DELETE_NON_ELEMENT
      = phi n                                              by ADD_SUB
*)
val rec_phi_eq_phi = store_thm(
  "rec_phi_eq_phi",
  ``!n. rec_phi n = phi n``,
  completeInduct_on `n` >>
  Cases_on `n = 0` >-
  rw[rec_phi_0, phi_0] >>
  Cases_on `n = 1` >-
  rw[rec_phi_1, phi_1] >>
  `0 < n /\ 1 < n` by decide_tac >>
  qabbrev_tac `s = {m | m < n /\ m divides n}` >>
  qabbrev_tac `t = SIGMA rec_phi s` >>
  `!m. m IN s <=> m < n /\ m divides n` by rw[Abbr`s`] >>
  `!m. m IN s ==> (rec_phi m = phi m)` by rw[] >>
  `t = SIGMA phi s` by rw[SUM_IMAGE_CONG, Abbr`t`] >>
  `s SUBSET (count n)` by rw[SUBSET_DEF] >>
  `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  `n NOTIN s` by rw[] >>
  (`n INSERT s = divisors n` by (rw[divisors_def, EXTENSION] >> metis_tac[LESS_OR_EQ, DIVIDES_REFL])) >>
  `n = SIGMA phi (divisors n)` by rw[Gauss_little_thm] >>
  `_ = phi n + SIGMA phi (s DELETE n)` by rw[GSYM SUM_IMAGE_THM] >>
  `_ = phi n + t` by metis_tac[DELETE_NON_ELEMENT] >>
  `rec_phi n = n - t` by metis_tac[rec_phi_def] >>
  decide_tac);


(* ------------------------------------------------------------------------- *)
(* Not Used                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: INJ (coprimes) (univ(:num) DIFF {1}) univ(:num -> bool) *)
(* Proof:
   By INJ_DEF, this is to show:
      x <> 1 /\ y <> 1 /\ coprimes x = coprimes y ==> x = y
   If x = 0, then y = 0              by coprimes_eq_empty
   If y = 0, then x = 0              by coprimes_eq_empty
   If x <> 0 and y <> 0,
      with x <> 1 and y <> 1         by given
      then 1 < x and 1 < y.
      Since MAX_SET (coprimes x) = x - 1    by coprimes_max, 1 < x
        and MAX_SET (coprimes y) = y - 1    by coprimes_max, 1 < y
         If coprimes x = coprimes y,
                 x - 1 = y - 1       by above
      Hence          x = y           by CANCEL_SUB
*)
val coprimes_from_notone_inj = store_thm(
  "coprimes_from_notone_inj",
  ``INJ (coprimes) (univ(:num) DIFF {1}) univ(:num -> bool)``,
  rw[INJ_DEF] >>
  Cases_on `x = 0` >-
  metis_tac[coprimes_eq_empty] >>
  Cases_on `y = 0` >-
  metis_tac[coprimes_eq_empty] >>
  `1 < x /\ 1 < y` by decide_tac >>
  `x - 1 = y - 1` by metis_tac[coprimes_max] >>
  decide_tac);
(* Not very useful. *)

(* Theorem: divisors n = IMAGE (gcd n) (upto n) *)
(* Proof:
     divisors n
   = {d | d <= n /\ d divides n}      by divisors_def
   = {d | d <= n /\ (gcd d n = d)}    by divides_iff_gcd_fix
   = {d | d <= n /\ (gcd n d = d)}    by GCD_SYM
   = {gcd n d | d | d <= n}           by replacemnt
   = IMAGE (gcd n) {d | d <= n}       by IMAGE_DEF
   = IMAGE (gcd n) (count (SUC n))    by count_def
   = IMAGE (gcd n) (upto n)           by notation

   By divisors_def, IN_IMAGE and EXTENSION, this is to show:
   (1) x <= n /\ x divides n ==> ?x'. (x = gcd n x') /\ x' < SUC n
       x <= n ==> x < SUC n           by LESS_EQ_IMP_LESS_SUC
       x divides n ==> x = gcd x n    by divides_iff_gcd_fix
                         = gcd n x    by GCD_SYM
   (2) x' < SUC n ==> gcd n x' <= n /\ gcd n x' divides n
       gcd n x' divides n             by GCD_IS_GREATEST_COMMON_DIVISOR
       If n = 0, x' < 1.
          That is, x' = 0             by arithmetic
           so gcd 0 0 = 0 <= 0        by GCD_0R
          and 0 divides 0             by ZERO_DIVIDES
       If n <> 0, 0 < n.
          gcd n x' divides n
          ==> gcd n x' <= n           by DIVIDES_LE
*)
val divisors_eq_image_gcd_upto = store_thm(
  "divisors_eq_image_gcd_upto",
  ``!n. divisors n = IMAGE (gcd n) (upto n)``,
  rw[divisors_def, EXTENSION, EQ_IMP_THM] >| [
    `x < SUC n` by decide_tac >>
    metis_tac[divides_iff_gcd_fix, GCD_SYM],
    Cases_on `n = 0` >| [
      `x' = 0` by decide_tac >>
      `gcd 0 0 = 0` by rw[GCD_0R] >>
      rw[],
      `0 < n` by decide_tac >>
      `(gcd n x') divides n` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
      rw[DIVIDES_LE]
    ],
    rw[GCD_IS_GREATEST_COMMON_DIVISOR]
  ]);

(* Theorem: (feq (gcd n)) equiv_on (upto n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = gcd n.
*)
val gcd_eq_equiv_on_upto = store_thm(
  "gcd_eq_equiv_on_upto",
  ``!n. (feq (gcd n)) equiv_on (upto n)``,
  rw[feq_equiv]);

(* Theorem: partition (feq (gcd n)) (upto n) = IMAGE (preimage (gcd n) (upto n)) (divisors n) *)
(* Proof:
   Let f = gcd n, s = upto n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                      by feq_partition_by_preimage
   = IMAGE (preimage f s) (IMAGE f s)                by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (upto n))   by expansion
   = IMAGE (preimage f s) (divisors n)               by divisors_eq_image_gcd_upto
*)
val gcd_eq_upto_partition_by_divisors = store_thm(
  "gcd_eq_upto_partition_by_divisors",
  ``!n. partition (feq (gcd n)) (upto n) = IMAGE (preimage (gcd n) (upto n)) (divisors n)``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = upto n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition_by_preimage] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_upto, Abbr`f`, Abbr`s`]);

(* Theorem: SIGMA f (upto n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n)) *)
(* Proof:
   Let g = gcd n, s = upto n.
   Since FINITE s               by upto_finite
     and (feq g) equiv_on s     by feq_equiv
   The result follows           by set_sigma_by_partition
*)
val sum_over_upto_by_gcd_partition = store_thm(
  "sum_over_upto_by_gcd_partition",
  ``!f n. SIGMA f (upto n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))``,
  rw[feq_equiv, set_sigma_by_partition]);

(* Theorem: SIGMA f (upto n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n)) *)
(* Proof:
     SIGMA f (upto n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))                by sum_over_upto_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))  by gcd_eq_upto_partition_by_divisors
*)
val sum_over_upto_by_divisors = store_thm(
  "sum_over_upto_by_divisors",
  ``!f n. SIGMA f (upto n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))``,
  rw[sum_over_upto_by_gcd_partition, gcd_eq_upto_partition_by_divisors]);

(* Similar results based on count *)

(* Theorem: 0 < n ==> (divisors n = IMAGE (gcd n) (count n)) *)
(* Proof:
     divisors n
   = IMAGE (gcd n) (upto n)                      by divisors_eq_image_gcd_upto
   = IMAGE (gcd n) (n INSERT (count n))          by upto_by_count
   = (gcd n n) INSERT (IMAGE (gcd n) (count n))  by IMAGE_INSERT
   = n INSERT (IMAGE (gcd n) (count n))          by GCD_REF
   = (gcd n 0) INSERT (IMAGE (gcd n) (count n))  by GCD_0R
   = IMAGE (gcd n) (0 INSERT (count n))          by IMAGE_INSERT
   = IMAGE (gcd n) (count n)                     by IN_COUNT, ABSORPTION, 0 < n.
*)
val divisors_eq_image_gcd_count = store_thm(
  "divisors_eq_image_gcd_count",
  ``!n. 0 < n ==> (divisors n = IMAGE (gcd n) (count n))``,
  rpt strip_tac >>
  `divisors n = IMAGE (gcd n) (upto n)` by rw[divisors_eq_image_gcd_upto] >>
  `_ = IMAGE (gcd n) (n INSERT (count n))` by rw[upto_by_count] >>
  `_ = n INSERT (IMAGE (gcd n) (count n))` by rw[GCD_REF] >>
  `_ = (gcd n 0) INSERT (IMAGE (gcd n) (count n))` by rw[GCD_0R] >>
  `_ = IMAGE (gcd n) (0 INSERT (count n))` by rw[] >>
  metis_tac[IN_COUNT, ABSORPTION]);

(* Theorem: (feq (gcd n)) equiv_on (count n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = count n.
*)
val gcd_eq_equiv_on_count = store_thm(
  "gcd_eq_equiv_on_count",
  ``!n. (feq (gcd n)) equiv_on (count n)``,
  rw[feq_equiv]);

(* Theorem: 0 < n ==> (partition (feq (gcd n)) (count n) = IMAGE (preimage (gcd n) (count n)) (divisors n)) *)
(* Proof:
   Let f = gcd n, s = count n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                      by feq_partition_by_preimage
   = IMAGE (preimage f s) (IMAGE f s)                by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (count n))  by expansion
   = IMAGE (preimage f s) (divisors n)               by divisors_eq_image_gcd_count, 0 < n
*)
val gcd_eq_count_partition_by_divisors = store_thm(
  "gcd_eq_count_partition_by_divisors",
  ``!n. 0 < n ==> (partition (feq (gcd n)) (count n) = IMAGE (preimage (gcd n) (count n)) (divisors n))``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = count n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition_by_preimage] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_count, Abbr`f`, Abbr`s`]);

(* Theorem: SIGMA f (count n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n)) *)
(* Proof:
   Let g = gcd n, s = count n.
   Since FINITE s               by FINITE_COUNT
     and (feq g) equiv_on s     by feq_equiv
   The result follows           by set_sigma_by_partition
*)
val sum_over_count_by_gcd_partition = store_thm(
  "sum_over_count_by_gcd_partition",
  ``!f n. SIGMA f (count n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))``,
  rw[feq_equiv, set_sigma_by_partition]);

(* Theorem: 0 < n ==> (SIGMA f (count n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))) *)
(* Proof:
     SIGMA f (count n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))                by sum_over_count_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))  by gcd_eq_count_partition_by_divisors
*)
val sum_over_count_by_divisors = store_thm(
  "sum_over_count_by_divisors",
  ``!f n. 0 < n ==> (SIGMA f (count n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n)))``,
  rw[sum_over_count_by_gcd_partition, gcd_eq_count_partition_by_divisors]);

(* Similar results based on natural *)

(* Theorem: 0 < n ==> (divisors n = IMAGE (gcd n) (natural n)) *)
(* Proof:
     divisors n
   = IMAGE (gcd n) (upto n)                      by divisors_eq_image_gcd_upto
   = IMAGE (gcd n) (0 INSERT natural n)          by upto_by_natural
   = (gcd 0 n) INSERT (IMAGE (gcd n) (natural n))  by IMAGE_INSERT
   = n INSERT (IMAGE (gcd n) (natural n))          by GCD_0L
   = (gcd n n) INSERT (IMAGE (gcd n) (natural n))  by GCD_REF
   = IMAGE (gcd n) (n INSERT (natural n))          by IMAGE_INSERT
   = IMAGE (gcd n) (natural n)                     by natural_has_last, ABSORPTION, 0 < n.
*)
val divisors_eq_image_gcd_natural = store_thm(
  "divisors_eq_image_gcd_natural",
  ``!n. 0 < n ==> (divisors n = IMAGE (gcd n) (natural n))``,
  rpt strip_tac >>
  `divisors n = IMAGE (gcd n) (upto n)` by rw[divisors_eq_image_gcd_upto] >>
  `_ = IMAGE (gcd n) (0 INSERT (natural n))` by rw[upto_by_natural] >>
  `_ = n INSERT (IMAGE (gcd n) (natural n))` by rw[GCD_0L] >>
  `_ = (gcd n n) INSERT (IMAGE (gcd n) (natural n))` by rw[GCD_REF] >>
  `_ = IMAGE (gcd n) (n INSERT (natural n))` by rw[] >>
  metis_tac[natural_has_last, ABSORPTION]);

(* Theorem: 0 < n ==> (partition (feq (gcd n)) (natural n) = IMAGE (preimage (gcd n) (natural n)) (divisors n)) *)
(* Proof:
   Let f = gcd n, s = natural n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                        by feq_partition_by_preimage
   = IMAGE (preimage f s) (IMAGE f s)                  by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (natural n))  by expansion
   = IMAGE (preimage f s) (divisors n)                 by divisors_eq_image_gcd_natural, 0 < n
*)
val gcd_eq_natural_partition_by_divisors = store_thm(
  "gcd_eq_natural_partition_by_divisors",
  ``!n. 0 < n ==> (partition (feq (gcd n)) (natural n) = IMAGE (preimage (gcd n) (natural n)) (divisors n))``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = natural n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition_by_preimage] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_natural, Abbr`f`, Abbr`s`]);

(* Theorem: 0 < n ==> (SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))) *)
(* Proof:
     SIGMA f (natural n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))                by sum_over_natural_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))  by gcd_eq_natural_partition_by_divisors
*)
val sum_over_natural_by_preimage_divisors = store_thm(
  "sum_over_natural_by_preimage_divisors",
  ``!f n. 0 < n ==> (SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n)))``,
  rw[sum_over_natural_by_gcd_partition, gcd_eq_natural_partition_by_divisors]);

(* Theorem: (f 1 = g 1) /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> (f = g) *)
(* Proof:
   By FUN_EQ_THM, this is to show: !x. f x = g x.
   By complete induction on x.
   Let s = divisors x, t = s DELETE x.
   Then x IN s                            by divisors_has_last
    and (s = x INSERT t) /\ x NOTIN t     by INSERT_DELETE, IN_DELETE
   Note FINITE s                          by divisors_finite
     so FINITE t                          by FINITE_DELETE

   Claim: SIGMA f t = SIGMA g t
   Proof: By SUM_IMAGE_CONG, this is to show:
             !z. z IN t ==> (f z = g z)
          But z IN s <=> z <= x /\ z divides x     by divisors_element
           so z IN t <=> z < x /\ z divides x      by IN_DELETE
          ==> f z = g z                            by induction hypothesis

   Now      SIGMA f s = SIGMA g s         by implication
   or f x + SIGMA f t = g x + SIGMA g t   by SUM_IMAGE_INSERT
   or             f x = g x               by SIGMA f t = SIGMA g t
*)
Theorem sum_image_divisors_cong:
  !f g. f 1 = g 1 /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==>
        f = g
Proof
  rw[FUN_EQ_THM] >>
  completeInduct_on `x` >>
  qabbrev_tac `s = divisors x` >>
  qabbrev_tac `t = s DELETE x` >>
  `x IN s` by rw[divisors_has_last, Abbr`s`] >>
  `(s = x INSERT t) /\ x NOTIN t` by rw[Abbr`t`] >>
  `SIGMA f t = SIGMA g t`
    by (irule SUM_IMAGE_CONG >> simp[] >>
        rw[divisors_element, Abbr`t`, Abbr`s`]) >>
  `FINITE t` by rw[divisors_finite, Abbr`t`, Abbr`s`] >>
  `SIGMA f s = f x + SIGMA f t` by simp[SUM_IMAGE_INSERT] >>
  `SIGMA g s = g x + SIGMA g t` by simp[SUM_IMAGE_INSERT] >>
  `SIGMA f s = SIGMA g s` by metis_tac[] >>
  decide_tac
QED
(* But this is not very useful! *)

(* ------------------------------------------------------------------------- *)
(* Mobius Function and Inversion Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   sq_free s          = {n | n IN s /\ square_free n}
   non_sq_free s      = {n | n IN s /\ ~(square_free n)}
   even_sq_free s     = {n | n IN (sq_free s) /\ EVEN (CARD (prime_factors n))}
   odd_sq_free s      = {n | n IN (sq_free s) /\ ODD (CARD (prime_factors n))}
   less_divisors n    = {x | x IN (divisors n) /\ x <> n}
   proper_divisors n  = {x | x IN (divisors n) /\ x <> 1 /\ x <> n}
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Square-free Number and Square-free Sets:
   square_free_def     |- !n. square_free n <=> !p. prime p /\ p divides n ==> ~(p * p divides n)
   square_free_1       |- square_free 1
   square_free_prime   |- !n. prime n ==> square_free n

   sq_free_element     |- !s n. n IN sq_free s <=> n IN s /\ square_free n
   sq_free_subset      |- !s. sq_free s SUBSET s
   sq_free_finite      |- !s. FINITE s ==> FINITE (sq_free s)
   non_sq_free_element |- !s n. n IN non_sq_free s <=> n IN s /\ ~square_free n
   non_sq_free_subset  |- !s. non_sq_free s SUBSET s
   non_sq_free_finite  |- !s. FINITE s ==> FINITE (non_sq_free s)
   sq_free_split       |- !s. (s = sq_free s UNION non_sq_free s) /\
                              (sq_free s INTER non_sq_free s = {})
   sq_free_union       |- !s. s = sq_free s UNION non_sq_free s
   sq_free_inter       |- !s. sq_free s INTER non_sq_free s = {}
   sq_free_disjoint    |- !s. DISJOINT (sq_free s) (non_sq_free s)

   Prime Divisors of a Number and Partitions of Square-free Set:
   prime_factors_def      |- !n. prime_factors n = {p | prime p /\ p IN divisors n}
   prime_factors_element  |- !n p. p IN prime_factors n <=> prime p /\ p <= n /\ p divides n
   prime_factors_subset   |- !n. prime_factors n SUBSET divisors n
   prime_factors_finite   |- !n. FINITE (prime_factors n)

   even_sq_free_element    |- !s n. n IN even_sq_free s <=> n IN s /\ square_free n /\ EVEN (CARD (prime_factors n))
   even_sq_free_subset     |- !s. even_sq_free s SUBSET s
   even_sq_free_finite     |- !s. FINITE s ==> FINITE (even_sq_free s)
   odd_sq_free_element     |- !s n. n IN odd_sq_free s <=> n IN s /\ square_free n /\ ODD (CARD (prime_factors n))
   odd_sq_free_subset      |- !s. odd_sq_free s SUBSET s
   odd_sq_free_finite      |- !s. FINITE s ==> FINITE (odd_sq_free s)
   sq_free_split_even_odd  |- !s. (sq_free s = even_sq_free s UNION odd_sq_free s) /\
                                  (even_sq_free s INTER odd_sq_free s = {})
   sq_free_union_even_odd  |- !s. sq_free s = even_sq_free s UNION odd_sq_free s
   sq_free_inter_even_odd  |- !s. even_sq_free s INTER odd_sq_free s = {}
   sq_free_disjoint_even_odd  |- !s. DISJOINT (even_sq_free s) (odd_sq_free s)

   Less Divisors of a number:
   less_divisors_element       |- !n x. x IN less_divisors n <=> x < n /\ x divides n
   less_divisors_0             |- less_divisors 0 = {}
   less_divisors_1             |- less_divisors 1 = {}
   less_divisors_subset_divisors   |- !n. less_divisors n SUBSET divisors n
   less_divisors_finite        |- !n. FINITE (less_divisors n)
   less_divisors_prime         |- !n. prime n ==> (less_divisors n = {1})
   less_divisors_has_one       |- !n. 1 < n ==> 1 IN less_divisors n
   less_divisors_nonzero       |- !n x. x IN less_divisors n ==> 0 < x
   less_divisors_has_cofactor  |- !n. 0 < n ==>
                                  !d. 1 < d /\ d IN less_divisors n ==> n DIV d IN less_divisors n

   Proper Divisors of a number:
   proper_divisors_element     |- !n x. x IN proper_divisors n <=> 1 < x /\ x < n /\ x divides n
   proper_divisors_0           |- proper_divisors 0 = {}
   proper_divisors_1           |- proper_divisors 1 = {}
   proper_divisors_subset      |- !n. proper_divisors n SUBSET less_divisors n
   proper_divisors_finite      |- !n. FINITE (proper_divisors n)
   proper_divisors_not_one     |- !n. 1 NOTIN proper_divisors n
   proper_divisors_by_less_divisors   |- !n. proper_divisors n = less_divisors n DELETE 1
   proper_divisors_prime       |- !n. prime n ==> (proper_divisors n = {})
   proper_divisors_has_cofactor   |- !n d. d IN proper_divisors n ==> n DIV d IN proper_divisors n
   proper_divisors_min_gt_1    |- !n. proper_divisors n <> {} ==> 1 < MIN_SET (proper_divisors n)
   proper_divisors_max_min     |- !n. proper_divisors n <> {} ==>
                                      (MAX_SET (proper_divisors n) = n DIV MIN_SET (proper_divisors n)) /\
                                      (MIN_SET (proper_divisors n) = n DIV MAX_SET (proper_divisors n))

   Useful Properties of Less Divisors:
   less_divisors_min             |- !n. 1 < n ==> (MIN_SET (less_divisors n) = 1)
   less_divisors_max             |- !n. MAX_SET (less_divisors n) <= n DIV 2
   less_divisors_subset_natural  |- !n. less_divisors n SUBSET natural (n DIV 2)

   Properties of Summation equals Perfect Power:
   perfect_power_special_inequality  |- !p. 1 < p ==> !n. p * (p ** n - 1) < (p - 1) * (2 * p ** n)
   perfect_power_half_inequality_1   |- !p n. 1 < p /\ 0 < n ==> 2 * p ** (n DIV 2) <= p ** n
   perfect_power_half_inequality_2   |- !p n. 1 < p /\ 0 < n ==>
                                        (p ** (n DIV 2) - 2) * p ** (n DIV 2) <= p ** n - 2 * p ** (n DIV 2)
   sigma_eq_perfect_power_bounds_1   |- !p. 1 < p ==>
                          !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
                              (!n. 0 < n ==> n * f n <= p ** n) /\
                               !n. 0 < n ==> p ** n - 2 * p ** (n DIV 2) < n * f n
   sigma_eq_perfect_power_bounds_2   |- !p. 1 < p ==>
                          !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
                              (!n. 0 < n ==> n * f n <= p ** n) /\
                               !n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * f n

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Mobius Function and Inversion                                             *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Square-free Number and Square-free Sets                                   *)
(* ------------------------------------------------------------------------- *)

(* Define square-free number *)
val square_free_def = Define`
    square_free n = !p. prime p /\ p divides n ==> ~(p * p divides n)
`;

(* Theorem: square_free 1 *)
(* Proof:
       square_free 1
   <=> !p. prime p /\ p divides 1 ==> ~(p * p divides 1)    by square_free_def
   <=> prime 1 ==> ~(1 * 1 divides 1)                       by DIVIDES_ONE
   <=> F ==> ~(1 * 1 divides 1)                             by NOT_PRIME_1
   <=> T                                                    by false assumption
*)
val square_free_1 = store_thm(
  "square_free_1",
  ``square_free 1``,
  rw[square_free_def]);

(* Theorem: prime n ==> square_free n *)
(* Proof:
       square_free n
   <=> !p. prime p /\ p divides n ==> ~(p * p divides n)   by square_free_def
   By contradiction, suppose (p * p divides n).
   Since p divides n ==> (p = n) \/ (p = 1)                by prime_def
     and p * p divides  ==> (p * p = n) \/ (p * p = 1)     by prime_def
     but p <> 1                                            by prime_def
      so p * p <> 1              by MULT_EQ_1
    Thus p * p = n = p,
      or p = 0 \/ p = 1          by SQ_EQ_SELF
     But p <> 0                  by NOT_PRIME_0
     and p <> 1                  by NOT_PRIME_1
    Thus there is a contradiction.
*)
val square_free_prime = store_thm(
  "square_free_prime",
  ``!n. prime n ==> square_free n``,
  rw_tac std_ss[square_free_def] >>
  spose_not_then strip_assume_tac >>
  `p * p = p` by metis_tac[prime_def, MULT_EQ_1] >>
  metis_tac[SQ_EQ_SELF, NOT_PRIME_0, NOT_PRIME_1]);

(* Overload square-free filter of a set *)
val _ = overload_on("sq_free", ``\s. {n | n IN s /\ square_free n}``);

(* Overload non-square-free filter of a set *)
val _ = overload_on("non_sq_free", ``\s. {n | n IN s /\ ~(square_free n)}``);

(* Theorem: n IN sq_free s <=> n IN s /\ square_free n *)
(* Proof: by notation. *)
val sq_free_element = store_thm(
  "sq_free_element",
  ``!s n. n IN sq_free s <=> n IN s /\ square_free n``,
  rw[]);

(* Theorem: sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val sq_free_subset = store_thm(
  "sq_free_subset",
  ``!s. sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (sq_free s) *)
(* Proof: by sq_free_subset, SUBSET_FINITE *)
val sq_free_finite = store_thm(
  "sq_free_finite",
  ``!s. FINITE s ==> FINITE (sq_free s)``,
  metis_tac[sq_free_subset, SUBSET_FINITE]);

(* Theorem: n IN non_sq_free s <=> n IN s /\ ~(square_free n) *)
(* Proof: by notation. *)
val non_sq_free_element = store_thm(
  "non_sq_free_element",
  ``!s n. n IN non_sq_free s <=> n IN s /\ ~(square_free n)``,
  rw[]);

(* Theorem: non_sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val non_sq_free_subset = store_thm(
  "non_sq_free_subset",
  ``!s. non_sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (non_sq_free s) *)
(* Proof: by non_sq_free_subset, SUBSET_FINITE *)
val non_sq_free_finite = store_thm(
  "non_sq_free_finite",
  ``!s. FINITE s ==> FINITE (non_sq_free s)``,
  metis_tac[non_sq_free_subset, SUBSET_FINITE]);

(* Theorem: (s = (sq_free s) UNION (non_sq_free s)) /\ ((sq_free s) INTER (non_sq_free s) = {}) *)
(* Proof:
   This is to show:
   (1) s = (sq_free s) UNION (non_sq_free s)
       True by EXTENSION, IN_UNION.
   (2) (sq_free s) INTER (non_sq_free s) = {}
       True by EXTENSION, IN_INTER
*)
val sq_free_split = store_thm(
  "sq_free_split",
  ``!s. (s = (sq_free s) UNION (non_sq_free s)) /\ ((sq_free s) INTER (non_sq_free s) = {})``,
  (rw[EXTENSION] >> metis_tac[]));

(* Theorem: s = (sq_free s) UNION (non_sq_free s) *)
(* Proof: extract from sq_free_split. *)
val sq_free_union = save_thm("sq_free_union", sq_free_split |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL);
(* val sq_free_union = |- !s. s = sq_free s UNION non_sq_free s: thm *)

(* Theorem: (sq_free s) INTER (non_sq_free s) = {} *)
(* Proof: extract from sq_free_split. *)
val sq_free_inter = save_thm("sq_free_inter", sq_free_split |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL);
(* val sq_free_inter = |- !s. sq_free s INTER non_sq_free s = {}: thm *)

(* Theorem: DISJOINT (sq_free s) (non_sq_free s) *)
(* Proof: by DISJOINT_DEF, sq_free_inter. *)
val sq_free_disjoint = store_thm(
  "sq_free_disjoint",
  ``!s. DISJOINT (sq_free s) (non_sq_free s)``,
  rw_tac std_ss[DISJOINT_DEF, sq_free_inter]);

(* ------------------------------------------------------------------------- *)
(* Prime Divisors of a Number and Partitions of Square-free Set              *)
(* ------------------------------------------------------------------------- *)

(* Define the prime divisors of a number *)
val prime_factors_def = Define`
    prime_factors n = {p | prime p /\ p IN (divisors n)}
`;
(* prime_divisors is used in triangle.hol *)

(* Theorem: p IN prime_factors n <=> prime p /\ p <= n /\ p divides n *)
(* Proof: by prime_factors_def, divisors_def *)
val prime_factors_element = store_thm(
  "prime_factors_element",
  ``!n p. p IN prime_factors n <=> prime p /\ p <= n /\ p divides n``,
  rw[prime_factors_def, divisors_def]);

(* Theorem: (prime_factors n) SUBSET (divisors n) *)
(* Proof:
       p IN (prime_factors n)
   ==> p IN (divisors n)              by prime_factors_def
   Hence (prime_factors n) SUBSET (divisors n)   by SUBSET_DEF
*)
val prime_factors_subset = store_thm(
  "prime_factors_subset",
  ``!n. (prime_factors n) SUBSET (divisors n)``,
  rw[prime_factors_def, SUBSET_DEF]);

(* Theorem: FINITE (prime_factors n) *)
(* Proof:
   Since (prime_factors n) SUBSET (divisors n)    by prime_factors_subset
     and FINITE (divisors n)           by divisors_finite
    Thus FINITE (prime_factors n)                 by SUBSET_FINITE
*)
val prime_factors_finite = store_thm(
  "prime_factors_finite",
  ``!n. FINITE (prime_factors n)``,
  metis_tac[prime_factors_subset, divisors_finite, SUBSET_FINITE]);

(* Overload even square-free filter of a set *)
val _ = overload_on("even_sq_free", ``\s. {n | n IN (sq_free s) /\ EVEN (CARD (prime_factors n))}``);

(* Overload odd square-free filter of a set *)
val _ = overload_on("odd_sq_free", ``\s. {n | n IN (sq_free s) /\ ODD (CARD (prime_factors n))}``);

(* Theorem: n IN even_sq_free s <=> n IN s /\ square_free n /\ EVEN (CARD (prime_factors n)) *)
(* Proof: by notation. *)
val even_sq_free_element = store_thm(
  "even_sq_free_element",
  ``!s n. n IN even_sq_free s <=> n IN s /\ square_free n /\ EVEN (CARD (prime_factors n))``,
  (rw[] >> metis_tac[]));

(* Theorem: even_sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val even_sq_free_subset = store_thm(
  "even_sq_free_subset",
  ``!s. even_sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (even_sq_free s) *)
(* Proof: by even_sq_free_subset, SUBSET_FINITE *)
val even_sq_free_finite = store_thm(
  "even_sq_free_finite",
  ``!s. FINITE s ==> FINITE (even_sq_free s)``,
  metis_tac[even_sq_free_subset, SUBSET_FINITE]);

(* Theorem: n IN odd_sq_free s <=> n IN s /\ square_free n /\ ODD (CARD (prime_factors n)) *)
(* Proof: by notation. *)
val odd_sq_free_element = store_thm(
  "odd_sq_free_element",
  ``!s n. n IN odd_sq_free s <=> n IN s /\ square_free n /\ ODD (CARD (prime_factors n))``,
  (rw[] >> metis_tac[]));

(* Theorem: odd_sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val odd_sq_free_subset = store_thm(
  "odd_sq_free_subset",
  ``!s. odd_sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (odd_sq_free s) *)
(* Proof: by odd_sq_free_subset, SUBSET_FINITE *)
val odd_sq_free_finite = store_thm(
  "odd_sq_free_finite",
  ``!s. FINITE s ==> FINITE (odd_sq_free s)``,
  metis_tac[odd_sq_free_subset, SUBSET_FINITE]);

(* Theorem: (sq_free s = (even_sq_free s) UNION (odd_sq_free s)) /\
            ((even_sq_free s) INTER (odd_sq_free s) = {}) *)
(* Proof:
   This is to show:
   (1) sq_free s = even_sq_free s UNION odd_sq_free s
       True by EXTENSION, IN_UNION, EVEN_ODD.
   (2) even_sq_free s INTER odd_sq_free s = {}
       True by EXTENSION, IN_INTER, EVEN_ODD.
*)
val sq_free_split_even_odd = store_thm(
  "sq_free_split_even_odd",
  ``!s. (sq_free s = (even_sq_free s) UNION (odd_sq_free s)) /\
       ((even_sq_free s) INTER (odd_sq_free s) = {})``,
  (rw[EXTENSION] >> metis_tac[EVEN_ODD]));

(* Theorem: sq_free s = (even_sq_free s) UNION (odd_sq_free s) *)
(* Proof: extract from sq_free_split_even_odd. *)
val sq_free_union_even_odd =
    save_thm("sq_free_union_even_odd", sq_free_split_even_odd |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL);
(* val sq_free_union_even_odd =
   |- !s. sq_free s = even_sq_free s UNION odd_sq_free s: thm *)

(* Theorem: (even_sq_free s) INTER (odd_sq_free s) = {} *)
(* Proof: extract from sq_free_split_even_odd. *)
val sq_free_inter_even_odd =
    save_thm("sq_free_inter_even_odd", sq_free_split_even_odd |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL);
(* val sq_free_inter_even_odd =
   |- !s. even_sq_free s INTER odd_sq_free s = {}: thm *)

(* Theorem: DISJOINT (even_sq_free s) (odd_sq_free s) *)
(* Proof: by DISJOINT_DEF, sq_free_inter_even_odd. *)
val sq_free_disjoint_even_odd = store_thm(
  "sq_free_disjoint_even_odd",
  ``!s. DISJOINT (even_sq_free s) (odd_sq_free s)``,
  rw_tac std_ss[DISJOINT_DEF, sq_free_inter_even_odd]);

(* ------------------------------------------------------------------------- *)
(* Less Divisors of a number.                                                *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of divisors less than n *)
val _ = overload_on("less_divisors", ``\n. {x | x IN (divisors n) /\ x <> n}``);

(* Theorem: x IN (less_divisors n) <=> (x < n /\ x divides n) *)
(* Proof: by divisors_element. *)
val less_divisors_element = store_thm(
  "less_divisors_element",
  ``!n x. x IN (less_divisors n) <=> (x < n /\ x divides n)``,
  rw[divisors_element, EQ_IMP_THM]);

(* Theorem: less_divisors 0 = {} *)
(* Proof: by divisors_element. *)
val less_divisors_0 = store_thm(
  "less_divisors_0",
  ``less_divisors 0 = {}``,
  rw[divisors_element]);

(* Theorem: less_divisors 1 = {} *)
(* Proof: by divisors_element. *)
val less_divisors_1 = store_thm(
  "less_divisors_1",
  ``less_divisors 1 = {}``,
  rw[divisors_element]);

(* Theorem: (less_divisors n) SUBSET (divisors n) *)
(* Proof: by SUBSET_DEF *)
val less_divisors_subset_divisors = store_thm(
  "less_divisors_subset_divisors",
  ``!n. (less_divisors n) SUBSET (divisors n)``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE (less_divisors n) *)
(* Proof:
   Since (less_divisors n) SUBSET (divisors n)   by less_divisors_subset_divisors
     and FINITE (divisors n)                     by divisors_finite
      so FINITE (proper_divisors n)              by SUBSET_FINITE
*)
val less_divisors_finite = store_thm(
  "less_divisors_finite",
  ``!n. FINITE (less_divisors n)``,
  metis_tac[divisors_finite, less_divisors_subset_divisors, SUBSET_FINITE]);

(* Theorem: prime n ==> (less_divisors n = {1}) *)
(* Proof:
   Since prime n
     ==> !b. b divides n ==> (b = n) \/ (b = 1)   by prime_def
   But (less_divisors n) excludes n               by less_divisors_element
   and 1 < n                                      by ONE_LT_PRIME
   Hence less_divisors n = {1}
*)
val less_divisors_prime = store_thm(
  "less_divisors_prime",
  ``!n. prime n ==> (less_divisors n = {1})``,
  rpt strip_tac >>
  `!b. b divides n ==> (b = n) \/ (b = 1)` by metis_tac[prime_def] >>
  rw[less_divisors_element, EXTENSION, EQ_IMP_THM] >| [
    `x <> n` by decide_tac >>
    metis_tac[],
    rw[ONE_LT_PRIME]
  ]);

(* Theorem: 1 < n ==> 1 IN (less_divisors n) *)
(* Proof:
       1 IN (less_divisors n)
   <=> 1 < n /\ 1 divides n     by less_divisors_element
   <=> T                        by ONE_DIVIDES_ALL
*)
val less_divisors_has_one = store_thm(
  "less_divisors_has_one",
  ``!n. 1 < n ==> 1 IN (less_divisors n)``,
  rw[less_divisors_element]);

(* Theorem: x IN (less_divisors n) ==> 0 < x *)
(* Proof:
   Since x IN (less_divisors n),
         x < n /\ x divides n                 by less_divisors_element
   By contradiction, if x = 0, then n = 0     by ZERO_DIVIDES
   This contradicts x < n.
*)
val less_divisors_nonzero = store_thm(
  "less_divisors_nonzero",
  ``!n x. x IN (less_divisors n) ==> 0 < x``,
  metis_tac[less_divisors_element, ZERO_DIVIDES, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n ==> !d. 1 < d /\ d IN (less_divisors n) ==> (n DIV d) IN (less_divisors n) *)
(* Proof:
      d IN (less_divisors n)
  ==> d IN (divisors n)                   by notation
  ==> (n DIV d) IN (divisors n)           by divisors_has_cofactor
   Also n DIV d < n                       by DIV_LESS, 0 < n /\ 1 < d
   thus n DIV d <> n                      by LESS_NOT_EQ
  Hence (n DIV d) IN (less_divisors n)    by notation
*)
val less_divisors_has_cofactor = store_thm(
  "less_divisors_has_cofactor",
  ``!n. 0 < n ==> !d. 1 < d /\ d IN (less_divisors n) ==> (n DIV d) IN (less_divisors n)``,
  rw[divisors_has_cofactor, DIV_LESS, LESS_NOT_EQ]);

(* ------------------------------------------------------------------------- *)
(* Proper Divisors of a number.                                              *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of proper divisors of n *)
val _ = overload_on("proper_divisors", ``\n. {x | x IN (divisors n) /\ x <> 1 /\ x <> n}``);

(* Theorem: x IN (proper_divisors n) <=> (1 < x /\ x < n /\ x divides n) *)
(* Proof:
   Since x IN (divisors n)
     ==> x <= n /\ x divides n       by divisors_element
   Since x <= n but x <> n, x < n.
   If x = 0, x divides n ==> n = 0   by ZERO_DIVIDES
   But x <> n, so x <> 0.
   With x <> 0 /\ x <> 1 ==> 1 < x.
*)
val proper_divisors_element = store_thm(
  "proper_divisors_element",
  ``!n x. x IN (proper_divisors n) <=> (1 < x /\ x < n /\ x divides n)``,
  rw[divisors_element, EQ_IMP_THM] >>
  `x <> 0` by metis_tac[ZERO_DIVIDES] >>
  decide_tac);

(* Theorem: proper_divisors 0 = {} *)
(* Proof: by proper_divisors_element. *)
val proper_divisors_0 = store_thm(
  "proper_divisors_0",
  ``proper_divisors 0 = {}``,
  rw[proper_divisors_element, EXTENSION]);

(* Theorem: proper_divisors 1 = {} *)
(* Proof: by proper_divisors_element. *)
val proper_divisors_1 = store_thm(
  "proper_divisors_1",
  ``proper_divisors 1 = {}``,
  rw[proper_divisors_element, EXTENSION]);

(* Theorem: (proper_divisors n) SUBSET (less_divisors n) *)
(* Proof: by SUBSET_DEF *)
val proper_divisors_subset = store_thm(
  "proper_divisors_subset",
  ``!n. (proper_divisors n) SUBSET (less_divisors n)``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE (proper_divisors n) *)
(* Proof:
   Since (proper_divisors n) SUBSET (less_divisors n) by proper_divisors_subset
     and FINITE (less_divisors n)                     by less_divisors_finite
      so FINITE (proper_divisors n)                   by SUBSET_FINITE
*)
val proper_divisors_finite = store_thm(
  "proper_divisors_finite",
  ``!n. FINITE (proper_divisors n)``,
  metis_tac[less_divisors_finite, proper_divisors_subset, SUBSET_FINITE]);

(* Theorem: 1 NOTIN (proper_divisors n) *)
(* Proof: proper_divisors_element *)
val proper_divisors_not_one = store_thm(
  "proper_divisors_not_one",
  ``!n. 1 NOTIN (proper_divisors n)``,
  rw[proper_divisors_element]);

(* Theorem: proper_divisors n = (less_divisors n) DELETE 1 *)
(* Proof:
      proper_divisors n
    = {x | x IN (divisors n) /\ x <> 1 /\ x <> n}   by notation
    = {x | x IN (divisors n) /\ x <> n} DELETE 1    by IN_DELETE
    = (less_divisors n) DELETE 1
*)
val proper_divisors_by_less_divisors = store_thm(
  "proper_divisors_by_less_divisors",
  ``!n. proper_divisors n = (less_divisors n) DELETE 1``,
  rw[divisors_element, EXTENSION, EQ_IMP_THM]);

(* Theorem: prime n ==> (proper_divisors n = {}) *)
(* Proof:
      proper_divisors n
    = (less_divisors n) DELETE 1  by proper_divisors_by_less_divisors
    = {1} DELETE 1                by less_divisors_prime, prime n
    = {}                          by SING_DELETE
*)
val proper_divisors_prime = store_thm(
  "proper_divisors_prime",
  ``!n. prime n ==> (proper_divisors n = {})``,
  rw[proper_divisors_by_less_divisors, less_divisors_prime]);

(* Theorem: d IN (proper_divisors n) ==> (n DIV d) IN (proper_divisors n) *)
(* Proof:
   Let e = n DIV d.
   Since d IN (proper_divisors n)
     ==> 1 < d /\ d < n                   by proper_divisors_element
     and d IN (less_divisors n)           by proper_divisors_subset
      so e IN (less_divisors n)           by less_divisors_has_cofactor
     and 0 < e                            by less_divisors_nonzero
   Since d divides n                      by less_divisors_element
      so n = e * d                        by DIV_MULT_EQ, 0 < d
    thus e <> 1 since n <> d              by MULT_LEFT_1
    With 0 < e /\ e <> 1
     ==> e IN (proper_divisors n)         by proper_divisors_by_less_divisors, IN_DELETE
*)
val proper_divisors_has_cofactor = store_thm(
  "proper_divisors_has_cofactor",
  ``!n d. d IN (proper_divisors n) ==> (n DIV d) IN (proper_divisors n)``,
  rpt strip_tac >>
  qabbrev_tac `e = n DIV d` >>
  `1 < d /\ d < n` by metis_tac[proper_divisors_element] >>
  `d IN (less_divisors n)` by metis_tac[proper_divisors_subset, SUBSET_DEF] >>
  `e IN (less_divisors n)` by rw[less_divisors_has_cofactor, Abbr`e`] >>
  `0 < e` by metis_tac[less_divisors_nonzero] >>
  `0 < d /\ n <> d` by decide_tac >>
  `e <> 1` by metis_tac[less_divisors_element, DIV_MULT_EQ, MULT_LEFT_1] >>
  metis_tac[proper_divisors_by_less_divisors, IN_DELETE]);

(* Theorem: (proper_divisors n) <> {} ==> 1 < MIN_SET (proper_divisors n) *)
(* Proof:
   Let s = proper_divisors n.
   Since !x. x IN s ==> 1 < x        by proper_divisors_element
     But MIN_SET s IN s              by MIN_SET_IN_SET
   Hence 1 < MIN_SET s               by above
*)
val proper_divisors_min_gt_1 = store_thm(
  "proper_divisors_min_gt_1",
  ``!n. (proper_divisors n) <> {} ==> 1 < MIN_SET (proper_divisors n)``,
  metis_tac[MIN_SET_IN_SET, proper_divisors_element]);

(* Theorem: (proper_divisors n) <> {} ==>
            (MAX_SET (proper_divisors n) = n DIV (MIN_SET (proper_divisors n))) /\
            (MIN_SET (proper_divisors n) = n DIV (MAX_SET (proper_divisors n)))     *)
(* Proof:
   Let s = proper_divisors n, b = MIN_SET s.
   By MAX_SET_ELIM, this is to show:
   (1) FINITE s, true                     by proper_divisors_finite
   (2) s <> {} /\ x IN s /\ !y. y IN s ==> y <= x ==> x = n DIV b /\ b = n DIV x
       Note s <> {} ==> n <> 0            by proper_divisors_0
        Let m = n DIV b.
       Note n DIV x IN s                  by proper_divisors_has_cofactor, 0 < n, 1 < b.
       Also b IN s /\ b <= x              by MIN_SET_IN_SET, s <> {}
       thus 1 < b                         by proper_divisors_min_gt_1
         so m IN s                        by proper_divisors_has_cofactor, 0 < n, 1 < x.
         or 1 < m                         by proper_divisors_nonzero
        and m <= x                        by implication, x = MAX_SET s.
       Thus n DIV x <= n DIV m            by DIV_LE_MONOTONE_REVERSE [1], 0 < x, 0 < m.
        But n DIV m
          = n DIV (n DIV b) = b           by divide_by_cofactor, b divides n.
         so n DIV x <= b                  by [1]
      Since b <= n DIV x                  by MIN_SET_PROPERTY, b = MIN_SET s, n DIV x IN s.
         so n DIV x = b                   by LESS_EQUAL_ANTISYM (gives second subgoal)
      Hence m = n DIV b
              = n DIV (n DIV x) = x       by divide_by_cofactor, x divides n (gives first subgoal)
*)
val proper_divisors_max_min = store_thm(
  "proper_divisors_max_min",
  ``!n. (proper_divisors n) <> {} ==>
       (MAX_SET (proper_divisors n) = n DIV (MIN_SET (proper_divisors n))) /\
       (MIN_SET (proper_divisors n) = n DIV (MAX_SET (proper_divisors n)))``,
  ntac 2 strip_tac >>
  qabbrev_tac `s = proper_divisors n` >>
  qabbrev_tac `b = MIN_SET s` >>
  DEEP_INTRO_TAC MAX_SET_ELIM >>
  strip_tac >-
  rw[proper_divisors_finite, Abbr`s`] >>
  ntac 3 strip_tac >>
  `n <> 0` by metis_tac[proper_divisors_0] >>
  `b IN s /\ b <= x` by rw[MIN_SET_IN_SET, Abbr`b`] >>
  `1 < b` by rw[proper_divisors_min_gt_1, Abbr`s`, Abbr`b`] >>
  `0 < n /\ 1 < x` by decide_tac >>
  qabbrev_tac `m = n DIV b` >>
  `m IN s /\ (n DIV x) IN s` by rw[proper_divisors_has_cofactor, Abbr`m`, Abbr`s`] >>
  `1 < m` by metis_tac[proper_divisors_element] >>
  `0 < x /\ 0 < m` by decide_tac >>
  `n DIV x <= n DIV m` by rw[DIV_LE_MONOTONE_REVERSE] >>
  `b divides n /\ x divides n` by metis_tac[proper_divisors_element] >>
  `n DIV m = b` by rw[divide_by_cofactor, Abbr`m`] >>
  `b <= n DIV x` by rw[MIN_SET_PROPERTY, Abbr`b`] >>
  `b = n DIV x` by rw[LESS_EQUAL_ANTISYM] >>
  `m = x` by rw[divide_by_cofactor, Abbr`m`] >>
  decide_tac);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Useful Properties of Less Divisors                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < n ==> (MIN_SET (less_divisors n) = 1) *)
(* Proof:
   Let s = less_divisors n.
   Since 1 < n ==> 1 IN s         by less_divisors_has_one
      so s <> {}                  by MEMBER_NOT_EMPTY
     and !y. y IN s ==> 0 < y     by less_divisors_nonzero
      or !y. y IN s ==> 1 <= y    by LESS_EQ
   Hence 1 = MIN_SET s            by MIN_SET_TEST
*)
val less_divisors_min = store_thm(
  "less_divisors_min",
  ``!n. 1 < n ==> (MIN_SET (less_divisors n) = 1)``,
  metis_tac[less_divisors_has_one, MEMBER_NOT_EMPTY,
             MIN_SET_TEST, less_divisors_nonzero, LESS_EQ, ONE]);

(* Theorem: MAX_SET (less_divisors n) <= n DIV 2 *)
(* Proof:
   Let s = less_divisors n, m = MAX_SET s.
   If s = {},
      Then m = MAX_SET {} = 0          by MAX_SET_EMPTY
       and 0 <= n DIV 2 is trivial.
   If s <> {},
      Then n <> 0 /\ n <> 1            by less_divisors_0, less_divisors_1
   Note 1 IN s                         by less_divisors_has_one
   Consider t = s DELETE 1.
   Then t = proper_divisors n          by proper_divisors_by_less_divisors
   If t = {},
      Then s = {1}                     by DELETE_EQ_SING
       and m = 1                       by SING_DEF, IN_SING (same as MAX_SET_SING)
     Since 2 <= n                      by 1 < n
      thus n DIV n <= n DIV 2          by DIV_LE_MONOTONE_REVERSE
        or n DIV n = 1 = m <= n DIV 2  by DIVMOD_ID, 0 < n
   If t <> {},
      Let b = MIN_SET t
      Then MAX_SET t = n DIV b         by proper_divisors_max_min, t <> {}
     Since MIN_SET s = 1               by less_divisors_min, 1 < n
       and FINITE s                    by less_divisors_finite
       and s <> {1}                    by DELETE_EQ_SING
      thus m = MAX_SET t               by MAX_SET_DELETE, s <> {1}

       Now 1 < b                       by proper_divisors_min_gt_1
        so 2 <= b                      by LESS_EQ, 1 < b
     Hence n DIV b <= n DIV 2          by DIV_LE_MONOTONE_REVERSE
       or        m <= n DIV 2          by m = MAX_SET t = n DIV b
*)

Theorem less_divisors_max:
  !n. MAX_SET (less_divisors n) <= n DIV 2
Proof
  rpt strip_tac >>
  qabbrev_tac `s = less_divisors n` >>
  qabbrev_tac `m = MAX_SET s` >>
  Cases_on `s = {}` >- rw[MAX_SET_EMPTY, Abbr`m`] >>
  `n <> 0 /\ n <> 1` by metis_tac[less_divisors_0, less_divisors_1] >>
  `1 < n` by decide_tac >>
  `1 IN s` by rw[less_divisors_has_one, Abbr`s`] >>
  qabbrev_tac `t = proper_divisors n` >>
  `t = s DELETE 1`  by rw[proper_divisors_by_less_divisors, Abbr`t`, Abbr`s`] >>
  Cases_on `t = {}` >| [
    `s = {1}` by rfs[] >>
    `m = 1` by rw[MAX_SET_SING, Abbr`m`] >>
    `(2 <= n) /\ (0 < 2) /\ (0 < n) /\ (n DIV n = 1)` by rw[] >>
    metis_tac[DIV_LE_MONOTONE_REVERSE],
    qabbrev_tac `b = MIN_SET t` >>
    `MAX_SET t = n DIV b` by metis_tac[proper_divisors_max_min] >>
    `MIN_SET s = 1` by rw[less_divisors_min, Abbr`s`] >>
    `FINITE s` by rw[less_divisors_finite, Abbr`s`] >>
    `s <> {1}` by metis_tac[DELETE_EQ_SING] >>
    `m = MAX_SET t` by metis_tac[MAX_SET_DELETE] >>
    `1 < b` by rw[proper_divisors_min_gt_1, Abbr`b`, Abbr`t`] >>
    `2 <= b /\ (0 < b) /\ (0 < 2)` by decide_tac >>
    `n DIV b <= n DIV 2` by rw[DIV_LE_MONOTONE_REVERSE] >>
    decide_tac
  ]
QED

(* Theorem: (less_divisors n) SUBSET (natural (n DIV 2)) *)
(* Proof:
   Let s = less_divisors n
   If n = 0 or n - 1,
   Then s = {}                        by less_divisors_0, less_divisors_1
    and {} SUBSET t, for any t.       by EMPTY_SUBSET
   If n <> 0 and n <> 1, 1 < n.
   Note FINITE s                      by less_divisors_finite
    and x IN s ==> x <= MAX_SET s     by MAX_SET_PROPERTY, FINITE s
    But MAX_SET s <= n DIV 2          by less_divisors_max
   Thus x IN s ==> x <= n DIV 2       by LESS_EQ_TRANS
   Note s <> {}                       by MEMBER_NOT_EMPTY, x IN s
    and x IN s ==> MIN_SET s <= x     by MIN_SET_PROPERTY, s <> {}
  Since 1 = MIN_SET s, 1 <= x         by less_divisors_min, 1 < n
   Thus 0 < x <= n DIV 2              by LESS_EQ
     or x IN (natural (n DIV 2))      by natural_element
*)
val less_divisors_subset_natural = store_thm(
  "less_divisors_subset_natural",
  ``!n. (less_divisors n) SUBSET (natural (n DIV 2))``,
  rpt strip_tac >>
  qabbrev_tac `s = less_divisors n` >>
  qabbrev_tac `m = n DIV 2` >>
  Cases_on `(n = 0) \/ (n = 1)` >-
  metis_tac[less_divisors_0, less_divisors_1, EMPTY_SUBSET] >>
  `1 < n` by decide_tac >>
  rw_tac std_ss[SUBSET_DEF] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `FINITE s` by rw[less_divisors_finite, Abbr`s`] >>
  `x <= MAX_SET s` by rw[MAX_SET_PROPERTY] >>
  `MIN_SET s <= x` by rw[MIN_SET_PROPERTY] >>
  `MAX_SET s <= m` by rw[less_divisors_max, Abbr`s`, Abbr`m`] >>
  `MIN_SET s = 1` by rw[less_divisors_min, Abbr`s`] >>
  `0 < x /\ x <= m` by decide_tac >>
  rw[natural_element]);

(* ------------------------------------------------------------------------- *)
(* Properties of Summation equals Perfect Power                              *)
(* ------------------------------------------------------------------------- *)

(* Idea for the theorem below (for m = n DIV 2 when applied in bounds):
      p * (p ** m - 1) / (p - 1)
   <  p * p ** m / (p - 1)        discard subtraction
   <= p * p ** m / (p / 2)        replace by smaller denominator
    = 2 * p ** m                  double division and cancel p
   or p * (p ** m - 1) < (p - 1) * 2 * p ** m
*)

(* Theorem: 1 < p ==> !n. p * (p ** n - 1) < (p - 1) * (2 * p ** n) *)
(* Proof:
   Let q = p ** n
   Then 1 <= q                       by ONE_LE_EXP, 0 < p
     so p <= p * q                   by LE_MULT_LCANCEL, p <> 0
   Also 1 < p ==> 2 <= p             by LESS_EQ
     so 2 * q <= p * q               by LE_MULT_RCANCEL, q <> 0
   Thus   LHS
        = p * (q - 1)
        = p * q - p                  by LEFT_SUB_DISTRIB
    And   RHS
        = (p - 1) * (2 * q)
        = p * (2 * q) - 2 * q        by RIGHT_SUB_DISTRIB
        = 2 * (p * q) - 2 * q        by MULT_ASSOC, MULT_COMM
        = (p * q + p * q) - 2 * q    by TIMES2
        = (p * q - p + p + p * q) - 2 * q  by SUB_ADD, p <= p * q
        = LHS + p + p * q - 2 * q    by above
        = LHS + p + (p * q - 2 * q)  by LESS_EQ_ADD_SUB, 2 * q <= p * q
        = LHS + p + (p - 2) * q      by RIGHT_SUB_DISTRIB

    Since 0 < p                      by 1 < p
      and 0 <= (p - 2) * q           by 2 <= p
    Hence LHS < RHS                  by discarding positive terms
*)
val perfect_power_special_inequality = store_thm(
  "perfect_power_special_inequality",
  ``!p. 1 < p ==> !n. p * (p ** n - 1) < (p - 1) * (2 * p ** n)``,
  rpt strip_tac >>
  qabbrev_tac `q = p ** n` >>
  `p <> 0 /\ 2 <= p` by decide_tac >>
  `1 <= q` by rw[ONE_LE_EXP, Abbr`q`] >>
  `p <= p * q` by rw[] >>
  `2 * q <= p * q` by rw[] >>
  qabbrev_tac `l = p * (q - 1)` >>
  qabbrev_tac `r = (p - 1) * (2 * q)` >>
  `l = p * q - p` by rw[Abbr`l`] >>
  `r = p * (2 * q) - 2 * q` by rw[Abbr`r`] >>
  `_ = 2 * (p * q) - 2 * q` by rw[] >>
  `_ = (p * q + p * q) - 2 * q` by rw[] >>
  `_ = (p * q - p + p + p * q) - 2 * q` by rw[] >>
  `_ = l + p + p * q - 2 * q` by rw[] >>
  `_ = l + p + (p * q - 2 * q)` by rw[] >>
  `_ = l + p + (p - 2) * q` by rw[] >>
  decide_tac);

(* Theorem: 1 < p /\ 1 < n ==>
            p ** (n DIV 2) * p ** (n DIV 2) <= p ** n /\
            2 * p ** (n DIV 2) <= p ** (n DIV 2) * p ** (n DIV 2) *)
(* Proof:
   Let m = n DIV 2, q = p ** m.
   The goal becomes: q * q <= p ** n /\ 2 * q <= q * q.
      Note 1 < p ==> 0 < p.
   First goal: q * q <= p ** n
      Then 0 < q                    by EXP_POS, 0 < p
       and 2 * m <= n               by DIV_MULT_LE, 0 < 2.
      thus p ** (2 * m) <= p ** n   by EXP_BASE_LE_MONO, 1 < p.
     Since p ** (2 * m)
         = p ** (m + m)             by TIMES2
         = q * q                    by EXP_ADD
      Thus q * q <= p ** n          by above

   Second goal: 2 * q <= q * q
     Since 1 < n, so 2 <= n         by LESS_EQ
        so 2 DIV 2 <= n DIV 2       by DIV_LE_MONOTONE, 0 < 2.
        or 1 <= m, i.e. 0 < m       by DIVMOD_ID, 0 < 2.
      Thus 1 < q                    by ONE_LT_EXP, 1 < p, 0 < m.
        so 2 <= q                   by LESS_EQ
       and 2 * q <= q * q           by MULT_RIGHT_CANCEL, q <> 0.
     Hence 2 * q <= p ** n          by LESS_EQ_TRANS
*)
val perfect_power_half_inequality_lemma = prove(
  ``!p n. 1 < p /\ 1 < n ==>
         p ** (n DIV 2) * p ** (n DIV 2) <= p ** n /\
         2 * p ** (n DIV 2) <= p ** (n DIV 2) * p ** (n DIV 2)``,
  ntac 3 strip_tac >>
  qabbrev_tac `m = n DIV 2` >>
  qabbrev_tac `q = p ** m` >>
  strip_tac >| [
    `0 < p /\ 0 < 2` by decide_tac >>
    `0 < q /\ q <> 0` by rw[EXP_POS, Abbr`q`] >>
    `2 * m <= n` by metis_tac[DIV_MULT_LE, MULT_COMM] >>
    `p ** (2 * m) <= p ** n` by rw[EXP_BASE_LE_MONO] >>
    `p ** (2 * m) = p ** (m + m)` by rw[] >>
    `_ = q * q` by rw[EXP_ADD, Abbr`q`] >>
    decide_tac,
    `2 <= n /\ 0 < 2` by decide_tac >>
    `1 <= m` by metis_tac[DIV_LE_MONOTONE, DIVMOD_ID] >>
    `0 < m` by decide_tac >>
    `1 < q` by rw[ONE_LT_EXP, Abbr`q`] >>
    rw[]
  ]);

(* Theorem: 1 < p /\ 0 < n ==> 2 * p ** (n DIV 2) <= p ** n *)
(* Proof:
   Let m = n DIV 2, q = p ** m.
   The goal becomes: 2 * q <= p ** n
   If n = 1,
      Then m = 0                    by ONE_DIV, 0 < 2.
       and q = 1                    by EXP
       and p ** n = p               by EXP_1
     Since 1 < p ==> 2 <= p         by LESS_EQ
     Hence 2 * q <= p = p ** n      by MULT_RIGHT_1
   If n <> 1, 1 < n.
      Then q * q <= p ** n /\
           2 * q <= q * q           by perfect_power_half_inequality_lemma
     Hence 2 * q <= p ** n          by LESS_EQ_TRANS
*)
val perfect_power_half_inequality_1 = store_thm(
  "perfect_power_half_inequality_1",
  ``!p n. 1 < p /\ 0 < n ==> 2 * p ** (n DIV 2) <= p ** n``,
  rpt strip_tac >>
  qabbrev_tac `m = n DIV 2` >>
  qabbrev_tac `q = p ** m` >>
  Cases_on `n = 1` >| [
    `m = 0` by rw[Abbr`m`] >>
    `(q = 1) /\ (p ** n = p)` by rw[Abbr`q`] >>
    `2 <= p` by decide_tac >>
    rw[],
    `1 < n` by decide_tac >>
    `q * q <= p ** n /\ 2 * q <= q * q` by rw[perfect_power_half_inequality_lemma, Abbr`q`, Abbr`m`] >>
    decide_tac
  ]);

(* Theorem: 1 < p /\ 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) <= p ** n - 2 * p ** (n DIV 2) *)
(* Proof:
   Let m = n DIV 2, q = p ** m.
   The goal becomes: (q - 2) * q <= p ** n - 2 * q
   If n = 1,
      Then m = 0                    by ONE_DIV, 0 < 2.
       and q = 1                    by EXP
       and p ** n = p               by EXP_1
     Since 1 < p ==> 2 <= p         by LESS_EQ
        or 0 <= p - 2               by SUB_LEFT_LESS_EQ
     Hence (q - 2) * q = 0 <= p - 2
   If n <> 1, 1 < n.
      Then q * q <= p ** n /\ 2 * q <= q * q   by perfect_power_half_inequality_lemma
      Thus q * q - 2 * q <= p ** n - 2 * q     by LE_SUB_RCANCEL, 2 * q <= q * q
        or   (q - 2) * q <= p ** n - 2 * q     by RIGHT_SUB_DISTRIB
*)
val perfect_power_half_inequality_2 = store_thm(
  "perfect_power_half_inequality_2",
  ``!p n. 1 < p /\ 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) <= p ** n - 2 * p ** (n DIV 2)``,
  rpt strip_tac >>
  qabbrev_tac `m = n DIV 2` >>
  qabbrev_tac `q = p ** m` >>
  Cases_on `n = 1` >| [
    `m = 0` by rw[Abbr`m`] >>
    `(q = 1) /\ (p ** n = p)` by rw[Abbr`q`] >>
    `0 <= p - 2 /\ (1 - 2 = 0)` by decide_tac >>
    rw[],
    `1 < n` by decide_tac >>
    `q * q <= p ** n /\ 2 * q <= q * q` by rw[perfect_power_half_inequality_lemma, Abbr`q`, Abbr`m`] >>
    decide_tac
  ]);

(* Already in pred_setTheory:
SUM_IMAGE_SUBSET_LE;
!f s t. FINITE s /\ t SUBSET s ==> SIGMA f t <= SIGMA f s: thm
SUM_IMAGE_MONO_LESS_EQ;
|- !s. FINITE s ==> (!x. x IN s ==> f x <= g x) ==> SIGMA f s <= SIGMA g s: thm
*)

(* Theorem: 1 < p ==> !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
            (!n. 0 < n ==> n * (f n) <= p ** n) /\
            (!n. 0 < n ==> p ** n - 2 * p ** (n DIV 2) < n * (f n)) *)
(* Proof:
   Step 1: prove a specific lemma for sum decomposition
   Claim: !n. 0 < n ==> (divisors n DIFF {n}) SUBSET (natural (n DIV 2)) /\
          (p ** n = SIGMA (\d. d * f d) (divisors n)) ==>
          (p ** n = n * f n + SIGMA (\d. d * f d) (divisors n DIFF {n}))
   Proof: Let s = divisors n, a = {n}, b = s DIFF a, m = n DIV 2.
          Then b = less_divisors n        by EXTENSION,IN_DIFF
           and b SUBSET (natural m)       by less_divisors_subset_natural
          This gives the first part.
          For the second part:
          Note a SUBSET s                 by divisors_has_last, SUBSET_DEF
           and b SUBSET s                 by DIFF_SUBSET
          Thus s = b UNION a              by UNION_DIFF, a SUBSET s
           and DISJOINT b a               by DISJOINT_DEF, EXTENSION
           Now FINITE s                   by divisors_finite
            so FINITE a /\ FINITE b       by SUBSET_FINITE, by a SUBSEt s /\ b SUBSET s

               p ** n
             = SIGMA (\d. d * f d) s              by implication
             = SIGMA (\d. d * f d) (b UNION a)    by above, s = b UNION a
             = SIGMA (\d. d * f d) b + SIGMA (\d. d * f d) a   by SUM_IMAGE_DISJOINT, FINITE a /\ FINITE b
             = SIGMA (\d. d * f d) b + n * f n    by SUM_IMAGE_SING
             = n * f n + SIGMA (\d. d * f d) b    by ADD_COMM
          This gives the second part.

   Step 2: Upper bound, to show: !n. 0 < n ==> n * f n <= p ** n
           Let b = divisors n DIFF {n}
           Since n * f n + SIGMA (\d. d * f d) b = p ** n    by lemma
           Hence n * f n <= p ** n                           by 0 <= SIGMA (\d. d * f d) b

   Step 3: Lower bound, to show: !n. 0 < n ==> p ** n - p ** (n DIV 2) <= n * f n
           Let s = divisors n, a = {n}, b = s DIFF a, m = n DIV 2.
            Note b SUBSET (natural m) /\
                 (p ** n = n * f n + SIGMA (\d. d * f d) b)  by lemma
           Since FINITE (natural m)                          by natural_finite
            thus SIGMA (\d. d * f d) b
              <= SIGMA (\d. d * f d) (natural m)             by SUM_IMAGE_SUBSET_LE [1]
            Also !d. d IN (natural m) ==> 0 < d              by natural_element
             and !d. 0 < d ==> d * f d <= p ** d             by upper bound (Step 2)
            thus !d. d IN (natural m) ==> d * f d <= p ** d  by implication
           Hence SIGMA (\d. d * f d) (natural m)
              <= SIGMA (\d. p ** d) (natural m)              by SUM_IMAGE_MONO_LESS_EQ [2]
             Now 1 < p ==> 0 < p /\ (p - 1) <> 0             by arithmetic

             (p - 1) * SIGMA (\d. d * f d) b
          <= (p - 1) * SIGMA (\d. d * f d) (natural m)       by LE_MULT_LCANCEL, [1]
          <= (p - 1) * SIGMA (\d. p ** d) (natural m)        by LE_MULT_LCANCEL, [2]
           = p * (p ** m - 1)                                by sigma_geometric_natural_eqn
           < (p - 1) * (2 * p ** m)                          by perfect_power_special_inequality

             (p - 1) * SIGMA (\d. d * f d) b < (p - 1) * (2 * p ** m)   by LESS_EQ_LESS_TRANS
             or        SIGMA (\d. d * f d) b < 2 * p ** m               by LT_MULT_LCANCEL, (p - 1) <> 0

            But 2 * p ** m <= p ** n                         by perfect_power_half_inequality_1, 1 < p, 0 < n
           Thus p ** n = p ** n - 2 * p ** m + 2 * p ** m    by SUB_ADD, 2 * p ** m <= p ** n
       Combinig with lemma,
           p ** n - 2 * p ** m + 2 * p ** m < n * f n + 2 * p ** m
             or         p ** n - 2 * p ** m < n * f n        by LESS_MONO_ADD_EQ, no condition
*)
Theorem sigma_eq_perfect_power_bounds_1:
  !p.
    1 < p ==>
    !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
        (!n. 0 < n ==> n * (f n) <= p ** n) /\
        (!n. 0 < n ==> p ** n - 2 * p ** (n DIV 2) < n * (f n))
Proof
  ntac 4 strip_tac >>
  ‘∀n. 0 < n ==>
       (divisors n DIFF {n}) SUBSET (natural (n DIV 2)) /\
       (p ** n = SIGMA (\d. d * f d) (divisors n) ==>
        p ** n = n * f n + SIGMA (\d. d * f d) (divisors n DIFF {n}))’
    by (ntac 2 strip_tac >>
        qabbrev_tac `s = divisors n` >>
        qabbrev_tac `a = {n}` >>
        qabbrev_tac `b = s DIFF a` >>
        qabbrev_tac `m = n DIV 2` >>
        `b = less_divisors n` by rw[EXTENSION, Abbr`b`, Abbr`a`, Abbr`s`] >>
        `b SUBSET (natural m)` by metis_tac[less_divisors_subset_natural] >>
        strip_tac >- rw[] >>
        `a SUBSET s` by rw[divisors_has_last, SUBSET_DEF, Abbr`s`, Abbr`a`] >>
        `b SUBSET s` by rw[Abbr`b`] >>
        `s = b UNION a` by rw[UNION_DIFF, Abbr`b`] >>
        `DISJOINT b a`
          by (rw[DISJOINT_DEF, Abbr`b`, EXTENSION] >> metis_tac[]) >>
        `FINITE s` by rw[divisors_finite, Abbr`s`] >>
        `FINITE a /\ FINITE b` by metis_tac[SUBSET_FINITE] >>
        strip_tac >>
        `_ = SIGMA (\d. d * f d) (b UNION a)` by metis_tac[Abbr`s`] >>
        `_ = SIGMA (\d. d * f d) b + SIGMA (\d. d * f d) a`
          by rw[SUM_IMAGE_DISJOINT] >>
        `_ = SIGMA (\d. d * f d) b + n * f n` by rw[SUM_IMAGE_SING, Abbr`a`] >>
        rw[]) >>
  conj_asm1_tac >| [
    rpt strip_tac >>
    `p ** n = n * f n + SIGMA (\d. d * f d) (divisors n DIFF {n})` by rw[] >>
    decide_tac,
    rpt strip_tac >>
    qabbrev_tac `s = divisors n` >>
    qabbrev_tac `a = {n}` >>
    qabbrev_tac `b = s DIFF a` >>
    qabbrev_tac `m = n DIV 2` >>
    `b SUBSET (natural m) /\ (p ** n = n * f n + SIGMA (\d. d * f d) b)`
      by rw[Abbr`s`, Abbr`a`, Abbr`b`, Abbr`m`] >>
    `FINITE (natural m)` by rw[natural_finite] >>
    `SIGMA (\d. d * f d) b <= SIGMA (\d. d * f d) (natural m)`
      by rw[SUM_IMAGE_SUBSET_LE] >>
    `!d. d IN (natural m) ==> 0 < d` by rw[natural_element] >>
    `SIGMA (\d. d * f d) (natural m) <= SIGMA (\d. p ** d) (natural m)`
      by rw[SUM_IMAGE_MONO_LESS_EQ] >>
    `0 < p /\ (p - 1) <> 0` by decide_tac >>
    `(p - 1) * SIGMA (\d. p ** d) (natural m) = p * (p ** m - 1)`
      by rw[sigma_geometric_natural_eqn] >>
    `p * (p ** m - 1) < (p - 1) * (2 * p ** m)`
      by rw[perfect_power_special_inequality] >>
    `SIGMA (\d. d * f d) b < 2 * p ** m`
      by metis_tac[LE_MULT_LCANCEL, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS,
                   LT_MULT_LCANCEL] >>
    `p ** n < n * f n + 2 * p ** m` by decide_tac >>
    `2 * p ** m <= p ** n` by rw[perfect_power_half_inequality_1, Abbr`m`] >>
    decide_tac
  ]
QED

(* Theorem: 1 < p ==> !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
            (!n. 0 < n ==> n * (f n) <= p ** n) /\
            (!n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n)) *)
(* Proof:
   For the first goal: (!n. 0 < n ==> n * (f n) <= p ** n)
       True by sigma_eq_perfect_power_bounds_1.
   For the second goal: (!n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n))
       Let m = n DIV 2.
       Then p ** n - 2 * p ** m < n * (f n)                     by sigma_eq_perfect_power_bounds_1
        and (p ** m - 2) * p ** m <= p ** n - 2 * p ** m        by perfect_power_half_inequality_2
      Hence (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n)   by LESS_EQ_LESS_TRANS
*)
val sigma_eq_perfect_power_bounds_2 = store_thm(
  "sigma_eq_perfect_power_bounds_2",
  ``!p. 1 < p ==> !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
   (!n. 0 < n ==> n * (f n) <= p ** n) /\
   (!n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n))``,
  rpt strip_tac >-
  rw[sigma_eq_perfect_power_bounds_1] >>
  qabbrev_tac `m = n DIV 2` >>
  `p ** n - 2 * p ** m < n * (f n)` by rw[sigma_eq_perfect_power_bounds_1, Abbr`m`] >>
  `(p ** m - 2) * p ** m <= p ** n - 2 * p ** m` by rw[perfect_power_half_inequality_2, Abbr`m`] >>
  decide_tac);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Binomial scripts in HOL:
C:\jc\www\ml\hol\info\Hol\examples\miller\RSA\summationScript.sml
C:\jc\www\ml\hol\info\Hol\examples\miller\RSA\powerScript.sml
C:\jc\www\ml\hol\info\Hol\examples\miller\RSA\binomialScript.sml
*)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Binomial Documentation                                                    *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Binomial Coefficients:
   binomial_def        |- (binomial 0 0 = 1) /\ (!n. binomial (SUC n) 0 = 1) /\
                          (!k. binomial 0 (SUC k) = 0) /\
                          !n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)
   binomial_alt        |- !n k. binomial n 0 = 1 /\ binomial 0 (k + 1) = 0 /\
                                binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1)
   binomial_less_0     |- !n k. n < k ==> (binomial n k = 0)
   binomial_n_0        |- !n. binomial n 0 = 1
   binomial_n_n        |- !n. binomial n n = 1
   binomial_0_n        |- !n. binomial 0 n = if n = 0 then 1 else 0
   binomial_recurrence |- !n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)
   binomial_formula    |- !n k. binomial (n + k) k * (FACT n * FACT k) = FACT (n + k)
   binomial_formula2   |- !n k. k <= n ==> (FACT n = binomial n k * (FACT (n - k) * FACT k))
   binomial_formula3   |- !n k. k <= n ==> (binomial n k = FACT n DIV (FACT k * FACT (n - k)))
   binomial_fact       |- !n k. k <= n ==> (binomial n k = FACT n DIV (FACT k * FACT (n - k)))
   binomial_n_k        |- !n k. k <= n ==> (binomial n k = FACT n DIV FACT k DIV FACT (n - k)
   binomial_n_1        |- !n. binomial n 1 = n
   binomial_sym        |- !n k. k <= n ==> (binomial n k = binomial n (n - k))
   binomial_is_integer |- !n k. k <= n ==> (FACT k * FACT (n - k)) divides (FACT n)
   binomial_pos        |- !n k. k <= n ==> 0 < binomial n k
   binomial_eq_0       |- !n k. (binomial n k = 0) <=> n < k
   binomial_up_eqn     |- !n. 0 < n ==> !k. n * binomial (n - 1) k = (n - k) * binomial n k
   binomial_up         |- !n. 0 < n ==> !k. binomial (n - 1) k = (n - k) * binomial n k DIV n
   binomial_right_eqn  |- !n. 0 < n ==> !k. (k + 1) * binomial n (k + 1) = (n - k) * binomial n k
   binomial_right      |- !n. 0 < n ==> !k. binomial n (k + 1) = (n - k) * binomial n k DIV (k + 1)
   binomial_monotone   |- !n k. k < HALF n ==> binomial n k < binomial n (k + 1)
   binomial_max        |- !n k. binomial n k <= binomial n (HALF n)

   Primes and Binomial Coefficients:
   prime_divides_binomials     |- !n.  prime n ==> 1 < n /\ !k. 0 < k /\ k < n ==> n divides (binomial n k)
   prime_divides_binomials_alt |- !n k. prime n /\ 0 < k /\ k < n ==> n divides binomial n k
   prime_divisor_property      |- !n p. 1 < n /\ p < n /\ prime p /\ p divides n ==> ~(p divides (FACT (n - 1) DIV FACT (n - p)))
   divides_binomials_imp_prime |- !n. 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k)) ==> prime n
   prime_iff_divides_binomials |- !n. prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> n divides (binomial n k)
   prime_iff_divides_binomials_alt
                               |- !n. prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> binomial n k MOD n = 0

   Binomial Theorem:
   GENLIST_binomial_index_shift |- !n x y. GENLIST ((\k. binomial n k * x ** SUC (n - k) * y ** k) o SUC) n =
                                           GENLIST (\k. binomial n (SUC k) * x ** (n - k) * y ** SUC k) n
   binomial_index_shift   |- !n x y. (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) o SUC =
                                     (\k. binomial (SUC n) (SUC k) * x ** (n - k) * y ** SUC k)
   binomial_term_merge_x  |- !n x y. (\k. x * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
                                     (\k. binomial n k * x ** SUC (n - k) * y ** k)
   binomial_term_merge_y  |- !n x y. (\k. y * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
                                     (\k. binomial n k * x ** (n - k) * y ** SUC k)
   binomial_thm     |- !n x y. (x + y) ** n = SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n))
   binomial_thm_alt |- !n x y. (x + y) ** n = SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (n + 1))
   binomial_sum     |- !n. SUM (GENLIST (binomial n) (SUC n)) = 2 ** n
   binomial_sum_alt |- !n. SUM (GENLIST (binomial n) (n + 1)) = 2 ** n

   Binomial Horizontal List:
   binomial_horizontal_0        |- binomial_horizontal 0 = [1]
   binomial_horizontal_len      |- !n. LENGTH (binomial_horizontal n) = n + 1
   binomial_horizontal_mem      |- !n k. k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n)
   binomial_horizontal_mem_iff  |- !n k. MEM (binomial n k) (binomial_horizontal n) <=> k <= n
   binomial_horizontal_member   |- !n x. MEM x (binomial_horizontal n) <=> ?k. k <= n /\ (x = binomial n k)
   binomial_horizontal_element  |- !n k. k <= n ==> (EL k (binomial_horizontal n) = binomial n k)
   binomial_horizontal_pos      |- !n. EVERY (\x. 0 < x) (binomial_horizontal n)
   binomial_horizontal_pos_alt  |- !n x. MEM x (binomial_horizontal n) ==> 0 < x
   binomial_horizontal_sum      |- !n. SUM (binomial_horizontal n) = 2 ** n
   binomial_horizontal_max      |- !n. MAX_LIST (binomial_horizontal n) = binomial n (HALF n)
   binomial_row_max             |- !n. MAX_SET (IMAGE (binomial n) (count (n + 1))) = binomial n (HALF n)
   binomial_product_identity    |- !m n k. k <= m /\ m <= n ==>
                          (binomial m k * binomial n m = binomial n k * binomial (n - k) (m - k))
   binomial_middle_upper_bound  |- !n. binomial n (HALF n) <= 4 ** HALF n

   Stirling's Approximation:
   Stirling = (!n. FACT n = (SQRT (2 * pi * n)) * (n DIV e) ** n) /\
              (!n. SQRT n = n ** h) /\ (2 * h = 1) /\ (0 < pi) /\ (0 < e) /\
              (!a b x y. (a * b) DIV (x * y) = (a DIV x) * (b DIV y)) /\
              (!a b c. (a DIV c) DIV (b DIV c) = a DIV b)
   binomial_middle_by_stirling  |- Stirling ==>
               !n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = 2 ** (n + 1) DIV SQRT (2 * pi * n))

   Useful theorems for Binomial:
   binomial_range_shift  |- !n . 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
                                            (!h. h < PRE n ==> ((binomial n (SUC h)) MOD n = 0)))
   binomial_mod_zero     |- !n. 0 < n ==> !k. (binomial n k MOD n = 0) <=>
                                          (!x y. (binomial n k * x ** (n-k) * y ** k) MOD n = 0)
   binomial_range_shift_alt   |- !n . 0 < n ==> ((!k. 0 < k /\ k < n ==>
            (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0))) <=>
            (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))))
   binomial_mod_zero_alt  |- !n. 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
            !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0)

   Binomial Theorem with prime exponent:
   binomial_thm_prime  |- !p. prime p ==> (!x y. (x + y) ** p MOD p = (x ** p + y ** p) MOD p)
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Binomial Coefficients                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define Binomials:
   C(n,0) = 1
   C(0,k) = 0 if k > 0
   C(n+1,k+1) = C(n,k) + C(n,k+1)
*)
val binomial_def = Define`
    (binomial 0 0 = 1) /\
    (binomial (SUC n) 0 = 1) /\
    (binomial 0 (SUC k) = 0)  /\
    (binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k))
`;

(* Theorem: alternative definition of C(n,k). *)
(* Proof: by binomial_def. *)
Theorem binomial_alt:
  !n k. (binomial n 0 = 1) /\
         (binomial 0 (k + 1) = 0) /\
         (binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1))
Proof
  rewrite_tac[binomial_def, GSYM ADD1] >>
  (Cases_on `n` >> simp[binomial_def])
QED

(* Basic properties *)

(* Theorem: C(n,k) = 0 if n < k *)
(* Proof:
   By induction on n.
   Base case: C(0,k) = 0 if 0 < k, by definition.
   Step case: assume C(n,k) = 0 if n < k.
   then for SUC n < k,
        C(SUC n, k)
      = C(SUC n, SUC h)   where k = SUC h
      = C(n,h) + C(n,SUC h)  h < SUC h = k
      = 0 + 0             by induction hypothesis
      = 0
*)
val binomial_less_0 = store_thm(
  "binomial_less_0",
  ``!n k. n < k ==> (binomial n k = 0)``,
  Induct_on `n` >-
  metis_tac[binomial_def, num_CASES, NOT_ZERO_LT_ZERO] >>
  rw[binomial_def] >>
  `?h. k = SUC h` by metis_tac[SUC_NOT, NOT_ZERO_LT_ZERO, LESS_EQ_SUC, LESS_TRANS] >>
  metis_tac[binomial_def, LESS_MONO_EQ, LESS_TRANS, LESS_SUC, ADD_0]);

(* Theorem: C(n,0) = 1 *)
(* Proof:
   If n = 0, C(n, 0) = C(0, 0) = 1            by binomial_def
   If n <> 0, n = SUC m, and C(SUC m, 0) = 1  by binomial_def
*)
val binomial_n_0 = store_thm(
  "binomial_n_0",
  ``!n. binomial n 0 = 1``,
  metis_tac[binomial_def, num_CASES]);

(* Theorem: C(n,n) = 1 *)
(* Proof:
   By induction on n.
   Base case: C(0,0) = 1,  true by binomial_def.
   Step case: assume C(n,n) = 1
     C(SUC n, SUC n)
   = C(n,n) + C(n,SUC n)
   = 1 + C(n,SUC n)      by induction hypothesis
   = 1 + 0               by binomial_less_0
   = 1
*)
val binomial_n_n = store_thm(
  "binomial_n_n",
  ``!n. binomial n n = 1``,
  Induct_on `n` >-
  metis_tac[binomial_def] >>
  metis_tac[binomial_def, LESS_SUC, binomial_less_0, ADD_0]);

(* Theorem: binomial 0 n = if n = 0 then 1 else 0 *)
(* Proof:
   If n = 0,
      binomial 0 0 = 1     by binomial_n_0
   If n <> 0, then 0 < n.
      binomial 0 n = 0     by binomial_less_0
*)
val binomial_0_n = store_thm(
  "binomial_0_n",
  ``!n. binomial 0 n = if n = 0 then 1 else 0``,
  rw[binomial_n_0, binomial_less_0]);

(* Theorem: C(n+1,k+1) = C(n,k) + C(n,k+1) *)
(* Proof: by definition. *)
val binomial_recurrence = store_thm(
  "binomial_recurrence",
  ``!n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)``,
  rw[binomial_def]);

(* Theorem: C(n+k,k) = (n+k)!/n!k!  *)
(* Proof:
   By induction on k.
   Base case: C(n,0) = n!n! = 1   by binomial_n_0
   Step case: assume C(n+k,k) = (n+k)!/n!k!
   To prove C(n+SUC k, SUC k) = (n+SUC k)!/n!(SUC k)!
      By induction on n.
      Base case: C(SUC k, SUC k) = (SUC k)!/(SUC k)! = 1   by binomial_n_n
      Step case: assume C(n+SUC k, SUC k) = (n +SUC k)!/n!(SUC k)!
      To prove C(SUC n + SUC k, SUC k) = (SUC n + SUC k)!/(SUC n)!(SUC k)!
        C(SUC n + SUC k, SUC k)
      = C(SUC SUC (n+k), SUC k)
      = C(SUC (n+k),k) + C(SUC (n+k), SUC k)
      = C(SUC n + k, k) + C(n + SUC k, SUC k)
      = (SUC n + k)!/(SUC n)!k! + (n + SUC k)!/n!(SUC k)!   by two induction hypothesis
      = ((SUC n + k)!(SUC k) + (n + SUC k)(SUC n))/(SUC n)!(SUC k)!
      = (SUC n + SUC k)!/(SUC n)!(SUC k)!
*)
val binomial_formula = store_thm(
  "binomial_formula",
  ``!n k. binomial (n+k) k * (FACT n * FACT k) = FACT (n+k)``,
  Induct_on `k` >-
  metis_tac[binomial_n_0, FACT, MULT_CLAUSES, ADD_0] >>
  Induct_on `n` >-
  metis_tac[binomial_n_n, FACT, MULT_CLAUSES, ADD_CLAUSES] >>
  `SUC n + SUC k = SUC (SUC (n+k))` by decide_tac >>
  `SUC (n + k) = SUC n + k` by decide_tac >>
  `binomial (SUC n + SUC k) (SUC k) * (FACT (SUC n) * FACT (SUC k)) =
    (binomial (SUC (n + k)) k +
     binomial (SUC (n + k)) (SUC k)) * (FACT (SUC n) * FACT (SUC k))`
    by metis_tac[binomial_recurrence] >>
  `_ = binomial (SUC (n + k)) k * (FACT (SUC n) * FACT (SUC k)) +
        binomial (SUC (n + k)) (SUC k) * (FACT (SUC n) * FACT (SUC k))`
        by metis_tac[RIGHT_ADD_DISTRIB] >>
  `_ = binomial (SUC n + k) k * (FACT (SUC n) * ((SUC k) * FACT k)) +
        binomial (n + SUC k) (SUC k) * ((SUC n) * FACT n * FACT (SUC k))`
        by metis_tac[ADD_COMM, SUC_ADD_SYM, FACT] >>
  `_ = binomial (SUC n + k) k * FACT (SUC n) * FACT k * (SUC k) +
        binomial (n + SUC k) (SUC k) * FACT n * FACT (SUC k) * (SUC n)`
        by metis_tac[MULT_COMM, MULT_ASSOC] >>
  `_ = FACT (SUC n + k) * SUC k + FACT (n + SUC k) * SUC n`
        by metis_tac[MULT_COMM, MULT_ASSOC] >>
  `_ = FACT (SUC (n+k)) * SUC k + FACT (SUC (n+k)) * SUC n`
        by metis_tac[ADD_COMM, SUC_ADD_SYM] >>
  `_ = FACT (SUC (n+k)) * (SUC k + SUC n)` by metis_tac[LEFT_ADD_DISTRIB] >>
  `_ = (SUC n + SUC k) * FACT (SUC (n+k))` by metis_tac[MULT_COMM, ADD_COMM] >>
  metis_tac[FACT]);

(* Theorem: C(n,k) = n!/k!(n-k)!  for 0 <= k <= n *)
(* Proof:
     FACT n
   = FACT ((n-k)+k)                                 by SUB_ADD, k <= n.
   = binomial ((n-k)+k) k * (FACT (n-k) * FACT k)   by binomial_formula
   = binomial n k * (FACT (n-k) * FACT k))          by SUB_ADD, k <= n.
*)
val binomial_formula2 = store_thm(
  "binomial_formula2",
  ``!n k. k <= n ==> (FACT n = binomial n k * (FACT (n-k) * FACT k))``,
  metis_tac[binomial_formula, SUB_ADD]);

(* Theorem: k <= n ==> binomial n k = (FACT n) DIV ((FACT k) * (FACT (n - k))) *)
(* Proof:
    binomial n k
  = (binomial n k * (FACT (n - k) * FACT k)) DIV ((FACT (n - k) * FACT k))  by MULT_DIV
  = (FACT n) DIV ((FACT (n - k) * FACT k))      by binomial_formula2
  = (FACT n) DIV ((FACT k * FACT (n - k)))      by MULT_COMM
*)
val binomial_formula3 = store_thm(
  "binomial_formula3",
  ``!n k. k <= n ==> (binomial n k = (FACT n) DIV ((FACT k) * (FACT (n - k))))``,
  metis_tac[binomial_formula2, MULT_COMM, MULT_DIV, MULT_EQ_0, FACT_LESS, NOT_ZERO_LT_ZERO]);

(* Theorem alias. *)
val binomial_fact = save_thm("binomial_fact", binomial_formula3);
(* val binomial_fact = |- !n k. k <= n ==> (binomial n k = FACT n DIV (FACT k * FACT (n - k))): thm *)

(* Theorem: k <= n ==> binomial n k = (FACT n) DIV (FACT k) DIV (FACT (n - k)) *)
(* Proof:
    binomial n k
  = (FACT n) DIV ((FACT k * FACT (n - k)))      by binomial_formula3
  = (FACT n) DIV (FACT k) DIV (FACT (n - k))    by DIV_DIV_DIV_MULT
*)
val binomial_n_k = store_thm(
  "binomial_n_k",
  ``!n k. k <= n ==> (binomial n k = (FACT n) DIV (FACT k) DIV (FACT (n - k)))``,
  metis_tac[DIV_DIV_DIV_MULT, binomial_formula3, MULT_EQ_0, FACT_LESS, NOT_ZERO_LT_ZERO]);

(* Theorem: binomial n 1 = n *)
(* Proof:
   If n = 0,
        binomial 0 1
      = if 1 = 0 then 1 else 0                by binomial_0_n
      = 0                                     by 1 = 0 = F
   If n <> 0, then 0 < n.
      Thus 1 <= n, and n = SUC (n-1)          by 0 < n
        binomial n 1
      = FACT n DIV FACT 1 DIV FACT (n - 1)    by binomial_n_k, 1 <= n
      = FACT n DIV 1 DIV (FACT (n-1))         by FACT, ONE
      = FACT n DIV (FACT (n-1))               by DIV_1
      = (n * FACT (n-1)) DIV (FACT (n-1))     by FACT
      = n                                     by MULT_DIV, FACT_LESS
*)
val binomial_n_1 = store_thm(
  "binomial_n_1",
  ``!n. binomial n 1 = n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[binomial_0_n] >>
  `1 <= n /\ (n = SUC (n-1))` by decide_tac >>
  `binomial n 1 = FACT n DIV FACT 1 DIV FACT (n - 1)` by rw[binomial_n_k] >>
  `_ = FACT n DIV 1 DIV (FACT (n-1))` by EVAL_TAC >>
  `_ = FACT n DIV (FACT (n-1))` by rw[] >>
  `_ = (n * FACT (n-1)) DIV (FACT (n-1))` by metis_tac[FACT] >>
  `_ = n` by rw[MULT_DIV, FACT_LESS] >>
  rw[]);

(* Theorem: k <= n ==> (binomial n k = binomial n (n-k)) *)
(* Proof:
   Note (n-k) <= n always.
     binomial n k
   = (FACT n) DIV (FACT k * FACT (n - k))           by binomial_formula3, k <= n.
   = (FACT n) DIV (FACT (n - k) * FACT k)           by MULT_COMM
   = (FACT n) DIV (FACT (n - k) * FACT (n-(n-k)))   by n - (n-k) = k
   = binomial n (n-k)                               by binomial_formula3, (n-k) <= n.
*)
val binomial_sym = store_thm(
  "binomial_sym",
  ``!n k. k <= n ==> (binomial n k = binomial n (n-k))``,
  rpt strip_tac >>
  `n - (n-k) = k` by decide_tac >>
  `(n-k) <= n` by decide_tac >>
  rw[binomial_formula3, MULT_COMM]);

(* Theorem: k <= n ==> (FACT k * FACT (n-k)) divides (FACT n) *)
(* Proof:
   Since FACT n = binomial n k * (FACT (n - k) * FACT k)   by binomial_formula2
                = binomial n k * (FACT k * FACT (n - k))   by MULT_COMM
   Hence (FACT k * FACT (n-k)) divides (FACT n)            by divides_def
*)
val binomial_is_integer = store_thm(
  "binomial_is_integer",
  ``!n k. k <= n ==> (FACT k * FACT (n-k)) divides (FACT n)``,
  metis_tac[binomial_formula2, MULT_COMM, divides_def]);

(* Theorem: k <= n ==> 0 < binomial n k *)
(* Proof:
   Since  FACT n = binomial n k * (FACT (n - k) * FACT k)  by binomial_formula2
     and  0 < FACT n, 0 < FACT (n-k), 0 < FACT k           by FACT_LESS
   Hence  0 < binomial n k                                 by ZERO_LESS_MULT
*)
val binomial_pos = store_thm(
  "binomial_pos",
  ``!n k. k <= n ==> 0 < binomial n k``,
  metis_tac[binomial_formula2, FACT_LESS, ZERO_LESS_MULT]);

(* Theorem: (binomial n k = 0) <=> n < k *)
(* Proof:
   If part: (binomial n k = 0) ==> n < k
      By contradiction, suppose k <= n.
      Then 0 < binomial n k                by binomial_pos
      This contradicts binomial n k = 0    by NOT_ZERO_LT_ZERO
   Only-if part: n < k ==> (binomial n k = 0)
      This is true                         by binomial_less_0
*)
val binomial_eq_0 = store_thm(
  "binomial_eq_0",
  ``!n k. (binomial n k = 0) <=> n < k``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `k <= n` by decide_tac >>
    metis_tac[binomial_pos, NOT_ZERO_LT_ZERO],
    rw[binomial_less_0]
  ]);

(* Relating Binomial to its up-entry:

   binomial n k = (n, k, n-k) = n! / k! (n-k)!
   binomial (n-1) k = (n-1, k, n-1-k) = (n-1)! / k! (n-1-k)!
                    = (n!/n) / k! ((n-k)!/(n-k))
                    = (n-k) * binomial n k / n
*)

(* Theorem: 0 < n ==> !k. n * binomial (n-1) k = (n-k) * (binomial n k) *)
(* Proof:
   If n <= k, that is n-1 < k.
      So   binomial (n-1) k = 0      by binomial_less_0
      and  n - k = 0                 by arithmetic
      Hence true                     by MULT_EQ_0
   Otherwise k < n,
      or k <= n, 1 <= n-k, k <= n-1
      Therefore,
      FACT n = binomial n k * (FACT (n - k) * FACT k)             by binomial_formula2, k <= n.
             = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)   by FACT
             = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)   by MULT_ASSOC
             = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)   by MULT_COMM
      FACT n = n * FACT (n-1)                                     by FACT
             = n * (binomial (n-1) k * (FACT (n-1-k) * FACT k))   by binomial_formula2, k <= n-1.
             = (n * binomial (n-1) k) * (FACT (n-1-k) * FACT k)   by MULT_ASSOC
      Since  0 < FACT (n-1-k) * FACT k                            by FACT_LESS, MULT_EQ_0
             n * binomial (n-1) k = (n-k) * (binomial n k)        by MULT_RIGHT_CANCEL
*)
val binomial_up_eqn = store_thm(
  "binomial_up_eqn",
  ``!n. 0 < n ==> !k. n * binomial (n-1) k = (n-k) * (binomial n k)``,
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  Cases_on `n <= k` >| [
    `n-1 < k /\ (n - k = 0)` by decide_tac >>
    `binomial (n - 1) k = 0` by rw[binomial_less_0] >>
    metis_tac[MULT_EQ_0],
    `k < n /\ k <= n /\ 1 <= n-k /\ k <= n-1` by decide_tac >>
    `SUC (n-1) = n` by decide_tac >>
    `SUC (n-1-k) = n - k` by metis_tac[SUB_PLUS, ADD_COMM, ADD1, SUB_ADD] >>
    `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
    `_ = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)` by metis_tac[FACT] >>
    `_ = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    `FACT n = n * FACT (n-1)` by metis_tac[FACT] >>
    `_ = n * (binomial (n-1) k * (FACT (n-1-k) * FACT k))` by rw_tac std_ss[GSYM binomial_formula2] >>
    `_ = (n * binomial (n-1) k) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    metis_tac[FACT_LESS, MULT_EQ_0, MULT_RIGHT_CANCEL]
  ]);

(* Theorem: 0 < n ==> !k. binomial (n-1) k = ((n-k) * (binomial n k)) DIV n *)
(* Proof:
   Since  n * binomial (n-1) k = (n-k) * (binomial n k)        by binomial_up_eqn
              binomial (n-1) k = (n-k) * (binomial n k) DIV n  by DIV_SOLVE, 0 < n.
*)
val binomial_up = store_thm(
  "binomial_up",
  ``!n. 0 < n ==> !k. binomial (n-1) k = ((n-k) * (binomial n k)) DIV n``,
  rw[binomial_up_eqn, DIV_SOLVE]);

(* Relating Binomial to its right-entry:

   binomial n k = (n, k, n-k) = n! / k! (n-k)!
   binomial n (k+1) = (n, k+1, n-k-1) = n! / (k+1)! (n-k-1)!
                    = n! / (k+1) * k! ((n-k)!/(n-k))
                    = (n-k) * binomial n k / (k+1)
*)

(* Theorem: 0 < n ==> !k. (k + 1) * binomial n (k+1) = (n - k) * binomial n k *)
(* Proof:
   If n <= k, that is n < k+1.
      So   binomial n (k+1) = 0      by binomial_less_0
      and  n - k = 0                 by arithmetic
      Hence true                     by MULT_EQ_0
   Otherwise k < n,
      or k <= n, 1 <= n-k, k+1 <= n
      Therefore,
      FACT n = binomial n k * (FACT (n - k) * FACT k)             by binomial_formula2, k <= n.
             = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)   by FACT
             = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)   by MULT_ASSOC
             = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)   by MULT_COMM
      FACT n = binomial n (k+1) * (FACT (n-(k+1)) * FACT (k+1))      by binomial_formula2, k+1 <= n.
             = binomial n (k+1) * (FACT (n-1-k) * FACT (k+1))        by SUB_PLUS, ADD_COMM
             = binomial n (k+1) * (FACT (n-1-k) * ((k+1) * FACT k))  by FACT
             = binomial n (k+1) * ((k+1) * (FACT (n-1-k) * FACT k))  by MULT_ASSOC, MULT_COMM
             = (k+1) * binomial n (k+1) * (FACT (n-1-k) * FACT k)    by MULT_COMM, MULT_ASSOC
      Since  0 < FACT (n-1-k) * FACT k                            by FACT_LESS, MULT_EQ_0
             (k+1) * binomial n (k+1) = (n-k) * (binomial n k)    by MULT_RIGHT_CANCEL
*)
val binomial_right_eqn = store_thm(
  "binomial_right_eqn",
  ``!n. 0 < n ==> !k. (k + 1) * binomial n (k+1) = (n - k) * binomial n k``,
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  Cases_on `n <= k` >| [
    `n < k+1` by decide_tac >>
    `binomial n (k+1) = 0` by rw[binomial_less_0] >>
    `n - k = 0` by decide_tac >>
    metis_tac[MULT_EQ_0],
    `k < n /\ k <= n /\ 1 <= n-k /\ k+1 <= n` by decide_tac >>
    `SUC k = k + 1` by decide_tac >>
    `SUC (n-1-k) = n - k` by metis_tac[SUB_PLUS, ADD_COMM, ADD1, SUB_ADD] >>
    `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
    `_ = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)` by metis_tac[FACT] >>
    `_ = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    `FACT n = binomial n (k+1) * (FACT (n-(k+1)) * FACT (k+1))` by rw[binomial_formula2] >>
    `_ = binomial n (k+1) * (FACT (n-1-k) * FACT (k+1))` by metis_tac[SUB_PLUS, ADD_COMM] >>
    `_ = binomial n (k+1) * (FACT (n-1-k) * ((k+1) * FACT k))` by metis_tac[FACT] >>
    `_ = binomial n (k+1) * ((FACT (n-1-k) * (k+1)) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = binomial n (k+1) * ((k+1) * (FACT (n-1-k)) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    `_ = (binomial n (k+1) * (k+1)) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = (k+1) * binomial n (k+1) * (FACT (n-1-k) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    metis_tac[FACT_LESS, MULT_EQ_0, MULT_RIGHT_CANCEL]
  ]);

(* Theorem: 0 < n ==> !k. binomial n (k+1) = (n - k) * binomial n k DIV (k+1) *)
(* Proof:
   Since  (k + 1) * binomial n (k+1) = (n - k) * binomial n k  by binomial_right_eqn
          binomial n (k+1) = (n - k) * binomial n k DIV (k+1)  by DIV_SOLVE, 0 < k+1.
*)
val binomial_right = store_thm(
  "binomial_right",
  ``!n. 0 < n ==> !k. binomial n (k+1) = (n - k) * binomial n k DIV (k+1)``,
  rw[binomial_right_eqn, DIV_SOLVE, DECIDE ``!k. 0 < k+1``]);

(*
       k < HALF n <=> k + 1 <= n - k
n = 5, HALF n = 2, binomial 5 k: 1, 5, 10, 10, 5, 1
                              k= 0, 1,  2,  3, 4, 5
       k < 2      <=> k + 1 <= 5 - k
       k = 0              1 <= 5   binomial 5 1 >= binomial 5 0
       k = 1              2 <= 4   binomial 5 2 >= binomial 5 1
n = 6, HALF n = 3, binomial 6 k: 1, 6, 15, 20, 15, 6, 1
                              k= 0, 1, 2,  3,  4,  5, 6
       k < 3      <=> k + 1 <= 6 - k
       k = 0              1 <= 6   binomial 6 1 >= binomial 6 0
       k = 1              2 <= 5   binomial 6 2 >= binomial 6 1
       k = 2              3 <= 4   binomial 6 3 >= binomial 6 2
*)

(* Theorem: k < HALF n ==> binomial n k < binomial n (k + 1) *)
(* Proof:
   Note k < HALF n ==> 0 < n               by ZERO_DIV, 0 < 2
   also k < HALF n ==> k + 1 < n - k       by LESS_HALF_IFF
     so 0 < k + 1 /\ 0 < n - k             by arithmetic
    Now (k + 1) * binomial n (k + 1) = (n - k) * binomial n k   by binomial_right_eqn, 0 < n
   Note HALF n <= n                        by DIV_LESS_EQ, 0 < 2
     so k < HALF n <= n                    by above
   Thus 0 < binomial n k                   by binomial_pos, k <= n
    and 0 < binomial n (k + 1)             by MULT_0, MULT_EQ_0
  Hence binomial n k < binomial n (k + 1)  by MULT_EQ_LESS_TO_MORE
*)
val binomial_monotone = store_thm(
  "binomial_monotone",
  ``!n k. k < HALF n ==> binomial n k < binomial n (k + 1)``,
  rpt strip_tac >>
  `k + 1 < n - k` by rw[GSYM LESS_HALF_IFF] >>
  `0 < k + 1 /\ 0 < n - k` by decide_tac >>
  `(k + 1) * binomial n (k + 1) = (n - k) * binomial n k` by rw[binomial_right_eqn] >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `0 < binomial n k` by rw[binomial_pos] >>
  `0 < binomial n (k + 1)` by metis_tac[MULT_0, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[MULT_EQ_LESS_TO_MORE]);

(* Theorem: binomial n k <= binomial n (HALF n) *)
(* Proof:
   Since  (k + 1) * binomial n (k + 1) = (n - k) * binomial n k     by binomial_right_eqn
                    binomial n (k + 1) / binomial n k = (n - k) / (k + 1)
   As k varies from 0, 1,  to (n-1), n
   the ratio varies from n/1, (n-1)/2, (n-2)/3, ...., 1/n, 0/(n+1).
   The ratio is greater than 1 when      (n - k) / (k + 1) > 1
   or  n - k > k + 1
   or      n > 2 * k + 1
   or HALF n >= k + (HALF 1)
   or      k <= HALF n
   Thus (binomial n (HALF n)) is greater than all preceding coefficients.
   For k > HALF n, note that (binomial n k = binomial n (n - k))   by binomial_sym
   Hence (binomial n (HALF n)) is greater than all succeeding coefficients, too.

   If n = 0,
      binomial 0 k = 1 or 0    by binomial_0_n
      binomial 0 (HALF 0) = 1  by binomial_0_n, ZERO_DIV
      Hence true.
   If n <> 0,
      If k = HALF n, trivially true.
      If k < HALF n,
         Then binomial n k < binomial n (HALF n)           by binomial_monotone, MONOTONE_MAX
         Hence true.
      If ~(k < HALF n), HALF n < k.
         Then n - k <= HALF n                              by MORE_HALF_IMP
         If k > n,
            Then binomial n k = 0, hence true              by binomial_less_0
         If ~(k > n), then k <= n.
            Then binomial n k = binomial n (n - k)         by binomial_sym, k <= n
            If n - k = HALF n, trivially true.
            Otherwise, n - k < HALF n,
            Thus binomial n (n - k) < binomial n (HALF n)  by binomial_monotone, MONOTONE_MAX
         Hence true.
*)
val binomial_max = store_thm(
  "binomial_max",
  ``!n k. binomial n k <= binomial n (HALF n)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[binomial_0_n] >>
  Cases_on `k = HALF n` >-
  rw[] >>
  Cases_on `k < HALF n` >| [
    `binomial n k < binomial n (HALF n)` by rw[binomial_monotone, MONOTONE_MAX] >>
    decide_tac,
    `HALF n < k` by decide_tac >>
    `n - k <= HALF n` by rw[MORE_HALF_IMP] >>
    Cases_on `k > n` >-
    rw[binomial_less_0] >>
    `k <= n` by decide_tac >>
    `binomial n k = binomial n (n - k)` by rw[GSYM binomial_sym] >>
    Cases_on `n - k = HALF n` >-
    rw[] >>
    `n - k < HALF n` by decide_tac >>
    `binomial n (n - k) < binomial n (HALF n)` by rw[binomial_monotone, MONOTONE_MAX] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Primes and Binomial Coefficients                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: n is prime ==> n divides C(n,k)  for all 0 < k < n *)
(* Proof:
   C(n,k) = n!/k!/(n-k)!
   or n! = C(n,k) k! (n-k)!
   n divides n!, so n divides the product C(n,k) k!(n-k)!
   For a prime n, n cannot divide k!(n-k)!, all factors less than prime n.
   By Euclid's lemma, a prime divides a product must divide a factor.
   So p divides C(n,k).
*)
val prime_divides_binomials = store_thm(
  "prime_divides_binomials",
  ``!n. prime n ==> 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k))``,
  rpt strip_tac >-
  metis_tac[ONE_LT_PRIME] >>
  `(n = n-k + k) /\ (n-k) < n` by decide_tac >>
  `FACT n = (binomial n k) * (FACT (n-k) * FACT k)` by metis_tac[binomial_formula] >>
  `~(n divides (FACT k)) /\ ~(n divides (FACT (n-k)))` by metis_tac[PRIME_BIG_NOT_DIVIDES_FACT] >>
  `n divides (FACT n)` by metis_tac[DIVIDES_FACT, LESS_TRANS] >>
  metis_tac[P_EUCLIDES]);

(* Theorem: n is prime ==> n divides C(n,k)  for all 0 < k < n *)
(* Proof: by prime_divides_binomials *)
val prime_divides_binomials_alt = store_thm(
  "prime_divides_binomials_alt",
  ``!n k. prime n /\ 0 < k /\ k < n ==> n divides (binomial n k)``,
  rw[prime_divides_binomials]);

(* Theorem: If prime p divides n, p does not divide (n-1)!/(n-p)! *)
(* Proof:
   By contradiction.
   (n-1)...(n-p+1)/p  cannot be an integer
   as p cannot divide any of the numerator.
   Note: when p divides n, the nearest multiples for p are n+/-p.
*)
val prime_divisor_property = store_thm(
  "prime_divisor_property",
  ``!n p. 1 < n /\ p < n /\ prime p /\ p divides n ==>
   ~(p divides ((FACT (n-1)) DIV (FACT (n-p))))``,
  spose_not_then strip_assume_tac >>
  `1 < p` by metis_tac[ONE_LT_PRIME] >>
  `n-p < n-1` by decide_tac >>
  `(FACT (n-1)) DIV (FACT (n-p)) = PROD_SET (IMAGE SUC ((count (n-1)) DIFF (count (n-p))))`
   by metis_tac[FACT_REDUCTION, MULT_DIV, FACT_LESS] >>
  `(count (n-1)) DIFF (count (n-p)) = {x | (n-p) <= x /\ x < (n-1)}`
   by srw_tac[ARITH_ss][EXTENSION, EQ_IMP_THM] >>
  `IMAGE SUC {x | (n-p) <= x /\ x < (n-1)} = {x | (n-p) < x /\ x < n}` by
  (srw_tac[ARITH_ss][EXTENSION, EQ_IMP_THM] >>
  qexists_tac `x-1` >>
  decide_tac) >>
  `FINITE (count (n - 1) DIFF count (n - p))` by rw[] >>
  `?y. y IN {x| n - p < x /\ x < n} /\ p divides y` by metis_tac[PROD_SET_EUCLID, IMAGE_FINITE] >>
  `!m n y. y IN {x | m < x /\ x < n} ==> m < y /\ y < n` by rw[] >>
  `n-p < y /\ y < n` by metis_tac[] >>
  `y < n + p` by decide_tac >>
  `y = n` by metis_tac[MULTIPLE_INTERVAL] >>
  decide_tac);

(* Theorem: n divides C(n,k)  for all 0 < k < n ==> n is prime *)
(* Proof:
   By contradiction. Let p be a proper factor of n, 1 < p < n.
   Then C(n,p) = n(n-1)...(n-p+1)/p(p-1)..1
   is divisible by n/p, but not n, since
   C(n,p)/n = (n-1)...(n-p+1)/p(p-1)...1
   cannot be an integer as p cannot divide any of the numerator.
   Note: when p divides n, the nearest multiples for p are n+/-p.
*)
val divides_binomials_imp_prime = store_thm(
  "divides_binomials_imp_prime",
  ``!n. 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k)) ==> prime n``,
  (spose_not_then strip_assume_tac) >>
  `?p. prime p /\ p < n /\ p divides n` by metis_tac[PRIME_FACTOR_PROPER] >>
  `n divides (binomial n p)` by metis_tac[PRIME_POS] >>
  `0 < p` by metis_tac[PRIME_POS] >>
  `(n = n-p + p) /\ (n-p) < n` by decide_tac >>
  `FACT n = (binomial n p) * (FACT (n-p) * FACT p)` by metis_tac[binomial_formula] >>
  `(n = SUC (n-1)) /\ (p = SUC (p-1))` by decide_tac >>
  `(FACT n = n * FACT (n-1)) /\ (FACT p = p * FACT (p-1))` by metis_tac[FACT] >>
  `n * FACT (n-1) = (binomial n p) * (FACT (n-p) * (p * FACT (p-1)))` by metis_tac[] >>
  `0 < n` by decide_tac >>
  `?q. binomial n p = n * q` by metis_tac[divides_def, MULT_COMM] >>
  `0 <> n` by decide_tac >>
  `FACT (n-1) = q * (FACT (n-p) * (p * FACT (p-1)))`
    by metis_tac[EQ_MULT_LCANCEL, MULT_ASSOC] >>
  `_ = q * ((FACT (p-1) * p)* FACT (n-p))` by metis_tac[MULT_COMM] >>
  `_ = q * FACT (p-1) * p * FACT (n-p)` by metis_tac[MULT_ASSOC] >>
  `FACT (n-1) DIV FACT (n-p) = q * FACT (p-1) * p` by metis_tac[MULT_DIV, FACT_LESS] >>
  metis_tac[divides_def, prime_divisor_property]);

(* Theorem: n is prime iff n divides C(n,k)  for all 0 < k < n *)
(* Proof:
   By prime_divides_binomials and
   divides_binomials_imp_prime.
*)
val prime_iff_divides_binomials = store_thm(
  "prime_iff_divides_binomials",
  ``!n. prime n <=> 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k))``,
  metis_tac[prime_divides_binomials, divides_binomials_imp_prime]);

(* Theorem: prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0) *)
(* Proof: by prime_iff_divides_binomials *)
val prime_iff_divides_binomials_alt = store_thm(
  "prime_iff_divides_binomials_alt",
  ``!n. prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)``,
  rw[prime_iff_divides_binomials, DIVIDES_MOD_0]);

(* ------------------------------------------------------------------------- *)
(* Binomial Theorem                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Binomial Index Shifting, for
     SUM (k=1..n) C(n,k)x^(n+1-k)y^k
   = SUM (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1)
 *)
(* Proof:
SUM (k=1..n) C(n,k)x^(n+1-k)y^k
= SUM (MAP (\k. (binomial n k)* x**(n+1-k) * y**k) (GENLIST SUC n))
= SUM (GENLIST (\k. (binomial n k)* x**(n+1-k) * y**k) o SUC n)

SUM (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1)
= SUM (MAP (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) (GENLIST I n))
= SUM (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) o I n)
= SUM (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) n)

i.e.

(\k. (binomial n k)* x**(n-k+1) * y**k) o SUC
= (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1))
*)
(* Theorem: Binomial index shift for GENLIST *)
val GENLIST_binomial_index_shift = store_thm(
  "GENLIST_binomial_index_shift",
  ``!n x y. GENLIST ((\k. binomial n k * x ** SUC(n - k) * y ** k) o SUC) n =
           GENLIST (\k. binomial n (SUC k) * x ** (n-k) * y**(SUC k)) n``,
  rw_tac std_ss[GENLIST_FUN_EQ] >>
  `SUC (n - SUC k) = n - k` by decide_tac >>
  rw_tac std_ss[]);

(* This is closely related to above, with (SUC n) replacing (n),
   but does not require k < n. *)
(* Proof: by function equality. *)
val binomial_index_shift = store_thm(
  "binomial_index_shift",
  ``!n x y. (\k. binomial (SUC n) k * x ** ((SUC n) - k) * y ** k) o SUC =
           (\k. binomial (SUC n) (SUC k) * x ** (n-k) * y ** (SUC k))``,
  rw_tac std_ss[FUN_EQ_THM]);

(* Pattern for binomial expansion:

    (x+y)(x^3 + 3x^2y + 3xy^2 + y^3)
    = x(x^3) + 3x(x^2y) + 3x(xy^2) + x(y^3) +
                 y(x^3) + 3y(x^2y) + 3y(xy^2) + y(y^3)
    = x^4 + (3+1)x^3y + (3+3)(x^2y^2) + (1+3)(xy^3) + y^4
    = x^4 + 4x^3y     + 6x^2y^2       + 4xy^3       + y^4

*)

(* Theorem: multiply x into a binomial term *)
(* Proof: by function equality and EXP. *)
val binomial_term_merge_x = store_thm(
  "binomial_term_merge_x",
  ``!n x y. (\k. x * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
           (\k. binomial n k * x ** (SUC(n - k)) * y ** k)``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `x * (binomial n k * x ** (n - k) * y ** k) =
    binomial n k * (x * x ** (n - k)) * y ** k` by decide_tac >>
  metis_tac[EXP]);

(* Theorem: multiply y into a binomial term *)
(* Proof: by functional equality and EXP. *)
val binomial_term_merge_y = store_thm(
  "binomial_term_merge_y",
  ``!n x y. (\k. y * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
           (\k. binomial n k * x ** (n - k) * y ** (SUC k))``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `y * (binomial n k * x ** (n - k) * y ** k) =
    binomial n k * x ** (n - k) * (y * y ** k)` by decide_tac >>
  metis_tac[EXP]);

(* Theorem: [Binomial Theorem]  (x + y)^n = SUM (k=0..n) C(n,k)x^(n-k)y^k  *)
(* Proof:
   By induction on n.
   Base case: to prove (x + y)^0 = SUM (k=0..0) C(0,k)x^(0-k)y^k
   (x + y)^0 = 1    by EXP
   SUM (k=0..0) C(0,k)x^(n-k)y^k = C(0,0)x^(0-0)y^0 = C(0,0) = 1  by EXP, binomial_def
   Step case: assume (x + y)^n = SUM (k=0..n) C(n,k)x^(n-k)y^k
    to prove: (x + y)^SUC n = SUM (k=0..(SUC n)) C(SUC n,k)x^((SUC n)-k)y^k
      (x + y)^SUC n
    = (x + y)(x + y)^n      by EXP
    = (x + y) SUM (k=0..n) C(n,k)x^(n-k)y^k   by induction hypothesis
    = x (SUM (k=0..n) C(n,k)x^(n-k)y^k) +
      y (SUM (k=0..n) C(n,k)x^(n-k)y^k)       by RIGHT_ADD_DISTRIB
    = SUM (k=0..n) C(n,k)x^(n+1-k)y^k +
      SUM (k=0..n) C(n,k)x^(n-k)y^(k+1)       by moving factor into SUM
    = C(n,0)x^(n+1) + SUM (k=1..n) C(n,k)x^(n+1-k)y^k +
                      SUM (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)
                                              by breaking sum

    = C(n,0)x^(n+1) + SUM (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1) +
                      SUM (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)
                                              by index shifting
    = C(n,0)x^(n+1) +
      SUM (k=0..n-1) [C(n,k+1) + C(n,k)] x^(n-k)y^(k+1) +
      C(n,n)y^(n+1)                           by merging sums
    = C(n,0)x^(n+1) +
      SUM (k=0..n-1) C(n+1,k+1) x^(n-k)y^(k+1) +
      C(n,n)y^(n+1)                           by binomial recurrence
    = C(n,0)x^(n+1) +
      SUM (k=1..n) C(n+1,k) x^(n+1-k)y^k +
      C(n,n)y^(n+1)                           by index shifting again
    = C(n+1,0)x^(n+1) +
      SUM (k=1..n) C(n+1,k) x^(n+1-k)y^k +
      C(n+1,n+1)y^(n+1)                       by binomial identities
    = SUM (k=0..(SUC n))C(SUC n,k) x^((SUC n)-k)y^k
                                              by synthesis of sum
*)
val binomial_thm = store_thm(
  "binomial_thm",
  ``!n x y. (x + y) ** n = SUM (GENLIST (\k. (binomial n k) * x ** (n-k) * y ** k) (SUC n))``,
  Induct_on `n` >-
  rw[EXP, binomial_n_n] >>
  rw_tac std_ss[EXP] >>
  `(x + y) * SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n)) =
    x * SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n)) +
    y * SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n))`
    by metis_tac[RIGHT_ADD_DISTRIB] >>
  `_ = SUM (GENLIST ((\k. x * k) o (\k. binomial n k * x ** (n - k) * y ** k)) (SUC n)) +
        SUM (GENLIST ((\k. y * k) o (\k. binomial n k * x ** (n - k) * y ** k)) (SUC n))`
    by metis_tac[SUM_MULT, MAP_GENLIST] >>
  `_ = SUM (GENLIST (\k. binomial n k * x ** SUC(n - k) * y ** k) (SUC n)) +
        SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw[binomial_term_merge_x, binomial_term_merge_y] >>
  `_ = (\k. binomial n k * x ** SUC (n - k) * y ** k) 0 +
         SUM (GENLIST ((\k. binomial n k * x ** SUC (n - k) * y ** k) o SUC) n) +
        SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw[SUM_DECOMPOSE_FIRST] >>
  `_ = (\k. binomial n k * x ** SUC (n - k) * y ** k) 0 +
         SUM (GENLIST ((\k. binomial n k * x ** SUC (n - k) * y ** k) o SUC) n) +
        (SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n) +
         (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n )`
    by rw[SUM_DECOMPOSE_LAST] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
         SUM (GENLIST (\k. binomial n (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
        (SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n) +
         (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n )`
    by metis_tac[GENLIST_binomial_index_shift] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
        (SUM (GENLIST (\k. binomial n (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
         SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n)) +
         (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by decide_tac >>
  `_ = (\k. binomial n k * x ** SUC (n - k) * y ** k) 0 +
        SUM (GENLIST (\k. (binomial n (SUC k) * x ** (n - k) * y ** (SUC k) +
                           binomial n k * x ** (n - k) * y ** (SUC k))) n) +
        (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by metis_tac[SUM_ADD_GENLIST] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
        SUM (GENLIST (\k. (binomial n (SUC k) + binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by rw[RIGHT_ADD_DISTRIB, MULT_ASSOC] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
        SUM (GENLIST (\k. binomial (SUC n) (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by rw[binomial_recurrence, ADD_COMM] >>
  `_ = binomial (SUC n) 0 * x ** (SUC n) * y ** 0 +
        SUM (GENLIST (\k. binomial (SUC n) (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
        binomial (SUC n) (SUC n) * x ** 0 * y ** (SUC n)`
        by rw[binomial_n_0, binomial_n_n] >>
  `_ = binomial (SUC n) 0 * x ** (SUC n) * y ** 0 +
        SUM (GENLIST ((\k. binomial (SUC n) k * x ** ((SUC n) - k) * y ** k) o SUC) n) +
        binomial (SUC n) (SUC n) * x ** 0 * y ** (SUC n)`
        by rw[binomial_index_shift] >>
  `_ = SUM (GENLIST (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) (SUC n)) +
        (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) (SUC n)`
        by rw[SUM_DECOMPOSE_FIRST] >>
  `_ = SUM (GENLIST (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) (SUC (SUC n)))`
        by rw[SUM_DECOMPOSE_LAST] >>
  decide_tac);

(* This is a milestone theorem. *)

(* Derive an alternative form. *)
val binomial_thm_alt = save_thm("binomial_thm_alt",
    binomial_thm |> SIMP_RULE bool_ss [ADD1]);
(* val binomial_thm_alt =
   |- !n x y. (x + y) ** n =
              SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (n + 1)): thm *)

(* Theorem: SUM (GENLIST (binomial n) (SUC n)) = 2 ** n *)
(* Proof: by binomial_sum_alt and function equality. *)
(* Proof:
   Put x = 1, y = 1 in binomial_thm,
   (1 + 1) ** n = SUM (GENLIST (\k. binomial n k * 1 ** (n - k) * 1 ** k) (SUC n))
   (1 + 1) ** n = SUM (GENLIST (\k. binomial n k) (SUC n))    by EXP_1
   or    2 ** n = SUM (GENLIST (binomial n) (SUC n))          by FUN_EQ_THM
*)
Theorem binomial_sum:
  !n. SUM (GENLIST (binomial n) (SUC n)) = 2 ** n
Proof
  rpt strip_tac >>
  `!n. (\k. binomial n k * 1 ** (n - k) * 1 ** k) = binomial n` by rw[FUN_EQ_THM] >>
  `SUM (GENLIST (binomial n) (SUC n)) =
    SUM (GENLIST (\k. binomial n k * 1 ** (n - k) * 1 ** k) (SUC n))` by fs[] >>
  `_ = (1 + 1) ** n` by rw[GSYM binomial_thm] >>
  simp[]
QED

(* Derive an alternative form. *)
val binomial_sum_alt = save_thm("binomial_sum_alt",
    binomial_sum |> SIMP_RULE bool_ss [ADD1]);
(* val binomial_sum_alt = |- !n. SUM (GENLIST (binomial n) (n + 1)) = 2 ** n: thm *)

(* ------------------------------------------------------------------------- *)
(* Binomial Horizontal List                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define Horizontal List in Pascal Triangle *)
(*
val binomial_horizontal_def = Define `
  binomial_horizontal n = GENLIST (binomial n) (SUC n)
`;
*)

(* Use overloading for binomial_horizontal n. *)
val _ = overload_on("binomial_horizontal", ``\n. GENLIST (binomial n) (n + 1)``);

(* Theorem: binomial_horizontal 0 = [1] *)
(* Proof:
     binomial_horizontal 0
   = GENLIST (binomial 0) (0 + 1)    by notation
   = SNOC (binomial 0 0) []          by GENLIST, ONE
   = [binomial 0 0]                  by SNOC
   = [1]                             by binomial_n_0
*)
val binomial_horizontal_0 = store_thm(
  "binomial_horizontal_0",
  ``binomial_horizontal 0 = [1]``,
  rw[binomial_n_0]);

(* Theorem: LENGTH (binomial_horizontal n) = n + 1 *)
(* Proof:
     LENGTH (binomial_horizontal n)
   = LENGTH (GENLIST (binomial n) (n + 1)) by notation
   = n + 1                                 by LENGTH_GENLIST
*)
val binomial_horizontal_len = store_thm(
  "binomial_horizontal_len",
  ``!n. LENGTH (binomial_horizontal n) = n + 1``,
  rw[]);

(* Theorem: k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n) *)
(* Proof: by MEM_GENLIST *)
val binomial_horizontal_mem = store_thm(
  "binomial_horizontal_mem",
  ``!n k. k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n)``,
  metis_tac[MEM_GENLIST]);

(* Theorem: MEM (binomial n k) (binomial_horizontal n) <=> k <= n *)
(* Proof:
   If part: MEM (binomial n k) (binomial_horizontal n) ==> k <= n
      By contradiction, suppose n < k.
      Then binomial n k = 0        by binomial_less_0, ~(k <= n)
       But ?m. m < n + 1 ==> 0 = binomial n m    by MEM_GENLIST
        or m <= n ==> binomial n m = 0           by m < n + 1
       Yet binomial n m <> 0                     by binomial_eq_0
      This is a contradiction.
   Only-if part: k <= n ==> MEM (binomial n k) (binomial_horizontal n)
      By MEM_GENLIST, this is to show:
           ?m. m < n + 1 /\ (binomial n k = binomial n m)
      Note k <= n ==> k < n + 1,
      Take m = k, the result follows.
*)
val binomial_horizontal_mem_iff = store_thm(
  "binomial_horizontal_mem_iff",
  ``!n k. MEM (binomial n k) (binomial_horizontal n) <=> k <= n``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `binomial n k = 0` by rw[binomial_less_0] >>
    fs[MEM_GENLIST] >>
    `m <= n` by decide_tac >>
    fs[binomial_eq_0],
    rw[MEM_GENLIST] >>
    `k < n + 1` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: MEM x (binomial_horizontal n) <=> ?k. k <= n /\ (x = binomial n k) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n + 1 /\ (x = binomial n m)) <=> ?k. k <= n /\ (x = binomial n k)
   Since m < n + 1 <=> m <= n              by LE_LT1
   This is trivially true.
*)
val binomial_horizontal_member = store_thm(
  "binomial_horizontal_member",
  ``!n x. MEM x (binomial_horizontal n) <=> ?k. k <= n /\ (x = binomial n k)``,
  metis_tac[MEM_GENLIST, LE_LT1]);

(* Theorem: k <= n ==> (EL k (binomial_horizontal n) = binomial n k) *)
(* Proof: by EL_GENLIST *)
val binomial_horizontal_element = store_thm(
  "binomial_horizontal_element",
  ``!n k. k <= n ==> (EL k (binomial_horizontal n) = binomial n k)``,
  rw[EL_GENLIST]);

(* Theorem: EVERY (\x. 0 < x) (binomial_horizontal n) *)
(* Proof:
       EVERY (\x. 0 < x) (binomial_horizontal n)
   <=> EVERY (\x. 0 < x) (GENLIST (binomial n) (n + 1)) by notation
   <=> !k. k < n + 1 ==>  0 < binomial n k              by EVERY_GENLIST
   <=> !k. k <= n ==> 0 < binomial n k                  by arithmetic
   <=> T                                                by binomial_pos
*)
val binomial_horizontal_pos = store_thm(
  "binomial_horizontal_pos",
  ``!n. EVERY (\x. 0 < x) (binomial_horizontal n)``,
  rpt strip_tac >>
  `!k n. k < n + 1 <=> k <= n` by decide_tac >>
  rw_tac std_ss[EVERY_GENLIST, LESS_EQ_IFF_LESS_SUC, binomial_pos]);

(* Theorem: MEM x (binomial_horizontal n) ==> 0 < x *)
(* Proof: by binomial_horizontal_pos, EVERY_MEM *)
val binomial_horizontal_pos_alt = store_thm(
  "binomial_horizontal_pos_alt",
  ``!n x. MEM x (binomial_horizontal n) ==> 0 < x``,
  metis_tac[binomial_horizontal_pos, EVERY_MEM]);

(* Theorem: SUM (binomial_horizontal n) = 2 ** n *)
(* Proof:
     SUM (binomial_horizontal n)
   = SUM (GENLIST (binomial n) (n + 1))   by notation
   = 2 ** n                               by binomial_sum, ADD1
*)
val binomial_horizontal_sum = store_thm(
  "binomial_horizontal_sum",
  ``!n. SUM (binomial_horizontal n) = 2 ** n``,
  rw_tac std_ss[binomial_sum, GSYM ADD1]);

(* Theorem: MAX_LIST (binomial_horizontal n) = binomial n (HALF n) *)
(* Proof:
   Let l = binomial_horizontal n, m = binomial n (HALF n).
   Then l <> []                   by binomial_horizontal_len, LENGTH_NIL
    and HALF n <= n               by DIV_LESS_EQ, 0 < 2
     or HALF n < n + 1            by arithmetic
   Also MEM m l                   by binomial_horizontal_mem
    and !x. MEM x l ==> x <= m    by binomial_max, MEM_GENLIST
   Thus m = MAX_LIST l            by MAX_LIST_TEST
*)
val binomial_horizontal_max = store_thm(
  "binomial_horizontal_max",
  ``!n. MAX_LIST (binomial_horizontal n) = binomial n (HALF n)``,
  rpt strip_tac >>
  qabbrev_tac `l = binomial_horizontal n` >>
  qabbrev_tac `m = binomial n (HALF n)` >>
  `l <> []` by metis_tac[binomial_horizontal_len, LENGTH_NIL, DECIDE``n + 1 <> 0``] >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n < n + 1` by decide_tac >>
  `MEM m l` by rw[binomial_horizontal_mem, Abbr`l`, Abbr`m`] >>
  metis_tac[binomial_max, MEM_GENLIST, MAX_LIST_TEST]);

(* Theorem: MAX_SET (IMAGE (binomial n) (count (n + 1))) = binomial n (HALF n) *)
(* Proof:
   Let f = binomial n, s = IMAGE f (count (n + 1)).
   Note FINITE (count (n + 1))      by FINITE_COUNT
     so FINITE s                    by IMAGE_FINITE
   Also count (n + 1) <> {}         by COUNT_EQ_EMPTY, n + 1 <> 0
     so s <> {}                     by IMAGE_EQ_EMPTY
    Now !k. k IN (count (n + 1)) ==> f k <= f (HALF n)   by binomial_max
    ==> !x. x IN s ==> x <= f (HALF n)                   by IN_IMAGE
   Also HALF n <= n                 by DIV_LESS_EQ, 0 < 2
     so HALF n IN (count (n + 1))   by IN_COUNT
    ==> f (HALF n) IN s             by IN_IMAGE
   Thus MAX_SET s = f (HALF n)      by MAX_SET_TEST
*)
val binomial_row_max = store_thm(
  "binomial_row_max",
  ``!n. MAX_SET (IMAGE (binomial n) (count (n + 1))) = binomial n (HALF n)``,
  rpt strip_tac >>
  qabbrev_tac `f = binomial n` >>
  qabbrev_tac `s = IMAGE f (count (n + 1))` >>
  `FINITE s` by rw[Abbr`s`] >>
  `s <> {}` by rw[COUNT_EQ_EMPTY, Abbr`s`] >>
  `!k. k IN (count (n + 1)) ==> f k <= f (HALF n)` by rw[binomial_max, Abbr`f`] >>
  `!x. x IN s ==> x <= f (HALF n)` by metis_tac[IN_IMAGE] >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n IN (count (n + 1))` by rw[] >>
  `f (HALF n) IN s` by metis_tac[IN_IMAGE] >>
  rw[MAX_SET_TEST]);

(* Theorem: k <= m /\ m <= n ==>
           ((binomial m k) * (binomial n m) = (binomial n k) * (binomial (n - k) (m - k))) *)
(* Proof:
   Using binomial_formula2,

     (binomial m k) * (binomial n m)
         n!            m!
   = ----------- * ------------------      binomial formula
     m! (n - m)!    k! (m - k)!
        n!           m!
   = ----------- * ------------------      cancel m!
      k! m!        (m - k)! (n - m)!
        n!            (n - k)!
   = ----------- * ------------------      replace by (n - k)!
     k! (n - k)!   (m - k)! (n - m)!

   = (binomial n k) * (binomial (n - k) (m - k))   binomial formula
*)
val binomial_product_identity = store_thm(
  "binomial_product_identity",
  ``!m n k. k <= m /\ m <= n ==>
           ((binomial m k) * (binomial n m) = (binomial n k) * (binomial (n - k) (m - k)))``,
  rpt strip_tac >>
  `m - k <= n - k` by decide_tac >>
  `(n - k) - (m - k) = n - m` by decide_tac >>
  `FACT m = binomial m k * (FACT (m - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT n = binomial n m * (FACT (n - m) * FACT m)` by rw[binomial_formula2] >>
  `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT (n - k) = binomial (n - k) (m - k) * (FACT (n - m) * FACT (m - k))` by metis_tac[binomial_formula2] >>
  `FACT n = FACT (n - m) * (FACT k * (FACT (m - k) * ((binomial m k) * (binomial n m))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `FACT n = FACT (n - m) * (FACT k * (FACT (m - k) * ((binomial n k) * (binomial (n - k) (m - k)))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[MULT_LEFT_CANCEL, FACT_LESS, NOT_ZERO_LT_ZERO]);

(* Theorem: binomial n (HALF n) <= 4 ** (HALF n) *)
(* Proof:
   Let m = HALF n, l = binomial_horizontal n
   Note LENGTH l = n + 1               by binomial_horizontal_len
   If EVEN n,
      Then n = 2 * m                   by EVEN_HALF
       and m <= n                      by m <= 2 * m
      Note EL m l <= SUM l             by SUM_LE_EL, m < n + 1
       Now EL m l = binomial n m       by binomial_horizontal_element, m <= n
       and SUM l
         = 2 ** n                      by binomial_horizontal_sum
         = 4 ** m                      by EXP_EXP_MULT
      Hence binomial n m <= 4 ** m.
   If ~EVEN n,
      Then ODD n                       by EVEN_ODD
       and n = 2 * m + 1               by ODD_HALF
        so m + 1 <= n                  by m + 1 <= 2 * m + 1
      with m <= n                      by m + 1 <= n
      Note EL m l = binomial n m       by binomial_horizontal_element, m <= n
       and EL (m + 1) l = binomial n (m + 1)  by binomial_horizontal_element, m + 1 <= n
      Note binomial n (m + 1) = binomial n m  by binomial_sym
      Thus 2 * binomial n m
         = binomial n m + binomial n (m + 1)   by above
         = EL m l + EL (m + 1) l
        <= SUM l                       by SUM_LE_SUM_EL, m < m + 1, m + 1 < n + 1
       and SUM l
         = 2 ** n                      by binomial_horizontal_sum
         = 2 * 2 ** (2 * m)            by EXP, ADD1
         = 2 * 4 ** m                  by EXP_EXP_MULT
      Hence binomial n m <= 4 ** m.
*)
val binomial_middle_upper_bound = store_thm(
  "binomial_middle_upper_bound",
  ``!n. binomial n (HALF n) <= 4 ** (HALF n)``,
  rpt strip_tac >>
  qabbrev_tac `m = HALF n` >>
  qabbrev_tac `l = binomial_horizontal n` >>
  `LENGTH l = n + 1` by rw[binomial_horizontal_len, Abbr`l`] >>
  Cases_on `EVEN n` >| [
    `n = 2 * m` by rw[EVEN_HALF, Abbr`m`] >>
    `m < n + 1` by decide_tac >>
    `EL m l <= SUM l` by rw[SUM_LE_EL] >>
    `EL m l = binomial n m` by rw[binomial_horizontal_element, Abbr`l`] >>
    `SUM l = 2 ** n` by rw[binomial_horizontal_sum, Abbr`l`] >>
    `_ = 4 ** m` by rw[EXP_EXP_MULT] >>
    decide_tac,
    `ODD n` by metis_tac[EVEN_ODD] >>
    `n = 2 * m + 1` by rw[ODD_HALF, Abbr`m`] >>
    `EL m l = binomial n m` by rw[binomial_horizontal_element, Abbr`l`] >>
    `EL (m + 1) l = binomial n (m + 1)` by rw[binomial_horizontal_element, Abbr`l`] >>
    `binomial n (m + 1) = binomial n m` by rw[Once binomial_sym] >>
    `EL m l + EL (m + 1) l <= SUM l` by rw[SUM_LE_SUM_EL] >>
    `SUM l = 2 ** n` by rw[binomial_horizontal_sum, Abbr`l`] >>
    `_ = 2 * 2 ** (2 * m)` by metis_tac[EXP, ADD1] >>
    `_ = 2 * 4 ** m` by rw[EXP_EXP_MULT] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Stirling's Approximation                                                  *)
(* ------------------------------------------------------------------------- *)

(* Stirling's formula: n! ~ sqrt(2 pi n) (n/e)^n. *)
val _ = overload_on("Stirling",
   ``(!n. FACT n = (SQRT (2 * pi * n)) * (n DIV e) ** n) /\
     (!n. SQRT n = n ** h) /\ (2 * h = 1) /\ (0 < pi) /\ (0 < e) /\
     (!a b x y. (a * b) DIV (x * y) = (a DIV x) * (b DIV y)) /\
     (!a b c. (a DIV c) DIV (b DIV c) = a DIV b)``);

(* Theorem: Stirling ==>
            !n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = (2 ** (n + 1)) DIV (SQRT (2 * pi * n))) *)
(* Proof:
   Note HALF n <= n                 by DIV_LESS_EQ, 0 < 2
   Let k = HALF n, then n = 2 * k   by EVEN_HALF
   Note 0 < k                       by 0 < n = 2 * k
     so (k * 2) DIV k = 2           by MULT_TO_DIV, 0 < k
     or n DIV k = 2                 by MULT_COMM
   Also 0 < pi * n                  by MULT_EQ_0, 0 < pi, 0 < n
     so 0 < 2 * pi * n              by arithmetic

   Some theorems on the fly:
   Claim: !a b j. (a ** j) DIV (b ** j) = (a DIV b) ** j       [1]
   Proof: By induction on j.
          Base: (a ** 0) DIV (b ** 0) = (a DIV b) ** 0
                (a ** 0) DIV (b ** 0)
              = 1 DIV 1 = 1             by EXP, DIVMOD_ID, 0 < 1
              = (a DIV b) ** 0          by EXP
          Step: (a ** j) DIV (b ** j) = (a DIV b) ** j ==>
                (a ** (SUC j)) DIV (b ** (SUC j)) = (a DIV b) ** (SUC j)
                (a ** (SUC j)) DIV (b ** (SUC j))
              = (a * a ** j) DIV (b * b ** j)        by EXP
              = (a DIV b) * ((a ** j) DIV (b ** j))  by assumption
              = (a DIV b) * (a DIV b) ** j           by induction hypothesis
              = (a DIV b) ** (SUC j)                 by EXP

   Claim: !a b c. (a DIV b) * c = (a * c) DIV b      [2]
   Proof:   (a DIV b) * c
          = (a DIV b) * (c DIV 1)                    by DIV_1
          = (a * c) DIV (b * 1)                      by assumption
          = (a * c) DIV b                            by MULT_RIGHT_1

   Claim: !a b. a DIV b = 2 * (a DIV (2 * b))        [3]
   Proof:   a DIV b
          = 1 * (a DIV b)                            by MULT_LEFT_1
          = (n DIV n) * (a DIV b)                    by DIVMOD_ID, 0 < n
          = (n * a) DIV (n * b)                      by assumption
          = (n * a) DIV (k * (2 * b))                by arithmetic, n = 2 * k
          = (n DIV k) * (a DIV (2 * b))              by assumption
          = 2 * (a DIV (2 * b))                      by n DIV k = 2

   Claim: !a b. 0 < b ==> (a * (b ** h DIV b) = a DIV (b ** h))    [4]
   Proof: Let c = b ** h.
          Then b = c * c               by EXP_EXP_MULT
            so 0 < c                   by MULT_EQ_0, 0 < b
              a * (c DIV b)
            = (c DIV b) * a            by MULT_COMM
            = (a * c) DIV b            by [2]
            = (a * c) DIV (c * c)      by b = c * c
            = (a DIV c) * (c DIV c)    by assumption
            = a DIV c                  by DIVMOD_ID, c DIV c = 1, 0 < c

   Note  (FACT k) ** 2
       = (SQRT (2 * pi * k)) ** 2 * ((k DIV e) ** k) ** 2    by EXP_BASE_MULT
       = (SQRT (2 * pi * k)) ** 2 * (k DIV e) ** n           by EXP_EXP_MULT, n = 2 * k
       = (SQRT (pi * n)) ** 2 * (k DIV e) ** n               by MULT_ASSOC, 2 * k = n
       = ((pi * n) ** h) ** 2 * (k DIV e) ** n               by assumption
       = (pi * n) * (k DIV e) ** n                           by EXP_EXP_MULT, h * 2 = 1

     binomial n (HALF n)
   = binomial n k                             by k = HALF n
   = FACT n DIV (FACT k * FACT (n - k))       by binomial_formula3, k <= n
   = FACT n DIV (FACT k * FACT k)             by arithmetic, n - k = 2 * k - k = k
   = FACT n DIV ((FACT k) ** 2)               by EXP_2
   = FACT n DIV ((pi * n) * (k DIV e) ** n)   by above
   = ((2 * pi * n) ** h * (n DIV e) ** n) DIV ((pi * n) * (k DIV e) ** n)        by assumption
   = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) ** n DIV ((k DIV e) ** n))    by (a * b) DIV (x * y) = (a DIV x) * (b DIV y)
   = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) DIV (k DIV e)) ** n           by (a ** n) DIV (b ** n) = (a DIV b) ** n)
   = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * ((n DIV e) DIV (k DIV e)) ** n   by MULT_ASSOC, a DIV b = 2 * a DIV (2 * b)
   = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * (n DIV k) ** n                   by assumption, apply DIV_DIV_DIV_MULT
   = 2 DIV (2 * pi * n) ** h * (n DIV k) ** n                                    by 2 * x ** h DIV x = 2 DIV (x ** h)
   = 2 DIV (2 * pi * n) ** h * 2 ** n                                            by n DIV k = 2
   = 2 * 2 ** n DIV (2 * pi * n) ** h                                            by (a DIV b) * c = a * c DIV b
   = 2 ** (SUC n) DIV (2 * pi * n) ** h                                          by EXP
   = 2 ** (n + 1)) DIV (SQRT (2 * pi * n))                                       by ADD1, assumption
*)
val binomial_middle_by_stirling = store_thm(
  "binomial_middle_by_stirling",
  ``Stirling ==> !n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = (2 ** (n + 1)) DIV (SQRT (2 * pi * n)))``,
  rpt strip_tac >>
  `HALF n <= n /\ (n = 2 * HALF n)` by rw[DIV_LESS_EQ, EVEN_HALF] >>
  qabbrev_tac `k = HALF n` >>
  `0 < k` by decide_tac >>
  `n DIV k = 2` by metis_tac[MULT_TO_DIV, MULT_COMM] >>
  `0 < pi * n` by metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  `0 < 2 * pi * n` by decide_tac >>
  `(FACT k) ** 2 = (SQRT (2 * pi * k)) ** 2 * ((k DIV e) ** k) ** 2` by rw[EXP_BASE_MULT] >>
  `_ = (SQRT (2 * pi * k)) ** 2 * (k DIV e) ** n` by rw[GSYM EXP_EXP_MULT] >>
  `_ = (pi * n) * (k DIV e) ** n` by rw[GSYM EXP_EXP_MULT] >>
  (`!a b j. (a ** j) DIV (b ** j) = (a DIV b) ** j` by (Induct_on `j` >> rw[EXP])) >>
  `!a b c. (a DIV b) * c = (a * c) DIV b` by metis_tac[DIV_1, MULT_RIGHT_1] >>
  `!a b. a DIV b = 2 * (a DIV (2 * b))` by metis_tac[DIVMOD_ID, MULT_LEFT_1] >>
  `!a b. 0 < b ==> (a * (b ** h DIV b) = a DIV (b ** h))` by
  (rpt strip_tac >>
  qabbrev_tac `c = b ** h` >>
  `b = c * c` by rw[GSYM EXP_EXP_MULT, Abbr`c`] >>
  `0 < c` by metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  `a * (c DIV b) = (a * c) DIV (c * c)` by metis_tac[MULT_COMM] >>
  `_ = (a DIV c) * (c DIV c)` by metis_tac[] >>
  metis_tac[DIVMOD_ID, MULT_RIGHT_1]) >>
  `binomial n k = (FACT n) DIV (FACT k * FACT (n - k))` by metis_tac[binomial_formula3] >>
  `_ = (FACT n) DIV (FACT k) ** 2` by metis_tac[EXP_2, DECIDE``2 * k - k = k``] >>
  `_ = ((2 * pi * n) ** h * (n DIV e) ** n) DIV ((pi * n) * (k DIV e) ** n)` by prove_tac[] >>
  `_ = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) ** n DIV ((k DIV e) ** n))` by metis_tac[] >>
  `_ = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) DIV (k DIV e)) ** n` by metis_tac[] >>
  `_ = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * ((n DIV e) DIV (k DIV e)) ** n` by metis_tac[MULT_ASSOC] >>
  `_ = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * (n DIV k) ** n` by metis_tac[] >>
  `_ = 2 DIV (2 * pi * n) ** h * (n DIV k) ** n` by metis_tac[] >>
  `_ = 2 DIV (2 * pi * n) ** h * 2 ** n` by metis_tac[] >>
  `_ = (2 * 2 ** n DIV (2 * pi * n) ** h)` by metis_tac[] >>
  metis_tac[EXP, ADD1]);

(* ------------------------------------------------------------------------- *)
(* Useful theorems for Binomial                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: !k. 0 < k /\ k < n ==> (binomial n k MOD n = 0) <=>
            !h. 0 <= h /\ h < PRE n ==> (binomial n (SUC h) MOD n = 0) *)
(* Proof: by h = PRE k, or k = SUC h.
   If part: put k = SUC h,
      then 0 < SUC h ==>  0 <= h,
       and SUC h < n ==> PRE (SUC h) = h < PRE n  by prim_recTheory.PRE
   Only-if part: put h = PRE k,
      then 0 <= PRE k ==> 0 < k
       and PRE k < PRE n ==> k < n                by INV_PRE_LESS
*)
val binomial_range_shift = store_thm(
  "binomial_range_shift",
  ``!n . 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
                   (!h. h < PRE n ==> ((binomial n (SUC h)) MOD n = 0)))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `0 < SUC h /\ SUC h < n` by decide_tac >>
    rw_tac std_ss[],
    `k <> 0` by decide_tac >>
    `?h. k = SUC h` by metis_tac[num_CASES] >>
    `h < PRE n` by decide_tac >>
    rw_tac std_ss[]
  ]);

(* Theorem: binomial n k MOD n = 0 <=> (binomial n k * x ** (n-k) * y ** k) MOD n = 0 *)
(* Proof:
       (binomial n k * x ** (n-k) * y ** k) MOD n = 0
   <=> (binomial n k * (x ** (n-k) * y ** k)) MOD n = 0    by MULT_ASSOC
   <=> (((binomial n k) MOD n) * ((x ** (n - k) * y ** k) MOD n)) MOD n = 0  by MOD_TIMES2
   If part, apply 0 * z = 0  by MULT.
   Only-if part, pick x = 1, y = 1, apply EXP_1.
*)
val binomial_mod_zero = store_thm(
  "binomial_mod_zero",
  ``!n. 0 < n ==> !k. (binomial n k MOD n = 0) <=> (!x y. (binomial n k * x ** (n-k) * y ** k) MOD n = 0)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[MOD_TIMES2, ZERO_MOD, MULT] >>
  metis_tac[EXP_1, MULT_RIGHT_1]);


(* Theorem: (!k. 0 < k /\ k < n ==> (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0))) <=>
            (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))) *)
(* Proof: by h = PRE k, or k = SUC h. *)
val binomial_range_shift_alt = store_thm(
  "binomial_range_shift_alt",
  ``!n . 0 < n ==> ((!k. 0 < k /\ k < n ==> (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0))) <=>
                   (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `0 < SUC h /\ SUC h < n` by decide_tac >>
    rw_tac std_ss[],
    `k <> 0` by decide_tac >>
    `?h. k = SUC h` by metis_tac[num_CASES] >>
    `h < PRE n` by decide_tac >>
    rw_tac std_ss[]
  ]);

(* Theorem: !k. 0 < k /\ k < n ==> (binomial n k) MOD n = 0 <=>
            !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0 *)
(* Proof:
       !k. 0 < k /\ k < n ==> (binomial n k) MOD n = 0
   <=> !k. 0 < k /\ k < n ==> !x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0)   by binomial_mod_zero
   <=> !h. h < PRE n ==> !x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0)  by binomial_range_shift_alt
   <=> !x y. EVERY (\z. z = 0) (GENLIST (\k. (binomial n (SUC k) * x ** (n - (SUC k)) * y ** (SUC k)) MOD n) (PRE n)) by EVERY_GENLIST
   <=> !x y. EVERY (\x. x = 0) (GENLIST ((\k. binomial n k * x ** (n - k) * y ** k) o SUC) (PRE n)  by FUN_EQ_THM
   <=> !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0   by SUM_EQ_0
*)
val binomial_mod_zero_alt = store_thm(
  "binomial_mod_zero_alt",
  ``!n. 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
                  !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0)``,
  rpt strip_tac >>
  `!x y. (\k. (binomial n (SUC k) * x ** (n - SUC k) * y ** (SUC k)) MOD n) = (\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC` by rw_tac std_ss[FUN_EQ_THM] >>
  `(!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
    (!k. 0 < k /\ k < n ==> (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0)))` by rw_tac std_ss[binomial_mod_zero] >>
  `_ = (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0)))` by rw_tac std_ss[binomial_range_shift_alt] >>
  `_ = !x y h. h < PRE n ==> (((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))` by metis_tac[] >>
  rw_tac std_ss[EVERY_GENLIST, SUM_EQ_0]);


(* ------------------------------------------------------------------------- *)
(* Binomial Theorem with prime exponent                                      *)
(* ------------------------------------------------------------------------- *)


(* Theorem: [Binomial Expansion for prime exponent]  (x + y)^p = x^p + y^p (mod p) *)
(* Proof:
     (x+y)^p  (mod p)
   = SUM (k=0..p) C(p,k)x^(p-k)y^k  (mod p)                                     by binomial theorem
   = (C(p,0)x^py^0 + SUM (k=1..(p-1)) C(p,k)x^(p-k)y^k + C(p,p)x^0y^p) (mod p)  by breaking sum
   = (x^p + SUM (k=1..(p-1)) C(p,k)x^(p-k)y^k + y^k) (mod p)                    by binomial_n_0, binomial_n_n
   = ((x^p mod p) + (SUM (k=1..(p-1)) C(p,k)x^(p-k)y^k) (mod p) + (y^p mod p)) mod p   by MOD_PLUS
   = ((x^p mod p) + (SUM (k=1..(p-1)) (C(p,k)x^(p-k)y^k) (mod p)) + (y^p mod p)) mod p
   = (x^p mod p  + 0 + y^p mod p) mod p                                         by prime_iff_divides_binomials
   = (x^p + y^p) (mod p)                                                        by MOD_PLUS
*)
val binomial_thm_prime = store_thm(
  "binomial_thm_prime",
  ``!p. prime p ==> (!x y. (x + y) ** p MOD p = (x ** p + y ** p) MOD p)``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `!k. 0 < k /\ k < p ==> ((binomial p k) MOD p  = 0)` by metis_tac[prime_iff_divides_binomials, DIVIDES_MOD_0] >>
  `SUM (GENLIST ((\k. binomial p k * x ** (p - k) * y ** k) o SUC) (PRE p)) MOD p = 0` by metis_tac[SUM_GENLIST_MOD, binomial_mod_zero_alt, ZERO_MOD] >>
  `(x + y) ** p MOD p = (x ** p + SUM (GENLIST ((\k. binomial p k * x ** (p - k) * y ** k) o SUC) (PRE p)) + y ** p) MOD p` by rw_tac std_ss[binomial_thm, SUM_DECOMPOSE_FIRST_LAST, binomial_n_0, binomial_n_n, EXP] >>
  metis_tac[MOD_PLUS3, ADD_0, MOD_PLUS]);

(* ------------------------------------------------------------------------- *)
(* Leibniz Harmonic Triangle Documentation                                   *)
(* ------------------------------------------------------------------------- *)
(* Type: (# are temp)
   triple                = <| a: num; b: num; c: num |>
#  path                  = :num list
   Overloading:
   leibniz_vertical n    = [1 .. (n+1)]
   leibniz_up       n    = REVERSE (leibniz_vertical n)
   leibniz_horizontal n  = GENLIST (leibniz n) (n + 1)
   binomial_horizontal n = GENLIST (binomial n) (n + 1)
#  ta                    = (triplet n k).a
#  tb                    = (triplet n k).b
#  tc                    = (triplet n k).c
   p1 zigzag p2          = leibniz_zigzag p1 p2
   p1 wriggle p2         = RTC leibniz_zigzag p1 p2
   leibniz_col_arm a b n = MAP (\x. leibniz (a - x) b) [0 ..< n]
   leibniz_seg_arm a b n = MAP (\x. leibniz a (b + x)) [0 ..< n]

   leibniz_seg n k h     = IMAGE (\j. leibniz n (k + j)) (count h)
   leibniz_row n h       = IMAGE (leibniz n) (count h)
   leibniz_col h         = IMAGE (\i. leibniz i 0) (count h)
   lcm_run n             = list_lcm [1 .. n]
#  beta n k              = k * binomial n k
#  beta_horizontal n     = GENLIST (beta n o SUC) n
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:
   RTC_TRANS          |- R^* x y /\ R^* y z ==> R^* x z

   Leibniz Triangle (Denominator form):
#  leibniz_def        |- !n k. leibniz n k = (n + 1) * binomial n k
   leibniz_0_n        |- !n. leibniz 0 n = if n = 0 then 1 else 0
   leibniz_n_0        |- !n. leibniz n 0 = n + 1
   leibniz_n_n        |- !n. leibniz n n = n + 1
   leibniz_less_0     |- !n k. n < k ==> (leibniz n k = 0)
   leibniz_sym        |- !n k. k <= n ==> (leibniz n k = leibniz n (n - k))
   leibniz_monotone   |- !n k. k < HALF n ==> leibniz n k < leibniz n (k + 1)
   leibniz_pos        |- !n k. k <= n ==> 0 < leibniz n k
   leibniz_eq_0       |- !n k. (leibniz n k = 0) <=> n < k
   leibniz_alt        |- !n. leibniz n = (\j. (n + 1) * j) o binomial n
   leibniz_def_alt    |- !n k. leibniz n k = (\j. (n + 1) * j) (binomial n k)
   leibniz_up_eqn     |- !n. 0 < n ==> !k. (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k
   leibniz_up         |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1)
   leibniz_up_alt     |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
   leibniz_right_eqn  |- !n. 0 < n ==> !k. (k + 1) * leibniz n (k + 1) = (n - k) * leibniz n k
   leibniz_right      |- !n. 0 < n ==> !k. leibniz n (k + 1) = (n - k) * leibniz n k DIV (k + 1)
   leibniz_property   |- !n. 0 < n ==> !k. leibniz n k * leibniz (n - 1) k =
                                           leibniz n (k + 1) * (leibniz n k - leibniz (n - 1) k)
   leibniz_formula    |- !n k. k <= n ==> (leibniz n k = (n + 1) * FACT n DIV (FACT k * FACT (n - k)))
   leibniz_recurrence |- !n. 0 < n ==> !k. k < n ==> (leibniz n (k + 1) = leibniz n k *
                                           leibniz (n - 1) k DIV (leibniz n k - leibniz (n - 1) k))
   leibniz_n_k        |- !n k. 0 < k /\ k <= n ==> (leibniz n k =
                                           leibniz n (k - 1) * leibniz (n - 1) (k - 1)
                                           DIV (leibniz n (k - 1) - leibniz (n - 1) (k - 1)))
   leibniz_lcm_exchange  |- !n. 0 < n ==> !k. lcm (leibniz n k) (leibniz (n - 1) k) =
                                              lcm (leibniz n k) (leibniz n (k + 1))
   leibniz_middle_lower  |- !n. 4 ** n <= leibniz (TWICE n) n

   LCM of a list of numbers:
#  list_lcm_def          |- (list_lcm [] = 1) /\ !h t. list_lcm (h::t) = lcm h (list_lcm t)
   list_lcm_nil          |- list_lcm [] = 1
   list_lcm_cons         |- !h t. list_lcm (h::t) = lcm h (list_lcm t)
   list_lcm_sing         |- !x. list_lcm [x] = x
   list_lcm_snoc         |- !x l. list_lcm (SNOC x l) = lcm x (list_lcm l)
   list_lcm_map_times    |- !n l. list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l
   list_lcm_pos          |- !l. EVERY_POSITIVE l ==> 0 < list_lcm l
   list_lcm_pos_alt      |- !l. POSITIVE l ==> 0 < list_lcm l
   list_lcm_lower_bound  |- !l. EVERY_POSITIVE l ==> SUM l <= LENGTH l * list_lcm l
   list_lcm_lower_bound_alt          |- !l. POSITIVE l ==> SUM l <= LENGTH l * list_lcm l
   list_lcm_is_common_multiple       |- !x l. MEM x l ==> x divides (list_lcm l)
   list_lcm_is_least_common_multiple |- !l m. (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m
   list_lcm_append       |- !l1 l2. list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2)
   list_lcm_append_3     |- !l1 l2 l3. list_lcm (l1 ++ l2 ++ l3) = list_lcm [list_lcm l1; list_lcm l2; list_lcm l3]
   list_lcm_reverse      |- !l. list_lcm (REVERSE l) = list_lcm l
   list_lcm_suc          |- !n. list_lcm [1 .. n + 1] = lcm (n + 1) (list_lcm [1 .. n])
   list_lcm_nonempty_lower      |- !l. l <> [] /\ EVERY_POSITIVE l ==> SUM l DIV LENGTH l <= list_lcm l
   list_lcm_nonempty_lower_alt  |- !l. l <> [] /\ POSITIVE l ==> SUM l DIV LENGTH l <= list_lcm l
   list_lcm_divisor_lcm_pair    |- !l x y. MEM x l /\ MEM y l ==> lcm x y divides list_lcm l
   list_lcm_lower_by_lcm_pair   |- !l x y. POSITIVE l /\ MEM x l /\ MEM y l ==> lcm x y <= list_lcm l
   list_lcm_upper_by_common_multiple
                                |- !l m. 0 < m /\ (!x. MEM x l ==> x divides m) ==> list_lcm l <= m
   list_lcm_by_FOLDR     |- !ls. list_lcm ls = FOLDR lcm 1 ls
   list_lcm_by_FOLDL     |- !ls. list_lcm ls = FOLDL lcm 1 ls

   Lists in Leibniz Triangle:

   Veritcal Lists in Leibniz Triangle
   leibniz_vertical_alt      |- !n. leibniz_vertical n = GENLIST (\i. 1 + i) (n + 1)
   leibniz_vertical_0        |- leibniz_vertical 0 = [1]
   leibniz_vertical_len      |- !n. LENGTH (leibniz_vertical n) = n + 1
   leibniz_vertical_not_nil  |- !n. leibniz_vertical n <> []
   leibniz_vertical_pos      |- !n. EVERY_POSITIVE (leibniz_vertical n)
   leibniz_vertical_pos_alt  |- !n. POSITIVE (leibniz_vertical n)
   leibniz_vertical_mem      |- !n x. 0 < x /\ x <= n + 1 <=> MEM x (leibniz_vertical n)
   leibniz_vertical_snoc     |- !n. leibniz_vertical (n + 1) = SNOC (n + 2) (leibniz_vertical n)

   leibniz_up_0              |- leibniz_up 0 = [1]
   leibniz_up_len            |- !n. LENGTH (leibniz_up n) = n + 1
   leibniz_up_pos            |- !n. EVERY_POSITIVE (leibniz_up n)
   leibniz_up_mem            |- !n x. 0 < x /\ x <= n + 1 <=> MEM x (leibniz_up n)
   leibniz_up_cons           |- !n. leibniz_up (n + 1) = n + 2::leibniz_up n

   leibniz_horizontal_0      |- leibniz_horizontal 0 = [1]
   leibniz_horizontal_len    |- !n. LENGTH (leibniz_horizontal n) = n + 1
   leibniz_horizontal_el     |- !n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)
   leibniz_horizontal_mem    |- !n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)
   leibniz_horizontal_mem_iff   |- !n k. MEM (leibniz n k) (leibniz_horizontal n) <=> k <= n
   leibniz_horizontal_member    |- !n x. MEM x (leibniz_horizontal n) <=> ?k. k <= n /\ (x = leibniz n k)
   leibniz_horizontal_element   |- !n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)
   leibniz_horizontal_head   |- !n. TAKE 1 (leibniz_horizontal (n + 1)) = [n + 2]
   leibniz_horizontal_divisor|- !n k. k <= n ==> leibniz n k divides list_lcm (leibniz_horizontal n)
   leibniz_horizontal_pos    |- !n. EVERY_POSITIVE (leibniz_horizontal n)
   leibniz_horizontal_pos_alt|- !n. POSITIVE (leibniz_horizontal n)
   leibniz_horizontal_alt    |- !n. leibniz_horizontal n = MAP (\j. (n + 1) * j) (binomial_horizontal n)
   leibniz_horizontal_lcm_alt|- !n. list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n)
   leibniz_horizontal_sum          |- !n. SUM (leibniz_horizontal n) = (n + 1) * SUM (binomial_horizontal n)
   leibniz_horizontal_sum_eqn      |- !n. SUM (leibniz_horizontal n) = (n + 1) * 2 ** n:
   leibniz_horizontal_average      |- !n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) =
                                          SUM (binomial_horizontal n)
   leibniz_horizontal_average_eqn  |- !n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = 2 ** n

   Using Triplet and Paths:
   triplet_def               |- !n k. triplet n k =
                                           <|a := leibniz n k;
                                             b := leibniz (n + 1) k;
                                             c := leibniz (n + 1) (k + 1)
                                            |>
   leibniz_triplet_member    |- !n k. (ta = leibniz n k) /\
                                      (tb = leibniz (n + 1) k) /\ (tc = leibniz (n + 1) (k + 1))
   leibniz_right_entry       |- !n k. (k + 1) * tc = (n + 1 - k) * tb
   leibniz_up_entry          |- !n k. (n + 2) * ta = (n + 1 - k) * tb
   leibniz_triplet_property  |- !n k. ta * tb = tc * (tb - ta)
   leibniz_triplet_lcm       |- !n k. lcm tb ta = lcm tb tc

   Zigzag Path in Leibniz Triangle:
   leibniz_zigzag_def        |- !p1 p2. p1 zigzag p2 <=>
                                ?n k x y. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)
   list_lcm_zigzag           |- !p1 p2. p1 zigzag p2 ==> (list_lcm p1 = list_lcm p2)
   leibniz_zigzag_tail       |- !p1 p2. p1 zigzag p2 ==> !x. [x] ++ p1 zigzag [x] ++ p2
   leibniz_horizontal_zigzag |- !n k. k <= n ==>
                                TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) zigzag
                                TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)
   leibniz_triplet_0         |- leibniz_up 1 zigzag leibniz_horizontal 1

   Wriggle Paths in Leibniz Triangle:
   list_lcm_wriggle         |- !p1 p2. p1 wriggle p2 ==> (list_lcm p1 = list_lcm p2)
   leibniz_zigzag_wriggle   |- !p1 p2. p1 zigzag p2 ==> p1 wriggle p2
   leibniz_wriggle_tail     |- !p1 p2. p1 wriggle p2 ==> !x. [x] ++ p1 wriggle [x] ++ p2
   leibniz_wriggle_refl     |- !p1. p1 wriggle p1
   leibniz_wriggle_trans    |- !p1 p2 p3. p1 wriggle p2 /\ p2 wriggle p3 ==> p1 wriggle p3
   leibniz_horizontal_wriggle_step  |- !n k. k <= n + 1 ==>
      TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle leibniz_horizontal (n + 1)
   leibniz_horizontal_wriggle |- !n. [leibniz (n + 1) 0] ++ leibniz_horizontal n wriggle leibniz_horizontal (n + 1)

   Path Transform keeping LCM:
   leibniz_up_wriggle_horizontal  |- !n. leibniz_up n wriggle leibniz_horizontal n
   leibniz_lcm_property           |- !n. list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n)
   leibniz_vertical_divisor       |- !n k. k <= n ==> leibniz n k divides list_lcm (leibniz_vertical n)

   Lower Bound of Leibniz LCM:
   leibniz_horizontal_lcm_lower  |- !n. 2 ** n <= list_lcm (leibniz_horizontal n)
   leibniz_vertical_lcm_lower    |- !n. 2 ** n <= list_lcm (leibniz_vertical n)
   lcm_lower_bound               |- !n. 2 ** n <= list_lcm [1 .. (n + 1)]

   Leibniz LCM Invariance:
   leibniz_col_arm_0    |- !a b. leibniz_col_arm a b 0 = []
   leibniz_seg_arm_0    |- !a b. leibniz_seg_arm a b 0 = []
   leibniz_col_arm_1    |- !a b. leibniz_col_arm a b 1 = [leibniz a b]
   leibniz_seg_arm_1    |- !a b. leibniz_seg_arm a b 1 = [leibniz a b]
   leibniz_col_arm_len  |- !a b n. LENGTH (leibniz_col_arm a b n) = n
   leibniz_seg_arm_len  |- !a b n. LENGTH (leibniz_seg_arm a b n) = n
   leibniz_col_arm_el   |- !n k. k < n ==> !a b. EL k (leibniz_col_arm a b n) = leibniz (a - k) b
   leibniz_seg_arm_el   |- !n k. k < n ==> !a b. EL k (leibniz_seg_arm a b n) = leibniz a (b + k)
   leibniz_seg_arm_head |- !a b n. TAKE 1 (leibniz_seg_arm a b (n + 1)) = [leibniz a b]
   leibniz_col_arm_cons |- !a b n. leibniz_col_arm (a + 1) b (n + 1) = leibniz (a + 1) b::leibniz_col_arm a b n

   leibniz_seg_arm_zigzag_step       |- !n k. k < n ==> !a b.
                   TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) zigzag
                   TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)
   leibniz_seg_arm_wriggle_step      |- !n k. k < n + 1 ==> !a b.
                   TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
                   leibniz_seg_arm (a + 1) b (n + 1)
   leibniz_seg_arm_wriggle_row_arm   |- !a b n. [leibniz (a + 1) b] ++ leibniz_seg_arm a b n wriggle
                                                leibniz_seg_arm (a + 1) b (n + 1)
   leibniz_col_arm_wriggle_row_arm   |- !a b n. b <= a /\ n <= a + 1 - b ==>
                                                leibniz_col_arm a b n wriggle leibniz_seg_arm a b n
   leibniz_lcm_invariance            |- !a b n. b <= a /\ n <= a + 1 - b ==>
                                        (list_lcm (leibniz_col_arm a b n) = list_lcm (leibniz_seg_arm a b n))
   leibniz_col_arm_n_0               |- !n. leibniz_col_arm n 0 (n + 1) = leibniz_up n
   leibniz_seg_arm_n_0               |- !n. leibniz_seg_arm n 0 (n + 1) = leibniz_horizontal n
   leibniz_up_wriggle_horizontal_alt |- !n. leibniz_up n wriggle leibniz_horizontal n
   leibniz_up_lcm_eq_horizontal_lcm  |- !n. list_lcm (leibniz_up n) = list_lcm (leibniz_horizontal n)

   Set GCD as Big Operator:
   big_gcd_def                |- !s. big_gcd s = ITSET gcd s 0
   big_gcd_empty              |- big_gcd {} = 0
   big_gcd_sing               |- !x. big_gcd {x} = x
   big_gcd_reduction          |- !s x. FINITE s /\ x NOTIN s ==> (big_gcd (x INSERT s) = gcd x (big_gcd s))
   big_gcd_is_common_divisor  |- !s. FINITE s ==> !x. x IN s ==> big_gcd s divides x
   big_gcd_is_greatest_common_divisor
                              |- !s. FINITE s ==> !m. (!x. x IN s ==> m divides x) ==> m divides big_gcd s
   big_gcd_insert             |- !s. FINITE s ==> !x. big_gcd (x INSERT s) = gcd x (big_gcd s)
   big_gcd_two                |- !x y. big_gcd {x; y} = gcd x y
   big_gcd_positive           |- !s. FINITE s /\ s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s
   big_gcd_map_times          |- !s. FINITE s /\ s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s

   Set LCM as Big Operator:
   big_lcm_def                |- !s. big_lcm s = ITSET lcm s 1
   big_lcm_empty              |- big_lcm {} = 1
   big_lcm_sing               |- !x. big_lcm {x} = x
   big_lcm_reduction          |- !s x. FINITE s /\ x NOTIN s ==> (big_lcm (x INSERT s) = lcm x (big_lcm s))
   big_lcm_is_common_multiple |- !s. FINITE s ==> !x. x IN s ==> x divides big_lcm s
   big_lcm_is_least_common_multiple
                              |- !s. FINITE s ==> !m. (!x. x IN s ==> x divides m) ==> big_lcm s divides m
   big_lcm_insert             |- !s. FINITE s ==> !x. big_lcm (x INSERT s) = lcm x (big_lcm s)
   big_lcm_two                |- !x y. big_lcm {x; y} = lcm x y
   big_lcm_positive           |- !s. FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s
   big_lcm_map_times          |- !s. FINITE s /\ s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s

   LCM Lower bound using big LCM:
   leibniz_seg_def            |- !n k h. leibniz_seg n k h = {leibniz n (k + j) | j IN count h}
   leibniz_row_def            |- !n h. leibniz_row n h = {leibniz n j | j IN count h}
   leibniz_col_def            |- !h. leibniz_col h = {leibniz j 0 | j IN count h}
   leibniz_col_eq_natural     |- !n. leibniz_col n = natural n
   big_lcm_seg_transform      |- !n k h. lcm (leibniz (n + 1) k) (big_lcm (leibniz_seg n k h)) =
                                         big_lcm (leibniz_seg (n + 1) k (h + 1))
   big_lcm_row_transform      |- !n h. lcm (leibniz (n + 1) 0) (big_lcm (leibniz_row n h)) =
                                       big_lcm (leibniz_row (n + 1) (h + 1))
   big_lcm_corner_transform   |- !n. big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1))
   big_lcm_count_lower_bound  |- !f n. (!x. x IN count (n + 1) ==> 0 < f x) ==>
                                       SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1)))
   big_lcm_natural_eqn        |- !n. big_lcm (natural (n + 1)) =
                                     (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))
   big_lcm_lower_bound        |- !n. 2 ** n <= big_lcm (natural (n + 1))
   big_lcm_eq_list_lcm        |- !l. big_lcm (set l) = list_lcm l

   List LCM depends only on its set of elements:
   list_lcm_absorption        |- !x l. MEM x l ==> (list_lcm (x::l) = list_lcm l)
   list_lcm_nub               |- !l. list_lcm (nub l) = list_lcm l
   list_lcm_nub_eq_if_set_eq  |- !l1 l2. (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2))
   list_lcm_eq_if_set_eq      |- !l1 l2. (set l1 = set l2) ==> (list_lcm l1 = list_lcm l2)

   Set LCM by List LCM:
   set_lcm_def                |- !s. set_lcm s = list_lcm (SET_TO_LIST s)
   set_lcm_empty              |- set_lcm {} = 1
   set_lcm_nonempty           |- !s. FINITE s /\ s <> {} ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s)))
   set_lcm_sing               |- !x. set_lcm {x} = x
   set_lcm_eq_list_lcm        |- !l. set_lcm (set l) = list_lcm l
   set_lcm_eq_big_lcm         |- !s. FINITE s ==> (set_lcm s = big_lcm s)
   set_lcm_insert             |- !s. FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm s)
   set_lcm_is_common_multiple        |- !x s. FINITE s /\ x IN s ==> x divides set_lcm s
   set_lcm_is_least_common_multiple  |- !s m. FINITE s /\ (!x. x IN s ==> x divides m) ==> set_lcm s divides m
   pairwise_coprime_prod_set_eq_set_lcm
                             |- !s. FINITE s /\ PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s)
   pairwise_coprime_prod_set_divides
                             |- !s m. FINITE s /\ PAIRWISE_COPRIME s /\
                                      (!x. x IN s ==> x divides m) ==> PROD_SET s divides m

   Nair's Trick (direct):
   lcm_run_by_FOLDL          |- !n. lcm_run n = FOLDL lcm 1 [1 .. n]
   lcm_run_by_FOLDR          |- !n. lcm_run n = FOLDR lcm 1 [1 .. n]
   lcm_run_0                 |- lcm_run 0 = 1
   lcm_run_1                 |- lcm_run 1 = 1
   lcm_run_suc               |- !n. lcm_run (n + 1) = lcm (n + 1) (lcm_run n)
   lcm_run_pos               |- !n. 0 < lcm_run n
   lcm_run_small             |- (lcm_run 2 = 2) /\ (lcm_run 3 = 6) /\ (lcm_run 4 = 12) /\
                                (lcm_run 5 = 60) /\ (lcm_run 6 = 60) /\ (lcm_run 7 = 420) /\
                                (lcm_run 8 = 840) /\ (lcm_run 9 = 2520)
   lcm_run_divisors          |- !n. n + 1 divides lcm_run (n + 1) /\ lcm_run n divides lcm_run (n + 1)
   lcm_run_monotone          |- !n. lcm_run n <= lcm_run (n + 1)
   lcm_run_lower             |- !n. 2 ** n <= lcm_run (n + 1)
   lcm_run_leibniz_divisor   |- !n k. k <= n ==> leibniz n k divides lcm_run (n + 1)
   lcm_run_lower_odd         |- !n. n * 4 ** n <= lcm_run (TWICE n + 1)
   lcm_run_lower_even        |- !n. n * 4 ** n <= lcm_run (TWICE (n + 1))
   lcm_run_lower_better      |- !n. 7 <= n ==> 2 ** n <= lcm_run n

   lcm_run_odd_lower         |- !n. ODD n ==> HALF n * HALF (2 ** n) <= lcm_run n
   lcm_run_even_lower        |- !n. EVEN n ==> HALF (n - 2) * HALF (HALF (2 ** n)) <= lcm_run n
   lcm_run_odd_lower_alt     |- !n. ODD n /\ 5 <= n ==> 2 ** n <= lcm_run n
   lcm_run_even_lower_alt    |- !n. EVEN n /\ 8 <= n ==> 2 ** n <= lcm_run n
   lcm_run_lower_better      |- !n. 7 <= n ==> 2 ** n <= lcm_run n

   Nair's Trick (rework):
   lcm_run_odd_factor        |- !n. 0 < n ==> n * leibniz (TWICE n) n divides lcm_run (TWICE n + 1)
   lcm_run_lower_odd         |- !n. n * 4 ** n <= lcm_run (TWICE n + 1)
   lcm_run_lower_odd_iff     |- !n. ODD n ==> (2 ** n <= lcm_run n <=> 5 <= n)
   lcm_run_lower_even_iff    |- !n. EVEN n ==> (2 ** n <= lcm_run n <=> (n = 0) \/ 8 <= n)
   lcm_run_lower_better_iff  |- !n. 2 ** n <= lcm_run n <=> (n = 0) \/ (n = 5) \/ 7 <= n

   Nair's Trick (consecutive):
   lcm_upto_def              |- (lcm_upto 0 = 1) /\ !n. lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n)
   lcm_upto_0                |- lcm_upto 0 = 1
   lcm_upto_SUC              |- !n. lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n)
   lcm_upto_alt              |- (lcm_upto 0 = 1) /\ !n. lcm_upto (n + 1) = lcm (n + 1) (lcm_upto n)
   lcm_upto_1                |- lcm_upto 1 = 1
   lcm_upto_small            |- (lcm_upto 2 = 2) /\ (lcm_upto 3 = 6) /\ (lcm_upto 4 = 12) /\
                                (lcm_upto 5 = 60) /\ (lcm_upto 6 = 60) /\ (lcm_upto 7 = 420) /\
                                (lcm_upto 8 = 840) /\ (lcm_upto 9 = 2520) /\ (lcm_upto 10 = 2520)
   lcm_upto_eq_list_lcm      |- !n. lcm_upto n = list_lcm [1 .. n]
   lcm_upto_lower            |- !n. 2 ** n <= lcm_upto (n + 1)
   lcm_upto_divisors         |- !n. n + 1 divides lcm_upto (n + 1) /\ lcm_upto n divides lcm_upto (n + 1)
   lcm_upto_monotone         |- !n. lcm_upto n <= lcm_upto (n + 1)
   lcm_upto_leibniz_divisor  |- !n k. k <= n ==> leibniz n k divides lcm_upto (n + 1)
   lcm_upto_lower_odd        |- !n. n * 4 ** n <= lcm_upto (TWICE n + 1)
   lcm_upto_lower_even       |- !n. n * 4 ** n <= lcm_upto (TWICE (n + 1))
   lcm_upto_lower_better     |- !n. 7 <= n ==> 2 ** n <= lcm_upto n

   Simple LCM lower bounds:
   lcm_run_lower_simple      |- !n. HALF (n + 1) <= lcm_run n
   lcm_run_alt               |- !n. lcm_run n = lcm_run (n - 1 + 1)
   lcm_run_lower_good        |- !n. 2 ** (n - 1) <= lcm_run n

   Upper Bound by Leibniz Triangle:
   leibniz_eqn               |- !n k. leibniz n k = (n + 1 - k) * binomial (n + 1) k
   leibniz_right_alt         |- !n k. leibniz n (k + 1) = (n - k) * binomial (n + 1) (k + 1)
   leibniz_binomial_identity         |- !m n k. k <= m /\ m <= n ==>
                   (leibniz n k * binomial (n - k) (m - k) = leibniz m k * binomial (n + 1) (m + 1))
   leibniz_divides_leibniz_factor    |- !m n k. k <= m /\ m <= n ==>
                                         leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)
   leibniz_horizontal_member_divides |- !m n x. n <= TWICE m + 1 /\ m <= n /\
                                                MEM x (leibniz_horizontal n) ==>
                               x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)
   lcm_run_divides_property  |- !m n. n <= TWICE m /\ m <= n ==>
                                      lcm_run n divides lcm_run m * binomial n m
   lcm_run_bound_recurrence  |- !m n. n <= TWICE m /\ m <= n ==> lcm_run n <= lcm_run m * binomial n m
   lcm_run_upper_bound       |- !n. lcm_run n <= 4 ** n

   Beta Triangle:
   beta_0_n        |- !n. beta 0 n = 0
   beta_n_0        |- !n. beta n 0 = 0
   beta_less_0     |- !n k. n < k ==> (beta n k = 0)
   beta_eqn        |- !n k. beta (n + 1) (k + 1) = leibniz n k
   beta_alt        |- !n k. 0 < n /\ 0 < k ==> (beta n k = leibniz (n - 1) (k - 1))
   beta_pos        |- !n k. 0 < k /\ k <= n ==> 0 < beta n k
   beta_eq_0       |- !n k. (beta n k = 0) <=> (k = 0) \/ n < k
   beta_sym        |- !n k. k <= n ==> (beta n k = beta n (n - k + 1))

   Beta Horizontal List:
   beta_horizontal_0            |- beta_horizontal 0 = []
   beta_horizontal_len          |- !n. LENGTH (beta_horizontal n) = n
   beta_horizontal_eqn          |- !n. beta_horizontal (n + 1) = leibniz_horizontal n
   beta_horizontal_alt          |- !n. 0 < n ==> (beta_horizontal n = leibniz_horizontal (n - 1))
   beta_horizontal_mem          |- !n k. 0 < k /\ k <= n ==> MEM (beta n k) (beta_horizontal n)
   beta_horizontal_mem_iff      |- !n k. MEM (beta n k) (beta_horizontal n) <=> 0 < k /\ k <= n
   beta_horizontal_member       |- !n x. MEM x (beta_horizontal n) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k)
   beta_horizontal_element      |- !n k. k < n ==> (EL k (beta_horizontal n) = beta n (k + 1))
   lcm_run_by_beta_horizontal   |- !n. 0 < n ==> (lcm_run n = list_lcm (beta_horizontal n))
   lcm_run_beta_divisor         |- !n k. 0 < k /\ k <= n ==> beta n k divides lcm_run n
   beta_divides_beta_factor     |- !m n k. k <= m /\ m <= n ==> beta n k divides beta m k * binomial n m
   lcm_run_divides_property_alt |- !m n. n <= TWICE m /\ m <= n ==> lcm_run n divides binomial n m * lcm_run m
   lcm_run_upper_bound          |- !n. lcm_run n <= 4 ** n

   LCM Lower Bound using Maximum:
   list_lcm_ge_max               |- !l. POSITIVE l ==> MAX_LIST l <= list_lcm l
   lcm_lower_bound_by_list_lcm   |- !n. (n + 1) * binomial n (HALF n) <= list_lcm [1 .. (n + 1)]
   big_lcm_ge_max                |- !s. FINITE s /\ (!x. x IN s ==> 0 < x) ==> MAX_SET s <= big_lcm s
   lcm_lower_bound_by_big_lcm    |- !n. (n + 1) * binomial n (HALF n) <= big_lcm (natural (n + 1))

   Consecutive LCM function:
   lcm_lower_bound_by_list_lcm_stirling  |- Stirling /\ (!n c. n DIV SQRT (c * (n - 1)) = SQRT (n DIV c)) ==>
                                            !n. ODD n ==> SQRT (n DIV (2 * pi)) * 2 ** n <= list_lcm [1 .. n]
   big_lcm_non_decreasing                |- !n. big_lcm (natural n) <= big_lcm (natural (n + 1))
   lcm_lower_bound_by_big_lcm_stirling   |- Stirling /\ (!n c. n DIV SQRT (c * (n - 1)) = SQRT (n DIV c)) ==>
                                            !n. ODD n ==> SQRT (n DIV (2 * pi)) * 2 ** n <= big_lcm (natural n)

   Extra Theorems:
   gcd_prime_product_property   |- !p m n. prime p /\ m divides n /\ ~(p * m divides n) ==> (gcd (p * m) n = m)
   lcm_prime_product_property   |- !p m n. prime p /\ m divides n /\ ~(p * m divides n) ==> (lcm (p * m) n = p * n)
   list_lcm_prime_factor        |- !p l. prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l)
   list_lcm_prime_factor_member |- !p l. prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x

*)

(* ------------------------------------------------------------------------- *)
(* Leibniz Harmonic Triangle                                                 *)
(* ------------------------------------------------------------------------- *)

(*

Leibniz Harmonic Triangle (fraction form)

       c <= r
r = 1  1
r = 2  1/2  1/2
r = 3  1/3  1/6   1/3
r = 4  1/4  1/12  1/12  1/4
r = 5  1/5  1/10  1/20  1/10  1/5

In general,  L(r,1) = 1/r,  L(r,c) = |L(r-1,c-1) - L(r,c-1)|

Solving, L(r,c) = 1/(r C(r-1,c-1)) = 1/(c C(r,c))
where C(n,m) is the binomial coefficient of Pascal Triangle.

c = 1 are the 1/(1 * natural numbers
c = 2 are the 1/(2 * triangular numbers)
c = 3 are the 1/(3 * tetrahedral numbers)

Sum of denominators of n-th row = n 2**(n-1).

Note that  L(r,c) = Integral(0,1) x ** (c-1) * (1-x) ** (r-c) dx

Another form:  L(n,1) = 1/n, L(n,k) = L(n-1,k-1) - L(n,k-1)
Solving,  L(n,k) = 1/ k C(n,k) = 1/ n C(n-1,k-1)

Still another notation  H(n,r) = 1/ (n+1)C(n,r) = (n-r)!r!/(n+1)!  for 0 <= r <= n

Harmonic Denominator Number Triangle (integer form)
g(d,n) = 1/H(d,n)     where H(d,h) is the Leibniz Harmonic Triangle
g(d,n) = (n+d)C(d,n)  where C(d,h) is the Pascal's Triangle.
g(d,n) = n(n+1)...(n+d)/d!

(k+1)-th row of Pascal's triangle:  x^4 + 4x^3 + 6x^2 + 4x + 1
Perform differentiation, d/dx -> 4x^3 + 12x^2 + 12x + 4
which is k-th row of Harmonic Denominator Number Triangle.

(k+1)-th row of Pascal's triangle: (x+1)^(k+1)
k-th row of Harmonic Denominator Number Triangle: d/dx[(x+1)^(k+1)]

  d/dx[(x+1)^(k+1)]
= d/dx[SUM C(k+1,j) x^j]    j = 0...(k+1)
= SUM C(k+1,j) d/dx[x^j]
= SUM C(k+1,j) j x^(j-1)    j = 1...(k+1)
= SUM C(k+1,j+1) (j+1) x^j  j = 0...k
= SUM D(k,j) x^j            with D(k,j) = (j+1) C(k+1,j+1)  ???

*)

(* Another presentation of triangles:

The harmonic triangle of Leibniz
    1/1   1/2   1/3   1/4    1/5   .... harmonic fractions
       1/2   1/6   1/12   1/20     .... successive difference
          1/3   1/12   1/30   ...
            1/4     1/20  ... ...
                1/5   ... ... ...

Pascal's triangle
    1    1   1   1   1   1   1     .... units
       1   2   3   4   5   6       .... sum left and above
         1   3   6   10  15  21
           1   4   10  20  35
             1   5   15  35
               1   6   21


*)

(* LCM Lemma

(n+1) lcm (C(n,0) to C(n,n)) = lcm (1 to (n+1))

m-th number in the n-th row of Leibniz triangle is:  1/ (n+1)C(n,m)

LHS = (n+1) LCM (C(n,0), C(n,1), ..., C(n,n)) = lcd of fractions in n-th row of Leibniz triangle.

Any such number is an integer linear combination of fractions on triangle’s sides
1/1, 1/2, 1/3, ... 1/n, and vice versa.

So LHS = lcd (1/1, 1/2, 1/3, ..., 1/n) = RHS = lcm (1,2,3, ..., (n+1)).

0-th row:               1
1-st row:           1/2  1/2
2-nd row:        1/3  1/6  1/3
3-rd row:    1/4  1/12  1/12  1/4
4-th row: 1/5  1/20  1/30  1/20  1/5

4-th row: 1/5 C(4,m), C(4,m) = 1 4 6 4 1, hence 1/5 1/20 1/30 1/20 1/5
  lcd (1/5 1/20 1/30 1/20 1/5)
= lcm (5, 20, 30, 20, 5)
= lcm (5 C(4,0), 5 C(4,1), 5 C(4,2), 5 C(4,3), 5 C(4,4))
= 5 lcm (C(4,0), C(4,1), C(4,2), C(4,3), C(4,4))

But 1/5 = harmonic
    1/20 = 1/4 - 1/5 = combination of harmonic
    1/30 = 1/12 - 1/20 = (1/3 - 1/4) - (1/4 - 1/5) = combination of harmonic

  lcd (1/5 1/20 1/30 1/20 1/5)
= lcd (combination of harmonic from 1/1 to 1/5)
= lcd (1/1 to 1/5)
= lcm (1 to 5)

Theorem:  lcd (1/x 1/y 1/z) = lcm (x y z)
Theorem:  lcm (kx ky kz) = k lcm (x y z)
Theorem:  lcd (combination of harmonic from 1/1 to 1/n) = lcd (1/1 to 1/n)
Then apply first theorem, lcd (1/1 to 1/n) = lcm (1 to n)
*)

(* LCM Bound
   0 < n ==> 2^(n-1) < lcm (1 to n)

  lcm (1 to n)
= n lcm (C(n-1,0) to C(n-1,n-1))  by LCM Lemma
>= n max (0 <= j <= n-1) C(n-1,j)
>= SUM (0 <= j <= n-1) C(n-1,j)
= 2^(n-1)

  lcm (1 to 5)
= 5 lcm (C(4,0), C(4,1), C(4,2), C(4,3), C(4,4))


>= C(4,0) + C(4,1) + C(4,2) + C(4,3) + C(4,4)
= (1 + 1)^4
= 2^4

  lcm (1 to 5)             = 1x2x3x4x5/2 = 60
= 5 lcm (1 4 6 4 1)        = 5 x 12
=  lcm (1 4 6 4 1)         --> unfold 5x to add 5 times
 + lcm (1 4 6 4 1)
 + lcm (1 4 6 4 1)
 + lcm (1 4 6 4 1)
 + lcm (1 4 6 4 1)
>= 1 + 4 + 6 + 4 + 1       --> pick one of each 5 C(n,m), i.e. diagonal
= (1 + 1)^4                --> fold back binomial
= 2^4                      = 16

Actually, can take 5 lcm (1 4 6 4 1) >= 5 x 6 = 30,
but this will need estimation of C(n, n/2), or C(2n,n), involving Stirling's formula.

Theorem: lcm (x y z) >= x  or lcm (x y z) >= y  or lcm (x y z) >= z

*)

(*

More generally, there is an identity for 0 <= k <= n:

(n+1) lcm (C(n,0), C(n,1), ..., C(n,k)) = lcm (n+1, n, n-1, ..., n+1-k)

This is simply that fact that any integer linear combination of
f(x), delta f(x), delta^2 f(x), ..., delta^k f(x)
is an integer linear combination of f(x), f(x-1), f(x-2), ..., f(x-k)
where delta is the difference operator, f(x) = 1/x, and x = n+1.

BTW, Leibnitz harmonic triangle too gives this identity.

That's correct, but the use of absolute values in the Leibniz triangle and
its specialized definition somewhat obscures the generic, linear nature of the identity.

  f(x) = f(n+1)   = 1/(n+1)
f(x-1) = f(n)     = 1/n
f(x-2) = f(n-1)   = 1/(n-1)
f(x-k) = f(n+1-k) = 1/(n+1-k)

        f(x) = f(n+1) = 1/(n+1) = 1/(n+1)C(n,0)
  delta f(x) = f(x-1) - f(x) = 1/n - 1/(n+1) = 1/n(n+1) = 1/(n+1)C(n,1)
             = C(1,0) f(x-1) - C(1,1) f(x)
delta^2 f(x) = delta f(x-1) - delta f(x) = 1/(n-1)n - 1/n(n+1)
             = (n(n+1) - n(n-1))/(n)(n+1)(n)(n-1)
             = 2n/n(n+1)n(n-1) = 1/(n+1)(n(n-1)/2) = 1/(n+1)C(n,2)
delta^2 f(x) = delta f(x-1) - delta f(x)
             = (f(x-2) - f(x-1)) - (f(x-1) - f(x))
             = f(x-2) - 2 f(x-1) + f(x)
             = C(2,0) f(x-2) - C(2,1) f(x-1) + C(2,2) f(x)
delta^3 f(x) = delta^2 f(x-1) - delta^2 f(x)
             = (f(x-3) - 2 f(x-2) + f(x-1)) - (f(x-2) - 2 f(x-1) + f(x))
             = f(x-3) - 3 f(x-2) + 3 f(x-1) - f(x)
             = C(3,0) f(x-3) - C(3,1) f(x-2) + C(3,2) f(x-2) - C(3,3) f(x)

delta^k f(x) = C(k,0) f(x-k) - C(k,1) f(x-k+1) + ... + (-1)^k C(k,k) f(x)
             = SUM(0 <= j <= k) (-1)^k C(k,j) f(x-k+j)
Also,
        f(x) = 1/(n+1)C(n,0)
  delta f(x) = 1/(n+1)C(n,1)
delta^2 f(x) = 1/(n+1)C(n,2)
delta^k f(x) = 1/(n+1)C(n,k)

so lcd (f(x), df(x), d^2f(x), ..., d^kf(x))
 = lcm ((n+1)C(n,0),(n+1)C(n,1),...,(n+1)C(n,k))   by lcd-to-lcm
 = lcd (f(x), f(x-1), f(x-2), ..., f(x-k))         by linear combination
 = lcm ((n+1), n, (n-1), ..., (n+1-k))             by lcd-to-lcm

How to formalize:
lcd (f(x), df(x), d^2f(x), ..., d^kf(x)) = lcd (f(x), f(x-1), f(x-2), ..., f(x-k))

Simple case: lcd (f(x), df(x)) = lcd (f(x), f(x-1))

  lcd (f(x), df(x))
= lcd (f(x), f(x-1) - f(x))
= lcd (f(x), f(x-1))

Can we have
  LCD {f(x), df(x)}
= LCD {f(x), f(x-1) - f(x)} = LCD {1/x, 1/(x-1) - 1/x}
= LCD {f(x), f(x-1), f(x)}  = lcm {x, x(x-1)}
= LCD {f(x), f(x-1)}        = x(x-1) = lcm {x, x-1} = LCD {1/x, 1/(x-1)}

*)

(* Step 1: From Pascal's Triangle to Leibniz's Triangle

Pascal's Triangle:

row 0    1
row 1    1   1
row 2    1   2   1
row 3    1   3   3   1
row 4    1   4   6   4   1
row 5    1   5  10  10   5  1

The rule is: boundary = 1, entry = up      + left-up
         or: C(n,0) = 1, C(n,k) = C(n-1,k) + C(n-1,k-1)

Multiple each row by successor of its index, i.e. row n -> (n + 1) (row n):
Multiples Triangle (or Modified Triangle):

1 * row 0   1
2 * row 1   2  2
3 * row 2   3  6  3
4 * row 3   4  12 12  4
5 * row 4   5  20 30 20  5
6 * row 5   6  30 60 60 30  6

The rule is: boundary = n, entry = left * left-up / (left - left-up)
         or: L(n,0) = n, L(n,k) = L(n,k-1) * L(n-1,k-1) / (L(n,k-1) - L(n-1,k-1))

Then   lcm(1, 2)
     = lcm(2)
     = lcm(2, 2)

       lcm(1, 2, 3)
     = lcm(lcm(1,2), 3)  using lcm(1,2,...,n,n+1) = lcm(lcm(1,2,...,n), n+1)
     = lcm(2, 3)         using lcm(1,2)
     = lcm(2*3/1, 3)     using lcm(L(n,k-1), L(n-1,k-1)) = lcm(L(n,k-1), L(n-1,k-1)/(L(n,k-1), L(n-1,k-1)), L(n-1,k-1))
     = lcm(6, 3)
     = lcm(3, 6, 3)

       lcm(1, 2, 3, 4)
     = lcm(lcm(1,2,3), 4)
     = lcm(lcm(6,3), 4)
     = lcm(6, 3, 4)
     = lcm(6, 3*4/1, 4)
     = lcm(6, 12, 4)
     = lcm(6*12/6, 12, 4)
     = lcm(12, 12, 4)
     = lcm(4, 12, 12, 4)

       lcm(1, 2, 3, 4, 5)
     = lcm(lcm(2,3,4), 5)
     = lcm(lcm(12,4), 5)
     = lcm(12, 4, 5)
     = lcm(12, 4*5/1, 5)
     = lcm(12, 20, 5)
     = lcm(12*20/8, 20, 5)
     = lcm(30, 20, 5)
     = lcm(5, 20, 30, 20, 5)

       lcm(1, 2, 3, 4, 5, 6)
     = lcm(lcm(1, 2, 3, 4, 5), 6)
     = lcm(lcm(30,20,5), 6)
     = lcm(30, 20, 5, 6)
     = lcm(30, 20, 5*6/1, 6)
     = lcm(30, 20, 30, 6)
     = lcm(30, 20*30/10, 30, 6)
     = lcm(20, 60, 30, 6)
     = lcm(20*60/40, 60, 30, 6)
     = lcm(30, 60, 30, 6)
     = lcm(6, 30, 60, 30, 6)

Invert each entry of Multiples Triangle into a unit fraction:
Leibniz's Triangle:

1/(1 * row 0)   1/1
1/(2 * row 1)   1/2  1/2
1/(3 * row 2)   1/3  1/6  1/3
1/(4 * row 3)   1/4  1/12 1/12 1/4
1/(5 * row 4)   1/5  1/20 1/30 1/20 1/5
1/(6 * row 5)   1/6  1/30 1/60 1/60 1/30 1/6

Theorem: In the Multiples Triangle, the vertical-lcm = horizontal-lcm.
i.e.    lcm (1, 2, 3) = lcm (3, 6, 3) = 6
        lcm (1, 2, 3, 4) = lcm (4, 12, 12, 4) = 12
        lcm (1, 2, 3, 4, 5) = lcm (5, 20, 30, 20, 5) = 60
        lcm (1, 2, 3, 4, 5, 6) = lcm (6, 30, 60, 60, 30, 6) = 60
Proof: With reference to Leibniz's Triangle, note: term = left-up - left
  lcm (5, 20, 30, 20, 5)
= lcm (5, 20, 30)                   by reduce repetition
= lcm (5, d(1/20), d(1/30))         by denominator of fraction
= lcm (5, d(1/4 - 1/5), d(1/30))    by term = left-up - left
= lcm (5, lcm(4, 5), d(1/12 - 1/20))     by denominator of fraction subtraction
= lcm (5, 4, lcm(12, 20))                by lcm (a, lcm (a, b)) = lcm (a, b)
= lcm (5, 4, lcm(d(1/12), d(1/20)))      to fraction again
= lcm (5, 4, lcm(d(1/3 - 1/4), d(1/4 - 1/5)))   by Leibniz's Triangle
= lcm (5, 4, lcm(lcm(3,4),     lcm(4,5)))       by fraction subtraction denominator
= lcm (5, 4, lcm(3, 4, 5))                      by lcm merge
= lcm (5, 4, 3)                                 merge again
= lcm (5, 4, 3, 2)                              by lcm include factor (!!!)
= lcm (5, 4, 3, 2, 1)                           by lcm include 1

Note: to make 30, need 12, 20
      to make 12, need 3, 4; to make 20, need 4, 5
  lcm (1, 2, 3, 4, 5)
= lcm (1, 2, lcm(3,4), lcm(4,5), 5)
= lcm (1, 2, d(1/3 - 1/4), d(1/4 - 1/5), 5)
= lcm (1, 2, d(1/12), d(1/20), 5)
= lcm (1, 2, 12, 20, 5)
= lcm (1, 2, lcm(12, 20), 20, 5)
= lcm (1, 2, d(1/12 - 1/20), 20, 5)
= lcm (1, 2, d(1/30), 20, 5)
= lcm (1, 2, 30, 20, 5)
= lcm (1, 30, 20, 5)             can drop factor !!
= lcm (30, 20, 5)                can drop 1
= lcm (5, 20, 30, 20, 5)

  lcm (1, 2, 3, 4, 5, 6)
= lcm (lcm (1, 2, 3, 4, 5), lcm(5,6), 6)
= lcm (lcm (5, 20, 30, 20, 5), d(1/5 - 1/6), 6)
= lcm (lcm (5, 20, 30, 20, 5), d(1/30), 6)
= lcm (lcm (5, 20, 30, 20, 5), 30, 6)
= lcm (lcm (5, 20, 30, 20, 5), 30, 6)
= lcm (5, 30, 20, 6)
= lcm (30, 20, 6)               can drop factor !!
= lcm (lcm(20, 30), 30, 6)
= lcm (d(1/20 - 1/30), 30, 6)
= lcm (d(1/60), 30, 6)
= lcm (60, 30, 6)
= lcm (6, 30, 60, 30, 6)

  lcm (1, 2)
= lcm (lcm(1,2), 2)
= lcm (2, 2)

  lcm (1, 2, 3)
= lcm (lcm(1, 2), 3)
= lcm (2, 3) --> lcm (2x3/(3-2), 3) = lcm (6, 3)
= lcm (lcm(2, 3), 3)   -->  lcm (6, 3) = lcm (3, 6, 3)
= lcm (d(1/2 - 1/3), 3)
= lcm (d(1/6), 3)
= lcm (6, 3) = lcm (3, 6, 3)

  lcm (1, 2, 3, 4)
= lcm (lcm(1, 2, 3), 4)
= lcm (lcm(6, 3), 4)
= lcm (6, 3, 4)
= lcm (6, lcm(3, 4), 4) --> lcm (6, 12, 4) = lcm (6x12/(12-6), 12, 4)
= lcm (6, d(1/3 - 1/4), 4)                 = lcm (12, 12, 4) = lcm (4, 12, 12, 4)
= lcm (6, d(1/12), 4)
= lcm (6, 12, 4)
= lcm (lcm(6, 12), 4)
= lcm (d(1/6 - 1/12), 4)
= lcm (d(1/12), 4)
= lcm (12, 4) = lcm (4, 12, 12, 4)

  lcm (1, 2, 3, 4, 5)
= lcm (lcm(1, 2, 3, 4), 5)
= lcm (lcm(12, 4), 5)
= lcm (12, 4, 5)
= lcm (12, lcm(4,5), 5) --> lcm (12, 20, 5) = lcm (12x20/(20-12), 20, 5)
= lcm (12, d(1/4 - 1/5), 5)                 = lcm (240/8, 20, 5) but lcm(12,20) != 30
= lcm (12, d(1/20), 5)                      = lcm (30, 20, 5)    use lcm(a,b,c) = lcm(ab/(b-a), b, c)
= lcm (12, 20, 5)
= lcm (lcm(12,20), 20, 5)
= lcm (d(1/12 - 1/20), 20, 5)
= lcm (d(1/30), 20, 5)
= lcm (30, 20, 5) = lcm (5, 20, 30, 20, 5)

  lcm (1, 2, 3, 4, 5, 6)
= lcm (lcm(1, 2, 3, 4, 5), 6)
= lcm (lcm(30, 20, 5), 6)
= lcm (30, 20, 5, 6)
= lcm (30, 20, lcm(5,6), 6) --> lcm (30, 20, 30, 6) = lcm (30, 20x30/(30-20), 30, 6)
= lcm (30, 20, d(1/5 - 1/6), 6)                     = lcm (30, 60, 30, 6)
= lcm (30, 20, d(1/30), 6)                          = lcm (30x60/(60-30), 60, 30, 6)
= lcm (30, 20, 30, 6)                               = lcm (60, 60, 30, 6)
= lcm (30, lcm(20,30), 30, 6)
= lcm (30, d(1/20 - 1/30), 30, 6)
= lcm (30, d(1/60), 30, 6)
= lcm (30, 60, 30, 6)
= lcm (lcm(30, 60), 60, 30, 6)
= lcm (d(1/30 - 1/60), 60, 30, 6)
= lcm (d(1/60), 60, 30, 6)
= lcm (60, 60, 30, 6)
= lcm (60, 30, 6) = lcm (6, 30, 60, 60, 30, 6)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: R^* x y /\ R^* y z ==> R^* x z *)
(* Proof: by RTC_TRANSITIVE, transitive_def *)
val RTC_TRANS = store_thm(
  "RTC_TRANS",
  ``R^* x y /\ R^* y z ==> R^* x z``,
  metis_tac[RTC_TRANSITIVE, transitive_def]);

(* ------------------------------------------------------------------------- *)
(* Leibniz Triangle (Denominator form)                                       *)
(* ------------------------------------------------------------------------- *)

(* Define Leibniz Triangle *)
val leibniz_def = Define`
  leibniz n k = (n + 1) * binomial n k
`;

(* export simple definition *)
val _ = export_rewrites["leibniz_def"];

(* Theorem: leibniz 0 n = if n = 0 then 1 else 0 *)
(* Proof:
     leibniz 0 n
   = (0 + 1) * binomial 0 n     by leibniz_def
   = if n = 0 then 1 else 0     by binomial_n_0
*)
val leibniz_0_n = store_thm(
  "leibniz_0_n",
  ``!n. leibniz 0 n = if n = 0 then 1 else 0``,
  rw[binomial_0_n]);

(* Theorem: leibniz n 0 = n + 1 *)
(* Proof:
     leibniz n 0
   = (n + 1) * binomial n 0     by leibniz_def
   = (n + 1) * 1                by binomial_n_0
   = n + 1
*)
val leibniz_n_0 = store_thm(
  "leibniz_n_0",
  ``!n. leibniz n 0 = n + 1``,
  rw[binomial_n_0]);

(* Theorem: leibniz n n = n + 1 *)
(* Proof:
     leibniz n n
   = (n + 1) * binomial n n     by leibniz_def
   = (n + 1) * 1                by binomial_n_n
   = n + 1
*)
val leibniz_n_n = store_thm(
  "leibniz_n_n",
  ``!n. leibniz n n = n + 1``,
  rw[binomial_n_n]);

(* Theorem: n < k ==> leibniz n k = 0 *)
(* Proof:
     leibniz n k
   = (n + 1) * binomial n k     by leibniz_def
   = (n + 1) * 0                by binomial_less_0
   = 0
*)
val leibniz_less_0 = store_thm(
  "leibniz_less_0",
  ``!n k. n < k ==> (leibniz n k = 0)``,
  rw[binomial_less_0]);

(* Theorem: k <= n ==> (leibniz n k = leibniz n (n-k)) *)
(* Proof:
     leibniz n k
   = (n + 1) * binomial n k       by leibniz_def
   = (n + 1) * binomial n (n-k)   by binomial_sym
   = leibniz n (n-k)              by leibniz_def
*)
val leibniz_sym = store_thm(
  "leibniz_sym",
  ``!n k. k <= n ==> (leibniz n k = leibniz n (n-k))``,
  rw[leibniz_def, GSYM binomial_sym]);

(* Theorem: k < HALF n ==> leibniz n k < leibniz n (k + 1) *)
(* Proof:
   Assume k < HALF n, and note that 0 < (n + 1).
                  leibniz n k < leibniz n (k + 1)
   <=> (n + 1) * binomial n k < (n + 1) * binomial n (k + 1)    by leibniz_def
   <=>           binomial n k < binomial n (k + 1)              by LT_MULT_LCANCEL
   <=>  T                                                       by binomial_monotone
*)
val leibniz_monotone = store_thm(
  "leibniz_monotone",
  ``!n k. k < HALF n ==> leibniz n k < leibniz n (k + 1)``,
  rw[leibniz_def, binomial_monotone]);

(* Theorem: k <= n ==> 0 < leibniz n k *)
(* Proof:
   Since leibniz n k = (n + 1) * binomial n k  by leibniz_def
     and 0 < n + 1, 0 < binomial n k           by binomial_pos
   Hence 0 < leibniz n k                       by ZERO_LESS_MULT
*)
val leibniz_pos = store_thm(
  "leibniz_pos",
  ``!n k. k <= n ==> 0 < leibniz n k``,
  rw[leibniz_def, binomial_pos, ZERO_LESS_MULT, DECIDE``!n. 0 < n + 1``]);

(* Theorem: (leibniz n k = 0) <=> n < k *)
(* Proof:
       leibniz n k = 0
   <=> (n + 1) * (binomial n k = 0)     by leibniz_def
   <=> binomial n k = 0                 by MULT_EQ_0, n + 1 <> 0
   <=> n < k                            by binomial_eq_0
*)
val leibniz_eq_0 = store_thm(
  "leibniz_eq_0",
  ``!n k. (leibniz n k = 0) <=> n < k``,
  rw[leibniz_def, binomial_eq_0]);

(* Theorem: leibniz n = (\j. (n + 1) * j) o (binomial n) *)
(* Proof: by leibniz_def and function equality. *)
val leibniz_alt = store_thm(
  "leibniz_alt",
  ``!n. leibniz n = (\j. (n + 1) * j) o (binomial n)``,
  rw[leibniz_def, FUN_EQ_THM]);

(* Theorem: leibniz n k = (\j. (n + 1) * j) (binomial n k) *)
(* Proof: by leibniz_def *)
val leibniz_def_alt = store_thm(
  "leibniz_def_alt",
  ``!n k. leibniz n k = (\j. (n + 1) * j) (binomial n k)``,
  rw_tac std_ss[leibniz_def]);

(*
Picture of Leibniz Triangle L-corner:
    b = L (n-1) k
    a = L n     k   c = L n (k+1)

a = L n k = (n+1) * (n, k, n-k) = (n+1, k, n-k) = (n+1)! / k! (n-k)!
b = L (n-1) k = n * (n-1, k, n-1-k) = (n , k, n-k-1) = n! / k! (n-k-1)! = a * (n-k)/(n+1)
c = L n (k+1) = (n+1) * (n, k+1, n-(k+1)) = (n+1, k+1, n-k-1) = (n+1)! / (k+1)! (n-k-1)! = a * (n-k)/(k+1)

a * b = a * a * (n-k)/(n+1)
a - b = a - a * (n-k)/(n+1) = a * (1 - (n-k)/(n+1)) = a * (n+1 - n+k)/(n+1) = a * (k+1)/(n+1)
Hence
  a * b /(a - b)
= [a * a * (n-k)/(n+1)] / [a * (k+1)/(n+1)]
= a * (n-k)/(k+1)
= c
or a * b = c * (a - b)
*)

(* Theorem: 0 < n ==> !k. (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k *)
(* Proof:
     (n + 1) * leibniz (n - 1) k
   = (n + 1) * ((n-1 + 1) * binomial (n-1) k)     by leibniz_def
   = (n + 1) * (n * binomial (n-1) k)             by SUB_ADD, 1 <= n.
   = (n + 1) * ((n - k) * (binomial n k))         by binomial_up_eqn
   = ((n + 1) * (n - k)) * binomial n k           by MULT_ASSOC
   = ((n - k) * (n + 1)) * binomial n k           by MULT_COMM
   = (n - k) * ((n + 1) * binomial n k)           by MULT_ASSOC
   = (n - k) * leibniz n k                        by leibniz_def
*)
val leibniz_up_eqn = store_thm(
  "leibniz_up_eqn",
  ``!n. 0 < n ==> !k. (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k``,
  rw[leibniz_def] >>
  `1 <= n` by decide_tac >>
  metis_tac[SUB_ADD, binomial_up_eqn, MULT_ASSOC, MULT_COMM]);

(* Theorem: 0 < n ==> !k. leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1) *)
(* Proof:
   Since  (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k    by leibniz_up_eqn
          leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1)  by DIV_SOLVE, 0 < n+1.
*)
val leibniz_up = store_thm(
  "leibniz_up",
  ``!n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1)``,
  rw[leibniz_up_eqn, DIV_SOLVE]);

(* Theorem: 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k *)
(* Proof:
     leibniz (n - 1) k
   = (n - k) * leibniz n k DIV (n + 1)                  by leibniz_up, 0 < n
   = (n - k) * ((n + 1) * binomial n k) DIV (n + 1)     by leibniz_def
   = (n + 1) * ((n - k) * binomial n k) DIV (n + 1)     by MULT_ASSOC, MULT_COMM
   = (n - k) * binomial n k                             by MULT_DIV, 0 < n + 1
*)
val leibniz_up_alt = store_thm(
  "leibniz_up_alt",
  ``!n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k``,
  metis_tac[leibniz_up, leibniz_def, MULT_DIV, MULT_ASSOC, MULT_COMM, DECIDE``0 < x + 1``]);

(* Theorem: 0 < n ==> !k. (k + 1) * leibniz n (k+1) = (n - k) * leibniz n k *)
(* Proof:
     (k + 1) * leibniz n (k+1)
   = (k + 1) * ((n + 1) * binomial n (k+1))   by leibniz_def
   = (k + 1) * (n + 1) * binomial n (k+1)     by MULT_ASSOC
   = (n + 1) * (k + 1) * binomial n (k+1)     by MULT_COMM
   = (n + 1) * ((k + 1) * binomial n (k+1))   by MULT_ASSOC
   = (n + 1) * ((n - k) * (binomial n k))     by binomial_right_eqn
   = ((n + 1) * (n - k)) * binomial n k       by MULT_ASSOC
   = ((n - k) * (n + 1)) * binomial n k       by MULT_COMM
   = (n - k) * ((n + 1) * binomial n k)       by MULT_ASSOC
   = (n - k) * leibniz n k                    by leibniz_def
*)
val leibniz_right_eqn = store_thm(
  "leibniz_right_eqn",
  ``!n. 0 < n ==> !k. (k + 1) * leibniz n (k+1) = (n - k) * leibniz n k``,
  metis_tac[leibniz_def, MULT_COMM, MULT_ASSOC, binomial_right_eqn]);

(* Theorem: 0 < n ==> !k. leibniz n (k+1) = (n - k) * (leibniz n k) DIV (k + 1) *)
(* Proof:
   Since  (k + 1) * leibniz n (k+1) = (n - k) * leibniz n k    by leibniz_right_eqn
          leibniz n (k+1) = (n - k) * (leibniz n k) DIV (k+1)  by DIV_SOLVE, 0 < k+1.
*)
val leibniz_right = store_thm(
  "leibniz_right",
  ``!n. 0 < n ==> !k. leibniz n (k+1) = (n - k) * (leibniz n k) DIV (k+1)``,
  rw[leibniz_right_eqn, DIV_SOLVE]);

(* Note: Following is the property from Leibniz Harmonic Triangle:
   1 / leibniz n (k+1) = 1 / leibniz (n-1) k  - 1 / leibniz n k
                       = (leibniz n k - leibniz (n-1) k) / leibniz n k * leibniz (n-1) k
*)

(* The Idea:
                                                b
Actually, lcm a b = lcm b c = lcm c a     for   a c  in Leibniz Triangle.
The only relationship is: c = ab/(a - b), or ab = c(a - b).

Is this a theorem:  ab = c(a - b)  ==> lcm a b = lcm b c = lcm c a
Or in fractions,   1/c = 1/b - 1/a ==> lcm a b = lcm b c = lcm c a ?

lcm a b
= a b / (gcd a b)
= c(a - b) / (gcd a (a - b))
= ac(a - b) / gcd a (a-b) / a
= lcm (a (a-b)) c / a
= lcm (ca c(a-b)) / a
= lcm (ca ab) / a
= lcm (b c)

lcm a b = a b / gcd a b = a b / gcd a (a-b) = a b c / gcd ca c(a-b)
= c (a-b) c / gcd ca c(a-b) = lcm ca c(a-b) / a = lcm ca ab / a = lcm b c

  lcm b c
= b c / gcd b c
= a b c / gcd a*b a*c
= a b c / gcd c*(a-b) c*a
= a b / gcd (a-b) a
= a b / gcd b a
= lcm (a b)
= lcm a b

  lcm a c
= a c / gcd a c
= a b c / gcd b*a b*c
= a b c / gcd c*(a-b) b*c
= a b / gcd (a-b) b
= a b / gcd a b
= lcm a b

Yes!

This is now in LCM_EXCHANGE:
val it = |- !a b c. (a * b = c * (a - b)) ==> (lcm a b = lcm a c): thm
*)

(* Theorem: 0 < n ==>
   !k. leibniz n k * leibniz (n-1) k = leibniz n (k+1) * (leibniz n k - leibniz (n-1) k) *)
(* Proof:
   If n <= k,
      then  n-1 < k, and n < k+1.
      so    leibniz (n-1) k = 0         by leibniz_less_0, n-1 < k.
      and   leibniz n (k+1) = 0         by leibniz_less_0, n < k+1.
      Hence true                        by MULT_EQ_0
   Otherwise, k < n, or k <= n.
      then  (n+1) - (n-k) = k+1.

        (k + 1) * (c * (a - b))
      = (k + 1) * c * (a - b)                   by MULT_ASSOC
      = ((n+1) - (n-k)) * c * (a - b)           by above
      = (n - k) * a * (a - b)                   by leibniz_right_eqn
      = (n - k) * a * a - (n - k) * a * b       by LEFT_SUB_DISTRIB
      = (n + 1) * b * a - (n - k) * a * b       by leibniz_up_eqn
      = (n + 1) * (a * b) - (n - k) * (a * b)   by MULT_ASSOC, MULT_COMM
      = ((n+1) - (n-k)) * (a * b)               by RIGHT_SUB_DISTRIB
      = (k + 1) * (a * b)                       by above

      Since (k+1) <> 0, the result follows      by MULT_LEFT_CANCEL
*)
val leibniz_property = store_thm(
  "leibniz_property",
  ``!n. 0 < n ==>
   !k. leibniz n k * leibniz (n-1) k = leibniz n (k+1) * (leibniz n k - leibniz (n-1) k)``,
  rpt strip_tac >>
  Cases_on `n <= k` >-
  rw[leibniz_less_0] >>
  `(n+1) - (n-k) = k+1` by decide_tac >>
  `(k+1) <> 0` by decide_tac >>
  qabbrev_tac `a = leibniz n k` >>
  qabbrev_tac `b = leibniz (n - 1) k` >>
  qabbrev_tac `c = leibniz n (k + 1)` >>
  `(k + 1) * (c * (a - b)) = ((n+1) - (n-k)) * c * (a - b)` by rw_tac std_ss[MULT_ASSOC] >>
  `_ = (n - k) * a * (a - b)` by rw_tac std_ss[leibniz_right_eqn, Abbr`c`, Abbr`a`] >>
  `_ = (n - k) * a * a - (n - k) * a * b` by rw_tac std_ss[LEFT_SUB_DISTRIB] >>
  `_ = (n + 1) * b * a - (n - k) * a * b` by rw_tac std_ss[leibniz_up_eqn, Abbr`b`, Abbr`a`] >>
  `_ = (n + 1) * (a * b) - (n - k) * (a * b)` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `_ = ((n+1) - (n-k)) * (a * b)` by rw_tac std_ss[RIGHT_SUB_DISTRIB] >>
  `_ = (k + 1) * (a * b)` by rw_tac std_ss[] >>
  metis_tac[MULT_LEFT_CANCEL]);

(* Theorem: k <= n ==> (leibniz n k = (n + 1) * FACT n DIV (FACT k * FACT (n - k))) *)
(* Proof:
   Note  (FACT k * FACT (n - k)) divides (FACT n)       by binomial_is_integer
    and  0 < FACT k * FACT (n - k)                      by FACT_LESS, ZERO_LESS_MULT
     leibniz n k
   = (n + 1) * binomial n k                             by leibniz_def
   = (n + 1) * (FACT n DIV (FACT k * FACT (n - k)))     by binomial_formula3
   = (n + 1) * FACT n DIV (FACT k * FACT (n - k))       by MULTIPLY_DIV
*)
val leibniz_formula = store_thm(
  "leibniz_formula",
  ``!n k. k <= n ==> (leibniz n k = (n + 1) * FACT n DIV (FACT k * FACT (n - k)))``,
  metis_tac[leibniz_def, binomial_formula3, binomial_is_integer, FACT_LESS, MULTIPLY_DIV, ZERO_LESS_MULT]);

(* Theorem: 0 < n ==>
   !k. k < n ==> leibniz n (k+1) = leibniz n k * leibniz (n-1) k DIV (leibniz n k - leibniz (n-1) k) *)
(* Proof:
   By leibniz_property,
   leibniz n (k+1) * (leibniz n k - leibniz (n-1) k) = leibniz n k * leibniz (n-1) k
   Since 0 < leibniz n k and 0 < leibniz (n-1) k     by leibniz_pos
      so 0 < (leibniz n k - leibniz (n-1) k)         by MULT_EQ_0
   Hence by MULT_COMM, DIV_SOLVE, 0 < (leibniz n k - leibniz (n-1) k),
   leibniz n (k+1) = leibniz n k * leibniz (n-1) k DIV (leibniz n k - leibniz (n-1) k)
*)
val leibniz_recurrence = store_thm(
  "leibniz_recurrence",
  ``!n. 0 < n ==>
   !k. k < n ==> (leibniz n (k+1) = leibniz n k * leibniz (n-1) k DIV (leibniz n k - leibniz (n-1) k))``,
  rpt strip_tac >>
  `k <= n /\ k <= (n-1)` by decide_tac >>
  `leibniz n (k+1) * (leibniz n k - leibniz (n-1) k) = leibniz n k * leibniz (n-1) k` by rw[leibniz_property] >>
  `0 < leibniz n k /\ 0 < leibniz (n-1) k` by rw[leibniz_pos] >>
  `0 < (leibniz n k - leibniz (n-1) k)` by metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  rw_tac std_ss[DIV_SOLVE, MULT_COMM]);

(* Theorem: 0 < k /\ k <= n ==>
   (leibniz n k = leibniz n (k-1) * leibniz (n-1) (k-1) DIV (leibniz n (k-1) - leibniz (n-1) (k-1))) *)
(* Proof:
   Since 0 < k, k = SUC h     for some h
      or k = h + 1            by ADD1
     and h = k - 1            by arithmetic
   Since 0 < k and k <= n,
         0 < n and h < n.
   Hence true by leibniz_recurrence.
*)
val leibniz_n_k = store_thm(
  "leibniz_n_k",
  ``!n k. 0 < k /\ k <= n ==>
   (leibniz n k = leibniz n (k-1) * leibniz (n-1) (k-1) DIV (leibniz n (k-1) - leibniz (n-1) (k-1)))``,
  rpt strip_tac >>
  `?h. k = h + 1` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO, ADD1] >>
  `(h = k - 1) /\ h < n /\ 0 < n` by decide_tac >>
  metis_tac[leibniz_recurrence]);

(* Theorem: 0 < n ==>
   !k. lcm (leibniz n k) (leibniz (n-1) k) = lcm (leibniz n k) (leibniz n (k+1)) *)
(* Proof:
   By leibniz_property,
   leibniz n k * leibniz (n - 1) k = leibniz n (k + 1) * (leibniz n k - leibniz (n - 1) k)
   Hence true by LCM_EXCHANGE.
*)
val leibniz_lcm_exchange = store_thm(
  "leibniz_lcm_exchange",
  ``!n. 0 < n ==> !k. lcm (leibniz n k) (leibniz (n-1) k) = lcm (leibniz n k) (leibniz n (k+1))``,
  rw[leibniz_property, LCM_EXCHANGE]);

(* Theorem: 4 ** n <= leibniz (2 * n) n *)
(* Proof:
   Let m = 2 * n.
   Then n = HALF m                              by HALF_TWICE
   Let l1 = GENLIST (K (binomial m n)) (m + 1)
   and l2 = GENLIST (binomial m) (m + 1)
   Note LENGTH l1 = LENGTH l2 = m + 1           by LENGTH_GENLIST

   Claim: !k. k < m + 1 ==> EL k l2 <= EL k l1
   Proof: Note EL k l1 = binomial m n           by EL_GENLIST
           and EL k l2 = binomial m k           by EL_GENLIST
         Apply binomial m k <= binomial m n     by binomial_max
           The result follows

     leibniz m n
   = (m + 1) * binomial m n                     by leibniz_def
   = SUM (GENLIST (K (binomial m n)) (m + 1))   by SUM_GENLIST_K
   >= SUM (GENLIST (\k. binomial m k) (m + 1))  by SUM_LE, above
    = SUM (GENLIST (binomial m) (SUC m))        by ADD1
    = 2 ** m                                    by binomial_sum
    = 2 ** (2 * n)                              by notation
    = (2 ** 2) ** n                             by EXP_EXP_MULT
    = 4 ** n                                    by arithmetic
*)
val leibniz_middle_lower = store_thm(
  "leibniz_middle_lower",
  ``!n. 4 ** n <= leibniz (2 * n) n``,
  rpt strip_tac >>
  qabbrev_tac `m = 2 * n` >>
  `n = HALF m` by rw[HALF_TWICE, Abbr`m`] >>
  qabbrev_tac `l1 = GENLIST (K (binomial m n)) (m + 1)` >>
  qabbrev_tac `l2 = GENLIST (binomial m) (m + 1)` >>
  `!k. k < m + 1 ==> EL k l2 <= EL k l1` by rw[binomial_max, EL_GENLIST, Abbr`l1`, Abbr`l2`] >>
  `leibniz m n = (m + 1) * binomial m n` by rw[leibniz_def] >>
  `_ = SUM l1` by rw[SUM_GENLIST_K, Abbr`l1`] >>
  `SUM l2 = SUM (GENLIST (binomial m) (SUC m))` by rw[ADD1, Abbr`l2`] >>
  `_ = 2 ** m` by rw[binomial_sum] >>
  `_ = 4 ** n` by rw[EXP_EXP_MULT, Abbr`m`] >>
  metis_tac[SUM_LE, LENGTH_GENLIST]);

(* ------------------------------------------------------------------------- *)
(* Property of Leibniz Triangle                                              *)
(* ------------------------------------------------------------------------- *)

(*
binomial_recurrence |- !n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)
This means:
           B n k  + B n  k*
                       v
                    B n* k*
However, for the Leibniz Triangle, the recurrence is:
           L n k
           L n* k  -> L n* k* = (L n* k)(L n k) / (L n* k - L n k)
That is, it takes a different style, and has the property:
                    1 / L n* k* = 1 / L n k - 1 / L n* k
Why?
First, some verification.
Pascal:     [1]  3   3
                [4]  6 = 3 + 3 = 6
Leibniz:        12  12
               [20] 30 = 20 * 12 / (20 - 12) = 20 * 12 / 8 = 30
Now, the 20 comes from 4 = 3 + 1.
Originally,  30 = 5 * 6          by definition based on multiple
                = 5 * (3 + 3)    by Pascal
                = 4 * (3 + 3) + (3 + 3)
                = 12 + 12 + 6
In terms of factorials,  30 = 5 * 6 = 5 * B(4,2) = 5 * 4!/2!2!
                         20 = 5 * 4 = 5 * B(4,1) = 5 * 4!/1!3!
                         12 = 4 * 3 = 4 * B(3,1) = 4 * 3!/1!2!
So  1/30 = (2!2!)/(5 4!)     1 / n** B n* k* = k*! (n* - k* )! / n** n*! = (n - k)! k*! / n**!
    1/20 = (1!3!)/(5 4!)     1 / n** B n* k
    1/12 = (1!2!)/(4 3!)     1 / n* B n k
    1/12 - 1/20
  = (1!2!)/(4 3!) - (1!3!)/(5 4!)
  = (1!2!)/4! - (1!3!)/5!
  = 5(1!2!)/5! - (1!3!)/5!
  = (5(1!2!) - (1!3!))/5!
  = (5 1! - 3 1!) 2!/5!
  = (5 - 3)1! 2!/5!
  = 2! 2! / 5!

    1 / n B n k - 1 / n** B n* k
  = k! (n-k)! / n* n! - k! (n* - k)! / n** n*!
  = k! (n-k)! / n*! - k!(n* - k)! / n** n*!
  = (n** (n-k)! - (n* - k)!) k! / n** n*!
  = (n** - (n* - k)) (n - k)! k! / n** n*!
  = (k+1) (n - k)! k! / n** n*!
  = (n* - k* )! k*! / n** n*!
  = 1 / n** B n* k*

Direct without using unit fractions,

L n k = n* B n k = n* n! / k! (n-k)! = n*! / k! (n-k)!
L n* k = n** B n* k = n** n*! / k! (n* - k)! = n**! / k! (n* - k)!
L n* k* = n** B n* k* = n** n*! / k*! (n* - k* )! = n**! / k*! (n-k)!

(L n* k) * (L n k) = n**! n*! / k! (n* - k)! k! (n-k)!
(L n* k) - (L n k) = n**! / k! (n* - k)! - n*! / k! (n-k)!
                   = n**! / k! (n-k)!( 1/(n* - k) - 1/ n** )
                   = n**! / k! (n-k)! (n** - n* + k)/(n* - k)(n** )
                   = n**! / k! (n-k)! k* / (n* - k) n**
                   = n*! k* / k! (n* - k)!
(L n* k) * (L n k) / (L n* k) - (L n k)
= n**! /k! (n-k)! k*
= n**! /k*! (n-k)!
= L n* k*
So:    L n k
       L n* k --> L n* k*

Can the LCM be shown directly?
lcm (L n* k, L n k) = lcm (L n* k, L n* k* )
To prove this, need to show:
both have the same common multiples, and least is the same -- probably yes due to common L n* k.

In general, what is the condition for   lcm a b = lcm a c ?
Well,  lcm a b = a b / gcd a b,  lcm a c = a c / gcd a c
So it must be    a b gcd a c = a c gcd a b, or b * gcd a c = c * gcd a b.

It this true for Leibniz triangle?
Let a = 5, b = 4, c = 20.  b * gcd a c = 4 * gcd 5 20 = 4 * 5 = 20
                           c * gcd a b = 20 * gcd 5 4 = 20
Verify lcm a b = lcm 5 4 = 20 = 5 * 4 / gcd 5 4
       lcm a c = lcm 5 20 = 20 = 5 * 20 / gcd 5 20
       5 * 4 / gcd 5 4 = 5 * 20 / gcd 5 20
or        4 * gcd 5 20 = 20 * gcd 5 4

(L n k) * gcd (L n* k, L n* k* ) = (L n* k* ) * gcd (L n* k, L n k)

or n* B n k * gcd (n** B n* k, n** B n* k* ) = (n** B n* k* ) * gcd (n** B n* k, n* B n k)
By GCD_COMMON_FACTOR, !m n k. gcd (k * m) (k * n) = k * gcd m n
   n** n* B n k gcd (B n* k, B n* k* ) = (n** B n* k* ) * gcd (n** B n* k, n* B n k)
*)

(* Special Property of Leibniz Triangle
For:    L n k
        L n+ k --> L n+ k+

L n k  = n+! / k! (n-k)!
L n+ k = n++! / k! (n+ - k)! = n++ n+! / k! (n+ - k) k! = (n++ / n+ - k) L n k
L n+ k+ = n++! / k+! (n-k)! = (L n+ k) * (L n k) / (L n+ k - L n k) = (n++ / k+) L n k
Let g = gcd (L n+ k) (L n k), then L n+ k+ = lcm (L n+ k) (L n k) / (co n+ k - co n k)
where co n+ k = L n+ k / g, co n k = L n k / g.

    L n+ k = (n++ / n+ - k) L n k,
and L n+ k+ = (n++ / k+) L n k
e.g. L 3 1 = 12
     L 4 1 = 20, or (3++ / 3+ - 1) L 3 1 = (5/3) 12 = 20.
     L 4 2 = 30, or (3++ / 1+) L 3 1 = (5/2) 12 = 30.
so lcm (L 4 1) (L 3 1) = lcm (5/3)*12 12 = 12 * 5 = 60   since 3 must divide 12.
   lcm (L 4 1) (L 4 2) = lcm (5/3)*12 (5/2)*12 = 12 * 5 = 60  since 3, 2 must divide 12.

By LCM_COMMON_FACTOR |- !m n k. lcm (k * m) (k * n) = k * lcm m n
lcm a (a * b DIV c) = a * b

So the picture is:     (L n k)
                       (L n k) * (n+2)/(n-k+1)   (L n k) * (n+2)/(k+1)

A better picture:
Pascal:       (B n-1 k) = (n-1, k, n-k-1)
              (B n k)   = (n, k, n-k)     (B n k+1) = (n, k+1, n-k-1)
Leibniz:      (L n-1 k) = (n, k, n-k-1) = (L n k) / (n+1) * (n-k-1)
              (L n k)   = (n+1, k, n-k)   (L n k+1) = (n+1, k+1, n-k-1) = (L n k) / (n-k-1) * (k+1)
And we want:
    LCM (L, (n-k-1) * L DIV (n+1)) = LCM (L, (k+1) * L DIV (n-k-1)).

Theorem:   lcm a ((a * b) DIV c) = (a * b) DIV (gcd b c)
Assume this theorem,
LHS = L * (n-k-1) DIV gcd (n-k-1, n+1)
RHS = L * (k+1) DIV gcd (k+1, n-k-1)
Still no hope to show LHS = RHS !

LCM of fractions:
lcm (a/c, b/c) = lcm(a, b)/c
lcm (a/c, b/d) = ... = lcm(a, b)/gcd(c, d)
Hence lcm (a, a*b/c) = lcm(a*b/b, a*b/c) = a * b / gcd (b, c)
*)

(* Special Property of Leibniz Triangle -- another go
Leibniz:    L(5,1) = 30 = b
            L(6,1) = 42 = a   L(6,2) = 105 = c,  c = ab/(a - b), or ab = c(a - b)
Why is LCM 42 30 = LCM 42 105 = 210 = 2x3x5x7?
First, b = L(5,1) = 30 = (6,1,4) = 6!/1!4! = 7!/1!5! * (5/7) = a * (5/7) = 2x3x5
       a = L(6,1) = 42 = (7,1,5) = 7!/1!5! = 2x3x7 = b * (7/5) = c * (2/5)
       c = L(6,2) = 105 = (7,2,4) = 7!/2!4! = 7!/1!5! * (5/2) = a * (5/2) = 3x5x7
Any common multiple of a, b must have 5, 7 as factor, also with factor 2 (by common k = 1)
Any common multiple of a, c must have 5, 2 as factor, also with factor 7 (by common n = 6)
Also n = 5 implies a factor 6, k = 2 imples a factor 2.
LCM a b = a b / GCD a b
        = c (a - b) / GCD a b
        = (m c') (m a' - (m-1)b') / GCD (m a') (m-1 b')
LCM a c = a c / GCD a c
        = (m a') (m c') / GCD (m a') (m c')     where c' = a' + b' from Pascal triangle
        = m a' (a' + b') / GCD a' (a' + b')
        = m a' (a' + b') / GCD a' b'
        = a' c / GCD a' b'
Can we prove:    c(a - b) / GCD a b = c a' / GCD a' b'
or                 (a - b) GCD a' b' = a' GCD a b ?
or                a GCD a' b' = a' GCD a b + b GCD a' b' ?
or                    ab GCD a' b' = c a' GCD a b?
or                    m (b GCD a' b') = c GCD a b?
or                       b GCD a' b' = c' GCD a b?
b = (a DIV 7) * 5
c = (a DIV 2) * 5
lcm (a, b) = lcm (a, (a DIV 7) * 5) = lcm (a, 5)
lcm (a, c) = lcm (a, (a DIV 2) * 5) = lcm (a, 5)
Is this a theorem: lcm (a, (a DIV p) * b) = lcm (a, b) if p | a ?
Let c = lcm (a, b). Then a | c, b | c.
Since a = (a DIV p) * p, (a DIV p) * p | c.
Hence  ((a DIV p) * b) * p | b * c.
How to conclude ((a DIV p) * b) | c?

A counter-example:
lcm (42, 9) = 126 = 2x3x3x7.
lcm (42, (42 DIV 3) * 9) = 126 = 2x3x3x7.
lcm (42, (42 DIV 6) * 9) = 126 = 2x3x3x7.
lcm (42, (42 DIV 2) * 9) = 378 = 2x3x3x3x7.
lcm (42, (42 DIV 7) * 9) = 378 = 2x3x3x3x7.

LCM a c
= LCM a (ab/(a-b))    let g = GCD(a,b), a = gA, b=gB, coprime A,B.
= LCM gA gAB/(A-B)
= g LCM A AB/(A-B)
= (ab/LCM a b) LCM A AB/(A-B)
*)

(* ------------------------------------------------------------------------- *)
(* LCM of a list of numbers                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define LCM of a list of numbers *)
val list_lcm_def = Define`
  (list_lcm [] = 1) /\
  (list_lcm (h::t) = lcm h (list_lcm t))
`;

(* export simple definition *)
val _ = export_rewrites["list_lcm_def"];

(* Theorem: list_lcm [] = 1 *)
(* Proof: by list_lcm_def. *)
val list_lcm_nil = store_thm(
  "list_lcm_nil",
  ``list_lcm [] = 1``,
  rw[]);

(* Theorem: list_lcm (h::t) = lcm h (list_lcm t) *)
(* Proof: by list_lcm_def. *)
val list_lcm_cons = store_thm(
  "list_lcm_cons",
  ``!h t. list_lcm (h::t) = lcm h (list_lcm t)``,
  rw[]);

(* Theorem: list_lcm [x] = x *)
(* Proof:
     list_lcm [x]
   = lcm x (list_lcm [])    by list_lcm_cons
   = lcm x 1                by list_lcm_nil
   = x                      by LCM_1
*)
val list_lcm_sing = store_thm(
  "list_lcm_sing",
  ``!x. list_lcm [x] = x``,
  rw[]);

(* Theorem: list_lcm (SNOC x l) = list_lcm (x::l) *)
(* Proof:
   By induction on l.
   Base case: list_lcm (SNOC x []) = lcm x (list_lcm [])
     list_lcm (SNOC x [])
   = list_lcm [x]           by SNOC
   = lcm x (list_lcm [])    by list_lcm_def
   Step case: list_lcm (SNOC x l) = lcm x (list_lcm l) ==>
              !h. list_lcm (SNOC x (h::l)) = lcm x (list_lcm (h::l))
     list_lcm (SNOC x (h::l))
   = list_lcm (h::SNOC x l)        by SNOC
   = lcm h (list_lcm (SNOC x l))   by list_lcm_def
   = lcm h (lcm x (list_lcm l))    by induction hypothesis
   = lcm x (lcm h (list_lcm l))    by LCM_ASSOC_COMM
   = lcm x (list_lcm h::l)         by list_lcm_def
*)
val list_lcm_snoc = store_thm(
  "list_lcm_snoc",
  ``!x l. list_lcm (SNOC x l) = lcm x (list_lcm l)``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[LCM_ASSOC_COMM]);

(* Theorem: list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l *)
(* Proof:
   By induction on l.
   Base case: !n. list_lcm (MAP (\k. n * k) []) = if [] = [] then 1 else n * list_lcm []
       list_lcm (MAP (\k. n * k) [])
     = list_lcm []                      by MAP
     = 1                                by list_lcm_nil
   Step case: !n. list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l ==>
              !h n. list_lcm (MAP (\k. n * k) (h::l)) = if h::l = [] then 1 else n * list_lcm (h::l)
     Note h::l <> []                    by NOT_NIL_CONS
     If l = [], h::l = [h]
       list_lcm (MAP (\k. n * k) [h])
     = list_lcm [n * h]                 by MAP
     = n * h                            by list_lcm_sing
     = n * list_lcm [h]                 by list_lcm_sing
     If l <> [],
       list_lcm (MAP (\k. n * k) (h::l))
     = list_lcm ((n * h) :: MAP (\k. n * k) l)      by MAP
     = lcm (n * h) (list_lcm (MAP (\k. n * k) l))   by list_lcm_cons
     = lcm (n * h) (n * list_lcm l)                 by induction hypothesis
     = n * (lcm h (list_lcm l))                     by LCM_COMMON_FACTOR
     = n * list_lcm (h::l)                          by list_lcm_cons
*)
val list_lcm_map_times = store_thm(
  "list_lcm_map_times",
  ``!n l. list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l``,
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  rw_tac std_ss[LCM_COMMON_FACTOR, MAP, list_lcm_cons]);

(* Theorem: EVERY_POSITIVE l ==> 0 < list_lcm l *)
(* Proof:
   By induction on l.
   Base case: EVERY_POSITIVE [] ==> 0 < list_lcm []
     Note  EVERY_POSITIVE [] = T      by EVERY_DEF
     Since list_lcm [] = 1            by list_lcm_nil
     Hence true since 0 < 1           by SUC_POS, ONE.
   Step case: EVERY_POSITIVE l ==> 0 < list_lcm l ==>
              !h. EVERY_POSITIVE (h::l) ==> 0 < list_lcm (h::l)
     Note EVERY_POSITIVE (h::l)
      ==> 0 < h and EVERY_POSITIVE l              by EVERY_DEF
     Since list_lcm (h::l) = lcm h (list_lcm l)   by list_lcm_cons
       and 0 < list_lcm l                         by induction hypothesis
        so h <= lcm h (list_lcm l)                by LCM_LE, 0 < h.
     Hence 0 < list_lcm (h::l)                    by LESS_LESS_EQ_TRANS
*)
val list_lcm_pos = store_thm(
  "list_lcm_pos",
  ``!l. EVERY_POSITIVE l ==> 0 < list_lcm l``,
  Induct >-
  rw[] >>
  metis_tac[EVERY_DEF, list_lcm_cons, LCM_LE, LESS_LESS_EQ_TRANS]);

(* Theorem: POSITIVE l ==> 0 < list_lcm l *)
(* Proof: by list_lcm_pos, EVERY_MEM *)
val list_lcm_pos_alt = store_thm(
  "list_lcm_pos_alt",
  ``!l. POSITIVE l ==> 0 < list_lcm l``,
  rw[list_lcm_pos, EVERY_MEM]);

(* Theorem: EVERY_POSITIVE l ==> SUM l <= (LENGTH l) * list_lcm l *)
(* Proof:
   By induction on l.
   Base case: EVERY_POSITIVE [] ==> SUM [] <= LENGTH [] * list_lcm []
     Note EVERY_POSITIVE [] = T      by EVERY_DEF
     Since SUM [] = 0                by SUM
       and LENGTH [] = 0             by LENGTH_NIL
     Hence true by MULT, as 0 <= 0   by LESS_EQ_REFL
   Step case: EVERY_POSITIVE l ==> SUM l <= LENGTH l * list_lcm l ==>
              !h. EVERY_POSITIVE (h::l) ==> SUM (h::l) <= LENGTH (h::l) * list_lcm (h::l)
     Note EVERY_POSITIVE (h::l)
      ==> 0 < h and EVERY_POSITIVE l          by EVERY_DEF
      ==> 0 < h and 0 < list_lcm l            by list_lcm_pos
     If l = [], LENGTH l = 0.
     SUM (h::[]) = SUM [h] = h                by SUM
       LENGTH (h::[]) * list_lcm (h::[])
     = 1 * list_lcm [h]                       by ONE
     = 1 * h                                  by list_lcm_sing
     = h                                      by MULT_LEFT_1
     If l <> [], LENGTH l <> 0                by LENGTH_NIL ... [1]
     SUM (h::l)
   = h + SUM l                                by SUM
   <= h + LENGTH l * list_lcm l               by induction hypothesis
   <= lcm h (list_lcm l) + LENGTH l * list_lcm l            by LCM_LE, 0 < h
   <= lcm h (list_lcm l) + LENGTH l * (lcm h (list_lcm l))  by LCM_LE, 0 < list_lcm l, [1]
   = (1 + LENGTH l) * (lcm h (list_lcm l))    by RIGHT_ADD_DISTRIB
   = SUC (LENGTH l) * (lcm h (list_lcm l))    by SUC_ONE_ADD
   = LENGTH (h::l) * (lcm h (list_lcm l))     by LENGTH
   = LENGTH (h::l) * list_lcm (h::l)          by list_lcm_cons
*)
val list_lcm_lower_bound = store_thm(
  "list_lcm_lower_bound",
  ``!l. EVERY_POSITIVE l ==> SUM l <= (LENGTH l) * list_lcm l``,
  Induct >>
  rw[] >>
  Cases_on `l = []` >-
  rw[] >>
  `lcm h (list_lcm l) + LENGTH l * (lcm h (list_lcm l)) = SUC (LENGTH l) * (lcm h (list_lcm l))` by rw[RIGHT_ADD_DISTRIB, SUC_ONE_ADD] >>
  `LENGTH l <> 0` by metis_tac[LENGTH_NIL] >>
  `0 < list_lcm l` by rw[list_lcm_pos] >>
  `h <= lcm h (list_lcm l) /\ list_lcm l <= lcm h (list_lcm l)` by rw[LCM_LE] >>
  `LENGTH l * list_lcm l <= LENGTH l * (lcm h (list_lcm l))` by rw[LE_MULT_LCANCEL] >>
  `h + SUM l <= h + LENGTH l * list_lcm l` by rw[] >>
  decide_tac);

(* Another version to eliminate EVERY by MEM. *)
val list_lcm_lower_bound_alt = save_thm("list_lcm_lower_bound_alt",
    list_lcm_lower_bound |> SIMP_RULE (srw_ss()) [EVERY_MEM]);
(* > list_lcm_lower_bound_alt;
val it = |- !l. POSITIVE l ==> SUM l <= LENGTH l * list_lcm l: thm
*)

(* Theorem: list_lcm l is a common multiple of its members.
            MEM x l ==> x divides (list_lcm l) *)
(* Proof:
   By induction on l.
   Base case: !x. MEM x [] ==> x divides (list_lcm [])
     True since MEM x [] = F     by MEM
   Step case: !x. MEM x l ==> x divides (list_lcm l) ==>
              !h x. MEM x (h::l) ==> x divides (list_lcm (h::l))
     Note MEM x (h::l) <=> x = h, or MEM x l       by MEM
      and list_lcm (h::l) = lcm h (list_lcm l)     by list_lcm_cons
     If x = h,
        divides h (lcm h (list_lcm l)) is true     by LCM_IS_LEAST_COMMON_MULTIPLE
     If MEM x l,
        x divides (list_lcm l)                     by induction hypothesis
        (list_lcm l) divides (lcm h (list_lcm l))  by LCM_IS_LEAST_COMMON_MULTIPLE
        Hence x divides (lcm h (list_lcm l))       by DIVIDES_TRANS
*)
val list_lcm_is_common_multiple = store_thm(
  "list_lcm_is_common_multiple",
  ``!x l. MEM x l ==> x divides (list_lcm l)``,
  Induct_on `l` >>
  rw[] >>
  metis_tac[LCM_IS_LEAST_COMMON_MULTIPLE, DIVIDES_TRANS]);

(* Theorem: If m is a common multiple of members of l, (list_lcm l) divides m.
           (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m *)
(* Proof:
   By induction on l.
   Base case: !m. (!x. MEM x [] ==> x divides m) ==> divides (list_lcm []) m
     Since list_lcm [] = 1       by list_lcm_nil
       and divides 1 m is true   by ONE_DIVIDES_ALL
   Step case: !m. (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m ==>
              !h m. (!x. MEM x (h::l) ==> x divides m) ==> divides (list_lcm (h::l)) m
     Note MEM x (h::l) <=> x = h, or MEM x l       by MEM
      and list_lcm (h::l) = lcm h (list_lcm l)     by list_lcm_cons
     Put x = h,   divides h m                      by MEM h (h::l) = T
     Put MEM x l, x divides m                      by MEM x (h::l) = T
         giving   (list_lcm l) divides m           by induction hypothesis
     Hence        divides (lcm h (list_lcm l)) m   by LCM_IS_LEAST_COMMON_MULTIPLE
*)
val list_lcm_is_least_common_multiple = store_thm(
  "list_lcm_is_least_common_multiple",
  ``!l m. (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m``,
  Induct >-
  rw[] >>
  rw[LCM_IS_LEAST_COMMON_MULTIPLE]);

(*
> EVAL ``list_lcm []``;
val it = |- list_lcm [] = 1: thm
> EVAL ``list_lcm [1; 2; 3]``;
val it = |- list_lcm [1; 2; 3] = 6: thm
> EVAL ``list_lcm [1; 2; 3; 4; 5]``;
val it = |- list_lcm [1; 2; 3; 4; 5] = 60: thm
> EVAL ``list_lcm (GENLIST SUC 5)``;
val it = |- list_lcm (GENLIST SUC 5) = 60: thm
> EVAL ``list_lcm (GENLIST SUC 4)``;
val it = |- list_lcm (GENLIST SUC 4) = 12: thm
> EVAL ``lcm 5 (list_lcm (GENLIST SUC 4))``;
val it = |- lcm 5 (list_lcm (GENLIST SUC 4)) = 60: thm
> EVAL ``SNOC 5 (GENLIST SUC 4)``;
val it = |- SNOC 5 (GENLIST SUC 4) = [1; 2; 3; 4; 5]: thm
> EVAL ``list_lcm (SNOC 5 (GENLIST SUC 4))``;
val it = |- list_lcm (SNOC 5 (GENLIST SUC 4)) = 60: thm
> EVAL ``GENLIST (\k. leibniz 5 k) (SUC 5)``;
val it = |- GENLIST (\k. leibniz 5 k) (SUC 5) = [6; 30; 60; 60; 30; 6]: thm
> EVAL ``list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5))``;
val it = |- list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5)) = 60: thm
> EVAL ``list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5))``;
val it = |- (list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5))) <=> T: thm
> EVAL ``list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (leibniz 5) (SUC 5))``;
val it = |- (list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (leibniz 5) (SUC 5))) <=> T: thm
*)

(* Theorem: list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2) *)
(* Proof:
   By induction on l1.
   Base: !l2. list_lcm ([] ++ l2) = lcm (list_lcm []) (list_lcm l2)
      LHS = list_lcm ([] ++ l2)
          = list_lcm l2                      by APPEND
          = lcm 1 (list_lcm l2)              by LCM_1
          = lcm (list_lcm []) (list_lcm l2)  by list_lcm_nil
          = RHS
   Step:  !l2. list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2) ==>
          !h l2. list_lcm (h::l1 ++ l2) = lcm (list_lcm (h::l1)) (list_lcm l2)
        list_lcm (h::l1 ++ l2)
      = list_lcm (h::(l1 ++ l2))                   by APPEND
      = lcm h (list_lcm (l1 ++ l2))                by list_lcm_cons
      = lcm h (lcm (list_lcm l1) (list_lcm l2))    by induction hypothesis
      = lcm (lcm h (list_lcm l1)) (list_lcm l2)    by LCM_ASSOC
      = lcm (list_lcm (h::l1)) (list_lcm l2)       by list_lcm_cons
*)
val list_lcm_append = store_thm(
  "list_lcm_append",
  ``!l1 l2. list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2)``,
  Induct >-
  rw[] >>
  rw[LCM_ASSOC]);

(* Theorem: list_lcm (l1 ++ l2 ++ l3) = list_lcm [(list_lcm l1); (list_lcm l2); (list_lcm l3)] *)
(* Proof:
     list_lcm (l1 ++ l2 ++ l3)
   = lcm (list_lcm (l1 ++ l2)) (list_lcm l3)                    by list_lcm_append
   = lcm (lcm (list_lcm l1) (list_lcm l2)) (list_lcm l3)        by list_lcm_append
   = lcm (list_lcm l1) (lcm (list_lcm l2) (list_lcm l3))        by LCM_ASSOC
   = lcm (list_lcm l1) (list_lcm [(list_lcm l2); list_lcm l3])  by list_lcm_cons
   = list_lcm [list_lcm l1; list_lcm l2; list_lcm l3]           by list_lcm_cons
*)
val list_lcm_append_3 = store_thm(
  "list_lcm_append_3",
  ``!l1 l2 l3. list_lcm (l1 ++ l2 ++ l3) = list_lcm [(list_lcm l1); (list_lcm l2); (list_lcm l3)]``,
  rw[list_lcm_append, LCM_ASSOC, list_lcm_cons]);

(* Theorem: list_lcm (REVERSE l) = list_lcm l *)
(* Proof:
   By induction on l.
   Base: list_lcm (REVERSE []) = list_lcm []
       True since REVERSE [] = []          by REVERSE_DEF
   Step: list_lcm (REVERSE l) = list_lcm l ==>
         !h. list_lcm (REVERSE (h::l)) = list_lcm (h::l)
        list_lcm (REVERSE (h::l))
      = list_lcm (REVERSE l ++ [h])        by REVERSE_DEF
      = lcm (list_lcm (REVERSE l)) (list_lcm [h])   by list_lcm_append
      = lcm (list_lcm l) (list_lcm [h])             by induction hypothesis
      = lcm (list_lcm [h]) (list_lcm l)             by LCM_COMM
      = list_lcm ([h] ++ l)                         by list_lcm_append
      = list_lcm (h::l)                             by CONS_APPEND
*)
val list_lcm_reverse = store_thm(
  "list_lcm_reverse",
  ``!l. list_lcm (REVERSE l) = list_lcm l``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  `list_lcm (REVERSE (h::l)) = list_lcm (REVERSE l ++ [h])` by rw[] >>
  `_ = lcm (list_lcm (REVERSE l)) (list_lcm [h])` by rw[list_lcm_append] >>
  `_ = lcm (list_lcm l) (list_lcm [h])` by rw[] >>
  `_ = lcm (list_lcm [h]) (list_lcm l)` by rw[LCM_COMM] >>
  `_ = list_lcm ([h] ++ l)` by rw[list_lcm_append] >>
  `_ = list_lcm (h::l)` by rw[] >>
  decide_tac);

(* Theorem: list_lcm [1 .. (n + 1)] = lcm (n + 1) (list_lcm [1 .. n])) *)
(* Proof:
     list_lcm [1 .. (n + 1)]
   = list_lcm (SONC (n + 1) [1 .. n])   by listRangeINC_SNOC, 1 <= n + 1
   = lcm (n + 1) (list_lcm [1 .. n])    by list_lcm_snoc
*)
val list_lcm_suc = store_thm(
  "list_lcm_suc",
  ``!n. list_lcm [1 .. (n + 1)] = lcm (n + 1) (list_lcm [1 .. n])``,
  rw[listRangeINC_SNOC, list_lcm_snoc]);

(* Theorem: l <> [] /\ EVERY_POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l *)
(* Proof:
   Note LENGTH l <> 0                           by LENGTH_NIL
    and SUM l <= LENGTH l * list_lcm l          by list_lcm_lower_bound
     so (SUM l) DIV (LENGTH l) <= list_lcm l    by DIV_LE
*)
val list_lcm_nonempty_lower = store_thm(
  "list_lcm_nonempty_lower",
  ``!l. l <> [] /\ EVERY_POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l``,
  metis_tac[list_lcm_lower_bound, DIV_LE, LENGTH_NIL, NOT_ZERO_LT_ZERO]);

(* Theorem: l <> [] /\ POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l *)
(* Proof:
   Note LENGTH l <> 0                           by LENGTH_NIL
    and SUM l <= LENGTH l * list_lcm l          by list_lcm_lower_bound_alt
     so (SUM l) DIV (LENGTH l) <= list_lcm l    by DIV_LE
*)
val list_lcm_nonempty_lower_alt = store_thm(
  "list_lcm_nonempty_lower_alt",
  ``!l. l <> [] /\ POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l``,
  metis_tac[list_lcm_lower_bound_alt, DIV_LE, LENGTH_NIL, NOT_ZERO_LT_ZERO]);

(* Theorem: MEM x l /\ MEM y l ==> (lcm x y) <= list_lcm l *)
(* Proof:
   Note x divides (list_lcm l)          by list_lcm_is_common_multiple
    and y divides (list_lcm l)          by list_lcm_is_common_multiple
    ==> (lcm x y) divides (list_lcm l)  by LCM_IS_LEAST_COMMON_MULTIPLE
*)
val list_lcm_divisor_lcm_pair = store_thm(
  "list_lcm_divisor_lcm_pair",
  ``!l x y. MEM x l /\ MEM y l ==> (lcm x y) divides list_lcm l``,
  rw[list_lcm_is_common_multiple, LCM_IS_LEAST_COMMON_MULTIPLE]);

(* Theorem: POSITIVE l /\ MEM x l /\ MEM y l ==> (lcm x y) <= list_lcm l *)
(* Proof:
   Note (lcm x y) divides (list_lcm l)  by list_lcm_divisor_lcm_pair
    Now 0 < list_lcm l                  by list_lcm_pos_alt
   Thus (lcm x y) <= list_lcm l         by DIVIDES_LE
*)
val list_lcm_lower_by_lcm_pair = store_thm(
  "list_lcm_lower_by_lcm_pair",
  ``!l x y. POSITIVE l /\ MEM x l /\ MEM y l ==> (lcm x y) <= list_lcm l``,
  rw[list_lcm_divisor_lcm_pair, list_lcm_pos_alt, DIVIDES_LE]);

(* Theorem: 0 < m /\ (!x. MEM x l ==> x divides m) ==> list_lcm l <= m *)
(* Proof:
   Note list_lcm l divides m     by list_lcm_is_least_common_multiple
   Thus list_lcm l <= m          by DIVIDES_LE, 0 < m
*)
val list_lcm_upper_by_common_multiple = store_thm(
  "list_lcm_upper_by_common_multiple",
  ``!l m. 0 < m /\ (!x. MEM x l ==> x divides m) ==> list_lcm l <= m``,
  rw[list_lcm_is_least_common_multiple, DIVIDES_LE]);

(* Theorem: list_lcm ls = FOLDR lcm 1 ls *)
(* Proof:
   By induction on ls.
   Base: list_lcm [] = FOLDR lcm 1 []
         list_lcm []
       = 1                        by list_lcm_nil
       = FOLDR lcm 1 []           by FOLDR
   Step: list_lcm ls = FOLDR lcm 1 ls ==>
         !h. list_lcm (h::ls) = FOLDR lcm 1 (h::ls)
         list_lcm (h::ls)
       = lcm h (list_lcm ls)      by list_lcm_def
       = lcm h (FOLDR lcm 1 ls)   by induction hypothesis
       = FOLDR lcm 1 (h::ls)      by FOLDR
*)
val list_lcm_by_FOLDR = store_thm(
  "list_lcm_by_FOLDR",
  ``!ls. list_lcm ls = FOLDR lcm 1 ls``,
  Induct >> rw[]);

(* Theorem: list_lcm ls = FOLDL lcm 1 ls *)
(* Proof:
   Note COMM lcm  since !x y. lcm x y = lcm y x                    by LCM_COMM
    and ASSOC lcm since !x y z. lcm x (lcm y z) = lcm (lcm x y) z  by LCM_ASSOC
    Now list_lcm ls
      = FOLDR lcm 1 ls          by list_lcm_by FOLDR
      = FOLDL lcm 1 ls          by FOLDL_EQ_FOLDR, COMM lcm, ASSOC lcm
*)
val list_lcm_by_FOLDL = store_thm(
  "list_lcm_by_FOLDL",
  ``!ls. list_lcm ls = FOLDL lcm 1 ls``,
  simp[list_lcm_by_FOLDR] >>
  irule (GSYM FOLDL_EQ_FOLDR) >>
  rpt strip_tac >-
  rw[LCM_ASSOC, combinTheory.ASSOC_DEF] >>
  rw[LCM_COMM, combinTheory.COMM_DEF]);

(* ------------------------------------------------------------------------- *)
(* Lists in Leibniz Triangle                                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Veritcal Lists in Leibniz Triangle                                        *)
(* ------------------------------------------------------------------------- *)

(* Define Vertical List in Leibniz Triangle *)
(*
val leibniz_vertical_def = Define `
  leibniz_vertical n = GENLIST SUC (SUC n)
`;

(* Use overloading for leibniz_vertical n. *)
val _ = overload_on("leibniz_vertical", ``\n. GENLIST ((+) 1) (n + 1)``);
*)

(* Define Vertical (downward list) in Leibniz Triangle *)

(* Use overloading for leibniz_vertical n. *)
val _ = overload_on("leibniz_vertical", ``\n. [1 .. (n+1)]``);

(* Theorem: leibniz_vertical n = GENLIST (\i. 1 + i) (n + 1) *)
(* Proof:
     leibniz_vertical n
   = [1 .. (n+1)]                        by notation
   = GENLIST (\i. 1 + i) (n+1 + 1 - 1)   by listRangeINC_def
   = GENLIST (\i. 1 + i) (n + 1)         by arithmetic
*)
val leibniz_vertical_alt = store_thm(
  "leibniz_vertical_alt",
  ``!n. leibniz_vertical n = GENLIST (\i. 1 + i) (n + 1)``,
  rw[listRangeINC_def]);

(* Theorem: leibniz_vertical 0 = [1] *)
(* Proof:
     leibniz_vertical 0
   = [1 .. (0+1)]         by notation
   = [1 .. 1]             by arithmetic
   = [1]                  by listRangeINC_SING
*)
val leibniz_vertical_0 = store_thm(
  "leibniz_vertical_0",
  ``leibniz_vertical 0 = [1]``,
  rw[]);

(* Theorem: LENGTH (leibniz_vertical n) = n + 1 *)
(* Proof:
     LENGTH (leibniz_vertical n)
   = LENGTH [1 .. (n+1)]             by notation
   = n + 1 + 1 - 1                   by listRangeINC_LEN
   = n + 1                           by arithmetic
*)
val leibniz_vertical_len = store_thm(
  "leibniz_vertical_len",
  ``!n. LENGTH (leibniz_vertical n) = n + 1``,
  rw[listRangeINC_LEN]);

(* Theorem: leibniz_vertical n <> [] *)
(* Proof:
      LENGTH (leibniz_vertical n)
    = n + 1                         by leibniz_vertical_len
    <> 0                            by ADD1, SUC_NOT_ZERO
    Thus leibniz_vertical n <> []   by LENGTH_EQ_0
*)
val leibniz_vertical_not_nil = store_thm(
  "leibniz_vertical_not_nil",
  ``!n. leibniz_vertical n <> []``,
  metis_tac[leibniz_vertical_len, LENGTH_EQ_0, DECIDE``!n. n + 1 <> 0``]);

(* Theorem: EVERY_POSITIVE (leibniz_vertical n) *)
(* Proof:
       EVERY_POSITIVE (leibniz_vertical n)
   <=> EVERY_POSITIVE GENLIST (\i. 1 + i) (n+1)   by leibniz_vertical_alt
   <=> !i. i < n + 1 ==> 0 < 1 + i                by EVERY_GENLIST
   <=> !i. i < n + 1 ==> T                        by arithmetic
   <=> T
*)
val leibniz_vertical_pos = store_thm(
  "leibniz_vertical_pos",
  ``!n. EVERY_POSITIVE (leibniz_vertical n)``,
  rw[leibniz_vertical_alt, EVERY_GENLIST]);

(* Theorem: POSITIVE (leibniz_vertical n) *)
(* Proof: by leibniz_vertical_pos, EVERY_MEM *)
val leibniz_vertical_pos_alt = store_thm(
  "leibniz_vertical_pos_alt",
  ``!n. POSITIVE (leibniz_vertical n)``,
  rw[leibniz_vertical_pos, EVERY_MEM]);

(* Theorem: 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_vertical n) *)
(* Proof:
   Note: (leibniz_vertical n) has 1 to (n+1), inclusive:
       MEM x (leibniz_vertical n)
   <=> MEM x [1 .. (n+1)]              by notation
   <=> 1 <= x /\ x <= n + 1            by listRangeINC_MEM
   <=> 0 < x /\ x <= n + 1             by num_CASES, LESS_EQ_MONO
*)
val leibniz_vertical_mem = store_thm(
  "leibniz_vertical_mem",
  ``!n x. 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_vertical n)``,
  rw[]);

(* Theorem: leibniz_vertical (n + 1) = SNOC (n + 2) (leibniz_vertical n) *)
(* Proof:
     leibniz_vertical (n + 1)
   = [1 .. (n+1 +1)]                     by notation
   = SNOC (n+1 + 1) [1 .. (n+1)]         by listRangeINC_SNOC
   = SNOC (n + 2) (leibniz_vertical n)   by notation
*)
val leibniz_vertical_snoc = store_thm(
  "leibniz_vertical_snoc",
  ``!n. leibniz_vertical (n + 1) = SNOC (n + 2) (leibniz_vertical n)``,
  rw[listRangeINC_SNOC]);;

(* Use overloading for leibniz_up n. *)
val _ = overload_on("leibniz_up", ``\n. REVERSE (leibniz_vertical n)``);

(* Theorem: leibniz_up 0 = [1] *)
(* Proof:
     leibniz_up 0
   = REVERSE (leibniz_vertical 0)  by notation
   = REVERSE [1]                   by leibniz_vertical_0
   = [1]                           by REVERSE_SING
*)
val leibniz_up_0 = store_thm(
  "leibniz_up_0",
  ``leibniz_up 0 = [1]``,
  rw[]);

(* Theorem: LENGTH (leibniz_up n) = n + 1 *)
(* Proof:
     LENGTH (leibniz_up n)
   = LENGTH (REVERSE (leibniz_vertical n))   by notation
   = LENGTH (leibniz_vertical n)             by LENGTH_REVERSE
   = n + 1                                   by leibniz_vertical_len
*)
val leibniz_up_len = store_thm(
  "leibniz_up_len",
  ``!n. LENGTH (leibniz_up n) = n + 1``,
  rw[leibniz_vertical_len]);

(* Theorem: EVERY_POSITIVE (leibniz_up n) *)
(* Proof:
       EVERY_POSITIVE (leibniz_up n)
   <=> EVERY_POSITIVE (REVERSE (leibniz_vertical n))   by notation
   <=> EVERY_POSITIVE (leibniz_vertical n)             by EVERY_REVERSE
   <=> T                                               by leibniz_vertical_pos
*)
val leibniz_up_pos = store_thm(
  "leibniz_up_pos",
  ``!n. EVERY_POSITIVE (leibniz_up n)``,
  rw[leibniz_vertical_pos, EVERY_REVERSE]);

(* Theorem: 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_up n) *)
(* Proof:
   Note: (leibniz_up n) has (n+1) downto 1, inclusive:
       MEM x (leibniz_up n)
   <=> MEM x (REVERSE (leibniz_vertical n))     by notation
   <=> MEM x (leibniz_vertical n)               by MEM_REVERSE
   <=> T                                        by leibniz_vertical_mem
*)
val leibniz_up_mem = store_thm(
  "leibniz_up_mem",
  ``!n x. 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_up n)``,
  rw[]);

(* Theorem: leibniz_up (n + 1) = (n + 2) :: (leibniz_up n) *)
(* Proof:
     leibniz_up (n + 1)
   = REVERSE (leibniz_vertical (n + 1))            by notation
   = REVERSE (SNOC (n + 2) (leibniz_vertical n))   by leibniz_vertical_snoc
   = (n + 2) :: (leibniz_up n)                     by REVERSE_SNOC
*)
val leibniz_up_cons = store_thm(
  "leibniz_up_cons",
  ``!n. leibniz_up (n + 1) = (n + 2) :: (leibniz_up n)``,
  rw[leibniz_vertical_snoc, REVERSE_SNOC]);

(* ------------------------------------------------------------------------- *)
(* Horizontal List in Leibniz Triangle                                       *)
(* ------------------------------------------------------------------------- *)

(* Define row (horizontal list) in Leibniz Triangle *)
(*
val leibniz_horizontal_def = Define `
  leibniz_horizontal n = GENLIST (leibniz n) (SUC n)
`;

(* Use overloading for leibniz_horizontal n. *)
val _ = overload_on("leibniz_horizontal", ``\n. GENLIST (leibniz n) (n + 1)``);
*)

(* Use overloading for leibniz_horizontal n. *)
val _ = overload_on("leibniz_horizontal", ``\n. GENLIST (leibniz n) (n + 1)``);

(*
> EVAL ``leibniz_horizontal 0``;
val it = |- leibniz_horizontal 0 = [1]: thm
> EVAL ``leibniz_horizontal 1``;
val it = |- leibniz_horizontal 1 = [2; 2]: thm
> EVAL ``leibniz_horizontal 2``;
val it = |- leibniz_horizontal 2 = [3; 6; 3]: thm
> EVAL ``leibniz_horizontal 3``;
val it = |- leibniz_horizontal 3 = [4; 12; 12; 4]: thm
> EVAL ``leibniz_horizontal 4``;
val it = |- leibniz_horizontal 4 = [5; 20; 30; 20; 5]: thm
> EVAL ``leibniz_horizontal 5``;
val it = |- leibniz_horizontal 5 = [6; 30; 60; 60; 30; 6]: thm
> EVAL ``leibniz_horizontal 6``;
val it = |- leibniz_horizontal 6 = [7; 42; 105; 140; 105; 42; 7]: thm
> EVAL ``leibniz_horizontal 7``;
val it = |- leibniz_horizontal 7 = [8; 56; 168; 280; 280; 168; 56; 8]: thm
> EVAL ``leibniz_horizontal 8``;
val it = |- leibniz_horizontal 8 = [9; 72; 252; 504; 630; 504; 252; 72; 9]: thm
*)

(* Theorem: leibniz_horizontal 0 = [1] *)
(* Proof:
     leibniz_horizontal 0
   = GENLIST (leibniz 0) (0 + 1)    by notation
   = GENLIST (leibniz 0) 1          by arithmetic
   = [leibniz 0 0]                  by GENLIST
   = [1]                            by leibniz_n_0
*)
val leibniz_horizontal_0 = store_thm(
  "leibniz_horizontal_0",
  ``leibniz_horizontal 0 = [1]``,
  rw_tac std_ss[GENLIST_1, leibniz_n_0]);

(* Theorem: LENGTH (leibniz_horizontal n) = n + 1 *)
(* Proof:
     LENGTH (leibniz_horizontal n)
   = LENGTH (GENLIST (leibniz n) (n + 1))   by notation
   = n + 1                                  by LENGTH_GENLIST
*)
val leibniz_horizontal_len = store_thm(
  "leibniz_horizontal_len",
  ``!n. LENGTH (leibniz_horizontal n) = n + 1``,
  rw[]);

(* Theorem: k <= n ==> EL k (leibniz_horizontal n) = leibniz n k *)
(* Proof:
   Note k <= n means k < SUC n.
     EL k (leibniz_horizontal n)
   = EL k (GENLIST (leibniz n) (n + 1))   by notation
   = EL k (GENLIST (leibniz n) (SUC n))   by ADD1
   = leibniz n k                          by EL_GENLIST, k < SUC n.
*)
val leibniz_horizontal_el = store_thm(
  "leibniz_horizontal_el",
  ``!n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)``,
  rw[LESS_EQ_IMP_LESS_SUC]);

(* Theorem: k <= n ==> MEM (leibniz n k) (leibniz_horizontal n) *)
(* Proof:
   Note k <= n ==> k < (n + 1)
   Thus MEM (leibniz n k) (GENLIST (leibniz n) (n + 1))        by MEM_GENLIST
     or MEM (leibniz n k) (leibniz_horizontal n)               by notation
*)
val leibniz_horizontal_mem = store_thm(
  "leibniz_horizontal_mem",
  ``!n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)``,
  metis_tac[MEM_GENLIST, DECIDE``k <= n ==> k < n + 1``]);

(* Theorem: MEM (leibniz n k) (leibniz_horizontal n) <=> k <= n *)
(* Proof:
   If part: (leibniz n k) (leibniz_horizontal n) ==> k <= n
      By contradiction, suppose n < k.
      Then leibniz n k = 0        by binomial_less_0, ~(k <= n)
       But ?m. m < n + 1 ==> 0 = leibniz n m    by MEM_GENLIST
        or m <= n ==> leibniz n m = 0           by m < n + 1
       Yet leibniz n m <> 0                     by leibniz_eq_0
      This is a contradiction.
   Only-if part: k <= n ==> (leibniz n k) (leibniz_horizontal n)
      By MEM_GENLIST, this is to show:
           ?m. m < n + 1 /\ (leibniz n k = leibniz n m)
      Note k <= n ==> k < n + 1,
      Take m = k, the result follows.
*)
val leibniz_horizontal_mem_iff = store_thm(
  "leibniz_horizontal_mem_iff",
  ``!n k. MEM (leibniz n k) (leibniz_horizontal n) <=> k <= n``,
  rw_tac bool_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `leibniz n k = 0` by rw[leibniz_less_0] >>
    fs[MEM_GENLIST] >>
    `m <= n` by decide_tac >>
    fs[binomial_eq_0],
    rw[MEM_GENLIST] >>
    `k < n + 1` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: MEM x (leibniz_horizontal n) <=> ?k. k <= n /\ (x = leibniz n k) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n + 1 /\ (x = (n + 1) * binomial n m)) <=> ?k. k <= n /\ (x = (n + 1) * binomial n k)
   Since m < n + 1 <=> m <= n              by LE_LT1
   This is trivially true.
*)
val leibniz_horizontal_member = store_thm(
  "leibniz_horizontal_member",
  ``!n x. MEM x (leibniz_horizontal n) <=> ?k. k <= n /\ (x = leibniz n k)``,
  metis_tac[MEM_GENLIST, LE_LT1]);

(* Theorem: k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k) *)
(* Proof: by EL_GENLIST *)
val leibniz_horizontal_element = store_thm(
  "leibniz_horizontal_element",
  ``!n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)``,
  rw[EL_GENLIST]);

(* Theorem: TAKE 1 (leibniz_horizontal (n + 1)) = [n + 2] *)
(* Proof:
     TAKE 1 (leibniz_horizontal (n + 1))
   = TAKE 1 (GENLIST (leibniz (n + 1)) (n + 1 + 1))                      by notation
   = TAKE 1 (GENLIST (leibniz (SUC n)) (SUC (SUC n)))                    by ADD1
   = TAKE 1 ((leibniz (SUC n) 0) :: GENLIST ((leibniz (SUC n)) o SUC) n) by GENLIST_CONS
   = (leibniz (SUC n) 0):: TAKE 0 (GENLIST ((leibniz (SUC n)) o SUC) n)  by TAKE_def
   = [leibniz (SUC n) 0]:: []                                            by TAKE_0
   = [SUC n + 1]                                                         by leibniz_n_0
   = [n + 2]                                                             by ADD1
*)
val leibniz_horizontal_head = store_thm(
  "leibniz_horizontal_head",
  ``!n. TAKE 1 (leibniz_horizontal (n + 1)) = [n + 2]``,
  rpt strip_tac >>
  `(!n. n + 1 = SUC n) /\ (!n. n + 2 = SUC (SUC n))` by decide_tac >>
  rw[GENLIST_CONS, leibniz_n_0]);

(* Theorem: k <= n ==> (leibniz n k) divides list_lcm (leibniz_horizontal n) *)
(* Proof:
   Note MEM (leibniz n k) (leibniz_horizontal n)                by leibniz_horizontal_mem
     so (leibniz n k) divides list_lcm (leibniz_horizontal n)   by list_lcm_is_common_multiple
*)
val leibniz_horizontal_divisor = store_thm(
  "leibniz_horizontal_divisor",
  ``!n k. k <= n ==> (leibniz n k) divides list_lcm (leibniz_horizontal n)``,
  rw[leibniz_horizontal_mem, list_lcm_is_common_multiple]);

(* Theorem: EVERY_POSITIVE (leibniz_horizontal n) *)
(* Proof:
   Let l = leibniz_horizontal n
   Then LENGTH l = n + 1                     by leibniz_horizontal_len
       EVERY_POSITIVE l
   <=> !k. k < LENGTH l ==> 0 < (EL k l)     by EVERY_EL
   <=> !k. k < n + 1 ==> 0 < (EL k l)        by above
   <=> !k. k <= n ==> 0 < EL k l             by arithmetic
   <=> !k. k <= n ==> 0 < leibniz n k        by leibniz_horizontal_el
   <=> T                                     by leibniz_pos
*)
Theorem leibniz_horizontal_pos:
  !n. EVERY_POSITIVE (leibniz_horizontal n)
Proof
  simp[EVERY_EL, binomial_pos]
QED

(* Theorem: POSITIVE (leibniz_horizontal n) *)
(* Proof: by leibniz_horizontal_pos, EVERY_MEM *)
val leibniz_horizontal_pos_alt = store_thm(
  "leibniz_horizontal_pos_alt",
  ``!n. POSITIVE (leibniz_horizontal n)``,
  metis_tac[leibniz_horizontal_pos, EVERY_MEM]);

(* Theorem: leibniz_horizontal n = MAP (\j. (n+1) * j) (binomial_horizontal n) *)
(* Proof:
     leibniz_horizontal n
   = GENLIST (leibniz n) (n + 1)                          by notation
   = GENLIST ((\j. (n + 1) * j) o (binomial n)) (n + 1)   by leibniz_alt
   = MAP (\j. (n + 1) * j) (GENLIST (binomial n) (n + 1)) by MAP_GENLIST
   = MAP (\j. (n + 1) * j) (binomial_horizontal n)        by notation
*)
val leibniz_horizontal_alt = store_thm(
  "leibniz_horizontal_alt",
  ``!n. leibniz_horizontal n = MAP (\j. (n+1) * j) (binomial_horizontal n)``,
  rw_tac std_ss[leibniz_alt, MAP_GENLIST]);

(* Theorem: list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n) *)
(* Proof:
   Since LENGTH (binomial_horizontal n) = n + 1             by binomial_horizontal_len
         binomial_horizontal n <> []                        by LENGTH_NIL ... [1]
     list_lcm (leibniz_horizontal n)
   = list_lcm (MAP (\j (n+1) * j) (binomial_horizontal n))  by leibniz_horizontal_alt
   = (n + 1) * list_lcm (binomial_horizontal n)             by list_lcm_map_times, [1]
*)
val leibniz_horizontal_lcm_alt = store_thm(
  "leibniz_horizontal_lcm_alt",
  ``!n. list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n)``,
  rpt strip_tac >>
  `LENGTH (binomial_horizontal n) = n + 1` by rw[binomial_horizontal_len] >>
  `n + 1 <> 0` by decide_tac >>
  `binomial_horizontal n <> []` by metis_tac[LENGTH_NIL] >>
  rw_tac std_ss[leibniz_horizontal_alt, list_lcm_map_times]);

(* Theorem: SUM (leibniz_horizontal n) = (n + 1) * SUM (binomial_horizontal n) *)
(* Proof:
     SUM (leibniz_horizontal n)
   = SUM (MAP (\j. (n + 1) * j) (binomial_horizontal n))   by leibniz_horizontal_alt
   = (n + 1) * SUM (binomial_horizontal n)                 by SUM_MULT
*)
val leibniz_horizontal_sum = store_thm(
  "leibniz_horizontal_sum",
  ``!n. SUM (leibniz_horizontal n) = (n + 1) * SUM (binomial_horizontal n)``,
  rw[leibniz_horizontal_alt, SUM_MULT] >>
  `(\j. j * (n + 1)) = $* (n + 1)` by rw[FUN_EQ_THM] >>
  rw[]);

(* Theorem: SUM (leibniz_horizontal n) = (n + 1) * 2 ** n *)
(* Proof:
     SUM (leibniz_horizontal n)
   = (n + 1) * SUM (binomial_horizontal n)       by leibniz_horizontal_sum
   = (n + 1) * 2 ** n                            by binomial_horizontal_sum
*)
val leibniz_horizontal_sum_eqn = store_thm(
  "leibniz_horizontal_sum_eqn",
  ``!n. SUM (leibniz_horizontal n) = (n + 1) * 2 ** n``,
  rw[leibniz_horizontal_sum, binomial_horizontal_sum]);

(* Theorem: SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = SUM (binomial_horizontal n) *)
(* Proof:
   Note LENGTH (leibniz_horizontal n) = n + 1    by leibniz_horizontal_len
     so 0 < LENGTH (leibniz_horizontal n)        by 0 < n + 1

        SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n)
      = ((n + 1) * SUM (binomial_horizontal n))  DIV (n + 1)     by leibniz_horizontal_sum
      = SUM (binomial_horizontal n)                              by MULT_TO_DIV, 0 < n + 1
*)
val leibniz_horizontal_average = store_thm(
  "leibniz_horizontal_average",
  ``!n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = SUM (binomial_horizontal n)``,
  metis_tac[leibniz_horizontal_sum, leibniz_horizontal_len, MULT_TO_DIV, DECIDE``0 < n + 1``]);

(* Theorem: SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = 2 ** n *)
(* Proof:
        SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n)
      = SUM (binomial_horizontal n)    by leibniz_horizontal_average
      = 2 ** n                         by binomial_horizontal_sum
*)
val leibniz_horizontal_average_eqn = store_thm(
  "leibniz_horizontal_average_eqn",
  ``!n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = 2 ** n``,
  rw[leibniz_horizontal_average, binomial_horizontal_sum]);

(* ------------------------------------------------------------------------- *)
(* Transform from Vertical LCM to Horizontal LCM.                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Using Triplet and Paths                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define a triple type *)
val _ = Hol_datatype`
  triple = <| a: num;
              b: num;
              c: num
            |>
`;

(* A triplet is a triple composed of Leibniz node and children. *)
val triplet_def = Define`
    (triplet n k):triple =
        <| a := leibniz n k;
           b := leibniz (n + 1) k;
           c := leibniz (n + 1) (k + 1)
         |>
`;

(* can even do this after definition of triple type:

val triple_def = Define`
    triple n k =
        <| a := leibniz n k;
           b := leibniz (n + 1) k;
           c := leibniz (n + 1) (k + 1)
          |>
`;
*)

(* Overload elements of a triplet *)
(*
val _ = overload_on("tri_a", ``leibniz n k``);
val _ = overload_on("tri_b", ``leibniz (SUC n) k``);
val _ = overload_on("tri_c", ``leibniz (SUC n) (SUC k)``);

val _ = overload_on("tri_a", ``(triple n k).a``);
val _ = overload_on("tri_b", ``(triple n k).b``);
val _ = overload_on("tri_c", ``(triple n k).c``);
*)
val _ = temp_overload_on("ta", ``(triplet n k).a``);
val _ = temp_overload_on("tb", ``(triplet n k).b``);
val _ = temp_overload_on("tc", ``(triplet n k).c``);

(* Theorem: (ta = leibniz n k) /\ (tb = leibniz (n + 1) k) /\ (tc = leibniz (n + 1) (k + 1)) *)
(* Proof: by triplet_def *)
val leibniz_triplet_member = store_thm(
  "leibniz_triplet_member",
  ``!n k. (ta = leibniz n k) /\ (tb = leibniz (n + 1) k) /\ (tc = leibniz (n + 1) (k + 1))``,
  rw[triplet_def]);

(* Theorem: (k + 1) * tc = (n + 1 - k) * tb *)
(* Proof:
   Apply: > leibniz_right_eqn |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==> !k. (k + 1) * leibniz (n + 1) (k + 1) = (n + 1 - k) * leibniz (n + 1) k: thm
*)
val leibniz_right_entry = store_thm(
  "leibniz_right_entry",
  ``!(n k):num. (k + 1) * tc = (n + 1 - k) * tb``,
  rw_tac arith_ss[triplet_def, leibniz_right_eqn]);

(* Theorem: (n + 2) * ta = (n + 1 - k) * tb *)
(* Proof:
   Apply: > leibniz_up_eqn |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==> !k. (n + 1 + 1) * leibniz (n + 1 - 1) k = (n + 1 - k) * leibniz (n + 1) k: thm
*)
val leibniz_up_entry = store_thm(
  "leibniz_up_entry",
  ``!(n k):num. (n + 2) * ta = (n + 1 - k) * tb``,
  rw_tac std_ss[triplet_def, leibniz_up_eqn |> SPEC ``n+1`` |> SIMP_RULE arith_ss[]]);

(* Theorem: ta * tb = tc * (tb - ta) *)
(* Proof:
   Apply > leibniz_property |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==> !k. !k. leibniz (n + 1) k * leibniz (n + 1 - 1) k =
     leibniz (n + 1) (k + 1) * (leibniz (n + 1) k - leibniz (n + 1 - 1) k): thm
*)
val leibniz_triplet_property = store_thm(
  "leibniz_triplet_property",
  ``!(n k):num. ta * tb = tc * (tb - ta)``,
  rw_tac std_ss[triplet_def, MULT_COMM, leibniz_property |> SPEC ``n+1`` |> SIMP_RULE arith_ss[]]);

(* Direct proof of same result, for the paper. *)

(* Theorem: ta * tb = tc * (tb - ta) *)
(* Proof:
   If n < k,
      Note n < k ==> ta = 0               by triplet_def, leibniz_less_0
      also n + 1 < k + 1 ==> tc = 0       by triplet_def, leibniz_less_0
      Thus ta * tb = 0 = tc * (tb - ta)   by MULT_EQ_0
   If ~(n < k),
      Then (n + 2) - (n + 1 - k) = k + 1  by arithmetic, k <= n.

        (k + 1) * ta * tb
      = (n + 2 - (n + 1 - k)) * ta * tb
      = (n + 2) * ta * tb - (n + 1 - k) * ta * tb         by RIGHT_SUB_DISTRIB
      = (n + 1 - k) * tb * tb - (n + 1 - k) * ta * tb     by leibniz_up_entry
      = (n + 1 - k) * tb * tb - (n + 1 - k) * tb * ta     by MULT_ASSOC, MULT_COMM
      = (n + 1 - k) * tb * (tb - ta)                      by LEFT_SUB_DISTRIB
      = (k + 1) * tc * (tb - ta)                          by leibniz_right_entry

      Since k + 1 <> 0, the result follows                by MULT_LEFT_CANCEL
*)
val leibniz_triplet_property = store_thm(
  "leibniz_triplet_property",
  ``!(n k):num. ta * tb = tc * (tb - ta)``,
  rpt strip_tac >>
  Cases_on `n < k` >-
  rw[triplet_def, leibniz_less_0] >>
  `(n + 2) - (n + 1 - k) = k + 1` by decide_tac >>
  `(k + 1) * ta * tb = (n + 2 - (n + 1 - k)) * ta * tb` by rw[] >>
  `_ = (n + 2) * ta * tb - (n + 1 - k) * ta * tb` by rw_tac std_ss[RIGHT_SUB_DISTRIB] >>
  `_ = (n + 1 - k) * tb * tb - (n + 1 - k) * ta * tb` by rw_tac std_ss[leibniz_up_entry] >>
  `_ = (n + 1 - k) * tb * tb - (n + 1 - k) * tb * ta` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `_ = (n + 1 - k) * tb * (tb - ta)` by rw_tac std_ss[LEFT_SUB_DISTRIB] >>
  `_ = (k + 1) * tc * (tb - ta)` by rw_tac std_ss[leibniz_right_entry] >>
  `k + 1 <> 0` by decide_tac >>
  metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC]);

(* Theorem: lcm tb ta = lcm tb tc *)
(* Proof:
   Apply: > leibniz_lcm_exchange |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==>
            !k. lcm (leibniz (n + 1) k) (leibniz (n + 1 - 1) k) =
                lcm (leibniz (n + 1) k) (leibniz (n + 1) (k + 1)): thm
*)
val leibniz_triplet_lcm = store_thm(
  "leibniz_triplet_lcm",
  ``!(n k):num. lcm tb ta = lcm tb tc``,
  rw_tac std_ss[triplet_def, leibniz_lcm_exchange |> SPEC ``n+1`` |> SIMP_RULE arith_ss[]]);

(* ------------------------------------------------------------------------- *)
(* Zigzag Path in Leibniz Triangle                                           *)
(* ------------------------------------------------------------------------- *)

(* Define a path type *)
val _ = temp_type_abbrev("path", Type `:num list`);

(* Define paths reachable by one zigzag *)
val leibniz_zigzag_def = Define`
    leibniz_zigzag (p1: path) (p2: path) <=>
    ?(n k):num (x y):path. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)
`;
val _ = overload_on("zigzag", ``leibniz_zigzag``);
val _ = set_fixity "zigzag" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: p1 zigzag p2 ==> (list_lcm p1 = list_lcm p2) *)
(* Proof:
   Given p1 zigzag p2,
     ==> ?n k x y. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)  by leibniz_zigzag_def

     list_lcm p1
   = list_lcm (x ++ [tb; ta] ++ y)                      by above
   = lcm (list_lcm (x ++ [tb; ta])) (list_lcm y)        by list_lcm_append
   = lcm (list_lcm (x ++ ([tb; ta]))) (list_lcm y)      by APPEND_ASSOC
   = lcm (lcm (list_lcm x) (list_lcm ([tb; ta]))) (list_lcm y)   by list_lcm_append
   = lcm (lcm (list_lcm x) (lcm tb ta)) (list_lcm y)    by list_lcm_append, list_lcm_sing
   = lcm (lcm (list_lcm x) (lcm tb tc)) (list_lcm y)    by leibniz_triplet_lcm
   = lcm (lcm (list_lcm x) (list_lcm ([tb; tc]))) (list_lcm y)   by list_lcm_append, list_lcm_sing
   = lcm (list_lcm (x ++ ([tb; tc]))) (list_lcm y)      by list_lcm_append
   = lcm (list_lcm (x ++ [tb; tc])) (list_lcm y)        by APPEND_ASSOC
   = list_lcm (x ++ [tb; tc] ++ y)                      by list_lcm_append
   = list_lcm p2                                        by above
*)
val list_lcm_zigzag = store_thm(
  "list_lcm_zigzag",
  ``!p1 p2. p1 zigzag p2 ==> (list_lcm p1 = list_lcm p2)``,
  rw_tac std_ss[leibniz_zigzag_def] >>
  `list_lcm (x ++ [tb; ta] ++ y) = lcm (list_lcm (x ++ [tb; ta])) (list_lcm y)` by rw[list_lcm_append] >>
  `_ = lcm (list_lcm (x ++ ([tb; ta]))) (list_lcm y)` by rw[] >>
  `_ = lcm (lcm (list_lcm x) (lcm tb ta)) (list_lcm y)` by rw[list_lcm_append] >>
  `_ = lcm (lcm (list_lcm x) (lcm tb tc)) (list_lcm y)` by rw[leibniz_triplet_lcm] >>
  `_ = lcm (list_lcm (x ++ ([tb; tc]))) (list_lcm y)`  by rw[list_lcm_append] >>
  `_ = lcm (list_lcm (x ++ [tb; tc])) (list_lcm y)` by rw[] >>
  `_ = list_lcm (x ++ [tb; tc] ++ y)` by rw[list_lcm_append] >>
  rw[]);

(* Theorem: p1 zigzag p2 ==> !x. ([x] ++ p1) zigzag ([x] ++ p2) *)
(* Proof:
   Since p1 zigzag p2
     ==> ?n k x y. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)  by leibniz_zigzag_def

      [x] ++ p1
    = [x] ++ (x ++ [tb; ta] ++ y)        by above
    = [x] ++ x ++ [tb; ta] ++ y          by APPEND
      [x] ++ p2
    = [x] ++ (x ++ [tb; tc] ++ y)        by above
    = [x] ++ x ++ [tb; tc] ++ y          by APPEND
   Take new x = [x] ++ x, new y = y.
   Then ([x] ++ p1) zigzag ([x] ++ p2)   by leibniz_zigzag_def
*)
val leibniz_zigzag_tail = store_thm(
  "leibniz_zigzag_tail",
  ``!p1 p2. p1 zigzag p2 ==> !x. ([x] ++ p1) zigzag ([x] ++ p2)``,
  metis_tac[leibniz_zigzag_def, APPEND]);

(* Theorem: k <= n ==>
            TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) zigzag
            TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n) *)
(* Proof:
   Since k <= n, k < n + 1, and k + 1 < n + 2.
   Hence k < LENGTH (leibniz_horizontal (n + 1)),

    Let x = TAKE k (leibniz_horizontal (n + 1))
    and y = DROP (k + 1) (leibniz_horizontal n)
        TAKE (k + 1) (leibniz_horizontal (n + 1))
      = TAKE (SUC k) (leibniz_horizontal (SUC n))   by ADD1
      = SNOC tb x                                   by TAKE_SUC_BY_TAKE, k < LENGTH (leibniz_horizontal (n + 1))
      = x ++ [tb]                                   by SNOC_APPEND
        TAKE (k + 2) (leibniz_horizontal (n + 1))
      = TAKE (SUC (SUC k)) (leibniz_horizontal (SUC n))   by ADD1
      = SNOC tc (SNOC tb x)                         by TAKE_SUC_BY_TAKE, k + 1 < LENGTH (leibniz_horizontal (n + 1))
      = x ++ [tb; tc]                               by SNOC_APPEND
        DROP k (leibniz_horizontal n)
      = ta :: y                                     by DROP_BY_DROP_SUC, k < LENGTH (leibniz_horizontal n)
      = [ta] ++ y                                   by CONS_APPEND
   Hence
    Let p1 = TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n)
           = x ++ [tb] ++ [ta] ++ y
           = x ++ [tb; ta] ++ y                     by APPEND
    Let p2 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)
           = x ++ [tb; tc] ++ y
   Therefore p1 zigzag p2                           by leibniz_zigzag_def
*)
val leibniz_horizontal_zigzag = store_thm(
  "leibniz_horizontal_zigzag",
  ``!n k. k <= n ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) zigzag
                    TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)``,
  rpt strip_tac >>
  qabbrev_tac `x = TAKE k (leibniz_horizontal (n + 1))` >>
  qabbrev_tac `y = DROP (k + 1) (leibniz_horizontal n)` >>
  `k <= n + 1` by decide_tac >>
  `EL k (leibniz_horizontal n) = ta` by rw_tac std_ss[triplet_def, leibniz_horizontal_el] >>
  `EL k (leibniz_horizontal (n + 1)) = tb` by rw_tac std_ss[triplet_def, leibniz_horizontal_el] >>
  `EL (k + 1) (leibniz_horizontal (n + 1)) = tc` by rw_tac std_ss[triplet_def, leibniz_horizontal_el] >>
  `k < n + 1` by decide_tac >>
  `k < LENGTH (leibniz_horizontal (n + 1))` by rw[leibniz_horizontal_len] >>
  `TAKE (k + 1) (leibniz_horizontal (n + 1)) = TAKE (SUC k) (leibniz_horizontal (n + 1))` by rw[ADD1] >>
  `_ = SNOC tb x` by rw[TAKE_SUC_BY_TAKE, Abbr`x`] >>
  `_ = x ++ [tb]` by rw[] >>
  `SUC k < n + 2` by decide_tac >>
  `SUC k < LENGTH (leibniz_horizontal (n + 1))` by rw[leibniz_horizontal_len] >>
  `TAKE (k + 2) (leibniz_horizontal (n + 1)) = TAKE (SUC (SUC k)) (leibniz_horizontal (n + 1))` by rw[ADD1] >>
  `_ = SNOC tc (SNOC tb x)` by rw_tac std_ss[TAKE_SUC_BY_TAKE, ADD1, Abbr`x`] >>
  `_ = x ++ [tb; tc]` by rw[] >>
  `DROP k (leibniz_horizontal n) = [ta] ++ y` by rw[DROP_BY_DROP_SUC, ADD1, Abbr`y`] >>
  qabbrev_tac `p1 = TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n)` >>
  qabbrev_tac `p2 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ y` >>
  `p1 = x ++ [tb; ta] ++ y` by rw[Abbr`p1`, Abbr`x`, Abbr`y`] >>
  `p2 = x ++ [tb; tc] ++ y` by rw[Abbr`p2`, Abbr`x`] >>
  metis_tac[leibniz_zigzag_def]);

(* Theorem: (leibniz_up 1) zigzag (leibniz_horizontal 1) *)
(* Proof:
   Since leibniz_up 1
       = [2; 1]                  by EVAL_TAC
       = [] ++ [2; 1] ++ []      by EVAL_TAC
     and leibniz_horizontal 1
       = [2; 2]                  by EVAL_TAC
       = [] ++ [2; 2] ++ []      by EVAL_TAC
     Now the first Leibniz triplet is:
         (triplet 0 0).a = 1     by EVAL_TAC
         (triplet 0 0).b = 2     by EVAL_TAC
         (triplet 0 0).c = 2     by EVAL_TAC
   Hence (leibniz_up 1) zigzag (leibniz_horizontal 1)   by leibniz_zigzag_def
*)
val leibniz_triplet_0 = store_thm(
  "leibniz_triplet_0",
  ``(leibniz_up 1) zigzag (leibniz_horizontal 1)``,
  `leibniz_up 1 = [] ++ [2; 1] ++ []` by EVAL_TAC >>
  `leibniz_horizontal 1 = [] ++ [2; 2] ++ []` by EVAL_TAC >>
  `((triplet 0 0).a = 1) /\ ((triplet 0 0).b = 2) /\ ((triplet 0 0).c = 2)` by EVAL_TAC >>
  metis_tac[leibniz_zigzag_def]);

(* ------------------------------------------------------------------------- *)
(* Wriggle Paths in Leibniz Triangle                                         *)
(* ------------------------------------------------------------------------- *)

(* Define paths reachable by many zigzags *)
(*
val leibniz_wriggle_def = Define`
    leibniz_wriggle (p1: path) (p2: path) <=>
    ?(m:num) (f:num -> path).
          (p1 = f 0) /\
          (p2 = f m) /\
          (!k. k < m ==> (f k) zigzag (f (SUC k)))
`;
*)

(* Define paths reachable by many zigzags by closure *)
val _ = overload_on("wriggle", ``RTC leibniz_zigzag``); (* RTC = reflexive transitive closure *)
val _ = set_fixity "wriggle" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: p1 wriggle p2 ==> (list_lcm p1 = list_lcm p2) *)
(* Proof:
   By RTC_STRONG_INDUCT.
   Base: list_lcm p1 = list_lcm p1, trivially true.
   Step: p1 zigzag p1' /\ p1' wriggle p2 /\ list_lcm p1' = list_lcm p2 ==> list_lcm p1 = list_lcm p2
         list_lcm p1
       = list_lcm p1'     by list_lcm_zigzag
       = list_lcm p2      by induction hypothesis
*)
val list_lcm_wriggle = store_thm(
  "list_lcm_wriggle",
  ``!p1 p2. p1 wriggle p2 ==> (list_lcm p1 = list_lcm p2)``,
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  metis_tac[list_lcm_zigzag]);

(* Theorem: p1 zigzag p2 ==> p1 wriggle p2 *)
(* Proof:
     p1 wriggle p2
   = p1 (RTC zigzag) p2    by notation
   = p1 zigzag p2          by RTC_SINGLE
*)
val leibniz_zigzag_wriggle = store_thm(
  "leibniz_zigzag_wriggle",
  ``!p1 p2. p1 zigzag p2 ==> p1 wriggle p2``,
  rw[]);

(* Theorem: p1 wriggle p2 ==> !x. ([x] ++ p1) wriggle ([x] ++ p2) *)
(* Proof:
   By RTC_STRONG_INDUCT.
   Base: [x] ++ p1 wriggle [x] ++ p1
      True by RTC_REFL.
   Step: p1 zigzag p1' /\ p1' wriggle p2 /\ !x. [x] ++ p1' wriggle [x] ++ p2 ==>
         [x] ++ p1 wriggle [x] ++ p2
      Since p1 zigzag p1',
         so [x] ++ p1 zigzag [x] ++ p1'    by leibniz_zigzag_tail
         or [x] ++ p1 wriggle [x] ++ p1'   by leibniz_zigzag_wriggle
       With [x] ++ p1' wriggle [x] ++ p2   by induction hypothesis
      Hence [x] ++ p1 wriggle [x] ++ p2    by RTC_TRANS
*)
val leibniz_wriggle_tail = store_thm(
  "leibniz_wriggle_tail",
  ``!p1 p2. p1 wriggle p2 ==> !x. ([x] ++ p1) wriggle ([x] ++ p2)``,
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  metis_tac[leibniz_zigzag_tail, leibniz_zigzag_wriggle, RTC_TRANS]);

(* Theorem: p1 wriggle p1 *)
(* Proof: by RTC_REFL *)
val leibniz_wriggle_refl = store_thm(
  "leibniz_wriggle_refl",
  ``!p1. p1 wriggle p1``,
  metis_tac[RTC_REFL]);

(* Theorem: p1 wriggle p2 /\ p2 wriggle p3 ==> p1 wriggle p3 *)
(* Proof: by RTC_TRANS *)
val leibniz_wriggle_trans = store_thm(
  "leibniz_wriggle_trans",
  ``!p1 p2 p3. p1 wriggle p2 /\ p2 wriggle p3 ==> p1 wriggle p3``,
  metis_tac[RTC_TRANS]);

(* Theorem: k <= n + 1 ==>
            TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
            leibniz_horizontal (n + 1) *)
(* Proof:
   By induction on the difference: n + 1 - k.
   Base: k = n + 1 ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
                       leibniz_horizontal (n + 1)
           TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n)
         = TAKE (n + 2) (leibniz_horizontal (n + 1)) ++ DROP (n + 1) (leibniz_horizontal n)  by k = n + 1
         = leibniz_horizontal (n + 1) ++ []       by TAKE_LENGTH_ID, DROP_LENGTH_NIL
         = leibniz_horizontal (n + 1)             by APPEND_NIL
         Hence they wriggle to each other         by RTC_REFL
   Step: k <= n + 1 ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
                        leibniz_horizontal (n + 1)
        Let p1 = leibniz_horizontal (n + 1)
            p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_horizontal n)
            p3 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)
       Then p2 zigzag p3                 by leibniz_horizontal_zigzag
        and p3 wriggle p1                by induction hypothesis
       Hence p2 wriggle p1               by RTC_RULES
*)
val leibniz_horizontal_wriggle_step = store_thm(
  "leibniz_horizontal_wriggle_step",
  ``!n k. k <= n + 1 ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
                        leibniz_horizontal (n + 1)``,
  Induct_on `n + 1 - k` >| [
    rpt strip_tac >>
    rw_tac arith_ss[] >>
    `n + 1 = k` by decide_tac >>
    rw[TAKE_LENGTH_ID_rwt, DROP_LENGTH_NIL_rwt],
    rpt strip_tac >>
    `v = n - k` by decide_tac >>
    `v = (n + 1) - (k + 1)` by decide_tac >>
    `k <= n` by decide_tac >>
    `k + 1 <= n + 1` by decide_tac >>
    `k + 1 + 1 = k + 2` by decide_tac >>
    qabbrev_tac `p1 = leibniz_horizontal (n + 1)` >>
    qabbrev_tac `p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_horizontal n)` >>
    qabbrev_tac `p3 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)` >>
    `p2 zigzag p3` by rw[leibniz_horizontal_zigzag, Abbr`p1`, Abbr`p2`, Abbr`p3`] >>
    metis_tac[RTC_RULES]
  ]);

(* Theorem: ([leibniz (n + 1) 0] ++ leibniz_horizontal n) wriggle leibniz_horizontal (n + 1) *)
(* Proof:
   Apply > leibniz_horizontal_wriggle_step |> SPEC ``n:num`` |> SPEC ``0`` |> SIMP_RULE std_ss[DROP_0];
   val it = |- TAKE 1 (leibniz_horizontal (n + 1)) ++ leibniz_horizontal n wriggle leibniz_horizontal (n + 1): thm
*)
val leibniz_horizontal_wriggle = store_thm(
  "leibniz_horizontal_wriggle",
  ``!n. ([leibniz (n + 1) 0] ++ leibniz_horizontal n) wriggle leibniz_horizontal (n + 1)``,
  rpt strip_tac >>
  `TAKE 1 (leibniz_horizontal (n + 1)) = [leibniz (n + 1) 0]` by rw[leibniz_horizontal_head, binomial_n_0] >>
  metis_tac[leibniz_horizontal_wriggle_step |> SPEC ``n:num`` |> SPEC ``0`` |> SIMP_RULE std_ss[DROP_0]]);

(* ------------------------------------------------------------------------- *)
(* Path Transform keeping LCM                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (leibniz_up n) wriggle (leibniz_horizontal n) *)
(* Proof:
   By induction on n.
   Base: leibniz_up 0 wriggle leibniz_horizontal 0
      Since leibniz_up 0 = [1]                             by leibniz_up_0
        and leibniz_horizontal 0 = [1]                     by leibniz_horizontal_0
      Hence leibniz_up 0 wriggle leibniz_horizontal 0      by leibniz_wriggle_refl
   Step: leibniz_up n wriggle leibniz_horizontal n ==>
         leibniz_up (SUC n) wriggle leibniz_horizontal (SUC n)
         Let x = leibniz (n + 1) 0.
         Then x = n + 2                                    by leibniz_n_0
          Now leibniz_up (n + 1) = [x] ++ (leibniz_up n)   by leibniz_up_cons
        Since leibniz_up n wriggle leibniz_horizontal n    by induction hypothesis
           so ([x] ++ (leibniz_up n)) wriggle
              ([x] ++ (leibniz_horizontal n))              by leibniz_wriggle_tail
          and ([x] ++ (leibniz_horizontal n)) wriggle
              (leibniz_horizontal (n + 1))                 by leibniz_horizontal_wriggle
        Hence leibniz_up (SUC n) wriggle
              leibniz_horizontal (SUC n)                   by leibniz_wriggle_trans, ADD1
*)
val leibniz_up_wriggle_horizontal = store_thm(
  "leibniz_up_wriggle_horizontal",
  ``!n. (leibniz_up n) wriggle (leibniz_horizontal n)``,
  Induct >-
  rw[leibniz_up_0, leibniz_horizontal_0] >>
  qabbrev_tac `x = leibniz (n + 1) 0` >>
  `x = n + 2` by rw[leibniz_n_0, Abbr`x`] >>
  `leibniz_up (n + 1) = [x] ++ (leibniz_up n)` by rw[leibniz_up_cons, Abbr`x`] >>
  `([x] ++ (leibniz_up n)) wriggle ([x] ++ (leibniz_horizontal n))` by rw[leibniz_wriggle_tail] >>
  `([x] ++ (leibniz_horizontal n)) wriggle (leibniz_horizontal (n + 1))` by rw[leibniz_horizontal_wriggle, Abbr`x`] >>
  metis_tac[leibniz_wriggle_trans, ADD1]);

(* Theorem: list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n) *)
(* Proof:
   Since leibniz_up n = REVERSE (leibniz_vertical n)    by notation
     and leibniz_up n wriggle leibniz_horizontal n      by leibniz_up_wriggle_horizontal
         list_lcm (leibniz_vertical n)
       = list_lcm (leibniz_up n)                        by list_lcm_reverse
       = list_lcm (leibniz_horizontal n)                by list_lcm_wriggle
*)
val leibniz_lcm_property = store_thm(
  "leibniz_lcm_property",
  ``!n. list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n)``,
  metis_tac[leibniz_up_wriggle_horizontal, list_lcm_wriggle, list_lcm_reverse]);

(* This is a milestone theorem. *)

(* Theorem: k <= n ==> (leibniz n k) divides list_lcm (leibniz_vertical n) *)
(* Proof:
   Note (leibniz n k) divides list_lcm (leibniz_horizontal n)   by leibniz_horizontal_divisor
    ==> (leibniz n k) divides list_lcm (leibniz_vertical n)     by leibniz_lcm_property
*)
val leibniz_vertical_divisor = store_thm(
  "leibniz_vertical_divisor",
  ``!n k. k <= n ==> (leibniz n k) divides list_lcm (leibniz_vertical n)``,
  metis_tac[leibniz_horizontal_divisor, leibniz_lcm_property]);

(* ------------------------------------------------------------------------- *)
(* Lower Bound of Leibniz LCM                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 2 ** n <= list_lcm (leibniz_horizontal n) *)
(* Proof:
   Note LENGTH (binomail_horizontal n) = n + 1    by binomial_horizontal_len
    and EVERY_POSITIVE (binomial_horizontal n) by binomial_horizontal_pos .. [1]
     list_lcm (leibniz_horizontal n)
   = (n + 1) * list_lcm (binomial_horizontal n)   by leibniz_horizontal_lcm_alt
   >= SUM (binomial_horizontal n)                 by list_lcm_lower_bound, [1]
   = 2 ** n                                       by binomial_horizontal_sum
*)
val leibniz_horizontal_lcm_lower = store_thm(
  "leibniz_horizontal_lcm_lower",
  ``!n. 2 ** n <= list_lcm (leibniz_horizontal n)``,
  rpt strip_tac >>
  `LENGTH (binomial_horizontal n) = n + 1` by rw[binomial_horizontal_len] >>
  `EVERY_POSITIVE (binomial_horizontal n)` by rw[binomial_horizontal_pos] >>
  `list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n)` by rw[leibniz_horizontal_lcm_alt] >>
  `SUM (binomial_horizontal n) = 2 ** n` by rw[binomial_horizontal_sum] >>
  metis_tac[list_lcm_lower_bound]);

(* Theorem: 2 ** n <= list_lcm (leibniz_vertical n) *)
(* Proof:
    list_lcm (leibniz_vertical n)
  = list_lcm (leibniz_horizontal n)      by leibniz_lcm_property
  >= 2 ** n                              by leibniz_horizontal_lcm_lower
*)
val leibniz_vertical_lcm_lower = store_thm(
  "leibniz_vertical_lcm_lower",
  ``!n. 2 ** n <= list_lcm (leibniz_vertical n)``,
  rw_tac std_ss[leibniz_horizontal_lcm_lower, leibniz_lcm_property]);

(* Theorem: 2 ** n <= list_lcm [1 .. (n + 1)] *)
(* Proof: by leibniz_vertical_lcm_lower. *)
val lcm_lower_bound = store_thm(
  "lcm_lower_bound",
  ``!n. 2 ** n <= list_lcm [1 .. (n + 1)]``,
  rw[leibniz_vertical_lcm_lower]);

(* ------------------------------------------------------------------------- *)
(* Leibniz LCM Invariance                                                    *)
(* ------------------------------------------------------------------------- *)

(* Use overloading for leibniz_col_arm rooted at leibniz a b, of length n. *)
val _ = overload_on("leibniz_col_arm", ``\a b n. MAP (\x. leibniz (a - x) b) [0 ..< n]``);

(* Use overloading for leibniz_seg_arm rooted at leibniz a b, of length n. *)
val _ = overload_on("leibniz_seg_arm", ``\a b n. MAP (\x. leibniz a (b + x)) [0 ..< n]``);

(*
> EVAL ``leibniz_col_arm 5 1 4``;
val it = |- leibniz_col_arm 5 1 4 = [30; 20; 12; 6]: thm
> EVAL ``leibniz_seg_arm 5 1 4``;
val it = |- leibniz_seg_arm 5 1 4 = [30; 60; 60; 30]: thm
> EVAL ``list_lcm (leibniz_col_arm 5 1 4)``;
val it = |- list_lcm (leibniz_col_arm 5 1 4) = 60: thm
> EVAL ``list_lcm (leibniz_seg_arm 5 1 4)``;
val it = |- list_lcm (leibniz_seg_arm 5 1 4) = 60: thm
*)

(* Theorem: leibniz_col_arm a b 0 = [] *)
(* Proof:
     leibniz_col_arm a b 0
   = MAP (\x. leibniz (a - x) b) [0 ..< 0]     by notation
   = MAP (\x. leibniz (a - x) b) []            by listRangeLHI_def
   = []                                        by MAP
*)
val leibniz_col_arm_0 = store_thm(
  "leibniz_col_arm_0",
  ``!a b. leibniz_col_arm a b 0 = []``,
  rw[]);

(* Theorem: leibniz_seg_arm a b 0 = [] *)
(* Proof:
     leibniz_seg_arm a b 0
   = MAP (\x. leibniz a (b + x)) [0 ..< 0]     by notation
   = MAP (\x. leibniz a (b + x)) []            by listRangeLHI_def
   = []                                        by MAP
*)
val leibniz_seg_arm_0 = store_thm(
  "leibniz_seg_arm_0",
  ``!a b. leibniz_seg_arm a b 0 = []``,
  rw[]);

(* Theorem: leibniz_col_arm a b 1 = [leibniz a b] *)
(* Proof:
     leibniz_col_arm a b 1
   = MAP (\x. leibniz (a - x) b) [0 ..< 1]     by notation
   = MAP (\x. leibniz (a - x) b) [0]           by listRangeLHI_def
   = (\x. leibniz (a - x) b) 0 ::[]            by MAP
   = [leibniz a b]                             by function application
*)
val leibniz_col_arm_1 = store_thm(
  "leibniz_col_arm_1",
  ``!a b. leibniz_col_arm a b 1 = [leibniz a b]``,
  rw[listRangeLHI_def]);

(* Theorem: leibniz_seg_arm a b 1 = [leibniz a b] *)
(* Proof:
     leibniz_seg_arm a b 1
   = MAP (\x. leibniz a (b + x)) [0 ..< 1]     by notation
   = MAP (\x. leibniz a (b + x)) [0]           by listRangeLHI_def
   = (\x. leibniz a (b + x)) 0 :: []           by MAP
   = [leibniz a b]                             by function application
*)
val leibniz_seg_arm_1 = store_thm(
  "leibniz_seg_arm_1",
  ``!a b. leibniz_seg_arm a b 1 = [leibniz a b]``,
  rw[listRangeLHI_def]);

(* Theorem: LENGTH (leibniz_col_arm a b n) = n *)
(* Proof:
     LENGTH (leibniz_col_arm a b n)
   = LENGTH (MAP (\x. leibniz (a - x) b) [0 ..< n])   by notation
   = LENGTH [0 ..< n]                                 by LENGTH_MAP
   = LENGTH (GENLIST (\i. i) n)                       by listRangeLHI_def
   = m                                                by LENGTH_GENLIST
*)
val leibniz_col_arm_len = store_thm(
  "leibniz_col_arm_len",
  ``!a b n. LENGTH (leibniz_col_arm a b n) = n``,
  rw[]);

(* Theorem: LENGTH (leibniz_seg_arm a b n) = n *)
(* Proof:
     LENGTH (leibniz_seg_arm a b n)
   = LENGTH (MAP (\x. leibniz a (b + x)) [0 ..< n])   by notation
   = LENGTH [0 ..< n]                                 by LENGTH_MAP
   = LENGTH (GENLIST (\i. i) n)                       by listRangeLHI_def
   = m                                                by LENGTH_GENLIST
*)
val leibniz_seg_arm_len = store_thm(
  "leibniz_seg_arm_len",
  ``!a b n. LENGTH (leibniz_seg_arm a b n) = n``,
  rw[]);

(* Theorem: k < n ==> !a b. EL k (leibniz_col_arm a b n) = leibniz (a - k) b *)
(* Proof:
   Note LENGTH [0 ..< n] = n                      by LENGTH_listRangeLHI
     EL k (leibniz_col_arm a b n)
   = EL k (MAP (\x. leibniz (a - x) b) [0 ..< n]) by notation
   = (\x. leibniz (a - x) b) (EL k [0 ..< n])     by EL_MAP
   = (\x. leibniz (a - x) b) k                    by EL_listRangeLHI
   = leibniz (a - k) b
*)
val leibniz_col_arm_el = store_thm(
  "leibniz_col_arm_el",
  ``!n k. k < n ==> !a b. EL k (leibniz_col_arm a b n) = leibniz (a - k) b``,
  rw[EL_MAP, EL_listRangeLHI]);

(* Theorem: k < n ==> !a b. EL k (leibniz_seg_arm a b n) = leibniz a (b + k) *)
(* Proof:
   Note LENGTH [0 ..< n] = n                      by LENGTH_listRangeLHI
     EL k (leibniz_seg_arm a b n)
   = EL k (MAP (\x. leibniz a (b + x)) [0 ..< n]) by notation
   = (\x. leibniz a (b + x)) (EL k [0 ..< n])     by EL_MAP
   = (\x. leibniz a (b + x)) k                    by EL_listRangeLHI
   = leibniz a (b + k)
*)
val leibniz_seg_arm_el = store_thm(
  "leibniz_seg_arm_el",
  ``!n k. k < n ==> !a b. EL k (leibniz_seg_arm a b n) = leibniz a (b + k)``,
  rw[EL_MAP, EL_listRangeLHI]);

(* Theorem: TAKE 1 (leibniz_seg_arm a b (n + 1)) = [leibniz a b] *)
(* Proof:
   Note LENGTH (leibniz_seg_arm a b (n + 1)) = n + 1   by leibniz_seg_arm_len
    and 0 < n + 1                                      by ADD1, SUC_POS
     TAKE 1 (leibniz_seg_arm a b (n + 1))
   = TAKE (SUC 0) (leibniz_seg_arm a b (n + 1))        by ONE
   = SNOC (EL 0 (leibniz_seg_arm a b (n + 1))) []      by TAKE_SUC_BY_TAKE, TAKE_0
   = [EL 0 (leibniz_seg_arm a b (n + 1))]              by SNOC_NIL
   = leibniz a b                                       by leibniz_seg_arm_el
*)
val leibniz_seg_arm_head = store_thm(
  "leibniz_seg_arm_head",
  ``!a b n. TAKE 1 (leibniz_seg_arm a b (n + 1)) = [leibniz a b]``,
  metis_tac[leibniz_seg_arm_len, leibniz_seg_arm_el,
             ONE, TAKE_SUC_BY_TAKE, TAKE_0, SNOC_NIL, DECIDE``!n. 0 < n + 1 /\ (n + 0 = n)``]);

(* Theorem: leibniz_col_arm (a + 1) b (n + 1) = leibniz (a + 1) b :: leibniz_col_arm a b n *)
(* Proof:
   Note (\x. leibniz (a + 1 - x) b) o SUC
      = (\x. leibniz (a + 1 - (x + 1)) b)     by FUN_EQ_THM
      = (\x. leibniz (a - x) b)               by arithmetic

     leibniz_col_arm (a + 1) b (n + 1)
   = MAP (\x. leibniz (a + 1 - x) b) [0 ..< (n + 1)]                  by notation
   = MAP (\x. leibniz (a + 1 - x) b) (0::[1 ..< (n+1)])               by listRangeLHI_CONS, 0 < n + 1
   = (\x. leibniz (a + 1 - x) b) 0 :: MAP (\x. leibniz (a + 1 - x) b) [1 ..< (n+1)]   by MAP
   = leibniz (a + 1) b :: MAP (\x. leibniz (a + 1 - x) b) [1 ..< (n+1)]       by function application
   = leibniz (a + 1) b :: MAP ((\x. leibniz (a + 1 - x) b) o SUC) [0 ..< n]   by listRangeLHI_MAP_SUC
   = leibniz (a + 1) b :: MAP (\x. leibniz (a - x) b) [0 ..< n]        by above
   = leibniz (a + 1) b :: leibniz_col_arm a b n                        by notation
*)
val leibniz_col_arm_cons = store_thm(
  "leibniz_col_arm_cons",
  ``!a b n. leibniz_col_arm (a + 1) b (n + 1) = leibniz (a + 1) b :: leibniz_col_arm a b n``,
  rpt strip_tac >>
  `!a x. a + 1 - SUC x + 1 = a - x + 1` by decide_tac >>
  `!a x. a + 1 - SUC x = a - x` by decide_tac >>
  `(\x. leibniz (a + 1 - x) b) o SUC = (\x. leibniz (a + 1 - (x + 1)) b)` by rw[FUN_EQ_THM] >>
  `0 < n + 1` by decide_tac >>
  `leibniz_col_arm (a + 1) b (n + 1) = MAP (\x. leibniz (a + 1 - x) b) (0::[1 ..< (n+1)])` by rw[listRangeLHI_CONS] >>
  `_ = leibniz (a + 1) b :: MAP (\x. leibniz (a + 1 - x) b) [0+1 ..< (n+1)]` by rw[] >>
  `_ = leibniz (a + 1) b :: MAP ((\x. leibniz (a + 1 - x) b) o SUC) [0 ..< n]` by rw[listRangeLHI_MAP_SUC] >>
  `_ = leibniz (a + 1) b :: leibniz_col_arm a b n` by rw[] >>
  rw[]);

(* Theorem: k < n ==> !a b.
    TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) zigzag
    TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n) *)
(* Proof:
   Since k <= n, k < n + 1, and k + 1 < n + 2.
   Hence k < LENGTH (leibniz_seg_arm a b (n + 1)),

    Let x = TAKE k (leibniz_seg_arm a b (n + 1))
    and y = DROP (k + 1) (leibniz_seg_arm a b n)
        TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1))
      = TAKE (SUC k) (leibniz_seg_arm (a + 1) b (n + 1))   by ADD1
      = SNOC t.b x                                         by TAKE_SUC_BY_TAKE, k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))
      = x ++ [t.b]                                    by SNOC_APPEND
        TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1))
      = TAKE (SUC (SUC k)) (leibniz_seg_arm (a + 1) b (SUC n))   by ADD1
      = SNOC t.c (SNOC t.b x)                         by TAKE_SUC_BY_TAKE, SUC k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))
      = x ++ [t.b; t.c]                               by SNOC_APPEND
        DROP k (leibniz_seg_arm a b n)
      = t.a :: y                                      by DROP_BY_DROP_SUC, k < LENGTH (leibniz_seg_arm a b n)
      = [t.a] ++ y                                    by CONS_APPEND
   Hence
    Let p1 = TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n)
           = x ++ [t.b] ++ [t.a] ++ y
           = x ++ [t.b; t.a] ++ y                     by APPEND
    Let p2 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)
           = x ++ [t.b; t.c] ++ y
   Therefore p1 zigzag p2                             by leibniz_zigzag_def
*)
val leibniz_seg_arm_zigzag_step = store_thm(
  "leibniz_seg_arm_zigzag_step",
  ``!n k. k < n ==> !a b.
    TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) zigzag
    TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)``,
  rpt strip_tac >>
  qabbrev_tac `x = TAKE k (leibniz_seg_arm (a + 1) b (n + 1))` >>
  qabbrev_tac `y = DROP (k + 1) (leibniz_seg_arm a b n)` >>
  qabbrev_tac `t = triplet a (b + k)` >>
  `k < n + 1 /\ k + 1 < n + 1` by decide_tac >>
  `EL k (leibniz_seg_arm a b n) = t.a` by rw[triplet_def, leibniz_seg_arm_el, Abbr`t`] >>
  `EL k (leibniz_seg_arm (a + 1) b (n + 1)) = t.b` by rw[triplet_def, leibniz_seg_arm_el, Abbr`t`] >>
  `EL (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) = t.c` by rw[triplet_def, leibniz_seg_arm_el, Abbr`t`] >>
  `k < LENGTH (leibniz_seg_arm a b (n + 1))` by rw[leibniz_seg_arm_len] >>
  `TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) = TAKE (SUC k) (leibniz_seg_arm (a + 1) b (n + 1))` by rw[ADD1] >>
  `_ = SNOC t.b x` by rw[TAKE_SUC_BY_TAKE, Abbr`x`] >>
  `_ = x ++ [t.b]` by rw[] >>
  `SUC k < n + 1` by decide_tac >>
  `SUC k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))` by rw[leibniz_seg_arm_len] >>
  `k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))` by decide_tac >>
  `TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) = TAKE (SUC (SUC k)) (leibniz_seg_arm (a + 1) b (n + 1))` by rw[ADD1] >>
  `_ = SNOC t.c (SNOC t.b x)` by metis_tac[TAKE_SUC_BY_TAKE, ADD1] >>
  `_ = x ++ [t.b; t.c]` by rw[] >>
  `DROP k (leibniz_seg_arm a b n) = [t.a] ++ y` by rw[DROP_BY_DROP_SUC, ADD1, Abbr`y`] >>
  qabbrev_tac `p1 = TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n)` >>
  qabbrev_tac `p2 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ y` >>
  `p1 = x ++ [t.b; t.a] ++ y` by rw[Abbr`p1`, Abbr`x`, Abbr`y`] >>
  `p2 = x ++ [t.b; t.c] ++ y` by rw[Abbr`p2`, Abbr`x`] >>
  metis_tac[leibniz_zigzag_def]);

(* Theorem: k < n + 1 ==> !a b.
            TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
            leibniz_seg_arm (a + 1) b (n + 1) *)
(* Proof:
   By induction on the difference: n - k.
   Base: k = n ==> TAKE (k + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
                   leibniz_seg_arm a b (n + 1)
         Note LENGTH (leibniz_seg_arm (a + 1) b (n + 1)) = n + 1   by leibniz_seg_arm_len
          and LENGTH (leibniz_seg_arm a b n) = n                   by leibniz_seg_arm_len
           TAKE (k + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP k (leibniz_seg_arm a b n)
         = TAKE (n + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP n (leibniz_seg_arm a b n)  by k = n
         = leibniz_seg_arm a b n ++ []           by TAKE_LENGTH_ID, DROP_LENGTH_NIL
         = leibniz_seg_arm a b n                 by APPEND_NIL
         Hence they wriggle to each other        by RTC_REFL
   Step: k < n + 1 ==> TAKE (k + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
                       leibniz_seg_arm a b (n + 1)
        Let p1 = leibniz_seg_arm (a + 1) b (n + 1)
            p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_seg_arm a b n)
            p3 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)
       Then p2 zigzag p3                 by leibniz_seg_arm_zigzag_step
        and p3 wriggle p1                by induction hypothesis
       Hence p2 wriggle p1               by RTC_RULES
*)
val leibniz_seg_arm_wriggle_step = store_thm(
  "leibniz_seg_arm_wriggle_step",
  ``!n k. k < n + 1 ==> !a b.
    TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
    leibniz_seg_arm (a + 1) b (n + 1)``,
  Induct_on `n - k` >| [
    rpt strip_tac >>
    `k = n` by decide_tac >>
    metis_tac[leibniz_seg_arm_len, TAKE_LENGTH_ID, DROP_LENGTH_NIL, APPEND_NIL, RTC_REFL],
    rpt strip_tac >>
    qabbrev_tac `p1 = leibniz_seg_arm (a + 1) b (n + 1)` >>
    qabbrev_tac `p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_seg_arm a b n)` >>
    qabbrev_tac `p3 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)` >>
    `p2 zigzag p3` by rw[leibniz_seg_arm_zigzag_step, Abbr`p1`, Abbr`p2`, Abbr`p3`] >>
    `v = n - (k + 1)` by decide_tac >>
    `k + 1 < n + 1` by decide_tac >>
    `k + 1 + 1 = k + 2` by decide_tac >>
    metis_tac[RTC_RULES]
  ]);

(* Theorem: ([leibniz (a + 1) b] ++ leibniz_seg_arm a b n) wriggle leibniz_seg_arm (a + 1) b (n + 1) *)
(* Proof:
   Apply > leibniz_seg_arm_wriggle_step |> SPEC ``n:num`` |> SPEC ``0`` |> SIMP_RULE std_ss[DROP_0];
   val it =
   |- 0 < n + 1 ==> !a b.
     TAKE 1 (leibniz_seg_arm (a + 1) b (n + 1)) ++ leibniz_seg_arm a b n wriggle
     leibniz_seg_arm (a + 1) b (n + 1):
   thm

   Note 0 < n + 1                                       by ADD1, SUC_POS
     [leibniz (a + 1) b] ++ leibniz_seg_arm a b n
   = TAKE 1 (leibniz_seg_arm (a + 1) b (n + 1)) ++ leibniz_seg_arm a b n           by leibniz_seg_arm_head
   = TAKE 1 (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP 0 (leibniz_seg_arm a b n)  by DROP_0
   wriggle leibniz_seg_arm (a + 1) b (n + 1)            by leibniz_seg_arm_wriggle_step, put k = 0
*)
val leibniz_seg_arm_wriggle_row_arm = store_thm(
  "leibniz_seg_arm_wriggle_row_arm",
  ``!a b n. ([leibniz (a + 1) b] ++ leibniz_seg_arm a b n) wriggle leibniz_seg_arm (a + 1) b (n + 1)``,
  rpt strip_tac >>
  `0 < n + 1 /\ (0 + 1 = 1)` by decide_tac >>
  metis_tac[leibniz_seg_arm_head, leibniz_seg_arm_wriggle_step, DROP_0]);

(* Theorem: b <= a /\ n <= a + 1 - b ==> (leibniz_col_arm a b n) wriggle (leibniz_seg_arm a b n) *)
(* Proof:
   By induction on n.
   Base: leibniz_col_arm a b 0 wriggle leibniz_seg_arm a b 0
      Since leibniz_col_arm a b 0 = []                     by leibniz_col_arm_0
        and leibniz_seg_arm a b 0 = []                     by leibniz_seg_arm_0
      Hence leibniz_col_arm a b 0 wriggle leibniz_seg_arm a b 0   by leibniz_wriggle_refl
   Step: !a b. leibniz_col_arm a b n wriggle leibniz_seg_arm a b n ==>
         leibniz_col_arm a b (SUC n) wriggle leibniz_seg_arm a b (SUC n)
         Induct_on a.
         Base: b <= 0 /\ SUC n <= 0 + 1 - b ==> leibniz_col_arm 0 b (SUC n) wriggle leibniz_seg_arm 0 b (SUC n)
         Note SUC n <= 1 - b ==> n = 0, since 0 <= b.
              leibniz_col_arm 0 b (SUC 0)
            = leibniz_col_arm 0 b 1                       by ONE
            = [leibniz 0 b]                               by leibniz_col_arm_1
              leibniz_seg_arm 0 b (SUC 0)
            = leibniz_seg_arm 0 b 1                       by ONE
            = [leibniz 0 b]                               by leibniz_seg_arm_1
         Hence leibniz_col_arm 0 b 1 wriggle
               leibniz_seg_arm 0 b 1                      by leibniz_wriggle_refl
         Step: b <= SUC a /\ SUC n <= SUC a + 1 - b ==> leibniz_col_arm (SUC a) b (SUC n) wriggle leibniz_seg_arm (SUC a) b (SUC n)
         Note n <= a + 1 - b
           If a + 1 = b,
              Then n = 0,
                leibniz_col_arm (SUC a) b (SUC 0)
              = leibniz_col_arm (SUC a) b 1               by ONE
              = [leibniz (SUC a) b]                       by leibniz_col_arm_1
              = leibniz_seg_arm (SUC a) b 1               by leibniz_seg_arm_1
              = leibniz_seg_arm (SUC a) b (SUC 0)         by ONE
          Hence leibniz_col_arm (SUC a) b 1 wriggle
                leibniz_seg_arm (SUC a) b 1               by leibniz_wriggle_refl
           If a + 1 <> b,
         Then b <= a, and induction hypothesis applies.
         Let x = leibniz (a + 1) b.
         Then leibniz_col_arm (a + 1) b (n + 1)
            = [x] ++ (leibniz_col_arm a b n)              by leibniz_col_arm_cons
        Since leibniz_col_arm a b n
              wriggle leibniz_seg_arm a b n               by induction hypothesis
           so ([x] ++ (leibniz_col_arm a b n)) wriggle
              ([x] ++ (leibniz_seg_arm a b n))            by leibniz_wriggle_tail
          and ([x] ++ (leibniz_seg_arm a b n)) wriggle
              (leibniz_seg_arm (a + 1) b (n + 1))         by leibniz_seg_arm_wriggle_row_arm
        Hence leibniz_col_arm a b (SUC n) wriggle
              leibniz_seg_arm a b (SUC n)                 by leibniz_wriggle_trans, ADD1
*)
val leibniz_col_arm_wriggle_row_arm = store_thm(
  "leibniz_col_arm_wriggle_row_arm",
  ``!a b n. b <= a /\ n <= a + 1 - b ==> (leibniz_col_arm a b n) wriggle (leibniz_seg_arm a b n)``,
  Induct_on `n` >-
  rw[leibniz_col_arm_0, leibniz_seg_arm_0] >>
  rpt strip_tac >>
  Induct_on `a` >| [
    rpt strip_tac >>
    `n = 0` by decide_tac >>
    metis_tac[leibniz_col_arm_1, leibniz_seg_arm_1, ONE, leibniz_wriggle_refl],
    rpt strip_tac >>
    `n <= a + 1 - b` by decide_tac >>
    Cases_on `a + 1 = b` >| [
      `n = 0` by decide_tac >>
      metis_tac[leibniz_col_arm_1, leibniz_seg_arm_1, ONE, leibniz_wriggle_refl],
      `b <= a` by decide_tac >>
      qabbrev_tac `x = leibniz (a + 1) b` >>
      `leibniz_col_arm (a + 1) b (n + 1) = [x] ++ (leibniz_col_arm a b n)` by rw[leibniz_col_arm_cons, Abbr`x`] >>
      `([x] ++ (leibniz_col_arm a b n)) wriggle ([x] ++ (leibniz_seg_arm a b n))` by rw[leibniz_wriggle_tail] >>
      `([x] ++ (leibniz_seg_arm a b n)) wriggle (leibniz_seg_arm (a + 1) b (n + 1))` by rw[leibniz_seg_arm_wriggle_row_arm, Abbr`x`] >>
      metis_tac[leibniz_wriggle_trans, ADD1]
    ]
  ]);

(* Theorem: b <= a /\ n <= a + 1 - b ==> (list_lcm (leibniz_col_arm a b n) = list_lcm (leibniz_seg_arm a b n)) *)
(* Proof:
   Since (leibniz_col_arm a b n) wriggle (leibniz_seg_arm a b n)   by leibniz_col_arm_wriggle_row_arm
     the result follows                                            by list_lcm_wriggle
*)
val leibniz_lcm_invariance = store_thm(
  "leibniz_lcm_invariance",
  ``!a b n. b <= a /\ n <= a + 1 - b ==> (list_lcm (leibniz_col_arm a b n) = list_lcm (leibniz_seg_arm a b n))``,
  rw[leibniz_col_arm_wriggle_row_arm, list_lcm_wriggle]);

(* This is a milestone theorem. *)

(* This is used to give another proof of leibniz_up_wriggle_horizontal *)

(* Theorem: leibniz_col_arm n 0 (n + 1) = leibniz_up n *)
(* Proof:
     leibniz_col_arm n 0 (n + 1)
   = MAP (\x. leibniz (n - x) 0) [0 ..< (n + 1)]      by notation
   = MAP (\x. leibniz (n - x) 0) [0 .. n]             by listRangeLHI_to_listRangeINC
   = MAP ((\x. leibniz x 0) o (\x. n - x)) [0 .. n]   by function composition
   = REVERSE (MAP (\x. leibniz x 0) [0 .. n])         by listRangeINC_REVERSE_MAP
   = REVERSE (MAP (\x. x + 1) [0 .. n])               by leibniz_n_0
   = REVERSE (MAP SUC [0 .. n])                       by ADD1
   = REVERSE (MAP (I o SUC) [0 .. n])                 by I_THM
   = REVERSE [1 .. (n+1)]                             by listRangeINC_MAP_SUC
   = REVERSE (leibniz_vertical n)                     by notation
   = leibniz_up n                                     by notation
*)
val leibniz_col_arm_n_0 = store_thm(
  "leibniz_col_arm_n_0",
  ``!n. leibniz_col_arm n 0 (n + 1) = leibniz_up n``,
  rpt strip_tac >>
  `(\x. x + 1) = SUC` by rw[FUN_EQ_THM] >>
  `(\x. leibniz x 0) o (\x. n - x + 0) = (\x. leibniz (n - x) 0)` by rw[FUN_EQ_THM] >>
  `leibniz_col_arm n 0 (n + 1) = MAP (\x. leibniz (n - x) 0) [0 .. n]` by rw[listRangeLHI_to_listRangeINC] >>
  `_ = MAP ((\x. leibniz x 0) o (\x. n - x + 0)) [0 .. n]` by rw[] >>
  `_ = REVERSE (MAP (\x. leibniz x 0) [0 .. n])` by rw[listRangeINC_REVERSE_MAP] >>
  `_ = REVERSE (MAP (\x. x + 1) [0 .. n])` by rw[leibniz_n_0] >>
  `_ = REVERSE (MAP SUC [0 .. n])` by rw[ADD1] >>
  `_ = REVERSE (MAP (I o SUC) [0 .. n])` by rw[] >>
  `_ = REVERSE [1 .. (n+1)]` by rw[GSYM listRangeINC_MAP_SUC] >>
  rw[]);

(* Theorem: leibniz_seg_arm n 0 (n + 1) = leibniz_horizontal n *)
(* Proof:
     leibniz_seg_arm n 0 (n + 1)
   = MAP (\x. leibniz n x) [0 ..< (n + 1)]       by notation
   = MAP (\x. leibniz n x) [0 .. n]              by listRangeLHI_to_listRangeINC
   = MAP (leibniz n) [0 .. n]                    by FUN_EQ_THM
   = MAP (leibniz n) (GENLIST (\i. i) (n + 1))   by listRangeINC_def
   = GENLIST ((leibniz n) o I) (n + 1)           by MAP_GENLIST
   = GENLIST (leibniz n) (n + 1)                 by I_THM
   = leibniz_horizontal n                        by notation
*)
val leibniz_seg_arm_n_0 = store_thm(
  "leibniz_seg_arm_n_0",
  ``!n. leibniz_seg_arm n 0 (n + 1) = leibniz_horizontal n``,
  rpt strip_tac >>
  `(\x. x) = I` by rw[FUN_EQ_THM] >>
  `(\x. leibniz n x) = leibniz n` by rw[FUN_EQ_THM] >>
  `leibniz_seg_arm n 0 (n + 1) = MAP (leibniz n) [0 .. n]` by rw_tac std_ss[listRangeLHI_to_listRangeINC] >>
  `_ = MAP (leibniz n) (GENLIST (\i. i) (n + 1))` by rw[listRangeINC_def] >>
  `_ = MAP (leibniz n) (GENLIST I (n + 1))` by metis_tac[] >>
  `_ = GENLIST ((leibniz n) o I) (n + 1)` by rw[MAP_GENLIST] >>
  `_ = GENLIST (leibniz n) (n + 1)` by rw[] >>
  rw[]);

(* Theorem: (leibniz_up n) wriggle (leibniz_horizontal n) *)
(* Proof:
   Note 0 <= n /\ n + 1 <= n + 1 - 0, so leibniz_col_arm_wriggle_row_arm applies.
     leibniz_up n
   = leibniz_col_arm n 0 (n + 1)         by leibniz_col_arm_n_0
   wriggle leibniz_seg_arm n 0 (n + 1)   by leibniz_col_arm_wriggle_row_arm
   = leibniz_horizontal n                by leibniz_seg_arm_n_0
*)
val leibniz_up_wriggle_horizontal_alt = store_thm(
  "leibniz_up_wriggle_horizontal_alt",
  ``!n. (leibniz_up n) wriggle (leibniz_horizontal n)``,
  rpt strip_tac >>
  `0 <= n /\ n + 1 <= n + 1 - 0` by decide_tac >>
  metis_tac[leibniz_col_arm_wriggle_row_arm, leibniz_col_arm_n_0, leibniz_seg_arm_n_0]);

(* Theorem: list_lcm (leibniz_up n) = list_lcm (leibniz_horizontal n) *)
(* Proof: by leibniz_up_wriggle_horizontal_alt, list_lcm_wriggle *)
val leibniz_up_lcm_eq_horizontal_lcm = store_thm(
  "leibniz_up_lcm_eq_horizontal_lcm",
  ``!n. list_lcm (leibniz_up n) = list_lcm (leibniz_horizontal n)``,
  rw[leibniz_up_wriggle_horizontal_alt, list_lcm_wriggle]);

(* This is another proof of the milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Set GCD as Big Operator                                                   *)
(* ------------------------------------------------------------------------- *)

(* Big Operators:
SUM_IMAGE_DEF   |- !f s. SIGMA f s = ITSET (\e acc. f e + acc) s 0: thm
PROD_IMAGE_DEF  |- !f s. PI f s = ITSET (\e acc. f e * acc) s 1: thm
*)

(* Define big_gcd for a set *)
val big_gcd_def = Define`
    big_gcd s = ITSET gcd s 0
`;

(* Theorem: big_gcd {} = 0 *)
(* Proof:
     big_gcd {}
   = ITSET gcd {} 0    by big_gcd_def
   = 0                 by ITSET_EMPTY
*)
val big_gcd_empty = store_thm(
  "big_gcd_empty",
  ``big_gcd {} = 0``,
  rw[big_gcd_def, ITSET_EMPTY]);

(* Theorem: big_gcd {x} = x *)
(* Proof:
     big_gcd {x}
   = ITSET gcd {x} 0    by big_gcd_def
   = gcd x 0            by ITSET_SING
   = x                  by GCD_0R
*)
val big_gcd_sing = store_thm(
  "big_gcd_sing",
  ``!x. big_gcd {x} = x``,
  rw[big_gcd_def, ITSET_SING]);

(* Theorem: FINITE s /\ x NOTIN s ==> (big_gcd (x INSERT s) = gcd x (big_gcd s)) *)
(* Proof:
   Note big_gcd s = ITSET gcd s 0                   by big_lcm_def
   Since !x y z. gcd x (gcd y z) = gcd y (gcd x z)  by GCD_ASSOC_COMM
   The result follows                               by ITSET_REDUCTION
*)
val big_gcd_reduction = store_thm(
  "big_gcd_reduction",
  ``!s x. FINITE s /\ x NOTIN s ==> (big_gcd (x INSERT s) = gcd x (big_gcd s))``,
  rw[big_gcd_def, ITSET_REDUCTION, GCD_ASSOC_COMM]);

(* Theorem: FINITE s ==> !x. x IN s ==> (big_gcd s) divides x *)
(* Proof:
   By finite induction on s.
   Base: x IN {} ==> big_gcd {} divides x
      True since x IN {} = F                           by MEMBER_NOT_EMPTY
   Step: !x. x IN s ==> big_gcd s divides x ==>
         e NOTIN s /\ x IN (e INSERT s) ==> big_gcd (e INSERT s) divides x
      Since e NOTIN s,
         so big_gcd (e INSERT s) = gcd e (big_gcd s)   by big_gcd_reduction
      By IN_INSERT,
      If x = e,
         to show: gcd e (big_gcd s) divides e, true    by GCD_IS_GREATEST_COMMON_DIVISOR
      If x <> e, x IN s,
         to show gcd e (big_gcd s) divides x,
         Since (big_gcd s) divides x                   by induction hypothesis, x IN s
           and (big_gcd s) divides gcd e (big_gcd s)   by GCD_IS_GREATEST_COMMON_DIVISOR
            so gcd e (big_gcd s) divides x             by DIVIDES_TRANS
*)
val big_gcd_is_common_divisor = store_thm(
  "big_gcd_is_common_divisor",
  ``!s. FINITE s ==> !x. x IN s ==> (big_gcd s) divides x``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  metis_tac[MEMBER_NOT_EMPTY] >>
  metis_tac[big_gcd_reduction, IN_INSERT, GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_TRANS]);

(* Theorem: FINITE s ==> !m. (!x. x IN s ==> m divides x) ==> m divides (big_gcd s) *)
(* Proof:
   By finite induction on s.
   Base: m divides big_gcd {}
      Since big_gcd {} = 0                        by big_gcd_empty
      Hence true                                  by ALL_DIVIDES_0
   Step: !m. (!x. x IN s ==> m divides x) ==> m divides big_gcd s ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> m divides x ==> m divides big_gcd (e INSERT s)
      Note x IN e INSERT s ==> x = e \/ x IN s    by IN_INSERT
      Put x = e, then m divides e                 by x divides m, x = e
      Put x IN s, then m divides big_gcd s        by induction hypothesis
      Therefore, m divides gcd e (big_gcd s)      by GCD_IS_GREATEST_COMMON_DIVISOR
             or  m divides big_gcd (e INSERT s)   by big_gcd_reduction, e NOTIN s
*)
val big_gcd_is_greatest_common_divisor = store_thm(
  "big_gcd_is_greatest_common_divisor",
  ``!s. FINITE s ==> !m. (!x. x IN s ==> m divides x) ==> m divides (big_gcd s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[big_gcd_empty] >>
  metis_tac[big_gcd_reduction, GCD_IS_GREATEST_COMMON_DIVISOR, IN_INSERT]);

(* Theorem: FINITE s ==> !x. big_gcd (x INSERT s) = gcd x (big_gcd s) *)
(* Proof:
   If x IN s,
      Then (big_gcd s) divides x          by big_gcd_is_common_divisor
           gcd x (big_gcd s)
         = gcd (big_gcd s) x              by GCD_SYM
         = big_gcd s                      by divides_iff_gcd_fix
         = big_gcd (x INSERT s)           by ABSORPTION
   If x NOTIN s, result is true           by big_gcd_reduction
*)
val big_gcd_insert = store_thm(
  "big_gcd_insert",
  ``!s. FINITE s ==> !x. big_gcd (x INSERT s) = gcd x (big_gcd s)``,
  rpt strip_tac >>
  Cases_on `x IN s` >-
  metis_tac[big_gcd_is_common_divisor, divides_iff_gcd_fix, ABSORPTION, GCD_SYM] >>
  rw[big_gcd_reduction]);

(* Theorem: big_gcd {x; y} = gcd x y *)
(* Proof:
     big_gcd {x; y}
   = big_gcd (x INSERT y)          by notation
   = gcd x (big_gcd {y})           by big_gcd_insert
   = gcd x (big_gcd {y INSERT {}}) by notation
   = gcd x (gcd y (big_gcd {}))    by big_gcd_insert
   = gcd x (gcd y 0)               by big_gcd_empty
   = gcd x y                       by gcd_0R
*)
val big_gcd_two = store_thm(
  "big_gcd_two",
  ``!x y. big_gcd {x; y} = gcd x y``,
  rw[big_gcd_insert, big_gcd_empty]);

(* Theorem: FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s *)
(* Proof:
   By finite induction on s.
   Base: {} <> {} /\ !x. x IN {} ==> 0 < x ==> 0 < big_gcd {}
      True since {} <> {} = F
   Step: s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s ==>
         e NOTIN s /\ e INSERT s <> {} /\ !x. x IN e INSERT s ==> 0 < x ==> 0 < big_gcd (e INSERT s)
      Note 0 < e /\ !x. x IN s ==> 0 < x   by IN_INSERT
      If s = {},
           big_gcd (e INSERT {})
         = big_gcd {e}                     by IN_INSERT
         = e > 0                           by big_gcd_sing
      If s <> {},
        so 0 < big_gcd s                   by induction hypothesis
       ==> 0 < gcd e (big_gcd s)           by GCD_EQ_0
        or 0 < big_gcd (e INSERT s)        by big_gcd_insert
*)
val big_gcd_positive = store_thm(
  "big_gcd_positive",
  ``!s. FINITE s /\ s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s``,
  `!s. FINITE s ==> s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[] >>
  `0 < e /\ (!x. x IN s ==> 0 < x)` by rw[] >>
  Cases_on `s = {}` >-
  rw[big_gcd_sing] >>
  metis_tac[big_gcd_insert, GCD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: FINITE s /\ s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s *)
(* Proof:
   By finite induction on s.
   Base: {} <> {} ==> ..., must be true.
   Step: s <> {} ==> !!k. big_gcd (IMAGE ($* k) s) = k * big_gcd s ==>
         e NOTIN s ==> big_gcd (IMAGE ($* k) (e INSERT s)) = k * big_gcd (e INSERT s)
      If s = {},
         big_gcd (IMAGE ($* k) (e INSERT {}))
       = big_gcd (IMAGE ($* k) {e})        by IN_INSERT, s = {}
       = big_gcd {k * e}                   by IMAGE_SING
       = k * e                             by big_gcd_sing
       = k * big_gcd {e}                   by big_gcd_sing
       = k * big_gcd (e INSERT {})         by IN_INSERT, s = {}
     If s <> {},
         big_gcd (IMAGE ($* k) (e INSERT s))
       = big_gcd ((k * e) INSERT (IMAGE ($* k) s))   by IMAGE_INSERT
       = gcd (k * e) (big_gcd (IMAGE ($* k) s))      by big_gcd_insert
       = gcd (k * e) (k * big_gcd s)                 by induction hypothesis
       = k * gcd e (big_gcd s)                       by GCD_COMMON_FACTOR
       = k * big_gcd (e INSERT s)                    by big_gcd_insert
*)
val big_gcd_map_times = store_thm(
  "big_gcd_map_times",
  ``!s. FINITE s /\ s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s``,
  `!s. FINITE s ==> s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[] >>
  Cases_on `s = {}` >-
  rw[big_gcd_sing] >>
  `big_gcd (IMAGE ($* k) (e INSERT s)) = gcd (k * e) (k * big_gcd s)` by rw[big_gcd_insert] >>
  `_ = k * gcd e (big_gcd s)` by rw[GCD_COMMON_FACTOR] >>
  `_ = k * big_gcd (e INSERT s)` by rw[big_gcd_insert] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Set LCM as Big Operator                                                   *)
(* ------------------------------------------------------------------------- *)

(* big_lcm s = ITSET (\e x. lcm e x) s 1 = ITSET lcm s 1, of course! *)
val big_lcm_def = Define`
    big_lcm s = ITSET lcm s 1
`;

(* Theorem: big_lcm {} = 1 *)
(* Proof:
     big_lcm {}
   = ITSET lcm {} 1     by big_lcm_def
   = 1                  by ITSET_EMPTY
*)
val big_lcm_empty = store_thm(
  "big_lcm_empty",
  ``big_lcm {} = 1``,
  rw[big_lcm_def, ITSET_EMPTY]);

(* Theorem: big_lcm {x} = x *)
(* Proof:
     big_lcm {x}
   = ITSET lcm {x} 1     by big_lcm_def
   = lcm x 1             by ITSET_SING
   = x                   by LCM_1
*)
val big_lcm_sing = store_thm(
  "big_lcm_sing",
  ``!x. big_lcm {x} = x``,
  rw[big_lcm_def, ITSET_SING]);

(* Theorem: FINITE s /\ x NOTIN s ==> (big_lcm (x INSERT s) = lcm x (big_lcm s)) *)
(* Proof:
   Note big_lcm s = ITSET lcm s 1                   by big_lcm_def
   Since !x y z. lcm x (lcm y z) = lcm y (lcm x z)  by LCM_ASSOC_COMM
   The result follows                               by ITSET_REDUCTION
*)
val big_lcm_reduction = store_thm(
  "big_lcm_reduction",
  ``!s x. FINITE s /\ x NOTIN s ==> (big_lcm (x INSERT s) = lcm x (big_lcm s))``,
  rw[big_lcm_def, ITSET_REDUCTION, LCM_ASSOC_COMM]);

(* Theorem: FINITE s ==> !x. x IN s ==> x divides (big_lcm s) *)
(* Proof:
   By finite induction on s.
   Base: x IN {} ==> x divides big_lcm {}
      True since x IN {} = F                           by MEMBER_NOT_EMPTY
   Step: !x. x IN s ==> x divides big_lcm s ==>
         e NOTIN s /\ x IN (e INSERT s) ==> x divides big_lcm (e INSERT s)
      Since e NOTIN s,
         so big_lcm (e INSERT s) = lcm e (big_lcm s)   by big_lcm_reduction
      By IN_INSERT,
      If x = e,
         to show: e divides lcm e (big_lcm s), true    by LCM_DIVISORS
      If x <> e, x IN s,
         to show x divides lcm e (big_lcm s),
         Since x divides (big_lcm s)                   by induction hypothesis, x IN s
           and (big_lcm s) divides lcm e (big_lcm s)   by LCM_DIVISORS
            so x divides lcm e (big_lcm s)             by DIVIDES_TRANS
*)
val big_lcm_is_common_multiple = store_thm(
  "big_lcm_is_common_multiple",
  ``!s. FINITE s ==> !x. x IN s ==> x divides (big_lcm s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  metis_tac[MEMBER_NOT_EMPTY] >>
  metis_tac[big_lcm_reduction, IN_INSERT, LCM_DIVISORS, DIVIDES_TRANS]);

(* Theorem: FINITE s ==> !m. (!x. x IN s ==> x divides m) ==> (big_lcm s) divides m *)
(* Proof:
   By finite induction on s.
   Base: big_lcm {} divides m
      Since big_lcm {} = 1                        by big_lcm_empty
      Hence true                                  by ONE_DIVIDES_ALL
   Step: !m. (!x. x IN s ==> x divides m) ==> big_lcm s divides m ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> x divides m ==> big_lcm (e INSERT s) divides m
      Note x IN e INSERT s ==> x = e \/ x IN s    by IN_INSERT
      Put x = e, then e divides m                 by x divides m, x = e
      Put x IN s, then big_lcm s divides m        by induction hypothesis
      Therefore, lcm e (big_lcm s) divides m      by LCM_IS_LEAST_COMMON_MULTIPLE
             or  big_lcm (e INSERT s) divides m   by big_lcm_reduction, e NOTIN s
*)
val big_lcm_is_least_common_multiple = store_thm(
  "big_lcm_is_least_common_multiple",
  ``!s. FINITE s ==> !m. (!x. x IN s ==> x divides m) ==> (big_lcm s) divides m``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[big_lcm_empty] >>
  metis_tac[big_lcm_reduction, LCM_IS_LEAST_COMMON_MULTIPLE, IN_INSERT]);

(* Theorem: FINITE s ==> !x. big_lcm (x INSERT s) = lcm x (big_lcm s) *)
(* Proof:
   If x IN s,
      Then x divides (big_lcm s)          by big_lcm_is_common_multiple
           lcm x (big_lcm s)
         = big_lcm s                      by divides_iff_lcm_fix
         = big_lcm (x INSERT s)           by ABSORPTION
   If x NOTIN s, result is true           by big_lcm_reduction
*)
val big_lcm_insert = store_thm(
  "big_lcm_insert",
  ``!s. FINITE s ==> !x. big_lcm (x INSERT s) = lcm x (big_lcm s)``,
  rpt strip_tac >>
  Cases_on `x IN s` >-
  metis_tac[big_lcm_is_common_multiple, divides_iff_lcm_fix, ABSORPTION] >>
  rw[big_lcm_reduction]);

(* Theorem: big_lcm {x; y} = lcm x y *)
(* Proof:
     big_lcm {x; y}
   = big_lcm (x INSERT y)          by notation
   = lcm x (big_lcm {y})           by big_lcm_insert
   = lcm x (big_lcm {y INSERT {}}) by notation
   = lcm x (lcm y (big_lcm {}))    by big_lcm_insert
   = lcm x (lcm y 1)               by big_lcm_empty
   = lcm x y                       by LCM_1
*)
val big_lcm_two = store_thm(
  "big_lcm_two",
  ``!x y. big_lcm {x; y} = lcm x y``,
  rw[big_lcm_insert, big_lcm_empty]);

(* Theorem: FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s *)
(* Proof:
   By finite induction on s.
   Base: !x. x IN {} ==> 0 < x ==> 0 < big_lcm {}
      big_lcm {} = 1 > 0     by big_lcm_empty
   Step: (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> 0 < x ==> 0 < big_lcm (e INSERT s)
      Note 0 < e /\ !x. x IN s ==> 0 < x   by IN_INSERT
        so 0 < big_lcm s                   by induction hypothesis
       ==> 0 < lcm e (big_lcm s)           by LCM_EQ_0
        or 0 < big_lcm (e INSERT s)        by big_lcm_insert
*)
val big_lcm_positive = store_thm(
  "big_lcm_positive",
  ``!s. FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[big_lcm_empty] >>
  `0 < e /\ (!x. x IN s ==> 0 < x)` by rw[] >>
  metis_tac[big_lcm_insert, LCM_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: FINITE s /\ s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s *)
(* Proof:
   By finite induction on s.
   Base: {} <> {} ==> ..., must be true.
   Step: s <> {} ==> !!k. big_lcm (IMAGE ($* k) s) = k * big_lcm s ==>
         e NOTIN s ==> big_lcm (IMAGE ($* k) (e INSERT s)) = k * big_lcm (e INSERT s)
      If s = {},
         big_lcm (IMAGE ($* k) (e INSERT {}))
       = big_lcm (IMAGE ($* k) {e})        by IN_INSERT, s = {}
       = big_lcm {k * e}                   by IMAGE_SING
       = k * e                             by big_lcm_sing
       = k * big_lcm {e}                   by big_lcm_sing
       = k * big_lcm (e INSERT {})         by IN_INSERT, s = {}
     If s <> {},
         big_lcm (IMAGE ($* k) (e INSERT s))
       = big_lcm ((k * e) INSERT (IMAGE ($* k) s))   by IMAGE_INSERT
       = lcm (k * e) (big_lcm (IMAGE ($* k) s))      by big_lcm_insert
       = lcm (k * e) (k * big_lcm s)                 by induction hypothesis
       = k * lcm e (big_lcm s)                       by LCM_COMMON_FACTOR
       = k * big_lcm (e INSERT s)                    by big_lcm_insert
*)
val big_lcm_map_times = store_thm(
  "big_lcm_map_times",
  ``!s. FINITE s /\ s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s``,
  `!s. FINITE s ==> s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[] >>
  Cases_on `s = {}` >-
  rw[big_lcm_sing] >>
  `big_lcm (IMAGE ($* k) (e INSERT s)) = lcm (k * e) (k * big_lcm s)` by rw[big_lcm_insert] >>
  `_ = k * lcm e (big_lcm s)` by rw[LCM_COMMON_FACTOR] >>
  `_ = k * big_lcm (e INSERT s)` by rw[big_lcm_insert] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* LCM Lower bound using big LCM                                             *)
(* ------------------------------------------------------------------------- *)

(* Laurent's leib.v and leib.html

Lemma leibn_lcm_swap m n :
   lcmn 'L(m.+1, n) 'L(m, n) = lcmn 'L(m.+1, n) 'L(m.+1, n.+1).
Proof.
rewrite ![lcmn 'L(m.+1, n) _]lcmnC.
by apply/lcmn_swap/leibnS.
Qed.

Notation "\lcm_ ( i < n ) F" :=
 (\big[lcmn/1%N]_(i < n ) F%N)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \lcm_ ( i  <  n  ) '/  '  F ']'") : nat_scope.

Canonical Structure lcmn_moid : Monoid.law 1 :=
  Monoid.Law lcmnA lcm1n lcmn1.
Canonical lcmn_comoid := Monoid.ComLaw lcmnC.

Lemma lieb_line n i k : lcmn 'L(n.+1, i) (\lcm_(j < k) 'L(n, i + j)) =
                   \lcm_(j < k.+1) 'L(n.+1, i + j).
Proof.
elim: k i => [i|k1 IH i].
  by rewrite big_ord_recr !big_ord0 /= lcmn1 lcm1n addn0.
rewrite big_ord_recl /= addn0.
rewrite lcmnA leibn_lcm_swap.
rewrite (eq_bigr (fun j : 'I_k1 => 'L(n, i.+1 + j))).
rewrite -lcmnA.
rewrite IH.
rewrite [RHS]big_ord_recl.
rewrite addn0; congr (lcmn _ _).
by apply: eq_bigr => j _; rewrite addnS.
move=> j _.
by rewrite addnS.
Qed.

Lemma leib_corner n : \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) 'L(n, i).
Proof.
elim: n => [|n IH]; first by rewrite !big_ord_recr !big_ord0 /=.
rewrite big_ord_recr /= IH lcmnC.
rewrite (eq_bigr (fun i : 'I_n.+1 => 'L(n, 0 + i))) //.
by rewrite lieb_line.
Qed.

Lemma main_result n : 2^n.-1 <= \lcm_(i < n) i.+1.
Proof.
case: n => [|n /=]; first by rewrite big_ord0.
have <-: \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) i.+1.
  by apply: eq_bigr => i _; rewrite leibn0.
rewrite leib_corner.
have -> : forall j,  \lcm_(i < j.+1) 'L(n, i) = n.+1 *  \lcm_(i < j.+1) 'C(n, i).
  elim=> [|j IH]; first by rewrite !big_ord_recr !big_ord0 /= !lcm1n.
  by rewrite big_ord_recr [in RHS]big_ord_recr /= IH muln_lcmr.
rewrite (expnDn 1 1) /=  (eq_bigr (fun i : 'I_n.+1 => 'C(n, i))) =>
       [|i _]; last by rewrite !exp1n !muln1.
have <- : forall n m,  \sum_(i < n) m = n * m.
  by move=> m1 n1; rewrite sum_nat_const card_ord.
apply: leq_sum => i _.
apply: dvdn_leq; last by rewrite (bigD1 i) //= dvdn_lcml.
apply big_ind => // [x y Hx Hy|x H]; first by rewrite lcmn_gt0 Hx.
by rewrite bin_gt0 -ltnS.
Qed.

*)

(*
Lemma lieb_line n i k : lcmn 'L(n.+1, i) (\lcm_(j < k) 'L(n, i + j)) = \lcm_(j < k.+1) 'L(n.+1, i + j).

translates to:
      !n i k. lcm (leibniz (n + 1) i) (big_lcm {leibniz n (i + j) | j | j < k}) =
              big_lcm {leibniz (n+1) (i + j) | j | j < k + 1}`;

The picture is:

    n-th row:  L n i          L n (i+1) ....     L n (i + (k-1))
(n+1)-th row:  L (n+1) i

(n+1)-th row:  L (n+1) i  L (n+1) (i+1) .... L (n+1) (i + (k-1))  L (n+1) (i + k)

If k = 1, this is:  L n i        transform to:
                    L (n+1) i                   L (n+1) i  L (n+1) (i+1)
which is Leibniz triplet.

In general, if true for k, then for the next (k+1)

    n-th row:  L n i          L n (i+1) ....     L n (i + (k-1))  L n (i + k)
(n+1)-th row:  L (n+1) i
=                                                                 L n (i + k)
(n+1)-th row:  L (n+1) i  L (n+1) (i+1) .... L (n+1) (i + (k-1))  L (n+1) (i + k)
by induction hypothesis
=
(n+1)-th row:  L (n+1) i  L (n+1) (i+1) .... L (n+1) (i + (k-1))  L (n+1) (i + k) L (n+1) (i + (k+1))
by Leibniz triplet.

*)

(* Introduce a segment, a partial horizontal row, in Leibniz Denominator Triangle *)
val _ = overload_on("leibniz_seg", ``\n k h. IMAGE (\j. leibniz n (k + j)) (count h)``);
(* This is a segment starting at leibniz n k, of length h *)

(* Introduce a horizontal row in Leibniz Denominator Triangle *)
val _ = overload_on("leibniz_row", ``\n h. IMAGE (leibniz n) (count h)``);
(* This is a row starting at leibniz n 0, of length h *)

(* Introduce a vertical column in Leibniz Denominator Triangle *)
val _ = overload_on("leibniz_col", ``\h. IMAGE (\i. leibniz i 0) (count h)``);
(* This is a column starting at leibniz 0 0, descending for a length h *)

(* Representations of paths based on indexed sets *)

(* Theorem: leibniz_seg n k h = {leibniz n (k + j) | j | j IN (count h)} *)
(* Proof: by notation *)
val leibniz_seg_def = store_thm(
  "leibniz_seg_def",
  ``!n k h. leibniz_seg n k h = {leibniz n (k + j) | j | j IN (count h)}``,
  rw[EXTENSION]);

(* Theorem: leibniz_row n h = {leibniz n j | j | j IN (count h)} *)
(* Proof: by notation *)
val leibniz_row_def = store_thm(
  "leibniz_row_def",
  ``!n h. leibniz_row n h = {leibniz n j | j | j IN (count h)}``,
  rw[EXTENSION]);

(* Theorem: leibniz_col h = {leibniz j 0 | j | j IN (count h)} *)
(* Proof: by notation *)
val leibniz_col_def = store_thm(
  "leibniz_col_def",
  ``!h. leibniz_col h = {leibniz j 0 | j | j IN (count h)}``,
  rw[EXTENSION]);

(* Theorem: leibniz_col n = natural n *)
(* Proof:
     leibniz_col n
   = IMAGE (\i. leibniz i 0) (count n)    by notation
   = IMAGE (\i. i + 1) (count n)          by leibniz_n_0
   = IMAGE (\i. SUC i) (count n)          by ADD1
   = IMAGE SUC (count n)                  by FUN_EQ_THM
   = natural n                            by notation
*)
val leibniz_col_eq_natural = store_thm(
  "leibniz_col_eq_natural",
  ``!n. leibniz_col n = natural n``,
  rw[leibniz_n_0, ADD1, FUN_EQ_THM]);

(* The following can be taken as a generalisation of the Leibniz Triplet LCM exchange. *)
(* When length h = 1, the top row is a singleton, and the next row is a duplet, altogether a triplet. *)

(* Theorem: lcm (leibniz (n + 1) k) (big_lcm (leibniz_seg n k h)) = big_lcm (leibniz_seg (n + 1) k (h + 1)) *)
(* Proof:
   Let p = (\j. leibniz n (k + j)), q = (\j. leibniz (n + 1) (k + j)).
   Note q 0 = (leibniz (n + 1) k)                   by function application [1]
   The goal is: lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count h))) = big_lcm (IMAGE q (count (h + 1)))

   By induction on h, length of the row.
   Base case: lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count 0))) = big_lcm (IMAGE q (count (0 + 1)))
           lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count 0)))
         = lcm (q 0) (big_lcm (IMAGE p (count 0)))  by [1]
         = lcm (q 0) (big_lcm (IMAGE p {}))         by COUNT_ZERO
         = lcm (q 0) (big_lcm {})                   by IMAGE_EMPTY
         = lcm (q 0) 1                              by big_lcm_empty
         = q 0                                      by LCM_1
         = big_lcm {q 0}                            by big_lcm_sing
         = big_lcm (IMAEG q {0})                    by IMAGE_SING
         = big_lcm (IMAGE q (count 1))              by count_def, EXTENSION

   Step case: lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count h))) = big_lcm (IMAGE q (count (h + 1))) ==>
              lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (upto h))) = big_lcm (IMAGE q (count (SUC h + 1)))
     Note !n. FINITE (count n)                      by FINITE_COUNT
      and !s. FINITE s ==> FINITE (IMAGE f s)       by IMAGE_FINITE
     Also p h = (triplet n (k + h)).a               by leibniz_triplet_member
          q h = (triplet n (k + h)).b               by leibniz_triplet_member
          q (h + 1) = (triplet n (k + h)).c         by leibniz_triplet_member
     Thus lcm (q h) (p h) = lcm (q h) (q (h + 1))   by leibniz_triplet_lcm

       lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (upto h)))
     = lcm (q 0) (big_lcm (IMAGE p (count (SUC h))))              by [1], notation
     = lcm (q 0) (big_lcm (IMAGE p (h INSERT count h)))           by upto_by_count
     = lcm (q 0) (big_lcm ((p h) INSERT (IMAGE p (count h))))     by IMAGE_INSERT
     = lcm (q 0) (lcm (p h) (big_lcm (IMAGE p (count h))))        by big_lcm_insert
     = lcm (p h) (lcm (q 0) (big_lcm (IMAGE p (count h))))        by LCM_ASSOC_COMM
     = lcm (p h) (big_lcm (IMAGE q (count (h + 1))))              by induction hypothesis
     = lcm (p h) (big_lcm (IMAGE q (count (SUC h))))              by ADD1
     = lcm (p h) (big_lcm (IMAGE q (h INSERT (count h)))          by upto_by_count
     = lcm (p h) (big_lcm ((q h) INSERT IMAGE q (count h)))       by IMAGE_INSERT
     = lcm (p h) (lcm (q h) (big_lcm (IMAGE q (count h))))        by big_lcm_insert
     = lcm (lcm (p h) (q h)) (big_lcm (IMAGE q (count h)))        by LCM_ASSOC
     = lcm (lcm (q h) (p h)) (big_lcm (IMAGE q (count h)))        by LCM_COM
     = lcm (lcm (q h) (q (h + 1))) (big_lcm (IMAGE q (count h)))  by leibniz_triplet_lcm
     = lcm (q (h + 1)) (lcm (q h) (big_lcm (IMAGE q (count h))))  by LCM_ASSOC, LCM_COMM
     = lcm (q (h + 1)) (big_lcm ((q h) INSERT IMAGE q (count h))) by big_lcm_insert
     = lcm (q (h + 1)) (big_lcm (IMAGE q (h INSERT count h))      by IMAGE_INSERT
     = lcm (q (h + 1)) (big_lcm (IMAGE q (count (h + 1))))        by upto_by_count, ADD1
     = big_lcm ((q (h + 1)) INSERT (IMAGE q (count (h + 1))))     by big_lcm_insert
     = big_lcm IMAGE q ((h + 1) INSERT (count (h + 1)))           by IMAGE_INSERT
     = big_lcm (IMAGE q (count (SUC (h + 1))))                    by upto_by_count
     = big_lcm (IMAGE q (count (SUC h + 1)))                      by ADD
*)
val big_lcm_seg_transform = store_thm(
  "big_lcm_seg_transform",
  ``!n k h. lcm (leibniz (n + 1) k) (big_lcm (leibniz_seg n k h)) =
           big_lcm (leibniz_seg (n + 1) k (h + 1))``,
  rpt strip_tac >>
  qabbrev_tac `p = (\j. leibniz n (k + j))` >>
  qabbrev_tac `q = (\j. leibniz (n + 1) (k + j))` >>
  Induct_on `h` >| [
    `count 0 = {}` by rw[] >>
    `count 1 = {0}` by rw[COUNT_1] >>
    rw_tac std_ss[IMAGE_EMPTY, big_lcm_empty, IMAGE_SING, LCM_1, big_lcm_sing, Abbr`p`, Abbr`q`],
    `leibniz (n + 1) k = q 0` by rw[Abbr`q`] >>
    simp[] >>
    `lcm (q h) (p h) = lcm (q h) (q (h + 1))` by
  (`p h = (triplet n (k + h)).a` by rw[leibniz_triplet_member, Abbr`p`] >>
    `q h = (triplet n (k + h)).b` by rw[leibniz_triplet_member, Abbr`q`] >>
    `q (h + 1) = (triplet n (k + h)).c` by rw[leibniz_triplet_member, Abbr`q`] >>
    rw[leibniz_triplet_lcm]) >>
    `lcm (q 0) (big_lcm (IMAGE p (count (SUC h)))) = lcm (q 0) (lcm (p h) (big_lcm (IMAGE p (count h))))` by rw[upto_by_count, big_lcm_insert] >>
    `_ = lcm (p h) (lcm (q 0) (big_lcm (IMAGE p (count h))))` by rw[LCM_ASSOC_COMM] >>
    `_ = lcm (p h) (big_lcm (IMAGE q (count (SUC h))))` by metis_tac[ADD1] >>
    `_ = lcm (p h) (lcm (q h) (big_lcm (IMAGE q (count h))))` by rw[upto_by_count, big_lcm_insert] >>
    `_ = lcm (q (h + 1)) (lcm (q h) (big_lcm (IMAGE q (count h))))` by metis_tac[LCM_ASSOC, LCM_COMM] >>
    `_ = lcm (q (h + 1)) (big_lcm (IMAGE q (count (SUC h))))` by rw[upto_by_count, big_lcm_insert] >>
    `_ = lcm (q (h + 1)) (big_lcm (IMAGE q (count (h + 1))))` by rw[ADD1] >>
    `_ = big_lcm (IMAGE q (count (SUC (h + 1))))` by rw[upto_by_count, big_lcm_insert] >>
    metis_tac[ADD]
  ]);

(* Theorem: lcm (leibniz (n + 1) 0) (big_lcm (leibniz_row n h)) = big_lcm (leibniz_row (n + 1) (h + 1)) *)
(* Proof:
   Note !n h. leibniz_row n h = leibniz_seg n 0 h   by FUN_EQ_THM
   Take k = 0 in big_lcm_seg_transform, the result follows.
*)
val big_lcm_row_transform = store_thm(
  "big_lcm_row_transform",
  ``!n h. lcm (leibniz (n + 1) 0) (big_lcm (leibniz_row n h)) = big_lcm (leibniz_row (n + 1) (h + 1))``,
  rpt strip_tac >>
  `!n h. leibniz_row n h = leibniz_seg n 0 h` by rw[FUN_EQ_THM] >>
  metis_tac[big_lcm_seg_transform]);

(* Theorem: big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1)) *)
(* Proof:
   Let f = \i. leibniz i 0, then f 0 = leibniz 0 0.
   By induction on n.
   Base: big_lcm (leibniz_col (0 + 1)) = big_lcm (leibniz_row 0 (0 + 1))
         big_lcm (leibniz_col (0 + 1))
       = big_lcm (IMAGE f (count 1))              by notation
       = big_lcm (IMAGE f) {0})                   by COUNT_1
       = big_lcm {f 0}                            by IMAGE_SING
       = big_lcm {leibniz 0 0}                    by f 0
       = big_lcm (IMAGE (leibniz 0) {0})          by IMAGE_SING
       = big_lcm (IMAGE (leibniz 0) (count 1))    by COUNT_1

   Step: big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1)) ==>
         big_lcm (leibniz_col (SUC n + 1)) = big_lcm (leibniz_row (SUC n) (SUC n + 1))
         big_lcm (leibniz_col (SUC n + 1))
       = big_lcm (IMAGE f (count (SUC n + 1)))                             by notation
       = big_lcm (IMAGE f (count (SUC (n + 1))))                           by ADD
       = big_lcm (IMAGE f ((n + 1) INSERT (count (n + 1))))                by upto_by_count
       = big_lcm ((f (n + 1)) INSERT (IMAGE f (count (n + 1))))            by IMAGE_INSERT
       = lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))               by big_lcm_insert
       = lcm (f (n + 1)) (big_lcm (IMAGE (leibniz n) (count (n + 1))))     by induction hypothesis
       = lcm (leibniz (n + 1) 0) (big_lcm (IMAGE (leibniz n) (count (n + 1))))  by f (n + 1)
       = big_lcm (IMAGE (leibniz (n + 1)) (count (n + 1 + 1)))             by big_lcm_line_transform
       = big_lcm (IMAGE (leibniz (SUC n)) (count (SUC n + 1)))             by ADD1
*)
val big_lcm_corner_transform = store_thm(
  "big_lcm_corner_transform",
  ``!n. big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1))``,
  Induct >-
  rw[COUNT_1, IMAGE_SING] >>
  qabbrev_tac `f = \i. leibniz i 0` >>
  `big_lcm (IMAGE f (count (SUC n + 1))) = big_lcm (IMAGE f (count (SUC (n + 1))))` by rw[ADD] >>
  `_ = lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[upto_by_count, big_lcm_insert] >>
  `_ = lcm (leibniz (n + 1) 0) (big_lcm (IMAGE (leibniz n) (count (n + 1))))` by rw[Abbr`f`] >>
  `_ = big_lcm (IMAGE (leibniz (n + 1)) (count (n + 1 + 1)))` by rw[big_lcm_row_transform] >>
  `_ = big_lcm (IMAGE (leibniz (SUC n)) (count (SUC n + 1)))` by rw[ADD1] >>
  rw[]);

(* Theorem: (!x. x IN (count (n + 1)) ==> 0 < f x) ==>
            SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1))) *)
(* Proof:
   By induction on n.
   Base: SUM (GENLIST f (0 + 1)) <= (0 + 1) * big_lcm (IMAGE f (count (0 + 1)))
      LHS = SUM (GENLIST f 1)
          = SUM [f 0]                 by GENLIST_1
          = f 0                       by SUM
      RHS = 1 * big_lcm (IMAGE f (count 1))
          = big_lcm (IMAGE f {0})     by COUNT_1
          = big_lcm (f 0)             by IMAGE_SING
          = f 0                       by big_lcm_sing
      Thus LHS <= RHS                 by arithmetic
   Step: SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1))) ==>
         SUM (GENLIST f (SUC n + 1)) <= (SUC n + 1) * big_lcm (IMAGE f (count (SUC n + 1)))
      Note 0 < f (n + 1)                                by (n + 1) IN count (SUC n + 1)
       and !y. y IN count (n + 1) ==> y IN count (SUC n + 1)  by IN_COUNT
       and !x. x IN IMAGE f (count (n + 1)) ==> 0 < x   by IN_IMAGE, above
        so 0 < big_lcm (IMAGE f (count (n + 1)))        by big_lcm_positive
       and 0 < SUC n                                    by SUC_POS
      Thus f (n + 1) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))  by LCM_LE
       and big_lcm (IMAGE f (count (n + 1))) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))  by LCM_LE

      LHS = SUM (GENLIST f (SUC n + 1))
          = SUM (GENLIST f (SUC (n + 1)))                         by ADD
          = SUM (SNOC (f (n + 1)) (GENLIST f (n + 1)))            by GENLIST
          = SUM (GENLIST f (n + 1)) + f (n + 1)                   by SUM_SNOC
      RHS = (SUC n + 1) * big_lcm (IMAGE f (count (SUC n + 1)))
          = (SUC n + 1) * big_lcm (IMAGE f (count (SUC (n + 1)))) by ADD
          = (SUC n + 1) * big_lcm (IMAGE f ((n + 1) INSERT (count (n + 1))))      by upto_by_count
          = (SUC n + 1) * big_lcm ((f (n + 1)) INSERT (IMAGE f (count (n + 1))))  by IMAGE_INSERT
          = (SUC n + 1) * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))     by big_lcm_insert
          = SUC n * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))
            +    1 * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))    by RIGHT_ADD_DISTRIB
          >= SUC n * (big_lcm (IMAGE f (count (n + 1))))  + f (n + 1)       by LCM_LE
           = (n + 1) * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1)      by ADD1
          >= SUM (GENLIST f (n + 1)) + f (n + 1)                            by induction hypothesis
           = LHS                                                            by above
*)
val big_lcm_count_lower_bound = store_thm(
  "big_lcm_count_lower_bound",
  ``!f n. (!x. x IN (count (n + 1)) ==> 0 < f x) ==>
    SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1)))``,
  rpt strip_tac >>
  Induct_on `n` >| [
    rpt strip_tac >>
    `SUM (GENLIST f 1) = f 0` by rw[] >>
    `1 * big_lcm (IMAGE f (count 1)) = f 0` by rw[COUNT_1, big_lcm_sing] >>
    rw[],
    rpt strip_tac >>
    `big_lcm (IMAGE f (count (SUC n + 1))) = big_lcm (IMAGE f (count (SUC (n + 1))))` by rw[ADD] >>
    `_ = lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[upto_by_count, big_lcm_insert] >>
    `!x. (SUC n + 1) * x = SUC n * x + x` by rw[] >>
    `0 < f (n + 1)` by rw[] >>
    `!y. y IN count (n + 1) ==> y IN count (SUC n + 1)` by rw[] >>
    `!x. x IN IMAGE f (count (n + 1)) ==> 0 < x` by metis_tac[IN_IMAGE] >>
    `0 < big_lcm (IMAGE f (count (n + 1)))` by rw[big_lcm_positive] >>
    `0 < SUC n` by rw[] >>
    `f (n + 1) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[LCM_LE] >>
    `big_lcm (IMAGE f (count (n + 1))) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[LCM_LE] >>
    `!a b c x. 0 < a /\ 0 < b /\ 0 < c /\ a <= x /\ b <= x ==> c * a + b <= c * x + x` by
  (rpt strip_tac >>
    `c * a <= c * x` by rw[] >>
    decide_tac) >>
    `SUC n * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1) <= (SUC n + 1) * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by metis_tac[] >>
    `SUC n * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1) = (n + 1) * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1)` by rw[ADD1] >>
    `SUM (GENLIST f (SUC n + 1)) = SUM (GENLIST f (SUC (n + 1)))` by rw[ADD] >>
    `_ = SUM (GENLIST f (n + 1)) + f (n + 1)` by rw[GENLIST, SUM_SNOC] >>
    metis_tac[LESS_EQ_TRANS, DECIDE``!a x y. 0 < a /\ x <= y ==> x + a <= y + a``]
  ]);

(* Theorem: big_lcm (natural (n + 1)) = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1))) *)
(* Proof:
   Note SUC = \i. i + 1                                      by ADD1, FUN_EQ_THM
            = \i. leibniz i 0                                by leibniz_n_0
    and leibniz n = \j. (n + 1) * binomial n j               by leibniz_def, FUN_EQ_THM
     so !s. IMAGE SUC s = IMAGE (\i. leibniz i 0) s          by IMAGE_CONG
    and !s. IMAGE (leibniz n) s = IMAGE (\j. (n + 1) * binomial n j) s   by IMAGE_CONG
   also !s. IMAGE (binomial n) s = IMAGE (\j. binomial n j) s            by FUN_EQ_THM, IMAGE_CONG
    and count (n + 1) <> {}                                  by COUNT_EQ_EMPTY, n + 1 <> 0 [1]

     big_lcm (IMAGE SUC (count (n + 1)))
   = big_lcm (IMAGE (\i. leibniz i 0) (count (n + 1)))       by above
   = big_lcm (IMAGE (leibniz n) (count (n + 1)))             by big_lcm_corner_transform
   = big_lcm (IMAGE (\j. (n + 1) * binomial n j) (count (n + 1)))       by leibniz_def
   = big_lcm (IMAGE ($* (n + 1)) (IMAGE (binomial n) (count (n + 1))))  by IMAGE_COMPOSE, o_DEF
   = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))  by big_lcm_map_times, FINITE_COUNT, [1]
*)
val big_lcm_natural_eqn = store_thm(
  "big_lcm_natural_eqn",
  ``!n. big_lcm (natural (n + 1)) = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))``,
  rpt strip_tac >>
  `SUC = \i. leibniz i 0` by rw[leibniz_n_0, FUN_EQ_THM] >>
  `leibniz n = \j. (n + 1) * binomial n j` by rw[leibniz_def, FUN_EQ_THM] >>
  `!s. IMAGE SUC s = IMAGE (\i. leibniz i 0) s` by rw[IMAGE_CONG] >>
  `!s. IMAGE (leibniz n) s = IMAGE (\j. (n + 1) * binomial n j) s` by rw[IMAGE_CONG] >>
  `!s. IMAGE (binomial n) s = IMAGE (\j. binomial n j) s` by rw[FUN_EQ_THM, IMAGE_CONG] >>
  `count (n + 1) <> {}` by rw[COUNT_EQ_EMPTY] >>
  `big_lcm (IMAGE SUC (count (n + 1))) = big_lcm (IMAGE (leibniz n) (count (n + 1)))` by rw[GSYM big_lcm_corner_transform] >>
  `_ = big_lcm (IMAGE (\j. (n + 1) * binomial n j) (count (n + 1)))` by rw[] >>
  `_ = big_lcm (IMAGE ($* (n + 1)) (IMAGE (binomial n) (count (n + 1))))` by rw[GSYM IMAGE_COMPOSE, combinTheory.o_DEF] >>
  `_ = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))` by rw[big_lcm_map_times] >>
  rw[]);

(* Theorem: 2 ** n <= big_lcm (natural (n + 1)) *)
(* Proof:
   Note !x. x IN (count (n + 1)) ==> 0 < (binomial n) x      by binomial_pos, IN_COUNT [1]
     big_lcm (natural (n + 1))
   = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))  by big_lcm_natural_eqn
   >= SUM (GENLIST (binomial n) (n + 1))                     by big_lcm_count_lower_bound, [1]
   = SUM (GENLIST (binomial n) (SUC n))                      by ADD1
   = 2 ** n                                                  by binomial_sum
*)
val big_lcm_lower_bound = store_thm(
  "big_lcm_lower_bound",
  ``!n. 2 ** n <= big_lcm (natural (n + 1))``,
  rpt strip_tac >>
  `!x. x IN (count (n + 1)) ==> 0 < (binomial n) x` by rw[binomial_pos] >>
  `big_lcm (IMAGE SUC (count (n + 1))) = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))` by rw[big_lcm_natural_eqn] >>
  `SUM (GENLIST (binomial n) (n + 1)) = 2 ** n` by rw[GSYM binomial_sum, ADD1] >>
  metis_tac[big_lcm_count_lower_bound]);

(* Another proof of the milestone theorem. *)

(* Theorem: big_lcm (set l) = list_lcm l *)
(* Proof:
   By induction on l.
   Base: big_lcm (set []) = list_lcm []
       big_lcm (set [])
     = big_lcm {}        by LIST_TO_SET
     = 1                 by big_lcm_empty
     = list_lcm []       by list_lcm_nil
   Step: big_lcm (set l) = list_lcm l ==> !h. big_lcm (set (h::l)) = list_lcm (h::l)
     Note FINITE (set l)            by FINITE_LIST_TO_SET
       big_lcm (set (h::l))
     = big_lcm (h INSERT set l)     by LIST_TO_SET
     = lcm h (big_lcm (set l))      by big_lcm_insert, FINITE (set t)
     = lcm h (list_lcm l)           by induction hypothesis
     = list_lcm (h::l)              by list_lcm_cons
*)
val big_lcm_eq_list_lcm = store_thm(
  "big_lcm_eq_list_lcm",
  ``!l. big_lcm (set l) = list_lcm l``,
  Induct >-
  rw[big_lcm_empty] >>
  rw[big_lcm_insert]);

(* ------------------------------------------------------------------------- *)
(* List LCM depends only on its set of elements                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MEM x l ==> (list_lcm (x::l) = list_lcm l) *)
(* Proof:
   By induction on l.
   Base: MEM x [] ==> (list_lcm [x] = list_lcm [])
      True by MEM x [] = F                         by MEM
   Step: MEM x l ==> (list_lcm (x::l) = list_lcm l) ==>
         !h. MEM x (h::l) ==> (list_lcm (x::h::l) = list_lcm (h::l))
      Note MEM x (h::l) ==> (x = h) \/ (MEM x l)   by MEM
      If x = h,
         list_lcm (h::h::l)
       = lcm h (lcm h (list_lcm l))   by list_lcm_cons
       = lcm (lcm h h) (list_lcm l)   by LCM_ASSOC
       = lcm h (list_lcm l)           by LCM_REF
       = list_lcm (h::l)              by list_lcm_cons
      If x <> h, MEM x l
         list_lcm (x::h::l)
       = lcm x (lcm h (list_lcm l))   by list_lcm_cons
       = lcm h (lcm x (list_lcm l))   by LCM_ASSOC_COMM
       = lcm h (list_lcm (x::l))      by list_lcm_cons
       = lcm h (list_lcm l)           by induction hypothesis, MEM x l
       = list_lcm (h::l)              by list_lcm_cons
*)
val list_lcm_absorption = store_thm(
  "list_lcm_absorption",
  ``!x l. MEM x l ==> (list_lcm (x::l) = list_lcm l)``,
  rpt strip_tac >>
  Induct_on `l` >-
  metis_tac[MEM] >>
  rw[MEM] >| [
    `lcm h (lcm h (list_lcm l)) = lcm (lcm h h) (list_lcm l)` by rw[LCM_ASSOC] >>
    rw[LCM_REF],
    `lcm x (lcm h (list_lcm l)) = lcm h (lcm x (list_lcm l))` by rw[LCM_ASSOC_COMM] >>
    `_  = lcm h (list_lcm (x::l))` by metis_tac[list_lcm_cons] >>
    rw[]
  ]);

(* Theorem: list_lcm (nub l) = list_lcm l *)
(* Proof:
   By induction on l.
   Base: list_lcm (nub []) = list_lcm []
      True since nub [] = []         by nub_nil
   Step: list_lcm (nub l) = list_lcm l ==> !h. list_lcm (nub (h::l)) = list_lcm (h::l)
      If MEM h l,
           list_lcm (nub (h::l))
         = list_lcm (nub l)         by nub_cons, MEM h l
         = list_lcm l               by induction hypothesis
         = list_lcm (h::l)          by list_lcm_absorption, MEM h l
      If ~(MEM h l),
           list_lcm (nub (h::l))
         = list_lcm (h::nub l)      by nub_cons, ~(MEM h l)
         = lcm h (list_lcm (nub l)) by list_lcm_cons
         = lcm h (list_lcm l)       by induction hypothesis
         = list_lcm (h::l)          by list_lcm_cons
*)
val list_lcm_nub = store_thm(
  "list_lcm_nub",
  ``!l. list_lcm (nub l) = list_lcm l``,
  Induct >-
  rw[nub_nil] >>
  metis_tac[nub_cons, list_lcm_cons, list_lcm_absorption]);

(* Theorem: (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2)) *)
(* Proof:
   By induction on l1.
   Base: !l2. (set [] = set l2) ==> (list_lcm (nub []) = list_lcm (nub l2))
        Note set [] = set l2 ==> l2 = []    by LIST_TO_SET_EQ_EMPTY
        Hence true.
   Step: !l2. (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2)) ==>
         !h l2. (set (h::l1) = set l2) ==> (list_lcm (nub (h::l1)) = list_lcm (nub l2))
        If MEM h l1,
          Then h IN (set l1)            by notation
                set (h::l1)
              = h INSERT set l1         by LIST_TO_SET
              = set l1                  by ABSORPTION_RWT
           Thus set l1 = set l2,
             so list_lcm (nub (h::l1))
              = list_lcm (nub l1)       by nub_cons, MEM h l1
              = list_lcm (nub l2)       by induction hypothesis, set l1 = set l2

        If ~(MEM h l1),
          Then set (h::l1) = set l2
           ==> ?p1 p2. nub l2 = p1 ++ [h] ++ p2
                  and  set l1 = set (p1 ++ p2)            by LIST_TO_SET_REDUCTION

                list_lcm (nub (h::l1))
              = list_lcm (h::nub l1)                      by nub_cons, ~(MEM h l1)
              = lcm h (list_lcm (nub l1))                 by list_lcm_cons
              = lcm h (list_lcm (nub (p1 ++ p2)))         by induction hypothesis
              = lcm h (list_lcm (p1 ++ p2))               by list_lcm_nub
              = lcm h (lcm (list_lcm p1) (list_lcm p2))   by list_lcm_append
              = lcm (list_lcm p1) (lcm h (list_lcm p2))   by LCM_ASSOC_COMM
              = lcm (list_lcm p1) (list_lcm (h::p2))      by list_lcm_append
              = lcm (list_lcm p1) (list_lcm ([h] ++ p2))  by CONS_APPEND
              = list_lcm (p1 ++ ([h] ++ p2))              by list_lcm_append
              = list_lcm (p1 ++ [h] ++ p2)                by APPEND_ASSOC
              = list_lcm (nub l2)                         by above
*)
val list_lcm_nub_eq_if_set_eq = store_thm(
  "list_lcm_nub_eq_if_set_eq",
  ``!l1 l2. (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2))``,
  Induct >-
  rw[LIST_TO_SET_EQ_EMPTY] >>
  rpt strip_tac >>
  Cases_on `MEM h l1` >-
  metis_tac[LIST_TO_SET, ABSORPTION_RWT, nub_cons] >>
  `?p1 p2. (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2))` by metis_tac[LIST_TO_SET_REDUCTION] >>
  `list_lcm (nub (h::l1)) = list_lcm (h::nub l1)` by rw[nub_cons] >>
  `_ = lcm h (list_lcm (nub l1))` by rw[list_lcm_cons] >>
  `_ = lcm h (list_lcm (nub (p1 ++ p2)))` by metis_tac[] >>
  `_ = lcm h (list_lcm (p1 ++ p2))` by rw[list_lcm_nub] >>
  `_ = lcm h (lcm (list_lcm p1) (list_lcm p2))` by rw[list_lcm_append] >>
  `_ = lcm (list_lcm p1) (lcm h (list_lcm p2))` by rw[LCM_ASSOC_COMM] >>
  `_ = lcm (list_lcm p1) (list_lcm ([h] ++ p2))` by rw[list_lcm_cons] >>
  metis_tac[list_lcm_append, APPEND_ASSOC]);

(* Theorem: (set l1 = set l2) ==> (list_lcm l1 = list_lcm l2) *)
(* Proof:
      set l1 = set l2
   ==> list_lcm (nub l1) = list_lcm (nub l2)   by list_lcm_nub_eq_if_set_eq
   ==>       list_lcm l1 = list_lcm l2         by list_lcm_nub
*)
val list_lcm_eq_if_set_eq = store_thm(
  "list_lcm_eq_if_set_eq",
  ``!l1 l2. (set l1 = set l2) ==> (list_lcm l1 = list_lcm l2)``,
  metis_tac[list_lcm_nub_eq_if_set_eq, list_lcm_nub]);

(* ------------------------------------------------------------------------- *)
(* Set LCM by List LCM                                                       *)
(* ------------------------------------------------------------------------- *)

(* Define LCM of a set *)
(* none works!
val set_lcm_def = Define`
   (set_lcm {} = 1) /\
   !s. FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm (s DELETE x))
`;
val set_lcm_def = Define`
   (set_lcm {} = 1) /\
   (!s. FINITE s ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s))))
`;
val set_lcm_def = Define`
   set_lcm s = if s = {} then 1 else lcm (CHOICE s) (set_lcm (REST s))
`;
*)
val set_lcm_def = Define`
    set_lcm s = list_lcm (SET_TO_LIST s)
`;

(* Theorem: set_lcm {} = 1 *)
(* Proof:
     set_lcm {}
   = lcm_list (SET_TO_LIST {})   by set_lcm_def
   = lcm_list []                 by SET_TO_LIST_EMPTY
   = 1                           by list_lcm_nil
*)
val set_lcm_empty = store_thm(
  "set_lcm_empty",
  ``set_lcm {} = 1``,
  rw[set_lcm_def]);

(* Theorem: FINITE s /\ s <> {} ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s))) *)
(* Proof:
     set_lcm s
   = list_lcm (SET_TO_LIST s)                         by set_lcm_def
   = list_lcm (CHOICE s::SET_TO_LIST (REST s))        by SET_TO_LIST_THM
   = lcm (CHOICE s) (list_lcm (SET_TO_LIST (REST s))) by list_lcm_cons
   = lcm (CHOICE s) (set_lcm (REST s))                by set_lcm_def
*)
val set_lcm_nonempty = store_thm(
  "set_lcm_nonempty",
  ``!s. FINITE s /\ s <> {} ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s)))``,
  rw[set_lcm_def, SET_TO_LIST_THM, list_lcm_cons]);

(* Theorem: set_lcm {x} = x *)
(* Proof:
     set_lcm {x}
   = list_lcm (SET_TO_LIST {x})    by set_lcm_def
   = list_lcm [x]                  by SET_TO_LIST_SING
   = x                             by list_lcm_sing
*)
val set_lcm_sing = store_thm(
  "set_lcm_sing",
  ``!x. set_lcm {x} = x``,
  rw_tac std_ss[set_lcm_def, SET_TO_LIST_SING, list_lcm_sing]);

(* Theorem: set_lcm (set l) = list_lcm l *)
(* Proof:
   Let t = SET_TO_LIST (set l)
   Note FINITE (set l)                    by FINITE_LIST_TO_SET
   Then set t
      = set (SET_TO_LIST (set l))         by notation
      = set l                             by SET_TO_LIST_INV, FINITE (set l)

        set_lcm (set l)
      = list_lcm (SET_TO_LIST (set l))    by set_lcm_def
      = list_lcm t                        by notation
      = list_lcm l                        by list_lcm_eq_if_set_eq, set t = set l
*)
val set_lcm_eq_list_lcm = store_thm(
  "set_lcm_eq_list_lcm",
  ``!l. set_lcm (set l) = list_lcm l``,
  rw[FINITE_LIST_TO_SET, SET_TO_LIST_INV, set_lcm_def, list_lcm_eq_if_set_eq]);

(* Theorem: FINITE s ==> (set_lcm s = big_lcm s) *)
(* Proof:
     set_lcm s
   = list_lcm (SET_TO_LIST s)       by set_lcm_def
   = big_lcm (set (SET_TO_LIST s))  by big_lcm_eq_list_lcm
   = big_lcm s                      by SET_TO_LIST_INV, FINITE s
*)
val set_lcm_eq_big_lcm = store_thm(
  "set_lcm_eq_big_lcm",
  ``!s. FINITE s ==> (big_lcm s = set_lcm s)``,
  metis_tac[set_lcm_def, big_lcm_eq_list_lcm, SET_TO_LIST_INV]);

(* Theorem: FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm s) *)
(* Proof: by big_lcm_insert, set_lcm_eq_big_lcm *)
val set_lcm_insert = store_thm(
  "set_lcm_insert",
  ``!s. FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm s)``,
  rw[big_lcm_insert, GSYM set_lcm_eq_big_lcm]);

(* Theorem: FINITE s /\ x IN s ==> x divides (set_lcm s) *)
(* Proof:
   Note FINITE s /\ x IN s
    ==> MEM x (SET_TO_LIST s)               by MEM_SET_TO_LIST
    ==> x divides list_lcm (SET_TO_LIST s)  by list_lcm_is_common_multiple
     or x divides (set_lcm s)               by set_lcm_def
*)
val set_lcm_is_common_multiple = store_thm(
  "set_lcm_is_common_multiple",
  ``!x s. FINITE s /\ x IN s ==> x divides (set_lcm s)``,
  rw[set_lcm_def] >>
  `MEM x (SET_TO_LIST s)` by rw[MEM_SET_TO_LIST] >>
  rw[list_lcm_is_common_multiple]);

(* Theorem: FINITE s /\ (!x. x IN s ==> x divides m) ==> set_lcm s divides m *)
(* Proof:
   Note FINITE s
    ==> !x. x IN s <=> MEM x (SET_TO_LIST s)    by MEM_SET_TO_LIST
   Thus list_lcm (SET_TO_LIST s) divides m      by list_lcm_is_least_common_multiple
     or                set_lcm s divides m      by set_lcm_def
*)
val set_lcm_is_least_common_multiple = store_thm(
  "set_lcm_is_least_common_multiple",
  ``!s m. FINITE s /\ (!x. x IN s ==> x divides m) ==> set_lcm s divides m``,
  metis_tac[set_lcm_def, MEM_SET_TO_LIST, list_lcm_is_least_common_multiple]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s) *)
(* Proof:
   By finite induction on s.
   Base: set_lcm {} = PROD_SET {}
           set_lcm {}
         = 1                by set_lcm_empty
         = PROD_SET {}      by PROD_SET_EMPTY
   Step: PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s) ==>
         e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==> set_lcm (e INSERT s) = PROD_SET (e INSERT s)
      Note !z. z IN s ==> coprime e z  by IN_INSERT
      Thus coprime e (PROD_SET s)      by every_coprime_prod_set_coprime
           set_lcm (e INSERT s)
         = lcm e (set_lcm s)      by set_lcm_insert
         = lcm e (PROD_SET s)     by induction hypothesis
         = e * (PROD_SET s)       by LCM_COPRIME
         = PROD_SET (e INSERT s)  by PROD_SET_INSERT, e NOTIN s
*)
val pairwise_coprime_prod_set_eq_set_lcm = store_thm(
  "pairwise_coprime_prod_set_eq_set_lcm",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s)``,
  `!s. FINITE s ==> PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s)` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[set_lcm_empty, PROD_SET_EMPTY] >>
  fs[] >>
  `!z. z IN s ==> coprime e z` by metis_tac[] >>
  `coprime e (PROD_SET s)` by rw[every_coprime_prod_set_coprime] >>
  `set_lcm (e INSERT s) = lcm e (set_lcm s)` by rw[set_lcm_insert] >>
  `_ = lcm e (PROD_SET s)` by rw[] >>
  `_ = e * (PROD_SET s)` by rw[LCM_COPRIME] >>
  `_ = PROD_SET (e INSERT s)` by rw[PROD_SET_INSERT] >>
  rw[]);

(* This is a generalisation of LCM_COPRIME |- !m n. coprime m n ==> (lcm m n = m * n)  *)

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s /\ (!x. x IN s ==> x divides m) ==> (PROD_SET s) divides m *)
(* Proof:
   Note PROD_SET s = set_lcm s      by pairwise_coprime_prod_set_eq_set_lcm
    and set_lcm s divides m         by set_lcm_is_least_common_multiple
    ==> (PROD_SET s) divides m
*)
val pairwise_coprime_prod_set_divides = store_thm(
  "pairwise_coprime_prod_set_divides",
  ``!s m. FINITE s /\ PAIRWISE_COPRIME s /\ (!x. x IN s ==> x divides m) ==> (PROD_SET s) divides m``,
  rw[set_lcm_is_least_common_multiple, GSYM pairwise_coprime_prod_set_eq_set_lcm]);

(* ------------------------------------------------------------------------- *)
(* Nair's Trick - using List LCM directly                                    *)
(* ------------------------------------------------------------------------- *)

(* Overload on consecutive LCM *)
val _ = overload_on("lcm_run", ``\n. list_lcm [1 .. n]``);

(* Theorem: lcm_run n = FOLDL lcm 1 [1 .. n] *)
(* Proof:
     lcm_run n
   = list_lcm [1 .. n]      by notation
   = FOLDL lcm 1 [1 .. n]   by list_lcm_by_FOLDL
*)
val lcm_run_by_FOLDL = store_thm(
  "lcm_run_by_FOLDL",
  ``!n. lcm_run n = FOLDL lcm 1 [1 .. n]``,
  rw[list_lcm_by_FOLDL]);

(* Theorem: lcm_run n = FOLDL lcm 1 [1 .. n] *)
(* Proof:
     lcm_run n
   = list_lcm [1 .. n]      by notation
   = FOLDR lcm 1 [1 .. n]   by list_lcm_by_FOLDR
*)
val lcm_run_by_FOLDR = store_thm(
  "lcm_run_by_FOLDR",
  ``!n. lcm_run n = FOLDR lcm 1 [1 .. n]``,
  rw[list_lcm_by_FOLDR]);

(* Theorem: lcm_run 0 = 1 *)
(* Proof:
     lcm_run 0
   = list_lcm [1 .. 0]    by notation
   = list_lcm []          by listRangeINC_EMPTY, 0 < 1
   = 1                    by list_lcm_nil
*)
val lcm_run_0 = store_thm(
  "lcm_run_0",
  ``lcm_run 0 = 1``,
  rw[listRangeINC_EMPTY]);

(* Theorem: lcm_run 1 = 1 *)
(* Proof:
     lcm_run 1
   = list_lcm [1 .. 1]    by notation
   = list_lcm [1]         by leibniz_vertical_0
   = 1                    by list_lcm_sing
*)
val lcm_run_1 = store_thm(
  "lcm_run_1",
  ``lcm_run 1 = 1``,
  rw[leibniz_vertical_0, list_lcm_sing]);

(* Theorem alias *)
val lcm_run_suc = save_thm("lcm_run_suc", list_lcm_suc);
(* val lcm_run_suc = |- !n. lcm_run (n + 1) = lcm (n + 1) (lcm_run n): thm *)

(* Theorem: 0 < lcm_run n *)
(* Proof:
   Note EVERY_POSITIVE [1 .. n]     by listRangeINC_EVERY
     so lcm_run n
      = list_lcm [1 .. n]           by notation
      > 0                           by list_lcm_pos
*)
val lcm_run_pos = store_thm(
  "lcm_run_pos",
  ``!n. 0 < lcm_run n``,
  rw[list_lcm_pos, listRangeINC_EVERY]);

(* Theorem: (lcm_run 2 = 2) /\ (lcm_run 3 = 6) /\ (lcm_run 4 = 12) /\ (lcm_run 5 = 60) /\ ...  *)
(* Proof: by evaluation *)
val lcm_run_small = store_thm(
  "lcm_run_small",
  ``(lcm_run 2 = 2) /\ (lcm_run 3 = 6) /\ (lcm_run 4 = 12) /\ (lcm_run 5 = 60) /\
   (lcm_run 6 = 60) /\ (lcm_run 7 = 420) /\ (lcm_run 8 = 840) /\ (lcm_run 9 = 2520)``,
  EVAL_TAC);

(* Theorem: (n + 1) divides lcm_run (n + 1) /\ (lcm_run n) divides lcm_run (n + 1) *)
(* Proof:
   If n = 0,
      Then 0 + 1 = 1                by arithmetic
       and lcm_run 0 = 1            by lcm_run_0
      Hence true                    by ONE_DIVIDES_ALL
   If n <> 0,
      Then n - 1 + 1 = n                       by arithmetic, 0 < n
           lcm_run (n + 1)
         = list_lcm [1 .. (n + 1)]             by notation
         = list_lcm (SNOC (n + 1) [1 .. n])    by leibniz_vertical_snoc
         = lcm (n + 1) (list_lcm [1 .. n])     by list_lcm_snoc]
         = lcm (n + 1) (lcm_run n)             by notation
      Hence true                               by LCM_DIVISORS
*)
val lcm_run_divisors = store_thm(
  "lcm_run_divisors",
  ``!n. (n + 1) divides lcm_run (n + 1) /\ (lcm_run n) divides lcm_run (n + 1)``,
  strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `(n - 1 + 1 = n) /\ (n - 1 + 2 = n + 1)` by decide_tac >>
  `lcm_run (n + 1) = list_lcm (SNOC (n + 1) [1 .. n])` by metis_tac[leibniz_vertical_snoc] >>
  `_ = lcm (n + 1) (lcm_run n)` by rw[list_lcm_snoc] >>
  rw[LCM_DIVISORS]);

(* Theorem: lcm_run n <= lcm_run (n + 1) *)
(* Proof:
   Note 0 < lcm_run n                  by lcm_run_pos
      lcm_run (n + 1)
    = list_lcm [1 .. (n + 1)]          by notation
    = list_lcm (SNOC (n + 1) [1 .. n]) by listRangeINC_SNOC, 1 <= n + 1
    = lcm (n + 1) (lcm_run n)          by list_lcm_snoc
    >= lcm_run n                       by LCM_LE, 0 < n + 1
*)
val lcm_run_monotone = store_thm(
  "lcm_run_monotone",
  ``!n. lcm_run n <= lcm_run (n + 1)``,
  rw[lcm_run_pos, listRangeINC_SNOC, list_lcm_snoc, LCM_LE]);

(* Another proof of same theorem *)

(* Theorem: lcm_run n <= lcm_run (n + 1) *)
(* Proof:
   Note lcm_run n divides lcm_run (n + 1)   by lcm_run_divisors
    and 0 < lcm_run (n + 1)  ]              by lcm_run_pos
     so lcm_run n <= lcm_run (n + 1)        by DIVIDES_LE
*)
val lcm_run_monotone = store_thm(
  "lcm_run_monotone",
  ``!n. lcm_run n <= lcm_run (n + 1)``,
  rw[lcm_run_divisors, lcm_run_pos, DIVIDES_LE]);

(* Theorem: 2 ** n <= lcm_run (n + 1) *)
(* Proof:
     lcm_run (n + 1)
   = list_lcm [1 .. (n + 1)]   by notation
   >= 2 ** n                   by lcm_lower_bound
*)
val lcm_run_lower = save_thm("lcm_run_lower", lcm_lower_bound);
(*
val lcm_run_lower = |- !n. 2 ** n <= lcm_run (n + 1): thm
*)

(* Theorem: !n k. k <= n ==> leibniz n k divides lcm_run (n + 1) *)
(* Proof: by notation, leibniz_vertical_divisor *)
val lcm_run_leibniz_divisor = save_thm("lcm_run_leibniz_divisor", leibniz_vertical_divisor);
(*
val lcm_run_leibniz_divisor = |- !n k. k <= n ==> leibniz n k divides lcm_run (n + 1): thm
*)

(* Theorem: n * 4 ** n <= lcm_run (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n.
   Let m = 2 * n.

   Claim: (m + 1) * binomial m n divides lcm_run (m + 1)       [1]
   Proof: Note n <= m                                          by LESS_MONO_MULT, 1 <= 2
           ==> (leibniz m n) divides lcm_run (m + 1)           by lcm_run_leibniz_divisor, n <= m
            or (m + 1) * binomial m n divides lcm_run (m + 1)  by leibniz_def

   Claim: n * binomial m n divides lcm_run (m + 1)             [2]
   Proof: Note 0 < m /\ n <= m - 1                             by 0 < n
           and m - 1 + 1 = m                                   by 0 < m
          Thus (leibniz (m - 1) n) divides lcm_run m           by lcm_run_leibniz_divisor, n <= m - 1
          Note (lcm_run m) divides lcm_run (m + 1)             by lcm_run_divisors
            so (leibniz (m - 1) n) divides lcm_run (m + 1)     by DIVIDES_TRANS
           and leibniz (m - 1) n
             = (m - n) * binomial m n                          by leibniz_up_alt
             = n * binomial m n                                by m - n = n

   Note coprime n (m + 1)                         by GCD_EUCLID, GCD_1, 1 < n
   Thus lcm (n * binomial m n) ((m + 1) * binomial m n)
      = n * (m + 1) * binomial m n                by LCM_COMMON_COPRIME
      = n * ((m + 1) * binomial m n)              by MULT_ASSOC
      = n * leibniz m n                           by leibniz_def
    ==> n * leibniz m n divides lcm_run (m + 1)   by LCM_DIVIDES, [1], [2]
   Note 0 < lcm_run (m + 1)                       by lcm_run_pos
     or n * leibniz m n <= lcm_run (m + 1)        by DIVIDES_LE, 0 < lcm_run (m + 1)
    Now          4 ** n <= leibniz m n            by leibniz_middle_lower
     so      n * 4 ** n <= n * leibniz m n        by LESS_MONO_MULT, MULT_COMM
     or      n * 4 ** n <= lcm_run (m + 1)        by LESS_EQ_TRANS
*)
val lcm_run_lower_odd = store_thm(
  "lcm_run_lower_odd",
  ``!n. n * 4 ** n <= lcm_run (2 * n + 1)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `m = 2 * n` >>
  `(m + 1) * binomial m n divides lcm_run (m + 1)` by
  (`n <= m` by rw[Abbr`m`] >>
  metis_tac[lcm_run_leibniz_divisor, leibniz_def]) >>
  `n * binomial m n divides lcm_run (m + 1)` by
    (`0 < m /\ n <= m - 1` by rw[Abbr`m`] >>
  `m - 1 + 1 = m` by decide_tac >>
  `(leibniz (m - 1) n) divides lcm_run m` by metis_tac[lcm_run_leibniz_divisor] >>
  `(lcm_run m) divides lcm_run (m + 1)` by rw[lcm_run_divisors] >>
  `leibniz (m - 1) n = (m - n) * binomial m n` by rw[leibniz_up_alt] >>
  `_ = n * binomial m n` by rw[Abbr`m`] >>
  metis_tac[DIVIDES_TRANS]) >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  `lcm (n * binomial m n) ((m + 1) * binomial m n) = n * (m + 1) * binomial m n` by rw[LCM_COMMON_COPRIME] >>
  `_ = n * leibniz m n` by rw[leibniz_def, MULT_ASSOC] >>
  `n * leibniz m n divides lcm_run (m + 1)` by metis_tac[LCM_DIVIDES] >>
  `n * leibniz m n <= lcm_run (m + 1)` by rw[DIVIDES_LE, lcm_run_pos] >>
  `4 ** n <= leibniz m n` by rw[leibniz_middle_lower, Abbr`m`] >>
  metis_tac[LESS_MONO_MULT, MULT_COMM, LESS_EQ_TRANS]);

(* Theorem: n * 4 ** n <= lcm_run (2 * (n + 1)) *)
(* Proof:
     lcm_run (2 * (n + 1))
   = lcm_run (2 * n + 2)        by arithmetic
   >= lcm_run (2 * n + 1)       by lcm_run_monotone
   >= n * 4 ** n                by lcm_run_lower_odd
*)
val lcm_run_lower_even = store_thm(
  "lcm_run_lower_even",
  ``!n. n * 4 ** n <= lcm_run (2 * (n + 1))``,
  rpt strip_tac >>
  `2 * (n + 1) = 2 * n + 1 + 1` by decide_tac >>
  metis_tac[lcm_run_monotone, lcm_run_lower_odd, LESS_EQ_TRANS]);

(* Theorem: 7 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   If ODD n, ?k. n = SUC (2 * k)       by ODD_EXISTS,
      When 5 <= 7 <= n = 2 * k + 1     by ADD1
           2 <= k                      by arithmetic
       and lcm_run n
         = lcm_run (2 * k + 1)         by notation
         >= k * 4 ** k                 by lcm_run_lower_odd
         >= 2 * 4 ** k                 by k >= 2, LESS_MONO_MULT
          = 2 * 2 ** (2 * k)           by EXP_EXP_MULT
          = 2 ** SUC (2 * k)           by EXP
          = 2 ** n                     by n = SUC (2 * k)
   If EVEN n, ?m. n = 2 * m            by EVEN_EXISTS
      Note ODD 7 /\ ODD 9              by arithmetic
      If n = 8,
         LHS = 2 ** 8 = 256,
         RHS = lcm_run 8 = 840         by lcm_run_small
         Hence true.
      Otherwise, 10 <= n               by 7 <= n, n <> 7, n <> 8, n <> 9
      Since 0 < n, 0 < m               by MULT_EQ_0
         so ?k. m = SUC k              by num_CASES
       When 10 <= n = 2 * (k + 1)      by ADD1
             4 <= k                    by arithmetic
       and lcm_run n
         = lcm_run (2 * (k + 1))       by notation
         >= k * 4 ** k                 by lcm_run_lower_even
         >= 4 * 4 ** k                 by k >= 4, LESS_MONO_MULT
          = 4 ** SUC k                 by EXP
          = 4 ** m                     by notation
          = 2 ** (2 * m)               by EXP_EXP_MULT
          = 2 ** n                     by n = 2 * m
*)
val lcm_run_lower_better = store_thm(
  "lcm_run_lower_better",
  ``!n. 7 <= n ==> 2 ** n <= lcm_run n``,
  rpt strip_tac >>
  Cases_on `ODD n` >| [
    `?k. n = SUC (2 * k)` by rw[GSYM ODD_EXISTS] >>
    `2 <= k` by decide_tac >>
    `2 * 4 ** k <= k * 4 ** k` by rw[LESS_MONO_MULT] >>
    `lcm_run n = lcm_run (2 * k + 1)` by rw[ADD1] >>
    `2 ** n = 2 * 2 ** (2 * k)` by rw[EXP] >>
    `_ = 2 * 4 ** k` by rw[EXP_EXP_MULT] >>
    metis_tac[lcm_run_lower_odd, LESS_EQ_TRANS],
    `ODD 7 /\ ODD 9` by rw[] >>
    `EVEN n /\ n <> 7 /\ n <> 9` by metis_tac[ODD_EVEN] >>
    `?m. n = 2 * m` by rw[GSYM EVEN_EXISTS] >>
    `m <> 0` by decide_tac >>
    `?k. m = SUC k` by metis_tac[num_CASES] >>
    Cases_on `n = 8` >-
    rw[lcm_run_small] >>
    `4 <= k` by decide_tac >>
    `4 * 4 ** k <= k * 4 ** k` by rw[LESS_MONO_MULT] >>
    `lcm_run n = lcm_run (2 * (k + 1))` by rw[ADD1] >>
    `2 ** n = 4 ** m` by rw[EXP_EXP_MULT] >>
    `_ = 4 * 4 ** k` by rw[EXP] >>
    metis_tac[lcm_run_lower_even, LESS_EQ_TRANS]
  ]);

(* A very good result, another major theorem. *)

(* Theorem: ODD n ==> (HALF n) * HALF (2 ** n) <= lcm_run n *)
(* Proof:
   Let k = HALF n.
   Then n = 2 * k + 1              by ODD_HALF
    and HALF (2 ** n)
      = HALF (2 ** (2 * k + 1))    by above
      = HALF (2 ** (SUC (2 * k)))  by ADD1
      = HALF (2 * 2 ** (2 * k))    by EXP
      = 2 ** (2 * k)               by HALF_TWICE
      = 4 ** k                     by EXP_EXP_MULT
   Since k * 4 ** k <= lcm_run (2 * k + 1)  by lcm_run_lower_odd
   The result follows.
*)
val lcm_run_odd_lower = store_thm(
  "lcm_run_odd_lower",
  ``!n. ODD n ==> (HALF n) * HALF (2 ** n) <= lcm_run n``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `n = 2 * k + 1` by rw[ODD_HALF, Abbr`k`] >>
  `HALF (2 ** n) = HALF (2 ** (SUC (2 * k)))` by rw[ADD1] >>
  `_ = HALF (2 * 2 ** (2 * k))` by rw[EXP] >>
  `_ = 2 ** (2 * k)` by rw[HALF_TWICE] >>
  `_ = 4 ** k` by rw[EXP_EXP_MULT] >>
  metis_tac[lcm_run_lower_odd]);

(* Theorem: EVEN n ==> HALF (n - 2) * HALF (HALF (2 ** n)) <= lcm_run n *)
(* Proof:
   If n = 0, HALF (n - 2) = 0, so trivially true.
   If n <> 0,
   Let h = HALF n.
   Then n = 2 * h         by EVEN_HALF
   Note h <> 0            by n <> 0
     so ?k. h = k + 1     by num_CASES, ADD1
     or n = 2 * k + 2     by n = 2 * (k + 1)
    and HALF (HALF (2 ** n))
      = HALF (HALF (2 ** (2 * k + 2)))        by above
      = HALF (HALF (2 ** SUC (SUC (2 * k))))  by ADD1
      = HALF (HALF (2 * (2 * 2 ** (2 * k))))  by EXP
      = 2 ** (2 * k)                          by HALF_TWICE
      = 4 ** k                                by EXP_EXP_MULT
   Also n - 2 = 2 * k                         by 0 < n, n = 2 * k + 2
     so HALF (n - 2) = k                      by HALF_TWICE
   Since k * 4 ** k <= lcm_run (2 * (k + 1))  by lcm_run_lower_even
   The result follows.
*)
Theorem lcm_run_even_lower:
  !n. EVEN n ==> HALF (n - 2) * HALF (HALF (2 ** n)) <= lcm_run n
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >- rw[] >>
  qabbrev_tac `h = HALF n` >>
  `n = 2 * h` by rw[EVEN_HALF, Abbr`h`] >>
  `h <> 0` by rw[Abbr`h`] >>
  `?k. h = k + 1` by metis_tac[num_CASES, ADD1] >>
  `HALF (HALF (2 ** n)) = HALF (HALF (2 ** SUC (SUC (2 * k))))` by simp[ADD1] >>
  `_ = HALF (HALF (2 * (2 * 2 ** (2 * k))))` by rw[EXP] >>
  `_ = 2 ** (2 * k)` by rw[HALF_TWICE] >>
  `_ = 4 ** k` by rw[EXP_EXP_MULT] >>
  `n - 2 = 2 * k` by decide_tac >>
  `HALF (n - 2) = k` by rw[HALF_TWICE] >>
  metis_tac[lcm_run_lower_even]
QED

(* Theorem: ODD n /\ 5 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   This follows by lcm_run_odd_lower
   if we can show: 2 ** n <= HALF n * HALF (2 ** n)

   Note HALF 5 = 2            by arithmetic
    and HALF 5 <= HALF n      by DIV_LE_MONOTONE, 0 < 2
   Also n <> 0                by 5 <= n
     so ?m. n = SUC m         by num_CASES
        HALF n * HALF (2 ** n)
      = HALF n * HALF (2 * 2 ** m)     by EXP
      = HALF n * 2 ** m                by HALF_TWICE
      >= 2 * 2 ** m                    by LESS_MONO_MULT
       = 2 ** (SUC m)                  by EXP
       = 2 ** n                        by n = SUC m
*)
val lcm_run_odd_lower_alt = store_thm(
  "lcm_run_odd_lower_alt",
  ``!n. ODD n /\ 5 <= n ==> 2 ** n <= lcm_run n``,
  rpt strip_tac >>
  `2 ** n <= HALF n * HALF (2 ** n)` by
  (`HALF 5 = 2` by EVAL_TAC >>
  `HALF 5 <= HALF n` by rw[DIV_LE_MONOTONE] >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `HALF n * HALF (2 ** n) = HALF n * HALF (2 * 2 ** m)` by rw[EXP] >>
  `_ = HALF n * 2 ** m` by rw[HALF_TWICE] >>
  `2 * 2 ** m <= HALF n * 2 ** m` by rw[LESS_MONO_MULT] >>
  rw[EXP]) >>
  metis_tac[lcm_run_odd_lower, LESS_EQ_TRANS]);

(* Theorem: EVEN n /\ 8 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   If n = 8,
      Then 2 ** 8 = 256         by arithmetic
       and lcm_run 8 = 840      by lcm_run_small
      Thus true.
   If n <> 8,
      Note ODD 9                by arithmetic
        so n <> 9               by ODD_EVEN
        or 10 <= n              by 8 <= n, n <> 9
      This follows by lcm_run_even_lower
      if we can show: 2 ** n <= HALF (n - 2) * HALF (HALF (2 ** n))

       Let m = n - 2.
      Then 8 <= m               by arithmetic
        or HALF 8 <= HALF m     by DIV_LE_MONOTONE, 0 < 2
       and HALF 8 = 4 = 2 * 2   by arithmetic
       Now n = SUC (SUC m)      by arithmetic
           HALF m * HALF (HALF (2 ** n))
         = HALF m * HALF (HALF (2 ** (SUC (SUC m))))    by above
         = HALF m * HALF (HALF (2 * (2 * 2 ** m)))      by EXP
         = HALF m * 2 ** m                              by HALF_TWICE
         >= 4 * 2 ** m          by LESS_MONO_MULT
          = 2 * (2 * 2 ** m)    by MULT_ASSOC
          = 2 ** (SUC (SUC m))  by EXP
          = 2 ** n              by n = SUC (SUC m)
*)
val lcm_run_even_lower_alt = store_thm(
  "lcm_run_even_lower_alt",
  ``!n. EVEN n /\ 8 <= n ==> 2 ** n <= lcm_run n``,
  rpt strip_tac >>
  Cases_on `n = 8` >-
  rw[lcm_run_small] >>
  `2 ** n <= HALF (n - 2) * HALF (HALF (2 ** n))` by
  (`ODD 9` by rw[] >>
  `n <> 9` by metis_tac[ODD_EVEN] >>
  `8 <= n - 2` by decide_tac >>
  qabbrev_tac `m = n - 2` >>
  `n = SUC (SUC m)` by rw[Abbr`m`] >>
  `HALF m * HALF (HALF (2 ** n)) = HALF m * HALF (HALF (2 * (2 * 2 ** m)))` by rw[EXP] >>
  `_ = HALF m * 2 ** m` by rw[HALF_TWICE] >>
  `HALF 8 <= HALF m` by rw[DIV_LE_MONOTONE] >>
  `HALF 8 = 4` by EVAL_TAC >>
  `2 * (2 * 2 ** m) <= HALF m * 2 ** m` by rw[LESS_MONO_MULT] >>
  rw[EXP]) >>
  metis_tac[lcm_run_even_lower, LESS_EQ_TRANS]);

(* Theorem: 7 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   If EVEN n,
      Node ODD 7                 by arithmetic
        so n <> 7                by EVEN_ODD
        or 8 <= n                by arithmetic
      Hence true                 by lcm_run_even_lower_alt
   If ~EVEN n, then ODD n        by EVEN_ODD
      Note 7 <= n ==> 5 <= n     by arithmetic
      Hence true                 by lcm_run_odd_lower_alt
*)
val lcm_run_lower_better = store_thm(
  "lcm_run_lower_better",
  ``!n. 7 <= n ==> 2 ** n <= lcm_run n``,
  rpt strip_tac >>
  `EVEN n \/ ODD n` by rw[EVEN_OR_ODD] >| [
    `ODD 7` by rw[] >>
    `n <> 7` by metis_tac[ODD_EVEN] >>
    rw[lcm_run_even_lower_alt],
    rw[lcm_run_odd_lower_alt]
  ]);

(* Another way to prove this result of Nair. *)

(* ------------------------------------------------------------------------- *)
(* Nair's Trick -- rework                                                    *)
(* ------------------------------------------------------------------------- *)

(*
Picture:
leibniz_lcm_property    |- !n. lcm_run (n + 1) = list_lcm (leibniz_horizontal n)
leibniz_horizontal_mem  |- !n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)
so:
lcm_run (2*n + 1) = list_lcm (leibniz_horizontal (2*n))
and leibniz_horizontal (2*n) has members: 0, 1, 2, ...., n, (n + 1), ....., (2*n)
note: n <= 2*n, always, (n+1) <= 2*n = (n+n) when 1 <= n.
thus:
Both  B = (leibniz 2*n n) and C = (leibniz 2*n n+1) divides lcm_run (2*n + 1),
  or  (lcm B C) divides lcm_run (2*n + 1).
But   (lcm B C) = (lcm B A)    where A = (leibniz 2*n-1 n).
By leibniz_def    |- !n k. leibniz n k = (n + 1) * binomial n k
By leibniz_up_alt |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
 so B = (2*n + 1) * binomial 2*n n
and A = (2*n - n) * binomial 2*n n = n * binomial 2*n n
and lcm B A = lcm ((2*n + 1) * binomial 2*n n) (n * binomial 2*n n)
            = (lcm (2*n + 1) n) * binomial 2*n n        by LCM_COMMON_FACTOR
            = n * (2*n + 1) * binomial 2*n n            by coprime (2*n+1) n
            = n * (leibniz 2*n n)                       by leibniz_def
*)

(* Theorem: 0 < n ==> n * (leibniz (2 * n) n) divides lcm_run (2 * n + 1) *)
(* Proof:
   Note 1 <= n                 by 0 < n
   Let m = 2 * n,
   Then n <= 2 * n = m, and
        n + 1 <= n + n = m     by arithmetic
   Also coprime n (m + 1)      by GCD_EUCLID

   Identify a triplet:
   Let t = triplet (m - 1) n
   Then t.a = leibniz (m - 1) n       by triplet_def
        t.b = leibniz m n             by triplet_def
        t.c = leibniz m (n + 1)       by triplet_def

   Note MEM t.b (leibniz_horizontal m)        by leibniz_horizontal_mem, n <= m
    and MEM t.c (leibniz_horizontal m)        by leibniz_horizontal_mem, n + 1 <= m
    ==> lcm t.b t.c divides list_lcm (leibniz_horizontal m)  by list_lcm_divisor_lcm_pair
                          = lcm_run (m + 1)   by leibniz_lcm_property

   Let k = binomial m n.
        lcm t.b t.c
      = lcm t.b t.a                           by leibniz_triplet_lcm
      = lcm ((m + 1) * k) t.a                 by leibniz_def
      = lcm ((m + 1) * k) ((m - n) * k)       by leibniz_up_alt
      = lcm ((m + 1) * k) (n * k)             by m = 2 * n
      = n * (m + 1) * k                       by LCM_COMMON_COPRIME, LCM_SYM, coprime n (m + 1)
      = n * leibniz m n                       by leibniz_def
   Thus (n * leibniz m n) divides lcm_run (m + 1)
*)
val lcm_run_odd_factor = store_thm(
  "lcm_run_odd_factor",
  ``!n. 0 < n ==> n * (leibniz (2 * n) n) divides lcm_run (2 * n + 1)``,
  rpt strip_tac >>
  qabbrev_tac `m = 2 * n` >>
  `n <= m /\ n + 1 <= m` by rw[Abbr`m`] >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  qabbrev_tac `t = triplet (m - 1) n` >>
  `t.a = leibniz (m - 1) n` by rw[triplet_def, Abbr`t`] >>
  `t.b = leibniz m n` by rw[triplet_def, Abbr`t`] >>
  `t.c = leibniz m (n + 1)` by rw[triplet_def, Abbr`t`] >>
  `t.b divides lcm_run (m + 1)` by metis_tac[lcm_run_leibniz_divisor] >>
  `t.c divides lcm_run (m + 1)` by metis_tac[lcm_run_leibniz_divisor] >>
  `lcm t.b t.c divides lcm_run (m + 1)` by rw[LCM_IS_LEAST_COMMON_MULTIPLE] >>
  qabbrev_tac `k = binomial m n` >>
  `lcm t.b t.c = lcm t.b t.a` by rw[leibniz_triplet_lcm, Abbr`t`] >>
  `_ = lcm ((m + 1) * k) ((m - n) * k)` by rw[leibniz_def, leibniz_up_alt, Abbr`k`] >>
  `_ = lcm ((m + 1) * k) (n * k)` by rw[Abbr`m`] >>
  `_ = n * (m + 1) * k` by rw[LCM_COMMON_COPRIME, LCM_SYM] >>
  `_ = n * leibniz m n` by rw[leibniz_def, Abbr`k`] >>
  metis_tac[]);

(* Theorem: n * 4 ** n <= lcm_run (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n.
   Note     4 ** n <= leibniz (2 * n) n        by leibniz_middle_lower
     so n * 4 ** n <= n * leibniz (2 * n) n    by LESS_MONO_MULT, MULT_COMM
    Let k = n * leibniz (2 * n) n.
   Then k divides lcm_run (2 * n + 1)          by lcm_run_odd_factor
    Now       0 < lcm_run (2 * n + 1)          by lcm_run_pos
     so             k <= lcm_run (2 * n + 1)   by DIVIDES_LE
   Overall n * 4 ** n <= lcm_run (2 * n + 1)   by LESS_EQ_TRANS
*)
val lcm_run_lower_odd = store_thm(
  "lcm_run_lower_odd",
  ``!n. n * 4 ** n <= lcm_run (2 * n + 1)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  `4 ** n <= leibniz (2 * n) n` by rw[leibniz_middle_lower] >>
  `n * 4 ** n <= n * leibniz (2 * n) n` by rw[LESS_MONO_MULT, MULT_COMM] >>
  `n * leibniz (2 * n) n <= lcm_run (2 * n + 1)` by rw[lcm_run_odd_factor, lcm_run_pos, DIVIDES_LE] >>
  rw[LESS_EQ_TRANS]);

(* Another direct proof of the same theorem *)

(* Theorem: n * 4 ** n <= lcm_run (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n, or 1 <= n                 by arithmetic

   Let m = 2 * n,
   Then n <= 2 * n = m, and
        n + 1 <= n + n = m     by arithmetic, 1 <= n
   Also coprime n (m + 1)      by GCD_EUCLID

   Identify a triplet:
   Let t = triplet (m - 1) n
   Then t.a = leibniz (m - 1) n       by triplet_def
        t.b = leibniz m n             by triplet_def
        t.c = leibniz m (n + 1)       by triplet_def

   Note MEM t.b (leibniz_horizontal m)        by leibniz_horizontal_mem, n <= m
    and MEM t.c (leibniz_horizontal m)        by leibniz_horizontal_mem, n + 1 <= m
    and POSITIVE (leibniz_horizontal m)       by leibniz_horizontal_pos_alt
    ==> lcm t.b t.c <= list_lcm (leibniz_horizontal m)  by list_lcm_lower_by_lcm_pair
                     = lcm_run (m + 1)        by leibniz_lcm_property

   Let k = binomial m n.
        lcm t.b t.c
      = lcm t.b t.a                           by leibniz_triplet_lcm
      = lcm ((m + 1) * k) t.a                 by leibniz_def
      = lcm ((m + 1) * k) ((m - n) * k)       by leibniz_up_alt
      = lcm ((m + 1) * k) (n * k)             by m = 2 * n
      = n * (m + 1) * k                       by LCM_COMMON_COPRIME, LCM_SYM, coprime n (m + 1)
      = n * leibniz m n                       by leibniz_def
   Thus (n * leibniz m n) divides lcm_run (m + 1)

      Note     4 ** n <= leibniz m n          by leibniz_middle_lower
        so n * 4 ** n <= n * leibniz m n      by LESS_MONO_MULT, MULT_COMM
   Overall n * 4 ** n <= lcm_run (2 * n + 1)  by LESS_EQ_TRANS
*)
val lcm_run_lower_odd = store_thm(
  "lcm_run_lower_odd",
  ``!n. n * 4 ** n <= lcm_run (2 * n + 1)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  qabbrev_tac `m = 2 * n` >>
  `n <= m /\ n + 1 <= m` by rw[Abbr`m`] >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  qabbrev_tac `t = triplet (m - 1) n` >>
  `t.a = leibniz (m - 1) n` by rw[triplet_def, Abbr`t`] >>
  `t.b = leibniz m n` by rw[triplet_def, Abbr`t`] >>
  `t.c = leibniz m (n + 1)` by rw[triplet_def, Abbr`t`] >>
  `MEM t.b (leibniz_horizontal m)` by metis_tac[leibniz_horizontal_mem] >>
  `MEM t.c (leibniz_horizontal m)` by metis_tac[leibniz_horizontal_mem] >>
  `POSITIVE (leibniz_horizontal m)` by metis_tac[leibniz_horizontal_pos_alt] >>
  `lcm t.b t.c <= lcm_run (m + 1)` by metis_tac[leibniz_lcm_property, list_lcm_lower_by_lcm_pair] >>
  `lcm t.b t.c = n * leibniz m n` by
  (qabbrev_tac `k = binomial m n` >>
  `lcm t.b t.c = lcm t.b t.a` by rw[leibniz_triplet_lcm, Abbr`t`] >>
  `_ = lcm ((m + 1) * k) ((m - n) * k)` by rw[leibniz_def, leibniz_up_alt, Abbr`k`] >>
  `_ = lcm ((m + 1) * k) (n * k)` by rw[Abbr`m`] >>
  `_ = n * (m + 1) * k` by rw[LCM_COMMON_COPRIME, LCM_SYM] >>
  `_ = n * leibniz m n` by rw[leibniz_def, Abbr`k`] >>
  rw[]) >>
  `4 ** n <= leibniz m n` by rw[leibniz_middle_lower, Abbr`m`] >>
  `n * 4 ** n <= n * leibniz m n` by rw[LESS_MONO_MULT] >>
  metis_tac[LESS_EQ_TRANS]);

(* Theorem: ODD n ==> (2 ** n <= lcm_run n <=> 5 <= n) *)
(* Proof:
   If part: 2 ** n <= lcm_run n ==> 5 <= n
      By contradiction, suppose n < 5.
      By ODD n, n = 1 or n = 3.
      If n = 1, LHS = 2 ** 1 = 2         by arithmetic
                RHS = lcm_run 1 = 1      by lcm_run_1
                Hence false.
      If n = 3, LHS = 2 ** 3 = 8         by arithmetic
                RHS = lcm_run 3 = 6      by lcm_run_small
                Hence false.
   Only-if part: 5 <= n ==> 2 ** n <= lcm_run n
      Let h = HALF n.
      Then n = 2 * h + 1                 by ODD_HALF
        so          4 <= 2 * h           by 5 - 1 = 4
        or          2 <= h               by arithmetic
       ==> 2 * 4 ** h <= h * 4 ** h      by LESS_MONO_MULT
       But 2 * 4 ** h
         = 2 * (2 ** 2) ** h             by arithmetic
         = 2 * 2 ** (2 * h)              by EXP_EXP_MULT
         = 2 ** SUC (2 * h)              by EXP
         = 2 ** n                        by ADD1, n = 2 * h + 1
      With h * 4 ** h <= lcm_run n       by lcm_run_lower_odd
        or     2 ** n <= lcm_run n       by LESS_EQ_TRANS
*)
val lcm_run_lower_odd_iff = store_thm(
  "lcm_run_lower_odd_iff",
  ``!n. ODD n ==> (2 ** n <= lcm_run n <=> 5 <= n)``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n < 5` by decide_tac >>
    `EVEN 0 /\ EVEN 2 /\ EVEN 4` by rw[] >>
    `n <> 0 /\ n <> 2 /\ n <> 4` by metis_tac[EVEN_ODD] >>
    `(n = 1) \/ (n = 3)` by decide_tac >-
    fs[] >>
    fs[lcm_run_small],
    qabbrev_tac `h = HALF n` >>
    `n = 2 * h + 1` by rw[ODD_HALF, Abbr`h`] >>
    `2 * 4 ** h <= h * 4 ** h` by rw[] >>
    `2 * 4 ** h = 2 * 2 ** (2 * h)` by rw[EXP_EXP_MULT] >>
    `_ = 2 ** n` by rw[GSYM EXP] >>
    `h * 4 ** h <= lcm_run n` by rw[lcm_run_lower_odd] >>
    decide_tac
  ]);

(* Theorem: EVEN n ==> (2 ** n <= lcm_run n <=> (n = 0) \/ 8 <= n) *)
(* Proof:
   If part: 2 ** n <= lcm_run n ==> (n = 0) \/ 8 <= n
      By contradiction, suppose n <> 0 /\ n < 8.
      By EVEN n, n = 2 or n = 4 or n = 6.
         If n = 2, LHS = 2 ** 2 = 4              by arithmetic
                   RHS = lcm_run 2 = 2           by lcm_run_small
                   Hence false.
         If n = 4, LHS = 2 ** 4 = 16             by arithmetic
                   RHS = lcm_run 4 = 12          by lcm_run_small
                   Hence false.
         If n = 6, LHS = 2 ** 6 = 64             by arithmetic
                   RHS = lcm_run 6 = 60          by lcm_run_small
                   Hence false.
   Only-if part: (n = 0) \/ 8 <= n ==> 2 ** n <= lcm_run n
         If n = 0, LHS = 2 ** 0 = 1              by arithmetic
                   RHS = lcm_run 0 = 1           by lcm_run_0
                   Hence true.
         If n = 8, LHS = 2 ** 8 = 256            by arithmetic
                   RHS = lcm_run 8 = 840         by lcm_run_small
                   Hence true.
         Otherwise, 10 <= n, since ODD 9.
         Let h = HALF n, k = h - 1.
         Then n = 2 * h                          by EVEN_HALF
                = 2 * (k + 1)                    by k = h - 1
                = 2 * k + 2                      by arithmetic
          But lcm_run (2 * k + 1) <= lcm_run (2 * k + 2)  by lcm_run_monotone
          and k * 4 ** k <= lcm_run (2 * k + 1)           by lcm_run_lower_odd

          Now          5 <= h                    by 10 <= h
           so          4 <= k                    by k = h - 1
          ==> 4 * 4 ** k <= k * 4 ** k           by LESS_MONO_MULT

              4 * 4 ** k
            = (2 ** 2) * (2 ** 2) ** k           by arithmetic
            = (2 ** 2) * (2 ** (2 * k))          by EXP_EXP_MULT
            = 2 ** (2 * k + 2)                   by EXP_ADD
            = 2 ** n                             by n = 2 * k + 2

         Overall 2 ** n <= lcm_run n             by LESS_EQ_TRANS
*)
val lcm_run_lower_even_iff = store_thm(
  "lcm_run_lower_even_iff",
  ``!n. EVEN n ==> (2 ** n <= lcm_run n <=> (n = 0) \/ 8 <= n)``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n < 8` by decide_tac >>
    `ODD 1 /\ ODD 3 /\ ODD 5 /\ ODD 7` by rw[] >>
    `n <> 1 /\ n <> 3 /\ n <> 5 /\ n <> 7` by metis_tac[EVEN_ODD] >>
    `(n = 2) \/ (n = 4) \/ (n = 6)` by decide_tac >-
    fs[lcm_run_small] >-
    fs[lcm_run_small] >>
    fs[lcm_run_small],
    fs[lcm_run_0],
    Cases_on `n = 8` >-
    rw[lcm_run_small] >>
    `ODD 9` by rw[] >>
    `n <> 9` by metis_tac[EVEN_ODD] >>
    `10 <= n` by decide_tac >>
    qabbrev_tac `h = HALF n` >>
    `n = 2 * h` by rw[EVEN_HALF, Abbr`h`] >>
    qabbrev_tac `k = h - 1` >>
    `lcm_run (2 * k + 1) <= lcm_run (2 * k + 1 + 1)` by rw[lcm_run_monotone] >>
    `2 * k + 1 + 1 = n` by rw[Abbr`k`] >>
    `k * 4 ** k <= lcm_run (2 * k + 1)` by rw[lcm_run_lower_odd] >>
    `4 * 4 ** k <= k * 4 ** k` by rw[Abbr`k`] >>
    `4 * 4 ** k = 2 ** 2 * 2 ** (2 * k)` by rw[EXP_EXP_MULT] >>
    `_ = 2 ** (2 * k + 2)` by rw[GSYM EXP_ADD] >>
    `_ = 2 ** n` by rw[] >>
    metis_tac[LESS_EQ_TRANS]
  ]);

(* Theorem: 2 ** n <= lcm_run n <=> (n = 0) \/ (n = 5) \/ 7 <= n *)
(* Proof:
   If EVEN n,
      Then n <> 5, n <> 7, so 8 <= n    by arithmetic
      Thus true                         by lcm_run_lower_even_iff
   If ~EVEN n, then ODD n               by EVEN_ODD
      Then n <> 0, n <> 6, so 5 <= n    by arithmetic
      Thus true                         by lcm_run_lower_odd_iff
*)
val lcm_run_lower_better_iff = store_thm(
  "lcm_run_lower_better_iff",
  ``!n. 2 ** n <= lcm_run n <=> (n = 0) \/ (n = 5) \/ 7 <= n``,
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `ODD 5 /\ ODD 7` by rw[] >>
    `n <> 5 /\ n <> 7` by metis_tac[EVEN_ODD] >>
    metis_tac[lcm_run_lower_even_iff, DECIDE``8 <= n <=> (7 <= n /\ n <> 7)``],
    `EVEN 0 /\ EVEN 6` by rw[] >>
    `ODD n /\ n <> 0 /\ n <> 6` by metis_tac[EVEN_ODD] >>
    metis_tac[lcm_run_lower_odd_iff, DECIDE``5 <= n <=> (n = 5) \/ (n = 6) \/ (7 <= n)``]
  ]);

(* This is the ultimate goal! *)

(* ------------------------------------------------------------------------- *)
(* Nair's Trick - using consecutive LCM                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the consecutive LCM function *)
val lcm_upto_def = Define`
    (lcm_upto 0 = 1) /\
    (lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n))
`;

(* Extract theorems from definition *)
val lcm_upto_0 = save_thm("lcm_upto_0", lcm_upto_def |> CONJUNCT1);
(* val lcm_upto_0 = |- lcm_upto 0 = 1: thm *)

val lcm_upto_SUC = save_thm("lcm_upto_SUC", lcm_upto_def |> CONJUNCT2);
(* val lcm_upto_SUC = |- !n. lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n): thm *)

(* Theorem: (lcm_upto 0 = 1) /\ (!n. lcm_upto (n+1) = lcm (n+1) (lcm_upto n)) *)
(* Proof: by lcm_upto_def *)
val lcm_upto_alt = store_thm(
  "lcm_upto_alt",
  ``(lcm_upto 0 = 1) /\ (!n. lcm_upto (n+1) = lcm (n+1) (lcm_upto n))``,
  metis_tac[lcm_upto_def, ADD1]);

(* Theorem: lcm_upto 1 = 1 *)
(* Proof:
     lcm_upto 1
   = lcm_upto (SUC 0)          by ONE
   = lcm (SUC 0) (lcm_upto 0)  by lcm_upto_SUC
   = lcm (SUC 0) 1             by lcm_upto_0
   = lcm 1 1                   by ONE
   = 1                         by LCM_REF
*)
val lcm_upto_1 = store_thm(
  "lcm_upto_1",
  ``lcm_upto 1 = 1``,
  metis_tac[lcm_upto_def, LCM_REF, ONE]);

(* Theorem: lcm_upto n for small n *)
(* Proof: by evaluation. *)
val lcm_upto_small = store_thm(
  "lcm_upto_small",
  ``(lcm_upto 2 = 2) /\ (lcm_upto 3 = 6) /\ (lcm_upto 4 = 12) /\
   (lcm_upto 5 = 60) /\ (lcm_upto 6 = 60) /\ (lcm_upto 7 = 420) /\
   (lcm_upto 8 = 840) /\ (lcm_upto 9 = 2520) /\ (lcm_upto 10 = 2520)``,
  EVAL_TAC);

(* Theorem: lcm_upto n = list_lcm [1 .. n] *)
(* Proof:
   By induction on n.
   Base: lcm_upto 0 = list_lcm [1 .. 0]
         lcm_upto 0
       = 1                     by lcm_upto_0
       = list_lcm []           by list_lcm_nil
       = list_lcm [1 .. 0]     by listRangeINC_EMPTY
   Step: lcm_upto n = list_lcm [1 .. n] ==> lcm_upto (SUC n) = list_lcm [1 .. SUC n]
         lcm_upto (SUC n)
       = lcm (SUC n) (lcm_upto n)            by lcm_upto_SUC
       = lcm (SUC n) (list_lcm [1 .. n])     by induction hypothesis
       = list_lcm (SNOC (SUC n) [1 .. n])    by list_lcm_snoc
       = list_lcm [1 .. (SUC n)]             by listRangeINC_SNOC, ADD1, 1 <= n + 1
*)
val lcm_upto_eq_list_lcm = store_thm(
  "lcm_upto_eq_list_lcm",
  ``!n. lcm_upto n = list_lcm [1 .. n]``,
  Induct >-
  rw[lcm_upto_0, list_lcm_nil, listRangeINC_EMPTY] >>
  rw[lcm_upto_SUC, list_lcm_snoc, listRangeINC_SNOC, ADD1]);

(* Theorem: 2 ** n <= lcm_upto (n + 1) *)
(* Proof:
     lcm_upto (n + 1)
   = list_lcm [1 .. (n + 1)]   by lcm_upto_eq_list_lcm
   >= 2 ** n                   by lcm_lower_bound
*)
val lcm_upto_lower = store_thm(
  "lcm_upto_lower",
  ``!n. 2 ** n <= lcm_upto (n + 1)``,
  rw[lcm_upto_eq_list_lcm, lcm_lower_bound]);

(* Theorem: 0 < lcm_upto (n + 1) *)
(* Proof:
     lcm_upto (n + 1)
   >= 2 ** n                   by lcm_upto_lower
    > 0                        by EXP_POS, 0 < 2
*)
val lcm_upto_pos = store_thm(
  "lcm_upto_pos",
  ``!n. 0 < lcm_upto (n + 1)``,
  metis_tac[lcm_upto_lower, EXP_POS, LESS_LESS_EQ_TRANS, DECIDE``0 < 2``]);

(* Theorem: (n + 1) divides lcm_upto (n + 1) /\ (lcm_upto n) divides lcm_upto (n + 1) *)
(* Proof:
   Note lcm_upto (n + 1) = lcm (n + 1) (lcm_upto n)   by lcm_upto_alt
     so (n + 1) divides lcm_upto (n + 1)
    and (lcm_upto n) divides lcm_upto (n + 1)         by LCM_DIVISORS
*)
val lcm_upto_divisors = store_thm(
  "lcm_upto_divisors",
  ``!n. (n + 1) divides lcm_upto (n + 1) /\ (lcm_upto n) divides lcm_upto (n + 1)``,
  rw[lcm_upto_alt, LCM_DIVISORS]);

(* Theorem: lcm_upto n <= lcm_upto (n + 1) *)
(* Proof:
   Note (lcm_upto n) divides lcm_upto (n + 1)   by lcm_upto_divisors
    and 0 < lcm_upto (n + 1)                  by lcm_upto_pos
     so lcm_upto n <= lcm_upto (n + 1)          by DIVIDES_LE
*)
val lcm_upto_monotone = store_thm(
  "lcm_upto_monotone",
  ``!n. lcm_upto n <= lcm_upto (n + 1)``,
  rw[lcm_upto_divisors, lcm_upto_pos, DIVIDES_LE]);

(* Theorem: k <= n ==> (leibniz n k) divides lcm_upto (n + 1) *)
(* Proof:
   Note (leibniz n k) divides list_lcm (leibniz_vertical n)   by leibniz_vertical_divisor
    ==> (leibniz n k) divides list_lcm [1 .. (n + 1)]         by notation
     or (leibniz n k) divides lcm_upto (n + 1)                by lcm_upto_eq_list_lcm
*)
val lcm_upto_leibniz_divisor = store_thm(
  "lcm_upto_leibniz_divisor",
  ``!n k. k <= n ==> (leibniz n k) divides lcm_upto (n + 1)``,
  metis_tac[leibniz_vertical_divisor, lcm_upto_eq_list_lcm]);

(* Theorem: n * 4 ** n <= lcm_upto (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n.
   Let m = 2 * n.

   Claim: (m + 1) * binomial m n divides lcm_upto (m + 1)       [1]
   Proof: Note n <= m                                           by LESS_MONO_MULT, 1 <= 2
           ==> (leibniz m n) divides lcm_upto (m + 1)           by lcm_upto_leibniz_divisor, n <= m
            or (m + 1) * binomial m n divides lcm_upto (m + 1)  by leibniz_def

   Claim: n * binomial m n divides lcm_upto (m + 1)             [2]
   Proof: Note (lcm_upto m) divides lcm_upto (m + 1)            by lcm_upto_divisors
          Also 0 < m /\ n <= m - 1                              by 0 < n
           and m - 1 + 1 = m                                    by 0 < m
          Thus (leibniz (m - 1) n) divides lcm_upto m           by lcm_upto_leibniz_divisor, n <= m - 1
            or (leibniz (m - 1) n) divides lcm_upto (m + 1)     by DIVIDES_TRANS
           and leibniz (m - 1) n
             = (m - n) * binomial m n                           by leibniz_up_alt
             = n * binomial m n                                 by m - n = n

   Note coprime n (m + 1)                         by GCD_EUCLID, GCD_1, 1 < n
   Thus lcm (n * binomial m n) ((m + 1) * binomial m n)
      = n * (m + 1) * binomial m n                by LCM_COMMON_COPRIME
      = n * ((m + 1) * binomial m n)              by MULT_ASSOC
      = n * leibniz m n                           by leibniz_def
    ==> n * leibniz m n divides lcm_upto (m + 1)  by LCM_DIVIDES, [1], [2]
   Note 0 < lcm_upto (m + 1)                      by lcm_upto_pos
     or n * leibniz m n <= lcm_upto (m + 1)       by DIVIDES_LE, 0 < lcm_upto (m + 1)
    Now          4 ** n <= leibniz m n            by leibniz_middle_lower
     so      n * 4 ** n <= n * leibniz m n        by LESS_MONO_MULT, MULT_COMM
     or      n * 4 ** n <= lcm_upto (m + 1)       by LESS_EQ_TRANS
*)
val lcm_upto_lower_odd = store_thm(
  "lcm_upto_lower_odd",
  ``!n. n * 4 ** n <= lcm_upto (2 * n + 1)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `m = 2 * n` >>
  `(m + 1) * binomial m n divides lcm_upto (m + 1)` by
  (`n <= m` by rw[Abbr`m`] >>
  metis_tac[lcm_upto_leibniz_divisor, leibniz_def]) >>
  `n * binomial m n divides lcm_upto (m + 1)` by
    (`(lcm_upto m) divides lcm_upto (m + 1)` by rw[lcm_upto_divisors] >>
  `0 < m /\ n <= m - 1` by rw[Abbr`m`] >>
  `m - 1 + 1 = m` by decide_tac >>
  `(leibniz (m - 1) n) divides lcm_upto m` by metis_tac[lcm_upto_leibniz_divisor] >>
  `(leibniz (m - 1) n) divides lcm_upto (m + 1)` by metis_tac[DIVIDES_TRANS] >>
  `leibniz (m - 1) n = (m - n) * binomial m n` by rw[leibniz_up_alt] >>
  `_ = n * binomial m n` by rw[Abbr`m`] >>
  metis_tac[]) >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  `lcm (n * binomial m n) ((m + 1) * binomial m n) = n * (m + 1) * binomial m n` by rw[LCM_COMMON_COPRIME] >>
  `_ = n * leibniz m n` by rw[leibniz_def, MULT_ASSOC] >>
  `n * leibniz m n divides lcm_upto (m + 1)` by metis_tac[LCM_DIVIDES] >>
  `n * leibniz m n <= lcm_upto (m + 1)` by rw[DIVIDES_LE, lcm_upto_pos] >>
  `4 ** n <= leibniz m n` by rw[leibniz_middle_lower, Abbr`m`] >>
  metis_tac[LESS_MONO_MULT, MULT_COMM, LESS_EQ_TRANS]);

(* Theorem: n * 4 ** n <= lcm_upto (2 * (n + 1)) *)
(* Proof:
     lcm_upto (2 * (n + 1))
   = lcm_upto (2 * n + 2)        by arithmetic
   >= lcm_upto (2 * n + 1)       by lcm_upto_monotone
   >= n * 4 ** n                 by lcm_upto_lower_odd
*)
val lcm_upto_lower_even = store_thm(
  "lcm_upto_lower_even",
  ``!n. n * 4 ** n <= lcm_upto (2 * (n + 1))``,
  rpt strip_tac >>
  `2 * (n + 1) = 2 * n + 1 + 1` by decide_tac >>
  metis_tac[lcm_upto_monotone, lcm_upto_lower_odd, LESS_EQ_TRANS]);

(* Theorem: 7 <= n ==> 2 ** n <= lcm_upto n *)
(* Proof:
   If ODD n, ?k. n = SUC (2 * k)       by ODD_EXISTS,
      When 5 <= 7 <= n = 2 * k + 1     by ADD1
           2 <= k                      by arithmetic
       and lcm_upto n
         = lcm_upto (2 * k + 1)        by notation
         >= k * 4 ** k                 by lcm_upto_lower_odd
         >= 2 * 4 ** k                 by k >= 2, LESS_MONO_MULT
          = 2 * 2 ** (2 * k)           by EXP_EXP_MULT
          = 2 ** SUC (2 * k)           by EXP
          = 2 ** n                     by n = SUC (2 * k)
   If EVEN n, ?m. n = 2 * m            by EVEN_EXISTS
      Note ODD 7 /\ ODD 9              by arithmetic
      If n = 8,
         LHS = 2 ** 8 = 256,
         RHS = lcm_upto 8 = 840        by lcm_upto_small
         Hence true.
      Otherwise, 10 <= n               by 7 <= n, n <> 7, n <> 8, n <> 9
      Since 0 < n, 0 < m               by MULT_EQ_0
         so ?k. m = SUC k              by num_CASES
       When 10 <= n = 2 * (k + 1)      by ADD1
             4 <= k                    by arithmetic
       and lcm_upto n
         = lcm_upto (2 * (k + 1))      by notation
         >= k * 4 ** k                 by lcm_upto_lower_even
         >= 4 * 4 ** k                 by k >= 4, LESS_MONO_MULT
          = 4 ** SUC k                 by EXP
          = 4 ** m                     by notation
          = 2 ** (2 * m)               by EXP_EXP_MULT
          = 2 ** n                     by n = 2 * m
*)
val lcm_upto_lower_better = store_thm(
  "lcm_upto_lower_better",
  ``!n. 7 <= n ==> 2 ** n <= lcm_upto n``,
  rpt strip_tac >>
  Cases_on `ODD n` >| [
    `?k. n = SUC (2 * k)` by rw[GSYM ODD_EXISTS] >>
    `2 <= k` by decide_tac >>
    `2 * 4 ** k <= k * 4 ** k` by rw[LESS_MONO_MULT] >>
    `lcm_upto n = lcm_upto (2 * k + 1)` by rw[ADD1] >>
    `2 ** n = 2 * 2 ** (2 * k)` by rw[EXP] >>
    `_ = 2 * 4 ** k` by rw[EXP_EXP_MULT] >>
    metis_tac[lcm_upto_lower_odd, LESS_EQ_TRANS],
    `ODD 7 /\ ODD 9` by rw[] >>
    `EVEN n /\ n <> 7 /\ n <> 9` by metis_tac[ODD_EVEN] >>
    `?m. n = 2 * m` by rw[GSYM EVEN_EXISTS] >>
    `m <> 0` by decide_tac >>
    `?k. m = SUC k` by metis_tac[num_CASES] >>
    Cases_on `n = 8` >-
    rw[lcm_upto_small] >>
    `4 <= k` by decide_tac >>
    `4 * 4 ** k <= k * 4 ** k` by rw[LESS_MONO_MULT] >>
    `lcm_upto n = lcm_upto (2 * (k + 1))` by rw[ADD1] >>
    `2 ** n = 4 ** m` by rw[EXP_EXP_MULT] >>
    `_ = 4 * 4 ** k` by rw[EXP] >>
    metis_tac[lcm_upto_lower_even, LESS_EQ_TRANS]
  ]);

(* This is a very significant result. *)

(* ------------------------------------------------------------------------- *)
(* Simple LCM lower bounds -- rework                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: HALF (n + 1) <= lcm_run n *)
(* Proof:
   If n = 0,
      LHS = HALF 1 = 0                by arithmetic
      RHS = lcm_run 0 = 1             by lcm_run_0
      Hence true.
   If n <> 0, 0 < n.
      Let l = [1 .. n].
      Then l <> []                    by listRangeINC_NIL, n <> 0
        so EVERY_POSITIVE l           by listRangeINC_EVERY
        lcm_run n
      = list_lcm l                    by notation
      >= (SUM l) DIV (LENGTH l)       by list_lcm_nonempty_lower, l <> []
       = (SUM l) DIV n                by listRangeINC_LEN
       = (HALF (n * (n + 1))) DIV n   by sum_1_to_n_eqn
       = HALF ((n * (n + 1)) DIV n)   by DIV_DIV_DIV_MULT, 0 < 2, 0 < n
       = HALF (n + 1)                 by MULT_TO_DIV
*)
val lcm_run_lower_simple = store_thm(
  "lcm_run_lower_simple",
  ``!n. HALF (n + 1) <= lcm_run n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  qabbrev_tac `l = [1 .. n]` >>
  `l <> []` by rw[listRangeINC_NIL, Abbr`l`] >>
  `EVERY_POSITIVE l` by rw[listRangeINC_EVERY, Abbr`l`] >>
  `(SUM l) DIV (LENGTH l) = (SUM l) DIV n` by rw[listRangeINC_LEN, Abbr`l`] >>
  `_ = (HALF (n * (n + 1))) DIV n` by rw[sum_1_to_n_eqn, Abbr`l`] >>
  `_ = HALF ((n * (n + 1)) DIV n)` by rw[DIV_DIV_DIV_MULT] >>
  `_ = HALF (n + 1)` by rw[MULT_TO_DIV] >>
  metis_tac[list_lcm_nonempty_lower]);

(* This is a simple result, good but not very useful. *)

(* Theorem: lcm_run n = list_lcm (leibniz_vertical (n - 1)) *)
(* Proof:
   If n = 0,
      Then n - 1 + 1 = 0 - 1 + 1 = 1
       but lcm_run 0 = 1 = lcm_run 1, hence true.
   If n <> 0,
      Then n - 1 + 1 = n, hence true trivially.
*)
val lcm_run_alt = store_thm(
  "lcm_run_alt",
  ``!n. lcm_run n = list_lcm (leibniz_vertical (n - 1))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0, lcm_run_1] >>
  rw[]);

(* Theorem: 2 ** (n - 1) <= lcm_run n *)
(* Proof:
   If n = 0,
      LHS = HALF 1 = 0                by arithmetic
      RHS = lcm_run 0 = 1             by lcm_run_0
      Hence true.
   If n <> 0, 0 < n, or 1 <= n.
      Let l = leibniz_horizontal (n - 1).
      Then LENGTH l = n               by leibniz_horizontal_len
        so l <> []                    by LENGTH_NIL, n <> 0
       and EVERY_POSITIVE l           by leibniz_horizontal_pos
        lcm_run n
      = list_lcm (leibniz_vertical (n - 1)) by lcm_run_alt
      = list_lcm l                    by leibniz_lcm_property
      >= (SUM l) DIV (LENGTH l)       by list_lcm_nonempty_lower, l <> []
       = 2 ** (n - 1)                 by leibniz_horizontal_average_eqn
*)
val lcm_run_lower_good = store_thm(
  "lcm_run_lower_good",
  ``!n. 2 ** (n - 1) <= lcm_run n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `0 < n /\ 1 <= n /\ (n - 1 + 1 = n)` by decide_tac >>
  qabbrev_tac `l = leibniz_horizontal (n - 1)` >>
  `lcm_run n = list_lcm l` by metis_tac[leibniz_lcm_property] >>
  `LENGTH l = n` by metis_tac[leibniz_horizontal_len] >>
  `l <> []` by metis_tac[LENGTH_NIL] >>
  `EVERY_POSITIVE l` by rw[leibniz_horizontal_pos, Abbr`l`] >>
  metis_tac[list_lcm_nonempty_lower, leibniz_horizontal_average_eqn]);

(* ------------------------------------------------------------------------- *)
(* Upper Bound by Leibniz Triangle                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: leibniz n k = (n + 1 - k) * binomial (n + 1) k *)
(* Proof: by leibniz_up_alt:
leibniz_up_alt |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
*)
val leibniz_eqn = store_thm(
  "leibniz_eqn",
  ``!n k. leibniz n k = (n + 1 - k) * binomial (n + 1) k``,
  rw[GSYM leibniz_up_alt]);

(* Theorem: leibniz n (k + 1) = (n - k) * binomial (n + 1) (k + 1) *)
(* Proof: by leibniz_up_alt:
leibniz_up_alt |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
*)
val leibniz_right_alt = store_thm(
  "leibniz_right_alt",
  ``!n k. leibniz n (k + 1) = (n - k) * binomial (n + 1) (k + 1)``,
  metis_tac[leibniz_up_alt, DECIDE``0 < n + 1 /\ (n + 1 - 1 = n) /\ (n + 1 - (k + 1) = n - k)``]);

(* Leibniz Stack:
       \
            \
                \
                    \
                     (L k k) <-- boundary of Leibniz Triangle
                        |    \            |-- (m - k) = distance
                        |   k <= m <= n  <-- m
                        |         \           (n - k) = height, or max distance
                        |     binomial (n+1) (m+1) is at south-east of binomial n m
                        |              \
                        |                   \
   n-th row: ....... (L n k) .................

leibniz_binomial_identity
|- !m n k. k <= m /\ m <= n ==> (leibniz n k * binomial (n - k) (m - k) = leibniz m k * binomial (n + 1) (m + 1))
This says: (leibniz n k) at bottom is related to a stack entry (leibniz m k).
leibniz_divides_leibniz_factor
|- !m n k. k <= m /\ m <= n ==> leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)
This is just a corollary of leibniz_binomial_identity, by divides_def.

leibniz_horizontal_member_divides
|- !m n x. n <= TWICE m + 1 /\ m <= n /\ MEM x (leibniz_horizontal n) ==>
           x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)
This says: for the n-th row, q = list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)
           is a common multiple of all members of the n-th row when n <= TWICE m + 1 /\ m <= n
That means, for the n-th row, pick any m-th row for HALF (n - 1) <= m <= n
Compute its list_lcm (leibniz_horizontal m), then multiply by binomial (n + 1) (m + 1) as q.
This value q is a common multiple of all members in n-th row.
The proof goes through all members of n-th row, i.e. (L n k) for k <= n.
To apply leibniz_binomial_identity, the condition is k <= m, not k <= n.
Since m has been picked (between HALF n and n), divide k into two parts: k <= m, m < k <= n.
For the first part, apply leibniz_binomial_identity.
For the second part, use symmetry L n (n - k) = L n k, then apply leibniz_binomial_identity.
With k <= m, m <= n, we apply leibniz_binomial_identity:
(1) Each member x = leibniz n k divides p = leibniz m k * binomial (n + 1) (m + 1), stack member with a factor.
(2) But leibniz m k is a member of (leibniz_horizontal m)
(3) Thus leibniz m k divides list_lcm (leibniz_horizontal m), the stack member divides its row list_lcm
    ==>  p divides q           by multiplying both by binomial (n + 1) (m + 1)
(4) Hence x divides q.
With the other half by symmetry, all members x divides q.
Corollary 1:
lcm_run_divides_property
|- !m n. n <= TWICE m /\ m <= n ==> lcm_run n divides binomial n m * lcm_run m
This follows by list_lcm_is_least_common_multiple and leibniz_lcm_property.
Corollary 2:
lcm_run_bound_recurrence
|- !m n. n <= TWICE m /\ m <= n ==> lcm_run n <= lcm_run m * binomial n m
Then lcm_run_upper_bound |- !n. lcm_run n <= 4 ** n  follows by complete induction on n.
*)

(* Theorem: k <= m /\ m <= n ==>
           ((leibniz n k) * (binomial (n - k) (m - k)) = (leibniz m k) * (binomial (n + 1) (m + 1))) *)
(* Proof:
     leibniz n k * (binomial (n - k) (m - k))
   = (n + 1) * (binomial n k) * (binomial (n - k) (m - k))     by leibniz_def
                    n!              (n - k)!
   = (n + 1) * ------------- * ------------------              binomial formula
                 k! (n - k)!    (m - k)! (n - m)!
                    n!                 1
   = (n + 1) * -------------- * ------------------             cancel (n - k)!
                 k! 1           (m - k)! (n - m)!
                    n!               (m + 1)!
   = (n + 1) * -------------- * ------------------             replace by (m + 1)!
                k! (m + 1)!     (m - k)! (n - m)!
                  (n + 1)!           m!
   = (m + 1) * -------------- * ------------------             merge and split factorials
                k! (m + 1)!     (m - k)! (n - m)!
                    m!             (n + 1)!
   = (m + 1) * -------------- * ------------------             binomial formula
                k! (m - k)!      (m + 1)! (n - m)!
   = leibniz m k * binomial (n + 1) (m + 1)                    by leibniz_def
*)
val leibniz_binomial_identity = store_thm(
  "leibniz_binomial_identity",
  ``!m n k. k <= m /\ m <= n ==>
           ((leibniz n k) * (binomial (n - k) (m - k)) = (leibniz m k) * (binomial (n + 1) (m + 1)))``,
  rw[leibniz_def] >>
  `m + 1 <= n + 1` by decide_tac >>
  `m - k <= n - k` by decide_tac >>
  `(n - k) - (m - k) = n - m` by decide_tac >>
  `(n + 1) - (m + 1) = n - m` by decide_tac >>
  `FACT m = binomial m k * (FACT (m - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT (n + 1) = binomial (n + 1) (m + 1) * (FACT (n - m) * FACT (m + 1))` by metis_tac[binomial_formula2] >>
  `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT (n - k) = binomial (n - k) (m - k) * (FACT (n - m) * FACT (m - k))` by metis_tac[binomial_formula2] >>
  `!n. FACT (n + 1) = (n + 1) * FACT n` by metis_tac[FACT, ADD1] >>
  `FACT (n + 1) = FACT (n - m) * (FACT k * (FACT (m - k) * ((m + 1) * (binomial m k) * (binomial (n + 1) (m + 1)))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `FACT (n + 1) = FACT (n - m) * (FACT k * (FACT (m - k) * ((n + 1) * (binomial n k) * (binomial (n - k) (m - k)))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[MULT_LEFT_CANCEL, FACT_LESS, NOT_ZERO_LT_ZERO]);

(* Theorem: k <= m /\ m <= n ==> leibniz n k divides leibniz m k * binomial (n + 1) (m + 1) *)
(* Proof:
   Note leibniz m k * binomial (n + 1) (m + 1)
      = leibniz n k * binomial (n - k) (m - k)                 by leibniz_binomial_identity
   Thus leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)
                                                               by divides_def, MULT_COMM
*)
val leibniz_divides_leibniz_factor = store_thm(
  "leibniz_divides_leibniz_factor",
  ``!m n k. k <= m /\ m <= n ==> leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)``,
  metis_tac[leibniz_binomial_identity, divides_def, MULT_COMM]);

(* Theorem: n <= 2 * m + 1 /\ m <= n /\ MEM x (leibniz_horizontal n) ==>
            x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1) *)
(* Proof:
   Let q = list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1).
   Note MEM x (leibniz_horizontal n)
    ==> ?k. k <= n /\ (x = leibniz n k)          by leibniz_horizontal_member
   Here the picture is:
                HALF n ... m .... n
          0 ........ k .......... n
   We need k <= m to get x divides q, by applying leibniz_divides_leibniz_factor.
   For m < k <= n, we shall use symmetry to get x divides q.
   If k <= m,
      Let p = (leibniz m k) * binomial (n + 1) (m + 1).
      Then x divides p                           by leibniz_divides_leibniz_factor, k <= m, m <= n
       and MEM (leibniz m k) (leibniz_horizontal m)   by leibniz_horizontal_member, k <= m
       ==> (leibniz m k) divides list_lcm (leibniz_horizontal m)   by list_lcm_is_common_multiple
        so (leibniz m k) * binomial (n + 1) (m + 1)
           divides
           list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)   by DIVIDES_CANCEL, binomial_pos
        or p divides q                           by notation
      Thus x divides q                           by DIVIDES_TRANS
   If ~(k <= m), then m < k.
      Note x = leibniz n (n - k)                 by leibniz_sym, k <= n
       Now n <= m + m + 1                        by given n <= 2 * m + 1
        so n - k <= m + m + 1 - k                by arithmetic
       and m + m + 1 - k <= m                    by m < k, so m + 1 <= k
        or n - k <= m                            by LESS_EQ_TRANS
       Let j = n - k, p = (leibniz m j) * binomial (n + 1) (m + 1).
      Then x divides p                           by leibniz_divides_leibniz_factor, j <= m, m <= n
       and MEM (leibniz m j) (leibniz_horizontal m)   by leibniz_horizontal_member, j <= m
       ==> (leibniz m j) divides list_lcm (leibniz_horizontal m)   by list_lcm_is_common_multiple
        so (leibniz m j) * binomial (n + 1) (m + 1)
           divides
           list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)   by DIVIDES_CANCEL, binomial_pos
        or p divides q                           by notation
      Thus x divides q                           by DIVIDES_TRANS
*)
val leibniz_horizontal_member_divides = store_thm(
  "leibniz_horizontal_member_divides",
  ``!m n x. n <= 2 * m + 1 /\ m <= n /\ MEM x (leibniz_horizontal n) ==>
           x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)``,
  rpt strip_tac >>
  qabbrev_tac `q = list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)` >>
  `?k. k <= n /\ (x = leibniz n k)` by rw[GSYM leibniz_horizontal_member] >>
  Cases_on `k <= m` >| [
    qabbrev_tac `p = (leibniz m k) * binomial (n + 1) (m + 1)` >>
    `x divides p` by rw[leibniz_divides_leibniz_factor, Abbr`p`] >>
    `MEM (leibniz m k) (leibniz_horizontal m)` by metis_tac[leibniz_horizontal_member] >>
    `(leibniz m k) divides list_lcm (leibniz_horizontal m)` by rw[list_lcm_is_common_multiple] >>
    `p divides q` by rw[GSYM DIVIDES_CANCEL, binomial_pos, Abbr`p`, Abbr`q`] >>
    metis_tac[DIVIDES_TRANS],
    `n - k <= m` by decide_tac >>
    qabbrev_tac `j = n - k` >>
    `x = leibniz n j` by rw[Once leibniz_sym, Abbr`j`] >>
    qabbrev_tac `p = (leibniz m j) * binomial (n + 1) (m + 1)` >>
    `x divides p` by rw[leibniz_divides_leibniz_factor, Abbr`p`] >>
    `MEM (leibniz m j) (leibniz_horizontal m)` by metis_tac[leibniz_horizontal_member] >>
    `(leibniz m j) divides list_lcm (leibniz_horizontal m)` by rw[list_lcm_is_common_multiple] >>
    `p divides q` by rw[GSYM DIVIDES_CANCEL, binomial_pos, Abbr`p`, Abbr`q`] >>
    metis_tac[DIVIDES_TRANS]
  ]);

(* Theorem: n <= 2 * m /\ m <= n ==> (lcm_run n) divides (lcm_run m) * binomial n m *)
(* Proof:
   If n = 0,
      Then lcm_run 0 = 1                         by lcm_run_0
      Hence true                                 by ONE_DIVIDES_ALL
   If n <> 0,
      Then 0 < n, and 0 < m                      by n <= 2 * m`
      Thus m - 1 <= n - 1                        by m <= n
       and n - 1 <= 2 * m - 1                    by n <= 2 * m
                  = 2 * (m - 1) + 1
      Thus !x. MEM x (leibniz_horizontal (n - 1)) ==>
            x divides list_lcm (leibniz_horizontal (m - 1)) * binomial n m
                                                 by leibniz_horizontal_member_divides
       ==> list_lcm (leibniz_horizontal (n - 1)) divides
           list_lcm (leibniz_horizontal (m - 1)) * binomial n m
                                                 by list_lcm_is_least_common_multiple
       But lcm_run n = leibniz_horizontal (n - 1)          by leibniz_lcm_property
       and lcm_run m = leibniz_horizontal (m - 1)          by leibniz_lcm_property
           list_lcm (leibniz_horizontal h) divides q       by list_lcm_is_least_common_multiple
      Thus (lcm_run n) divides (lcm_run m) * binomial n m  by above
*)
val lcm_run_divides_property = store_thm(
  "lcm_run_divides_property",
  ``!m n. n <= 2 * m /\ m <= n ==> (lcm_run n) divides (lcm_run m) * binomial n m``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `0 < n` by decide_tac >>
  `0 < m` by decide_tac >>
  `m - 1 <= n - 1` by decide_tac >>
  `n - 1 <= 2 * (m - 1) + 1` by decide_tac >>
  `(n - 1 + 1 = n) /\ (m - 1 + 1 = m)` by decide_tac >>
  metis_tac[leibniz_horizontal_member_divides, list_lcm_is_least_common_multiple, leibniz_lcm_property]);

(* Theorem: n <= 2 * m /\ m <= n ==> (lcm_run n) <= (lcm_run m) * binomial n m *)
(* Proof:
   Note 0 < lcm_run m                                    by lcm_run_pos
    and 0 < binomial n m                                 by binomial_pos
     so 0 < lcm_run m * binomial n m                     by MULT_EQ_0
    Now (lcm_run n) divides (lcm_run m) * binomial n m   by lcm_run_divides_property
   Thus (lcm_run n) <= (lcm_run m) * binomial n m        by DIVIDES_LE
*)
val lcm_run_bound_recurrence = store_thm(
  "lcm_run_bound_recurrence",
  ``!m n. n <= 2 * m /\ m <= n ==> (lcm_run n) <= (lcm_run m) * binomial n m``,
  rpt strip_tac >>
  `0 < lcm_run m * binomial n m` by metis_tac[lcm_run_pos, binomial_pos, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  rw[lcm_run_divides_property, DIVIDES_LE]);

(* Theorem: lcm_run n <= 4 ** n *)
(* Proof:
   By complete induction on n.
   If EVEN n,
      Base: n = 0.
         LHS = lcm_run 0 = 1               by lcm_run_0
         RHS = 4 ** 0 = 1                  by EXP
         Hence true.
      Step: n <> 0 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = lcm_run m * binomial n m.
         Then n = 2 * m                    by EVEN_HALF
           so m <= 2 * m = n               by arithmetic
          ==> lcm_run n <= c               by lcm_run_bound_recurrence, m <= n
          But m <> 0                       by n <> 0
           so m < n                        by arithmetic
          Now c = lcm_run m * binomial n m by notation
               <= 4 ** m * binomial n m    by induction hypothesis, m < n
               <= 4 ** m * 4 ** m          by binomial_middle_upper_bound
                = 4 ** (m + m)             by EXP_ADD
                = 4 ** n                   by TIMES2, n = 2 * m
         Hence lcm_run n <= 4 ** n.
   If ~EVEN n,
      Then ODD n                           by EVEN_ODD
      Base: n = 1.
         LHS = lcm_run 1 = 1               by lcm_run_1
         RHS = 4 ** 1 = 4                  by EXP
         Hence true.
      Step: n <> 1 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = lcm_run (m + 1) * binomial n (m + 1).
         Then n = 2 * m + 1                by ODD_HALF
          and 0 < m                        by n <> 1
          and m + 1 <= 2 * m + 1 = n       by arithmetic
          ==> (lcm_run n) <= c             by lcm_run_bound_recurrence, m + 1 <= n
          But m + 1 <> n                   by m <> 0
           so m + 1 < n                    by m + 1 <> n
          Now c = lcm_run (m + 1) * binomial n (m + 1)   by notation
               <= 4 ** (m + 1) * binomial n (m + 1)      by induction hypothesis, m + 1 < n
                = 4 ** (m + 1) * binomial n m            by binomial_sym, n - (m + 1) = m
               <= 4 ** (m + 1) * 4 ** m                  by binomial_middle_upper_bound
                = 4 ** m * 4 ** (m + 1)    by arithmetic
                = 4 ** (m + (m + 1))       by EXP_ADD
                = 4 ** (2 * m + 1)         by arithmetic
                = 4 ** n                   by n = 2 * m + 1
         Hence lcm_run n <= 4 ** n.
*)
val lcm_run_upper_bound = store_thm(
  "lcm_run_upper_bound",
  ``!n. lcm_run n <= 4 ** n``,
  completeInduct_on `n` >>
  Cases_on `EVEN n` >| [
    Cases_on `n = 0` >-
    rw[lcm_run_0] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m` by rw[EVEN_HALF, Abbr`m`] >>
    qabbrev_tac `c = lcm_run m * binomial n m` >>
    `lcm_run n <= c` by rw[lcm_run_bound_recurrence, Abbr`c`] >>
    `lcm_run m <= 4 ** m` by rw[] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** m * 4 ** m` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** m * 4 ** m = 4 ** n` by metis_tac[EXP_ADD, TIMES2] >>
    decide_tac,
    `ODD n` by metis_tac[EVEN_ODD] >>
    Cases_on `n = 1` >-
    rw[lcm_run_1] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m + 1` by rw[ODD_HALF, Abbr`m`] >>
    qabbrev_tac `c = lcm_run (m + 1) * binomial n (m + 1)` >>
    `lcm_run n <= c` by rw[lcm_run_bound_recurrence, Abbr`c`] >>
    `lcm_run (m + 1) <= 4 ** (m + 1)` by rw[] >>
    `binomial n (m + 1) = binomial n m` by rw[Once binomial_sym] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** (m + 1) * 4 ** m` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** (m + 1) * 4 ** m = 4 ** n` by metis_tac[MULT_COMM, EXP_ADD, ADD_ASSOC, TIMES2] >>
    decide_tac
  ]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Beta Triangle                                                             *)
(* ------------------------------------------------------------------------- *)

(* Define beta triangle *)
(* Use temp_overload so that beta is invisibe outside:
val beta_def = Define`
    beta n k = k * (binomial n k)
`;
*)
val _ = temp_overload_on ("beta", ``\n k. k * (binomial n k)``); (* for temporary overloading *)
(* can use overload, but then hard to print and change the appearance of too many theorem? *)

(*

Pascal's Triangle (k <= n)
n = 0    1 = binomial 0 0
n = 1    1  1
n = 2    1  2  1
n = 3    1  3  3  1
n = 4    1  4  6  4  1
n = 5    1  5 10 10  5  1
n = 6    1  6 15 20 15  6  1

Beta Triangle (0 < k <= n)
n = 1       1                = 1 * (1)                = leibniz_horizontal 0
n = 2       2  2             = 2 * (1  1)             = leibniz_horizontal 1
n = 3       3  6  3          = 3 * (1  2  1)          = leibniz_horizontal 2
n = 4       4 12 12  4       = 4 * (1  3  3  1)       = leibniz_horizontal 3
n = 5       5 20 30 20  5    = 5 * (1  4  6  4  1)    = leibniz_horizontal 4
n = 6       6 30 60 60 30  6 = 6 * (1  5 10 10  5  1) = leibniz_horizontal 5

> EVAL ``let n = 10 in let k = 6 in (beta (n+1) (k+1) = leibniz n k)``; --> T
> EVAL ``let n = 10 in let k = 4 in (beta (n+1) (k+1) = leibniz n k)``; --> T
> EVAL ``let n = 10 in let k = 3 in (beta (n+1) (k+1) = leibniz n k)``; --> T

*)

(* Theorem: beta 0 n = 0 *)
(* Proof:
     beta 0 n
   = n * (binomial 0 n)              by notation
   = n * (if n = 0 then 1 else 0)    by binomial_0_n
   = 0
*)
val beta_0_n = store_thm(
  "beta_0_n",
  ``!n. beta 0 n = 0``,
  rw[binomial_0_n]);

(* Theorem: beta n 0 = 0 *)
(* Proof: by notation *)
val beta_n_0 = store_thm(
  "beta_n_0",
  ``!n. beta n 0 = 0``,
  rw[]);

(* Theorem: n < k ==> (beta n k = 0) *)
(* Proof: by notation, binomial_less_0 *)
val beta_less_0 = store_thm(
  "beta_less_0",
  ``!n k. n < k ==> (beta n k = 0)``,
  rw[binomial_less_0]);

(* Theorem: beta (n + 1) (k + 1) = leibniz n k *)
(* Proof:
   If k <= n, then k + 1 <= n + 1                by arithmetic
        beta (n + 1) (k + 1)
      = (k + 1) binomial (n + 1) (k + 1)         by notation
      = (k + 1) (n + 1)!  / (k + 1)! (n - k)!    by binomial_formula2
      = (n + 1) n! / k! (n - k)!                 by factorial composing and decomposing
      = (n + 1) * binomial n k                   by binomial_formula2
      = leibniz_horizontal n k                   by leibniz_def
   If ~(k <= n), then n < k /\ n + 1 < k + 1     by arithmetic
     Then beta (n + 1) (k + 1) = 0               by beta_less_0
      and leibniz n k = 0                        by leibniz_less_0
     Hence true.
*)
val beta_eqn = store_thm(
  "beta_eqn",
  ``!n k. beta (n + 1) (k + 1) = leibniz n k``,
  rpt strip_tac >>
  Cases_on `k <= n` >| [
    `(n + 1) - (k + 1) = n - k` by decide_tac >>
    `k + 1 <= n + 1` by decide_tac >>
    `FACT (n - k) * FACT k * beta (n + 1) (k + 1) = FACT (n - k) * FACT k * ((k + 1) * binomial (n + 1) (k + 1))` by rw[] >>
    `_ = FACT (n - k) * FACT (k + 1) * binomial (n + 1) (k + 1)` by metis_tac[FACT, ADD1, MULT_ASSOC, MULT_COMM] >>
    `_ = FACT (n + 1)` by metis_tac[binomial_formula2,  MULT_ASSOC, MULT_COMM] >>
    `_ = (n + 1) * FACT n` by metis_tac[FACT, ADD1] >>
    `_ = FACT (n - k) * FACT k * ((n + 1) * binomial n k)` by metis_tac[binomial_formula2, MULT_ASSOC, MULT_COMM] >>
    `_ = FACT (n - k) * FACT k * (leibniz n k)` by rw[leibniz_def] >>
    `FACT k <> 0 /\ FACT (n - k) <> 0` by metis_tac[FACT_LESS, NOT_ZERO_LT_ZERO] >>
    metis_tac[EQ_MULT_LCANCEL, MULT_ASSOC],
    rw[beta_less_0, leibniz_less_0]
  ]);

(* Theorem: 0 < n /\ 0 < k ==> (beta n k = leibniz (n - 1) (k - 1)) *)
(* Proof: by beta_eqn *)
val beta_alt = store_thm(
  "beta_alt",
  ``!n k. 0 < n /\ 0 < k ==> (beta n k = leibniz (n - 1) (k - 1))``,
  rw[GSYM beta_eqn]);

(* Theorem: 0 < k /\ k <= n ==> 0 < beta n k *)
(* Proof:
       0 < beta n k
   <=> beta n k <> 0                 by NOT_ZERO_LT_ZERO
   <=> k * (binomial n k) <> 0       by notation
   <=> k <> 0 /\ binomial n k <> 0   by MULT_EQ_0
   <=> k <> 0 /\ k <= n              by binomial_pos
   <=> 0 < k /\ k <= n               by NOT_ZERO_LT_ZERO
*)
val beta_pos = store_thm(
  "beta_pos",
  ``!n k. 0 < k /\ k <= n ==> 0 < beta n k``,
  metis_tac[MULT_EQ_0, binomial_pos, NOT_ZERO_LT_ZERO]);

(* Theorem: (beta n k = 0) <=> (k = 0) \/ n < k *)
(* Proof:
       beta n k = 0
   <=> k * (binomial n k) = 0           by notation
   <=> (k = 0) \/ (binomial n k = 0)    by MULT_EQ_0
   <=> (k = 0) \/ (n < k)               by binomial_eq_0
*)
val beta_eq_0 = store_thm(
  "beta_eq_0",
  ``!n k. (beta n k = 0) <=> (k = 0) \/ n < k``,
  rw[binomial_eq_0]);

(*
binomial_sym  |- !n k. k <= n ==> (binomial n k = binomial n (n - k))
leibniz_sym   |- !n k. k <= n ==> (leibniz n k = leibniz n (n - k))
*)

(* Theorem: k <= n ==> (beta n k = beta n (n - k + 1)) *)
(* Proof:
   If k = 0,
      Then beta n 0 = 0                  by beta_n_0
       and beta n (n + 1) = 0            by beta_less_0
      Hence true.
   If k <> 0, then 0 < k
      Thus 0 < n                         by k <= n
         beta n k
      = leibniz (n - 1) (k - 1)          by beta_alt
      = leibniz (n - 1) (n - k)          by leibniz_sym
      = leibniz (n - 1) (n - k + 1 - 1)  by arithmetic
      = beta n (n - k + 1)               by beta_alt
*)
val beta_sym = store_thm(
  "beta_sym",
  ``!n k. k <= n ==> (beta n k = beta n (n - k + 1))``,
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[beta_n_0, beta_less_0] >>
  rw[beta_alt, Once leibniz_sym]);

(* ------------------------------------------------------------------------- *)
(* Beta Horizontal List                                                      *)
(* ------------------------------------------------------------------------- *)

(*
> EVAL ``leibniz_horizontal 3``;    --> [4; 12; 12; 4]
> EVAL ``GENLIST (beta 4) 5``;      --> [0; 4; 12; 12; 4]
> EVAL ``TL (GENLIST (beta 4) 5)``; --> [4; 12; 12; 4]
*)

(* Use overloading for a row of beta n k, k = 1 to n. *)
(* val _ = overload_on("beta_horizontal", ``\n. TL (GENLIST (beta n) (n + 1))``); *)
(* use a direct GENLIST rather than tail of a GENLIST *)
val _ = temp_overload_on("beta_horizontal", ``\n. GENLIST (beta n o SUC) n``); (* for temporary overloading *)

(*
> EVAL ``leibniz_horizontal 5``; --> [6; 30; 60; 60; 30; 6]
> EVAL ``beta_horizontal 6``;    --> [6; 30; 60; 60; 30; 6]
*)

(* Theorem: beta_horizontal 0 = [] *)
(* Proof:
     beta_horizontal 0
   = GENLIST (beta 0 o SUC) 0    by notation
   = []                          by GENLIST
*)
val beta_horizontal_0 = store_thm(
  "beta_horizontal_0",
  ``beta_horizontal 0 = []``,
  rw[]);

(* Theorem: LENGTH (beta_horizontal n) = n *)
(* Proof:
     LENGTH (beta_horizontal n)
   = LENGTH (GENLIST (beta n o SUC) n)     by notation
   = n                                     by LENGTH_GENLIST
*)
val beta_horizontal_len = store_thm(
  "beta_horizontal_len",
  ``!n. LENGTH (beta_horizontal n) = n``,
  rw[]);

(* Theorem: beta_horizontal (n + 1) = leibniz_horizontal n *)
(* Proof:
   Note beta_horizontal (n + 1) = GENLIST ((beta (n + 1) o SUC)) (n + 1)   by notation
    and leibniz_horizontal n = GENLIST (leibniz n) (n + 1)          by notation
    Now (beta (n + 1)) o SUC) k
      = beta (n + 1) (k + 1)                              by ADD1
      = leibniz n k                                       by beta_eqn
   Thus beta_horizontal (n + 1) = leibniz_horizontal n    by GENLIST_FUN_EQ
*)
val beta_horizontal_eqn = store_thm(
  "beta_horizontal_eqn",
  ``!n. beta_horizontal (n + 1) = leibniz_horizontal n``,
  rw[GENLIST_FUN_EQ, beta_eqn, ADD1]);

(* Theorem: 0 < n ==> (beta_horizontal n = leibniz_horizontal (n - 1)) *)
(* Proof: by beta_horizontal_eqn *)
val beta_horizontal_alt = store_thm(
  "beta_horizontal_alt",
  ``!n. 0 < n ==> (beta_horizontal n = leibniz_horizontal (n - 1))``,
  metis_tac[beta_horizontal_eqn, DECIDE``0 < n ==> (n - 1 + 1 = n)``]);

(* Theorem: 0 < k /\ k <= n ==> MEM (beta n k) (beta_horizontal n) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      ?m. m < n /\ (beta n k = beta n (SUC m))
   Since k <> 0, k = SUC m,
     and SUC m = k <= n ==> m < n     by arithmetic
   So take this m, and the result follows.
*)
val beta_horizontal_mem = store_thm(
  "beta_horizontal_mem",
  ``!n k. 0 < k /\ k <= n ==> MEM (beta n k) (beta_horizontal n)``,
  rpt strip_tac >>
  rw[MEM_GENLIST] >>
  `?m. k = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  `m < n` by decide_tac >>
  metis_tac[]);

(* too weak:
binomial_horizontal_mem  |- !n k. k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n)
leibniz_horizontal_mem   |- !n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)
*)

(* Theorem: MEM (beta n k) (beta_horizontal n) <=> 0 < k /\ k <= n *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n /\ (beta n k = beta n (SUC m))) <=> 0 < k /\ k <= n
   If part: (?m. m < n /\ (beta n k = beta n (SUC m))) ==> 0 < k /\ k <= n
      By contradiction, suppose k = 0 \/ n < k
      Note SUC m <> 0 /\ ~(n < SUC m)     by m < n
      Thus beta n (SUC m) <> 0            by beta_eq_0
        or beta n k <> 0                  by beta n k = beta n (SUC m)
       ==> (k <> 0) /\ ~(n < k)           by beta_eq_0
      This contradicts k = 0 \/ n < k.
  Only-if part: 0 < k /\ k <= n ==> ?m. m < n /\ (beta n k = beta n (SUC m))
      Note k <> 0, so ?m. k = SUC m       by num_CASES
       and SUC m <= n <=> m < n           by LESS_EQ
        so Take this m, and the result follows.
*)
val beta_horizontal_mem_iff = store_thm(
  "beta_horizontal_mem_iff",
  ``!n k. MEM (beta n k) (beta_horizontal n) <=> 0 < k /\ k <= n``,
  rw[MEM_GENLIST] >>
  rewrite_tac[EQ_IMP_THM] >>
  strip_tac >| [
    spose_not_then strip_assume_tac >>
    `SUC m <> 0 /\ ~(n < SUC m)` by decide_tac >>
    `(k <> 0) /\ ~(n < k)` by metis_tac[beta_eq_0] >>
    decide_tac,
    strip_tac >>
    `?m. k = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
    metis_tac[LESS_EQ]
  ]);

(* Theorem: MEM x (beta_horizontal n) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n /\ (x = beta n (SUC m))) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k)
   Since 0 < k /\ k <= n <=> ?m. (k = SUC m) /\ m < n  by num_CASES, LESS_EQ
   This is trivially true.
*)
val beta_horizontal_member = store_thm(
  "beta_horizontal_member",
  ``!n x. MEM x (beta_horizontal n) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k)``,
  rw[MEM_GENLIST] >>
  metis_tac[num_CASES, NOT_ZERO_LT_ZERO, SUC_NOT_ZERO, LESS_EQ]);

(* Theorem: k < n ==> (EL k (beta_horizontal n) = beta n (k + 1)) *)
(* Proof: by EL_GENLIST, ADD1 *)
val beta_horizontal_element = store_thm(
  "beta_horizontal_element",
  ``!n k. k < n ==> (EL k (beta_horizontal n) = beta n (k + 1))``,
  rw[EL_GENLIST, ADD1]);

(* Theorem: 0 < n ==> (lcm_run n = list_lcm (beta_horizontal n)) *)
(* Proof:
   Note n <> 0
    ==> n = SUC k for some k          by num_CASES
     or n = k + 1                     by ADD1
     lcm_run n
   = lcm_run (k + 1)
   = list_lcm (leibniz_horizontal k)  by leibniz_lcm_property
   = list_lcm (beta_horizontal n)     by beta_horizontal_eqn
*)
val lcm_run_by_beta_horizontal = store_thm(
  "lcm_run_by_beta_horizontal",
  ``!n. 0 < n ==> (lcm_run n = list_lcm (beta_horizontal n))``,
  metis_tac[leibniz_lcm_property, beta_horizontal_eqn, num_CASES, ADD1, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < k /\ k <= n ==> (beta n k) divides lcm_run n *)
(* Proof:
   Note 0 < n                                       by 0 < k /\ k <= n
    and MEM (beta n k) (beta_horizontal n)          by beta_horizontal_mem
   also lcm_run n = list_lcm (beta_horizontal n)    by lcm_run_by_beta_horizontal, 0 < n
   Thus (beta n k) divides lcm_run n                by list_lcm_is_common_multiple
*)
val lcm_run_beta_divisor = store_thm(
  "lcm_run_beta_divisor",
  ``!n k. 0 < k /\ k <= n ==> (beta n k) divides lcm_run n``,
  rw[beta_horizontal_mem, lcm_run_by_beta_horizontal, list_lcm_is_common_multiple]);

(* Theorem: k <= m /\ m <= n ==> (beta n k) divides (beta m k) * (binomial n m) *)
(* Proof:
   Note (binomial m k) * (binomial n m)
      = (binomial n k) * (binomial (n - k) (m - k))                  by binomial_product_identity
   Thus binomial n k divides binomial m k * binomial n m             by divides_def, MULT_COMM
    ==> k * binomial n k divides k * (binomial m k * binomial n m)   by DIVIDES_CANCEL_COMM
                              = (k * binomial m k) * binomial n m    by MULT_ASSOC
     or (beta n k) divides (beta m k) * (binomial n m)               by notation
*)
val beta_divides_beta_factor = store_thm(
  "beta_divides_beta_factor",
  ``!m n k. k <= m /\ m <= n ==> (beta n k) divides (beta m k) * (binomial n m)``,
  rw[] >>
  `binomial n k divides binomial m k * binomial n m` by metis_tac[binomial_product_identity, divides_def, MULT_COMM] >>
  metis_tac[DIVIDES_CANCEL_COMM, MULT_ASSOC]);

(* Theorem: n <= 2 * m /\ m <= n ==> (lcm_run n) divides (binomial n m) * (lcm_run m) *)
(* Proof:
   If n = 0,
      Then lcm_run 0 = 1                         by lcm_run_0
      Hence true                                 by ONE_DIVIDES_ALL
   If n <> 0, then 0 < n.
   Let q = (binomial n m) * (lcm_run m)

   Claim: !x. MEM x (beta_horizontal n) ==> x divides q
   Proof: Note MEM x (beta_horizontal n)
           ==> ?k. 0 < k /\ k <= n /\ (x = beta n k)   by beta_horizontal_member
          Here the picture is:
                     HALF n ... m .... n
              0 ........ k ........... n
          We need k <= m to get x divides q.
          For m < k <= n, we shall use symmetry to get x divides q.
          If k <= m,
             Let p = (beta m k) * (binomial n m).
             Then x divides p                    by beta_divides_beta_factor, k <= m, m <= n
              and (beta m k) divides lcm_run m   by lcm_run_beta_divisor, 0 < k /\ k <= m
               so (beta m k) * (binomial n m)
                  divides
                  (lcm_run m) * (binomial n m)   by DIVIDES_CANCEL, binomial_pos
               or p divides q                    by MULT_COMM
             Thus x divides q                    by DIVIDES_TRANS
          If ~(k <= m), then m < k.
             Note x = beta n (n - k + 1)         by beta_sym, k <= n
              Now n <= m + m                     by given
               so n - k + 1 <= m + m + 1 - k     by arithmetic
              and m + m + 1 - k <= m             by m < k
              ==> n - k + 1 <= m                 by arithmetic
              Let h = n - k + 1, p = (beta m h) * (binomial n m).
             Then x divides p                    by beta_divides_beta_factor, h <= m, m <= n
              and (beta m h) divides lcm_run m   by lcm_run_beta_divisor, 0 < h /\ h <= m
               so (beta m h) * (binomial n m)
                  divides
                  (lcm_run m) * (binomial n m)   by DIVIDES_CANCEL, binomial_pos
               or p divides q                    by MULT_COMM
             Thus x divides q                    by DIVIDES_TRANS

   Therefore,
          (list_lcm (beta_horizontal n)) divides q      by list_lcm_is_least_common_multiple, Claim
       or                    (lcm_run n) divides q      by lcm_run_by_beta_horizontal, 0 < n
*)
val lcm_run_divides_property_alt = store_thm(
  "lcm_run_divides_property_alt",
  ``!m n. n <= 2 * m /\ m <= n ==> (lcm_run n) divides (binomial n m) * (lcm_run m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `q = (binomial n m) * (lcm_run m)` >>
  `!x. MEM x (beta_horizontal n) ==> x divides q` by
  (rpt strip_tac >>
  `?k. 0 < k /\ k <= n /\ (x = beta n k)` by rw[GSYM beta_horizontal_member] >>
  Cases_on `k <= m` >| [
    qabbrev_tac `p = (beta m k) * (binomial n m)` >>
    `x divides p` by rw[beta_divides_beta_factor, Abbr`p`] >>
    `(beta m k) divides lcm_run m` by rw[lcm_run_beta_divisor] >>
    `p divides q` by metis_tac[DIVIDES_CANCEL, MULT_COMM, binomial_pos] >>
    metis_tac[DIVIDES_TRANS],
    `x = beta n (n - k + 1)` by rw[Once beta_sym] >>
    `n - k + 1 <= m` by decide_tac >>
    qabbrev_tac `h = n - k + 1` >>
    qabbrev_tac `p = (beta m h) * (binomial n m)` >>
    `x divides p` by rw[beta_divides_beta_factor, Abbr`p`] >>
    `(beta m h) divides lcm_run m` by rw[lcm_run_beta_divisor, Abbr`h`] >>
    `p divides q` by metis_tac[DIVIDES_CANCEL, MULT_COMM, binomial_pos] >>
    metis_tac[DIVIDES_TRANS]
  ]) >>
  `(list_lcm (beta_horizontal n)) divides q` by metis_tac[list_lcm_is_least_common_multiple] >>
  metis_tac[lcm_run_by_beta_horizontal]);

(* This is the original lcm_run_divides_property to give lcm_run_upper_bound. *)

(* Theorem: lcm_run n <= 4 ** n *)
(* Proof:
   By complete induction on n.
   If EVEN n,
      Base: n = 0.
         LHS = lcm_run 0 = 1               by lcm_run_0
         RHS = 4 ** 0 = 1                  by EXP
         Hence true.
      Step: n <> 0 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = binomial n m * lcm_run m.
         Then n = 2 * m                    by EVEN_HALF
           so m <= 2 * m = n               by arithmetic
         Note 0 < binomial n m             by binomial_pos, m <= n
          and 0 < lcm_run m                by lcm_run_pos
          ==> 0 < c                        by MULT_EQ_0
         Thus (lcm_run n) divides c        by lcm_run_divides_property, m <= n
           or lcm_run n
           <= c                            by DIVIDES_LE, 0 < c
            = (binomial n m) * lcm_run m   by notation
           <= (binomial n m) * 4 ** m      by induction hypothesis, m < n
           <= 4 ** m * 4 ** m              by binomial_middle_upper_bound
            = 4 ** (m + m)                 by EXP_ADD
            = 4 ** n                       by TIMES2, n = 2 * m
         Hence lcm_run n <= 4 ** n.
   If ~EVEN n,
      Then ODD n                           by EVEN_ODD
      Base: n = 1.
         LHS = lcm_run 1 = 1               by lcm_run_1
         RHS = 4 ** 1 = 4                  by EXP
         Hence true.
      Step: n <> 1 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = binomial n (m + 1) * lcm_run (m + 1).
         Then n = 2 * m + 1                by ODD_HALF
          and 0 < m                        by n <> 1
          and m + 1 <= 2 * m + 1 = n       by arithmetic
          But m + 1 <> n                   by m <> 0
           so m + 1 < n                    by m + 1 <> n
         Note 0 < binomial n (m + 1)       by binomial_pos, m + 1 <= n
          and 0 < lcm_run (m + 1)          by lcm_run_pos
          ==> 0 < c                        by MULT_EQ_0
         Thus (lcm_run n) divides c        by lcm_run_divides_property, 0 < m + 1, m + 1 <= n
           or lcm_run n
           <= c                            by DIVIDES_LE, 0 < c
            = (binomial n (m + 1)) * lcm_run (m + 1)   by notation
           <= (binomial n (m + 1)) * 4 ** (m + 1)      by induction hypothesis, m + 1 < n
            = (binomial n m) * 4 ** (m + 1)            by binomial_sym, n - (m + 1) = m
           <= 4 ** m * 4 ** (m + 1)        by binomial_middle_upper_bound
            = 4 ** (m + (m + 1))           by EXP_ADD
            = 4 ** (2 * m + 1)             by arithmetic
            = 4 ** n                       by n = 2 * m + 1
         Hence lcm_run n <= 4 ** n.
*)
val lcm_run_upper_bound = store_thm(
  "lcm_run_upper_bound",
  ``!n. lcm_run n <= 4 ** n``,
  completeInduct_on `n` >>
  Cases_on `EVEN n` >| [
    Cases_on `n = 0` >-
    rw[lcm_run_0] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m` by rw[EVEN_HALF, Abbr`m`] >>
    qabbrev_tac `c = binomial n m * lcm_run m` >>
    `m <= n` by decide_tac >>
    `0 < c` by metis_tac[binomial_pos, lcm_run_pos, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
    `lcm_run n <= c` by rw[lcm_run_divides_property, DIVIDES_LE, Abbr`c`] >>
    `lcm_run m <= 4 ** m` by rw[] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** m * 4 ** m` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** m * 4 ** m = 4 ** n` by metis_tac[EXP_ADD, TIMES2] >>
    decide_tac,
    `ODD n` by metis_tac[EVEN_ODD] >>
    Cases_on `n = 1` >-
    rw[lcm_run_1] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m + 1` by rw[ODD_HALF, Abbr`m`] >>
    `0 < m` by rw[] >>
    qabbrev_tac `c = binomial n (m + 1) * lcm_run (m + 1)` >>
    `m + 1 <= n` by decide_tac >>
    `0 < c` by metis_tac[binomial_pos, lcm_run_pos, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
    `lcm_run n <= c` by rw[lcm_run_divides_property, DIVIDES_LE, Abbr`c`] >>
    `lcm_run (m + 1) <= 4 ** (m + 1)` by rw[] >>
    `binomial n (m + 1) = binomial n m` by rw[Once binomial_sym] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** m * 4 ** (m + 1)` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** m * 4 ** (m + 1) = 4 ** n` by metis_tac[EXP_ADD, ADD_ASSOC, TIMES2] >>
    decide_tac
  ]);

(* This is the original proof of the upper bound. *)

(* ------------------------------------------------------------------------- *)
(* LCM Lower Bound using Maximum                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: POSITIVE l ==> MAX_LIST l <= list_lcm l *)
(* Proof:
   If l = [],
      Note MAX_LIST [] = 0          by MAX_LIST_NIL
       and list_lcm [] = 1          by list_lcm_nil
      Hence true.
   If l <> [],
      Let x = MAX_LIST l.
      Then MEM x l                  by MAX_LIST_MEM
       and x divides (list_lcm l)   by list_lcm_is_common_multiple
       Now 0 < list_lcm l           by list_lcm_pos, EVERY_MEM
        so x <= list_lcm l          by DIVIDES_LE, 0 < list_lcm l
*)
val list_lcm_ge_max = store_thm(
  "list_lcm_ge_max",
  ``!l. POSITIVE l ==> MAX_LIST l <= list_lcm l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[MAX_LIST_NIL, list_lcm_nil] >>
  `MEM (MAX_LIST l) l` by rw[MAX_LIST_MEM] >>
  `0 < list_lcm l` by rw[list_lcm_pos, EVERY_MEM] >>
  rw[list_lcm_is_common_multiple, DIVIDES_LE]);

(* Theorem: (n + 1) * binomial n (HALF n) <= list_lcm [1 .. (n + 1)] *)
(* Proof:
   Note !k. MEM k (binomial_horizontal n) ==> 0 < k by binomial_horizontal_pos_alt [1]

    list_lcm [1 .. (n + 1)]
  = list_lcm (leibniz_vertical n)                by notation
  = list_lcm (leibniz_horizontal n)              by leibniz_lcm_property
  = (n + 1) * list_lcm (binomial_horizontal n)   by leibniz_horizontal_lcm_alt
  >= (n + 1) * MAX_LIST (binomial_horizontal n)  by list_lcm_ge_max, [1], LE_MULT_LCANCEL
  = (n + 1) * binomial n (HALF n)                by binomial_horizontal_max
*)
val lcm_lower_bound_by_list_lcm = store_thm(
  "lcm_lower_bound_by_list_lcm",
  ``!n. (n + 1) * binomial n (HALF n) <= list_lcm [1 .. (n + 1)]``,
  rpt strip_tac >>
  `MAX_LIST (binomial_horizontal n) <= list_lcm (binomial_horizontal n)` by
  (irule list_lcm_ge_max >>
  metis_tac[binomial_horizontal_pos_alt]) >>
  `list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n)` by rw[leibniz_lcm_property] >>
  `_ = (n + 1) * list_lcm (binomial_horizontal n)` by rw[leibniz_horizontal_lcm_alt] >>
  `n + 1 <> 0` by decide_tac >>
  metis_tac[LE_MULT_LCANCEL, binomial_horizontal_max]);

(* Theorem: FINITE s /\ (!x. x IN s ==> 0 < x) ==> MAX_SET s <= big_lcm s *)
(* Proof:
   If s = {},
      Note MAX_SET {} = 0          by MAX_SET_EMPTY
       and big_lcm {} = 1          by big_lcm_empty
      Hence true.
   If s <> {},
      Let x = MAX_SET s.
      Then x IN s                  by MAX_SET_IN_SET
       and x divides (big_lcm s)   by big_lcm_is_common_multiple
       Now 0 < big_lcm s           by big_lcm_positive
        so x <= big_lcm s          by DIVIDES_LE, 0 < big_lcm s
*)
val big_lcm_ge_max = store_thm(
  "big_lcm_ge_max",
  ``!s. FINITE s /\ (!x. x IN s ==> 0 < x) ==> MAX_SET s <= big_lcm s``,
  rpt strip_tac >>
  Cases_on `s = {}` >-
  rw[MAX_SET_EMPTY, big_lcm_empty] >>
  `(MAX_SET s) IN s` by rw[MAX_SET_IN_SET] >>
  `0 < big_lcm s` by rw[big_lcm_positive] >>
  rw[big_lcm_is_common_multiple, DIVIDES_LE]);

(* Theorem: (n + 1) * binomial n (HALF n) <= big_lcm (natural (n + 1)) *)
(* Proof:
   Claim: MAX_SET (IMAGE (binomial n) (count (n + 1))) <= big_lcm (IMAGE (binomial n) count (n + 1))
   Proof: By big_lcm_ge_max, this is to show:
          (1) FINITE (IMAGE (binomial n) (count (n + 1)))
              This is true                                    by FINITE_COUNT, IMAGE_FINITE
          (2) !x. x IN IMAGE (binomial n) (count (n + 1)) ==> 0 < x
              This is true                                    by binomial_pos, IN_IMAGE, IN_COUNT

     big_lcm (natural (n + 1))
   = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))   by big_lcm_natural_eqn
   >= (n + 1) * MAX_SET (IMAGE (binomial n) (count (n + 1)))  by claim, LE_MULT_LCANCEL
   = (n + 1) * binomial n (HALF n)                            by binomial_row_max
*)
val lcm_lower_bound_by_big_lcm = store_thm(
  "lcm_lower_bound_by_big_lcm",
  ``!n. (n + 1) * binomial n (HALF n) <= big_lcm (natural (n + 1))``,
  rpt strip_tac >>
  `MAX_SET (IMAGE (binomial n) (count (n + 1))) <=
       big_lcm (IMAGE (binomial n) (count (n + 1)))` by
  ((irule big_lcm_ge_max >> rpt conj_tac) >-
  metis_tac[binomial_pos, IN_IMAGE, IN_COUNT, DECIDE``x < n + 1 ==> x <= n``] >>
  rw[]
  ) >>
  metis_tac[big_lcm_natural_eqn, LE_MULT_LCANCEL, binomial_row_max, DECIDE``n + 1 <> 0``]);

(* ------------------------------------------------------------------------- *)
(* Consecutive LCM function                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
            !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= list_lcm [1 .. n] *)
(* Proof:
   Note ODD n ==> n <> 0                  by EVEN_0, EVEN_ODD
   If n = 1,
      Note 1 <= pi                        by 0 < pi
        so 2 <= 2 * pi                    by LE_MULT_LCANCEL, 2 <> 0
        or 1 < 2 * pi                     by arithmetic
      Thus 1 DIV (2 * pi) = 0             by ONE_DIV, 1 < 2 * pi
       and SQRT (1 DIV (2 * pi)) = 0      by ZERO_EXP, 0 ** h, h <> 0
       But list_lcm [1 .. 1] = 1          by list_lcm_sing
        so SQRT (1 DIV (2 * pi)) * 2 ** 1 <= list_lcm [1 .. 1]    by MULT
   If n <> 1,
      Then 0 < n - 1.
      Let m = n - 1, then n = m + 1       by arithmetic
      and n * binomial m (HALF m) <= list_lcm [1 .. n]   by lcm_lower_bound_by_list_lcm
      Now !a b c. (a DIV b) * c = (a * c) DIV b          by DIV_1, MULT_RIGHT_1, c = c DIV 1, b * 1 = b
      Note ODD n ==> EVEN m               by EVEN_ODD_SUC, ADD1
           n * binomial m (HALF m)
         = n * (2 ** n DIV SQRT (2 * pi * m))     by binomial_middle_by_stirling
         = (2 ** n DIV SQRT (2 * pi * m)) * n     by MULT_COMM
         = (2 ** n * n) DIV (SQRT (2 * pi * m))   by above
         = (n * 2 ** n) DIV (SQRT (2 * pi * m))   by MULT_COMM
         = (n DIV SQRT (2 * pi * m)) * 2 ** n     by above
         = (SQRT (n DIV (2 * pi)) * 2 ** n        by assumption, m = n - 1
      Hence SQRT (n DIV (2 * pi))) * (2 ** n) <= list_lcm [1 .. n]
*)
val lcm_lower_bound_by_list_lcm_stirling = store_thm(
  "lcm_lower_bound_by_list_lcm_stirling",
  ``Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
   !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= list_lcm [1 .. n]``,
  rpt strip_tac >>
  `!n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = 2 ** (n + 1) DIV SQRT (2 * pi * n))` by prove_tac[binomial_middle_by_stirling] >>
  `n <> 0` by metis_tac[EVEN_0, EVEN_ODD] >>
  Cases_on `n = 1` >| [
    `1 <= pi` by decide_tac >>
    `1 < 2 * pi` by decide_tac >>
    `1 DIV (2 * pi) = 0` by rw[ONE_DIV] >>
    `SQRT (1 DIV (2 * pi)) * 2 ** 1 = 0` by rw[] >>
    rw[list_lcm_sing],
    `0 < n - 1 /\ (n = (n - 1) + 1)` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `n * binomial m (HALF m) <= list_lcm [1 .. n]` by metis_tac[lcm_lower_bound_by_list_lcm] >>
    `EVEN m` by metis_tac[EVEN_ODD_SUC, ADD1] >>
    `!a b c. (a DIV b) * c = (a * c) DIV b` by metis_tac[DIV_1, MULT_RIGHT_1] >>
    `n * binomial m (HALF m) = n * (2 ** n DIV SQRT (2 * pi * m))` by rw[] >>
    `_ = (n DIV SQRT (2 * pi * m)) * 2 ** n` by metis_tac[MULT_COMM] >>
    metis_tac[]
  ]);

(* Theorem: big_lcm (natural n) <= big_lcm (natural (n + 1)) *)
(* Proof:
   Note FINITE (natural n)                    by natural_finite
    and 0 < big_lcm (natural n)               by big_lcm_positive, natural_element
       big_lcm (natural n)
    <= lcm (SUC n) (big_lcm (natural n))      by LCM_LE, 0 < SUC n, 0 < big_lcm (natural n)
     = big_lcm ((SUC n) INSERT (natural n))   by big_lcm_insert
     = big_lcm (natural (SUC n))              by natural_suc
     = big_lcm (natural (n + 1))              by ADD1
*)
val big_lcm_non_decreasing = store_thm(
  "big_lcm_non_decreasing",
  ``!n. big_lcm (natural n) <= big_lcm (natural (n + 1))``,
  rpt strip_tac >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `0 < big_lcm (natural n)` by rw[big_lcm_positive, natural_element] >>
  `big_lcm (natural (n + 1)) = big_lcm (natural (SUC n))` by rw[ADD1] >>
  `_ = big_lcm ((SUC n) INSERT (natural n))` by rw[natural_suc] >>
  `_ = lcm (SUC n) (big_lcm (natural n))` by rw[big_lcm_insert] >>
  rw[LCM_LE]);

(* Theorem: Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
            !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= big_lcm (natural n) *)
(* Proof:
   Note ODD n ==> n <> 0                  by EVEN_0, EVEN_ODD
   If n = 1,
      Note 1 <= pi                        by 0 < pi
        so 2 <= 2 * pi                    by LE_MULT_LCANCEL, 2 <> 0
        or 1 < 2 * pi                     by arithmetic
      Thus 1 DIV (2 * pi) = 0             by ONE_DIV, 1 < 2 * pi
       and SQRT (1 DIV (2 * pi)) = 0      by ZERO_EXP, 0 ** h, h <> 0
       But big_lcm (natural 1) = 1        by list_lcm_sing, natural_1
        so SQRT (1 DIV (2 * pi)) * 2 ** 1 <= big_lcm (natural 1)    by MULT
   If n <> 1,
      Then 0 < n - 1.
      Let m = n - 1, then n = m + 1       by arithmetic
      and n * binomial m (HALF m) <= big_lcm (natural n)   by lcm_lower_bound_by_big_lcm
      Now !a b c. (a DIV b) * c = (a * c) DIV b            by DIV_1, MULT_RIGHT_1, c = c DIV 1, b * 1 = b
      Note ODD n ==> EVEN m               by EVEN_ODD_SUC, ADD1
           n * binomial m (HALF m)
         = n * (2 ** n DIV SQRT (2 * pi * m))     by binomial_middle_by_stirling
         = (2 ** n DIV SQRT (2 * pi * m)) * n     by MULT_COMM
         = (2 ** n * n) DIV (SQRT (2 * pi * m))   by above
         = (n * 2 ** n) DIV (SQRT (2 * pi * m))   by MULT_COMM
         = (n DIV SQRT (2 * pi * m)) * 2 ** n     by above
         = (SQRT (n DIV (2 * pi)) * 2 ** n        by assumption, m = n - 1
      Hence SQRT (n DIV (2 * pi))) * (2 ** n) <= big_lcm (natural n)
*)
val lcm_lower_bound_by_big_lcm_stirling = store_thm(
  "lcm_lower_bound_by_big_lcm_stirling",
  ``Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
   !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= big_lcm (natural n)``,
  rpt strip_tac >>
  `!n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = 2 ** (n + 1) DIV SQRT (2 * pi * n))` by prove_tac[binomial_middle_by_stirling] >>
  `n <> 0` by metis_tac[EVEN_0, EVEN_ODD] >>
  Cases_on `n = 1` >| [
    `1 <= pi` by decide_tac >>
    `1 < 2 * pi` by decide_tac >>
    `1 DIV (2 * pi) = 0` by rw[ONE_DIV] >>
    `SQRT (1 DIV (2 * pi)) * 2 ** 1 = 0` by rw[] >>
    rw[big_lcm_sing],
    `0 < n - 1 /\ (n = (n - 1) + 1)` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `n * binomial m (HALF m) <= big_lcm (natural n)` by metis_tac[lcm_lower_bound_by_big_lcm] >>
    `EVEN m` by metis_tac[EVEN_ODD_SUC, ADD1] >>
    `!a b c. (a DIV b) * c = (a * c) DIV b` by metis_tac[DIV_1, MULT_RIGHT_1] >>
    `n * binomial m (HALF m) = n * (2 ** n DIV SQRT (2 * pi * m))` by rw[] >>
    `_ = (n DIV SQRT (2 * pi * m)) * 2 ** n` by metis_tac[MULT_COMM] >>
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Extra Theorems (not used)                                                 *)
(* ------------------------------------------------------------------------- *)

(*
This is GCD_CANCEL_MULT by coprime p n, and coprime p n ==> coprime (p ** k) n by coprime_exp.
Note prime_not_divides_is_coprime.
*)

(* Theorem: prime p /\ m divides n /\ ~((p * m) divides n) ==> (gcd (p * m) n = m) *)
(* Proof:
   Note m divides n ==> ?q. n = q * m     by divides_def

   Claim: coprime p q
   Proof: By contradiction, suppose gcd p q <> 1.
          Since (gcd p q) divides p       by GCD_IS_GREATEST_COMMON_DIVISOR
             so gcd p q = p               by prime_def, gcd p q <> 1.
             or p divides q               by divides_iff_gcd_fix
          Now, m <> 0 because
               If m = 0, p * m = 0        by MULT_0
               Then m divides n and ~((p * m) divides n) are contradictory.
          Thus p * m divides q * m        by DIVIDES_MULTIPLE_IFF, MULT_COMM, p divides q, m <> 0
          But q * m = n, contradicting ~((p * m) divides n).

      gcd (p * m) n
    = gcd (p * m) (q * m)                 by n = q * m
    = m * gcd p q                         by GCD_COMMON_FACTOR, MULT_COMM
    = m * 1                               by coprime p q, from Claim
    = m
*)
val gcd_prime_product_property = store_thm(
  "gcd_prime_product_property",
  ``!p m n. prime p /\ m divides n /\ ~((p * m) divides n) ==> (gcd (p * m) n = m)``,
  rpt strip_tac >>
  `?q. n = q * m` by rw[GSYM divides_def] >>
  `m <> 0` by metis_tac[MULT_0] >>
  `coprime p q` by
  (spose_not_then strip_assume_tac >>
  `(gcd p q) divides p` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
  `gcd p q = p` by metis_tac[prime_def] >>
  `p divides q` by rw[divides_iff_gcd_fix] >>
  metis_tac[DIVIDES_MULTIPLE_IFF, MULT_COMM]) >>
  metis_tac[GCD_COMMON_FACTOR, MULT_COMM, MULT_RIGHT_1]);

(* Theorem: prime p /\ m divides n /\ ~((p * m) divides n) ==>(lcm (p * m) n = p * n) *)
(* Proof:
   Note m <> 0                             by MULT_0, m divides n /\ ~((p * m) divides n)
   and   m * lcm (p * m) n
       = gcd (p * m) n * lcm (p * m) n     by gcd_prime_product_property
       = (p * m) * n                       by GCD_LCM
       = (m * p) * n                       by MULT_COMM
       = m * (p * n)                       by MULT_ASSOC
   Thus   lcm (p * m) n = p * n            by MULT_LEFT_CANCEL
*)
val lcm_prime_product_property = store_thm(
  "lcm_prime_product_property",
  ``!p m n. prime p /\ m divides n /\ ~((p * m) divides n) ==>(lcm (p * m) n = p * n)``,
  rpt strip_tac >>
  `m <> 0` by metis_tac[MULT_0] >>
  `m * lcm (p * m) n = gcd (p * m) n * lcm (p * m) n` by rw[gcd_prime_product_property] >>
  `_ = (p * m) * n` by rw[GCD_LCM] >>
  `_ = m * (p * n)` by metis_tac[MULT_COMM, MULT_ASSOC] >>
  metis_tac[MULT_LEFT_CANCEL]);

(* Theorem: prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l) *)
(* Proof:
   By induction on l.
   Base: prime p /\ p divides list_lcm [] ==> p divides PROD_SET (set [])
      Note list_lcm [] = 1                  by list_lcm_nil
       and PROD_SET (set [])
         = PROD_SET {}                      by LIST_TO_SET
         = 1                                by PROD_SET_EMPTY
      Hence conclusion is alredy in predicate, thus true.
   Step: prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l) ==>
         prime p /\ p divides list_lcm (h::l) ==> p divides PROD_SET (set (h::l))
      Note PROD_SET (set (h::l))
         = PROD_SET (h INSERT set l)        by LIST_TO_SET
      This is to show: p divides PROD_SET (h INSERT set l)

      Let x = list_lcm l.
      Since p divides (lcm h x)             by given
         so p divides (gcd h x) * (lcm h x) by DIVIDES_MULTIPLE
         or p divides h * x                 by GCD_LCM
        ==> p divides h  or  p divides x    by P_EUCLIDES
      Case: p divides h.
      If h IN set l, or MEM h l,
         Then h divides x                                       by list_lcm_is_common_multiple
           so p divides x                                       by DIVIDES_TRANS
         Thus p divides PROD_SET (set l)                        by induction hypothesis
           or p divides PROD_SET (h INSERT set l)               by ABSORPTION
      If ~(h IN set l),
         Then PROD_SET (h INSERT set l) = h * PROD_SET (set l)  by PROD_SET_INSERT
           or p divides PROD_SET (h INSERT set l)               by DIVIDES_MULTIPLE, MULT_COMM
      Case: p divides x.
      If h IN set l, or MEM h l,
         Then p divides PROD_SET (set l)                        by induction hypothesis
           or p divides PROD_SET (h INSERT set l)               by ABSORPTION
      If ~(h IN set l),
         Then PROD_SET (h INSERT set l) = h * PROD_SET (set l)  by PROD_SET_INSERT
           or p divides PROD_SET (h INSERT set l)               by DIVIDES_MULTIPLE
*)
val list_lcm_prime_factor = store_thm(
  "list_lcm_prime_factor",
  ``!p l. prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l)``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[] >>
  qabbrev_tac `x = list_lcm l` >>
  `(gcd h x) * (lcm h x) = h * x` by rw[GCD_LCM] >>
  `p divides (h * x)` by metis_tac[DIVIDES_MULTIPLE] >>
  `p divides h \/ p divides x` by rw[P_EUCLIDES] >| [
    Cases_on `h IN set l` >| [
      `h divides x` by rw[list_lcm_is_common_multiple, Abbr`x`] >>
      `p divides x` by metis_tac[DIVIDES_TRANS] >>
      fs[ABSORPTION],
      rw[PROD_SET_INSERT] >>
      metis_tac[DIVIDES_MULTIPLE, MULT_COMM]
    ],
    Cases_on `h IN set l` >-
    fs[ABSORPTION] >>
    rw[PROD_SET_INSERT] >>
    metis_tac[DIVIDES_MULTIPLE]
  ]);

(* Theorem: prime p /\ p divides PROD_SET (set l) ==> ?x. MEM x l /\ p divides x *)
(* Proof:
   By induction on l.
   Base: prime p /\ p divides PROD_SET (set []) ==> ?x. MEM x [] /\ p divides x
          p divides PROD_SET (set [])
      ==> p divides PROD_SET {}            by LIST_TO_SET
      ==> p divides 1                      by PROD_SET_EMPTY
      ==> p = 1                            by DIVIDES_ONE
      This contradicts with 1 < p          by ONE_LT_PRIME
   Step: prime p /\ p divides PROD_SET (set l) ==> ?x. MEM x l /\ p divides x ==>
         !h. prime p /\ p divides PROD_SET (set (h::l)) ==> ?x. MEM x (h::l) /\ p divides x
      Note PROD_SET (set (h::l))
         = PROD_SET (h INSERT set l)                              by LIST_TO_SET
      This is to show: ?x. ((x = h) \/ MEM x l) /\ p divides x    by MEM
      If h IN set l, or MEM h l,
         Then h INSERT set l = set l                              by ABSORPTION
         Thus ?x. MEM x l /\ p divides x                          by induction hypothesis
      If ~(h IN set l),
         Then PROD_SET (h INSERT set l) = h * PROD_SET (set l)    by PROD_SET_INSERT
         Thus p divides h \/ p divides (PROD_SET (set l))         by P_EUCLIDES
         Case p divides h.
              Take x = h, the result is true.
         Case p divides PROD_SET (set l).
              Then ?x. MEM x l /\ p divides x                     by induction hypothesis
*)
val list_product_prime_factor = store_thm(
  "list_product_prime_factor",
  ``!p l. prime p /\ p divides PROD_SET (set l) ==> ?x. MEM x l /\ p divides x``,
  strip_tac >>
  Induct >| [
    rpt strip_tac >>
    `PROD_SET (set []) = 1` by rw[PROD_SET_EMPTY] >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `p <> 1` by decide_tac >>
    metis_tac[DIVIDES_ONE],
    rw[] >>
    Cases_on `h IN set l` >-
    metis_tac[ABSORPTION] >>
    fs[PROD_SET_INSERT] >>
    `p divides h \/ p divides (PROD_SET (set l))` by rw[P_EUCLIDES] >-
    metis_tac[] >>
    metis_tac[]
  ]);

(* Theorem: prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x *)
(* Proof: by list_lcm_prime_factor, list_product_prime_factor *)
val list_lcm_prime_factor_member = store_thm(
  "list_lcm_prime_factor_member",
  ``!p l. prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x``,
  rw[list_lcm_prime_factor, list_product_prime_factor]);

(* ------------------------------------------------------------------------- *)
(* Integer Functions Computation Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   SQRT n       = ROOT 2 n
   LOG2 n       = LOG 2 n
   n power_of b = perfect_power n b
*)

(* Definitions and Theorems (# are exported):

   ROOT computation:
   ROOT_POWER       |- !a n. 1 < a /\ 0 < n ==> (ROOT n (a ** n) = a)
   ROOT_FROM_POWER  |- !m n b. 0 < m /\ (b ** m = n) ==> (b = ROOT m n)
#  ROOT_OF_0        |- !m. 0 < m ==> (ROOT m 0 = 0)
#  ROOT_OF_1        |- !m. 0 < m ==> (ROOT m 1 = 1)
   ROOT_EQ_0        |- !m. 0 < m ==> !n. (ROOT m n = 0) <=> (n = 0)
#  ROOT_1           |- !n. ROOT 1 n = n
   ROOT_THM         |- !r. 0 < r ==> !n p. (ROOT r n = p) <=> p ** r <= n /\ n < SUC p ** r
   ROOT_compute     |- !r n. 0 < r ==> (ROOT r 0 = 0) /\
                            (ROOT r n = (let x = 2 * ROOT r (n DIV 2 ** r)
                                          in if n < SUC x ** r then x else SUC x))
   ROOT_EQN         |- !r n. 0 < r ==> (ROOT r n =
                             (let m = TWICE (ROOT r (n DIV 2 ** r))
                               in m + if (m + 1) ** r <= n then 1 else 0))
   ROOT_EVAL        |- !r n. ROOT r n =
                             if r = 0 then ROOT 0 n
                             else if n = 0 then 0
                             else (let m = TWICE (ROOT r (n DIV 2 ** r))
                                    in m + if SUC m ** r <= n then 1 else 0)
   ROOT_SUC         |- !r n. 0 < r ==>
                             ROOT r (SUC n) = ROOT r n +
                                              if SUC n = SUC (ROOT r n) ** r then 1 else 0
   ROOT_EQ_1        |- !m. 0 < m ==> !n. (ROOT m n = 1) <=> 0 < n /\ n < 2 ** m
   ROOT_LE_SELF     |- !m n. 0 < m ==> ROOT m n <= n
   ROOT_EQ_SELF     |- !m n. 0 < m ==> (ROOT m n = n) <=> (m = 1) \/ (n = 0) \/ (n = 1))
   ROOT_GE_SELF     |- !m n. 0 < m ==> (n <= ROOT m n) <=> (m = 1) \/ (n = 0) \/ (n = 1))
   ROOT_LE_REVERSE  |- !a b n. 0 < a /\ a <= b ==> ROOT b n <= ROOT a n

   Square Root:
   SQRT_PROPERTY    |- !n. 0 < n ==> SQRT n ** 2 <= n /\ n < SUC (SQRT n) ** 2
   SQRT_THM         |- !n p. (SQRT n = p) <=> p ** 2 <= n /\ n < SUC p ** 2
   SQ_SQRT_LE       |- !n. SQ (SQRT n) <= n
   SQRT_LE          |- !n m. n <= m ==> SQRT n <= SQRT m
   SQRT_LT          |- !n m. n < m ==> SQRT n <= SQRT m
#  SQRT_0           |- SQRT 0 = 0
#  SQRT_1           |- SQRT 1 = 1
   SQRT_EQ_0        |- !n. (SQRT n = 0) <=> (n = 0)
   SQRT_EQ_1        |- !n. (SQRT n = 1) <=> (n = 1) \/ (n = 2) \/ (n = 3)
   SQRT_EXP_2       |- !n. SQRT (n ** 2) = n
   SQRT_OF_SQ       |- !n. SQRT (n ** 2) = n
   SQRT_SQ          |- !n. SQRT (SQ n) = n
   SQRT_LE_SELF     |- !n. SQRT n <= n
   SQRT_GE_SELF     |- !n. n <= SQRT n <=> (n = 0) \/ (n = 1)
   SQRT_EQ_SELF     |- !n. (SQRT n = n) <=> (n = 0) \/ (n = 1)
   SQRT_LE_IMP      |- !n m. SQRT n <= m ==> n <= 3 * m ** 2

   Logarithm:
   LOG_EXACT_EXP    |- !a. 1 < a ==> !n. LOG a (a ** n) = n
   EXP_TO_LOG       |- !a b n. 1 < a /\ 0 < b /\ b <= a ** n ==> LOG a b <= n
   LOG_THM          |- !a n. 1 < a /\ 0 < n ==>
                       !p. (LOG a n = p) <=> a ** p <= n /\ n < a ** SUC p
   LOG_EVAL         |- !m n. LOG m n = if m <= 1 \/ n = 0 then LOG m n
                             else if n < m then 0 else SUC (LOG m (n DIV m))
   LOG_TEST         |- !a n. 1 < a /\ 0 < n ==>
                       !p. (LOG a n = p) <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n
   LOG_POWER        |- !b x n. 1 < b /\ 0 < x /\ 0 < n ==>
                          n * LOG b x <= LOG b (x ** n) /\
                          LOG b (x ** n) < n * SUC (LOG b x)
   LOG_LE_REVERSE   |- !a b n. 1 < a /\ 0 < n /\ a <= b ==> LOG b n <= LOG a n

#  LOG2_1              |- LOG2 1 = 0
#  LOG2_2              |- LOG2 2 = 1
   LOG2_THM            |- !n. 0 < n ==> !p. (LOG2 n = p) <=> 2 ** p <= n /\ n < 2 ** SUC p
   LOG2_PROPERTY       |- !n. 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n)
   TWO_EXP_LOG2_LE     |- !n. 0 < n ==> 2 ** LOG2 n <= n
   LOG2_UNIQUE         |- !n m. 2 ** m <= n /\ n < 2 ** SUC m ==> (LOG2 n = m)
   LOG2_EQ_0           |- !n. 0 < n ==> (LOG2 n = 0 <=> n = 1)
   LOG2_EQ_1           |- !n. 0 < n ==> ((LOG2 n = 1) <=> (n = 2) \/ (n = 3))
   LOG2_LE_MONO        |- !n m. 0 < n ==> n <= m ==> LOG2 n <= LOG2 m
   LOG2_LE             |- !n m. 0 < n /\ n <= m ==> LOG2 n <= LOG2 m
   LOG2_LT             |- !n m. 0 < n /\ n < m ==> LOG2 n <= LOG2 m
   LOG2_LT_SELF        |- !n. 0 < n ==> LOG2 n < n
   LOG2_NEQ_SELF       |- !n. 0 < n ==> LOG2 n <> n
   LOG2_EQ_SELF        |- !n. (LOG2 n = n) ==> (n = 0)
#  LOG2_POS            |- !n. 1 < n ==> 0 < LOG2 n
   LOG2_TWICE_LT       |- !n. 1 < n ==> 1 < 2 * LOG2 n
   LOG2_TWICE_SQ       |- !n. 1 < n ==> 4 <= (2 * LOG2 n) ** 2
   LOG2_SUC_TWICE_SQ   |- !n. 0 < n ==> 4 <= (2 * SUC (LOG2 n)) ** 2
   LOG2_SUC_SQ         |- !n. 1 < n ==> 1 < SUC (LOG2 n) ** 2
   LOG2_SUC_TIMES_SQ_DIV_2_POS  |- !n m. 1 < m ==> 0 < SUC (LOG2 n) * (m ** 2 DIV 2)
   LOG2_2_EXP          |- !n. LOG2 (2 ** n) = n
   LOG2_EXACT_EXP      |- !n. (2 ** LOG2 n = n) <=> ?k. n = 2 ** k
   LOG2_MULT_EXP       |- !n m. 0 < n ==> (LOG2 (n * 2 ** m) = LOG2 n + m)
   LOG2_TWICE          |- !n. 0 < n ==> (LOG2 (TWICE n) = 1 + LOG2 n)
   LOG2_HALF           |- !n. 1 < n ==> (LOG2 (HALF n) = LOG2 n - 1)
   LOG2_BY_HALF        |- !n. 1 < n ==> (LOG2 n = 1 + LOG2 (HALF n))
   LOG2_DIV_EXP        |- !n m. 2 ** m < n ==> (LOG2 (n DIV 2 ** m) = LOG2 n - m)

   LOG2 Computation:
   halves_def          |- !n. halves n = if n = 0 then 0 else SUC (halves (HALF n))
   halves_alt          |- !n. halves n = if n = 0 then 0 else 1 + halves (HALF n)
#  halves_0            |- halves 0 = 0
#  halves_1            |- halves 1 = 1
#  halves_2            |- halves 2 = 2
#  halves_pos          |- !n. 0 < n ==> 0 < halves n
   halves_by_LOG2      |- !n. 0 < n ==> (halves n = 1 + LOG2 n)
   LOG2_compute        |- !n. LOG2 n = if n = 0 then LOG2 0 else halves n - 1
   halves_le           |- !m n. m <= n ==> halves m <= halves n
   halves_eq_0         |- !n. (halves n = 0) <=> (n = 0)
   halves_eq_1         |- !n. (halves n = 1) <=> (n = 1)

   Perfect Power and Power Free:
   perfect_power_def        |- !n m. perfect_power n m <=> ?e. n = m ** e
   perfect_power_self       |- !n. perfect_power n n
   perfect_power_0_m        |- !m. perfect_power 0 m <=> (m = 0)
   perfect_power_1_m        |- !m. perfect_power 1 m
   perfect_power_n_0        |- !n. perfect_power n 0 <=> (n = 0) \/ (n = 1)
   perfect_power_n_1        |- !n. perfect_power n 1 <=> (n = 1)
   perfect_power_mod_eq_0   |- !n m. 0 < m /\ 1 < n /\ n MOD m = 0 ==>
                                     (perfect_power n m <=> perfect_power (n DIV m) m)
   perfect_power_mod_ne_0   |- !n m. 0 < m /\ 1 < n /\ n MOD m <> 0 ==> ~perfect_power n m
   perfect_power_test       |- !n m. perfect_power n m <=>
                                     if n = 0 then m = 0
                                     else if n = 1 then T
                                     else if m = 0 then n <= 1
                                     else if m = 1 then n = 1
                                     else if n MOD m = 0 then perfect_power (n DIV m) m
                                     else F
   perfect_power_suc        |- !m n. 1 < m /\ perfect_power n m /\ perfect_power (SUC n) m ==>
                                     (m = 2) /\ (n = 1)
   perfect_power_not_suc    |- !m n. 1 < m /\ 1 < n /\ perfect_power n m ==> ~perfect_power (SUC n) m
   LOG_SUC                  |- !b n. 1 < b /\ 0 < n ==>
                                     LOG b (SUC n) = LOG b n +
                                         if perfect_power (SUC n) b then 1 else 0
   perfect_power_bound_LOG2 |- !n. 0 < n ==> !m. perfect_power n m <=> ?k. k <= LOG2 n /\ (n = m ** k)
   perfect_power_condition  |- !p q. prime p /\ (?x y. 0 < x /\ (p ** x = q ** y)) ==> perfect_power q p
   perfect_power_cofactor   |- !n p. 0 < p /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p)
   perfect_power_cofactor_alt
                            |- !n p. 0 < n /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p)
   perfect_power_2_odd      |- !n. perfect_power n 2 ==> (ODD n <=> (n = 1))

   Power Free:
   power_free_def           |- !n. power_free n <=> !m e. (n = m ** e) ==> (m = n) /\ (e = 1)
   power_free_0             |- power_free 0 <=> F
   power_free_1             |- power_free 1 <=> F
   power_free_gt_1          |- !n. power_free n ==> 1 < n
   power_free_alt           |- !n. power_free n <=> 1 < n /\ !m. perfect_power n m ==> (n = m)
   prime_is_power_free      |- !n. prime n ==> power_free n
   power_free_perfect_power |- !m n. power_free n /\ perfect_power n m ==> (n = m)
   power_free_property      |- !n. power_free n ==> !j. 1 < j ==> ROOT j n ** j <> n
   power_free_check_all     |- !n. power_free n <=> 1 < n /\ !j. 1 < j ==> ROOT j n ** j <> n

   Upper Logarithm:
   count_up_def   |- !n m k. count_up n m k = if m = 0 then 0
                                else if n <= m then k
                                else count_up n (2 * m) (SUC k)
   ulog_def       |- !n. ulog n = count_up n 1 0
#  ulog_0         |- ulog 0 = 0
#  ulog_1         |- ulog 1 = 0
#  ulog_2         |- ulog 2 = 1

   count_up_exit       |- !m n. m <> 0 /\ n <= m ==> !k. count_up n m k = k
   count_up_suc        |- !m n. m <> 0 /\ m < n ==> !k. count_up n m k = count_up n (2 * m) (SUC k)
   count_up_suc_eqn    |- !m. m <> 0 ==> !n t. 2 ** t * m < n ==>
                          !k. count_up n m k = count_up n (2 ** SUC t * m) (SUC k + t)
   count_up_exit_eqn   |- !m. m <> 0 ==> !n t. 2 ** t * m < 2 * n /\ n <= 2 ** t * m ==>
                          !k. count_up n m k = k + t
   ulog_unique         |- !m n. 2 ** m < 2 * n /\ n <= 2 ** m ==> (ulog n = m)
   ulog_eqn            |- !n. ulog n = if 1 < n then SUC (LOG2 (n - 1)) else 0
   ulog_suc            |- !n. 0 < n ==> (ulog (SUC n) = SUC (LOG2 n))
   ulog_property       |- !n. 0 < n ==> 2 ** ulog n < 2 * n /\ n <= 2 ** ulog n
   ulog_thm            |- !n. 0 < n ==> !m. (ulog n = m) <=> 2 ** m < 2 * n /\ n <= 2 ** m
   ulog_def_alt        |- (ulog 0 = 0) /\
                          !n. 0 < n ==> !m. (ulog n = m) <=> n <= 2 ** m /\ 2 ** m < TWICE n
   ulog_eq_0           |- !n. (ulog n = 0) <=> (n = 0) \/ (n = 1)
   ulog_eq_1           |- !n. (ulog n = 1) <=> (n = 2)
   ulog_le_1           |- !n. ulog n <= 1 <=> n <= 2
   ulog_le             |- !m n. n <= m ==> ulog n <= ulog m
   ulog_lt             |- !m n. n < m ==> ulog n <= ulog m
   ulog_2_exp          |- !n. ulog (2 ** n) = n
   ulog_le_self        |- !n. ulog n <= n
   ulog_eq_self        |- !n. (ulog n = n) <=> (n = 0)
   ulog_lt_self        |- !n. 0 < n ==> ulog n < n
   ulog_exp_exact      |- !n. (2 ** ulog n = n) <=> perfect_power n 2
   ulog_exp_not_exact  |- !n. ~perfect_power n 2 ==> 2 ** ulog n <> n
   ulog_property_not_exact   |- !n. 0 < n /\ ~perfect_power n 2 ==> n < 2 ** ulog n
   ulog_property_odd         |- !n. 1 < n /\ ODD n ==> n < 2 ** ulog n
   exp_to_ulog         |- !m n. n <= 2 ** m ==> ulog n <= m
#  ulog_pos            |- !n. 1 < n ==> 0 < ulog n
   ulog_ge_1           |- !n. 1 < n ==> 1 <= ulog n
   ulog_sq_gt_1        |- !n. 2 < n ==> 1 < ulog n ** 2
   ulog_twice_sq       |- !n. 1 < n ==> 4 <= TWICE (ulog n) ** 2
   ulog_alt            |- !n. ulog n = if n = 0 then 0
                              else if perfect_power n 2 then LOG2 n else SUC (LOG2 n)
   ulog_LOG2           |- !n. 0 < n ==> LOG2 n <= ulog n /\ ulog n <= 1 + LOG2 n
   perfect_power_bound_ulog
                       |- !n. 0 < n ==> !m. perfect_power n m <=> ?k. k <= ulog n /\ (n = m ** k)

   Upper Log Theorems:
   ulog_mult      |- !m n. ulog (m * n) <= ulog m + ulog n
   ulog_exp       |- !m n. ulog (m ** n) <= n * ulog m
   ulog_even      |- !n. 0 < n /\ EVEN n ==> (ulog n = 1 + ulog (HALF n))
   ulog_odd       |- !n. 1 < n /\ ODD n ==> ulog (HALF n) + 1 <= ulog n
   ulog_half      |- !n. 1 < n ==> ulog (HALF n) + 1 <= ulog n
   sqrt_upper     |- !n. SQRT n <= 2 ** ulog n

   Power Free up to a limit:
   power_free_upto_def |- !n k. n power_free_upto k <=> !j. 1 < j /\ j <= k ==> ROOT j n ** j <> n
   power_free_upto_0   |- !n. n power_free_upto 0 <=> T
   power_free_upto_1   |- !n. n power_free_upto 1 <=> T
   power_free_upto_suc |- !n k. 0 < k /\ n power_free_upto k ==>
                               (n power_free_upto k + 1 <=> ROOT (k + 1) n ** (k + 1) <> n)
   power_free_check_upto_LOG2  |- !n. power_free n <=> 1 < n /\ n power_free_upto LOG2 n
   power_free_check_upto_ulog  |- !n. power_free n <=> 1 < n /\ n power_free_upto ulog n
   power_free_check_upto       |- !n b. LOG2 n <= b ==> (power_free n <=> 1 < n /\ n power_free_upto b)
   power_free_2        |- power_free 2
   power_free_3        |- power_free 3
   power_free_test_def |- !n. power_free_test n <=> 1 < n /\ n power_free_upto ulog n
   power_free_test_eqn |- !n. power_free_test n <=> power_free n
   power_free_test_upto_LOG2   |- !n. power_free n <=>
                                      1 < n /\ !j. 1 < j /\ j <= LOG2 n ==> ROOT j n ** j <> n
   power_free_test_upto_ulog   |- !n. power_free n <=>
                                      1 < n /\ !j. 1 < j /\ j <= ulog n ==> ROOT j n ** j <> n

   Another Characterisation of Power Free:
   power_index_def      |- !n k. power_index n k =
                                      if k <= 1 then 1
                                 else if ROOT k n ** k = n then k
                                 else power_index n (k - 1)
   power_index_0        |- !n. power_index n 0 = 1
   power_index_1        |- !n. power_index n 1 = 1
   power_index_eqn      |- !n k. ROOT (power_index n k) n ** power_index n k = n
   power_index_root     |- !n k. perfect_power n (ROOT (power_index n k) n)
   power_index_of_1     |- !k. power_index 1 k = if k = 0 then 1 else k
   power_index_exact_root      |- !n k. 0 < k /\ (ROOT k n ** k = n) ==> (power_index n k = k)
   power_index_not_exact_root  |- !n k. ROOT k n ** k <> n ==> (power_index n k = power_index n (k - 1))
   power_index_no_exact_roots  |- !m n k. k <= m /\ (!j. k < j /\ j <= m ==> ROOT j n ** j <> n) ==>
                                          (power_index n m = power_index n k)
   power_index_lower    |- !m n k. k <= m /\ (ROOT k n ** k = n) ==> k <= power_index n m
   power_index_pos      |- !n k. 0 < power_index n k
   power_index_upper    |- !n k. 0 < k ==> power_index n k <= k
   power_index_equal    |- !m n k. 0 < k /\ k <= m ==>
                           ((power_index n m = power_index n k) <=> !j. k < j /\ j <= m ==> ROOT j n ** j <> n)
   power_index_property |- !m n k. (power_index n m = k) ==> !j. k < j /\ j <= m ==> ROOT j n ** j <> n

   power_free_by_power_index_LOG2
                        |- !n. power_free n <=> 1 < n /\ (power_index n (LOG2 n) = 1)
   power_free_by_power_index_ulog
                        |- !n. power_free n <=> 1 < n /\ (power_index n (ulog n) = 1)

*)

(* ------------------------------------------------------------------------- *)
(* ROOT Computation                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ROOT n (a ** n) = a *)
(* Proof:
   Since   a < SUC a         by LESS_SUC
      a ** n < (SUC a) ** n  by EXP_BASE_LT_MONO
   Let b = a ** n,
   Then  a ** n <= b         by LESS_EQ_REFL
    and  b < (SUC a) ** n    by above
   Hence a = ROOT n b        by ROOT_UNIQUE
*)
val ROOT_POWER = store_thm(
  "ROOT_POWER",
  ``!a n. 1 < a /\ 0 < n ==> (ROOT n (a ** n) = a)``,
  rw[EXP_BASE_LT_MONO, ROOT_UNIQUE]);

(* Theorem: 0 < m /\ (b ** m = n) ==> (b = ROOT m n) *)
(* Proof:
   Note n <= n                  by LESS_EQ_REFL
     so b ** m <= n             by b ** m = n
   Also b < SUC b               by LESS_SUC
     so b ** m < (SUC b) ** m   by EXP_EXP_LT_MONO, 0 < m
     so n < (SUC b) ** m        by b ** m = n
   Thus b = ROOT m n            by ROOT_UNIQUE
*)
val ROOT_FROM_POWER = store_thm(
  "ROOT_FROM_POWER",
  ``!m n b. 0 < m /\ (b ** m = n) ==> (b = ROOT m n)``,
  rpt strip_tac >>
  rw[ROOT_UNIQUE]);

(* Theorem: 0 < m ==> (ROOT m 0 = 0) *)
(* Proof:
   Note 0 ** m = 0    by EXP_0
   Thus 0 = ROOT m 0  by ROOT_FROM_POWER
*)
val ROOT_OF_0 = store_thm(
  "ROOT_OF_0[simp]",
  ``!m. 0 < m ==> (ROOT m 0 = 0)``,
  rw[ROOT_FROM_POWER]);

(* Theorem: 0 < m ==> (ROOT m 1 = 1) *)
(* Proof:
   Note 1 ** m = 1    by EXP_1
   Thus 1 = ROOT m 1  by ROOT_FROM_POWER
*)
val ROOT_OF_1 = store_thm(
  "ROOT_OF_1[simp]",
  ``!m. 0 < m ==> (ROOT m 1 = 1)``,
  rw[ROOT_FROM_POWER]);

(* Theorem: 0 < r ==> !n p. (ROOT r n = p) <=> (p ** r <= n /\ n < SUC p ** r) *)
(* Proof:
   If part: 0 < r ==> ROOT r n ** r <= n /\ n < SUC (ROOT r n) ** r
      This is true             by ROOT, 0 < r
   Only-if part: p ** r <= n /\ n < SUC p ** r ==> ROOT r n = p
      This is true             by ROOT_UNIQUE
*)
val ROOT_THM = store_thm(
  "ROOT_THM",
  ``!r. 0 < r ==> !n p. (ROOT r n = p) <=> (p ** r <= n /\ n < SUC p ** r)``,
  metis_tac[ROOT, ROOT_UNIQUE]);

(* Rework proof of ROOT_COMPUTE in logroot theory. *)
(* ./num/extra_theories/logrootScript.sml *)

(* ROOT r n = r-th root of n.

Make use of indentity:
n ^ (1/r) = 2 (n/ 2^r) ^(1/r)

if n = 0 then 0
else (* precompute *) let x = 2 * r-th root of (n DIV (2 ** r))
     (* apply *) in if n < (SUC x) ** r then x else (SUC x)
*)

(*

val lem = prove(``0 < r ==> (0 ** r = 0)``, RW_TAC arith_ss [EXP_EQ_0]);

val ROOT_COMPUTE = Q.store_thm("ROOT_COMPUTE",
   `!r n.
       0 < r ==>
       (ROOT r 0 = 0) /\
       (ROOT r n = let x = 2 * ROOT r (n DIV 2 ** r) in
                      if n < SUC x ** r then x else SUC x)`,
   RW_TAC (arith_ss ++ boolSimps.LET_ss) []
   THEN MATCH_MP_TAC ROOT_UNIQUE
   THEN CONJ_TAC
   THEN FULL_SIMP_TAC arith_ss [NOT_LESS, EXP_1, lem]
   THEN MAP_FIRST MATCH_MP_TAC
          [LESS_EQ_TRANS, DECIDE ``!a b c. a < b /\ b <= c ==> a < c``]
   THENL [
      Q.EXISTS_TAC `ROOT r n ** r`,
      Q.EXISTS_TAC `SUC (ROOT r n) ** r`]
   THEN RW_TAC arith_ss
           [ROOT, GSYM EXP_LE_ISO, GSYM ROOT_DIV, DECIDE ``0 < 2n``]
   THEN METIS_TAC
           [DIVISION, MULT_COMM, DECIDE ``0 < 2n``,
            DECIDE ``(a = b + c) ==> b <= a:num``, ADD1, LE_ADD_LCANCEL,
            DECIDE ``a <= 1 = a < 2n``]);

> ROOT_COMPUTE;
val it =
   |- !r n.
     0 < r ==>
     (ROOT r 0 = 0) /\
     (ROOT r n =
      (let x = 2 * ROOT r (n DIV 2 ** r)
       in
         if n < SUC x ** r then x else SUC x)):
   thm
*)

(* Theorem: 0 < m ==> !n. (ROOT m n = 0) <=> (n = 0) *)
(* Proof:
   If part: ROOT m n = 0 ==> n = 0
      Note n < SUC (ROOT m n) ** r      by ROOT
        or n < SUC 0 ** m               by ROOT m n = 0
        so n < 1                        by ONE, EXP_1
        or n = 0                        by arithmetic
   Only-if part: ROOT m 0 = 0, true     by ROOT_OF_0
*)
val ROOT_EQ_0 = store_thm(
  "ROOT_EQ_0",
  ``!m. 0 < m ==> !n. (ROOT m n = 0) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  `n < 1` by metis_tac[ROOT, EXP_1, ONE] >>
  decide_tac);

(* Theorem: ROOT 1 n = n *)
(* Proof:
   Note n ** 1 = n      by EXP_1
     so n ** 1 <= n
   Also n < SUC n       by LESS_SUC
     so n < SUC n ** 1  by EXP_1
   Thus ROOT 1 n = n    by ROOT_UNIQUE
*)
val ROOT_1 = store_thm(
  "ROOT_1[simp]",
  ``!n. ROOT 1 n = n``,
  rw[ROOT_UNIQUE]);

(* This is a rework of logrootTheory.ROOT_COMPUTE *)

(* Theorem: 0 < r ==> (ROOT r 0 = 0) /\
           (ROOT r n = let x = 2 * ROOT r (n DIV 2 ** r) in if n < SUC x ** r then x else SUC x) *)
(* Proof:
   This is to show:
   (1) ROOT r 0 = 0, true     by ROOT_EQ_0
   (2) ROOT r n = (let x = 2 * ROOT r (n DIV 2 ** r) in if n < SUC x ** r then x else SUC x)
       Let x = 2 * ROOT r (n DIV 2 ** r).
       To show: ROOT r n = if n < SUC x ** r then x else SUC x
       By ROOT_UNIQUE, this is to show:
       (1) n < SUC (if n < SUC x ** r then x else SUC x) ** r
           If n < SUC x ** r, to show: n < SUC x ** r, true trivially
           If ~(n < SUC x ** r), to show: n < SUC (SUC x) ** r
           Let y = SUC (ROOT r n) ** r.
           Then n < y                                   by ROOT
            and ROOT r n <= SUC (2 * HALF (ROOT r n))   by TWO_HALF_LESS_EQ
            But x = 2 * HALF (ROOT r n)                 by ROOT_DIV
             so ROOT r n <= SUC x                       by above
             or        y <= SUC (SUC x) ** r            by EXP_LE_ISO
           Thus         n < SUC (SUC x) ** r            by LESS_LESS_EQ_TRANS

       (2) (if n < SUC x ** r then x else SUC x) ** r <= n
           If n < SUC x ** r, to show: x ** r <= n
           Let y = ROOT r n ** r.
           Then y <= n                                  by ROOT
            and 2 * HALF (ROOT r n) <= ROOT r n         by TWO_HALF_LESS_EQ
            But x = 2 * HALF (ROOT r n)                 by ROOT_DIV
             so x <= ROOT r n                           by above
             or        x ** r <= y                      by EXP_LE_ISO
           Thus        x ** r <= n                      by LESS_EQ_TRANS

*)
val ROOT_compute = store_thm(
  "ROOT_compute",
  ``!r n. 0 < r ==> (ROOT r 0 = 0) /\
                   (ROOT r n = let x = 2 * ROOT r (n DIV 2 ** r) in
                               if n < SUC x ** r then x else SUC x)``,
  rpt strip_tac >-
  rw[ROOT_EQ_0] >>
  rw_tac std_ss[] >>
  (irule ROOT_UNIQUE >> rpt conj_tac >> simp[]) >| [
    rw[] >>
    `x = 2 * HALF (ROOT r n)` by rw[ROOT_DIV, Abbr`x`] >>
    qabbrev_tac `y = SUC (ROOT r n) ** r` >>
    `n < y` by rw[ROOT, Abbr`y`] >>
    `ROOT r n <= SUC x` by rw[TWO_HALF_LESS_EQ] >>
    `y <= SUC (SUC x) ** r` by rw[EXP_LE_ISO, Abbr`y`] >>
    decide_tac,
    rw[] >>
    `x = 2 * HALF (ROOT r n)` by rw[ROOT_DIV, Abbr`x`] >>
    qabbrev_tac `y = ROOT r n ** r` >>
    `y <= n` by rw[ROOT, Abbr`y`] >>
    `x <= ROOT r n` by rw[TWO_HALF_LESS_EQ] >>
    `x ** r <= y` by rw[EXP_LE_ISO, Abbr`y`] >>
    decide_tac
  ]);

(* Theorem: 0 < r ==> (ROOT r n =
            let m = 2 * ROOT r (n DIV 2 ** r) in m + if (m + 1) ** r <= n then 1 else 0) *)
(* Proof:
     ROOT k n
   = if n < SUC m ** k then m else SUC m               by ROOT_COMPUTE
   = if SUC m ** k <= n then SUC m else m              by logic
   = if (m + 1) ** k <= n then (m + 1) else m          by ADD1
   = m + if (m + 1) ** k <= n then 1 else 0            by arithmetic
*)
val ROOT_EQN = store_thm(
  "ROOT_EQN",
  ``!r n. 0 < r ==> (ROOT r n =
         let m = 2 * ROOT r (n DIV 2 ** r) in m + if (m + 1) ** r <= n then 1 else 0)``,
  rw_tac std_ss[] >>
  Cases_on `(m + 1) ** r <= n` >-
  rw[ROOT_COMPUTE, ADD1] >>
  rw[ROOT_COMPUTE, ADD1]);

(* Theorem: ROOT r n =
    if r = 0 then ROOT 0 n else
    if n = 0 then 0 else
    let m = TWICE (ROOT r (n DIV 2 ** r)) in
    m + if (SUC m) ** r <= n then 1 else 0 *)
(* Proof: by ROOT_OF_0, ROOT_EQN *)
val ROOT_EVAL = store_thm(
  "ROOT_EVAL[compute]", (* put in computeLib *)
  ``!r n. ROOT r n =
    if r = 0 then ROOT 0 n else
    if n = 0 then 0 else
    let m = TWICE (ROOT r (n DIV 2 ** r)) in
    m + if (SUC m) ** r <= n then 1 else 0``,
  metis_tac[ROOT_OF_0, ROOT_EQN, ADD1, NOT_ZERO_LT_ZERO]);
(* Put ROOT_EVAL into computeLib *)

(*
> EVAL ``ROOT 3 125``;
val it = |- ROOT 3 125 = 5: thm
> EVAL ``ROOT 3 100``;
val it = |- ROOT 3 100 = 4: thm
> EVAL ``MAP (ROOT 3) [1 .. 20]``; =
      [1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]: thm
> EVAL ``MAP (ROOT 3) [1 .. 30]``; =
      [1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3]: thm
*)

(* Theorem: 0 < r ==>
            (ROOT r (SUC n) = ROOT r n + if SUC n = (SUC (ROOT r n)) ** r then 1 else 0) *)
(* Proof:
   Let x = ROOT r n, y = ROOT r (SUC n).  x <= y.
   Note n < (SUC x) ** r /\ x ** r <= n          by ROOT_THM
    and SUC n < (SUC y) ** r /\ y ** r <= SUC n  by ROOT_THM
   Since n < (SUC x) ** r,
    SUC n <= (SUC x) ** r.
   If SUC n = (SUC x) ** r,
      Then y = ROOT r (SUC n)
             = ROOT r ((SUC x) ** r)
             = SUC x                             by ROOT_POWER
   If SUC n < (SUC x) ** r,
      Then x ** r <= n < SUC n                   by LESS_SUC
      Thus x = y                                 by ROOT_THM
*)
val ROOT_SUC = store_thm(
  "ROOT_SUC",
  ``!r n. 0 < r ==>
   (ROOT r (SUC n) = ROOT r n + if SUC n = (SUC (ROOT r n)) ** r then 1 else 0)``,
  rpt strip_tac >>
  qabbrev_tac `x = ROOT r n` >>
  qabbrev_tac `y = ROOT r (SUC n)` >>
  Cases_on `n = 0` >| [
    `x = 0` by rw[ROOT_OF_0, Abbr`x`] >>
    `y = 1` by rw[ROOT_OF_1, Abbr`y`] >>
    simp[],
    `x <> 0` by rw[ROOT_EQ_0, Abbr`x`] >>
    `n < (SUC x) ** r /\ x ** r <= n` by metis_tac[ROOT_THM] >>
    `SUC n < (SUC y) ** r /\ y ** r <= SUC n` by metis_tac[ROOT_THM] >>
    `(SUC n = (SUC x) ** r) \/ SUC n < (SUC x) ** r` by decide_tac >| [
      `1 < SUC x` by decide_tac >>
      `y = SUC x` by metis_tac[ROOT_POWER] >>
      simp[],
      `x ** r <= SUC n` by decide_tac >>
      `x = y` by metis_tac[ROOT_THM] >>
      simp[]
    ]
  ]);

(*
ROOT_SUC;
|- !r n. 0 < r ==> ROOT r (SUC n) = ROOT r n + if SUC n = SUC (ROOT r n) ** r then 1 else 0
Let z = ROOT r n.

   z(n)
   -------------------------------------------------
                      n   (n+1=(z+1)**r)

> EVAL ``MAP (ROOT 2) [1 .. 20]``;
val it = |- MAP (ROOT 2) [1 .. 20] =
      [1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 4; 4; 4; 4; 4]: thm
       1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20
*)

(* Theorem: 0 < m ==> !n. (ROOT m n = 1) <=> (0 < n /\ n < 2 ** m) *)
(* Proof:
       ROOT m n = 1
   <=> 1 ** m <= n /\ n < (SUC 1) ** m    by ROOT_THM, 0 < m
   <=> 1 <= n /\ n < 2 ** m               by TWO, EXP_1
   <=> 0 < n /\ n < 2 ** m                by arithmetic
*)
val ROOT_EQ_1 = store_thm(
  "ROOT_EQ_1",
  ``!m. 0 < m ==> !n. (ROOT m n = 1) <=> (0 < n /\ n < 2 ** m)``,
  rpt strip_tac >>
  `!n. 0 < n <=> 1 <= n` by decide_tac >>
  metis_tac[ROOT_THM, TWO, EXP_1]);

(* Theorem: 0 < m ==> ROOT m n <= n *)
(* Proof:
   Let r = ROOT m n.
   Note r <= r ** m   by X_LE_X_EXP, 0 < m
          <= n        by ROOT
*)
val ROOT_LE_SELF = store_thm(
  "ROOT_LE_SELF",
  ``!m n. 0 < m ==> ROOT m n <= n``,
  metis_tac[X_LE_X_EXP, ROOT, LESS_EQ_TRANS]);

(* Theorem: 0 < m ==> ((ROOT m n = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1))) *)
(* Proof:
   If part: ROOT m n = n ==> m = 1 \/ n = 0 \/ n = 1
      Note n ** m <= n               by ROOT, 0 < r
       But n <= n ** m               by X_LE_X_EXP, 0 < m
        so n ** m = n                by EQ_LESS_EQ
       ==> m = 1 or n = 0 or n = 1   by EXP_EQ_SELF
   Only-if part: ROOT 1 n = n /\ ROOT m 0 = 0 /\ ROOT m 1 = 1
      True by ROOT_1, ROOT_OF_0, ROOT_OF_1.
*)
val ROOT_EQ_SELF = store_thm(
  "ROOT_EQ_SELF",
  ``!m n. 0 < m ==> ((ROOT m n = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1)))``,
  (rw_tac std_ss[EQ_IMP_THM] >> rw[]) >>
  `n ** m <= n` by metis_tac[ROOT] >>
  `n <= n ** m` by rw[X_LE_X_EXP] >>
  `n ** m = n` by decide_tac >>
  rw[GSYM EXP_EQ_SELF]);

(* Theorem: 0 < m ==> (n <= ROOT m n <=> ((m = 1) \/ (n = 0) \/ (n = 1))) *)
(* Proof:
   Note ROOT m n <= n                     by ROOT_LE_SELF
   Thus n <= ROOT m n <=> ROOT m n = n    by EQ_LESS_EQ
   The result follows                     by ROOT_EQ_SELF
*)
val ROOT_GE_SELF = store_thm(
  "ROOT_GE_SELF",
  ``!m n. 0 < m ==> (n <= ROOT m n <=> ((m = 1) \/ (n = 0) \/ (n = 1)))``,
  metis_tac[ROOT_LE_SELF, ROOT_EQ_SELF, EQ_LESS_EQ]);

(*
EVAL ``MAP (\k. ROOT k 100)  [1 .. 10]``; = [100; 10; 4; 3; 2; 2; 1; 1; 1; 1]: thm

This shows (ROOT k) is a decreasing function of k,
but this is very hard to prove without some real number theory.
Even this is hard to prove: ROOT 3 n <= ROOT 2 n

No! -- this can be proved, see below.
*)

(* Theorem: 0 < a /\ a <= b ==> ROOT b n <= ROOT a n *)
(* Proof:
   Let x = ROOT a n, y = ROOT b n. To show: y <= x.
   By contradiction, suppose x < y.
   Then SUC x <= y.
   Note x ** a <= n /\ n < (SUC x) ** a     by ROOT
    and y ** b <= n /\ n < (SUC y) ** b     by ROOT
    But a <= b
        (SUC x) ** a
     <= (SUC x) ** b       by EXP_BASE_LEQ_MONO_IMP, 0 < SUC x, a <= b
     <=       y ** b       by EXP_EXP_LE_MONO, 0 < b
   This leads to n < (SUC x) ** a <= y ** b <= n, a contradiction.
*)
val ROOT_LE_REVERSE = store_thm(
  "ROOT_LE_REVERSE",
  ``!a b n. 0 < a /\ a <= b ==> ROOT b n <= ROOT a n``,
  rpt strip_tac >>
  qabbrev_tac `x = ROOT a n` >>
  qabbrev_tac `y = ROOT b n` >>
  spose_not_then strip_assume_tac >>
  `0 < b /\ SUC x <= y` by decide_tac >>
  `x ** a <= n /\ n < (SUC x) ** a` by rw[ROOT, Abbr`x`] >>
  `y ** b <= n /\ n < (SUC y) ** b` by rw[ROOT, Abbr`y`] >>
  `(SUC x) ** a <= (SUC x) ** b` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  `(SUC x) ** b <= y ** b` by rw[EXP_EXP_LE_MONO] >>
  decide_tac);


(* ------------------------------------------------------------------------- *)
(* Square Root                                                               *)
(* ------------------------------------------------------------------------- *)
(* Use overload for SQRT *)
val _ = overload_on ("SQRT", ``\n. ROOT 2 n``);

(*
> EVAL ``SQRT 4``;
val it = |- SQRT 4 = 2: thm
> EVAL ``(SQRT 4) ** 2``;
val it = |- SQRT 4 ** 2 = 4: thm
> EVAL ``(SQRT 5) ** 2``;
val it = |- SQRT 5 ** 2 = 4: thm
> EVAL ``(SQRT 8) ** 2``;
val it = |- SQRT 8 ** 2 = 4: thm
> EVAL ``(SQRT 9) ** 2``;
val it = |- SQRT 9 ** 2 = 9: thm

> EVAL ``LOG2 4``;
val it = |- LOG2 4 = 2: thm
> EVAL ``2 ** (LOG2 4)``;
val it = |- 2 ** LOG2 4 = 4: thm
> EVAL ``2 ** (LOG2 5)``;
val it = |- 2 ** LOG2 5 = 4: thm
> EVAL ``2 ** (LOG2 6)``;
val it = |- 2 ** LOG2 6 = 4: thm
> EVAL ``2 ** (LOG2 7)``;
val it = |- 2 ** LOG2 7 = 4: thm
> EVAL ``2 ** (LOG2 8)``;
val it = |- 2 ** LOG2 8 = 8: thm

> EVAL ``SQRT 9``;
val it = |- SQRT 9 = 3: thm
> EVAL ``SQRT 8``;
val it = |- SQRT 8 = 2: thm
> EVAL ``SQRT 7``;
val it = |- SQRT 7 = 2: thm
> EVAL ``SQRT 6``;
val it = |- SQRT 6 = 2: thm
> EVAL ``SQRT 5``;
val it = |- SQRT 5 = 2: thm
> EVAL ``SQRT 4``;
val it = |- SQRT 4 = 2: thm
> EVAL ``SQRT 3``;
val it = |- SQRT 3 = 1: thm
*)

(*
EXP_BASE_LT_MONO |- !b. 1 < b ==> !n m. b ** m < b ** n <=> m < n
LT_EXP_ISO       |- !e a b. 1 < e ==> (a < b <=> e ** a < e ** b)

ROOT_exists      |- !r n. 0 < r ==> ?rt. rt ** r <= n /\ n < SUC rt ** r
ROOT_UNIQUE      |- !r n p. p ** r <= n /\ n < SUC p ** r ==> (ROOT r n = p)
ROOT_LE_MONO     |- !r x y. 0 < r ==> x <= y ==> ROOT r x <= ROOT r y

LOG_exists       |- ?f. !a n. 1 < a /\ 0 < n ==> a ** f a n <= n /\ n < a ** SUC (f a n)
LOG_UNIQUE       |- !a n p. a ** p <= n /\ n < a ** SUC p ==> (LOG a n = p)
LOG_LE_MONO      |- !a x y. 1 < a /\ 0 < x ==> x <= y ==> LOG a x <= LOG a y

LOG_EXP    |- !n a b. 1 < a /\ 0 < b ==> (LOG a (a ** n * b) = n + LOG a b)
LOG        |- !a n. 1 < a /\ 0 < n ==> a ** LOG a n <= n /\ n < a ** SUC (LOG a n)
*)

(* Theorem: 0 < n ==> (SQRT n) ** 2 <= n /\ n < SUC (SQRT n) ** 2 *)
(* Proof: by ROOT:
   |- !r n. 0 < r ==> ROOT r n ** r <= n /\ n < SUC (ROOT r n) ** r
*)
val SQRT_PROPERTY = store_thm(
  "SQRT_PROPERTY",
  ``!n. (SQRT n) ** 2 <= n /\ n < SUC (SQRT n) ** 2``,
  rw[ROOT]);

(* Obtain a theorem *)
val SQRT_THM = save_thm("SQRT_THM",
    ROOT_THM |> SPEC ``2`` |> SIMP_RULE (srw_ss())[]);
(* val SQRT_THM = |- !n p. (SQRT n = p) <=> p ** 2 <= n /\ n < SUC p ** 2: thm *)

(* Theorem: SQ (SQRT n) <= n *)
(* Proof: by SQRT_PROPERTY, EXP_2 *)
val SQ_SQRT_LE = store_thm(
  "SQ_SQRT_LE",
  ``!n. SQ (SQRT n) <= n``,
  metis_tac[SQRT_PROPERTY, EXP_2]);

(* Theorem: n <= m ==> SQRT n <= SQRT m *)
(* Proof: by ROOT_LE_MONO *)
val SQRT_LE = store_thm(
  "SQRT_LE",
  ``!n m. n <= m ==> SQRT n <= SQRT m``,
  rw[ROOT_LE_MONO]);

(* Theorem: n < m ==> SQRT n <= SQRT m *)
(* Proof:
   Since n < m ==> n <= m   by LESS_IMP_LESS_OR_EQ
   This is true             by ROOT_LE_MONO
*)
val SQRT_LT = store_thm(
  "SQRT_LT",
  ``!n m. n < m ==> SQRT n <= SQRT m``,
  rw[ROOT_LE_MONO, LESS_IMP_LESS_OR_EQ]);

(* Theorem: SQRT 0 = 0 *)
(* Proof: by ROOT_OF_0 *)
val SQRT_0 = store_thm(
  "SQRT_0[simp]",
  ``SQRT 0 = 0``,
  rw[]);

(* Theorem: SQRT 1 = 1 *)
(* Proof: by ROOT_OF_1 *)
val SQRT_1 = store_thm(
  "SQRT_1[simp]",
  ``SQRT 1 = 1``,
  rw[]);

(* Theorem: SQRT n = 0 <=> n = 0 *)
(* Proof:
   If part: SQRT n = 0 ==> n = 0.
   By contradiction, suppose n <> 0.
      This means 1 <= n
      Hence  SQRT 1 <= SQRT n   by SQRT_LE
         so       1 <= SQRT n   by SQRT_1
      This contradicts SQRT n = 0.
   Only-if part: n = 0 ==> SQRT n = 0
      True since SQRT 0 = 0     by SQRT_0
*)
val SQRT_EQ_0 = store_thm(
  "SQRT_EQ_0",
  ``!n. (SQRT n = 0) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `1 <= n` by decide_tac >>
  `SQRT 1 <= SQRT n` by rw[SQRT_LE] >>
  `SQRT 1 = 1` by rw[] >>
  decide_tac);

(* Theorem: SQRT n = 1 <=> n = 1 \/ n = 2 \/ n = 3 *)
(* Proof:
   If part: SQRT n = 1 ==> (n = 1) \/ (n = 2) \/ (n = 3).
   By contradiction, suppose n <> 1 /\ n <> 2 /\ n <> 3.
      Note n <> 0    by SQRT_EQ_0
      This means 4 <= n
      Hence  SQRT 4 <= SQRT n   by SQRT_LE
         so       2 <= SQRT n   by EVAL_TAC, SQRT 4 = 2
      This contradicts SQRT n = 1.
   Only-if part: n = 1 \/ n = 2 \/ n = 3 ==> SQRT n = 1
      All these are true        by EVAL_TAC
*)
val SQRT_EQ_1 = store_thm(
  "SQRT_EQ_1",
  ``!n. (SQRT n = 1) <=> ((n = 1) \/ (n = 2) \/ (n = 3))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n <> 0` by metis_tac[SQRT_EQ_0] >>
    `4 <= n` by decide_tac >>
    `SQRT 4 <= SQRT n` by rw[SQRT_LE] >>
    `SQRT 4 = 2` by EVAL_TAC >>
    decide_tac,
    EVAL_TAC,
    EVAL_TAC,
    EVAL_TAC
  ]);

(* Theorem: SQRT (n ** 2) = n *)
(* Proof:
   If 1 < n, true                       by ROOT_POWER, 0 < 2
   Otherwise, n = 0 or n = 1.
      When n = 0,
           SQRT (0 ** 2) = SQRT 0 = 0   by SQRT_0
      When n = 1,
           SQRT (1 ** 2) = SQRT 1 = 1   by SQRT_1
*)
val SQRT_EXP_2 = store_thm(
  "SQRT_EXP_2",
  ``!n. SQRT (n ** 2) = n``,
  rpt strip_tac >>
  Cases_on `1 < n` >-
  fs[ROOT_POWER] >>
  `(n = 0) \/ (n = 1)` by decide_tac >>
  rw[]);

(* Theorem alias *)
val SQRT_OF_SQ = save_thm("SQRT_OF_SQ", SQRT_EXP_2);
(* val SQRT_OF_SQ = |- !n. SQRT (n ** 2) = n: thm *)

(* Theorem: SQRT (SQ n) = n *)
(* Proof:
     SQRT (SQ n)
   = SQRT (n ** 2)     by EXP_2
   = n                 by SQRT_EXP_2
*)
val SQRT_SQ = store_thm(
  "SQRT_SQ",
  ``!n. SQRT (SQ n) = n``,
  metis_tac[SQRT_EXP_2, EXP_2]);

(* Theorem: SQRT n <= n *)
(* Proof:
   Note      n <= n ** 2          by SELF_LE_SQ
   Thus SQRT n <= SQRT (n ** 2)   by SQRT_LE
     or SQRT n <= n               by SQRT_EXP_2
*)
val SQRT_LE_SELF = store_thm(
  "SQRT_LE_SELF",
  ``!n. SQRT n <= n``,
  metis_tac[SELF_LE_SQ, SQRT_LE, SQRT_EXP_2]);

(* Theorem: (n <= SQRT n) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: (n <= SQRT n) ==> ((n = 0) \/ (n = 1))
     By contradiction, suppose n <> 0 /\ n <> 1.
     Then 1 < n, implying n ** 2 <= SQRT n ** 2   by EXP_BASE_LE_MONO
      but SQRT n ** 2 <= n                        by SQRT_PROPERTY
       so n ** 2 <= n                             by LESS_EQ_TRANS
       or n * n <= n * 1                          by EXP_2
       or     n <= 1                              by LE_MULT_LCANCEL, n <> 0.
     This contradicts 1 < n.
   Only-if part: ((n = 0) \/ (n = 1)) ==> (n <= SQRT n)
     This is to show:
     (1) 0 <= SQRT 0, true by SQRT 0 = 0          by SQRT_0
     (2) 1 <= SQRT 1, true by SQRT 1 = 1          by SQRT_1
*)
val SQRT_GE_SELF = store_thm(
  "SQRT_GE_SELF",
  ``!n. (n <= SQRT n) <=> ((n = 0) \/ (n = 1))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `1 < n` by decide_tac >>
    `n ** 2 <= SQRT n ** 2` by rw[EXP_BASE_LE_MONO] >>
    `SQRT n ** 2 <= n` by rw[SQRT_PROPERTY] >>
    `n ** 2 <= n` by metis_tac[LESS_EQ_TRANS] >>
    `n * n <= n * 1` by metis_tac[EXP_2, MULT_RIGHT_1] >>
    `n <= 1` by metis_tac[LE_MULT_LCANCEL] >>
    decide_tac,
    rw[],
    rw[]
  ]);

(* Theorem: (SQRT n = n) <=> ((n = 0) \/ (n = 1)) *)
(* Proof: by ROOT_EQ_SELF, 0 < 2 *)
val SQRT_EQ_SELF = store_thm(
  "SQRT_EQ_SELF",
  ``!n. (SQRT n = n) <=> ((n = 0) \/ (n = 1))``,
  rw[ROOT_EQ_SELF]);

(* Theorem: SQRT n <= m ==> n <= 3 * (m ** 2) *)
(* Proof:
   Note n < (SUC (SQRT n)) ** 2                by SQRT_PROPERTY
          = SUC ((SQRT n) ** 2) + 2 * SQRT n   by SUC_SQ
   Thus n <= m ** 2 + 2 * m                    by SQRT n <= m
          <= m ** 2 + 2 * m ** 2               by arithmetic
           = 3 * m ** 2
*)
val SQRT_LE_IMP = store_thm(
  "SQRT_LE_IMP",
  ``!n m. SQRT n <= m ==> n <= 3 * (m ** 2)``,
  rpt strip_tac >>
  `n < (SUC (SQRT n)) ** 2` by rw[SQRT_PROPERTY] >>
  `SUC (SQRT n) ** 2 = SUC ((SQRT n) ** 2) + 2 * SQRT n` by rw[SUC_SQ] >>
  `SQRT n ** 2 <= m ** 2` by rw[] >>
  `2 * SQRT n <= 2 * m` by rw[] >>
  `2 * m <= 2 * m * m` by rw[] >>
  `2 * m * m = 2 * m ** 2` by rw[] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Logarithm                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < a ==> LOG a (a ** n) = n *)
(* Proof:
     LOG a (a ** n)
   = LOG a ((a ** n) * 1)     by MULT_RIGHT_1
   = n + LOG a 1              by LOG_EXP
   = n + 0                    by LOG_1
   = n                        by ADD_0
*)
val LOG_EXACT_EXP = store_thm(
  "LOG_EXACT_EXP",
  ``!a. 1 < a ==> !n. LOG a (a ** n) = n``,
  metis_tac[MULT_RIGHT_1, LOG_EXP, LOG_1, ADD_0, DECIDE``0 < 1``]);

(* Theorem: 1 < a /\ 0 < b /\ b <= a ** n ==> LOG a b <= n *)
(* Proof:
   Given     b <= a ** n
       LOG a b <= LOG a (a ** n)   by LOG_LE_MONO
                = n                by LOG_EXACT_EXP
*)
val EXP_TO_LOG = store_thm(
  "EXP_TO_LOG",
  ``!a b n. 1 < a /\ 0 < b /\ b <= a ** n ==> LOG a b <= n``,
  metis_tac[LOG_LE_MONO, LOG_EXACT_EXP]);

(* Theorem: 1 < a /\ 0 < n ==> !p. (LOG a n = p) <=> (a ** p <= n /\ n < a ** SUC p) *)
(* Proof:
   If part: 1 < a /\ 0 < n ==> a ** LOG a n <= n /\ n < a ** SUC (LOG a n)
      This is true by LOG.
   Only-if part: a ** p <= n /\ n < a ** SUC p ==> LOG a n = p
      This is true by LOG_UNIQUE
*)
val LOG_THM = store_thm(
  "LOG_THM",
  ``!a n. 1 < a /\ 0 < n ==> !p. (LOG a n = p) <=> (a ** p <= n /\ n < a ** SUC p)``,
  metis_tac[LOG, LOG_UNIQUE]);

(* Theorem: LOG m n = if m <= 1 \/ (n = 0) then LOG m n
            else if n < m then 0 else SUC (LOG m (n DIV m)) *)
(* Proof: by LOG_RWT *)
val LOG_EVAL = store_thm(
  "LOG_EVAL[compute]",
  ``!m n. LOG m n = if m <= 1 \/ (n = 0) then LOG m n
         else if n < m then 0 else SUC (LOG m (n DIV m))``,
  rw[LOG_RWT]);
(* Put to computeLib for LOG evaluation of any base *)

(*
> EVAL ``MAP (LOG 3) [1 .. 20]``; =
      [0; 0; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]: thm
> EVAL ``MAP (LOG 3) [1 .. 30]``; =
      [0; 0; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3]: thm
*)

(* Theorem: 1 < a /\ 0 < n ==>
           !p. (LOG a n = p) <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n *)
(* Proof:
   Note !p. LOG a n = p
        <=> n < a ** SUC p /\ a ** p <= n                by LOG_THM
        <=> n < a ** SUC p /\ a * a ** p <= a * n        by LE_MULT_LCANCEL
        <=> n < a ** SUC p /\ a ** SUC p <= a * n        by EXP
        <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n   by arithmetic
*)
val LOG_TEST = store_thm(
  "LOG_TEST",
  ``!a n. 1 < a /\ 0 < n ==>
   !p. (LOG a n = p) <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n``,
  rw[EQ_IMP_THM] >| [
    `n < a ** SUC (LOG a n)` by metis_tac[LOG_THM] >>
    decide_tac,
    `a ** (LOG a n) <= n` by metis_tac[LOG_THM] >>
    rw[EXP],
    `a * a ** p <= a * n` by fs[EXP] >>
    `a ** p <= n` by fs[] >>
    `n < a ** SUC p` by decide_tac >>
    metis_tac[LOG_THM]
  ]);

(* For continuous functions, log_b (x ** y) = y * log_b x. *)

(* Theorem: 1 < b /\ 0 < x /\ 0 < n ==>
           n * LOG b x <= LOG b (x ** n) /\ LOG b (x ** n) < n * SUC (LOG b x) *)
(* Proof:
   Note:
> LOG_THM |> SPEC ``b:num`` |> SPEC ``x:num``;
val it = |- 1 < b /\ 0 < x ==> !p. LOG b x = p <=> b ** p <= x /\ x < b ** SUC p: thm
> LOG_THM |> SPEC ``b:num`` |> SPEC ``(x:num) ** n``;
val it = |- 1 < b /\ 0 < x ** n ==>
   !p. LOG b (x ** n) = p <=> b ** p <= x ** n /\ x ** n < b ** SUC p: thm

   Let y = LOG b x, z = LOG b (x ** n).
   Then b ** y <= x /\ x < b ** SUC y              by LOG_THM, (1)
    and b ** z <= x ** n /\ x ** n < b ** SUC z    by LOG_THM, (2)
   From (1),
        b ** (n * y) <= x ** n /\                  by EXP_EXP_LE_MONO, EXP_EXP_MULT
        x ** n < b ** (n * SUC y)                  by EXP_EXP_LT_MONO, EXP_EXP_MULT, 0 < n
   Cross combine with (2),
        b ** (n * y) <= x ** n < b ** SUC z
    and b ** z <= x ** n < b ** (n * y)
    ==> n * y < SUC z /\ z < n * SUC y             by EXP_BASE_LT_MONO
     or    n * y <= z /\ z < n * SUC y
*)
val LOG_POWER = store_thm(
  "LOG_POWER",
  ``!b x n. 1 < b /\ 0 < x /\ 0 < n ==>
           n * LOG b x <= LOG b (x ** n) /\ LOG b (x ** n) < n * SUC (LOG b x)``,
  ntac 4 strip_tac >>
  `0 < x ** n` by rw[] >>
  qabbrev_tac `y = LOG b x` >>
  qabbrev_tac `z = LOG b (x ** n)` >>
  `b ** y <= x /\ x < b ** SUC y` by metis_tac[LOG_THM] >>
  `b ** z <= x ** n /\ x ** n < b ** SUC z` by metis_tac[LOG_THM] >>
  `b ** (y * n) <= x ** n` by rw[EXP_EXP_MULT] >>
  `x ** n < b ** ((SUC y) * n)` by rw[EXP_EXP_MULT] >>
  `b ** (y * n) < b ** SUC z` by decide_tac >>
  `b ** z < b ** (SUC y * n)` by decide_tac >>
  `y * n < SUC z` by metis_tac[EXP_BASE_LT_MONO] >>
  `z < SUC y * n` by metis_tac[EXP_BASE_LT_MONO] >>
  decide_tac);

(* Theorem: 1 < a /\ 0 < n /\ a <= b ==> LOG b n <= LOG a n *)
(* Proof:
   Let x = LOG a n, y = LOG b n. To show: y <= x.
   By contradiction, suppose x < y.
   Then SUC x <= y.
   Note a ** x <= n /\ n < a ** SUC x     by LOG_THM
    and b ** y <= n /\ n < b ** SUC y     by LOG_THM
    But a <= b
        a ** SUC x
     <= b ** SUC x         by EXP_EXP_LE_MONO, 0 < SUC x
     <= b ** y             by EXP_BASE_LEQ_MONO_IMP, SUC x <= y
   This leads to n < a ** SUC x <= b ** y <= n, a contradiction.
*)
val LOG_LE_REVERSE = store_thm(
  "LOG_LE_REVERSE",
  ``!a b n. 1 < a /\ 0 < n /\ a <= b ==> LOG b n <= LOG a n``,
  rpt strip_tac >>
  qabbrev_tac `x = LOG a n` >>
  qabbrev_tac `y = LOG b n` >>
  spose_not_then strip_assume_tac >>
  `1 < b /\ SUC x <= y` by decide_tac >>
  `a ** x <= n /\ n < a ** SUC x` by metis_tac[LOG_THM] >>
  `b ** y <= n /\ n < b ** SUC y` by metis_tac[LOG_THM] >>
  `a ** SUC x <= b ** SUC x` by rw[EXP_EXP_LE_MONO] >>
  `b ** SUC x <= b ** y` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  decide_tac);

(* Overload LOG base 2 *)
val _ = overload_on ("LOG2", ``\n. LOG 2 n``);

(* Theorem: LOG2 1 = 0 *)
(* Proof:
   LOG_1 |> SPEC ``2``;
   val it = |- 1 < 2 ==> LOG2 1 = 0: thm
*)
val LOG2_1 = store_thm(
  "LOG2_1[simp]",
  ``LOG2 1 = 0``,
  rw[LOG_1]);

(* Theorem: LOG2 2 = 1 *)
(* Proof:
   LOG_BASE |> SPEC ``2``;
   val it = |- 1 < 2 ==> LOG2 2 = 1: thm
*)
val LOG2_2 = store_thm(
  "LOG2_2[simp]",
  ``LOG2 2 = 1``,
  rw[LOG_BASE]);

(* Obtain a theorem *)
val LOG2_THM = save_thm("LOG2_THM",
    LOG_THM |> SPEC ``2`` |> SIMP_RULE (srw_ss())[]);
(* val LOG2_THM = |- !n. 0 < n ==> !p. (LOG2 n = p) <=> 2 ** p <= n /\ n < 2 ** SUC p: thm *)

(* Theorem: 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n) *)
(* Proof:
   LOG |> SPEC ``2``;
   val it = |- !n. 1 < 2 /\ 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n): thm
*)
val LOG2_PROPERTY = store_thm(
  "LOG2_PROPERTY",
  ``!n. 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n)``,
  rw[LOG]);

(* Obtain the same theorem *)
val LOG2_PROPERTY = save_thm("LOG2_PROPERTY",
    LOG |> SPEC ``2`` |> SIMP_RULE (srw_ss())[]);
(* val LOG2_PROPERTY = |- !n. 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n): thm *)

(* Theorem: 0 < n ==> 2 ** LOG2 n <= n) *)
(* Proof: by LOG2_PROPERTY *)
val TWO_EXP_LOG2_LE = store_thm(
  "TWO_EXP_LOG2_LE",
  ``!n. 0 < n ==> 2 ** LOG2 n <= n``,
  rw[LOG2_PROPERTY]);

(* Obtain a theorem *)
val LOG2_UNIQUE = save_thm("LOG2_UNIQUE",
    LOG_UNIQUE |> SPEC ``2`` |> SPEC ``n:num`` |> SPEC ``m:num`` |> GEN_ALL);
(* val LOG2_UNIQUE = |- !n m. 2 ** m <= n /\ n < 2 ** SUC m ==> LOG2 n = m: thm *)

(* Theorem: 0 < n ==> ((LOG2 n = 0) <=> (n = 1)) *)
(* Proof:
   LOG_EQ_0 |> SPEC ``2``;
   |- !b. 1 < 2 /\ 0 < b ==> (LOG2 b = 0 <=> b < 2)
*)
val LOG2_EQ_0 = store_thm(
  "LOG2_EQ_0",
  ``!n. 0 < n ==> ((LOG2 n = 0) <=> (n = 1))``,
  rw[LOG_EQ_0]);

(* Theorem: 0 < n ==> LOG2 n = 1 <=> (n = 2) \/ (n = 3) *)
(* Proof:
   If part: LOG2 n = 1 ==> n = 2 \/ n = 3
      Note  2 ** 1 <= n /\ n < 2 ** SUC 1  by LOG2_PROPERTY
        or       2 <= n /\ n < 4           by arithmetic
      Thus  n = 2 or n = 3.
   Only-if part: LOG2 2 = 1 /\ LOG2 3 = 1
      Note LOG2 2 = 1                      by LOG2_2
       and LOG2 3 = 1                      by LOG2_UNIQUE
     since 2 ** 1 <= 3 /\ 3 < 2 ** SUC 1 ==> (LOG2 3 = 1)
*)
val LOG2_EQ_1 = store_thm(
  "LOG2_EQ_1",
  ``!n. 0 < n ==> ((LOG2 n = 1) <=> ((n = 2) \/ (n = 3)))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    imp_res_tac LOG2_PROPERTY >>
    rfs[],
    rw[],
    irule LOG2_UNIQUE >>
    simp[]
  ]);

(* Obtain theorem *)
val LOG2_LE_MONO = save_thm("LOG2_LE_MONO",
    LOG_LE_MONO |> SPEC ``2`` |> SPEC ``n:num`` |> SPEC ``m:num``
                |> SIMP_RULE (srw_ss())[] |> GEN_ALL);
(* val LOG2_LE_MONO = |- !n m. 0 < n ==> n <= m ==> LOG2 n <= LOG2 m: thm *)

(* Theorem: 0 < n /\ n <= m ==> LOG2 n <= LOG2 m *)
(* Proof: by LOG_LE_MONO *)
val LOG2_LE = store_thm(
  "LOG2_LE",
  ``!n m. 0 < n /\ n <= m ==> LOG2 n <= LOG2 m``,
  rw[LOG_LE_MONO, DECIDE``1 < 2``]);

(* Note: next is not LOG2_LT_MONO! *)

(* Theorem: 0 < n /\ n < m ==> LOG2 n <= LOG2 m *)
(* Proof:
   Since n < m ==> n <= m   by LESS_IMP_LESS_OR_EQ
   This is true             by LOG_LE_MONO
*)
val LOG2_LT = store_thm(
  "LOG2_LT",
  ``!n m. 0 < n /\ n < m ==> LOG2 n <= LOG2 m``,
  rw[LOG_LE_MONO, LESS_IMP_LESS_OR_EQ, DECIDE``1 < 2``]);

(* Theorem: 0 < n ==> LOG2 n < n *)
(* Proof:
       LOG2 n
     < 2 ** (LOG2 n)     by X_LT_EXP_X, 1 < 2
    <= n                 by LOG2_PROPERTY, 0 < n
*)
val LOG2_LT_SELF = store_thm(
  "LOG2_LT_SELF",
  ``!n. 0 < n ==> LOG2 n < n``,
  rpt strip_tac >>
  `LOG2 n < 2 ** (LOG2 n)` by rw[X_LT_EXP_X] >>
  `2 ** LOG2 n <= n` by rw[LOG2_PROPERTY] >>
  decide_tac);

(* Theorem: 0 < n ==> LOG2 n <> n *)
(* Proof:
   Note n < LOG2 n     by LOG2_LT_SELF
   Thus n <> LOG2 n    by arithmetic
*)
val LOG2_NEQ_SELF = store_thm(
  "LOG2_NEQ_SELF",
  ``!n. 0 < n ==> LOG2 n <> n``,
  rpt strip_tac >>
  `LOG2 n < n` by rw[LOG2_LT_SELF] >>
  decide_tac);

(* Theorem: LOG2 n = n ==> n = 0 *)
(* Proof: by LOG2_NEQ_SELF *)
val LOG2_EQ_SELF = store_thm(
  "LOG2_EQ_SELF",
  ``!n. (LOG2 n = n) ==> (n = 0)``,
  metis_tac[LOG2_NEQ_SELF, DECIDE``~(0 < n) <=> (n = 0)``]);

(* Theorem: 1 < n ==> 0 < LOG2 n *)
(* Proof:
       1 < n
   ==> 2 <= n
   ==> LOG2 2 <= LOG2 n     by LOG2_LE
   ==>      1 <= LOG2 n     by LOG_BASE, LOG2 2 = 1
    or      0 < LOG2 n
*)
val LOG2_POS = store_thm(
  "LOG2_POS[simp]",
  ``!n. 1 < n ==> 0 < LOG2 n``,
  rpt strip_tac >>
  `LOG2 2 = 1` by rw[LOG_BASE, DECIDE``1 < 2``] >>
  `2 <= n` by decide_tac >>
  `LOG2 2 <= LOG2 n` by rw[LOG2_LE] >>
  decide_tac);

(* Theorem: 1 < n ==> 1 < 2 * LOG2 n *)
(* Proof:
       1 < n
   ==> 2 <= n
   ==> LOG2 2 <= LOG2 n        by LOG2_LE
   ==>      1 <= LOG2 n        by LOG_BASE, LOG2 2 = 1
   ==>  2 * 1 <= 2 * LOG2 n    by LE_MULT_LCANCEL
    or      1 < 2 * LOG2 n
*)
val LOG2_TWICE_LT = store_thm(
  "LOG2_TWICE_LT",
  ``!n. 1 < n ==> 1 < 2 * (LOG2 n)``,
  rpt strip_tac >>
  `LOG2 2 = 1` by rw[LOG_BASE, DECIDE``1 < 2``] >>
  `2 <= n` by decide_tac >>
  `LOG2 2 <= LOG2 n` by rw[LOG2_LE] >>
  `1 <= LOG2 n` by decide_tac >>
  `2 <= 2 * LOG2 n` by rw_tac arith_ss[LE_MULT_LCANCEL, DECIDE``0 < 2``] >>
  decide_tac);

(* Theorem: 1 < n ==> 4 <= (2 * (LOG2 n)) ** 2 *)
(* Proof:
       1 < n
   ==> 2 <= n
   ==> LOG2 2 <= LOG2 n              by LOG2_LE
   ==>      1 <= LOG2 n              by LOG2_2, or LOG_BASE, LOG2 2 = 1
   ==>  2 * 1 <= 2 * LOG2 n          by LE_MULT_LCANCEL
   ==> 2 ** 2 <= (2 * LOG2 n) ** 2   by EXP_EXP_LE_MONO
   ==>      4 <= (2 * LOG2 n) ** 2
*)
val LOG2_TWICE_SQ = store_thm(
  "LOG2_TWICE_SQ",
  ``!n. 1 < n ==> 4 <= (2 * (LOG2 n)) ** 2``,
  rpt strip_tac >>
  `LOG2 2 = 1` by rw[] >>
  `2 <= n` by decide_tac >>
  `LOG2 2 <= LOG2 n` by rw[LOG2_LE] >>
  `1 <= LOG2 n` by decide_tac >>
  `2 <= 2 * LOG2 n` by rw_tac arith_ss[LE_MULT_LCANCEL, DECIDE``0 < 2``] >>
  `2 ** 2 <= (2 * LOG2 n) ** 2` by rw[EXP_EXP_LE_MONO, DECIDE``0 < 2``] >>
  `2 ** 2 = 4` by rw_tac arith_ss[] >>
  decide_tac);

(* Theorem: 0 < n ==> 4 <= (2 * SUC (LOG2 n)) ** 2 *)
(* Proof:
       0 < n
   ==> 1 <= n
   ==> LOG2 1 <= LOG2 n                    by LOG2_LE
   ==>      0 <= LOG2 n                    by LOG2_1, or LOG_BASE, LOG2 1 = 0
   ==>      1 <= SUC (LOG2 n)              by LESS_EQ_MONO
   ==>  2 * 1 <= 2 * SUC (LOG2 n)          by LE_MULT_LCANCEL
   ==> 2 ** 2 <= (2 * SUC (LOG2 n)) ** 2   by EXP_EXP_LE_MONO
   ==>      4 <= (2 * SUC (LOG2 n)) ** 2
*)
val LOG2_SUC_TWICE_SQ = store_thm(
  "LOG2_SUC_TWICE_SQ",
  ``!n. 0 < n ==> 4 <= (2 * SUC (LOG2 n)) ** 2``,
  rpt strip_tac >>
  `LOG2 1 = 0` by rw[] >>
  `1 <= n` by decide_tac >>
  `LOG2 1 <= LOG2 n` by rw[LOG2_LE] >>
  `1 <= SUC (LOG2 n)` by decide_tac >>
  `2 <= 2 * SUC (LOG2 n)` by rw_tac arith_ss[LE_MULT_LCANCEL, DECIDE``0 < 2``] >>
  `2 ** 2 <= (2 * SUC (LOG2 n)) ** 2` by rw[EXP_EXP_LE_MONO, DECIDE``0 < 2``] >>
  `2 ** 2 = 4` by rw_tac arith_ss[] >>
  decide_tac);

(* Theorem: 1 < n ==> 1 < (SUC (LOG2 n)) ** 2 *)
(* Proof:
   Note 0 < LOG2 n                 by LOG2_POS, 1 < n
     so 1 < SUC (LOG2 n)           by arithmetic
    ==> 1 < (SUC (LOG2 n)) ** 2    by ONE_LT_EXP, 0 < 2
*)
val LOG2_SUC_SQ = store_thm(
  "LOG2_SUC_SQ",
  ``!n. 1 < n ==> 1 < (SUC (LOG2 n)) ** 2``,
  rpt strip_tac >>
  `0 < LOG2 n` by rw[] >>
  `1 < SUC (LOG2 n)` by decide_tac >>
  rw[ONE_LT_EXP]);

(* Theorem: 1 < m ==> 0 < SUC (LOG2 n) * (m ** 2 DIV 2) *)
(* Proof:
   Since 1 < m ==> 1 < m ** 2 DIV 2             by ONE_LT_HALF_SQ
   Hence           0 < m ** 2 DIV 2
     and           0 < 0 < SUC (LOG2 n)         by prim_recTheory.LESS_0
   Therefore 0 < SUC (LOG2 n) * (m ** 2 DIV 2)  by ZERO_LESS_MULT
*)
val LOG2_SUC_TIMES_SQ_DIV_2_POS = store_thm(
  "LOG2_SUC_TIMES_SQ_DIV_2_POS",
  ``!n m. 1 < m ==> 0 < SUC (LOG2 n) * (m ** 2 DIV 2)``,
  rpt strip_tac >>
  `1 < m ** 2 DIV 2` by rw[ONE_LT_HALF_SQ] >>
  `0 < m ** 2 DIV 2 /\ 0 < SUC (LOG2 n)` by decide_tac >>
  rw[ZERO_LESS_MULT]);

(* Theorem: LOG2 (2 ** n) = n *)
(* Proof: by LOG_EXACT_EXP *)
val LOG2_2_EXP = store_thm(
  "LOG2_2_EXP",
  ``!n. LOG2 (2 ** n) = n``,
  rw[LOG_EXACT_EXP]);

(* Theorem: (2 ** (LOG2 n) = n) <=> ?k. n = 2 ** k *)
(* Proof:
   If part: 2 ** LOG2 n = n ==> ?k. n = 2 ** k
      True by taking k = LOG2 n.
   Only-if part: 2 ** LOG2 (2 ** k) = 2 ** k
      Note LOG2 n = k               by LOG_EXACT_EXP, 1 < 2
        or n = 2 ** k = 2 ** LOG2 n.
*)
val LOG2_EXACT_EXP = store_thm(
  "LOG2_EXACT_EXP",
  ``!n. (2 ** (LOG2 n) = n) <=> ?k. n = 2 ** k``,
  metis_tac[LOG2_2_EXP]);

(* Theorem: 0 < n ==> LOG2 (n * 2 ** m) = (LOG2 n) + m *)
(* Proof:
   LOG_EXP |> SPEC ``m:num`` |> SPEC ``2`` |> SPEC ``n:num``;
   val it = |- 1 < 2 /\ 0 < n ==> LOG2 (2 ** m * n) = m + LOG2 n: thm
*)
val LOG2_MULT_EXP = store_thm(
  "LOG2_MULT_EXP",
  ``!n m. 0 < n ==> (LOG2 (n * 2 ** m) = (LOG2 n) + m)``,
  rw[GSYM LOG_EXP]);

(* Theorem: 0 < n ==> (LOG2 (2 * n) = 1 + LOG2 n) *)
(* Proof:
   LOG_MULT |> SPEC ``2`` |> SPEC ``n:num``;
   val it = |- 1 < 2 /\ 0 < n ==> LOG2 (TWICE n) = SUC (LOG2 n): thm
*)
val LOG2_TWICE = store_thm(
  "LOG2_TWICE",
  ``!n. 0 < n ==> (LOG2 (2 * n) = 1 + LOG2 n)``,
  rw[LOG_MULT]);

(* Theorem: 1 < n ==> LOG2 (HALF n) = (LOG2 n) - 1 *)
(* Proof:
   Note: > LOG_DIV |> SPEC ``2`` |> SPEC ``n:num``;
   val it = |- 1 < 2 /\ 2 <= n ==> LOG2 n = 1 + LOG2 (HALF n): thm
   Hence the result.
*)
val LOG2_HALF = store_thm(
  "LOG2_HALF",
  ``!n. 1 < n ==> (LOG2 (HALF n) = (LOG2 n) - 1)``,
  rpt strip_tac >>
  `LOG2 n = 1 + LOG2 (HALF n)` by rw[LOG_DIV] >>
  decide_tac);

(* Theorem: 1 < n ==> (LOG2 n = 1 + LOG2 (HALF n)) *)
(* Proof: by LOG_DIV:
> LOG_DIV |> SPEC ``2``;
val it = |- !x. 1 < 2 /\ 2 <= x ==> (LOG2 x = 1 + LOG2 (HALF x)): thm
*)
val LOG2_BY_HALF = store_thm(
  "LOG2_BY_HALF",
  ``!n. 1 < n ==> (LOG2 n = 1 + LOG2 (HALF n))``,
  rw[LOG_DIV]);

(* Theorem: 2 ** m < n ==> LOG2 (n DIV 2 ** m) = (LOG2 n) - m *)
(* Proof:
   By induction on m.
   Base: !n. 2 ** 0 < n ==> LOG2 (n DIV 2 ** 0) = LOG2 n - 0
         LOG2 (n DIV 2 ** 0)
       = LOG2 (n DIV 1)                by EXP_0
       = LOG2 n                        by DIV_1
       = LOG2 n - 0                    by SUB_0
   Step: !n. 2 ** m < n ==> LOG2 (n DIV 2 ** m) = LOG2 n - m ==>
         !n. 2 ** SUC m < n ==> LOG2 (n DIV 2 ** SUC m) = LOG2 n - SUC m
       Note 2 ** SUC m = 2 * 2 ** m       by EXP, [1]
       Thus HALF (2 * 2 ** m) <= HALF n   by DIV_LE_MONOTONE
         or            2 ** m <= HALF n   by HALF_TWICE
       If 2 ** m < HALF n,
            LOG2 (n DIV 2 ** SUC m)
          = LOG2 (n DIV (2 * 2 ** m))     by [1]
          = LOG2 ((HALF n) DIV 2 ** m)    by DIV_DIV_DIV_MULT
          = LOG2 (HALF n) - m             by induction hypothesis, 2 ** m < HALF n
          = (LOG2 n - 1) - m              by LOG2_HALF, 1 < n
          = LOG2 n - (1 + m)              by arithmetic
          = LOG2 n - SUC m                by ADD1
       Otherwise 2 ** m = HALF n,
            LOG2 (n DIV 2 ** SUC m)
          = LOG2 (n DIV (2 * 2 ** m))     by [1]
          = LOG2 ((HALF n) DIV 2 ** m)    by DIV_DIV_DIV_MULT
          = LOG2 ((HALF n) DIV (HALF n))  by 2 ** m = HALF n
          = LOG2 1                        by DIVMOD_ID, 0 < HALF n
          = 0                             by LOG2_1
            LOG2 n
          = 1 + LOG2 (HALF n)             by LOG_DIV
          = 1 + LOG2 (2 ** m)             by 2 ** m = HALF n
          = 1 + m                         by LOG2_2_EXP
          = SUC m                         by SUC_ONE_ADD
       Thus RHS = LOG2 n - SUC m = 0 = LHS.
*)

Theorem LOG2_DIV_EXP:
  !n m. 2 ** m < n ==> LOG2 (n DIV 2 ** m) = LOG2 n - m
Proof
  Induct_on ‘m’ >- rw[] >>
  rpt strip_tac >>
  ‘1 < 2 ** SUC m’ by rw[ONE_LT_EXP] >>
  ‘1 < n’ by decide_tac >>
  fs[EXP] >>
  ‘2 ** m <= HALF n’
    by metis_tac[DIV_LE_MONOTONE, HALF_TWICE, LESS_IMP_LESS_OR_EQ,
                 DECIDE “0 < 2”] >>
  ‘LOG2 (n DIV (TWICE (2 ** m))) = LOG2 ((HALF n) DIV 2 ** m)’
    by rw[DIV_DIV_DIV_MULT] >>
  fs[LESS_OR_EQ] >- rw[LOG2_HALF] >>
  ‘LOG2 n = 1 + LOG2 (HALF n)’  by rw[LOG_DIV] >>
  ‘_ = 1 + m’ by metis_tac[LOG2_2_EXP] >>
  ‘_ = SUC m’ by rw[] >>
  ‘0 < HALF n’ suffices_by rw[] >>
  metis_tac[DECIDE “0 < 2”, ZERO_LT_EXP]
QED

(* ------------------------------------------------------------------------- *)
(* LOG2 Computation                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define halves n = count of HALFs of n to 0, recursively. *)
val halves_def = Define`
    halves n = if n = 0 then 0 else SUC (halves (HALF n))
`;

(* Theorem: halves n = if n = 0 then 0 else 1 + (halves (HALF n)) *)
(* Proof: by halves_def, ADD1 *)
val halves_alt = store_thm(
  "halves_alt",
  ``!n. halves n = if n = 0 then 0 else 1 + (halves (HALF n))``,
  rw[Once halves_def, ADD1]);

(* Extract theorems from definition *)
val halves_0 = save_thm("halves_0[simp]", halves_def |> SPEC ``0`` |> SIMP_RULE arith_ss[]);
(* val halves_0 = |- halves 0 = 0: thm *)
val halves_1 = save_thm("halves_1[simp]", halves_def |> SPEC ``1`` |> SIMP_RULE arith_ss[]);
(* val halves_1 = |- halves 1 = 1: thm *)
val halves_2 = save_thm("halves_2[simp]", halves_def |> SPEC ``2`` |> SIMP_RULE arith_ss[halves_1]);
(* val halves_2 = |- halves 2 = 2: thm *)

(* Theorem: 0 < n ==> 0 < halves n *)
(* Proof: by halves_def *)
val halves_pos = store_thm(
  "halves_pos[simp]",
  ``!n. 0 < n ==> 0 < halves n``,
  rw[Once halves_def]);

(* Theorem: 0 < n ==> (halves n = 1 + LOG2 n) *)
(* Proof:
   By complete induction on n.
    Assume: !m. m < n ==> 0 < m ==> (halves m = 1 + LOG2 m)
   To show: 0 < n ==> (halves n = 1 + LOG2 n)
   Note HALF n < n            by HALF_LESS, 0 < n
   Need 0 < HALF n to apply induction hypothesis.
   If HALF n = 0,
      Then n = 1              by HALF_EQ_0
           halves 1
         = SUC (halves 0)     by halves_def
         = 1                  by halves_def
         = 1 + LOG2 1         by LOG2_1
   If HALF n <> 0,
      Then n <> 1                  by HALF_EQ_0
        so 1 < n                   by n <> 0, n <> 1.
           halves n
         = SUC (halves (HALF n))   by halves_def
         = SUC (1 + LOG2 (HALF n)) by induction hypothesis
         = SUC (LOG2 n)            by LOG2_BY_HALF
         = 1 + LOG2 n              by ADD1
*)
val halves_by_LOG2 = store_thm(
  "halves_by_LOG2",
  ``!n. 0 < n ==> (halves n = 1 + LOG2 n)``,
  completeInduct_on `n` >>
  strip_tac >>
  rw[Once halves_def] >>
  Cases_on `n = 1` >-
  simp[Once halves_def] >>
  `HALF n < n` by rw[HALF_LESS] >>
  `HALF n <> 0` by fs[HALF_EQ_0] >>
  simp[LOG2_BY_HALF]);

(* Theorem: LOG2 n = if n = 0 then LOG2 0 else (halves n - 1) *)
(* Proof:
   If 0 < n,
      Note 0 < halves n            by halves_pos
       and halves n = 1 + LOG2 n   by halves_by_LOG2
        or LOG2 n = halves - 1.
   If n = 0, make it an infinite loop.
*)
val LOG2_compute = store_thm(
  "LOG2_compute[compute]",
  ``!n. LOG2 n = if n = 0 then LOG2 0 else (halves n - 1)``,
  rpt strip_tac >>
  (Cases_on `n = 0` >> simp[]) >>
  `0 < halves n` by rw[] >>
  `halves n = 1 + LOG2 n` by rw[halves_by_LOG2] >>
  decide_tac);

(* Put this to computeLib *)
(* val _ = computeLib.add_persistent_funs ["LOG2_compute"]; *)

(*
EVAL ``LOG2 16``; --> 4
EVAL ``LOG2 17``; --> 4
EVAL ``LOG2 32``; --> 5
EVAL ``LOG2 1024``; --> 10
EVAL ``LOG2 1023``; --> 9
*)

(* Michael's method *)
(*
Define `count_divs n = if 2 <= n then 1 + count_divs (n DIV 2) else 0`;

g `0 < n ==> (LOG2 n = count_divs n)`;
e (completeInduct_on `n`);
e strip_tac;
e (ONCE_REWRITE_TAC [theorm "count_divs_def"]);
e (Cases_on `2 <= n`);
e (mp_tac (Q.SPECL [`2`, `n`] LOG_DIV));
e (simp[]);
(* prove on-the-fly *)
e (`0 < n DIV 2` suffices_by simp[]);
(* DB.match [] ``x < k DIV n``; *)
e (simp[arithmeticTheory.X_LT_DIV]);
e (`n = 1` by simp[]);
LOG_1;
e (simp[it]);
val foo = top_thm();

g `!n. LOG2 n = if 0 < n then count_divs n else LOG2 n`;

e (rw[]);
e (simp[foo]);
e (lfs[]); ???

val bar = top_thm();
var bar = save_thm("bar", bar);
computeLib.add_persistent_funs ["bar"];
EVAL ``LOG2 16``;
EVAL ``LOG2 17``;
EVAL ``LOG2 32``;
EVAL ``LOG2 1024``;
EVAL ``LOG2 1023``;
EVAL ``LOG2 0``; -- loops!

So for n = 97,
EVAL ``LOG2 97``; --> 6
EVAL ``4 * LOG2 97 * LOG2 97``; --> 4 * 6 * 6 = 4 * 36 = 144

Need ord_r (97) > 144, r < 97, not possible ???

val count_divs_def = Define `count_divs n = if 1 < n then 1 + count_divs (n DIV 2) else 0`;

val LOG2_by_count_divs = store_thm(
  "LOG2_by_count_divs",
  ``!n. 0 < n ==> (LOG2 n = count_divs n)``,
  completeInduct_on `n` >>
  strip_tac >>
  ONCE_REWRITE_TAC[count_divs_def] >>
  rw[] >| [
    mp_tac (Q.SPECL [`2`, `n`] LOG_DIV) >>
    `2 <= n` by decide_tac >>
    `0 < n DIV 2` by rw[X_LT_DIV] >>
    simp[],
    `n = 1` by decide_tac >>
    simp[LOG_1]
  ]);

val LOG2_compute = store_thm(
  "LOG2_compute[compute]",
  ``!n. LOG2 n = if 0 < n then count_divs n else LOG2 n``,
  rw_tac std_ss[LOG2_by_count_divs]);

*)

(* Theorem: m <= n ==> halves m <= halves n *)
(* Proof:
   If m = 0,
      Then halves m = 0            by halves_0
      Thus halves m <= halves n    by 0 <= halves n
   If m <> 0,
      Then 0 < m and 0 < n   by m <= n
        so halves m = 1 + LOG2 m   by halves_by_LOG2
       and halves n = 1 + LOG2 n   by halves_by_LOG2
       and LOG2 m <= LOG2 n        by LOG2_LE
       ==> halves m <= halves n    by arithmetic
*)
val halves_le = store_thm(
  "halves_le",
  ``!m n. m <= n ==> halves m <= halves n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[] >>
  `0 < m /\ 0 < n` by decide_tac >>
  `LOG2 m <= LOG2 n` by rw[LOG2_LE] >>
  rw[halves_by_LOG2]);

(* Theorem: (halves n = 0) <=> (n = 0) *)
(* Proof: by halves_pos, halves_0 *)
val halves_eq_0 = store_thm(
  "halves_eq_0",
  ``!n. (halves n = 0) <=> (n = 0)``,
  metis_tac[halves_pos, halves_0, NOT_ZERO_LT_ZERO]);

(* Theorem: (halves n = 1) <=> (n = 1) *)
(* Proof:
   If part: halves n = 1 ==> n = 1
      By contradiction, assume n <> 1.
      Note n <> 0                   by halves_eq_0
        so 2 <= n                   by n <> 0, n <> 1
        or halves 2 <= halves n     by halves_le
       But halves 2 = 2             by halves_2
      This gives 2 <= 1, a contradiction.
   Only-if part: halves 1 = 1, true by halves_1
*)
val halves_eq_1 = store_thm(
  "halves_eq_1",
  ``!n. (halves n = 1) <=> (n = 1)``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `n <> 0` by metis_tac[halves_eq_0, DECIDE``1 <> 0``] >>
  `2 <= n` by decide_tac >>
  `halves 2 <= halves n` by rw[halves_le] >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* Perfect Power                                                             *)
(* ------------------------------------------------------------------------- *)

(* Define a PerfectPower number *)
val perfect_power_def = Define`
  perfect_power (n:num) (m:num) <=> ?e. (n = m ** e)
`;

(* Overload perfect_power *)
val _ = overload_on("power_of", ``perfect_power``);
val _ = set_fixity "power_of" (Infix(NONASSOC, 450)); (* same as relation *)
(* from pretty-printing, a good idea. *)

(* Theorem: perfect_power n n *)
(* Proof:
   True since n = n ** 1   by EXP_1
*)
val perfect_power_self = store_thm(
  "perfect_power_self",
  ``!n. perfect_power n n``,
  metis_tac[perfect_power_def, EXP_1]);

(* Theorem: perfect_power 0 m <=> (m = 0) *)
(* Proof: by perfect_power_def, EXP_EQ_0 *)
val perfect_power_0_m = store_thm(
  "perfect_power_0_m",
  ``!m. perfect_power 0 m <=> (m = 0)``,
  rw[perfect_power_def, EQ_IMP_THM]);

(* Theorem: perfect_power 1 m *)
(* Proof: by perfect_power_def, take e = 0 *)
val perfect_power_1_m = store_thm(
  "perfect_power_1_m",
  ``!m. perfect_power 1 m``,
  rw[perfect_power_def] >>
  metis_tac[]);

(* Theorem: perfect_power n 0 <=> ((n = 0) \/ (n = 1)) *)
(* Proof: by perfect_power_def, ZERO_EXP. *)
val perfect_power_n_0 = store_thm(
  "perfect_power_n_0",
  ``!n. perfect_power n 0 <=> ((n = 0) \/ (n = 1))``,
  rw[perfect_power_def] >>
  metis_tac[ZERO_EXP]);

(* Theorem: perfect_power n 1 <=> (n = 1) *)
(* Proof: by perfect_power_def, EXP_1 *)
val perfect_power_n_1 = store_thm(
  "perfect_power_n_1",
  ``!n. perfect_power n 1 <=> (n = 1)``,
  rw[perfect_power_def]);

(* Theorem: 0 < m /\ 1 < n /\ (n MOD m = 0) ==>
            (perfect_power n m) <=> (perfect_power (n DIV m) m) *)
(* Proof:
   If part: perfect_power n m ==> perfect_power (n DIV m) m
      Note ?e. n = m ** e              by perfect_power_def
       and e <> 0                      by EXP_0, n <> 1
        so ?k. e = SUC k               by num_CASES
        or n = m ** SUC k
       ==> n DIV m = m ** k            by EXP_SUC_DIV
      Thus perfect_power (n DIV m) m   by perfect_power_def
   Only-if part: perfect_power (n DIV m) m ==> perfect_power n m
      Note ?e. n DIV m = m ** e        by perfect_power_def
       Now m divides n                 by DIVIDES_MOD_0, n MOD m = 0, 0 < m
       ==> n = m * (n DIV m)           by DIVIDES_EQN_COMM, 0 < m
             = m * m ** e              by above
             = m ** (SUC e)            by EXP
      Thus perfect_power n m           by perfect_power_def
*)
val perfect_power_mod_eq_0 = store_thm(
  "perfect_power_mod_eq_0",
  ``!n m. 0 < m /\ 1 < n /\ (n MOD m = 0) ==>
     ((perfect_power n m) <=> (perfect_power (n DIV m) m))``,
  rw[perfect_power_def] >>
  rw[EQ_IMP_THM] >| [
    `m ** e <> 1` by decide_tac >>
    `e <> 0` by metis_tac[EXP_0] >>
    `?k. e = SUC k` by metis_tac[num_CASES] >>
    qexists_tac `k` >>
    rw[EXP_SUC_DIV],
    `m divides n` by rw[DIVIDES_MOD_0] >>
    `n = m * (n DIV m)` by rw[GSYM DIVIDES_EQN_COMM] >>
    metis_tac[EXP]
  ]);

(* Theorem: 0 < m /\ 1 < n /\ (n MOD m <> 0) ==> ~(perfect_power n m) *)
(* Proof:
   By contradiction, assume perfect_power n m.
   Then ?e. n = m ** e      by perfect_power_def
    Now e <> 0              by EXP_0, n <> 1
     so ?k. e = SUC k       by num_CASES
        n = m ** SUC k
          = m * (m ** k)    by EXP
          = (m ** k) * m    by MULT_COMM
   Thus m divides n         by divides_def
    ==> n MOD m = 0         by DIVIDES_MOD_0
   This contradicts n MOD m <> 0.
*)
val perfect_power_mod_ne_0 = store_thm(
  "perfect_power_mod_ne_0",
  ``!n m. 0 < m /\ 1 < n /\ (n MOD m <> 0) ==> ~(perfect_power n m)``,
  rpt strip_tac >>
  fs[perfect_power_def] >>
  `n <> 1` by decide_tac >>
  `e <> 0` by metis_tac[EXP_0] >>
  `?k. e = SUC k` by metis_tac[num_CASES] >>
  `n = m * m ** k` by fs[EXP] >>
  `m divides n` by metis_tac[divides_def, MULT_COMM] >>
  metis_tac[DIVIDES_MOD_0]);

(* Theorem: perfect_power n m =
         if n = 0 then (m = 0)
         else if n = 1 then T
         else if m = 0 then (n <= 1)
         else if m = 1 then (n = 1)
         else if n MOD m = 0 then perfect_power (n DIV m) m else F *)
(* Proof:
   If n = 0, to show:
      perfect_power 0 m <=> (m = 0), true   by perfect_power_0_m
   If n = 1, to show:
      perfect_power 1 m = T, true           by perfect_power_1_m
   If m = 0, to show:
      perfect_power n 0 <=> (n <= 1), true  by perfect_power_n_0
   If m = 1, to show:
      perfect_power n 1 <=> (n = 1), true   by perfect_power_n_1
   Otherwise,
      If n MOD m = 0, to show:
      perfect_power (n DIV m) m <=> perfect_power n m, true
                                            by perfect_power_mod_eq_0
      If n MOD m <> 0, to show:
      ~perfect_power n m, true              by perfect_power_mod_ne_0
*)
val perfect_power_test = store_thm(
  "perfect_power_test",
  ``!n m. perfect_power n m =
         if n = 0 then (m = 0)
         else if n = 1 then T
         else if m = 0 then (n <= 1)
         else if m = 1 then (n = 1)
         else if n MOD m = 0 then perfect_power (n DIV m) m else F``,
  rpt strip_tac >>
  (Cases_on `n = 0` >> simp[perfect_power_0_m]) >>
  (Cases_on `n = 1` >> simp[perfect_power_1_m]) >>
  `1 < n` by decide_tac >>
  (Cases_on `m = 0` >> simp[perfect_power_n_0]) >>
  `0 < m` by decide_tac >>
  (Cases_on `m = 1` >> simp[perfect_power_n_1]) >>
  (Cases_on `n MOD m = 0` >> simp[]) >-
  rw[perfect_power_mod_eq_0] >>
  rw[perfect_power_mod_ne_0]);

(* Theorem: 1 < m /\ perfect_power n m /\ perfect_power (SUC n) m ==> (m = 2) /\ (n = 1) *)
(* Proof:
   Note ?x. n = m ** x                by perfect_power_def
    and ?y. SUC n = m ** y            by perfect_power_def
   Since n < SUC n                    by LESS_SUC
    ==>  x < y                        by EXP_BASE_LT_MONO
   Let d = y - x.
   Then 0 < d /\ (y = x + d).
   Let v = m ** d
   Note 1 < v                         by ONE_LT_EXP, 1 < m
    and m ** y = n * v                by EXP_ADD
   Let z = v - 1.
   Then 0 < z /\ (v = z + 1).
    and SUC n = n * v
              = n * (z + 1)
              = n * z + n * 1         by LEFT_ADD_DISTRIB
              = n * z + n
    ==> n * z = 1                     by ADD1
    ==> n = 1 /\ z = 1                by MULT_EQ_1
     so v = 2                         by v = z + 1

   To show: m = 2.
   By contradiction, suppose m <> 2.
   Then      2 < m                    by 1 < m, m <> 2
    ==> 2 ** y < m ** y               by EXP_EXP_LT_MONO
               = n * v = 2 = 2 ** 1   by EXP_1
    ==>      y < 1                    by EXP_BASE_LT_MONO
   Thus y = 0, but y <> 0 by x < y,
   leading to a contradiction.
*)

Theorem perfect_power_suc:
  !m n. 1 < m /\ perfect_power n m /\ perfect_power (SUC n) m ==>
        m = 2 /\ n = 1
Proof
  ntac 3 strip_tac >>
  `?x. n = m ** x` by fs[perfect_power_def] >>
  `?y. SUC n = m ** y` by fs[GSYM perfect_power_def] >>
  `n < SUC n` by decide_tac >>
  `x < y` by metis_tac[EXP_BASE_LT_MONO] >>
  qabbrev_tac `d = y - x` >>
  `0 < d /\ (y = x + d)` by fs[Abbr`d`] >>
  qabbrev_tac `v = m ** d` >>
  `m ** y = n * v` by fs[EXP_ADD, Abbr`v`] >>
  `1 < v` by rw[ONE_LT_EXP, Abbr`v`] >>
  qabbrev_tac `z = v - 1` >>
  `0 < z /\ (v = z + 1)` by fs[Abbr`z`] >>
  `n * v = n * z + n * 1` by rw[] >>
  `n * z = 1` by decide_tac >>
  `n = 1 /\ z = 1` by metis_tac[MULT_EQ_1] >>
  `v = 2` by decide_tac >>
  simp[] >>
  spose_not_then strip_assume_tac >>
  `2 < m` by decide_tac >>
  `2 ** y < m ** y` by simp[EXP_EXP_LT_MONO] >>
  `m ** y = 2` by decide_tac >>
  `2 ** y < 2 ** 1` by metis_tac[EXP_1] >>
  `y < 1` by fs[EXP_BASE_LT_MONO] >>
  decide_tac
QED

(* Theorem: 1 < m /\ 1 < n /\ perfect_power n m ==> ~perfect_power (SUC n) m *)
(* Proof:
   By contradiction, suppose perfect_power (SUC n) m.
   Then n = 1        by perfect_power_suc
   This contradicts 1 < n.
*)
val perfect_power_not_suc = store_thm(
  "perfect_power_not_suc",
  ``!m n. 1 < m /\ 1 < n /\ perfect_power n m ==> ~perfect_power (SUC n) m``,
  spose_not_then strip_assume_tac >>
  `n = 1` by metis_tac[perfect_power_suc] >>
  decide_tac);

(* Theorem: 1 < b /\ 0 < n ==>
           (LOG b (SUC n) = LOG b n + if perfect_power (SUC n) b then 1 else 0) *)
(* Proof:
   Let x = LOG b n, y = LOG b (SUC n).  x <= y
   Note SUC n <= b ** SUC x /\ b ** SUC x <= b * n            by LOG_TEST
    and SUC (SUC n) <= b ** SUC y /\ b ** SUC y <= b * SUC n  by LOG_TEST, 0 < SUC n

   If SUC n = b ** SUC x,
      Then perfect_power (SUC n) b       by perfect_power_def
       and y = LOG b (SUC n)
             = LOG b (b ** SUC x)
             = SUC x                     by LOG_EXACT_EXP
             = x + 1                     by ADD1
      hence true.
   Otherwise, SUC n < b ** SUC x,
      Then SUC (SUC n) <= b ** SUC x     by SUC n < b ** SUC x
       and b * n < b * SUC n             by LT_MULT_LCANCEL, n < SUC n
      Thus b ** SUC x <= b * n < b * SUC n
        or y = x                         by LOG_TEST
      Claim: ~perfect_power (SUC n) b
      Proof: By contradiction, suppose perfect_power (SUC n) b.
             Then ?e. SUC n = b ** e.
             Thus y = LOG b (SUC n)
                    = LOG b (b ** e)     by LOG_EXACT_EXP
                    = e
              ==> b * n < b * SUC n
                        = b * b ** e     by SUC n = b ** e
                        = b ** SUC e     by EXP
                        = b ** SUC x     by e = y = x
              This contradicts b ** SUC x <= b * n
      With ~perfect_power (SUC n) b, hence true.
*)

Theorem LOG_SUC:
  !b n. 1 < b /\ 0 < n ==>
    (LOG b (SUC n) = LOG b n + if perfect_power (SUC n) b then 1 else 0)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘x = LOG b n’ >>
  qabbrev_tac ‘y = LOG b (SUC n)’ >>
  ‘0 < SUC n’ by decide_tac >>
  ‘SUC n <= b ** SUC x /\ b ** SUC x <= b * n’ by metis_tac[LOG_TEST] >>
  ‘SUC (SUC n) <= b ** SUC y /\ b ** SUC y <= b * SUC n’
    by metis_tac[LOG_TEST] >>
  ‘(SUC n = b ** SUC x) \/ (SUC n < b ** SUC x)’ by decide_tac >| [
    ‘perfect_power (SUC n) b’ by metis_tac[perfect_power_def] >>
    ‘y = SUC x’ by rw[LOG_EXACT_EXP, Abbr‘y’] >>
    simp[],
    ‘SUC (SUC n) <= b ** SUC x’ by decide_tac >>
    ‘b * n < b * SUC n’ by rw[] >>
    ‘b ** SUC x <= b * SUC n’ by decide_tac >>
    ‘y = x’ by metis_tac[LOG_TEST] >>
    ‘~perfect_power (SUC n) b’
      by (spose_not_then strip_assume_tac >>
          `?e. SUC n = b ** e` by fs[perfect_power_def] >>
          `y = e` by (simp[Abbr`y`] >> fs[] >> rfs[LOG_EXACT_EXP]) >>
          `b * n < b ** SUC x` by metis_tac[EXP] >>
          decide_tac) >>
    simp[]
  ]
QED

(*
LOG_SUC;
|- !b n. 1 < b /\ 0 < n ==> LOG b (SUC n) = LOG b n + if perfect_power (SUC n) b then 1 else 0
Let v = LOG b n.

   v       v+1.      v+2.     v+3.
   -----------------------------------------------
   b       b ** 2        b ** 3             b ** 4

> EVAL ``MAP (LOG 2) [1 .. 20]``;
val it = |- MAP (LOG 2) [1 .. 20] =
      [0; 1; 1; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3; 4; 4; 4; 4; 4]: thm
       1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20
*)

(* Theorem: 0 < n ==> !m. perfect_power n m <=> ?k. k <= LOG2 n /\ (n = m ** k) *)
(* Proof:
   If part: perfect_power n m ==> ?k. k <= LOG2 n /\ (n = m ** k)
      Given perfect_power n m, ?e. (n = m ** e)    by perfect_power_def
      If n = 1,
         Then LOG2 1 = 0                           by LOG2_1
         Take k = 0, then 1 = m ** 0               by EXP_0
      If n <> 1, so e <> 0                         by EXP
                and m <> 1                         by EXP_1
       also n <> 0, so m <> 0                      by ZERO_EXP
      Therefore 2 <= m
            ==> 2 ** e <= m ** e                   by EXP_BASE_LE_MONO, 1 < 2
            But n < 2 ** (SUC (LOG2 n))            by LOG2_PROPERTY, 0 < n
        or 2 ** e < 2 ** (SUC (LOG2 n))
        hence   e < SUC (LOG2 n)                   by EXP_BASE_LT_MONO, 1 < 2
        i.e.    e <= LOG2 n
   Only-if part: ?k. k <= LOG2 n /\ (n = m ** k) ==> perfect_power n m
      True by perfect_power_def.
*)
val perfect_power_bound_LOG2 = store_thm(
  "perfect_power_bound_LOG2",
  ``!n. 0 < n ==> !m. perfect_power n m <=> ?k. k <= LOG2 n /\ (n = m ** k)``,
  rw[EQ_IMP_THM] >| [
    Cases_on `n = 1` >-
    simp[] >>
    `?e. (n = m ** e)` by rw[GSYM perfect_power_def] >>
    `n <> 0 /\ 1 < n /\ 1 < 2` by decide_tac >>
    `e <> 0` by metis_tac[EXP] >>
    `m <> 1` by metis_tac[EXP_1] >>
    `m <> 0` by metis_tac[ZERO_EXP] >>
    `2 <= m` by decide_tac >>
    `2 ** e <= n` by rw[EXP_BASE_LE_MONO] >>
    `n < 2 ** (SUC (LOG2 n))` by rw[LOG2_PROPERTY] >>
    `e < SUC (LOG2 n)` by metis_tac[EXP_BASE_LT_MONO, LESS_EQ_LESS_TRANS] >>
    `e <= LOG2 n` by decide_tac >>
    metis_tac[],
    metis_tac[perfect_power_def]
  ]);

(* Theorem: prime p /\ (?x y. 0 < x /\ (p ** x = q ** y)) ==> perfect_power q p *)
(* Proof:
   Note ?k. (q = p ** k)     by power_eq_prime_power, prime p, 0 < x
   Thus perfect_power q p    by perfect_power_def
*)
val perfect_power_condition = store_thm(
  "perfect_power_condition",
  ``!p q. prime p /\ (?x y. 0 < x /\ (p ** x = q ** y)) ==> perfect_power q p``,
  metis_tac[power_eq_prime_power, perfect_power_def]);

(* Theorem: 0 < p /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p) *)
(* Proof:
   Let q = n DIV p.
   Then n = p * q                   by DIVIDES_EQN_COMM, 0 < p
   If part: perfect_power n p ==> perfect_power q p
      Note ?k. n = p ** k           by perfect_power_def
      If k = 0,
         Then p * q = p ** 0 = 1    by EXP
          ==> p = 1 and q = 1       by MULT_EQ_1
           so perfect_power q p     by perfect_power_self
      If k <> 0, k = SUC h for some h.
         Then p * q = p ** SUC h
                    = p * p ** h    by EXP
           or     q = p ** h        by MULT_LEFT_CANCEL, p <> 0
           so perfect_power q p     by perfect_power_self

   Only-if part: perfect_power q p ==> perfect_power n p
      Note ?k. q = p ** k           by perfect_power_def
         so n = p * q = p ** SUC k  by EXP
       thus perfect_power n p       by perfect_power_def
*)
val perfect_power_cofactor = store_thm(
  "perfect_power_cofactor",
  ``!n p. 0 < p /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p)``,
  rpt strip_tac >>
  qabbrev_tac `q = n DIV p` >>
  `n = p * q` by rw[GSYM DIVIDES_EQN_COMM, Abbr`q`] >>
  simp[EQ_IMP_THM] >>
  rpt strip_tac >| [
    `?k. p * q = p ** k` by rw[GSYM perfect_power_def] >>
    Cases_on `k` >| [
      `(p = 1) /\ (q = 1)` by metis_tac[MULT_EQ_1, EXP] >>
      metis_tac[perfect_power_self],
      `q = p ** n'` by metis_tac[EXP, MULT_LEFT_CANCEL, NOT_ZERO_LT_ZERO] >>
      metis_tac[perfect_power_def]
    ],
    `?k. q = p ** k` by rw[GSYM perfect_power_def] >>
    `p * q = p ** SUC k` by rw[EXP] >>
    metis_tac[perfect_power_def]
  ]);

(* Theorem: 0 < n /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p) *)
(* Proof:
   Note 0 < p           by ZERO_DIVIDES, 0 < n
   The result follows   by perfect_power_cofactor
*)
val perfect_power_cofactor_alt = store_thm(
  "perfect_power_cofactor_alt",
  ``!n p. 0 < n /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p)``,
  rpt strip_tac >>
  `0 < p` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  qabbrev_tac `q = n DIV p` >>
  rw[perfect_power_cofactor]);

(* Theorem: perfect_power n 2 ==> (ODD n <=> (n = 1)) *)
(* Proof:
   If part: perfect_power n 2 /\ ODD n ==> n = 1
      By contradiction, suppose n <> 1.
      Note ?k. n = 2 ** k     by perfect_power_def
      Thus k <> 0             by EXP
        so ?h. k = SUC h      by num_CASES
           n = 2 ** (SUC h)   by above
             = 2 * 2 ** h     by EXP
       ==> EVEN n             by EVEN_DOUBLE
      This contradicts ODD n  by EVEN_ODD
   Only-if part: perfect_power n 2 /\ n = 1 ==> ODD n
      This is true              by ODD_1
*)
val perfect_power_2_odd = store_thm(
  "perfect_power_2_odd",
  ``!n. perfect_power n 2 ==> (ODD n <=> (n = 1))``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `?k. n = 2 ** k` by rw[GSYM perfect_power_def] >>
  `k <> 0` by metis_tac[EXP] >>
  `?h. k = SUC h` by metis_tac[num_CASES] >>
  `n = 2 * 2 ** h` by rw[EXP] >>
  metis_tac[EVEN_DOUBLE, EVEN_ODD]);

(* ------------------------------------------------------------------------- *)
(* Power Free                                                                *)
(* ------------------------------------------------------------------------- *)

(* Define a PowerFree number: a trivial perfect power *)
val power_free_def = zDefine`
   power_free (n:num) <=> !m e. (n = m ** e) ==> (m = n) /\ (e = 1)
`;
(* Use zDefine as this is not computationally effective. *)

(* Theorem: power_free 0 = F *)
(* Proof:
   Note 0 ** 2 = 0         by ZERO_EXP
   Thus power_free 0 = F   by power_free_def
*)
val power_free_0 = store_thm(
  "power_free_0",
  ``power_free 0 = F``,
  rw[power_free_def]);

(* Theorem: power_free 1 = F *)
(* Proof:
   Note 0 ** 0 = 1         by ZERO_EXP
   Thus power_free 1 = F   by power_free_def
*)
val power_free_1 = store_thm(
  "power_free_1",
  ``power_free 1 = F``,
  rw[power_free_def]);

(* Theorem: power_free n ==> 1 < n *)
(* Proof:
   By contradiction, suppose n = 0 or n = 1.
   Then power_free 0 = F     by power_free_0
    and power_free 1 = F     by power_free_1
*)
val power_free_gt_1 = store_thm(
  "power_free_gt_1",
  ``!n. power_free n ==> 1 < n``,
  metis_tac[power_free_0, power_free_1, DECIDE``1 < n <=> (n <> 0 /\ n <> 1)``]);

(* Theorem: power_free n <=> 1 < n /\ (!m. perfect_power n m ==> (n = m)) *)
(* Proof:
   If part: power_free n ==> 1 < n /\ (!m. perfect_power n m ==> (n = m))
      Note power_free n
       ==> 1 < n                by power_free_gt_1
       Now ?e. n = m ** e       by perfect_power_def
       ==> n = m                by power_free_def

   Only-if part: 1 < n /\ (!m. perfect_power n m ==> (n = m)) ==> power_free n
      By power_free_def, this is to show:
         (n = m ** e) ==> (m = n) /\ (e = 1)
      Note perfect_power n m    by perfect_power_def, ?e.
       ==> m = n                by implication
        so n = n ** e           by given, m = n
       ==> e = 1                by POWER_EQ_SELF
*)
val power_free_alt = store_thm(
  "power_free_alt",
  ``!n. power_free n <=> 1 < n /\ (!m. perfect_power n m ==> (n = m))``,
  rw[EQ_IMP_THM] >-
  rw[power_free_gt_1] >-
  fs[power_free_def, perfect_power_def] >>
  fs[power_free_def, perfect_power_def] >>
  rpt strip_tac >-
  metis_tac[] >>
  `n = m` by metis_tac[] >>
  metis_tac[POWER_EQ_SELF]);

(* Theorem: prime n ==> power_free n *)
(* Proof:
   Let n = m ** e. To show that n is power_free,
   (1) show m = n, by squeezing m as a factor of prime n.
   (2) show e = 1, by applying prime_powers_eq
   This is a typical detective-style proof.

   Note prime n ==> n <> 1               by NOT_PRIME_1

   Claim: !m e. n = m ** e ==> m = n
   Proof: Note m <> 1                    by EXP_1, n <> 1
           and e <> 0                    by EXP, n <> 1
          Thus e = SUC k for some k      by num_CASES
               n = m ** SUC k
                 = m * (m ** k)          by EXP
                 = (m ** k) * m          by MULT_COMM
          Thus m divides n,              by divides_def
           But m <> 1, so m = n          by prime_def

   The claim satisfies half of the power_free_def.
   With m = n, prime m,
    and e <> 0                           by EXP, n <> 1
   Thus n = n ** 1 = m ** e              by EXP_1
    ==> e = 1                            by prime_powers_eq, 0 < e.
*)
val prime_is_power_free = store_thm(
  "prime_is_power_free",
  ``!n. prime n ==> power_free n``,
  rpt strip_tac >>
  `n <> 1` by metis_tac[NOT_PRIME_1] >>
  `!m e. (n = m ** e) ==> (m = n)` by
  (rpt strip_tac >>
  `m <> 1` by metis_tac[EXP_1] >>
  metis_tac[EXP, num_CASES, MULT_COMM, divides_def, prime_def]) >>
  `!m e. (n = m ** e) ==> (e = 1)` by metis_tac[EXP, EXP_1, prime_powers_eq, NOT_ZERO_LT_ZERO] >>
  metis_tac[power_free_def]);

(* Theorem: power_free n /\ perfect_power n m ==> (n = m) *)
(* Proof:
   Note ?e. n = m ** e        by perfect_power_def
    ==> n = m                 by power_free_def
*)
val power_free_perfect_power = store_thm(
  "power_free_perfect_power",
  ``!m n. power_free n /\ perfect_power n m ==> (n = m)``,
  metis_tac[perfect_power_def, power_free_def]);

(* Theorem: power_free n ==> (!j. 1 < j ==> (ROOT j n) ** j <> n) *)
(* Proof:
   By contradiction, suppose (ROOT j n) ** j = n.
   Then j = 1                 by power_free_def
   This contradicts 1 < j.
*)
val power_free_property = store_thm(
  "power_free_property",
  ``!n. power_free n ==> (!j. 1 < j ==> (ROOT j n) ** j <> n)``,
  spose_not_then strip_assume_tac >>
  `j = 1` by metis_tac[power_free_def] >>
  decide_tac);

(* We have:
power_free_0   |- power_free 0 <=> F
power_free_1   |- power_free 1 <=> F
So, given 1 < n, how to check power_free n ?
*)

(* Theorem: power_free n <=> 1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n) *)
(* Proof:
   If part: power_free n ==> 1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n)
      Note 1 < n                       by power_free_gt_1
      The rest is true                 by power_free_property.
   Only-if part: 1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n) ==> power_free n
      By contradiction, assume ~(power_free n).
      That is, ?m e. n = m ** e /\ (m = m ** e ==> e <> 1)   by power_free_def
      Note 1 < m /\ 0 < e             by ONE_LT_EXP, 1 < n
      Thus ROOT e n = m               by ROOT_POWER, 1 < m, 0 < e
      By the implication, ~(1 < e), or e <= 1.
      Since 0 < e, this shows e = 1.
      Then m = m ** e                 by EXP_1
      This gives e <> 1, a contradiction.
*)
val power_free_check_all = store_thm(
  "power_free_check_all",
  ``!n. power_free n <=> 1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n)``,
  rw[EQ_IMP_THM] >-
  rw[power_free_gt_1] >-
  rw[power_free_property] >>
  simp[power_free_def] >>
  spose_not_then strip_assume_tac >>
  `1 < m /\ 0 < e` by metis_tac[ONE_LT_EXP] >>
  `ROOT e n = m` by rw[ROOT_POWER] >>
  `~(1 < e)` by metis_tac[] >>
  `e = 1` by decide_tac >>
  rw[]);

(* However, there is no need to check all the exponents:
  just up to (LOG2 n) or (ulog n) is sufficient.
  See earlier part with power_free_upto_def. *)

(* ------------------------------------------------------------------------- *)
(* Upper Logarithm                                                           *)
(* ------------------------------------------------------------------------- *)

(* Find the power of 2 more or equal to n *)
val count_up_def = tDefine "count_up" `
  count_up n m k =
       if m = 0 then 0 (* just to provide m <> 0 for the next one *)
  else if n <= m then k else count_up n (2 * m) (SUC k)
` (WF_REL_TAC `measure (\(n, m, k). n - m)`);

(* Define upper LOG2 n by count_up *)
val ulog_def = Define`
    ulog n = count_up n 1 0
`;

(*
> EVAL ``ulog 1``; --> 0
> EVAL ``ulog 2``; --> 1
> EVAL ``ulog 3``; --> 2
> EVAL ``ulog 4``; --> 2
> EVAL ``ulog 5``; --> 3
> EVAL ``ulog 6``; --> 3
> EVAL ``ulog 7``; --> 3
> EVAL ``ulog 8``; --> 3
> EVAL ``ulog 9``; --> 4
*)

(* Theorem: ulog 0 = 0 *)
(* Proof:
     ulog 0
   = count_up 0 1 0    by ulog_def
   = 0                 by count_up_def, 0 <= 1
*)
val ulog_0 = store_thm(
  "ulog_0[simp]",
  ``ulog 0 = 0``,
  rw[ulog_def, Once count_up_def]);

(* Theorem: ulog 1 = 0 *)
(* Proof:
     ulog 1
   = count_up 1 1 0    by ulog_def
   = 0                 by count_up_def, 1 <= 1
*)
val ulog_1 = store_thm(
  "ulog_1[simp]",
  ``ulog 1 = 0``,
  rw[ulog_def, Once count_up_def]);

(* Theorem: ulog 2 = 1 *)
(* Proof:
     ulog 2
   = count_up 2 1 0    by ulog_def
   = count_up 2 2 1    by count_up_def, ~(1 < 2)
   = 1                 by count_up_def, 2 <= 2
*)
val ulog_2 = store_thm(
  "ulog_2[simp]",
  ``ulog 2 = 1``,
  rw[ulog_def, Once count_up_def] >>
  rw[Once count_up_def]);

(* Theorem: m <> 0 /\ n <= m ==> !k. count_up n m k = k *)
(* Proof: by count_up_def *)
val count_up_exit = store_thm(
  "count_up_exit",
  ``!m n. m <> 0 /\ n <= m ==> !k. count_up n m k = k``,
  rw[Once count_up_def]);

(* Theorem: m <> 0 /\ m < n ==> !k. count_up n m k = count_up n (2 * m) (SUC k) *)
(* Proof: by count_up_def *)
val count_up_suc = store_thm(
  "count_up_suc",
  ``!m n. m <> 0 /\ m < n ==> !k. count_up n m k = count_up n (2 * m) (SUC k)``,
  rw[Once count_up_def]);

(* Theorem: m <> 0 ==>
            !t. 2 ** t * m < n ==> !k. count_up n m k = count_up n (2 ** (SUC t) * m) ((SUC k) + t) *)
(* Proof:
   By induction on t.
   Base: 2 ** 0 * m < n ==> !k. count_up n m k = count_up n (2 ** SUC 0 * m) (SUC k + 0)
      Simplifying, this is to show:
          m < n ==> !k. count_up n m k = count_up n (2 * m) (SUC k)
      which is true by count_up_suc.
   Step: 2 ** t * m < n ==> !k. count_up n m k = count_up n (2 ** SUC t * m) (SUC k + t) ==>
         2 ** SUC t * m < n ==> !k. count_up n m k = count_up n (2 ** SUC (SUC t) * m) (SUC k + SUC t)
      Note 2 ** SUC t <> 0        by EXP_EQ_0, 2 <> 0
        so 2 ** SUC t * m <> 0    by MULT_EQ_0, m <> 0
       and 2 ** SUC t * m
         = 2 * 2 ** t * m         by EXP
         = 2 * (2 ** t * m)       by MULT_ASSOC
      Thus (2 ** t * m) < n       by MULT_LESS_IMP_LESS, 0 < 2
         count_up n m k
       = count_up n (2 ** SUC t * m) (SUC k + t)             by induction hypothesis
       = count_up n (2 * (2 ** SUC t * m)) (SUC (SUC k + t)) by count_up_suc
       = count_up n (2 ** SUC (SUC t) * m) (SUC k + SUC t)   by EXP, ADD1
*)
val count_up_suc_eqn = store_thm(
  "count_up_suc_eqn",
  ``!m. m <> 0 ==>
   !n t. 2 ** t * m < n ==> !k. count_up n m k = count_up n (2 ** (SUC t) * m) ((SUC k) + t)``,
  ntac 3 strip_tac >>
  Induct >-
  rw[count_up_suc] >>
  rpt strip_tac >>
  qabbrev_tac `q = 2 ** t * m` >>
  `2 ** SUC t <> 0` by metis_tac[EXP_EQ_0, DECIDE``2 <> 0``] >>
  `2 ** SUC t * m <> 0` by metis_tac[MULT_EQ_0] >>
  `2 ** SUC t * m = 2 * q` by rw_tac std_ss[EXP, MULT_ASSOC, Abbr`q`] >>
  `q < n` by rw[MULT_LESS_IMP_LESS] >>
  rw[count_up_suc, EXP, ADD1]);

(* Theorem: m <> 0 ==> !n t. 2 ** t * m < 2 * n /\ n <= 2 ** t * m ==> !k. count_up n m k = k + t *)
(* Proof:
   If t = 0,
      Then n <= m           by EXP
        so count_up n m k
         = k                by count_up_exit
         = k + 0            by ADD_0
   If t <> 0,
      Then ?s. t = SUC s            by num_CASES
      Note 2 ** t * m
         = 2 ** SUC s * m           by above
         = 2 * 2 ** s * m           by EXP
         = 2 * (2 ** s * m)         by MULT_ASSOC
      Note 2 ** SUC s * m < 2 * n   by given
        so   (2 ** s * m) < n       by LT_MULT_RCANCEL, 2 <> 0

        count_up n m k
      = count_up n (2 ** t * m) ((SUC k) + t)   by count_up_suc_eqn
      = (SUC k) + t                             by count_up_exit
*)
val count_up_exit_eqn = store_thm(
  "count_up_exit_eqn",
  ``!m. m <> 0 ==> !n t. 2 ** t * m < 2 * n /\ n <= 2 ** t * m ==> !k. count_up n m k = k + t``,
  rpt strip_tac >>
  Cases_on `t` >-
  fs[count_up_exit] >>
  qabbrev_tac `q = 2 ** n' * m` >>
  `2 ** SUC n' * m = 2 * q` by rw_tac std_ss[EXP, MULT_ASSOC, Abbr`q`] >>
  `q < n` by decide_tac >>
  `count_up n m k = count_up n (2 ** (SUC n') * m) ((SUC k) + n')` by rw[count_up_suc_eqn, Abbr`q`] >>
  `_ = (SUC k) + n'` by rw[count_up_exit] >>
  rw[]);

(* Theorem: 2 ** m < 2 * n /\ n <= 2 ** m ==> (ulog n = m) *)
(* Proof:
   Put m = 1 in count_up_exit_eqn:
       2 ** t * 1 < 2 * n /\ n <= 2 ** t * 1 ==> !k. count_up n 1 k = k + t
   Put k = 0, and apply MULT_RIGHT_1, ADD:
       2 ** t * 1 < 2 * n /\ n <= 2 ** t * 1 ==> count_up n 1 0 = t
   Then apply ulog_def to get the result, and rename t by m.
*)
val ulog_unique = store_thm(
  "ulog_unique",
  ``!m n. 2 ** m < 2 * n /\ n <= 2 ** m ==> (ulog n = m)``,
  metis_tac[ulog_def, count_up_exit_eqn, MULT_RIGHT_1, ADD, DECIDE``1 <> 0``]);

(* Theorem: ulog n = if 1 < n then SUC (LOG2 (n - 1)) else 0 *)
(* Proof:
   If 1 < n,
      Then 0 < n - 1      by 1 < n
       ==> 2 ** LOG2 (n - 1) <= (n - 1) /\
           (n - 1) < 2 ** SUC (LOG2 (n - 1))      by LOG2_PROPERTY
        or 2 ** LOG2 (n - 1) < n /\
           n <= 2 ** SUC (LOG2 (n - 1))           by shifting inequalities
       Let t = SUC (LOG2 (n - 1)).
       Then 2 ** t = 2 * 2 ** (LOG2 (n - 1))      by EXP
                   < 2 * n                        by LT_MULT_LCANCEL, 2 ** LOG2 (n - 1) < n
       Thus ulog n = t                            by ulog_unique.
   If ~(1 < n),
      Then n <= 1, or n = 0 or n = 1.
      If n = 0, ulog n = 0                        by ulog_0
      If n = 1, ulog n = 0                        by ulog_1
*)
val ulog_eqn = store_thm(
  "ulog_eqn",
  ``!n. ulog n = if 1 < n then SUC (LOG2 (n - 1)) else 0``,
  rw[] >| [
    `0 < n - 1` by decide_tac >>
    `2 ** LOG2 (n - 1) <= (n - 1) /\ (n - 1) < 2 ** SUC (LOG2 (n - 1))` by metis_tac[LOG2_PROPERTY] >>
    `2 * 2 ** LOG2 (n - 1) < 2 * n /\ n <= 2 ** SUC (LOG2 (n - 1))` by decide_tac >>
    rw[EXP, ulog_unique],
    metis_tac[ulog_0, ulog_1, DECIDE``~(1 < n) <=> (n = 0) \/ (n = 1)``]
  ]);

(* Theorem: 0 < n ==> (ulog (SUC n) = SUC (LOG2 n)) *)
(* Proof:
   Note 0 < n ==> 1 < SUC n      by LT_ADD_RCANCEL, ADD1
   Thus ulog (SUC n)
      = SUC (LOG2 (SUC n - 1))   by ulog_eqn
      = SUC (LOG2 n)             by SUC_SUB1
*)
val ulog_suc = store_thm(
  "ulog_suc",
  ``!n. 0 < n ==> (ulog (SUC n) = SUC (LOG2 n))``,
  rpt strip_tac >>
  `1 < SUC n` by decide_tac >>
  rw[ulog_eqn]);

(* Theorem: 0 < n ==> 2 ** (ulog n) < 2 * n /\ n <= 2 ** (ulog n) *)
(* Proof:
   Apply ulog_eqn, this is to show:
   (1) 1 < n ==> 2 ** SUC (LOG2 (n - 1)) < 2 * n
       Let m = n - 1.
       Note 0 < m                   by 1 < n
        ==> 2 ** LOG2 m <= m        by TWO_EXP_LOG2_LE, 0 < m
         or             <= n - 1    by notation
       Thus 2 ** LOG2 m < n         by inequality [1]
        and 2 ** SUC (LOG2 m)
          = 2 * 2 ** (LOG2 m)       by EXP
          < 2 * n                   by LT_MULT_LCANCEL, [1]
   (2) 1 < n ==> n <= 2 ** SUC (LOG2 (n - 1))
       Let m = n - 1.
       Note 0 < m                          by 1 < n
        ==> m < 2 ** SUC (LOG2 m)          by LOG2_PROPERTY, 0 < m
        n - 1 < 2 ** SUC (LOG2 m)          by notation
            n <= 2 ** SUC (LOG2 m)         by inequality [2]
         or n <= 2 ** SUC (LOG2 (n - 1))   by notation
*)
val ulog_property = store_thm(
  "ulog_property",
  ``!n. 0 < n ==> 2 ** (ulog n) < 2 * n /\ n <= 2 ** (ulog n)``,
  rw[ulog_eqn] >| [
    `0 < n - 1` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `2 ** SUC (LOG2 m) = 2 * 2 ** (LOG2 m)` by rw[EXP] >>
    `2 ** LOG2 m <= n - 1` by rw[TWO_EXP_LOG2_LE, Abbr`m`] >>
    decide_tac,
    `0 < n - 1` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `2 ** SUC (LOG2 m) = 2 * 2 ** (LOG2 m)` by rw[EXP] >>
    `n - 1 < 2 ** SUC (LOG2 m)` by metis_tac[LOG2_PROPERTY] >>
    decide_tac
  ]);

(* Theorem: 0 < n ==> !m. (ulog n = m) <=> 2 ** m < 2 * n /\ n <= 2 ** m *)
(* Proof:
   If part: 0 < n ==> 2 ** (ulog n) < 2 * n /\ n <= 2 ** (ulog n)
      True by ulog_property, 0 < n
   Only-if part: 2 ** m < 2 * n /\ n <= 2 ** m ==> ulog n = m
      True by ulog_unique
*)
val ulog_thm = store_thm(
  "ulog_thm",
  ``!n. 0 < n ==> !m. (ulog n = m) <=> (2 ** m < 2 * n /\ n <= 2 ** m)``,
  metis_tac[ulog_property, ulog_unique]);

(* Have an equation to present the definition *)
val ulog_def_alt = save_thm("ulog_def_alt", CONJ ulog_0 ulog_thm);
(* val ulog_def_alt =
|- (ulog 0 = 0) /\ !n. 0 < n ==> !m. ulog n = m <=> 2 ** m < TWICE n /\ n <= 2 ** m: thm *)

(* This is OK, but the followig is better *)

(* Theorem: (ulog 0 = 0) /\ !n. 0 < n ==> !m. (ulog n = m) <=> (n <= 2 ** m /\ 2 ** m < 2 * n) *)
(* Proof: by ulog_0 ulog_thm *)
val ulog_def_alt = store_thm(
  "ulog_def_alt",
  ``(ulog 0 = 0) /\ !n. 0 < n ==> !m. (ulog n = m) <=> (n <= 2 ** m /\ 2 ** m < 2 * n)``,
  rw[ulog_0, ulog_thm]);

(* Theorem: (ulog n = 0) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   Note !n. SUC n <> 0                   by NOT_SUC
     so if 1 < n, ulog n <> 0            by ulog_eqn
   Thus ulog n = 0 <=> ~(1 < n)          by above
     or            <=> n <= 1            by negation
     or            <=> n = 0 or n = 1    by range
*)
val ulog_eq_0 = store_thm(
  "ulog_eq_0",
  ``!n. (ulog n = 0) <=> ((n = 0) \/ (n = 1))``,
  rw[ulog_eqn]);

(* Theorem: (ulog n = 1) <=> (n = 2) *)
(* Proof:
   If part: ulog n = 1 ==> n = 2
      Note n <> 0 and n <> 1             by ulog_eq_0
      Thus 1 < n, or 0 < n - 1           by arithmetic
       ==> SUC (LOG2 (n - 1)) = 1        by ulog_eqn, 1 < n
        or      LOG2 (n - 1) = 0         by SUC_EQ, ONE
       ==>            n - 1 < 2          by LOG_EQ_0, 0 < n - 1
        or                n <= 2         by inequality
      Combine with 1 < n, n = 2.
   Only-if part: ulog 2 = 1
         ulog 2
       = ulog (SUC 1)                    by TWO
       = SUC (LOG2 1)                    by ulog_suc
       = SUC 0                           by LOG_1, 0 < 2
       = 1                               by ONE
*)
val ulog_eq_1 = store_thm(
  "ulog_eq_1",
  ``!n. (ulog n = 1) <=> (n = 2)``,
  rw[EQ_IMP_THM] >>
  `n <> 0 /\ n <> 1` by metis_tac[ulog_eq_0, DECIDE``1 <> 0``] >>
  `1 < n /\ 0 < n - 1` by decide_tac >>
  `SUC (LOG2 (n - 1)) = 1` by metis_tac[ulog_eqn] >>
  `LOG2 (n - 1) = 0` by decide_tac >>
  `n - 1 < 2` by metis_tac[LOG_EQ_0, DECIDE``1 < 2``] >>
  decide_tac);

(* Theorem: ulog n <= 1 <=> n <= 2 *)
(* Proof:
       ulog n <= 1
   <=> ulog n = 0 \/ ulog n = 1   by arithmetic
   <=> n = 0 \/ n = 1 \/ n = 2    by ulog_eq_0, ulog_eq_1
   <=> n <= 2                     by arithmetic

*)
val ulog_le_1 = store_thm(
  "ulog_le_1",
  ``!n. ulog n <= 1 <=> n <= 2``,
  rpt strip_tac >>
  `ulog n <= 1 <=> ((ulog n = 0) \/ (ulog n = 1))` by decide_tac >>
  rw[ulog_eq_0, ulog_eq_1]);

(* Theorem: n <= m ==> ulog n <= ulog m *)
(* Proof:
   If n = 0,
      Note ulog 0 = 0      by ulog_0
      and 0 <= ulog m      for anything
   If n = 1,
      Note ulog 1 = 0      by ulog_1
      Thus 0 <= ulog m     by arithmetic
   If n <> 1, then 1 < n
      Note n <= m, so 1 < m
      Thus 0 < n - 1       by arithmetic
       and n - 1 <= m - 1  by arithmetic
       ==> LOG2 (n - 1) <= LOG2 (m - 1)              by LOG2_LE
       ==> SUC (LOG2 (n - 1)) <= SUC (LOG2 (m - 1))  by LESS_EQ_MONO
        or          ulog n <= ulog m                 by ulog_eqn, 1 < n, 1 < m
*)
val ulog_le = store_thm(
  "ulog_le",
  ``!m n. n <= m ==> ulog n <= ulog m``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  Cases_on `n = 1` >-
  rw[] >>
  rw[ulog_eqn, LOG2_LE]);

(* Theorem: n < m ==> ulog n <= ulog m *)
(* Proof: by ulog_le *)
val ulog_lt = store_thm(
  "ulog_lt",
  ``!m n. n < m ==> ulog n <= ulog m``,
  rw[ulog_le]);

(* Theorem: ulog (2 ** n) = n *)
(* Proof:
   Note 0 < 2 ** n             by EXP_POS, 0 < 2
   From 1 < 2                  by arithmetic
    ==> 2 ** n < 2 * 2 ** n    by LT_MULT_RCANCEL, 0 < 2 ** n
    Now 2 ** n <= 2 ** n       by LESS_EQ_REFL
   Thus ulog (2 ** n) = n      by ulog_unique
*)
val ulog_2_exp = store_thm(
  "ulog_2_exp",
  ``!n. ulog (2 ** n) = n``,
  rpt strip_tac >>
  `0 < 2 ** n` by rw[EXP_POS] >>
  `2 ** n < 2 * 2 ** n` by decide_tac >>
  `2 ** n <= 2 ** n` by decide_tac >>
  rw[ulog_unique]);

(* Theorem: ulog n <= n *)
(* Proof:
   Note      n < 2 ** n          by X_LT_EXP_X
   Thus ulog n <= ulog (2 ** n)  by ulog_lt
     or ulog n <= n              by ulog_2_exp
*)
val ulog_le_self = store_thm(
  "ulog_le_self",
  ``!n. ulog n <= n``,
  metis_tac[X_LT_EXP_X, ulog_lt, ulog_2_exp, DECIDE``1 < 2n``]);

(* Theorem: ulog n = n <=> n = 0 *)
(* Proof:
   If part: ulog n = n ==> n = 0
      By contradiction, assume n <> 0
      Then ?k. n = SUC k            by num_CASES, n < 0
        so  2 ** SUC k < 2 * SUC k  by ulog_property
        or  2 * 2 ** k < 2 * SUC k  by EXP
       ==>      2 ** k < SUC k      by arithmetic
        or      2 ** k <= k         by arithmetic
      This contradicts k < 2 ** k   by X_LT_EXP_X, 0 < 2
   Only-if part: ulog 0 = 0
      This is true                  by ulog_0
*)
val ulog_eq_self = store_thm(
  "ulog_eq_self",
  ``!n. (ulog n = n) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `?k. n = SUC k` by metis_tac[num_CASES] >>
  `2 * (2 ** k) = 2 ** SUC k` by rw[EXP] >>
  `0 < n` by decide_tac >>
  `2 ** SUC k < 2 * SUC k` by metis_tac[ulog_property] >>
  `2 ** k <= k` by decide_tac >>
  `k < 2 ** k` by rw[X_LT_EXP_X] >>
  decide_tac);

(* Theorem: 0 < n ==> ulog n < n *)
(* Proof:
   By contradiction, assume ~(ulog n < n).
   Then n <= ulog n      by ~(ulog n < n)
    But ulog n <= n      by ulog_le_self
    ==> ulog n = n       by arithmetic
     so n = 0            by ulog_eq_self
   This contradicts 0 < n.
*)
val ulog_lt_self = store_thm(
  "ulog_lt_self",
  ``!n. 0 < n ==> ulog n < n``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `ulog n <= n` by rw[ulog_le_self] >>
  `ulog n = n` by decide_tac >>
  `n = 0` by rw[GSYM ulog_eq_self] >>
  decide_tac);

(* Theorem: (2 ** (ulog n) = n) <=> perfect_power n 2 *)
(* Proof:
   Using perfect_power_def,
   If part: 2 ** (ulog n) = n ==> ?e. n = 2 ** e
      True by taking e = ulog n.
   Only-if part: 2 ** ulog (2 ** e) = 2 ** e
      This is true by ulog_2_exp
*)
val ulog_exp_exact = store_thm(
  "ulog_exp_exact",
  ``!n. (2 ** (ulog n) = n) <=> perfect_power n 2``,
  rw[perfect_power_def, EQ_IMP_THM] >-
  metis_tac[] >>
  rw[ulog_2_exp]);

(* Theorem: ~(perfect_power n 2) ==> 2 ** ulog n <> n *)
(* Proof: by ulog_exp_exact. *)
val ulog_exp_not_exact = store_thm(
  "ulog_exp_not_exact",
  ``!n. ~(perfect_power n 2) ==> 2 ** ulog n <> n``,
  rw[ulog_exp_exact]);

(* Theorem: 0 < n /\ ~(perfect_power n 2) ==> n < 2 ** ulog n *)
(* Proof:
   Note n <= 2 ** ulog n    by ulog_property, 0 < n
    But n <> 2 ** ulog n    by ulog_exp_not_exact, ~(perfect_power n 2)
   Thus  n < 2 ** ulog n    by LESS_OR_EQ
*)
val ulog_property_not_exact = store_thm(
  "ulog_property_not_exact",
  ``!n. 0 < n /\ ~(perfect_power n 2) ==> n < 2 ** ulog n``,
  metis_tac[ulog_property, ulog_exp_not_exact, LESS_OR_EQ]);

(* Theorem: 1 < n /\ ODD n ==> n < 2 ** ulog n *)
(* Proof:
   Note 0 < n /\ n <> 1        by 1 < n
   Thus n <= 2 ** ulog n       by ulog_property, 0 < n
    But ~(perfect_power n 2)   by perfect_power_2_odd, n <> 1
    ==> n <> 2 ** ulog n       by ulog_exp_not_exact, ~(perfect_power n 2)
   Thus n < 2 ** ulog n        by LESS_OR_EQ
*)
val ulog_property_odd = store_thm(
  "ulog_property_odd",
  ``!n. 1 < n /\ ODD n ==> n < 2 ** ulog n``,
  rpt strip_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  `n <= 2 ** ulog n` by metis_tac[ulog_property] >>
  `~(perfect_power n 2)` by metis_tac[perfect_power_2_odd] >>
  `2 ** ulog n <> n` by rw[ulog_exp_not_exact] >>
  decide_tac);

(* Theorem: n <= 2 ** m ==> ulog n <= m *)
(* Proof:
      n <= 2 ** m
   ==> ulog n <= ulog (2 ** m)    by ulog_le
   ==> ulog n <= m                by ulog_2_exp
*)
val exp_to_ulog = store_thm(
  "exp_to_ulog",
  ``!m n. n <= 2 ** m ==> ulog n <= m``,
  metis_tac[ulog_le, ulog_2_exp]);

(* Theorem: 1 < n ==> 0 < ulog n *)
(* Proof:
   Note 1 < n ==> n <> 0 /\ n <> 1     by arithmetic
     so ulog n <> 0                    by ulog_eq_0
     or 0 < ulog n                     by NOT_ZERO_LT_ZERO
*)
val ulog_pos = store_thm(
  "ulog_pos[simp]",
  ``!n. 1 < n ==> 0 < ulog n``,
  metis_tac[ulog_eq_0, NOT_ZERO, DECIDE``1 < n <=> n <> 0 /\ n <> 1``]);

(* Theorem: 1 < n ==> 1 <= ulog n *)
(* Proof:
   Note  0 < ulog n      by ulog_pos
   Thus  1 <= ulog n     by arithmetic
*)
val ulog_ge_1 = store_thm(
  "ulog_ge_1",
  ``!n. 1 < n ==> 1 <= ulog n``,
  metis_tac[ulog_pos, DECIDE``0 < n ==> 1 <= n``]);

(* Theorem: 2 < n ==> 1 < (ulog n) ** 2 *)
(* Proof:
   Note 1 < n /\ n <> 2      by 2 < n
     so 0 < ulog n           by ulog_pos, 1 < n
    and ulog n <> 1          by ulog_eq_1, n <> 2
   Thus 1 < ulog n           by ulog n <> 0, ulog n <> 1
     so 1 < (ulog n) ** 2    by ONE_LT_EXP, 0 < 2
*)
val ulog_sq_gt_1 = store_thm(
  "ulog_sq_gt_1",
  ``!n. 2 < n ==> 1 < (ulog n) ** 2``,
  rpt strip_tac >>
  `1 < n /\ n <> 2` by decide_tac >>
  `0 < ulog n` by rw[] >>
  `ulog n <> 1` by rw[ulog_eq_1] >>
  `1 < ulog n` by decide_tac >>
  rw[ONE_LT_EXP]);

(* Theorem: 1 < n ==> 4 <= (2 * ulog n) ** 2 *)
(* Proof:
   Note  0 < ulog n               by ulog_pos, 1 < n
   Thus  2 <= 2 * ulog n          by arithmetic
     or  4 <= (2 * ulog n) ** 2   by EXP_BASE_LE_MONO
*)
val ulog_twice_sq = store_thm(
  "ulog_twice_sq",
  ``!n. 1 < n ==> 4 <= (2 * ulog n) ** 2``,
  rpt strip_tac >>
  `0 < ulog n` by rw[ulog_pos] >>
  `2 <= 2 * ulog n` by decide_tac >>
  `2 ** 2 <= (2 * ulog n) ** 2` by rw[EXP_BASE_LE_MONO] >>
  `2 ** 2 = 4` by rw[] >>
  decide_tac);

(* Theorem: ulog n = if n = 0 then 0
                else if (perfect_power n 2) then (LOG2 n) else SUC (LOG2 n) *)
(* Proof:
   This is to show:
   (1) ulog 0 = 0, true            by ulog_0
   (2) perfect_power n 2 ==> ulog n = LOG2 n
       Note ?k. n = 2 ** k         by perfect_power_def
       Thus ulog n = k             by ulog_exp_exact
        and LOG2 n = k             by LOG_EXACT_EXP, 1 < 2
   (3) ~(perfect_power n 2) ==> ulog n = SUC (LOG2 n)
       Let m = SUC (LOG2 n).
       Then 2 ** m
          = 2 * 2 ** (LOG2 n)      by EXP
          <= 2 * n                 by TWO_EXP_LOG2_LE
       But n <> LOG2 n             by LOG2_EXACT_EXP, ~(perfect_power n 2)
       Thus 2 ** m < 2 * n         [1]

       Also n < 2 ** m             by LOG2_PROPERTY
       Thus n <= 2 ** m,           [2]
       giving ulog n = m           by ulog_unique, [1] [2]
*)
val ulog_alt = store_thm(
  "ulog_alt",
  ``!n. ulog n = if n = 0 then 0
                else if (perfect_power n 2) then (LOG2 n) else SUC (LOG2 n)``,
  rw[] >-
  metis_tac[perfect_power_def, ulog_exp_exact, LOG_EXACT_EXP, DECIDE``1 < 2``] >>
  qabbrev_tac `m = SUC (LOG2 n)` >>
  (irule ulog_unique >> rpt conj_tac) >| [
    `2 ** m = 2 * 2 ** (LOG2 n)` by rw[EXP, Abbr`m`] >>
    `2 ** (LOG2 n) <= n` by rw[TWO_EXP_LOG2_LE] >>
    `2 ** (LOG2 n) <> n` by rw[LOG2_EXACT_EXP, GSYM perfect_power_def] >>
    decide_tac,
    `n < 2 ** m` by rw[LOG2_PROPERTY, Abbr`m`] >>
    decide_tac
  ]);

(*
Thus, for 0 < n, (ulog n) and SUC (LOG2 n) differ only for (perfect_power n 2).
This means that replacing AKS bounds of SUC (LOG2 n) by (ulog n)
only affect calculations involving (perfect_power n 2),
which are irrelevant for primality testing !
However, in display, (ulog n) is better, while SUC (LOG2 n) is a bit ugly.
*)

(* Theorem: 0 < n ==> (LOG2 n <= ulog n /\ ulog n <= 1 + LOG2 n) *)
(* Proof: by ulog_alt *)
val ulog_LOG2 = store_thm(
  "ulog_LOG2",
  ``!n. 0 < n ==> (LOG2 n <= ulog n /\ ulog n <= 1 + LOG2 n)``,
  rw[ulog_alt]);

(* Theorem: 0 < n ==> !m. perfect_power n m <=> ?k. k <= ulog n /\ (n = m ** k) *)
(* Proof: by perfect_power_bound_LOG2, ulog_LOG2 *)
val perfect_power_bound_ulog = store_thm(
  "perfect_power_bound_ulog",
  ``!n. 0 < n ==> !m. perfect_power n m <=> ?k. k <= ulog n /\ (n = m ** k)``,
  rw[EQ_IMP_THM] >| [
    `LOG2 n <= ulog n` by rw[ulog_LOG2] >>
    metis_tac[perfect_power_bound_LOG2, LESS_EQ_TRANS],
    metis_tac[perfect_power_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Upper Log Theorems                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ulog (m * n) <= ulog m + ulog n *)
(* Proof:
   Let x = ulog (m * n), y = ulog m + ulog n.
   Note    m * n <= 2 ** x      < 2 * m * n      by ulog_thm
    and        m <= 2 ** ulog m < 2 * m          by ulog_thm
    and        n <= 2 ** ulog n < 2 * n          by ulog_thm
   Note that 2 ** ulog m * 2 ** ulog n = 2 ** y  by EXP_ADD
   Multiplying inequalities,
           m * n <= 2 ** y                 by LE_MONO_MULT2
                    2 ** y < 4 * m * n     by LT_MONO_MULT2
    The picture is:
           m * n  ....... 2 * m * n ....... 4 * m * n
                   2 ** x somewhere
                          2 ** y somewhere
    If 2 ** y < 2 * m * n,
       Then x = y                          by ulog_unique
    Otherwise,
       2 ** y is in the second range.
    Then    2 ** x < 2 ** y                since 2 ** x in the first
      or         x < y                     by EXP_BASE_LT_MONO
    Combining these two cases: x <= y.
*)
val ulog_mult = store_thm(
  "ulog_mult",
  ``!m n. ulog (m * n) <= ulog m + ulog n``,
  rpt strip_tac >>
  Cases_on `(m = 0) \/ (n = 0)` >-
  fs[] >>
  `m * n <> 0` by rw[] >>
  `0 < m /\ 0 < n /\ 0 < m * n` by decide_tac >>
  qabbrev_tac `x = ulog (m * n)` >>
  qabbrev_tac `y = ulog m + ulog n` >>
  `m * n <= 2 ** x /\ 2 ** x < TWICE (m * n)` by metis_tac[ulog_thm] >>
  `m * n <= 2 ** y /\ 2 ** y < (TWICE m) * (TWICE n)` by metis_tac[ulog_thm, LE_MONO_MULT2, LT_MONO_MULT2, EXP_ADD] >>
  Cases_on `2 ** y < TWICE (m * n)` >| [
    `y = x` by metis_tac[ulog_unique] >>
    decide_tac,
    `2 ** x < 2 ** y /\ 1 < 2` by decide_tac >>
    `x < y` by metis_tac[EXP_BASE_LT_MONO] >>
    decide_tac
  ]);

(* Theorem: ulog (m ** n) <= n * ulog m *)
(* Proof:
   By induction on n.
   Base: ulog (m ** 0) <= 0 * ulog m
      LHS = ulog (m ** 0)
          = ulog 1            by EXP_0
          = 0                 by ulog_1
          <= 0 * ulog m       by MULT
          = RHS
   Step: ulog (m ** n) <= n * ulog m ==> ulog (m ** SUC n) <= SUC n * ulog m
      LHS = ulog (m ** SUC n)
          = ulog (m * m ** n)          by EXP
          <= ulog m + ulog (m ** n)    by ulog_mult
          <= ulog m + n * ulog m       by induction hypothesis
           = (1 + n) * ulog m          by RIGHT_ADD_DISTRIB
           = SUC n * ulog m            by ADD1, ADD_COMM
           = RHS
*)
val ulog_exp = store_thm(
  "ulog_exp",
  ``!m n. ulog (m ** n) <= n * ulog m``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[EXP_0] >>
  `ulog (m ** SUC n) <= ulog m + ulog (m ** n)` by rw[EXP, ulog_mult] >>
  `ulog m + ulog (m ** n) <= ulog m + n * ulog m` by rw[] >>
  `ulog m + n * ulog m = SUC n * ulog m` by rw[ADD1] >>
  decide_tac);

(* Theorem: 0 < n /\ EVEN n ==> (ulog n = 1 + ulog (HALF n)) *)
(* Proof:
   Let k = HALF n.
   Then 0 < k                                      by HALF_EQ_0, EVEN n
    and EVEN n ==> n = TWICE k                     by EVEN_HALF
   Note        n <= 2 ** ulog n < 2 * n            by ulog_thm, by 0 < n
    and        k <= 2 ** ulog k < 2 * k            by ulog_thm, by 0 < k
    so     2 * k <= 2 * 2 ** ulog k < 2 * 2 * k    by multiplying 2
    or         n <= 2 ** (1 + ulog k) < 2 * n      by EXP
  Thus     ulog n = 1 + ulog k                     by ulog_unique
*)
val ulog_even = store_thm(
  "ulog_even",
  ``!n. 0 < n /\ EVEN n ==> (ulog n = 1 + ulog (HALF n))``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `n = TWICE k` by rw[EVEN_HALF, Abbr`k`] >>
  `0 < k` by rw[Abbr`k`] >>
  `n <= 2 ** ulog n /\ 2 ** ulog n < 2 * n` by metis_tac[ulog_thm] >>
  `k <= 2 ** ulog k /\ 2 ** ulog k < 2 * k` by metis_tac[ulog_thm] >>
  `2 <> 0` by decide_tac >>
  `n <= 2 * 2 ** ulog k` by rw[LE_MULT_LCANCEL] >>
  `2 * 2 ** ulog k < 2 * n` by rw[LT_MULT_LCANCEL] >>
  `2 * 2 ** ulog k = 2 ** (1 + ulog k)` by metis_tac[EXP, ADD1, ADD_COMM] >>
  metis_tac[ulog_unique]);

(* Theorem: 1 < n /\ ODD n ==> ulog (HALF n) + 1 <= ulog n *)
(* Proof:
   Let k = HALF n.
   Then 0 < k                                      by HALF_EQ_0, 1 < n
    and ODD n ==> n = TWICE k + 1                  by ODD_HALF
   Note        n <= 2 ** ulog n < 2 * n            by ulog_thm, by 0 < n
    and        k <= 2 ** ulog k < 2 * k            by ulog_thm, by 0 < k
    so     2 * k <= 2 * 2 ** ulog k < 2 * 2 * k    by multiplying 2
    or     (2 * k) <= 2 ** (1 + ulog k) < 2 * (2 * k)  by EXP
  Since    2 * k < n, so 2 * (2 * k) < 2 * n,
  the picture is:
           2 * k ... n ...... 2 * (2 * k) ... 2 * n
                       <---  2 ** ulog n ---->
                 <--- 2 ** (1 + ulog k) -->
  If n <= 2 ** (1 + ulog k), then ulog n = 1 + ulog k    by ulog_unique
  Otherwise, 2 ** (1 + ulog k) < 2 ** ulog n
         so         1 + ulog k < ulog n            by EXP_BASE_LT_MONO, 1 < 2
  Combining, 1 + ulog k <= ulog n.
*)
val ulog_odd = store_thm(
  "ulog_odd",
  ``!n. 1 < n /\ ODD n ==> ulog (HALF n) + 1 <= ulog n``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `(n <> 0) /\ (n <> 1)` by decide_tac >>
  `0 < n /\ 0 < k` by metis_tac[HALF_EQ_0, NOT_ZERO_LT_ZERO] >>
  `n = TWICE k + 1` by rw[ODD_HALF, Abbr`k`] >>
  `n <= 2 ** ulog n /\ 2 ** ulog n < 2 * n` by metis_tac[ulog_thm] >>
  `k <= 2 ** ulog k /\ 2 ** ulog k < 2 * k` by metis_tac[ulog_thm] >>
  `2 <> 0 /\ 1 < 2` by decide_tac >>
  `2 * k <= 2 * 2 ** ulog k` by rw[LE_MULT_LCANCEL] >>
  `2 * 2 ** ulog k < 2 * (2 * k)` by rw[LT_MULT_LCANCEL] >>
  `2 * 2 ** ulog k = 2 ** (1 + ulog k)` by metis_tac[EXP, ADD1, ADD_COMM] >>
  Cases_on `n <= 2 ** (1 + ulog k)` >| [
    `2 * k < n` by decide_tac >>
    `2 * (2 * k) < 2 * n` by rw[LT_MULT_LCANCEL] >>
    `2 ** (1 + ulog k) < TWICE n` by decide_tac >>
    `1 + ulog k = ulog n` by metis_tac[ulog_unique] >>
    decide_tac,
    `2 ** (1 + ulog k) < 2 ** ulog n` by decide_tac >>
    `1 + ulog k < ulog n` by metis_tac[EXP_BASE_LT_MONO] >>
    decide_tac
  ]);

(*
EVAL ``let n = 13 in [ulog (HALF n) + 1; ulog n]``;
|- (let n = 13 in [ulog (HALF n) + 1; ulog n]) = [4; 4]:
|- (let n = 17 in [ulog (HALF n) + 1; ulog n]) = [4; 5]:
*)

(* Theorem: 1 < n ==> ulog (HALF n) + 1 <= ulog n *)
(* Proof:
   Note 1 < n ==> 0 < n   by arithmetic
   If EVEN n, true        by ulog_even, 0 < n
   If ODD n, true         by ulog_odd, 1 < n, ODD_EVEN.
*)
val ulog_half = store_thm(
  "ulog_half",
  ``!n. 1 < n ==> ulog (HALF n) + 1 <= ulog n``,
  rpt strip_tac >>
  Cases_on `EVEN n` >-
  rw[ulog_even] >>
  rw[ODD_EVEN, ulog_odd]);

(* Theorem: SQRT n <= 2 ** (ulog n) *)
(* Proof:
   Note      n <= 2 ** ulog n     by ulog_property
    and SQRT n <= n               by SQRT_LE_SELF
   Thus SQRT n <= 2 ** ulog n     by LESS_EQ_TRANS
     or SQRT n <=
*)
val sqrt_upper = store_thm(
  "sqrt_upper",
  ``!n. SQRT n <= 2 ** (ulog n)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `n <= 2 ** ulog n` by rw[ulog_property] >>
  `SQRT n <= n` by rw[SQRT_LE_SELF] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Power Free up to a limit                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define a power free property of a number *)
val power_free_upto_def = Define`
    power_free_upto n k <=> !j. 1 < j /\ j <= k ==> (ROOT j n) ** j <> n
`;
(* make this an infix relation. *)
val _ = set_fixity "power_free_upto" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: (n power_free_upto 0) = T *)
(* Proof: by power_free_upto_def, no counter-example. *)
val power_free_upto_0 = store_thm(
  "power_free_upto_0",
  ``!n. (n power_free_upto 0) = T``,
  rw[power_free_upto_def]);

(* Theorem: (n power_free_upto 1) = T *)
(* Proof: by power_free_upto_def, no counter-example. *)
val power_free_upto_1 = store_thm(
  "power_free_upto_1",
  ``!n. (n power_free_upto 1) = T``,
  rw[power_free_upto_def]);

(* Theorem: 0 < k /\ (n power_free_upto k) ==>
            ((n power_free_upto (k + 1)) <=> ROOT (k + 1) n ** (k + 1) <> n) *)
(* Proof: by power_free_upto_def *)
val power_free_upto_suc = store_thm(
  "power_free_upto_suc",
  ``!n k. 0 < k /\ (n power_free_upto k) ==>
         ((n power_free_upto (k + 1)) <=> ROOT (k + 1) n ** (k + 1) <> n)``,
  rw[power_free_upto_def] >>
  rw[EQ_IMP_THM] >>
  metis_tac[LESS_OR_EQ, DECIDE``k < n + 1 ==> k <= n``]);

(* Theorem: ower_free n <=> 1 < n /\ n power_free_upto (LOG2 n) *)
(* Proof:
   By power_free_check_all and power_free_upto_def,
   this result is true if we can show that:
      1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n) <=>
      1 < n /\ (!j. 1 < j /\ j <= LOG2 n ==> (ROOT j n) ** j <> n)
   That is, to show that:
        1 < n /\ 1 < j /\ (!j. 1 < j /\ j <= LOG2 n ==> ROOT j n ** j <> n) ==> (ROOT j n) ** j <> n
   By contradiction, suppose (ROOT j n) ** j = n.
   Let m = ROOT j n.
   Then m ** j = n                       by above
   Thus perfect_power n m                by perfect_power_def
    ==> ?k. k <= LOG2 n /\ n = m ** k    by perfect_power_bound_LOG2
    But 1 < m                            by ONE_LT_EXP, 1 < n
   Thus j = k                            by EXP_BASE_INJECTIVE, 1 < m
   The implication gives m ** j <> n, a contradiction.
*)
val power_free_check_upto_LOG2 = store_thm(
  "power_free_check_upto_LOG2",
  ``!n. power_free n <=> 1 < n /\ n power_free_upto (LOG2 n)``,
  rw[power_free_check_all, power_free_upto_def] >>
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `m = ROOT j n` >>
  `perfect_power n m` by metis_tac[perfect_power_def] >>
  `?k. k <= LOG2 n /\ (n = m ** k)` by fs[GSYM perfect_power_bound_LOG2] >>
  `1 < m` by metis_tac[ONE_LT_EXP] >>
  `j = k` by fs[ ] >>
  metis_tac[]);

(* Theorem: power_free n <=> 1 < n /\ (!j. 1 < j /\ j <= ulog n ==> (ROOT j n) ** j <> n) *)
(* Proof:
   By power_free_check_all and power_free_upto_def,
   this result is true if we can show that:
        1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n) <=>
        1 < n /\ (!j. 1 < j /\ j <= ulog n ==> (ROOT j n) ** j <> n)
   That is, to show that:
        1 < n /\ 1 < j /\ (!j. 1 < j /\ j <= ulog n ==> ROOT j n ** j <> n) ==> (ROOT j n) ** j <> n
   By contradiction, suppose (ROOT j n) ** j = n.
   Let m = ROOT j n.
   Then m ** j = n                      by above
   Thus perfect_power n m               by perfect_power_def
    ==> ?k. k <= LOG2 n /\ n = m ** k   by perfect_power_bound_LOG2
    But 1 < m                           by ONE_LT_EXP, 1 < n
   Thus j = k                           by EXP_BASE_INJECTIVE, 1 < m
   Note LOG2 n <= ulog n                by ulog_LOG2, 0 < n
   Thus j <= ulog n                     by j = k, k <= LOG2 n, LOG2 n <= ulog n
   The implication gives m ** j <> n, a contradiction.
*)
val power_free_check_upto_ulog = store_thm(
  "power_free_check_upto_ulog",
  ``!n. power_free n <=> 1 < n /\ n power_free_upto (ulog n)``,
  rw[power_free_check_all, power_free_upto_def] >>
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `m = ROOT j n` >>
  `perfect_power n m` by metis_tac[perfect_power_def] >>
  `?k. k <= LOG2 n /\ (n = m ** k)` by fs[GSYM perfect_power_bound_LOG2] >>
  `1 < m` by metis_tac[ONE_LT_EXP] >>
  `j = k` by fs[EXP_BASE_INJECTIVE] >>
  `LOG2 n <= ulog n` by rw[ulog_LOG2] >>
  `j <= ulog n` by decide_tac >>
  metis_tac[]);

(* More general proof of the above assertions *)

(* Theorem: LOG2 n <= b ==> (power_free n <=> (1 < n /\ n power_free_upto b)) *)
(* Proof:
   If part: LOG2 n <= b /\ power_free n ==> 1 < n /\ n power_free_upto b
      (1) 1 < n,
          By contradiction, suppose n <= 1.
          Then n = 0, but power_free 0 = F      by power_free_0
            or n = 1, but power_free 1 = F      by power_free_1
      (2) n power_free_upto b,
          By power_free_upto_def, this is to show:
             1 < j /\ j <= b ==> ROOT j n ** j <> n
          By contradiction, suppose ROOT j n ** j = n.
          Then n = m ** j   where m = ROOT j n, with j <> 1.
          This contradicts power_free n         by power_free_def

   Only-if part: 1 < n /\ LOG2 n <= b /\ n power_free_upto b ==> power_free n
      By contradiction, suppose ~(power_free n).
      Then ?e. n = m ** e  with n = m ==> e <> 1   by power_free_def
       ==> perfect_power n m                    by perfect_power_def
      Thus ?k. k <= LOG2 n /\ (n = m ** k)      by perfect_power_bound_LOG2, 0 < n
       Now k <> 0                               by EXP_0, n <> 1
        so m = ROOT k n                         by ROOT_FROM_POWER, k <> 0

      Claim: k <> 1
      Proof: Note m <> 0                        by ROOT_EQ_0, n <> 0
              and m <> 1                        by EXP_1, k <> 0, n <> 1
              ==> 1 < m                         by m <> 0, m <> 1
             Thus n = m ** e = m ** k ==> k = e by EXP_BASE_INJECTIVE
              But e <> 1
                  since e = 1 ==> n <> m,       by n = m ==> e <> 1
                    yet n = m ** 1 ==> n = m    by EXP_1
             Since k = e, k <> 1.

      Therefore 1 < k                           by k <> 0, k <> 1
      and k <= LOG2 n /\ LOG2 n <= b ==> k <= b by arithmetic
      With 1 < k /\ k <= b /\ m = ROOT k n /\ m ** k = n,
      These will give a contradiction           by power_free_upto_def
*)
val power_free_check_upto = store_thm(
  "power_free_check_upto",
  ``!n b. LOG2 n <= b ==> (power_free n <=> (1 < n /\ n power_free_upto b))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `(n = 0) \/ (n = 1)` by decide_tac >-
    fs[power_free_0] >>
    fs[power_free_1],
    rw[power_free_upto_def] >>
    spose_not_then strip_assume_tac >>
    `j <> 1` by decide_tac >>
    metis_tac[power_free_def],
    simp[power_free_def] >>
    spose_not_then strip_assume_tac >>
    `perfect_power n m` by metis_tac[perfect_power_def] >>
    `0 < n /\ n <> 1` by decide_tac >>
    `?k. k <= LOG2 n /\ (n = m ** k)` by rw[GSYM perfect_power_bound_LOG2] >>
    `k <> 0` by metis_tac[EXP_0] >>
    `m = ROOT k n` by rw[ROOT_FROM_POWER] >>
    `k <> 1` by
  (`m <> 0` by rw[ROOT_EQ_0] >>
    `m <> 1 /\ e <> 1` by metis_tac[EXP_1] >>
    `1 < m` by decide_tac >>
    metis_tac[EXP_BASE_INJECTIVE]) >>
    `1 < k` by decide_tac >>
    `k <= b` by decide_tac >>
    metis_tac[power_free_upto_def]
  ]);

(* Theorem: power_free n <=> (1 < n /\ n power_free_upto LOG2 n) *)
(* Proof: by power_free_check_upto, LOG2 n <= LOG2 n *)
val power_free_check_upto_LOG2 = store_thm(
  "power_free_check_upto_LOG2",
  ``!n. power_free n <=> (1 < n /\ n power_free_upto LOG2 n)``,
  rw[power_free_check_upto]);

(* Theorem: power_free n <=> (1 < n /\ n power_free_upto ulog n) *)
(* Proof:
   If n = 0,
      LHS = power_free 0 = F        by power_free_0
          = RHS, as 1 < 0 = F
   If n <> 0,
      Then LOG2 n <= ulog n         by ulog_LOG2, 0 < n
      The result follows            by power_free_check_upto
*)
val power_free_check_upto_ulog = store_thm(
  "power_free_check_upto_ulog",
  ``!n. power_free n <=> (1 < n /\ n power_free_upto ulog n)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[power_free_0] >>
  rw[power_free_check_upto, ulog_LOG2]);

(* Theorem: power_free 2 *)
(* Proof:
       power_free 2
   <=> 2 power_free_upto (LOG2 2)   by power_free_check_upto_LOG2
   <=> 2 power_free_upto 1          by LOG2_2
   <=> T                            by power_free_upto_1
*)
val power_free_2 = store_thm(
  "power_free_2",
  ``power_free 2``,
  rw[power_free_check_upto_LOG2, power_free_upto_1]);

(* Theorem: power_free 3 *)
(* Proof:
   Note 3 power_free_upto 1         by power_free_upto_1
       power_free 3
   <=> 3 power_free_upto (ulog 3)   by power_free_check_upto_ulog
   <=> 3 power_free_upto 2          by evaluation
   <=> ROOT 2 3 ** 2 <> 3           by power_free_upto_suc, 0 < 1
   <=> T                            by evaluation
*)
val power_free_3 = store_thm(
  "power_free_3",
  ``power_free 3``,
  `3 power_free_upto 1` by rw[power_free_upto_1] >>
  `ulog 3 = 2` by EVAL_TAC >>
  `ROOT 2 3 ** 2 <> 3` by EVAL_TAC >>
  `power_free 3 <=> 3 power_free_upto 2` by rw[power_free_check_upto_ulog] >>
  metis_tac[power_free_upto_suc, DECIDE``0 < 1 /\ (1 + 1 = 2)``]);

(* Define a power free test, based on (ulog n), for computation. *)
val power_free_test_def = Define`
    power_free_test n <=>(1 < n /\ n power_free_upto (ulog n))
`;

(* Theorem: power_free_test n = power_free n *)
(* Proof: by power_free_test_def, power_free_check_upto_ulog *)
val power_free_test_eqn = store_thm(
  "power_free_test_eqn",
  ``!n. power_free_test n = power_free n``,
  rw[power_free_test_def, power_free_check_upto_ulog]);

(* Theorem: power_free n <=>
       (1 < n /\ !j. 1 < j /\ j <= (LOG2 n) ==> ROOT j n ** j <> n) *)
(* Proof: by power_free_check_upto_ulog, power_free_upto_def *)
val power_free_test_upto_LOG2 = store_thm(
  "power_free_test_upto_LOG2",
  ``!n. power_free n <=>
       (1 < n /\ !j. 1 < j /\ j <= (LOG2 n) ==> ROOT j n ** j <> n)``,
  rw[power_free_check_upto_LOG2, power_free_upto_def]);

(* Theorem: power_free n <=>
       (1 < n /\ !j. 1 < j /\ j <= (ulog n) ==> ROOT j n ** j <> n) *)
(* Proof: by power_free_check_upto_ulog, power_free_upto_def *)
val power_free_test_upto_ulog = store_thm(
  "power_free_test_upto_ulog",
  ``!n. power_free n <=>
       (1 < n /\ !j. 1 < j /\ j <= (ulog n) ==> ROOT j n ** j <> n)``,
  rw[power_free_check_upto_ulog, power_free_upto_def]);

(* ------------------------------------------------------------------------- *)
(* Another Characterisation of Power Free                                    *)
(* ------------------------------------------------------------------------- *)

(* Define power index of n, the highest index of n in power form by descending from k *)
val power_index_def = Define `
    power_index n k <=>
        if k <= 1 then 1
        else if (ROOT k n) ** k = n then k
        else power_index n (k - 1)
`;

(* Theorem: power_index n 0 = 1 *)
(* Proof: by power_index_def *)
val power_index_0 = store_thm(
  "power_index_0",
  ``!n. power_index n 0 = 1``,
  rw[Once power_index_def]);

(* Theorem: power_index n 1 = 1 *)
(* Proof: by power_index_def *)
val power_index_1 = store_thm(
  "power_index_1",
  ``!n. power_index n 1 = 1``,
  rw[Once power_index_def]);

(* Theorem: (ROOT (power_index n k) n) ** (power_index n k) = n *)
(* Proof:
   By induction on k.
   Base: ROOT (power_index n 0) n ** power_index n 0 = n
        ROOT (power_index n 0) n ** power_index n 0
      = (ROOT 1 n) ** 1          by power_index_0
      = n ** 1                   by ROOT_1
      = n                        by EXP_1
   Step: ROOT (power_index n k) n ** power_index n k = n ==>
         ROOT (power_index n (SUC k)) n ** power_index n (SUC k) = n
      If k = 0,
        ROOT (power_index n (SUC 0)) n ** power_index n (SUC 0)
      = ROOT (power_index n 1) n ** power_index n 1     by ONE
      = (ROOT 1 n) ** 1                                 by power_index_1
      = n ** 1                                          by ROOT_1
      = n                                               by EXP_1
      If k <> 0,
         Then ~(SUC k <= 1)                                     by 0 < k
         If ROOT (SUC k) n ** SUC k = n,
            Then power_index n (SUC k) = SUC k                  by power_index_def
              so ROOT (power_index n (SUC k)) n ** power_index n (SUC k)
               = ROOT (SUC k) n ** SUC k                        by above
               = n                                              by condition
         If ROOT (SUC k) n ** SUC k <> n,
            Then power_index n (SUC k) = power_index n k        by power_index_def
              so ROOT (power_index n (SUC k)) n ** power_index n (SUC k)
               = ROOT (power_index n k) n ** power_index n k    by above
               = n                                              by induction hypothesis
*)
val power_index_eqn = store_thm(
  "power_index_eqn",
  ``!n k. (ROOT (power_index n k) n) ** (power_index n k) = n``,
  rpt strip_tac >>
  Induct_on `k` >-
  rw[power_index_0] >>
  Cases_on `k = 0` >-
  rw[power_index_1] >>
  `~(SUC k <= 1)` by decide_tac >>
  rw_tac std_ss[Once power_index_def] >-
  rw[Once power_index_def] >>
  `power_index n (SUC k) = power_index n k` by rw[Once power_index_def] >>
  rw[]);

(* Theorem: perfect_power n (ROOT (power_index n k) n) *)
(* Proof:
   Let m = ROOT (power_index n k) n.
   By perfect_power_def, this is to show:
      ?e. n = m ** e
   Take e = power_index n k.
     m ** e
   = (ROOT (power_index n k) n) ** (power_index n k)     by root_compute_eqn
   = n                                                   by power_index_eqn
*)
val power_index_root = store_thm(
  "power_index_root",
  ``!n k. perfect_power n (ROOT (power_index n k) n)``,
  metis_tac[perfect_power_def, power_index_eqn]);

(* Theorem: power_index 1 k = if k = 0 then 1 else k *)
(* Proof:
   If k = 0,
      power_index 1 0 = 1               by power_index_0
   If k <> 0, then 0 < k.
      If k = 1,
         Then power_index 1 1 = 1 = k   by power_index_1
      If k <> 1, 1 < k.
         Note ROOT k 1 = 1              by ROOT_OF_1, 0 < k.
           so power_index 1 k = k       by power_index_def
*)
val power_index_of_1 = store_thm(
  "power_index_of_1",
  ``!k. power_index 1 k = if k = 0 then 1 else k``,
  rw[Once power_index_def]);

(* Theorem: 0 < k /\ ((ROOT k n) ** k = n) ==> (power_index n k = k) *)
(* Proof:
   If k = 1,
      True since power_index n 1 = 1      by power_index_1
   If k <> 1, then 1 < k                  by 0 < k
      True                                by power_index_def
*)
val power_index_exact_root = store_thm(
  "power_index_exact_root",
  ``!n k. 0 < k /\ ((ROOT k n) ** k = n) ==> (power_index n k = k)``,
  rpt strip_tac >>
  Cases_on `k = 1` >-
  rw[power_index_1] >>
  `1 < k` by decide_tac >>
  rw[Once power_index_def]);

(* Theorem: (ROOT k n) ** k <> n ==> (power_index n k = power_index n (k - 1)) *)
(* Proof:
   If k = 0,
      Then k = k - 1                  by k = 0
      Thus true trivially.
   If k = 1,
      Note power_index n 1 = 1        by power_index_1
       and power_index n 0 = 1        by power_index_0
      Thus true.
   If k <> 0 /\ k <> 1, then 1 < k    by arithmetic
      True                            by power_index_def
*)
val power_index_not_exact_root = store_thm(
  "power_index_not_exact_root",
  ``!n k. (ROOT k n) ** k <> n ==> (power_index n k = power_index n (k - 1))``,
  rpt strip_tac >>
  Cases_on `k = 0` >| [
    `k = k - 1` by decide_tac >>
    rw[],
    Cases_on `k = 1` >-
    rw[power_index_0, power_index_1] >>
    `1 < k` by decide_tac >>
    rw[Once power_index_def]
  ]);

(* Theorem: k <= m /\ (!j. k < j /\ j <= m ==> (ROOT j n) ** j <> n) ==> (power_index n m = power_index n k) *)
(* Proof:
   By induction on (m - k).
   Base: k <= m /\ 0 = m - k ==> power_index n m = power_index n k
      Note m <= k            by 0 = m - k
        so m = k             by k <= m
      Thus true trivially.
   Step: !m'. v = m' - k /\ k <= m' /\ ... ==> power_index n m' = power_index n k ==>
         SUC v = m - k ==> power_index n m = power_index n k
      If m = k, true trivially.
      If m <> k, then k < m.
         Thus k <= (m - 1), and v = (m - 1) - k.
         Note ROOT m n ** m <> n          by j = m in implication
         Thus power_index n m
            = power_index n (m - 1)       by power_index_not_exact_root
            = power_index n k             by induction hypothesis, m' = m - 1.
*)
val power_index_no_exact_roots = store_thm(
  "power_index_no_exact_roots",
  ``!m n k. k <= m /\ (!j. k < j /\ j <= m ==> (ROOT j n) ** j <> n) ==> (power_index n m = power_index n k)``,
  rpt strip_tac >>
  Induct_on `m - k` >| [
    rpt strip_tac >>
    `m = k` by decide_tac >>
    rw[],
    rpt strip_tac >>
    Cases_on `m = k` >-
    rw[] >>
    `ROOT m n ** m <> n` by rw[] >>
    `k <= m - 1` by decide_tac >>
    `power_index n (m - 1) = power_index n k` by rw[] >>
    rw[power_index_not_exact_root]
  ]);

(* The theorem power_index_equal requires a detective-style proof, based on these lemma. *)

(* Theorem: k <= m /\ ((ROOT k n) ** k = n) ==> k <= power_index n m *)
(* Proof:
   If k = 0,
      Then n = 1                          by EXP
      If m = 0,
         Then power_index 1 0 = 1         by power_index_of_1
          But k <= 0, so k = 0            by arithmetic
         Hence k <= power_index n m
      If m <> 0,
         Then power_index 1 m = m         by power_index_of_1
         Hence k <= power_index 1 m = m   by given

   If k <> 0, then 0 < k.
      Let s = {j | j <= m /\ ((ROOT j n) ** j = n)}
      Then s SUBSET (count (SUC m))       by SUBSET_DEF
       ==> FINITE s                       by SUBSET_FINITE, FINITE_COUNT
      Note k IN s                         by given
       ==> s <> {}                        by MEMBER_NOT_EMPTY
      Let t = MAX_SET s.

      Claim: !x. t < x /\ x <= m ==> (ROOT x n) ** x <> n
      Proof: By contradiction, suppose (ROOT x n) ** x = n
             Then x IN s, so x <= t       by MAX_SET_PROPERTY
             This contradicts t < x.

      Note t IN s                              by MAX_SET_IN_SET
        so t <= m /\ (ROOT t n) ** t = n       by above
      Thus power_index n m = power_index n t   by power_index_no_exact_roots, t <= m
       and power_index n t = t                 by power_index_exact_root, (ROOT t n) ** t = n
       But k <= t                              by MAX_SET_PROPERTY
      Thus k <= t = power_index n m
*)
val power_index_lower = store_thm(
  "power_index_lower",
  ``!m n k. k <= m /\ ((ROOT k n) ** k = n) ==> k <= power_index n m``,
  rpt strip_tac >>
  Cases_on `k = 0` >| [
    `n = 1` by fs[EXP] >>
    rw[power_index_of_1],
    `0 < k` by decide_tac >>
    qabbrev_tac `s = {j | j <= m /\ ((ROOT j n) ** j = n)}` >>
    `!j. j IN s <=> j <= m /\ ((ROOT j n) ** j = n)` by rw[Abbr`s`] >>
    `s SUBSET (count (SUC m))` by rw[SUBSET_DEF] >>
    `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
    `k IN s` by rw[] >>
    `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
    qabbrev_tac `t = MAX_SET s` >>
    `!x. t < x /\ x <= m ==> (ROOT x n) ** x <> n` by
  (spose_not_then strip_assume_tac >>
    `x IN s` by rw[] >>
    `x <= t` by rw[MAX_SET_PROPERTY, Abbr`t`] >>
    decide_tac) >>
    `t IN s` by rw[MAX_SET_IN_SET, Abbr`t`] >>
    `power_index n m = power_index n t` by metis_tac[power_index_no_exact_roots] >>
    `k <= t` by rw[MAX_SET_PROPERTY, Abbr`t`] >>
    `(ROOT t n) ** t = n` by metis_tac[] >>
    `power_index n t = t` by rw[power_index_exact_root] >>
    decide_tac
  ]);

(* Theorem: 0 < power_index n k *)
(* Proof:
   If k = 0,
      True since power_index n 0 = 1         by power_index_0
   If k <> 0,
      Then 1 <= k.
      Note (ROOT 1 n) ** 1 = n ** 1 = n      by ROOT_1, EXP_1
      Thus 1 <= power_index n k              by power_index_lower
        or 0 < power_index n k
*)
val power_index_pos = store_thm(
  "power_index_pos",
  ``!n k. 0 < power_index n k``,
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[power_index_0] >>
  `1 <= power_index n k` by rw[power_index_lower, EXP_1] >>
  decide_tac);

(* Theorem: 0 < k ==> power_index n k <= k *)
(* Proof:
   By induction on k.
   Base: 0 < 0 ==> power_index n 0 <= 0
      True by 0 < 0 = F.
   Step: 0 < k ==> power_index n k <= k ==>
         0 < SUC k ==> power_index n (SUC k) <= SUC k
      If k = 0,
         Then SUC k = 1                   by ONE
         True since power_index n 1 = 1   by power_index_1
      If k <> 0,
         Let m = SUC k, or k = m - 1.
         Then 1 < m                       by arithmetic
         If (ROOT m n) ** m = n,
            Then power_index n m
               = m <= m                   by power_index_exact_root
         If (ROOT m n) ** m <> n,
            Then power_index n m
               = power_index n (m - 1)    by power_index_not_exact_root
               = power_index n k          by m - 1 = k
               <= k                       by induction hypothesis
             But k < SUC k = m            by LESS_SUC
            Thus power_index n m < m      by LESS_EQ_LESS_TRANS
              or power_index n m <= m     by LESS_IMP_LESS_OR_EQ
*)
val power_index_upper = store_thm(
  "power_index_upper",
  ``!n k. 0 < k ==> power_index n k <= k``,
  strip_tac >>
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[power_index_1] >>
  `1 < SUC k` by decide_tac >>
  qabbrev_tac `m = SUC k` >>
  Cases_on `(ROOT m n) ** m = n` >-
  rw[power_index_exact_root] >>
  rw[power_index_not_exact_root, Abbr`m`]);

(* Theorem: 0 < k /\ k <= m ==>
            ((power_index n m = power_index n k) <=> (!j. k < j /\ j <= m ==> (ROOT j n) ** j <> n)) *)
(* Proof:
   If part: 0 < k /\ k <= m /\ power_index n m = power_index n k /\ k < j /\ j <= m ==> ROOT j n ** j <> n
      By contradiction, suppose ROOT j n ** j = n.
      Then j <= power_index n m      by power_index_lower
      But       power_index n k <= k by power_index_upper, 0 < k
      Thus j <= k                    by LESS_EQ_TRANS
      This contradicts k < j.
   Only-if part: 0 < k /\ k <= m /\ !j. k < j /\ j <= m ==> ROOT j n ** j <> n ==>
                 power_index n m = power_index n k
      True by power_index_no_exact_roots
*)
val power_index_equal = store_thm(
  "power_index_equal",
  ``!m n k. 0 < k /\ k <= m ==>
    ((power_index n m = power_index n k) <=> (!j. k < j /\ j <= m ==> (ROOT j n) ** j <> n))``,
  rpt strip_tac >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `j <= power_index n m` by rw[power_index_lower] >>
    `power_index n k <= k` by rw[power_index_upper] >>
    decide_tac,
    rw[power_index_no_exact_roots]
  ]);

(* Theorem: (power_index n m = k) ==> !j. k < j /\ j <= m ==> (ROOT j n) ** j <> n *)
(* Proof:
   By contradiction, suppose k < j /\ j <= m /\ (ROOT j n) ** j = n.
   Then j <= power_index n m                   by power_index_lower
   This contradicts power_index n m = k < j    by given
*)
val power_index_property = store_thm(
  "power_index_property",
  ``!m n k. (power_index n m = k) ==> !j. k < j /\ j <= m ==> (ROOT j n) ** j <> n``,
  spose_not_then strip_assume_tac >>
  `j <= power_index n m` by rw[power_index_lower] >>
  decide_tac);

(* Theorem: power_free n <=> (1 < n) /\ (power_index n (LOG2 n) = 1) *)
(* Proof:
   By power_free_check_upto_LOG2, power_free_upto_def, this is to show:
      1 < n /\ (!j. 1 < j /\ j <= LOG2 n ==> ROOT j n ** j <> n) <=>
      1 < n /\ (power_index n (LOG2 n) = 1)
   If part:
      Note 0 < LOG2 n              by LOG2_POS, 1 < n
           power_index n (LOG2 n)
         = power_index n 1         by power_index_no_exact_roots, 1 <= LOG2 n
         = 1                       by power_index_1
   Only-if part, true              by power_index_property
*)
val power_free_by_power_index_LOG2 = store_thm(
  "power_free_by_power_index_LOG2",
  ``!n. power_free n <=> (1 < n) /\ (power_index n (LOG2 n) = 1)``,
  rw[power_free_check_upto_LOG2, power_free_upto_def] >>
  rw[EQ_IMP_THM] >| [
    `0 < LOG2 n` by rw[] >>
    `1 <= LOG2 n` by decide_tac >>
    `power_index n (LOG2 n) = power_index n 1` by rw[power_index_no_exact_roots] >>
    rw[power_index_1],
    metis_tac[power_index_property]
  ]);

(* Theorem: power_free n <=> (1 < n) /\ (power_index n (ulog n) = 1) *)
(* Proof:
   By power_free_check_upto_ulog, power_free_upto_def, this is to show:
      1 < n /\ (!j. 1 < j /\ j <= ulog n ==> ROOT j n ** j <> n) <=>
      1 < n /\ (power_index n (ulog n) = 1)
   If part:
      Note 0 < ulog n              by ulog_POS, 1 < n
           power_index n (ulog n)
         = power_index n 1         by power_index_no_exact_roots, 1 <= ulog n
         = 1                       by power_index_1
   Only-if part, true              by power_index_property
*)
val power_free_by_power_index_ulog = store_thm(
  "power_free_by_power_index_ulog",
  ``!n. power_free n <=> (1 < n) /\ (power_index n (ulog n) = 1)``,
  rw[power_free_check_upto_ulog, power_free_upto_def] >>
  rw[EQ_IMP_THM] >| [
    `0 < ulog n` by rw[] >>
    `1 <= ulog n` by decide_tac >>
    `power_index n (ulog n) = power_index n 1` by rw[power_index_no_exact_roots] >>
    rw[power_index_1],
    metis_tac[power_index_property]
  ]);

(* ------------------------------------------------------------------------- *)
(* Primality Tests Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(*

   Two Factors Properties:
   two_factors_property_1  |- !n a b. (n = a * b) /\ a < SQRT n ==> SQRT n <= b
   two_factors_property_2  |- !n a b. (n = a * b) /\ SQRT n < a ==> b <= SQRT n
   two_factors_property    |- !n a b. (n = a * b) ==> a <= SQRT n \/ b <= SQRT n

   Primality or Compositeness based on SQRT:
   prime_by_sqrt_factors  |- !p. prime p <=>
                                 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p)
   prime_factor_estimate  |- !n. 1 < n ==>
                                 (~prime n <=> ?p. prime p /\ p divides n /\ p <= SQRT n)

   Primality Testing Algorithm:
   factor_seek_def     |- !q n c. factor_seek n c q =
                                  if c <= q then n
                                  else if 1 < q /\ (n MOD q = 0) then q
                                  else factor_seek n c (q + 1)
   prime_test_def      |- !n. prime_test n <=>
                              if n <= 1 then F else factor_seek n (1 + SQRT n) 2 = n
   factor_seek_bound   |- !n c q. 0 < n ==> factor_seek n c q <= n
   factor_seek_thm     |- !n c q. 1 < q /\ q <= c /\ c <= n ==>
                          (factor_seek n c q = n <=> !p. q <= p /\ p < c ==> ~(p divides n))
   prime_test_thm      |- !n. prime n <=> prime_test n

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Two Factors Properties                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (n = a * b) /\ a < SQRT n ==> SQRT n <= b *)
(* Proof:
   If n = 0, then a = 0 or b = 0          by MULT_EQ_0
   But SQRT 0 = 0                         by SQRT_0
   so a <> 0, making b = 0, and SQRT n <= b true.
   If n <> 0, a <> 0 and b <> 0           by MULT_EQ_0
   By contradiction, suppose b < SQRT n.
   Then  n = a * b < a * SQRT n           by LT_MULT_LCANCEL, 0 < a.
    and a * SQRT n < SQRT n * SQRT n      by LT_MULT_RCANCEL, 0 < SQRT n.
   making  n < (SQRT n) ** 2              by LESS_TRANS, EXP_2
   This contradicts (SQRT n) ** 2 <= n    by SQRT_PROPERTY
*)
val two_factors_property_1 = store_thm(
  "two_factors_property_1",
  ``!n a b. (n = a * b) /\ a < SQRT n ==> SQRT n <= b``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `a <> 0 /\ (b = 0) /\ (SQRT n = 0)` by metis_tac[MULT_EQ_0, SQRT_0, DECIDE``~(0 < 0)``] >>
    decide_tac,
    `a <> 0 /\ b <> 0` by metis_tac[MULT_EQ_0] >>
    spose_not_then strip_assume_tac >>
    `b < SQRT n` by decide_tac >>
    `0 < a /\ 0 < b /\ 0 < SQRT n` by decide_tac >>
    `n < a * SQRT n` by rw[] >>
    `a * SQRT n < SQRT n * SQRT n` by rw[] >>
    `n < (SQRT n) ** 2` by metis_tac[LESS_TRANS, EXP_2] >>
    `(SQRT n) ** 2 <= n` by rw[SQRT_PROPERTY] >>
    decide_tac
  ]);

(* Theorem: (n = a * b) /\ SQRT n < a ==> b <= SQRT n *)
(* Proof:
   If n = 0, then a = 0 or b = 0             by MULT_EQ_0
   But SQRT 0 = 0                            by SQRT_0
   so a <> 0, making b = 0, and b <= SQRT n true.
   If n <> 0, a <> 0 and b <> 0              by MULT_EQ_0
   By contradiction, suppose SQRT n < b.
   Then SUC (SQRT n) ** 2
      = SUC (SQRT n) * SUC (SQRT n)          by EXP_2
      <= a * SUC (SQRT n)                    by LT_MULT_RCANCEL, 0 < SUC (SQRT n).
      <= a * b = n                           by LT_MULT_LCANCEL, 0 < a.
   Giving (SUC (SQRT n)) ** 2 <= n           by LESS_EQ_TRANS
   or SQRT ((SUC (SQRT n)) ** 2) <= SQRT n   by SQRT_LE
   or       SUC (SQRT n) <= SQRT n           by SQRT_OF_SQ
   which is a contradiction to !m. SUC m > m by LESS_SUC_REFL
 *)
val two_factors_property_2 = store_thm(
  "two_factors_property_2",
  ``!n a b. (n = a * b) /\ SQRT n < a ==> b <= SQRT n``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `a <> 0 /\ (b = 0) /\ (SQRT 0 = 0)` by metis_tac[MULT_EQ_0, SQRT_0, DECIDE``~(0 < 0)``] >>
    decide_tac,
    `a <> 0 /\ b <> 0` by metis_tac[MULT_EQ_0] >>
    spose_not_then strip_assume_tac >>
    `SQRT n < b` by decide_tac >>
    `SUC (SQRT n) <= a /\ SUC (SQRT n) <= b` by decide_tac >>
    `SUC (SQRT n) * SUC (SQRT n) <= a * SUC (SQRT n)` by rw[] >>
    `a * SUC (SQRT n) <= n` by rw[] >>
    `SUC (SQRT n) ** 2  <= n` by metis_tac[LESS_EQ_TRANS, EXP_2] >>
    `SUC (SQRT n) <= SQRT n` by metis_tac[SQRT_LE, SQRT_OF_SQ] >>
    decide_tac
  ]);

(* Theorem: (n = a * b) ==> a <= SQRT n \/ b <= SQRT n *)
(* Proof:
   By contradiction, suppose SQRT n < a /\ SQRT n < b.
   Then (n = a * b) /\ SQRT n < a ==> b <= SQRT n  by two_factors_property_2
   which contradicts SQRT n < b.
 *)
val two_factors_property = store_thm(
  "two_factors_property",
  ``!n a b. (n = a * b) ==> a <= SQRT n \/ b <= SQRT n``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `SQRT n < a` by decide_tac >>
  metis_tac[two_factors_property_2]);

(* ------------------------------------------------------------------------- *)
(* Primality or Compositeness based on SQRT                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p <=> 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p) *)
(* Proof:
   If part: prime p ==> 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p)
     First one: prime p ==> 1 < p  is true    by ONE_LT_PRIME
     Second one: by contradiction, suppose q divides p.
     But prime p /\ q divides p ==> (q = p) or (q = 1)  by prime_def
     Given 1 < q, q <> 1, hence q = p.
     This means p <= SQRT p, giving p = 0 or p = 1      by SQRT_GE_SELF
     which contradicts p <> 0 and p <> 1                by PRIME_POS, prime_def
   Only-if part: 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p) ==> prime p
     By prime_def, this is to show:
     (1) p <> 1, true since 1 < p.
     (2) b divides p ==> (b = p) \/ (b = 1)
         By contradiction, suppose b <> p /\ b <> 1.
         b divides p ==> ?a. p = a * b     by divides_def
         which means a <= SQRT p \/ b <= SQRT p   by two_factors_property
         If a <= SQRT p,
         1 < p ==> p <> 0, so a <> 0  by MULT
         also b <> p ==> a <> 1       by MULT_LEFT_1
         so 1 < a, and a divides p    by prime_def, MULT_COMM
         The implication gives ~(a divides p), a contradiction.
         If b <= SQRT p,
         1 < p ==> p <> 0, so b <> 0  by MULT_0
         also b <> 1, so 1 < b, and b divides p.
         The implication gives ~(b divides p), a contradiction.
 *)
val prime_by_sqrt_factors = store_thm(
  "prime_by_sqrt_factors",
  ``!p. prime p <=> 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p)``,
  rw[EQ_IMP_THM] >-
  rw[ONE_LT_PRIME] >-
 (spose_not_then strip_assume_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `p <> 0 /\ q <> 1` by decide_tac >>
  `(q = p) /\ p <> 1` by metis_tac[prime_def] >>
  metis_tac[SQRT_GE_SELF]) >>
  rw[prime_def] >>
  spose_not_then strip_assume_tac >>
  `?a. p = a * b` by rw[GSYM divides_def] >>
  `a <= SQRT p \/ b <= SQRT p` by rw[two_factors_property] >| [
    `a <> 1` by metis_tac[MULT_LEFT_1] >>
    `p <> 0` by decide_tac >>
    `a <> 0` by metis_tac[MULT] >>
    `1 < a` by decide_tac >>
    metis_tac[divides_def, MULT_COMM],
    `p <> 0` by decide_tac >>
    `b <> 0` by metis_tac[MULT_0] >>
    `1 < b` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: 1 < n ==> (~prime n <=> ?p. prime p /\ p divides n /\ p <= SQRT n) *)
(* Proof:
   If part ~prime n ==> ?p. prime p /\ p divides n /\ p <= SQRT n
   Given n <> 1, ?p. prime p /\ p divides n  by PRIME_FACTOR
   If p <= SQRT n, take this p.
   If ~(p <= SQRT n), SQRT n < p.
      Since p divides n, ?q. n = p * q       by divides_def, MULT_COMM
      Hence q <= SQRT n                      by two_factors_property_2
      Since prime p but ~prime n, q <> 1     by MULT_RIGHT_1
         so ?t. prime t /\ t divides q       by PRIME_FACTOR
      Since 1 < n, n <> 0, so q <> 0         by MULT_0
         so t divides q ==> t <= q           by DIVIDES_LE, 0 < q.
      Take t, then t divides n               by DIVIDES_TRANS
               and t <= SQRT n               by LESS_EQ_TRANS
    Only-if part: ?p. prime p /\ p divides n /\ p <= SQRT n ==> ~prime n
      By contradiction, assume prime n.
      Then p divides n ==> p = 1 or p = n    by prime_def
      But prime p ==> p <> 1, so p = n       by ONE_LT_PRIME
      Giving p <= SQRT p,
      thus forcing p = 0 or p = 1            by SQRT_GE_SELF
      Both are impossible for prime p.
*)
val prime_factor_estimate = store_thm(
  "prime_factor_estimate",
  ``!n. 1 < n ==> (~prime n <=> ?p. prime p /\ p divides n /\ p <= SQRT n)``,
  rpt strip_tac >>
  `n <> 1` by decide_tac >>
  rw[EQ_IMP_THM] >| [
    `?p. prime p /\ p divides n` by rw[PRIME_FACTOR] >>
    Cases_on `p <= SQRT n` >-
    metis_tac[] >>
    `SQRT n < p` by decide_tac >>
    `?q. n = q * p` by rw[GSYM divides_def] >>
    `_ = p * q` by rw[MULT_COMM] >>
    `q <= SQRT n` by metis_tac[two_factors_property_2] >>
    `q <> 1` by metis_tac[MULT_RIGHT_1] >>
    `?t. prime t /\ t divides q` by rw[PRIME_FACTOR] >>
    `n <> 0` by decide_tac >>
    `q <> 0` by metis_tac[MULT_0] >>
    `0 < q ` by decide_tac >>
    `t <= q` by rw[DIVIDES_LE] >>
    `q divides n` by metis_tac[divides_def] >>
    metis_tac[DIVIDES_TRANS, LESS_EQ_TRANS],
    spose_not_then strip_assume_tac >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `p <> 1 /\ p <> 0` by decide_tac >>
    `p = n` by metis_tac[prime_def] >>
    metis_tac[SQRT_GE_SELF]
  ]);

(* ------------------------------------------------------------------------- *)
(* Primality Testing Algorithm                                               *)
(* ------------------------------------------------------------------------- *)

(* Seek the prime factor of number n, starting with q, up to cutoff c. *)
val factor_seek_def = tDefine "factor_seek" `
  factor_seek n c q =
    if c <= q then n
    else if 1 < q /\ (n MOD q = 0) then q
    else factor_seek n c (q + 1)
`(WF_REL_TAC `measure (\(n,c,q). c - q)` >> simp[]);
(* Use 1 < q so that, for prime n, it gives a result n for any initial q, including q = 1. *)

(* Primality test by seeking a factor exceeding (SQRT n). *)
val prime_test_def = Define`
    prime_test n =
       if n <= 1 then F
       else factor_seek n (1 + SQRT n) 2 = n
`;

(*
EVAL ``MAP prime_test [1 .. 15]``; = [F; T; T; F; T; F; T; F; F; F; T; F; T; F; F]: thm
*)

(* Theorem: 0 < n ==> factor_seek n c q <= n *)
(* Proof:
   By induction from factor_seek_def.
   If c <= q,
      Then factor_seek n c q = n, hence true    by factor_seek_def
   If q = 0,
      Then factor_seek n c 0 = 0, hence true    by factor_seek_def
   If n MOD q = 0,
      Then factor_seek n c q = q                by factor_seek_def
      Thus q divides n                          by DIVIDES_MOD_0, q <> 0
      hence q <= n                              by DIVIDES_LE, 0 < n
   Otherwise,
         factor_seek n c q
       = factor_seek n c (q + 1)                by factor_seek_def
      <= n                                      by induction hypothesis
*)
val factor_seek_bound = store_thm(
  "factor_seek_bound",
  ``!n c q. 0 < n ==> factor_seek n c q <= n``,
  ho_match_mp_tac (theorem "factor_seek_ind") >>
  rw[] >>
  rw[Once factor_seek_def] >>
  `q divides n` by rw[DIVIDES_MOD_0] >>
  rw[DIVIDES_LE]);

(* Theorem: 1 < q /\ q <= c /\ c <= n ==>
   ((factor_seek n c q = n) <=> (!p. q <= p /\ p < c ==> ~(p divides n))) *)
(* Proof:
   By induction from factor_seek_def, this is to show:
   (1) n MOD q = 0 ==> ?p. (q <= p /\ p < c) /\ p divides n
       Take p = q, then n MOD q = 0 ==> q divides n       by DIVIDES_MOD_0, 0 < q
   (2) n MOD q <> 0 ==> factor_seek n c (q + 1) = n <=>
                        !p. q <= p /\ p < c ==> ~(p divides n)
            factor_seek n c (q + 1) = n
        <=> !p. q + 1 <= p /\ p < c ==> ~(p divides n))   by induction hypothesis
         or !p.      q < p /\ p < c ==> ~(p divides n))
        But n MOD q <> 0 gives ~(q divides n)             by DIVIDES_MOD_0, 0 < q
       Thus !p.     q <= p /\ p < c ==> ~(p divides n))
*)
val factor_seek_thm = store_thm(
  "factor_seek_thm",
  ``!n c q. 1 < q /\ q <= c /\ c <= n ==>
   ((factor_seek n c q = n) <=> (!p. q <= p /\ p < c ==> ~(p divides n)))``,
  ho_match_mp_tac (theorem "factor_seek_ind") >>
  rw[] >>
  rw[Once factor_seek_def] >| [
    qexists_tac `q` >>
    rw[DIVIDES_MOD_0],
    rw[EQ_IMP_THM] >>
    spose_not_then strip_assume_tac >>
    `0 < q` by decide_tac >>
    `p <> q` by metis_tac[DIVIDES_MOD_0] >>
    `q + 1 <= p` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: prime n = prime_test n *)
(* Proof:
       prime n
   <=> 1 < n /\ !q. 1 < q /\ n <= SQRT n ==> ~(n divides p)     by prime_by_sqrt_factors
   <=> 1 < n /\ !q. 2 <= q /\ n < c ==> ~(n divides p)          where c = 1 + SQRT n
   Under 1 < n,
   Note SQRT n <> 0         by SQRT_EQ_0, n <> 0
     so 1 < 1 + SQRT n = c, or 2 <= c.
   Also SQRT n <= n         by SQRT_LE_SELF
    but SQRT n <> n         by SQRT_EQ_SELF, 1 < n
     so SQRT n < n, or c <= n.
   Thus 1 < n /\ !q. 2 <= q /\ n < c ==> ~(n divides p)
    <=> factor_seek n c q = n                              by factor_seek_thm
    <=> prime_test n                                       by prime_test_def
*)
val prime_test_thm = store_thm(
  "prime_test_thm",
  ``!n. prime n = prime_test n``,
  rw[prime_test_def, prime_by_sqrt_factors] >>
  rw[EQ_IMP_THM] >| [
    qabbrev_tac `c = SQRT n + 1` >>
    `0 < 2` by decide_tac >>
    `SQRT n <> 0` by rw[SQRT_EQ_0] >>
    `2 <= c` by rw[Abbr`c`] >>
    `SQRT n <= n` by rw[SQRT_LE_SELF] >>
    `SQRT n <> n` by rw[SQRT_EQ_SELF] >>
    `c <= n` by rw[Abbr`c`] >>
    `!q. 2 <= q /\ q < c ==> ~(q divides n)` by fs[Abbr`c`] >>
    rw[factor_seek_thm],
    qabbrev_tac `c = SQRT n + 1` >>
    `0 < 2` by decide_tac >>
    `SQRT n <> 0` by rw[SQRT_EQ_0] >>
    `2 <= c` by rw[Abbr`c`] >>
    `SQRT n <= n` by rw[SQRT_LE_SELF] >>
    `SQRT n <> n` by rw[SQRT_EQ_SELF] >>
    `c <= n` by rw[Abbr`c`] >>
    fs[factor_seek_thm] >>
    `!p. 1 < p /\ p <= SQRT n ==> ~(p divides n)` by fs[Abbr`c`] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Prime Power Documentation                                                 *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   ppidx n                     = prime_power_index p n
   common_prime_divisors m n   = (prime_divisors m) INTER (prime_divisors n)
   total_prime_divisors m n    = (prime_divisors m) UNION (prime_divisors n)
   park_on m n                 = {p | p IN common_prime_divisors m n /\ ppidx m <= ppidx n}
   park_off m n                = {p | p IN common_prime_divisors m n /\ ppidx n < ppidx m}
   park m n                    = PROD_SET (IMAGE (\p. p ** ppidx m) (park_on m n))
*)
(* Definitions and Theorems (# are exported):

   Helper Theorem:
   self_to_log_index_member       |- !n x. MEM x [1 .. n] ==> MEM (x ** LOG x n) [1 .. n]

   Prime Power or Coprime Factors:
   prime_power_or_coprime_factors    |- !n. 1 < n ==> (?p k. 0 < k /\ prime p /\ (n = p ** k)) \/
                                        ?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ 1 < b /\ a < n /\ b < n
   non_prime_power_coprime_factors   |- !n. 1 < n /\ ~(?p k. 0 < k /\ prime p /\ (n = p ** k)) ==>
                                        ?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ a < n /\ 1 < b /\ b < n
   pairwise_coprime_for_prime_powers |- !s f. s SUBSET prime ==> PAIRWISE_COPRIME (IMAGE (\p. p ** f p) s)

   Prime Power Index:
   prime_power_index_exists       |- !n p. 0 < n /\ prime p ==> ?m. p ** m divides n /\ coprime p (n DIV p ** m)
   prime_power_index_def          |- !p n. 0 < n /\ prime p ==>
                                           p ** ppidx n divides n /\ coprime p (n DIV p ** ppidx n)
   prime_power_factor_divides     |- !n p. prime p ==> p ** ppidx n divides n
   prime_power_cofactor_coprime   |- !n p. 0 < n /\ prime p ==> coprime p (n DIV p ** ppidx n)
   prime_power_eqn                |- !n p. 0 < n /\ prime p ==> (n = p ** ppidx n * (n DIV p ** ppidx n))
   prime_power_divisibility       |- !n p. 0 < n /\ prime p ==> !k. p ** k divides n <=> k <= ppidx n
   prime_power_index_maximal      |- !n p. 0 < n /\ prime p ==> !k. k > ppidx n ==> ~(p ** k divides n)
   prime_power_index_of_divisor   |- !m n. 0 < n /\ m divides n ==> !p. prime p ==> ppidx m <= ppidx n
   prime_power_index_test         |- !n p. 0 < n /\ prime p ==>
                                     !k. (k = ppidx n) <=> ?q. (n = p ** k * q) /\ coprime p q:
   prime_power_index_1            |- !p. prime p ==> (ppidx 1 = 0)
   prime_power_index_eq_0         |- !n p. 0 < n /\ prime p /\ ~(p divides n) ==> (ppidx n = 0)
   prime_power_index_prime_power  |- !p. prime p ==> !k. ppidx (p ** k) = k
   prime_power_index_prime        |- !p. prime p ==> (ppidx p = 1)
   prime_power_index_eqn          |- !n p. 0 < n /\ prime p ==> (let q = n DIV p ** ppidx n in
                                                         (n = p ** ppidx n * q) /\ coprime p q)
   prime_power_index_pos          |- !n p. 0 < n /\ prime p /\ p divides n ==> 0 < ppidx n

   Prime Power and GCD, LCM:
   gcd_prime_power_factor       |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                        (gcd a b = p ** MIN (ppidx a) (ppidx b) * gcd (a DIV p ** ppidx a) (b DIV p ** ppidx b))
   gcd_prime_power_factor_divides_gcd
                                |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           p ** MIN (ppidx a) (ppidx b) divides gcd a b
   gcd_prime_power_cofactor_coprime
                                |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           coprime p (gcd (a DIV p ** ppidx a) (b DIV p ** ppidx b))
   gcd_prime_power_index        |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           (ppidx (gcd a b) = MIN (ppidx a) (ppidx b))
   gcd_prime_power_divisibility |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                   !k. p ** k divides gcd a b ==> k <= MIN (ppidx a) (ppidx b)

   lcm_prime_power_factor       |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
       (lcm a b = p ** MAX (ppidx a) (ppidx b) * lcm (a DIV p ** ppidx a) (b DIV p ** ppidx b))
   lcm_prime_power_factor_divides_lcm
                                |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           p ** MAX (ppidx a) (ppidx b) divides lcm a b
   lcm_prime_power_cofactor_coprime
                                |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           coprime p (lcm (a DIV p ** ppidx a) (b DIV p ** ppidx b))
   lcm_prime_power_index        |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           (ppidx (lcm a b) = MAX (ppidx a) (ppidx b))
   lcm_prime_power_divisibility |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                   !k. p ** k divides lcm a b ==> k <= MAX (ppidx a) (ppidx b)

   Prime Powers and List LCM:
   list_lcm_prime_power_factor_divides   |- !l p. prime p ==> p ** MAX_LIST (MAP ppidx l) divides list_lcm l
   list_lcm_prime_power_index            |- !l p. prime p /\ POSITIVE l ==>
                                                  (ppidx (list_lcm l) = MAX_LIST (MAP ppidx l))
   list_lcm_prime_power_divisibility     |- !l p. prime p /\ POSITIVE l ==>
                                            !k. p ** k divides list_lcm l ==> k <= MAX_LIST (MAP ppidx l)
   list_lcm_prime_power_factor_member    |- !l p. prime p /\ l <> [] /\ POSITIVE l ==>
                                            !k. p ** k divides list_lcm l ==> ?x. MEM x l /\ p ** k divides x
   lcm_special_for_prime_power       |- !p. prime p ==> !m n. (n = p ** SUC (ppidx m)) ==> (lcm n m = p * m)
   lcm_special_for_coprime_factors   |- !n a b. (n = a * b) /\ coprime a b ==>
                                        !m. a divides m /\ b divides m ==> (lcm n m = m)

   Prime Divisors:
   prime_divisors_def            |- !n. prime_divisors n = {p | prime p /\ p divides n}
   prime_divisors_element        |- !n p. p IN prime_divisors n <=> prime p /\ p divides n
   prime_divisors_subset_natural |- !n. 0 < n ==> prime_divisors n SUBSET natural n
   prime_divisors_finite         |- !n. 0 < n ==> FINITE (prime_divisors n)
   prime_divisors_0              |- prime_divisors 0 = prime
   prime_divisors_1              |- prime_divisors 1 = {}
   prime_divisors_subset_prime   |- !n. prime_divisors n SUBSET prime
   prime_divisors_nonempty       |- !n. 1 < n ==> prime_divisors n <> {}
   prime_divisors_empty_iff      |- !n. (prime_divisors n = {}) <=> (n = 1)
   prime_divisors_0_not_sing     |- ~SING (prime_divisors 0)
   prime_divisors_prime          |- !n. prime n ==> (prime_divisors n = {n})
   prime_divisors_prime_power    |- !n. prime n ==> !k. 0 < k ==> (prime_divisors (n ** k) = {n})
   prime_divisors_sing           |- !n. SING (prime_divisors n) <=> ?p k. prime p /\ 0 < k /\ (n = p ** k)
   prime_divisors_sing_alt       |- !n p. (prime_divisors n = {p}) <=> ?k. prime p /\ 0 < k /\ (n = p ** k)
   prime_divisors_sing_property  |- !n. SING (prime_divisors n) ==> (let p = CHOICE (prime_divisors n) in
                                        prime p /\ (n = p ** ppidx n))
   prime_divisors_divisor_subset     |- !m n. m divides n ==> prime_divisors m SUBSET prime_divisors n
   prime_divisors_common_divisor     |- !n m x. x divides m /\ x divides n ==>
                                         prime_divisors x SUBSET prime_divisors m INTER prime_divisors n
   prime_divisors_common_multiple    |- !n m x. m divides x /\ n divides x ==>
                                         prime_divisors m UNION prime_divisors n SUBSET prime_divisors x
   prime_power_index_common_divisor  |- !n m x. 0 < m /\ 0 < n /\ x divides m /\ x divides n ==>
                                        !p. prime p ==> ppidx x <= MIN (ppidx m) (ppidx n)
   prime_power_index_common_multiple |- !n m x. 0 < x /\ m divides x /\ n divides x ==>
                                        !p. prime p ==> MAX (ppidx m) (ppidx n) <= ppidx x
   prime_power_index_le_log_index    |- !n p. 0 < n /\ prime p ==> ppidx n <= LOG p n

   Prime-related Sets:
   primes_upto_def                |- !n. primes_upto n = {p | prime p /\ p <= n}
   prime_powers_upto_def          |- !n. prime_powers_upto n = IMAGE (\p. p ** LOG p n) (primes_upto n)
   prime_power_divisors_def       |- !n. prime_power_divisors n = IMAGE (\p. p ** ppidx n) (prime_divisors n)

   primes_upto_element            |- !n p. p IN primes_upto n <=> prime p /\ p <= n
   primes_upto_subset_natural     |- !n. primes_upto n SUBSET natural n
   primes_upto_finite             |- !n. FINITE (primes_upto n)
   primes_upto_pairwise_coprime   |- !n. PAIRWISE_COPRIME (primes_upto n)
   primes_upto_0                  |- primes_upto 0 = {}
   primes_count_0                 |- primes_count 0 = 0
   primes_upto_1                  |- primes_upto 1 = {}
   primes_count_1                 |- primes_count 1 = 0

   prime_powers_upto_element      |- !n x. x IN prime_powers_upto n <=>
                                           ?p. (x = p ** LOG p n) /\ prime p /\ p <= n
   prime_powers_upto_element_alt  |- !p n. prime p /\ p <= n ==> p ** LOG p n IN prime_powers_upto n
   prime_powers_upto_finite       |- !n. FINITE (prime_powers_upto n)
   prime_powers_upto_pairwise_coprime  |- !n. PAIRWISE_COPRIME (prime_powers_upto n)
   prime_powers_upto_0            |- prime_powers_upto 0 = {}
   prime_powers_upto_1            |- prime_powers_upto 1 = {}

   prime_power_divisors_element   |- !n x. x IN prime_power_divisors n <=>
                                           ?p. (x = p ** ppidx n) /\ prime p /\ p divides n
   prime_power_divisors_element_alt |- !p n. prime p /\ p divides n ==>
                                             p ** ppidx n IN prime_power_divisors n
   prime_power_divisors_finite      |- !n. 0 < n ==> FINITE (prime_power_divisors n)
   prime_power_divisors_pairwise_coprime  |- !n. PAIRWISE_COPRIME (prime_power_divisors n)
   prime_power_divisors_1         |- prime_power_divisors 1 = {}

   Factorisations:
   prime_factorisation          |- !n. 0 < n ==> (n = PROD_SET (prime_power_divisors n))
   basic_prime_factorisation    |- !n. 0 < n ==>
                                       (n = PROD_SET (IMAGE (\p. p ** ppidx n) (prime_divisors n)))
   divisor_prime_factorisation  |- !m n. 0 < n /\ m divides n ==>
                                         (m = PROD_SET (IMAGE (\p. p ** ppidx m) (prime_divisors n)))
   gcd_prime_factorisation      |- !m n. 0 < m /\ 0 < n ==>
                                         (gcd m n = PROD_SET (IMAGE (\p. p ** MIN (ppidx m) (ppidx n))
                                                           (prime_divisors m INTER prime_divisors n)))
   lcm_prime_factorisation      |- !m n. 0 < m /\ 0 < n ==>
                                         (lcm m n = PROD_SET (IMAGE (\p. p ** MAX (ppidx m) (ppidx n))
                                                           (prime_divisors m UNION prime_divisors n)))

   GCD and LCM special coprime decompositions:
   common_prime_divisors_element     |- !m n p. p IN common_prime_divisors m n <=>
                                                p IN prime_divisors m /\ p IN prime_divisors n
   common_prime_divisors_finite      |- !m n. 0 < m /\ 0 < n ==> FINITE (common_prime_divisors m n)
   common_prime_divisors_pairwise_coprime     |- !m n. PAIRWISE_COPRIME (common_prime_divisors m n)
   common_prime_divisors_min_image_pairwise_coprime
   |- !m n. PAIRWISE_COPRIME (IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n))
   total_prime_divisors_element      |- !m n p. p IN total_prime_divisors m n <=>
                                                p IN prime_divisors m \/ p IN prime_divisors n
   total_prime_divisors_finite       |- !m n. 0 < m /\ 0 < n ==> FINITE (total_prime_divisors m n)
   total_prime_divisors_pairwise_coprime      |- !m n. PAIRWISE_COPRIME (total_prime_divisors m n)
   total_prime_divisors_max_image_pairwise_coprime
   |- !m n. PAIRWISE_COPRIME (IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n))

   park_on_element   |- !m n p. p IN park_on m n <=>
                                p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx m <= ppidx n
   park_off_element  |- !m n p. p IN park_off m n <=>
                                p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx n < ppidx m
   park_off_alt      |- !m n. park_off m n = common_prime_divisors m n DIFF park_on m n
   park_on_subset_common    |- !m n. park_on m n SUBSET common_prime_divisors m n
   park_off_subset_common   |- !m n. park_off m n SUBSET common_prime_divisors m n
   park_on_subset_total     |- !m n. park_on m n SUBSET total_prime_divisors m n
   park_off_subset_total    |- !m n. park_off m n SUBSET total_prime_divisors m n
   park_on_off_partition    |- !m n. common_prime_divisors m n =|= park_on m n # park_off m n
   park_off_image_has_not_1 |- !m n. 1 NOTIN IMAGE (\p. p ** ppidx m) (park_off m n)

   park_on_off_common_image_partition
         |- !m n. (let s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n) in
                   let u = IMAGE (\p. p ** ppidx m) (park_on m n) in
                   let v = IMAGE (\p. p ** ppidx n) (park_off m n) in
                   0 < m ==> s =|= u # v)
   gcd_park_decomposition  |- !m n. 0 < m /\ 0 < n ==>
                                    (let a = mypark m n in let b = gcd m n DIV a in
                                     (b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n))) /\
                                     (gcd m n = a * b) /\ coprime a b)
   gcd_park_decompose      |- !m n. 0 < m /\ 0 < n ==>
                                    (let a = mypark m n in let b = gcd m n DIV a in
                                     (gcd m n = a * b) /\ coprime a b)

   park_on_off_total_image_partition
         |- !m n. (let s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n) in
                   let u = IMAGE (\p. p ** ppidx m) (prime_divisors m DIFF park_on m n) in
                   let v = IMAGE (\p. p ** ppidx n) (prime_divisors n DIFF park_off m n) in
                   0 < m /\ 0 < n ==> s =|= u # v)
   lcm_park_decomposition  |- !m n. 0 < m /\ 0 < n ==>
                               (let a = park m n in let b = gcd m n DIV a in
                                let p = m DIV a in let q = a * n DIV gcd m n in
                                (b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n))) /\
           (p = PROD_SET (IMAGE (\p. p ** ppidx m) (prime_divisors m DIFF park_on m n))) /\
           (q = PROD_SET (IMAGE (\p. p ** ppidx n) (prime_divisors n DIFF park_off m n))) /\
            (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q))
   lcm_park_decompose      |- !m n. 0 < m /\ 0 < n ==>
                              (let a = park m n in let p = m DIV a in let q = a * n DIV gcd m n in
                               (lcm m n = p * q) /\ coprime p q)
   lcm_gcd_park_decompose  |- !m n. 0 < m /\ 0 < n ==>
                               (let a = park m n in let b = gcd m n DIV a in
                                let p = m DIV a in let q = a * n DIV gcd m n in
                                (lcm m n = p * q) /\ coprime p q /\
                                (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q))

   Consecutive LCM Recurrence:
   lcm_fun_def        |- (lcm_fun 0 = 1) /\
                          !n. lcm_fun (SUC n) = if n = 0 then 1 else
                              case some p. ?k. 0 < k /\ prime p /\ (SUC n = p ** k) of
                                NONE => lcm_fun n
                              | SOME p => p * lcm_fun n
   lcm_fun_0          |- lcm_fun 0 = 1
   lcm_fun_SUC        |- !n. lcm_fun (SUC n) = if n = 0 then 1 else
                             case some p. ?k. 0 < k /\ prime p /\ (SUC n = p ** k) of
                               NONE => lcm_fun n
                             | SOME p => p * lcm_fun n
   lcm_fun_1          |- lcm_fun 1 = 1
   lcm_fun_2          |- lcm_fun 2 = 2
   lcm_fun_suc_some   |- !n p. prime p /\ (?k. 0 < k /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = p * lcm_fun n)
   lcm_fun_suc_none   |- !n. ~(?p k. 0 < k /\ prime p /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = lcm_fun n)
   list_lcm_prime_power_index_lower   |- !l p. prime p /\ l <> [] /\ POSITIVE l ==>
                                         !x. MEM x l ==> ppidx x <= ppidx (list_lcm l)
   list_lcm_with_last_prime_power     |- !n p k. prime p /\ (n + 2 = p ** k) ==>
                                          (list_lcm [1 .. n + 2] = p * list_lcm (leibniz_vertical n))
   list_lcm_with_last_non_prime_power |- !n. (!p k. (k = 0) \/ ~prime p \/ n + 2 <> p ** k) ==>
                                          (list_lcm [1 .. n + 2] = list_lcm (leibniz_vertical n))
   list_lcm_eq_lcm_fun                |- !n. list_lcm (leibniz_vertical n) = lcm_fun (n + 1)
   lcm_fun_lower_bound                |- !n. 2 ** n <= lcm_fun (n + 1)
   lcm_fun_lower_bound_alt            |- !n. 0 < n ==> 2 ** (n - 1) <= lcm_fun n
   prime_power_index_suc_special      |- !n p. 0 < n /\ prime p /\ (SUC n = p ** ppidx (SUC n)) ==>
                                               (ppidx (SUC n) = SUC (ppidx (list_lcm [1 .. n])))
   prime_power_index_suc_property     |- !n p. 0 < n /\ prime p /\ (n + 1 = p ** ppidx (n + 1)) ==>
                                               (ppidx (n + 1) = 1 + ppidx (list_lcm [1 .. n]))

   Consecutive LCM Recurrence - Rework:
   list_lcm_by_last_prime_power      |- !n. SING (prime_divisors (n + 1)) ==>
                         (list_lcm [1 .. (n + 1)] = CHOICE (prime_divisors (n + 1)) * list_lcm [1 .. n])
   list_lcm_by_last_non_prime_power  |- !n. ~SING (prime_divisors (n + 1)) ==>
                         (list_lcm (leibniz_vertical n) = list_lcm [1 .. n])
   list_lcm_recurrence               |- !n. list_lcm (leibniz_vertical n) = (let s = prime_divisors (n + 1) in
                                            if SING s then CHOICE s * list_lcm [1 .. n] else list_lcm [1 .. n])
   list_lcm_option_last_prime_power     |- !n p. (prime_divisors (n + 1) = {p}) ==>
                                                 (list_lcm (leibniz_vertical n) = p * list_lcm [1 .. n])
   list_lcm_option_last_non_prime_power |- !n. (!p. prime_divisors (n + 1) <> {p}) ==>
                                               (list_lcm (leibniz_vertical n) = list_lcm [1 .. n])
   list_lcm_option_recurrence           |- !n. list_lcm (leibniz_vertical n) =
                                               case some p. prime_divisors (n + 1) = {p} of
                                                 NONE => list_lcm [1 .. n]
                                               | SOME p => p * list_lcm [1 .. n]

   Relating Consecutive LCM to Prime Functions:
   Theorems on Prime-related Sets:
   prime_powers_upto_list_mem     |- !n x. MEM x (SET_TO_LIST (prime_powers_upto n)) <=>
                                           ?p. (x = p ** LOG p n) /\ prime p /\ p <= n
   prime_powers_upto_lcm_prime_to_log_divisor
                                  |- !n p. prime p /\ p <= n ==>
                                           p ** LOG p n divides set_lcm (prime_powers_upto n)
   prime_powers_upto_lcm_prime_divisor
                                  |- !n p. prime p /\ p <= n ==> p divides set_lcm (prime_powers_upto n)
   prime_powers_upto_lcm_prime_to_power_divisor
                                  |- !n p. prime p /\ p <= n ==>
                                           p ** ppidx n divides set_lcm (prime_powers_upto n)
   prime_powers_upto_lcm_divisor  |- !n x. 0 < x /\ x <= n ==> x divides set_lcm (prime_powers_upto n)

   Consecutive LCM and Prime-related Sets:
   lcm_run_eq_set_lcm_prime_powers   |- !n. lcm_run n = set_lcm (prime_powers_upto n)
   set_lcm_prime_powers_upto_eqn     |- !n. set_lcm (prime_powers_upto n) = PROD_SET (prime_powers_upto n)
   lcm_run_eq_prod_set_prime_powers  |- !n. lcm_run n = PROD_SET (prime_powers_upto n)
   prime_powers_upto_prod_set_le     |- !n. PROD_SET (prime_powers_upto n) <= n ** primes_count n
   lcm_run_upper_by_primes_count     |- !n. lcm_run n <= n ** primes_count n
   prime_powers_upto_prod_set_ge     |- !n. PROD_SET (primes_upto n) <= PROD_SET (prime_powers_upto n)
   lcm_run_lower_by_primes_product   |- !n. PROD_SET (primes_upto n) <= lcm_run n
   prime_powers_upto_prod_set_mix_ge |- !n. n ** primes_count n <=
                                            PROD_SET (primes_upto n) * PROD_SET (prime_powers_upto n)
   primes_count_upper_by_product     |- !n. n ** primes_count n <= PROD_SET (primes_upto n) * lcm_run n
   primes_count_upper_by_lcm_run     |- !n. n ** primes_count n <= lcm_run n ** 2
   lcm_run_lower_by_primes_count     |- !n. SQRT (n ** primes_count n) <= lcm_run n
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MEM x [1 .. n] ==> MEM (x ** LOG x n) [1 .. n] *)
(* Proof:
   By listRangeINC_MEM, this is to show:
   (1) 1 <= x /\ x <= n ==> 1 <= x ** LOG x n
       Note 0 < x               by 1 <= x
         so 0 < x ** LOG x n    by EXP_POS, 0 < x
         or 1 <= x ** LOG x n   by arithmetic
   (2) 1 <= x /\ x <= n ==> x ** LOG x n <= n
       Note 1 <= n /\ 0 < n     by arithmetic
       If x = 1,
          Then true             by EXP_1
       If x <> 1,
          Then 1 < x, so true   by LOG
*)
val self_to_log_index_member = store_thm(
  "self_to_log_index_member",
  ``!n x. MEM x [1 .. n] ==> MEM (x ** LOG x n) [1 .. n]``,
  rw[listRangeINC_MEM] >-
  metis_tac[EXP_POS, DECIDE ``0 < n <=> 1 <= n``] >>
  `0 < n /\ 1 <= n` by decide_tac >>
  Cases_on `x = 1` >-
  rw[EXP_1] >>
  rw[LOG]);

(* ------------------------------------------------------------------------- *)
(* Prime Power or Coprime Factors                                            *)
(* ------------------------------------------------------------------------- *)

(*
The concept of a prime number goes like this:
* Given a number n > 1, it has factors n = a * b.
  Either there are several possibilities, or there is just the trivial: 1 * n and n * 1.
  A number with only trivial factors is a prime, otherwise it is a composite.
The concept of a prime power number goes like this:
* Given a number n > 1, it has factors n = a * b.
  Either a and b can be chosen to be coprime, or this choice is impossible.
  A number that cannot have coprime factors is a prime power, otherwise a coprime product.
*)

(* Theorem: 1 < n ==> (?p k. 0 < k /\ prime p /\ (n = p ** k)) \/
                      (?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ 1 < b /\ a < n /\ b < n) *)
(* Proof:
   Note 1 < n ==> 0 < n /\ n <> 0 /\ n <> 1        by arithmetic
    Now ?p. prime p /\ p divides n                 by PRIME_FACTOR, n <> 1
     so ?k. 0 < k /\ p ** k divides n /\
            coprime p (n DIV p ** k)               by FACTOR_OUT_PRIME, EXP_1, 0 < n
   Note 0 < p                by PRIME_POS
     so 0 < p ** k           by EXP_POS
    Let b = n DIV p ** k.
   Then n = (p ** k) * b     by DIVIDES_EQN_COMM, 0 < p ** m

   If b = 1,
      Then n = p ** k        by MULT_RIGHT_1
      Take k for the first assertion.
   If b <> 1,
      Let a = p ** k.
       Then coprime a b      by coprime_exp, coprime p b
      Since p <> 1           by NOT_PRIME_1
         so a <> 1           by EXP_EQ_1
        and b <> 0           by MULT_0
        Now a divides n /\ b divides n        by divides_def, MULT_COMM
         so a <= n /\ b <= n                  by DIVIDES_LE, 0 < n
        but a <> n /\ b <> n                  by MULT_LEFT_ID, MULT_RIGHT_ID
       Thus 1 < a /\ 1 < b /\ a < n /\ b < n  by arithmetic
      Take a, b for the second assertion.
*)
val prime_power_or_coprime_factors = store_thm(
  "prime_power_or_coprime_factors",
  ``!n. 1 < n ==> (?p k. 0 < k /\ prime p /\ (n = p ** k)) \/
                 (?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ 1 < b /\ a < n /\ b < n)``,
  rpt strip_tac >>
  `0 < n /\ n <> 0 /\ n <> 1` by decide_tac >>
  `?p. prime p /\ p divides n` by rw[PRIME_FACTOR] >>
  `?k. 0 < k /\ p ** k divides n /\ coprime p (n DIV p ** k)` by metis_tac[FACTOR_OUT_PRIME, EXP_1] >>
  `0 < p ** k` by rw[PRIME_POS, EXP_POS] >>
  qabbrev_tac `b = n DIV p ** k` >>
  `n = (p ** k) * b` by rw[GSYM DIVIDES_EQN_COMM, Abbr`b`] >>
  Cases_on `b = 1` >-
  metis_tac[MULT_RIGHT_1] >>
  qabbrev_tac `a = p ** k` >>
  `coprime a b` by rw[coprime_exp, Abbr`a`] >>
  `a <> 1` by metis_tac[EXP_EQ_1, NOT_PRIME_1, NOT_ZERO_LT_ZERO] >>
  `b <> 0` by metis_tac[MULT_0] >>
  `a divides n /\ b divides n` by metis_tac[divides_def, MULT_COMM] >>
  `a <= n /\ b <= n` by rw[DIVIDES_LE] >>
  `a <> n /\ b <> n` by metis_tac[MULT_LEFT_ID, MULT_RIGHT_ID] >>
  `1 < a /\ 1 < b /\ a < n /\ b < n` by decide_tac >>
  metis_tac[]);

(* The following is the more powerful version of this:
   Simple theorem: If n is not a prime, then ?a b. (n = a * b) /\ 1 < a /\ a < n /\ 1 < b /\ b < n
   Powerful theorem: If n is not a prime power, then ?a b. (n = a * b) /\ 1 < a /\ a < n /\ 1 < b /\ b < n
*)

(* Theorem: 1 < n /\ ~(?p k. 0 < k /\ prime p /\ (n = p ** k)) ==>
            ?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ a < n /\ 1 < b /\ b < n *)
(* Proof:
   Since 1 < n, n <> 1 and 0 < n                by arithmetic
    Note ?p. prime p /\ p divides n             by PRIME_FACTOR, n <> 1
     and ?m. 0 < m /\ p ** m divides n /\
         !k. coprime (p ** k) (n DIV p ** m)    by FACTOR_OUT_PRIME, 0 < n

   Let a = p ** m, b = n DIV a.
   Since 0 < p                                  by PRIME_POS
      so 0 < a                                  by EXP_POS, 0 < p
    Thus n = a * b                              by DIVIDES_EQN_COMM, 0 < a

    Also 1 < p                                  by ONE_LT_PRIME
      so 1 < a                                  by ONE_LT_EXP, 1 < p, 0 < m
     and b < n                                  by DIV_LESS, Abbr, 0 < n
     Now b <> 1                                 by MULT_RIGHT_1, n not perfect power of any prime
     and b <> 0                                 by MULT_0, n = a * b, 0 < n
     ==> 1 < b                                  by b <> 0 /\ b <> 1
    Also a <= n                                 by DIVIDES_LE
     and a <> n                                 by MULT_RIGHT_1
     ==> a < n                                  by arithmetic
    Take these a and b, the result follows.
*)
val non_prime_power_coprime_factors = store_thm(
  "non_prime_power_coprime_factors",
  ``!n. 1 < n /\ ~(?p k. 0 < k /\ prime p /\ (n = p ** k)) ==>
   ?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ a < n /\ 1 < b /\ b < n``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `?p. prime p /\ p divides n` by rw[PRIME_FACTOR] >>
  `?m. 0 < m /\ p ** m divides n /\ !k. coprime (p ** k) (n DIV p ** m)` by rw[FACTOR_OUT_PRIME] >>
  qabbrev_tac `a = p ** m` >>
  qabbrev_tac `b = n DIV a` >>
  `0 < a` by rw[PRIME_POS, EXP_POS, Abbr`a`] >>
  `n = a * b` by metis_tac[DIVIDES_EQN_COMM] >>
  `1 < a` by rw[ONE_LT_EXP, ONE_LT_PRIME, Abbr`a`] >>
  `b < n` by rw[DIV_LESS, Abbr`b`] >>
  `b <> 1` by metis_tac[MULT_RIGHT_1] >>
  `b <> 0` by metis_tac[MULT_0, NOT_ZERO_LT_ZERO] >>
  `1 < b` by decide_tac >>
  `a <= n` by rw[DIVIDES_LE] >>
  `a <> n` by metis_tac[MULT_RIGHT_1] >>
  `a < n` by decide_tac >>
  metis_tac[]);

(* Theorem: s SUBSET prime ==> PAIRWISE_COPRIME (IMAGE (\p. p ** f p) s) *)
(* Proof:
   By SUBSET_DEF, this is to show:
      (!x. x IN s ==> prime x) /\ p IN s /\ p' IN s /\ p ** f <> p' ** f ==> coprime (p ** f) (p' ** f)
   Note prime p /\ prime p'          by in_prime
    and p <> p'                      by p ** f <> p' ** f
   Thus coprime (p ** f) (p' ** f)   by prime_powers_coprime
*)
val pairwise_coprime_for_prime_powers = store_thm(
  "pairwise_coprime_for_prime_powers",
  ``!s f. s SUBSET prime ==> PAIRWISE_COPRIME (IMAGE (\p. p ** f p) s)``,
  rw[SUBSET_DEF] >>
  `prime p /\ prime p' /\ p <> p'` by metis_tac[in_prime] >>
  rw[prime_powers_coprime]);

(* ------------------------------------------------------------------------- *)
(* Prime Power Index                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n /\ prime p ==> ?m. (p ** m) divides n /\ coprime p (n DIV (p ** m)) *)
(* Proof:
   Note ?q m. (n = (p ** m) * q) /\ coprime p q     by prime_power_factor
   Let t = p ** m.
   Then t divides n                                 by divides_def, MULT_COMM
    Now 0 < p                                       by PRIME_POS
     so 0 < t                                       by EXP_POS
    ==> n = t * (n DIV t)                           by DIVIDES_EQN_COMM
   Thus q = n DIV t                                 by MULT_LEFT_CANCEL
   Take this m, and the result follows.
*)
val prime_power_index_exists = store_thm(
  "prime_power_index_exists",
  ``!n p. 0 < n /\ prime p ==> ?m. (p ** m) divides n /\ coprime p (n DIV (p ** m))``,
  rpt strip_tac >>
  `?q m. (n = (p ** m) * q) /\ coprime p q` by rw[prime_power_factor] >>
  qabbrev_tac `t = p ** m` >>
  `t divides n` by metis_tac[divides_def, MULT_COMM] >>
  `0 < t` by rw[PRIME_POS, EXP_POS, Abbr`t`] >>
  metis_tac[DIVIDES_EQN_COMM, MULT_LEFT_CANCEL, NOT_ZERO_LT_ZERO]);

(* Apply Skolemization *)
val lemma = prove(
  ``!p n. ?m. 0 < n /\ prime p ==> (p ** m) divides n /\ coprime p (n DIV (p ** m))``,
  metis_tac[prime_power_index_exists]);
(* Note !p n, for first parameter p, second parameter n. *)
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define prime power index *)
(*
- SIMP_RULE bool_ss [SKOLEM_THM] lemma;
> val it = |- ?f. !p n. 0 < n /\ prime p ==> p ** f p n divides n /\ coprime p (n DIV p ** f p n): thm
*)
val prime_power_index_def = new_specification(
    "prime_power_index_def",
    ["prime_power_index"],
    SIMP_RULE bool_ss [SKOLEM_THM] lemma);
(*
> val prime_power_index_def = |- !p n. 0 < n /\ prime p ==>
  p ** prime_power_index p n divides n /\ coprime p (n DIV p ** prime_power_index p n): thm
*)

(* Overload on prime_power_index of prime p *)
val _ = overload_on("ppidx", ``prime_power_index p``);

(*
> prime_power_index_def;
val it = |- !p n. 0 < n /\ prime p ==> p ** ppidx n divides n /\ coprime p (n DIV p ** ppidx n): thm
*)

(* Theorem: prime p ==> (p ** (ppidx n)) divides n *)
(* Proof: by prime_power_index_def, and ALL_DIVIDES_0 *)
val prime_power_factor_divides = store_thm(
  "prime_power_factor_divides",
  ``!n p. prime p ==> (p ** (ppidx n)) divides n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  rw[prime_power_index_def]);

(* Theorem: 0 < n /\ prime p ==> coprime p (n DIV p ** ppidx n) *)
(* Proof: by prime_power_index_def *)
val prime_power_cofactor_coprime = store_thm(
  "prime_power_cofactor_coprime",
  ``!n p. 0 < n /\ prime p ==> coprime p (n DIV p ** ppidx n)``,
  rw[prime_power_index_def]);

(* Theorem: 0 < n /\ prime p ==> (n = p ** (ppidx n) * (n DIV p ** (ppidx n))) *)
(* Proof:
   Let q = p ** (ppidx n).
   Then q divides n             by prime_power_factor_divides
    But 0 < n ==> n <> 0,
     so q <> 0, or 0 < q        by ZERO_DIVIDES
   Thus n = q * (n DIV q)       by DIVIDES_EQN_COMM, 0 < q
*)
val prime_power_eqn = store_thm(
  "prime_power_eqn",
  ``!n p. 0 < n /\ prime p ==> (n = p ** (ppidx n) * (n DIV p ** (ppidx n)))``,
  rpt strip_tac >>
  qabbrev_tac `q = p ** (ppidx n)` >>
  `q divides n` by rw[prime_power_factor_divides, Abbr`q`] >>
  `0 < q` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  rw[GSYM DIVIDES_EQN_COMM]);

(* Theorem: 0 < n /\ prime p ==> !k. (p ** k) divides n <=> k <= (ppidx n) *)
(* Proof:
   Let m = ppidx n.
   Then p ** m divides n                      by prime_power_factor_divides
   If part: p ** k divides n ==> k <= m
      By contradiction, suppose m < k.
      Let q = n DIV p ** m.
      Then n = p ** m * q                     by prime_power_eqn
       ==> ?t. n = p ** k * t                 by divides_def, MULT_COMM
      Let d = k - m.
      Then 0 < d                              by m < k
       ==> p ** k = p ** m * p ** d           by EXP_BY_ADD_SUB_LT
       But 0 < p ** m                         by PRIME_POS, EXP_POS
        so p ** m <> 0                        by arithmetic
      Thus q = p ** d * t                     by MULT_LEFT_CANCEL, MULT_ASSOC
     Since p divides p ** d                   by prime_divides_self_power, 0 < d
        so p divides q                        by DIVIDES_MULT
        or gcd p q = p                        by divides_iff_gcd_fix
       But coprime p q                        by prime_power_cofactor_coprime
      This is a contradiction since p <> 1    by NOT_PRIME_1

   Only-if part: k <= m ==> p ** k divides n
     Note p ** m = p ** d * p ** k            by EXP_BY_ADD_SUB_LE, MULT_COMM
     Thus p ** k divides p ** m               by divides_def
      ==> p ** k divides n                    by DIVIDES_TRANS
*)

Theorem prime_power_divisibility:
  !n p. 0 < n /\ prime p ==> !k. (p ** k) divides n <=> k <= (ppidx n)
Proof
  rpt strip_tac >>
  qabbrev_tac `m = ppidx n` >>
  `p ** m divides n` by rw[prime_power_factor_divides, Abbr`m`] >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `m < k` by decide_tac >>
    qabbrev_tac `q = n DIV p ** m` >>
    `n = p ** m * q` by rw[prime_power_eqn, Abbr`m`, Abbr`q`] >>
    `?t. n = p ** k * t` by metis_tac[divides_def, MULT_COMM] >>
    `p ** k = p ** m * p ** (k - m)` by rw[EXP_BY_ADD_SUB_LT] >>
    `0 < k - m` by decide_tac >>
    qabbrev_tac `d = k - m` >>
    `0 < p ** m` by rw[PRIME_POS, EXP_POS] >>
    `p ** m <> 0` by decide_tac >>
    `q = p ** d * t` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    `p divides p ** d` by rw[prime_divides_self_power] >>
    `p divides q` by simp[DIVIDES_MULTIPLE] >>
    `gcd p q = p` by rw[GSYM divides_iff_gcd_fix] >>
    `coprime p q` by rw[GSYM prime_power_cofactor_coprime, Abbr`m`, Abbr`q`] >>
    metis_tac[NOT_PRIME_1],
    `p ** m = p ** (m - k) * p ** k` by rw[EXP_BY_ADD_SUB_LE, MULT_COMM] >>
    `p ** k divides p ** m` by metis_tac[divides_def] >>
    metis_tac[DIVIDES_TRANS]
  ]
QED

(* Theorem: 0 < n /\ prime p ==> !k. k > ppidx n ==> ~(p ** k divides n) *)
(* Proof: by prime_power_divisibility *)
val prime_power_index_maximal = store_thm(
  "prime_power_index_maximal",
  ``!n p. 0 < n /\ prime p ==> !k. k > ppidx n ==> ~(p ** k divides n)``,
  rw[prime_power_divisibility]);

(* Theorem: 0 < n /\ m divides n ==> !p. prime p ==> ppidx m <= ppidx n *)
(* Proof:
   Note 0 < m                      by ZERO_DIVIDES, 0 < n
   Thus p ** ppidx m divides m     by prime_power_factor_divides, 0 < m
    ==> p ** ppidx m divides n     by DIVIDES_TRANS
     or ppidx m <= ppidx n         by prime_power_divisibility, 0 < n
*)
val prime_power_index_of_divisor = store_thm(
  "prime_power_index_of_divisor",
  ``!m n. 0 < n /\ m divides n ==> !p. prime p ==> ppidx m <= ppidx n``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `p ** ppidx m divides m` by rw[prime_power_factor_divides] >>
  `p ** ppidx m divides n` by metis_tac[DIVIDES_TRANS] >>
  rw[GSYM prime_power_divisibility]);

(* Theorem: 0 < n /\ prime p ==> !k. (k = ppidx n) <=> (?q. (n = p ** k * q) /\ coprime p q) *)
(* Proof:
   If part: k = ppidx n ==> ?q. (n = p ** k * q) /\ coprime p q
      Let q = n DIV p ** k, where k = ppidx n.
      Then n = p ** k * q           by prime_power_eqn
       and coprime p q              by prime_power_cofactor_coprime
   Only-if part: n = p ** k * q /\ coprime p q ==> k = ppidx n
      Note n = p ** (ppidx n) * q   by prime_power_eqn

      Thus p ** k divides n         by divides_def, MULT_COMM
       ==> k <= ppidx n             by prime_power_divisibility

      Claim: ppidx n <= k
      Proof: By contradiction, suppose k < ppidx n.
             Let d = ppidx n - k, then 0 < d.
             Let nq = n DIV p ** (ppidx n).
             Then n = p ** (ppidx n) * nq              by prime_power_eqn
             Note p ** ppidx n = p ** k * p ** d       by EXP_BY_ADD_SUB_LT
              Now 0 < p ** k                           by PRIME_POS, EXP_POS
               so q = p ** d * nq                      by MULT_LEFT_CANCEL, MULT_ASSOC, p ** k <> 0
              But p divides p ** d                     by prime_divides_self_power, 0 < d
              and p ** d divides q                     by divides_def, MULT_COMM
              ==> p divides q                          by DIVIDES_TRANS
               or gcd p q = p                          by divides_iff_gcd_fix
              This contradicts coprime p q as p <> 1   by NOT_PRIME_1

      With k <= ppidx n and ppidx n <= k, k = ppidx n  by LESS_EQUAL_ANTISYM
*)
val prime_power_index_test = store_thm(
  "prime_power_index_test",
  ``!n p. 0 < n /\ prime p ==> !k. (k = ppidx n) <=> (?q. (n = p ** k * q) /\ coprime p q)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[prime_power_eqn, prime_power_cofactor_coprime] >>
  qabbrev_tac `n = p ** k * q` >>
  `p ** k divides n` by metis_tac[divides_def, MULT_COMM] >>
  `k <= ppidx n` by rw[GSYM prime_power_divisibility] >>
  `ppidx n <= k` by
  (spose_not_then strip_assume_tac >>
  `k < ppidx n /\ 0 < ppidx n - k` by decide_tac >>
  `p ** ppidx n = p ** k * p ** (ppidx n - k)` by rw[EXP_BY_ADD_SUB_LT] >>
  qabbrev_tac `d = ppidx n - k` >>
  qabbrev_tac `nq = n DIV p ** (ppidx n)` >>
  `n = p ** (ppidx n) * nq` by rw[prime_power_eqn, Abbr`nq`] >>
  `0 < p ** k` by rw[PRIME_POS, EXP_POS] >>
  `q = p ** d * nq` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC, NOT_ZERO_LT_ZERO] >>
  `p divides p ** d` by rw[prime_divides_self_power] >>
  `p ** d divides q` by metis_tac[divides_def, MULT_COMM] >>
  `p divides q` by metis_tac[DIVIDES_TRANS] >>
  `gcd p q = p` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[NOT_PRIME_1]) >>
  decide_tac);

(* Theorem: prime p ==> (ppidx 1 = 0) *)
(* Proof:
   Note 1 = p ** 0 * 1      by EXP, MULT_RIGHT_1
    and coprime p 1         by GCD_1
     so ppidx 1 = 0         by prime_power_index_test, 0 < 1
*)
val prime_power_index_1 = store_thm(
  "prime_power_index_1",
  ``!p. prime p ==> (ppidx 1 = 0)``,
  rpt strip_tac >>
  `1 = p ** 0 * 1` by rw[] >>
  `coprime p 1` by rw[GCD_1] >>
  metis_tac[prime_power_index_test, DECIDE``0 < 1``]);

(* Theorem: 0 < n /\ prime p /\ ~(p divides n) ==> (ppidx n = 0) *)
(* Proof:
   By contradiction, suppose ppidx n <> 0.
   Then 0 < ppidx n              by NOT_ZERO_LT_ZERO
   Note p ** ppidx n divides n   by prime_power_index_def, 0 < n
    and 1 < p                    by ONE_LT_PRIME
     so p divides p ** ppidx n   by divides_self_power, 0 < n, 1 < p
    ==> p divides n              by DIVIDES_TRANS
   This contradicts ~(p divides n).
*)
val prime_power_index_eq_0 = store_thm(
  "prime_power_index_eq_0",
  ``!n p. 0 < n /\ prime p /\ ~(p divides n) ==> (ppidx n = 0)``,
  spose_not_then strip_assume_tac >>
  `p ** ppidx n divides n` by rw[prime_power_index_def] >>
  `p divides p ** ppidx n` by rw[divides_self_power, ONE_LT_PRIME] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: prime p ==> (ppidx (p ** k) = k) *)
(* Proof:
   Note p ** k = p ** k * 1   by EXP, MULT_RIGHT_1
    and coprime p 1           by GCD_1
    Now 0 < p ** k            by PRIME_POS, EXP_POS
     so ppidx (p ** k) = k    by prime_power_index_test, 0 < p ** k
*)
val prime_power_index_prime_power = store_thm(
  "prime_power_index_prime_power",
  ``!p. prime p ==> !k. ppidx (p ** k) = k``,
  rpt strip_tac >>
  `p ** k = p ** k * 1` by rw[] >>
  `coprime p 1` by rw[GCD_1] >>
  `0 < p ** k` by rw[PRIME_POS, EXP_POS] >>
  metis_tac[prime_power_index_test]);

(* Theorem: prime p ==> (ppidx p = 1) *)
(* Proof:
   Note 0 < p             by PRIME_POS
    and p = p ** 1 * 1    by EXP_1, MULT_RIGHT_1
    and coprime p 1       by GCD_1
     so ppidx p = 1       by prime_power_index_test
*)
val prime_power_index_prime = store_thm(
  "prime_power_index_prime",
  ``!p. prime p ==> (ppidx p = 1)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `p = p ** 1 * 1` by rw[] >>
  metis_tac[prime_power_index_test, GCD_1]);

(* Theorem: 0 < n /\ prime p ==> let q = n DIV (p ** ppidx n) in (n = p ** ppidx n * q) /\ (coprime p q) *)
(* Proof:
   This is to show:
   (1) n = p ** ppidx n * q
       Note p ** ppidx n divides n      by prime_power_index_def
        Now 0 < p                       by PRIME_POS
         so 0 < p ** ppidx n            by EXP_POS
        ==> n = p ** ppidx n * q        by DIVIDES_EQN_COMM, 0 < p ** ppidx n
   (2) coprime p q, true                by prime_power_index_def
*)
val prime_power_index_eqn = store_thm(
  "prime_power_index_eqn",
  ``!n p. 0 < n /\ prime p ==> let q = n DIV (p ** ppidx n) in (n = p ** ppidx n * q) /\ (coprime p q)``,
  metis_tac[prime_power_index_def, PRIME_POS, EXP_POS, DIVIDES_EQN_COMM]);

(* Theorem: 0 < n /\ prime p /\ p divides n ==> 0 < ppidx n *)
(* Proof:
   By contradiction, suppose ~(0 < ppidx n).
   Then ppidx n = 0                       by NOT_ZERO_LT_ZERO
   Note ?q. coprime p q /\
            n = p ** ppidx n * q          by prime_power_index_eqn
              = p ** 0 * q                by ppidx n = 0
              = 1 * q                     by EXP_0
              = q                         by MULT_LEFT_1
    But 1 < p                             by ONE_LT_PRIME
    and coprime p q ==> ~(p divides q)    by coprime_not_divides
    This contradicts p divides q          by p divides n, n = q
*)
val prime_power_index_pos = store_thm(
  "prime_power_index_pos",
  ``!n p. 0 < n /\ prime p /\ p divides n ==> 0 < ppidx n``,
  spose_not_then strip_assume_tac >>
  `ppidx n = 0` by decide_tac >>
  `?q. coprime p q /\ (n = p ** ppidx n * q)` by metis_tac[prime_power_index_eqn] >>
  `_ = q` by rw[] >>
  metis_tac[coprime_not_divides, ONE_LT_PRIME]);

(* ------------------------------------------------------------------------- *)
(* Prime Power and GCD, LCM                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < a /\ 0 < b /\ prime p ==>
            (gcd a b = p ** MIN (ppidx a) (ppidx b) * gcd (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b))) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Then coprime p qa                       by prime_power_cofactor_coprime
    and coprime p qb                       by prime_power_cofactor_coprime
   Also a = p ** ma * qa                   by prime_power_eqn
    and b = p ** mb * qb                   by prime_power_eqn

   If ma < mb, let d = mb - ma.
      Then p ** mb = p ** ma * p ** d      by EXP_BY_ADD_SUB_LT
       and coprime (p ** d) qa             by coprime_exp
           gcd a b
         = p ** ma * gcd qa (p ** d * qb)  by GCD_COMMON_FACTOR, MULT_ASSOC
         = p ** ma * gcd qa qb             by gcd_coprime_cancel, GCD_SYM, coprime (p ** d) qa
         = p ** (MIN ma mb) * gcd qa qb    by MIN_DEF

   If ~(ma < mb), let d = ma - mb.
      Then p ** ma = p ** mb * p ** d      by EXP_BY_ADD_SUB_LE
       and coprime (p ** d) qb             by coprime_exp
           gcd a b
         = p ** mb * gcd (p ** d * qa) qb  by GCD_COMMON_FACTOR, MULT_ASSOC
         = p ** mb * gcd qa qb             by gcd_coprime_cancel, coprime (p ** d) qb
         = p ** (MIN ma mb) * gcd qa qb    by MIN_DEF
*)
val gcd_prime_power_factor = store_thm(
  "gcd_prime_power_factor",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==>
    (gcd a b = p ** MIN (ppidx a) (ppidx b) * gcd (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b)))``,
  rpt strip_tac >>
  qabbrev_tac `ma = ppidx a` >>
  qabbrev_tac `qa = a DIV p ** ma` >>
  qabbrev_tac `mb = ppidx b` >>
  qabbrev_tac `qb = b DIV p ** mb` >>
  `coprime p qa` by rw[prime_power_cofactor_coprime, Abbr`ma`, Abbr`qa`] >>
  `coprime p qb` by rw[prime_power_cofactor_coprime, Abbr`mb`, Abbr`qb`] >>
  `a = p ** ma * qa` by rw[prime_power_eqn, Abbr`ma`, Abbr`qa`] >>
  `b = p ** mb * qb` by rw[prime_power_eqn, Abbr`mb`, Abbr`qb`] >>
  Cases_on `ma < mb` >| [
    `p ** mb = p ** ma * p ** (mb - ma)` by rw[EXP_BY_ADD_SUB_LT] >>
    qabbrev_tac `d = mb - ma` >>
    `coprime (p ** d) qa` by rw[coprime_exp] >>
    `gcd a b = p ** ma * gcd qa (p ** d * qb)` by metis_tac[GCD_COMMON_FACTOR, MULT_ASSOC] >>
    `_ = p ** ma * gcd qa qb` by metis_tac[gcd_coprime_cancel, GCD_SYM] >>
    rw[MIN_DEF],
    `p ** ma = p ** mb * p ** (ma - mb)` by rw[EXP_BY_ADD_SUB_LE] >>
    qabbrev_tac `d = ma - mb` >>
    `coprime (p ** d) qb` by rw[coprime_exp] >>
    `gcd a b = p ** mb * gcd (p ** d * qa) qb` by metis_tac[GCD_COMMON_FACTOR, MULT_ASSOC] >>
    `_ = p ** mb * gcd qa qb` by rw[gcd_coprime_cancel] >>
    rw[MIN_DEF]
  ]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> (p ** MIN (ppidx a) (ppidx b)) divides (gcd a b) *)
(* Proof: by gcd_prime_power_factor, divides_def *)
val gcd_prime_power_factor_divides_gcd = store_thm(
  "gcd_prime_power_factor_divides_gcd",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> (p ** MIN (ppidx a) (ppidx b)) divides (gcd a b)``,
  prove_tac[gcd_prime_power_factor, divides_def, MULT_COMM]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> coprime p (gcd (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b))) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Then coprime p qa             by prime_power_cofactor_coprime
       gcd p (gcd qa qb)
     = gcd (gcd p qa) qb         by GCD_ASSOC
     = gcd 1 qb                  by coprime p qa
     = 1                         by GCD_1
*)
val gcd_prime_power_cofactor_coprime = store_thm(
  "gcd_prime_power_cofactor_coprime",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> coprime p (gcd (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b)))``,
  rw[prime_power_cofactor_coprime, GCD_ASSOC, GCD_1]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> (ppidx (gcd a b) = MIN (ppidx a) (ppidx b)) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Let m = MIN ma mb.
   Then gcd a b = p ** m * (gcd qa qb)     by gcd_prime_power_factor
   Note 0 < gcd a b                        by GCD_POS
    and coprime p (gcd qa qb)              by gcd_prime_power_cofactor_coprime
   Thus ppidx (gcd a b) = m                by prime_power_index_test
*)
val gcd_prime_power_index = store_thm(
  "gcd_prime_power_index",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> (ppidx (gcd a b) = MIN (ppidx a) (ppidx b))``,
  metis_tac[gcd_prime_power_factor, GCD_POS, prime_power_index_test, gcd_prime_power_cofactor_coprime]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> !k. p ** k divides gcd a b ==> k <= MIN (ppidx a) (ppidx b) *)
(* Proof:
   Note 0 < gcd a b                     by GCD_POS
   Thus k <= ppidx (gcd a b)            by prime_power_divisibility
     or k <= MIN (ppidx a) (ppidx b)    by gcd_prime_power_index
*)
val gcd_prime_power_divisibility = store_thm(
  "gcd_prime_power_divisibility",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> !k. p ** k divides gcd a b ==> k <= MIN (ppidx a) (ppidx b)``,
  metis_tac[GCD_POS, prime_power_divisibility, gcd_prime_power_index]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==>
            (lcm a b = p ** MAX (ppidx a) (ppidx b) * lcm (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b))) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Then coprime p qa                       by prime_power_cofactor_coprime
    and coprime p qb                       by prime_power_cofactor_coprime
   Also a = p ** ma * qa                   by prime_power_eqn
    and b = p ** mb * qb                   by prime_power_eqn
   Note (gcd a b) * (lcm a b) = a * b      by GCD_LCM
    and gcd qa qb <> 0                     by GCD_EQ_0, MULT_0, 0 < a, 0 < b.

   If ma < mb,
      Then gcd a b = p ** ma * gcd qa qb              by gcd_prime_power_factor, MIN_DEF
       and a * b = (p ** ma * qa) * (p ** mb * qb)    by above
      Note p ** ma <> 0                               by MULT, 0 < a = p ** ma * qa
           gcd qa qb * lcm a b
         = qa * (p ** mb * qb)                        by MULT_LEFT_CANCEL, MULT_ASSOC
         = qa * qb * (p ** mb)                        by MULT_ASSOC_COMM
         = gcd qa qb * lcm qa qb * (p ** mb)          by GCD_LCM
      Thus lcm a b = lcm qa qb * p ** mb              by MULT_LEFT_CANCEL, MULT_ASSOC
                   = p ** mb * lcm qa qb              by MULT_COMM
                   = p ** (MAX ma mb) * lcm qa qb     by MAX_DEF

   If ~(ma < mb),
      Then gcd a b = p ** mb * gcd qa qb              by gcd_prime_power_factor, MIN_DEF
       and a * b = (p ** mb * qb) * (p ** ma * qa)    by MULT_COMM
      Note p ** mb <> 0                               by MULT, 0 < b = p ** mb * qb
           gcd qa qb * lcm a b
         = qb * (p ** ma * qa)                        by MULT_LEFT_CANCEL, MULT_ASSOC
         = qa * qb * (p ** ma)                        by MULT_ASSOC_COMM, MULT_COMM
         = gcd qa qb * lcm qa qb * (p ** ma)          by GCD_LCM
      Thus lcm a b = lcm qa qb * p ** ma              by MULT_LEFT_CANCEL, MULT_ASSOC
                   = p ** ma * lcm qa qb              by MULT_COMM
                   = p ** (MAX ma mb) * lcm qa qb     by MAX_DEF
*)
val lcm_prime_power_factor = store_thm(
  "lcm_prime_power_factor",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==>
    (lcm a b = p ** MAX (ppidx a) (ppidx b) * lcm (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b)))``,
  rpt strip_tac >>
  qabbrev_tac `ma = ppidx a` >>
  qabbrev_tac `qa = a DIV p ** ma` >>
  qabbrev_tac `mb = ppidx b` >>
  qabbrev_tac `qb = b DIV p ** mb` >>
  `coprime p qa` by rw[prime_power_cofactor_coprime, Abbr`ma`, Abbr`qa`] >>
  `coprime p qb` by rw[prime_power_cofactor_coprime, Abbr`mb`, Abbr`qb`] >>
  `a = p ** ma * qa` by rw[prime_power_eqn, Abbr`ma`, Abbr`qa`] >>
  `b = p ** mb * qb` by rw[prime_power_eqn, Abbr`mb`, Abbr`qb`] >>
  `(gcd a b) * (lcm a b) = a * b` by rw[GCD_LCM] >>
  `gcd qa qb <> 0` by metis_tac[GCD_EQ_0, MULT_0, NOT_ZERO_LT_ZERO] >>
  Cases_on `ma < mb` >| [
    `gcd a b = p ** ma * gcd qa qb` by metis_tac[gcd_prime_power_factor, MIN_DEF] >>
    `a * b = (p ** ma * qa) * (p ** mb * qb)` by rw[] >>
    `p ** ma <> 0` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
    `gcd qa qb * lcm a b = qa * (p ** mb * qb)` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    `_ = qa * qb * (p ** mb)` by rw[MULT_ASSOC_COMM] >>
    `_ = gcd qa qb * lcm qa qb * (p ** mb)` by metis_tac[GCD_LCM] >>
    `lcm a b = lcm qa qb * p ** mb` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    rw[MAX_DEF, Once MULT_COMM],
    `gcd a b = p ** mb * gcd qa qb` by metis_tac[gcd_prime_power_factor, MIN_DEF] >>
    `a * b = (p ** mb * qb) * (p ** ma * qa)` by rw[Once MULT_COMM] >>
    `p ** mb <> 0` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
    `gcd qa qb * lcm a b = qb * (p ** ma * qa)` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    `_ = qa * qb * (p ** ma)` by rw[MULT_ASSOC_COMM, Once MULT_COMM] >>
    `_ = gcd qa qb * lcm qa qb * (p ** ma)` by metis_tac[GCD_LCM] >>
    `lcm a b = lcm qa qb * p ** ma` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    rw[MAX_DEF, Once MULT_COMM]
  ]);

(* The following is the two-number version of prime_power_factor_divides *)

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> (p ** MAX (ppidx a) (ppidx b)) divides (lcm a b) *)
(* Proof: by lcm_prime_power_factor, divides_def *)
val lcm_prime_power_factor_divides_lcm = store_thm(
  "lcm_prime_power_factor_divides_lcm",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> (p ** MAX (ppidx a) (ppidx b)) divides (lcm a b)``,
  prove_tac[lcm_prime_power_factor, divides_def, MULT_COMM]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> coprime p (lcm (a DIV p ** ppidx a) (b DIV p ** ppidx b)) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Then coprime p qa                   by prime_power_cofactor_coprime
    and coprime p qb                   by prime_power_cofactor_coprime

   Simple if we have: gcd_over_lcm: gcd x (lcm y z) = lcm (gcd x y) (gcd x z)
   But we don't, so use another approach.

   Note 1 < p                          by ONE_LT_PRIME
   Let d = gcd p (lcm qa qb).
   By contradiction, assume d <> 1.
   Note d divides p                    by GCD_IS_GREATEST_COMMON_DIVISOR
     so d = p                          by prime_def, d <> 1
     or p divides lcm qa qb            by divides_iff_gcd_fix, gcd p (lcm qa qb) = d = p
    But (lcm qa qb) divides (qa * qb)  by GCD_LCM, divides_def
     so p divides qa * qb              by DIVIDES_TRANS
    ==> p divides qa or p divides qb   by P_EUCLIDES
    This contradicts coprime p qa
                 and coprime p qb      by coprime_not_divides, 1 < p
*)
val lcm_prime_power_cofactor_coprime = store_thm(
  "lcm_prime_power_cofactor_coprime",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> coprime p (lcm (a DIV p ** ppidx a) (b DIV p ** ppidx b))``,
  rpt strip_tac >>
  qabbrev_tac `ma = ppidx a` >>
  qabbrev_tac `mb = ppidx b` >>
  qabbrev_tac `qa = a DIV p ** ma` >>
  qabbrev_tac `qb = b DIV p ** mb` >>
  `coprime p qa` by rw[prime_power_cofactor_coprime, Abbr`ma`, Abbr`qa`] >>
  `coprime p qb` by rw[prime_power_cofactor_coprime, Abbr`mb`, Abbr`qb`] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd p (lcm qa qb)` >>
  `d divides p` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d = p` by metis_tac[prime_def] >>
  `p divides lcm qa qb` by rw[divides_iff_gcd_fix, Abbr`d`] >>
  `(lcm qa qb) divides (qa * qb)` by metis_tac[GCD_LCM, divides_def] >>
  `p divides qa * qb` by metis_tac[DIVIDES_TRANS] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  metis_tac[P_EUCLIDES, coprime_not_divides]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> (ppidx (lcm a b) = MAX (ppidx a) (ppidx b)) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Let m = MAX ma mb.
   Then lcm a b = p ** m * (lcm qa qb)     by lcm_prime_power_factor
   Note 0 < lcm a b                        by LCM_POS
    and coprime p (lcm qa qb)              by lcm_prime_power_cofactor_coprime
     so ppidx (lcm a b) = m                by prime_power_index_test
*)
val lcm_prime_power_index = store_thm(
  "lcm_prime_power_index",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> (ppidx (lcm a b) = MAX (ppidx a) (ppidx b))``,
  metis_tac[lcm_prime_power_factor, LCM_POS, lcm_prime_power_cofactor_coprime, prime_power_index_test]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> !k. p ** k divides lcm a b ==> k <= MAX (ppidx a) (ppidx b) *)
(* Proof:
   Note 0 < lcm a b                     by LCM_POS
     so k <= ppidx (lcm a b)            by prime_power_divisibility
     or k <= MAX (ppidx a) (ppidx b)    by lcm_prime_power_index
*)
val lcm_prime_power_divisibility = store_thm(
  "lcm_prime_power_divisibility",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> !k. p ** k divides lcm a b ==> k <= MAX (ppidx a) (ppidx b)``,
  metis_tac[LCM_POS, prime_power_divisibility, lcm_prime_power_index]);

(* ------------------------------------------------------------------------- *)
(* Prime Powers and List LCM                                                 *)
(* ------------------------------------------------------------------------- *)

(*
If a prime-power divides a list_lcm, the prime-power must divides some element in the list for list_lcm.
Note: this is not true for non-prime-power.
*)

(* Theorem: prime p ==> p ** (MAX_LIST (MAP (ppidx) l)) divides list_lcm l *)
(* Proof:
   If l = [],
         p ** MAX_LIST (MAP ppidx [])
       = p ** MAX_LIST []              by MAP
       = p ** 0                        by MAX_LIST_NIL
       = 1
       Hence true                      by ONE_DIVIDES_ALL
       In fact, list_lcm [] = 1        by list_lcm_nil
   If l <> [],
      Let ml = MAP ppidx l.
      Then ml <> []                                 by MAP_EQ_NIL
       ==> MEM (MAX_LIST ml) ml                     by MAX_LIST_MEM, ml <> []
        so ?x. (MAX_LIST ml = ppidx x) /\ MEM x l   by MEM_MAP
      Thus p ** ppidx x divides x                   by prime_power_factor_divides
       Now x divides list_lcm l                     by list_lcm_is_common_multiple
        so p ** (ppidx x)
         = p ** (MAX_LIST ml) divides list_lcm l    by DIVIDES_TRANS
*)
val list_lcm_prime_power_factor_divides = store_thm(
  "list_lcm_prime_power_factor_divides",
  ``!l p. prime p ==> p ** (MAX_LIST (MAP (ppidx) l)) divides list_lcm l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[MAX_LIST_NIL] >>
  qabbrev_tac `ml = MAP ppidx l` >>
  `ml <> []` by rw[Abbr`ml`] >>
  `MEM (MAX_LIST ml) ml` by rw[MAX_LIST_MEM] >>
  `?x. (MAX_LIST ml = ppidx x) /\ MEM x l` by metis_tac[MEM_MAP] >>
  `p ** ppidx x divides x` by rw[prime_power_factor_divides] >>
  `x divides list_lcm l` by rw[list_lcm_is_common_multiple] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: prime p /\ POSITIVE l ==> (ppidx (list_lcm l) = MAX_LIST (MAP ppidx l)) *)
(* Proof:
   By induction on l.
   Base: ppidx (list_lcm []) = MAX_LIST (MAP ppidx [])
         ppidx (list_lcm [])
       = ppidx 1                      by list_lcm_nil
       = 0                            by prime_power_index_1
       = MAX_LIST []                  by MAX_LIST_NIL
       = MAX_LIST (MAP ppidx [])      by MAP

   Step: ppidx (list_lcm l) = MAX_LIST (MAP ppidx l) ==>
         ppidx (list_lcm (h::l)) = MAX_LIST (MAP ppidx (h::l))
       Note 0 < list_lcm l                           by list_lcm_pos, EVERY_MEM
         ppidx (list_lcm (h::l))
       = ppidx (lcm h (list_lcm l))                  by list_lcm_cons
       = MAX (ppidx h) (ppidx (list_lcm l))          by lcm_prime_power_index, 0 < list_lcm l
       = MAX (ppidx h) (MAX_LIST (MAP ppidx l))      by induction hypothesis
       = MAX_LIST (ppidx h :: MAP ppidx l)           by MAX_LIST_CONS
       = MAX_LIST (MAP ppidx (h::l))                 by MAP
*)
val list_lcm_prime_power_index = store_thm(
  "list_lcm_prime_power_index",
  ``!l p. prime p /\ POSITIVE l ==> (ppidx (list_lcm l) = MAX_LIST (MAP ppidx l))``,
  Induct >-
  rw[prime_power_index_1] >>
  rpt strip_tac >>
  `0 < list_lcm l` by rw[list_lcm_pos, EVERY_MEM] >>
  `ppidx (list_lcm (h::l)) = ppidx (lcm h (list_lcm l))` by rw[list_lcm_cons] >>
  `_ = MAX (ppidx h) (ppidx (list_lcm l))` by rw[lcm_prime_power_index] >>
  `_ = MAX (ppidx h) (MAX_LIST (MAP ppidx l))` by rw[] >>
  `_ = MAX_LIST (ppidx h :: MAP ppidx l)` by rw[MAX_LIST_CONS] >>
  `_ = MAX_LIST (MAP ppidx (h::l))` by rw[] >>
  rw[]);

(* Theorem: prime p /\ POSITIVE l ==>
            !k. p ** k divides list_lcm l ==> k <= MAX_LIST (MAP ppidx l) *)
(* Proof:
   Note 0 < list_lcm l                by list_lcm_pos, EVERY_MEM
     so k <= ppidx (list_lcm l)       by prime_power_divisibility
     or k <= MAX_LIST (MAP ppidx l)   by list_lcm_prime_power_index
*)
val list_lcm_prime_power_divisibility = store_thm(
  "list_lcm_prime_power_divisibility",
  ``!l p. prime p /\ POSITIVE l ==>
   !k. p ** k divides list_lcm l ==> k <= MAX_LIST (MAP ppidx l)``,
  rpt strip_tac >>
  `0 < list_lcm l` by rw[list_lcm_pos, EVERY_MEM] >>
  metis_tac[prime_power_divisibility, list_lcm_prime_power_index]);

(* Theorem: prime p /\ l <> [] /\ POSITIVE l ==>
            !k. p ** k divides list_lcm l ==> ?x. MEM x l /\ p ** k divides x *)
(* Proof:
   Let ml = MAP ppidx l.

   Step 1: Get member x that attains ppidx x = MAX_LIST ml
   Note ml <> []                                  by MAP_EQ_NIL
   Then MEM (MAX_LIST ml) ml                      by MAX_LIST_MEM, ml <> []
    ==> ?x. (MAX_LIST ml = ppidx x) /\ MEM x l    by MEM_MAP

   Step 2: Show that this is a suitable x
   Note p ** k divides list_lcm l                 by given
    ==> k <= MAX_LIST ml                          by list_lcm_prime_power_divisibility
    Now 1 < p                                     by ONE_LT_PRIME
     so p ** k divides p ** (MAX_LIST ml)         by power_divides_iff, 1 < p
    and p ** (ppidx x) divides x                  by prime_power_factor_divides
   Thus p ** k divides x                          by DIVIDES_TRANS

   Take this x, and the result follows.
*)
val list_lcm_prime_power_factor_member = store_thm(
  "list_lcm_prime_power_factor_member",
  ``!l p. prime p /\ l <> [] /\ POSITIVE l ==>
   !k. p ** k divides list_lcm l ==> ?x. MEM x l /\ p ** k divides x``,
  rpt strip_tac >>
  qabbrev_tac `ml = MAP ppidx l` >>
  `ml <> []` by rw[Abbr`ml`] >>
  `MEM (MAX_LIST ml) ml` by rw[MAX_LIST_MEM] >>
  `?x. (MAX_LIST ml = ppidx x) /\ MEM x l` by metis_tac[MEM_MAP] >>
  `k <= MAX_LIST ml` by rw[list_lcm_prime_power_divisibility, Abbr`ml`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `p ** k divides p ** (MAX_LIST ml)` by rw[power_divides_iff] >>
  `p ** (ppidx x) divides x` by rw[prime_power_factor_divides] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: prime p ==> !m n. (n = p ** SUC (ppidx m)) ==> (lcm n m = p * m) *)
(* Proof:
   If m = 0,
      lcm n 0 = 0           by LCM_0
              = p * 0       by MULT_0
   If m <> 0, then 0 < m.
      Note 0 < n            by PRIME_POS, EXP_POS
      Let nq = n DIV p ** (ppidx n), mq = m DIV p ** (ppidx m).
      Let k = ppidx m.
      Note ppidx n = SUC k  by prime_power_index_prime_power
       and nq = 1           by DIVMOD_ID
       Now MAX (ppidx n) (ppidx m)
         = MAX (SUC k) k              by above
         = SUC k                      by MAX_DEF

           lcm n m
         = p ** MAX (ppidx n) (ppidx m) * (lcm nq mq)    by lcm_prime_power_factor
         = p ** (SUC k) * (lcm 1 mq)                     by above
         = p ** (SUC k) * mq                             by LCM_1
         = p * p ** k * mq                               by EXP
         = p * (p ** k * mq)                             by MULT_ASSOC
         = p * m                                         by prime_power_eqn
*)
val lcm_special_for_prime_power = store_thm(
  "lcm_special_for_prime_power",
  ``!p. prime p ==> !m n. (n = p ** SUC (ppidx m)) ==> (lcm n m = p * m)``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[] >>
  `0 < m` by decide_tac >>
  `0 < n` by rw[PRIME_POS, EXP_POS] >>
  qabbrev_tac `k = ppidx m` >>
  `ppidx n = SUC k` by rw[prime_power_index_prime_power] >>
  `MAX (SUC k) k = SUC k` by rw[MAX_DEF] >>
  qabbrev_tac `mq = m DIV p ** (ppidx m)` >>
  qabbrev_tac `nq = n DIV p ** (ppidx n)` >>
  `nq = 1` by rw[DIVMOD_ID, Abbr`nq`] >>
  `lcm n m = p ** (SUC k) * (lcm nq mq)` by metis_tac[lcm_prime_power_factor] >>
  metis_tac[LCM_1, EXP, MULT_ASSOC, prime_power_eqn]);

(* Theorem: (n = a * b) /\ coprime a b ==> !m. a divides m /\ b divides m ==> (lcm n m = m) *)
(* Proof:
   If n = 0,
      Then a * b = 0 ==> a = 0 or b = 0           by MULT_EQ_0
        so a divides m /\ b divides m ==> m = 0   by ZERO_DIVIDES
      Since lcm 0 m = 0                           by LCM_0
         so lcm n m = m                           by above
   If n <> 0,
      Note (a * b) divides m                      by coprime_product_divides
        or       n divides m                      by n = a * b
        so    lcm n m = m                         by divides_iff_lcm_fix
*)
val lcm_special_for_coprime_factors = store_thm(
  "lcm_special_for_coprime_factors",
  ``!n a b. (n = a * b) /\ coprime a b ==> !m. a divides m /\ b divides m ==> (lcm n m = m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `m = 0` by metis_tac[MULT_EQ_0, ZERO_DIVIDES] >>
    rw[LCM_0],
    `n divides m` by rw[coprime_product_divides] >>
    rw[GSYM divides_iff_lcm_fix]
  ]);

(* ------------------------------------------------------------------------- *)
(* Prime Divisors                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define the prime divisors of a number *)
val prime_divisors_def = Define`
    prime_divisors n = {p | prime p /\ p divides n}
`;

(* Theorem: p IN prime_divisors n <=> prime p /\ p divides n *)
(* Proof: by prime_divisors_def *)
val prime_divisors_element = store_thm(
  "prime_divisors_element",
  ``!n p. p IN prime_divisors n <=> prime p /\ p divides n``,
  rw[prime_divisors_def]);

(* Theorem: 0 < n ==> (prime_divisors n) SUBSET (natural n) *)
(* Proof:
   By prime_divisors_element, SUBSET_DEF,
   this is to show: ?x'. (x = SUC x') /\ x' < n
   Note prime x /\ x divides n
    ==> 0 < x /\ x <= n            by PRIME_POS, DIVIDES_LE, 0 < n
    ==> 0 < x /\ PRE x < n         by arithmetic
   Take x' = PRE x,
   Then SUC x' = SUC (PRE x) = x   by SUC_PRE, 0 < x
*)
val prime_divisors_subset_natural = store_thm(
  "prime_divisors_subset_natural",
  ``!n. 0 < n ==> (prime_divisors n) SUBSET (natural n)``,
  rw[prime_divisors_element, SUBSET_DEF] >>
  `x <= n` by rw[DIVIDES_LE] >>
  `PRE x < n` by decide_tac >>
  `0 < x` by rw[PRIME_POS] >>
  metis_tac[SUC_PRE]);

(* Theorem: 0 < n ==> FINITE (prime_divisors n) *)
(* Proof:
   Note (prime_divisors n) SUBSET (natural n)  by prime_divisors_subset_natural, 0 < n
    and FINITE (natural n)                     by natural_finite
     so FINITE (prime_divisors n)              by SUBSET_FINITE
*)
val prime_divisors_finite = store_thm(
  "prime_divisors_finite",
  ``!n. 0 < n ==> FINITE (prime_divisors n)``,
  metis_tac[prime_divisors_subset_natural, natural_finite, SUBSET_FINITE]);


(* Note: prime: num -> bool is also a set, so prime = {p | prime p} *)

(* Theorem: prime_divisors 0 = prime *)
(* Proof: by prime_divisors_def, ALL_DIVIDES_0 *)
val prime_divisors_0 = store_thm(
  "prime_divisors_0",
  ``prime_divisors 0 = prime``,
  rw[prime_divisors_def, EXTENSION, IN_DEF]);

(* Theorem: prime_divisors 0 = {p | prime p} *)
(* Proof: by prime_divisors_def, ALL_DIVIDES_0 *)
val prime_divisors_0 = store_thm(
  "prime_divisors_0",
  ``prime_divisors 0 = {p | prime p}``,
  rw[prime_divisors_def]);

(* Theorem: prime_divisors n = {} *)
(* Proof: by prime_divisors_def, DIVIDES_ONE, NOT_PRIME_1 *)
val prime_divisors_1 = store_thm(
  "prime_divisors_1",
  ``prime_divisors 1 = {}``,
  rw[prime_divisors_def, EXTENSION]);

(* Theorem: (prime_divisors n) SUBSET prime *)
(* Proof: by prime_divisors_element, SUBSET_DEF, IN_DEF *)
val prime_divisors_subset_prime = store_thm(
  "prime_divisors_subset_prime",
  ``!n. (prime_divisors n) SUBSET prime``,
  rw[prime_divisors_element, SUBSET_DEF, IN_DEF]);

(* Theorem: 1 < n ==> prime_divisors n <> {} *)
(* Proof:
   Note n <> 1                       by 1 < n
     so ?p. prime p /\ p divides n   by PRIME_FACTOR
     or p IN prime_divisors n        by prime_divisors_element
    ==> prime_divisors n <> {}       by MEMBER_NOT_EMPTY
*)
val prime_divisors_nonempty = store_thm(
  "prime_divisors_nonempty",
  ``!n. 1 < n ==> prime_divisors n <> {}``,
  metis_tac[PRIME_FACTOR, prime_divisors_element, MEMBER_NOT_EMPTY, DECIDE``1 < n ==> n <> 1``]);

(* Theorem: (prime_divisors n = {}) <=> (n = 1) *)
(* Proof: by prime_divisors_def, DIVIDES_ONE, NOT_PRIME_1, PRIME_FACTOR *)
val prime_divisors_empty_iff = store_thm(
  "prime_divisors_empty_iff",
  ``!n. (prime_divisors n = {}) <=> (n = 1)``,
  rw[prime_divisors_def, EXTENSION] >>
  metis_tac[DIVIDES_ONE, NOT_PRIME_1, PRIME_FACTOR]);

(* Theorem: ~ SING (prime_divisors 0) *)
(* Proof:
   Let s = prime_divisors 0.
   By contradiction, suppose SING s.
   Note prime 2                  by PRIME_2
    and prime 3                  by PRIME_3
     so 2 IN s /\ 3 IN s         by prime_divisors_0
   This contradicts SING s       by SING_ELEMENT
*)
val prime_divisors_0_not_sing = store_thm(
  "prime_divisors_0_not_sing",
  ``~ SING (prime_divisors 0)``,
  rpt strip_tac >>
  qabbrev_tac `s = prime_divisors 0` >>
  `2 IN s /\ 3 IN s` by rw[PRIME_2, PRIME_3, prime_divisors_0, Abbr`s`] >>
  metis_tac[SING_ELEMENT, DECIDE``2 <> 3``]);

(* Theorem: prime n ==> (prime_divisors n = {n}) *)
(* Proof:
   By prime_divisors_def, EXTENSION, this is to show:
      prime x /\ x divides n <=> (x = n)
   This is true                      by prime_divides_prime
*)
val prime_divisors_prime = store_thm(
  "prime_divisors_prime",
  ``!n. prime n ==> (prime_divisors n = {n})``,
  rw[prime_divisors_def, EXTENSION] >>
  metis_tac[prime_divides_prime]);

(* Theorem: prime n ==> (prime_divisors n = {n}) *)
(* Proof:
   By prime_divisors_def, EXTENSION, this is to show:
     prime x /\ x divides n ** k <=> (x = n)
   If part: prime x /\ x divides n ** k ==> (x = n)
      This is true                   by prime_divides_prime_power
   Only-if part: prime n /\ 0 < k ==> n divides n ** k
      This is true                   by prime_divides_power, DIVIDES_REFL
*)
val prime_divisors_prime_power = store_thm(
  "prime_divisors_prime_power",
  ``!n. prime n ==> !k. 0 < k ==> (prime_divisors (n ** k) = {n})``,
  rw[prime_divisors_def, EXTENSION] >>
  rw[EQ_IMP_THM] >-
  metis_tac[prime_divides_prime_power] >>
  metis_tac[prime_divides_power, DIVIDES_REFL]);

(* Theorem: SING (prime_divisors n) <=> ?p k. prime p /\ 0 < k /\ (n = p ** k) *)
(* Proof:
   If part: SING (prime_divisors n) ==> ?p k. prime p /\ 0 < k /\ (n = p ** k)
      Note n <> 0                                       by prime_divisors_0_not_sing
      Claim: n <> 1
      Proof: By contradiction, suppose n = 1.
             Then prime_divisors 1 = {}                 by prime_divisors_1
              but SING {} = F                           by SING_EMPTY

        Thus 1 < n                                      by n <> 0, n <> 1
         ==> ?p. prime p /\ p divides n                 by PRIME_FACTOR
        also ?q m. (n = p ** m * q) /\ (coprime p q)    by prime_power_factor, 0 < n
        Note q <> 0                                     by MULT_EQ_0
      Claim: q = 1
      Proof: By contradiction, suppose q <> 1.
             Then 1 < q                                 by q <> 0, q <> 1
              ==> ?z. prime z /\ z divides q            by PRIME_FACTOR
              Now 1 < p                                 by ONE_LT_PRIME
               so ~(p divides q)                        by coprime_not_divides, 1 < p, coprime p q
               or p <> z                                by z divides q, but ~(p divides q)
              But q divides n                           by divides_def, n = p ** m * q
             Thus z divides n                           by DIVIDES_TRANS
               so p IN (prime_divisors n)               by prime_divisors_element
              and z IN (prime_divisors n)               by prime_divisors_element
             This contradicts SING (prime_divisors n)   by SING_ELEMENT

      Thus q = 1,
       ==> n = p ** m                                   by MULT_RIGHT_1
       and m <> 0                                       by EXP_0, n <> 1
      Thus take this prime p, and exponent m, and 0 < m by NOT_ZERO_LT_ZERO

   Only-if part: ?p k. prime p /\ 0 < k /\ (n = p ** k) ==> SING (prime_divisors n)
      Note (prime_divisors p ** k) = {p}                by prime_divisors_prime_power
        so SING (prime_divisors n)                      by SING_DEF
*)
val prime_divisors_sing = store_thm(
  "prime_divisors_sing",
  ``!n. SING (prime_divisors n) <=> ?p k. prime p /\ 0 < k /\ (n = p ** k)``,
  rw[EQ_IMP_THM] >| [
    `n <> 0` by metis_tac[prime_divisors_0_not_sing] >>
    `n <> 1` by metis_tac[prime_divisors_1, SING_EMPTY] >>
    `0 < n /\ 1 < n` by decide_tac >>
    `?p. prime p /\ p divides n` by rw[PRIME_FACTOR] >>
    `?q m. (n = p ** m * q) /\ (coprime p q)` by rw[prime_power_factor] >>
    `q <> 0` by metis_tac[MULT_EQ_0] >>
    Cases_on `q = 1` >-
    metis_tac[MULT_RIGHT_1, EXP_0, NOT_ZERO_LT_ZERO] >>
    `?z. prime z /\ z divides q` by rw[PRIME_FACTOR] >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `p <> z` by metis_tac[coprime_not_divides] >>
    `z divides n` by metis_tac[divides_def, DIVIDES_TRANS] >>
    metis_tac[prime_divisors_element, SING_ELEMENT],
    metis_tac[prime_divisors_prime_power, SING_DEF]
  ]);

(* Theorem: (prime_divisors n = {p}) <=> ?k. prime p /\ 0 < k /\ (n = p ** k) *)
(* Proof:
   If part: prime_divisors n = {p} ==> ?k. prime p /\ 0 < k /\ (n = p ** k)
      Note prime p                                     by prime_divisors_element, IN_SING
       and SING (prime_divisors n)                     by SING_DEF
       ==> ?q k. prime q /\ 0 < k /\ (n = q ** k)      by prime_divisors_sing
      Take this k, then q = p                          by prime_divisors_prime_power, IN_SING
   Only-if part: prime p ==> prime_divisors (p ** k) = {p}
      This is true                                     by prime_divisors_prime_power
*)
val prime_divisors_sing_alt = store_thm(
  "prime_divisors_sing_alt",
  ``!n p. (prime_divisors n = {p}) <=> ?k. prime p /\ 0 < k /\ (n = p ** k)``,
  metis_tac[prime_divisors_sing, SING_DEF, IN_SING, prime_divisors_element, prime_divisors_prime_power]);

(* Theorem: SING (prime_divisors n) ==>
            let p = CHOICE (prime_divisors n) in prime p /\ (n = p ** ppidx n) *)
(* Proof:
   Let s = prime_divisors n.
   Note n <> 0                    by prime_divisors_0_not_sing
    and n <> 1                    by prime_divisors_1, SING_EMPTY
    ==> s <> {}                   by prime_divisors_empty_iff, n <> 1
   Note p = CHOICE s IN s         by CHOICE_DEF
     so prime p /\ p divides n    by prime_divisors_element
   Thus need only to show: n = p ** ppidx n
   Note ?q. (n = p ** ppidx n * q) /\
            coprime p q           by prime_power_factor, prime_power_index_test, 0 < n
   Claim: q = 1
   Proof: By contradiction, suppose q <> 1.
          Note 1 < p                        by ONE_LT_PRIME, prime p
           and q <> 0                       by MULT_EQ_0
           ==> ?z. prime z /\ z divides q   by PRIME_FACTOR, 1 < q
          Note ~(p divides q)               by coprime_not_divides, 1 < p
           ==> z <> p                       by z divides q
          Also q divides n                  by divides_def, n = p ** ppidx n * q
           ==> z divides n                  by DIVIDES_TRANS
          Thus p IN s /\ z IN s             by prime_divisors_element
            or p = z, contradicts z <> p    by SING_ELEMENT

   Thus q = 1, and n = p ** ppidx n         by MULT_RIGHT_1
*)
val prime_divisors_sing_property = store_thm(
  "prime_divisors_sing_property",
  ``!n. SING (prime_divisors n) ==>
       let p = CHOICE (prime_divisors n) in prime p /\ (n = p ** ppidx n)``,
  ntac 2 strip_tac >>
  qabbrev_tac `s = prime_divisors n` >>
  `n <> 0` by metis_tac[prime_divisors_0_not_sing] >>
  `n <> 1` by metis_tac[prime_divisors_1, SING_EMPTY] >>
  `s <> {}` by rw[prime_divisors_empty_iff, Abbr`s`] >>
  `prime (CHOICE s) /\ (CHOICE s) divides n` by metis_tac[CHOICE_DEF, prime_divisors_element] >>
  rw_tac std_ss[] >>
  rw[] >>
  `0 < n` by decide_tac >>
  `?q. (n = p ** ppidx n * q) /\ coprime p q` by metis_tac[prime_power_factor, prime_power_index_test] >>
  reverse (Cases_on `q = 1`) >| [
    `q <> 0` by metis_tac[MULT_EQ_0] >>
    `?z. prime z /\ z divides q` by rw[PRIME_FACTOR] >>
    `z <> p` by metis_tac[coprime_not_divides, ONE_LT_PRIME] >>
    `z divides n` by metis_tac[divides_def, DIVIDES_TRANS] >>
    metis_tac[prime_divisors_element, SING_ELEMENT],
    rw[]
  ]);

(* Theorem: m divides n ==> (prime_divisors m) SUBSET (prime_divisors n) *)
(* Proof:
   Note !x. x IN prime_divisors m
    ==>     prime x /\ x divides m    by prime_divisors_element
    ==>     primx x /\ x divides n    by DIVIDES_TRANS
    ==>     x IN prime_divisors n     by prime_divisors_element
     or (prime_divisors m) SUBSET (prime_divisors n)   by SUBSET_DEF
*)
val prime_divisors_divisor_subset = store_thm(
  "prime_divisors_divisor_subset",
  ``!m n. m divides n ==> (prime_divisors m) SUBSET (prime_divisors n)``,
  rw[prime_divisors_element, SUBSET_DEF] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: x divides m /\ x divides n ==>
            (prime_divisors x SUBSET (prime_divisors m) INTER (prime_divisors n)) *)
(* Proof:
   By prime_divisors_element, SUBSET_DEF, this is to show:
   (1) x' divides x /\ x divides m ==> x' divides m, true   by DIVIDES_TRANS
   (2) x' divides x /\ x divides n ==> x' divides n, true   by DIVIDES_TRANS
*)
val prime_divisors_common_divisor = store_thm(
  "prime_divisors_common_divisor",
  ``!n m x. x divides m /\ x divides n ==>
           (prime_divisors x SUBSET (prime_divisors m) INTER (prime_divisors n))``,
  rw[prime_divisors_element, SUBSET_DEF] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: m divides x /\ n divides x ==>
            (prime_divisors m UNION prime_divisors n) SUBSET prime_divisors x *)
(* Proof:
   By prime_divisors_element, SUBSET_DEF, this is to show:
   (1) x' divides m /\ m divides x ==> x' divides x, true   by DIVIDES_TRANS
   (2) x' divides n /\ n divides x ==> x' divides x, true   by DIVIDES_TRANS
*)
val prime_divisors_common_multiple = store_thm(
  "prime_divisors_common_multiple",
  ``!n m x. m divides x /\ n divides x ==>
           (prime_divisors m UNION prime_divisors n) SUBSET prime_divisors x``,
  rw[prime_divisors_element, SUBSET_DEF] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: 0 < m /\ 0 < n /\ x divides m /\ x divides n ==>
            !p. prime p ==> ppidx x <= MIN (ppidx m) (ppidx n) *)
(* Proof:
   Note ppidx x <= ppidx m                    by prime_power_index_of_divisor, 0 < m
    and ppidx x <= ppidx n                    by prime_power_index_of_divisor, 0 < n
    ==> ppidx x <= MIN (ppidx m) (ppidx n)    by MIN_LE
*)
val prime_power_index_common_divisor = store_thm(
  "prime_power_index_common_divisor",
  ``!n m x. 0 < m /\ 0 < n /\ x divides m /\ x divides n ==>
   !p. prime p ==> ppidx x <= MIN (ppidx m) (ppidx n)``,
  rw[MIN_LE, prime_power_index_of_divisor]);

(* Theorem: 0 < x /\ m divides x /\ n divides x ==>
            !p. prime p ==> MAX (ppidx m) (ppidx n) <= ppidx x *)
(* Proof:
   Note ppidx m <= ppidx x                    by prime_power_index_of_divisor, 0 < x
    and ppidx n <= ppidx x                    by prime_power_index_of_divisor, 0 < x
    ==> MAX (ppidx m) (ppidx n) <= ppidx x    by MAX_LE
*)
val prime_power_index_common_multiple = store_thm(
  "prime_power_index_common_multiple",
  ``!n m x. 0 < x /\ m divides x /\ n divides x ==>
   !p. prime p ==> MAX (ppidx m) (ppidx n) <= ppidx x``,
  rw[MAX_LE, prime_power_index_of_divisor]);

(*
prime p = 2,    n = 10,   LOG 2 10 = 3, but ppidx 10 = 1, since 4 cannot divide 10.
10 = 2^1 * 5^1
*)

(* Theorem: 0 < n /\ prime p ==> ppidx n <= LOG p n *)
(* Proof:
   By contradiction, suppose LOG p n < ppidx n.
   Then SUC (LOG p n) <= ppidx n                    by arithmetic
   Note 1 < p                                       by ONE_LT_PRIME
     so p ** (SUC (LOG p n)) divides p ** ppidx n   by power_divides_iff, 1 < p
    But p ** ppidx n divides n                      by prime_power_index_def
    ==> p ** SUC (LOG p n) divides n                by DIVIDES_TRANS
     or p ** SUC (LOG p n) <= n                     by DIVIDES_LE, 0 < n
   This contradicts n < p ** SUC (LOG p n)          by LOG, 0 < n, 1 < p
*)
val prime_power_index_le_log_index = store_thm(
  "prime_power_index_le_log_index",
  ``!n p. 0 < n /\ prime p ==> ppidx n <= LOG p n``,
  spose_not_then strip_assume_tac >>
  `SUC (LOG p n) <= ppidx n` by decide_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `p ** (SUC (LOG p n)) divides p ** ppidx n` by rw[power_divides_iff] >>
  `p ** ppidx n divides n` by rw[prime_power_index_def] >>
  `p ** SUC (LOG p n) divides n` by metis_tac[DIVIDES_TRANS] >>
  `p ** SUC (LOG p n) <= n` by rw[DIVIDES_LE] >>
  `n < p ** SUC (LOG p n)` by rw[LOG] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Prime-related Sets                                                        *)
(* ------------------------------------------------------------------------- *)

(*
Example: Take n = 10.
primes_upto 10 = {2; 3; 5; 7}
prime_powers_upto 10 = {8; 9; 5; 7}
SET_TO_LIST (prime_powers_upto 10) = [8; 9; 5; 7]
set_lcm (prime_powers_upto 10) = 2520
lcm_run 10 = 2520

Given n,
First get (primes_upto n) = {p | prime p /\ p <= n}
For each prime p, map to p ** LOG p n.

logroot.LOG  |- !a n. 1 < a /\ 0 < n ==> a ** LOG a n <= n /\ n < a ** SUC (LOG a n)
*)

(* val _ = clear_overloads_on "pd"; in Mobius theory *)
(* open primePowerTheory; *)

(*
> prime_power_index_def;
val it = |- !p n. 0 < n /\ prime p ==> p ** ppidx n divides n /\ coprime p (n DIV p ** ppidx n): thm
*)

(* Define the set of primes up to n *)
val primes_upto_def = Define`
    primes_upto n = {p | prime p /\ p <= n}
`;

(* Overload the counts of primes up to n *)
val _ = overload_on("primes_count", ``\n. CARD (primes_upto n)``);

(* Define the prime powers up to n *)
val prime_powers_upto_def = Define`
    prime_powers_upto n = IMAGE (\p. p ** LOG p n) (primes_upto n)
`;

(* Define the prime power divisors of n *)
val prime_power_divisors_def = Define`
    prime_power_divisors n = IMAGE (\p. p ** ppidx n) (prime_divisors n)
`;

(* Theorem: p IN primes_upto n <=> prime p /\ p <= n *)
(* Proof: by primes_upto_def *)
val primes_upto_element = store_thm(
  "primes_upto_element",
  ``!n p. p IN primes_upto n <=> prime p /\ p <= n``,
  rw[primes_upto_def]);

(* Theorem: (primes_upto n) SUBSET (natural n) *)
(* Proof:
   By primes_upto_def, SUBSET_DEF,
   this is to show: prime x /\ x <= n ==> ?x'. (x = SUC x') /\ x' < n
   Note 0 < x            by PRIME_POS, prime x
     so PRE x < n        by x <= n
    and SUC (PRE x) = x  by SUC_PRE, 0 < x
   Take x' = PRE x, and the result follows.
*)
val primes_upto_subset_natural = store_thm(
  "primes_upto_subset_natural",
  ``!n. (primes_upto n) SUBSET (natural n)``,
  rw[primes_upto_def, SUBSET_DEF] >>
  `0 < x` by rw[PRIME_POS] >>
  `PRE x < n` by decide_tac >>
  metis_tac[SUC_PRE]);

(* Theorem: FINITE (primes_upto n) *)
(* Proof:
   Note (primes_upto n) SUBSET (natural n)   by primes_upto_subset_natural
    and FINITE (natural n)                   by natural_finite
    ==> FINITE (primes_upto n)               by SUBSET_FINITE
*)
val primes_upto_finite = store_thm(
  "primes_upto_finite",
  ``!n. FINITE (primes_upto n)``,
  metis_tac[primes_upto_subset_natural, natural_finite, SUBSET_FINITE]);

(* Theorem: PAIRWISE_COPRIME (primes_upto n) *)
(* Proof:
   Let s = prime_power_divisors n
   This is to show: prime x /\ prime y /\ x <> y ==> coprime x y
   This is true                by primes_coprime
*)
val primes_upto_pairwise_coprime = store_thm(
  "primes_upto_pairwise_coprime",
  ``!n. PAIRWISE_COPRIME (primes_upto n)``,
  metis_tac[primes_upto_element, primes_coprime]);

(* Theorem: primes_upto 0 = {} *)
(* Proof:
       p IN primes_upto 0
   <=> prime p /\ p <= 0     by primes_upto_element
   <=> prime 0               by p <= 0
   <=> F                     by NOT_PRIME_0
*)
val primes_upto_0 = store_thm(
  "primes_upto_0",
  ``primes_upto 0 = {}``,
  rw[primes_upto_element, EXTENSION]);

(* Theorem: primes_count 0 = 0 *)
(* Proof:
     primes_count 0
   = CARD (primes_upto 0)     by notation
   = CARD {}                  by primes_upto_0
   = 0                        by CARD_EMPTY
*)
val primes_count_0 = store_thm(
  "primes_count_0",
  ``primes_count 0 = 0``,
  rw[primes_upto_0]);

(* Theorem: primes_upto 1 = {} *)
(* Proof:
       p IN primes_upto 1
   <=> prime p /\ p <= 1     by primes_upto_element
   <=> prime 0 or prime 1    by p <= 1
   <=> F                     by NOT_PRIME_0, NOT_PRIME_1
*)
val primes_upto_1 = store_thm(
  "primes_upto_1",
  ``primes_upto 1 = {}``,
  rw[primes_upto_element, EXTENSION, DECIDE``x <= 1 <=> (x = 0) \/ (x = 1)``] >>
  metis_tac[NOT_PRIME_0, NOT_PRIME_1]);

(* Theorem: primes_count 1 = 0 *)
(* Proof:
     primes_count 1
   = CARD (primes_upto 1)     by notation
   = CARD {}                  by primes_upto_1
   = 0                        by CARD_EMPTY
*)
val primes_count_1 = store_thm(
  "primes_count_1",
  ``primes_count 1 = 0``,
  rw[primes_upto_1]);

(* Theorem: x IN prime_powers_upto n <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= n *)
(* Proof: by prime_powers_upto_def, primes_upto_element *)
val prime_powers_upto_element = store_thm(
  "prime_powers_upto_element",
  ``!n x. x IN prime_powers_upto n <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= n``,
  rw[prime_powers_upto_def, primes_upto_element]);

(* Theorem: prime p /\ p <= n ==> (p ** LOG p n) IN (prime_powers_upto n) *)
(* Proof: by prime_powers_upto_element *)
val prime_powers_upto_element_alt = store_thm(
  "prime_powers_upto_element_alt",
  ``!p n. prime p /\ p <= n ==> (p ** LOG p n) IN (prime_powers_upto n)``,
  metis_tac[prime_powers_upto_element]);

(* Theorem: FINITE (prime_powers_upto n) *)
(* Proof:
   Note prime_powers_upto n =
        IMAGE (\p. p ** LOG p n) (primes_upto n)   by prime_powers_upto_def
    and FINITE (primes_upto n)                     by primes_upto_finite
    ==> FINITE (prime_powers_upto n)               by IMAGE_FINITE
*)
val prime_powers_upto_finite = store_thm(
  "prime_powers_upto_finite",
  ``!n. FINITE (prime_powers_upto n)``,
  rw[prime_powers_upto_def, primes_upto_finite]);

(* Theorem: PAIRWISE_COPRIME (prime_powers_upto n) *)
(* Proof:
   Let s = prime_power_divisors n
   This is to show: x IN s /\ y IN s /\ x <> y ==> coprime x y
   Note ?p1. prime p1 /\ (x = p1 ** LOG p1 n) /\ p1 <= n   by prime_powers_upto_element
    and ?p2. prime p2 /\ (y = p2 ** LOG p2 n) /\ p2 <= n   by prime_powers_upto_element
    and p1 <> p2                                           by prime_powers_eq
   Thus coprime x y                                        by prime_powers_coprime
*)
val prime_powers_upto_pairwise_coprime = store_thm(
  "prime_powers_upto_pairwise_coprime",
  ``!n. PAIRWISE_COPRIME (prime_powers_upto n)``,
  metis_tac[prime_powers_upto_element, prime_powers_eq, prime_powers_coprime]);

(* Theorem: prime_powers_upto 0 = {} *)
(* Proof:
       x IN prime_powers_upto 0
   <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= 0     by prime_powers_upto_element
   <=> ?p. (x = p ** LOG p n) /\ prime 0               by p <= 0
   <=> F                                               by NOT_PRIME_0
*)
val prime_powers_upto_0 = store_thm(
  "prime_powers_upto_0",
  ``prime_powers_upto 0 = {}``,
  rw[prime_powers_upto_element, EXTENSION]);

(* Theorem: prime_powers_upto 1 = {} *)
(* Proof:
       x IN prime_powers_upto 1
   <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= 1     by prime_powers_upto_element
   <=> ?p. (x = p ** LOG p n) /\ prime 0 or prime 1    by p <= 0
   <=> F                                               by NOT_PRIME_0, NOT_PRIME_1
*)
val prime_powers_upto_1 = store_thm(
  "prime_powers_upto_1",
  ``prime_powers_upto 1 = {}``,
  rw[prime_powers_upto_element, EXTENSION, DECIDE``x <= 1 <=> (x = 0) \/ (x = 1)``] >>
  metis_tac[NOT_PRIME_0, NOT_PRIME_1]);

(* Theorem: x IN prime_power_divisors n <=> ?p. (x = p ** ppidx n) /\ prime p /\ p divides n *)
(* Proof: by prime_power_divisors_def, prime_divisors_element *)
val prime_power_divisors_element = store_thm(
  "prime_power_divisors_element",
  ``!n x. x IN prime_power_divisors n <=> ?p. (x = p ** ppidx n) /\ prime p /\ p divides n``,
  rw[prime_power_divisors_def, prime_divisors_element]);

(* Theorem: prime p /\ p divides n ==> (p ** ppidx n) IN (prime_power_divisors n) *)
(* Proof: by prime_power_divisors_element *)
val prime_power_divisors_element_alt = store_thm(
  "prime_power_divisors_element_alt",
  ``!p n. prime p /\ p divides n ==> (p ** ppidx n) IN (prime_power_divisors n)``,
  metis_tac[prime_power_divisors_element]);

(* Theorem: 0 < n ==> FINITE (prime_power_divisors n) *)
(* Proof:
   Note prime_power_divisors n =
        IMAGE (\p. p ** ppidx n) (prime_divisors n)   by prime_power_divisors_def
    and FINITE (prime_divisors n)                     by prime_divisors_finite, 0 < n
    ==> FINITE (prime_power_divisors n)               by IMAGE_FINITE
*)
val prime_power_divisors_finite = store_thm(
  "prime_power_divisors_finite",
  ``!n. 0 < n ==> FINITE (prime_power_divisors n)``,
  rw[prime_power_divisors_def, prime_divisors_finite]);

(* Theorem: PAIRWISE_COPRIME (prime_power_divisors n) *)
(* Proof:
   Let s = prime_power_divisors n
   This is to show: x IN s /\ y IN s /\ x <> y ==> coprime x y
   Note ?p1. prime p1 /\
             (x = p1 ** prime_power_index p1 n) /\ p1 divides n   by prime_power_divisors_element
    and ?p2. prime p2 /\
             (y = p2 ** prime_power_index p2 n) /\ p2 divides n   by prime_power_divisors_element
    and p1 <> p2                                                  by prime_powers_eq
   Thus coprime x y                                               by prime_powers_coprime
*)
val prime_power_divisors_pairwise_coprime = store_thm(
  "prime_power_divisors_pairwise_coprime",
  ``!n. PAIRWISE_COPRIME (prime_power_divisors n)``,
  metis_tac[prime_power_divisors_element, prime_powers_eq, prime_powers_coprime]);

(* Theorem: prime_power_divisors 1 = {} *)
(* Proof:
       x IN prime_power_divisors 1
   <=> ?p. (x = p ** ppidx n) /\ prime p /\ p divides 1     by prime_power_divisors_element
   <=> ?p. (x = p ** ppidx n) /\ prime 1                    by DIVIDES_ONE
   <=> F                                                    by NOT_PRIME_1
*)
val prime_power_divisors_1 = store_thm(
  "prime_power_divisors_1",
  ``prime_power_divisors 1 = {}``,
  rw[prime_power_divisors_element, EXTENSION]);

(* ------------------------------------------------------------------------- *)
(* Factorisations                                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> (n = PROD_SET (prime_power_divisors n)) *)
(* Proof:
   Let s = prime_power_divisors n.
   The goal becomes: n = PROD_SET s
   Note FINITE s                       by prime_power_divisors_finite

   Claim: (PROD_SET s) divides n
   Proof: Note !z. z IN s <=>
               ?p. (z = p ** ppidx n) /\ prime p /\ p divides n     by prime_power_divisors_element
           ==> !z. z IN s ==> z divides n       by prime_power_index_def

          Note PAIRWISE_COPRIME s               by prime_power_divisors_pairwise_coprime
          Thus set_lcm s = PROD_SET s           by pairwise_coprime_prod_set_eq_set_lcm
           But (set_lcm s) divides n            by set_lcm_is_least_common_multiple
           ==> PROD_SET s divides n             by above

   Therefore, ?q. n = q * PROD_SET s            by divides_def, Claim.
   Claim: q = 1
   Proof: By contradiction, suppose q <> 1.
          Then ?p. prime p /\ p divides q       by PRIME_FACTOR
          Let u = p ** ppidx n, v = n DIV u.
          Then u divides n /\ coprime p v       by prime_power_index_def, 0 < n, prime p
          Note 0 < p                            by PRIME_POS
           ==> 0 < u                            by EXP_POS, 0 < p
          Thus n = v * u                        by DIVIDES_EQN, 0 < u

          Claim: u divides (PROD_SET s)
          Proof: Note q divides n               by divides_def, MULT_COMM
                  ==> p divides n               by DIVIDES_TRANS
                  ==> p IN (prime_divisors n)   by prime_divisors_element
                  ==> u IN s                    by prime_power_divisors_element_alt
                 Thus u divides (PROD_SET s)    by PROD_SET_ELEMENT_DIVIDES, FINITE s

          Hence ?t. PROD_SET s = t * u          by divides_def, u divides (PROD_SET s)
             or v * u = n = q * (t * u)         by above
                          = (q * t) * u         by MULT_ASSOC
           ==> v = q * t                        by MULT_RIGHT_CANCEL, NOT_ZERO_LT_ZERO
           But p divideq q                      by above
           ==> p divides v                      by DIVIDES_MULT
          Note 1 < p                            by ONE_LT_PRIME
           ==> ~(coprime p v)                   by coprime_not_divides
          This contradicts coprime p v.

   Thus n = q * PROD_SET s, and q = 1           by Claim
     or n = PROD_SET s                          by MULT_LEFT_1
*)
val prime_factorisation = store_thm(
  "prime_factorisation",
  ``!n. 0 < n ==> (n = PROD_SET (prime_power_divisors n))``,
  rpt strip_tac >>
  qabbrev_tac `s = prime_power_divisors n` >>
  `FINITE s` by rw[prime_power_divisors_finite, Abbr`s`] >>
  `(PROD_SET s) divides n` by
  (`!z. z IN s ==> z divides n` by metis_tac[prime_power_divisors_element, prime_power_index_def] >>
  `PAIRWISE_COPRIME s` by metis_tac[prime_power_divisors_pairwise_coprime, Abbr`s`] >>
  metis_tac[pairwise_coprime_prod_set_eq_set_lcm, set_lcm_is_least_common_multiple]) >>
  `?q. n = q * PROD_SET s` by rw[GSYM divides_def] >>
  `q = 1` by
    (spose_not_then strip_assume_tac >>
  `?p. prime p /\ p divides q` by rw[PRIME_FACTOR] >>
  qabbrev_tac `u = p ** ppidx n` >>
  qabbrev_tac `v = n DIV u` >>
  `u divides n /\ coprime p v` by rw[prime_power_index_def, Abbr`u`, Abbr`v`] >>
  `0 < u` by rw[EXP_POS, PRIME_POS, Abbr`u`] >>
  `n = v * u` by rw[GSYM DIVIDES_EQN, Abbr`v`] >>
  `u divides (PROD_SET s)` by
      (`p divides n` by metis_tac[divides_def, MULT_COMM, DIVIDES_TRANS] >>
  `p IN (prime_divisors n)` by rw[prime_divisors_element] >>
  `u IN s` by metis_tac[prime_power_divisors_element_alt] >>
  rw[PROD_SET_ELEMENT_DIVIDES]) >>
  `?t. PROD_SET s = t * u` by rw[GSYM divides_def] >>
  `v = q * t` by metis_tac[MULT_RIGHT_CANCEL, MULT_ASSOC, NOT_ZERO_LT_ZERO] >>
  `p divides v` by rw[DIVIDES_MULT] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  metis_tac[coprime_not_divides]) >>
  rw[]);

(* This is a little milestone theorem. *)

(* Theorem: 0 < n ==> (n = PROD_SET (IMAGE (\p. p ** ppidx n) (prime_divisors n))) *)
(* Proof: by prime_factorisation, prime_power_divisors_def *)
val basic_prime_factorisation = store_thm(
  "basic_prime_factorisation",
  ``!n. 0 < n ==> (n = PROD_SET (IMAGE (\p. p ** ppidx n) (prime_divisors n)))``,
  rw[prime_factorisation, GSYM prime_power_divisors_def]);

(* Theorem: 0 < n /\ m divides n ==> (m = PROD_SET (IMAGE (\p. p ** ppidx m) (prime_divisors n))) *)
(* Proof:
   Note 0 < m                 by ZERO_DIVIDES, 0 < n
   Let s = prime_divisors n, t = IMAGE (\p. p ** ppidx m) s.
   The goal is: m = PROD_SET t

   Note FINITE s              by prime_divisors_finite
    ==> FINITE t              by IMAGE_FINITE
    and PAIRWISE_COPRIME t    by prime_divisors_element, prime_powers_coprime

   By DIVIDES_ANTISYM, this is to show:
   (1) m divides PROD_SET t
       Let r = prime_divisors m
       Then m = PROD_SET (IMAGE (\p. p ** ppidx m) r)  by basic_prime_factorisation
        and r SUBSET s                                 by prime_divisors_divisor_subset
        ==> (IMAGE (\p. p ** ppidx m) r) SUBSET t      by IMAGE_SUBSET
        ==> m divides PROD_SET t                       by pairwise_coprime_prod_set_subset_divides
   (2) PROD_SET t divides m
       Claim: !x. x IN t ==> x divides m
       Proof: Note ?p. p IN s /\ (x = p ** (ppidx m))  by IN_IMAGE
               and prime p                             by prime_divisors_element
                so 1 < p                               by ONE_LT_PRIME
               Now p ** ppidx m divides m              by prime_power_factor_divides
                or x divides m                         by above
       Hence PROD_SET t divides m                      by pairwise_coprime_prod_set_divides
*)
val divisor_prime_factorisation = store_thm(
  "divisor_prime_factorisation",
  ``!m n. 0 < n /\ m divides n ==> (m = PROD_SET (IMAGE (\p. p ** ppidx m) (prime_divisors n)))``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  qabbrev_tac `s = prime_divisors n` >>
  qabbrev_tac `t = IMAGE (\p. p ** ppidx m) s` >>
  `FINITE s` by rw[prime_divisors_finite, Abbr`s`] >>
  `FINITE t` by rw[Abbr`t`] >>
  `PAIRWISE_COPRIME t` by
  (rw[Abbr`t`] >>
  `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element] >>
  rw[prime_powers_coprime]) >>
  (irule DIVIDES_ANTISYM >> rpt conj_tac) >| [
    qabbrev_tac `r = prime_divisors m` >>
    `m = PROD_SET (IMAGE (\p. p ** ppidx m) r)` by rw[basic_prime_factorisation, Abbr`r`] >>
    `r SUBSET s` by rw[prime_divisors_divisor_subset, Abbr`r`, Abbr`s`] >>
    metis_tac[pairwise_coprime_prod_set_subset_divides, IMAGE_SUBSET],
    `!x. x IN t ==> x divides m` by
  (rpt strip_tac >>
    qabbrev_tac `f = \p:num. p ** (ppidx m)` >>
    `?p. p IN s /\ (x = p ** (ppidx m))` by metis_tac[IN_IMAGE] >>
    `prime p` by metis_tac[prime_divisors_element] >>
    rw[prime_power_factor_divides]) >>
    rw[pairwise_coprime_prod_set_divides]
  ]);

(* Theorem: 0 < m /\ 0 < n ==>
           (gcd m n = PROD_SET (IMAGE (\p. p ** (MIN (ppidx m) (ppidx n)))
                               ((prime_divisors m) INTER (prime_divisors n)))) *)
(* Proof:
   Let sm = prime_divisors m, sn = prime_divisors n, s = sm INTER sn.
   Let tm = IMAGE (\p. p ** ppidx m) sm, tn = IMAGE (\p. p ** ppidx m) sn,
        t = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) s.
   The goal is: gcd m n = PROD_SET t

   By GCD_PROPERTY, this is to show:
   (1) PROD_SET t divides m /\ PROD_SET t divides n
       Note FINITE sm /\ FINITE sn              by prime_divisors_finite
        ==> FINITE s                            by FINITE_INTER
        and FINITE tm /\ FINITE tn /\ FINITE t  by IMAGE_FINITE
       Also PAIRWISE_COPRIME t                  by IN_INTER, prime_divisors_element, prime_powers_coprime

       Claim: !x. x IN t ==> x divides m /\ x divides n
       Prood: Note x IN t
               ==> ?p. p IN s /\ x = p ** MIN (ppidx m) (ppidx n)   by IN_IMAGE
               ==> p IN sm /\ p IN sn                               by IN_INTER
              Note prime p                      by prime_divisors_element
               ==> p ** ppidx m divides m       by prime_power_factor_divides
               and p ** ppidx n divides n       by prime_power_factor_divides
              Note MIN (ppidx m) (ppidx n) <= ppidx m   by MIN_DEF
               and MIN (ppidx m) (ppidx n) <= ppidx n   by MIN_DEF
               ==> x divides p ** ppidx m       by prime_power_divides_iff
               and x divides p ** ppidx n       by prime_power_divides_iff
                or x divides m /\ x divides n   by DIVIDES_TRANS

      Therefore, PROD_SET t divides m           by pairwise_coprime_prod_set_divides, Claim
             and PROD_SET t divides n           by pairwise_coprime_prod_set_divides, Claim

   (2) !x. x divides m /\ x divides n ==> x divides PROD_SET t
       Let k = PROD_SET t, sx = prime_divisors x, tx = IMAGE (\p. p ** ppidx x) sx.
       Note 0 < x                    by ZERO_DIVIDES, 0 < m
        and x = PROD_SET tx          by basic_prime_factorisation, 0 < x
       The aim is to show: PROD_SET tx divides k

       Note FINITE sx                by prime_divisors_finite
        ==> FINITE tx                by IMAGE_FINITE
        and PAIRWISE_COPRIME tx      by prime_divisors_element, prime_powers_coprime

       Claim: !z. z IN tx ==> z divides k
       Proof: Note z IN tx
               ==> ?p. p IN sx /\ (z = p ** ppidx x)       by IN_IMAGE
              Note prime p                                 by prime_divisors_element
               and sx SUBSET sm /\ sx SUBSET sn            by prime_divisors_divisor_subset, x | m, x | n
               ==> p IN sm /\ p IN sn                      by SUBSET_DEF
                or p IN s                                  by IN_INTER
              Also ppidx x <= MIN (ppidx m) (ppidx n)      by prime_power_index_common_divisor
               ==> z divides p ** MIN (ppidx m) (ppidx n)  by prime_power_divides_iff
               But p ** MIN (ppidx m) (ppidx n) IN t       by IN_IMAGE
               ==> p ** MIN (ppidx m) (ppidx n) divides k  by PROD_SET_ELEMENT_DIVIDES
                or z divides k                             by DIVIDES_TRANS

       Therefore, PROD_SET tx divides k                    by pairwise_coprime_prod_set_divides
*)
val gcd_prime_factorisation = store_thm(
  "gcd_prime_factorisation",
  ``!m n. 0 < m /\ 0 < n ==>
         (gcd m n = PROD_SET (IMAGE (\p. p ** (MIN (ppidx m) (ppidx n)))
                             ((prime_divisors m) INTER (prime_divisors n))))``,
  rpt strip_tac >>
  qabbrev_tac `sm = prime_divisors m` >>
  qabbrev_tac `sn = prime_divisors n` >>
  qabbrev_tac `s = sm INTER sn` >>
  qabbrev_tac `tm = IMAGE (\p. p ** ppidx m) sm` >>
  qabbrev_tac `tn = IMAGE (\p. p ** ppidx m) sn` >>
  qabbrev_tac `t = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) s` >>
  `FINITE sm /\ FINITE sn /\ FINITE s` by rw[prime_divisors_finite, Abbr`sm`, Abbr`sn`, Abbr`s`] >>
  `FINITE tm /\ FINITE tn /\ FINITE t` by rw[Abbr`tm`, Abbr`tn`, Abbr`t`] >>
  `PAIRWISE_COPRIME t` by
  (rw[Abbr`t`] >>
  `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element, IN_INTER] >>
  rw[prime_powers_coprime]) >>
  `!x. x IN t ==> x divides m /\ x divides n` by
    (ntac 2 strip_tac >>
  qabbrev_tac `f = \p:num. p ** MIN (ppidx m) (ppidx n)` >>
  `?p. p IN s /\ p IN sm /\ p IN sn /\ (x = p ** MIN (ppidx m) (ppidx n))` by metis_tac[IN_IMAGE, IN_INTER] >>
  `prime p` by metis_tac[prime_divisors_element] >>
  `p ** ppidx m divides m /\ p ** ppidx n divides n` by rw[prime_power_factor_divides] >>
  `MIN (ppidx m) (ppidx n) <= ppidx m /\ MIN (ppidx m) (ppidx n) <= ppidx n` by rw[] >>
  metis_tac[prime_power_divides_iff, DIVIDES_TRANS]) >>
  rw[GCD_PROPERTY] >-
  rw[pairwise_coprime_prod_set_divides] >-
  rw[pairwise_coprime_prod_set_divides] >>
  qabbrev_tac `k = PROD_SET t` >>
  qabbrev_tac `sx = prime_divisors x` >>
  qabbrev_tac `tx = IMAGE (\p. p ** ppidx x) sx` >>
  `0 < x` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `x = PROD_SET tx` by rw[basic_prime_factorisation, Abbr`tx`, Abbr`sx`] >>
  `FINITE sx` by rw[prime_divisors_finite, Abbr`sx`] >>
  `FINITE tx` by rw[Abbr`tx`] >>
  `PAIRWISE_COPRIME tx` by
  (rw[Abbr`tx`] >>
  `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element] >>
  rw[prime_powers_coprime]) >>
  `!z. z IN tx ==> z divides k` by
    (rw[Abbr`tx`] >>
  `prime p` by metis_tac[prime_divisors_element] >>
  `p IN sm /\ p IN sn` by metis_tac[prime_divisors_divisor_subset, SUBSET_DEF] >>
  `p IN s` by metis_tac[IN_INTER] >>
  `ppidx x <= MIN (ppidx m) (ppidx n)` by rw[prime_power_index_common_divisor] >>
  `(p ** ppidx x) divides p ** MIN (ppidx m) (ppidx n)` by rw[prime_power_divides_iff] >>
  qabbrev_tac `f = \p:num. p ** MIN (ppidx m) (ppidx n)` >>
  `p ** MIN (ppidx m) (ppidx n) IN t` by metis_tac[IN_IMAGE] >>
  metis_tac[PROD_SET_ELEMENT_DIVIDES, DIVIDES_TRANS]) >>
  rw[pairwise_coprime_prod_set_divides]);

(* This is a major milestone theorem. *)

(* Theorem: 0 < m /\ 0 < n ==>
           (lcm m n = PROD_SET (IMAGE (\p. p ** (MAX (ppidx m) (ppidx n)))
                               ((prime_divisors m) UNION (prime_divisors n)))) *)
(* Proof:
   Let sm = prime_divisors m, sn = prime_divisors n, s = sm UNION sn.
   Let tm = IMAGE (\p. p ** ppidx m) sm, tn = IMAGE (\p. p ** ppidx m) sn,
        t = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) s.
   The goal is: lcm m n = PROD_SET t

   By LCM_PROPERTY, this is to show:
   (1) m divides PROD_SET t /\ n divides PROD_SET t
       Let k = PROD_SET t.
       Note m = PROD_SET tm      by basic_prime_factorisation, 0 < m
        and n = PROD_SET tn      by basic_prime_factorisation, 0 < n
      Also PAIRWISE_COPRIME tm   by prime_divisors_element, prime_powers_coprime
       and PAIRWISE_COPRIME tn   by prime_divisors_element, prime_powers_coprime

      Claim: !z. z IN tm ==> z divides k
      Proof: Note z IN tm
              ==> ?p. p IN sm /\ (z = p ** ppidx m)       by IN_IMAGE
              ==> p IN s                                  by IN_UNION
              and prime p                                 by prime_divisors_element
             Note ppidx m <= MAX (ppidx m) (ppidx n)      by MAX_DEF
              ==> z divides p ** MAX (ppidx m) (ppidx n)  by prime_power_divides_iff
              But p ** MAX (ppidx m) (ppidx n) IN t       by IN_IMAGE
              and p ** MAX (ppidx m) (ppidx n) divides k  by PROD_SET_ELEMENT_DIVIDES
             Thus z divides k                             by DIVIDES_TRANS

      Similarly, !z. z IN tn ==> z divides k
      Hence (PROD_SET tm) divides k /\ (PROD_SET tn) divides k    by pairwise_coprime_prod_set_divides
         or             m divides k /\ n divides k                by above

   (2) m divides x /\ n divides x ==> PROD_SET t divides x
       If x = 0, trivially true      by ALL_DIVIDES_ZERO
       If x <> 0, then 0 < x.
       Note PAIRWISE_COPRIME t       by prime_divisors_element, prime_powers_coprimem IN_UNION

       Claim: !z. z IN t ==> z divides x
       Proof: Note z IN t
               ==> ?p. p IN s /\ (z = p ** MAX (ppidx m) (ppidx n))   by IN_IMAGE
                or prime p                               by prime_divisors_element, IN_UNION
              Note MAX (ppidx m) (ppidx n) <= ppidx x    by prime_power_index_common_multiple, 0 < x
                so z divides p ** ppidx x                by prime_power_divides_iff
               But p ** ppidx x divides x                by prime_power_factor_divides
              Thus z divides x                           by DIVIDES_TRANS
       Hence PROD_SET t divides x                        by pairwise_coprime_prod_set_divides
*)
val lcm_prime_factorisation = store_thm(
  "lcm_prime_factorisation",
  ``!m n. 0 < m /\ 0 < n ==>
         (lcm m n = PROD_SET (IMAGE (\p. p ** (MAX (ppidx m) (ppidx n)))
                             ((prime_divisors m) UNION (prime_divisors n))))``,
  rpt strip_tac >>
  qabbrev_tac `sm = prime_divisors m` >>
  qabbrev_tac `sn = prime_divisors n` >>
  qabbrev_tac `s = sm UNION sn` >>
  qabbrev_tac `tm = IMAGE (\p. p ** ppidx m) sm` >>
  qabbrev_tac `tn = IMAGE (\p. p ** ppidx n) sn` >>
  qabbrev_tac `t = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) s` >>
  `FINITE sm /\ FINITE sn /\ FINITE s` by rw[prime_divisors_finite, Abbr`sm`, Abbr`sn`, Abbr`s`] >>
  `FINITE tm /\ FINITE tn /\ FINITE t` by rw[Abbr`tm`, Abbr`tn`, Abbr`t`] >>
  rw[LCM_PROPERTY] >| [
    qabbrev_tac `k = PROD_SET t` >>
    `m = PROD_SET tm` by rw[basic_prime_factorisation, Abbr`tm`, Abbr`sm`] >>
    `PAIRWISE_COPRIME tm` by
  (rw[Abbr`tm`] >>
    `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element] >>
    rw[prime_powers_coprime]) >>
    `!z. z IN tm ==> z divides k` by
    (rw[Abbr`tm`] >>
    `prime p` by metis_tac[prime_divisors_element] >>
    `p IN s` by metis_tac[IN_UNION] >>
    `ppidx m <= MAX (ppidx m) (ppidx n)` by rw[] >>
    `(p ** ppidx m) divides p ** MAX (ppidx m) (ppidx n)` by rw[prime_power_divides_iff] >>
    qabbrev_tac `f = \p:num. p ** MAX (ppidx m) (ppidx n)` >>
    `p ** MAX (ppidx m) (ppidx n) IN t` by metis_tac[IN_IMAGE] >>
    metis_tac[PROD_SET_ELEMENT_DIVIDES, DIVIDES_TRANS]) >>
    rw[pairwise_coprime_prod_set_divides],
    qabbrev_tac `k = PROD_SET t` >>
    `n = PROD_SET tn` by rw[basic_prime_factorisation, Abbr`tn`, Abbr`sn`] >>
    `PAIRWISE_COPRIME tn` by
  (rw[Abbr`tn`] >>
    `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element] >>
    rw[prime_powers_coprime]) >>
    `!z. z IN tn ==> z divides k` by
    (rw[Abbr`tn`] >>
    `prime p` by metis_tac[prime_divisors_element] >>
    `p IN s` by metis_tac[IN_UNION] >>
    `ppidx n <= MAX (ppidx m) (ppidx n)` by rw[] >>
    `(p ** ppidx n) divides p ** MAX (ppidx m) (ppidx n)` by rw[prime_power_divides_iff] >>
    qabbrev_tac `f = \p:num. p ** MAX (ppidx m) (ppidx n)` >>
    `p ** MAX (ppidx m) (ppidx n) IN t` by metis_tac[IN_IMAGE] >>
    metis_tac[PROD_SET_ELEMENT_DIVIDES, DIVIDES_TRANS]) >>
    rw[pairwise_coprime_prod_set_divides],
    Cases_on `x = 0` >-
    rw[] >>
    `0 < x` by decide_tac >>
    `PAIRWISE_COPRIME t` by
  (rw[Abbr`t`] >>
    `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element, IN_UNION] >>
    rw[prime_powers_coprime]) >>
    `!z. z IN t ==> z divides x` by
    (rw[Abbr`t`] >>
    `prime p` by metis_tac[prime_divisors_element, IN_UNION] >>
    `MAX (ppidx m) (ppidx n) <= ppidx x` by rw[prime_power_index_common_multiple] >>
    `p ** MAX (ppidx m) (ppidx n) divides p ** ppidx x` by rw[prime_power_divides_iff] >>
    `p ** ppidx x divides x` by rw[prime_power_factor_divides] >>
    metis_tac[DIVIDES_TRANS]) >>
    rw[pairwise_coprime_prod_set_divides]
  ]);

(* Another major milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* GCD and LCM special coprime decompositions                                *)
(* ------------------------------------------------------------------------- *)

(*
Notes
=|===
Given two numbers m and n, with d = gcd m n, and cofactors a = m/d, b = n/d.
Is it true that gcd a n = 1 ?

Take m = 2^3 * 3^2 = 8 * 9 = 72,  n = 2^2 * 3^3 = 4 * 27 = 108
Then gcd m n = d = 2^2 * 3^2 = 4 * 9 = 36, with cofactors a = 2, b = 3.
In this case, gcd a n = gcd 2 108 <> 1.
But lcm m n = 2^3 * 3^3 = 8 * 27 = 216

Ryan Vinroot's method:
Take m = 2^7 * 3^5 * 5^4 * 7^4    n = 2^6 * 3*7 * 5^4 * 11^4
Then m = a b c d = (7^4) (5^4) (2^7) (3^5)
 and n = x y z t = (11^4) (5^4) (3^7) (2^6)
Note b = y always, and lcm m n = a b c x z, gcd m n = d y z
Define P = a b c, Q = x z, then coprime P Q, and lcm P Q = a b c x z = lcm m n = P * Q

a = PROD (all prime factors of m which are not prime factors of n) = 7^4
b = PROD (all prime factors of m common with m and equal powers in both) = 5^4
c = PROD (all prime factors of m common with m but more powers in m) = 2^7
d = PROD (all prime factors of m common with m but more powers in n) = 3^5

x = PROD (all prime factors of n which are not prime factors of m) = 11^4
y = PROD (all prime factors of n common with n and equal powers in both) = 5^4
z = PROD (all prime factors of n common with n but more powers in n) = 3^7
t = PROD (all prime factors of n common with n but more powers in m) = 2^6

Let d = gcd m n. If d <> 1, then it consists of prime powers, e.g. 2^3 * 3^2 * 5
Since d is to take the minimal of prime powers common to both m n,
each prime power in d must occur fully in either m or n.
e.g. it may be the case that:   m = 2^3 * 3 * 5 * a,   n = 2 * 3^2 * 5 * b
where a, b don't have prime factors 2, 3, 5, and coprime a b.
and lcm m n = a * b * 2^3 * 3^2 * 5, taking the maximal of prime powers common to both.
            = (a * 2^3) * (b * 3^2 * 5) = P * Q with coprime P Q.

Ryan Vinroot's method (again):
Take m = 2^7 * 3^5 * 5^4 * 7^4    n = 2^6 * 3*7 * 5^4 * 11^4
Then gcd m n = 2^6 * 3^5 * 5^4, lcm m n = 2^7 * 3^7 * 5^4 * 7^4 * 11^4
Take d = 3^5 * 5^4  (compare m to gcd n m, take the full factors of gcd in m )
     e = gcd n m / d = 2^6        (take what is left over)
Then P = m / d = 2^7 * 7^4
     Q = n / e = 3^7 * 5^4 * 11^4
 so P | m, there is ord p = P.
and Q | n, there is ord q = Q.
and coprime P Q, so ord (p * q) = P * Q = lcm m n.

d = PROD {p ** ppidx m | p | prime p /\ p | (gcd m n) /\ (ppidx (gcd n m) = ppidx m)}
e = gcd n m / d

prime_factorisation  |- !n. 0 < n ==> (n = PROD_SET (prime_power_divisors n)

This is because:   m = 2^7 * 3^5 * 5^4 * 7^4 * 11^0
                   n = 2^6 * 3^7 * 5^4 * 7^0 * 11^4
we know that gcd m n = 2^6 * 3^5 * 5^4 * 7^0 * 11^0   taking minimum
             lcm m n = 2^7 * 3^7 * 5^4 * 7^4 * 11^4   taking maximum
Thus, using gcd m n as a guide,
pick               d = 2^0 * 3^5 * 5^4 , taking common minimum,
Then   P = m / d  will remove these common minimum from m,
but    Q = n / e = n / (gcd m n / d) = n * d / gcd m n   will include their common maximum
This separation of prime factors keep coprime P Q, but P * Q = lcm m n.

*)

(* Overload the park sets *)
val _ = overload_on ("common_prime_divisors",
        ``\m n. (prime_divisors m) INTER (prime_divisors n)``);
val _ = overload_on ("total_prime_divisors",
        ``\m n. (prime_divisors m) UNION (prime_divisors n)``);
val _ = overload_on ("park_on",
        ``\m n. {p | p IN common_prime_divisors m n /\ ppidx m <= ppidx n}``);
val _ = overload_on ("park_off",
        ``\m n. {p | p IN common_prime_divisors m n /\ ppidx n < ppidx m}``);
(* Overload the parking divisor of GCD *)
val _ = overload_on("park", ``\m n. PROD_SET (IMAGE (\p. p ** ppidx m) (park_on m n))``);

(* Note:
The basic one is park_on m n, defined only for 0 < m and 0 < n.
*)

(* Theorem: p IN common_prime_divisors m n <=> p IN prime_divisors m /\ p IN prime_divisors n *)
(* Proof: by IN_INTER *)
val common_prime_divisors_element = store_thm(
  "common_prime_divisors_element",
  ``!m n p. p IN common_prime_divisors m n <=> p IN prime_divisors m /\ p IN prime_divisors n``,
  rw[]);

(* Theorem: 0 < m /\ 0 < n ==> FINITE (common_prime_divisors m n) *)
(* Proof: by prime_divisors_finite, FINITE_INTER *)
val common_prime_divisors_finite = store_thm(
  "common_prime_divisors_finite",
  ``!m n. 0 < m /\ 0 < n ==> FINITE (common_prime_divisors m n)``,
  rw[prime_divisors_finite]);

(* Theorem: PAIRWISE_COPRIME (common_prime_divisors m n) *)
(* Proof:
   Note x IN prime_divisors m ==> prime x    by prime_divisors_element
    and y IN prime_divisors n ==> prime y    by prime_divisors_element
    and x <> y ==> coprime x y               by primes_coprime
*)
val common_prime_divisors_pairwise_coprime = store_thm(
  "common_prime_divisors_pairwise_coprime",
  ``!m n. PAIRWISE_COPRIME (common_prime_divisors m n)``,
  metis_tac[prime_divisors_element, primes_coprime, IN_INTER]);

(* Theorem: PAIRWISE_COPRIME (IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n)) *)
(* Proof:
   Note (prime_divisors m) SUBSET prime            by prime_divisors_subset_prime
     so (common_prime_divisors m n) SUBSET prime   by SUBSET_INTER_SUBSET
   Thus true                                       by pairwise_coprime_for_prime_powers
*)
val common_prime_divisors_min_image_pairwise_coprime = store_thm(
  "common_prime_divisors_min_image_pairwise_coprime",
  ``!m n. PAIRWISE_COPRIME (IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n))``,
  metis_tac[prime_divisors_subset_prime, SUBSET_INTER_SUBSET, pairwise_coprime_for_prime_powers]);

(* Theorem: p IN total_prime_divisors m n <=> p IN prime_divisors m \/ p IN prime_divisors n *)
(* Proof: by IN_UNION *)
val total_prime_divisors_element = store_thm(
  "total_prime_divisors_element",
  ``!m n p. p IN total_prime_divisors m n <=> p IN prime_divisors m \/ p IN prime_divisors n``,
  rw[]);

(* Theorem: 0 < m /\ 0 < n ==> FINITE (total_prime_divisors m n) *)
(* Proof: by prime_divisors_finite, FINITE_UNION *)
val total_prime_divisors_finite = store_thm(
  "total_prime_divisors_finite",
  ``!m n. 0 < m /\ 0 < n ==> FINITE (total_prime_divisors m n)``,
  rw[prime_divisors_finite]);

(* Theorem: PAIRWISE_COPRIME (total_prime_divisors m n) *)
(* Proof:
   Note x IN prime_divisors m ==> prime x    by prime_divisors_element
    and y IN prime_divisors n ==> prime y    by prime_divisors_element
    and x <> y ==> coprime x y               by primes_coprime
*)
val total_prime_divisors_pairwise_coprime = store_thm(
  "total_prime_divisors_pairwise_coprime",
  ``!m n. PAIRWISE_COPRIME (total_prime_divisors m n)``,
  metis_tac[prime_divisors_element, primes_coprime, IN_UNION]);

(* Theorem: PAIRWISE_COPRIME (IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n)) *)
(* Proof:
   Note prime_divisors m SUBSET prime      by prime_divisors_subset_prime
    and prime_divisors n SUBSET prime      by prime_divisors_subset_prime
     so (total_prime_divisors m n) SUBSET prime    by UNION_SUBSET
   Thus true                                       by pairwise_coprime_for_prime_powers
*)
val total_prime_divisors_max_image_pairwise_coprime = store_thm(
  "total_prime_divisors_max_image_pairwise_coprime",
  ``!m n. PAIRWISE_COPRIME (IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n))``,
  metis_tac[prime_divisors_subset_prime, UNION_SUBSET, pairwise_coprime_for_prime_powers]);

(* Theorem: p IN park_on m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx m <= ppidx n *)
(* Proof: by IN_INTER *)
val park_on_element = store_thm(
  "park_on_element",
  ``!m n p. p IN park_on m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx m <= ppidx n``,
  rw[] >>
  metis_tac[]);

(* Theorem: p IN park_off m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx n < ppidx m *)
(* Proof: by IN_INTER *)
val park_off_element = store_thm(
  "park_off_element",
  ``!m n p. p IN park_off m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx n < ppidx m``,
  rw[] >>
  metis_tac[]);

(* Theorem: park_off m n = (common_prime_divisors m n) DIFF (park_on m n) *)
(* Proof: by EXTENSION, NOT_LESS_EQUAL *)
val park_off_alt = store_thm(
  "park_off_alt",
  ``!m n. park_off m n = (common_prime_divisors m n) DIFF (park_on m n)``,
  rw[EXTENSION] >>
  metis_tac[NOT_LESS_EQUAL]);

(* Theorem: park_on m n SUBSET common_prime_divisors m n *)
(* Proof: by SUBSET_DEF *)
val park_on_subset_common = store_thm(
  "park_on_subset_common",
  ``!m n. park_on m n SUBSET common_prime_divisors m n``,
  rw[SUBSET_DEF]);

(* Theorem: park_off m n SUBSET common_prime_divisors m n *)
(* Proof: by SUBSET_DEF *)
val park_off_subset_common = store_thm(
  "park_off_subset_common",
  ``!m n. park_off m n SUBSET common_prime_divisors m n``,
  rw[SUBSET_DEF]);

(* Theorem: park_on m n SUBSET total_prime_divisors m n *)
(* Proof: by SUBSET_DEF *)
val park_on_subset_total = store_thm(
  "park_on_subset_total",
  ``!m n. park_on m n SUBSET total_prime_divisors m n``,
  rw[SUBSET_DEF]);

(* Theorem: park_off m n SUBSET total_prime_divisors m n *)
(* Proof: by SUBSET_DEF *)
val park_off_subset_total = store_thm(
  "park_off_subset_total",
  ``!m n. park_off m n SUBSET total_prime_divisors m n``,
  rw[SUBSET_DEF]);

(* Theorem: common_prime_divisors m n =|= park_on m n # park_off m n *)
(* Proof:
   Let s = common_prime_divisors m n.
   Note park_on m n SUBSET s                     by park_on_subset_common
    and park_off m n = s DIFF (park_on m n)      by park_off_alt
     so s = park_on m n UNION park_off m n /\
        DISJOINT (park_on m n) (park_off m n)    by partition_by_subset
*)
val park_on_off_partition = store_thm(
  "park_on_off_partition",
  ``!m n. common_prime_divisors m n =|= park_on m n # park_off m n``,
  metis_tac[partition_by_subset, park_on_subset_common, park_off_alt]);

(* Theorem: 1 NOTIN (IMAGE (\p. p ** ppidx m) (park_off m n)) *)
(* Proof:
   By contradiction, suppse 1 IN (IMAGE (\p. p ** ppidx m) (park_off m n)).
   Then ?p. p IN park_off m n /\ (1 = p ** ppidx m)   by IN_IMAGE
     or p IN prime_divisors m /\
        p IN prime_divisors n /\ ppidx n < ppidx m    by park_off_element
    But prime p                     by prime_divisors_element
    and p <> 1                      by NOT_PRIME_1
   Thus ppidx m = 0                 by EXP_EQ_1
     or ppidx n < 0, which is F     by NOT_LESS_0
*)
val park_off_image_has_not_1 = store_thm(
  "park_off_image_has_not_1",
  ``!m n. 1 NOTIN (IMAGE (\p. p ** ppidx m) (park_off m n))``,
  rw[] >>
  spose_not_then strip_assume_tac >>
  `prime p` by metis_tac[prime_divisors_element] >>
  `p <> 1` by metis_tac[NOT_PRIME_1] >>
  decide_tac);

(*
For the example,
This is because:   m = 2^7 * 3^5 * 5^4 * 7^4 * 11^0
                   n = 2^6 * 3^7 * 5^4 * 7^0 * 11^4
we know that gcd m n = 2^6 * 3^5 * 5^4 * 7^0 * 11^0   taking minimum
             lcm m n = 2^7 * 3^7 * 5^4 * 7^4 * 11^4   taking maximum
Thus, using gcd m n as a guide,
pick               d = 2^0 * 3^5 * 5^4 , taking common minimum,
Then   P = m / d  will remove these common minimum from m,
but    Q = n / e = n / (gcd m n / d) = n * d / gcd m n   will include their common maximum
This separation of prime factors keep coprime P Q, but P * Q = lcm m n.
common_prime_divisors m n = {2; 3; 5}  s = {2^6; 3^5; 5^4} with MIN
park_on m n = {3; 5}  u = IMAGE (\p. p ** ppidx m) (park_on m n) = {3^5; 5^4}
park_off m n = {2}    v = IMAGE (\p. p ** ppidx n) (park_off m n) = {2^6}
Note                      IMAGE (\p. p ** ppidx m) (park_off m n) = {2^7}
and                       IMAGE (\p. p ** ppidx n) (park_on m n) = {3^7; 5^4}

total_prime_divisors m n = {2; 3; 5; 7; 11}  s = {2^7; 3^7; 5^4; 7^4; 11^4} with MAX
sm = (prime_divisors m) DIFF (park_on m n) = {2; 7}, u = IMAGE (\p. p ** ppidx m) sm = {2^7; 7^4}
sn = (prime_divisors n) DIFF (park_off m n) = {3; 5; 11}, v = IMAGE (\p. p ** ppidx n) sn = {3^7; 5^4; 11^4}

park_on_element
|- !m n p. p IN park_on m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx m <= ppidx n
park_off_element
|- !m n p. p IN park_off m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx n < ppidx m
*)

(* Theorem: let s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n) in
            let u = IMAGE (\p. p ** ppidx m) (park_on m n) in
            let v = IMAGE (\p. p ** ppidx n) (park_off m n) in
            0 < m ==> s =|= u # v *)
(* Proof:
   This is to show:
   (1) s = u UNION v
       By EXTENSION, this is to show:
       (a) !x. x IN s ==> x IN u \/ x IN v            by IN_UNION
           Note x IN s
            ==> ?p. (x = p ** MIN (ppidx m) (ppidx n)) /\
                 p IN common_prime_divisors m n       by IN_IMAGE
          If ppidx m <= ppidx n
             Then MIN (ppidx m) (ppidx n) = ppidx m   by MIN_DEF
              and p IN park_on m n                    by common_prime_divisors_element, park_on_element
              ==> x IN u                              by IN_IMAGE
          If ~(ppidx m <= ppidx n),
            so ppidx n < ppidx m                      by NOT_LESS_EQUAL
             Then MIN (ppidx m) (ppidx n) = ppidx n   by MIN_DEF
              and p IN park_off m n                   by common_prime_divisors_element, park_off_element
              ==> x IN v                              by IN_IMAGE
       (b) x IN u ==> x IN s
           Note x IN u
            ==> ?p. (x = p ** ppidx m) /\
                    p IN park_on m n                  by IN_IMAGE
            ==> ppidx m <= ppidx n                    by park_on_element
           Thus MIN (ppidx m) (ppidx n) = ppidx m     by MIN_DEF
             so p IN common_prime_divisors m n        by park_on_subset_common, SUBSET_DEF
            ==> x IN s                                by IN_IMAGE
       (c) x IN v ==> x IN s
           Note x IN v
            ==> ?p. (x = p ** ppidx n) /\
                    p IN park_off m n                 by IN_IMAGE
            ==> ppidx n < ppidx m                     by park_off_element
           Thus MIN (ppidx m) (ppidx n) = ppidx n     by MIN_DEF
             so p IN common_prime_divisors m n        by park_off_subset_common, SUBSET_DEF
            ==> x IN s                                by IN_IMAGE
   (2) DISJOINT u v
       This is to show: u INTER v = {}                by DISJOINT_DEF
       By contradiction, suppse u INTER v <> {}.
       Then ?x. x IN u /\ x IN v                      by MEMBER_NOT_EMPTY, IN_INTER
       Thus ?p. p IN park_on m n /\ (x = p ** ppidx m)                  by IN_IMAGE
        and ?q. q IN park_off m n /\ (x = q ** prime_power_index q n)   by IN_IMAGE
        ==> prime p /\ prime q /\ p divides m         by park_on_element, park_off_element
                                                         prime_divisors_element
       Also 0 < ppidx m                               by prime_power_index_pos, p divides m, 0 < m
        ==> p = q                                     by prime_powers_eq
       Thus p IN (park_on m n) INTER (park_off m n)   by IN_INTER
        But DISJOINT (park_on m n) (park_off m n)     by park_on_off_partition
         so there is a contradiction                  by IN_DISJOINT
*)
val park_on_off_common_image_partition = store_thm(
  "park_on_off_common_image_partition",
  ``!m n. let s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n) in
         let u = IMAGE (\p. p ** ppidx m) (park_on m n) in
         let v = IMAGE (\p. p ** ppidx n) (park_off m n) in
         0 < m ==> s =|= u # v``,
  rpt strip_tac >>
  qabbrev_tac `f = \p:num. p ** MIN (ppidx m) (ppidx n)` >>
  qabbrev_tac `f1 = \p:num. p ** ppidx m` >>
  qabbrev_tac `f2 = \p:num. p ** ppidx n` >>
  rw_tac std_ss[] >| [
    rw[EXTENSION, EQ_IMP_THM] >| [
      `?p. (x = p ** MIN (ppidx m) (ppidx n)) /\ p IN common_prime_divisors m n` by metis_tac[IN_IMAGE] >>
      Cases_on `ppidx m <= ppidx n` >| [
        `MIN (ppidx m) (ppidx n) = ppidx m` by rw[MIN_DEF] >>
        `p IN park_on m n` by metis_tac[common_prime_divisors_element, park_on_element] >>
        metis_tac[IN_IMAGE],
        `MIN (ppidx m) (ppidx n) = ppidx n` by rw[MIN_DEF] >>
        `p IN park_off m n` by metis_tac[common_prime_divisors_element, park_off_element, NOT_LESS_EQUAL] >>
        metis_tac[IN_IMAGE]
      ],
      `?p. (x = p ** ppidx m) /\ p IN park_on m n` by metis_tac[IN_IMAGE] >>
      `ppidx m <= ppidx n` by metis_tac[park_on_element] >>
      `MIN (ppidx m) (ppidx n) = ppidx m` by rw[MIN_DEF] >>
      `p IN common_prime_divisors m n` by metis_tac[park_on_subset_common, SUBSET_DEF] >>
      metis_tac[IN_IMAGE],
      `?p. (x = p ** ppidx n) /\ p IN park_off m n` by metis_tac[IN_IMAGE] >>
      `ppidx n < ppidx m` by metis_tac[park_off_element] >>
      `MIN (ppidx m) (ppidx n) = ppidx n` by rw[MIN_DEF] >>
      `p IN common_prime_divisors m n` by metis_tac[park_off_subset_common, SUBSET_DEF] >>
      metis_tac[IN_IMAGE]
    ],
    rw[DISJOINT_DEF] >>
    spose_not_then strip_assume_tac >>
    `?x. x IN u /\ x IN v` by metis_tac[MEMBER_NOT_EMPTY, IN_INTER] >>
    `?p. p IN park_on m n /\ (x = p ** ppidx m)` by prove_tac[IN_IMAGE] >>
    `?q. q IN park_off m n /\ (x = q ** prime_power_index q n)` by prove_tac[IN_IMAGE] >>
    `prime p /\ prime q /\ p divides m` by metis_tac[park_on_element, park_off_element, prime_divisors_element] >>
    `0 < ppidx m` by rw[prime_power_index_pos] >>
    `p = q` by metis_tac[prime_powers_eq] >>
    metis_tac[park_on_off_partition, IN_DISJOINT]
  ]);

(* Theorem: 0 < m /\ 0 < n ==> let a = park m n in let b = gcd m n DIV a in
           (b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n))) /\ (gcd m n = a * b) /\ coprime a b *)
(* Proof:
   Let s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n),
       u = IMAGE (\p. p ** ppidx m) (park_on m n),
       v = IMAGE (\p. p ** ppidx n) (park_off m n).
   Then s =|= u # v                         by park_on_off_common_image_partition
   Let a = PROD_SET u, b = PROD_SET v, c = PROD_SET s.
   Then FINITE s                            by common_prime_divisors_finite, IMAGE_FINITE, 0 < m, 0 < n
    and PAIRWISE_COPRIME s                  by common_prime_divisors_min_image_pairwise_coprime
    ==> (c = a * b) /\ coprime a b          by pairwise_coprime_prod_set_partition
   Note c = gcd m n                         by gcd_prime_factorisation
    and a = park m n                        by notation
   Note c <> 0                              by GCD_EQ_0, 0 < m, 0 < n
   Thus a <> 0, or 0 < a                    by MULT_EQ_0
     so b = c DIV a                         by DIV_SOLVE_COMM, 0 < a
   Therefore,
        b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n)) /\
        gcd m n = a * b /\ coprime a b      by above
*)

Theorem gcd_park_decomposition:
  !m n. 0 < m /\ 0 < n ==> let a = park m n in let b = gcd m n DIV a in
        b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n)) /\
        gcd m n = a * b /\ coprime a b
Proof
  rpt strip_tac >>
  qabbrev_tac `s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n)` >>
  qabbrev_tac `u = IMAGE (\p. p ** ppidx m) (park_on m n)` >>
  qabbrev_tac `v = IMAGE (\p. p ** ppidx n) (park_off m n)` >>
  `s =|= u # v` by metis_tac[park_on_off_common_image_partition] >>
  qabbrev_tac `a = PROD_SET u` >>
  qabbrev_tac `b = PROD_SET v` >>
  qabbrev_tac `c = PROD_SET s` >>
  `FINITE s` by rw[common_prime_divisors_finite, Abbr`s`] >>
  `PAIRWISE_COPRIME s` by metis_tac[common_prime_divisors_min_image_pairwise_coprime] >>
  `(c = a * b) /\ coprime a b`
    by (simp[Abbr`a`, Abbr`b`, Abbr`c`] >>
        metis_tac[pairwise_coprime_prod_set_partition]) >>
  metis_tac[gcd_prime_factorisation, GCD_EQ_0, MULT_EQ_0, DIV_SOLVE_COMM,
            NOT_ZERO_LT_ZERO]
QED

(* Theorem: 0 < m /\ 0 < n ==> let a = park m n in let b = gcd m n DIV a in
            (gcd m n = a * b) /\ coprime a b *)
(* Proof: by gcd_park_decomposition *)
val gcd_park_decompose = store_thm(
  "gcd_park_decompose",
  ``!m n. 0 < m /\ 0 < n ==> let a = park m n in let b = gcd m n DIV a in
         (gcd m n = a * b) /\ coprime a b``,
  metis_tac[gcd_park_decomposition]);

(*
For the example:
total_prime_divisors m n = {2; 3; 5; 7; 11}  s = {2^7; 3^7; 5^4; 7^4; 11^4} with MAX
sm = (prime_divisors m) DIFF (park_on m n) = {2; 7}, u = IMAGE (\p. p ** ppidx m) sm = {2^7; 7^4}
sn = (prime_divisors n) DIFF (park_off m n) = {3; 5; 11}, v = IMAGE (\p. p ** ppidx n) sn = {3^7; 5^4; 11^4}
*)

(* Theorem: let s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n) in
            let u = IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n)) in
            let v = IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n)) in
            0 < m /\ 0 < n ==> s =|= u # v *)
(* Proof:
   This is to show:
   (1) s = u UNION v
       By EXTENSION, this is to show:
       (a) x IN s ==> x IN u \/ x IN v
           Note x IN s
            ==> ?p. p IN total_prime_divisors m n /\
                    (x = p ** MAX (ppidx m) (ppidx n))         by IN_IMAGE
           By total_prime_divisors_element,

           If p IN prime_divisors m,
              Then prime p /\ p divides m                      by prime_divisors_element
              If p IN park_on m n,
                 Then p IN prime_divisors n /\
                      ppidx m <= ppidx n                       by park_on_element
                  ==> MAX (ppidx m) (ppidx n) = ppidx n        by MAX_DEF
                 Note DISJOINT (park_on m n) (park_off m n)    by park_on_off_partition
                 Thus p NOTIN park_off m n                     by IN_DISJOINT
                  ==> p IN prime_divisors n DIFF park_off m n  by IN_DIFF
                 Therefore x IN v                              by IN_IMAGE
              If p NOTIN park_on m n,
                 Then p IN prime_divisors m DIFF park_on m n   by IN_DIFF
                 By park_on_element, either [1] or [2]:
                 [1] p NOTIN prime_divisors n
                     Then ppidx n = 0   by prime_divisors_element, prime_power_index_eq_0, 0 < n
                      ==> MAX (ppidx m) (ppidx n) = ppidx m    by MAX_DEF
                     Therefore x IN u                          by IN_IMAGE
                 [2] ~(ppidx m <= ppidx n)
                     Then MAX (ppidx m) (ppidx n) = ppidx m    by MAX_DEF
                     Therefore x IN u                          by IN_IMAGE

           If p IN prime_divisors n,
              Then prime p /\ p divides n                      by prime_divisors_element
              If p IN park_off m n,
                 Then p IN prime_divisors m /\
                      ppidx n < ppidx m                        by park_off_element
                  ==> MAX (ppidx m) (ppidx n) = ppidx m        by MAX_DEF
                 Note DISJOINT (park_on m n) (park_off m n)    by park_on_off_partition
                 Thus p NOTIN park_on m n                      by IN_DISJOINT
                  ==> p IN prime_divisors m DIFF park_on m n   by IN_DIFF
                 Therefore x IN u                              by IN_IMAGE
              If p NOTIN park_off m n,
                 Then p IN prime_divisors n DIFF park_off m n  by IN_DIFF
                 By park_off_element, either [1] or [2]:
                 [1] p NOTIN prime_divisors m
                     Then ppidx m = 0   by prime_divisors_element, prime_power_index_eq_0, 0 < m
                      ==> MAX (ppidx m) (ppidx n) = ppidx n    by MAX_DEF
                     Therefore x IN v                          by IN_IMAGE
                 [2] ~(ppidx n < ppidx m)
                     Then MAX (ppidx m) (ppidx n) = ppidx n    by MAX_DEF
                     Therefore x IN v                          by IN_IMAGE

       (b) x IN u ==> x IN s
           Note x IN u
            ==> ?p. p IN prime_divisors m DIFF park_on m n /\
                    (x = p ** ppidx m)                        by IN_IMAGE
           Thus p IN prime_divisors m /\ p NOTIN park_on m n  by IN_DIFF
           Note p IN total_prime_divisors m n                 by total_prime_divisors_element
           By park_on_element, either [1] or [2]:
           [1] p NOTIN prime_divisors n
               Then ppidx n = 0  by prime_divisors_element, prime_power_index_eq_0, 0 < n
                ==> MAX (ppidx m) (ppidx n) = ppidx m         by MAX_DEF
               Therefore x IN u                               by IN_IMAGE
           [2] ~(ppidx m <= ppidx n)
               Then MAX (ppidx m) (ppidx n) = ppidx m         by MAX_DEF
               Therefore x IN u                               by IN_IMAGE

       (c) x IN v ==> x IN s
           Note x IN v
            ==> ?p. p IN prime_divisors n DIFF park_off m n /\
                    (x = p ** ppidx n)                        by IN_IMAGE
           Thus p IN prime_divisors n /\ p NOTIN park_off m n by IN_DIFF
           Note p IN total_prime_divisors m n                 by total_prime_divisors_element
           By park_off_element, either [1] or [2]:
           [1] p NOTIN prime_divisors m
               Then ppidx m = 0  by prime_divisors_element, prime_power_index_eq_0, 0 < m
                ==> MAX (ppidx m) (ppidx n) = ppidx n         by MAX_DEF
               Therefore x IN v                               by IN_IMAGE
           [2] ~(ppidx n < ppidx m)
               Then MAX (ppidx m) (ppidx n) = ppidx n         by MAX_DEF
               Therefore x IN v                               by IN_IMAGE

   (2) DISJOINT u v
       This is to show: u INTER v = {}          by DISJOINT_DEF
       By contradiction, suppse u INTER v <> {}.
       Then ?x. x IN u /\ x IN v                by MEMBER_NOT_EMPTY, IN_INTER
       Note x IN u
        ==> ?p. p IN prime_divisors m DIFF park_on m n /\
                (x = p ** ppidx m)              by IN_IMAGE
        and x IN v
        ==> ?q. q IN prime_divisors n DIFF park_off m n /\
               (x = q ** prime_power_index q n)   by IN_IMAGE
       Thus p IN prime_divisors m /\ p NOTIN park_on m n   by IN_DIFF
        and q IN prime_divisors n /\ q NOTIN park_off m n  by IN_DIFF [1]
        Now prime p /\ prime q /\ p divides m     by prime_divisors_element
        and 0 < ppidx m                           by prime_power_index_pos, p divides m, 0 < m
        ==> p = q                                 by prime_powers_eq
       Thus p IN common_prime_divisors m n        by common_prime_divisors_element, [1]
        ==> p IN park_on m n \/ p IN park_off m n by park_on_off_partition, IN_UNION
       This is a contradiction with [1].
*)
val park_on_off_total_image_partition = store_thm(
  "park_on_off_total_image_partition",
  ``!m n. let s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n) in
         let u = IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n)) in
         let v = IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n)) in
         0 < m /\ 0 < n ==> s =|= u # v``,
  rpt strip_tac >>
  qabbrev_tac `f = \p:num. p ** MAX (ppidx m) (ppidx n)` >>
  qabbrev_tac `f1 = \p:num. p ** ppidx m` >>
  qabbrev_tac `f2 = \p:num. p ** ppidx n` >>
  rw_tac std_ss[] >| [
    rw[EXTENSION, EQ_IMP_THM] >| [
      `?p. p IN total_prime_divisors m n /\ (x = p ** MAX (ppidx m) (ppidx n))` by metis_tac[IN_IMAGE] >>
      `p IN prime_divisors m \/ p IN prime_divisors n` by rw[GSYM total_prime_divisors_element] >| [
        `prime p /\ p divides m` by metis_tac[prime_divisors_element] >>
        Cases_on `p IN park_on m n` >| [
          `p IN prime_divisors n /\ ppidx m <= ppidx n` by metis_tac[park_on_element] >>
          `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
          `p NOTIN park_off m n` by metis_tac[park_on_off_partition, IN_DISJOINT] >>
          `p IN prime_divisors n DIFF park_off m n` by rw[] >>
          metis_tac[IN_IMAGE],
          `p IN prime_divisors m DIFF park_on m n` by rw[] >>
          `p NOTIN prime_divisors n \/ ~(ppidx m <= ppidx n)` by metis_tac[park_on_element] >| [
            `ppidx n = 0` by metis_tac[prime_divisors_element, prime_power_index_eq_0] >>
            `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
            metis_tac[IN_IMAGE],
            `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
            metis_tac[IN_IMAGE]
          ]
        ],
        `prime p /\ p divides n` by metis_tac[prime_divisors_element] >>
        Cases_on `p IN park_off m n` >| [
          `p IN prime_divisors m /\ ppidx n < ppidx m` by metis_tac[park_off_element] >>
          `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
          `p NOTIN park_on m n` by metis_tac[park_on_off_partition, IN_DISJOINT] >>
          `p IN prime_divisors m DIFF park_on m n` by rw[] >>
          metis_tac[IN_IMAGE],
          `p IN prime_divisors n DIFF park_off m n` by rw[] >>
          `p NOTIN prime_divisors m \/ ~(ppidx n < ppidx m)` by metis_tac[park_off_element] >| [
            `ppidx m = 0` by metis_tac[prime_divisors_element, prime_power_index_eq_0] >>
            `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
            metis_tac[IN_IMAGE],
            `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
            metis_tac[IN_IMAGE]
          ]
        ]
      ],
      `?p. p IN prime_divisors m DIFF park_on m n /\ (x = p ** ppidx m)` by prove_tac[IN_IMAGE] >>
      `p IN prime_divisors m /\ p NOTIN park_on m n` by metis_tac[IN_DIFF] >>
      `p IN total_prime_divisors m n` by rw[total_prime_divisors_element] >>
      `p NOTIN prime_divisors n \/ ~(ppidx m <= ppidx n)` by metis_tac[park_on_element] >| [
        `ppidx n = 0` by metis_tac[prime_divisors_element, prime_power_index_eq_0] >>
        `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
        metis_tac[IN_IMAGE],
        `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
        metis_tac[IN_IMAGE]
      ],
      `?p. p IN prime_divisors n DIFF park_off m n /\ (x = p ** ppidx n)` by prove_tac[IN_IMAGE] >>
      `p IN prime_divisors n /\ p NOTIN park_off m n` by metis_tac[IN_DIFF] >>
      `p IN total_prime_divisors m n` by rw[total_prime_divisors_element] >>
      `p NOTIN prime_divisors m \/ ~(ppidx n < ppidx m)` by metis_tac[park_off_element] >| [
        `ppidx m = 0` by metis_tac[prime_divisors_element, prime_power_index_eq_0] >>
        `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
        metis_tac[IN_IMAGE],
        `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
        metis_tac[IN_IMAGE]
      ]
    ],
    rw[DISJOINT_DEF] >>
    spose_not_then strip_assume_tac >>
    `?x. x IN u /\ x IN v` by metis_tac[MEMBER_NOT_EMPTY, IN_INTER] >>
    `?p. p IN prime_divisors m DIFF park_on m n /\ (x = p ** ppidx m)` by prove_tac[IN_IMAGE] >>
    `?q. q IN prime_divisors n DIFF park_off m n /\ (x = q ** prime_power_index q n)` by prove_tac[IN_IMAGE] >>
    `p IN prime_divisors m /\ p NOTIN park_on m n` by metis_tac[IN_DIFF] >>
    `q IN prime_divisors n /\ q NOTIN park_off m n` by metis_tac[IN_DIFF] >>
    `prime p /\ prime q /\ p divides m` by metis_tac[prime_divisors_element] >>
    `0 < ppidx m` by rw[prime_power_index_pos] >>
    `p = q` by metis_tac[prime_powers_eq] >>
    `p IN common_prime_divisors m n` by rw[common_prime_divisors_element] >>
    metis_tac[park_on_off_partition, IN_UNION]
  ]);

(* Theorem: 0 < m /\ 0 < n ==>
           let a = park m n in let b = gcd m n DIV a in
           let p = m DIV a in let q = (a * n) DIV (gcd m n) in
           (b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n))) /\
           (p = PROD_SET (IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n)))) /\
           (q = PROD_SET (IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n)))) /\
           (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q) *)
(* Proof:
   Let s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n),
       u = IMAGE (\p. p ** ppidx m) (park_on m n),
       v = IMAGE (\p. p ** ppidx n) (park_off m n),
       h = IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n)),
       k = IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n)),
       a = PROD_SET u, b = PROD_SET v, c = PROD_SET s, p = PROD_SET h, q = PROD_SET k
       x = IMAGE (\p. p ** ppidx m) (prime_divisors m),
       y = IMAGE (\p. p ** ppidx n) (prime_divisors n),
   Let g = gcd m n.

   Step 1: GCD
   Note a = park m n                       by notation
    and g = a * b                          by gcd_park_decomposition

   Step 2: LCM
   Note c = lcm m n                        by lcm_prime_factorisation
   Note s =|= h # k                        by park_on_off_total_image_partition
    and FINITE (total_prime_divisors m n)  by total_prime_divisors_finite, 0 < m, 0 < n
    ==> FINITE s                           by IMAGE_FINITE
   also PAIRWISE_COPRIME s                 by total_prime_divisors_max_image_pairwise_coprime
   Thus (c = p * q) /\ coprime p q         by pairwise_coprime_prod_set_partition

   Step 3: Identities
   Note m = PROD_SET x                     by basic_prime_factorisation
        n = PROD_SET y                     by basic_prime_factorisation

   For the identity:  m = a * p
   We need:  PROD_SET x = PROD_SET u * PROD_SET h
   This requires:     x = u UNION h /\ DISJOINT u h, i.e. x =|= u # h
   or partition: (prime_divisors m) --> (park_on m n) and (prime_divisors m) DIFF (park_on m n)

   Claim: m = a * p
   Proof: Claim: h = x DIFF u
          Proof: Let pk = park_on m n, pm = prime_divisors m, f = \p. p ** ppidx m.
                 Note pk SUBSET pm                by park_on_element, prime_divisors_element, SUBSET_DEF
                  ==> INJ f pm UNIV               by INJ_DEF, prime_divisors_element,
                                                     prime_power_index_pos, prime_powers_eq
                   x DIFF u
                 = (IMAGE f pm) DIFF (IMAGE f pk) by notation
                 = IMAGE f (pm DIFF pk)           by IMAGE_INJ_SUBSET_DIFF
                 = h                              by notation
          Note FINITE x                           by prime_divisors_finite, IMAGE_FINITE
           and u SUBSET x                         by SUBSET_DEF, IMAGE_SUBSET
          Thus x =|= u # h                        by partition_by_subset
           ==> m = a * p                          by PROD_SET_PRODUCT_BY_PARTITION

   For the identity:  n = b * q
   We need:  PROD_SET y = PROD_SET v * PROD_SET k
   This requires:     y = v UNION k /\ DISJOINT v k, i.e y =|= v # k
   or partition: (prime_divisors n) --> (park_off m n) and (prime_divisors n) DIFF (park_off m n)

   Claim: n = b * q
   Proof: Claim: k = y DIFF v
          Proof: Let pk = park_off m n, pn = prime_divisors n, f = \p. p ** ppidx n.
                 Note pk SUBSET pn                by park_off_element, prime_divisors_element, SUBSET_DEF
                  ==> INJ f pn UNIV               by INJ_DEF, prime_divisors_element,
                                                     prime_power_index_pos, prime_powers_eq
                   y DIFF v
                 = (IMAGE f pn) DIFF (IMAGE f pk) by notation
                 = IMAGE f (pn DIFF pk)           by IMAGE_INJ_SUBSET_DIFF
                 = k                              by notation
          Note FINITE y                           by prime_divisors_finite, IMAGE_FINITE
           and v SUBSET y                         by SUBSET_DEF, IMAGE_SUBSET
          Thus y =|= v # k                        by partition_by_subset
           ==> n = b * q                          by PROD_SET_PRODUCT_BY_PARTITION

   Proof better:
         Note m * n = g * c                       by GCD_LCM
                    = (a * b) * (p * q)           by above
                    = (a * p) * (b * q)           by MULT_COMM, MULT_ASSOC
                    = m * (b * q)                 by m = a * p
         Thus     n = b * q                       by MULT_LEFT_CANCEL, 0 < m

   Thus g <> 0 /\ c <> 0     by GCD_EQ_0, LCM_EQ_0, m <> 0, n <> 0
    ==> p <> 0 /\ a <> 0     by MULT_EQ_0
    ==> b = g DIV a          by DIV_SOLVE_COMM, 0 < a
    ==> p = m DIV a          by DIV_SOLVE_COMM, 0 < a
    and q = c DIV p          by DIV_SOLVE_COMM, 0 < p
   Note g divides n          by GCD_IS_GREATEST_COMMON_DIVISOR
     so g divides a * n      by DIVIDES_MULTIPLE
     or a * n = a * (b * q)  by n = b * q from Claim 2
              = (a * b) * q  by MULT_ASSOC
              = g * q        by g = a * b
              = q * g        by MULT_COMM
     so g divides a * n      by divides_def
   Thus q = c DIV p                      by above
          = ((m * n) DIV g) DIV p        by lcm_def, m <> 0, n <> 0
          = (m * n) DIV (g * p)          by DIV_DIV_DIV_MULT, 0 < g, 0 < p
          = ((a * p) * n) DIV (g * p)    by m = a * p, Claim 1
          = (p * (a * n)) DIV (p * g)    by MULT_COMM, MULT_ASSOC
          = (a * n) DIV g                by DIV_COMMON_FACTOR, 0 < p, g divides a * n

   This gives all the assertions:
        (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\
        (m = a * p) /\ (n = b * q)       by MULT_COMM
*)

Theorem lcm_park_decomposition:
  !m n.
    0 < m /\ 0 < n ==>
    let a = park m n ; b = gcd m n DIV a ;
        p = m DIV a  ; q = (a * n) DIV (gcd m n)
    in
        b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n)) /\
        p = PROD_SET (IMAGE (\p. p ** ppidx m)
                      ((prime_divisors m) DIFF (park_on m n))) /\
        q = PROD_SET (IMAGE (\p. p ** ppidx n)
                      ((prime_divisors n) DIFF (park_off m n))) /\
        lcm m n = p * q /\ coprime p q /\ gcd m n = a * b /\ m = a * p /\
        n = b * q
Proof
  rpt strip_tac >>
  qabbrev_tac ‘s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n)’ >>
  qabbrev_tac ‘u = IMAGE (\p. p ** ppidx m) (park_on m n)’ >>
  qabbrev_tac ‘v = IMAGE (\p. p ** ppidx n) (park_off m n)’ >>
  qabbrev_tac ‘h = IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n))’ >>
  qabbrev_tac ‘k = IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n))’ >>
  qabbrev_tac ‘a = PROD_SET u’ >>
  qabbrev_tac ‘b = PROD_SET v’ >>
  qabbrev_tac ‘c = PROD_SET s’ >>
  qabbrev_tac ‘p = PROD_SET h’ >>
  qabbrev_tac ‘q = PROD_SET k’ >>
  qabbrev_tac ‘x = IMAGE (\p. p ** ppidx m) (prime_divisors m)’ >>
  qabbrev_tac ‘y = IMAGE (\p. p ** ppidx n) (prime_divisors n)’ >>
  qabbrev_tac ‘g = gcd m n’ >>
  ‘a = park m n’ by rw[Abbr‘a’] >>
  ‘g = a * b’ by metis_tac[gcd_park_decomposition] >>
  ‘c = lcm m n’ by rw[lcm_prime_factorisation, Abbr‘c’, Abbr‘s’] >>
  ‘s =|= h # k’ by metis_tac[park_on_off_total_image_partition] >>
  ‘FINITE s’ by rw[total_prime_divisors_finite, Abbr‘s’] >>
  ‘PAIRWISE_COPRIME s’
    by metis_tac[total_prime_divisors_max_image_pairwise_coprime] >>
  ‘(c = p * q) /\ coprime p q’
    by (simp[Abbr‘p’, Abbr‘q’, Abbr‘c’] >>
        metis_tac[pairwise_coprime_prod_set_partition]) >>
  ‘m = PROD_SET x’ by rw[basic_prime_factorisation, Abbr‘x’] >>
  ‘n = PROD_SET y’ by rw[basic_prime_factorisation, Abbr‘y’] >>
  ‘m = a * p’
    by (‘h = x DIFF u’
         by (‘park_on m n SUBSET prime_divisors m’
              by metis_tac[park_on_element,prime_divisors_element,SUBSET_DEF] >>
             ‘INJ (\p. p ** ppidx m) (prime_divisors m) UNIV’
               by (rw[INJ_DEF] >>
                   metis_tac[prime_divisors_element, prime_power_index_pos,
                             prime_powers_eq]) >>
             metis_tac[IMAGE_INJ_SUBSET_DIFF]) >>
        ‘FINITE x’ by rw[prime_divisors_finite, Abbr‘x’] >>
        ‘u SUBSET x’ by rw[SUBSET_DEF, Abbr‘u’, Abbr‘x’] >>
        ‘x =|= u # h’ by metis_tac[partition_by_subset] >>
        metis_tac[PROD_SET_PRODUCT_BY_PARTITION]) >>
  ‘n = b * q’
    by (‘m * n = g * c’ by metis_tac[GCD_LCM] >>
        ‘_ = (a * p) * (b * q)’ by rw[] >>
        ‘_ = m * (b * q)’ by rw[] >>
        metis_tac[MULT_LEFT_CANCEL, NOT_ZERO_LT_ZERO]) >>
  ‘m <> 0 /\ n <> 0’ by decide_tac >>
  ‘g <> 0 /\ c <> 0’ by metis_tac[GCD_EQ_0, LCM_EQ_0] >>
  ‘p <> 0 /\ a <> 0’ by metis_tac[MULT_EQ_0] >>
  ‘b = g DIV a’ by metis_tac[DIV_SOLVE_COMM, NOT_ZERO_LT_ZERO] >>
  ‘p = m DIV a’ by metis_tac[DIV_SOLVE_COMM, NOT_ZERO_LT_ZERO] >>
  ‘q = c DIV p’ by metis_tac[DIV_SOLVE_COMM, NOT_ZERO_LT_ZERO] >>
  ‘g divides a * n’ by metis_tac[divides_def, MULT_ASSOC, MULT_COMM] >>
  ‘c = (m * n) DIV g’ by metis_tac[lcm_def] >>
  ‘q = (m * n) DIV (g * p)’ by metis_tac[DIV_DIV_DIV_MULT, NOT_ZERO_LT_ZERO] >>
  ‘_ = (p * (a * n)) DIV (p * g)’ by metis_tac[MULT_COMM, MULT_ASSOC] >>
  ‘_ = (a * n) DIV g’ by metis_tac[DIV_COMMON_FACTOR, NOT_ZERO_LT_ZERO] >>
  metis_tac[]
QED

(* Theorem: 0 < m /\ 0 < n ==> let a = park m n in let p = m DIV a in let q = (a * n) DIV (gcd m n) in
            (lcm m n = p * q) /\ coprime p q *)
(* Proof: by lcm_park_decomposition *)
val lcm_park_decompose = store_thm(
  "lcm_park_decompose",
  ``!m n. 0 < m /\ 0 < n ==> let a = park m n in let p = m DIV a in let q = (a * n) DIV (gcd m n) in
         (lcm m n = p * q) /\ coprime p q``,
  metis_tac[lcm_park_decomposition]);

(* Theorem: 0 < m /\ 0 < n ==>
            let a = park m n in let b = gcd m n DIV a in
            let p = m DIV a in let q = (a * n) DIV (gcd m n) in
            (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q) *)
(* Proof: by lcm_park_decomposition *)
val lcm_gcd_park_decompose = store_thm(
  "lcm_gcd_park_decompose",
  ``!m n. 0 < m /\ 0 < n ==>
        let a = park m n in let b = gcd m n DIV a in
        let p = m DIV a in let q = (a * n) DIV (gcd m n) in
         (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q)``,
  metis_tac[lcm_park_decomposition]);

(* ------------------------------------------------------------------------- *)
(* Consecutive LCM Recurrence                                                *)
(* ------------------------------------------------------------------------- *)

(*
> optionTheory.some_def;
val it = |- !P. $some P = if ?x. P x then SOME (@x. P x) else NONE: thm
*)

(*
Cannot do this: Definition is schematic in the following variables: p

val lcm_fun_def = Define`
  lcm_fun n = if n = 0 then 1
      else if n = 1 then 1
    else if ?p k. 0 < k /\ prime p /\ (n = p ** k) then p * lcm_fun (n - 1)
  else lcm_fun (n - 1)
`;
*)

(* NOT this:
val lcm_fun_def = Define`
  (lcm_fun 1 = 1) /\
  (lcm_fun (SUC n) = case some p. ?k. (SUC n = p ** k) of
                    SOME p => p * (lcm_fun n)
                  | NONE   => lcm_fun n)
`;
*)

(*
Question: don't know how to prove termination
(* Define the B(n) function *)
val lcm_fun_def = Define`
  (lcm_fun 1 = 1) /\
  (lcm_fun n = case some p. ?k. 0 < k /\ prime p /\ (n = p ** k) of
                    SOME p => p * (lcm_fun (n - 1))
                  | NONE   => lcm_fun (n - 1))
`;

` (* use a measure that is decreasing *)
e (WF_REL_TAC `measure (\n k. k * n)`);
e (rpt strip_tac);
*)

(* Define the Consecutive LCM Function *)
val lcm_fun_def = Define`
  (lcm_fun 0 = 1) /\
  (lcm_fun (SUC n) = if n = 0 then 1 else
      case some p. ?k. 0 < k /\ prime p /\ (SUC n = p ** k) of
        SOME p => p * (lcm_fun n)
      | NONE   => lcm_fun n)
`;

(* Another possible definition -- but need to work with pairs:

val lcm_fun_def = Define`
  (lcm_fun 0 = 1) /\
  (lcm_fun (SUC n) = if n = 0 then 1 else
      case some (p, k). 0 < k /\ prime p /\ (SUC n = p ** k) of
        SOME (p, k) => p * (lcm_fun n)
      | NONE        => lcm_fun n)
`;

By prime_powers_eq, when SOME, such (p, k) exists uniquely, or NONE.
*)

(* Get components of definition *)
val lcm_fun_0 = save_thm("lcm_fun_0", lcm_fun_def |> CONJUNCT1);
(* val lcm_fun_0 = |- lcm_fun 0 = 1: thm *)
val lcm_fun_SUC = save_thm("lcm_fun_SUC", lcm_fun_def |> CONJUNCT2);
(* val lcm_fun_SUC = |- !n. lcm_fun (SUC n) = if n = 0 then 1 else
                            case some p. ?k. SUC n = p ** k of
                            NONE => lcm_fun n | SOME p => p * lcm_fun n: thm *)

(* Theorem: lcm_fun 1 = 1 *)
(* Proof:
     lcm_fun 1
   = lcm_fun (SUC 0)   by ONE
   = 1                 by lcm_fun_def
*)
val lcm_fun_1 = store_thm(
  "lcm_fun_1",
  ``lcm_fun 1 = 1``,
  rw_tac bool_ss[lcm_fun_def, ONE]);

(* Theorem: lcm_fun 2 = 2 *)
(* Proof:
   Note 2 = 2 ** 1                by EXP_1
    and prime 2                   by PRIME_2
    and 0 < k /\ prime p /\ (2 ** 1 = p ** k)
    ==> (p = 2) /\ (k = 1)        by prime_powers_eq

     lcm_fun 2
   = lcm_fun (SUC 1)              by TWO
   = case some p. ?k. 0 < k /\ prime p /\ (SUC 1 = p ** k) of
       SOME p => p * (lcm_fun 1)
     | NONE   => lcm_fun 1)       by lcm_fun_def
   = SOME 2                       by some_intro, above
   = 2 * (lcm_fun 1)              by definition
   = 2 * 1                        by lcm_fun_1
   = 2                            by arithmetic
*)
val lcm_fun_2 = store_thm(
  "lcm_fun_2",
  ``lcm_fun 2 = 2``,
  simp_tac bool_ss[lcm_fun_def, lcm_fun_1, TWO] >>
  `prime 2 /\ (2 = 2 ** 1)` by rw[PRIME_2] >>
  DEEP_INTRO_TAC some_intro >>
  rw_tac std_ss[] >-
  metis_tac[prime_powers_eq] >>
  metis_tac[DECIDE``0 < 1``]);

(* Theorem: prime p /\ (?k. 0 < k /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = p * lcm_fun n) *)
(* Proof: by lcm_fun_def, prime_powers_eq *)
val lcm_fun_suc_some = store_thm(
  "lcm_fun_suc_some",
  ``!n p. prime p /\ (?k. 0 < k /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = p * lcm_fun n)``,
  rw[lcm_fun_def] >>
  DEEP_INTRO_TAC some_intro >>
  (rw_tac std_ss[] >> metis_tac[prime_powers_eq]));

(* Theorem: ~(?p k. 0 < k /\ prime p /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = lcm_fun n) *)
(* Proof: by lcm_fun_def *)
val lcm_fun_suc_none = store_thm(
  "lcm_fun_suc_none",
  ``!n. ~(?p k. 0 < k /\ prime p /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = lcm_fun n)``,
  rw[lcm_fun_def] >>
  DEEP_INTRO_TAC some_intro >>
  rw_tac std_ss[] >>
  `k <> 0` by decide_tac >>
  metis_tac[]);

(* Theorem: prime p /\ l <> [] /\ POSITIVE l ==> !x. MEM x l ==> ppidx x <= ppidx (list_lcm l) *)
(* Proof:
   Note ppidx (list_lcm l) = MAX_LIST (MAP ppidx l)   by list_lcm_prime_power_index
    and MEM (ppidx x) (MAP ppidx l)                   by MEM_MAP, MEM x l
   Thus ppidx x <= ppidx (list_lcm l)                 by MAX_LIST_PROPERTY
*)
val list_lcm_prime_power_index_lower = store_thm(
  "list_lcm_prime_power_index_lower",
  ``!l p. prime p /\ l <> [] /\ POSITIVE l ==> !x. MEM x l ==> ppidx x <= ppidx (list_lcm l)``,
  rpt strip_tac >>
  `ppidx (list_lcm l) = MAX_LIST (MAP ppidx l)` by rw[list_lcm_prime_power_index] >>
  `MEM (ppidx x) (MAP ppidx l)` by metis_tac[MEM_MAP] >>
  rw[MAX_LIST_PROPERTY]);

(*
The keys to show list_lcm_eq_lcm_fun are:
(1) Given a number n and a prime p that divides n, you can extract all the p's in n,
    giving n = (p ** k) * q for some k, and coprime p q. This is FACTOR_OUT_PRIME, or FACTOR_OUT_POWER.
(2) To figure out the LCM, use the GCD_LCM identity, i.e. figure out first the GCD.

Therefore, let m = consecutive LCM.
Consider given two number m, n; and a prime p with p divides n.
By (1), n = (p ** k) * q, with coprime p q.
If q > 1, then n = a * b where a, b are both less than n, and coprime a b: take a = p ** k, b = q.
          Now, if a divides m, and b divides m --- which is the case when m = consecutive LCM,
          By coprime a b, (a * b) divides m, or n divides m,
          or gcd m n = n       by divides_iff_gcd_fix
          or lcm m n = (m * n) DIV (gcd m n) = (m * n) DIV n = m (or directly by divides_iff_lcm_fix)
If q = 1, then n is a pure prime p power: n = p ** k, with k > 0.
          Now, m = (p ** j) * t  with coprime p t, although it may be that j = 0.
          For list LCM, j <= k, since the numbers are consecutive. In fact, j = k - 1
          Thus n = (p ** j) * p, and gcd m n = (p ** j) gcd p t = (p ** j)  by GCD_COMMON_FACTOR
          or lcm m n = (m * n) DIV (gcd m n)
                     = m * (n DIV (p ** j))
                     = m * ((p ** j) * p) DIV (p ** j)
                     = m * p = p * m
*)

(* Theorem: prime p /\ (n + 2 = p ** k) ==> (list_lcm [1 .. (n + 2)] = p * list_lcm [1 .. (n + 1)]) *)
(* Proof:
   Note n + 2 = SUC (SUC n) <> 1         by ADD1, TWO
   Thus p ** k <> 1, or k <> 0           by EXP_EQ_1
    ==> ?h. k = SUC h                    by num_CASES
    and n + 2 = x ** SUC h               by above

    Let l = [1 .. (n + 1)], m = list_lcm l.
    Note POSITIVE l                      by leibniz_vertical_pos, EVERY_MEM
     Now h < SUC h = k                   by LESS_SUC
      so p ** h < p ** k = n + 2         by EXP_BASE_LT_MONO, 1 < p
     ==> MEM (p ** h) l                  by leibniz_vertical_mem
    Note l <> []                         by leibniz_vertical_not_nil
      so ppidx (p ** h) <= ppidx m       by list_lcm_prime_power_index_lower
      or              h <= ppidx m       by prime_power_index_prime_power

    Claim: ppidx m <= h
    Proof: By contradiction, suppose h < ppidx m.
           Then k <= ppidx m                       by k = SUC h
            and p ** k divides p ** (ppidx m)      by power_divides_iff
            But p ** (ppidx m) divides m           by prime_power_factor_divides
             so p ** k divides m                   by DIVIDES_TRANS
            ==> ?z. MEM z l /\ (n + 2) divides z   by list_lcm_prime_power_factor_member
             or (n + 2) <= z                       by DIVIDES_LE, 0 < z, all members are positive
            Now z <= n + 1                         by leibniz_vertical_mem
           This leads to a contradiction: n + 2 <= n + 1.

    Therefore ppidx m = h                          by h <= ppidx m /\ ppidx m <= h, by Claim.

       list_lcm [1 .. (n + 2)]
     = list_lcm (SNOC (n + 2) l)                   by leibniz_vertical_snoc, n + 2 = SUC (n + 1)
     = lcm (n + 2) m                               by list_lcm_snoc
     = p * m                                       by lcm_special_for_prime_power
*)
val list_lcm_with_last_prime_power = store_thm(
  "list_lcm_with_last_prime_power",
  ``!n p k. prime p /\ (n + 2 = p ** k) ==> (list_lcm [1 .. (n + 2)] = p * list_lcm [1 .. (n + 1)])``,
  rpt strip_tac >>
  `n + 2 <> 1` by decide_tac >>
  `0 <> k` by metis_tac[EXP_EQ_1] >>
  `?h. k = SUC h` by metis_tac[num_CASES] >>
  qabbrev_tac `l = leibniz_vertical n` >>
  qabbrev_tac `m = list_lcm l` >>
  `POSITIVE l` by rw[leibniz_vertical_pos, EVERY_MEM, Abbr`l`] >>
  `h < k` by rw[] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `p ** h < p ** k` by rw[EXP_BASE_LT_MONO] >>
  `0 < p ** h` by rw[PRIME_POS, EXP_POS] >>
  `p ** h <= n + 1` by decide_tac >>
  `MEM (p ** h) l` by rw[leibniz_vertical_mem, Abbr`l`] >>
  `ppidx (p ** h) = h` by rw[prime_power_index_prime_power] >>
  `l <> []` by rw[leibniz_vertical_not_nil, Abbr`l`] >>
  `h <= ppidx m` by metis_tac[list_lcm_prime_power_index_lower] >>
  `ppidx m <= h` by
  (spose_not_then strip_assume_tac >>
  `k <= ppidx m` by decide_tac >>
  `p ** k divides p ** (ppidx m)` by rw[power_divides_iff] >>
  `p ** (ppidx m) divides m` by rw[prime_power_factor_divides] >>
  `p ** k divides m` by metis_tac[DIVIDES_TRANS] >>
  `?z. MEM z l /\ (n + 2) divides z` by metis_tac[list_lcm_prime_power_factor_member] >>
  `(n + 2) <= z` by rw[DIVIDES_LE] >>
  `z <= n + 1` by metis_tac[leibniz_vertical_mem, Abbr`l`] >>
  decide_tac) >>
  `h = ppidx m` by decide_tac >>
  `list_lcm [1 .. (n + 2)] = list_lcm (SNOC (n + 2) l)` by rw[GSYM leibniz_vertical_snoc, Abbr`l`] >>
  `_ = lcm (n + 2) m` by rw[list_lcm_snoc, Abbr`m`] >>
  `_ = p * m` by rw[lcm_special_for_prime_power] >>
  rw[]);

(* Theorem: (!p k. (k = 0) \/ ~prime p \/ n + 2 <> p ** k) ==>
            (list_lcm [1 .. (n + 2)] = list_lcm [1 .. (n + 1)]) *)
(* Proof:
   Note 1 < n + 2,
    ==> ?a b. (n + 2 = a * b) /\ coprime a b /\
              1 < a /\ 1 < b /\ a < n + 2 /\ b < n + 2    by prime_power_or_coprime_factors
     or 0 < a /\ 0 < b /\ a <= n + 1 /\ b <= n + 1        by arithmetic
    Let l = leibniz_vertical n, m = list_lcm l.
    Then MEM a l and MEM b l                              by leibniz_vertical_mem
     and a divides m /\ b divides m                       by list_lcm_is_common_multiple
     ==> (n + 2) divides m                                by coprime_product_divides, coprime a b

      list_lcm (leibniz_vertical (n + 1))
    = list_lcm (SNOC (n + 2) l)                           by leibniz_vertical_snoc
    = lcm (n + 2) m                                       by list_lcm_snoc
    = m                                                   by divides_iff_lcm_fix
*)
val list_lcm_with_last_non_prime_power = store_thm(
  "list_lcm_with_last_non_prime_power",
  ``!n. (!p k. (k = 0) \/ ~prime p \/ n + 2 <> p ** k) ==>
       (list_lcm [1 .. (n + 2)] = list_lcm [1 .. (n + 1)])``,
  rpt strip_tac >>
  `1 < n + 2` by decide_tac >>
  `!k. ~(0 < k) = (k = 0)` by decide_tac >>
  `?a b. (n + 2 = a * b) /\ coprime a b /\ 1 < a /\ 1 < b /\ a < n + 2 /\ b < n + 2` by metis_tac[prime_power_or_coprime_factors] >>
  `0 < a /\ 0 < b /\ a <= n + 1 /\ b <= n + 1` by decide_tac >>
  qabbrev_tac `l = leibniz_vertical n` >>
  qabbrev_tac `m = list_lcm l` >>
  `MEM a l /\ MEM b l` by rw[leibniz_vertical_mem, Abbr`l`] >>
  `a divides m /\ b divides m` by rw[list_lcm_is_common_multiple, Abbr`m`] >>
  `(n + 2) divides m` by rw[coprime_product_divides] >>
  `list_lcm [1 .. (n + 2)] = list_lcm (SNOC (n + 2) l)` by rw[GSYM leibniz_vertical_snoc, Abbr`l`] >>
  `_ = lcm (n + 2) m` by rw[list_lcm_snoc, Abbr`m`] >>
  `_ = m` by rw[GSYM divides_iff_lcm_fix] >>
  rw[]);

(* Theorem: list_lcm [1 .. (n + 1)] = lcm_fun (n + 1) *)
(* Proof:
   By induction on n.
   Base: list_lcm [1 .. 0 + 1] = lcm_fun (0 + 1)
      LHS = list_lcm [1 .. 0 + 1]
          = list_lcm [1]                by leibniz_vertical_0
          = 1                           by list_lcm_sing
      RHS = lcm_fun (0 + 1)
          = lcm_fun 1                   by ADD
          = 1 = LHS                     by lcm_fun_1
   Step: list_lcm [1 .. n + 1] = lcm_fun (n + 1) ==>
         list_lcm [1 .. SUC n + 1] = lcm_fun (SUC n + 1)
      Note (SUC n) <> 0                 by SUC_NOT_ZERO
       and n + 2 = SUC (SUC n)          by ADD1, TWO
      By lcm_fun_def, this is to show:
         list_lcm [1 .. SUC n + 1] = case some p. ?k. 0 < k /\ prime p /\ (SUC (SUC n) = p ** k) of
                                       NONE => lcm_fun (SUC n)
                                     | SOME p => p * lcm_fun (SUC n)

      If SOME,
         Then 0 < k /\ prime p /\ SUC (SUC n) = p ** k
         This is the case of perfect prime power.
            list_lcm (leibniz_vertical (SUC n))
          = list_lcm (leibniz_vertical (n + 1))    by ADD1
          = p * list_lcm (leibniz_vertical n)      by list_lcm_with_last_prime_power
          = p * lcm_fun (SUC n)                    by induction hypothesis
      If NONE,
         Then !x k. ~(0 < k) \/ ~prime x \/ SUC (SUC n) <> x ** k
         This is the case of non-perfect prime power.
             list_lcm (leibniz_vertical (SUC n))
           = list_lcm (leibniz_vertical (n + 1))   by ADD1
           = list_lcm (leibniz_vertical n)         by list_lcm_with_last_non_prime_power
           = lcm_fun (SUC n)                       by induction hypothesis
*)
val list_lcm_eq_lcm_fun = store_thm(
  "list_lcm_eq_lcm_fun",
  ``!n. list_lcm [1 .. (n + 1)] = lcm_fun (n + 1)``,
  Induct >-
  rw[leibniz_vertical_0, list_lcm_sing, lcm_fun_1] >>
  `(SUC n) + 1 = SUC (SUC n)` by rw[] >>
  `list_lcm [1 .. SUC n + 1] = case some p. ?k. 0 < k /\ prime p /\ ((SUC n) + 1 = p ** k) of
                                       NONE => lcm_fun (SUC n)
                                     | SOME p => p * lcm_fun (SUC n)` suffices_by rw[lcm_fun_def] >>
  `n + 2 = (SUC n) + 1` by rw[] >>
  DEEP_INTRO_TAC some_intro >>
  rw[] >-
  metis_tac[list_lcm_with_last_prime_power, ADD1] >>
  metis_tac[list_lcm_with_last_non_prime_power, ADD1]);

(* This is a major milestone theorem! *)

(* Theorem: 2 ** n <= lcm_fun (SUC n) *)
(* Proof:
   Note 2 ** n <= list_lcm (leibniz_vertical n)          by lcm_lower_bound
    and list_lcm (leibniz_vertical n) = lcm_fun (SUC n)  by list_lcm_eq_lcm_fun\
     so 2 ** n <= lcm_fun (SUC n)
*)
val lcm_fun_lower_bound = store_thm(
  "lcm_fun_lower_bound",
  ``!n. 2 ** n <= lcm_fun (n + 1)``,
  rw[GSYM list_lcm_eq_lcm_fun, lcm_lower_bound]);

(* Theorem: 0 < n ==> 2 ** (n - 1) <= lcm_fun n *)
(* Proof:
   Note 0 < n ==> ?m. n = SUC m      by num_CASES
     or m = n - 1                    by SUC_SUB1
   Apply lcm_fun_lower_bound,
     put n = SUC m, and the result follows.
*)
val lcm_fun_lower_bound_alt = store_thm(
  "lcm_fun_lower_bound_alt",
  ``!n. 0 < n ==> 2 ** (n - 1) <= lcm_fun n``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `(n - 1 = m) /\ (n = m + 1)` by decide_tac >>
  metis_tac[lcm_fun_lower_bound]);

(* Theorem: 0 < n /\ prime p /\ (SUC n = p ** ppidx (SUC n)) ==>
            (ppidx (SUC n) = SUC (ppidx (list_lcm [1 .. n]))) *)
(* Proof:
   Let z = SUC n,
   Then z = p ** ppidx z              by given
   Note n <> 0 /\ z <> 1              by 0 < n
    ==> ppidx z <> 0                  by EXP_EQ_1, z <> 1
    ==> ?h. ppidx z = SUC h           by num_CASES

   Let l = [1 .. n], m = list_lcm l, j = ppidx m.
   Current goal is to show: SUC h = SUC j
   which only need to show:     h = j    by INV_SUC_EQ
   Note l <> []                          by listRangeINC_NIL
    and POSITIVE l                       by listRangeINC_MEM, [1]
   Also 1 < p                            by ONE_LT_PRIME

   Claim: h <= j
   Proof: Note h < SUC h                 by LESS_SUC
          Thus p ** h < z = p ** SUC h   by EXP_BASE_LT_MONO, 1 < p
           ==> p ** h <= n               by z = SUC n
          Also 0 < p ** h                by EXP_POS, 0 < p
           ==> MEM (p ** h) l            by listRangeINC_MEM, 0 < p ** h /\ p ** h <= n
          Note ppidx (p ** h) = h        by prime_power_index_prime_power
          Thus h <= j = ppidx m          by list_lcm_prime_power_index_lower, l <> []

   Claim: j <= h
   Proof: By contradiction, suppose h < j.
          Then SUC h <= j                by arithmetic
           ==> z divides p ** j          by power_divides_iff, 1 < p, z = p ** SUC h, SUC h <= j
           But p ** j divides m          by prime_power_factor_divides
           ==> z divides m               by DIVIDES_TRANS
          Thus ?y. MEM y l /\ z divides y    by list_lcm_prime_power_factor_member, l <> []
          Note 0 < y                     by all members of l, [1]
            so z <= y                    by DIVIDES_LE, 0 < y
            or SUC n <= y                by z = SUC n
           But ?u. n = u + 1             by num_CASES, ADD1, n <> 0
            so y <= n                    by listRangeINC_MEM, MEM y l
          This leads to SUC n <= n, a contradiction.

   By these two claims, h = j.
*)
val prime_power_index_suc_special = store_thm(
  "prime_power_index_suc_special",
  ``!n p. 0 < n /\ prime p /\ (SUC n = p ** ppidx (SUC n)) ==>
         (ppidx (SUC n) = SUC (ppidx (list_lcm [1 .. n])))``,
  rpt strip_tac >>
  qabbrev_tac `z = SUC n` >>
  `n <> 0 /\ z <> 1` by rw[Abbr`z`] >>
  `?h. ppidx z = SUC h` by metis_tac[EXP_EQ_1, num_CASES] >>
  qabbrev_tac `l = [1 .. n]` >>
  qabbrev_tac `m = list_lcm l` >>
  qabbrev_tac `j = ppidx m` >>
  `h <= j /\ j <= h` suffices_by rw[] >>
  `l <> []` by rw[listRangeINC_NIL, Abbr`l`] >>
  `POSITIVE l` by rw[Abbr`l`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  rpt strip_tac >| [
    `h < SUC h` by rw[] >>
    `p ** h < z` by metis_tac[EXP_BASE_LT_MONO] >>
    `p ** h <= n` by rw[Abbr`z`] >>
    `0 < p ** h` by rw[EXP_POS] >>
    `MEM (p ** h) l` by rw[Abbr`l`] >>
    metis_tac[prime_power_index_prime_power, list_lcm_prime_power_index_lower],
    spose_not_then strip_assume_tac >>
    `SUC h <= j` by decide_tac >>
    `z divides p ** j` by metis_tac[power_divides_iff] >>
    `p ** j divides m` by rw[prime_power_factor_divides, Abbr`j`] >>
    `z divides m` by metis_tac[DIVIDES_TRANS] >>
    `?y. MEM y l /\ z divides y` by metis_tac[list_lcm_prime_power_factor_member] >>
    `SUC n <= y` by rw[DIVIDES_LE, Abbr`z`] >>
    `y <= n` by metis_tac[listRangeINC_MEM] >>
    decide_tac
  ]);

(* Theorem: 0 < n /\ prime p /\ (n + 1 = p ** ppidx (n + 1)) ==>
            (ppidx (n + 1) = 1 + (ppidx (list_lcm [1 .. n]))) *)
(* Proof: by prime_power_index_suc_special, ADD1, ADD_COMM *)
val prime_power_index_suc_property = store_thm(
  "prime_power_index_suc_property",
  ``!n p. 0 < n /\ prime p /\ (n + 1 = p ** ppidx (n + 1)) ==>
         (ppidx (n + 1) = 1 + (ppidx (list_lcm [1 .. n])))``,
  metis_tac[prime_power_index_suc_special, ADD1, ADD_COMM]);

(* ------------------------------------------------------------------------- *)
(* Consecutive LCM Recurrence - Rework                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: SING (prime_divisors (n + 1)) ==>
            (list_lcm [1 .. (n + 1)] = CHOICE (prime_divisors (n + 1)) * list_lcm [1 .. n]) *)
(* Proof:
   Let z = n + 1.
   Then ?p. prime_divisors z = {p}      by SING_DEF
   By CHOICE_SING, this is to show: list_lcm [1 .. z] = p * list_lcm [1 .. n]

   Note prime p /\ (z = p ** ppidx z)   by prime_divisors_sing_property, CHOICE_SING
    and z <> 1 /\ n <> 0                by prime_divisors_1, NOT_SING_EMPTY, ADD
   Note ppidx z <> 0                    by EXP_EQ_1, z <> 1
    ==> ?h. ppidx z = SUC h             by num_CASES, EXP
   Thus z = p ** SUC h = p ** h * p     by EXP, MULT_COMM

   Let m = list_lcm [1 .. n], j = ppidx m.
   Note EVERY_POSITIVE l                by listRangeINC_MEM, EVERY_MEM
     so 0 < m                           by list_lcm_pos
    ==> ?q. (m = p ** j * q) /\
            coprime p q                 by prime_power_index_eqn
   Note 0 < n                           by n <> 0
   Thus SUC h = SUC j                   by prime_power_index_suc_special, ADD1, 0 < n
     or     h = j                       by INV_SUC_EQ

        list_lcm [1 .. z]
      = lcm z m                         by list_lcm_suc
      = p * m                           by lcm_special_for_prime_power
*)
Theorem list_lcm_by_last_prime_power:
  !n.
    SING (prime_divisors (n + 1)) ==>
    list_lcm [1 .. (n + 1)] =
    CHOICE (prime_divisors (n + 1)) * list_lcm [1 .. n]
Proof
  rpt strip_tac >>
  qabbrev_tac ‘z = n + 1’ >>
  ‘?p. prime_divisors z = {p}’ by rw[GSYM SING_DEF] >>
  rw[] >>
  ‘prime p /\ (z = p ** ppidx z)’ by metis_tac[prime_divisors_sing_property, CHOICE_SING] >>
  ‘z <> 1 /\ n <> 0’ by metis_tac[prime_divisors_1, NOT_SING_EMPTY, ADD] >>
  ‘?h. ppidx z = SUC h’ by metis_tac[EXP_EQ_1, num_CASES] >>
  qabbrev_tac ‘m = list_lcm [1 .. n]’ >>
  qabbrev_tac ‘j = ppidx m’ >>
  ‘0 < m’ by rw[list_lcm_pos, EVERY_MEM, Abbr‘m’] >>
  ‘?q. (m = p ** j * q) /\ coprime p q’ by metis_tac[prime_power_index_eqn] >>
  ‘0 < n’ by decide_tac >>
  ‘SUC h = SUC j’ by metis_tac[prime_power_index_suc_special, ADD1] >>
  ‘h = j’ by decide_tac >>
  ‘list_lcm [1 .. z] = lcm z m’ by rw[list_lcm_suc, Abbr‘z’, Abbr‘m’] >>
  ‘_ = p * m’ by metis_tac[lcm_special_for_prime_power] >>
  rw[]
QED

(* Theorem: ~ SING (prime_divisors (n + 1)) ==> (list_lcm [1 .. (n + 1)] = list_lcm [1 .. n]) *)
(* Proof:
   Let z = n + 1, l = [1 .. n], m = list_lcm l.
   The goal is to show: list_lcm [1 .. z] = m.

   If z = 1,
      Then n = 0               by 1 = n + 1
      LHS = list_lcm [1 .. z]
          = list_lcm [1 .. 1]    by z = 1
          = list_lcm [1]         by listRangeINC_SING
          = 1                    by list_lcm_sing
      RHS = list_lcm [1 .. n]
          = list_lcm [1 .. 0]    by n = 0
          = list_lcm []          by listRangeINC_EMPTY
          = 1 = LHS              by list_lcm_nil
   If z <> 1,
      Note z <> 0, or 0 < z      by z = n + 1
       ==> ?p. prime p /\ p divides z       by PRIME_FACTOR, z <> 1
       and 0 < ppidx z                      by prime_power_index_pos, 0 < z
       Let t = p ** ppidx z.
      Then ?q. (z = t * q) /\ coprime p q   by prime_power_index_eqn, 0 < z
       ==> coprime t q                      by coprime_exp
      Thus t <> 0 /\ q <> 0                 by MULT_EQ_0, z <> 0
       and q <> 1                           by prime_divisors_sing, MULT_RIGHT_1, ~SING (prime_divisors z)
      Note p <> 1                           by NOT_PRIME_1
       and t <> 1                           by EXP_EQ_1, ppidx z <> 0
      Thus 0 < q /\ q < n + 1               by z = t * q = n + 1
       and 0 < t /\ t < n + 1               by z = t * q = n + 1

      Then MEM q l                          by listRangeINC_MEM, 1 <= q <= n
       and MEM t l                          by listRangeINC_MEM, 1 <= t <= n
       ==> q divides m /\ t divides m       by list_lcm_is_common_multiple
       ==> q * t = z divides m              by coprime_product_divides, coprime t q

         list_lcm [1 .. z]
       = lcm z m                 by list_lcm_suc
       = m                       by divides_iff_lcm_fix
*)

Theorem list_lcm_by_last_non_prime_power:
  !n. ~ SING (prime_divisors (n + 1)) ==>
      list_lcm [1 .. (n + 1)] = list_lcm [1 .. n]
Proof
  rpt strip_tac >>
  qabbrev_tac `z = n + 1` >>
  Cases_on `z = 1` >| [
    `n = 0` by rw[Abbr`z`] >>
    `([1 .. z] = [1]) /\ ([1 .. n] = [])` by rw[listRangeINC_EMPTY] >>
    rw[list_lcm_sing, list_lcm_nil],
    `z <> 0 /\ 0 < z` by rw[Abbr`z`] >>
    `?p. prime p /\ p divides z` by rw[PRIME_FACTOR] >>
    `0 < ppidx z` by rw[prime_power_index_pos] >>
    qabbrev_tac `t = p ** ppidx z` >>
    `?q. (z = t * q) /\ coprime p q /\ coprime t q`
      by metis_tac[prime_power_index_eqn, coprime_exp] >>
    `t <> 0 /\ q <> 0` by metis_tac[MULT_EQ_0] >>
    `q <> 1` by metis_tac[prime_divisors_sing, MULT_RIGHT_1] >>
    `t <> 1` by metis_tac[EXP_EQ_1, NOT_PRIME_1, NOT_ZERO_LT_ZERO] >>
    `0 < q /\ q < n + 1` by rw[Abbr`z`] >>
    `0 < t /\ t < n + 1` by rw[Abbr`z`] >>
    qabbrev_tac `l = [1 .. n]` >>
    qabbrev_tac `m = list_lcm l` >>
    `MEM q l /\ MEM t l` by rw[Abbr`l`] >>
    `q divides m /\ t divides m`
      by simp[list_lcm_is_common_multiple, Abbr`m`] >>
    `z divides m`
      by (simp[] >> metis_tac[coprime_sym, coprime_product_divides]) >>
    `list_lcm [1 .. z] = lcm z m` by rw[list_lcm_suc, Abbr`z`, Abbr`m`] >>
    `_ = m` by rw[GSYM divides_iff_lcm_fix] >>
    rw[]
  ]
QED

(* Theorem: list_lcm [1 .. (n + 1)] = let s = prime_divisors (n + 1) in
            if SING s then CHOICE s * list_lcm [1 .. n] else list_lcm [1 .. n] *)
(* Proof: by list_lcm_with_last_prime_power, list_lcm_with_last_non_prime_power *)
val list_lcm_recurrence = store_thm(
  "list_lcm_recurrence",
  ``!n. list_lcm [1 .. (n + 1)] = let s = prime_divisors (n + 1) in
       if SING s then CHOICE s * list_lcm [1 .. n] else list_lcm [1 .. n]``,
  rw[list_lcm_by_last_prime_power, list_lcm_by_last_non_prime_power]);

(* Theorem: (prime_divisors (n + 1) = {p}) ==> (list_lcm [1 .. (n + 1)] = p * list_lcm [1 .. n]) *)
(* Proof: by list_lcm_by_last_prime_power, SING_DEF *)
val list_lcm_option_last_prime_power = store_thm(
  "list_lcm_option_last_prime_power",
  ``!n p. (prime_divisors (n + 1) = {p}) ==> (list_lcm [1 .. (n + 1)] = p * list_lcm [1 .. n])``,
  rw[list_lcm_by_last_prime_power, SING_DEF]);

(* Theorem:  (!p. prime_divisors (n + 1) <> {p}) ==> (list_lcm [1 .. (n + 1)] = list_lcm [1 .. n]) *)
(* Proof: by ist_lcm_by_last_non_prime_power, SING_DEF *)
val list_lcm_option_last_non_prime_power = store_thm(
  "list_lcm_option_last_non_prime_power",
  ``!n. (!p. prime_divisors (n + 1) <> {p}) ==> (list_lcm [1 .. (n + 1)] = list_lcm [1 .. n])``,
  rw[list_lcm_by_last_non_prime_power, SING_DEF]);

(* Theorem: list_lcm [1 .. (n + 1)] = case some p. (prime_divisors (n + 1)) = {p} of
              NONE => list_lcm [1 .. n]
            | SOME p => p * list_lcm [1 .. n] *)
(* Proof:
   For SOME p, true by list_lcm_option_last_prime_power
   For NONE, true   by list_lcm_option_last_non_prime_power
*)
val list_lcm_option_recurrence = store_thm(
  "list_lcm_option_recurrence",
  ``!n. list_lcm [1 .. (n + 1)] = case some p. (prime_divisors (n + 1)) = {p} of
              NONE => list_lcm [1 .. n]
            | SOME p => p * list_lcm [1 .. n]``,
  rpt strip_tac >>
  DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[list_lcm_option_last_prime_power, list_lcm_option_last_non_prime_power]);

(* ------------------------------------------------------------------------- *)
(* Relating Consecutive LCM to Prime Functions                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MEM x (SET_TO_LIST (prime_powers_upto n)) <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= n *)
(* Proof:
   Let s = prime_powers_upto n.
   Then FINITE s                             by prime_powers_upto_finite
    and !x. x IN s <=> MEM x (SET_TO_LIST s) by MEM_SET_TO_LIST
    The result follows                       by prime_powers_upto_element
*)
val prime_powers_upto_list_mem = store_thm(
  "prime_powers_upto_list_mem",
  ``!n x. MEM x (SET_TO_LIST (prime_powers_upto n)) <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= n``,
  rw[MEM_SET_TO_LIST, prime_powers_upto_element, prime_powers_upto_finite]);

(*
LOG_EQ_0  |- !a b. 1 < a /\ 0 < b ==> ((LOG a b = 0) <=> b < a)
*)

(* Theorem: prime p /\ p <= n ==> p ** LOG p n divides set_lcm (prime_powers_upto n) *)
(* Proof:
   Let s = prime_powers_upto n.
   Note FINITE s                        by prime_powers_upto_finite
    and p ** LOG p n IN s               by prime_powers_upto_element_alt
    ==> p ** LOG p n divides set_lcm s  by set_lcm_is_common_multiple
*)
val prime_powers_upto_lcm_prime_to_log_divisor = store_thm(
  "prime_powers_upto_lcm_prime_to_log_divisor",
  ``!n p. prime p /\ p <= n ==> p ** LOG p n divides set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  `FINITE (prime_powers_upto n)` by rw[prime_powers_upto_finite] >>
  `p ** LOG p n IN prime_powers_upto n` by rw[prime_powers_upto_element_alt] >>
  rw[set_lcm_is_common_multiple]);

(* Theorem: prime p /\ p <= n ==> p divides set_lcm (prime_powers_upto n) *)
(* Proof:
   Note 1 < p                           by ONE_LT_PRIME
     so LOG p n <> 0                    by LOG_EQ_0, 1 < p
    ==> p divides p ** LOG p n          by divides_self_power, 1 < p

   Note p ** LOG p n divides set_lcm s  by prime_powers_upto_lcm_prime_to_log_divisor
   Thus p divides set_lcm s             by DIVIDES_TRANS
*)
val prime_powers_upto_lcm_prime_divisor = store_thm(
  "prime_powers_upto_lcm_prime_divisor",
  ``!n p. prime p /\ p <= n ==> p divides set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `LOG p n <> 0` by rw[LOG_EQ_0] >>
  `p divides p ** LOG p n` by rw[divides_self_power] >>
  `p ** LOG p n divides set_lcm (prime_powers_upto n)` by rw[prime_powers_upto_lcm_prime_to_log_divisor] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: prime p /\ p <= n ==> p ** ppidx n divides set_lcm (prime_powers_upto n) *)
(* Proof:
   Note 1 < p                by ONE_LT_PRIME
    and 0 < n                by p <= n
    ==> ppidx n <= LOG p n   by prime_power_index_le_log_index, 0 < n
   Thus p ** ppidx n divides p ** LOG p n                   by power_divides_iff, 1 < p
    and p ** LOG p n divides set_lcm (prime_powers_upto n)  by prime_powers_upto_lcm_prime_to_log_divisor
     or p ** ppidx n divides set_lcm (prime_powers_upto n)  by DIVIDES_TRANS
*)
val prime_powers_upto_lcm_prime_to_power_divisor = store_thm(
  "prime_powers_upto_lcm_prime_to_power_divisor",
  ``!n p. prime p /\ p <= n ==> p ** ppidx n divides set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `0 < n` by decide_tac >>
  `ppidx n <= LOG p n` by rw[prime_power_index_le_log_index] >>
  `p ** ppidx n divides p ** LOG p n` by rw[power_divides_iff] >>
  `p ** LOG p n divides set_lcm (prime_powers_upto n)` by rw[prime_powers_upto_lcm_prime_to_log_divisor] >>
  metis_tac[DIVIDES_TRANS]);

(* The next theorem is based on this example:
Take n = 10,
prime_powers_upto 10 = {2^3; 3^2; 5^1; 7^1} = {8; 9; 5; 7}
set_lcm (prime_powers_upto 10) = 2520
For any 1 <= x <= 10, e.g. x = 6.
6 <= 10, 6 divides set_lcm (prime_powers_upto 10).

The reason is that:
6 = PROD_SET (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))   by prime_factorisation
prime_divisors 6 = {2; 3}
Because 2, 3 <= 6, 6 <= 10, the divisors 2,3 <= 10           by DIVIDES_LE
Thus 2^(LOG 2 10) = 2^3, 3^(LOG 3 10) = 3^2 IN prime_powers_upto 10)    by prime_powers_upto_element_alt
But  2^(ppidx 6) = 2^1 = 2 divides 6, 3^(ppidx 6) = 3^1 = 3 divides 6   by prime_power_index_def
 so  2^(ppidx 6) <= 10   and 3^(ppidx 6) <= 10.

In this example, 2^1 < 2^3    3^1 < 3^2  how to compare (ppidx x) with (LOG p n) in general? ##
Due to this,  2^(ppidx 6) divides 2^(LOG 2 10),    by prime_powers_divide
       and    3^(ppidx 6) divides 3^(LOG 3 10),
And 2^(LOG 2 10) divides set_lcm (prime_powers_upto 10)    by prime_powers_upto_lcm_prime_to_log_divisor
and 3^(LOG 3 10) divides set_lcm (prime_powers_upto 10)    by prime_powers_upto_lcm_prime_to_log_divisor
or !z. z IN (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))
   ==> z divides set_lcm (prime_powers_upto 10)            by verification
Hence set_lcm (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))  divides set_lcm (prime_powers_upto 10)
                                                           by set_lcm_is_least_common_multiple
But PAIRWISE_COPRIME (IMAGE (\p. p ** ppidx 6) (prime_divisors 6)),
Thus set_lcm (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))
   = PROD_SET (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))    by pairwise_coprime_prod_set_eq_set_lcm
   = 6                                                         by above
Hence x divides set_lcm (prime_powers_upto 10)

## maybe:
   ppidx x <= LOG p x       by prime_power_index_le_log_index
   LOG p x <= LOG p n       by LOG_LE_MONO
*)

(* Theorem: 0 < x /\ x <= n ==> x divides set_lcm (prime_powers_upto n) *)
(* Proof:
   Note 0 < n                  by 0 < x /\ x <= n
   Let m = set_lcm (prime_powers_upto n).
   The goal becomes: x divides m.

   Let s = prime_power_divisors x.
   Then x = PROD_SET s         by prime_factorisation, 0 < x

   Claim: !z. z IN s ==> z divides m
   Proof: By prime_power_divisors_element, this is to show:
             prime p /\ p divides x ==> p ** ppidx x divides m
          Note p <= x                     by DIVIDES_LE, 0 < x
          Thus p <= n                     by p <= x, x <= n
           ==> p ** LOG p n IN prime_powers_upto n   by prime_powers_upto_element_alt, b <= n
           ==> p ** LOG p n divides m     by prime_powers_upto_lcm_prime_to_log_divisor
          Note 1 < p                      by ONE_LT_PRIME
           and ppidx x <= LOG p x         by prime_power_index_le_log_index, 0 < n
          also LOG p x <= LOG p n         by LOG_LE_MONO, 1 < p
           ==> ppidx x <= LOG p n         by arithmetic
           ==> p ** ppidx x divides p ** LOG p n   by power_divides_iff, 1 < p
          Thus p ** ppidx x divides m     by DIVIDES_TRANS

   Note FINITE s                by prime_power_divisors_finite
    and set_lcm s divides m     by set_lcm_is_least_common_multiple, FINITE s
   Also PAIRWISE_COPRIME s      by prime_power_divisors_pairwise_coprime
    ==> PROD_SET s = set_lcm s  by pairwise_coprime_prod_set_eq_set_lcm
   Thus x divides m             by set_lcm s divides m
*)
val prime_powers_upto_lcm_divisor = store_thm(
  "prime_powers_upto_lcm_divisor",
  ``!n x. 0 < x /\ x <=  n ==> x divides set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  qabbrev_tac `m = set_lcm (prime_powers_upto n)` >>
  qabbrev_tac `s = prime_power_divisors x` >>
  `x = PROD_SET s` by rw[prime_factorisation, Abbr`s`] >>
  `!z. z IN s ==> z divides m` by
  (rw[prime_power_divisors_element, Abbr`s`] >>
  `p <= x` by rw[DIVIDES_LE] >>
  `p <= n` by decide_tac >>
  `p ** LOG p n IN prime_powers_upto n` by rw[prime_powers_upto_element_alt] >>
  `p ** LOG p n divides m` by rw[prime_powers_upto_lcm_prime_to_log_divisor, Abbr`m`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `ppidx x <= LOG p x` by rw[prime_power_index_le_log_index] >>
  `LOG p x <= LOG p n` by rw[LOG_LE_MONO] >>
  `ppidx x <= LOG p n` by decide_tac >>
  `p ** ppidx x divides p ** LOG p n` by rw[power_divides_iff] >>
  metis_tac[DIVIDES_TRANS]) >>
  `FINITE s` by rw[prime_power_divisors_finite, Abbr`s`] >>
  `set_lcm s divides m` by rw[set_lcm_is_least_common_multiple] >>
  metis_tac[prime_power_divisors_pairwise_coprime, pairwise_coprime_prod_set_eq_set_lcm]);

(* This is a key result. *)

(* ------------------------------------------------------------------------- *)
(* Consecutive LCM and Prime-related Sets                                    *)
(* ------------------------------------------------------------------------- *)

(*
Useful:
list_lcm_is_common_multiple  |- !x l. MEM x l ==> x divides list_lcm l
list_lcm_prime_factor        |- !p l. prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l)
list_lcm_prime_factor_member |- !p l. prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x
prime_power_index_pos        |- !n p. 0 < n /\ prime p /\ p divides n ==> 0 < ppidx n
*)

(* Theorem: lcm_run n = set_lcm (prime_powers_upto n) *)
(* Proof:
   By DIVIDES_ANTISYM, this is to show:
   (1) lcm_run n divides set_lcm (prime_powers_upto n)
       Let m = set_lcm (prime_powers_upto n)
       Note !x. MEM x [1 .. n] <=> 0 < x /\ x <= n   by listRangeINC_MEM
        and !x. 0 < x /\ x <= n ==> x divides m      by prime_powers_upto_lcm_divisor
       Thus lcm_run n divides m                      by list_lcm_is_least_common_multiple
   (2) set_lcm (prime_powers_upto n) divides lcm_run n
       Let s = prime_powers_upto n, m = lcm_run n
       Claim: !z. z IN s ==> z divides m
       Proof: Note ?p. (z = p ** LOG p n) /\
                       prime p /\ p <= n             by prime_powers_upto_element
               Now 0 < p                             by PRIME_POS
                so MEM p [1 .. n]                    by listRangeINC_MEM
               ==> MEM z [1 .. n]                    by self_to_log_index_member
              Thus z divides m                       by list_lcm_is_common_multiple

       Note FINITE s                   by prime_powers_upto_finite
       Thus set_lcm s divides m        by set_lcm_is_least_common_multiple, Claim
*)
val lcm_run_eq_set_lcm_prime_powers = store_thm(
  "lcm_run_eq_set_lcm_prime_powers",
  ``!n. lcm_run n = set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  (irule DIVIDES_ANTISYM >> rpt conj_tac) >| [
    `!x. MEM x [1 .. n] <=> 0 < x /\ x <= n` by rw[listRangeINC_MEM] >>
    `!x. 0 < x /\ x <= n ==> x divides set_lcm (prime_powers_upto n)` by rw[prime_powers_upto_lcm_divisor] >>
    rw[list_lcm_is_least_common_multiple],
    qabbrev_tac `s = prime_powers_upto n` >>
    qabbrev_tac `m = lcm_run n` >>
    `!z. z IN s ==> z divides m` by
  (rw[prime_powers_upto_element, Abbr`s`] >>
    `0 < p` by rw[PRIME_POS] >>
    `MEM p [1 .. n]` by rw[listRangeINC_MEM] >>
    `MEM (p ** LOG p n) [1 .. n]` by rw[self_to_log_index_member] >>
    rw[list_lcm_is_common_multiple, Abbr`m`]) >>
    `FINITE s` by rw[prime_powers_upto_finite, Abbr`s`] >>
    rw[set_lcm_is_least_common_multiple]
  ]);

(* Theorem: set_lcm (prime_powers_upto n) = PROD_SET (prime_powers_upto n) *)
(* Proof:
   Let s = prime_powers_upto n.
   Note FINITE s                  by prime_powers_upto_finite
    and PAIRWISE_COPRIME s        by prime_powers_upto_pairwise_coprime
   Thus set_lcm s = PROD_SET s    by pairwise_coprime_prod_set_eq_set_lcm
*)
val set_lcm_prime_powers_upto_eqn = store_thm(
  "set_lcm_prime_powers_upto_eqn",
  ``!n. set_lcm (prime_powers_upto n) = PROD_SET (prime_powers_upto n)``,
  metis_tac[prime_powers_upto_finite, prime_powers_upto_pairwise_coprime, pairwise_coprime_prod_set_eq_set_lcm]);

(* Theorem: lcm_run n = PROD_SET (prime_powers_upto n) *)
(* Proof:
     lcm_run n
   = set_lcm (prime_powers_upto n)
   = PROD_SET (prime_powers_upto n)
*)
val lcm_run_eq_prod_set_prime_powers = store_thm(
  "lcm_run_eq_prod_set_prime_powers",
  ``!n. lcm_run n = PROD_SET (prime_powers_upto n)``,
  rw[lcm_run_eq_set_lcm_prime_powers, set_lcm_prime_powers_upto_eqn]);

(* Theorem: PROD_SET (prime_powers_upto n) <= n ** (primes_count n) *)
(* Proof:
   Let s = (primes_upto n), f = \p. p ** LOG p n, t = prime_powers_upto n.
   Then IMAGE f s = t              by prime_powers_upto_def
    and FINITE s                   by primes_upto_finite
    and FINITE t                   by IMAGE_FINITE

   Claim: !x. x IN t ==> x <= n
   Proof: Note x IN t ==>
               ?p. (x = p ** LOG p n) /\ prime p /\ p <= n   by prime_powers_upto_element
           Now 1 < p               by ONE_LT_PRIME
            so 0 < n               by 1 < p, p <= n
           and p ** LOG p n <= n   by LOG
            or x <= n

   Thus PROD_SET t <= n ** CARD t  by PROD_SET_LE_CONSTANT, Claim

   Claim: INJ f s t
   Proof: By prime_powers_upto_element_alt, primes_upto_element, INJ_DEF,
          This is to show: prime p /\ prime p' /\ p ** LOG p n = p' ** LOG p' n ==> p = p'
          Note 1 < p               by ONE_LT_PRIME
            so 0 < n               by 1 < p, p <= n
           and LOG p n <> 0        by LOG_EQ_0, p <= n
            or 0 < LOG p n         by NOT_ZERO_LT_ZERO
           ==> p = p'              by prime_powers_eq

   Thus CARD (IMAGE f s) = CARD s  by INJ_CARD_IMAGE, Claim
     or PROD_SET t <= n ** CARD s  by above
*)

Theorem prime_powers_upto_prod_set_le:
  !n. PROD_SET (prime_powers_upto n) <= n ** (primes_count n)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘s = (primes_upto n)’ >>
  qabbrev_tac ‘f = \p. p ** LOG p n’ >>
  qabbrev_tac ‘t = prime_powers_upto n’ >>
  ‘IMAGE f s = t’ by simp[prime_powers_upto_def, Abbr‘f’, Abbr‘s’, Abbr‘t’] >>
  ‘FINITE s’ by rw[primes_upto_finite, Abbr‘s’] >>
  ‘FINITE t’ by metis_tac[IMAGE_FINITE] >>
  ‘!x. x IN t ==> x <= n’
    by (rw[prime_powers_upto_element, Abbr‘t’, Abbr‘f’] >>
        ‘1 < p’ by rw[ONE_LT_PRIME] >>
        rw[LOG]) >>
  ‘PROD_SET t <= n ** CARD t’ by rw[PROD_SET_LE_CONSTANT] >>
  ‘INJ f s t’
    by (rw[prime_powers_upto_element_alt, primes_upto_element, INJ_DEF, Abbr‘f’,
           Abbr‘s’, Abbr‘t’] >>
        ‘1 < p’ by rw[ONE_LT_PRIME] >>
        ‘0 < n’ by decide_tac >>
        ‘LOG p n <> 0’ by rw[LOG_EQ_0] >>
        metis_tac[prime_powers_eq, NOT_ZERO_LT_ZERO]) >>
  metis_tac[INJ_CARD_IMAGE]
QED

(* Theorem: lcm_run n <= n ** (primes_count n) *)
(* Proof:
      lcm_run n
    = PROD_SET (prime_powers_upto n)   by lcm_run_eq_prod_set_prime_powers
   <= n ** (primes_count n)            by prime_powers_upto_prod_set_le
*)
val lcm_run_upper_by_primes_count = store_thm(
  "lcm_run_upper_by_primes_count",
  ``!n. lcm_run n <= n ** (primes_count n)``,
  rw[lcm_run_eq_prod_set_prime_powers, prime_powers_upto_prod_set_le]);

(* This is a significant result. *)

(* Theorem: PROD_SET (primes_upto n) <= PROD_SET (prime_powers_upto n) *)
(* Proof:
   Let s = primes_upto n, f = \p. p ** LOG p n, t = prime_powers_upto n.
   The goal becomes: PROD_SET s <= PROD_SET t
   Note IMAGE f s = t           by prime_powers_upto_def
    and FINITE s                by primes_upto_finite

   Claim: INJ f s univ(:num)
   Proof: By primes_upto_element, INJ_DEF,
          This is to show: prime p /\ prime p' /\ p ** LOG p n = p' ** LOG p' n ==> p = p'
          Note 1 < p            by ONE_LT_PRIME
            so 0 < n            by 1 < p, p <= n
          Thus LOG p n <> 0     by LOG_EQ_0, p <= n
            or 0 < LOG p n      by NOT_ZERO_LT_ZERO
           ==> p = p'           by prime_powers_eq

   Also INJ I s univ(:num)      by primes_upto_element, INJ_DEF
    and IMAGE I s = s           by IMAGE_I

   Claim: !x. x IN s ==> I x <= f x
   Proof: By primes_upto_element,
          This is to show: prime x /\ x <= n ==> x <= x ** LOG x n
          Note 1 < x            by ONE_LT_PRIME
            so 0 < n            by 1 < x, x <= n
          Thus LOG x n <> 0     by LOG_EQ_0
            or 1 <= LOG x n     by LOG x n <> 0
           ==> x ** 1 <= x ** LOG x n   by EXP_BASE_LE_MONO
            or      x <= x ** LOG x n   by EXP_1

   Hence PROD_SET s <= PROD_SET t       by PROD_SET_LESS_EQ
*)
val prime_powers_upto_prod_set_ge = store_thm(
  "prime_powers_upto_prod_set_ge",
  ``!n. PROD_SET (primes_upto n) <= PROD_SET (prime_powers_upto n)``,
  rpt strip_tac >>
  qabbrev_tac `s = primes_upto n` >>
  qabbrev_tac `f = \p. p ** LOG p n` >>
  qabbrev_tac `t = prime_powers_upto n` >>
  `IMAGE f s = t` by rw[prime_powers_upto_def, Abbr`f`, Abbr`s`, Abbr`t`] >>
  `FINITE s` by rw[primes_upto_finite, Abbr`s`] >>
  `INJ f s univ(:num)` by
  (rw[primes_upto_element, INJ_DEF, Abbr`f`, Abbr`s`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `LOG p n <> 0` by rw[LOG_EQ_0] >>
  metis_tac[prime_powers_eq, NOT_ZERO_LT_ZERO]) >>
  `INJ I s univ(:num)` by rw[primes_upto_element, INJ_DEF, Abbr`s`] >>
  `IMAGE I s = s` by rw[] >>
  `!x. x IN s ==> I x <= f x` by
    (rw[primes_upto_element, Abbr`f`, Abbr`s`] >>
  `1 < x` by rw[ONE_LT_PRIME] >>
  `LOG x n <> 0` by rw[LOG_EQ_0] >>
  `1 <= LOG x n` by decide_tac >>
  metis_tac[EXP_BASE_LE_MONO, EXP_1]) >>
  metis_tac[PROD_SET_LESS_EQ]);

(* Theorem: PROD_SET (primes_upto n) <= lcm_run n *)
(* Proof:
      lcm_run n
    = set_lcm (prime_powers_upto n)    by lcm_run_eq_set_lcm_prime_powers
    = PROD_SET (prime_powers_upto n)   by set_lcm_prime_powers_upto_eqn
   >= PROD_SET (primes_upto n)         by prime_powers_upto_prod_set_ge
*)
val lcm_run_lower_by_primes_product = store_thm(
  "lcm_run_lower_by_primes_product",
  ``!n. PROD_SET (primes_upto n) <= lcm_run n``,
  rpt strip_tac >>
  `lcm_run n = set_lcm (prime_powers_upto n)` by rw[lcm_run_eq_set_lcm_prime_powers] >>
  `_ = PROD_SET (prime_powers_upto n)` by rw[set_lcm_prime_powers_upto_eqn] >>
  rw[prime_powers_upto_prod_set_ge]);

(* This is another significant result. *)

(* These are essentially Chebyshev functions. *)

(* Theorem: n ** primes_count n <= PROD_SET (primes_upto n) * (PROD_SET (prime_powers_upto n)) *)
(* Proof:
   Let s = (primes_upto n), f = \p. p ** LOG p n, t = prime_powers_upto n.
   The goal becomes: n ** CARD s <= PROD_SET s * PROD_SET t

   Note IMAGE f s = t                 by prime_powers_upto_def
    and FINITE s                      by primes_upto_finite
    and FINITE t                      by IMAGE_FINITE

   Claim: !p. p IN s ==> n <= I p * f p
   Proof: By primes_upto_element,
          This is to show: prime p /\ p <= n ==> n < p * p ** LOG p n
          Note 1 < p                  by ONE_LT_PRIME
            so 0 < n                  by 1 < p, p <= n
           ==> n < p ** (SUC (LOG p n))   by LOG
                 = p * p ** (LOG p n)     by EXP
            or n <= p * p ** (LOG p n)    by LESS_IMP_LESS_OR_EQ

   Note INJ I s univ(:num)            by primes_upto_element, INJ_DEF,
    and IMAGE I s = s                 by IMAGE_I

   Claim: INJ f s univ(:num)
   Proof: By primes_upto_element, INJ_DEF,
          This is to show: prime p /\ prime p' /\ p ** LOG p n = p' ** LOG p' n ==> p = p'
          Note 1 < p                  by ONE_LT_PRIME
            so 0 < n                  by 1 < p, p <= n
           ==> LOG p n <> 0           by LOG_EQ_0
            or 0 < LOG p n            by NOT_ZERO_LT_ZERO
          Thus p = p'                 by prime_powers_eq

   Therefore,
          n ** CARD s <= PROD_SET (IMAGE I s) * PROD_SET (IMAGE f s)
                                                     by PROD_SET_PRODUCT_GE_CONSTANT
      or  n ** CARD s <= PROD_SET s * PROD_SET t     by above
*)

Theorem prime_powers_upto_prod_set_mix_ge:
  !n. n ** primes_count n <=
        PROD_SET (primes_upto n) * (PROD_SET (prime_powers_upto n))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘s = (primes_upto n)’ >>
  qabbrev_tac ‘f = \p. p ** LOG p n’ >>
  qabbrev_tac ‘t = prime_powers_upto n’ >>
  ‘IMAGE f s = t’ by rw[prime_powers_upto_def, Abbr‘f’, Abbr‘s’, Abbr‘t’] >>
  ‘FINITE s’ by rw[primes_upto_finite, Abbr‘s’] >>
  ‘FINITE t’ by rw[] >>
  ‘!p. p IN s ==> n <= I p * f p’ by
  (rw[primes_upto_element, Abbr‘s’, Abbr‘f’] >>
  ‘1 < p’ by rw[ONE_LT_PRIME] >>
  rw[LOG, GSYM EXP, LESS_IMP_LESS_OR_EQ]) >>
  ‘INJ I s univ(:num)’ by rw[primes_upto_element, INJ_DEF, Abbr‘s’] >>
  ‘IMAGE I s = s’ by rw[] >>
  ‘INJ f s univ(:num)’ by
    (rw[primes_upto_element, INJ_DEF, Abbr‘f’, Abbr‘s’] >>
  ‘1 < p’ by rw[ONE_LT_PRIME] >>
  ‘LOG p n <> 0’ by rw[LOG_EQ_0] >>
  metis_tac[prime_powers_eq, NOT_ZERO_LT_ZERO]) >>
  metis_tac[PROD_SET_PRODUCT_GE_CONSTANT]);

(* Another significant result. *)

(* Theorem: n ** primes_count n <= PROD_SET (primes_upto n) * lcm_run n *)
(* Proof:
      n ** primes_count n
   <= PROD_SET (primes_upto n) * (PROD_SET (prime_powers_upto n))  by prime_powers_upto_prod_set_mix_ge
    = PROD_SET (primes_upto n) * lcm_run n                         by lcm_run_eq_prod_set_prime_powers
*)
val primes_count_upper_by_product = store_thm(
  "primes_count_upper_by_product",
  ``!n. n ** primes_count n <= PROD_SET (primes_upto n) * lcm_run n``,
  metis_tac[prime_powers_upto_prod_set_mix_ge, lcm_run_eq_prod_set_prime_powers]);

(* Theorem: n ** primes_count n <= (lcm_run n) ** 2 *)
(* Proof:
      n ** primes_count n
   <= PROD_SET (primes_upto n) * lcm_run n     by primes_count_upper_by_product
   <= lcm_run n * lcm_run n                    by lcm_run_lower_by_primes_product
    = (lcm_run n) ** 2                         by EXP_2
*)
val primes_count_upper_by_lcm_run = store_thm(
  "primes_count_upper_by_lcm_run",
  ``!n. n ** primes_count n <= (lcm_run n) ** 2``,
  rpt strip_tac >>
  `n ** primes_count n <= PROD_SET (primes_upto n) * lcm_run n` by rw[primes_count_upper_by_product] >>
  `PROD_SET (primes_upto n) <= lcm_run n` by rw[lcm_run_lower_by_primes_product] >>
  metis_tac[LESS_MONO_MULT, LESS_EQ_TRANS, EXP_2]);

(* Theorem: SQRT (n ** (primes_count n)) <= lcm_run n *)
(* Proof:
   Note          n ** primes_count n <= (lcm_run n) ** 2         by primes_count_upper_by_lcm_run
    ==>   SQRT (n ** primes_count n) <= SQRT ((lcm_run n) ** 2)  by ROOT_LE_MONO, 0 < 2
    But   SQRT ((lcm_run n) ** 2) = lcm_run n                    by ROOT_UNIQUE
   Thus SQRT (n ** (primes_count n)) <= lcm_run n
*)
val lcm_run_lower_by_primes_count = store_thm(
  "lcm_run_lower_by_primes_count",
  ``!n. SQRT (n ** (primes_count n)) <= lcm_run n``,
  rpt strip_tac >>
  `n ** primes_count n <= (lcm_run n) ** 2` by rw[primes_count_upper_by_lcm_run] >>
  `SQRT (n ** primes_count n) <= SQRT ((lcm_run n) ** 2)` by rw[ROOT_LE_MONO] >>
  `SQRT ((lcm_run n) ** 2) = lcm_run n` by rw[ROOT_UNIQUE] >>
  decide_tac);

(* Therefore:
   L(n) <= n ** pi(n)            by lcm_run_upper_by_primes_count
   PI(n) <= L(n)                 by lcm_run_lower_by_primes_product
   n ** pi(n) <= PI(n) * L(n)    by primes_count_upper_by_product

   giving:               L(n) <= n ** pi(n) <= L(n) ** 2      by primes_count_upper_by_lcm_run
      and:  SQRT (n ** pi(n)) <=       L(n) <= (n ** pi(n))   by lcm_run_lower_by_primes_count
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
