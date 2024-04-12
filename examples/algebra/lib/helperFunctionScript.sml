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
