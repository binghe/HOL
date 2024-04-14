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
val _ = html_theory "helperFunction";

(*===========================================================================*)
