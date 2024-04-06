(* ------------------------------------------------------------------------- *)
(* Elementary Number Theory - a collection of useful results for numbers     *)
(* (gcdset = greatest common divisor of a set of numbers)                    *)
(*                                                                           *)
(* Author: Hing-Lun Chan (Australian National University, 2019)              *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib BasicProvers

open arithmeticTheory dividesTheory gcdTheory pred_setTheory simpLib metisLib;

val ARITH_ss = numSimps.ARITH_ss;
val DECIDE = numLib.ARITH_PROVE;

fun DECIDE_TAC (g as (asl,_)) =
  ((MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith asl) THEN
    CONV_TAC Arith.ARITH_CONV)
   ORELSE tautLib.TAUT_TAC) g;

val arith_ss = bool_ss ++ ARITH_ss;
val std_ss = arith_ss;
val decide_tac = DECIDE_TAC;
val metis_tac = METIS_TAC;
val rw = SRW_TAC [ARITH_ss];
val simp = ASM_SIMP_TAC (srw_ss() ++ ARITH_ss);
val fs = FULL_SIMP_TAC (srw_ss() ++ ARITH_ss);
val qabbrev_tac = Q.ABBREV_TAC;
val qexists_tac = Q.EXISTS_TAC;

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
(* Set Theorems (from examples/algebra)                                      *)
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

(* Theorem: {x} SUBSET s /\ SING s <=> (s = {x}) *)
(* Proof:
   Note {x} SUBSET s ==> x IN s           by SUBSET_DEF
    and SING s ==> ?y. s = {y}            by SING_DEF
   Thus x IN {y} ==> x = y                by IN_SING
*)
Theorem SING_SUBSET :
    !s x. {x} SUBSET s /\ SING s <=> (s = {x})
Proof
    metis_tac[SING_DEF, IN_SING, SUBSET_DEF]
QED

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

(* Theorem: x NOTIN s ==> (x INSERT s) DELETE x = s *)
(* Proof:
    (x INSERT s) DELETE x
   = s DELETE x         by DELETE_INSERT
   = s                  by DELETE_NON_ELEMENT
*)
Theorem INSERT_DELETE_NON_ELEMENT:
  !x s. x NOTIN s ==> (x INSERT s) DELETE x = s
Proof
  simp[DELETE_INSERT, DELETE_NON_ELEMENT]
QED

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

(* in pred_setTheory:
SUBSET_DELETE_BOTH |- !s1 s2 x. s1 SUBSET s2 ==> s1 DELETE x SUBSET s2 DELETE x
*)

(* Theorem: s1 SUBSET s2 ==> x INSERT s1 SUBSET x INSERT s2 *)
(* Proof: by SUBSET_DEF *)
Theorem SUBSET_INSERT_BOTH:
  !s1 s2 x. s1 SUBSET s2 ==> x INSERT s1 SUBSET x INSERT s2
Proof
  simp[SUBSET_DEF]
QED

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

(* Theorem: FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t) *)
(* Proof:
   If part: CARD s = CARD t ==> s = t
      By contradiction, suppose s <> t.
      Then s PSUBSET t         by PSUBSET_DEF
        so CARD s < CARD t     by CARD_PSUBSET, FINITE t
      This contradicts CARD s = CARD t.
   Only-if part is trivial.
*)
Theorem SUBSET_CARD_EQ:
  !s t. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)
Proof
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `s PSUBSET t` by rw[PSUBSET_DEF] >>
  `CARD s < CARD t` by rw[CARD_PSUBSET] >>
  decide_tac
QED

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

(* Theorem: SURJ f s t ==> CARD (IMAGE f s) = CARD t *)
(* Proof:
   Note IMAGE f s = t              by IMAGE_SURJ
   Thus CARD (IMAGE f s) = CARD t  by above
*)
Theorem SURJ_CARD_IMAGE:
  !f s t. SURJ f s t ==> CARD (IMAGE f s) = CARD t
Proof
  simp[IMAGE_SURJ]
QED

(* ------------------------------------------------------------------------- *)
(* Image and Bijection (from examples/algebra)                               *)
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
val INJ_IMAGE_BIJ_ALT = store_thm(
  "INJ_IMAGE_BIJ_ALT",
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
val BIJ_THM = store_thm(
  "BIJ_THM",
  ``!f s t. BIJ f s t <=> (!x. x IN s ==> f x IN t) /\ (!y. y IN t ==> ?!x. x IN s /\ (f x = y))``,
  rw_tac std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >> metis_tac[]);

(* Theorem: BIJ f s t ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y) *)
(* Proof: by BIJ_DEF, INJ_DEF *)
Theorem BIJ_IS_INJ:
  !f s t. BIJ f s t ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)
Proof
  rw[BIJ_DEF, INJ_DEF]
QED

(* Theorem: BIJ f s t ==> !x. x IN t ==> ?y. y IN s /\ f y = x *)
(* Proof: by BIJ_DEF, SURJ_DEF. *)
Theorem BIJ_IS_SURJ:
  !f s t. BIJ f s t ==> !x. x IN t ==> ?y. y IN s /\ f y = x
Proof
  simp[BIJ_DEF, SURJ_DEF]
QED

(* Can remove in helperSet: FINITE_BIJ_PROPERTY
|- !f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ CARD s = CARD t
pred_setTheory.FINITE_BIJ
|- !f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ CARD s = CARD t
*)

(* Idea: improve FINITE_BIJ with iff of finiteness of s and t. *)

(* Theorem: BIJ f s t ==> (FINITE s <=> FINITE t) *)
(* Proof:
   If part: FINITE s ==> FINITE t
      This is true                 by FINITE_BIJ
   Only-if part: FINITE t ==> FINITE s
      Note BIJ (LINV f s) t s      by BIJ_LINV_BIJ
      Thus FINITE s                by FINITE_BIJ
*)
Theorem BIJ_FINITE_IFF:
  !f s t. BIJ f s t ==> (FINITE s <=> FINITE t)
Proof
  metis_tac[FINITE_BIJ, BIJ_LINV_BIJ]
QED

(* Theorem: INJ f s s /\ x IN s /\ y IN s ==> ((f x = f y) <=> (x = y)) *)
(* Proof: by INJ_DEF *)
Theorem INJ_EQ_11:
  !f s x y. INJ f s s /\ x IN s /\ y IN s ==> ((f x = f y) <=> (x = y))
Proof
  metis_tac[INJ_DEF]
QED

(* Theorem: INJ f univ(:'a) univ(:'b) ==> !x y. f x = f y <=> x = y *)
(* Proof: by INJ_DEF, IN_UNIV. *)
Theorem INJ_IMP_11:
  !f. INJ f univ(:'a) univ(:'b) ==> !x y. f x = f y <=> x = y
Proof
  metis_tac[INJ_DEF, IN_UNIV]
QED
(* This is better than INJ_EQ_11 above. *)

(* Theorem: BIJ I s s *)
(* Proof: by definitions. *)
val BIJ_I_SAME = store_thm(
  "BIJ_I_SAME",
  ``!s. BIJ I s s``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF]);

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
Theorem IMAGE_DIFF:
  !s t f. s SUBSET t /\ INJ f t UNIV ==> (IMAGE f (t DIFF s) = (IMAGE f t) DIFF (IMAGE f s))
Proof
  rw[SUBSET_DEF, INJ_DEF, EXTENSION] >>
  metis_tac[]
QED

val _ = export_theory()
