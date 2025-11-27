(*===========================================================================*)
(* Theory of Moore-Smith convergence nets, and special cases like sequences  *)
(*===========================================================================*)

(*
Theory nets
Ancestors
  pred_set pair arithmetic num prim_rec relation real topology
  metric
Libs
  numLib reduceLib pairLib mesonLib RealArith hurdUtils jrhUtils
  tautLib newtypeTools set_relation[qualified]
 *)
open HolKernel Parse boolLib bossLib;

open numLib reduceLib pairLib pred_setTheory mesonLib RealArith hurdUtils
     pairTheory arithmeticTheory numTheory prim_recTheory relationTheory
     jrhUtils realTheory topologyTheory metricTheory tautLib newtypeTools;

local open set_relationTheory in end;

val _ = new_theory "nets";

val _ = Parse.reveal "B";

val num_EQ_CONV = Arithconv.NEQ_CONV;
val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

(*---------------------------------------------------------------------------*)
(* Basic definitions: directed order, net, bounded net, pointwise limit [1]  *)
(*---------------------------------------------------------------------------*)

(* NOTE: According to [1], the property ‘!w. g w z ==> g w x /\ g w y’ is called
  "composition property".
 *)
Definition dorder :
   dorder (g:'a->'a->bool) =
     !x y. g x x /\ g y y ==> ?z. g z z /\ (!w. g w z ==> g w x /\ g w y)
End

val _ = set_fixity "tends" (Infixr 750);

(* A general function (s :'b -> 'a) tends to l (w.r.t. top and g) if for all
   neigh N of l, "eventually" g(m) IN N.
 *)
Definition tends :
   (s tends l) (top,g) =
      !N:'a->bool. neigh(top)(N,l) ==>
            ?n:'b. g n n /\ !m:'b. g m n ==> N(s m)
End

Definition bounded :
   bounded(m:('a)metric,(g:'b->'b->bool)) f =
      ?k x N. g N N /\ (!n. g n N ==> (dist m)(f(n),x) < k)
End

(* ‘tendsto (m,x)’ is a dorder defined on a metric. See also DORDER_TENDSTO.

   NOTE: The net ‘at’ is defined by ‘tendsto’.
 *)
Definition tendsto :
   tendsto(m:('a)metric,x) y z =
      (&0 < (dist m)(x,y) /\ (dist m)(x,y) <= (dist m)(x,z))
End

Theorem DORDER_LEMMA:
   !g:'a->'a->bool.
      dorder g ==>
        !P Q. (?n. g n n /\ (!m. g m n ==> P m)) /\
              (?n. g n n /\ (!m. g m n ==> Q m))
                  ==> (?n. g n n /\ (!m. g m n ==> P m /\ Q m))
Proof
  GEN_TAC THEN REWRITE_TAC[dorder] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN “N1:'a” STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN “N2:'a” STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [“N1:'a”, “N2:'a”]) THEN
  REWRITE_TAC[ASSUME “(g:'a->'a->bool) N1 N1”,ASSUME “(g:'a->'a->bool) N2 N2”] THEN
  DISCH_THEN(X_CHOOSE_THEN “n:'a” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “n:'a” THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “m:'a” THEN DISCH_TAC THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o
    assert(is_conj o snd o dest_imp o snd o dest_forall) o concl) THEN
  DISCH_THEN(MP_TAC o SPEC “m:'a”) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* Following tactic is useful in the following proofs                        *)
(*---------------------------------------------------------------------------*)

fun DORDER_THEN tac th =
  let val findpr = snd o dest_imp o body o rand o rand o body o rand
      val (t1,t2) = case map (rand o rand o body o rand)
            (strip_conj (concl th)) of
          [t1, t2] => (t1, t2)
        | _ => raise Match
      val dog = (rator o rator o rand o rator o body) t1
      val thl = map ((uncurry X_BETA_CONV) o (I ## rand) o dest_abs) [t1,t2]
      val th1 = CONV_RULE(EXACT_CONV thl) th
      val th2 = MATCH_MP DORDER_LEMMA (ASSUME “dorder ^dog”)
      val th3 = MATCH_MP th2 th1
      val th4 = CONV_RULE(EXACT_CONV(map SYM thl)) th3 in
      tac th4 end;

(*---------------------------------------------------------------------------*)
(* Show that sequences and pointwise limits in a metric space are directed   *)
(*---------------------------------------------------------------------------*)

Theorem DORDER_NGE:
   dorder ($>= :num->num->bool)
Proof
  REWRITE_TAC[dorder, GREATER_EQ, LESS_EQ_REFL] THEN
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(SPECL [“x:num”, “y:num”] LESS_EQ_CASES) THENL
    [EXISTS_TAC “y:num”, EXISTS_TAC “x:num”] THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LESS_EQ_TRANS THENL
    [EXISTS_TAC “y:num”, EXISTS_TAC “x:num”] THEN
  ASM_REWRITE_TAC[]
QED

Theorem DORDER_TENDSTO:
   !m:('a)metric. !x. dorder(tendsto(m,x))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[dorder, tendsto] THEN
  MAP_EVERY X_GEN_TAC [“u:'a”, “v:'a”] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC(SPECL [“(dist m)(x:'a,v)”, “(dist m)(x:'a,u)”] REAL_LE_TOTAL)
  THENL [EXISTS_TAC “v:'a”, EXISTS_TAC “u:'a”] THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN FIRST_ASSUM
    (fn th => (EXISTS_TAC o rand o concl) th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
QED

(*---------------------------------------------------------------------------*)
(* Simpler characterization of limit in a metric topology                    *)
(*---------------------------------------------------------------------------*)

Theorem MTOP_TENDS :
  !d g. !x:'b->'a. !x0. (x tends x0)(mtop(d),g) <=>
     !e. &0 < e ==> ?n. g n n /\ !m. g m n ==> dist(d)(x(m),x0) < e
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[tends] THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC “B(d)(x0:'a,e)”) THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (rand o rator) o snd) THENL
     [MATCH_MP_TAC BALL_NEIGH THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN REWRITE_TAC[ball] THEN
    BETA_TAC THEN
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [METRIC_SYM] THEN REWRITE_TAC[],
    GEN_TAC THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN “P:'a->bool” STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC “open_in(mtop(d)) (P:'a->bool)” THEN
    REWRITE_TAC[MTOP_OPEN] THEN DISCH_THEN(MP_TAC o SPEC “x0:'a”) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC “d:real”) THEN
    REWRITE_TAC[ASSUME “&0 < d”] THEN
    DISCH_THEN(X_CHOOSE_THEN “n:'b” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “n:'b” THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC “(P:'a->bool) SUBSET N” THEN
    REWRITE_TAC[SUBSET_applied] THEN DISCH_TAC THEN
    REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
    ONCE_REWRITE_TAC[METRIC_SYM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]
QED

(*---------------------------------------------------------------------------*)
(* Prove that a net in a metric topology cannot converge to different limits *)
(*---------------------------------------------------------------------------*)

Theorem MTOP_TENDS_UNIQ :
    !g d. dorder (g:'b->'b->bool) ==>
          (x tends x0)(mtop(d),g) /\ (x tends x1)(mtop(d),g) ==> (x0:'a = x1)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MTOP_TENDS] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  REWRITE_TAC[TAUT ‘(a ==> b) /\ (a ==> c) <=> a ==> b /\ c’] THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
  CONV_TAC NOT_FORALL_CONV THEN
  EXISTS_TAC “dist(d:('a)metric)(x0,x1) / &2” THEN
  W(C SUBGOAL_THEN ASSUME_TAC o rand o rator o rand o snd) THENL
   [REWRITE_TAC[REAL_LT_HALF1] THEN MATCH_MP_TAC METRIC_NZ THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'b” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC “N:'b”) THEN ASM_REWRITE_TAC[] THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
  REWRITE_TAC[REAL_HALF_DOUBLE, REAL_NOT_LT] THEN
  GEN_REWR_TAC(RAND_CONV o LAND_CONV) [METRIC_SYM] THEN
  MATCH_ACCEPT_TAC METRIC_TRIANGLE
QED

(*---------------------------------------------------------------------------*)
(* Simpler characterization of limit of a sequence in a metric topology      *)
(*---------------------------------------------------------------------------*)

val geq = Term`$>= : num->num->bool`;

Theorem SEQ_TENDS:
   !d:('a)metric. !x x0. (x tends x0)(mtop(d), ^geq) =
     !e. &0 < e ==> ?N. !n. ^geq n N ==> dist(d)(x(n),x0) < e
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, GREATER_EQ, LESS_EQ_REFL]
QED

(*---------------------------------------------------------------------------*)
(* And of limit of function between metric spaces                            *)
(*---------------------------------------------------------------------------*)

Theorem LIM_TENDS:
   !m1:('a)metric. !m2:('b)metric. !f x0 y0.
      limpt(mtop m1) x0 UNIV ==>
        ((f tends y0)(mtop(m2),tendsto(m1,x0)) =
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (dist m1)(x,x0) /\ (dist m1)(x,x0) <= d ==>
              (dist m2)(f(x),y0) < e)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MTOP_TENDS, tendsto] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC “&0 < e” THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN “z:'a” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “(dist m1)(x0:'a,z)” THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(ISPECL [“m1:('a)metric”, “x0:'a”, “x:'a”] METRIC_SYM) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC “limpt(mtop m1) (x0:'a) UNIV” THEN
    REWRITE_TAC[MTOP_LIMPT] THEN
    DISCH_THEN(MP_TAC o SPEC “d:real”) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIV_DEF] THEN
    DISCH_THEN(X_CHOOSE_THEN “y:'a” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “y:'a” THEN CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_NZ THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    X_GEN_TAC “x:'a” THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[METRIC_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “(dist m1)(x0:'a,y)” THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC]
QED

(*---------------------------------------------------------------------------*)
(* Similar, more conventional version, is also true at a limit point         *)
(*---------------------------------------------------------------------------*)

Theorem LIM_TENDS2:
   !m1:('a)metric. !m2:('b)metric. !f x0 y0.
      limpt(mtop m1) x0 UNIV ==>
        ((f tends y0)(mtop(m2),tendsto(m1,x0)) =
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (dist m1)(x,x0) /\ (dist m1)(x,x0) < d ==>
              (dist m2)(f(x),y0) < e)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP LIM_TENDS th]) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC “d:real” THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    EXISTS_TAC “d / &2” THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “d / &2” THEN ASM_REWRITE_TAC[REAL_LT_HALF2]]
QED

(*---------------------------------------------------------------------------*)
(* Simpler characterization of boundedness for the real line                 *)
(*---------------------------------------------------------------------------*)

Theorem MR1_BOUNDED:
   !(g:'a->'a->bool) f. bounded(mr1,g) f =
        ?k N. g N N /\ (!n. g n N ==> abs(f n) < k)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[bounded, MR1_DEF] THEN
  (CONV_TAC o LAND_CONV o RAND_CONV o ABS_CONV) SWAP_EXISTS_CONV
  THEN CONV_TAC(ONCE_DEPTH_CONV SWAP_EXISTS_CONV) THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  CONV_TAC(REDEPTH_CONV EXISTS_AND_CONV) THEN
  AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN “k:real” MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_TAC “x:real”) THEN
    EXISTS_TAC “abs(x) + k” THEN GEN_TAC THEN DISCH_TAC THEN
    SUBST1_TAC
      (SYM(SPECL [“(f:'a->real) n”, “x:real”] REAL_SUB_ADD)) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “abs((f:'a->real) n - x) + abs(x)” THEN
    REWRITE_TAC[ABS_TRIANGLE] THEN
    GEN_REWR_TAC RAND_CONV  [REAL_ADD_SYM] THEN
    REWRITE_TAC[REAL_LT_RADD] THEN
    ONCE_REWRITE_TAC[ABS_SUB] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [“k:real”, “&0”] THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG]]
QED

(*---------------------------------------------------------------------------*)
(* Firstly, prove useful forms of null and bounded nets                      *)
(*---------------------------------------------------------------------------*)

Theorem NET_NULL:
   !g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) = ((\n. x(n) - x0) tends &0)(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS] THEN BETA_TAC THEN
  REWRITE_TAC[MR1_DEF, REAL_SUB_LZERO] THEN EQUAL_TAC THEN
  REWRITE_TAC[REAL_NEG_SUB]
QED

Theorem NET_CONV_BOUNDED:
   !g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) ==> bounded(mr1,g) x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, bounded] THEN
  DISCH_THEN(MP_TAC o SPEC “&1”) THEN
  REWRITE_TAC[REAL_LT, ONE, LESS_0] THEN
  REWRITE_TAC[GSYM(ONE)] THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [“&1”, “x0:real”, “N:'a”] THEN
  ASM_REWRITE_TAC[]
QED

Theorem NET_CONV_NZ:
   !g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        ?N. g N N /\ (!n. g n N ==> ~(x n = &0))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, bounded] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC “abs(x0)”) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MR1_DEF, REAL_SUB_RZERO, REAL_LT_REFL]
QED

Theorem NET_CONV_IBOUNDED:
   !g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        bounded(mr1,g) (\n. inv(x n))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, MR1_BOUNDED, MR1_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[ABS_NZ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC “abs(x0) / &2”) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [“&2 / abs(x0)”, “N:'a”] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC “n:'a” THEN
  DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN “(abs(x0) / & 2) < abs(x(n:'a))” ASSUME_TAC THENL
   [SUBST1_TAC(SYM(SPECL [“abs(x0) / &2”, “abs(x0) / &2”, “abs(x(n:'a))”]
      REAL_LT_LADD)) THEN
    REWRITE_TAC[REAL_HALF_DOUBLE] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “abs(x0 - x(n:'a)) + abs(x(n))” THEN
    ASM_REWRITE_TAC[REAL_LT_RADD] THEN
    SUBST1_TAC(SYM(AP_TERM “abs”
      (SPECL [“x0:real”, “x(n:'a):real”] REAL_SUB_ADD))) THEN
    MATCH_ACCEPT_TAC ABS_TRIANGLE, ALL_TAC] THEN
  SUBGOAL_THEN “&0 < abs(x(n:'a))” ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC “abs(x0) / &2” THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1], ALL_TAC] THEN
  SUBGOAL_THEN “&2 / abs(x0) = inv(abs(x0) / &2)” SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_RINV_UNIQ THEN REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
        “(a * b) * (c * d) = (d * a) * (b * c)”] THEN
    SUBGOAL_THEN “~(abs(x0) = &0) /\ ~(&2 = &0)”
      (fn th => CONJUNCTS_THEN(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) th
            THEN REWRITE_TAC[REAL_MUL_LID]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[ABS_NZ, ABS_ABS],
      REWRITE_TAC[REAL_INJ] THEN CONV_TAC(RAND_CONV num_EQ_CONV) THEN
      REWRITE_TAC[]], ALL_TAC] THEN
  SUBGOAL_THEN “~(x(n:'a) = &0)” (SUBST1_TAC o MATCH_MP ABS_INV) THENL
   [ASM_REWRITE_TAC[ABS_NZ], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[REAL_LT_HALF1]
QED

(*---------------------------------------------------------------------------*)
(* Now combining theorems for null nets                                      *)
(*---------------------------------------------------------------------------*)

Theorem NET_NULL_ADD:
   !g:'a->'a->bool. dorder g ==>
        !x y. (x tends &0)(mtop(mr1),g) /\ (y tends &0)(mtop(mr1),g) ==>
                ((\n. x(n) + y(n)) tends &0)(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC “e:real” THEN DISCH_TAC) o
    MP_TAC o end_itlist CONJ o map (SPEC “e / &2”) o CONJUNCTS) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(DORDER_THEN (X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC “abs(x(m:'a)) + abs(y(m:'a))” THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN RULE_ASSUM_TAC BETA_RULE THEN
  GEN_REWR_TAC RAND_CONV [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]
QED

Theorem NET_NULL_MUL:
   !g:'a->'a->bool. dorder g ==>
      !x y. bounded(mr1,g) x /\ (y tends &0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) tends &0)(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_BOUNDED] THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC “e:real” THEN DISCH_TAC) o MP_TAC) THEN
  CONV_TAC(LAND_CONV LEFT_AND_EXISTS_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN “k:real” MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o uncurry CONJ o (I ## SPEC “e / k”) o CONJ_PAIR) THEN
  SUBGOAL_THEN “&0 < k” ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN “N:'a”
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPEC “N:'a”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “abs(x(N:'a))” THEN ASM_REWRITE_TAC[ABS_POS], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  SUBGOAL_THEN “&0 < e / k” ASSUME_TAC THENL
   [FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_LT_RDIV_0 th] THEN
    ASM_REWRITE_TAC[] THEN NO_TAC), ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DORDER_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN (ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN “e = k * (e / k)” SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC “&0 < &0” THEN
    REWRITE_TAC[REAL_LT_REFL], ALL_TAC] THEN BETA_TAC THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
  ASM_REWRITE_TAC[ABS_POS]
QED

Theorem NET_NULL_CMUL:
   !g:'a->'a->bool. !k x.
      (x tends &0)(mtop(mr1),g) ==> ((\n. k * x(n)) tends &0)(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, MR1_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC “e:real” THEN DISCH_TAC) o MP_TAC) THEN
  ASM_CASES_TAC “k = &0” THENL
   [DISCH_THEN(MP_TAC o SPEC “&1”) THEN
    REWRITE_TAC[REAL_LT, ONE, LESS_SUC_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “N:'a” THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO, abs, REAL_LE_REFL],
    DISCH_THEN(MP_TAC o SPEC “e / abs(k)”) THEN
    SUBGOAL_THEN “&0 < e / abs(k)” ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_POS THEN
      ASM_REWRITE_TAC[GSYM ABS_NZ], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN “e = abs(k) * (e / abs(k))” SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
      ASM_REWRITE_TAC[ABS_ZERO], ALL_TAC] THEN
    REWRITE_TAC[ABS_MUL] THEN
    SUBGOAL_THEN “&0 < abs k” (fn th => REWRITE_TAC[MATCH_MP REAL_LT_LMUL th])
    THEN ASM_REWRITE_TAC[GSYM ABS_NZ]]
QED

(*---------------------------------------------------------------------------*)
(* Now real arithmetic theorems for convergent nets                          *)
(*---------------------------------------------------------------------------*)

Theorem NET_ADD:
   !g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\ (y tends y0)(mtop(mr1),g) ==>
                      ((\n. x(n) + y(n)) tends (x0 + y0))(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[NET_NULL] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th o MATCH_MP NET_NULL_ADD))
  THEN MATCH_MP_TAC(TAUT ‘(a = b) ==> a ==> b’) THEN EQUAL_TAC THEN
  BETA_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM))
QED

Theorem NET_NEG:
   !g:'a->'a->bool. dorder g ==>
        (!x x0. (x tends x0)(mtop(mr1),g) =
                  ((\n. ~(x n)) tends ~x0)(mtop(mr1),g))
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_NEG2] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB]
  THEN REFL_TAC
QED

Theorem NET_SUB:
   !g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\ (y tends y0)(mtop(mr1),g) ==>
                      ((\n. x(n) - y(n)) tends (x0 - y0))(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_sub] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “n:'a” “-(y (n:'a))”]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fn th => ONCE_REWRITE_TAC[GSYM(MATCH_MP NET_NEG th)]) THEN
  ASM_REWRITE_TAC[]
QED

Theorem NET_MUL:
   !g:'a->'a->bool. dorder g ==>
        !x y x0 y0. (x tends x0)(mtop(mr1),g) /\ (y tends y0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) tends (x0 * y0))(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[NET_NULL] THEN
  DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN “!a b c d. (a * b) - (c * d) =
                             (a * (b - d)) + ((a - c) * d)”
  (fn th => ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[real_sub, REAL_LDISTRIB, REAL_RDISTRIB, GSYM REAL_ADD_ASSOC]
    THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “n:'a” “x(n:'a) * (y(n) - y0)”]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “n:'a” “(x(n:'a) - x0) * y0”]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_NULL_ADD) THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  (CONV_TAC o EXACT_CONV o map (X_BETA_CONV “n:'a”))
   [“y(n:'a) - y0”, “x(n:'a) - x0”] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_NULL_MUL) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NET_CONV_BOUNDED THEN
    EXISTS_TAC “x0:real” THEN ONCE_REWRITE_TAC[NET_NULL] THEN
    ASM_REWRITE_TAC[],
    MATCH_MP_TAC NET_NULL_CMUL THEN ASM_REWRITE_TAC[]]
QED

Theorem NET_INV:
   !g:'a->'a->bool. dorder g ==>
        !x x0. (x tends x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
                   ((\n. inv(x(n))) tends inv x0)(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => STRIP_ASSUME_TAC th THEN
    MP_TAC(CONJ (MATCH_MP NET_CONV_IBOUNDED th)
                    (MATCH_MP NET_CONV_NZ th))) THEN
  REWRITE_TAC[MR1_BOUNDED] THEN
  CONV_TAC(ONCE_DEPTH_CONV LEFT_AND_EXISTS_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN “k:real” MP_TAC) THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o C CONJ(ASSUME “(x tends x0)(mtop mr1,(g:'a->'a->bool))”)) THEN
  ONCE_REWRITE_TAC[NET_NULL] THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN BETA_TAC
  THEN DISCH_THEN(curry op THEN (X_GEN_TAC “e:real” THEN DISCH_TAC) o MP_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV RIGHT_AND_FORALL_CONV) THEN
  DISCH_THEN(ASSUME_TAC o SPEC “e * (abs(x0) * (inv k))”) THEN
  SUBGOAL_THEN “&0 < k” ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(X_CHOOSE_THEN “N:'a” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPEC “N:'a”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “abs(inv(x(N:'a)))” THEN
    ASM_REWRITE_TAC[ABS_POS], ALL_TAC] THEN
  SUBGOAL_THEN “&0 < e * (abs(x0) * inv k)” ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
    MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” (CONJUNCTS_THEN ASSUME_TAC)) THEN
  EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “n:'a” THEN DISCH_THEN(ANTE_RES_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC BETA_RULE THEN POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN “inv(x n) - inv x0 =
                inv(x n) * (inv x0 * (x0 - x(n:'a)))” SUBST1_TAC THENL
   [REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME “~(x0 = &0)”)] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN REPEAT AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_RINV (ASSUME “~(x(n:'a) = &0)”)] THEN
    REWRITE_TAC[REAL_MUL_RID], ALL_TAC] THEN
  REWRITE_TAC[ABS_MUL] THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  SUBGOAL_THEN “e = e * ((abs(inv x0) * abs(x0)) * (inv k * k))”
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM ABS_MUL] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME “~(x0 = &0)”)] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV
      (GSYM(MATCH_MP REAL_LT_IMP_NE (ASSUME “&0 < k”)))] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    REWRITE_TAC[abs, REAL_LE, LESS_OR_EQ, ONE, LESS_SUC_REFL] THEN
    REWRITE_TAC[SYM ONE, REAL_MUL_RID], ALL_TAC] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    “a * ((b * c) * (d * e)) = e * (b * (a * (c * d)))”] THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  MATCH_MP_TAC ABS_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ABS_MUL] THEN SUBGOAL_THEN “&0 < abs(inv x0)”
    (fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LT_LMUL th]) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  MATCH_MP_TAC REAL_INV_NZ THEN ASM_REWRITE_TAC[]
QED

Theorem NET_DIV:
   !g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\
                  (y tends y0)(mtop(mr1),g) /\ ~(y0 = &0) ==>
                      ((\n. x(n) / y(n)) tends (x0 / y0))(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “n:'a” “inv(y(n:'a))”]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_INV) THEN
  ASM_REWRITE_TAC[]
QED

Theorem NET_ABS:
   !g x x0. (x tends x0)(mtop(mr1),g) ==>
               ((\n:'a. abs(x n)) tends abs(x0))(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS] THEN
  DISCH_TAC THEN X_GEN_TAC “e:real” THEN
  DISCH_THEN(fn th => POP_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “n:'a” THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC “dist(mr1)(x(n:'a),x0)” THEN CONJ_TAC THENL
   [REWRITE_TAC[MR1_DEF, ABS_SUB_ABS],
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]
QED

(*---------------------------------------------------------------------------*)
(* Comparison between limits                                                 *)
(*---------------------------------------------------------------------------*)

Theorem NET_LE:
   !g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\
                  (y tends y0)(mtop(mr1),g) /\
                  (?N. g N N /\ !n. g n N ==> x(n) <= y(n))
                        ==> x0 <= y0
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWR_TAC I [TAUT ‘a = ~~a:bool’] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[MTOP_TENDS] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o
    map (SPEC “(x0 - y0) / &2”) o CONJUNCTS) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_exists o concl) THEN
  DISCH_THEN(fn th1 => DISCH_THEN (fn th2 => MP_TAC(CONJ th1 th2))) THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o SPEC “N:'a”) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MR1_DEF] THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC ABS_BETWEEN2 THEN
  MAP_EVERY EXISTS_TAC [“y0:real”, “x0:real”] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM ACCEPT_TAC
QED

(* ------------------------------------------------------------------------- *)
(*  Net As Type                                                              *)
(* ------------------------------------------------------------------------- *)

(* old definition *)
Definition isnet :
   isnet g <=> !x y. (!z. g z x ==> g z y) \/ (!z. g z y ==> g z x)
End

val net_tydef = new_type_definition
 ("net",
  prove (``?(g:'a->'a->bool). isnet g``,
        EXISTS_TAC ``\x:'a y:'a. F`` THEN REWRITE_TAC[isnet]));

val net_ty_bij = define_new_type_bijections
    {name="net_tybij",
     ABS="mk_net", REP="netord",tyax=net_tydef};

Theorem net_tybij[allow_rebind]:
  (!a. mk_net (netord a) = a) /\
  (!r. (!x y. (!z. r z x ==> r z y) \/ (!z. r z y ==> r z x)) <=>
       (netord (mk_net r) = r))
Proof
  SIMP_TAC std_ss [net_ty_bij, GSYM isnet]
QED

Theorem NET :
   !n x y. (!z. netord n z x ==> netord n z y) \/
           (!z. netord n z y ==> netord n z x)
Proof
   REWRITE_TAC[net_tybij, ETA_AX]
QED

Theorem OLDNET :
    !n x y. netord n x x /\ netord n y y
           ==> ?z. netord n z z /\
                   !w. netord n w z ==> netord n w x /\ netord n w y
Proof
  MESON_TAC[NET]
QED

Theorem NET_DILEMMA :
   !net. (?a. (?x. netord net x a) /\ (!x. netord net x a ==> P x)) /\
         (?b. (?x. netord net x b) /\ (!x. netord net x b ==> Q x))
     ==> ?c. (?x. netord net x c) /\ (!x. netord net x c ==> P x /\ Q x)
Proof
  MESON_TAC[NET]
QED

(* NOTE: It seems that purpose of “g x x” in dorder for “at a”, is to make
   sure ‘x <> a’, or 0 < mdist m (x,a).
 *)
Theorem DORDER_NET :
    !net. dorder (netord net)
Proof
    RW_TAC std_ss [dorder, OLDNET]
QED

(* ------------------------------------------------------------------------- *)
(* Common nets and the "within" modifier for nets.                           *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "within" (Infix(NONASSOC, 450));
val _ = set_fixity "in_direction" (Infix(NONASSOC, 450));

(* HOL-Light: (atpointof top a) = mk_net({u | open_in top u /\ a IN u},{a})

   NOTE: HOL-Light's “atpointof” takes a (general) topology, while here HOL4
   takes a metric (therefore only works for metrizable topology).
 *)
Definition atpointof_def[nocompute]:
    atpointof m a = mk_net (tendsto (m,a))
End

(* HOL-Light: at a = atpointof euclidean a *)
Definition at_DEF :
    at z = atpointof mr1 z
End

(* The previous "definition" now (again) becomes a theorem. *)
Theorem at_def :
    !z. at z = mk_net (tendsto (mr1,z))
Proof
    RW_TAC std_ss [at_DEF, atpointof_def]
QED

Theorem atpointof :
    !m a. atpointof m a =
          mk_net (\x y. 0 < mdist m (x,a) /\ mdist m (x,a) <= mdist m (y,a))
Proof
    RW_TAC std_ss [atpointof_def]
 >> AP_TERM_TAC
 >> RW_TAC std_ss [FUN_EQ_THM, tendsto]
 >> PROVE_TAC [METRIC_SYM]
QED

(* |- !a. at a = mk_net (\x y. 0 < dist (x,a) /\ dist (x,a) <= dist (y,a)) *)
Theorem at = atpointof |> ISPEC “mr1”
                       |> REWRITE_RULE [GSYM at_DEF, GSYM dist_def]

(* HOL-Light: at_infinity = mk_net({{x | b <= norm x} | b IN (:real)},{}) *)
Definition at_infinity[nocompute]:
  at_infinity = mk_net(\x y. abs(x) >= abs(y))
End

(* HOL-Light: at_posinfinity = mk_net({{x | a <= x} | a IN (:real)},{}) *)
Definition at_posinfinity[nocompute]:
  at_posinfinity = mk_net(\x y:real. x >= y)
End

(* HOL-Light: at_neginfinity = mk_net({{x | x <= a} | a IN (:real)},{}) *)
Definition at_neginfinity[nocompute]:
  at_neginfinity = mk_net(\x y:real. x <= y)
End

(* HOL-Light: sequentially = mk_net({from n | n IN (:num)},{}) *)
Definition sequentially[nocompute]:
  sequentially = mk_net(\m:num n. m >= n)
End

(* NOTE: “within” only requires “x IN s” (next step) but not for “y” *)
Definition within[nocompute]:
  (net within s) = mk_net(\x y. netord net x y /\ x IN s)
End

Definition in_direction[nocompute]:
  (a in_direction v) = ((at a) within {b | ?c. &0 <= c /\ (b - a = c * v)})
End

(* ------------------------------------------------------------------------- *)
(* Prove that they are all nets.                                             *)
(* ------------------------------------------------------------------------- *)

fun NET_PROVE_TAC [def] =
  SIMP_TAC std_ss [GSYM FUN_EQ_THM, def] THEN
  REWRITE_TAC [ETA_AX] THEN
  ASM_SIMP_TAC std_ss [GSYM(CONJUNCT2 net_tybij)];

(* NOTE: Most of the time, user only need to use this theorem instead of the
   definition(s) of “atpointof”.
 *)
Theorem ATPOINTOF :
   !m a x y.
      netord(atpointof m a) x y <=>
      0 < mdist m (x,a) /\ mdist m (x,a) <= mdist m (y,a)
Proof
  NTAC 2 GEN_TAC THEN NET_PROVE_TAC[atpointof] THEN
  METIS_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS, REAL_LET_TRANS]
QED

(* |- !a x y.
        netord (at a) x y <=> 0 < dist (x,a) /\ dist (x,a) <= dist (y,a)
 *)
Theorem AT = ATPOINTOF |> ISPEC “mr1”
                       |> REWRITE_RULE [GSYM at_DEF, GSYM dist_def]

Theorem tendsto_alt_atpointof :
    !m a. tendsto (m,a) = netord (atpointof m a)
Proof
    rw [FUN_EQ_THM, tendsto, ATPOINTOF]
 >> METIS_TAC [MDIST_SYM]
QED

(* Connection between HOL4's “tendsto” and HOL-Light's “at”, cf. [at_def]

   |- !a. tendsto (mr1,a) = netord (at a)
 *)
Theorem tendsto_mr1 = tendsto_alt_atpointof |> ISPEC “mr1”
                                            |> REWRITE_RULE [GSYM at_DEF]

Theorem AT_INFINITY:
   !x y. netord at_infinity x y <=> abs(x) >= abs(y)
Proof
  NET_PROVE_TAC[at_infinity] THEN
  REWRITE_TAC[real_ge, REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS]
QED

Theorem AT_POSINFINITY:
   !x y. netord at_posinfinity x y <=> x >= y
Proof
  NET_PROVE_TAC[at_posinfinity] THEN
  REWRITE_TAC[real_ge, REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS]
QED

Theorem AT_NEGINFINITY:
   !x y. netord at_neginfinity x y <=> x <= y
Proof
  NET_PROVE_TAC[at_neginfinity] THEN
  REWRITE_TAC[real_ge, REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS]
QED

Theorem SEQUENTIALLY:
   !m n. netord sequentially m n <=> m >= n
Proof
  NET_PROVE_TAC[sequentially] THEN REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN
  MESON_TAC[LESS_EQ_CASES, LESS_EQ_REFL, LESS_EQ_TRANS]
QED

Theorem WITHIN:
   !n s x y. netord(n within s) x y <=> netord n x y /\ x IN s
Proof
  GEN_TAC THEN GEN_TAC THEN SIMP_TAC std_ss [within, GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 net_tybij), ETA_AX] THEN
  METIS_TAC[NET]
QED

Theorem IN_DIRECTION:
   !a v x y. netord(a in_direction v) x y <=>
                &0 < dist(x,a) /\ dist(x,a) <= dist(y,a) /\
                 ?c. &0 <= c /\ (x - a = c * v)
Proof
  SIMP_TAC std_ss [WITHIN, AT, in_direction, GSPECIFICATION] THEN METIS_TAC []
QED

Theorem NET_WITHIN_UNIV :
    !net. (net within UNIV) = net
Proof
    rw [within]
 >> ‘(\x y. netord net x y) = netord net’ by rw [FUN_EQ_THM]
 >> simp [net_tybij]
QED

Theorem WITHIN_UNIV :
    !x. (at x within UNIV) = at x
Proof
    REWRITE_TAC [NET_WITHIN_UNIV]
QED

Theorem WITHIN_WITHIN:
   !net s t. ((net within s) within t) = (net within (s INTER t))
Proof
  ONCE_REWRITE_TAC[within] THEN
  REWRITE_TAC[WITHIN, IN_INTER, GSYM CONJ_ASSOC]
QED

(* ------------------------------------------------------------------------- *)
(* netfilter (compatible with HOL-Light)                                     *)
(* ------------------------------------------------------------------------- *)

Definition netfilter_def :
    netfilter net = {{y | netord net y x} | x | T}
End

Theorem NETFILTER_AT_POSINFINITY :
    netfilter at_posinfinity = {{x | a <= x} | a IN univ(:real)}
Proof
    simp [netfilter_def, AT_POSINFINITY, real_ge]
QED

Theorem NETFILTER_AT_NEGINFINITY :
    netfilter at_neginfinity = {{x | x <= a} | a IN univ(:real)}
Proof
    simp [netfilter_def, AT_NEGINFINITY]
QED

Theorem NETFILTER_AT_INFINITY :
    netfilter at_infinity = {{x | b <= abs x} | b IN univ(:real)}
Proof
    simp [netfilter_def, AT_INFINITY, real_ge]
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘abs x'’ >> REFL_TAC)
 >> Cases_on ‘0 <= b’
 >- (Q.EXISTS_TAC ‘abs b’ >> simp [ABS_REDUCE])
 >> fs [REAL_NOT_LE]
 >> Know ‘!x. b <= abs x <=> 0 <= abs x’
 >- (Q.X_GEN_TAC ‘x’ \\
     EQ_TAC >> rw [] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘0’ >> simp [ABS_POS, REAL_LT_IMP_LE])
 >> Rewr'
 >> Q.EXISTS_TAC ‘0’ >> simp [ABS_0]
QED

Theorem NETFILTER_SEQUENTIALLY :
    netfilter sequentially = {from n | n IN univ(:num)}
Proof
    simp [netfilter_def, SEQUENTIALLY, GREATER_EQ, from_def]
QED

Theorem NETFILTER_ATPOINTOF :
    !m a. netfilter (atpointof m a) =
            {{y | y <> a /\ dist m (y,a) <= dist m (x,a)} | x | T}
Proof
    simp [netfilter_def, ATPOINTOF, MDIST_POS_EQ]
QED

(* !a. netfilter (at a) =
          {{y | y <> a /\ dist (y,a) <= dist (x,a)} | x | T}
 *)
Theorem NETFILTER_AT =
        NETFILTER_ATPOINTOF |> ISPEC “mr1”
                            |> REWRITE_RULE [GSYM dist_def, GSYM at_DEF]

(* ------------------------------------------------------------------------- *)
(* It's also sometimes useful to extract the limit point from the net.       *)
(* ------------------------------------------------------------------------- *)

Definition netlimit :
    netlimit net = @a. !x. ~(netord net x a)
End

Theorem NETLIMIT_ATPOINTOF :
    !m a. netlimit(atpointof m a) = a
Proof
    RW_TAC std_ss [netlimit, ATPOINTOF]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (Q.EXISTS_TAC ‘a’ \\
     rw [MDIST_REFL, REAL_NOT_LE])
 >> rw [REAL_NOT_LE, REAL_NOT_LT]
 >> CCONTR_TAC
 >> Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘x’)
 >> simp [REAL_NOT_LE]
 >> rw [REAL_LT_LE, METRIC_NZ]
QED

(* |- !a. netlimit (at a) = a *)
Theorem NETLIMIT_AT = NETLIMIT_ATPOINTOF |> ISPEC “mr1”
                   |> REWRITE_RULE [GSYM at_DEF]

(* NOTE: This is compatible with HOL-Light *)
Definition netlimits_def :
    netlimits net = if ?a. !x. ~(netord net x a) then {netlimit net} else {}
End

Theorem NETLIMITS_ATPOINTOF :
    !m a. netlimits (atpointof m a) = {a}
Proof
    rpt GEN_TAC
 >> qabbrev_tac ‘net = atpointof m a’
 >> Know ‘?a. !x. ~(netord net x a)’
 >- (Q.EXISTS_TAC ‘a’ \\
     rw [Abbr ‘net’, ATPOINTOF, MDIST_REFL, REAL_NOT_LE])
 >> DISCH_TAC
 >> simp [netlimits_def]
 >> simp [NETLIMIT_ATPOINTOF, Abbr ‘net’]
QED

(* |- !a. netlimits (at a) = {a} *)
Theorem NETLIMITS_AT = NETLIMITS_ATPOINTOF |> ISPEC “mr1”
                    |> REWRITE_RULE [GSYM at_DEF]

(* ------------------------------------------------------------------------- *)
(* Identify trivial limits, where we can't approach arbitrarily closely.     *)
(* ------------------------------------------------------------------------- *)

(* HOL-Light's definition of ‘trivial_limit’
   |- !net. trivial_limit net <=> eventually (\x. F) net
 *)
Definition trivial_limit :
    trivial_limit net <=>
      (!(a:'a) b. a = b) \/
      ?(a:'a) b. ~(a = b) /\ !x. ~(netord(net) x a) /\ ~(netord(net) x b)
End

Theorem NONTRIVIAL_LIMIT_WITHIN :
    !net s. trivial_limit net ==> trivial_limit(net within s)
Proof
    REWRITE_TAC[trivial_limit, WITHIN] THEN MESON_TAC[]
QED

Theorem REAL_CHOOSE_SIZE :
   !c. &0 <= c ==> (?x. abs x = c:real)
Proof
  METIS_TAC [ABS_REFL]
QED

Theorem TRIVIAL_LIMIT_AT_INFINITY :
    ~(trivial_limit at_infinity)
Proof
  REWRITE_TAC[trivial_limit, AT_INFINITY, real_ge] THEN
  MESON_TAC[REAL_LE_REFL, REAL_CHOOSE_SIZE, REAL_LT_01, REAL_LT_LE]
QED

Theorem TRIVIAL_LIMIT_AT_POSINFINITY :
    ~(trivial_limit at_posinfinity)
Proof
  REWRITE_TAC[trivial_limit, AT_POSINFINITY, DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [``&0:real``, ``&1:real``]) THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM, NOT_EXISTS_THM, real_ge, REAL_NOT_LE] THEN
  MESON_TAC[REAL_LT_TOTAL, REAL_LT_ANTISYM]
QED

Theorem TRIVIAL_LIMIT_AT_NEGINFINITY :
    ~(trivial_limit at_neginfinity)
Proof
  REWRITE_TAC[trivial_limit, AT_NEGINFINITY, DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [``&0:real``, ``&1:real``]) THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM, NOT_EXISTS_THM, real_ge, REAL_NOT_LE] THEN
  MESON_TAC[REAL_LT_TOTAL, REAL_LT_ANTISYM]
QED

Theorem TRIVIAL_LIMIT_SEQUENTIALLY :
    ~(trivial_limit sequentially)
Proof
  REWRITE_TAC[trivial_limit, SEQUENTIALLY] THEN
  MESON_TAC[GREATER_EQ, LESS_EQ_REFL, SUC_NOT]
QED

(* ------------------------------------------------------------------------- *)
(* Some property holds "sufficiently close" to the limit point.              *)
(* ------------------------------------------------------------------------- *)

(* cf. HOL-Light's definition of “eventually”:
let eventually = new_definition
 `eventually (P:A->bool) net <=>
        netfilter net = {} \/
        ?u. u IN netfilter net /\
            !x. x IN u DIFF netlimits net ==> P x`;;
 *)
Definition eventually :
    eventually p net <=>
      trivial_limit net \/
      ?y. (?x. netord net x y) /\ (!x. netord net x y ==> p x)
End

Theorem EVENTUALLY_FALSE :
    !net. eventually (\x. F) net <=> trivial_limit net
Proof
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

(* This is HOL-Light's definition of ‘trivial_limit’
   |- !net. trivial_limit net <=> eventually (\x. F) net
 *)
Theorem trivial_limit_def = GSYM EVENTUALLY_FALSE

Theorem EVENTUALLY_TRUE :
    !net. eventually (\x. T) net <=> T
Proof
  REWRITE_TAC[eventually, trivial_limit] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_HAPPENS :
    !net p. eventually p net ==> trivial_limit net \/ ?x. p x
Proof
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem NOT_EVENTUALLY :
    !net p. (!x. ~(p x)) /\ ~(trivial_limit net) ==> ~(eventually p net)
Proof
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem ALWAYS_EVENTUALLY :
    !net p. (!x. p x) ==> eventually p net
Proof
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[eventually, trivial_limit] THEN
  MESON_TAC[]
QED

Theorem EVENTUALLY_SEQUENTIALLY :
    !p. eventually p sequentially <=> ?N. !n. N <= n ==> p n
Proof
  REWRITE_TAC[eventually, SEQUENTIALLY, GREATER_EQ, LESS_EQ_REFL,
    TRIVIAL_LIMIT_SEQUENTIALLY] THEN  MESON_TAC[LESS_EQ_REFL]
QED

Theorem EVENTUALLY_AT_INFINITY :
    !p. eventually p at_infinity <=> ?b. !x. abs(x) >= b ==> p x
Proof
  SIMP_TAC std_ss [eventually, AT_INFINITY, TRIVIAL_LIMIT_AT_INFINITY] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[REAL_LE_REFL], ALL_TAC] THEN
  MESON_TAC[real_ge, REAL_LE_REFL, REAL_CHOOSE_SIZE,
    REAL_ARITH ``&0 <= b:real \/ (!x. x >= &0 ==> x >= b)``]
QED

Theorem EVENTUALLY_AT_POSINFINITY :
    !p. eventually p at_posinfinity <=> ?b. !x. x >= b ==> p x
Proof
  REWRITE_TAC[eventually, TRIVIAL_LIMIT_AT_POSINFINITY, AT_POSINFINITY] THEN
  MESON_TAC[REAL_ARITH ``x >= x``]
QED

Theorem EVENTUALLY_AT_NEGINFINITY :
    !p. eventually p at_neginfinity <=> ?b. !x. x <= b ==> p x
Proof
  REWRITE_TAC[eventually, TRIVIAL_LIMIT_AT_NEGINFINITY, AT_NEGINFINITY] THEN
  MESON_TAC[REAL_LE_REFL]
QED

Theorem EVENTUALLY_AT_INFINITY_POS :
    !p:real->bool.
        eventually p at_infinity <=> ?b. &0 < b /\ !x. abs x >= b ==> p x
Proof
  GEN_TAC THEN REWRITE_TAC[EVENTUALLY_AT_INFINITY, real_ge] THEN
  MESON_TAC[REAL_ARITH ``&0 < abs b + &1 /\ (abs b + &1 <= x ==> b <= x:real)``]
QED

(* NOTE: The other direction seems non-provable in HOL4...

let EVENTUALLY_WITHIN_IMP = prove
 (`!net (P:A->bool) s.
        eventually P (net within s) <=>
        eventually (\x. x IN s ==> P x) net`,
  REWRITE_TAC[eventually; WITHIN; RELATIVE_TO; EXISTS_IN_GSPEC] THEN
  REWRITE_TAC[INTERS_GSPEC; NETLIMITS_WITHIN] THEN SET_TAC[]);;
 *)
Theorem EVENTUALLY_WITHIN_IMP :
   !net (P:'a->bool) s.
         eventually P (net within s) <=>
         eventually (\x. x IN s ==> P x) net
Proof
    RW_TAC std_ss [eventually]
 >> EQ_TAC >> rpt STRIP_TAC (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      cheat,
      (* goal 2 (of 4) *)
      DISJ2_TAC (* provable *) \\
      fs [WITHIN] \\
      Q.EXISTS_TAC ‘y’ \\
      CONJ_TAC >- (Q.EXISTS_TAC ‘x’ >> art []) \\
      simp [],
      (* goal 3 (of 4) *)
      DISJ1_TAC \\
      MATCH_MP_TAC NONTRIVIAL_LIMIT_WITHIN >> art [],
      (* goal 4 (of 4) *)
      Cases_on ‘trivial_limit (net within s)’ >> simp [] \\
      fs [trivial_limit] \\
      simp [WITHIN] \\
      cheat ]
QED

(* ------------------------------------------------------------------------- *)
(* Combining theorems for "eventually". *)
(* ------------------------------------------------------------------------- *)

Theorem EVENTUALLY_AND :
  !net:('a net) p q.
   eventually (\x. p x /\ q x) net <=>
   eventually p net /\ eventually q net
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually] THEN
  ASM_CASES_TAC ``trivial_limit(net:('a net))`` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN SIMP_TAC std_ss [NET_DILEMMA] THENL [MESON_TAC [], ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC NET_DILEMMA THEN METIS_TAC []
QED

Theorem EVENTUALLY_MONO :
  !net:('a net) p q.
  (!x. p x ==> q x) /\ eventually p net
    ==> eventually q net
Proof
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_MP :
  !net:('a net) p q.
  eventually (\x. p x ==> q x) net /\ eventually p net
  ==> eventually q net
Proof
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_FORALL :
  !net:('a net) p s:'b->bool.
  FINITE s /\ ~(s = {})
  ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
   !a. a IN s ==> eventually (p a) net)
Proof
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  KNOW_TAC ``!s:'b->bool. (s <> ({} :'b -> bool) ==>
   (eventually (\(x :'a). !(a :'b). a IN s ==> (p :'b -> 'a -> bool) a x)
   (net :'a net) <=> !(a :'b). a IN s ==> eventually (p a) net)) =
             (\s. s <> ({} :'b -> bool) ==>
   (eventually (\(x :'a). !(a :'b). a IN s ==> (p :'b -> 'a -> bool) a x)
   (net :'a net) <=> !(a :'b). a IN s ==> eventually (p a) net)) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [FORALL_IN_INSERT, EVENTUALLY_AND, ETA_AX] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``t:'b->bool``, ``b:'b``] THEN
  ASM_CASES_TAC ``t:'b->bool = {}`` THEN
  ASM_SIMP_TAC std_ss [NOT_IN_EMPTY, EVENTUALLY_TRUE] THEN METIS_TAC []
QED

Theorem FORALL_EVENTUALLY :
  !net:('a net) p s:'b->bool.
   FINITE s /\ ~(s = {})
   ==> ((!a. a IN s ==> eventually (p a) net) <=>
   eventually (\x. !a. a IN s ==> p a x) net)
Proof
  SIMP_TAC std_ss [EVENTUALLY_FORALL]
QED

(* NOTE: In HOL-Light, this theorem has “~(a IN topspace top) \/ _” as the
   conclusion, which in HOL4, “topspace (mtop m) = UNIV”, is not needed:

   |- !P top a:A.
        eventually P (atpointof top a) <=>
        ~(a IN topspace top) \/
        ?u. open_in top u /\ a IN u /\ !x. x IN u DELETE a ==> P x

   NOTE: Added “limpt (mtop m) a univ(:'a)” as necessary antecedents.

Theorem EVENTUALLY_ATPOINTOF :
    !P m a. limpt (mtop m) a univ(:'a) ==>
           (eventually P (atpointof m a) <=>
            ?u. open_in (mtop m) u /\ a IN u /\ !x. x IN u DELETE a ==> P x)
Proof
    rw [eventually, ATPOINTOF]
 >> EQ_TAC >> rw []
 (* goal 1 (of 3): trivial_limit ==> ?u. open_in (mtop m) u /\ ... *)
 >- (fs [trivial_limit]
     >- (Q.EXISTS_TAC ‘topspace (mtop m)’ \\
         REWRITE_TAC [OPEN_IN_TOPSPACE] \\
         simp [TOPSPACE_MTOP]) \\
     rename1 ‘x <> y’ \\
     fs [ATPOINTOF, REAL_NOT_LE, FORALL_AND_THM] \\
     Cases_on ‘a = x’
     >- (fs [METRIC_SAME] \\
         Q.PAT_X_ASSUM ‘!z. _’ (MP_TAC o Q.SPEC ‘y’) \\
         simp [METRIC_NZ]) \\
     Q.PAT_X_ASSUM ‘!z. _ \/ dist m (x,a) < dist m (z,a)’ (MP_TAC o Q.SPEC ‘x’) \\
     simp [METRIC_NZ])
 (* goal 2 (of 3): a < x <= y (assuming 0 < a) *)
 >- (qabbrev_tac ‘r = dist m (y,a)’ \\
    ‘0 < r’ by PROVE_TAC [REAL_LTE_TRANS] \\
     Q.EXISTS_TAC ‘B m (a,r)’ \\
     REWRITE_TAC [OPEN_IN_MBALL] \\
     CONJ_TAC >- (MATCH_MP_TAC CENTRE_IN_MBALL >> simp [MSPACE]) \\
     Q.X_GEN_TAC ‘z’ \\
     rw [IN_MBALL] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     simp [METRIC_NZ, Once MDIST_SYM] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 (* goal 3 (of 3): a < x <= y (assuming 0 < a) *)
 >> DISJ2_TAC
 >> fs [MTOP_OPEN', MTOP_LIMPT']
 >> Q.PAT_X_ASSUM ‘!x. x IN u ==> ?e. _’ (MP_TAC o Q.SPEC ‘a’) >> rw []
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?y. _’ (MP_TAC o Q.SPEC ‘e’) >> rw [IN_APP]
 >> Q.EXISTS_TAC ‘y’
 >> CONJ_TAC >- (Q.EXISTS_TAC ‘y’ >> simp [METRIC_NZ])
 >> rpt STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> reverse CONJ_TAC >- fs [MDIST_POS_EQ]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘dist m (a,y)’ >> art []
 >> ONCE_REWRITE_TAC [MDIST_SYM] >> art []
QED
 *)

(* NOTE: This theorem is trivial (by NET_WITHIN_UNIV and MSPACE) in HOL4.
   The original HOL-Light version is:

   |- !top a:A. (atpointof top a) within (topspace top) = atpointof top a
 *)
Theorem ATPOINTOF_WITHIN_TOPSPACE :
    !m a. ((atpointof m a) within (mspace m)) = atpointof m a
Proof
    rw [NET_WITHIN_UNIV, MSPACE]
QED

(* TODO: The other direction seems non-provable in HOL4...
Theorem TRIVIAL_LIMIT_ATPOINTOF_WITHIN :
    !m s a. trivial_limit(atpointof m a within s) <=>
            a NOTIN mtop m derived_set_of s
Proof
    rw [trivial_limit, WITHIN, ATPOINTOF, derived_set_of_alt_limpt]
 >> EQ_TAC >> rw []
 >- (rw [MTOP_LIMPT'] \\
     Q.EXISTS_TAC ‘1’ >> simp [])
 >- (rename1 ‘x <> y’ \\
     rw [MTOP_LIMPT'] \\
     fs [FORALL_AND_THM, REAL_NOT_LT, REAL_NOT_LE] \\
     fs [MDIST_LE_0, GSYM DISJ_ASSOC] \\
     Cases_on ‘a <> x’
     >- (Q.EXISTS_TAC ‘dist m (x,a)’ >> simp [METRIC_NZ] \\
         Q.X_GEN_TAC ‘z’ \\
         Cases_on ‘a = z’ >> simp [] \\
         Q.PAT_X_ASSUM ‘!x'. _ \/ dist m (x,a) < dist m (x',a) \/ _’
           (MP_TAC o Q.SPEC ‘z’) >> simp [MDIST_EQ_0] \\
        ‘dist m (a,z) = dist m (z,a)’ by simp [MDIST_SYM] >> POP_ORW \\
         reverse STRIP_TAC >- art [] \\
         DISJ2_TAC \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     fs [] \\
     POP_ASSUM (fs o wrap o SYM) \\
     Q.EXISTS_TAC ‘dist m (y,a)’ >> simp [METRIC_NZ] \\
     Q.X_GEN_TAC ‘z’ \\
     Cases_on ‘a = z’ >> simp [] \\
     Q.PAT_X_ASSUM ‘!x'. _ \/ dist m (y,a) < dist m (x',a) \/ _’
        (MP_TAC o Q.SPEC ‘z’) >> simp [MDIST_EQ_0] \\
    ‘dist m (a,z) = dist m (z,a)’ by simp [MDIST_SYM] >> POP_ORW \\
     reverse STRIP_TAC >- art [] \\
     DISJ2_TAC \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 (* stage work *)
 >> Cases_on ‘!a b. a = b’ >> simp []
 >> fs [] >> rename1 ‘x <> y’
 (* a is not a limit point in s, but do we know “a IN s”? *)
 >> fs [MTOP_LIMPT', REAL_NOT_LT, REAL_NOT_LE]
 >> simp [MDIST_LE_0, MDIST_EQ_0]
 >> Cases_on ‘s = {}’ >> fs []
 >- (qexistsl_tac [‘x’, ‘y’] >> art [])
 >> Cases_on ‘s = {a}’ >> fs []
 >- (qexistsl_tac [‘x’, ‘y’] >> art [])
 >> qabbrev_tac ‘t = s DELETE a’
 >> Know ‘?z. z IN t’
 >- (Q.PAT_X_ASSUM ‘s <> {a}’ MP_TAC \\
     simp [Once EXTENSION] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘z’ STRIP_ASSUME_TAC) \\
     Cases_on ‘z = a’ >> fs []
     >- (rw [Abbr ‘t’, Once EXTENSION] \\
         fs [GSYM MEMBER_NOT_EMPTY] >> rename1 ‘b IN s’ \\
         Q.EXISTS_TAC ‘b’ >> PROVE_TAC []) \\
     rw [Abbr ‘t’, Once EXTENSION] \\
     Q.EXISTS_TAC ‘z’ >> art [])
 >> DISCH_TAC
 >> cheat
QED

Theorem DERIVED_SET_OF_TRIVIAL_LIMIT :
   !m s a. a IN mtop m derived_set_of s ==>
          ~trivial_limit (atpointof m a within s)
Proof
    PROVE_TAC [TRIVIAL_LIMIT_ATPOINTOF_WITHIN]
QED

Theorem TRIVIAL_LIMIT_ATPOINTOF :
   !m a. trivial_limit (atpointof m a) ==>
         a NOTIN mtop m derived_set_of mspace m
Proof
  ONCE_REWRITE_TAC[GSYM ATPOINTOF_WITHIN_TOPSPACE] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_ATPOINTOF_WITHIN]
QED

(* NOTE: Added “a IN mtop m derived_set_of P” as necessary antecedents *)
Theorem EVENTUALLY_ATPOINTOF_METRIC :
    !P m a. limpt (mtop m) a univ(:'a) ==>
       (eventually P (atpointof m a) <=>
        a IN mspace m
        ==> ?d. &0 < d /\
                !x. x IN mspace m /\ &0 < mdist m (x,a) /\ mdist m (x,a) < d
                    ==> P x)
Proof
    rpt STRIP_TAC
 >> rw [EVENTUALLY_ATPOINTOF]
 >> EQ_TAC >> rw [MSPACE]
 >- (fs [MTOP_OPEN'] \\
     Q.PAT_X_ASSUM ‘!x. x IN u ==> _’ (MP_TAC o Q.SPEC ‘a’) >> rw [] \\
     Q.EXISTS_TAC ‘e’ >> rw [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     reverse CONJ_TAC
     >- (CCONTR_TAC >> fs [METRIC_SAME]) \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     simp [Once MDIST_SYM])
 >> Q.EXISTS_TAC ‘B m (a,d)’
 >> simp [OPEN_IN_MBALL]
 >> CONJ_TAC >- (MATCH_MP_TAC CENTRE_IN_MBALL >> simp [MSPACE])
 >> rw [IN_MBALL, MSPACE]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> simp [MDIST_POS_LT]
 >> simp [Once MDIST_SYM]
QED
 *)

Theorem NETLIMIT_WITHIN :
   !a:real s. ~(trivial_limit (at a within s))
    ==> (netlimit (at a within s) = a)
Proof
  REWRITE_TAC[trivial_limit, netlimit, AT, WITHIN, DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   ``!x:real. ~(&0 < dist(x,a) /\ dist(x,a) <= dist(a,a) /\ x IN s)``
    ASSUME_TAC THENL
    [ ASM_MESON_TAC[DIST_REFL, REAL_NOT_LT], ASM_MESON_TAC[] ]
QED

(* ------------------------------------------------------------------------- *)
(* Limits in a topological space (from HOL-Light's Multivariate/metric.ml)   *)
(* ------------------------------------------------------------------------- *)

Definition limit :
   limit top (f:'a->'b) l net <=>
     l IN topspace top /\
     (!u. open_in top u /\ l IN u ==> eventually (\x. f x IN u) net)
End

(*
Theorem LIMIT_ATPOINTOF :
    !m top' f x y. limpt (mtop m) x univ(:'a) ==>
       (limit top' f y (atpointof m x) <=>
        y IN topspace top' /\
        !v. open_in top' v /\ y IN v
                 ==> ?u. open_in (mtop m) u /\ x IN u /\
                         IMAGE f (u DELETE x) SUBSET v)
Proof
    RW_TAC std_ss [limit, EVENTUALLY_ATPOINTOF]
 >> qabbrev_tac ‘top = mtop m’
 >> Cases_on ‘y IN topspace top'’ >> simp []
 >> AP_TERM_TAC >> ABS_TAC
 >> SET_TAC [] (* amazing ... *)
QED

Theorem TOPCONTINUOUS_AT_ATPOINTOF :
    !m top' f x. limpt (mtop m) x univ(:'a) ==>
       (topcontinuous_at (mtop m) top' f x <=>
        (!x. f x IN topspace top') /\
        limit top' f (f x) (atpointof m x))
Proof
    rw [topcontinuous_at, TOPSPACE_MTOP, LIMIT_ATPOINTOF]
 >> Cases_on ‘!x. f x IN topspace top'’ >> simp []
 >> SET_TAC []
QED

Theorem CONTINUOUS_MAP_ATPOINTOF :
    !m top' f. (!x. limpt (mtop m) x univ(:'a)) ==>
       (continuous_map (mtop m,top') f <=>
        !x. limit top' f (f x) (atpointof m x))
Proof
    rw [CONTINUOUS_MAP_EQ_TOPCONTINUOUS_AT, TOPSPACE_MTOP]
 >> simp [TOPCONTINUOUS_AT_ATPOINTOF, limit]
 >> METIS_TAC []
QED

Theorem LIMIT_CONTINUOUS_MAP :
    !m top' f a b. (!x. limpt (mtop m) x univ(:'a)) /\
        continuous_map(mtop m,top') f /\ f a = b
        ==> limit top' f b (atpointof m a)
Proof
    MESON_TAC[CONTINUOUS_MAP_ATPOINTOF]
QED
 *)

(* Connection between HOL-Light's ‘limit’ and HOL4's ‘tends’

   NOTE: The net with ‘limit’ must be reflexive, which is not assumed in general.
   Further more, the net cannot be trivial, and ‘l IN topspace top’ must be
   assumed because it's not included with ‘f tends l’.
 *)
Theorem tends_imp_limit :
    !top f l net. ~trivial_limit net /\ l IN topspace top ==>
                 (f tends l) (top,netord net) ==> limit top (f:'a->'b) l net
Proof
    rw [limit, tends, eventually, OPEN_NEIGH]
 >> Q.PAT_X_ASSUM ‘!x. u x ==> _’ (MP_TAC o Q.SPEC ‘l’)
 >> POP_ASSUM MP_TAC
 >> rw [IN_APP]
 >> Q.PAT_X_ASSUM ‘!N. neigh top (N,l) ==> _’ (MP_TAC o Q.SPEC ‘N’) >> rw []
 >> Q.EXISTS_TAC ‘n’
 >> CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> art [])
 >> rpt STRIP_TAC
 >> ‘f x IN N’ by rw [IN_APP]
 >> ‘f x IN u’ by PROVE_TAC [SUBSET_DEF] >> fs [IN_APP]
QED

Theorem limit_alt_tends :
    !top f l net. ~trivial_limit net /\ l IN topspace top /\
                 (!x y. netord net x y ==> netord net y y) ==>
                 (limit top (f:'a->'b) l net <=> (f tends l) (top,netord net))
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- rw [tends_imp_limit]
 >> rw [limit, tends, reflexive_def, neigh]
 >> Q.PAT_X_ASSUM ‘!u. open_in top u /\ l IN u ==> _’ (MP_TAC o Q.SPEC ‘P’)
 >> rw [IN_APP, eventually]
 >> Q.EXISTS_TAC ‘y’
 >> CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> art [])
 >> rpt STRIP_TAC
 >> ‘f m IN P’ by rw [IN_APP]
 >> ‘f m IN N’ by PROVE_TAC [SUBSET_DEF] >> fs [IN_APP]
QED

(* ------------------------------------------------------------------------- *)
(* More sequential characterizations in a metric space.                      *)
(* ------------------------------------------------------------------------- *)

(* !x. P x ==> Q x) ==> (!x. P x) ==> !x. Q x *)
Theorem MONO_FORALL = MONO_ALL

(* |- !P Q. (!x. P x) /\ (!x. Q x) <=> !x. P x /\ Q x *)
Theorem AND_FORALL_THM = GSYM FORALL_AND_THM

(*
Theorem EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY_lemma[local] :
    !met P s a. limpt (mtop met) a univ(:'a) ==>
       (eventually P (atpointof met a within s) <=>
        !x. (!n. x(n) IN (s INTER mspace met) DELETE a) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially)
Proof
    rw [MSPACE]
    REWRITE_TAC[EVENTUALLY_WITHIN_IMP; EVENTUALLY_ATPOINTOF] THEN
    REWRITE_TAC[limit; TOPSPACE_MTOPOLOGY] THEN
    ASM_CASES_TAC `(a:A) IN mspace met` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_IMP; IN_DELETE; IN_INTER] THEN
    X_GEN_TAC `u:A->bool` THEN STRIP_TAC THEN
    X_GEN_TAC `x:num->A` THEN REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN ASM SET_TAC[];
    STRIP_TAC THEN
    REWRITE_TAC[EVENTUALLY_ATPOINTOF_METRIC; EVENTUALLY_WITHIN_IMP] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[IMP_CONJ; MDIST_POS_EQ] THEN
    GEN_REWRITE_TAC I [MESON[]
      `(?d. P d /\ Q d) <=> ~(!d. P d ==> ~Q d)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV)
     [NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?x. (!n. (x n) IN mspace met /\
              ~(x n = a) /\
               mdist met (x n,a) < inv(&n + &1) /\
               x n IN s /\
               ~P(x n:A)) /\
          (!n. mdist met (x(SUC n),a) < mdist met (x n,a))`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN STRIP_TAC THEN
      SIMP_TAC[TAUT `(p /\ q /\ r /\ s /\ t) /\ u <=>
                      p /\ q /\ (r /\ u) /\ s /\ t`] THEN
      REWRITE_TAC[GSYM REAL_LT_MIN] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_MIN; MDIST_POS_EQ; REAL_LT_INV_EQ] THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `x:num->A`) THEN
      ASM_REWRITE_TAC[NOT_IMP; IN_DELETE; IN_INTER; GSYM CONJ_ASSOC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC  TRANSITIVE_STEPWISE_LT THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        DISCH_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC WLOG_LT THEN ASM_MESON_TAC[REAL_LT_REFL];
        ASM_REWRITE_TAC[LIMIT_METRIC; EVENTUALLY_SEQUENTIALLY] THEN
        MATCH_MP_TAC FORALL_POS_MONO_1 THEN CONJ_TAC THENL
         [MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
        X_GEN_TAC `N:num` THEN EXISTS_TAC `N:num` THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        TRANS_TAC REAL_LTE_TRANS `inv(&n + &1)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[EVENTUALLY_FALSE; TRIVIAL_LIMIT_SEQUENTIALLY]]]]);;
*)

(*
let [EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY;
     EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY_INJ;
     EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY_DECREASING] = (CONJUNCTS o prove)
 (`(
   (!met P s a:A.
        eventually P (atpointof (mtopology met) a within s) <=>
        !x. (!n. x(n) IN (s INTER mspace met) DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially) /\
   (!met P s a:A.
        eventually P (atpointof (mtopology met) a within s) <=>
        !x. (!n. x(n) IN (s INTER mspace met) DELETE a) /\
            (!m n. m < n ==> mdist met (x n,a) < mdist met (x m,a)) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially)
   `,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(r ==> s) /\ (q ==> r) /\ (p ==> q) /\ (s ==> p)
    ==> (p <=> q) /\ (p <=> r) /\ (p <=> s)`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:num->A` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_LT_REFL];

    MATCH_MP_TAC MONO_FORALL THEN MESON_TAC[];
*)

(*
let EVENTUALLY_ATPOINTOF_SEQUENTIALLY = prove
 (`!met P a:A.
        eventually P (atpointof (mtopology met) a) <=>
        !x. (!n. x(n) IN mspace met DELETE a) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM NET_WITHIN_UNIV] THEN
  SIMP_TAC[EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY; INTER_UNIV]);;

let EVENTUALLY_ATPOINTOF_SEQUENTIALLY_INJ = prove
 (`!met P a:A.
        eventually P (atpointof (mtopology met) a) <=>
        !x. (!n. x(n) IN mspace met DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM NET_WITHIN_UNIV] THEN
  SIMP_TAC[EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY_INJ; INTER_UNIV]);;

let EVENTUALLY_ATPOINTOF_SEQUENTIALLY_DECREASING = prove
 (`!met P a:A.
        eventually P (atpointof (mtopology met) a) <=>
        !x. (!n. x(n) IN mspace met DELETE a) /\
            (!m n. m < n ==> mdist met (x n,a) < mdist met (x m,a)) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM NET_WITHIN_UNIV] THEN
  SIMP_TAC[EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY_DECREASING; INTER_UNIV]);;
*)

(*
let LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN = prove
 (`!m1 m2 s f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a within s) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN (s INTER mspace m1) DELETE a) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [limit] THEN
  ASM_CASES_TAC `(l:B) IN mspace m2` THEN
  ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o RAND_CONV) [limit] THEN
  REWRITE_TAC[EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY] THEN
  ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY; o_DEF; RIGHT_IMP_FORALL_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP; CONJ_ACI]);;
  *)

(*
let LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN_INJ = prove
 (`!m1 m2 s f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a within s) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN (s INTER mspace m1) DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [limit] THEN
  ASM_CASES_TAC `(l:B) IN mspace m2` THEN
  ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o RAND_CONV) [limit] THEN
  REWRITE_TAC[EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY_INJ] THEN
  ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY; o_DEF; RIGHT_IMP_FORALL_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP; CONJ_ACI]);;

let LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN_DECREASING = prove
 (`!m1 m2 s f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a within s) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN (s INTER mspace m1) DELETE a) /\
            (!m n. m < n ==> mdist m1 (x n,a) < mdist m1 (x m,a)) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [limit] THEN
  ASM_CASES_TAC `(l:B) IN mspace m2` THEN
  ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o RAND_CONV) [limit] THEN
  REWRITE_TAC[EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY_DECREASING] THEN
  ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY; o_DEF; RIGHT_IMP_FORALL_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP; CONJ_ACI]);;

let LIMIT_ATPOINTOF_SEQUENTIALLY = prove
 (`!m1 m2 f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN mspace m1 DELETE a) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM NET_WITHIN_UNIV] THEN
  REWRITE_TAC[LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN] THEN
  REWRITE_TAC[INTER_UNIV]);;

let LIMIT_ATPOINTOF_SEQUENTIALLY_INJ = prove
 (`!m1 m2 f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN mspace m1 DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM NET_WITHIN_UNIV] THEN
  REWRITE_TAC[LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN_INJ] THEN
  REWRITE_TAC[INTER_UNIV]);;

let LIMIT_ATPOINTOF_SEQUENTIALLY_DECREASING = prove
 (`!m1 m2 f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN mspace m1 DELETE a) /\
            (!m n. m < n ==> mdist m1 (x n,a) < mdist m1 (x m,a)) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM NET_WITHIN_UNIV] THEN
  REWRITE_TAC[LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN_DECREASING] THEN
  REWRITE_TAC[INTER_UNIV]);;
*)

(* ------------------------------------------------------------------------- *)
(*  Directed Sets and Net (alternative approach to “:'a net”) following [2]  *)
(* ------------------------------------------------------------------------- *)

(* Also called "upwards filtering". See, e.g., [2, p.65], [3] and [4, p.301].

   NOTE: In case ‘x’ or ‘y’ is the maximal element, we have ‘z = x’ or ‘z = y’,
   and therefore ‘(z,z) IN r’, i.e. “r” must be an less-equal (<=) relation.
 *)
Definition upwards_directed_def :
    upwards_directed r s =
    !x y. x IN s /\ y IN s ==> ?z. z IN s /\ (x,z) IN r /\ (y,z) IN r
End

(* See, e.g. [2, p.65] (Directed Sets and Nets)

   NOTE: The 1st argument of the preorder is "smaller (or equal)" than the 2nd
   argument. This is more natural than ‘dorder’ and ‘isnet’ and makes TRANS_TAC
   applicable.

   NOTE: Here we used “reflexive” from set_relationTheory but relationTheory,
   to make sure that the reflexivity is limited within D. This is important for
   some concrete nets like “atpointof” (or “at”), whose ordering is like this:

     g = \x y. 0 < dist m (x,a) /\ dist m (x,a) <= dist m (y,a)

   Note that “g (x,x)” doesn't hold if x = a.

   On the other hand, the “transitive” definition in both relation theories
   does not take any domain argument. This seems good enough for practical uses
   including our case, e.g. transitivity (even for elements outside of D) can
   be proved for “atpointof” with the above ordering definition.

   Note also that reflexive + transitive = pre-order (aka "quasi-order").
 *)
Definition is_dset_def :
   is_dset (D,g) = (D <> {} /\
                    reflexive (rel_to_reln g) D /\
                    transitive (rel_to_reln g) /\
                    upwards_directed (rel_to_reln g) D)
End

Theorem dset_EXISTS[local] :
    ?dset. is_dset dset
Proof
    Q.EXISTS_TAC ‘(UNIV,\x y. T)’
 >> simp [is_dset_def, upwards_directed_def,
          set_relationTheory.rel_to_reln_def,
          set_relationTheory.reflexive_def,
          set_relationTheory.transitive_def]
QED

val dset_tydef as {absrep_id, newty, repabs_pseudo_id,
                   termP, termP_exists, termP_term_REP,
                   term_ABS_pseudo11, term_ABS_t,
                   term_REP_11, term_REP_t} =
    rich_new_type {tyname = "dset",
                   exthm  = dset_EXISTS,
                   ABS    = "mk_dset",
                   REP    = "dest_dset"};

Theorem dset_tybij :
    (!n. mk_dset (dest_dset n) = n) /\
    (!D g. is_dset (D,g) <=> dest_dset (mk_dset (D,g)) = (D,g))
Proof
    rw [absrep_id]
 >> EQ_TAC
 >- (DISCH_TAC \\
     MATCH_MP_TAC repabs_pseudo_id >> art [])
 >> rw [termP_exists]
 >> Q.EXISTS_TAC ‘mk_dset (D,g)’ >> art []
QED

(* |- !n. is_dset (dest_dset n) *)
Theorem dest_dset_is_dset =
        termP_term_REP |> Q.INST [‘g’ |-> ‘n’] |> GEN_ALL

(* |- !n n'. is_dset n /\ is_dset n' ==> (mk_dset n = mk_dset n' <=> n = n') *)
Theorem mk_dset_11 =
        term_ABS_pseudo11 |> Q.INST [‘x’ |-> ‘n’, ‘y’ |-> ‘n'’]
                          |> Q.GENL [‘n’, ‘n'’]

(* |- !n n'. dest_dset n = dest_dset n' <=> n = n' *)
Theorem dest_dset_11 =
        term_REP_11 |> Q.INST [‘g’ |-> ‘n’, ‘h’ |-> ‘n'’]
                    |> Q.GENL [‘n’, ‘n'’]

Overload dset_dom = “\n. FST (dest_dset n)”
Overload dset_ord = “\n. SND (dest_dset n)”

(*
Theorem netord_reflexive :
    !net x. x IN netdom net ==> netord net x x
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPEC ‘net’ isnet_dest_net)
 >> Cases_on ‘dest_net net’ >> fs [isnet_def]
QED

Theorem netord_transitive :
    !net x y z. x IN netdom net /\ y IN netdom net /\ z IN netdom net /\
                netord net y x /\ netord net z y ==> netord net z x
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPEC ‘net’ isnet_dest_net)
 >> Cases_on ‘dest_net net’ >> fs [isnet_def]
 >> rpt STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘y’ >> art []
QED

Theorem netord_upward_directed :
    !net x y. x IN netdom net /\ y IN netdom net ==>
              ?z. z IN netdom net /\ netord net z x /\ netord net z y
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPEC ‘net’ isnet_dest_net)
 >> Cases_on ‘dest_net net’ >> fs [isnet_def]
QED
 *)

(*
Theorem OLDNET :
    !net x y. x IN netdom net /\ y IN netdom net
          ==> ?z. z IN netdom net /\
                  !w. w IN netdom net /\ netord net w z ==>
                      netord net w x /\ netord net w y
Proof
    RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [‘net’, ‘x’, ‘y’] netord_upward_directed)
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘z’
 >> RW_TAC std_ss []
 >| [ MATCH_MP_TAC netord_transitive \\
      Q.EXISTS_TAC ‘z’ >> art [],
      MATCH_MP_TAC netord_transitive \\
      Q.EXISTS_TAC ‘z’ >> art [] ]
QED

(* NOTE: totality is additionally assumed here. *)
Theorem NET :
   !net x y. x IN netdom net /\ y IN netdom net /\
            (!a b. a IN netdom net /\ b IN netdom net ==>
                   netord net a b \/ netord net b a) ==>
            (!z. z IN netdom net /\ netord net z x ==> netord net z y) \/
            (!z. z IN netdom net /\ netord net z y ==> netord net z x)
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (MP_TAC o Q.SPECL [‘x’, ‘y’])
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 2) *)
      DISJ1_TAC >> rpt STRIP_TAC \\
      MATCH_MP_TAC netord_transitive \\
      Q.EXISTS_TAC ‘x’ >> art [],
      (* goal 2 (of 2) *)
      DISJ2_TAC >> rpt STRIP_TAC \\
      MATCH_MP_TAC netord_transitive \\
      Q.EXISTS_TAC ‘y’ >> art [] ]
QED
 *)
(* new way
Theorem NET_DILEMMA :
   !net. (!a b. a IN netdom net /\ b IN netdom net ==>
                netord net a b \/ netord net b a) /\
         (?a. a IN netdom net /\
              !x. x IN netdom net /\ netord net x a ==> P x) /\
         (?b. b IN netdom net /\
              !y. y IN netdom net /\ netord net y b ==> Q y)
     ==> ?c. c IN netdom net /\
             !z. z IN netdom net /\ netord net z c ==> P z /\ Q z
Proof
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!a b. _’ (MP_TAC o Q.SPECL [‘a’, ‘b’])
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 2): a is greater *)
      Q.EXISTS_TAC ‘a’ >> rw [] \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
      MATCH_MP_TAC netord_transitive \\
      Q.EXISTS_TAC ‘a’ >> art [],
      (* goal 2 (of 2): b is greater *)
      Q.EXISTS_TAC ‘b’ >> rw [] \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
      MATCH_MP_TAC netord_transitive \\
      Q.EXISTS_TAC ‘b’ >> art [] ]
QED
 *)

(* END *)
val _ = export_theory ();

(* References:

 [1] Moore, E.H., Smith, H.L.: A General Theory of Limits. American Journal of
     Mathematics. 44, 102-121 (1922).
 [2] Kelley, J.L.: General Topology. Springer Science & Business Media (1975).
 [3] https://en.wikipedia.org/wiki/Net_(mathematics)
 [4] Schilling, R.L.: Measures, Integrals and Martingales (2nd Edition).
     Cambridge University Press (2017).
 *)
