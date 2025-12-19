(*===========================================================================*)
(* Theory of Moore-Smith convergence nets, and special cases like sequences  *)
(*===========================================================================*)

(*
Theory nets
Ancestors
  pred_set pair combin arithmetic num prim_rec relation real topology
  metric cardinal
Libs
  numLib reduceLib pairLib mesonLib RealField hurdUtils jrhUtils tautLib
 *)
open HolKernel Parse boolLib bossLib;

open numLib reduceLib pairLib pred_setTheory mesonLib realLib hurdUtils
     pairTheory arithmeticTheory numTheory prim_recTheory relationTheory
     jrhUtils realTheory topologyTheory metricTheory tautLib combinTheory
     cardinalTheory;

val _ = new_theory "nets";

val _ = Parse.reveal "B";

val NUM_EQ_CONV = Arithconv.NEQ_CONV;
val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC;

(* !x. P x ==> Q x) ==> (!x. P x) ==> !x. Q x *)
Theorem MONO_FORALL = MONO_ALL

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
      REWRITE_TAC[REAL_INJ] THEN CONV_TAC(RAND_CONV NUM_EQ_CONV) THEN
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

   old definition (\x y. 0 < mdist (x,a) /\ mdist m (x,a) <= mdist m (y,a))

Definition atpointof_def[nocompute]:
    atpointof m a = mk_net (tendsto (m,a))
End

   new definition (removed “0 < mdist (x,a)” to make the order reflexive):
 *)
Definition atpointof[nocompute]:
    atpointof m a = mk_net (\x y. mdist m (x,a) <= mdist m (y,a))
End

(* HOL-Light: at a = atpointof euclidean a *)
Definition at_def:
    at z = atpointof mr1 z
End

(* |- !a. at a = mk_net (\x y. dist (x,a) <= dist (y,a)) *)
Theorem at = atpointof |> ISPEC “mr1”
                       |> REWRITE_RULE [GSYM at_def, GSYM dist_def]

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

(* HOL-Light's definition:

let within = new_definition
  `net within s = mk_net (netfilter net relative_to s,netlimits net)`;;

   NOTE: “within” only requires “x IN s” (next value) but not for “y”:
 *)
Definition within[nocompute]:
  (net within s) = mk_net(\x y. netord net x y /\ x IN s)
End

Definition in_direction:
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
      netord(atpointof m a) x y <=> mdist m (x,a) <= mdist m (y,a)
Proof
  NTAC 2 GEN_TAC THEN NET_PROVE_TAC[atpointof] THEN
  METIS_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS, REAL_LET_TRANS]
QED

(* |- !a x y. netord (at a) x y <=> dist (x,a) <= dist (y,a) *)
Theorem AT = ATPOINTOF |> ISPEC “mr1”
                       |> REWRITE_RULE [GSYM at_def, GSYM dist_def]

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
                 dist(x,a) <= dist(y,a) /\
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
(* It's also sometimes useful to extract the limit point from the net.       *)
(* ------------------------------------------------------------------------- *)

(* old definition:
Definition netlimit :
    netlimit net = @a. !x. ~(netord net x a)
End

   new definition:
 *)
Definition netlimit_def :
    netlimit net = @a. !x. x <> a ==> ~(netord net x a)
End

(* |- !net. netlimit net = @a. !x. netord net x a ==> x = a *)
Theorem netlimit_alt = REWRITE_RULE [CONTRAPOS_THM] netlimit_def

Theorem NETLIMIT_ATPOINTOF :
    !m a. netlimit(atpointof m a) = a
Proof
    RW_TAC std_ss [netlimit_def, ATPOINTOF]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (Q.EXISTS_TAC ‘a’ \\
     Q.X_GEN_TAC ‘x’ \\
     rw [MDIST_REFL, REAL_NOT_LE, MDIST_POS_LT])
 >> rw [REAL_NOT_LE]
 >> CCONTR_TAC
 >> Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘a’)
 >> simp [REAL_NOT_LT, MDIST_REFL, MDIST_POS_LE]
QED

(* |- !a. netlimit (at a) = a *)
Theorem NETLIMIT_AT = NETLIMIT_ATPOINTOF |> ISPEC “mr1”
                   |> REWRITE_RULE [GSYM at_def]

(* NOTE: This definition is compatible with HOL-Light *)
Definition netlimits_def :
    netlimits net = {a | !x. x <> a ==> ~(netord net x a)}
End

(* |- !net. netlimits net = {a | !x. netord net x a ==> x = a}

   cf. set_relationTheory.maximal_elements_def
 *)
Theorem netlimits_alt = REWRITE_RULE [CONTRAPOS_THM] netlimits_def

(* NOTE: This theorem is the definition of “netlimit” in HOL-Light *)
Theorem netlimit :
    !n. netlimit n = (@x. x IN netlimits n)
Proof
    rw [netlimit_def, netlimits_def]
QED

Theorem NETLIMITS_ATPOINTOF :
    !m a. netlimits (atpointof m a) = {a}
Proof
    rw [netlimits_def, ATPOINTOF, MDIST_POS_EQ, REAL_NOT_LE]
 >> rw [Once EXTENSION]
 >> reverse EQ_TAC >- rw [MDIST_REFL, MDIST_POS_EQ]
 >> rpt STRIP_TAC
 >> CCONTR_TAC
 >> Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘a’)
 >> simp [REAL_NOT_LT, MDIST_REFL, MDIST_POS_LE]
QED

(* |- !a. netlimits (at a) = {a} *)
Theorem NETLIMITS_AT = NETLIMITS_ATPOINTOF |> ISPEC “mr1”
                    |> REWRITE_RULE [GSYM at_def]

Theorem NETLIMITS_SEQUENTIALLY :
    netlimits sequentially = {}
Proof
    rw [Once EXTENSION, NOT_IN_EMPTY, netlimits_def, SEQUENTIALLY, GREATER_EQ]
 >> Q.EXISTS_TAC ‘SUC x’ >> simp []
QED

Theorem NETLIMITS_AT_POSINFINITY :
    netlimits at_posinfinity = {}
Proof
    rw [Once EXTENSION, NOT_IN_EMPTY, netlimits_def, AT_POSINFINITY, real_ge]
 >> Q.EXISTS_TAC ‘x + 1’
 >> REAL_ARITH_TAC
QED

Theorem NETLIMITS_AT_NEGINFINITY :
    netlimits at_neginfinity = {}
Proof
    rw [Once EXTENSION, NOT_IN_EMPTY, netlimits_def, AT_NEGINFINITY]
 >> Q.EXISTS_TAC ‘x - 1’
 >> REAL_ARITH_TAC
QED

Theorem NETLIMITS_AT_INFINITY :
    netlimits at_infinity = {}
Proof
    rw [Once EXTENSION, NOT_IN_EMPTY, netlimits_def, AT_INFINITY, real_ge]
 >> Cases_on ‘0 <= x’
 >- (Q.EXISTS_TAC ‘x + 1’ \\
    ‘0 <= x + 1’ by simp [REAL_LE_ADD] \\
     simp [ABS_REDUCE] >> REAL_ARITH_TAC)
 >> fs [REAL_NOT_LE, ABS_EQ_NEG]
 >> Q.EXISTS_TAC ‘x - 1’
 >> Know ‘x - 1 < 0’
 >- (simp [REAL_SUB_LT_NEG] \\
     Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘0’ >> simp [])
 >> DISCH_TAC
 >> simp [ABS_EQ_NEG]
 >> REAL_ARITH_TAC
QED

(* NOTE: This lemma shows that “within” makes netlimits potentially larger. *)
Theorem NETLIMITS_WITHIN_lemma1[local] :
    netlimits net SUBSET netlimits (net within s)
Proof
    rw [SUBSET_DEF, netlimits_def, WITHIN]
QED

Theorem NETLIMITS_WITHIN_lemma2[local] :
    (!x. (!y. y <> x ==> ~netord net y x \/ y NOTIN s) ==> x IN netlimits net) ==>
    netlimits (net within s) SUBSET netlimits net
Proof
    rpt STRIP_TAC
 >> simp [SUBSET_DEF, Once netlimits_def, WITHIN]
QED

Theorem NETLIMITS_WITHIN_lemma3[local] :
    (!x. (!y. y <> x ==> ~netord net y x \/ y NOTIN s) ==> x IN netlimits net) <=>
    (!x. x NOTIN netlimits net ==> ?y. y IN s /\ y <> x /\ netord net y x)
Proof
    METIS_TAC []
QED

(* NOTE: This definition is the exact condition for “NETLIMITS_WITHIN” to hold. *)
Definition net_condition_def :
    net_condition net s =
      !x. x NOTIN netlimits net ==> ?y. y IN s /\ y <> x /\ netord net y x
End

Theorem NET_CONDITION_MONO :
    !net s t. net_condition net s /\ s SUBSET t ==> net_condition net t
Proof
    rw [net_condition_def, SUBSET_DEF]
 >> METIS_TAC []
QED

Theorem NET_CONDITION_UNIV :
    !net. net_condition net UNIV
Proof
    rw [net_condition_def, netlimits_def]
QED

Theorem NETLIMITS_WITHIN :
    !net s. net_condition net s ==> netlimits (net within s) = netlimits net
Proof
    RW_TAC std_ss [net_condition_def]
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> REWRITE_TAC [NETLIMITS_WITHIN_lemma1]
 >> MATCH_MP_TAC NETLIMITS_WITHIN_lemma2
 >> ASM_REWRITE_TAC [NETLIMITS_WITHIN_lemma3]
QED

Theorem NET_CONDITION_ATPOINTOF :
    !m a s. a IN s ==> net_condition (atpointof m a) s
Proof
    rw [ATPOINTOF, net_condition_def, NETLIMITS_ATPOINTOF]
 >> Q.EXISTS_TAC ‘a’ >> simp [MDIST_REFL, MDIST_POS_LE]
QED

(* |- !a s. a IN s ==> net_condition (at a) s *)
Theorem NET_CONDITION_AT =
        NET_CONDITION_ATPOINTOF |> ISPEC “mr1” |> REWRITE_RULE [GSYM at_def]

Theorem NETLIMITS_ATPOINTOF_WITHIN :
    !m a s. a IN s ==> netlimits ((atpointof m a) within s) =
                       netlimits (atpointof m a)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC NETLIMITS_WITHIN
 >> MATCH_MP_TAC NET_CONDITION_ATPOINTOF >> art []
QED

(* |- !a s. a IN s ==> netlimits (at a within s) = netlimits (at a) *)
Theorem NETLIMITS_AT_WITHIN =
        NETLIMITS_ATPOINTOF_WITHIN |> ISPEC “mr1” |> REWRITE_RULE [GSYM at_def]

(* NOTE: added ‘a IN s’ to satisfy net_condition *)
Theorem NETLIMIT_WITHIN :
    !a s. a IN s ==> netlimit (at a within s) = a
Proof
    rpt STRIP_TAC
 >> ‘net_condition (at a) s’ by PROVE_TAC [NET_CONDITION_AT]
 >> simp [netlimit, NETLIMITS_WITHIN]
 >> REWRITE_TAC[GSYM netlimit]
 >> REWRITE_TAC[NETLIMIT_AT]
QED

(* ------------------------------------------------------------------------- *)
(* netfilter (compatible with HOL-Light)                                     *)
(* ------------------------------------------------------------------------- *)

(* NOTE: “x NOTIN netlimits net” is necessary for EVENTUALLY_ATPOINTOF below *)
Definition netfilter_def :
    netfilter net = {{y | netord net y x} | x | x NOTIN netlimits net}
End

(* NOTE: This is the theorem NET of HOL-Light *)
Theorem NETFILTER :
    !n s t. s IN netfilter n /\ t IN netfilter n ==> s INTER t IN netfilter n
Proof
    rpt GEN_TAC
 >> simp [netfilter_def]
 >> DISCH_THEN (CONJUNCTS_THEN2
                 (Q.X_CHOOSE_THEN ‘u’ STRIP_ASSUME_TAC)
                 (Q.X_CHOOSE_THEN ‘v’ STRIP_ASSUME_TAC))
 >> ‘s INTER t = {y | netord n y u /\ netord n y v}’ by ASM_SET_TAC []
 >> POP_ORW
 (* applying NET here! *)
 >> STRIP_ASSUME_TAC (Q.SPECL [‘n’, ‘u’, ‘v’] NET)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘u’ >> ASM_SET_TAC [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘v’ >> ASM_SET_TAC [] ]
QED

Theorem NETFILTER_AT_POSINFINITY :
    netfilter at_posinfinity = {{x | a <= x} | a IN univ(:real)}
Proof
    simp [netfilter_def, NETLIMITS_AT_POSINFINITY, AT_POSINFINITY, real_ge]
QED

Theorem NETFILTER_AT_NEGINFINITY :
    netfilter at_neginfinity = {{x | x <= a} | a IN univ(:real)}
Proof
    simp [netfilter_def, NETLIMITS_AT_NEGINFINITY, AT_NEGINFINITY]
QED

Theorem NETFILTER_AT_INFINITY :
    netfilter at_infinity = {{x | b <= abs x} | b IN univ(:real)}
Proof
    simp [netfilter_def, NETLIMITS_AT_INFINITY, AT_INFINITY, real_ge]
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
    simp [netfilter_def, NETLIMITS_SEQUENTIALLY, SEQUENTIALLY, GREATER_EQ, from_def]
QED

Theorem NETFILTER_ATPOINTOF :
    !m a. netfilter (atpointof m a) = {{y | dist m (y,a) <= dist m (x,a)} | x | x <> a}
Proof
    simp [netfilter_def, NETLIMITS_ATPOINTOF, ATPOINTOF, MDIST_POS_EQ]
QED

(* |- !a. netfilter (at a) = {{y | dist (y,a) <= dist (x,a)} | x | x <> a} *)
Theorem NETFILTER_AT =
        NETFILTER_ATPOINTOF |> ISPEC “mr1”
                            |> REWRITE_RULE [GSYM dist_def, GSYM at_def]

(* NOTE: This theorem is HOL-Light's WITHIN *)
Theorem NETFILTER_WITHIN :
    !net s. net_condition net s ==>
           (netfilter (net within s) = netfilter net relative_to s)
Proof
    rw [netfilter_def, WITHIN, RELATIVE_TO, NETLIMITS_WITHIN]
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- (rename1 ‘x NOTIN netlimits net’ \\
     Q.EXISTS_TAC ‘{y | netord net y x}’ \\
     reverse CONJ_TAC >- (Q.EXISTS_TAC ‘x’ >> art []) \\
     SET_TAC [])
 >> rename1 ‘x NOTIN netlimits net’
 >> Q.EXISTS_TAC ‘x’ >> art []
 >> SET_TAC []
QED

(* ------------------------------------------------------------------------- *)
(* Some property holds "sufficiently close" to the limit point (eventually). *)
(* ------------------------------------------------------------------------- *)
(* Identify trivial limits, where we can't approach arbitrarily closely.     *)
(* ------------------------------------------------------------------------- *)

(* old definitions:
Definition trivial_limit :
    trivial_limit net <=>
      (!(a:'a) b. a = b) \/
      ?(a:'a) b. ~(a = b) /\ !x. ~(netord(net) x a) /\ ~(netord(net) x b)
End

Definition eventually :
    eventually p net <=>
      trivial_limit net \/
      ?y. (?x. netord net x y) /\ (!x. netord net x y ==> p x)
End

   new definitions (compatible with HOL-Light):
 *)
Definition eventually :
    eventually (P :'a -> bool) net <=>
      netfilter net = {} \/
      ?u. u IN netfilter net /\ !x. x IN u DIFF netlimits net ==> P x
End

(* NOTE: This definition is "golden", should never be changed. *)
Definition trivial_limit :
    trivial_limit net = eventually (\x. F) net
End

Theorem NETFILTER_IMP_TRIVIAL_LIMIT :
    !net. netfilter net = {} ==> trivial_limit net
Proof
    rw [trivial_limit, eventually]
QED

Theorem TRIVIAL_LIMIT_IMP_NETFILTER[local] :
    !net. reflexive (netord net) ==> trivial_limit net ==> netfilter net = {}
Proof
    rw [trivial_limit, eventually]
 >> Q.PAT_X_ASSUM ‘u IN netfilter net’ (STRIP_ASSUME_TAC o SRULE [netfilter_def])
 >> Q.PAT_X_ASSUM ‘u = {y | netord net y x}’ (fs o wrap)
 >> Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘x’) >> simp []
 >> fs [reflexive_def]
QED

(* NOTE: ‘within’ nets are NOT reflexive. *)
Theorem trivial_limit_alt_netfilter :
    !net. reflexive (netord net) ==> (trivial_limit net <=> netfilter net = {})
Proof
    PROVE_TAC [NETFILTER_IMP_TRIVIAL_LIMIT, TRIVIAL_LIMIT_IMP_NETFILTER]
QED

(* NOTE: added “net_condition net s” after porting from HOL-Light *)
Theorem EVENTUALLY_WITHIN_IMP :
    !net (P:'a->bool) s. net_condition net s ==>
       (eventually P (net within s) <=>
        eventually (\x. x IN s ==> P x) net)
Proof
    rw [eventually, NETFILTER_WITHIN, RELATIVE_TO]
 >> ‘{s INTER s' | netfilter net s'} = {} <=> netfilter net = {}’ by SET_TAC []
 >> POP_ORW
 >> simp [NETLIMITS_WITHIN]
 >> Cases_on ‘netfilter net = {}’ >> simp []
 >> EQ_TAC >> rw []
 >- (rename1 ‘netfilter net t’ \\
    ‘t IN netfilter net’ by simp [IN_APP] \\
     Q.EXISTS_TAC ‘t’ >> rw [])
 >> Q.EXISTS_TAC ‘s INTER u’
 >> reverse CONJ_TAC >- rw []
 >> Q.EXISTS_TAC ‘u’ >> art []
 >> FULL_SIMP_TAC bool_ss [IN_APP]
QED

(* NOTE: added “net_condition net s” after porting from HOL-Light *)
Theorem EVENTUALLY_IMP_WITHIN :
    !net (P:'a->bool) s. net_condition net s /\
        eventually P net ==> eventually P (net within s)
Proof
    rw [EVENTUALLY_WITHIN_IMP]
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [eventually]
 >> MESON_TAC []
QED

(* NOTE: added “net_condition (net within s) t” after porting from HOL-Light *)
Theorem EVENTUALLY_WITHIN_INTER_IMP :
    !net (P:'a->bool) s t. net_condition (net within s) t ==>
       (eventually P (net within s INTER t) <=>
        eventually (\x. x IN t ==> P x) (net within s))
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [GSYM WITHIN_WITHIN]
 >> simp [EVENTUALLY_WITHIN_IMP]
QED

(* NOTE: added “net_condition net s” *)
Theorem NONTRIVIAL_LIMIT_WITHIN :
    !net s. net_condition net s /\ trivial_limit net ==> trivial_limit(net within s)
Proof
    rw [trivial_limit]
 >> simp [EVENTUALLY_IMP_WITHIN]
QED

Theorem EVENTUALLY_HAPPENS :
    !net p. eventually p net ==> trivial_limit net \/ ?x. p x
Proof
  REWRITE_TAC[trivial_limit, eventually] THEN SET_TAC[]
QED

Theorem ALWAYS_EVENTUALLY :
    !net p. (!x. p x) ==> eventually p net
Proof
  SIMP_TAC std_ss[eventually] THEN SET_TAC[]
QED

Theorem EVENTUALLY_MONO :
    !net:('a net) p q.
        (!x. p x ==> q x) /\ eventually p net
        ==> eventually q net
Proof
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_AND :
    !net:('a net) p q.
        eventually (\x. p x /\ q x) net <=>
        eventually p net /\ eventually q net
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [ (* goal 1 (of 2) *)
    DISCH_THEN(fn th => CONJ_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    SIMP_TAC bool_ss [],
    (* goal 2 (of 2) *)
    REWRITE_TAC[eventually] THEN
    ASM_CASES_TAC ``netfilter(net:'a net) = {}`` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN ``u:'a->bool`` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN ``v:'a->bool`` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC ``u INTER v:'a->bool`` THEN
    ASM_SIMP_TAC std_ss [IN_INTER, NETFILTER] THEN ASM_SET_TAC[] ]
QED

Theorem EVENTUALLY_MP :
    !net:('a net) p q.
        eventually (\x. p x ==> q x) net /\ eventually p net
        ==> eventually q net
Proof
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_EQ_MP :
    !net P Q. eventually (\x:'a. P x <=> Q x) net /\ eventually P net
             ==> eventually Q net
Proof
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘eventually P net’ MP_TAC
 >> MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP)
 >> POP_ASSUM MP_TAC
 >> MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP)
 >> MATCH_MP_TAC ALWAYS_EVENTUALLY
 >> SIMP_TAC bool_ss []
QED

Theorem EVENTUALLY_IFF :
    !net P Q. eventually (\x:'a. P x <=> Q x) net
             ==> (eventually P net <=> eventually Q net)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  (MATCH_MP_TAC o REWRITE_RULE[IMP_CONJ]) EVENTUALLY_EQ_MP THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  ASM_REWRITE_TAC[]
QED

Theorem EVENTUALLY_FALSE :
    !net. eventually (\x. F) net <=> trivial_limit net
Proof
  REWRITE_TAC[trivial_limit]
QED

Theorem EVENTUALLY_TRUE :
    !net. eventually (\x. T) net <=> T
Proof
  REWRITE_TAC[eventually] THEN SET_TAC[]
QED

(* NOTE: added “net_condition net s /\ net_condition net t” after porting from HOL-Light *)
Theorem EVENTUALLY_WITHIN_SUBSET :
    !P net s t:'a->bool. net_condition net t /\
       eventually P (net within s) /\ t SUBSET s ==> eventually P (net within t)
Proof
    rpt STRIP_TAC
 >> ‘net_condition net s’ by PROVE_TAC [NET_CONDITION_MONO]
 >> Q.PAT_X_ASSUM ‘eventually P (net within s)’ MP_TAC
 >> simp [EVENTUALLY_WITHIN_IMP]
 >> MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO)
 >> ASM_SET_TAC[]
QED

(* NOTE: added “net_condition net s” after porting from HOL-Light *)
Theorem ALWAYS_WITHIN_EVENTUALLY :
    !net P. net_condition net s /\ (!x. x IN s ==> P x) ==> eventually P (net within s)
Proof
    rpt STRIP_TAC
 >> simp [EVENTUALLY_WITHIN_IMP, EVENTUALLY_TRUE]
QED

Theorem NOT_EVENTUALLY :
    !net p. (!x. ~(p x)) /\ ~(trivial_limit net) ==> ~(eventually p net)
Proof
  REWRITE_TAC[eventually, trivial_limit] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_FORALL :
    !net:('a net) p s:'b->bool.
        FINITE s /\ ~(s = {})
        ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
             !a. a IN s ==> eventually (p a) net)
Proof
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC bool_ss [FORALL_IN_INSERT, EVENTUALLY_AND] THEN
  MAP_EVERY X_GEN_TAC [``b:'b``, ``t:'b->bool``] THEN
  ASM_CASES_TAC ``t:'b->bool = {}`` THEN
  ASM_SIMP_TAC bool_ss [NOT_IN_EMPTY, EVENTUALLY_TRUE] THEN
  METIS_TAC []
QED

Theorem FORALL_EVENTUALLY :
    !net:('a net) p s:'b->bool.
        FINITE s /\ ~(s = {})
        ==> ((!a. a IN s ==> eventually (p a) net) <=>
             eventually (\x. !a. a IN s ==> p a x) net)
Proof
  SIMP_TAC bool_ss [EVENTUALLY_FORALL]
QED

Theorem EVENTUALLY_TRIVIAL :
    !net P:'a->bool. trivial_limit net ==> eventually P net
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[trivial_limit] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REWRITE_TAC[]
QED

Theorem EVENTUALLY_SEQUENTIALLY :
    !p. eventually p sequentially <=> ?N. !n. N <= n ==> p n
Proof
  REWRITE_TAC[eventually, NETFILTER_SEQUENTIALLY, NETLIMITS_SEQUENTIALLY] THEN
  SIMP_TAC bool_ss [SIMPLE_IMAGE, EXISTS_IN_IMAGE, IMAGE_EQ_EMPTY, UNIV_NOT_EMPTY] THEN
  rw [IN_UNIV, INTERS_IMAGE, IN_FROM, IN_DIFF, NOT_IN_EMPTY]
QED

Theorem TRIVIAL_LIMIT_SEQUENTIALLY :
    ~(trivial_limit sequentially)
Proof
  REWRITE_TAC[trivial_limit, EVENTUALLY_SEQUENTIALLY] THEN
  MESON_TAC[LE_REFL]
QED

Theorem EVENTUALLY_HAPPENS_SEQUENTIALLY :
    !P. eventually P sequentially ==> ?n. P n
Proof
  MESON_TAC[EVENTUALLY_HAPPENS, TRIVIAL_LIMIT_SEQUENTIALLY]
QED

(* NOTE: added “net_condition sequentially k” after porting from HOL-Light

   But to satisfy “net_condition sequentially k”, k cannot be finite...
 *)
Theorem EVENTUALLY_SEQUENTIALLY_WITHIN :
    !k p. net_condition sequentially k ==>
         (eventually p (sequentially within k) <=>
          FINITE k \/ (?N. !n. n IN k /\ N <= n ==> p n))
Proof
  rpt STRIP_TAC THEN
  simp [EVENTUALLY_WITHIN_IMP, EVENTUALLY_SEQUENTIALLY] THEN
  ASM_CASES_TAC ``FINITE (k:num->bool)`` THEN ASM_REWRITE_TAC[] THENL
  [POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[num_FINITE]) THEN
   EXISTS_TAC ``a + (1 :num)`` THEN
   REWRITE_TAC[ARITH_PROVE ``a + 1 <= n <=> a < n:num``] THEN
   ASM_MESON_TAC[NOT_LE],
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC[num_INFINITE_EQ] THEN
   MESON_TAC[]]
QED

Theorem TRIVIAL_LIMIT_SEQUENTIALLY_WITHIN :
    !k. net_condition sequentially k ==>
       (trivial_limit (sequentially within k) <=> FINITE k)
Proof
  rpt STRIP_TAC THEN REWRITE_TAC[trivial_limit] THEN
  simp [EVENTUALLY_SEQUENTIALLY_WITHIN] THEN
  ASM_CASES_TAC ``FINITE (k:num->bool)`` THEN ASM_REWRITE_TAC[] THEN
  simp [NOT_EXISTS_THM, NOT_FORALL_THM] THEN GEN_TAC THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE[num_INFINITE_EQ]) THEN
  MESON_TAC[]
QED

Theorem EVENTUALLY_SUBSEQUENCE :
    !P r. (!m n. m < n ==> r m < r n) /\ eventually P sequentially
         ==> eventually (P o r) sequentially
Proof
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY, o_THM] THEN
  MESON_TAC[MONOTONE_BIGGER, LE_TRANS]
QED

(* ------------------------------------------------------------------------- *)
(* Within "empty" - no need for net_condition                                *)
(* ------------------------------------------------------------------------- *)

Theorem WITHIN_EMPTY :
    !net. netord (net within {}) x y <=> F
Proof
    rw [WITHIN]
QED

Theorem NETLIMITS_WITHIN_EMPTY :
    !net. netlimits (net within {}) = UNIV
Proof
    rw [netlimits_def, WITHIN_EMPTY]
QED

Theorem NETFILTER_WITHIN_EMPTY :
    !net. netfilter (net within {}) = {}
Proof
    rw [netfilter_def, NETLIMITS_WITHIN_EMPTY]
QED

Theorem EVENTUALLY_WITHIN_EMPTY :
    !net p. eventually p (net within {})
Proof
    rw [eventually, NETFILTER_WITHIN_EMPTY]
QED

Theorem TRIVIAL_LIMIT_WITHIN_EMPTY :
    !net. trivial_limit (net within {})
Proof
    rw [trivial_limit, EVENTUALLY_WITHIN_EMPTY]
QED

(* ------------------------------------------------------------------------- *)
(* Limits at a point in a topological (metric in HOL4) space                 *)
(* ------------------------------------------------------------------------- *)

(* NOTE: recall that “netfilter net = {}” is the 1st part of “eventually” *)
Theorem NETFILTER_EQ_EMPTY :
    !net. netfilter net = {} <=> netlimits net = UNIV
Proof
    rw [netfilter_def, Once EXTENSION, NOT_IN_EMPTY]
 >> simp [Once EXTENSION]
QED

Theorem NETFILTER_ATPOINTOF_EQ_EMPTY :
    !m a. netfilter (atpointof m a) = {} <=> !x. x = a
Proof
    rw [NETFILTER_ATPOINTOF, Once EXTENSION, NOT_IN_EMPTY]
QED

(* NOTE: HOL-Light's “atpointof top a” becomes HOL4's “atpointof m a”. *)
Theorem EVENTUALLY_ATPOINTOF_IMP :
    !P m (a:'a).
        eventually P (atpointof m a) ==>
        ?u. open_in (mtop m) u /\ a IN u /\ !x. x IN u DELETE a ==> P x
Proof
    rpt GEN_TAC
 >> simp [eventually, NETLIMITS_ATPOINTOF]
 (* special case: there's only one value in type alpha *)
 >> Cases_on ‘!y. y = a’
 >- (‘netfilter (atpointof m a) = {}’
       by PROVE_TAC [NETFILTER_ATPOINTOF_EQ_EMPTY] >> simp [] \\
     Q.EXISTS_TAC ‘{a}’ >> simp [] \\
     rw [MTOP_OPEN'] \\
     Q.EXISTS_TAC ‘1’ >> simp [])
 >> FULL_SIMP_TAC bool_ss [NETFILTER_ATPOINTOF] (* this asserts ‘y <> a’ *)
 >> Know ‘{{y | dist m (y,a) <= dist m (x,a)} | x | x <> a} <> {}’
 >- (rw [Once EXTENSION, NOT_IN_EMPTY] \\
     Q.EXISTS_TAC ‘y’ >> art [])
 >> Rewr
 >> simp [EXISTS_IN_GSPEC]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘z’ STRIP_ASSUME_TAC)
 >> qabbrev_tac ‘r = dist m (z,a)’
 >> ‘0 < r’ by simp [Abbr ‘r’, MDIST_POS_LT]
 >> Q.EXISTS_TAC ‘mball m (a,r)’
 >> rw [OPEN_IN_MBALL, IN_MBALL, MSPACE, MDIST_REFL]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> simp [Once MDIST_SYM]
QED

(* NOTE: added “limpt (mtop m) a UNIV” to finish the proof (direction: right to left) *)
Theorem EVENTUALLY_ATPOINTOF :
    !P m (a:'a). limpt (mtop m) a UNIV ==>
       (eventually P (atpointof m a) <=>
        ?u. open_in (mtop m) u /\ a IN u /\ !x. x IN u DELETE a ==> P x)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [EVENTUALLY_ATPOINTOF_IMP]
 >> simp [eventually, NETLIMITS_ATPOINTOF]
 (* special case: there's only one value in type alpha *)
 >> Cases_on ‘!y. y = a’
 >- (‘netfilter (atpointof m a) = {}’
       by PROVE_TAC [NETFILTER_ATPOINTOF_EQ_EMPTY] >> simp [] \\
     Q.EXISTS_TAC ‘{a}’ >> simp [] \\
     rw [MTOP_OPEN'] \\
     Q.EXISTS_TAC ‘1’ >> simp [])
 >> FULL_SIMP_TAC bool_ss [NETFILTER_ATPOINTOF] (* this asserts ‘y <> a’ *)
 >> Know ‘{{y | dist m (y,a) <= dist m (x,a)} | x | x <> a} <> {}’
 >- (rw [Once EXTENSION, NOT_IN_EMPTY] \\
     Q.EXISTS_TAC ‘y’ >> art [])
 >> Rewr
 >> simp [EXISTS_IN_GSPEC]
 >> STRIP_TAC
 >> fs [MTOP_OPEN']
 >> Q.PAT_X_ASSUM ‘!x. x IN u ==> ?e. _’ (MP_TAC o Q.SPEC ‘a’) >> rw []
 (* using extra antecedents *)
 >> fs [MTOP_LIMPT']
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?y. _’ (MP_TAC o Q.SPEC ‘e’) >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘z’ STRIP_ASSUME_TAC)
 >> Q.EXISTS_TAC ‘z’ >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘dist m (a,z)’ >> art []
 >> ONCE_REWRITE_TAC [MDIST_SYM] >> art []
QED

Theorem ATPOINTOF_WITHIN_TOPSPACE :
    !m (a:'a). ((atpointof m a) within (topspace (mtop m))) = atpointof m a
Proof
    simp [NET_WITHIN_UNIV, TOPSPACE_MTOP]
QED

(* NOTE: added “a IN s /\ limpt (mtop m) a univ(:'a)” needed by some lemmas *)
Theorem TRIVIAL_LIMIT_ATPOINTOF_WITHIN :
    !m s (a:'a). a IN s /\ limpt (mtop m) a univ(:'a) ==>
       (trivial_limit(atpointof m a within s) <=>
        ~(a IN (mtop m) derived_set_of s))
Proof
    rpt STRIP_TAC
 >> ‘net_condition (atpointof m a) s’ by PROVE_TAC [NET_CONDITION_ATPOINTOF]
 >> simp [trivial_limit, EVENTUALLY_WITHIN_IMP]
 >> ASM_SIMP_TAC bool_ss [EVENTUALLY_ATPOINTOF]
 >> simp [derived_set_of, TOPSPACE_MTOP]
 >> SET_TAC []
QED

(* |- !m s a.
        a IN s /\ limpt (mtop m) a univ(:'a) ==>
        (trivial_limit (atpointof m a within s) <=> ~limpt (mtop m) a s)
 *)
Theorem TRIVIAL_LIMIT_ATPOINTOF_WITHIN' =
        TRIVIAL_LIMIT_ATPOINTOF_WITHIN |> SRULE [derived_set_of_alt_limpt]

(* |- !s a.
        a IN s ==>
        (trivial_limit (at a within s) <=>
         a NOTIN mtop mr1 derived_set_of s)
 *)
Theorem TRIVIAL_LIMIT_AT_WITHIN =
        TRIVIAL_LIMIT_ATPOINTOF_WITHIN |> ISPEC “mr1” |> SRULE [MR1_LIMPT, GSYM at_def]

Theorem DERIVED_SET_OF_TRIVIAL_LIMIT :
    !m s (a:'a). a IN s /\ limpt (mtop m) a univ(:'a) ==>
      (a IN (mtop m) derived_set_of s <=> ~trivial_limit(atpointof m a within s))
Proof
    PROVE_TAC[TRIVIAL_LIMIT_ATPOINTOF_WITHIN]
QED

Theorem TRIVIAL_LIMIT_ATPOINTOF :
    !m (a:'a). limpt (mtop m) a univ(:'a) ==>
       (trivial_limit(atpointof m a) <=>
        ~(a IN (mtop m) derived_set_of topspace (mtop m)))
Proof
    ONCE_REWRITE_TAC[GSYM ATPOINTOF_WITHIN_TOPSPACE]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC TRIVIAL_LIMIT_ATPOINTOF_WITHIN
 >> simp [TOPSPACE_MTOP]
QED

(* |- !m a. limpt (mtop m) a univ(:'a) ==> ~trivial_limit (atpointof m a) *)
Theorem TRIVIAL_LIMIT_ATPOINTOF' =
        TRIVIAL_LIMIT_ATPOINTOF |> SRULE [derived_set_of_alt_limpt, TOPSPACE_MTOP]

(* |- !a. ~trivial_limit (at a) *)
Theorem TRIVIAL_LIMIT_AT =
        TRIVIAL_LIMIT_ATPOINTOF' |> ISPEC “mr1” |> SRULE [MR1_LIMPT, GSYM at_def]

(* NOTE: added “limpt (mtop m) a univ(:'a)” needed by some lemmas *)
Theorem EVENTUALLY_ATPOINTOF_METRIC :
    !P m (a:'a). limpt (mtop m) a univ(:'a) ==>
       (eventually P (atpointof m a) <=>
        a IN mspace m
        ==> ?d. &0 < d /\
                !x. x IN mspace m /\ &0 < mdist m (x,a) /\ mdist m (x,a) < d
                    ==> P x)
Proof
    rpt STRIP_TAC
 >> simp [EVENTUALLY_ATPOINTOF, MSPACE]
 >> EQ_TAC
 >- (STRIP_TAC \\
     fs [OPEN_IN_MTOPOLOGY] \\
     Q.PAT_X_ASSUM ‘!x. x IN u ==> ?r. 0 < r /\ _’ (MP_TAC o Q.SPEC ‘a’) >> simp [] \\
     rw [IMP_CONJ, MDIST_POS_EQ, IN_MBALL, SUBSET_DEF, Once MDIST_SYM, MSPACE] \\
     ASM_SET_TAC [])
 >> rw [IMP_CONJ, MDIST_POS_EQ]
 >> EXISTS_TAC ``mball m (a:'a,d)``
 >> simp [OPEN_IN_MBALL, CENTRE_IN_MBALL, IN_DELETE, MSPACE]
 >> simp [IN_MBALL, MSPACE]
 >> ASM_MESON_TAC [MDIST_SYM]
QED

(* |- !P m a.
        limpt (mtop m) a univ(:'a) ==>
        (eventually P (atpointof m a) <=>
         ?d. 0 < d /\ !x. 0 < dist m (x,a) /\ dist m (x,a) < d ==> P x)
 *)
Theorem EVENTUALLY_ATPOINTOF_METRIC' =
        EVENTUALLY_ATPOINTOF_METRIC |> SRULE [MSPACE]

(* ------------------------------------------------------------------------- *)
(* The "eventually" property in Euclidean space.                             *)
(* ------------------------------------------------------------------------- *)

(* NOTE: added ‘a IN s’ for needed lemmas *)
Theorem EVENTUALLY_WITHIN :
    !s a p. a IN s ==>
       (eventually p (at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d ==> p(x))
Proof
    rpt STRIP_TAC
 >> Know ‘net_condition (at a) s’
 >- (MATCH_MP_TAC NET_CONDITION_AT >> art [])
 >> DISCH_TAC
 >> simp [at_def, EVENTUALLY_WITHIN_IMP, dist_def]
 >> qabbrev_tac ‘P = \x. x IN s ==> p x’
 >> Know ‘eventually P (atpointof mr1 a) <=>
          ?d. 0 < d /\ !x. 0 < dist mr1 (x,a) /\ dist mr1 (x,a) < d ==> P x’
 >- (MATCH_MP_TAC EVENTUALLY_ATPOINTOF_METRIC' \\
     REWRITE_TAC [MR1_LIMPT])
 >> Rewr'
 >> simp [GSYM dist_def, Abbr ‘P’]
 >> MESON_TAC []
QED

(* |- !a p.
        eventually p (at a) <=>
        ?d. 0 < d /\ !x. 0 < dist (x,a) /\ dist (x,a) < d ==> p x
 *)
Theorem EVENTUALLY_AT =
        EVENTUALLY_WITHIN |> Q.SPEC ‘UNIV’ |> SRULE [NET_WITHIN_UNIV]

Theorem lemma[local]:
   &0 < d:real ==> x <= d / &2 ==> x < d
Proof
 SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_LT] THEN REAL_ARITH_TAC
QED

Theorem APPROACHABLE_LT_LE:
   !P f. (?d:real. &0 < d /\ !x. f(x) < d ==> P x) =
         (?d:real. &0 < d /\ !x. f(x) <= d ==> P x)
Proof
  MESON_TAC[REAL_LT_IMP_LE, lemma, REAL_LT_HALF1]
QED

Theorem EVENTUALLY_WITHIN_LE :
    !s a p. a IN s ==>
       (eventually p (at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d ==> p(x))
Proof
    rpt STRIP_TAC
 >> simp [EVENTUALLY_WITHIN]
 >> ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`]
 >> simp [APPROACHABLE_LT_LE]
QED

Theorem EVENTUALLY_AT_INFINITY :
    !p. eventually p at_infinity <=> ?b. !x. abs(x) >= b ==> p x
Proof
  REWRITE_TAC[eventually, NETFILTER_AT_INFINITY, NETLIMITS_AT_INFINITY] THEN
  SIMP_TAC bool_ss[EXISTS_IN_GSPEC, real_ge] THEN
  SIMP_TAC bool_ss[SET_RULE ``~({f x | x IN UNIV} = {})``] THEN
  simp []
QED

Theorem EVENTUALLY_AT_INFINITY_WITHIN :
    !p s. net_condition at_infinity s ==>
       (eventually p (at_infinity within s) <=>
        ?b. !x. x IN s /\ abs(x) >= b ==> p x)
Proof
    rpt STRIP_TAC
 >> simp [EVENTUALLY_WITHIN_IMP, EVENTUALLY_AT_INFINITY]
 >> MESON_TAC[]
QED

Theorem EVENTUALLY_AT_INFINITY_POS :
    !p. eventually p at_infinity <=> ?b. &0 < b /\ !x. abs x >= b ==> p x
Proof
  GEN_TAC THEN REWRITE_TAC[EVENTUALLY_AT_INFINITY, real_ge] THEN
  MESON_TAC[REAL_ARITH ``&0 < abs b + &1 /\ (abs b + &1 <= x ==> b <= x)``]
QED

Theorem TRIVIAL_LIMIT_AT_INFINITY :
    ~(trivial_limit at_infinity)
Proof
  REWRITE_TAC[trivial_limit, EVENTUALLY_AT_INFINITY, real_ge] THEN
  MESON_TAC[REAL_CHOOSE_SIZE, REAL_ARITH
    ``&0 <= abs b + &1 /\ b <= abs b + &1 /\ ~(abs b + &2 <= abs b + &1)``]
QED

Theorem EVENTUALLY_AT_POSINFINITY :
    !p. eventually p at_posinfinity <=> ?b. !x. x >= b ==> p x
Proof
  REWRITE_TAC[eventually, NETFILTER_AT_POSINFINITY, NETLIMITS_AT_POSINFINITY] THEN
  SIMP_TAC bool_ss[EXISTS_IN_GSPEC, real_ge] THEN
  SIMP_TAC bool_ss[SET_RULE ``~({f x | x IN UNIV} = {})``] THEN
  simp []
QED

Theorem TRIVIAL_LIMIT_AT_POSINFINITY :
    ~(trivial_limit at_posinfinity)
Proof
  REWRITE_TAC[EVENTUALLY_AT_POSINFINITY, trivial_limit, real_ge] THEN
  MESON_TAC[REAL_ARITH ``~(x + &1 <= x)``, REAL_LE_REFL]
QED

Theorem EVENTUALLY_AT_NEGINFINITY :
    !p. eventually p at_neginfinity <=> ?b. !x. x <= b ==> p x
Proof
  REWRITE_TAC[eventually, NETFILTER_AT_NEGINFINITY, NETLIMITS_AT_NEGINFINITY] THEN
  SIMP_TAC bool_ss[EXISTS_IN_GSPEC, real_ge] THEN
  SIMP_TAC bool_ss[SET_RULE ``~({f x | x IN UNIV} = {})``] THEN
  simp []
QED

Theorem TRIVIAL_LIMIT_AT_NEGINFINITY :
    ~(trivial_limit at_neginfinity)
Proof
  REWRITE_TAC[EVENTUALLY_AT_NEGINFINITY, trivial_limit, real_ge] THEN
  MESON_TAC[REAL_ARITH ``~(x <= x - &1)``, REAL_LE_REFL]
QED

(* ------------------------------------------------------------------------- *)
(* Limits in a topological space (from HOL-Light's Multivariate/metric.ml)   *)
(* ------------------------------------------------------------------------- *)

Definition limit :
   limit top (f:'a->'b) l net <=>
     l IN topspace top /\
     (!u. open_in top u /\ l IN u ==> eventually (\x. f x IN u) net)
End

Theorem LIMIT_IMP_WITHIN :
    !net top (f:'a->'b) l s. net_condition net s /\
        limit top f l net ==> limit top f l (net within s)
Proof
    RW_TAC std_ss [limit]
 >> MATCH_MP_TAC EVENTUALLY_IMP_WITHIN >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem LIMIT_IN_TOPSPACE :
    !net top f:'a->'b l. limit top f l net ==> l IN topspace top
Proof
  SIMP_TAC bool_ss [limit]
QED

Theorem LIMIT_CONST :
    !top net:'a net l:'b. limit top (\a. l) l net <=> l IN topspace top
Proof
  SIMP_TAC bool_ss [limit, EVENTUALLY_TRUE]
QED

Theorem LIMIT_REAL_CONST :
   !net:'a net l. limit (mtop mr1) (\a. l) l net
Proof
  REWRITE_TAC[LIMIT_CONST, TOPSPACE_MTOP, IN_UNIV]
QED

Theorem LIMIT_EVENTUALLY :
    !net top (f:'a->'b) l.
        l IN topspace top /\ eventually (\x. f x = l) net
        ==> limit top f l net
Proof
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[limit] THEN
  GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] EVENTUALLY_MONO)) THEN
  ASM_SIMP_TAC std_ss []
QED

(* NOTE: added “net_condition net t” after ported from HOL-Light. *)
Theorem LIMIT_WITHIN_SUBSET :
    !net top (f:'a->'b) l s t. net_condition net t /\
        limit top f l (net within s) /\ t SUBSET s
        ==> limit top f l (net within t)
Proof
    RW_TAC std_ss [limit]
 >> ‘net_condition net s’ by PROVE_TAC [NET_CONDITION_MONO]
 >> MATCH_MP_TAC EVENTUALLY_WITHIN_SUBSET
 >> Q.EXISTS_TAC ‘s’ >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(*
let LIMIT_SEQUENTIALLY = prove
 (`!top s l:A.
     limit top s l sequentially <=>
     l IN topspace top /\
     (!u. open_in top u /\ l IN u ==> (?N. !n. N <= n ==> s n IN u))`,
  REWRITE_TAC[limit; EVENTUALLY_SEQUENTIALLY]);;

let LIMIT_SEQUENTIALLY_OFFSET = prove
 (`!top f l:A k. limit top f l sequentially
                 ==> limit top (\i. f (i + k)) l sequentially`,
  SIMP_TAC[LIMIT_SEQUENTIALLY] THEN INTRO_TAC "! *; l lim; !u; hp" THEN
  USE_THEN "hp" (HYP_TAC "lim: @N. N" o C MATCH_MP) THEN
  EXISTS_TAC `N:num` THEN INTRO_TAC "!n; n" THEN
  USE_THEN "N" MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let LIMIT_SEQUENTIALLY_OFFSET_REV = prove
 (`!top f l:A k. limit top (\i. f (i + k)) l sequentially
                 ==> limit top f l sequentially`,
  SIMP_TAC[LIMIT_SEQUENTIALLY] THEN INTRO_TAC "! *; l lim; !u; hp" THEN
  USE_THEN "hp" (HYP_TAC "lim: @N. N" o C MATCH_MP) THEN
  EXISTS_TAC `N+k:num` THEN INTRO_TAC "!n; n" THEN
  REMOVE_THEN "N" (MP_TAC o SPEC `n-k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n - k + k = n:num` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let LIMIT_ATPOINTOF = prove
 (`!top top' f:A->B x y.
        limit top' f y (atpointof top x) <=>
        y IN topspace top' /\
        (x IN topspace top
         ==> !v. open_in top' v /\ y IN v
                 ==> ?u. open_in top u /\ x IN u /\
                         IMAGE f (u DELETE x) SUBSET v)`,
  REPEAT GEN_TAC THEN ASM_SIMP_TAC[limit; EVENTUALLY_ATPOINTOF] THEN
  ASM_CASES_TAC `(y:B) IN topspace top'` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:A) IN topspace top` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN SET_TAC[]);;

let LIMIT_ATPOINTOF_SELF = prove
 (`!top1 top2 f:A->B a.
        limit top2 f (f a) (atpointof top1 a) <=>
        f a IN topspace top2 /\
        (a IN topspace top1
         ==> (!v. open_in top2 v /\ f a IN v
                  ==> (?u. open_in top1 u /\ a IN u /\ IMAGE f u SUBSET v)))`,
  REWRITE_TAC[LIMIT_ATPOINTOF] THEN SET_TAC[]);;
 *)
 
Theorem LIMIT_TRIVIAL :
    !net f:'a->'b top y.
        trivial_limit net /\ y IN topspace top ==> limit top f y net
Proof
  SIMP_TAC std_ss[limit, EVENTUALLY_TRIVIAL]
QED

Theorem LIMIT_HAUSDORFF_UNIQUE :
  !net top (f:'a->'b) l1 l2.
     ~trivial_limit net /\
     hausdorff_space top /\
     limit top f l1 net /\
     limit top f l2 net
     ==> l1 = l2
Proof
    REWRITE_TAC[limit, hausdorff_space]
 >> rpt STRIP_TAC
 >> CCONTR_TAC
 >> Q.PAT_X_ASSUM ‘!x y. _’ (MP_TAC o Q.SPECL [‘l1’, ‘l2’])
 >> simp [NOT_EXISTS_THM]
 >> rpt GEN_TAC
 >> Suff `open_in top u /\ open_in top v /\ l1 IN u /\ l2 IN v
           ==> ?x. f x IN u /\ f x IN v` >- SET_TAC []
 >> STRIP_TAC
 >> `eventually (\x. f x IN u /\ f x IN v) net` by ASM_SIMP_TAC std_ss [EVENTUALLY_AND]
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP EVENTUALLY_HAPPENS))
 >> ASM_MESON_TAC[]
QED

Theorem HAUSDORFF_SPACE_MTOPOLOGY :
    !m:'a metric. hausdorff_space(mtopology m)
Proof
  REWRITE_TAC[hausdorff_space, TOPSPACE_MTOPOLOGY] THEN
  MAP_EVERY X_GEN_TAC [``m:'a metric``, ``x:'a``, ``y:'a``] THEN STRIP_TAC THEN
  EXISTS_TAC ``mball m (x:'a,mdist m (x,y) / &2)`` THEN
  EXISTS_TAC ``mball m (y:'a,mdist m (x,y) / &2)`` THEN
  REWRITE_TAC[SET_RULE ``DISJOINT s t <=> !x. x IN s /\ x IN t ==> F``] THEN
  REWRITE_TAC[OPEN_IN_MBALL, IN_MBALL] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
 (* CONV_TAC METRIC_ARITH *)
    simp [MSPACE, MDIST_REFL]
 >> DISCH_TAC (* x <> y *)
 >> simp [MDIST_POS_LT, REAL_LT_DIV]
 >> Q.X_GEN_TAC ‘z’
 >> simp [REAL_NOT_LT]
 >> MP_TAC (Q.SPECL [‘m’, ‘x’, ‘z’, ‘y’] MDIST_TRIANGLE)
 >> qabbrev_tac ‘a = dist m (x,y)’
 >> qabbrev_tac ‘b = dist m (x,z)’
 >> simp [Once MDIST_SYM]
 >> qabbrev_tac ‘c = dist m (y,z)’
 >> RealField.REAL_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Topological limit in metric spaces.                                       *)
(* ------------------------------------------------------------------------- *)

Theorem LIMIT_IN_MSPACE :
    !net m f:'a->'b l. limit (mtopology m) f l net ==> l IN mspace m
Proof
  MESON_TAC[LIMIT_IN_TOPSPACE, TOPSPACE_MTOPOLOGY]
QED

Theorem LIMIT_METRIC_UNIQUE :
  !net m f:'a->'b l1 l2.
     ~trivial_limit net /\
     limit (mtopology m) f l1 net /\
     limit (mtopology m) f l2 net
     ==> l1 = l2
Proof
  MESON_TAC[LIMIT_HAUSDORFF_UNIQUE, HAUSDORFF_SPACE_MTOPOLOGY]
QED

Theorem LIMIT_METRIC :
  !m f:'a->'b l net.
     limit (mtopology m) f l net <=>
     l IN mspace m /\
     (!e. &0 < e
          ==> eventually (\x. f x IN mspace m /\ mdist m (f x, l) < e) net)
Proof
    rpt GEN_TAC
 >> REWRITE_TAC[limit, OPEN_IN_MTOPOLOGY, TOPSPACE_MTOPOLOGY]
 >> EQ_TAC
 >- (rw [MSPACE] \\
     Q.PAT_X_ASSUM ‘!u. _’ (MP_TAC o Q.SPEC ‘mball m (l,e)’) \\
     simp [CENTRE_IN_MBALL, MSPACE] \\
     simp [IN_MBALL, MSPACE, MDIST_REFL] \\
     impl_tac
     >- (rpt STRIP_TAC \\
         Q.EXISTS_TAC ‘e - mdist m (l,x)’ \\
         CONJ_TAC >- REAL_ASM_ARITH_TAC \\
         simp [SUBSET_DEF, IN_MBALL, MSPACE] \\
         Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
         Q_TAC (TRANS_TAC REAL_LET_TRANS) `mdist m (l,x) + mdist m (x,y)` \\
         ASM_SIMP_TAC std_ss [MDIST_TRIANGLE] \\
         REAL_ASM_ARITH_TAC) \\
     simp [Once MDIST_SYM])
 >> rw [MSPACE]
 >> MATCH_MP_TAC EVENTUALLY_MONO
 >> Q.PAT_X_ASSUM ‘!x. x IN u ==> _’ (MP_TAC o Q.SPEC ‘l’) >> rw []
 >> Q.EXISTS_TAC ‘\x. dist m (f x,l) < r’ >> rw []
 >> Q.PAT_X_ASSUM ‘_ SUBSET u’ MP_TAC >> rw [SUBSET_DEF]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> rw [IN_MBALL, MSPACE, Once MDIST_SYM]
QED

Theorem LIMIT_METRIC_SEQUENTIALLY :
  !m f:num->'a l.
     limit (mtopology m) f l sequentially <=>
     l IN mspace m /\
     (!e. &0 < e ==> (?N. !n. N <= n
                              ==> f n IN mspace m /\ mdist m (f n,l) < e))
Proof
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [LIMIT_METRIC, EVENTUALLY_SEQUENTIALLY]
QED

(* ------------------------------------------------------------------------- *)
(* Combining theorems for real limits.                                       *)
(* ------------------------------------------------------------------------- *)

Theorem REAL_HALF :
   (!e. &0 < e / &2 <=> &0 < e) /\
   (!e. e / &2 + e / &2 = e) /\
   (!e. &2 * (e / &2) = e)
Proof
  REAL_ARITH_TAC
QED

Theorem LIMIT_REAL_MUL :
    !(net:'a net) f g l m.
        limit (mtop mr1) f l net /\ limit (mtop mr1) g m net
        ==> limit (mtop mr1) (\x. f x * g x) (l * m) net
Proof
  REPEAT GEN_TAC THEN
  simp [LIMIT_METRIC, MR1_DEF, MSPACE] THEN
  DISCH_TAC THEN Q.X_GEN_TAC ‘e’ THEN DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN(MP_TAC o Q.SPEC
    `min (&1) (e / &2 / (abs l + abs m + &1))`)) THEN
  ASM_SIMP_TAC std_ss[REAL_HALF, REAL_LT_DIV, REAL_LT_MIN, REAL_LT_01, IMP_IMP,
    GSYM EVENTUALLY_AND, REAL_ARITH “&0 < abs x + abs y + &1”] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  SIMP_TAC std_ss[REAL_LT_RDIV_EQ, REAL_ARITH “&0 < abs x + abs y + &1”] THEN
  Q.X_GEN_TAC ‘y’ THEN
  SIMP_TAC std_ss[REAL_LT_RDIV_EQ, REAL_ARITH “&0 < abs x + abs y + &1”] THEN
  DISCH_THEN(CONJUNCTS_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
   “abs((f' - f) * g') <= x /\ abs((g' - g) * f) <= y
    ==> x < e / &2 ==> y < e / &2
        ==> abs(f' * g' - f * g) < e”) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL_IMP THEN
  ASM_REAL_ARITH_TAC
QED

Theorem LIMIT_REAL_LMUL :
    !(net:'a net) c f l.
        limit (mtop mr1) f l net
        ==> limit (mtop mr1) (\x. c * f x) (c * l) net
Proof
  SIMP_TAC std_ss[LIMIT_REAL_MUL, LIMIT_REAL_CONST]
QED

Theorem LIMIT_REAL_NEG :
    !(net:'a net) f l.
        limit (mtop mr1) f l net
        ==> limit (mtop mr1) (\x. -(f x)) (-l) net
Proof
  ONCE_REWRITE_TAC[REAL_ARITH “-x:real = -(&1) * x”] THEN
  REWRITE_TAC[LIMIT_REAL_LMUL]
QED

Theorem LIMIT_REAL_ADD :
    !(net:'a net) f g l m.
        limit (mtop mr1) f l net /\ limit (mtop mr1) g m net
        ==> limit (mtop mr1) (\x. f x + g x) (l + m) net
Proof
    rpt GEN_TAC
 >> simp [LIMIT_METRIC, MSPACE, MR1_DEF] >> DISCH_TAC
 >> Q.X_GEN_TAC ‘e’ >> DISCH_TAC
 >> FIRST_X_ASSUM (CONJUNCTS_THEN (MP_TAC o Q.SPEC ‘e / 2’))
 >> ASM_SIMP_TAC std_ss [REAL_HALF, IMP_IMP, GSYM EVENTUALLY_AND]
 >> MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO)
 >> simp []
 >> REAL_ARITH_TAC
QED

Theorem LIMIT_REAL_SUB :
    !(net:'a net) f g l m.
        limit (mtop mr1) f l net /\ limit (mtop mr1) g m net
        ==> limit (mtop mr1) (\x. f x - g x) (l - m) net
Proof
  SIMP_TAC std_ss[real_sub, LIMIT_REAL_ADD, LIMIT_REAL_NEG]
QED

Theorem LIMIT_REAL_ABS :
    !(net:'a net) f l.
        limit (mtop mr1) f l net
        ==> limit (mtop mr1) (\x. abs(f x)) (abs l) net
Proof
  REPEAT GEN_TAC THEN
  simp [LIMIT_METRIC, MSPACE, MR1_DEF] THEN
  HO_MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  simp [] THEN REAL_ARITH_TAC
QED

Theorem LIMIT_REAL_MAX :
    !(net:'a net) f g l m.
        limit (mtop mr1) f l net /\ limit (mtop mr1) g m net
        ==> limit (mtop mr1) (\x. max (f x) (g x)) (max l m) net
Proof
  REWRITE_TAC[REAL_ARITH “max a b = inv(&2) * (abs(a - b) + a + b)”] THEN
  REPEAT STRIP_TAC THEN HO_MATCH_MP_TAC LIMIT_REAL_LMUL THEN
  REPEAT(HO_MATCH_MP_TAC LIMIT_REAL_ADD THEN CONJ_TAC) THEN
  ASM_SIMP_TAC std_ss[LIMIT_REAL_SUB, LIMIT_REAL_ABS]
QED

Theorem LIMIT_REAL_MIN :
    !(net:'a net) f g l m.
        limit (mtop mr1) f l net /\ limit (mtop mr1) g m net
        ==> limit (mtop mr1) (\x. min (f x) (g x)) (min l m) net
Proof
  REWRITE_TAC[REAL_ARITH “min a b = inv(&2) * ((a + b) - abs(a - b))”] THEN
  REPEAT STRIP_TAC THEN HO_MATCH_MP_TAC LIMIT_REAL_LMUL THEN
  ASM_SIMP_TAC std_ss[LIMIT_REAL_ADD, LIMIT_REAL_SUB, LIMIT_REAL_ABS]
QED

(* END *)
val _ = export_theory ();

(* References:

 [1] Moore, E.H., Smith, H.L.: A General Theory of Limits. American Journal of
     Mathematics. 44, 102-121 (1922).
 [2] Kelley, J.L.: General Topology. Springer Science & Business Media (1975).
 [3] https://en.wikipedia.org/wiki/Net_(mathematics)

 *)
