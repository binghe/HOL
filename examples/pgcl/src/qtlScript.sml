(* -*-sml-*- *)
(* ========================================================================= *)
(* Create "qtlTheory" containing syntax and semantics of a temporal logic    *)
(* built on top of a probabilistic program.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
val () = app load
  ["bossLib", "realLib", "rich_listTheory", "intLib", "stringTheory",
   "metisLib", "wpTheory"];
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib intLib realLib;
open combinTheory listTheory rich_listTheory stringTheory integerTheory
     realTheory;
open posetTheory expectationTheory wpTheory;

(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "qtl"                                           *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "qtl";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;
val lemma = I prove;

(* ------------------------------------------------------------------------- *)
(* Temporal logic formulas: syntax                                           *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `formula = Atom of 'a expect
           | Not of formula
           | And of formula => formula
           | Next of formula
           | Eventually of formula
           | Unless of formula => formula`;

val False_def = Define `False = Atom Zero`;

val True_def = Define `True = Not False`;

val Or_def = Define `Or x y = Not (And (Not x) (Not y))`;

val Always_def = Define `Always x = Unless x False`;

(* ------------------------------------------------------------------------- *)
(* Temporal logic formulas: semantics                                        *)
(* ------------------------------------------------------------------------- *)

val sem_def = Define
  `(sem step (Atom e) = \s. probify (e s)) /\
   (sem step (Not a) = Compl (sem step a)) /\
   (sem step (And a b) = Min (sem step a) (sem step b)) /\
   (sem step (Next a) = step (sem step a)) /\
   (sem step (Eventually a) = prob_lfp (\e. Max (sem step a) (step e))) /\
   (sem step (Unless a b) =
    prob_gfp (\e. Max (sem step b) (Min (sem step a) (step e))))`;

val sem_next = store_thm
  ("sem_next",
   ``!step a. sem step (Next a) = step (sem step a)``,
   RW_TAC std_ss [sem_def]);

val true_alt = store_thm
  ("true_alt",
   ``!step. sem step True = One``,
   RW_TAC std_ss [sem_def, True_def, One_def, False_def]
   ++ CONV_TAC FUN_EQ_CONV
   ++ RW_TAC real_ss [Compl_def, Zero_def, probify_basic]);

val or_alt = store_thm
  ("or_alt",
   ``!step a b. sem step (Or a b) = Max (sem step a) (sem step b)``,
   RW_TAC std_ss [sem_def, Or_def]
   ++ CONV_TAC FUN_EQ_CONV
   ++ RW_TAC real_ss [Compl_def, Max_def, Min_def, REAL_MIN_MAX]);

(* ------------------------------------------------------------------------- *)
(* (expect1,Leq) is a complete poset                                         *)
(* ------------------------------------------------------------------------- *)
(***
val expect1_poset = store_thm
  ("expect1_poset",
   ``poset (expect1,Leq)``,
   RW_TAC std_ss [poset_def]
   << [PROVE_TAC [expect1_basic],
       PROVE_TAC [leq_refl],
       PROVE_TAC [leq_antisym],
       PROVE_TAC [leq_trans]]);

val prob_lub = store_thm
  ("prob_lub",
   ``!p x.
       lub (expect1,Leq) p x =
       if (?y. expect1 y /\ p y) then
         (!s. x s = sup (\r. ?y. (expect1 y /\ p y) /\ (y s = r)))
       else (x = Zero)``,
   REVERSE (RW_TAC std_ss [lub_def, Leq_def])
   >> (POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [GSYM IMP_DISJ_THM]
       ++ EQ_TAC
       << [RW_TAC std_ss []
           ++ CONV_TAC FUN_EQ_CONV
           ++ POP_ASSUM (MP_TAC o Q.SPEC `Zero`)
           ++ SIMP_TAC std_ss [expect1_basic]
           ++ RW_TAC std_ss [Zero_def]
           ++ REWRITE_TAC [GSYM REAL_LE_ANTISYM]
           ++ REVERSE CONJ_TAC >> PROVE_TAC [expect1_def]
           ++ POP_ASSUM (MATCH_MP_TAC o CONV_RULE RIGHT_IMP_FORALL_CONV)
           ++ PROVE_TAC [],
           SIMP_TAC std_ss [expect1_basic]
           ++ RW_TAC std_ss [Zero_def]
           ++ PROVE_TAC [expect1_def]])
   ++ EQ_TAC
   << [RW_TAC std_ss []
       ++ ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
       ++ CONJ_TAC
       << [POP_ASSUM
           (HO_MATCH_MP_TAC o CONV_RULE (QUANT_CONV RIGHT_IMP_FORALL_CONV))
           ++ RW_TAC std_ss []
           << [FULL_SIMP_TAC std_ss [expect1_def]
               ++ RW_TAC std_ss []
               << [MATCH_MP_TAC REAL_IMP_LE_SUP
                   ++ RW_TAC std_ss []
                   ++ METIS_TAC [],
                   MATCH_MP_TAC REAL_IMP_SUP_LE
                   ++ RW_TAC std_ss []
                   ++ METIS_TAC []],
               MATCH_MP_TAC REAL_IMP_LE_SUP
               ++ SIMP_TAC std_ss [CONJ_ASSOC]
               ++ CONJ_TAC >> PROVE_TAC []
               ++ Q.EXISTS_TAC `y' s`
               ++ PROVE_TAC [REAL_LE_REFL]],
           MATCH_MP_TAC REAL_IMP_SUP_LE
           ++ RW_TAC std_ss [] >> PROVE_TAC []
           ++ Q.PAT_ASSUM `!z. P z` (K ALL_TAC)
           ++ Q.PAT_ASSUM `!z. P z`
              (HO_MATCH_MP_TAC o CONV_RULE (QUANT_CONV RIGHT_IMP_FORALL_CONV))
           ++ RW_TAC std_ss []],
       RW_TAC std_ss []
       << [Suff `expect1 (\s. x s)`
           >> (CONV_TAC (DEPTH_CONV ETA_CONV) ++ REWRITE_TAC [])
           ++ RW_TAC std_ss []
           ++ FULL_SIMP_TAC std_ss [expect1_def]
           ++ RW_TAC std_ss []
           << [MATCH_MP_TAC REAL_IMP_LE_SUP
               ++ RW_TAC std_ss []
               ++ METIS_TAC [],
               MATCH_MP_TAC REAL_IMP_SUP_LE
               ++ RW_TAC std_ss []
               ++ METIS_TAC []],
           MATCH_MP_TAC REAL_IMP_LE_SUP
           ++ RW_TAC std_ss []
           ++ PROVE_TAC [expect1_def, REAL_LE_REFL],
           MATCH_MP_TAC REAL_IMP_SUP_LE
           ++ RW_TAC std_ss [] >> PROVE_TAC []
           ++ FIRST_ASSUM
              (MATCH_MP_TAC o CONV_RULE (QUANT_CONV RIGHT_IMP_FORALL_CONV))
           ++ PROVE_TAC []]]);

val prob_lub_epsilon = store_thm
  ("prob_lub_epsilon",
   ``!p x e s.
       0 < e /\ (?y. expect1 y /\ p y) /\ lub (expect1,Leq) p x ==>
       ?y. (expect1 y /\ p y) /\ x s <= y s + e``,
   RW_TAC std_ss [prob_lub, Leq_def, Zero_def]
   ++ MP_TAC (Q.SPECL [`\r. ?y. (expect1 y /\ p y) /\ (y s = r)`, `e`]
              SUP_EPSILON)
   ++ MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
   ++ CONJ_TAC >> (RW_TAC std_ss [] ++ PROVE_TAC [expect1_def])
   ++ RW_TAC std_ss []
   ++ PROVE_TAC []);

val up_complete_prob = store_thm
  ("up_complete_prob",
   ``!p. (?x. expect1 x /\ p x) ==> ?k. lub (expect1,Leq) p k``,
   RW_TAC std_ss []
   ++ Q.EXISTS_TAC `\s. sup (\r. ?y. (expect1 y /\ p y) /\ (y s = r))`
   ++ Q.PAT_ASSUM `expect1 X` MP_TAC
   ++ RW_TAC std_ss [lub_def, Leq_def, expect1_def]
   ++ (MATCH_MP_TAC REAL_IMP_LE_SUP || MATCH_MP_TAC REAL_IMP_SUP_LE)
   ++ BETA_TAC
   ++ PROVE_TAC [REAL_LE_REFL]);

val down_complete_prob = store_thm
  ("down_complete_prob",
   ``!p. (?x. expect1 x /\ p x) ==> ?k. glb (expect1,Leq) p k``,
   RW_TAC std_ss []
   ++ Q.EXISTS_TAC `\s. inf (\r. ?y. (expect1 y /\ p y) /\ (y s = r))`
   ++ Q.PAT_ASSUM `expect1 X` MP_TAC
   ++ RW_TAC std_ss [glb_def, Leq_def, expect1_def]
   ++ (MATCH_MP_TAC REAL_IMP_LE_INF || MATCH_MP_TAC REAL_IMP_INF_LE)
   ++ BETA_TAC
   ++ PROVE_TAC [REAL_LE_REFL]);

val complete_prob = store_thm
  ("complete_prob",
   ``complete (expect1,Leq)``,
   RW_TAC std_ss [complete_def]
   ++ PROVE_TAC [up_complete_prob, down_complete_prob]);

val expect1_lt_lub = store_thm
  ("expect1_lt_lub",
   ``!p x z s.
       lub (expect1,Leq) p x /\ expect1 z /\ z s < x s ==>
       ?y. expect1 y /\ p y /\ z s < y s``,
   RW_TAC std_ss [lub_def, Leq_def]
   ++ Suff `~!y. expect1 y /\ p y ==> y s <= z s`
   >> SIMP_TAC real_ss [GSYM real_lt, CONJ_ASSOC]
   ++ STRIP_TAC
   ++ Q.PAT_ASSUM `!z. P z /\ (!y. Q y z) ==> R z` MP_TAC
   ++ SIMP_TAC std_ss [GSYM CONJ_ASSOC]
   ++ Q.EXISTS_TAC `\e. if e = s then z s else x e`
   ++ CONJ_TAC
   >> (REPEAT (Q.PAT_ASSUM `expect1 X` MP_TAC)
       ++ RW_TAC real_ss [expect1_def]
       ++ RW_TAC real_ss [])
   ++ CONJ_TAC >> (RW_TAC real_ss [] ++ RW_TAC real_ss [])
   ++ Q.EXISTS_TAC `s`
   ++ RW_TAC real_ss [GSYM real_lt]);

val function_min = store_thm
  ("function_min",
   ``!t1 t2.
       function (expect1,Leq) t1 /\ function (expect1,Leq) t2 ==>
       function (expect1,Leq) (\e. Min (t1 e) (t2 e))``,
   RW_TAC real_ss [function_def, expect1_min]);

val function_max = store_thm
  ("function_max",
   ``!t1 t2.
       function (expect1,Leq) t1 /\ function (expect1,Leq) t2 ==>
       function (expect1,Leq) (\e. Max (t1 e) (t2 e))``,
   RW_TAC real_ss [function_def, expect1_max]);

val monotonic_min = store_thm
  ("monotonic_min",
   ``!t1 t2.
       monotonic (expect1,Leq) t1 /\ monotonic (expect1,Leq) t2 ==>
       monotonic (expect1,Leq) (\e. Min (t1 e) (t2 e))``,
   RW_TAC real_ss [monotonic_def, Min_def]
   ++ REPEAT (Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPECL [`x`, `y`]))
   ++ ASM_REWRITE_TAC []
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [Leq_def]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `s`)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `s`)
   ++ POP_ASSUM_LIST (K ALL_TAC)
   ++ Q.SPEC_TAC (`t1 x s`, `x1`)
   ++ Q.SPEC_TAC (`t2 x s`, `x2`)
   ++ Q.SPEC_TAC (`t1 y s`, `y1`)
   ++ Q.SPEC_TAC (`t2 y s`, `y2`)
   ++ RW_TAC std_ss [min_def]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ REAL_ARITH_TAC);

val monotonic_max = store_thm
  ("monotonic_max",
   ``!t1 t2.
       monotonic (expect1,Leq) t1 /\ monotonic (expect1,Leq) t2 ==>
       monotonic (expect1,Leq) (\e. Max (t1 e) (t2 e))``,
   RW_TAC real_ss [monotonic_def, Max_def]
   ++ REPEAT (Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPECL [`x`, `y`]))
   ++ ASM_REWRITE_TAC []
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [Leq_def]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `s`)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `s`)
   ++ POP_ASSUM_LIST (K ALL_TAC)
   ++ Q.SPEC_TAC (`t1 x s`, `x1`)
   ++ Q.SPEC_TAC (`t2 x s`, `x2`)
   ++ Q.SPEC_TAC (`t1 y s`, `y1`)
   ++ Q.SPEC_TAC (`t2 y s`, `y2`)
   ++ RW_TAC std_ss [max_def]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ REAL_ARITH_TAC);
***)

(* ------------------------------------------------------------------------- *)
(* Fixed points of expectation transformers                                  *)
(* ------------------------------------------------------------------------- *)
(***
val expect_lfp_exists = store_thm
  ("expect_lfp_exists",
   ``!phi.
       function (expect1,Leq) phi /\ monotonic (expect1,Leq) phi ==>
       ?g. lfp (expect1,Leq) phi g``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC (INST_TYPE [alpha |-> ``:'a expect``] knaster_tarski_lfp)
   ++ RW_TAC std_ss [expect1_poset, complete_prob]);

val expect_lfp_def = new_specification
  ("expect_lfp_def", ["expect_lfp"],
   CONV_RULE (QUANT_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV)
   expect_lfp_exists);

val healthy_lfp = store_thm
  ("healthy_lfp",
   ``!phi. healthy phi ==> lfp (expect1,Leq) phi (expect_lfp phi)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC expect_lfp_def
   ++ SIMP_TAC std_ss [function_def, monotonic_def]
   ++ CONJ_TAC >> PROVE_TAC [healthy_prob]
   ++ PROVE_TAC [expect1_expect, healthy_mono]);

val expect_gfp_exists = store_thm
  ("expect_gfp_exists",
   ``!phi.
       function (expect1,Leq) phi /\ monotonic (expect1,Leq) phi ==>
       ?g. gfp (expect1,Leq) phi g``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC (INST_TYPE [alpha |-> ``:'a expect``] knaster_tarski_gfp)
   ++ RW_TAC std_ss [expect1_poset, complete_prob]);

val expect_gfp_def = new_specification
  ("expect_gfp_def", ["expect_gfp"],
   CONV_RULE (QUANT_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV)
   expect_gfp_exists);

val healthy_gfp = store_thm
  ("healthy_gfp",
   ``!phi. healthy phi ==> gfp (expect1,Leq) phi (expect_gfp phi)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC expect_gfp_def
   ++ SIMP_TAC std_ss [function_def, monotonic_def]
   ++ CONJ_TAC >> PROVE_TAC [healthy_prob]
   ++ PROVE_TAC [expect1_expect, healthy_mono]);

(* ------------------------------------------------------------------------- *)
(* Refinement                                                                *)
(* ------------------------------------------------------------------------- *)

val refines_def = Define
  `refines t1 t2 = !r. wf_expect r ==> Leq (t1 r) (t2 r)`;

val refines_refl = store_thm
  ("refines_refl",
   ``!t. refines t t``,
   RW_TAC real_ss [refines_def, Leq_def]);

val refines_trans = store_thm
  ("refines_trans",
   ``!t1 t2 t3. refines t1 t2 /\ refines t2 t3 ==> refines t1 t3``,
   RW_TAC real_ss [refines_def]
   ++ PROVE_TAC [leq_trans]);

val refines_zero = store_thm
  ("refines_zero",
   ``!t. healthy t ==> refines (\r. Zero) t``,
   RW_TAC std_ss [refines_def]
   ++ PROVE_TAC [healthy_expect, wf_expect_zero_leq]);

val refines_lfp = store_thm
  ("refines_lfp",
   ``!t1 t2.
        function (expect1,Leq) t1 /\ monotonic (expect1,Leq) t1 /\
        function (expect1,Leq) t2 /\ monotonic (expect1,Leq) t2 /\
        refines t1 t2 ==>
        Leq (expect_lfp t1) (expect_lfp t2)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `t1` expect_lfp_def)
   ++ MP_TAC (Q.SPEC `t2` expect_lfp_def)
   ++ RW_TAC std_ss [lfp_def]
   ++ POP_ASSUM MATCH_MP_TAC
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `refines X Y` MP_TAC
   ++ SIMP_TAC std_ss [refines_def]
   ++ DISCH_THEN (MP_TAC o Q.SPEC `expect_lfp t2`)
   ++ ASM_SIMP_TAC std_ss [expect1_expect]);

val refines_gfp = store_thm
  ("refines_gfp",
   ``!t1 t2.
        function (expect1,Leq) t1 /\ monotonic (expect1,Leq) t1 /\
        function (expect1,Leq) t2 /\ monotonic (expect1,Leq) t2 /\
        refines t1 t2 ==>
        Leq (expect_gfp t1) (expect_gfp t2)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `t1` expect_gfp_def)
   ++ MP_TAC (Q.SPEC `t2` expect_gfp_def)
   ++ RW_TAC std_ss [gfp_def]
   ++ FIRST_ASSUM MATCH_MP_TAC
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `refines X Y` MP_TAC
   ++ SIMP_TAC std_ss [refines_def]
   ++ DISCH_THEN (MP_TAC o Q.SPEC `expect_gfp t1`)
   ++ ASM_SIMP_TAC std_ss [expect1_expect]);
***)

(* ------------------------------------------------------------------------- *)
(* The healthiness condition makes sure that fixed points always exist, and  *)
(* that everything interprets to a well-formed probability                   *)
(* ------------------------------------------------------------------------- *)

val eventually_lfp_lemma = lemma
  (``!step a.
        wf_trans step /\ wf_prob (sem step a) ==>
        lfp (wf_prob,Leq) (\e. Max (sem step a) (step e))
        (sem step (Eventually a))``,
   RW_TAC std_ss [sem_def]
   ++ MATCH_MP_TAC prob_lfp_def
   ++ CONJ_TAC
   << [HO_MATCH_MP_TAC function_max
       ++ RW_TAC std_ss [function_def]
       ++ PROVE_TAC [wf_trans_prob],
       HO_MATCH_MP_TAC monotonic_max
       ++ RW_TAC std_ss [monotonic_def]
       ++ PROVE_TAC [wf_trans_mono, wf_prob_expect, leq_refl]]);

val unless_gfp_lemma = lemma
  (``!step a b.
        wf_trans step /\ wf_prob (sem step a) /\ wf_prob (sem step b) ==>
        gfp (wf_prob,Leq) (\e. Max (sem step b) (Min (sem step a) (step e)))
        (sem step (Unless a b))``,
   RW_TAC std_ss [sem_def]
   ++ MATCH_MP_TAC prob_gfp_def
   ++ CONJ_TAC
   << [HO_MATCH_MP_TAC function_max
       ++ CONJ_TAC
       >> (RW_TAC std_ss [function_def] ++ PROVE_TAC [wf_trans_prob])
       ++ HO_MATCH_MP_TAC function_min
       ++ RW_TAC std_ss [function_def]
       ++ PROVE_TAC [wf_trans_prob],
       HO_MATCH_MP_TAC monotonic_max
       ++ CONJ_TAC
       >> (RW_TAC std_ss [monotonic_def]
           ++ PROVE_TAC [wf_trans_mono, wf_prob_expect, leq_refl])
       ++ HO_MATCH_MP_TAC monotonic_min
       ++ RW_TAC std_ss [monotonic_def]
       ++ PROVE_TAC [wf_trans_mono, wf_prob_expect, leq_refl]]);

val wf_trans_formula = store_thm
  ("wf_trans_formula",
   ``!step a. wf_trans step ==> wf_prob (sem step a)``,
   GEN_TAC
   ++ CONV_TAC FORALL_IMP_CONV
   ++ STRIP_TAC
   ++ Induct
   << [RW_TAC std_ss [sem_def, wf_prob_def, probify],
       RW_TAC std_ss [sem_def, wf_prob_compl],
       RW_TAC std_ss [sem_def, wf_prob_min],
       RW_TAC std_ss [sem_def, wf_trans_prob],
       MP_TAC (Q.SPECL [`step`, `a`] eventually_lfp_lemma)
       ++ RW_TAC std_ss [lfp_def],
       MP_TAC (Q.SPECL [`step`, `a`, `a'`] unless_gfp_lemma)
       ++ RW_TAC std_ss [gfp_def]]);

val wf_trans_eventually = store_thm
  ("wf_trans_eventually",
   ``!step a.
        wf_trans step ==>
        lfp (wf_prob,Leq) (\e. Max (sem step a) (step e))
        (sem step (Eventually a))``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC eventually_lfp_lemma
   ++ RW_TAC std_ss [wf_trans_formula]);

val wf_trans_unless = store_thm
  ("wf_trans_unless",
   ``!step a b.
        wf_trans step ==>
        gfp (wf_prob,Leq) (\e. Max (sem step b) (Min (sem step a) (step e)))
        (sem step (Unless a b))``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC unless_gfp_lemma
   ++ RW_TAC std_ss [wf_trans_formula]);

(* ------------------------------------------------------------------------- *)
(* Positive formulas and refinement                                          *)
(* ------------------------------------------------------------------------- *)

val polarity_def = Define
  `(polarity p (Atom e) = T) /\
   (polarity p (Not a) = polarity (~p) a) /\
   (polarity p (And a b) = polarity p a /\ polarity p b) /\
   (polarity p (Next a) = p /\ polarity p a) /\
   (polarity p (Eventually a) = p /\ polarity p a) /\
   (polarity p (Unless a b) = p /\ polarity p a /\ polarity p b)`;

val positive_def = Define `positive a = polarity T a`;

val positive_mono = store_thm
  ("positive_mono",
   ``!t1 t2 a.
       wf_trans t1 /\ wf_trans t2 /\ refines t1 t2 /\ positive a ==>
       Leq (sem t1 a) (sem t2 a)``,
   RW_TAC std_ss [positive_def]
   ++ Suff `!b. polarity b a ==> (if b then Leq else Geq) (sem t1 a) (sem t2 a)`
   >> METIS_TAC []
   ++ POP_ASSUM (K ALL_TAC)
   ++ Induct_on `a`
   << [RW_TAC std_ss [sem_def, leq_refl, Geq_def],
       RW_TAC std_ss [sem_def, leq_refl, Geq_def, leq_compl_2, polarity_def]
       ++ METIS_TAC [Geq_def],
       RW_TAC std_ss [polarity_def, sem_def, Geq_def]
       ++ METIS_TAC [min_imp_leq2, Geq_def],
       RW_TAC std_ss [polarity_def, sem_def]
       ++ Q.PAT_ASSUM `!b. P b` IMP_RES_TAC
       ++ FULL_SIMP_TAC std_ss []
       ++ MATCH_MP_TAC leq_trans
       ++ Q.EXISTS_TAC `t1 (sem t2 a)`
       ++ CONJ_TAC
       >> PROVE_TAC [wf_trans_mono, wf_prob_expect, wf_trans_formula]
       ++ Q.PAT_ASSUM `refines X Y` MP_TAC
       ++ SIMP_TAC std_ss [refines_def]
       ++ DISCH_THEN MATCH_MP_TAC
       ++ PROVE_TAC [wf_prob_expect, wf_trans_formula],
       RW_TAC std_ss [polarity_def, sem_def, Geq_def]
       ++ Q.PAT_ASSUM `!b. P b` IMP_RES_TAC
       ++ FULL_SIMP_TAC std_ss [Geq_def]
       ++ MATCH_MP_TAC refines_lfp
       ++ REPEAT CONJ_TAC
       ++ TRY (FIRST (map HO_MATCH_MP_TAC [function_max, monotonic_max]))
       ++ RW_TAC std_ss [function_def, monotonic_def, wf_trans_formula,
                         wf_trans_prob, leq_refl, wf_trans_mono, wf_prob_expect]
       ++ RW_TAC std_ss [refines_def]
       ++ MATCH_MP_TAC max_imp_leq2
       ++ RW_TAC std_ss []
       ++ Q.PAT_ASSUM `refines X Y` MP_TAC
       ++ SIMP_TAC std_ss [refines_def]
       ++ DISCH_THEN MATCH_MP_TAC
       ++ PROVE_TAC [wf_prob_expect, wf_trans_formula],
       RW_TAC std_ss [polarity_def, sem_def, Geq_def]
       ++ Q.PAT_ASSUM `!b. P b` IMP_RES_TAC
       ++ Q.PAT_ASSUM `!b. P b` IMP_RES_TAC
       ++ FULL_SIMP_TAC std_ss [Geq_def]
       ++ MATCH_MP_TAC refines_gfp
       ++ REPEAT
          (CONJ_TAC
           || HO_MATCH_MP_TAC function_max
           || HO_MATCH_MP_TAC function_min
           || HO_MATCH_MP_TAC monotonic_max
           || HO_MATCH_MP_TAC monotonic_min)
       ++ RW_TAC std_ss [function_def, monotonic_def, wf_trans_formula,
                         wf_trans_prob, leq_refl, wf_trans_mono, wf_prob_expect]
       ++ RW_TAC std_ss [refines_def]
       ++ MATCH_MP_TAC max_imp_leq2
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC min_imp_leq2
       ++ RW_TAC std_ss []
       ++ Q.PAT_ASSUM `refines X Y` MP_TAC
       ++ SIMP_TAC std_ss [refines_def]
       ++ DISCH_THEN MATCH_MP_TAC
       ++ PROVE_TAC [wf_prob_expect, wf_trans_formula]]);

(* ------------------------------------------------------------------------- *)
(* Some useful temporal laws                                                 *)
(* ------------------------------------------------------------------------- *)

val sem_max1_0 = store_thm
  ("sem_max1_0",
   ``!t a s. wf_trans t ==> (max 0 (sem t a s) = sem t a s)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`t`, `a`] wf_trans_formula)
   ++ RW_TAC std_ss [wf_prob_def, REAL_MAX_ALT]);

val eventually_expand = store_thm
  ("eventually_expand",
   ``!step a.
       wf_trans step ==>
       (Max (sem step a) (sem step (Next (Eventually a))) =
        sem step (Eventually a))``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`step`, `a`] wf_trans_eventually)
   ++ RW_TAC std_ss [lfp_def]
   ++ PROVE_TAC [sem_def]);

val double_eventually = store_thm
  ("double_eventually",
   ``!step a.
       wf_trans step ==>
       (sem step (Eventually (Eventually a)) = sem step (Eventually a))``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC leq_antisym
   ++ REVERSE CONJ_TAC
   >> (MP_TAC (Q.SPECL [`step`, `Eventually a`] eventually_expand)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => REWRITE_TAC [GSYM th])
       ++ RW_TAC std_ss [leq_max1])
   ++ MP_TAC (Q.SPECL [`step`, `Eventually a`] wf_trans_eventually)
   ++ RW_TAC std_ss [lfp_def]
   ++ POP_ASSUM MATCH_MP_TAC
   ++ RW_TAC std_ss [wf_trans_formula, max_leq, leq_refl]
   ++ MP_TAC (Q.SPECL [`step`, `a`] eventually_expand)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
   ++ RW_TAC std_ss [leq_max2, sem_next]);

(* ------------------------------------------------------------------------- *)
(* Since all programs give healthy transformers, the properties are free     *)
(* ------------------------------------------------------------------------- *)

val wp_formula = store_thm
  ("wp_formula",
   ``!step a. wf_prob (sem (wp step) a)``,
   REPEAT GEN_TAC
   ++ MATCH_MP_TAC wf_trans_formula
   ++ RW_TAC std_ss [wf_trans_wp]);

val wp_eventually = store_thm
  ("wp_eventually",
   ``!step a.
        lfp (wf_prob,Leq) (\e. Max (sem (wp step) a) (wp step e))
        (sem (wp step) (Eventually a))``,
   REPEAT GEN_TAC
   ++ MATCH_MP_TAC wf_trans_eventually
   ++ RW_TAC std_ss [wf_trans_wp]);

val wp_unless = store_thm
  ("wp_unless",
   ``!step a b.
        gfp (wf_prob,Leq)
        (\e. Max (sem (wp step) b) (Min (sem (wp step) a) (wp step e)))
        (sem (wp step) (Unless a b))``,
   REPEAT GEN_TAC
   ++ MATCH_MP_TAC wf_trans_unless
   ++ RW_TAC std_ss [wf_trans_wp]);

(* ------------------------------------------------------------------------- *)
(* The random walker                                                         *)
(* ------------------------------------------------------------------------- *)

val nstate_def = Define `nstate n = ((\v. if v = "n" then n else 0) : state)`;

val npred_def = Define
  `npred n = Atom ((\s. if s"n" = n then 1 else 0) : state expect)`;

val walk_def = Define
  `walk (step : state trans) =
   wf_trans step /\
   !a n.
     sem step a (nstate (n - 1)) / 3 + sem step a (nstate (n + 1)) / 3 <=
     sem step (Next a) (nstate n)`;

val walk_up_def = Define
  `walk_up step n = sem step (Eventually (npred (n + 1))) (nstate n)`;

val npred_nstate = store_thm
  ("npred_nstate",
   ``!t m n. sem t (npred m) (nstate n) = if m = n then 1 else 0``,
   RW_TAC std_ss [npred_def, nstate_def, sem_def, probify_basic]);

val walk_alt = store_thm
  ("walk_alt",
   ``!step.
       walk (step : state trans) =
       wf_trans step /\
       !a n.
         sem step a (nstate (n - 1)) + sem step a (nstate (n + 1)) <=
         3 * sem step (Next a) (nstate n)``,
   RW_TAC std_ss [walk_def, real_div, GSYM REAL_ADD_RDISTRIB]
   ++ Suff `!x y. x * inv 3 <= y = x <= 3 * y` >> RW_TAC std_ss []
   ++ Suff `!x y. x * inv 3 <= y = x * inv 3 <= (3 * y) * inv 3`
   >> (DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       ++ RW_TAC real_ss [REAL_LE_RMUL])
   ++ Suff `!y. 3 * y * inv 3 = y * 1` >> RW_TAC real_ss []
   ++ Suff `~(3r = 0)`
   >> METIS_TAC [REAL_MUL_SYM, REAL_MUL_ASSOC, REAL_MUL_RINV]
   ++ RW_TAC real_ss []);

val worst_walk_def = Define
  `worst_walk =
   Probs [(1 / 3, Assign "n" (\s. s"n" - 1));
          (1 / 3, Assign "n" (\s. s"n" + 1))]`;

val worst_walk_alt = store_thm
  ("worst_walk_alt",
   ``wp worst_walk x =
     wp (Probs [(1 / 3, Assign "n" (\s. s"n" - 1));
                (1 / 3, Assign "n" (\s. s"n" + 1))]) x``,
   RW_TAC std_ss [worst_walk_def]);

val walk_worst_walk = store_thm
  ("walk_worst_walk",
   ``walk (wp worst_walk)``,
   RW_TAC std_ss [walk_alt, wf_trans_wp, sem_next]
   ++ RW_TAC real_ss
      [worst_walk_alt, Probs_def, MAP, wp_def, probify_basic, Zero_def]
   ++ RW_TAC real_ss
      [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, REAL_DIV_LMUL, REAL_INJ]
   ++ MATCH_MP_TAC REAL_LE_ADD2
   ++ CONJ_TAC
   ++ MATCH_MP_TAC REAL_EQ_IMP_LE
   ++ REPEAT AP_TERM_TAC
   ++ CONV_TAC FUN_EQ_CONV
   ++ RW_TAC std_ss [nstate_def]);

(*
val walk_up_eqn = store_thm
  ("walk_up_eqn",
  ``!t n. walk t ==> walk_up t n pow 2 + 1 <= 3 * walk_up t n``,
   RW_TAC std_ss [walk_alt]
   ++ MATCH_MP_TAC REAL_LE_TRANS
   ++ Q.EXISTS_TAC
      `sem t (Eventually (npred (n + 1))) (nstate (n - 1)) +
       sem t (Eventually (npred (n + 1))) (nstate (n + 1))`
   ++ REVERSE CONJ_TAC
   >> (RW_TAC std_ss [walk_up_def]
       ++ MP_TAC (Q.SPECL [`t`, `npred (n + 1)`]
                  (INST_TYPE [alpha |-> ``:state``] eventually_expand))
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN
          (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
       ++ RW_TAC int_ss [Max_def, npred_nstate, INT_ADD_RID_UNIQ]
       ++ RW_TAC std_ss [sem_max1_0])
*)



val _ = export_theory();
