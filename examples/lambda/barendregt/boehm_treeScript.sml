(*---------------------------------------------------------------------------*
 * boehm_treeScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])         *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory llistTheory
     relationTheory ltreeTheory pathTheory posetTheory hurdUtils;

open basic_swapTheory binderLib termTheory appFOLDLTheory chap2Theory
     chap3Theory head_reductionTheory standardisationTheory solvableTheory;

val _ = new_theory "boehm_tree";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)

(* Definition 8.3.20 [1, p.177]

   A term may have several hnf's, e.g. if any of its hnf can still do beta
   reductions, after such reductions the term is still an hnf by definition.
   The (unique) terminating term of head reduction path is called "principle"
   hnf, which is used for defining Boehm trees.
 *)
Definition principle_hnf_def :
    principle_hnf = last o head_reduction_path
End

Theorem hnf_principle_hnf :
    !M. has_hnf M ==> hnf (principle_hnf M)
Proof
    rw [corollary11_4_8, principle_hnf_def]
 >> MP_TAC (Q.SPEC ‘M’ head_reduction_path_def)
 >> RW_TAC std_ss []
QED

Theorem principle_hnf_stable :
    !M. hnf M ==> principle_hnf M = M
Proof
    rw [principle_hnf_def]
 >> ‘finite (head_reduction_path M)’ by PROVE_TAC [hnf_has_hnf, corollary11_4_8]
 >> MP_TAC (Q.SPEC ‘M’ head_reduction_path_def)
 >> RW_TAC std_ss []
 (* applying is_head_reduction_thm *)
 >> qabbrev_tac ‘p = head_reduction_path M’
 >> STRIP_ASSUME_TAC (ISPEC “p :(term, redpos list) path” path_cases)
 >- fs []
 >> gs [is_head_reduction_thm, hnf_no_head_redex]
QED

(* used by principle_hnf_LAMl_appstar *)
Theorem lemma2[local] :
    hnf t /\ ALL_DISTINCT (MAP FST l) /\ ALL_DISTINCT (MAP SND l) /\
   (!y. MEM y (MAP SND l) ==> DISJOINT (FV y) (FV t)) ==>
    principle_hnf (LAMl (MAP FST l) t @* MAP SND l) = (FEMPTY |++ l) ' t
Proof
    cheat
QED

(* ‘principle_hnf’ can be used to do final beta-reductions to make a hnf abs-free *)
Theorem principle_hnf_LAMl_appstar :
    !xs vs t. hnf t /\ ALL_DISTINCT xs /\ vs = FRESH_list (LENGTH xs) (FV t) ==>
              principle_hnf (LAMl xs t @* (MAP VAR vs)) =
                (FEMPTY |++ ZIP (xs,MAP VAR vs)) ' t
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘n = LENGTH xs’
 >> MP_TAC (Q.SPECL [‘n’, ‘FV (t :term)’] FRESH_list_def)
 >> rw []
 >> qabbrev_tac ‘vs = FRESH_list n (FV t)’
 >> qabbrev_tac ‘ys :term list = MAP VAR vs’
 >> ‘LENGTH xs = LENGTH ys’ by rw [Abbr ‘n’, Abbr ‘ys’]
 >> qabbrev_tac ‘l = ZIP (xs,ys)’
 >> Know ‘ALL_DISTINCT ys’
 >- (qunabbrev_tac ‘ys’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [])
 >> DISCH_TAC
 >> Know ‘!y. MEM y ys ==> DISJOINT (FV y) (FV t)’
 >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV t)’ MP_TAC \\
     rw [Abbr ‘ys’, MEM_MAP, DISJOINT_ALT, MEM_EL] >> fs [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘n’ >> rw [])
 >> DISCH_TAC
 >> ‘xs = MAP FST l /\ ys = MAP SND l’ by rw [Abbr ‘l’, Abbr ‘ys’, MAP_ZIP]
 >> fs []
 >> MATCH_MP_TAC lemma2 >> art []
QED

(* hnf_head access the head variable term of an abs-free hnf. *)
local
  val hnf_head_defn =
     ‘hnf_head t = if is_comb t then hnf_head (rator t) else t’;
  (* Defn.tgoal (Hol_defn "hnf_head" hnf_head_defn) *)
  val tactic = WF_REL_TAC ‘measure size’ >> rw [is_comb_APP_EXISTS] >> rw [];
in
  val (hnf_head_def, SOME hnf_head_ind) =
       TotalDefn.tDefine "hnf_head" hnf_head_defn tactic;
end;

Theorem hnf_head_appstar :
    !t. ~is_comb t ==> hnf_head (t @* args) = t
Proof
    Induct_on ‘args’ using SNOC_INDUCT
 >> rw [appstar_SNOC, Once hnf_head_def]
QED

Overload hnf_headvar = “\t. THE_VAR (hnf_head t)”

(* hnf_children retrives the ‘args’ part of an abs-free hnf (VAR y @* args) *)
local
  val hnf_children_defn =
     ‘hnf_children t = if is_comb t then SNOC (rand t) (hnf_children (rator t))
                       else []’;
  (* Defn.tgoal (Hol_defn "hnf_children" hnf_children_defn); *)
  val tactic = WF_REL_TAC ‘measure size’ >> rw [is_comb_APP_EXISTS] >> rw [];
in
  val (hnf_children_def, SOME hnf_children_ind) =
      TotalDefn.tDefine "hnf_children" hnf_children_defn tactic;
end;

Theorem hnf_children_thm :
   (!y.     hnf_children ((VAR :string -> term) y) = []) /\
   (!v t.   hnf_children (LAM v t) = []) /\
   (!t1 t2. hnf_children (t1 @@ t2) = SNOC t2 (hnf_children t1))
Proof
   rpt (rw [Once hnf_children_def])
QED

Theorem hnf_children_appstar :
    !t. ~is_comb t ==> hnf_children (t @* args) = args
Proof
    Induct_on ‘args’ using SNOC_INDUCT
 >- rw [Once hnf_children_def]
 >> RW_TAC std_ss [appstar_SNOC]
 >> rw [Once hnf_children_def]
QED

Theorem absfree_hnf_cases :
    !M. hnf M /\ ~is_abs M <=> ?y args. M = VAR y @* args
Proof
    Q.X_GEN_TAC ‘M’
 >> EQ_TAC
 >- (STRIP_TAC \\
    ‘?vs args y. ALL_DISTINCT vs /\ M = LAMl vs (VAR y @* args)’ by METIS_TAC [hnf_cases] \\
     reverse (Cases_on ‘vs = []’) >- fs [] \\
     qexistsl_tac [‘y’, ‘args’] >> rw [])
 >> rpt STRIP_TAC
 >- rw [hnf_appstar]
 >> rfs [is_abs_cases]
QED

Theorem absfree_hnf_thm :
    !M. hnf M /\ ~is_abs M ==> M = hnf_head M @* hnf_children M
Proof
    rw [absfree_hnf_cases]
 >> rw [hnf_children_appstar, hnf_head_appstar]
QED

(* The needed unfolding function for ltree_unfold for Boehm Tree *)
Definition BT_generator_def :
    BT_generator (M :term) =
      if solvable M then
         let M0 = principle_hnf M;
              n = LAMl_size M0;
             vs = FRESH_list n (FV M0);
             M1 = principle_hnf (M0 @* (MAP VAR vs));
             M2 = LAMl vs (hnf_head M1);
         in
            (SOME M2, fromList (hnf_children M1))
      else
        (NONE, LNIL)
End

(* NOTE: The type of ‘BT M’ is a :term option ltree (:boehm_tree). In [1], BT(M)
   denotes a partial function mapping sequence of numbers (path) to ltree nodes,
   which is ‘ltree_el (BT M)’:

   |- ltree_el (Branch a ts) [] = SOME (a,LLENGTH ts) /\
      ltree_el (Branch a ts) (n::ns) =
        case LNTH n ts of NONE => NONE | SOME t => ltree_el t ns
 *)
Definition BT_def :
    BT = ltree_unfold BT_generator
End

(* the type of Boehm tree *)
Type boehm_tree[pp] = “:term option ltree”

(* the trees that are the tree of a term *)
Definition Boehm_def :
    Boehm = {BT(M) | T}
End

(* Remarks 10.1.3 (iii) [1, p.216]: unsolvable terms all have the same Boehm
   tree (‘bot’).
 *)
Overload bot = “Branch NONE (LNIL :boehm_tree llist)”
val _ = Unicode.unicode_version {u = UTF8.chr 0x22A5, tmnm = "bot"};

Theorem unsolvable_BT :
    !M. unsolvable M ==> BT M = bot
Proof
    rw [BT_def, BT_generator_def, ltree_unfold, ltree_map]
QED

Theorem unsolvable_BT_EQ :
    !M N. unsolvable M /\ unsolvable N ==> BT M = BT N
Proof
    rw [unsolvable_BT]
QED

(* Proposition 10.1.6 [1, p.219] *)
Theorem lameq_cong_BT :
    !M N. M == N ==> BT M = BT N
Proof
    cheat
QED

(*---------------------------------------------------------------------------*
 *  Comparing Boehm trees (can be moved to ltreeTheory)
 *---------------------------------------------------------------------------*)

(* “ltree_subset A B” <=> A results from B by cutting off some subtrees *)
Definition ltree_subset_def :
    ltree_subset A B <=> (subtrees A) SUBSET (subtrees B)
End

(* “ltree_paths A” has the type “:num list -> bool” (a set of number lists).

   |- ltree_lookup t [] = SOME t /\
      ltree_lookup (Branch a ts) (n::ns) =
        case LNTH n ts of NONE => NONE | SOME t => ltree_lookup t ns
 *)
Definition ltree_paths_def :
    ltree_paths A = {path | IS_SOME (ltree_lookup A path)}
End

Theorem ltree_paths_alt :
    !A. ltree_paths A = {path | IS_SOME (ltree_el A path)}
Proof
    cheat
QED

Theorem ltree_subset_alt :
    !A B. ltree_subset A B <=> (ltree_paths A) SUBSET (ltree_paths B)
Proof
    cheat
QED

(*---------------------------------------------------------------------------*
 * FV (free variables) and BV (binding variables) of Boehm trees
 *---------------------------------------------------------------------------*)

(* BV of a single term *)
Definition BV_of_hnf_def :
    BV_of_hnf (M :term) = let M0 = principle_hnf M;
                               n = LAMl_size M0;
                              vs = FRESH_list n (FV M0)
                          in set vs
End

Definition BV_of_ltree_node_def :
    BV_of_ltree_node M p =
      let node = ltree_el M p in
          if IS_SOME node then
             BV_of_hnf (THE (FST (THE node)))
          else EMPTY
End

(* BV_of_ltree_path: the set of binding variables up to a path *)
local
  (* usage: Defn.tgoal (Hol_defn "BV_of_ltree_path" BV_of_ltree_path_defn); *)
  val BV_of_ltree_path_defn =
     ‘BV_of_ltree_path (M :boehm_tree) p =
         if p = [] then BV_of_ltree_node M p
         else BV_of_ltree_path M (FRONT p) UNION
              BV_of_ltree_node M p’;
  (* for solving the above tgoal *)
  val tactic = WF_REL_TAC ‘measure (LENGTH o SND)’ \\
               rw [LENGTH_FRONT] \\
               fs [NOT_NIL_EQ_LENGTH_NOT_0];
in
  val (BV_of_ltree_path_def, SOME BV_of_ltree_path_ind) =
       TotalDefn.tDefine "BV_of_ltree_path" BV_of_ltree_path_defn tactic;
end;

Overload BV = “BV_of_ltree_path”

(* BT of a single variable *)
Overload BT_VAR = “\x. (Branch (SOME (VAR x)) [| |]) :boehm_tree”

val example_10_1_20 =
   “Branch (SOME (LAMl [x; y] (VAR z))) [| BT_VAR x; BT_VAR y |]”;

Definition FV_of_hnf_head_def :
    FV_of_hnf_head (M :term) =
          let M0 = principle_hnf M;
               n = LAMl_size M0;
              vs = FRESH_list n (FV M0);
              M1 = principle_hnf (M0 @* (MAP VAR vs))
          in
              FV (hnf_head M1)
End

Definition FV_of_ltree_node_def :
    FV_of_ltree_node (M :boehm_tree) p =
      let node = ltree_el M p in
          if IS_SOME node then
             FV_of_hnf_head (THE (FST (THE node)))
          else EMPTY
End

Definition FV_of_ltree_path_def :
    FV_of_ltree_path M p = FV_of_ltree_node M p DIFF BV_of_ltree_path M p
End

Definition FV_of_ltree_def :
    FV_of_ltree M = BIGUNION (IMAGE (FV_of_ltree_path M) (ltree_paths M))
End

Overload FV = “FV_of_ltree”

Theorem FV_of_ltree_empty_imp_closed :
    !M. FV (BT M) = {} ==> closed M
Proof
    rw [FV_of_ltree_def]
 >- (fs [ltree_paths_def, NOT_IN_EMPTY, Once EXTENSION, NOT_IN_EMPTY] \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘[]’)) \\
     rw [ltree_lookup_def])
 >> fs [Once EXTENSION]
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘{}’))
 >> rw [ltree_paths_def]
 >> rename1 ‘FV_of_ltree_path (BT M) p = {}’
 >> Suff ‘!p. IS_SOME (ltree_lookup (BT M) p) /\
              FV_of_ltree_path (BT M) p = {} ==> closed M’
 >- (DISCH_THEN MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘p’ >> art [])
 >> KILL_TAC
 (* stage work *)
 >> cheat
QED

(*---------------------------------------------------------------------------*
 *  Equivalent terms
 *---------------------------------------------------------------------------*)

(* Definition 10.2.19

   M = LAMl v1 (y  @* Ms) @@ (MAP VAR v1) == y  @* Ms' (LENGTH: m)
   N = LAMl v2 (y' @* Ns) @@ (MAP VAR v2) == y' @* Ns' (LENGTH: m')

   y = y'
   n - m = n' - m' (possibly negative) <=> n + m' = n' + m (all non-negative)
 *)
Definition equivalent_def :
    equivalent (M :term) (N :term) =
        if solvable M /\ solvable N then
           let M0 = principle_hnf M;
               N0 = principle_hnf N;
               n  = LAMl_size M0;
               n' = LAMl_size N0;
               vs = FRESH_list (MAX n n') (FV M0 UNION FV N0);
               v  = TAKE n  vs;
               v' = TAKE n' vs;
               M1 = principle_hnf (M0 @* (MAP VAR v));
               N1 = principle_hnf (N0 @* (MAP VAR v'));
               y  = hnf_head M1;
               y' = hnf_head N1;
               m  = LENGTH (hnf_children M1);
               m' = LENGTH (hnf_children N1);
           in
               y = y' /\ n + m' = n' + m
        else
           ~solvable M /\ ~solvable N
End

(* From [1, p.238]. This concerte example shows that dB encoding is not easy in
   defining this "concept": the literal encoding of inner head variables are not
   the same for equivalent terms.
 *)
Theorem equivalent_example :
    equivalent (LAM x (VAR x @@ M)) (LAMl [y; z] (VAR y @* [M; N]))
Proof
    rw [equivalent_def]
 >> cheat
QED

Theorem unsolvable_imp_equivalent :
    !M N. unsolvable M /\ unsolvable N ==> equivalent M N
Proof
    rw [equivalent_def]
QED

(*---------------------------------------------------------------------------*
 *  Boehm transformations
 *---------------------------------------------------------------------------*)

(* Definition 10.3.3 (i) *)
Type transform[pp] = “:(term -> term) list”

(* Definition 10.3.3 (ii) *)
Definition solving_transform_def :
    solving_transform (f :term -> term) <=>
      (?x. f = \p. p @@ VAR x) \/ (?x N. f = [N/x])
End

(* Definition 10.3.3 (iii)

   NOTE: "Boehm transform is a finite composition of solving transforms
        (including the identity as a composition of zero transforms).

   Here we just define "Boehm transform" as a list of solving transforms,
   thus always finite. The "composition" part depends on how this list is used.
 *)
Definition Boehm_transform_def :
    Boehm_transform pi = EVERY solving_transform pi
End

(* ‘apply pi M’ (applying a Boehm transformation) means "M^{pi}" or "pi(M)" *)
Definition apply_def :
    apply pi = FOLDR $o I pi
End

(* NOTE: either FOLDL or FOLDR is correct (due to combinTheory.o_ASSOC),
         but FOLDR seems more natural requiring natural list induction in
         the next proof(s), while FOLDL would require SNOC_INDUCT.
 *)
Theorem apply_alt :
    !pi. apply pi = FOLDL $o I pi
Proof
    REWRITE_TAC [apply_def]
 >> Induct_on ‘pi’ >> rw []
 >> KILL_TAC (* only FOLDL is left *)
 >> Induct_on ‘pi’ using SNOC_INDUCT
 >> rw [FOLDL_SNOC]
 >> POP_ASSUM (rw o wrap o SYM)
QED

(* Lemma 10.3.4 (i) *)
Theorem Boehm_transform_ctxt :
    !pi. Boehm_transform pi ==> ?c. ctxt c /\ !M. apply pi M == c M
Proof
    Induct_on ‘pi’
 >> rw [Boehm_transform_def, apply_def]
 >- (Q.EXISTS_TAC ‘\x. x’ >> rw [ctxt_rules])
 >> fs [GSYM Boehm_transform_def, apply_def]
 >> fs [solving_transform_def]
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘\y. c y @@ (\y. VAR x) y’ >> rw [ctxt_rules] \\
      MATCH_MP_TAC lameq_APPL >> art [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘\y. (\z. LAM x (c z)) y @@ (\y. N) y’ \\
      rw [ctxt_rules, constant_contexts_exist] \\
      MATCH_MP_TAC lameq_TRANS \\
      Q.EXISTS_TAC ‘[N/x] (c M)’ \\
      reverse CONJ_TAC >- rw [lameq_rules] \\
      irule lameq_sub_cong >> rw [] ]
QED

(* Definition 10.3.5 (ii) *)
Definition head_original_def :
    head_original M0 = let n = LAMl_size M0;
                          vs = FRESH_list n (FV M0);
                          M1 = principle_hnf (M0 @* (MAP VAR vs));
                       in
                          EVERY (\e. hnf_head M1 # e) (hnf_children M1)
End

(* Definition 10.3.5 (iii) *)
Definition is_ready_def :
    is_ready M <=> unsolvable M \/
                  ~is_abs (principle_hnf M) /\ head_original (principle_hnf M)
End
(* Lemma 10.3.6 (i) *)
Theorem lemma10_3_6i :
    !M. ?pi. is_ready (apply pi M)
Proof
    cheat
QED

(* Lemma 10.4.1 (i) *)
Theorem separability_lemma1 :
    !M N. solvable (M :term) /\ solvable N /\ ~equivalent M N ==>
          !P Q. ?pi. apply pi M == P /\ apply pi N == Q
Proof
    cheat
QED

(* Lemma 10.4.1 (ii)

   NOTE: If M is solvable, then N is either solvable (but not equivalent),
         or just unsolvable.
 *)
Theorem separability_lemma2 :
    !M N. solvable M /\ ~equivalent M N ==>
          !P. ?pi. apply pi M == P /\ ~solvable (apply pi N)
Proof
    cheat
QED

(* Theorem 10.4.2 (i) *)
Theorem separability_thm :
    !M N. benf M /\ benf N /\ M <> N ==>
          !P Q. ?pi. apply pi M == P /\ apply pi N = Q
Proof
    cheat
QED

(* Theorem 10.4.2 (ii) *)
Theorem closed_separability_thm :
    !M N. benf M /\ benf N /\ M <> N /\ FV M = {} /\ FV N = {} ==>
          !P Q. ?L. M @* L == P /\ N @* L == Q
Proof
    cheat
QED

(* Theorem 2.1.36 [1, p.34] or Corollary 15.1.5

   NOTE: This theorem is not necessary if the antecedent of Theorem 2.1.40 is
         replaced by ‘has_benf M /\ has_benf N’.
 *)
Theorem has_benf_iff_has_bnf :
    !M. has_benf M <=> has_bnf M
Proof
    cheat
QED

(* Theorem 2.1.39 [1, p.35] or Theorem 10.4.3 (i) [1, p.256] *)
Theorem benf_incompatible :
    !M N. benf M /\ benf N /\ M <> N ==> incompatible M N
Proof
    cheat
QED

val _ = set_fixity "RINSERT" (Infixr 490);

(* ‘RINSERT’ inserts one more pair into an existing relation *)
Definition RINSERT :
    $RINSERT r R = \x y. R x y \/ (x = FST r /\ y = SND r)
End

(* Theorem 2.1.40 [1, p.35] (Hilbert-Post completeness of lambda(beta)+eta) *)
Theorem lameta_complete :
    !M N. has_bnf M /\ has_bnf N ==>
          lameta M N \/ ~consistent (conversion ((M,N) RINSERT (beta RUNION eta)))
Proof
    cheat
QED

val _ = export_theory ();
val _ = html_theory "boehm_tree";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
