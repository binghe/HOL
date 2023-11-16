(*---------------------------------------------------------------------------*
 * boehm_treeScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])         *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory rich_listTheory
     llistTheory relationTheory ltreeTheory pathTheory posetTheory hurdUtils;

open binderLib nomsetTheory termTheory appFOLDLTheory chap2Theory chap3Theory
     head_reductionTheory standardisationTheory solvableTheory reductionEval;

val _ = new_theory "boehm";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)

(* Theorem 2.1.36 [1, p.34] aka Corollary 15.1.5 [1, p.386]

   NOTE: This theorem is not necessary if the antecedent of Theorem 2.1.40 is
         replaced by ‘has_benf M /\ has_benf N’.

   Used by: has_bnf_imp_lameta_complete
 *)
Theorem has_benf_iff_has_bnf :
    !M. has_benf M <=> has_bnf M
Proof
    cheat
QED

(*---------------------------------------------------------------------------*
 *  ltreeTheory extras
 *---------------------------------------------------------------------------*)

Definition ltree_node_def :
    ltree_node (Branch a ts) = (a,ts)
End

Overload ltree_head     = “\A. FST (ltree_node A)”
Overload ltree_children = “\A. SND (ltree_node A)”

Definition ltree_paths_def :
    ltree_paths A = {p | IS_SOME (ltree_lookup A p)}
End

Theorem NIL_IN_ltree_paths[simp] :
    [] IN ltree_paths A
Proof
    rw [ltree_paths_def, ltree_lookup_def]
QED

(* TODO: can ‘ltree_finite A’ be removed? *)
Theorem ltree_paths_alt :
    !A. ltree_finite A ==> ltree_paths A = {p | IS_SOME (ltree_el A p)}
Proof
    HO_MATCH_MP_TAC ltree_finite_ind
 >> rw [ltree_paths_def]
 >> rw [GSYM SUBSET_ANTISYM_EQ, SUBSET_DEF] (* 2 subgoals, same tactics *)
 >> ( POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (‘x’, ‘p’) \\
      Induct_on ‘p’ >- rw [ltree_lookup_def, ltree_el_def] \\
      rw [ltree_lookup_def, ltree_el_def] \\
      Cases_on ‘LNTH h (fromList ts)’ >> fs [] \\
      Cases_on ‘h < LENGTH ts’ >> fs [LNTH_fromList] \\
      Q.PAT_X_ASSUM ‘EVERY P ts’ (MP_TAC o REWRITE_RULE [EVERY_EL]) \\
      DISCH_THEN (MP_TAC o (Q.SPEC ‘h’)) \\
      RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o REWRITE_RULE [GSYM SUBSET_ANTISYM_EQ]) \\
      rw [SUBSET_DEF] )
QED

(* ltree_subset A B <=> A results from B by "cutting off" some subtrees. Thus,

   1) The paths of A is a subset of paths of B
   2) The node contents for all paths of A is identical to those of B, but the number
      of successors at those nodes of B may be different (B may have more successors)

   NOTE: Simply defining ‘ltree_subset A B <=> subtrees A SUBSET subtrees B’ is wrong,
         as A may appear as a non-root subtree of B, i.e. ‘A IN subtrees B’ but there's
         no way to "cut off" B to get A, the resulting subtree in B always have some
         more path prefixes.
 *)
Definition ltree_subset_def :
    ltree_subset A B <=>
       (ltree_paths A) SUBSET (ltree_paths B) /\
       !p. p IN ltree_paths A ==>
           ltree_head (THE (ltree_lookup A p)) =
           ltree_head (THE (ltree_lookup B p))
End

(*---------------------------------------------------------------------------*
 *  Boehm tree
 *---------------------------------------------------------------------------*)

(* The type of Boehm tree:

   For each ltree node, ‘NONE’ represents {\bot} (for unsolvable terms), while
  ‘SOME (vs,t)’ represents ‘LAMl vs t’ (|- ?y. t = VAR y). The separation of vs
   and t has two purposes:

   1. ‘set vs’ is the set of binding variables (BV) at that ltree node.
   2. ‘LAMl vs t’ can be easily "expanded" (w.r.t. eta reduction) into terms
      such as ‘LAMl (vs ++ [z0;z1]) t’ (with two extra children ‘z0’ and ‘z1’)
      without changing ‘t’ (dB encoding requires extra lifts of ‘t’).
 *)
Type boehm_tree[pp] = “:(string list # term) option ltree”

(* The needed unfolding function for ltree_unfold for Boehm Tree

   NOTE: the purposes of ‘X’ is to eliminate more names when generating binding
   variables in the tree.
 *)
Definition BT_generator_def :
    BT_generator (X :string set) (M :term) =
      if solvable M then
         let M0 = principle_hnf M;
              n = LAMl_size M0;
             vs = FRESH_list n (X UNION FV M0);
             M1 = principle_hnf (M0 @* (MAP VAR vs));
             M2 = (vs,hnf_head M1)
         in
            (SOME M2,fromList (hnf_children M1))
      else
        (NONE, LNIL)
End

Definition BT_def :
    BT X = ltree_unfold (BT_generator X)
End

(* Boehm tree of a single free variable *)
Definition BT_VAR_def :
    BT_VAR x :boehm_tree = Branch (SOME (NIL,VAR x)) LNIL
End

(* Remarks 10.1.3 (iii) [1, p.216]: unsolvable terms all have the same Boehm
   tree (‘bot’). The following overloaded ‘bot’ may be returned by
  ‘THE (ltree_lookup A p)’ when looking up a terminal node of the Boehm tree.
 *)
Overload bot = “Branch NONE (LNIL :boehm_tree llist)”

(* Another form of ‘bot’, usually returned by “THE (ltree_el A p)”. *)
Overload bot = “(NONE :(string list # term) option, SOME 0)”

(* Unicode name: "base" *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x22A5, tmnm = "bot"};
val _ = TeX_notation {hol = "bot", TeX = ("\\ensuremath{\\bot}", 1)};

(* some easy theorems about Boehm trees of unsolvable terms *)
Theorem unsolvable_BT :
    !X M. unsolvable M ==> BT X M = bot
Proof
    rw [BT_def, BT_generator_def, ltree_unfold, ltree_map]
QED

Theorem unsolvable_BT_EQ :
    !X M N. unsolvable M /\ unsolvable N ==> BT X M = BT X N
Proof
    rw [unsolvable_BT]
QED

(* ‘Boehm’ is the set of trees that are the tree of a lambda term *)
Definition Boehm_def :
    Boehm X = {BT X M | T}
End

(* Proposition 10.1.6 [1, p.219] *)
Theorem lameq_cong_BT :
    !X M N. M == N ==> BT X M = BT X N
Proof
    cheat
QED

(*---------------------------------------------------------------------------*
 * FV (free variables) and BV (binding variables) of Boehm trees
 *---------------------------------------------------------------------------*)

(* ‘BV_of_ltree_node’ directly takes out the binding variable list stored in
   the Boehm tree.
 *)
Definition BV_of_ltree_node_def :
    BV_of_ltree_node (M :boehm_tree) p =
       let node = ltree_el M p in
       if IS_SOME node then
          let (vs,t) = THE (FST (THE node)) in set vs
          else EMPTY
End

Theorem BV_of_ltree_node_applied =
    SIMP_RULE std_ss [LET_DEF] BV_of_ltree_node_def

Definition BV_of_ltree_path_def :
    BV_of_ltree_path (M :boehm_tree) p =
         if p = [] then BV_of_ltree_node M p
         else BV_of_ltree_path M (FRONT p) UNION
              BV_of_ltree_node M p
Termination
    WF_REL_TAC ‘measure (LENGTH o SND)’
 >> rw [LENGTH_FRONT]
 >> fs [NOT_NIL_EQ_LENGTH_NOT_0]
End

Overload BV = “BV_of_ltree_path”

(* A concrete Boehm tree *)
val example_10_1_20 =
   “Branch (SOME ([x; y],VAR z)) [| BT_VAR x; BT_VAR y |]”;

Definition FV_of_ltree_node_def :
    FV_of_ltree_node (M :boehm_tree) p =
      let node = ltree_el M p in
          if IS_SOME node then
             let (vs,t) = THE (FST (THE node)) in FV t DIFF set vs
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
    !X M. FV (BT X M) = {} ==> closed M
Proof
    cheat
QED

(*---------------------------------------------------------------------------*
 *  Infinite eta reduction for trees
 *---------------------------------------------------------------------------*)

(* A (underlying) "naked" tree has only the structure (i.e. valid paths).

   NOTE: When building an Boehm tree expansion, the naked tree may be used for
   holding the combined set of binding variables up to the current tree node.
 *)
Type naked_tree[pp] = “:string set ltree”

(* from a set of ltree paths to a naked ltree.

   NOTE: A typical source of input X is ‘ltree_paths’ of any ltree.
*)
Definition fromPaths_def :
    fromPaths (X :num list set) :naked_tree =
       gen_ltree (\p. ({},SOME (CARD {x | SNOC x p IN X})))
End

Theorem ltree_paths_fromPaths :
    !X. ltree_paths (fromPaths X) = X
Proof
    cheat
QED

Theorem fromPaths_ltree_paths :
    !(A :naked_tree). fromPaths (ltree_paths A) = A
Proof
    cheat
QED

(* ‘denude (A :'a ltree)’ (or |A| in textbook) is the underlying naked tree of A *)
Definition denude_def :
    denude = ltree_map (\e. {})
End

Theorem denude_alt :
    !A. denude A = fromPaths (ltree_paths A)
Proof
    cheat
QED

(* ‘ltree_finite’ means finite branching *)
Theorem ltree_finite_BT :
    !X M. ltree_finite (BT X M)
Proof
    cheat
QED

(* Definition 10.2.8 (i) [1, p.232]:

   An one-step eta-expansion of A at path p is the result A' of replacing in A the
   subtree ‘ltree_lookup A p’ by another subtree with modified tree node and one more
   tree branch.
 *)
Definition eta_expansion1_def :
    eta_expansion1 (A :boehm_tree) (A' :boehm_tree) p =
    case (THE (ltree_lookup A p)) of
    Branch a ts =>
      case a of
        SOME (vs,t) => {A' | ?z. ~MEM z vs /\ z NOTIN FV A /\
                             A' = Branch (SOME (SNOC z vs,t)) (LAPPEND ts [| BT_VAR z |])}
      | NONE => {}
End

(* Definition 10.2.10 (i) *)
val _ = set_fixity "extends" (Infixr 490);

Definition extends_def :
    $extends (ts :naked_tree) (A :boehm_tree) <=>
       ltree_paths A SUBSET (ltree_paths ts) /\ ltree_finite ts /\
       !p. p IN (ltree_paths A) /\ THE (ltree_el A p) = bot ==>
           SND (THE (ltree_el ts p)) = SOME 0
End

(* Definition 10.2.10 (ii)

   NOTE: 1) The generator follows the structure of X (the naked tree) and thus must
         pass the original subtrees as SND of pairs for each generated children.

         2) The relatively simple definition should be able to cover all four cases
         mentioned in the textbook.
 *)
Definition eta_generator_def :
    eta_generator ((A,X) :boehm_tree # naked_tree) =
    if IS_SOME (ltree_head A) then
       let (vs,t) = THE (ltree_head A);
                Z = ltree_head X;           (* initially empty *)
               as = ltree_children A;
               xs = ltree_children X;
                m = THE (LLENGTH as);            (* never NONE *)
                n = THE (LLENGTH xs);            (* never NONE *)
              vs' = FRESH_list (n - m) (set vs UNION Z);
              as' = fromList (MAP BT_VAR vs')    (* maybe LNIL *)
       in
           (SOME (vs ++ vs',t), LZIP (LAPPEND as as',xs))
    else
       (NONE, LNIL)
End

(* generating eta expansions following a underlying naked tree *)
Definition eta_generate_def :
    eta_generate A ts = (ltree_unfold eta_generator) (A,ts)
End

(* Definition 10.2.10 (iii)

   NOTE: instead of following the textbook definition based on ‘expansion’:

   |- le_eta A B <=> ?X. X extends A /\ B = expansion A X

   We try to directly describe the relationship between A and B when ‘A <= B’

   NOTE: The 1st branch ‘!p. p IN ltree_paths A ==> ...’ also includes the case
         when ‘ltree_el A p = THE bot’ so is ‘ltree_el B p’.
 *)
Definition tree_le_eta_def :
    tree_le_eta (A :boehm_tree) (B :boehm_tree) <=>
   (!p. p IN ltree_paths A ==>
        p IN ltree_paths B /\ T) /\
   (!p. p IN ltree_paths B /\ p NOTIN ltree_paths A ==>
        T)
End

Overload "le_eta" = “tree_le_eta”

Theorem le_eta_imp_ltree_paths_subset :
    !A B. le_eta A B ==> ltree_paths A SUBSET ltree_paths B
Proof
    rw [tree_le_eta_def, SUBSET_DEF]
QED

(* This theorem connects ‘le_eta’ and ‘expansion’ (‘eta_generator’) *)
Theorem le_eta_expansion :
    !A B ts. ts extends A ==> le_eta A (eta_generate A ts)
Proof
    cheat
QED

(*---------------------------------------------------------------------------*
 *  Equivalent terms
 *---------------------------------------------------------------------------*)

(* Definition 10.2.19

   M = LAMl v1 (y  @* Ms) @@ (MAP VAR v1) == y  @* Ms'
   N = LAMl v2 (y' @* Ns) @@ (MAP VAR v2) == y' @* Ns'

   LENGTH Ms  = n /\ LENGTH Ns  = n'
   LENGTH Ms' = m /\ LENGTH Ns' = m'

   y = y'
   n - m = n' - m' (possibly negative) <=> n + m' = n' + m (non-negative)
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
Theorem not_equivalent_example :
    !x y. x <> y ==> ~equivalent (LAM x (VAR y @@ M)) (LAM y (VAR y @@ M))
Proof
    NTAC 3 STRIP_TAC
 >> ‘hnf (LAM x (VAR y @@ M)) /\ hnf (LAM y (VAR y @@ M))’ by rw []
 >> ‘solvable (LAM x (VAR y @@ M)) /\ solvable (LAM y (VAR y @@ M))’
       by rw [solvable_iff_has_hnf, hnf_has_hnf]
 >> simp [equivalent_def, principle_hnf_eq_self]
 >> ‘{y} UNION FV M DELETE y = FV M DELETE y’ by SET_TAC []
 >> POP_ORW
 >> ‘{y} UNION FV M DELETE x = (y INSERT FV M) DELETE x’ by SET_TAC []
 >> POP_ORW
 >> qabbrev_tac ‘ns = (y INSERT FV M) DELETE x UNION (FV M DELETE y)’
 >> ‘FINITE ns’ by rw [Abbr ‘ns’]
 >> drule (Q.SPECL [‘1’, ‘ns’] FRESH_list_def) >> STRIP_TAC
 >> qabbrev_tac ‘vs = FRESH_list 1 ns’
 >> qabbrev_tac ‘z = HD vs’
 >> ‘vs = [z]’ by METIS_TAC [SING_HD]
 >> simp [appstar_thm]
 (* applying principle_hnf_beta *)
 >> qabbrev_tac ‘t = VAR y @@ M’
 >> ‘hnf t’ by rw [Abbr ‘t’]
 >> Know ‘principle_hnf (LAM x t @@ VAR z) = [VAR z/x] t’
 >- (MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘t’] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs) ns’ MP_TAC \\
     rw [DISJOINT_ALT, Abbr ‘ns’] >> fs [])
 >> Rewr'
 >> Know ‘principle_hnf (LAM y t @@ VAR z) = [VAR z/y] t’
 >- (MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘t’] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs) ns’ MP_TAC \\
     rw [DISJOINT_ALT, Abbr ‘ns’] >> fs [])
 >> Rewr'
 >> DISJ1_TAC
 >> simp [Abbr ‘t’]
 >> NTAC 5 (simp [Once hnf_head_def])
 (* final goal: y <> z *)
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs) ns’ MP_TAC
 >> rw [DISJOINT_ALT, Abbr ‘ns’] >> fs []
QED

Theorem equivalent_example :
    equivalent (LAM x (VAR x @@ M)) (LAMl [y; z] (VAR y @* [M; N]))
Proof
    ‘hnf (LAM x (VAR y @@ M)) /\
     hnf (LAMl [y; z] (VAR y @* [M; N]))’ by rw [hnf_appstar]
 >> ‘solvable (LAM x (VAR y @@ M)) /\
     solvable (LAMl [y; z] (VAR y @* [M; N]))’
       by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> simp [equivalent_def, principle_hnf_eq_self]
 >> ‘MAX 1 (LAMl_size (LAMl [y; z] (VAR y @* [M; N]))) = 2’
       by rw [LAMl_thm, appstar_thm]
 >> POP_ORW
 >> Know ‘({x} UNION FV M DELETE x UNION FV (LAMl [y; z] (VAR y @* [M; N]))) =
          (FV M DELETE x) UNION (FV M UNION FV N DELETE y DELETE z)’
 >- (rw [LAMl_thm, appstar_thm] >> SET_TAC [])
 >> Rewr'
 >> qabbrev_tac ‘ns = (FV M DELETE x) UNION (FV M UNION FV N DELETE y DELETE z)’
 >> qabbrev_tac ‘vs = FRESH_list 2 ns’
 >> qabbrev_tac ‘vs1 = TAKE 1 vs’
 >> qabbrev_tac ‘vs2 = TAKE 2 vs’
 (* applying principle_hnf_LAMl_appstar *)
 >> cheat
QED

Theorem equivalent_unsolvables :
    !M N. unsolvable M /\ unsolvable N ==> equivalent M N
Proof
    rw [equivalent_def]
QED

(* Definition 10.2.21 (i) [1, p.238]

   NOTE: ‘A’ and ‘B’ are ltree nodes returned by ‘THE (ltree_el (BT M) p)’
 *)
Definition head_equivalent_def :
    head_equivalent (A :(string list # term) option # num option) B =
        if IS_SOME (FST A) /\ IS_SOME (FST B) then
           let (vs1,y ) = THE (FST A);
               (vs2,y') = THE (FST B);
               n  = LENGTH vs1;
               n' = LENGTH vs2;
               m  = THE (SND A);
               m' = THE (SND B)
            in
               y = y' /\ n + m' = n' + m
        else
            IS_NONE (FST A) /\ IS_NONE (FST B)
End

(* Definition 10.2.21 (ii) [1, p.238] *)
Definition subtree_eta_equiv_def :
    subtree_eta_equiv p (A :boehm_tree) (B :boehm_tree) =
        let A' = ltree_el A p;
            B' = ltree_el B p
        in
            if IS_SOME A' /\ IS_SOME B' then
               head_equivalent (THE A') (THE B')
            else
               IS_NONE A' /\ IS_NONE B'
End
Overload eta_sub_equiv = “subtree_eta_equiv”

(* Definition 10.2.23 (i) [1, p.239] *)
Definition eta_subset_def :
    eta_subset (A :boehm_tree) (B :boehm_tree) =
       ?A'. le_eta A A' /\ ltree_subset A' B
End

(* Definition 10.2.23 (ii) [1, p.239] *)
Definition eta_subset_eta_def :
    eta_subset_eta A B = ?A' B'. le_eta A A' /\ le_eta B B' /\ ltree_subset A' B'
End

(* Definition 10.2.25 [1, p.240] *)
Definition tree_eta_equiv_def :
    tree_eta_equiv A B <=> eta_subset_eta A B /\ eta_subset_eta B A
End

(* ‘eta_equiv’ is an equivalence relation over Boehm trees *)
val _ = set_fixity "=e=" (Infixr 490);
Overload "=e=" = “tree_eta_equiv”

(* Theorem 10.2.31, (i) <=> (iv) [1, p.244] *)
Theorem tree_eta_equiv_thm :
    !A B. tree_eta_equiv A B <=> !p. subtree_eta_equiv p A B
Proof
    cheat
QED

(* Definition 10.2.32 (iii) [1, p.245] *)
Definition term_le_eta_def :
    term_le_eta M N = let X = FV M UNION FV N in
                          tree_le_eta (BT X M) (BT X N)
End
Overload "le_eta" = “term_le_eta”

(* Definition 10.2.32 (iv) [1, p.245] *)
Definition term_eta_equiv_def :
    term_eta_equiv M N = let X = FV M UNION FV N in
                           tree_eta_equiv (BT X M) (BT X N)
End
Overload eta_equiv = “term_eta_equiv”

(* Definition 10.2.32 (v) [1, p.245] *)
Definition subterm_eta_equiv_def :
    subterm_eta_equiv p M N =
        let X = FV M UNION FV N in
            subtree_eta_equiv p (BT X M) (BT X N)
End
Overload eta_sub_equiv = “subterm_eta_equiv”

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

Theorem Boehm_transform_CONS[simp] :
    Boehm_transform (h::pi) <=> solving_transform h /\ Boehm_transform pi
Proof
    rw [Boehm_transform_def]
QED

Theorem Boehm_transform_SNOC[simp] :
    Boehm_transform (SNOC h pi) <=> Boehm_transform pi /\ solving_transform h
Proof
    rw [Boehm_transform_def, EVERY_SNOC]
QED

(* ‘apply pi M’ (applying a Boehm transformation) means "M^{pi}" or "pi(M)"

   NOTE: ‘apply [f1;f2;f3] M’ should be equivalent to ‘f3 (f2 (f1 M))’, thus
         this is naturally a FOLDR with REVERSE.
 *)
Definition apply_def :
    apply pi = FOLDR $o I (REVERSE pi)
End

(* Used by apply_alt *)
Theorem FOLDL_FOLDR_o_I[local] :
    FOLDL $o I = FOLDR $o I 
Proof
    simp [Once EQ_SYM_EQ, Once FUN_EQ_THM]
 >> Q.X_GEN_TAC ‘pi’
 >> Induct_on ‘pi’ >> rw [FOLDL, FOLDR]
 >> KILL_TAC (* only FOLDL is left *)
 >> Induct_on ‘pi’ using SNOC_INDUCT
 >> rw [FOLDL_SNOC, FOLDL]
 >> POP_ASSUM (rw o wrap o SYM)
QED

(* |- !pi. apply pi = FOLDL $o I (REVERSE pi)

   Used by: apply_CONS
 *)
Theorem apply_alt = REWRITE_RULE [SYM FOLDL_FOLDR_o_I] apply_def

Theorem apply_empty[simp] :
    apply [] = I
Proof
    rw [apply_def]
QED

Theorem apply_CONS[simp] :
    !f pi M. apply (f::pi) M = apply pi (f M)
Proof
    rw [apply_alt, o_DEF, GSYM SNOC_APPEND]
 >> rw [FOLDL_SNOC]
QED

Theorem apply_SNOC[simp] : 
    !f pi M. apply (SNOC f pi) M = f (apply pi M)
Proof
    rw [apply_def, o_DEF, GSYM SNOC_APPEND, REVERSE_SNOC]
QED

(* Lemma 10.3.4 (i) [1, p.246] *)
Theorem Boehm_transform_lameq_ctxt :
    !pi. Boehm_transform pi ==> ?c. ctxt c /\ !M. apply pi M == c M
Proof
    Induct_on ‘pi’ using SNOC_INDUCT
 >> rw [Boehm_transform_def, apply_def]
 >- (Q.EXISTS_TAC ‘\x. x’ >> rw [ctxt_rules])
 >> fs [GSYM Boehm_transform_def, apply_def]
 >> fs [solving_transform_def]
 >- (rename1 ‘x = \p. p @@ VAR y’ \\
     Q.EXISTS_TAC ‘\z. c z @@ (\z. VAR y) z’ >> rw [ctxt_rules] \\
     MATCH_MP_TAC lameq_APPL >> art [])
 (* stage work *)
 >> rename1 ‘x = [N/y]’
 >> Q.EXISTS_TAC ‘\z. (\z. LAM y (c z)) z @@ (\z. N) z’
 >> rw [ctxt_rules, constant_contexts_exist, FOLDR]
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘[N/y] (c M)’
 >> reverse CONJ_TAC >- rw [lameq_rules]
 >> irule lameq_sub_cong >> rw []
QED

(* Lemma 10.3.4 (ii) [1, p.246]

   Used by: Boehm_transform_lameq_appstar
 *)
Theorem Boehm_transform_lameq_LAMl_appstar :
    !pi. Boehm_transform pi ==>
         ?c. ctxt c /\ (!M. apply pi M == c M) /\
             !xs. FINITE xs ==>
                  ?Ns. !M. FV M SUBSET xs ==> c M == (LAMl (SET_TO_LIST xs) M) @* Ns
Proof
    cheat
QED

(* An corollary of the above lemma with ‘xs = {}’

   Used by: closed_separability_thm
 *)
Theorem Boehm_transform_lameq_appstar :
    !pi. Boehm_transform pi ==>
         ?Ns. !M. closed M ==> apply pi M == M @* Ns
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP Boehm_transform_lameq_LAMl_appstar))
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘{}’))
 >> rw [closed_def]
 >> Q.EXISTS_TAC ‘Ns’
 >> RW_TAC (betafy (srw_ss())) []
QED

(* Used by: distinct_benf_imp_inconsistent *)
Theorem Boehm_transform_asmlam_apply_cong :
    !pi M N. Boehm_transform pi /\ asmlam eqns M N ==>
             asmlam eqns (apply pi M) (apply pi N)
Proof
    Induct_on ‘pi’ >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> fs [Boehm_transform_def, solving_transform_def]
 >- rw [asmlam_rules]
 >> MATCH_MP_TAC asmlam_subst >> art []
QED

(* Used by: separability_lemma2 *)
Theorem Boehm_transform_lameq_apply_cong :
    !pi M N. Boehm_transform pi /\ M == N ==> apply pi M == apply pi N
Proof
    Induct_on ‘pi’ >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> fs [Boehm_transform_def, solving_transform_def]
 >- rw [lameq_rules]
 >> rw [lameq_sub_cong]
QED

(* Used by separability_thm *)
Theorem Boehm_transform_APPEND :
    !pi pi2. Boehm_transform p1 /\ Boehm_transform p2 ==> Boehm_transform (p1 ++ p2)
Proof
    rw [Boehm_transform_def]
QED

(* Used by separability_thm *)
Theorem Boehm_transform_apply_apply :
    !p1 p2 M. apply p1 (apply p2 M) = apply (p2 ++ p1) M
Proof
    Q.X_GEN_TAC ‘p1’
 >> Induct_on ‘p2’
 >> rw [APPEND_SNOC]
QED

(* Used by separability_lemma2 *)
Theorem apply_MAP_rightctxt_eq_appstar :
    !Ns t. apply (MAP rightctxt Ns) t = t @* Ns
Proof
    Induct_on ‘Ns’ >> rw [rightctxt_thm]
QED

(* Used by separability_lemma2 *)
Theorem unsolvable_apply :
    !pi M. Boehm_transform pi /\ unsolvable M ==> unsolvable (apply pi M)
Proof
    Induct_on ‘pi’ >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> fs [solving_transform_def, solvable_iff_has_hnf] (* 2 subgaols *)
 >| [ (* goal 1 (of 2) *)
      CCONTR_TAC >> fs [] \\
      METIS_TAC [has_hnf_APP_E],
      (* goal 2 (of 2) *)
      CCONTR_TAC >> fs [] \\
      METIS_TAC [has_hnf_SUB_E] ]
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
Theorem Boehm_transform_is_ready_exists :
    !M. ?pi. Boehm_transform pi /\ is_ready (apply pi M)
Proof
    cheat
QED

(* Definition 10.3.10 (ii) *)
Definition is_faithful_def :
    is_faithful p Fs pi =
       !M N. M IN Fs /\ N IN Fs ==>
            (subterm_eta_equiv p M N <=> equivalent (apply pi M) (apply pi N)) /\
            (!X. IS_SOME (ltree_lookup (BT X M) p) <=>
                 solvable (apply pi M))
End

Definition term_agrees_upto_def :
    term_agrees_upto M N p <=>
      !q. q <<= p ==> !X. ltree_el (BT X M) q = ltree_el (BT X N) q
End

(* Definition 10.3.10 (iv) *)
val _ = set_fixity "agrees_upto" (Infixr 490);
Definition agrees_upto_def :
    $agrees_upto Fs p = !M N. M IN Fs /\ N IN Fs ==> term_agrees_upto M N p
End

(* Lemma 10.3.11 (3) [1. p.251] *)
Theorem agrees_upto_lemma :
    !Fs p. Fs agrees_upto p ==>
           ?pi. Boehm_transform pi /\
                !M N. M IN Fs /\ N IN Fs ==>
                     (subterm_eta_equiv p M N <=>
                      subterm_eta_equiv p (apply pi M) (apply pi N))
Proof
    cheat
QED

(* Proposition 10.3.13 [1, p.253]

   Used by separability_thm
 *)
Theorem agrees_upto_thm :
    !Fs p. Fs agrees_upto p ==> ?pi. Boehm_transform pi /\ is_faithful p Fs pi
Proof
    cheat
QED

(*---------------------------------------------------------------------------*
 *  Separability of terms
 *---------------------------------------------------------------------------*)

(* Lemma 10.4.1 (i)

   Used by separability_thm, separability_lemma2
 *)
Theorem separability_lemma1 :
    !M N. solvable (M :term) /\ solvable N /\ ~equivalent M N ==>
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    cheat
QED

(* Lemma 10.4.1 (ii) *)
Theorem separability_lemma2 :
    !M N. solvable M /\ ~equivalent M N ==>
          !P. ?pi. Boehm_transform pi /\ apply pi M == P /\ ~solvable (apply pi N)
Proof
    rpt STRIP_TAC
 (* applying separability_lemma1, ‘~equivalent M N’ is only used here *)
 >> Cases_on ‘solvable N’
 >- (‘!P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q’
         by METIS_TAC [separability_lemma1] \\
     POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘P’, ‘Omega’])) \\
     Q.EXISTS_TAC ‘pi’ >> art [] \\
     METIS_TAC [lameq_solvable_cong, unsolvable_Omega])
 (* stage work *)
 >> ‘?M0. M == M0 /\ hnf M0’ by METIS_TAC [has_hnf_def, solvable_iff_has_hnf]
 >> ‘?vs args y. ALL_DISTINCT vs /\ M0 = LAMl vs (VAR y @* args)’
       by METIS_TAC [hnf_cases]
 >> qabbrev_tac ‘X = set vs UNION FV (VAR y @* args)’
 >> qabbrev_tac ‘n = LENGTH vs’
 >> qabbrev_tac ‘as = FRESH_list n X’
 >> qabbrev_tac ‘pi = SNOC [LAMl as P/y] (MAP rightctxt (MAP VAR vs))’
 >> Q.EXISTS_TAC ‘pi’
 >> STRONG_CONJ_TAC
 >- (rw [Abbr ‘pi’, Boehm_transform_def, EVERY_SNOC, EVERY_MAP]
     >- (rw [EVERY_MEM, solving_transform_def, FUN_EQ_THM, rightctxt_thm]) \\
     rw [solving_transform_def] \\
     DISJ2_TAC >> qexistsl_tac [‘y’, ‘LAMl as P’] >> rw [])
 >> DISCH_TAC
 (* applying unsolvable_apply *)
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC unsolvable_apply >> art [])
 (* stage work *) 
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply pi M0’
 >> CONJ_TAC >- (MATCH_MP_TAC Boehm_transform_lameq_apply_cong >> art [])
 >> POP_ASSUM K_TAC (* ‘Boehm_transform pi’ is not needed here *)
 >> rw [Abbr ‘pi’]
 >> qabbrev_tac ‘pi :transform = MAP rightctxt (MAP VAR vs)’
 >> qabbrev_tac ‘t = VAR y @* args’
 (* applying apply_MAP_rightctxt_eq_appstar *)
 >> Know ‘apply pi (LAMl vs t) = LAMl vs t @* MAP VAR vs’
 >- rw [Abbr ‘pi’, apply_MAP_rightctxt_eq_appstar]
 >> Rewr'
 (* applying lameq_LAMl_appstar *)
 >> cheat
QED

(* Exercise 10.6.9 [1, p.272]. It may avoid using Theorem 10.2.31.

   NOTE: the actual statements have ‘has_benf M /\ has_benf N’

   Used by: separability_thm
 *)
Theorem distinct_benf_no_subterm_eta_equiv :
    !M N. benf M /\ benf N /\ M <> N ==> ?p. ~subterm_eta_equiv p M N
Proof
    cheat
QED

(* Theorem 10.4.2 (i) [1, p.256]

   Used by: distinct_benf_imp_inconsistent
 *)
Theorem separability_thm :
    !M N. benf M /\ benf N /\ M <> N ==>
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    rpt STRIP_TAC
 (* TODO: find p with minimal length for ‘agrees_upto {M;N} p’ to hold *)
 >> ‘?p. ~subterm_eta_equiv p M N’
       by METIS_TAC [distinct_benf_no_subterm_eta_equiv]
 >> Know ‘{M; N} agrees_upto p’
 >- (cheat)
 >> DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP agrees_upto_thm))
 >> Know ‘~equivalent (apply pi M) (apply pi N)’
 >- (POP_ASSUM (MP_TAC o (Q.SPECL [‘M’, ‘N’]) o (REWRITE_RULE [is_faithful_def])) \\
     simp [])
 >> DISCH_TAC
 >> qabbrev_tac ‘M0 = apply pi M’
 >> qabbrev_tac ‘N0 = apply pi N’
 (* solvable mostly because M and N are bnf *)
 >> Know ‘solvable M0 /\ solvable N0’
 >- (rw [solvable_iff_has_hnf,
         Abbr ‘M0’, Abbr ‘N0’] (* 2 subgoals, same tactics *) \\
     cheat)
 >> STRIP_TAC
 >> ‘?pi. Boehm_transform pi /\ apply pi M0 == P /\ apply pi N0 == Q’
       by PROVE_TAC [separability_lemma1] (* this asserts pi' *)
 >> Q.EXISTS_TAC ‘pi ++ pi'’
 >> fs [Abbr ‘M0’, Abbr ‘N0’, Boehm_transform_APPEND, Boehm_transform_apply_apply]
QED

(* Theorem 10.4.2 (ii) [1, p.256] *)
Theorem closed_separability_thm :
    !M N. benf M /\ benf N /\ M <> N /\ closed M /\ closed N ==>
          !P Q. ?L. M @* L == P /\ N @* L == Q
Proof
    rpt STRIP_TAC
 >> ‘?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q’
       by METIS_TAC [separability_thm]
 >> ‘?Ns. !M. closed M ==> apply pi M == M @* Ns’
       by METIS_TAC [Boehm_transform_lameq_appstar]
 >> Q.EXISTS_TAC ‘Ns’
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘apply pi M’ >> art [] \\
      rw [lameq_SYM],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘apply pi N’ >> art [] \\
      rw [lameq_SYM] ]
QED

(* Corollary 10.4.3 (i) [1, p.256]

   Used by: distinct_benf_imp_incompatible
 *)
Theorem distinct_benf_imp_inconsistent :
    !M N. benf M /\ benf N /\ M <> N ==> inconsistent (asmlam {(M,N)})
Proof
    rw [inconsistent_def] >> rename1 ‘asmlam {(M,N)} P Q’
 >> ‘?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q’
       by METIS_TAC [separability_thm]
 >> qabbrev_tac ‘eqns = {(M,N)}’
 >> MATCH_MP_TAC asmlam_trans
 >> Q.EXISTS_TAC ‘apply pi M’
 >> CONJ_TAC >- (MATCH_MP_TAC lameq_asmlam >> rw [lameq_SYM])
 >> MATCH_MP_TAC asmlam_trans
 >> Q.EXISTS_TAC ‘apply pi N’
 >> reverse CONJ_TAC >- (MATCH_MP_TAC lameq_asmlam >> art [])
 >> MATCH_MP_TAC Boehm_transform_asmlam_apply_cong >> art []
 >> Suff ‘(M,N) IN eqns’ >- rw [asmlam_rules]
 >> rw [Abbr ‘eqns’]
QED

(* Theorem 2.1.39 [1, p.35]

   Used by: has_bnf_imp_lameta_complete
 *)
Theorem distinct_benf_imp_incompatible =
        REWRITE_RULE [GSYM incompatible_def] distinct_benf_imp_inconsistent

val _ = set_fixity "RINSERT" (Infixr 490);

(* ‘RINSERT’ inserts one more pair into an existing relation

   NOTE: this definition cannot be moved into relationTheory as pairTheory is
         not yet defined when building relationTheory.
 *)
Definition RINSERT :
    $RINSERT r R = \x y. R x y \/ (x = FST r /\ y = SND r)
End

Theorem RINSERT_MONO :
    !r R x y. R x y ==> (r RINSERT R) x y
Proof
    rw [RINSERT]
QED

(* Theorem 2.1.40 [1, p.35] aka Corollary 10.4.3 (ii) [1, p.256]

   Also know as "Hilbert-Post completeness of lambda(beta)+eta".
 *)
Theorem has_bnf_imp_lameta_complete :
    !M N. has_bnf M /\ has_bnf N ==>
          lameta M N \/ ~consistent (conversion ((M,N) RINSERT (beta RUNION eta)))
Proof
    rpt STRIP_TAC
 >> ‘has_benf M /\ has_benf N’ by PROVE_TAC [has_benf_iff_has_bnf]
 (* NOTE: the definition of ‘has_benf’ may be wrong *)
 >> ‘?M'. lameta M M' /\ benf M'’ by METIS_TAC [has_benf_def]
 >> ‘?N'. lameta N N' /\ benf N'’ by METIS_TAC [has_benf_def]
 >> Cases_on ‘M' = N'’
 >- (DISJ1_TAC \\
     MATCH_MP_TAC lameta_TRANS \\
     Q.EXISTS_TAC ‘N'’ >> rw [lameta_rules])
 (* applying benf_incompatible *)
 >> DISJ2_TAC
 >> Know ‘incompatible M' N'’
 >- (MATCH_MP_TAC distinct_benf_imp_incompatible >> art [])
 >> rw [incompatible_def]
 >> MATCH_MP_TAC inconsistent_mono
 >> Q.EXISTS_TAC ‘asmlam {(M',N')}’ >> art []
 >> qabbrev_tac ‘R = (M,N) RINSERT beta RUNION eta’
 >> simp [RSUBSET]
 >> HO_MATCH_MP_TAC asmlam_ind >> rw [] (* 7 subgoals, only the first is hard *)
 (* goal 1 (of 7 *)
 >- (MATCH_MP_TAC conversion_trans >> Q.EXISTS_TAC ‘M’ \\
     CONJ_TAC
     >- (irule (REWRITE_RULE [RSUBSET] conversion_monotone) \\
         Q.EXISTS_TAC ‘beta RUNION eta’ \\
         CONJ_TAC >- rw [Abbr ‘R’, RINSERT] \\
         rw [beta_eta_lameta, Once lameta_SYM]) \\
     MATCH_MP_TAC conversion_trans >> Q.EXISTS_TAC ‘N’ \\
     reverse CONJ_TAC
     >- (irule (REWRITE_RULE [RSUBSET] conversion_monotone) \\
         Q.EXISTS_TAC ‘beta RUNION eta’ \\
         CONJ_TAC >- rw [Abbr ‘R’, RINSERT] \\
         rw [beta_eta_lameta]) \\
     Suff ‘R M N’ >- rw [conversion_rules] \\
     rw [Abbr ‘R’, RINSERT])
 >| [ (* goal 2 (of 7) *)
      Suff ‘R (LAM x M'' @@ N'') ([N''/x] M'')’ >- rw [conversion_rules] \\
      rw [Abbr ‘R’] >> MATCH_MP_TAC RINSERT_MONO \\
      rw [RUNION] >> DISJ1_TAC \\
      rw [beta_def] >> qexistsl_tac [‘x’, ‘M''’] >> rw [],
      (* goal 3 (of 7) *)
      rw [conversion_rules],
      (* goal 4 (of 7) *)
      METIS_TAC [conversion_rules],
      (* goal 5 (of 7) *)
      PROVE_TAC [conversion_compatible, compatible_def, rightctxt, rightctxt_thm],
      (* goal 6 (of 7) *)
      PROVE_TAC [conversion_compatible, compatible_def, leftctxt],
      (* goal 7 (of 7) *)
      PROVE_TAC [conversion_compatible, compatible_def, absctxt] ]
QED

val _ = export_theory ();
val _ = html_theory "boehm";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
