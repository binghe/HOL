(*---------------------------------------------------------------------------*
 * boehmScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])              *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory rich_listTheory
     llistTheory relationTheory ltreeTheory pathTheory posetTheory hurdUtils;

open binderLib nomsetTheory termTheory appFOLDLTheory chap2Theory chap3Theory
     head_reductionTheory standardisationTheory solvableTheory reductionEval;

open horeductionTheory takahashiTheory;

val _ = new_theory "boehm";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val o_DEF = combinTheory.o_DEF;

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
              vsM = TAKE n  vs;
              vsN = TAKE n' vs;
               M1 = principle_hnf (M0 @* (MAP VAR vsM));
               N1 = principle_hnf (N0 @* (MAP VAR vsN));
               y  = hnf_head M1;
               y' = hnf_head N1;
               m  = LENGTH (hnf_children M1);
               m' = LENGTH (hnf_children N1);
           in
               y = y' /\ n + m' = n' + m
        else
           ~solvable M /\ ~solvable N
End

Theorem equivalent_comm :
    !M N. equivalent M N <=> equivalent N M
Proof
    RW_TAC std_ss [equivalent_def, Once MAX_COMM, Once UNION_COMM]
 >- (rename1 ‘y2 = y3 /\ n1 + m3 = n3 + m2 <=> y = y1 /\ n + m1 = n1 + m’ \\
    ‘n3 = n’ by rw [Abbr ‘n3’, Abbr ‘n’] >> gs [] \\
     EQ_TAC >> rw [])
 >>  METIS_TAC []
QED

Theorem equivalent_of_solvables :
    !M N. solvable M /\ solvable N ==>
         (equivalent M N <=>
          let M0 = principle_hnf M;
              N0 = principle_hnf N;
              n  = LAMl_size M0;
              n' = LAMl_size N0;
              vs = FRESH_list (MAX n n') (FV M0 UNION FV N0);
             vsM = TAKE n  vs;
             vsN = TAKE n' vs;
              M1 = principle_hnf (M0 @* (MAP VAR vsM));
              N1 = principle_hnf (N0 @* (MAP VAR vsN));
              y  = hnf_head M1;
              y' = hnf_head N1;
              m  = LENGTH (hnf_children M1);
              m' = LENGTH (hnf_children N1);
           in
              y = y' /\ n + m' = n' + m)
Proof
    RW_TAC std_ss [equivalent_def]
QED

Theorem equivalent_of_hnf :
    !M N. hnf M /\ hnf N ==>
         (equivalent M N <=>
          let n  = LAMl_size M;
              n' = LAMl_size N;
              vs = FRESH_list (MAX n n') (FV M UNION FV N);
             vsM = TAKE n  vs;
             vsN = TAKE n' vs;
              M1 = principle_hnf (M @* (MAP VAR vsM));
              N1 = principle_hnf (N @* (MAP VAR vsN));
              y  = hnf_head M1;
              y' = hnf_head N1;
              m  = LENGTH (hnf_children M1);
              m' = LENGTH (hnf_children N1);
           in
              y = y' /\ n + m' = n' + m)
Proof
    rpt STRIP_TAC
 >> ‘solvable M /\ solvable N’ by PROVE_TAC [hnf_has_hnf, solvable_iff_has_hnf]
 >> RW_TAC std_ss [equivalent_def, principle_hnf_eq_self]
 >> METIS_TAC []
QED

(* Given a hnf ‘M0’ and a shared binding variable list ‘vs’

   hnf_tac adds the following abbreviation and new assumptions:

   Abbrev (M1 = principle_hnf (M0 @* MAP VAR (TAKE (LAMl_size M0) vs)))
   M0 = LAMl (TAKE (LAMl_size M0) vs) (VAR y @* args)
   M1 = VAR y @* args

   where the names "M1", "y" and "args" can be chosen from inputs.
 *)
fun hnf_tac (M0,vs,M1,y,args) = let val n = “LAMl_size ^M0” in
    qabbrev_tac ‘^M1 = principle_hnf (^M0 @* MAP VAR (TAKE ^n ^vs))’
 >> Know ‘?^y ^args. ^M0 = LAMl (TAKE ^n ^vs) (VAR ^y @* ^args)’
 >- (irule (iffLR hnf_cases_shared) >> rw [])
 >> STRIP_TAC
 >> Know ‘^M1 = VAR ^y @* ^args’
 >- (qunabbrev_tac ‘^M1’ \\
     Q.PAT_ASSUM ‘^M0 = LAMl (TAKE ^n ^vs) (VAR ^y @* ^args)’
        (fn th => REWRITE_TAC [Once th]) \\
     MATCH_MP_TAC principle_hnf_reduce >> rw [hnf_appstar])
 >> DISCH_TAC
end;

(* The following combined tactic is useful after:

   RW_TAC std_ss [equivalent_of_solvables, principle_hnf_eq_self]

   NOTE: it doesn't work with equivalent_of_hnf
 *)
val equivalent_tac =
    ‘hnf M0 /\ hnf N0’ by PROVE_TAC [hnf_principle_hnf, solvable_iff_has_hnf]
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M0 UNION FV N0) /\
     LENGTH vs = MAX n n'’ by rw [Abbr ‘vs’, FRESH_list_def]
 >> ‘DISJOINT (set vs) (FV M0) /\ DISJOINT (set vs) (FV N0)’
      by METIS_TAC [DISJOINT_SYM, DISJOINT_UNION]
 >> qunabbrevl_tac [‘M1’, ‘N1’]
 >> hnf_tac (“M0 :term”, “vs :string list”,
             “M1 :term”, “y1 :string”, “args1 :term list”)
 >> hnf_tac (“N0 :term”, “vs :string list”,
             “N1 :term”, “y2 :string”, “args2 :term list”)
 >> ‘TAKE (LAMl_size M0) vs = vsM’ by rw [Abbr ‘vsM’, Abbr ‘n’]
 >> ‘TAKE (LAMl_size N0) vs = vsN’ by rw [Abbr ‘vsN’, Abbr ‘n'’]
 >> NTAC 2 (POP_ASSUM (rfs o wrap))
 (* reshaping and reordering assumptions *)
 >> qunabbrev_tac ‘M1’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vsM)’
 >> qunabbrev_tac ‘N1’
 >> qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vsN)’
 >> Q.PAT_X_ASSUM ‘M0 = _’ ASSUME_TAC
 >> Q.PAT_X_ASSUM ‘N0 = _’ ASSUME_TAC
 >> Q.PAT_X_ASSUM ‘M1 = _’ ASSUME_TAC
 >> Q.PAT_X_ASSUM ‘N1 = _’ ASSUME_TAC
 >> ‘VAR y1 = y’  by rw [Abbr ‘y’ , hnf_head_absfree]
 >> ‘VAR y2 = y'’ by rw [Abbr ‘y'’, hnf_head_absfree];

(* From [1, p.238]. This concerte example shows that dB encoding is not easy in
   defining this "concept": the literal encoding of inner head variables are not
   the same for equivalent terms.
 *)
Theorem not_equivalent_example :
    !x y. x <> y ==> ~equivalent (LAM x (VAR y @@ M)) (LAM y (VAR y @@ M))
Proof
 (* NOTE: ‘y’ must avoid here for the shared equivalent_tac *)
    qx_genl_tac [‘x’, ‘v’] >> DISCH_TAC
 >> ‘hnf (LAM x (VAR v @@ M)) /\ hnf (LAM v (VAR v @@ M))’ by rw []
 >> ‘solvable (LAM x (VAR v @@ M)) /\ solvable (LAM v (VAR v @@ M))’
       by rw [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [equivalent_of_solvables, principle_hnf_eq_self]
 (* applying shared tactics *)
 >> equivalent_tac
 (* eliminating n and n' *)
 >> qunabbrevl_tac [‘n’, ‘n'’]
 >> Know ‘LAMl_size M0 = 1 /\ LAMl_size N0 = 1’
 >- (rw [Abbr ‘M0’, Abbr ‘N0’, LAMl_size_def])
 >> DISCH_THEN (rfs o wrap)
 (* eliminating vsM and vsN *)
 >> qabbrev_tac ‘z = HD vs’
 >> ‘vs = [z]’ by METIS_TAC [SING_HD]
 >> Q.PAT_X_ASSUM ‘vsN = vsM’ (rfs o wrap o SYM)
 >> rfs [Abbr ‘vsN’]
 >> POP_ASSUM (rfs o wrap)
 (* stage work *)
 >> qunabbrevl_tac [‘M0’, ‘N0’]
 >> DISJ1_TAC
 >> qunabbrevl_tac [‘y’, ‘y'’]
 (* applying principle_hnf_beta *)
 >> qabbrev_tac ‘t = VAR v @@ M’
 >> ‘hnf t’ by rw [Abbr ‘t’]
 >> Know ‘M1 = [VAR z/x] t’
 >- (qunabbrev_tac ‘M1’ \\
     Cases_on ‘z = x’ >- POP_ASSUM (rfs o wrap) \\
     MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘t’] \\
     rfs [FV_thm])
 >> Rewr'
 >> Know ‘N1 = [VAR z/v] t’
 >- (qunabbrev_tac ‘N1’ \\
     Cases_on ‘z = v’ >- POP_ASSUM (rfs o wrap) \\
     MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘t’] \\
     rfs [FV_thm])
 >> Rewr'
 >> simp [Abbr ‘t’]
 (* final goal: y <> z *)
 >> Q.PAT_X_ASSUM ‘z # LAM x (VAR v @@ M)’ MP_TAC
 >> simp [FV_thm] >> PROVE_TAC []
QED

(* NOTE: not easy, plus useless...
Theorem equivalent_example :
    !x y z. y <> z ==>
            equivalent (LAM x (VAR x @@ M)) (LAMl [y; z] (VAR y @* [M; N]))
Proof
    qx_genl_tac [‘x’, ‘v’, ‘z’]
 >> ‘hnf (LAM x (VAR x @@ M)) /\
     hnf (LAMl [v; z] (VAR v @* [M; N]))’ by rw [hnf_appstar]
 >> ‘solvable (LAM x (VAR x @@ M)) /\
     solvable (LAMl [v; z] (VAR v @* [M; N]))’
       by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [equivalent_of_solvables, principle_hnf_eq_self]
 (* applying shared tactics *)
 >> equivalent_tac
 (* Let's try only the first subgoal *)
 >- (Q.PAT_X_ASSUM ‘M0 = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘N0 = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘M1 = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘N1 = _’ K_TAC \\
     NTAC 2 (POP_ASSUM K_TAC) \\
  (* eliminate n and n' *)
     qunabbrevl_tac [‘n’, ‘n'’] \\
     Know ‘LAMl_size M0 = 1 /\ LAMl_size N0 = 2’
     >- (rw [Abbr ‘M0’, Abbr ‘N0’, LAMl_size_def, LAMl_size_LAMl]) \\
     DISCH_THEN (rfs o wrap) \\
  (* eliminate vs, vsM, vsN *)
     Know ‘?v0 v1. vs = [v0; v1]’
     >- (qexistsl_tac [‘EL 0 vs’, ‘EL 1 vs’] \\
         rw [Once LIST_EQ_REWRITE] \\
         rename1 ‘i < 2’ \\
        ‘i = 0 \/ i = 1’ by rw [] >> rw []) >> STRIP_TAC \\
     POP_ASSUM (fn th => rfs [th, Abbr ‘vsN’, Abbr ‘vsM’]) \\
     qunabbrevl_tac [‘y’, ‘y'’] \\
  (* stage work *)
     Know ‘M1 = [VAR v0/x] (VAR x @@ M)’
     >- (qunabbrevl_tac [‘M0’, ‘M1’] \\
         Cases_on ‘v0 = x’
         >- (rw [lemma14a] \\
             MATCH_MP_TAC principle_hnf_reduce1 >> rw []) \\
         MATCH_MP_TAC principle_hnf_beta >> rw [FV_thm] \\
         rfs [FV_thm]) \\
     simp [SUB_THM] >> DISCH_TAC \\
  (* stage work

     N1 = principle_hnf (N0 @@ VAR v0 @@ VAR v1)
        = principle_hnf (LAM v (LAM z (VAR v @@ M @@ N)) @@ VAR v0 @@ VAR v1)
        = principle_hnf (
   *)
     Know ‘N1 = LAM v (LAM z (VAR v @@ M @@ N)) @@ VAR v0 @@ VAR v1’
     >- cheat \\
     cheat)
QED
 *)

Theorem equivalent_of_unsolvables :
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

Theorem solving_transform_subst[simp] :
    solving_transform [N/x]
Proof
    rw [solving_transform_def]
 >> DISJ2_TAC >> qexistsl_tac [‘x’, ‘N’] >> rw []
QED

Theorem solving_transform_rightctxt[simp] :
    solving_transform (rightctxt (VAR x))
Proof
    rw [solving_transform_def, FUN_EQ_THM]
 >> DISJ1_TAC
 >> Q.EXISTS_TAC ‘x’ >> rw [rightctxt_thm]
QED

Theorem solving_transform_lameq :
    !f M N. solving_transform f /\ M == N ==> f M == f N
Proof
    rw [solving_transform_def, FUN_EQ_THM]
 >- rw [lameq_rules]
 >> rw [lameq_sub_cong]
QED

(* Definition 10.3.3 (iii)

   NOTE: "Boehm transform is a finite composition of solving transforms
        (including the identity as a composition of zero transforms).

   Here we just define "Boehm transform" as a list of solving transforms,
   thus always finite. The "composition" part depends on how this list is used.
 *)
Definition Boehm_transform_def :
    Boehm_transform pi = EVERY solving_transform pi
End

Theorem Boehm_transform_empty[simp] :
    Boehm_transform []
Proof
    rw [Boehm_transform_def]
QED

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

   NOTE: ‘apply [f3;f2;f1] M = (f3 o f2 o f1) M = f3 (f2 (f1 M))’

   NOTE2: This function seems general: “:('a -> 'a) list -> 'a -> 'a”.
 *)
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
 >> Induct_on ‘pi’ >> rw [FOLDL, FOLDR]
 >> KILL_TAC (* only FOLDL is left *)
 >> Induct_on ‘pi’ using SNOC_INDUCT
 >> rw [FOLDL_SNOC, FOLDL]
 >> POP_ASSUM (rw o wrap o SYM)
QED

Theorem apply_rwts[simp] :
    (apply [] = I) /\
    (!f pi M. apply (f::pi) M = f (apply pi M)) /\
    (!f pi M. apply (SNOC f pi) M = apply pi (f M))
Proof
    NTAC 2 (CONJ_TAC >- rw [apply_def, o_DEF])
 >> rw [apply_alt, o_DEF, FOLDL_SNOC]
QED

(* Lemma 10.3.4 (i) [1, p.246] *)
Theorem Boehm_transform_lameq_ctxt :
    !pi. Boehm_transform pi ==> ?c. ctxt c /\ !M. apply pi M == c M
Proof
    Induct_on ‘pi’
 >> rw [Boehm_transform_def, apply_def]
 >- (Q.EXISTS_TAC ‘\x. x’ >> rw [ctxt_rules, FOLDR])
 >> fs [GSYM Boehm_transform_def, apply_def]
 >> fs [solving_transform_def]
 >- (Q.EXISTS_TAC ‘\y. c y @@ (\y. VAR x) y’ \\
     rw [ctxt_rules, FOLDR] \\
     MATCH_MP_TAC lameq_APPL >> art [])
 (* stage work *)
 >> Q.EXISTS_TAC ‘\y. (\z. LAM x (c z)) y @@ (\y. N) y’
 >> rw [ctxt_rules, constant_contexts_exist, FOLDR]
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘[N/x] (c M)’
 >> reverse CONJ_TAC >- rw [lameq_rules]
 >> irule lameq_sub_cong >> rw []
QED

(* Lemma 10.3.4 (ii) [1, p.246]

   Used by: Boehm_transform_lameq_appstar
 *)
Theorem Boehm_transform_lameq_LAMl_appstar :
    !pi. Boehm_transform pi ==>
         ?c. ctxt c /\ (!M. apply pi M == c M) /\
             !vs. ALL_DISTINCT vs ==>
                  ?Ns. !M. FV M SUBSET (set vs) ==> c M == LAMl vs M @* Ns
Proof
    Induct_on ‘pi’
 >- (rw [] \\
     Q.EXISTS_TAC ‘\x. x’ >> rw [ctxt_rules] \\
     Q.EXISTS_TAC ‘MAP VAR vs’ >> rpt STRIP_TAC \\
     rw [Once lameq_SYM, lameq_LAMl_appstar_VAR])
 >> rw []
 >> Q.PAT_X_ASSUM ‘Boehm_transform pi ==> P’ MP_TAC
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [solving_transform_def] (* 2 subgoals *)
 (* goal 1 (of 2) *)
 >- (Q.EXISTS_TAC ‘\z. c z @@ (\z. VAR x) z’ \\
     rw [ctxt_rules, lameq_rules] \\
     Q.PAT_X_ASSUM ‘!vs. ALL_DISTINCT vs ==> P’ (drule_then STRIP_ASSUME_TAC) \\
     Q.EXISTS_TAC ‘SNOC (VAR x) Ns’ \\
     rw [appstar_SNOC, lameq_rules])
 (* goal 2 (of 2) *)
 >> rename1 ‘h = [P/y]’
 >> qabbrev_tac ‘c1 = \z. LAM y (c z)’
 >> ‘ctxt c1’ by rw [ctxt_rules, Abbr ‘c1’]
 >> Q.EXISTS_TAC ‘\z. c1 z @@ (\z. P) z’
 >> CONJ_TAC >- rw [ctxt_rules, constant_contexts_exist]
 >> CONJ_TAC
 >- (rw [Abbr ‘c1’] \\
     MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘[P/y] (c M)’ \\
     rw [lameq_sub_cong, Once lameq_SYM, lameq_BETA])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!vs. ALL_DISTINCT vs ==> _’ (drule_then STRIP_ASSUME_TAC)
 >> Q.EXISTS_TAC ‘MAP [P/y] Ns’
 >> rw [Abbr ‘c1’]
 >> Q.PAT_X_ASSUM ‘!M. FV M SUBSET set vs ==> _’ (drule_then STRIP_ASSUME_TAC)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘[P/y] (c M)’ >> rw [lameq_BETA]
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘[P/y] (LAMl vs M @* Ns)’ >> rw [lameq_sub_cong]
 >> rw [appstar_SUB]
 >> Suff ‘[P/y] (LAMl vs M) = LAMl vs M’ >- rw []
 >> MATCH_MP_TAC lemma14b
 >> Suff ‘FV (LAMl vs M) = {}’ >- rw []
 >> rw [FV_LAMl]
 >> Q.PAT_X_ASSUM ‘FV M SUBSET (set vs)’ MP_TAC >> SET_TAC []
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
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘[]’))
 >> rw [closed_def]
 >> Q.EXISTS_TAC ‘Ns’
 >> RW_TAC (betafy (srw_ss())) []
QED

(* Used by: distinct_benf_imp_inconsistent *)
Theorem asmlam_apply_cong :
    !pi M N. Boehm_transform pi /\ asmlam eqns M N ==>
             asmlam eqns (apply pi M) (apply pi N)
Proof
    Induct_on ‘pi’ using SNOC_INDUCT >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> fs [solving_transform_def]
 >- rw [asmlam_rules]
 >> MATCH_MP_TAC asmlam_subst >> art []
QED

(* Used by: separability_lemma2 *)
Theorem lameq_apply_cong :
    !pi M N. Boehm_transform pi /\ M == N ==> apply pi M == apply pi N
Proof
    Induct_on ‘pi’ using SNOC_INDUCT >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> MATCH_MP_TAC solving_transform_lameq >> art []
QED

(* Used by separability_thm *)
Theorem Boehm_transform_APPEND :
    !p1 p2. Boehm_transform p1 /\ Boehm_transform p2 ==> Boehm_transform (p1 ++ p2)
Proof
    rw [Boehm_transform_def]
QED

(* Used by separability_thm *)
Theorem Boehm_apply_APPEND :
    !p1 p2 M. apply (p1 ++ p2) M = apply p1 (apply p2 M)
Proof
    Q.X_GEN_TAC ‘p1’
 >> Induct_on ‘p2’ using SNOC_INDUCT
 >> rw [APPEND_SNOC]
QED

(* Used by separability_lemma2 *)
Theorem Boehm_apply_MAP_rightctxt :
    !Ns t. apply (MAP rightctxt Ns) t = t @* (REVERSE Ns)
Proof
    Induct_on ‘Ns’ >> rw [rightctxt_thm]
 >> rw [GSYM SNOC_APPEND]
QED

(* Used by separability_lemma0 *)
Theorem Boehm_apply_MAP_rightctxt' :
    !Ns t. apply (MAP rightctxt (REVERSE Ns)) t = t @* Ns
Proof
    rpt GEN_TAC
 >> qabbrev_tac ‘Ns' = REVERSE Ns’
 >> ‘Ns = REVERSE Ns'’ by rw [Abbr ‘Ns'’, REVERSE_REVERSE]
 >> rw [Boehm_apply_MAP_rightctxt]
QED

(* Used by separability_lemma2 *)
Theorem Boehm_apply_unsolvable :
    !pi M. Boehm_transform pi /\ unsolvable M ==> unsolvable (apply pi M)
Proof
    Induct_on ‘pi’ using SNOC_INDUCT >> rw []
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
                          M1 = principle_hnf (M0 @* MAP VAR vs);
                       in
                          EVERY (\e. hnf_head M1 # e) (hnf_children M1)
End

(* Definition 10.3.5 (iii) *)
Definition is_ready_def :
    is_ready M <=> unsolvable M \/
                   ?N. M == N /\ hnf N /\ ~is_abs N /\ head_original N
End

(* cf. NEW_TAC

   NOTE: “FINITE X” must be present in the assumptions or provable by rw [].
 *)
fun FRESH_list_tac (vs,n,X) =
    qabbrev_tac ‘^vs = FRESH_list ^n X’
 >> KNOW_TAC “ALL_DISTINCT ^vs /\ DISJOINT (set ^vs) ^X /\ LENGTH ^vs = ^n”
 >- rw [FRESH_list_def, Abbr ‘^vs’]
 >> STRIP_TAC;

(* Lemma 10.3.6 (i) *)
Theorem EXISTS_Boehm_transform_is_ready :
    !M. ?pi. Boehm_transform pi /\ is_ready (apply pi M)
Proof
    Q.X_GEN_TAC ‘M’
 >> reverse (Cases_on ‘solvable M’)
 >- (Q.EXISTS_TAC ‘[]’ >> rw [is_ready_def])
 (* now M is solvable *)
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf, solvable_iff_has_hnf]
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘vs = FRESH_list n (FV M0)’
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M0) /\ LENGTH vs = n’
       by (rw [Abbr ‘vs’, FRESH_list_def])
 (* applying the shared hnf_tac *)
 >> hnf_tac (“M0 :term”, “vs :string list”,
             “M1 :term”, “y :string”, “args :term list”)
 >> ‘TAKE (LAMl_size M0) vs = vs’ by rw []
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 >> qabbrev_tac ‘xs :term list = MAP VAR vs’
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE xs)’
 >> ‘apply p1 M0 == M1’
       by (rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt', Abbr ‘xs’])
 >> qabbrev_tac ‘m = LENGTH args’
 (* X collects all free variables in ‘args’ *)
 >> qabbrev_tac ‘X = BIGUNION (IMAGE FV (set args))’
 >> Know ‘FINITE X’
 >- (qunabbrev_tac ‘X’ \\
     MATCH_MP_TAC FINITE_BIGUNION >> rw [] >> rw [])
 >> DISCH_TAC
 (* Z needs to avoid any free variables in args' *)
 >> FRESH_list_tac (“Z :string list”, “(m + 1) :num”, “X :string set”)
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘z = LAST Z’
 >> qabbrev_tac ‘P = LAMl Z (VAR z @* MAP VAR (FRONT Z))’
 >> qabbrev_tac ‘p2 = [[P/y]]’
 >> ‘apply p2 M1 = P @* MAP [P/y] args’ by (rw [Abbr ‘p2’, appstar_SUB])
 >> qabbrev_tac ‘args' = MAP [P/y] args’
 (* TODO: FV args vs. FV args'

  *)
 (* a needs to avoid any free variables in args' *)
 >> NEW_TAC "a" “X :string set”
 >> qabbrev_tac ‘p3 = [rightctxt (VAR a)]’
 >> Know ‘apply p3 (P @* args') == VAR a @* args'’
 >- (rw [Abbr ‘p3’, Abbr ‘P’, rightctxt_thm] \\
    ‘!t. LAMl Z t = LAMl (SNOC z (FRONT Z)) t’
         by (ASM_SIMP_TAC std_ss [Abbr ‘z’, SNOC_LAST_FRONT]) >> POP_ORW \\
     REWRITE_TAC [LAMl_SNOC] \\
     qabbrev_tac ‘t = LAM z (VAR z @* MAP VAR (FRONT Z))’ \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘LAM z (VAR z @* args') @@ VAR a’ \\
  (* applying lameq_LAMl_appstar_ssub *)
     CONJ_TAC
     >- (MATCH_MP_TAC lameq_APPL \\
         Suff ‘LAM z (VAR z @* args') = (FEMPTY |++ ZIP (FRONT Z,args')) ' t’
         >- (Rewr' \\
             MATCH_MP_TAC lameq_LAMl_appstar_ssub \\
             CONJ_TAC >- rw [ALL_DISTINCT_FRONT] \\
             CONJ_TAC >- rw [LENGTH_FRONT, Abbr ‘args'’] \\
             ONCE_REWRITE_TAC [DISJOINT_SYM] \\
             MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘set Z’ \\
             reverse CONJ_TAC >- rw [SUBSET_DEF, MEM_FRONT_NOT_NIL] \\
             ASM_SIMP_TAC std_ss [Once DISJOINT_SYM, Abbr ‘X’] \\
             cheat) \\
         cheat) \\
     cheat)
 (* final stage *)
 >> cheat
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

Theorem separability_lemma0_case2[local] :
    !y args1 args2 k. 0 < k /\ LENGTH args1 = LENGTH args2 + k ==>
       !P Q. ?pi. Boehm_transform pi /\
                  apply pi (VAR y @* args1) == P /\
                  apply pi (VAR y @* args2) == Q
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘M1 = VAR y @* args1’
 >> qabbrev_tac ‘N1 = VAR y @* args2’
 >> qabbrev_tac ‘p  = LENGTH args1’
 >> qabbrev_tac ‘p' = LENGTH args2’
 >> qabbrev_tac ‘vs = FRESH_list (k + 1) (y INSERT FV P UNION FV Q)’
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (y INSERT FV P UNION FV Q)’
      by rw [Abbr ‘vs’, FRESH_list_def]
 >> qabbrev_tac ‘a = HD vs’
 >> qabbrev_tac ‘bs = DROP 1 vs’
 >> Know ‘LENGTH bs + 1 = LENGTH vs /\ 1 < LENGTH vs’
 >- (‘LENGTH vs = k + 1’ by rw [Abbr ‘vs’, FRESH_list_def] \\
     rw [Abbr ‘bs’])
 >> STRIP_TAC
 >> ‘vs <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 (* p1 = ()a b_1 b_2 ... b_k *)
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE (MAP VAR vs))’
 >> ‘Boehm_transform p1’ by rw [Boehm_transform_def, Abbr ‘p1’, EVERY_MAP]
 >> ‘apply p1 M1 = VAR y @* (args1 ++ MAP VAR vs)’
      by (rw [Abbr ‘M1’, Abbr ‘p1’, Boehm_apply_MAP_rightctxt', appstar_APPEND])
 >> ‘apply p1 N1 = VAR y @* (args2 ++ MAP VAR vs)’
      by (rw [Abbr ‘N1’, Abbr ‘p1’, Boehm_apply_MAP_rightctxt', appstar_APPEND])
 (* p2 *)
 >> qabbrev_tac ‘Z = FRESH_list (p + 1) {}’
 >> ‘ALL_DISTINCT Z /\ LENGTH Z = p + 1’ by rw [Abbr ‘Z’, FRESH_list_def]
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘z = LAST Z’
 >> qabbrev_tac ‘p2 = [[LAMl Z (VAR z)/y]]’
 >> ‘Boehm_transform p2’ by rw [Boehm_transform_def, Abbr ‘p2’]
 >> Know ‘apply p2 (VAR y @* (args1 ++ MAP VAR vs)) == VAR a @* MAP VAR bs’
 >- (simp [Abbr ‘p2’, appstar_SUB] \\
     Know ‘MAP [LAMl Z (VAR z)/y] (MAP VAR vs) = MAP VAR vs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ (MP_TAC o (ONCE_REWRITE_RULE [DISJOINT_SYM])) \\
         rw [DISJOINT_ALT, MEM_EL] >> METIS_TAC []) >> Rewr' \\
     qabbrev_tac ‘args1' = MAP [LAMl Z (VAR z)/y] args1’ \\
     Know ‘LAMl Z (VAR z) = LAMl (FRONT Z) (LAM z (VAR z))’
     >- (REWRITE_TAC [GSYM LAMl_SNOC] \\
         Suff ‘SNOC z (FRONT Z) = Z’ >- Rewr \\
         qunabbrev_tac ‘z’ >> MATCH_MP_TAC SNOC_LAST_FRONT >> art []) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘t :term = LAM z (VAR z)’ \\
     MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘t @* MAP VAR vs’ \\
     CONJ_TAC >- (MATCH_MP_TAC lameq_appstar_cong \\
                  MATCH_MP_TAC lameq_LAMl_appstar_reduce \\
                  rw [Abbr ‘t’, Abbr ‘args1'’, LENGTH_FRONT]) \\
     qunabbrev_tac ‘t’ \\
     Know ‘MAP VAR vs = (VAR a::MAP VAR bs) :term list’
     >- (rw [Abbr ‘a’, Abbr ‘bs’, LIST_EQ_REWRITE, MAP_DROP] \\
         Cases_on ‘x’ >- rw [EL_MAP] \\
         rw [EL_MAP, EL_DROP, ADD1]) >> Rewr' \\
     rw [GSYM I_alt] \\
     MATCH_MP_TAC lameq_appstar_cong >> rw [lameq_I])
 >> DISCH_TAC
 >> qabbrev_tac ‘b0 = LAST bs’
 >> Know ‘apply p2 (VAR y @* (args2 ++ MAP VAR vs)) == VAR b0’
 >- (simp [Abbr ‘p2’, appstar_SUB] \\
     Know ‘MAP [LAMl Z (VAR z)/y] (MAP VAR vs) = MAP VAR vs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ (MP_TAC o (ONCE_REWRITE_RULE [DISJOINT_SYM])) \\
         rw [DISJOINT_ALT, MEM_EL] >> METIS_TAC []) >> Rewr' \\
     qabbrev_tac ‘args2' = MAP [LAMl Z (VAR z)/y] args2’ \\
     Know ‘LAMl Z (VAR z) = LAMl (FRONT Z) (LAM z (VAR z))’
     >- (REWRITE_TAC [GSYM LAMl_SNOC] \\
         Suff ‘SNOC z (FRONT Z) = Z’ >- Rewr \\
         qunabbrev_tac ‘z’ >> MATCH_MP_TAC SNOC_LAST_FRONT >> art []) >> Rewr' \\
     Know ‘args2' ++ MAP VAR vs = SNOC (VAR b0) (args2' ++ MAP VAR (FRONT vs))’
     >- (qunabbrev_tac ‘b0’ \\
         Know ‘VAR (LAST bs) :term = LAST (MAP VAR vs)’
         >- (rw [Abbr ‘bs’, listTheory.last_drop, LAST_MAP]) >> Rewr' \\
         Know ‘args2' ++ MAP VAR (FRONT vs) = FRONT (args2' ++ MAP VAR vs)’
         >- (rw [MAP_FRONT] \\
             MATCH_MP_TAC (GSYM FRONT_APPEND_NOT_NIL) >> rw []) >> Rewr' \\
         Suff ‘LAST (MAP VAR vs) = LAST (args2' ++ MAP VAR vs)’
         >- (Rewr' >> qabbrev_tac ‘l = args2' ++ MAP VAR vs’ \\
             MATCH_MP_TAC (GSYM SNOC_LAST_FRONT) >> rw [Abbr ‘l’]) \\
         MATCH_MP_TAC (GSYM LAST_APPEND_NOT_NIL) >> rw []) >> Rewr' \\
     REWRITE_TAC [appstar_SNOC] \\
     qabbrev_tac ‘t :term = LAM z (VAR z)’ \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘t @@ VAR b0’ \\
     CONJ_TAC >- (MATCH_MP_TAC lameq_APPL \\
                  MATCH_MP_TAC lameq_LAMl_appstar_reduce \\
                  rw [Abbr ‘t’, Abbr ‘args2'’, LENGTH_FRONT] \\
                 ‘LENGTH vs = k + 1’ by rw [Abbr ‘vs’, FRESH_list_def] >> rw []) \\
     rw [Abbr ‘t’, GSYM I_alt, lameq_I])
 >> DISCH_TAC
 (* p3 *)
 >> qabbrev_tac ‘f1 = [LAMl bs P/a]’
 >> qabbrev_tac ‘f2 = [Q/b0]’
 >> qabbrev_tac ‘p3 = [f2; f1]’
 >> Know ‘Boehm_transform p3’
 >- (rw [Abbr ‘p3’, Abbr ‘f1’, Abbr ‘f2’, Boehm_transform_def, EVERY_DEF])
 >> DISCH_TAC
 >> Know ‘f1 (VAR a @* MAP VAR bs) == P’
 >- (rw [Abbr ‘f1’, appstar_SUB] \\
     Know ‘MAP [LAMl bs P/a] (MAP VAR bs) = MAP VAR bs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b >> simp [FV_thm] \\
         Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
         Cases_on ‘vs’ >- FULL_SIMP_TAC std_ss [] \\
         fs [Abbr ‘a’, Abbr ‘bs’, LENGTH_DROP] \\
         METIS_TAC [MEM_EL]) >> Rewr' \\
     MATCH_MP_TAC lameq_LAMl_appstar_reduce >> simp [] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ MP_TAC \\
     rw [DISJOINT_ALT, Abbr ‘bs’, MEM_DROP, MEM_EL] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘f2 P = P’
 >- (rw [Abbr ‘f2’] >> MATCH_MP_TAC lemma14b \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ MP_TAC \\
     rw [DISJOINT_ALT, Abbr ‘bs’, Abbr ‘b0’, MEM_DROP, MEM_EL, LAST_EL, EL_DROP] \\
     Suff ‘PRE (LENGTH vs - 1) + 1 < LENGTH vs’ >- METIS_TAC [] \\
     rw [])
 >> DISCH_TAC
 >> Know ‘f1 (VAR b0) = VAR b0’
 >- (rw [Abbr ‘f1’] >> MATCH_MP_TAC lemma14b \\
     Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
     Cases_on ‘vs’ >- FULL_SIMP_TAC std_ss [] \\
     fs [Abbr ‘a’, Abbr ‘bs’, Abbr ‘b0’, LENGTH_DROP] \\
     ‘t <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0] \\
     rw [MEM_EL, LAST_EL] \\
     Suff ‘PRE (LENGTH t) < LENGTH t’ >- METIS_TAC [] \\
     rw [])
 >> DISCH_TAC
 >> ‘f2 (VAR b0) = Q’ by rw [Abbr ‘f2’]
 (* final stage *)
 >> Q.EXISTS_TAC ‘p3 ++ p2 ++ p1’
 >> CONJ_ASM1_TAC
 >- (MATCH_MP_TAC Boehm_transform_APPEND >> art [] \\
     MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      rw [Boehm_apply_APPEND] \\
      MATCH_MP_TAC lameq_TRANS \\
      Q.EXISTS_TAC ‘apply p3 (VAR a @* MAP VAR bs)’ \\
      CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> art []) \\
      rw [Abbr ‘p3’] \\
      MATCH_MP_TAC lameq_TRANS \\
      Q.EXISTS_TAC ‘f2 P’ \\
      reverse CONJ_TAC >- rw [] \\
      MATCH_MP_TAC solving_transform_lameq >> rw [Abbr ‘f2’],
      (* goal 2 (of 2) *)
      REWRITE_TAC [Boehm_apply_APPEND] \\
      Q.PAT_X_ASSUM ‘apply P1 N1 = _’ (ONCE_REWRITE_TAC o wrap) \\
      MATCH_MP_TAC lameq_TRANS \\
      Q.EXISTS_TAC ‘apply p3 (VAR b0)’ \\
      reverse CONJ_TAC >- rw [Abbr ‘p3’] \\
      MATCH_MP_TAC lameq_apply_cong >> art [] ]
QED

Theorem separability_lemma0[local] :
    !M N. solvable (M :term) /\ solvable N /\
          LAMl_size (principle_hnf M) <= LAMl_size (principle_hnf N) ==>
          equivalent M N \/
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    RW_TAC std_ss [equivalent_of_solvables]
 (* applying the shared equivalent_tac *)
 >> equivalent_tac
 (* cleanup MAX and vsN *)
 >> ‘MAX n n' = n'’ by rw [MAX_DEF]
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 >> ‘vsN = vs’ by rw [Abbr ‘vsN’, TAKE_LENGTH_ID_rwt]
 >> qunabbrev_tac ‘vsN’
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 (* Case 1 *)
 >> Cases_on ‘y <> y'’
 >- (simp [] >> rpt GEN_TAC \\
    ‘y1 <> y2’ by (CCONTR_TAC >> fs []) \\
     qabbrev_tac ‘k = n' - n’ \\
    ‘n + k = n'’ by rw [Abbr ‘k’] \\
     qabbrev_tac ‘p0 = MAP rightctxt (REVERSE (MAP VAR vs))’ \\
  (* properties of p0 *)
    ‘Boehm_transform p0’ by rw [Boehm_transform_def, Abbr ‘p0’, EVERY_MAP] \\
     Know ‘apply p0 N0 == N1’
     >- (rw [Abbr ‘p0’, Boehm_apply_MAP_rightctxt']) >> DISCH_TAC \\
     Know ‘apply p0 M0 == M1 @* DROP n (MAP VAR vs)’
     >- (qabbrev_tac ‘l :term list = MAP VAR vs’ \\
         qunabbrev_tac ‘p0’ \\
         Know ‘REVERSE l = REVERSE (TAKE n l ++ DROP n l)’
         >- REWRITE_TAC [TAKE_DROP] >> Rewr' \\
         REWRITE_TAC [REVERSE_APPEND, MAP_APPEND, Boehm_apply_APPEND] \\
         REWRITE_TAC [Boehm_apply_MAP_rightctxt'] \\
         MATCH_MP_TAC lameq_appstar_cong \\
         rw [Abbr ‘l’, Abbr ‘vsM’, GSYM MAP_TAKE]) >> DISCH_TAC \\
  (* now use P and Q

     NOTE: This Z = [z1;z2] contains two fresh variables fixing the textbook proof,
           where [1, p.254] the iterated substition "[LAMl as P/y1] [LAMl as' Q/y2]"
           must be fixed to act as a simultaneous substitition:

       [LAMl as [VAR z2/y2]P/y1] [LAMl as' [VAR z1/y1]Q/y2] [VAR y1/z1] [VAR y2/z2]
   *)
     qabbrev_tac ‘Z = FRESH_list 2 (FV P UNION FV Q)’ \\
    ‘ALL_DISTINCT Z /\ DISJOINT (set Z) (FV P UNION FV Q) /\ LENGTH Z = 2’
       by rw [FRESH_list_def, Abbr ‘Z’] \\
     qabbrev_tac ‘z1 = EL 0 Z’ \\
     qabbrev_tac ‘z2 = EL 1 Z’ \\
    ‘MEM z1 Z /\ MEM z2 Z’
       by (rw [MEM_EL, Abbr ‘z1’, Abbr ‘z2’] >| (* 2 subgoals *)
           [ Q.EXISTS_TAC ‘0’ >> rw [],
             Q.EXISTS_TAC ‘1’ >> rw [] ]) \\
    ‘z1 <> z2’ by (rw [Abbr ‘z1’, Abbr ‘z2’, ALL_DISTINCT_EL_IMP]) \\
     qabbrev_tac ‘as = FRESH_list (m + k) (FV P UNION set Z)’ \\
    ‘LENGTH as = m + k /\ DISJOINT (set as) (FV P UNION set Z)’
       by rw [Abbr ‘as’, FRESH_list_def] \\
     qabbrev_tac ‘as' = FRESH_list m' (FV Q UNION set Z)’ \\
    ‘LENGTH as' = m' /\ DISJOINT (set as') (FV Q UNION set Z)’
       by rw [Abbr ‘as'’, FRESH_list_def] \\
     qabbrev_tac ‘f1 = [LAMl as  ([VAR z2/y2] P)/y1]’ \\
     qabbrev_tac ‘f2 = [LAMl as' ([VAR z1/y1] Q)/y2]’ \\
     qabbrev_tac ‘f3 :term -> term = [VAR y1/z1]’ \\
     qabbrev_tac ‘f4 :term -> term = [VAR y2/z2]’ \\
     qabbrev_tac ‘p1 = [f4; f3; f2; f1]’ \\
  (* properties of p1 *)
    ‘Boehm_transform p1’ by rw [Boehm_transform_def, Abbr ‘p1’,
                                Abbr ‘f1’, Abbr ‘f2’, Abbr ‘f3’, Abbr ‘f4’] \\
     Know ‘DISJOINT (set as) (FV ([VAR z2/y2] P))’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV P UNION set Z’ >> art [] \\
         simp [FV_SUB] \\
         Cases_on ‘y2 IN FV P’ >> rw [SUBSET_DEF, Abbr ‘z2’] >> art []) \\
     DISCH_TAC \\
     Know ‘DISJOINT (set as') (FV ([VAR z1/y1] Q))’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV Q UNION set Z’ >> art [] \\
         simp [FV_SUB] \\
         Cases_on ‘y1 IN FV Q’ >> rw [SUBSET_DEF, Abbr ‘z2’] >> art []) \\
     DISCH_TAC \\
  (* stage work *)
     Q.EXISTS_TAC ‘p1 ++ p0’ \\
     CONJ_ASM1_TAC >- rw [Boehm_transform_APPEND] \\
     reverse CONJ_TAC >| (* 2 subgoals, Q part seems easier *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (p1 ++ p0) N0’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘N0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf >> art [GSYM solvable_iff_has_hnf]) \\
    (* eliminating p0 *)
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply p1 N1’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> art []) \\
       SIMP_TAC (srw_ss()) [Abbr ‘p1’] (* f4 (f3 (f2 (f1 N1))) == Q *) \\
    (* eliminating f1 *)
      ‘f1 N1 = VAR y2 @* (MAP f1 args2)’
          by (rw [appstar_SUB, Abbr ‘f1’]) >> POP_ORW \\
    (* eliminating f2 *)
       qunabbrev_tac ‘f2’ \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘f4 (f3 ([VAR z1/y1] Q))’ \\
       CONJ_TAC >- (MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f4’] \\
                    MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f3’] \\
                    MATCH_MP_TAC lameq_hnf_fresh_subst >> art [] \\
                    rw [Abbr ‘m'’, hnf_children_hnf]) \\
    (* eliminating f3 *)
       qunabbrev_tac ‘f3’ \\
       Know ‘[VAR y1/z1] ([VAR z1/y1] Q) = Q’
       >- (MATCH_MP_TAC lemma15b \\
           Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
           rw [DISJOINT_ALT] >> METIS_TAC []) >> Rewr' \\
    (* eliminating f4 *)
       qunabbrev_tac ‘f4’ \\
       Suff ‘[VAR y2/z2] Q = Q’ >- rw [] \\
       MATCH_MP_TAC lemma14b \\
       Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
       rw [DISJOINT_ALT] >> METIS_TAC [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (p1 ++ p0) M0’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘M0’ \\
                    MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf >> art [GSYM solvable_iff_has_hnf]) \\
    (* eliminating p0 *)
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply p1 (M1 @* DROP n (MAP VAR vs))’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> art []) \\
       SIMP_TAC (srw_ss()) [Abbr ‘p1’] (* f4 (f3 (f2 (f1 M1))) == P *) \\
    (* eliminating f1 *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘f4 (f3 (f2 ([VAR z2/y2] P)))’ \\
       CONJ_TAC >- (MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f4’] \\
                    MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f3’] \\
                    MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f2’] \\
                    rw [appstar_SUB, GSYM appstar_APPEND, Abbr ‘f1’] \\
                    MATCH_MP_TAC lameq_LAMl_appstar_reduce >> art [] \\
                    rw [Abbr ‘m’, hnf_children_hnf]) \\
    (* eliminating f2 *)
       Know ‘f2 ([VAR z2/y2] P) = [VAR z2/y2] P’
       >- (qunabbrev_tac ‘f2’ \\
           MATCH_MP_TAC lemma14b >> rw [FV_SUB] \\
           CCONTR_TAC >> ‘MEM y2 Z’ by METIS_TAC [] \\
           Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’
               (MP_TAC o ONCE_REWRITE_RULE [DISJOINT_SYM]) \\
           rw [DISJOINT_ALT] >> METIS_TAC []) >> Rewr' \\
    (* eliminating f3 *)
       Know ‘f3 ([VAR z2/y2] P) = [VAR z2/y2] P’
       >- (qunabbrev_tac ‘f3’ \\
           MATCH_MP_TAC lemma14b \\
           Suff ‘z1 # P’ >- rw [FV_SUB] \\
           Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
           rw [DISJOINT_ALT] >> METIS_TAC []) >> Rewr' \\
    (* eliminating f4 *)
       qunabbrev_tac ‘f4’ \\
       Suff ‘[VAR y2/z2] ([VAR z2/y2] P) = P’ >- rw [] \\
       MATCH_MP_TAC lemma15b \\
       Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
       rw [DISJOINT_ALT] >> METIS_TAC [] ])
 (* Case 2 *)
 >> REWRITE_TAC [DECIDE “P \/ Q <=> ~P ==> Q”]
 >> rfs [] >> DISCH_TAC (* m' + n <> m + n' *)
 >> rpt GEN_TAC
 (* p0 is the same as in case 1 *)
 >> qabbrev_tac ‘p0 = MAP rightctxt (REVERSE (MAP VAR vs))’
 (* properties of p0 *)
 >> ‘Boehm_transform p0’ by rw [Boehm_transform_def, Abbr ‘p0’, EVERY_MAP]
 >> Know ‘apply p0 N0 == N1’
 >- rw [Abbr ‘p0’, Boehm_apply_MAP_rightctxt']
 >> ‘LENGTH args2 = m'’ by rw [Abbr ‘m'’, hnf_children_hnf]
 >> Q.PAT_X_ASSUM ‘N1 = _’ (ONCE_REWRITE_TAC o wrap)
 >> DISCH_TAC
 >> Know ‘apply p0 M0 == M1 @* DROP n (MAP VAR vs)’
 >- (qabbrev_tac ‘l :term list = MAP VAR vs’ \\
     qunabbrev_tac ‘p0’ \\
     Know ‘REVERSE l = REVERSE (TAKE n l ++ DROP n l)’
     >- REWRITE_TAC [TAKE_DROP] >> Rewr' \\
     REWRITE_TAC [REVERSE_APPEND, MAP_APPEND, Boehm_apply_APPEND] \\
     REWRITE_TAC [Boehm_apply_MAP_rightctxt'] \\
     MATCH_MP_TAC lameq_appstar_cong \\
     rw [Abbr ‘l’, Abbr ‘vsM’, GSYM MAP_TAKE])
 >> ‘LENGTH args1 = m’ by rw [Abbr ‘m’, hnf_children_hnf]
 >> Q.PAT_X_ASSUM ‘M1 = _’ (ONCE_REWRITE_TAC o wrap)
 >> ‘VAR y1 = VAR y2 :term’ by PROVE_TAC [] >> POP_ORW
 >> REWRITE_TAC [GSYM appstar_APPEND]
 >> qabbrev_tac ‘args1' = args1 ++ DROP n (MAP VAR vs)’
 >> DISCH_TAC
 >> qabbrev_tac ‘l = LENGTH args1'’
 >> ‘l <> m'’ by rw [Abbr ‘l’, Abbr ‘args1'’]
 (* stage work *)
 >> ‘m' < l \/ l < m'’ by rw [] (* 2 subgoals, same ending tactics *)
 >| [ (* goal 1 (of 2) *)
      MP_TAC (Q.SPECL [‘y2’, ‘args1'’, ‘args2’, ‘l - m'’] separability_lemma0_case2) \\
      simp [] \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPECL [‘P’, ‘Q’])),
      (* goal 2 (of 2) *)
      MP_TAC (Q.SPECL [‘y2’, ‘args2’, ‘args1'’, ‘m' - l’] separability_lemma0_case2) \\
      simp [] \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPECL [‘Q’, ‘P’])) ]
 (* shared tactics *)
 >> (Q.EXISTS_TAC ‘pi ++ p0’ \\
     CONJ_ASM1_TAC >- rw [Boehm_transform_APPEND] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1.1 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (pi ++ p0) M0’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘M0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (y' @* args1')’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC lameq_apply_cong \\
       Q.PAT_X_ASSUM ‘VAR y2 = y'’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [],
       (* goal 1.2 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (pi ++ p0) N0’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘N0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (y @* args2)’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC lameq_apply_cong \\
       Q.PAT_X_ASSUM ‘y = y'’ (ONCE_REWRITE_TAC o wrap) \\
       Q.PAT_X_ASSUM ‘VAR y2 = y'’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [] ])
QED

(* Lemma 10.4.1 (i) [1, p.254] *)
Theorem separability_lemma1 :
    !M N. solvable (M :term) /\ solvable N /\ ~equivalent M N ==>
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘N0 = principle_hnf N’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘n' = LAMl_size N0’
 (* applying separability_lemma0 *)
 >> ‘n <= n' \/ n' <= n’ by rw []
 >- METIS_TAC [separability_lemma0]
 >> MP_TAC (Q.SPECL [‘N’, ‘M’] separability_lemma0)
 >> RW_TAC std_ss [Once equivalent_comm]
 >> POP_ASSUM (MP_TAC o Q.SPECL [‘Q’, ‘P’])
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘pi’ >> art []
QED

(* Lemma 10.4.1 (ii) [1, p.254] *)
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
 >> qabbrev_tac ‘as = FRESH_list (LENGTH args) (FV P)’
 >> qabbrev_tac ‘pi = [LAMl as P/y]::MAP rightctxt (MAP VAR (REVERSE vs))’
 >> Q.EXISTS_TAC ‘pi’
 >> STRONG_CONJ_TAC
 >- rw [Abbr ‘pi’, Boehm_transform_def, EVERY_SNOC, EVERY_MAP]
 >> DISCH_TAC
 (* applying Boehm_apply_unsolvable *)
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC Boehm_apply_unsolvable >> art [])
 (* stage work *)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply pi M0’
 >> CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> art [])
 >> POP_ASSUM K_TAC (* ‘Boehm_transform pi’ is not needed here *)
 >> rw [Abbr ‘pi’]
 >> qabbrev_tac ‘pi :transform = MAP rightctxt (MAP VAR (REVERSE (vs)))’
 >> qabbrev_tac ‘t = VAR y @* args’
 (* applying Boehm_apply_MAP_rightctxt *)
 >> Know ‘apply pi (LAMl vs t) = LAMl vs t @* MAP VAR vs’
 >- (rw [Abbr ‘pi’, Boehm_apply_MAP_rightctxt] \\
     rw [MAP_REVERSE, REVERSE_REVERSE])
 >> Rewr'
 (* applying lameq_LAMl_appstar_VAR *)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘[LAMl as P/y] t’
 >> CONJ_TAC
 >- (irule lameq_sub_cong >> rw [lameq_LAMl_appstar_VAR])
 >> rw [Abbr ‘t’, appstar_SUB]
 >> ‘DISJOINT (set as) (FV P) /\ LENGTH as = LENGTH args’
       by rw [FRESH_list_def, Abbr ‘as’]
 >> MATCH_MP_TAC lameq_LAMl_appstar_reduce >> rw []
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
 >> Q.EXISTS_TAC ‘pi' ++ pi’
 >> fs [Abbr ‘M0’, Abbr ‘N0’, Boehm_transform_APPEND, GSYM Boehm_apply_APPEND]
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
 >> MATCH_MP_TAC asmlam_apply_cong >> art []
 >> Suff ‘(M,N) IN eqns’ >- rw [asmlam_rules]
 >> rw [Abbr ‘eqns’]
QED

(* Theorem 2.1.39 [1, p.35]

   Used by: has_bnf_imp_lameta_complete
 *)
Theorem distinct_benf_imp_incompatible =
        REWRITE_RULE [GSYM incompatible_def] distinct_benf_imp_inconsistent

(* Theorem 2.1.40 [1, p.35] aka Corollary 10.4.3 (ii) [1, p.256]

   Also know as "Hilbert-Post completeness of lambda(beta)+eta".
 *)
Theorem has_bnf_imp_lameta_complete :
    !M N. has_bnf M /\ has_bnf N ==>
          lameta M N \/ ~consistent (conversion (RINSERT (beta RUNION eta) M N))
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
 >> qabbrev_tac ‘R = RINSERT (beta RUNION eta) M N’
 >> simp [RSUBSET]
 >> HO_MATCH_MP_TAC asmlam_ind >> rw [] (* 7 subgoals, only the first is hard *)
 (* goal 1 (of 7 *)
 >- (MATCH_MP_TAC conversion_TRANS >> Q.EXISTS_TAC ‘M’ \\
     CONJ_TAC
     >- (irule (REWRITE_RULE [RSUBSET] conversion_monotone) \\
         Q.EXISTS_TAC ‘beta RUNION eta’ \\
         CONJ_TAC >- rw [Abbr ‘R’, RINSERT] \\
         rw [beta_eta_lameta, Once lameta_SYM]) \\
     MATCH_MP_TAC conversion_TRANS >> Q.EXISTS_TAC ‘N’ \\
     reverse CONJ_TAC
     >- (irule (REWRITE_RULE [RSUBSET] conversion_monotone) \\
         Q.EXISTS_TAC ‘beta RUNION eta’ \\
         CONJ_TAC >- rw [Abbr ‘R’, RINSERT] \\
         rw [beta_eta_lameta]) \\
     Suff ‘R M N’ >- rw [conversion_rules] \\
     rw [Abbr ‘R’, RINSERT])
 >| [ (* goal 2 (of 7) *)
      Suff ‘R (LAM x M'' @@ N'') ([N''/x] M'')’ >- rw [conversion_rules] \\
      rw [Abbr ‘R’] >> MATCH_MP_TAC (REWRITE_RULE [RSUBSET] RSUBSET_RINSERT) \\
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
