(* ========================================================================== *)
(* FILE    : boehmScript.sml                                                  *)
(* TITLE   : (Effective) Boehm Trees (Chapter 10 of Barendregt 1984 [1])      *)
(*                                                                            *)
(* AUTHORS : 2023-2024 The Australian National University (Chun Tian)         *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory rich_listTheory
     llistTheory relationTheory ltreeTheory pathTheory posetTheory hurdUtils
     pairTheory finite_mapTheory topologyTheory listRangeTheory combinTheory
     tautLib listLib string_numTheory;

(* local theories *)
open binderLib basic_swapTheory nomsetTheory termTheory appFOLDLTheory
     chap2Theory chap3Theory head_reductionTheory standardisationTheory
     reductionEval solvableTheory horeductionTheory takahashiS3Theory;

(* enable basic monad support *)
open monadsyntax;
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

(* create the theory *)
val _ = new_theory "boehm";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

(* These theorems usually give unexpected results, should be applied manually *)
val _ = temp_delsimps ["IN_UNION", "APPEND_ASSOC"];

val _ = hide "B";
val _ = hide "C";
val _ = hide "W";
val _ = hide "Y";

val _ = set_trace "Goalstack.print_goal_at_top" 0;

(* Disable some conflicting overloads from labelledTermsTheory, by
   repeating the desired overloads again (this prioritizes them).
 *)
Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

(*---------------------------------------------------------------------------*
 *  Local utilities
 *---------------------------------------------------------------------------*)

(* NOTE: “FINITE X” must be present in the assumptions or provable by rw [].
   If ‘X’ is actually a literal union of sets, they will be broken into several
  ‘DISJOINT’ assumptions.

   NOTE: Usually the type of "X" is tricky, thus Q_TAC is recommended, e.g.:

   Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘FV M UNION FV N’
 *)
fun RNEWS_TAC (vs, r, n) X :tactic =
    qabbrev_tac ‘^vs = RNEWS ^r ^n ^X’
 >> Know ‘ALL_DISTINCT ^vs /\ DISJOINT (set ^vs) ^X /\ LENGTH ^vs = ^n’
 >- rw [RNEWS_def, Abbr ‘^vs’]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']));

fun NEWS_TAC (vs, n) = RNEWS_TAC (vs, numSyntax.zero_tm, n);

(* Given a hnf ‘M0’ and a shared (by multiple terms) binding variable list ‘vs’,
   HNF_TAC adds the following abbreviation and new assumptions:

   Abbrev (M1 = principle_hnf (M0 @* MAP VAR (TAKE (LAMl_size M0) vs)))
   M0 = LAMl (TAKE (LAMl_size M0) vs) (VAR y @* args)
   M1 = VAR y @* args

   where the names "M1", "y" and "args" can be chosen from inputs.

   NOTE: HNF_TAC expects that there's already an abbreviation for M1, which is
   re-defined as above with ‘TAKE’ involved. In case of single term who fully
   owns ‘vs’, the following tactics can be followed to eliminate ‘TAKE’:

  ‘TAKE n vs = vs’ by rw [] >> POP_ASSUM (rfs o wrap)

   NOTE: Since the symbol behind M1 is always presented in assumptions, it's
   recommended to use Q_TAC together, in the following form:

   Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                   “y :string”, “args :term list”)) ‘M1’

   This doesn't save much in number of letters, just putting ‘M1’ special in a
   sense that its abbreviation will be updated (deleted and re-defined).
 *)
fun HNF_TAC (M0, vs, y, args) M1 = let
    val n = “LAMl_size ^M0” in
    qunabbrev_tac ‘^M1’
 >> qabbrev_tac ‘^M1 = principle_hnf (^M0 @* MAP VAR (TAKE ^n ^vs))’
 >> Know ‘?^y ^args. ^M0 = LAMl (TAKE ^n ^vs) (VAR ^y @* ^args)’
 >- (‘hnf ^M0’ by PROVE_TAC [hnf_principle_hnf, hnf_principle_hnf'] \\
     irule (iffLR hnf_cases_shared) >> rw [])
 >> STRIP_TAC
 >> Know ‘^M1 = VAR ^y @* ^args’
 >- (qunabbrev_tac ‘^M1’ \\
     Q.PAT_ASSUM ‘^M0 = LAMl (TAKE ^n ^vs) (VAR ^y @* ^args)’
        (fn th => REWRITE_TAC [Once th]) \\
     MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> DISCH_TAC
end;

(* Remove all ‘T’s in current assumptions *)
val T_TAC = rpt (Q.PAT_X_ASSUM ‘T’ K_TAC);

(* Invented by Michael Norrish, which is roughly equivalent to RW_TAC std_ss ths
   (which eliminates LET and creates abbreviations) but does not do STRIP_TAC
   on the goal.
 *)
fun UNBETA_TAC ths tm =
  let val P = genvar (type_of tm --> bool)
  in
    CONV_TAC (UNBETA_CONV tm)
 >> qmatch_abbrev_tac ‘^P _’
 >> RW_TAC bool_ss ths
 >> simp [Abbr ‘^P’]
  end;

(*---------------------------------------------------------------------------*
 *  ltreeTheory extras
 *---------------------------------------------------------------------------*)

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
           ltree_node (THE (ltree_lookup A p)) =
           ltree_node (THE (ltree_lookup B p))
End

(*---------------------------------------------------------------------------*
 *  Boehm Trees (and subterms)
 *---------------------------------------------------------------------------*)

(* The type of Boehm trees:

   For each ltree node, ‘NONE’ represents {\bot} (for unsolvable terms), while
  ‘SOME (vs,y)’ represents ‘LAMl vs (VAR y)’. This separation of vs and y has
   at least two advantages:

   1. ‘set vs’ is the set of binding variables at that ltree node.
   2. ‘LAMl vs (VAR y)’ can easily "expand" (w.r.t. eta reduction) into terms
      such as ‘LAMl (vs ++ [z0;z1]) t’ (with two extra children ‘z0’ and ‘z1’)
      without changing the head variable (VAR y).
 *)
Type BT_node[pp]    = “:(string list # string) option”
Type boehm_tree[pp] = “:BT_node ltree”

(* Definition 10.1.9 [1, p.221] (Effective Boehm Tree)

   NOTE: For the correctness of the definition, ‘FINITE X’ and ‘FV M SUBSET X’,
   or something stronger ‘FV M SUBSET X UNION (RANK r X)’ for induction,
   must be assumed in antecedents.
 *)
Definition BT_generator_def :
    BT_generator X (M,r) =
      if solvable M then
         let M0 = principle_hnf M;
              n = LAMl_size M0;
             vs = RNEWS r n X;
             M1 = principle_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1;
              y = hnf_headvar M1;
              l = MAP (\e. (e,SUC r)) Ms;
         in
            (SOME (vs,y),fromList l)
      else
            (NONE, LNIL)
End

Definition BT_def[nocompute] :
    BT X = ltree_unfold (BT_generator X)
End

(* NOTE: ‘BT X (M,r)’ will show as ‘BT' X M r’ *)
Overload BT' = “\X M r. BT X (M,r)”

(* Definition 10.1.13 (iii)

   NOTE: The output ‘SOME (M,r)’ allows to write ‘BT X (THE (subterm X M p r))’.
   Defining ‘m = hnf_children_size M0’ instead of ‘LENGTH Ms’ has extra
   benefits in proving subterm_tpm lemmas.
 *)
Definition subterm_def :
    subterm X M     [] r = SOME (M,r) /\
    subterm X M (h::p) r =
      if solvable M then
         let M0 = principle_hnf M;
              n = LAMl_size M0;
             vs = RNEWS r n X;
             M1 = principle_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1;
              m = LENGTH Ms
         in
             if h < m then subterm X (EL h Ms) p (SUC r)
             else NONE
      else
         NONE
End

(* NOTE: The use of ‘subterm' X M p r’ assumes that ‘subterm X M p r <> NONE’ *)
Overload subterm' = “\X M p r. FST (THE (subterm X M p r))”

(* |- subterm X M [] r = SOME (M,r) *)
Theorem subterm_NIL[simp] = SPEC_ALL (cj 1 subterm_def)

Theorem subterm_NIL'[simp] :
    subterm' X M [] r = M
Proof
    rw [subterm_NIL]
QED

Theorem subterm_disjoint_lemma :
    !X M r n vs.
           FINITE X /\ FV M SUBSET X UNION RANK r /\ vs = RNEWS r n X
       ==> DISJOINT (set vs) (FV M)
Proof
    rw [DISJOINT_ALT']
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> Know ‘x IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF]
 >> rw [IN_UNION]
 >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
     rw [DISJOINT_ALT'])
 >> Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT]
 >> qunabbrev_tac ‘vs’
 >> MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []
QED

Theorem subterm_disjoint_lemma' :
    !X M r M0 n vs.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\ M0 = principle_hnf M /\ vs = RNEWS r n X
       ==> DISJOINT (set vs) (FV M0)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC DISJOINT_SUBSET
 >> Q.EXISTS_TAC ‘FV M’
 >> reverse CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap) \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> MATCH_MP_TAC subterm_disjoint_lemma
 >> qexistsl_tac [‘X’, ‘r’, ‘n’] >> art []
QED

(* NOTE: In general ‘solvable M’ doesn't imply ‘solvable (M @* args)’. The
   present lemma is a special case.
 *)
Theorem solvable_appstar :
    !X M r M0 n n' vs.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n' X /\ n <= n'
       ==> solvable (M0 @* MAP VAR vs)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n' :num”)) ‘X’
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (rw [Abbr ‘n’] >> irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘LENGTH vs’] >> rw [])
 >> STRIP_TAC
 >> qabbrev_tac ‘xs = TAKE n vs’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Know ‘M1 = VAR y @* args @* DROP n (MAP VAR vs)’
 >- (simp [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     simp [GSYM MAP_DROP] \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP n vs)’ \\
     MATCH_MP_TAC principle_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
 >> ‘hnf M1’ by rw [GSYM appstar_APPEND, hnf_appstar]
 >> Know ‘M0 @* MAP VAR vs ==
          LAMl xs (VAR y @* args) @* MAP VAR xs @* MAP VAR (DROP n vs)’
 >- (Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     simp [appstar_APPEND])
 >> DISCH_TAC
 >> qabbrev_tac ‘l = MAP VAR (DROP n vs)’
 >> qabbrev_tac ‘t = VAR y @* args’
 >> Know ‘LAMl xs t @* MAP VAR xs @* l == t @* l’
 >- (MATCH_MP_TAC lameq_appstar_cong >> rw [])
 >> DISCH_TAC
 >> ‘M0 @* MAP VAR vs == t @* l’ by PROVE_TAC [lameq_TRANS]
 >> Suff ‘solvable (t @* l)’ >- PROVE_TAC [lameq_solvable_cong]
 >> REWRITE_TAC [solvable_iff_has_hnf]
 >> MATCH_MP_TAC hnf_has_hnf
 >> simp [Abbr ‘t’, GSYM appstar_APPEND, hnf_appstar]
QED

Theorem solvable_appstar' :
    !X M r M0 n vs.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X
       ==> solvable (M0 @* MAP VAR vs)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC solvable_appstar
 >> qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘n’] >> simp []
QED

(* NOTE: Essentially, ‘hnf_children_size (principle_hnf M)’ is irrelevant with
         the excluding list. This lemma shows the equivalence in defining ‘m’.
 *)
Theorem hnf_children_size_alt :
    !X M r M0 n vs M1 Ms.
         FINITE X /\ FV M SUBSET X UNION RANK r /\ solvable M /\
         M0 = principle_hnf M /\
          n = LAMl_size M0 /\
         vs = RNEWS r n X /\
         M1 = principle_hnf (M0 @* MAP VAR vs) /\
         Ms = hnf_children M1
     ==> hnf_children_size M0 = LENGTH Ms
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
QED

Theorem subterm_of_solvables :
    !X M h p r. solvable M ==>
       subterm X M (h::p) r =
         let M0 = principle_hnf M;
              n = LAMl_size M0;
             vs = RNEWS r n X;
             M1 = principle_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1;
              m = LENGTH Ms
         in
            if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rw [subterm_def]
QED

(* NOTE: With [hnf_children_size_alt] now we are ready to prove this alternative
         definition of ‘subterm’.
 *)
Theorem subterm_alt :
    !X M h p r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
       subterm X M (h::p) r =
       if solvable M then
         let M0 = principle_hnf M;
              n = LAMl_size M0;
              m = hnf_children_size M0;
             vs = RNEWS r n X;
             M1 = principle_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1
         in
             if h < m then subterm X (EL h Ms) p (SUC r)
             else NONE
       else
         NONE
Proof
    RW_TAC std_ss [subterm_def]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Suff ‘m = m'’ >- rw []
 >> qunabbrevl_tac [‘m’, ‘m'’]
 >> MATCH_MP_TAC hnf_children_size_alt
 >> qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

(* This is the meaning of Boehm tree nodes, ‘fromNote’ translated from BT nodes
   to lambda terms in form of ‘SOME (LAMl vs (VAR y))’ or ‘NONE’.
 *)
Definition fromNode_def :
    fromNode = OPTION_MAP (\(vs,y). LAMl vs (VAR y))
End

(* Boehm tree of a single (free) variable ‘VAR y’ *)
Definition BT_VAR_def :
    BT_VAR y :boehm_tree = Branch (SOME ([],y)) LNIL
End

(* Remarks 10.1.3 (iii) [1, p.216]: unsolvable terms all have the same Boehm
   tree (‘bot’). The following overloaded ‘bot’ may be returned by
  ‘THE (ltree_lookup A p)’ when looking up a terminal node of the Boehm tree.

   See also BT_ltree_lookup_of_unsolvables and BT_ltree_el_of_unsolvables, for
   the raison d'etre of overloading "bot" on two different terms.
 *)
Overload bot = “Branch NONE (LNIL :boehm_tree llist)”

(* Another form of ‘bot’, usually returned by “THE (ltree_el A p)” *)
Overload bot = “(NONE, SOME 0) :(BT_node # num option)”

(* Unicode name: "base" *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x22A5, tmnm = "bot"};
val _ = TeX_notation {hol = "bot", TeX = ("\\ensuremath{\\bot}", 1)};

Theorem BT_of_unsolvables :
    !X M r. unsolvable M ==> BT' X M r = bot
Proof
    rw [BT_def, BT_generator_def, ltree_unfold, ltree_map]
QED

Theorem BT_of_unsolvables_cong :
    !X M N r. unsolvable M /\ unsolvable N ==> BT' X M r = BT' X N r
Proof
    rw [BT_of_unsolvables]
QED

Theorem BT_of_principle_hnf :
    !X M r. solvable M ==> BT' X (principle_hnf M) r = BT' X M r
Proof
    reverse (RW_TAC std_ss [BT_def, BT_generator_def, ltree_unfold])
 >- (Q.PAT_X_ASSUM ‘unsolvable M0’ MP_TAC >> simp [] \\
     rw [Abbr ‘M0’, solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf \\
     MATCH_MP_TAC hnf_principle_hnf' >> art [])
 >> ‘M0' = M0’ by rw [Abbr ‘M0'’, Abbr ‘M0’, principle_hnf_stable']
 >> qunabbrev_tac ‘M0'’
 >> POP_ASSUM (rfs o wrap)
 >> ‘principle_hnf M0 = M0’ by rw [Abbr ‘M0’, principle_hnf_stable']
 >> POP_ASSUM (rfs o wrap)
QED

Theorem BT_finite_branching :
    !X M r. finite_branching (BT' X M r)
Proof
    rpt GEN_TAC
 >> irule finite_branching_coind'
 >> Q.EXISTS_TAC ‘\b. ?X M r. b = BT' X M r’
 >> rw [] >- (qexistsl_tac [‘X’, ‘M’, ‘r’] >> rw [])
 (* stage work *)
 >> qabbrev_tac ‘A = BT' X M r’
 >> qabbrev_tac ‘a = ltree_node A’
 >> qabbrev_tac ‘ts = ltree_children A’
 >> qexistsl_tac [‘a’, ‘ts’]
 (* A = Branch a ts *)
 >> CONJ_TAC >- rw [Abbr ‘a’, Abbr ‘ts’]
 (* LFINITE ts *)
 >> CONJ_TAC
 >- rw [Abbr ‘A’, Abbr ‘ts’, BT_def, BT_generator_def, Once ltree_unfold,
        LFINITE_fromList]
 >> qabbrev_tac ‘P = \b. ?X M r. b = BT' X M r’
 (* stage work *)
 >> reverse (RW_TAC std_ss [Abbr ‘A’, Abbr ‘ts’, BT_def, BT_generator_def,
                            Once ltree_unfold])
 >- rw []
 >> rw [every_fromList_EVERY, LMAP_fromList, EVERY_MAP, Abbr ‘P’, EVERY_MEM,
        Abbr ‘l’]
 >> rename1 ‘MEM N Ms’
 >> qexistsl_tac [‘X’, ‘N’, ‘SUC r’] >> rw [BT_def]
QED

Theorem subterm_rank_lemma :
    !p X M N r r'. FINITE X /\ FV M SUBSET X UNION RANK r /\
                   subterm X M p r = SOME (N,r')
               ==> r' = r + LENGTH p /\ FV N SUBSET X UNION RANK r'
Proof
    Induct_on ‘p’ >- NTAC 2 (rw [])
 >> rpt GEN_TAC
 >> reverse (Cases_on ‘solvable M’) >- rw [subterm_def]
 >> UNBETA_TAC [subterm_of_solvables] “subterm X M (h::p) r”
 >> STRIP_TAC
 >> qabbrev_tac ‘M' = EL h Ms’
 >> Q.PAT_X_ASSUM ‘!X M N r r'. P’
      (MP_TAC o (Q.SPECL [‘X’, ‘M'’, ‘N’, ‘SUC r’, ‘r'’]))
 >> simp []
 >> Suff ‘FV M' SUBSET X UNION RANK (SUC r)’
 >- rw []
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (rfs o wrap o SYM)
 >> Know ‘!i. i < LENGTH Ms ==> FV (EL i Ms) SUBSET FV M1’
 >- (MATCH_MP_TAC hnf_children_FV_SUBSET \\
     simp [hnf_appstar])
 >> DISCH_TAC
 >> qunabbrev_tac ‘M'’
 >> qabbrev_tac ‘Y  = RANK r’
 >> qabbrev_tac ‘Y' = RANK (SUC r)’
 (* #1 *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M1’
 >> CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 (* #2 *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M0 UNION set vs’
 >> CONJ_TAC >- simp [FV_LAMl]
 (* #3 *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M UNION set vs’
 >> CONJ_TAC
 >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> rw [SUBSET_DEF, IN_UNION]
 >- (Know ‘x IN X UNION Y’ >- METIS_TAC [SUBSET_DEF] \\
     rw [IN_UNION] >- (DISJ1_TAC >> art []) \\
     DISJ2_TAC \\
     Suff ‘Y SUBSET Y'’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrevl_tac [‘Y’, ‘Y'’] \\
     MATCH_MP_TAC RANK_MONO >> rw [])
 >> DISJ2_TAC
 >> Suff ‘set vs SUBSET Y'’ >- METIS_TAC [SUBSET_DEF]
 >> qunabbrevl_tac [‘vs’, ‘Y'’]
 >> MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []
QED

Theorem subterm_rank_lemma' :
    !p X M N r r'. FINITE X /\ FV M SUBSET X /\
                   subterm X M p r = SOME (N,r')
               ==> r' = r + LENGTH p /\
                   FV N SUBSET X UNION RANK r'
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> MATCH_MP_TAC subterm_rank_lemma
 >> Q.EXISTS_TAC ‘M’ >> art []
 >> Q.PAT_X_ASSUM ‘FV M SUBSET X’ MP_TAC
 >> SET_TAC []
QED

Theorem subterm_induction_lemma :
    !X M r M0 n n' m vs M1 Ms h.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
            m = hnf_children_size M0 /\
           vs = RNEWS r n' X /\ n <= n' /\
           M1 = principle_hnf (M0 @* MAP VAR vs) /\
           Ms = hnf_children M1 /\ h < m
       ==> FV (EL h Ms) SUBSET X UNION RANK (SUC r)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n' :num”)) ‘X’
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (rw [Abbr ‘n’] >> irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘LENGTH vs’] >> rw [])
 >> STRIP_TAC
 >> qabbrev_tac ‘xs = TAKE n vs’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Know ‘M1 = VAR y @* args @* DROP n (MAP VAR vs)’
 >- (simp [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     simp [GSYM MAP_DROP] \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP n vs)’ \\
     MATCH_MP_TAC principle_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
 >> ‘hnf M1’ by rw [GSYM appstar_APPEND, hnf_appstar]
 >> ‘LENGTH args = m’ by rw [Abbr ‘m’]
 (* 1st SUBSET_TRANS *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M1’
 >> CONJ_TAC
 >- (irule hnf_children_FV_SUBSET \\
     rw [GSYM appstar_APPEND, hnf_appstar])
 (* 2nd SUBSET_TRANS *)
 >> Know ‘solvable (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC solvable_appstar \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘n'’] >> simp [])
 >> DISCH_TAC
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (M0 @* MAP VAR vs)’
 >> CONJ_TAC
 >- (qunabbrev_tac ‘M1’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> Q.PAT_X_ASSUM ‘M0 = LAMl xs (VAR y @* args)’ K_TAC
 >> rw [SUBSET_DEF, FV_appstar]
 >> Know ‘x IN FV M UNION set vs’
 >- (POP_ASSUM MP_TAC \\
     Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> POP_ASSUM K_TAC
 >> rw [Once IN_UNION]
 >- (Know ‘x IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 >> Know ‘set vs SUBSET RANK (SUC r)’
 >- (qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw [])
 >> DISCH_TAC
 >> Know ‘x IN RANK (SUC r)’ >- METIS_TAC [SUBSET_DEF]
 >> SET_TAC []
QED

Theorem subterm_induction_lemma' :
    !X M r M0 n m vs M1 Ms h.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
            m = hnf_children_size M0 /\
           vs = RNEWS r n X /\
           M1 = principle_hnf (M0 @* MAP VAR vs) /\
           Ms = hnf_children M1 /\ h < m
       ==> FV (EL h Ms) SUBSET X UNION RANK (SUC r)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC subterm_induction_lemma
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

Theorem subterm_FV_lemma :
    !X M r M0 n m vs M1 Ms h.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X /\
           M1 = principle_hnf (M0 @* MAP VAR vs) /\
           Ms = hnf_children M1 /\
            m = LENGTH Ms /\
            h < m
       ==> FV (EL h Ms) SUBSET X UNION RANK r UNION set vs
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> rfs []
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘M1’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘hnf M1’ by rw [hnf_appstar]
 >> Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM)
 >> ‘hnf_children M1 = args’ by rw [hnf_children_hnf]
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘FV (principle_hnf (M0 @* MAP VAR vs)) SUBSET FV (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
    ‘solvable M1’ by rw [solvable_iff_has_hnf, hnf_has_hnf] \\
     Suff ‘M0 @* MAP VAR vs == M1’ >- PROVE_TAC [lameq_solvable_cong] \\
     rw [])
 >> simp []
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> DISCH_TAC
 >> Know ‘FV (VAR y @* args) SUBSET FV M UNION set vs’
 >- (POP_ASSUM MP_TAC \\
     Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> POP_ASSUM K_TAC
 >> DISCH_TAC
 >> Know ‘FV (VAR y @* args) SUBSET X UNION RANK r UNION set vs’
 >- (POP_ASSUM MP_TAC \\
     Suff ‘FV M SUBSET X UNION RANK r’ >- SET_TAC [] >> art [])
 >> POP_ASSUM K_TAC
 >> DISCH_TAC
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV (VAR y @* args)’ >> art []
 >> rw [FV_appstar, SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNION]
 >> DISJ2_TAC
 >> Q.EXISTS_TAC ‘EL h args’ >> art []
 >> MATCH_MP_TAC EL_MEM >> art []
QED

Theorem subterm_headvar_lemma :
    !X M r M0 n vs M1.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X /\
           M1 = principle_hnf (M0 @* MAP VAR vs)
       ==> hnf_headvar M1 IN X UNION RANK (SUC r)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘solvable (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC solvable_appstar \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> Suff ‘FV M1 SUBSET X UNION RANK (SUC r)’
 >- rw [SUBSET_DEF, FV_appstar, IN_UNION]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV (M0 @* MAP VAR vs)’
 >> CONJ_TAC >- (qunabbrev_tac ‘M1’ \\
                 MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> REWRITE_TAC [FV_appstar_MAP_VAR]
 >> Q.PAT_X_ASSUM ‘M0 = _’ K_TAC
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV M UNION set vs’
 >> CONJ_TAC >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
                 qunabbrev_tac ‘M0’ \\
                 MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> rw [Abbr ‘vs’, SUBSET_DEF, IN_UNION]
 >- (Know ‘x IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 >> DISJ2_TAC
 >> Suff ‘set (RNEWS r n X) SUBSET RANK (SUC r)’ >- rw [SUBSET_DEF]
 >> rw [RNEWS_SUBSET_RANK]
QED

(* Proposition 10.1.6 [1, p.219] *)
Theorem lameq_BT_cong :
    !X M N r. FINITE X /\ FV M UNION FV N SUBSET X /\ M == N ==>
              BT' X M r = BT' X N r
Proof
    RW_TAC std_ss []
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     rw [BT_of_unsolvables])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 (* applying ltree_bisimulation *)
 >> rw [ltree_bisimulation]
 (* NOTE: ‘solvable P /\ solvable Q’ cannot be added here *)
 >> Q.EXISTS_TAC
     ‘\x y. ?P Q r. FV P UNION FV Q SUBSET X UNION RANK r /\
                    P == Q /\ x = BT' X P r /\ y = BT' X Q r’
 >> BETA_TAC
 >> CONJ_TAC
 >- (qexistsl_tac [‘M’, ‘N’, ‘r’] >> simp [] \\
     Q.PAT_X_ASSUM ‘FV M UNION FV N SUBSET X’ MP_TAC \\
     Q.PAT_X_ASSUM ‘FINITE X’ MP_TAC \\
     SET_TAC [])
 (* stage work *)
 >> qx_genl_tac [‘a1’, ‘ts1’, ‘a2’, ‘ts2’] >> STRIP_TAC
 >> qabbrev_tac ‘P0 = principle_hnf P’
 >> qabbrev_tac ‘Q0 = principle_hnf Q’
 >> qabbrev_tac ‘n  = LAMl_size P0’
 >> qabbrev_tac ‘n' = LAMl_size Q0’
 >> qabbrev_tac ‘vs = RNEWS r n  X’
 >> qabbrev_tac ‘vs'= RNEWS r n' X’
 >> qabbrev_tac ‘P1 = principle_hnf (P0 @* MAP VAR vs)’
 >> qabbrev_tac ‘Q1 = principle_hnf (Q0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ps = hnf_children P1’
 >> qabbrev_tac ‘Qs = hnf_children Q1’
 >> qabbrev_tac ‘y  = hnf_head P1’
 >> qabbrev_tac ‘y' = hnf_head Q1’
 (* applying ltree_unfold *)
 >> Q.PAT_X_ASSUM ‘_ = BT' X Q r’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def]
 >> Q.PAT_X_ASSUM ‘_ = BT' X P r’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def]
 >> NTAC 2 STRIP_TAC
 (* easy case: unsolvable P (and Q) *)
 >> reverse (Cases_on ‘solvable P’)
 >- (‘unsolvable Q’ by PROVE_TAC [lameq_solvable_cong] >> fs [] \\
     rw [llist_rel_def, LLENGTH_MAP])
 (* now both P and Q are solvable *)
 >> ‘solvable Q’ by PROVE_TAC [lameq_solvable_cong]
 >> fs []
 (* applying lameq_principle_hnf_size_eq' *)
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘P0’, ‘Q0’] \\
     MATCH_MP_TAC lameq_principle_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* proving y = y' *)
 >> STRONG_CONJ_TAC
 >- (MP_TAC (Q.SPECL [‘r’, ‘X’, ‘P’, ‘Q’, ‘P0’, ‘Q0’, ‘n’, ‘vs’, ‘P1’, ‘Q1’]
                     lameq_principle_hnf_head_eq) \\
     simp [GSYM solvable_iff_has_hnf])
 >> DISCH_THEN (rfs o wrap o GSYM)
 >> qunabbrevl_tac [‘y’, ‘y'’]
 (* applying lameq_principle_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘P’, ‘Q’, ‘P0’, ‘Q0’, ‘n’, ‘vs’, ‘P1’, ‘Q1’]
                     lameq_principle_hnf_thm)
 >> simp [GSYM solvable_iff_has_hnf]
 >> rw [llist_rel_def, LLENGTH_MAP, EL_MAP]
 >> Cases_on ‘i < LENGTH Ps’ >> fs [LNTH_fromList, EL_MAP]
 >> Q.PAT_X_ASSUM ‘(EL i Ps,SUC r) = z’  (ONCE_REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘(EL i Qs,SUC r) = z'’ (ONCE_REWRITE_TAC o wrap o SYM)
 >> qexistsl_tac [‘EL i Ps’, ‘EL i Qs’, ‘SUC r’] >> simp []
 >> qabbrev_tac ‘n = LAMl_size Q0’
 >> qabbrev_tac ‘m = LENGTH Qs’
 >> CONJ_TAC (* 2 symmetric subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘P’,‘P0’, ‘n’, ‘m’, ‘vs’, ‘P1’] >> simp [] \\
      qunabbrev_tac ‘vs’ \\
      Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
     ‘DISJOINT (set vs) (FV P0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
      Q_TAC (HNF_TAC (“P0 :term”, “vs :string list”,
                      “y  :string”, “args :term list”)) ‘P1’ \\
     ‘TAKE (LAMl_size P0) vs = vs’ by rw [] \\
      POP_ASSUM (rfs o wrap) \\
      Q.PAT_X_ASSUM ‘LENGTH Ps = m’ (REWRITE_TAC o wrap o SYM) \\
      AP_TERM_TAC >> simp [Abbr ‘Ps’],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘Q’,‘Q0’, ‘n’, ‘m’, ‘vs’, ‘Q1’] >> simp [] \\
      qunabbrev_tac ‘vs’ \\
      Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
     ‘DISJOINT (set vs) (FV Q0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
      Q_TAC (HNF_TAC (“Q0 :term”, “vs :string list”,
                      “y  :string”, “args :term list”)) ‘Q1’ \\
     ‘TAKE (LAMl_size Q0) vs = vs’ by rw [] \\
      POP_ASSUM (rfs o wrap) \\
      qunabbrev_tac ‘m’ \\
      AP_TERM_TAC >> simp [Abbr ‘Qs’] ]
QED

(* NOTE: This theorem indicates that ‘m = LENGTH Ms’ is more natural. *)
Theorem BT_ltree_el_NIL[local] :
    !X M r. ltree_el (BT' X M r) [] =
          if solvable M then
             let
               M0 = principle_hnf M;
                n = LAMl_size M0;
               vs = RNEWS r n X;
               M1 = principle_hnf (M0 @* MAP VAR vs);
               Ms = hnf_children M1;
                y = hnf_headvar M1;
                l = MAP (\e. (e,SUC r)) Ms;
                m = LENGTH Ms;
             in
               SOME (SOME (vs,y),SOME m)
          else
               SOME (NONE,SOME 0)
Proof
    rw [BT_def, Once ltree_unfold, BT_generator_def, ltree_el_def]
 >> simp [LMAP_fromList]
QED

(* This version uses ‘m = hnf_children_size M0’ *)
Theorem BT_ltree_el_NIL_alt[local] :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
          ltree_el (BT' X M r) [] =
          if solvable M then
             let
               M0 = principle_hnf M;
                n = LAMl_size M0;
                m = hnf_children_size M0;
               vs = RNEWS r n X;
               M1 = principle_hnf (M0 @* MAP VAR vs);
               Ms = hnf_children M1;
                y = hnf_headvar M1;
                l = MAP (\e. (e,SUC r)) Ms
             in
               SOME (SOME (vs,y),SOME m)
          else
               SOME (NONE,SOME 0)
Proof
    RW_TAC std_ss [BT_ltree_el_NIL]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (rfs o wrap o SYM)
 >> qunabbrevl_tac [‘m’, ‘m'’]
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC hnf_children_size_alt
 >> qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

(*---------------------------------------------------------------------------*
 *  More subterm properties
 *---------------------------------------------------------------------------*)

(* M0 is not needed if M is already an hnf *)
Theorem subterm_of_hnf :
    !X M h p r. FINITE X /\ hnf M ==>
      subterm X M (h::p) r =
        let  n = LAMl_size M;
            vs = RNEWS r n X;
            M1 = principle_hnf (M @* MAP VAR vs);
            Ms = hnf_children M1;
             m = LENGTH Ms;
        in
            if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principle_hnf_reduce]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘n' = n’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs' = vs’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1' = M1’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms' = Ms’ (fs o wrap o SYM)
QED

Theorem subterm_of_hnf_alt :
    !X M h p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ hnf M ==>
      subterm X M (h::p) r =
        let  n = LAMl_size M;
             m = hnf_children_size M;
            vs = RNEWS r n X;
            M1 = principle_hnf (M @* MAP VAR vs);
            Ms = hnf_children M1
        in
            if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [subterm_alt]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principle_hnf_reduce]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘n' = n’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs' = vs’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1' = M1’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms' = Ms’ (fs o wrap o SYM)
QED

(* In the extreme case, M is a absfree hnf (i.e. VAR y @* args), and the
   definition of subterm can be greatly simplified.
 *)
Theorem subterm_of_absfree_hnf :
    !X M h p r. hnf M /\ ~is_abs M ==>
       subterm X M (h::p) r =
       let Ms = hnf_children M;
            m = LENGTH Ms
       in
           if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principle_hnf_reduce]
 >> fs [Abbr ‘M0’]
 >> Know ‘n = 0’
 >- (qunabbrev_tac ‘n’ \\
     MATCH_MP_TAC LAMl_size_eq_0 >> art [])
 >> DISCH_THEN (fs o wrap)
 >> fs [Abbr ‘vs’]
 >> Q.PAT_X_ASSUM ‘Ms' = Ms’ (fs o wrap o SYM)
QED

Theorem subterm_of_absfree_hnf_explicit :
    !X y Ms h p r.
       subterm X (VAR y @* Ms) (h::p) r =
       if h < LENGTH Ms then
          subterm X (EL h Ms) p (SUC r)
       else
          NONE
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘VAR y @* Ms’, ‘h’, ‘p’, ‘r’] subterm_of_absfree_hnf)
 >> rw [hnf_appstar, is_abs_appstar]
QED

Theorem subterm_of_principle_hnf :
    !X M p r. solvable M /\ p <> [] ==>
              subterm X (principle_hnf M) p r = subterm X M p r
Proof
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> Cases_on ‘p’ >> fs []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘solvable M0’ by PROVE_TAC [solvable_principle_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0' = M0’ by rw [Abbr ‘M0'’, Abbr ‘M0’, principle_hnf_stable']
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘n = n'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
QED

(* NOTE: When subterm X M p = NONE, either 1) M or its subterm is unsolvable,
   or 2) p runs out of ltree_paths (BT X M). If we knew subterm X M p <> NONE
   a priori, then p IN ltree_paths (BT X M) must hold.
 *)
Theorem subterm_imp_ltree_paths :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
              p IN ltree_paths (BT' X M r)
Proof
    Induct_on ‘p’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> POP_ASSUM MP_TAC (* subterm X M (h::p) r <> NONE *)
 >> reverse (Cases_on ‘solvable M’)
 >- simp [subterm_def, ltree_paths_def, ltree_lookup]
 >> UNBETA_TAC [subterm_alt] “subterm X M (h::p) r”
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X M r”
 >> simp [LMAP_fromList, EL_MAP, Abbr ‘l’]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 (* extra work *)
 >> qunabbrev_tac ‘y’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Cases_on ‘h < m’ >> simp []
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap)
 >> DISCH_TAC
 >> simp [GSYM BT_def]
 >> fs [ltree_paths_def, ltree_lookup_def, LNTH_fromList, EL_MAP]
 >> T_TAC
 (* extra work *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

(* ltree_lookup returns more information (the entire subtree), thus can be
   used to construct the return value of ltree_el.

   NOTE: This theorem connects ‘ltree_el’ and ‘ltree_lookup’ for Boehm trees

   |- !X M p r.
         p IN ltree_paths (BT' X M r) ==>
         ltree_el (BT' X M r) p =
         do t' <- ltree_lookup (BT' X M r) p;
            SOME (ltree_node t',LLENGTH (ltree_children t'))
         od
 *)
Theorem BT_ltree_el_thm =
        ltree_el_alt_ltree_lookup |> INST_TYPE [“:'a” |-> “:BT_node”]
                                  |> Q.SPECL [‘p’, ‘BT' X M r’]
                                  |> Q.GENL [‘X’, ‘M’, ‘p’, ‘r’]

(* Lemma 10.1.15 [1, p.222] (subterm and ltree_lookup) *)
Theorem BT_subterm_lemma :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
              ltree_lookup (BT' X M r) p <> NONE /\
              BT X (THE (subterm X M p r)) = THE (ltree_lookup (BT' X M r) p)
Proof
    Induct_on ‘p’
 >- rw [subterm_def, ltree_lookup_def]
 >> rpt GEN_TAC
 >> UNBETA_TAC [subterm_def] “subterm X M (h::p) r”
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X M r”
 >> simp [LMAP_fromList, EL_MAP, Abbr ‘l’]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> STRIP_TAC
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 (* extra work *)
 >> qabbrev_tac ‘Y = RANK r’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qunabbrev_tac ‘y’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> simp [ltree_lookup, LNTH_fromList, EL_MAP, GSYM BT_def]
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (rfs o wrap)
 (* extra work *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

(* Lemma 10.1.15 (related) [1, p.222] (subterm and ltree_el)

   Assuming all involved terms are solvable:

   - “ltree_el (BT X M) p” returns ‘SOME (SOME (vs,y),SOME k)’ (ltree node),
   - “subterm X M p” returns ‘(Z,N)’ where N is the actual subterm.

   Then M0 := principle_hnf N has the explicit form: ‘LAMl vs (VAR y @* Ms)’,
   and ‘LENGTH Ms = k’ (NOTE: vs, y and k come from ‘ltree_el (BT X M) p’.

 *)
Theorem BT_subterm_thm :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE /\
              solvable (subterm' X M p r)
        ==> do (N,r') <- subterm X M p r;
                (t,m) <- ltree_el (BT' X M r) p;
               (xs,y) <- t;
                  M0 <<- principle_hnf N;
                   n <<- LAMl_size M0;
                  vs <<- RNEWS r' n X;
                  M1 <<- principle_hnf (M0 @* MAP VAR vs);
              return (vs = xs /\ hnf_headvar M1 = y /\
                      hnf_children_size M1 = THE m)
            od = SOME T
Proof
    rpt STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [subterm_imp_ltree_paths]
 >> Know ‘ltree_lookup (BT' X M r) p <> NONE /\
          BT X (THE (subterm X M p r)) = THE (ltree_lookup (BT' X M r) p)’
 >- (MATCH_MP_TAC BT_subterm_lemma >> art [])
 >> STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> gs [GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
 >> rename1 ‘subterm X M p r = SOME t’
 >> Cases_on ‘t’ >> fs []
 >> rename1 ‘subterm X M p r = SOME (N,r')’
 >> rw [BT_ltree_el_thm]
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X N r'”
 >> simp [LMAP_fromList, Abbr ‘l’]
(* stage work *)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r' :num”, “n :num”)) ‘X’
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘N’, ‘r'’, ‘n’] >> simp [] \\
     PROVE_TAC [subterm_rank_lemma])
 >> DISCH_TAC
 >> qunabbrev_tac ‘y’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> rw [Abbr ‘Ms’]
QED

(* NOTE: In the above theorem, when the antecedents hold, i.e.

         p IN ltree_paths (BT X M) /\ subterm X M p = NONE

   Then ‘subterm' X M (FRONT p)’ must be an unsolvable term. This result can be
   even improved to an iff, as the present theorem shows.
 *)
Theorem subterm_is_none_iff_parent_unsolvable :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p IN ltree_paths (BT' X M r) ==>
             (subterm X M p r = NONE <=>
              p <> [] /\ subterm X M (FRONT p) r <> NONE /\
              unsolvable (subterm' X M (FRONT p) r))
Proof
    Induct_on ‘p’ >- rw [subterm_def]
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BT' X M r)’ MP_TAC \\
     simp [subterm_def, BT_of_unsolvables, ltree_paths_def, ltree_lookup_def])
 >> UNBETA_TAC [subterm_of_solvables] “subterm X M (h::p) r”
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘Y = RANK r’
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘Ms’
 (* stage work, now M is solvable *)
 >> Cases_on ‘p = []’
 >- (rw [subterm_NIL] \\
     Q.PAT_X_ASSUM ‘[h] IN ltree_paths (BT' X M r)’ MP_TAC \\
     simp [BT_def, Once ltree_unfold, BT_generator_def, ltree_paths_def,
           ltree_lookup_def, LNTH_fromList] \\
     Cases_on ‘h < m’ >> simp [])
 (* now: p <> [] *)
 >> Know ‘h < m’
 >- (Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BT' X M r)’ MP_TAC \\
     simp [BT_def, Once ltree_unfold, BT_generator_def, ltree_paths_def,
           ltree_lookup_def, LNTH_fromList, EL_MAP] \\
     fs [] \\
     Cases_on ‘h < m’ >> simp [])
 >> DISCH_TAC
 >> simp [FRONT_DEF]
 (* stage work *)
 >> qabbrev_tac ‘N = EL h args’
 >> Know ‘subterm X M (h::FRONT p) r = subterm X N (FRONT p) (SUC r)’
 >- rw [subterm_def]
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘p <> []’ (rfs o wrap)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 (* p IN ltree_paths (BT X N) *)
 >> Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BT' X M r)’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def, ltree_paths_def,
          ltree_lookup_def, LNTH_fromList, EL_MAP]
 >> fs []
 >> DISCH_THEN K_TAC >> T_TAC
 >> qunabbrev_tac ‘N’
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

Theorem subterm_is_none_exclusive :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p IN ltree_paths (BT' X M r) /\
              subterm X M p r = NONE ==> subterm X M (FRONT p) r <> NONE
Proof
    METIS_TAC [subterm_is_none_iff_parent_unsolvable]
QED

(* NOTE: for whatever reasons such that ‘subterm X M p = NONE’, even when
        ‘p NOTIN ltree_paths (BT X M)’, the conclusion (rhs) always holds.
 *)
Theorem subterm_is_none_inclusive :
    !X M p r. subterm X M p r = NONE <=>
              !q. p <<= q ==> subterm X M q r = NONE
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- (DISCH_THEN (MP_TAC o (Q.SPEC ‘p’)) >> rw [])
 >> Q.ID_SPEC_TAC ‘r’
 >> Q.ID_SPEC_TAC ‘M’
 >> Q.ID_SPEC_TAC ‘X’
 >> Q.ID_SPEC_TAC ‘p’
 >> Induct_on ‘p’ >- rw [subterm_NIL]
 >> rw [subterm_def]
 >> Cases_on ‘q’ >> fs [subterm_def]
QED

Theorem subterm_solvable_lemma :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p <> [] /\ subterm X M p r <> NONE ==>
            (!q. q <<= p ==> subterm X M q r <> NONE) /\
            (!q. q <<= FRONT p ==> solvable (subterm' X M q r))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [subterm_imp_ltree_paths]
 >> CONJ_ASM1_TAC
 >- (Q.X_GEN_TAC ‘q’ >> DISCH_TAC \\
     CCONTR_TAC \\
     POP_ASSUM (MP_TAC o (REWRITE_RULE [Once subterm_is_none_inclusive])) \\
     DISCH_THEN (MP_TAC o (Q.SPEC ‘p’)) >> rw [])
 >> ‘0 < LENGTH p’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0]
 >> Q.X_GEN_TAC ‘q’
 >> Suff ‘!l. l <> [] /\ l <<= p ==> solvable (subterm' X M (FRONT l) r)’
 >- (DISCH_TAC \\
     DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_EQ_TAKE])) \\
     Know ‘q = FRONT (TAKE (SUC n) p)’
     >- (Know ‘FRONT (TAKE (SUC n) p) = TAKE (SUC n - 1) p’
         >- (MATCH_MP_TAC FRONT_TAKE \\
             rfs [LENGTH_FRONT]) >> Rewr' \\
         POP_ASSUM (ONCE_REWRITE_TAC o wrap) >> simp [] \\
         MATCH_MP_TAC TAKE_FRONT >> rfs [LENGTH_FRONT]) >> Rewr' \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     qabbrev_tac ‘l = TAKE (SUC n) p’ \\
     CONJ_TAC
     >- (rfs [LENGTH_FRONT, NOT_NIL_EQ_LENGTH_NOT_0, Abbr ‘l’, LENGTH_TAKE]) \\
     rw [IS_PREFIX_EQ_TAKE] \\
     Q.EXISTS_TAC ‘SUC n’ >> rw [Abbr ‘l’] \\
     rfs [LENGTH_FRONT])
 >> rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘l’, ‘X’, ‘M’, ‘r’]
                    subterm_is_none_iff_parent_unsolvable)
 >> ‘l IN ltree_paths (BT' X M r)’ by PROVE_TAC [ltree_paths_inclusive]
 >> simp []
 >> Suff ‘subterm X M (FRONT l) r <> NONE’ >- PROVE_TAC []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC IS_PREFIX_TRANS
 >> Q.EXISTS_TAC ‘l’ >> rw []
 >> MATCH_MP_TAC IS_PREFIX_BUTLAST' >> art []
QED

(* This stronger lemma does not require ‘subterm X M p r <> NONE’ *)
Theorem subterm_valid_path_lemma :
    !X p M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p IN ltree_paths (BT' X M r) /\ p <> [] ==>
              !q. q <<= FRONT p ==> subterm X M q r <> NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Cases_on ‘subterm X M p r = NONE’
 >- (POP_ASSUM MP_TAC \\
     rw [subterm_is_none_iff_parent_unsolvable] \\
     Cases_on ‘FRONT p = []’ >- fs [] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘FRONT p’, ‘r’] subterm_solvable_lemma) \\
     rw [])
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_solvable_lemma)
 >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC isPREFIX_TRANS
 >> Q.EXISTS_TAC ‘FRONT p’ >> rw [IS_PREFIX_BUTLAST']
QED

(* NOTE: ‘subterm X M p <> NONE’ implies ‘!q. q <<= FRONT p ==> solvable
  (subterm' X M q)’, and the following theorem deals with the case of
  ‘unsolvable (subterm' X M p)’.
 *)
Theorem BT_ltree_el_of_unsolvables :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
             (unsolvable (subterm' X M p r) <=>
              ltree_el (BT' X M r) p = SOME bot)
Proof
    Induct_on ‘p’
 >- (rpt STRIP_TAC \\
     EQ_TAC >- rw [BT_of_unsolvables, ltree_el_def] \\
     rpt STRIP_TAC \\
     fs [BT_ltree_el_NIL])
 >> rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_solvable_lemma)
 >> rw []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘[]’))
 >> rw [] (* solvable M *)
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) r <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘!q. q <<= h::p ==> subterm X M q r <> NONE’ K_TAC
 >> UNBETA_TAC [subterm_def] “subterm X M (h::p) r”
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X M r”
 >> simp [LMAP_fromList, EL_MAP, Abbr ‘l’]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> simp [LMAP_fromList, GSYM BT_def, ltree_el, LNTH_fromList, EL_MAP]
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 (* extra work *)
 >> qabbrev_tac ‘Y = RANK r’
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> qunabbrev_tac ‘y’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Cases_on ‘h < m’ >> simp []
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> DISCH_TAC
 (* applying IH *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 (* extra goals *)
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

(* NOTE: This proof is almost identical with the above lemma. Also note that
         the actual term behind ‘bot’ is different with the one above.
 *)
Theorem BT_ltree_lookup_of_unsolvables :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
             (unsolvable (subterm' X M p r) <=>
              ltree_lookup (BT' X M r) p = SOME bot)
Proof
    Induct_on ‘p’
 >- (rpt STRIP_TAC \\
     EQ_TAC >- rw [BT_of_unsolvables, ltree_lookup_def] \\
     rpt STRIP_TAC \\
     fs [ltree_lookup, BT_def, BT_generator_def, Once ltree_unfold])
 >> rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_solvable_lemma)
 >> rw []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘[]’))
 >> rw [] (* solvable M *)
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) r <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘!q. q <<= h::p ==> subterm X M q r <> NONE’ K_TAC
 >> UNBETA_TAC [subterm_def] “subterm X M (h::p) r”
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X M r”
 >> simp [LMAP_fromList, EL_MAP, Abbr ‘l’]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> simp [LMAP_fromList, GSYM BT_def, ltree_lookup, LNTH_fromList, EL_MAP]
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 (* extra work *)
 >> qabbrev_tac ‘Y = RANK r’
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> qunabbrev_tac ‘y’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Cases_on ‘h < m’ >> simp []
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap)
 >> T_TAC
 >> DISCH_TAC
 (* applying IH *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 (* extra goals *)
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

Theorem lameq_subterm_cong_none :
    !p X M N r. FINITE X /\
                FV M SUBSET X UNION RANK r /\
                FV N SUBSET X UNION RANK r /\ M == N ==>
               (subterm X M p r = NONE <=> subterm X N p r = NONE)
Proof
    Q.X_GEN_TAC ‘p’
 >> Cases_on ‘p = []’ >- rw []
 >> POP_ASSUM MP_TAC
 >> Q.ID_SPEC_TAC ‘p’
 >> Induct_on ‘p’ >- rw []
 >> RW_TAC std_ss []
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     Cases_on ‘p’ >> fs [subterm_def])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘M0’, ‘M0'’] \\
     MATCH_MP_TAC lameq_principle_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* applying lameq_principle_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘M’, ‘N’, ‘M0’, ‘M0'’, ‘n’, ‘vs’, ‘M1’, ‘M1'’]
                     lameq_principle_hnf_thm')
 >> simp []
 >> RW_TAC std_ss [Abbr ‘m’, Abbr ‘m'’]
 (* preparing for hnf_children_FV_SUBSET

    Here, once again, we need to get suitable explicit forms of P0 and Q0,
    to show that, P1 and Q1 are absfree hnf.
  *)
 >> qabbrev_tac ‘n = LAMl_size M0'’
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0) /\ DISJOINT (set vs) (FV M0')’
      by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> Q_TAC (HNF_TAC (“M0':term”, “vs :string list”,
                    “y' :string”, “args':term list”)) ‘M1'’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 (* refine P1 and Q1 again for clear assumptions using them *)
 >> qunabbrevl_tac [‘M1’, ‘M1'’]
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘M1' = principle_hnf (M0' @* MAP VAR vs)’
 >> ‘args = Ms’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘args' = Ms'’ (fs o wrap o SYM)
 >> qabbrev_tac ‘m = LENGTH args'’
 >> T_TAC
 >> Cases_on ‘h < m’ >> simp []
 >> Cases_on ‘p = []’ >> fs []
 (* final stage *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> simp []
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘M’, ‘M0’,  ‘n’, ‘m’, ‘vs’, ‘M1’ ] >> simp [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘N’, ‘M0'’, ‘n’, ‘m’, ‘vs’, ‘M1'’] >> simp [] ]
QED

Theorem lameq_subterm_cong :
    !p X M N r. FINITE X /\
                FV M SUBSET X UNION RANK r /\
                FV N SUBSET X UNION RANK r /\
                M == N /\
                subterm X M p r <> NONE /\
                subterm X N p r <> NONE
            ==> subterm' X M p r == subterm' X N p r
Proof
    Q.X_GEN_TAC ‘p’
 >> Cases_on ‘p = []’ >- rw []
 >> POP_ASSUM MP_TAC
 >> Q.ID_SPEC_TAC ‘p’
 >> Induct_on ‘p’ >- rw []
 >> RW_TAC std_ss []
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     Cases_on ‘p’ >> fs [subterm_def])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 >> Q.PAT_X_ASSUM ‘subterm X N (h::p) r <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) r <> NONE’ MP_TAC
 >> RW_TAC std_ss [subterm_of_solvables]
 >> gs []
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘M0’, ‘M0'’] \\
     MATCH_MP_TAC lameq_principle_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* applying lameq_principle_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘M’, ‘N’, ‘M0’, ‘M0'’, ‘n’, ‘vs’, ‘M1’, ‘M1'’]
                     lameq_principle_hnf_thm') >> simp []
 >> RW_TAC std_ss [Abbr ‘m’, Abbr ‘m'’]
 (* preparing for hnf_children_FV_SUBSET *)
 >> qabbrev_tac ‘n = LAMl_size M0'’
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0) /\ DISJOINT (set vs) (FV M0')’
      by METIS_TAC [subterm_disjoint_lemma']
 (* NOTE: the next two HNF_TAC will refine M1 and M1' *)
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> Q_TAC (HNF_TAC (“M0':term”, “vs :string list”,
                    “y' :string”, “args':term list”)) ‘M1'’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 (* refine P1 and Q1 again for clear assumptions using them *)
 >> qunabbrevl_tac [‘M1’, ‘M1'’]
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘M1' = principle_hnf (M0' @* MAP VAR vs)’
 >> ‘args = Ms’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘args' = Ms'’ (fs o wrap o SYM)
 >> qabbrev_tac ‘m = LENGTH args'’
 >> T_TAC
 >> Cases_on ‘p = []’ >> fs []
 (* final stage *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> simp []
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘M’, ‘M0’,  ‘n’, ‘m’, ‘vs’, ‘M1’ ] >> simp [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘N’, ‘M0'’, ‘n’, ‘m’, ‘vs’, ‘M1'’] >> simp [] ]
QED

(*****************************************************************************)
(*   ‘subterm X M p r’ w.r.t. different X and r                              *)
(*****************************************************************************)

Theorem subterm_tpm_lemma :
    !X Y p M pi r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV (tpm pi M) SUBSET Y UNION RANK r' /\
         set (MAP FST pi) SUBSET RANK r /\
         set (MAP SND pi) SUBSET RANK r' /\ r <= r'
     ==> (subterm X M p r = NONE <=>
          subterm Y (tpm pi M) p r' = NONE) /\
         (subterm X M p r <> NONE ==>
          ?pi'. tpm pi' (subterm' X M p r) = subterm' Y (tpm pi M) p r')
Proof
    qx_genl_tac [‘X’, ‘Y’]
 >> Induct_on ‘p’
 >- (rw [] >> Q.EXISTS_TAC ‘pi’ >> rw [])
 (* stage work *)
 >> rpt GEN_TAC >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable (tpm pi M)’ by PROVE_TAC [solvable_tpm] \\
     simp [subterm_def])
 >> ‘solvable (tpm pi M)’ by PROVE_TAC [solvable_tpm]
 >> UNBETA_TAC [subterm_alt] “subterm X M (h::p) r”
 (* preparing for expanding ‘subterm' Y (tpm pi M) (h::p)’ *)
 >> qabbrev_tac ‘M0' = principle_hnf (tpm pi M)’
 >> Know ‘M0' = tpm pi M0’
 >- (qunabbrevl_tac [‘M0’, ‘M0'’] \\
     MATCH_MP_TAC principle_hnf_tpm' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘m' = hnf_children_size M0'’
 >> Know ‘m' = m’ >- rw [Abbr ‘m’, Abbr ‘m'’, hnf_children_size_tpm]
 >> DISCH_TAC
 >> qabbrev_tac ‘n' = LAMl_size M0'’
 >> Know ‘n' = n’ >- rw [Abbr ‘n’, Abbr ‘n'’, LAMl_size_tpm]
 >> DISCH_TAC
 (* special case *)
 >> reverse (Cases_on ‘h < m’) >- simp [subterm_alt]
 (* stage work, now h < m *)
 >> simp [] (* eliminate ‘h < m’ in the goal *)
 >> UNBETA_TAC [subterm_alt] “subterm Y (tpm pi M) (h::p) r'”
 >> Q.PAT_X_ASSUM ‘tpm pi M0 = principle_hnf (tpm pi M)’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘n  = n'’  (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘n  = n''’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m' = m''’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m  = m'’  (fs o wrap o SYM)
 (* stage work *)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> qunabbrev_tac ‘vs'’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r' :num”, “n :num”)) ‘Y’
 (* vs1 is a permutated version of vs', to be used as first principles *)
 >> qabbrev_tac ‘vs1 = listpm string_pmact (REVERSE pi) vs'’
 >> ‘ALL_DISTINCT vs1’ by rw [Abbr ‘vs1’]
 (* rewriting inside the abbreviation of M1' *)
 >> Know ‘tpm pi M0 @* MAP VAR vs' = tpm pi (M0 @* MAP VAR vs1)’
 >- (rw [Abbr ‘vs1’, tpm_appstar] \\
     Suff ‘listpm term_pmact pi (MAP VAR (listpm string_pmact (REVERSE pi) vs')) =
           MAP VAR vs'’ >- rw [] \\
     rw [LIST_EQ_REWRITE, EL_MAP])
 >> DISCH_THEN (fs o wrap)
 (* prove that ‘M0 @* MAP VAR vs1’ correctly denude M0 *)
 >> Know ‘DISJOINT (set vs1) (FV M)’
 >- (rw [Abbr ‘vs1’, DISJOINT_ALT', MEM_listpm] \\
     Suff ‘DISJOINT (set vs') (FV (tpm pi M))’
     >- rw [DISJOINT_ALT', FV_tpm] \\
     MATCH_MP_TAC subterm_disjoint_lemma \\
     qabbrev_tac ‘n = LENGTH vs'’ \\
     qexistsl_tac [‘Y’, ‘r'’, ‘n’] >> simp [] \\
     rw [Abbr ‘M0’, principle_hnf_tpm'])
 >> DISCH_TAC
 >> ‘LENGTH vs1 = n’ by rw [Abbr ‘vs1’, LENGTH_listpm]
 (* stage work, now defining vs2 manually by primitives *)
 >> qabbrev_tac ‘Z = X UNION Y UNION set vs UNION set vs1’
 >> qabbrev_tac ‘z = SUC (string_width Z)’
 (* NOTE: vs is in rank r; vs1 seems also in the same rank *)
 >> qabbrev_tac ‘vs2 = alloc r z (z + n)’
 (* properties of vs2 *)
 >> Know ‘DISJOINT (set vs2) Z’
 >- (rw [Abbr ‘vs2’, Abbr ‘z’, DISJOINT_ALT', alloc_def, MEM_MAP] \\
     ONCE_REWRITE_TAC [TAUT ‘~P \/ Q \/ ~R <=> P /\ R ==> Q’] \\
     STRIP_TAC \\
    ‘FINITE Z’ by rw [Abbr ‘Z’] \\
     MP_TAC (Q.SPECL [‘x’, ‘Z’] string_width_thm) >> rw [])
 >> qunabbrev_tac ‘Z’
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> qabbrev_tac ‘Z = X UNION Y UNION set vs UNION set vs1’
 >> Know ‘DISJOINT (set vs2) (FV M)’
 >- (Q.PAT_X_ASSUM ‘FV M SUBSET X UNION RANK r’ MP_TAC \\
     rw [DISJOINT_ALT'] \\
     Know ‘x IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
     rw [IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs2) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Q.PAT_X_ASSUM ‘x IN FV M’ K_TAC \\
     Q.PAT_X_ASSUM ‘x IN RANK r’ MP_TAC \\
     Suff ‘DISJOINT (RANK r) (set vs2)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs2’ \\
     rw [DISJOINT_ALT, RANK, alloc_def, MEM_MAP] \\
     rw [n2s_11])
 >> DISCH_TAC
 >> ‘ALL_DISTINCT vs2 /\ LENGTH vs2 = n’ by rw [Abbr ‘vs2’, alloc_thm]
 (* stage work *)
 >> Know ‘DISJOINT (set vs2) (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘M2 = principle_hnf (M0 @* MAP VAR vs2)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs2 :string list”,
                    “y :string”, “args :term list”)) ‘M2’
 >> ‘TAKE n vs2 = vs2’ by rw [TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 >> ‘hnf M2’ by rw [hnf_appstar]
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs2) (FV M0)’ K_TAC
 >> Know ‘DISJOINT (set vs)  (FV M2) /\
          DISJOINT (set vs1) (FV M2)’
 >- (CONJ_TAC (* 2 subgoals, same tactics *) \\
     (MATCH_MP_TAC DISJOINT_SUBSET \\
      Q.EXISTS_TAC ‘FV M0 UNION set vs2’ \\
      CONJ_TAC >- (Q.PAT_X_ASSUM ‘M0 = LAMl vs2 (VAR y @* args)’ K_TAC \\
                   reverse (rw [DISJOINT_UNION'])
                   >- rw [Once DISJOINT_SYM] \\
                   MATCH_MP_TAC DISJOINT_SUBSET \\
                   Q.EXISTS_TAC ‘FV M’ >> art [] \\
                   qunabbrev_tac ‘M0’ \\
                   MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     ‘FV M0 UNION set vs2 = FV (M0 @* MAP VAR vs2)’ by rw [] >> POP_ORW \\
      qunabbrev_tac ‘M2’ \\
      MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
      Know ‘solvable (VAR y @* args)’
      >- (rw [solvable_iff_has_hnf] \\
          MATCH_MP_TAC hnf_has_hnf \\
          rw [hnf_appstar]) >> DISCH_TAC \\
      Suff ‘M0 @* MAP VAR vs2 == VAR y @* args’
      >- PROVE_TAC [lameq_solvable_cong] \\
      rw []))
 >> STRIP_TAC
 (* rewriting M1 and M1' (much harder) by tpm of M2 *)
 >> Know ‘M1 = tpm (ZIP (vs2,vs)) M2’
 >- (simp [Abbr ‘M1’] \\
     MATCH_MP_TAC principle_hnf_tpm_reduce' \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’
        (ONCE_REWRITE_TAC o wrap o SYM) >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘p1 = ZIP (vs2,vs)’
 >> Know ‘M1' = tpm pi (principle_hnf (M0 @* MAP VAR vs1))’
 >- (qunabbrev_tac ‘M1'’ \\
     MATCH_MP_TAC principle_hnf_tpm >> art [] \\
     REWRITE_TAC [has_hnf_thm] \\
     Q.EXISTS_TAC ‘fromPairs vs2 (MAP VAR vs1) ' (VAR y @* args)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC hreduce_LAMl_appstar \\
         rw [EVERY_MEM, MEM_MAP] >> rw [] \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs2) (set vs1)’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
    ‘FDOM (fromPairs vs2 (MAP VAR vs1)) = set vs2’ by rw [FDOM_fromPairs] \\
     Cases_on ‘MEM y vs2’
     >- (simp [ssub_thm, ssub_appstar, hnf_appstar] \\
         fs [MEM_EL] >> rename1 ‘i < LENGTH vs2’ \\
         Know ‘fromPairs vs2 (MAP VAR vs1) ' (EL i vs2) = EL i (MAP VAR vs1)’
         >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
         rw [EL_MAP]) \\
     simp [ssub_thm, ssub_appstar, hnf_appstar])
 >> DISCH_TAC
 >> Know ‘M1' = tpm pi (tpm (ZIP (vs2,vs1)) M2)’
 >- (POP_ORW >> simp [] \\
     MATCH_MP_TAC principle_hnf_tpm_reduce' \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’
        (ONCE_REWRITE_TAC o wrap o SYM) >> art [])
 >> POP_ASSUM K_TAC (* M1' = ... (already used) *)
 >> REWRITE_TAC [GSYM pmact_decompose]
 >> qabbrev_tac ‘p2 = pi ++ ZIP (vs2,vs1)’
 >> DISCH_TAC (* M1' = tpm p2 M2 *)
 (* applying hnf_children_tpm *)
 >> Know ‘Ms = MAP (tpm p1) args’
 >- (simp [Abbr ‘Ms’] \\
    ‘hnf_children M2 = args’ by rw [hnf_children_hnf] \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     rw [hnf_children_tpm])
 >> Rewr'
 >> Know ‘Ms' = MAP (tpm p2) args’
 >- (simp [Abbr ‘Ms'’] \\
    ‘hnf_children M2 = args’ by rw [hnf_children_hnf] \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     rw [hnf_children_tpm])
 >> Rewr'
 >> ‘LENGTH args = m’ by rw [Abbr ‘m’]
 >> simp [EL_MAP]
 >> qabbrev_tac ‘N = EL h args’
 >> qabbrev_tac ‘pi' = p2 ++ REVERSE p1’
 (* final stage *)
 >> Know ‘tpm p2 N = tpm pi' (tpm p1 N)’
 >- rw [Abbr ‘pi'’, pmact_decompose]
 >> Rewr'
 >> qabbrev_tac ‘N' = tpm p1 N’
 (* finally, using IH in a bulk way *)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 (* extra goal #1 (easy) *)
 >> CONJ_TAC
 >- (simp [Abbr ‘N'’, SUBSET_DEF, FV_tpm] \\
     rpt STRIP_TAC \\
     Know ‘FV N SUBSET FV M2’
     >- (qunabbrev_tac ‘N’ \\
         irule hnf_children_FV_SUBSET >> rw []) >> DISCH_TAC \\
     qabbrev_tac ‘x' = lswapstr (REVERSE p1) x’ \\
    ‘x' IN FV M2’ by METIS_TAC [SUBSET_DEF] \\
     Know ‘FV M2 SUBSET FV (M0 @* MAP VAR vs2)’
     >- (‘solvable M2’ by rw [solvable_iff_has_hnf, hnf_has_hnf] \\
         ‘M0 @* MAP VAR vs2 == M2’ by rw [] \\
         qunabbrev_tac ‘M2’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
         PROVE_TAC [lameq_solvable_cong]) \\
    ‘FV (M0 @* MAP VAR vs2) = FV M0 UNION set vs2’ by rw [] >> POP_ORW \\
     DISCH_TAC \\
     Know ‘FV M0 UNION set vs2 SUBSET FV M UNION set vs2’
     >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     DISCH_TAC \\
    ‘x' IN FV M UNION set vs2’ by METIS_TAC [SUBSET_TRANS, SUBSET_DEF] \\
    ‘x = lswapstr p1 x'’ by rw [Abbr ‘x'’] >> POP_ORW \\
     Suff ‘lswapstr p1 x' IN FV M UNION set vs’
     >- (Suff ‘FV M UNION set vs SUBSET X UNION RANK (SUC r)’
         >- SET_TAC [] \\
         simp [UNION_SUBSET] \\
         CONJ_TAC >- (MATCH_MP_TAC SUBSET_TRANS \\
                      Q.EXISTS_TAC ‘X UNION RANK r’ >> art [] \\
                      Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
                      MATCH_MP_TAC RANK_MONO >> rw []) \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘RANK (SUC r)’ >> simp [] \\
         qunabbrev_tac ‘vs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) \\
     MP_TAC (Q.SPECL [‘REVERSE p1’, ‘x'’, ‘FV M UNION set vs’]
                     (GSYM ssetpm_IN)) \\
     SIMP_TAC list_ss [pmact_UNION] \\
     Suff ‘x' IN ssetpm (REVERSE p1) (FV M) \/
           x' IN ssetpm (REVERSE p1) (set vs)’ >- simp [] \\
     Know ‘ssetpm (REVERSE p1) (FV M) = FV M’
     >- (irule ssetpm_14b \\
         simp [Abbr ‘p1’, REVERSE_ZIP, MAP_ZIP]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘x' IN FV M UNION set vs2’ MP_TAC \\
     rw [IN_UNION] >- (DISJ1_TAC >> art []) \\
     DISJ2_TAC \\
     qunabbrev_tac ‘p1’ \\
     MATCH_MP_TAC MEM_lswapstr >> rw [])
  (* extra goal #2 (hard) *)
 >> CONJ_TAC
 >- (simp [Abbr ‘N'’, FV_tpm, SUBSET_DEF] \\
     simp [GSYM lswapstr_append, GSYM REVERSE_APPEND] \\
     Q.X_GEN_TAC ‘x’ \\
     qabbrev_tac ‘x' = lswapstr (REVERSE (pi' ++ p1)) x’ \\
     qabbrev_tac ‘p3 = pi' ++ p1’ \\
    ‘x = lswapstr p3 x'’ by rw [Abbr ‘x'’] >> POP_ORW \\
     Know ‘FV N SUBSET FV M2’
     >- (qunabbrev_tac ‘N’ \\
         irule hnf_children_FV_SUBSET >> rw []) >> DISCH_TAC \\
     DISCH_TAC (* x' IN FV N *) \\
    ‘x' IN FV M2’ by METIS_TAC [SUBSET_DEF] \\
     Know ‘FV M2 SUBSET FV (M0 @* MAP VAR vs2)’
     >- (‘solvable M2’ by rw [solvable_iff_has_hnf, hnf_has_hnf] \\
         ‘M0 @* MAP VAR vs2 == M2’ by rw [] \\
         qunabbrev_tac ‘M2’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
         PROVE_TAC [lameq_solvable_cong]) \\
    ‘FV (M0 @* MAP VAR vs2) = FV M0 UNION set vs2’ by rw [] >> POP_ORW \\
     DISCH_TAC \\
     Know ‘FV M0 UNION set vs2 SUBSET FV M UNION set vs2’
     >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     DISCH_TAC \\
     Q.PAT_X_ASSUM ‘FV (tpm pi M) SUBSET Y UNION RANK r'’ MP_TAC \\
     simp [FV_tpm, SUBSET_DEF] \\
     DISCH_TAC \\
  (* NOTE: current relations of permutations:

     p1 = ZIP (vs2,vs)
     p2 = pi ++ ZIP (vs2,vs1)
     pi' = p2 ++ REVERSE p1
     p3 = pi' ++ p1 = p2 ++ REVERSE p1 ++ p1 == p2
     p4 = REVERSE pi ++ p3
     p4 = REVERSE pi ++ pi ++ ZIP (vs2,vs1) == ZIP (vs2,vs1)
   *)
    ‘p3 == p2’ by rw [Abbr ‘p3’, Abbr ‘pi'’, permof_inverse_append] \\
     qabbrev_tac ‘p4 = REVERSE pi ++ p3’ \\
     Know ‘p4 == ZIP (vs2,vs1)’
     >- (qunabbrev_tac ‘p4’ \\
         MATCH_MP_TAC (GEN_ALL permeq_trans) \\
         Q.EXISTS_TAC ‘REVERSE pi ++ p2’ \\
         CONJ_TAC
         >- (MATCH_MP_TAC app_permeq_monotone >> rw []) \\
         rw [Abbr ‘p2’, APPEND_ASSOC] \\
         MATCH_MP_TAC (GEN_ALL permeq_trans) \\
         Q.EXISTS_TAC ‘[] ++ ZIP (vs2,vs1)’ \\
         CONJ_TAC
         >- (MATCH_MP_TAC app_permeq_monotone >> rw [permof_inverse]) \\
         rw []) >> DISCH_TAC \\
    ‘x' IN FV M UNION set vs2’ by METIS_TAC [SUBSET_TRANS, SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘FV N SUBSET FV M2’ K_TAC \\
     Q.PAT_X_ASSUM ‘x' IN FV N’ K_TAC \\
     Q.PAT_X_ASSUM ‘x' IN FV M2’ K_TAC \\
     qunabbrev_tac ‘N’ \\
  (* stage work *)
     POP_ASSUM MP_TAC >> REWRITE_TAC [IN_UNION] \\
     STRIP_TAC (* x' IN FV M *)
     >- (Q.PAT_X_ASSUM ‘!x. lswapstr (REVERSE pi) x IN FV M ==> P’
           (MP_TAC o Q.SPEC ‘lswapstr p3 x'’) \\
         simp [GSYM pmact_append, IN_UNION] \\
         Suff ‘lswapstr p4 x' IN FV M’
         >- (rw [] >- art [] \\
             DISJ2_TAC \\
             Know ‘RANK r' SUBSET RANK (SUC r')’ >- rw [RANK_MONO] \\
             rw [SUBSET_DEF]) \\
         Know ‘lswapstr p4 x' = lswapstr (ZIP (vs2,vs1)) x'’
         >- (Q.PAT_X_ASSUM ‘p4 == ZIP (vs2,vs1)’ MP_TAC \\
             rw [permeq_thm]) >> Rewr' \\
         MP_TAC (Q.SPECL [‘REVERSE (ZIP (vs2,vs1))’, ‘x'’, ‘FV M’]
                         (GSYM ssetpm_IN)) \\
         SIMP_TAC list_ss [] >> DISCH_THEN K_TAC \\
         qabbrev_tac ‘p5 = REVERSE (ZIP (vs2,vs1))’ \\
         Suff ‘ssetpm p5 (FV M) = FV M’ >- (Rewr' >> art []) \\
         MATCH_MP_TAC ssetpm_14b \\
         simp [Abbr ‘p5’, MAP_REVERSE, MAP_ZIP]) \\
  (* remaining goal: MEM x' vs2 *)
     DISJ2_TAC \\
     Know ‘lswapstr p3 x' = lswapstr p2 x'’
     >- (Q.PAT_X_ASSUM ‘p3 == p2’ MP_TAC \\
         rw [permeq_thm]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!x. lswapstr (REVERSE pi) x IN FV M ==> P’ K_TAC \\
     simp [Abbr ‘p2’, pmact_append] \\
     POP_ASSUM MP_TAC (* MEM x' vs2 *) \\
     simp [MEM_EL] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
     POP_ORW (* ‘EL i vs2’ in the goal *) \\
     Know ‘lswapstr (ZIP (vs2,vs1)) (EL i vs2) = EL i vs1’
     >- (MATCH_MP_TAC lswapstr_apply_EL >> rw []) >> Rewr' \\
     simp [Abbr ‘vs1’] \\
     qabbrev_tac ‘vs1 = listpm string_pmact (REVERSE pi) vs'’ \\
     MP_TAC (Q.SPECL [‘r'’, ‘SUC r'’, ‘n’, ‘Y’] RNEWS_SUBSET_RANK) \\
     rw [SUBSET_DEF] \\
     POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM])
 (* final goals *)
 >> simp [Abbr ‘pi'’, MAP_APPEND, MAP_REVERSE, Abbr ‘p2’, Abbr ‘p1’, MAP_ZIP]
 >> Know ‘set (MAP FST pi) SUBSET RANK (SUC r)’
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘RANK r’ >> rw [RANK_MONO])
 >> Rewr
 >> Know ‘set (MAP SND pi) SUBSET RANK (SUC r')’
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘RANK r'’ >> rw [RANK_MONO])
 >> Rewr
 >> Know ‘set vs2 SUBSET RANK (SUC r)’
 >- (qunabbrev_tac ‘vs2’ \\
     MATCH_MP_TAC alloc_SUBSET_RANK >> rw [])
 >> Rewr
 (* NOTE: This proof requires that ‘r <= r'’ !!! *)
 >> Know ‘set vs SUBSET RANK (SUC r')’
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘RANK (SUC r)’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC RANK_MONO >> rw []) \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw [])
 >> Rewr
 (* final goal: set vs1 SUBSET RANK r' *)
 >> simp [SUBSET_DEF, Abbr ‘vs1’, MEM_listpm, MEM_EL]
 >> rpt STRIP_TAC
 >> rename1 ‘i < n’
 >> qabbrev_tac ‘x' = EL i vs'’
 >> ‘x = lswapstr (REVERSE pi) x'’ by rw []
 >> POP_ORW
 >> Q.PAT_X_ASSUM ‘lswapstr pi x = x'’ K_TAC
 >> Know ‘x' IN ROW r'’
 >- (MP_TAC (Q.SPECL [‘r'’, ‘n’, ‘Y’] RNEWS_SUBSET_ROW) \\
     simp [SUBSET_DEF] >> DISCH_THEN MATCH_MP_TAC \\
     rw [Abbr ‘x'’, EL_MEM])
 >> DISCH_TAC
 (* NOTE: x' is in rank r', while pi is either < r <= r' or < r', thus
    either key or value of pi is in rank < r'. Thus it works.
  *)
 >> Suff ‘lswapstr (REVERSE pi) x' = x'’
 >- (Rewr' \\
     MP_TAC (Q.SPECL [‘r'’, ‘SUC r'’, ‘n’, ‘Y’] RNEWS_SUBSET_RANK) \\
     simp [SUBSET_DEF] \\
     DISCH_THEN MATCH_MP_TAC \\
     rw [Abbr ‘x'’, EL_MEM])
 (* applying lswapstr_14b *)
 >> MATCH_MP_TAC lswapstr_14b
 >> simp [MAP_REVERSE]
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2): ~MEM x' (MAP FST pi) *)
      MP_TAC (Q.SPECL [‘r’, ‘r'’, ‘n’] RANK_ROW_DISJOINT) \\
      simp [DISJOINT_ALT] >> DISCH_TAC \\
      CCONTR_TAC >> METIS_TAC [SUBSET_DEF],
      (* goal 2 (of 2): ~MEM x' (MAP SND pi) *)
      MP_TAC (Q.SPECL [‘r'’, ‘r'’, ‘n’] RANK_ROW_DISJOINT) \\
      simp [DISJOINT_ALT] >> DISCH_TAC \\
      CCONTR_TAC >> METIS_TAC [SUBSET_DEF] ]
QED

(* This lemma reduces one more antecedent in subterm_tpm_lemma *)
Theorem FV_tpm_lemma :
    !Y M pi r r'. FINITE Y /\ FV M SUBSET Y UNION RANK r' /\
                  set (MAP FST pi) SUBSET RANK r /\
                  set (MAP SND pi) SUBSET RANK r' /\ r <= r'
              ==> FV (tpm pi M) SUBSET Y UNION RANK r'
Proof
    rpt STRIP_TAC
 >> rw [FV_tpm, SUBSET_DEF]
 >> qabbrev_tac ‘v = lswapstr (REVERSE pi) x’
 >> ‘x = lswapstr pi v’ by rw [Abbr ‘v’]
 >> POP_ORW
 >> Q.PAT_X_ASSUM ‘set (MAP SND pi) SUBSET RANK r'’ MP_TAC
 >> Q.PAT_X_ASSUM ‘set (MAP FST pi) SUBSET RANK r’  MP_TAC
 >> Know ‘v IN Y UNION RANK r'’ >- METIS_TAC [SUBSET_DEF]
 >> Q.PAT_X_ASSUM ‘r <= r'’ MP_TAC
 >> KILL_TAC
 >> Q.ID_SPEC_TAC ‘v’
 >> Induct_on ‘pi’ >- rw []
 >> rw [MAP]
 >> Q.PAT_X_ASSUM ‘!v. P’ (MP_TAC o Q.SPEC ‘v’) >> rw []
 >> qabbrev_tac ‘x = FST h’
 >> qabbrev_tac ‘y = SND h’
 >> qabbrev_tac ‘z = lswapstr pi v’
 >> rw [swapstr_def] >- ASM_SET_TAC []
 >> Suff ‘RANK r SUBSET RANK r'’ >- ASM_SET_TAC []
 >> rw [RANK_MONO]
QED

(* In this special version, X = Y *)
Theorem subterm_tpm_lemma' :
    !X p M pi r r'.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         set (MAP FST pi) SUBSET RANK r /\
         set (MAP SND pi) SUBSET RANK r' /\ r <= r' ==>
        (subterm X M p r = NONE <=> subterm X (tpm pi M) p r' = NONE) /\
        (subterm X M p r <> NONE ==>
         ?pi'. tpm pi' (subterm' X M p r) = subterm' X (tpm pi M) p r')
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MATCH_MP_TAC subterm_tpm_lemma >> art []
 >> MATCH_MP_TAC FV_tpm_lemma
 >> Q.EXISTS_TAC ‘r’ >> art []
 >> ‘RANK r SUBSET RANK r'’ by rw [RANK_MONO]
 >> ASM_SET_TAC []
QED

Theorem subterm_tpm_cong_lemma[local] :
    !X Y p M r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV M SUBSET Y UNION RANK r' /\ r <= r'
     ==> (subterm X M p r = NONE <=> subterm Y M p r' = NONE) /\
         (subterm X M p r <> NONE ==>
          tpm_rel (subterm' X M p r) (subterm' Y M p r'))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘p’, ‘M’, ‘[]’, ‘r’, ‘r'’] subterm_tpm_lemma)
 >> simp [tpm_rel_def]
QED

(* NOTE: ‘r <= r'’ is removed now. This is the final strong version. *)
Theorem subterm_tpm_cong :
    !X Y M p r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV M SUBSET Y UNION RANK r'
     ==> (subterm X M p r = NONE <=> subterm Y M p r' = NONE) /\
         (subterm X M p r <> NONE ==>
          tpm_rel (subterm' X M p r) (subterm' Y M p r'))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘r <= r' \/ r' <= r’ by rw []
 >- METIS_TAC [subterm_tpm_cong_lemma]
 >> REWRITE_TAC [tpm_rel_alt]
 >> MP_TAC (Q.SPECL [‘Y’, ‘X’, ‘p’, ‘M’, ‘r'’, ‘r’] subterm_tpm_cong_lemma)
 >> simp [tpm_rel_def]
 >> METIS_TAC []
QED

Theorem subterm_solvable_cong :
    !X Y M p r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV M SUBSET Y UNION RANK r' /\
         subterm X M p r <> NONE ==>
        (solvable (subterm' X M p r) <=> solvable (subterm' Y M p r'))
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘M’, ‘p’, ‘r’, ‘r'’] subterm_tpm_cong)
 >> rw []
 >> fs [tpm_rel_alt, solvable_tpm]
QED

(* In this way, two such terms have the same ‘hnf_children_size o principle_hnf’,
   because head reductions are congruence w.r.t. tpm.
 *)
Theorem subterm_hnf_children_size_cong :
    !X Y M p r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV M SUBSET Y UNION RANK r' /\
         subterm X M p r <> NONE /\ solvable (subterm' X M p r) ==>
         hnf_children_size (principle_hnf (subterm' X M p r)) =
         hnf_children_size (principle_hnf (subterm' Y M p r'))
Proof
    rpt STRIP_TAC
 >> ‘subterm Y M p r' <> NONE /\
     tpm_rel (subterm' X M p r) (subterm' Y M p r')’
       by METIS_TAC [subterm_tpm_cong]
 >> fs [tpm_rel_def]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> qabbrev_tac ‘N = subterm' X M p r’
 >> rw [principle_hnf_tpm']
QED

Theorem BT_tpm_lemma[local] :
    !X M pi r. FINITE X /\ FV M SUBSET X UNION RANK r /\
               set (MAP FST pi) SUBSET RANK r /\
               set (MAP SND pi) SUBSET RANK r
           ==> ltree_node (BT' X (tpm pi M) r) =
               ltree_node
                 (ltree_map (OPTION_MAP (λ(vs,y). (vs,lswapstr pi y))) (BT' X M r))
Proof
    rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘ltree_node (BT' X (tpm pi M) r) =
                       ltree_node (ltree_map f (BT' X M r))’
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable (tpm pi M)’ by rw [solvable_tpm] \\
     rw [BT_of_unsolvables, ltree_map, Abbr ‘f’])
 >> ‘solvable (tpm pi M)’ by rw [solvable_tpm]
 >> rw [BT_def, Once ltree_unfold, BT_generator_def]
 >> rw [BT_def, Once ltree_unfold, BT_generator_def, LMAP_fromList, ltree_map]
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> simp [principle_hnf_tpm']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Know ‘tpm pi M0 @* MAP VAR vs = tpm pi (M0 @* MAP VAR vs)’
 >- (simp [tpm_appstar] >> AP_TERM_TAC \\
     simp [Once LIST_EQ_REWRITE, EL_MAP] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC (GSYM lswapstr_14b) \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Know ‘DISJOINT (set (MAP FST pi)) (set (RNEWS r n X))’
       >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
           Q.EXISTS_TAC ‘RANK r’ >> art [] \\
           MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) \\
       rw [DISJOINT_ALT'] \\
       POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM],
       (* goal 2 (of 2) *)
       Know ‘DISJOINT (set (MAP SND pi)) (set (RNEWS r n X))’
       >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
           Q.EXISTS_TAC ‘RANK r’ >> art [] \\
           MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) \\
       rw [DISJOINT_ALT'] \\
       POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM] ])
 >> Rewr'
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw [] >> POP_ASSUM (rfs o wrap)
 >> Know ‘principle_hnf (tpm pi (LAMl vs (VAR y @* args) @* MAP VAR vs)) =
          tpm pi (principle_hnf (LAMl vs (VAR y @* args) @* MAP VAR vs))’
 >- (MATCH_MP_TAC principle_hnf_tpm' \\
    ‘LAMl vs (VAR y @* args) @* MAP VAR vs == VAR y @* args’
       by PROVE_TAC [lameq_LAMl_appstar_VAR] \\
     Suff ‘solvable (VAR y @* args)’ >- PROVE_TAC [lameq_solvable_cong] \\
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf >> simp [hnf_appstar])
 >> Rewr'
 >> simp [principle_hnf_beta_reduce, hnf_appstar, tpm_appstar]
 >> rw [Abbr ‘f’]
QED

Theorem BT_tpm_thm :
    !X M pi r. FINITE X /\ FV M SUBSET X UNION RANK r /\
               set (MAP FST pi) SUBSET RANK r /\
               set (MAP SND pi) SUBSET RANK r
           ==> BT' X (tpm pi M) r =
               ltree_map (OPTION_MAP (λ(vs,y). (vs,lswapstr pi y))) (BT' X M r)
Proof
    rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘BT' X (tpm pi M) r = ltree_map f (BT' X M r)’
 >> rw [ltree_bisimulation]
 >> Q.EXISTS_TAC ‘\t1 t2. ?N q. FV N SUBSET X UNION RANK q /\ r <= q /\
                                t1 = BT' X (tpm pi N) q /\
                                t2 = ltree_map f (BT' X N q) /\
                                ltree_node t1 = ltree_node t2’
 >> rw []
 >- (qexistsl_tac [‘M’, ‘r’] >> rw [Abbr ‘f’] \\
     MATCH_MP_TAC BT_tpm_lemma >> art [])
 (* stage work *)
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> reverse (Cases_on ‘solvable N’)
 >- (‘unsolvable (tpm pi N)’ by rw [solvable_tpm] \\
     simp [BT_of_unsolvables, Abbr ‘f’] >> Rewr' \\
     rw [llist_rel_def, ltree_map])
 >> ‘solvable (tpm pi N)’ by rw [solvable_tpm]
 >> Q_TAC (UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def]) ‘BT' X N q’
 >> Q_TAC (UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def])
          ‘BT' X (tpm pi N) q’
 >> gs [Abbr ‘M0'’, principle_hnf_tpm']
 >> Rewr' (* this eliminates ‘a’ and ‘ts’, both used already *)
 >> Q.PAT_X_ASSUM ‘n = n'’ (fs o wrap o SYM)
 >> fs [Abbr ‘vs'’]
 >> Q.PAT_X_ASSUM ‘RNEWS q n X = vs’ (rfs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “q :num”, “n :num”)) ‘X’
 >> Know ‘tpm pi M0 @* MAP VAR vs = tpm pi (M0 @* MAP VAR vs)’
 >- (simp [tpm_appstar] >> AP_TERM_TAC \\
     simp [Once LIST_EQ_REWRITE, EL_MAP] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC (GSYM lswapstr_14b) \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Know ‘DISJOINT (set (MAP FST pi)) (set (RNEWS q n X))’
       >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
           Q.EXISTS_TAC ‘RANK q’ \\
           reverse CONJ_TAC
           >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> rw [RANK_MONO]) \\
           MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) \\
       rw [DISJOINT_ALT'] \\
       POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM],
       (* goal 2 (of 2) *)
       Know ‘DISJOINT (set (MAP SND pi)) (set (RNEWS q n X))’
       >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
           Q.EXISTS_TAC ‘RANK q’ \\
           reverse CONJ_TAC
           >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> rw [RANK_MONO]) \\
           MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) \\
       rw [DISJOINT_ALT'] \\
       POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM] ])
 >> DISCH_THEN (fs o wrap)
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qunabbrevl_tac [‘y’, ‘y'’]
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw [] >> POP_ASSUM (rfs o wrap)
 >> simp [Abbr ‘M1'’, Abbr ‘Ms’, Abbr ‘Ms'’, Abbr ‘l’, Abbr ‘l'’]
 >> Know ‘principle_hnf (tpm pi (LAMl vs (VAR y @* args) @* MAP VAR vs)) =
          tpm pi (principle_hnf (LAMl vs (VAR y @* args) @* MAP VAR vs))’
 >- (MATCH_MP_TAC principle_hnf_tpm' \\
    ‘LAMl vs (VAR y @* args) @* MAP VAR vs == VAR y @* args’
       by PROVE_TAC [lameq_LAMl_appstar_VAR] \\
     Suff ‘solvable (VAR y @* args)’ >- PROVE_TAC [lameq_solvable_cong] \\
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf \\
     simp [hnf_appstar])
 >> Rewr'
 >> simp [principle_hnf_beta_reduce, hnf_appstar, tpm_appstar]
 >> simp [ltree_map, Abbr ‘f’, LMAP_fromList]
 >> Rewr' (* this eliminates ‘ts'’, already used *)
 (* stage work *)
 >> simp [llist_rel_def, LLENGTH_fromList, LNTH_fromList, EL_MAP]
 >> rpt STRIP_TAC
 >> qexistsl_tac [‘EL i args’, ‘SUC q’]
 >> simp [GSYM BT_def]
 >> CONJ_ASM1_TAC
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘N’, ‘M0’, ‘n’, ‘LENGTH args’, ‘vs’, ‘M1’] >> rw [])
 >> MATCH_MP_TAC BT_tpm_lemma >> art []
 >> CONJ_TAC (* 2 subgoals, same tactics *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’
 >> rw [RANK_MONO]
QED

(* tpm doesn't change ltree_paths

   NOTE: ‘FV (tpm pi M) SUBSET X UNION RANK r’ is derivable from other antecedents.
 *)
Theorem BT_ltree_paths_tpm :
    !X M pi r. FINITE X /\ FV M SUBSET X UNION RANK r /\
               set (MAP FST pi) SUBSET RANK r /\
               set (MAP SND pi) SUBSET RANK r
           ==> ltree_paths (BT' X M r) = ltree_paths (BT' X (tpm pi M) r)
Proof
    rw [BT_tpm_thm]
QED

(*---------------------------------------------------------------------------*
 *  Equivalent terms
 *---------------------------------------------------------------------------*)

(* Definition 10.2.19 [1, p. 238]

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
               vs = NEWS (MAX n n') (FV M UNION FV N);
              vsM = TAKE n  vs;
              vsN = TAKE n' vs;
               M1 = principle_hnf (M0 @* MAP VAR vsM);
               N1 = principle_hnf (N0 @* MAP VAR vsN);
               y  = hnf_head M1;
               y' = hnf_head N1;
               m  = LENGTH (hnf_children M1);
               m' = LENGTH (hnf_children N1);
           in
               y = y' /\ n + m' = n' + m
        else
           ~solvable M /\ ~solvable N
End

Theorem equivalent_reflexive :
    reflexive equivalent
Proof
    rw [reflexive_def, equivalent_def]
QED

(* |- !x. equivalent x x *)
Theorem equivalent_refl[simp] =
        REWRITE_RULE [reflexive_def] equivalent_reflexive

Theorem equivalent_symmetric :
    symmetric equivalent
Proof
    RW_TAC std_ss [symmetric_def, equivalent_def, Once MAX_COMM, Once UNION_COMM]
 >> reverse (Cases_on ‘solvable x /\ solvable y’) >- fs []
 >> simp []
 >> rename1 ‘y1 = y2 /\ m1 + n = m + n1 <=> y3 = y4 /\ m3 + n1 = m2 + n3’
 >> ‘n3 = n’ by rw [Abbr ‘n3’, Abbr ‘n’] >> gs []
 >> EQ_TAC >> rw []
QED

(* |- !x y. equivalent x y <=> equivalent y x *)
Theorem equivalent_comm = REWRITE_RULE [symmetric_def] equivalent_symmetric

Theorem equivalent_of_solvables :
    !M N. solvable M /\ solvable N ==>
         (equivalent M N <=>
          let M0 = principle_hnf M;
              N0 = principle_hnf N;
              n  = LAMl_size M0;
              n' = LAMl_size N0;
              vs = NEWS (MAX n n') (FV M UNION FV N);
             vsM = TAKE n  vs;
             vsN = TAKE n' vs;
              M1 = principle_hnf (M0 @* MAP VAR vsM);
              N1 = principle_hnf (N0 @* MAP VAR vsN);
              y  = hnf_head M1;
              y' = hnf_head N1;
              m  = LENGTH (hnf_children M1);
              m' = LENGTH (hnf_children N1);
           in
              y = y' /\ n + m' = n' + m)
Proof
    RW_TAC std_ss [equivalent_def]
QED

(* beta-equivalent terms are also equivalent here *)
Theorem lameq_imp_equivalent :
    !M N. M == N ==> equivalent M N
Proof
    rpt STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     rw [equivalent_def])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 >> qabbrev_tac ‘X = FV M UNION FV N’
 >> ‘FINITE X’ by rw [Abbr ‘X’]
 >> ‘LAMl_size (principle_hnf M) = LAMl_size (principle_hnf N)’
       by METIS_TAC [lameq_principle_hnf_size_eq']
 (* stage work *)
 >> RW_TAC std_ss [equivalent_of_solvables] (* 2 subgoals, same tactics *)
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) X /\ LENGTH vs = n’
       by (rw [Abbr ‘vs’, NEWS_def])
 >> ‘vsM = vs’ by rw [Abbr ‘vsM’, TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘vs = vsN’ (fs o wrap o SYM)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘M0’, ‘N0’, ‘n’, ‘vs’, ‘M1’, ‘N1’]
                    lameq_principle_hnf_thm_simple)
 >> simp [Abbr ‘X’, GSYM solvable_iff_has_hnf]
QED

(* NOTE: the initial calls of ‘principle_hnf’ get eliminated if the involved
         terms are already in head normal forms.
 *)
Theorem equivalent_of_hnf :
    !M N. hnf M /\ hnf N ==>
         (equivalent M N <=>
          let n  = LAMl_size M;
              n' = LAMl_size N;
              vs = NEWS (MAX n n') (FV M UNION FV N);
             vsM = TAKE n  vs;
             vsN = TAKE n' vs;
              M1 = principle_hnf (M @* MAP VAR vsM);
              N1 = principle_hnf (N @* MAP VAR vsN);
              y  = hnf_head M1;
              y' = hnf_head N1;
              m  = LENGTH (hnf_children M1);
              m' = LENGTH (hnf_children N1)
           in
              y = y' /\ n + m' = n' + m)
Proof
    rpt STRIP_TAC
 >> ‘solvable M /\ solvable N’ by PROVE_TAC [hnf_has_hnf, solvable_iff_has_hnf]
 >> RW_TAC std_ss [equivalent_def, principle_hnf_reduce]
 >> METIS_TAC []
QED

(* From [1, p.238]. This concerte example shows that dB encoding is not easy in
   defining this "concept": the literal encoding of inner head variables are not
   the same for equivalent terms.
 *)
Theorem not_equivalent_example :
    !x y. x <> y ==> ~equivalent (LAM x (VAR y @@ t)) (LAM y (VAR y @@ t))
Proof
    qx_genl_tac [‘x’, ‘v’] >> DISCH_TAC
 >> ‘hnf (LAM x (VAR v @@ t)) /\ hnf (LAM v (VAR v @@ t))’ by rw []
 >> ‘solvable (LAM x (VAR v @@ t)) /\ solvable (LAM v (VAR v @@ t))’
       by rw [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [equivalent_of_solvables, principle_hnf_reduce]
 (* fix M0 *)
 >> qunabbrev_tac ‘M0’ >> qabbrev_tac ‘M0 = LAM x (VAR v @@ t)’
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M0 UNION FV N0) /\
     LENGTH vs = MAX n n'’ by rw [Abbr ‘vs’, NEWS_def]
 >> ‘DISJOINT (set vs) (FV M0) /\ DISJOINT (set vs) (FV N0)’
      by METIS_TAC [DISJOINT_SYM, DISJOINT_UNION]
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y1 :string”, “args1 :term list”)) ‘M1’
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs :string list”,
                    “y2 :string”, “args2 :term list”)) ‘N1’
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
 >> ‘VAR y1 = y’  by rw [Abbr ‘y’ , absfree_hnf_head]
 >> ‘VAR y2 = y'’ by rw [Abbr ‘y'’, absfree_hnf_head]
 >> qunabbrevl_tac [‘n’, ‘n'’]
 >> Know ‘LAMl_size M0 = 1 /\ LAMl_size N0 = 1’
 >- (rw [Abbr ‘M0’, Abbr ‘N0’, LAMl_size_def])
 >> DISCH_THEN (rfs o wrap)
 >> ‘vsN = vs’ by rw [Abbr ‘vsN’, TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘vs = vsM’ (rfs o wrap o SYM)
 >> qunabbrev_tac ‘vsN’
 (* stage work *)
 >> qabbrev_tac ‘z = HD vs’
 >> ‘vs = [z]’ by METIS_TAC [SING_HD]
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrevl_tac [‘M0’, ‘N0’]
 >> DISJ1_TAC
 >> qunabbrevl_tac [‘y’, ‘y'’]
 >> Q.PAT_X_ASSUM ‘VAR y1 = hnf_head M1’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘_ = LAM z (VAR y1 @* args1)’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘_ = LAM z (VAR y2 @* args2)’ (rfs o wrap o SYM)
 (* now the goal is ‘y1 <> y2’ *)
 >> qabbrev_tac ‘u = VAR v @@ t’
 >> ‘hnf u’ by rw [Abbr ‘u’]
 >> Know ‘M1 = [VAR z/x] u’
 >- (qunabbrev_tac ‘M1’ \\
     Cases_on ‘z = x’ >- (POP_ASSUM (gs o wrap) \\
                          fs [principle_hnf_beta_reduce1]) \\
     MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘u’] \\
     rfs [FV_thm])
 >> DISCH_THEN (rfs o wrap)
 >> Know ‘N1 = [VAR z/v] u’
 >- (qunabbrev_tac ‘N1’ \\
     Cases_on ‘z = v’ >- (POP_ASSUM (rfs o wrap)) \\
     MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘u’] \\
     rfs [FV_thm])
 >> DISCH_THEN (rfs o wrap)
 >> qunabbrevl_tac [‘M1’, ‘N1’]
 >> rfs [Abbr ‘u’, app_eq_appstar]
 >> METIS_TAC []
QED

Theorem equivalent_of_unsolvables :
    !M N. unsolvable M /\ unsolvable N ==> equivalent M N
Proof
    rw [equivalent_def]
QED

(*---------------------------------------------------------------------------*
 *  Boehm transformations
 *---------------------------------------------------------------------------*)

(* Definition 10.3.3 (i) [1, p.246] *)
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

Theorem Boehm_transform_MAP_rightctxt_o_VAR[simp] :
    Boehm_transform (MAP (rightctxt o VAR) vs)
Proof
    rw [Boehm_transform_def, EVERY_MAP]
QED

(* ‘apply pi M’ (applying a Boehm transformation) means "M^{pi}" or "pi(M)"

   NOTE: ‘apply [f3;f2;f1] M = (f3 o f2 o f1) M = f3 (f2 (f1 M))’

   NOTE2: This function seems general: “:('a -> 'a) list -> 'a -> 'a”.
 *)
Definition apply_def :
    apply_functions pi = FOLDR $o I pi
End

Overload apply = “apply_functions”

(* NOTE: either FOLDL or FOLDR is correct (due to combinTheory.o_ASSOC),
         but FOLDR seems more natural requiring natural list induction in
         the next proof(s), while FOLDL would require SNOC_INDUCT.
 *)
Theorem apply_alt :
    !pi. apply pi = FOLDL $o I pi
Proof
    REWRITE_TAC [apply_def]
 >> LIST_INDUCT_TAC >> rw [FOLDL, FOLDR]
 >> KILL_TAC (* only FOLDL is left *)
 >> qid_spec_tac ‘pi’ >> SNOC_INDUCT_TAC
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

(* Lemma 10.3.4 (ii) [1, p.246] *)
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

(* An corollary of the above lemma with ‘xs = {}’ *)
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

Theorem Boehm_apply_asmlam_cong :
    !pi M N. Boehm_transform pi /\ asmlam eqns M N ==>
             asmlam eqns (apply pi M) (apply pi N)
Proof
    SNOC_INDUCT_TAC >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> fs [solving_transform_def]
 >- rw [asmlam_rules]
 >> MATCH_MP_TAC asmlam_subst >> art []
QED

Theorem Boehm_apply_lameq_cong :
    !pi M N. Boehm_transform pi /\ M == N ==> apply pi M == apply pi N
Proof
    SNOC_INDUCT_TAC >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> MATCH_MP_TAC solving_transform_lameq >> art []
QED

Theorem Boehm_transform_APPEND :
    !p1 p2. Boehm_transform p1 /\ Boehm_transform p2 ==> Boehm_transform (p1 ++ p2)
Proof
    rw [Boehm_transform_def]
QED

Theorem Boehm_apply_APPEND :
    !p1 p2 M. apply (p1 ++ p2) M = apply p1 (apply p2 M)
Proof
    Q.X_GEN_TAC ‘p1’
 >> SNOC_INDUCT_TAC
 >> rw [APPEND_SNOC]
QED

Theorem Boehm_apply_SNOC_SUB :
    !(N :term) v p M. apply (SNOC [N/v] p) M = apply p ([N/v] M)
Proof
    rw [apply_def, FOLDR_SNOC]
QED

Theorem Boehm_apply_MAP_rightctxt :
    !Ns t. apply (MAP rightctxt Ns) t = t @* (REVERSE Ns)
Proof
    Induct_on ‘Ns’ >> rw [rightctxt_thm]
 >> rw [GSYM SNOC_APPEND]
QED

Theorem Boehm_apply_MAP_rightctxt' :
    !Ns t. apply (MAP rightctxt (REVERSE Ns)) t = t @* Ns
Proof
    rpt GEN_TAC
 >> qabbrev_tac ‘Ns' = REVERSE Ns’
 >> ‘Ns = REVERSE Ns'’ by rw [Abbr ‘Ns'’, REVERSE_REVERSE]
 >> rw [Boehm_apply_MAP_rightctxt]
QED

(* NOTE: if M is solvable, ‘apply pi M’ may not be solvable. *)
Theorem Boehm_apply_unsolvable :
    !pi M. Boehm_transform pi /\ unsolvable M ==> unsolvable (apply pi M)
Proof
    SNOC_INDUCT_TAC >> rw []
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
                          vs = NEWS n (FV M0);
                          M1 = principle_hnf (M0 @* MAP VAR vs);
                       in
                          EVERY (\e. hnf_headvar M1 # e) (hnf_children M1)
End

(* Definition 10.3.5 (iii)

   NOTE: The original definition uses ‘M == N’ in place of ‘M -h->* N’, but that
   is not enough for us, for the purposes of reduce ‘subterm X M p’ to
  ‘subterm X N p’, if only ‘M == N’ is known.
 *)
Definition is_ready_def :
    is_ready M <=> unsolvable M \/
                   ?N. M -h->* N /\ hnf N /\ ~is_abs N /\ head_original N
End

Definition is_ready' :
    is_ready' M <=> is_ready M /\ solvable M
End

(* NOTE: This alternative definition of ‘is_ready’ consumes ‘head_original’
         and eliminated the ‘principle_hnf’ inside it.
 *)
Theorem is_ready_alt :
    !M. is_ready M <=>
        unsolvable M \/ ?y Ns. M -h->* VAR y @* Ns /\ EVERY (\e. y # e) Ns
Proof
    Q.X_GEN_TAC ‘M’
 >> reverse EQ_TAC
 >- (rw [is_ready_def] >- art [] \\
     DISJ2_TAC >> Q.EXISTS_TAC ‘VAR y @* Ns’ >> art [] \\
     rw [head_original_def, hnf_appstar])
 (* stage work *)
 >> rw [is_ready_def] >- art []
 >> DISJ2_TAC
 >> qabbrev_tac ‘n = LAMl_size N’
 >> Q_TAC (NEWS_TAC (“vs :string list”, “n :num”)) ‘FV N’
 >> qabbrev_tac ‘M1 = principle_hnf (N @* MAP VAR vs)’
 >> ‘EVERY (\e. hnf_headvar M1 # e) (hnf_children M1)’
       by METIS_TAC [head_original_def]
 >> Know ‘?y args. N = LAMl (TAKE (LAMl_size N) vs) (VAR y @* args)’
 >- (Suff ‘ALL_DISTINCT vs /\ LAMl_size N <= LENGTH vs /\ DISJOINT (set vs) (FV N)’
     >- METIS_TAC [hnf_cases_shared] \\
     rw [Abbr ‘n’])
 >> ‘TAKE (LAMl_size N) vs = vs’ by rw [] >> POP_ORW
 >> STRIP_TAC
 >> Know ‘M1 = VAR y @* args’
 >- (rw [Abbr ‘M1’] \\
     MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> DISCH_THEN (fn th => fs [th, hnf_head_hnf, hnf_children_hnf])
 (* stage work *)
 >> qexistsl_tac [‘y’, ‘args’] >> art []
QED

Theorem is_ready_alt' :
    !M. is_ready' M <=> solvable M /\
                        ?y Ns. M -h->* VAR y @* Ns /\ EVERY (\e. y # e) Ns
Proof
 (* NOTE: this proof relies on the new [NOT_AND'] in boolSimps.BOOL_ss *)
    rw [is_ready', is_ready_alt, RIGHT_AND_OVER_OR]
 >> REWRITE_TAC [Once CONJ_COMM]
QED

(* ‘subterm_width M p’ is the maximal number of children of all subterms of form
   ‘subterm X M q r’ such that ‘q <<= FRONT p’, irrelevant with particular X and r.

   NOTE: ‘h::p IN ltree_paths (BT' X M r)’ is assumed when using this definition.

   NOTE: ‘solvable (subterm' (FV M) M q 0’ is added as an important fix.
 *)
Definition subterm_width_def :
    subterm_width M     [] = 0 /\
    subterm_width M (h::p) =
    MAX_SET (IMAGE (hnf_children_size o principle_hnf)
                   {subterm' (FV M) M q 0 | q |
                    q <<= FRONT (h::p) /\ solvable (subterm' (FV M) M q 0)})
End

(* |- subterm_width M [] = 0 *)
Theorem subterm_width_NIL[simp] = SPEC_ALL (cj 1 subterm_width_def)

Theorem subterm_width_alt :
    !M h p.
      subterm_width M (h::p) =
      MAX_SET {hnf_children_size (principle_hnf (subterm' (FV M) M q 0)) | q |
               q <<= FRONT (h::p) /\ solvable (subterm' (FV M) M q 0)}
Proof
    rw [subterm_width_def]
 >> AP_TERM_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘q’ >> art [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘subterm' (FV M) M q 0’ >> art [] \\
      Q.EXISTS_TAC ‘q’ >> art [] ]
QED

(* NOTE: ‘p <> []’ is necessary for ‘FRONT p’ to be meaningful, and then
   subterm_valid_path_lemma makes sure that all involved ‘subterm X M q r’
   are meaningful (IS_SOME).

   NOTE: ‘solvable t’ is necessary, but if ‘p IN ltree_paths (BT' X M r)’, then
   at most we have ‘unsolvable (subterm' X M (FRONT p) r)’, all earlier subterms
   are solvable.
 *)
Theorem subterm_width_thm :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p <> [] /\ p IN ltree_paths (BT' X M r) ==>
              subterm_width M p =
              MAX_SET (IMAGE (hnf_children_size o principle_hnf)
                             {subterm' X M q r | q |
                              q <<= FRONT p /\ solvable (subterm' X M q r)})
Proof
    rpt STRIP_TAC
 >> ‘!q. q <<= FRONT p ==> subterm X M q r <> NONE’
       by PROVE_TAC [subterm_valid_path_lemma]
 >> Cases_on ‘p’ >> fs []
 >> rw [subterm_width_def]
 >> qabbrev_tac ‘p = h::t’
 >> ‘p <> []’ by rw [Abbr ‘p’]
 (* preparing for subterm_hnf_children_size_cong *)
 >> Know ‘!Z R. IMAGE (hnf_children_size o principle_hnf)
                  {subterm' Z M q R | q | q <<= FRONT p /\ solvable (subterm' Z M q R)} =
                {hnf_children_size (principle_hnf (subterm' Z M q R)) | q |
                 q <<= FRONT p /\ solvable (subterm' Z M q R)}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘q’ >> art [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘subterm' Z M q R’ >> art [] \\
       Q.EXISTS_TAC ‘q’ >> art [] ])
 >> Rewr
 (* preparing for subterm_hnf_children_size_cong *)
 >> AP_TERM_TAC
 (* applying subterm_tpm_cong *)
 >> Suff ‘!q. q <<= FRONT p /\ solvable (subterm' X M q r) ==>
              hnf_children_size (principle_hnf (subterm' (FV M) M q 0)) =
              hnf_children_size (principle_hnf (subterm' X M q r))’
 >- (DISCH_TAC \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘q’ >> art [] \\
       CONJ_ASM2_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
       MP_TAC (Q.SPECL [‘X’, ‘FV M’, ‘M’, ‘q’, ‘r’, ‘0’] subterm_solvable_cong) \\
       simp [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘q’ >> art [] \\
       CONJ_TAC >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
                    FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
       MP_TAC (Q.SPECL [‘X’, ‘FV M’, ‘M’, ‘q’, ‘r’, ‘0’] subterm_solvable_cong) \\
       simp [] ])
 >> rpt STRIP_TAC
 (* applying subterm_hnf_children_size_cong *)
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC subterm_hnf_children_size_cong
 >> simp []
QED

Theorem subterm_width_thm' :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p <> [] /\ p IN ltree_paths (BT' X M r) ==>
              subterm_width M p =
              MAX_SET {hnf_children_size (principle_hnf (subterm' X M q r)) | q |
                       q <<= FRONT p /\ solvable (subterm' X M q r)}
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> AP_TERM_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘q’ >> art [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘subterm' X M q r’ >> art [] \\
      Q.EXISTS_TAC ‘q’ >> art [] ]
QED

Theorem subterm_width_first :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p <> [] /\ p IN ltree_paths (BT' X M r) /\ solvable M ==>
              hnf_children_size (principle_hnf M) <= subterm_width M p
Proof
    rpt STRIP_TAC
 >> ‘!q. q <<= FRONT p ==> subterm X M q r <> NONE’
       by PROVE_TAC [subterm_valid_path_lemma]
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> irule MAX_SET_PROPERTY
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE \\
     MATCH_MP_TAC SUBSET_FINITE_I \\
     Q.EXISTS_TAC ‘IMAGE (\q. subterm' X M q r) {q | q <<= FRONT p}’ \\
     reverse CONJ_TAC >- (rw [SUBSET_DEF] \\
                          Q.EXISTS_TAC ‘q’ >> art []) \\
     MATCH_MP_TAC IMAGE_FINITE \\
     rw [FINITE_prefix])
 >> rw [o_DEF]
 >> Q.EXISTS_TAC ‘M’ >> rw []
 >> Q.EXISTS_TAC ‘[]’ >> rw []
QED

Theorem subterm_width_last :
    !X M p q r. FINITE X /\ FV M SUBSET X UNION RANK r /\
         p <> [] /\ p IN ltree_paths (BT' X M r) /\
         q <<= FRONT p /\ solvable (subterm' X M q r) ==>
         hnf_children_size (principle_hnf (subterm' X M q r)) <=
         subterm_width M p
Proof
    rpt STRIP_TAC
 >> ‘!q. q <<= FRONT p ==> subterm X M q r <> NONE’
       by PROVE_TAC [subterm_valid_path_lemma]
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> irule MAX_SET_PROPERTY
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE \\
     MATCH_MP_TAC SUBSET_FINITE_I \\
     Q.EXISTS_TAC ‘IMAGE (\q. subterm' X M q r) {q | q <<= FRONT p}’ \\
     reverse CONJ_TAC >- (rw [SUBSET_DEF] \\
                          Q.EXISTS_TAC ‘q'’ >> art []) \\
     MATCH_MP_TAC IMAGE_FINITE \\
     rw [FINITE_prefix])
 >> rw [o_DEF]
 >> Q.EXISTS_TAC ‘subterm' X M q r’ >> rw []
 >> Q.EXISTS_TAC ‘q’ >> rw []
QED

(* cf. unsolvable_subst *)
Theorem solvable_subst :
    !X M M0 r v P d. FINITE X /\ FV M SUBSET X UNION RANK r /\ v IN X UNION RANK r /\
                     M0 = principle_hnf M /\
                     P = permutator d /\ hnf_children_size M0 <= d /\
                     solvable M ==> solvable ([P/v] M)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘M0 == M’ by rw [Abbr ‘M0’, lameq_principle_hnf']
 >> ‘[P/v] M0 == [P/v] M’ by rw [lameq_sub_cong]
 >> Suff ‘solvable ([P/v] M0)’ >- PROVE_TAC [lameq_solvable_cong]
 >> ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator]
 >> ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT']
 >> Know ‘~MEM v vs’
 >- (Q.PAT_X_ASSUM ‘v IN X UNION RANK r’ MP_TAC \\
     rw [IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art [])
 >> DISCH_TAC
 >> simp [LAMl_SUB, appstar_SUB]
 >> reverse (Cases_on ‘y = v’)
 >- (simp [SUB_THM, solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar])
 >> simp [solvable_iff_has_hnf, has_hnf_thm]
 >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> qabbrev_tac ‘m = LENGTH args’
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’]
 >> fs [hnf_children_size_thm]
 (* applying permutator_hreduce_thm *)
 >> MP_TAC (Q.SPECL [‘{}’, ‘d’, ‘args'’] permutator_hreduce_thm)
 >> rw [Abbr ‘P’]
 >> Q.EXISTS_TAC ‘LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs))’
 >> rw [hnf_appstar, hnf_thm]
QED

Theorem solvable_subst_cong :
    !X M M0 r v P d. FINITE X /\ FV M SUBSET X UNION RANK r /\ v IN X UNION RANK r /\
                     M0 = principle_hnf M /\
                     P = permutator d /\ hnf_children_size M0 <= d ==>
                    (solvable ([P/v] M) <=> solvable M)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- PROVE_TAC [unsolvable_subst]
 >> DISCH_TAC
 >> MATCH_MP_TAC solvable_subst
 >> qexistsl_tac [‘X’, ‘M0’, ‘r’, ‘d’] >> rw []
QED

(* NOTE: When n = LAMl_size M0 <= LENGTH vs = n', the ‘m = hnf_children_size M0’
   and ‘m' = LENGTH (hnf_children M1)’ are not the same (m <= m').
 *)
Theorem subterm_width_induction_lemma :
    !X M h p r M0 n n' m vs' M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         h::p IN ltree_paths (BT' X M r) /\
         solvable M /\
         M0 = principle_hnf M /\
          n = LAMl_size M0 /\ n <= n' /\
          m = hnf_children_size M0 /\ h < m /\
        vs' = RNEWS r n' X /\
         M1 = principle_hnf (M0 @* MAP VAR vs') /\
         Ms = hnf_children M1 ==>
        (subterm_width M (h::p) <= d <=>
         m <= d /\ subterm_width (EL h Ms) p <= d)
Proof
    RW_TAC std_ss []
 >> Know ‘!q. q <<= FRONT (h::p) ==> subterm X M q r <> NONE’
 >- (MATCH_MP_TAC subterm_valid_path_lemma >> rw [])
 >> DISCH_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’
 >> ‘DISJOINT (set vs') (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1' = principle_hnf (M0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ms = hnf_children M1'’
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_width_thm) >> simp []
 >> DISCH_THEN K_TAC (* used already *)
 >> Cases_on ‘p = []’
 >- (fs [] \\
     Know ‘{subterm' X M q r | q | q = [] /\ solvable (subterm' X M q r)} = {M}’
     >- csimp [Once EXTENSION] >> Rewr' \\
     Know ‘IMAGE (hnf_children_size o principle_hnf) {M} =
           {hnf_children_size (principle_hnf M)}’
     >- rw [Once EXTENSION] >> Rewr' \\
     simp [MAX_SET_SING])
 (* applying subterm_width_thm again *)
 >> MP_TAC (Q.SPECL [‘X’, ‘EL h Ms’, ‘p’, ‘SUC r’] subterm_width_thm)
 >> simp []
 >> Know ‘FV (EL h Ms) SUBSET X UNION RANK (SUC r)’
 >- (MATCH_MP_TAC subterm_induction_lemma \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘n'’, ‘m’, ‘vs'’, ‘M1'’] >> simp [])
 >> DISCH_TAC
 (* now decompose M0 in two ways (M1 and M1') *)
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                     “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘?y' args'. M0 = LAMl (TAKE n vs') (VAR y' @* args')’
 >- (qunabbrev_tac ‘n’ >> irule (iffLR hnf_cases_shared) \\
     Q.PAT_X_ASSUM ‘M0 = _’ K_TAC >> simp [])
 >> STRIP_TAC
 >> Know ‘solvable (M0 @* MAP VAR vs')’
 >- (MATCH_MP_TAC solvable_appstar \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘n'’] >> simp [])
 >> DISCH_TAC
 >> Know ‘vs <<= vs'’
 >- (qunabbrevl_tac [‘vs’, ‘vs'’] \\
     MATCH_MP_TAC RNEWS_prefix >> rw [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> Know ‘TAKE n vs' = vs’
 >- (Q.PAT_X_ASSUM ‘LENGTH vs = n’ (REWRITE_TAC o wrap o SYM) \\
     simp [TAKE_LENGTH_APPEND])
 >> DISCH_THEN (rfs o wrap) >> T_TAC
 >> Q.PAT_X_ASSUM ‘y = y'’       (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘args = args'’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM)
 >> gs [MAP_APPEND, appstar_APPEND, LIST_TO_SET_APPEND, ALL_DISTINCT_APPEND]
 (* applying hreduce_BETA_extended *)
 >> Know ‘M0 @* MAP VAR vs @* MAP VAR l -h->* VAR y @* args @* MAP VAR l’
 >- (Q.PAT_X_ASSUM ‘_ = M0’ (REWRITE_TAC o wrap o SYM) \\
     REWRITE_TAC [hreduce_BETA_extended])
 >> DISCH_TAC
 >> Know ‘M1' = VAR y @* args @* MAP VAR l’
 >- (qunabbrev_tac ‘M1'’ \\
     simp [principle_hnf_thm', GSYM appstar_APPEND, hnf_appstar])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘M0 @* MAP VAR vs @* MAP VAR l -h->* _’ K_TAC
 >> Know ‘p IN ltree_paths (BT' X (EL h Ms) (SUC r))’
 >- (Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BT' X M r)’ MP_TAC \\
     simp [ltree_paths_def] \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X M r’ \\
     simp [GSYM BT_def, LMAP_fromList] \\
     simp [ltree_lookup_def, LNTH_fromList] \\
     Cases_on ‘h < LENGTH args’ >> simp [EL_MAP] \\
     Suff ‘EL h Ms = EL h args’ >- rw [] \\
     simp [Abbr ‘Ms’, GSYM appstar_APPEND] \\
     MATCH_MP_TAC EL_APPEND1 >> art [])
 >> DISCH_TAC
 >> simp []
 >> DISCH_THEN K_TAC
 (* stage work *)
 >> qmatch_abbrev_tac
     ‘MAX_SET (IMAGE (hnf_children_size o principle_hnf) s) <= d <=>
      m <= d /\ MAX_SET (IMAGE (hnf_children_size o principle_hnf) t) <= d’
 >> Know ‘s = M INSERT {subterm' X M q r | q |
                        ?x xs. q = x::xs /\ q <<= FRONT (h::p) /\
                               solvable (subterm' X M q r)}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [Abbr ‘s’] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Cases_on ‘q = []’ >- (DISJ1_TAC >> rw []) \\
       DISJ2_TAC >> Q.EXISTS_TAC ‘q’ >> rw [] \\
       Cases_on ‘q’ >> fs [],
       (* goal 2 (of 3) *)
       Q.EXISTS_TAC ‘[]’ >> rw [],
       (* goal 3 (of 3) *)
       rename1 ‘x::xs <<= FRONT (h::p)’ \\
       Q.EXISTS_TAC ‘x::xs’ >> art [] ])
 >> Rewr'
 >> qunabbrev_tac ‘s’
 >> qmatch_abbrev_tac
     ‘MAX_SET (IMAGE (hnf_children_size o principle_hnf) (M INSERT s)) <= d <=>
      m <= d /\ MAX_SET (IMAGE (hnf_children_size o principle_hnf) t) <= d’
 >> Know ‘s = t’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [Abbr ‘s’, Abbr ‘t’] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Cases_on ‘p’ >> gvs [] \\
       Q.EXISTS_TAC ‘xs’ >> art [] \\
       POP_ASSUM MP_TAC \\
       Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm' X M (h::xs) r’ \\
       Suff ‘EL h Ms = EL h args’ >- rw [] \\
       simp [Abbr ‘Ms’, GSYM appstar_APPEND, Abbr ‘m’] \\
       MATCH_MP_TAC EL_APPEND1 >> art [],
       (* goal 2 (of 2) *)
       fs [hnf_children_size_appstar, Abbr ‘m’] \\
       Q.EXISTS_TAC ‘h::q’ \\
       Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm' X M (h::q) r’ \\
       Know ‘EL h Ms = EL h args’
       >- (simp [Abbr ‘Ms’, GSYM appstar_APPEND] \\
           MATCH_MP_TAC EL_APPEND1 >> art []) \\
       DISCH_THEN (fs o wrap) \\
       Cases_on ‘p’ >> rw [] ])
 >> Rewr'
 >> qunabbrev_tac ‘s’
 >> REWRITE_TAC [IMAGE_INSERT]
 (* stage work *)
 >> qabbrev_tac ‘s = IMAGE (hnf_children_size o principle_hnf) t’
 >> simp [o_DEF]
 >> Suff ‘MAX_SET (m INSERT s) = MAX m (MAX_SET s)’
 >- (Rewr' >> rw [MAX_LE])
 >> Suff ‘FINITE s’ >- PROVE_TAC [MAX_SET_THM]
 >> qunabbrev_tac ‘s’
 >> MATCH_MP_TAC IMAGE_FINITE
 >> MATCH_MP_TAC SUBSET_FINITE_I
 >> Q.EXISTS_TAC ‘{subterm' X (EL h Ms) q (SUC r) | q | q <<= FRONT p}’
 >> reverse CONJ_TAC
 >- (rw [SUBSET_DEF, Abbr ‘t’] \\
     Q.EXISTS_TAC ‘q’ >> art [])
 >> qunabbrev_tac ‘t’
 >> Know ‘{subterm' X (EL h Ms) q (SUC r) | q <<= FRONT p} =
          IMAGE (\e. subterm' X (EL h Ms) e (SUC r)) {q | q <<= FRONT p}’
 >- rw [Once EXTENSION]
 >> Rewr'
 >> MATCH_MP_TAC IMAGE_FINITE
 >> rw [FINITE_prefix]
QED

Theorem subterm_width_induction_lemma' :
    !X M h p r M0 n m vs M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         h::p IN ltree_paths (BT' X M r) /\
         solvable M /\
         M0 = principle_hnf M /\
          n = LAMl_size M0 /\
          m = hnf_children_size M0 /\ h < m /\
         vs = RNEWS r n X /\
         M1 = principle_hnf (M0 @* MAP VAR vs) /\
         Ms = hnf_children M1 ==>
        (subterm_width M (h::p) <= d <=>
         m <= d /\ subterm_width (EL h Ms) p <= d)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC subterm_width_induction_lemma
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

(* NOTE: This is another induction lemma of subterm_width, which is more general
   but does not contain [subterm_width_induction_lemma].

   In this case, vs is NOT a prefix of vs' but actually disjoint with it.
   The proof becomes even harder, because ‘tpm’ is involved additionally.

   NOTE: ‘X’ is the usual excluded set for induction. ‘Y’ is a fixed variable set
   acting as ‘IMAGE FV (set Ms)’ if M is one of Ms.
 *)
Theorem subterm_width_induction_lemma_alt[local] :
    !X Y M h p r M0 n n' m vs' M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\ 0 < r /\
         FINITE Y /\ FV M SUBSET Y /\
         h::p IN ltree_paths (BT' X M r) /\
         M0 = principle_hnf M /\ solvable M /\
          n = LAMl_size M0 /\ n <= n' /\
          m = hnf_children_size M0 /\ h < m /\
        vs' = NEWS n' (X UNION Y) /\
         M1 = principle_hnf (M0 @* MAP VAR vs') /\
         Ms = hnf_children M1 ==>
        (subterm_width M (h::p) <= d <=>
         m <= d /\ subterm_width (EL h Ms) p <= d)
Proof
    RW_TAC std_ss []
 >> Know ‘!q. q <<= FRONT (h::p) ==> subterm X M q r <> NONE’
 >- (MATCH_MP_TAC subterm_valid_path_lemma >> rw [])
 >> DISCH_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> Q_TAC (NEWS_TAC (“vs' :string list”, “n' :num”)) ‘X UNION Y’
 >> Know ‘DISJOINT (set vs') (FV M)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘Y’ >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs') (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘M1' = principle_hnf (M0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ms = hnf_children M1'’
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_width_thm) >> simp []
 >> DISCH_THEN K_TAC (* used already *)
 >> Cases_on ‘p = []’
 >- (fs [] \\
     Know ‘{subterm' X M q r | q | q = [] /\ solvable (subterm' X M q r)} = {M}’
     >- csimp [Once EXTENSION] >> Rewr' \\
     Know ‘IMAGE (hnf_children_size o principle_hnf) {M} =
           {hnf_children_size (principle_hnf M)}’
     >- rw [Once EXTENSION] >> Rewr' \\
     simp [MAX_SET_SING])
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 (* Define vs as prefix of vs' *)
 >> qabbrev_tac ‘vs = TAKE n vs'’
 >> ‘ALL_DISTINCT vs’
       by (qunabbrev_tac ‘vs’ >> MATCH_MP_TAC ALL_DISTINCT_TAKE >> art [])
 >> ‘LENGTH vs = n’
       by (qunabbrev_tac ‘vs’ >> MATCH_MP_TAC LENGTH_TAKE >> art [])
 (* Define zs as substitutions of vs *)
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n :num”)) ‘X’
 >> Know ‘DISJOINT (set zs) (set vs')’
 >- (qunabbrev_tac ‘zs’ \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘RANK r’ >> rw [Once DISJOINT_SYM, DISJOINT_RANK_RNEWS'] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     CONJ_TAC >- rw [Abbr ‘vs'’, RNEWS_SUBSET_ROW] \\
     rw [ROW_SUBSET_RANK])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set zs) (set vs)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘set vs'’ >> art [] \\
     rw [Abbr ‘vs’, LIST_TO_SET_TAKE])
 >> DISCH_TAC
 (* now decompose M0 in two ways (to M1 and M1') *)
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR zs)’
 >> ‘DISJOINT (set zs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “zs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n zs = zs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘?y' args'. M0 = LAMl vs (VAR y' @* args')’
 >- (qunabbrevl_tac [‘n’, ‘vs’] >> irule (iffLR hnf_cases_shared) \\
     Q.PAT_X_ASSUM ‘M0 = _’ K_TAC \\
     simp [])
 >> STRIP_TAC (* this asserts y' and args' *)
 >> Know ‘vs <<= vs'’
 >- (simp [Abbr ‘vs’, IS_PREFIX_EQ_TAKE'] \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> qabbrev_tac ‘t = VAR y' @* args'’
 >> Know ‘principle_hnf (LAMl vs t @* MAP VAR zs) = tpm (ZIP (vs,zs)) t’
 >- (‘hnf t’ by rw [Abbr ‘t’, hnf_appstar] \\
     MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
     CONJ_TAC >- rw [Once DISJOINT_SYM] \\
     MATCH_MP_TAC subterm_disjoint_lemma \\
     qexistsl_tac [‘X’, ‘r’, ‘n’] >> simp [] \\
     Know ‘FV M0 SUBSET X UNION RANK r’
     >- (Suff ‘FV M0 SUBSET FV M’ >- METIS_TAC [SUBSET_DEF] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     Q.PAT_X_ASSUM ‘M0 = LAMl vs t’ (REWRITE_TAC o wrap) \\
     simp [FV_LAMl] \\
     Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs'’ \\
     CONJ_TAC >- simp [LIST_TO_SET_APPEND] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     CONJ_TAC >- rw [Abbr ‘vs'’, RNEWS_SUBSET_ROW] \\
     rw [ROW_SUBSET_RANK])
 >> Q.PAT_ASSUM ‘M0 = LAMl vs t’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M0 = LAMl zs _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = VAR y @* _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M0 = LAMl vs t’ (ASSUME_TAC o SYM)
 >> simp [Abbr ‘t’, tpm_appstar]
 >> qabbrev_tac ‘pi = ZIP (vs,zs)’
 >> qabbrev_tac ‘y'' = lswapstr pi y'’
 >> qabbrev_tac ‘args'' = listpm term_pmact pi args'’
 >> DISCH_THEN (ASSUME_TAC o SYM) (* store M1 *)
 (* applying hreduce_BETA_extended *)
 >> Know ‘M0 @* MAP VAR vs @* MAP VAR l -h->* VAR y' @* args' @* MAP VAR l’
 >- (Q.PAT_X_ASSUM ‘LAMl vs _ = M0’ (REWRITE_TAC o wrap o SYM) \\
     REWRITE_TAC [hreduce_BETA_extended])
 >> DISCH_TAC
 >> Know ‘M1' = VAR y' @* args' @* MAP VAR l’
 >- (qunabbrev_tac ‘M1'’ \\
     MATCH_MP_TAC hreduces_hnf_imp_principle_hnf \\
     simp [appstar_APPEND] \\
     simp [GSYM appstar_APPEND, hnf_appstar])
 >> DISCH_THEN (ASSUME_TAC o SYM) (* store M1' *)
 >> Know ‘Ms = args' ++ MAP VAR l’
 >- (qunabbrev_tac ‘Ms’ \\
     POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     simp [GSYM appstar_APPEND])
 >> DISCH_THEN (ASSUME_TAC o SYM) (* store Ms *)
 >> Know ‘LENGTH args = m’
 >- (qunabbrev_tac ‘m’ \\
     Q.PAT_X_ASSUM ‘LAMl zs (VAR y @* args) = M0’ (REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> DISCH_TAC
 >> Know ‘LENGTH args' = m’
 >- (qunabbrev_tac ‘m’ \\
     Q.PAT_X_ASSUM ‘LAMl vs (VAR y' @* args') = M0’ (REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> DISCH_TAC
 (* applying subterm_width_thm again *)
 >> MP_TAC (Q.SPECL [‘X’, ‘EL h Ms’, ‘p’, ‘SUC r’] subterm_width_thm)
 >> simp []
 >> Know ‘FV (EL h Ms) SUBSET X UNION RANK (SUC r)’
 >- (Q.PAT_X_ASSUM ‘args' ++ MAP VAR l = Ms’ (REWRITE_TAC o wrap o SYM) \\
     Know ‘EL h (args' ++ MAP VAR l) = EL h args'’
     >- (MATCH_MP_TAC EL_APPEND1 >> art []) >> Rewr' \\
     Know ‘FV M0 SUBSET X UNION RANK r’
     >- (Suff ‘FV M0 SUBSET FV M’ >- METIS_TAC [SUBSET_TRANS] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     Q.PAT_X_ASSUM ‘LAMl vs (VAR y' @* args') = M0’ (REWRITE_TAC o wrap o SYM) \\
     simp [FV_LAMl, FV_appstar] \\
     qabbrev_tac ‘s = BIGUNION (IMAGE FV (set args'))’ \\
     qabbrev_tac ‘t = FV (EL h args')’ \\
     Know ‘t SUBSET s’
     >- (rw [Abbr ‘t’, Abbr ‘s’, SUBSET_DEF] \\
         Q.EXISTS_TAC ‘FV (EL h args')’ >> art [] \\
         Q.EXISTS_TAC ‘EL h args'’ >> art [] \\
         rw [EL_MEM]) \\
     Suff ‘set vs SUBSET X UNION RANK r’
     >- (Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs'’ \\
     CONJ_TAC >- simp [LIST_TO_SET_APPEND] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     CONJ_TAC >- rw [Abbr ‘vs'’, RNEWS_SUBSET_ROW] \\
     rw [ROW_SUBSET_RANK])
 >> DISCH_TAC
 >> Know ‘p IN ltree_paths (BT' X (EL h Ms) (SUC r))’
 >- (Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BT' X M r)’ MP_TAC \\
     simp [ltree_paths_def] \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X M r’ \\
     simp [GSYM BT_def, LMAP_fromList] \\
     simp [ltree_lookup_def, LNTH_fromList, EL_MAP] \\
     Know ‘EL h (args' ++ MAP VAR l) = EL h args'’
     >- (MATCH_MP_TAC EL_APPEND1 >> art []) \\
     DISCH_THEN (fs o wrap) >> T_TAC \\
     simp [Abbr ‘args''’, Excl "LENGTH_listpm"] \\
  (* applying BT_ltree_paths_tpm *)
     qabbrev_tac ‘N = EL h args'’ \\
     Suff ‘ltree_lookup (BT' X N (SUC r)) p = NONE <=>
           ltree_lookup (BT' X (tpm pi N) (SUC r)) p = NONE’ >- rw [] \\
     MATCH_MP_TAC (SRULE [EXTENSION, ltree_paths_def] BT_ltree_paths_tpm) \\
     simp [Abbr ‘pi’, MAP_ZIP] \\
     CONJ_TAC
     >- (qabbrev_tac ‘vs' = vs ++ l’ \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs'’ \\
         CONJ_TAC >- simp [Abbr ‘vs'’, LIST_TO_SET_APPEND] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
         CONJ_TAC >- (Q.PAT_X_ASSUM ‘_ = vs'’ (REWRITE_TAC o wrap o SYM) \\
                      MATCH_MP_TAC RNEWS_SUBSET_ROW >> rw []) \\
         rw [ROW_SUBSET_RANK]) \\
     qunabbrev_tac ‘zs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw [])
 >> DISCH_TAC
 >> simp []
 >> DISCH_THEN K_TAC (* already used *)
 (* stage work *)
 >> qmatch_abbrev_tac
     ‘MAX_SET (IMAGE (hnf_children_size o principle_hnf) s) <= d <=>
      m <= d /\ MAX_SET (IMAGE (hnf_children_size o principle_hnf) t) <= d’
 >> Know ‘s = M INSERT {subterm' X M q r | q |
                        ?x xs. q = x::xs /\ q <<= FRONT (h::p) /\
                               solvable (subterm' X M q r)}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [Abbr ‘s’] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Cases_on ‘q = []’ >- (DISJ1_TAC >> rw []) \\
       DISJ2_TAC >> Q.EXISTS_TAC ‘q’ >> rw [] \\
       Cases_on ‘q’ >> fs [],
       (* goal 2 (of 3) *)
       Q.EXISTS_TAC ‘[]’ >> rw [],
       (* goal 3 (of 3) *)
       rename1 ‘x::xs <<= FRONT (h::p)’ \\
       Q.EXISTS_TAC ‘x::xs’ >> art [] ])
 >> Rewr'
 >> qunabbrev_tac ‘s’
 >> qmatch_abbrev_tac
     ‘MAX_SET (IMAGE (hnf_children_size o principle_hnf) (M INSERT s)) <= d <=>
      m <= d /\ MAX_SET (IMAGE (hnf_children_size o principle_hnf) t) <= d’
 >> REWRITE_TAC [IMAGE_INSERT]
 (* shared properties for the next ‘s = t’ subgoal *)
 >> Know ‘set (MAP FST pi) SUBSET RANK (SUC r) /\
          set (MAP SND pi) SUBSET RANK (SUC r)’
 >- (simp [Abbr ‘pi’, MAP_ZIP] \\
     reverse CONJ_TAC
     >- (qunabbrev_tac ‘zs’ \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW r’ \\
         simp [RNEWS_SUBSET_ROW, ROW_SUBSET_RANK]) \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs'’ \\
     CONJ_TAC >- simp [Abbr ‘vs'’] \\
     qunabbrev_tac ‘vs'’ \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     simp [RNEWS_SUBSET_ROW, ROW_SUBSET_RANK])
 >> STRIP_TAC
 >> Know ‘set (MAP FST (REVERSE pi)) SUBSET RANK (SUC r) /\
          set (MAP SND (REVERSE pi)) SUBSET RANK (SUC r)’
 >- (gs [Abbr ‘pi’, MAP_ZIP, REVERSE_ZIP])
 >> STRIP_TAC
 (* NOTE: According to LAMl_ALPHA, it should be clear that args and args' differs
    by a tpm. We cannot prove ‘s = t’, but their (hnf_children_size o principle_hnf)
    are the same, w.r.t. subterm_hnf_children_size_cong .
  *)
 >> Know ‘IMAGE (hnf_children_size o principle_hnf) s =
          IMAGE (hnf_children_size o principle_hnf) t’
 >- (ONCE_REWRITE_TAC [EXTENSION] \\
     Q.X_GEN_TAC ‘z’ >> EQ_TAC \\
     rw [Abbr ‘s’, Abbr ‘t’] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘x::xs <<= FRONT (h::p)’ \\
       Cases_on ‘p’ >> gs [Abbr ‘args''’] \\
       Know ‘EL h (args' ++ MAP VAR l) = EL h args'’
       >- (MATCH_MP_TAC EL_APPEND1 >> art []) \\
       DISCH_THEN (fs o wrap) \\
       POP_ASSUM MP_TAC (* solvable (subterm' X M (h::xs) r) *) \\
       Know ‘subterm X M (h::xs) r <> NONE’ >- rw [] \\
       Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::xs) r’ \\
       qabbrev_tac ‘N = EL h args'’ \\
       NTAC 2 STRIP_TAC \\
       Know ‘subterm X N xs (SUC r) <> NONE /\
             solvable (subterm' X N xs (SUC r))’
       >- (qabbrev_tac ‘N' = tpm pi N’ \\
          ‘N = tpm (REVERSE pi) N'’ by rw [Abbr ‘N'’] >> POP_ORW \\
           Know ‘FV (tpm pi N) SUBSET X UNION RANK (SUC r)’
           >- (MATCH_MP_TAC FV_tpm_lemma \\
               Q.EXISTS_TAC ‘SUC r’ >> simp []) >> DISCH_TAC \\
           Know ‘subterm X N' xs (SUC r) = NONE <=>
                 subterm X (tpm (REVERSE pi) N') xs (SUC r) = NONE’
           >- (MATCH_MP_TAC (cj 1 subterm_tpm_lemma') \\
               simp [Abbr ‘N'’]) >> simp [] \\
           DISCH_TAC \\
           Know ‘?pi'. tpm pi' (subterm' X N' xs (SUC r)) =
                       subterm' X (tpm (REVERSE pi) N') xs (SUC r)’
           >- (irule (cj 2 subterm_tpm_lemma') >> simp [Abbr ‘N'’]) \\
           STRIP_TAC \\
           POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
           simp [solvable_tpm]) >> STRIP_TAC \\
       Q.EXISTS_TAC ‘subterm' X N xs (SUC r)’ \\
       reverse CONJ_TAC >- (Q.EXISTS_TAC ‘xs’ >> art []) \\
    (* applying subterm_tpm_lemma' again *)
       Know ‘?pi'. tpm pi' (subterm' X N xs (SUC r)) =
                   subterm' X (tpm pi N) xs (SUC r)’
       >- (irule (cj 2 subterm_tpm_lemma') >> simp []) \\
       STRIP_TAC >> POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
       simp [principle_hnf_tpm'],
       (* goal 2 (of 2) *)
       Know ‘EL h (args' ++ MAP VAR l) = EL h args'’
       >- (MATCH_MP_TAC EL_APPEND1 >> art []) \\
       DISCH_THEN (fs o wrap) \\
       qabbrev_tac ‘N = EL h args'’ \\
       Q.EXISTS_TAC ‘subterm' X (EL h args) q (SUC r)’ \\
       gs [Abbr ‘args''’] \\
       Know ‘subterm X M (h::q) r <> NONE’
       >- (FIRST_X_ASSUM MATCH_MP_TAC \\
           Cases_on ‘p’ >> rw []) \\
       Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::q) r’ \\
       DISCH_TAC \\
       Know ‘subterm X N q (SUC r) <> NONE’
       >- (Know ‘subterm X N q (SUC r) = NONE <=>
                 subterm X (tpm pi N) q (SUC r) = NONE’
           >- (MATCH_MP_TAC (cj 1 subterm_tpm_lemma') >> simp []) >> simp []) \\
       DISCH_TAC \\
       Know ‘?pi'. tpm pi' (subterm' X N q (SUC r)) =
                   subterm' X (tpm pi N) q (SUC r)’
       >- (irule (cj 2 subterm_tpm_lemma') >> simp []) \\
       STRIP_TAC \\
       POP_ASSUM (ASSUME_TAC o SYM) \\
       simp [principle_hnf_tpm'] \\
       Q.EXISTS_TAC ‘h::q’ \\
       Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm' X M (h::q) r’ \\
       Cases_on ‘p’ >> rw [] ])
 >> Rewr'
 >> qunabbrev_tac ‘s’
 (* stage work *)
 >> qabbrev_tac ‘s = IMAGE (hnf_children_size o principle_hnf) t’
 >> simp [o_DEF]
 >> Suff ‘MAX_SET (m INSERT s) = MAX m (MAX_SET s)’
 >- (Rewr' >> rw [MAX_LE])
 >> Suff ‘FINITE s’ >- PROVE_TAC [MAX_SET_THM]
 >> qunabbrev_tac ‘s’
 >> MATCH_MP_TAC IMAGE_FINITE
 >> MATCH_MP_TAC SUBSET_FINITE_I
 >> Q.EXISTS_TAC ‘{subterm' X (EL h Ms) q (SUC r) | q | q <<= FRONT p}’
 >> reverse CONJ_TAC
 >- (rw [SUBSET_DEF, Abbr ‘t’] \\
     Q.EXISTS_TAC ‘q’ >> art [])
 >> qunabbrev_tac ‘t’
 >> Know ‘{subterm' X (EL h Ms) q (SUC r) | q <<= FRONT p} =
          IMAGE (\e. subterm' X (EL h Ms) e (SUC r)) {q | q <<= FRONT p}’
 >- rw [Once EXTENSION]
 >> Rewr'
 >> MATCH_MP_TAC IMAGE_FINITE
 >> rw [FINITE_prefix]
QED

(* NOTE: v, P and d are fixed free variables here *)
Theorem subterm_subst_cong_lemma[local] :
    !X. FINITE X ==>
        !q M p r. q <<= p /\
                  FV M SUBSET X UNION RANK r /\
                  subterm X M p r <> NONE /\
                  subterm_width M p <= d /\
                  P = permutator d /\ v IN X UNION RANK r
              ==> subterm X ([P/v] M) q r <> NONE /\
                  subterm_width ([P/v] M) q <= d /\
                  subterm' X ([P/v] M) q r = [P/v] (subterm' X M q r)
Proof
    NTAC 2 STRIP_TAC
 >> Induct_on ‘q’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [subterm_imp_ltree_paths]
 (* re-define P as abbreviations *)
 >> Q.PAT_X_ASSUM ‘P = permutator d’ (FULL_SIMP_TAC std_ss o wrap)
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘Y = X UNION RANK r’
 >> Cases_on ‘p = []’ >- fs []
 (* common properties of ‘p’ (this requires ‘p <> []’) *)
 >> ‘(!q. q <<= p ==> subterm X M q r <> NONE) /\
     (!q. q <<= FRONT p ==> solvable (subterm' X M q r))’
       by PROVE_TAC [subterm_solvable_lemma]
 >> qabbrev_tac ‘w = subterm_width M p’
 (* decompose ‘p’ and eliminate ‘p <> []’ *)
 >> Cases_on ‘p’ >> fs []
 (* cleanup assumptions *)
 >> Q.PAT_X_ASSUM ‘h = h'’ (fs o wrap o SYM)
 >> T_TAC
 (* preparing for eliminating ‘subterm' X M (h::q)’ *)
 >> Know ‘solvable M’
 >- (Q.PAT_X_ASSUM ‘!q. q <<= FRONT (h::t) ==> solvable _’
       (MP_TAC o (Q.SPEC ‘[]’)) >> rw [])
 >> DISCH_TAC
 >> Know ‘subterm X M (h::q) r <> NONE’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 >> UNBETA_TAC [subterm_of_solvables] “subterm X M (h::q) r”
 >> STRIP_TAC
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M0)’ K_TAC
 >> ‘Ms = args’ by rw [Abbr ‘Ms’, hnf_children_hnf]
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘Ms’
 >> ‘LENGTH args = m’ by rw [Abbr ‘m’]
 >> Know ‘m <= w’
 >- (MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘r’] subterm_width_first) \\
     rw [Abbr ‘w’])
 >> DISCH_TAC
 (* KEY: some shared subgoals needed at the end, before rewriting ‘[P/v] M’:

    2. subterm X (EL h args) t (SUC r) <> NONE
    3. subterm_width (EL h args) t <= d

    NOTE: the last subgoal requires deep properties of ‘subterm_width’. The
    involved tactics are not to be repeated in other parts of this lemma.
  *)
 >> Know ‘subterm X (EL h args) t (SUC r) <> NONE /\
          subterm_width (EL h args) t <= d’
 >- (CONJ_ASM1_TAC (* subterm X (EL h args) t (SUC r) <> NONE *)
     >- (Q.PAT_X_ASSUM ‘!q. q <<= h::t ==> subterm X M q r <> NONE’
           (MP_TAC o (Q.SPEC ‘h::t’)) \\
         simp [subterm_of_solvables] >> fs []) \\
  (* goal: subterm_width (EL h args) t <= d *)
     Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘w’ >> art [] \\
     qunabbrev_tac ‘w’ \\
  (* applying subterm_width_thm *)
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘r’] subterm_width_thm) \\
     simp [] >> DISCH_THEN K_TAC \\
     Cases_on ‘t = []’ >- rw [] \\
  (* applying subterm_width_thm again *)
     MP_TAC (Q.SPECL [‘X’, ‘EL h args’, ‘t’, ‘SUC r’] subterm_width_thm) \\
     Know ‘FV (EL h args) SUBSET X UNION RANK (SUC r)’
     >- (MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []) \\
     DISCH_TAC \\
    ‘t IN ltree_paths (BT' X (EL h args) (SUC r))’
        by PROVE_TAC [subterm_imp_ltree_paths] \\
     simp [] >> DISCH_THEN K_TAC (* already used *) \\
  (* applying SUBSET_MAX_SET *)
     MATCH_MP_TAC SUBSET_MAX_SET \\
     CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE \\
                  MATCH_MP_TAC SUBSET_FINITE_I \\
                  Q.EXISTS_TAC ‘{subterm' X (EL h args) q (SUC r) | q <<= FRONT t}’ \\
                  reverse CONJ_TAC
                  >- (rw [SUBSET_DEF] >> Q.EXISTS_TAC ‘q'’ >> art []) \\
                 ‘{subterm' X (EL h args) q (SUC r) | q <<= FRONT t} =
                   IMAGE (\p. subterm' X (EL h args) p (SUC r)) {q | q <<= FRONT t}’
                     by rw [Once EXTENSION] >> POP_ORW \\
                  MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix]) \\
     CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE \\
                  MATCH_MP_TAC SUBSET_FINITE_I \\
                  Q.EXISTS_TAC ‘{subterm' X M q r | q <<= FRONT (h::t)}’ \\
                  reverse CONJ_TAC
                  >- (rw [SUBSET_DEF] >> Q.EXISTS_TAC ‘q'’ >> art []) \\
                 ‘{subterm' X M q r | q <<= FRONT (h::t)} =
                   IMAGE (\p. subterm' X M p r) {q | q <<= FRONT (h::t)}’
                     by rw [Once EXTENSION] >> POP_ORW \\
                  MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix]) \\
     rw [SUBSET_DEF] (* this asserts ‘p <<= FRONT t *) \\
     rename1 ‘p <<= FRONT t’ \\
     Q.EXISTS_TAC ‘subterm' X (EL h args) p (SUC r)’ >> art [] \\
     Q.EXISTS_TAC ‘h::p’ \\
    ‘FRONT (h::t) <> []’ by rw [] \\
     Know ‘h::p <<= FRONT (h::t)’
     >- (simp [] >> Cases_on ‘t’ >> fs []) >> Rewr \\
     UNBETA_TAC [subterm_of_solvables] “subterm X M (h::p) r” \\
     simp [hnf_children_hnf])
 >> STRIP_TAC
 >> Know ‘~MEM v vs’
 >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     rw [Abbr ‘Y’, IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art [])
 >> DISCH_TAC
 (* NOTE: ‘[P/v] M’ is solvable iff ‘[P/v] M0’ is solvable, the latter is either
    already a hnf (v <> y), or can be head-reduced to a hnf (v = y).
  *)
 >> Know ‘solvable ([P/v] M)’
 >- (MATCH_MP_TAC solvable_subst \\
     qexistsl_tac [‘X’, ‘M0’, ‘r’, ‘d’] >> simp [])
 >> DISCH_TAC
 (* Now we need to know the exact form of ‘principle_hnf ([P/v] M)’.

    We know that ‘principle_hnf M = M0 = LAMl vs (VAR y @* args)’, which means
    that ‘M -h->* LAMl vs (VAR y @* args)’. Meanwhile, as -h->* is substitutive,
    thus ‘[P/v] M -h->* [P/v] LAMl vs (VAR y @* args)’. Depending on the nature
    of ‘v’, the ending term ‘[P/v] LAMl vs (VAR y @* args)’ may or may not be
    a hnf. But it has indeed a hnf, since ‘solvable ([P/v] M)’ has been proved.

    Case 1 (MEM v vs): Case unprovable (but is eliminated by adding ‘v IN X’)
    Case 2 (v <> y):   [P/v] LAMl vs (VAR y @* args) = LAMl vs (VAR y @* args')
    Case 3 (v = y):    [P/v] LAMl vs (VAR y @* args) = LAMl vs (P @* args'),
        where LAMl vs (P @* args') -h->*
              LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs))) =
              LAMl (vs ++ xs ++ [z]) (VAR z @* args' @* MAP VAR xs), a hnf

    Only Case 3 needs further head-reductions, but the final hnf is already clear
    when proving ‘solvable ([P/v] M)’. Easy.

    In all these cases, ‘h < hnf_children_size (principle_hnf ([P/v] M))’ holds:
    In Case 1 & 2, ‘hnf_children_size (principle_hnf ([P/v] M)) = LENGTH args’.
    In Case 3, ‘hnf_children_size (principle_hnf ([P/v] M)) >= LENGTH args’.
  *)
 >> ‘M -h->* M0’ by METIS_TAC [principle_hnf_thm']
 (* NOTE: we will need to further do head reductions on ‘[P/v] M0’ *)
 >> Know ‘[P/v] M -h->* [P/v] M0’ >- PROVE_TAC [hreduce_substitutive]
 >> ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT', FV_permutator, Abbr ‘P’]
 >> simp [LAMl_SUB, appstar_SUB]
 >> POP_ASSUM K_TAC (* DISJOINT (set vs) (FV P) *)
 >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> ‘LENGTH args' = LENGTH args’ by rw [Abbr ‘args'’]
 (* LHS rewriting of args', this will introduce M0' = principle_hnf ([P/v] M)
    and a new set of abbreviations (vs', n', ...).
  *)
 >> CONV_TAC (UNBETA_CONV “subterm X ([P/v] M) (h::q) r”)
 >> qmatch_abbrev_tac ‘f _’
 >> ASM_SIMP_TAC std_ss [subterm_of_solvables]
 >> BasicProvers.LET_ELIM_TAC
 >> Q.PAT_X_ASSUM ‘subterm X (EL h args) q (SUC r) <> NONE’ MP_TAC
 >> simp [Abbr ‘f’, hnf_children_hnf]
 >> DISCH_TAC (* subterm X (EL h args) q (SUC r) <> NONE *)
 >> Q.PAT_X_ASSUM ‘m = m’ K_TAC
 (* Case 2 (easy: vs = vs' /\ m = m') *)
 >> reverse (Cases_on ‘y = v’)
 >- (simp [LAMl_SUB, appstar_SUB] \\
     DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
    ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
    ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT'] \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘M0' = LAMl vs (VAR y @* args')’ by METIS_TAC [principle_hnf_thm'] \\
    ‘n = n'’ by rw [Abbr ‘n'’] \\
     POP_ASSUM (rfs o wrap o SYM) >> T_TAC \\
     qunabbrev_tac ‘n'’ \\
     Q.PAT_X_ASSUM ‘vs = vs'’ (rfs o wrap o SYM) \\
    ‘hnf (LAMl vs (VAR y @* args))’ by rw [hnf_appstar] \\
     fs [Abbr ‘M1'’, principle_hnf_beta_reduce] \\
     Q.PAT_X_ASSUM ‘args' = Ms’ (fs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘m' = m’ (fs o wrap o SYM) \\
     fs [Abbr ‘m'’] >> T_TAC \\
  (* applying subterm_width_induction_lemma' *)
     Know ‘subterm_width ([P/v] M) (h::q) <= d <=>
           m <= d /\ subterm_width (EL h args') q <= d’
     >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
         qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n’, ‘vs’, ‘VAR y @* args'’] \\
         simp [principle_hnf_beta_reduce] \\
         CONJ_TAC
         >- (rw [FV_SUB] \\
             MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
             SET_TAC []) \\
         fs [Abbr ‘m’, Abbr ‘args'’] \\
      (* remaining goal: h::q IN ltree_paths (BT' X ([P/v] M) r) *)
         MATCH_MP_TAC subterm_imp_ltree_paths >> art [] \\
         CONJ_TAC
         >- (rw [FV_SUB] \\
             MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
             SET_TAC []) \\
         Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X ([P/v] M) (h::q) r’ \\
         simp [principle_hnf_beta_reduce, EL_MAP] \\
         qabbrev_tac ‘N = EL h args’ \\
         Q.PAT_X_ASSUM ‘!M p r. _’ (MP_TAC o Q.SPECL [‘N’, ‘t’, ‘SUC r’]) \\
         simp [] \\
         Know ‘v IN X UNION RANK (SUC r)’
         >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
             Suff ‘Y SUBSET X UNION RANK (SUC r)’ >- rw [SUBSET_DEF] \\
             qunabbrev_tac ‘Y’ \\
             Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
             rw [RANK_MONO]) >> Rewr \\
         Suff ‘FV N SUBSET X UNION RANK (SUC r)’ >- rw [] \\
         qunabbrev_tac ‘N’ \\
         MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘principle_hnf M’, ‘LENGTH vs’, ‘LENGTH args’,
                       ‘vs’, ‘M1’] \\
         simp [LAMl_size_hnf, Abbr ‘M1’, principle_hnf_beta_reduce]) >> Rewr' \\
  (* now applying IH *)
     fs [Abbr ‘m’, Abbr ‘args'’, EL_MAP] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘t’ >> simp [] \\
  (* extra goals *)
     reverse CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
         qunabbrev_tac ‘Y’ >> simp [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     qunabbrev_tac ‘Y’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘LENGTH args’, ‘vs’, ‘M1’] \\
     simp [principle_hnf_beta_reduce, LAMl_size_hnf, Abbr ‘M1’])
 (* Case 3 (hard, vs <<= vs' *)
 >> Q.PAT_X_ASSUM ‘y = v’ (fs o wrap o SYM)
 >> simp [Abbr ‘P’]
 >> DISCH_TAC (* [permutator d/y] M -h->* ... *)
 (* applying permutator_hreduce_thm with a suitable excluded list

    NOTE: ‘vs'’ is to be proved extending vs (vs' = vs ++ ys), and we will need
          DISJOINT (set (SNOC z xs)) (set ys), thus here ‘set vs'’ is used.
  *)
 >> MP_TAC (Q.SPECL [‘set vs'’, ‘d’, ‘args'’] permutator_hreduce_thm)
 >> simp []
 >> STRIP_TAC (* this asserts new fresh lists to be renamed: ‘xs’ and ‘z’ *)
 >> rename1 ‘ALL_DISTINCT (SNOC z xs)’
 (* calculating head reductions of ‘[permutator d/y] M’ *)
 >> Know ‘[permutator d/y] M -h->*
          LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)))’
 >- (MATCH_MP_TAC hreduce_TRANS \\
     Q.EXISTS_TAC ‘LAMl vs (permutator d @* args')’ >> rw [])
 >> DISCH_TAC
 >> ‘hnf (LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs))))’
       by rw [hnf_LAMl, hnf_appstar]
 >> ‘M0' = LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)))’
       by METIS_TAC [principle_hnf_thm']
 >> Q.PAT_X_ASSUM ‘permutator d @* args' -h->* _’      K_TAC
 >> Q.PAT_X_ASSUM ‘[permutator d/y] M -h->* LAMl vs (permutator d @* args')’ K_TAC
 >> Know ‘LENGTH Ms = hnf_children_size M0'’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qabbrev_tac ‘P = permutator d’ \\
     qabbrev_tac ‘M' = [P/y] M’ \\
     qexistsl_tac [‘X’, ‘M'’, ‘r’, ‘n'’, ‘vs'’, ‘M1'’] >> simp [] \\
     qunabbrevl_tac [‘M'’, ‘Y’] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     MATCH_MP_TAC FV_SUB_SUBSET \\
     rw [Abbr ‘P’, closed_permutator])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 (* NOTE: this proof includes ‘m <= m'’ *)
 >> Know ‘h < m'’
 >- (MATCH_MP_TAC LESS_LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘m’ >> art [] \\
  (* below is the proof of ‘m <= m'’ *)
     qunabbrevl_tac [‘m’, ‘m'’] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [GSYM appstar_APPEND])
 >> Rewr
 >> Q.PAT_X_ASSUM ‘M0 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M0' = LAMl vs _’ (ASSUME_TAC o SYM)
 (* stage work *)
 >> Know ‘n' = n + LENGTH xs + 1’
 >- (qunabbrevl_tac [‘n’, ‘n'’] \\
     Q.PAT_X_ASSUM ‘_ = M0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M0'’ (REWRITE_TAC o wrap o SYM) \\
    ‘!t. LAMl vs (LAMl xs (LAM z t)) = LAMl (vs ++ xs ++ [z]) t’
        by rw [LAMl_APPEND] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘_ = M1’  (REWRITE_TAC o wrap o SYM) \\
     simp [LAMl_size_LAMl])
 >> DISCH_TAC
 >> qunabbrev_tac ‘vs'’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’
 (* applying NEWS_prefix !!! *)
 >> Know ‘vs <<= vs'’
 >- (qunabbrevl_tac [‘vs’, ‘vs'’] \\
     MATCH_MP_TAC RNEWS_prefix >> rw [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> rename1 ‘vs' = vs ++ ys’ (* l -> ys *)
 (* stage work *)
 >> gs [MAP_APPEND, appstar_APPEND, LIST_TO_SET_APPEND, ALL_DISTINCT_APPEND]
 (* applying hreduce_BETA_extended *)
 >> Know ‘M0' @* MAP VAR vs @* MAP VAR ys -h->*
          LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)) @* MAP VAR ys’
 >- (Q.PAT_X_ASSUM ‘_ = M0'’ (REWRITE_TAC o wrap o SYM) \\
     REWRITE_TAC [hreduce_BETA_extended])
 >> REWRITE_TAC [GSYM LAMl_SNOC]
 >> DISCH_TAC
 (* applying hreduce_LAMl_appstar *)
 >> qabbrev_tac ‘xs' = SNOC z xs’
 >> qabbrev_tac ‘t' = VAR z @* args' @* MAP VAR xs’
 >> Know ‘LAMl xs' t' @* MAP VAR ys -h->* fromPairs xs' (MAP VAR ys) ' t'’
 >- (MATCH_MP_TAC hreduce_LAMl_appstar >> simp [Abbr ‘xs'’] \\
     rw [EVERY_MEM, MEM_MAP] >> REWRITE_TAC [FV_thm] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set ys’ >> art [] \\
     rw [SUBSET_DEF])
 >> ‘FDOM (fromPairs xs' (MAP VAR ys)) = set xs'’
       by rw [FDOM_fromPairs, Abbr ‘xs'’]
 >> ASM_SIMP_TAC std_ss [Abbr ‘t'’, ssub_appstar, Abbr ‘xs'’]
 >> qabbrev_tac ‘fm = fromPairs (SNOC z xs) (MAP VAR ys)’
 >> Know ‘MAP ($' fm) args' = args'’
 >- (simp [LIST_EQ_REWRITE, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC ssub_14b' >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> simp [MEM_EL] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> Rewr'
 >> Know ‘?z'. fm ' (VAR z) = VAR z'’
 >- (simp [Abbr ‘fm’] \\
     qabbrev_tac ‘ls = SNOC z xs’ \\
     Know ‘z = LAST ls’ >- rw [Abbr ‘ls’, LAST_SNOC] \\
    ‘ls <> []’ by rw [Abbr ‘ls’] \\
     simp [LAST_EL] >> DISCH_THEN K_TAC \\
     qabbrev_tac ‘i = PRE (LENGTH ls)’ \\
     Q.EXISTS_TAC ‘EL i ys’ \\
    ‘i < LENGTH ys’ by rw [Abbr ‘i’, Abbr ‘ls’] \\
    ‘VAR (EL i ys) :term = EL i (MAP VAR ys)’ by rw [EL_MAP] >> POP_ORW \\
     MATCH_MP_TAC fromPairs_FAPPLY_EL \\
     simp [Abbr ‘i’, Abbr ‘ls’])
 >> STRIP_TAC >> POP_ORW
 >> qabbrev_tac ‘ls = MAP ($' fm) (MAP VAR xs)’ (* irrelevant list *)
 >> DISCH_TAC
 >> Know ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* VAR z' @* (args' ++ ls)’
 >- (REWRITE_TAC [appstar_APPEND] \\
     PROVE_TAC [hreduce_TRANS])
 >> Q.PAT_X_ASSUM ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* _’ K_TAC
 >> Q.PAT_X_ASSUM ‘_ -h->* VAR z' @* args' @* ls’           K_TAC
 >> DISCH_TAC
 >> ‘hnf (VAR z' @* (args' ++ ls))’ by rw [hnf_appstar]
 >> ‘has_hnf (M0' @* MAP VAR vs @* MAP VAR ys)’ by PROVE_TAC [has_hnf_thm]
 (* finall we got the explicit form of M1' *)
 >> ‘M1' = VAR z' @* (args' ++ ls)’ by METIS_TAC [principle_hnf_thm]
 >> Q.PAT_X_ASSUM ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* _’ K_TAC
 >> qabbrev_tac ‘P = permutator d’
 (* applying subterm_width_induction_lemma again *)
 >> Know ‘subterm_width ([P/y] M) (h::q) <= d <=>
          m' <= d /\ subterm_width (EL h Ms) q <= d’
 >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n'’, ‘vs'’, ‘M1'’] \\
     simp [appstar_APPEND] \\
     CONJ_ASM1_TAC
     >- (rw [FV_SUB] >- rw [Abbr ‘P’, FV_permutator] \\
         MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
         SET_TAC []) \\
     reverse CONJ_TAC (* h < m' *)
     >- (MATCH_MP_TAC LESS_LESS_EQ_TRANS \\
         Q.EXISTS_TAC ‘m’ >> art [] \\
         simp [Abbr ‘m'’, Abbr ‘Ms’, hnf_children_hnf]) \\
     MATCH_MP_TAC subterm_imp_ltree_paths >> simp [] \\
     simp [subterm_of_solvables, appstar_APPEND] \\
     simp [GSYM appstar_APPEND, hnf_children_hnf] \\
     Know ‘EL h (args' ++ ls) = EL h args'’
     >- (MATCH_MP_TAC EL_APPEND1 >> rw [Abbr ‘args'’]) >> Rewr' \\
     ASM_SIMP_TAC list_ss [Abbr ‘args'’, EL_MAP] \\
     Q.PAT_X_ASSUM ‘!M p r. _’ (MP_TAC o Q.SPECL [‘EL h args’, ‘t’, ‘SUC r’]) \\
     simp [] \\
     Know ‘y IN X UNION RANK (SUC r)’
     >- (Q.PAT_X_ASSUM ‘y IN Y’ MP_TAC \\
         Suff ‘Y SUBSET X UNION RANK (SUC r)’ >- rw [SUBSET_DEF] \\
         qunabbrev_tac ‘Y’ \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) >> Rewr \\
     Suff ‘FV (EL h args) SUBSET X UNION RANK (SUC r)’ >- rw [] \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] \\
     simp [LAMl_size_hnf, principle_hnf_beta_reduce] \\
     Q.PAT_X_ASSUM ‘LAMl vs M1 = M0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘VAR y @* args = M1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [hnf_children_appstar])
 >> Rewr'
 >> Know ‘EL h Ms = EL h args'’
 >- (simp [Abbr ‘Ms’, hnf_children_hnf] \\
     MATCH_MP_TAC EL_APPEND1 >> art [])
 >> Rewr'
 >> Know ‘m' <= d’
 >- (Q.PAT_X_ASSUM ‘hnf_children_size M0' = m'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M0'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [hnf_children_size_appstar, GSYM appstar_APPEND])
 >> Rewr
 >> Q.PAT_X_ASSUM ‘LENGTH args' = m’ K_TAC
 >> simp [Abbr ‘args'’, EL_MAP]
 >> qabbrev_tac ‘N = EL h args’
 (* applying IH, finally *)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘q’ >> simp []
 >> CONJ_TAC
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     Q.PAT_X_ASSUM ‘LAMl vs M1 = M0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘VAR y @* args = M1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> reverse CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘y IN Y’ MP_TAC \\
     rw [Abbr ‘Y’, IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     DISJ2_TAC \\
     POP_ASSUM MP_TAC \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- rw [SUBSET_DEF] \\
     simp [RANK_MONO])
 (* final goal: subterm_width N q <= d *)
 >> Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘w’ >> art []
 >> qunabbrevl_tac [‘N’, ‘w’]
 (* applying subterm_width_thm *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘r’] subterm_width_thm)
 >> simp []
 >> DISCH_THEN K_TAC
 (* if t = [], then l = [] *)
 >> Cases_on ‘t = []’ >- fs []
 >> Cases_on ‘q = []’ >- rw []
 (* applying subterm_width_thm again *)
 >> MP_TAC (Q.SPECL [‘X’, ‘EL h args’, ‘q’, ‘SUC r’] subterm_width_thm)
 >> Know ‘FV (EL h args) SUBSET X UNION RANK (SUC r)’
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     Q.PAT_X_ASSUM ‘LAMl vs M1 = M0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘VAR y @* args = M1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> DISCH_TAC
 >> ‘q IN ltree_paths (BT' X (EL h args) (SUC r))’
      by PROVE_TAC [subterm_imp_ltree_paths]
 >> simp [] >> DISCH_THEN K_TAC
 (* applying SUBSET_MAX_SET *)
 >> MATCH_MP_TAC SUBSET_MAX_SET
 >> CONJ_TAC (* FINITE #1 *)
 >- (MATCH_MP_TAC IMAGE_FINITE \\
     MATCH_MP_TAC SUBSET_FINITE_I \\
     Q.EXISTS_TAC ‘{subterm' X (EL h args) q' (SUC r) | q' <<= FRONT q}’ \\
     reverse CONJ_TAC
     >- (rw [SUBSET_DEF] >> Q.EXISTS_TAC ‘q'’ >> art []) \\
    ‘{subterm' X (EL h args) p (SUC r) | p <<= FRONT q} =
       IMAGE (\p. subterm' X (EL h args) p (SUC r)) {p | p <<= FRONT q}’
       by rw [Once EXTENSION] >> POP_ORW \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> CONJ_TAC (* FINITE #2 *)
 >- (MATCH_MP_TAC IMAGE_FINITE \\
     MATCH_MP_TAC SUBSET_FINITE_I \\
     Q.EXISTS_TAC ‘{subterm' X M q r | q <<= FRONT (h::t)}’ \\
     reverse CONJ_TAC
     >- (rw [SUBSET_DEF] >> Q.EXISTS_TAC ‘q'’ >> art []) \\
    ‘{subterm' X M q r | q <<= FRONT (h::t)} =
       IMAGE (\p. subterm' X M p r) {p | p <<= FRONT (h::t)}’
       by rw [Once EXTENSION] >> POP_ORW \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> rw [SUBSET_DEF] (* this asserts ‘q' <<= FRONT q’ *)
 >> rename1 ‘q1 <<= FRONT q’
 >> Q.EXISTS_TAC ‘subterm' X (EL h args) q1 (SUC r)’ >> art []
 >> Q.EXISTS_TAC ‘h::q1’
 >> ‘FRONT (h::t) <> []’ by rw []
 >> Know ‘h::q1 <<= FRONT (h::t)’
 >- (simp [] >> Cases_on ‘t’ >> fs [] \\
     MATCH_MP_TAC IS_PREFIX_TRANS \\
     Q.EXISTS_TAC ‘FRONT q’ >> rw [] \\
     MATCH_MP_TAC IS_PREFIX_FRONT_MONO >> rw [])
 >> Rewr
 >> UNBETA_TAC [subterm_of_solvables] “subterm X M (h::q1) r”
QED

(* This theorem can be repeatedly applied for ‘M ISUB ss’ *)
Theorem subterm_subst_cong :
    !p X M r y P d. FINITE X /\ FV M SUBSET X UNION RANK r /\
                    subterm X M p r <> NONE /\
                    P = permutator d /\ y IN X UNION RANK r /\
                    subterm_width M p <= d
                ==> subterm X ([P/y] M) p r <> NONE /\
                    subterm_width ([P/y] M) p <= d /\
                    subterm' X ([P/y] M) p r = [P/y] (subterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> irule subterm_subst_cong_lemma >> art []
 >> Q.EXISTS_TAC ‘p’ >> rw []
QED

(* NOTE: This reduced version is suitable for MATCH_MP_TAC later. *)
Theorem subterm_subst_cong'[local] :
    !p X M r y P d. FINITE X /\ FV M SUBSET X UNION RANK r /\
                    subterm X M p r <> NONE /\
                    P = permutator d /\ y IN X UNION RANK r /\
                    subterm_width M p <= d
                ==> subterm X ([P/y] M) p r <> NONE /\
                    subterm' X ([P/y] M) p r = [P/y] (subterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M’, ‘r’, ‘y’, ‘P’, ‘d’] subterm_subst_cong)
 >> rw []
QED

Theorem subterm_isub_cong :
    !ys p X M r P d ss.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
        subterm X M p r <> NONE /\
        P = permutator d /\
        subterm_width M p <= d /\
        (!y. MEM y ys ==> y IN X UNION RANK r) /\
        ss = MAP (\y. (P,y)) ys
    ==> subterm X (M ISUB ss) p r <> NONE /\
        subterm_width (M ISUB ss) p <= d /\
        subterm' X (M ISUB ss) p r = (subterm' X M p r) ISUB ss
Proof
    Induct_on ‘ys’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> POP_ORW
 >> simp []
 >> Q.PAT_X_ASSUM ‘P = permutator d’ K_TAC
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘N = [P/h] M’
 >> qabbrev_tac ‘ss = MAP (\y. (P,y)) ys’
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M’, ‘r’, ‘h’, ‘P’, ‘d’] subterm_subst_cong)
 >> simp []
 >> STRIP_TAC
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘P’ >> simp []
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV M’ >> art []
 >> rw [FV_SUB, Abbr ‘N’]
 >> rw [Abbr ‘P’, FV_permutator]
QED

Theorem subterm_isub_cong'[local] :
    !ys p X M r P d ss.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
        subterm X M p r <> NONE /\
        P = permutator d /\
        subterm_width M p <= d /\
        (!y. MEM y ys ==> y IN X UNION RANK r) /\
        ss = MAP (\y. (P,y)) ys
    ==> subterm X (M ISUB ss) p r <> NONE /\
        subterm' X (M ISUB ss) p r = (subterm' X M p r) ISUB ss
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘ys’, ‘p’, ‘X’, ‘M’, ‘r’, ‘P’, ‘d’, ‘ss’] subterm_isub_cong)
 >> rw []
QED

(* Lemma 10.3.6 (ii) [1, p.247]:

   NOTE: The construction of ‘pi’ needs a fixed ltree path ‘p’, so that we can
   collect the maximum number of children in all nodes along ‘p’.  In another
   word, there exists no universal ‘pi’ for which the conclusion holds for
   arbitrary ‘p’.

   NOTE: Added ‘subterm X M p <> NONE’ to antecedents so that ‘subterm' X M p’
   is defined/specified. ‘subterm X (apply pi M) p <> NONE’ can be derived.

   NOTE: ‘p <> []’ must be added into antecedents, otherwise the statement
   becomes:

   [...] |- !X M. ?pi. Boehm_transform pi /\ is_ready (apply pi M) /\
                       ?fm. apply pi M == fm ' M

   which is impossible if M is not already "is_ready".

   NOTE: Added ‘p IN ltree_paths (BT X (apply pi M))’ into conclusions for the
   needs in the user theorem.

   NOTE: Extended the conclusion with ‘!q. q <<= p /\ q <> []’

   NOTE: ‘FV (apply pi M) SUBSET X UNION RANK (SUC r)’ is added into the
   conclusions for the needs of Boehm_out_lemma.
 *)
Theorem Boehm_transform_exists_lemma :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p <> [] /\ subterm X M p r <> NONE ==>
       ?pi. Boehm_transform pi /\ is_ready' (apply pi M) /\
            FV (apply pi M) SUBSET X UNION RANK (SUC r) /\
            ?v P. closed P /\
              !q. q <<= p /\ q <> [] ==>
                  subterm X (apply pi M) q r <> NONE /\
                  subterm' X (apply pi M) q r = [P/v] (subterm' X M q r)
Proof
    rpt STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [subterm_imp_ltree_paths]
 >> ‘(!q. q <<= p ==> subterm X M q r <> NONE) /\
      !q. q <<= FRONT p ==> solvable (subterm' X M q r)’
       by (MATCH_MP_TAC subterm_solvable_lemma >> art [])
 >> Know ‘solvable M’
 >- (POP_ASSUM (MP_TAC o Q.SPEC ‘[]’) >> rw [])
 >> DISCH_TAC
 (* M0 is now meaningful since M is solvable *)
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 (* NOTE: here the excluded list must contain ‘FV M’. Just ‘FV M0’ doesn't
          work later, when calling the important [principle_hnf_denude_thm].
          This is conflicting with BT_generator_def and subterm_def.
  *)
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (qunabbrev_tac ‘n’ \\
    ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
     irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> STRIP_TAC
 (* eliminate ‘TAKE n vs’ *)
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Know ‘M1 = VAR y @* args’
 >- (qunabbrev_tac ‘M1’ >> POP_ORW \\
     MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH args’
 (* using ‘subterm_width’ and applying subterm_width_thm *)
 >> qabbrev_tac ‘d = subterm_width M p’
 >> Know ‘m <= d’
 >- (MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_first) \\
     rw [Abbr ‘d’])
 >> DISCH_TAC
 (* p1 is the first Boehm transformation for removing abstractions of M0 *)
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE (MAP VAR vs))’
 >> ‘Boehm_transform p1’ by rw [Abbr ‘p1’, MAP_MAP_o, GSYM MAP_REVERSE]
 >> ‘apply p1 M0 == M1’  by rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt']
 (* stage work (all correct until here)

    Now we define the permutator P (and then p2). This requires q + 1 fresh
    variables. The excluded list is at least X and FV M, and then ‘vs’.
    But since P is a closed term, these fresh variables seem irrelevant...
  *)
 >> qabbrev_tac ‘P = permutator d’
 >> ‘closed P’ by rw [Abbr ‘P’, closed_permutator]
 >> qabbrev_tac ‘p2 = [[P/y]]’
 >> ‘Boehm_transform p2’ by rw [Abbr ‘p2’]
 >> ‘apply p2 M1 = P @* MAP [P/y] args’ by rw [Abbr ‘p2’, appstar_SUB]
 >> qabbrev_tac ‘args' = MAP [P/y] args’
 >> Know ‘!i. i < m ==> FV (EL i args') SUBSET FV (EL i args)’
 >- (rw [Abbr ‘args'’, EL_MAP, FV_SUB] \\
     fs [closed_def])
 >> DISCH_TAC
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’, Abbr ‘m’]
 (* NOTE: Z contains ‘vs’ in addition to X and FV M *)
 >> qabbrev_tac ‘Z = X UNION FV M UNION set vs’
 >> ‘FINITE Z’ by (rw [Abbr ‘Z’] >> rw [])
 >> Know ‘solvable (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC solvable_appstar' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> Know ‘FV M1 SUBSET Z’
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV M0 UNION set vs’ \\
     reverse CONJ_TAC
     >- (qunabbrev_tac ‘Z’ \\
         Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     ‘FV M0 UNION set vs = FV (M0 @* MAP VAR vs)’ by rw [FV_appstar_MAP_VAR] \\
      POP_ORW \\
      qunabbrev_tac ‘M1’ \\
      MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘z = SUC (string_width Z)’
 >> qabbrev_tac ‘l = alloc r z (z + d - m + 1)’
 >> Know ‘ALL_DISTINCT l /\ LENGTH l = d - m + 1’
 >- rw [Abbr ‘l’, alloc_thm]
 >> STRIP_TAC
 >> Know ‘DISJOINT (set l) Z’
 >- (rw [Abbr ‘l’, Abbr ‘z’, DISJOINT_ALT', alloc_def, MEM_MAP] \\
     ONCE_REWRITE_TAC [TAUT ‘~P \/ Q \/ ~R <=> P /\ R ==> Q’] \\
     STRIP_TAC \\
    ‘FINITE Z’ by rw [Abbr ‘Z’] \\
     MP_TAC (Q.SPECL [‘x’, ‘Z’] string_width_thm) >> rw [])
 >> DISCH_TAC
 (* now recover the old definition of Y *)
 >> Know ‘DISJOINT (set l) (FV M1)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘Z’ >> art [])
 >> ASM_REWRITE_TAC [FV_appstar, FV_thm]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> Q.PAT_X_ASSUM ‘DISJOINT (set l) {y}’ (* ~MEM y l *)
       (STRIP_ASSUME_TAC o (SIMP_RULE (srw_ss()) [DISJOINT_ALT']))
 >> ‘l <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘as = FRONT l’
 >> ‘LENGTH as = d - m’ by rw [Abbr ‘as’, LENGTH_FRONT]
 >> qabbrev_tac ‘b = LAST l’
 >> Know ‘l = SNOC b as’
 >- (ASM_SIMP_TAC std_ss [Abbr ‘as’, Abbr ‘b’, SNOC_LAST_FRONT])
 >> DISCH_TAC
 >> qabbrev_tac ‘p3 = MAP rightctxt (REVERSE (MAP VAR l))’
 >> ‘Boehm_transform p3’ by rw [Abbr ‘p3’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* applying permutator_thm *)
 >> Know ‘apply p3 (P @* args') == VAR b @* args' @* MAP VAR as’
 >- (simp [Abbr ‘p3’, Abbr ‘P’, rightctxt_thm, MAP_SNOC,
           Boehm_apply_MAP_rightctxt'] \\
     REWRITE_TAC [GSYM appstar_APPEND, APPEND_ASSOC] \\
     MATCH_MP_TAC permutator_thm >> rw [])
 >> DISCH_TAC
 (* pre-final stage *)
 >> Q.EXISTS_TAC ‘p3 ++ p2 ++ p1’
 >> CONJ_ASM1_TAC
 >- (MATCH_MP_TAC Boehm_transform_APPEND >> art [] \\
     MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> Know ‘apply (p3 ++ p2 ++ p1) M == VAR b @* args' @* MAP VAR as’
 >- (MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply (p3 ++ p2 ++ p1) M0’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                  CONJ_TAC >- art [] \\
                  qunabbrev_tac ‘M0’ \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principle_hnf' >> art []) \\
     ONCE_REWRITE_TAC [Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply (p3 ++ p2) M1’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] \\
                  MATCH_MP_TAC Boehm_transform_APPEND >> art []) \\
     ONCE_REWRITE_TAC [Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply p3 (P @* args')’ >> art [] \\
     MATCH_MP_TAC Boehm_apply_lameq_cong >> rw [])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘principle_hnf (apply (p3 ++ p2 ++ p1) M) = VAR b @* args' @* MAP VAR as’
 >- (Q.PAT_X_ASSUM ‘Boehm_transform (p3 ++ p2 ++ p1)’ K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p1’               K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p2’               K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p3’               K_TAC \\
     Q.PAT_X_ASSUM ‘apply p1 M0 == M1’                K_TAC \\
     Q.PAT_X_ASSUM ‘apply p2 M1 = P @* args'’         K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’       K_TAC \\
  (* preparing for principle_hnf_denude_thm *)
     Q.PAT_X_ASSUM ‘apply (p3 ++ p2 ++ p1) M == _’ MP_TAC \\
     simp [Boehm_apply_APPEND, Abbr ‘p1’, Abbr ‘p2’, Abbr ‘p3’,
           Boehm_apply_MAP_rightctxt'] \\
     Know ‘[P/y] (M @* MAP VAR vs) @* MAP VAR (SNOC b as) =
           [P/y] (M @* MAP VAR vs @* MAP VAR (SNOC b as))’
     >- (simp [appstar_SUB] \\
         Suff ‘MAP [P/y] (MAP VAR (SNOC b as)) = MAP VAR (SNOC b as)’ >- Rewr \\
         Q.PAT_X_ASSUM ‘l = SNOC b as’ (ONCE_REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘LENGTH l = d - m + 1’ K_TAC \\
         rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         REWRITE_TAC [FV_thm, IN_SING] \\
         Q.PAT_X_ASSUM ‘~MEM y l’ MP_TAC \\
         rw [MEM_EL] >> METIS_TAC []) >> Rewr' \\
     DISCH_TAC (* [P/y] ... == ... *) \\
  (* applying principle_hnf_permutator *)
     Know ‘VAR b @* args' @* MAP VAR as =
           principle_hnf ([P/y] (VAR y @* args @* MAP VAR (SNOC b as)))’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         simp [appstar_SUB, appstar_SNOC, MAP_SNOC] \\
         Know ‘MAP [P/y] (MAP VAR as) = MAP VAR as’
         >- (Q.PAT_X_ASSUM ‘LENGTH as = _’ K_TAC \\
             rw [LIST_EQ_REWRITE, EL_MAP] \\
             MATCH_MP_TAC lemma14b >> rw [] \\
             Q.PAT_X_ASSUM ‘~MEM y (SNOC b as)’ MP_TAC \\
             rw [MEM_EL] >> PROVE_TAC []) >> Rewr' \\
         Know ‘[P/y] (VAR b) = VAR b’
         >- (MATCH_MP_TAC lemma14b >> fs [MEM_SNOC, IN_UNION]) >> Rewr' \\
         simp [Abbr ‘P’, GSYM appstar_APPEND] \\
         MATCH_MP_TAC principle_hnf_permutator >> rw []) >> Rewr' \\
  (* applying principle_hnf_SUB_cong *)
     MATCH_MP_TAC principle_hnf_SUB_cong \\
     CONJ_TAC (* has_hnf #1 *)
     >- (simp [GSYM solvable_iff_has_hnf, GSYM appstar_APPEND] \\
        ‘M0 == M’ by rw [lameq_principle_hnf', Abbr ‘M0’] \\
        ‘M0 @* (MAP VAR vs ++ MAP VAR (SNOC b as)) ==
          M @* (MAP VAR vs ++ MAP VAR (SNOC b as))’ by rw [lameq_appstar_cong] \\
         Suff ‘solvable (M0 @* (MAP VAR vs ++ MAP VAR (SNOC b as)))’
         >- PROVE_TAC [lameq_solvable_cong] \\
         NTAC 2 (POP_ASSUM K_TAC) \\
         REWRITE_TAC [appstar_APPEND] \\
         qabbrev_tac ‘M0' = M0 @* MAP VAR vs’ \\
        ‘M0' == M1’ by rw [Abbr ‘M0'’] \\
        ‘M0' @* MAP VAR (SNOC b as) == M1 @* MAP VAR (SNOC b as)’
           by rw [lameq_appstar_cong] \\
         Suff ‘solvable (M1 @* MAP VAR (SNOC b as))’
         >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf #2 *)
     >- (REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
         >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf # 3 *)
     >- (simp [appstar_SUB, MAP_SNOC] \\
         Know ‘MAP [P/y] (MAP VAR as) = MAP VAR as’
         >- (Q.PAT_X_ASSUM ‘LENGTH as = _’ K_TAC \\
             rw [LIST_EQ_REWRITE, EL_MAP] \\
             MATCH_MP_TAC lemma14b >> rw [] \\
             Q.PAT_X_ASSUM ‘~MEM y (SNOC b as)’ MP_TAC \\
             rw [MEM_EL] >> PROVE_TAC []) >> Rewr' \\
         Know ‘[P/y] (VAR b) = VAR b’
         >- (MATCH_MP_TAC lemma14b >> fs [MEM_SNOC, IN_UNION]) >> Rewr' \\
         simp [Abbr ‘P’, GSYM appstar_APPEND] \\
         REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Know ‘permutator d @* (args' ++ MAP VAR as) @@ VAR b ==
               VAR b @* (args' ++ MAP VAR as)’
         >- (MATCH_MP_TAC permutator_thm >> rw []) >> DISCH_TAC \\
         Suff ‘solvable (VAR b @* (args' ++ MAP VAR as))’
         >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
  (* applying the celebrating principle_hnf_denude_thm

     NOTE: here ‘DISJOINT (set vs) (FV M)’ is required, and this means that
          ‘vs’ must exclude ‘FV M’ instead of just ‘FV M0’.
   *)
     MATCH_MP_TAC principle_hnf_denude_thm >> rw [])
 >> DISCH_TAC
 >> simp [is_ready', GSYM CONJ_ASSOC]
 (* extra subgoal: solvable (apply (p3 ++ p2 ++ p1) M) *)
 >> ONCE_REWRITE_TAC [TAUT ‘P /\ Q /\ R <=> Q /\ P /\ R’]
 >> CONJ_ASM1_TAC
 >- (Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
     >- PROVE_TAC [lameq_solvable_cong] \\
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar])
 (* applying is_ready_alt *)
 >> CONJ_TAC
 >- (simp [is_ready_alt] \\
     qexistsl_tac [‘b’, ‘args' ++ MAP VAR as’] \\
     CONJ_TAC
     >- (MP_TAC (Q.SPEC ‘VAR b @* args' @* MAP VAR as’
                   (MATCH_MP principle_hnf_thm'
                             (ASSUME “solvable (apply (p3 ++ p2 ++ p1) M)”))) \\
         simp [appstar_APPEND]) \\
     simp [] (* now two EVERY *) \\
     reverse CONJ_TAC
     >- (rw [EVERY_MEM, Abbr ‘b’, Abbr ‘as’, MEM_MAP] >> rw [FV_thm] \\
         Q.PAT_X_ASSUM ‘ALL_DISTINCT l’ MP_TAC \\
         Q.PAT_X_ASSUM ‘l = SNOC (LAST l) (FRONT l)’ (ONCE_REWRITE_TAC o wrap) \\
         rw [ALL_DISTINCT_SNOC] >> PROVE_TAC []) \\
     rw [EVERY_MEM, MEM_MAP] \\
     qabbrev_tac ‘Y = BIGUNION (IMAGE FV (set args))’ \\
     rfs [LIST_TO_SET_SNOC] \\
     Suff ‘FV e SUBSET Y’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrev_tac ‘Y’ \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘BIGUNION (IMAGE FV (set args'))’ \\
     reverse CONJ_TAC
     >- (rw [SUBSET_DEF, IN_BIGUNION_IMAGE, MEM_EL] \\
         Q.EXISTS_TAC ‘EL n args’ \\
         CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> art []) \\
         POP_ASSUM MP_TAC \\
         Suff ‘FV (EL n args') SUBSET FV (EL n args)’ >- METIS_TAC [SUBSET_DEF] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     Q.EXISTS_TAC ‘e’ >> art [])
 (* extra goal *)
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘apply (p3 ++ p2 ++ p1) M == _’ K_TAC \\
     Q.PAT_X_ASSUM ‘principle_hnf (apply (p3 ++ p2 ++ p1) M) = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’ K_TAC \\
     rpt (Q.PAT_X_ASSUM ‘Boehm_transform _’ K_TAC) \\
     Q.PAT_X_ASSUM ‘solvable (apply (p3 ++ p2 ++ p1) M)’ K_TAC \\
     simp [Boehm_apply_APPEND, Abbr ‘p1’, Abbr ‘p2’, Abbr ‘p3’,
           Boehm_apply_MAP_rightctxt'] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     reverse CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW r’ \\
         rw [Abbr ‘l’, alloc_SUBSET_ROW] \\
         Suff ‘ROW r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [ROW_SUBSET_RANK]) \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV (M @* MAP VAR vs)’ \\
     CONJ_TAC >- (MATCH_MP_TAC FV_SUB_SUBSET >> art []) \\
     simp [FV_appstar] \\
     reverse CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW r’ \\
         rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
         Suff ‘ROW r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [ROW_SUBSET_RANK]) \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ >> art [] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 (* stage work, there's the textbook choice of y and P *)
 >> qabbrev_tac ‘pi = p3 ++ p2 ++ p1’
 >> qexistsl_tac [‘y’, ‘P’] >> art []
 >> NTAC 2 STRIP_TAC (* push ‘q <<= p’ to assumptions *)
 (* RHS rewriting from M to M0 *)
 >> Know ‘subterm X M0 q r = subterm X M q r’
 >- (qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC subterm_of_principle_hnf >> art [])
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
 (* LHS rewriting from M to M0 *)
 >> Know ‘subterm X (apply pi M) q r =
          subterm X (VAR b @* args' @* MAP VAR as) q r’
 >- (Q.PAT_X_ASSUM ‘_ = VAR b @* args' @* MAP VAR as’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     qabbrev_tac ‘t = apply pi M’ \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC subterm_of_principle_hnf >> art [])
 >> Rewr'
 (* stage cleanups *)
 >> Q.PAT_X_ASSUM ‘solvable (apply pi M)’          K_TAC
 >> Q.PAT_X_ASSUM ‘principle_hnf (apply pi M) = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘apply pi M == _’                K_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform pi’             K_TAC
 (* stage work, now ‘M’ is eliminated from both sides! *)
 >> Cases_on ‘q’ >- FULL_SIMP_TAC std_ss [] (* this asserts q = h::t *)
 >> Know ‘h < m’
 >- (Cases_on ‘p’ >> fs [] \\
     Q.PAT_X_ASSUM ‘h = h'’ (fs o wrap o SYM) \\
     Know ‘subterm X M (h::t) r <> NONE’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
     CONV_TAC (UNBETA_CONV “subterm X M (h::t) r”) \\
     qmatch_abbrev_tac ‘f _’ \\
     RW_TAC bool_ss [subterm_of_solvables] \\
     simp [Abbr ‘f’])
 >> DISCH_TAC
 (* applying subterm_of_absfree_hnf *)
 >> MP_TAC (Q.SPECL [‘X’, ‘VAR b @* args' @* MAP VAR as’, ‘h’, ‘t’, ‘r’]
                    subterm_of_absfree_hnf)
 >> simp [hnf_appstar, GSYM appstar_APPEND, hnf_children_appstar]
 >> DISCH_THEN K_TAC (* already used *)
 (* eliminating ‘MAP VAR as’ *)
 >> Know ‘EL h (args' ++ MAP VAR as) = EL h args'’
 >- (MATCH_MP_TAC EL_APPEND1 >> rw [])
 >> Rewr'
 (* eliminating ‘vs’

    NOTE: ‘subterm Y’ changed to ‘subterm Z’ at next level. There's no
    flexibility here on the choice of excluded variabes.
  *)
 >> Know ‘subterm X (LAMl vs (VAR y @* args)) (h::t) r =
          subterm X (EL h args) t (SUC r)’
 >- (MP_TAC (Q.SPECL [‘X’, ‘LAMl vs (VAR y @* args)’, ‘h’, ‘t’, ‘r’]
                     subterm_of_hnf) \\
     simp [hnf_LAMl, hnf_appstar] \\
     DISCH_THEN K_TAC (* already used *) \\
     Q.PAT_X_ASSUM ‘M0 = LAMl vs (VAR y @* args)’ (REWRITE_TAC o wrap o SYM) \\
     simp [hnf_children_hnf])
 >> Rewr'
 (* Now: subterm' Z (EL h args') t == [P/y] (subterm' Z (EL h args) t)

    First of all, those assumptions about p1,p2,p3 are no more needed.
  *)
 >> qunabbrev_tac ‘pi’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p1’         K_TAC
 >> Q.PAT_X_ASSUM ‘apply p1 M0 == M1’          K_TAC
 >> qunabbrev_tac ‘p1’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p2’         K_TAC
 >> Q.PAT_X_ASSUM ‘apply p2 M1 = P @* args'’   K_TAC
 >> qunabbrev_tac ‘p2’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p3’         K_TAC
 >> Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’ K_TAC
 >> qunabbrev_tac ‘p3’
 >> Q.PAT_X_ASSUM ‘h::t <> []’                 K_TAC (* too obvious *)
 >> qabbrev_tac ‘N  = EL h args’
 >> qabbrev_tac ‘N' = EL h args'’
 (* eliminating N' *)
 >> ‘N' = [P/y] N’ by simp [EL_MAP, Abbr ‘m’, Abbr ‘N’, Abbr ‘N'’, Abbr ‘args'’]
 >> POP_ORW
 >> qunabbrev_tac ‘N'’
 (* cleanup args' *)
 >> Q.PAT_X_ASSUM ‘!i. i < m ==> FV (EL i args') SUBSET FV (EL i args)’ K_TAC
 >> Q.PAT_X_ASSUM ‘LENGTH args' = m’ K_TAC
 >> qunabbrev_tac ‘args'’
 (* cleanup l, as and b *)
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT l’             K_TAC
 >> NTAC 2 (Q.PAT_X_ASSUM ‘DISJOINT (set l) _’ K_TAC)
 >> Q.PAT_X_ASSUM ‘LENGTH l = q - m + 1’       K_TAC
 >> Q.PAT_X_ASSUM ‘l <> []’                    K_TAC
 >> Q.PAT_X_ASSUM ‘l = SNOC b as’              K_TAC
 >> Q.PAT_X_ASSUM ‘~MEM y l’                   K_TAC
 >> Q.PAT_X_ASSUM ‘LENGTH as = q - m’          K_TAC
 >> qunabbrevl_tac [‘l’, ‘as’, ‘b’]
 (* applying subterm_headvar_lemma *)
 >> Know ‘hnf_headvar M1 IN X UNION RANK (SUC r)’
 >- (MATCH_MP_TAC subterm_headvar_lemma \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘vs’] >> simp [])
 >> ASM_SIMP_TAC std_ss [hnf_head_hnf, THE_VAR_thm]
 >> DISCH_TAC (* y IN X UNION RANK (SUC r) *)
 (* applying subterm_subst_cong *)
 >> MATCH_MP_TAC subterm_subst_cong'
 >> Q.EXISTS_TAC ‘d’
 >> simp [Abbr ‘P’]
 >> CONJ_TAC
 >- (qunabbrev_tac ‘N’ >> MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 (* stage work *)
 >> CONJ_ASM1_TAC (* subterm Z N t <> NONE *)
 >- (Q.PAT_X_ASSUM ‘!q. q <<= p ==> subterm X M q r <> NONE’
       (MP_TAC o Q.SPEC ‘h::t’) \\
     Q.PAT_X_ASSUM ‘M0 = _’ K_TAC \\
     simp [subterm_of_solvables])
 (* final goal: subterm_width (EL h args) t <= d *)
 >> qunabbrev_tac ‘d’
 (* applying subterm_width_thm *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> Cases_on ‘t = []’ >- rw []
 (* applying subterm_width_thm again *)
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘t’, ‘SUC r’] subterm_width_thm)
 >> Know ‘FV N SUBSET X UNION RANK (SUC r)’
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> DISCH_TAC
 >> ‘t IN ltree_paths (BT' X N (SUC r))’ by PROVE_TAC [subterm_imp_ltree_paths]
 >> simp [] >> DISCH_THEN K_TAC
 (* applying SUBSET_MAX_SET *)
 >> MATCH_MP_TAC SUBSET_MAX_SET
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE \\
     MATCH_MP_TAC SUBSET_FINITE_I \\
     Q.EXISTS_TAC ‘{subterm' X N q (SUC r) | q <<= FRONT t}’ \\
     reverse CONJ_TAC
     >- (rw [SUBSET_DEF] >> Q.EXISTS_TAC ‘q’ >> art []) \\
    ‘{subterm' X N q (SUC r) | q <<= FRONT t} =
      IMAGE (\p. subterm' X N p (SUC r)) {q | q <<= FRONT t}’
        by rw [Once EXTENSION] >> POP_ORW \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE \\
     MATCH_MP_TAC SUBSET_FINITE_I \\
     Q.EXISTS_TAC ‘{subterm' X M q r | q <<= FRONT p}’ \\
     reverse CONJ_TAC
     >- (rw [SUBSET_DEF] >> Q.EXISTS_TAC ‘q’ >> art []) \\
    ‘{subterm' X M q r | q <<= FRONT p} =
      IMAGE (\p. subterm' X M p r) {q | q <<= FRONT p}’
        by rw [Once EXTENSION] >> POP_ORW \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 (* final goal *)
 >> ‘hnf_children_size M0 = m’ by rw [Abbr ‘m’]
 >> Q.PAT_X_ASSUM ‘M0 = _’ K_TAC
 >> rw [SUBSET_DEF] (* this asserts ‘q <<= FRONT t’ *)
 >> Q.EXISTS_TAC ‘subterm' X N q (SUC r)’ >> art []
 >> Q.EXISTS_TAC ‘h::q’
 >> Know ‘FRONT p <> []’
 >- (Cases_on ‘p’ >> gs [] \\
     CCONTR_TAC >> gs [])
 >> DISCH_TAC
 >> Know ‘h::q <<= FRONT p’
 >- (qabbrev_tac ‘Y = X UNION RANK r’ \\
     qabbrev_tac ‘Y' = X UNION RANK (SUC r)’ \\
     Cases_on ‘p’ >> fs [] \\
     Cases_on ‘t'’ >> fs [] \\
     MATCH_MP_TAC IS_PREFIX_TRANS \\
     Q.EXISTS_TAC ‘FRONT t’ >> art [] \\
     MATCH_MP_TAC IS_PREFIX_FRONT_MONO >> rw [])
 >> DISCH_TAC
 >> simp []
 >> Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::q) r’
QED

(* Proposition 10.3.7 (i) [1, p.248] (Boehm out lemma)

   NOTE: This time the case ‘p = []’ can be included, but it's a trvial case.

   NOTE: The original lemma in textbook requires ‘p IN ltree_paths (BT X M)’,
   but this seems wrong, as ‘subterm X M p’ may not be defined if only ‘p’ is
   valid path (i.e. the subterm could be a bottom (\bot) as the result of un-
   solvable terms).

   NOTE: Can we enhance this lemma by using ‘-h->*’ instead of ‘==’?

   NOTE: Use subterm_imp_ltree_paths to prove ‘p IN ltree_paths (BT X M)’.
 *)
Theorem Boehm_out_lemma :
    !X p M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
              ?pi. Boehm_transform pi /\
                   ?ss. apply pi M == subterm' X M p r ISUB ss
Proof
    Q.X_GEN_TAC ‘X’
 >> Induct_on ‘p’
 >- (rw [] \\
     Q.EXISTS_TAC ‘[]’ >> rw [] \\
     Q.EXISTS_TAC ‘[]’ >> rw [])
 >> rpt STRIP_TAC
 >> rename1 ‘subterm X M (h::t) r <> NONE’
 >> qabbrev_tac ‘p = h::t’ (* head and tail *)
 >> ‘p <> []’ by rw [Abbr ‘p’]
 >> ‘(!q. q <<= p ==> subterm X M q r <> NONE) /\
      !q. q <<= FRONT p ==> solvable (subterm' X M q r)’
         by METIS_TAC [subterm_solvable_lemma]
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘r’] Boehm_transform_exists_lemma)
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘p0’ MP_TAC)
 >> RW_TAC std_ss [] (* push p0 properties to assumptions *)
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘p’)) (* put q = p *)
 >> rw []
 >> qabbrev_tac ‘M' = apply p0 M’
 >> ‘solvable M' /\ ?y Ms. M' -h->* VAR y @* Ms /\ EVERY (\e. y # e) Ms’
       by METIS_TAC [is_ready_alt']
 >> ‘principle_hnf M' = VAR y @* Ms’ by rw [principle_hnf_thm', hnf_appstar]
 (* stage work *)
 >> qunabbrev_tac ‘p’
 >> Know ‘h < LENGTH Ms’
 >- (Q.PAT_X_ASSUM ‘subterm X M' (h::t) r <> NONE’ MP_TAC \\
     RW_TAC std_ss [subterm_of_solvables] >> fs [])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH Ms’
 >> qabbrev_tac ‘N = EL h Ms’
 (* stage work *)
 >> Know ‘subterm X N t (SUC r) <> NONE /\
          subterm' X M' (h::t) r = subterm' X N t (SUC r)’
 >- (Q.PAT_X_ASSUM ‘subterm' X M' (h::t) r =
                    [P/v] (subterm' X M (h::t) r)’ K_TAC \\
     Q.PAT_X_ASSUM ‘subterm X M' (h::t) r <> NONE’ MP_TAC \\
     rw [subterm_of_solvables, Abbr ‘N’])
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘subterm' X M' (h::t) r = subterm' X N t (SUC r)’ (fs o wrap)
 >> T_TAC
 (* stage work, now define a selector *)
 >> qabbrev_tac ‘U = selector h m’
 >> qabbrev_tac ‘p1 = [[U/y]]’
 >> ‘Boehm_transform p1’ by rw [Abbr ‘p1’]
 >> qabbrev_tac ‘p10 = p1 ++ p0’
 >> ‘Boehm_transform p10’ by rw [Abbr ‘p10’, Boehm_transform_APPEND]
 (* applying properties of selector (U) *)
 >> Know ‘apply p10 M == N’
 >- (rw [Abbr ‘p10’, Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply p1 (principle_hnf M')’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                  CONJ_TAC >- art [] \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principle_hnf' >> art []) \\
     rw [Abbr ‘p1’, appstar_SUB] \\
     Know ‘MAP [U/y] Ms = Ms’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘EVERY (\e. y # e) Ms’ MP_TAC \\
         rw [EVERY_MEM, MEM_EL] \\
         POP_ASSUM MATCH_MP_TAC >> rename1 ‘i < m’ \\
         Q.EXISTS_TAC ‘i’ >> art []) >> Rewr' \\
     qunabbrevl_tac [‘U’, ‘N’] \\
     MATCH_MP_TAC selector_thm >> rw [Abbr ‘m’])
 >> DISCH_TAC
 (* stage work, now using IH *)
 >> Q.PAT_X_ASSUM ‘!M r. _’ (MP_TAC o (Q.SPECL [‘N’, ‘SUC r’])) >> simp []
 >> Know ‘FV N SUBSET X UNION RANK (SUC r)’
 >- (qunabbrevl_tac [‘N’, ‘M'’] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV (apply p0 M)’ >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV (VAR y @* Ms)’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC hreduce_FV_SUBSET >> art []) \\
     rw [SUBSET_DEF, FV_appstar, IN_UNION] \\
     DISJ2_TAC \\
     Q.EXISTS_TAC ‘FV (EL h Ms)’ >> art [] \\
     Q.EXISTS_TAC ‘EL h Ms’ >> rw [EL_MEM])
 >> RW_TAC std_ss []
 >> rename1 ‘apply p2 N == _ ISUB ss'’
 >> qabbrev_tac ‘N' = subterm' X M (h::t) r’
 (* final stage *)
 >> Q.EXISTS_TAC ‘p2 ++ p10’
 >> CONJ_TAC
 >- (MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> Q.EXISTS_TAC ‘[(P,v)] ++ ss'’
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply p2 N’
 >> simp [ISUB_def]
 >> rw [Boehm_apply_APPEND]
 >> MATCH_MP_TAC Boehm_apply_lameq_cong >> art []
QED

(*---------------------------------------------------------------------------*
 *  Faithfulness and agreements of terms
 *---------------------------------------------------------------------------*)

(* Definition 10.2.21 (i) [1, p.238]

   NOTE: ‘A’ and ‘B’ are ltree nodes returned by ‘THE (ltree_el (BT M) p)’
 *)
Definition head_equivalent_def :
    head_equivalent (A :BT_node # num option)
                    (B :BT_node # num option) =
      if IS_SOME (FST A) /\ IS_SOME (FST B) then
         let (vs1,y1) = THE (FST A);
             (vs2,y2) = THE (FST B);
                   n1 = LENGTH vs1;
                   n2 = LENGTH vs2;
                   m1 = THE (SND A);
                   m2 = THE (SND B)
         in
             LAMl vs1 (VAR y1) = LAMl vs2 (VAR y2) /\ n1 + m2 = n2 + m1
      else
         IS_NONE (FST A) /\ IS_NONE (FST B)
End

Theorem head_equivalent_refl[simp] :
    head_equivalent A A
Proof
    rw [head_equivalent_def]
 >> Cases_on ‘A’ >> fs []
 >> rename1 ‘IS_SOME a’
 >> Cases_on ‘a’ >> fs []
 >> Cases_on ‘x’ >> rw []
QED

Theorem head_equivalent_sym :
    !A B. head_equivalent A B ==> head_equivalent B A
Proof
    simp [head_equivalent_def]
 >> qx_genl_tac [‘A’, ‘B’]
 >> Cases_on ‘A’ >> Cases_on ‘B’ >> simp []
 >> Cases_on ‘q’ >> Cases_on ‘q'’ >> simp []
 >> Cases_on ‘x’ >> Cases_on ‘x'’ >> simp []
QED

Theorem head_equivalent_comm :
    !A B. head_equivalent A B <=> head_equivalent B A
Proof
    rpt GEN_TAC
 >> EQ_TAC >> rw [head_equivalent_sym]
QED

(* Definition 10.2.21 (ii) [1, p.238] *)
Definition subtree_equivalent_def :
    subtree_equivalent p (A :boehm_tree) (B :boehm_tree) =
        let A' = ltree_el A p;
            B' = ltree_el B p
        in
            if IS_SOME A' /\ IS_SOME B' then
               head_equivalent (THE A') (THE B')
            else
               IS_NONE A' /\ IS_NONE B'
End

Theorem subtree_equivalent_refl[simp] :
    subtree_equivalent p A A
Proof
    rw [subtree_equivalent_def]
QED

Theorem subtree_equivalent_sym :
    !p A B. subtree_equivalent p A B ==> subtree_equivalent p B A
Proof
    rpt GEN_TAC
 >> simp [subtree_equivalent_def]
 >> rw [Once head_equivalent_comm] >> rfs []
 >> CCONTR_TAC >> rfs []
QED

Theorem subtree_equivalent_comm :
    !p A B. subtree_equivalent p A B <=> subtree_equivalent p B A
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> rw [subtree_equivalent_sym]
QED

(* Definition 10.2.32 (v) [1, p.245] *)
Definition subterm_equivalent_def :
    subterm_equivalent p M N =
    subtree_equivalent p (BT' (FV M UNION FV N) M 0)
                         (BT' (FV M UNION FV N) N 0)
End

Theorem subterm_equivalent_refl[simp] :
    subterm_equivalent p M M
Proof
    rw [subterm_equivalent_def]
QED

Theorem subterm_equivalent_sym :
    !p M N. subterm_equivalent p M N ==> subterm_equivalent p N M
Proof
    rpt GEN_TAC
 >> simp [subterm_equivalent_def]
 >> ‘FV M UNION FV N = FV N UNION FV M’ by SET_TAC []
 >> POP_ORW
 >> rw [Once subtree_equivalent_comm]
QED

Theorem subterm_equivalent_comm :
    !p M N. subterm_equivalent p M N <=> subterm_equivalent p N M
Proof
    rpt GEN_TAC
 >> EQ_TAC >> rw [subterm_equivalent_sym]
QED

(* NOTE: ‘ltree_paths (BT' X M r) SUBSET ltree_paths (BT' X ([P/v] M) r)’ doesn't
         hold. Instead, we need to consider certain p and ‘d <= subterm_width M p’.
         This theorem holds even when M is not solvable.
 *)
Theorem BT_ltree_paths_subst_cong :
    !X P d v p M r.
         FINITE X /\ FV M SUBSET X UNION RANK r /\ v IN X UNION RANK r /\
         P = permutator d /\ subterm_width M p <= d /\
         p IN ltree_paths (BT' X M r) ==>
         p IN ltree_paths (BT' X ([P/v] M) r) /\
         subterm_width ([P/v] M) p <= d
Proof
    simp [ltree_paths_def]
 >> NTAC 4 GEN_TAC
 >> Induct_on ‘p’ >- rw [ltree_lookup]
 >> rpt GEN_TAC >> STRIP_TAC
 >> qabbrev_tac ‘P = permutator d’
 >> ‘h::p IN ltree_paths (BT' X M r)’ by rw [ltree_paths_def]
 >> Q.PAT_X_ASSUM ‘ltree_lookup (BT' X M r) (h::p) <> NONE’ MP_TAC
 >> qabbrev_tac ‘Y = X UNION RANK r’
 >> reverse (Cases_on ‘solvable M’)
 >- simp [BT_def, BT_generator_def, Once ltree_unfold, ltree_lookup_def]
 >> DISCH_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M0)’ K_TAC
 >> Know ‘~MEM v vs’
 >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     rw [Abbr ‘Y’, IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art [])
 >> DISCH_TAC
 >> Know ‘solvable ([P/v] M)’
 >- (MATCH_MP_TAC solvable_subst \\
     qexistsl_tac [‘X’,‘M0’, ‘r’, ‘d’] >> simp [] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_width_first) \\
     simp [ltree_paths_def])
 >> DISCH_TAC
 >> ‘M -h->* M0’ by METIS_TAC [principle_hnf_thm']
 >> Know ‘[P/v] M -h->* [P/v] M0’ >- PROVE_TAC [hreduce_substitutive]
 >> ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT', FV_permutator, Abbr ‘P’]
 >> simp [LAMl_SUB, appstar_SUB]
 >> POP_ASSUM K_TAC (* DISJOINT (set vs) (FV P) *)
 >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> qabbrev_tac ‘m = LENGTH args’
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’, Abbr ‘m’]
 >> DISCH_TAC
 >> Know ‘!i. i < m ==> FV (EL i args') SUBSET FV (EL i args)’
 >- (rw [Abbr ‘m’, Abbr ‘args'’, EL_MAP] \\
     qabbrev_tac ‘N = EL i args’ \\
     simp [FV_SUB] \\
    ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
     simp [] \\
     Cases_on ‘v IN FV N’ >> SET_TAC [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘ltree_lookup (BT' X M r) (h::p) <> NONE’
      (MP_TAC o REWRITE_RULE [BT_def, BT_generator_def, ltree_unfold])
 >> simp [principle_hnf_beta_reduce, hnf_appstar, LMAP_fromList,
          ltree_lookup_def, LNTH_fromList]
 >> Cases_on ‘h < m’ >> simp [EL_MAP, GSYM BT_def]
 >> DISCH_TAC
 >> Know ‘subterm_width M (h::p) <= d <=>
          m <= d /\ subterm_width (EL h args) p <= d’
 >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> DISCH_THEN (rfs o wrap)
 >> qabbrev_tac ‘N = EL h args’
 (* stage work *)
 >> reverse (Cases_on ‘y = v’)
 >- (Q.PAT_X_ASSUM ‘[P/v] M -h->* _’ MP_TAC \\
     simp [] >> DISCH_TAC \\
     qabbrev_tac ‘M0' = LAMl vs (VAR y @* args')’ \\
    ‘hnf M0'’ by rw [hnf_appstar, Abbr ‘M0'’] \\
    ‘principle_hnf ([P/v] M) = M0'’ by METIS_TAC [principle_hnf_thm'] \\
     Q.PAT_X_ASSUM ‘hnf M0'’ K_TAC \\
     Q.PAT_X_ASSUM ‘M0 = LAMl vs (VAR y @* args)’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘M1 = VAR y @* args’ (ASSUME_TAC o SYM) \\
    ‘hnf_children M1 = args’ by rw [hnf_children_hnf] \\
    ‘LAMl_size M0' = n’ by rw [Abbr ‘M0'’, LAMl_size_hnf] \\
    ‘principle_hnf (M0' @* MAP VAR vs) = VAR y @* args'’
       by rw [Abbr ‘M0'’, principle_hnf_beta_reduce, hnf_appstar] \\
     STRONG_CONJ_TAC
     >- (simp [BT_def, BT_generator_def, Once ltree_unfold, ltree_lookup_def,
               LNTH_fromList, EL_MAP] \\
         simp [GSYM BT_def, EL_MAP, Abbr ‘args'’] \\
         FIRST_X_ASSUM (MATCH_MP_TAC o cj 1) >> art [] \\
         CONJ_TAC
         >- (qunabbrev_tac ‘N’ \\
             MATCH_MP_TAC subterm_induction_lemma' \\
             qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
             Q.PAT_X_ASSUM ‘_ = M0’ (REWRITE_TAC o wrap o SYM) \\
             simp []) \\
         Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
         qunabbrev_tac ‘Y’ \\
         Suff ‘X UNION RANK r SUBSET X UNION (RANK (SUC r))’
         >- METIS_TAC [SUBSET_DEF] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) >> DISCH_TAC \\
     Know ‘subterm_width ([P/v] M) (h::p) <= d <=>
           m <= d /\ subterm_width (EL h args') p <= d’
     >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
         qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n’, ‘vs’, ‘VAR y @* args'’] \\
         simp [principle_hnf_beta_reduce, ltree_paths_def] \\
         CONJ_TAC
         >- (rw [FV_SUB, Abbr ‘P’, FV_permutator] \\
             MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
             SET_TAC []) \\
         fs [Abbr ‘m’, Abbr ‘args'’, Abbr ‘M0'’]) >> Rewr' \\
     simp [Abbr ‘args'’, EL_MAP] \\
     FIRST_X_ASSUM (MATCH_MP_TAC o cj 2) >> art [] \\
     Q.EXISTS_TAC ‘SUC r’ >> art [] \\
     CONJ_TAC
     >- (qunabbrev_tac ‘N’ \\
         MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
         Q.PAT_X_ASSUM ‘_ = M0’ (REWRITE_TAC o wrap o SYM) \\
         simp []) \\
     Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     qunabbrev_tac ‘Y’ \\
     Suff ‘X UNION RANK r SUBSET X UNION (RANK (SUC r))’
     >- METIS_TAC [SUBSET_DEF] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 (* stage work *)
 >> POP_ASSUM (rfs o wrap o SYM) (* [P/y] from now on *)
 >> Q.PAT_X_ASSUM ‘[P/y] M -h->* _’ MP_TAC
 >> simp [Abbr ‘P’]
 >> DISCH_TAC (* [permutator d/v] M -h->* ... *)
 (* NOTE: New frash variables xs and y will be asserted here:

    P @* args' -h->* LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)),

    thus ‘principle_hnf ([P/y] M) = LAMl (vs ++ xs ++ [z]) (VAR z @* ...)’

    Here LENGTH xs = d - m. Let n' be the LAMl_size of the above hnf.
  *)
 >> qabbrev_tac ‘n' = n + (d - m) + 1’
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n' :num”)) ‘X’
 >> MP_TAC (Q.SPECL [‘set zs’, ‘d’, ‘args'’] permutator_hreduce_thm)
 >> impl_tac >- rpt (rw [])
 >> REWRITE_TAC [DISJOINT_UNION]
 >> STRIP_TAC
 >> rename1 ‘ALL_DISTINCT (SNOC z xs)’ (* y' -> z *)
 >> qabbrev_tac ‘P = permutator d’
 >> Know ‘LAMl vs (P @* args') -h->*
          LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)))’
 >- (rw [hreduce_LAMl])
 >> qmatch_abbrev_tac ‘LAMl vs (P @* args') -h->* t ==> _’
 >> DISCH_TAC
 >> ‘hnf t’ by rw [Abbr ‘t’, hnf_appstar, hnf_LAMl]
 >> ‘[P/y] M -h->* t’ by PROVE_TAC [hreduce_TRANS]
 >> ‘principle_hnf ([P/y] M) = t’ by METIS_TAC [principle_hnf_thm']
 (* cleanup *)
 >> Q.PAT_X_ASSUM ‘P @* args' -h->* _’      K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs _ -h->* t’       K_TAC
 >> Q.PAT_X_ASSUM ‘[P/y] M -h->* LAMl vs _’ K_TAC
 >> Q.PAT_X_ASSUM ‘[P/y] M -h->* t’         K_TAC
 >> Q.PAT_X_ASSUM ‘hnf t’                   K_TAC
 >> qunabbrev_tac ‘t’
 (* stage work *)
 >> POP_ASSUM MP_TAC
 >> ‘!t. LAMl vs (LAMl xs (LAM z t)) = LAMl (vs ++ (SNOC z xs)) t’
       by rw [LAMl_APPEND]
 >> POP_ORW
 >> REWRITE_TAC [GSYM appstar_APPEND]
 >> qabbrev_tac ‘args'' = args' ++ MAP VAR xs’
 >> ‘LENGTH args'' = d’ by rw [Abbr ‘args''’]
 >> qabbrev_tac ‘xs' = SNOC z xs’
 >> ‘LENGTH xs' = d - m + 1’ by rw [Abbr ‘xs'’]
 >> qabbrev_tac ‘vs' = vs ++ xs'’
 >> DISCH_TAC (* principle_hnf ([P/y] M) = ... *)
 >> Know ‘LENGTH vs' = n'’
 >- (qunabbrevl_tac [‘n’, ‘n'’, ‘vs'’, ‘xs'’] \\
     Q.PAT_X_ASSUM ‘M0 = _’  (REWRITE_TAC o wrap) \\
     simp [LAMl_size_LAMl])
 >> DISCH_TAC
  (* applying NEWS_prefix *)
 >> Know ‘vs <<= zs’
 >- (qunabbrevl_tac [‘vs’, ‘zs’] \\
     MATCH_MP_TAC RNEWS_prefix >> rw [Abbr ‘n'’])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> rename1 ‘zs = vs ++ ys'’ (* l -> ys' *)
 >> Know ‘LENGTH ys' = d - m + 1’
 >- (Know ‘LENGTH zs = LENGTH (vs ++ ys')’ >- POP_ASSUM (REWRITE_TAC o wrap) \\
     simp [Abbr ‘n'’])
 >> DISCH_TAC
 >> Know ‘!N. MEM N args' ==> DISJOINT (FV N) (set ys')’
 >- (Q.X_GEN_TAC ‘x’ \\
     simp [MEM_EL] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
     POP_ORW \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘FV (EL i args)’ >> simp [] \\
  (* applying subterm_FV_lemma *)
     Know ‘FV (EL i args) SUBSET X UNION RANK r UNION set vs’
     >- (MATCH_MP_TAC subterm_FV_lemma \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘M1’] >> simp []) \\
     DISCH_TAC \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘X UNION RANK r UNION set vs’ \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     simp [DISJOINT_ALT'] \\
     rpt CONJ_TAC
     >- (NTAC 2 STRIP_TAC \\
         Q.PAT_X_ASSUM ‘DISJOINT (set zs) X’ MP_TAC \\
         rw [DISJOINT_ALT])
     >- (NTAC 2 STRIP_TAC \\
         MP_TAC (Q.SPECL [‘r’, ‘n'’, ‘X’] DISJOINT_RANK_RNEWS') \\
         rw [DISJOINT_ALT', IN_UNION]) \\
     Q.PAT_X_ASSUM ‘ALL_DISTINCT zs’ MP_TAC \\
     rw [ALL_DISTINCT_APPEND] >> METIS_TAC [])
 >> DISCH_TAC
 >> qabbrev_tac ‘t = VAR z @* args''’
 >> ‘hnf t’ by rw [Abbr ‘t’, hnf_appstar]
 >> qabbrev_tac ‘M0' = LAMl vs' t’
 >> ‘LAMl_size M0' = n'’ by rw [Abbr ‘M0'’, Abbr ‘t’]
 >> qabbrev_tac ‘M1' = principle_hnf (M0' @* MAP VAR zs)’
 >> Know ‘M1' = tpm (ZIP (xs',ys')) t’
 >- (simp [Abbr ‘M0'’, Abbr ‘M1'’, Abbr ‘vs'’, GSYM APPEND_ASSOC, appstar_APPEND,
           LAMl_APPEND] \\
     Know ‘principle_hnf (LAMl vs (LAMl xs' t) @* MAP VAR vs @* MAP VAR ys') =
           principle_hnf (LAMl xs' t @* MAP VAR ys')’
     >- (MATCH_MP_TAC principle_hnf_hreduce \\
         simp [hreduce_BETA_extended]) >> Rewr' \\
     MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
     CONJ_TAC >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT zs’ MP_TAC \\
                  Q.PAT_X_ASSUM ‘zs = vs ++ ys'’ (ONCE_REWRITE_TAC o wrap) \\
                  simp [ALL_DISTINCT_APPEND]) \\
     CONJ_ASM1_TAC
     >- (ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set zs’ >> art [] \\
         rw [LIST_TO_SET_APPEND]) \\
     simp [Abbr ‘t’, Abbr ‘args''’, FV_appstar] \\
     CONJ_TAC (* ~MEM z ys' *)
     >- (POP_ASSUM MP_TAC \\
         rw [DISJOINT_ALT, Abbr ‘xs'’]) \\
     reverse CONJ_TAC (* MAP VAR xs *)
     >- (Q.X_GEN_TAC ‘s’ >> rw [MEM_MAP] >> rw [] \\
         Q.PAT_X_ASSUM ‘DISJOINT (set xs') (set ys')’ MP_TAC \\
         rw [Abbr ‘xs'’, DISJOINT_ALT]) \\
     Q.X_GEN_TAC ‘s’ >> simp [MEM_MAP] \\
     rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘s = FV x’ (REWRITE_TAC o wrap) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘zs = vs ++ ys'’ (ASSUME_TAC o SYM)
 (* stage work *)
 >> STRONG_CONJ_TAC
 >- (simp [BT_def, BT_generator_def, Once ltree_unfold, ltree_lookup_def,
           LNTH_fromList, EL_MAP] \\
     REWRITE_TAC [GSYM BT_def] \\
     simp [hnf_children_tpm, EL_MAP] \\
     simp [Abbr ‘t’, hnf_children_hnf] \\
     Know ‘h < LENGTH args''’
     >- (Q_TAC (TRANS_TAC LESS_LESS_EQ_TRANS) ‘m’ >> art [] \\
         rw [Abbr ‘args''’]) >> Rewr \\
    ‘EL h args'' = EL h args'’ by rw [Abbr ‘args''’, EL_APPEND1] \\
     POP_ORW \\
     Know ‘tpm (ZIP (xs',ys')) (EL h args') = EL h args'’
     >- (MATCH_MP_TAC lemma14b_tpm >> simp [MAP_ZIP] \\
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         CONJ_TAC \\ (* 2 subgoals, same tactics *)
         FIRST_X_ASSUM MATCH_MP_TAC \\
         simp [EL_MEM]) >> Rewr' \\
     simp [Abbr ‘args'’, EL_MAP] \\
     FIRST_X_ASSUM (MATCH_MP_TAC o cj 1) >> art [] \\
     qunabbrev_tac ‘Y’ \\
     reverse CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘y IN X UNION RANK r’ MP_TAC \\
         Suff ‘X UNION RANK r SUBSET X UNION RANK (SUC r)’
         >- (REWRITE_TAC [SUBSET_DEF] \\
             DISCH_THEN (REWRITE_TAC o wrap)) \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> DISCH_TAC
 (* extra goal for subterm_width *)
 >> qabbrev_tac ‘pi = ZIP (xs',ys')’
 >> Q.PAT_X_ASSUM ‘hnf t’ K_TAC
 >> rfs [Abbr ‘t’, tpm_appstar]
 >> qabbrev_tac ‘Ms = listpm term_pmact pi args''’
 >> Know ‘subterm_width ([P/y] M) (h::p) <= d <=>
          d <= d /\ subterm_width (EL h Ms) p <= d’
 >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n'’, ‘zs’, ‘M1'’] \\
     simp [principle_hnf_beta_reduce, ltree_paths_def] \\
     CONJ_TAC
     >- (rw [FV_SUB, Abbr ‘P’, FV_permutator] \\
         MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
         SET_TAC []) \\
     simp [Abbr ‘M0'’])
 >> Rewr'
 >> simp [Abbr ‘Ms’, EL_MAP]
 >> ‘EL h args'' = EL h args'’ by rw [Abbr ‘args''’, EL_APPEND1]
 >> POP_ORW
 >> qunabbrev_tac ‘pi’
 >> Know ‘tpm (ZIP (xs',ys')) (EL h args') = EL h args'’
 >- (MATCH_MP_TAC lemma14b_tpm >> simp [MAP_ZIP] \\
     ONCE_REWRITE_TAC [DISJOINT_SYM] \\
     CONJ_TAC \\ (* 2 subgoals, same tactics *)
     FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM])
 >> Rewr'
 >> simp [Abbr ‘args'’, EL_MAP]
 >> FIRST_X_ASSUM (MATCH_MP_TAC o cj 2) >> art []
 >> Q.EXISTS_TAC ‘SUC r’ >> art []
 >> CONJ_TAC
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC
 >> qunabbrev_tac ‘Y’
 >> Suff ‘X UNION RANK r SUBSET X UNION (RANK (SUC r))’
 >- METIS_TAC [SUBSET_DEF]
 >> Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC []
 >> rw [RANK_MONO]
QED

Theorem BT_ltree_paths_isub_cong :
    !ys p X M r P d ss.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
        P = permutator d /\
        (!y. MEM y ys ==> y IN X UNION RANK r) /\ ss = MAP (\y. (P,y)) ys /\
        p IN ltree_paths (BT' X M r) /\
        subterm_width M p <= d
    ==> p IN ltree_paths (BT' X (M ISUB ss) r) /\
        subterm_width (M ISUB ss) p <= d
Proof
    Induct_on ‘ys’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘ss = _’ (REWRITE_TAC o wrap)
 >> simp []
 >> Q.PAT_X_ASSUM ‘P = permutator d’ K_TAC
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘N = [P/h] M’
 >> qabbrev_tac ‘ss = MAP (\y. (P,y)) ys’
 >> MP_TAC (Q.SPECL [‘X’, ‘P’, ‘d’, ‘h’, ‘p’, ‘M’, ‘r’] BT_ltree_paths_subst_cong)
 >> simp []
 >> STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘P’ >> simp []
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art []
 >> rw [FV_SUB, Abbr ‘N’]
 >> rw [Abbr ‘P’, FV_permutator]
QED

(* Definition 10.3.10 (iii) and (iv)

   NOTE: The purpose of X is to make sure all terms in Ms share the same excluded
         set (and thus perhaps also the same initial binding list).

   NOTE: ‘EVERY (\M. p IN ltree_paths (BT' X M r)) Ms’ could be added, but without
         it the definition is NOT wrong (ltree_el = NONE in this case). For the next
         big theorem, this condition is actually already included. Putting it into
         the definition only creates a new proof goal (which may be useful in the
         future).
 *)
Definition agree_upto_def :
    agree_upto X Ms p r <=>
       !M N. MEM M Ms /\ MEM N Ms ==>
             !q. q <<= p ==> ltree_el (BT' X M r) q =
                             ltree_el (BT' X N r) q
End

(* Lemma 10.3.11 [1. p.251]

   NOTE: ‘p <> []’ must be added, otherwise each N in Ns cannot be "is_ready".

   NOTE: ‘!X M. MEM M Ns ==> subterm X M p <> NONE’ will be later assumed for
   non-trivial cases. If any M in Ns doesn't satisfy this requirements, then
  ‘subterm X M p = NONE’ (the unsolvable case) and doesn't have contributions
   in ‘pi’.

   On the other hand, if any M in Ns is unsolvable (and p <> []), then p cannot
   be in ‘ltree_paths (BT X M)’. Thus all terms in Ns are solvable.
   Let's first put ‘EVERY solvable Ns’ in assumption to focus on the non-trivial
   part of this proof.

   NOTE: ‘0 < r’ is to ensure a non-empty ‘RANK r’ to allocate fresh
   variables in it (for the construction of Boehm transform ‘pi’).

   NOTE: ‘EVERY (\M. subterm X M p r <> NONE) Ms’ implies
  ‘EVERY (\M. p IN ltree_paths (BT' X M r)) Ms’, part of ‘agree_upto_def’.
   Perhaps the theorem can still be proved without this antecedents.

   NOTE: If ‘EVERY (\M. p IN ltree_paths (BT' X M r)) Ms’ is used instead,
   those who doesn't satisfy ‘subterm X M p r <> NONE’ has much easier proofs.
 *)
Theorem agree_upto_lemma :
    !X Ms p r. FINITE X /\ p <> [] /\ 0 < r /\
               BIGUNION (IMAGE FV (set Ms)) SUBSET X UNION RANK r /\
               agree_upto X Ms p r /\ Ms <> [] /\
               EVERY (\M. subterm X M p r <> NONE) Ms ==>
               ?pi. Boehm_transform pi /\
                    EVERY is_ready' (MAP (apply pi) Ms) /\
                    agree_upto X (MAP (apply pi) Ms) p r
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘k = LENGTH Ms’
 >> Q.PAT_X_ASSUM ‘EVERY P Ms’ MP_TAC
 >> rw [EVERY_EL]
 >> qabbrev_tac ‘M = \i. EL i Ms’ >> fs []
 >> Know ‘!i. i < k ==> FV (M i) SUBSET X UNION RANK r’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘_ SUBSET X UNION RANK r’ MP_TAC \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘M i’ >> art [] \\
     rw [Abbr ‘M’, EL_MEM])
 >> DISCH_TAC
 (* now derive some non-trivial assumptions *)
 >> ‘!i. i < k ==> (!q. q <<= p ==> subterm X (M i) q r <> NONE) /\
                    !q. q <<= FRONT p ==> solvable (subterm' X (M i) q r)’
       by METIS_TAC [subterm_solvable_lemma]
 (* convert previous assumption into easier forms for MATCH_MP_TAC *)
 >> ‘(!i q. i < k /\ q <<= p ==> subterm X (M i) q r <> NONE) /\
     (!i q. i < k /\ q <<= FRONT p ==> solvable (subterm' X (M i) q r))’
       by PROVE_TAC []
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> P /\ Q’ K_TAC
 (* In the original antecedents of this theorem, some M may be unsolvable,
    and that's the easy case.
  *)
 >> Know ‘!i. i < k ==> solvable (M i)’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i q. i < k /\ q <<= FRONT p ==> solvable _’
       (MP_TAC o Q.SPECL [‘i’, ‘[]’]) >> simp [])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> p IN ltree_paths (BT' X (M i) r)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC subterm_imp_ltree_paths >> rw [])
 >> DISCH_TAC
 (* define M0 *)
 >> qabbrev_tac ‘M0 = \i. principle_hnf (M i)’
 >> Know ‘!i. i < k ==> hnf (M0 i)’
 >- (rw [Abbr ‘M0’] \\
     MATCH_MP_TAC hnf_principle_hnf \\
     rw [GSYM solvable_iff_has_hnf] >> fs [EVERY_EL])
 >> DISCH_TAC
 >> qabbrev_tac ‘n = \i. LAMl_size (M0 i)’
 >> qabbrev_tac ‘n_max = MAX_SET (IMAGE n (count k))’
 >> Know ‘!i. i < k ==> n i <= n_max’
 >- (rw [Abbr ‘M0’, Abbr ‘n_max’] \\
     irule MAX_SET_PROPERTY >> rw [])
 >> DISCH_TAC
 >> qabbrev_tac ‘Y = BIGUNION (IMAGE FV (set Ms))’
 >> ‘FINITE Y’ by (rw [Abbr ‘Y’] >> REWRITE_TAC [FINITE_FV])
 (* ‘vs’ excludes all free variables in M

    NOTE: The basic requirement for ‘vs’ is that it must be disjoint with ‘Y’
    and is at row 0. But if we exclude ‘X UNION Y’, then it also holds that
    ‘set vs SUBSET X UNION RANK r’ just like another part of ‘M’.
  *)
 >> Q_TAC (NEWS_TAC (“vs :string list”, “n_max :num”)) ‘X UNION Y’
 (* construct p1 *)
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE (MAP VAR vs))’
 >> ‘Boehm_transform p1’ by rw [Abbr ‘p1’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* decompose M0 by hnf_cases_shared *)
 >> Know ‘!i. i < k ==> ?y args. M0 i = LAMl (TAKE (n i) vs) (VAR y @* args)’
 >- (rw [Abbr ‘n’] >> irule (iffLR hnf_cases_shared) \\
     rw [] >- fs [o_DEF] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV (EL i Ms)’ \\
     reverse CONJ_TAC
     >- (rw [Abbr ‘M0’] >> MATCH_MP_TAC principle_hnf_FV_SUBSET \\
         rw [GSYM solvable_iff_has_hnf]) \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs) Y’ MP_TAC \\
     rw [Abbr ‘Y’] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘M i’ >> rw [Abbr ‘M’, EL_MEM])
 (* now assert two functions y and args for each term in Ms *)
 >> simp [EXT_SKOLEM_THM'] (* from topologyTheory *)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘y’
                 (Q.X_CHOOSE_THEN ‘args’ STRIP_ASSUME_TAC))
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> hnf (M0 i)’ K_TAC
 (* define M1 *)
 >> qabbrev_tac ‘M1 = \i. principle_hnf (M0 i @* MAP VAR vs)’
 >> Know ‘!i. i < k ==> M1 i = VAR (y i) @* args i @* DROP (n i) (MAP VAR vs)’
 >- (rw [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR (y i) @* args i’ \\
     rw [GSYM MAP_DROP] \\
     qabbrev_tac ‘xs = TAKE (n i) vs’ \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP (n i) vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP (n i) vs)’ \\
     MATCH_MP_TAC principle_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
 (* calculating ‘apply p1 (M0 i)’ *)
 >> Know ‘!i. i < k ==> apply p1 (M0 i) == M1 i’
 >- (rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt'] \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites
       [ISPECL [“(n :num -> num) i”, “MAP VAR vs”] (GSYM TAKE_DROP)] \\
     REWRITE_TAC [appstar_APPEND] \\
     MATCH_MP_TAC lameq_appstar_cong \\
     rw [GSYM MAP_TAKE])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = \i. LENGTH (args i)’
 >> qabbrev_tac ‘d = MAX_LIST (MAP (\e. subterm_width e p) Ms)’
 >> Know ‘!i. i < k ==> m i <= d’
 >- (RW_TAC std_ss [] \\
     Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M i) p’ \\
     reverse CONJ_TAC
     >- (rw [Abbr ‘d’] \\
         MATCH_MP_TAC MAX_LIST_PROPERTY >> rw [MEM_MAP] \\
         Q.EXISTS_TAC ‘M i’ >> rw [EL_MEM, Abbr ‘M’]) \\
     MP_TAC (Q.SPECL [‘X’, ‘(M :num -> term) i’, ‘p’, ‘r’] subterm_width_first) \\
     simp [Abbr ‘m’])
 >> DISCH_TAC
 (* NOTE: Thus P(d) is not enough to cover M1, whose ‘hnf_children_size’ is
    bounded by ‘d + n_max’. *)
 >> qabbrev_tac ‘d_max = d + n_max’
 >> Know ‘!i. i < k ==> hnf_children_size (M1 i) <= d_max’
 >- (rw [Abbr ‘M1’, Abbr ‘d_max’, GSYM appstar_APPEND] \\
     MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO >> rw [])
 >> DISCH_TAC
 >> qabbrev_tac ‘P = permutator d_max’
 (* construct p2 *)
 >> qabbrev_tac ‘p2 = GENLIST (\i. [P/y i]) k’
 >> ‘Boehm_transform p2’ by rw [Boehm_transform_def, Abbr ‘p2’, EVERY_GENLIST]
 (* p2 can be rewritten to an ISUB *)
 >> qabbrev_tac ‘sub = \k. REVERSE (GENLIST (\i. (P,y i)) k)’
 >> Know ‘!t. apply p2 t = t ISUB sub k’
 >- (simp [Abbr ‘p2’, Abbr ‘sub’] \\
     Q.SPEC_TAC (‘k’, ‘j’) \\
     Induct_on ‘j’ >- rw [] \\
     rw [GENLIST, REVERSE_SNOC])
 >> DISCH_TAC
 (* properties of ‘sub’ (iterated substitution) *)
 >> Know ‘!j. DOM (sub j) = IMAGE y (count j) /\ FVS (sub j) = {}’
 >- (simp [Abbr ‘sub’] \\
     Induct_on ‘j’ >- rw [DOM_DEF, FVS_DEF] \\
     rw [GENLIST, REVERSE_SNOC, DOM_DEF, FVS_DEF, COUNT_SUC] >- SET_TAC [] \\
     rw [Abbr ‘P’, FV_permutator])
 >> DISCH_TAC
 >> Know ‘!j t. t IN DOM (sub j) ==> VAR t ISUB (sub j) = P’
 >- (Induct_on ‘j’ >- rw [Abbr ‘sub’] >> rw [] \\
     Know ‘P ISUB sub j = P’
     >- (Q.SPEC_TAC (‘j’, ‘j'’) \\
         Induct_on ‘j'’ >> fs [GENLIST, REVERSE_SNOC, Abbr ‘sub’] \\
         Suff ‘[P/y j'] P = P’ >- rw [] \\
         MATCH_MP_TAC lemma14b >> rw [Abbr ‘P’, FV_permutator]) >> DISCH_TAC \\
     reverse (Cases_on ‘y x IN DOM (sub j)’)
     >- (POP_ASSUM MP_TAC >> simp [] \\
         DISCH_THEN (MP_TAC o (Q.SPEC ‘x’)) >> rw [] \\
        ‘x = j’ by rw [] >> POP_ORW \\
         rfs [Abbr ‘sub’, GENLIST, REVERSE_SNOC]) \\
     rfs [Abbr ‘sub’, GENLIST, REVERSE_SNOC] \\
     rename1 ‘y x = y z’ \\
     Cases_on ‘y z = y j’ >> rw [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘z’ >> art [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o Q.SPEC ‘k’)
 >> Q.PAT_X_ASSUM ‘!j. DOM (sub j) = IMAGE y (count j) /\ FVS (sub j) = {}’
      (STRIP_ASSUME_TAC o Q.SPEC ‘k’)
 >> qabbrev_tac ‘ss = sub k’
 (* NOTE: Now we have a list of M1's whose children size is bounded by d_max.
    In the worst case, ‘P d_max @* M1 i’ will leave d_max+1 variable bindings
    at most (in this case, ‘args i = 0 /\ n i = n_max’), and to finally get a
   "is_ready" term, we should apply a fresh list of d_max+1 variables (l).
  *)
 >> Q_TAC (NEWS_TAC (“xs :string list”, “SUC d_max”)) ‘X UNION Y UNION set vs’
 (* p3 is the maximal possible fresh list to be applied after the permutator *)
 >> qabbrev_tac ‘p3 = MAP rightctxt (REVERSE (MAP VAR xs))’
 >> ‘Boehm_transform p3’ by rw [Abbr ‘p3’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* pre-final stage *)
 >> Q.EXISTS_TAC ‘p3 ++ p2 ++ p1’
 >> CONJ_TAC
 >- (MATCH_MP_TAC Boehm_transform_APPEND >> art [] \\
     MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> ‘Boehm_transform (p3 ++ p2 ++ p1)’
       by (rpt (MATCH_MP_TAC Boehm_transform_APPEND >> art []))
 >> qabbrev_tac ‘pi = p3 ++ p2 ++ p1’
 (* NOTE: requirements for ‘Z’

    1. y i IN Z /\ BIGUNION (IMAGE FV (set (args i))) SUBSET Z
    2. DISJOINT (set xs) Z
    3. Z SUBSET X UNION RANK (SUC r)
  *)
 >> qabbrev_tac ‘Z = Y UNION set vs’ (* or ‘X UNION RANK r UNION (set vs)’ *)
 >> ‘DISJOINT (set xs) Z’ by rw [Abbr ‘Z’, DISJOINT_UNION']
 (* FV properties of the head variable y (and children args) *)
 >> Know ‘!i. i < k ==> y i IN Z /\
                        BIGUNION (IMAGE FV (set (args i))) SUBSET Z’
 >- (NTAC 2 STRIP_TAC \\
     qabbrev_tac ‘Z' = FV (M i) UNION set vs’ \\
     Suff ‘y i IN Z' /\ BIGUNION (IMAGE FV (set (args i))) SUBSET Z'’
     >- (Suff ‘Z' SUBSET Z’ >- PROVE_TAC [SUBSET_DEF] \\
         Q.PAT_X_ASSUM ‘Y SUBSET X UNION RANK r’ MP_TAC \\
         simp [Abbr ‘Z'’, Abbr ‘Z’, Abbr ‘Y’] \\
         rw [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNION] \\
         DISJ1_TAC \\
         Q.EXISTS_TAC ‘M i’ >> art [] \\
         rw [Abbr ‘M’, EL_MEM]) \\
  (* applying principle_hnf_FV_SUBSET' *)
     Know ‘FV (M0 i) SUBSET FV (M i)’
     >- (SIMP_TAC std_ss [Abbr ‘M0’, o_DEF] \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> rw []) \\
     qunabbrev_tac ‘Z'’ \\
     Suff ‘y i IN FV (M0 i) UNION set vs /\
           BIGUNION (IMAGE FV (set (args i))) SUBSET
           FV (M0 i) UNION set vs’
     >- SET_TAC [] \\
     Know ‘FV (M1 i) SUBSET FV (M0 i @* MAP VAR vs)’
     >- (‘M1 i = principle_hnf (M0 i @* MAP VAR vs)’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
        ‘M0 i @* MAP VAR vs = apply p1 (M0 i)’
            by rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt'] >> POP_ORW \\
         Suff ‘solvable (M1 i)’ >- METIS_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf \\
         rw [GSYM appstar_APPEND, hnf_appstar]) \\
     REWRITE_TAC [FV_appstar_MAP_VAR] \\
     Know ‘y i IN FV (M1 i) /\
           BIGUNION (IMAGE FV (set (args i))) SUBSET FV (M1 i)’
     >- (rw [FV_appstar] >> SET_TAC []) \\
     rpt STRIP_TAC >- METIS_TAC [SUBSET_DEF] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV (M1 i)’ >> art [])
 >> DISCH_TAC
 >> Know ‘Z SUBSET X UNION RANK r’
 >- (rw [Abbr ‘Z’, UNION_SUBSET] \\
     Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw [])
 >> DISCH_TAC
 (* NOTE: now, before proving ‘EVERY is_ready' ...’, (for future subgoals) we
    need to calculute the principle_hnf of ‘apply pi (EL i Ms)’ for any i < k.

   ‘args'’ is the possibly substituted version of ‘args’.
  *)
 >> qabbrev_tac ‘args' = \i. MAP (\t. t ISUB ss) (args i)’
 (* abbreviate the tail term list after applying p2 *)
 >> qabbrev_tac ‘args2 = \i. MAP (\t. t ISUB ss) (DROP (n i) (MAP VAR vs))’
 (* calculating ‘apply p2 (M1 i)’ *)
 >> Know ‘!i. i < k ==> apply p2 (M1 i) = P @* args' i @* args2 i’
 >- rw [Abbr ‘args'’, Abbr ‘args2’, GSYM appstar_APPEND, MAP_APPEND, appstar_ISUB]
 >> DISCH_TAC
 (* calculating ‘apply p2 ...’ until reaching a hnf *)
 >> Know ‘!i. i < k ==> apply p3 (P @* args' i @* args2 i) =
                        P @* args' i @* args2 i @* MAP VAR xs’
 >- rw [Abbr ‘p3’, Boehm_apply_MAP_rightctxt']
 (* preparing for permutator_hreduce_more (no DISCH_TAC for above Know) *)
 >> qabbrev_tac ‘l = \i. args' i ++ args2 i ++ MAP VAR xs’
 >> ASM_SIMP_TAC bool_ss [GSYM appstar_APPEND, APPEND_ASSOC]
 (* now l appears in the goal *)
 >> REWRITE_TAC [appstar_APPEND]
 >> ‘!i. LENGTH (l i) = m i + (n_max - n i) + SUC d_max’
       by rw [Abbr ‘l’, Abbr ‘m’, Abbr ‘args2’, Abbr ‘args'’, Abbr ‘d_max’]
 >> ‘!i. d_max < LENGTH (l i)’ by rw []
 (* applying TAKE_DROP_SUC to break l into 3 pieces *)
 >> MP_TAC
      (Q.GEN ‘i’
        (ISPECL [“d_max :num”, “l (i :num) :term list”] (GSYM TAKE_DROP_SUC)))
 >> simp [] >> Rewr'
 >> REWRITE_TAC [appstar_APPEND, appstar_SING]
 (* The segmentation of list l(i) - apply (p3 ++ p2 ++ p1) (M i)
 |<-- m(i)<= d -->|<-- n_max-n(i) -->|<-------------- SUC d_max -------------->|
 |----- args' ----+----- args2 ------+-------------- MAP VAR xs ---------------|
 |------------------------------------ l --------------------------------------|
 |                                   |<-j->|
 |<-------- d_max = d + n_max ---------->| b
 |------------------- Ns ----------------+-+--------------- tl ----------------|
 |<-------------- d_max+1 ---------------->|
  *)
 >> qabbrev_tac ‘Ns = \i. TAKE d_max (l i)’
 >> qabbrev_tac ‘B  = \i. EL d_max (l i)’
 >> simp [] (* this put Ns and B in use *)
 >> qabbrev_tac ‘j  = \i. d_max - LENGTH (args' i ++ args2 i)’
 >> ‘!i. j i < LENGTH xs’ by rw [Abbr ‘j’, Abbr ‘args'’, Abbr ‘args2’, Abbr ‘d_max’]
 >> Know ‘!i. i < k ==> ?b. EL (j i) xs = b /\ B i = VAR b’
 >- (rw [Abbr ‘B’, Abbr ‘l’] \\
     Suff ‘EL d_max (args' i ++ args2 i ++ MAP VAR xs) = EL (j i) (MAP VAR xs)’
     >- rw [EL_MAP] \\
     SIMP_TAC bool_ss [Abbr ‘j’] \\
     MATCH_MP_TAC EL_APPEND2 \\
     rw [Abbr ‘args'’, Abbr ‘args2’, Abbr ‘d_max’] \\
     MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO >> rw [] \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> m i <= d’ MP_TAC \\
     simp [Abbr ‘m’])
 >> simp [EXT_SKOLEM_THM']
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘b’ STRIP_ASSUME_TAC) (* this asserts ‘b’ *)
 >> qabbrev_tac ‘tl = \i. DROP (SUC d_max) (l i)’
 >> simp []
 >> DISCH_TAC (* store ‘!i. i < k ==> apply p3 ...’ *)
 (* applying permutator_hreduce_more, it clearly reduces to a hnf *)
 >> Know ‘!i. i < k ==>
              P @* Ns i @@ VAR (b i) @* tl i -h->* VAR (b i) @* Ns i @* tl i’
 >- (RW_TAC std_ss [Abbr ‘P’] \\
     MATCH_MP_TAC permutator_hreduce_more >> rw [Abbr ‘Ns’])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> apply pi (M i) == VAR (b i) @* Ns i @* tl i’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply pi (M0 i)’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] \\
                  SIMP_TAC std_ss [Abbr ‘M0’] \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principle_hnf' >> rw []) \\
     Q.PAT_X_ASSUM ‘Boehm_transform pi’ K_TAC \\
     qunabbrev_tac ‘pi’ \\
     ONCE_REWRITE_TAC [Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply (p3 ++ p2) (M1 i)’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> rw [] \\
                  MATCH_MP_TAC Boehm_transform_APPEND >> art []) \\
     ASM_SIMP_TAC std_ss [Boehm_apply_APPEND] \\
     MATCH_MP_TAC hreduces_lameq >> rw [])
 >> DISCH_TAC
 (* calculating ‘principle_hnf (apply pi (M i))’ (hard) *)
 >> Know ‘!i. i < k ==>
              principle_hnf (apply pi (M i)) = VAR (b i) @* Ns i @* tl i’
 >- (rpt STRIP_TAC \\
     Know ‘MAP (\t. t ISUB ss) (MAP VAR xs) = MAP VAR xs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC ISUB_VAR_FRESH >> rw [GSYM DOM_ALT_MAP_SND] \\
         simp [IN_IMAGE, IN_COUNT, Once DISJ_SYM] \\
         STRONG_DISJ_TAC (* push ‘a < k’ *) \\
         rename1 ‘EL x xs <> y a’ \\
         CCONTR_TAC \\
        ‘y a IN Z’ by rw [] \\
         Q.PAT_X_ASSUM ‘DISJOINT (set xs) Z’ MP_TAC \\
         rw [DISJOINT_ALT] \\
         Q.EXISTS_TAC ‘EL x xs’ >> rw [EL_MEM]) >> DISCH_TAC \\
  (* NOTE: This MP_TAC is for applying principle_hnf_denude_thm later. From
     now on, both ‘apply pi M == ...’ and ‘principle_hnf (apply pi M) = ...’
     are simplified in parallel.
   *)
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply pi (M i) == _’
       (fn th => MP_TAC (MATCH_MP th (ASSUME “i < (k :num)”))) \\
     Q.PAT_X_ASSUM ‘Boehm_transform pi’ K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p3’ K_TAC \\
  (* NOTE: No need to unabbrev ‘p2’ here since ‘apply p2 t = t ISUB sub k’ *)
     ASM_SIMP_TAC std_ss [Abbr ‘pi’, Boehm_apply_APPEND, Abbr ‘p1’, Abbr ‘p3’] \\
     FULL_SIMP_TAC bool_ss [Boehm_apply_MAP_rightctxt'] \\
  (* stage work *)
    ‘(M i @* MAP VAR vs ISUB ss) @* MAP VAR xs =
     (M i @* MAP VAR vs @* MAP VAR xs) ISUB ss’ by rw [appstar_ISUB] >> POP_ORW \\
     DISCH_TAC (* store ‘M i @* MAP VAR vs @* MAP VAR xs ISUB sub k == ...’ *) \\
  (* rewriting RHS to principle_hnf of ISUB *)
     Know ‘VAR (b i) @* Ns i @* tl i =
           principle_hnf (P @* args' i @* args2 i @* MAP VAR xs)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
        ‘hnf (VAR (b i) @* Ns i @* tl i)’ by rw [GSYM appstar_APPEND, hnf_appstar] \\
         Suff ‘solvable (P @* args' i @* args2 i @* MAP VAR xs)’
         >- (METIS_TAC [principle_hnf_thm']) \\
         Suff ‘solvable (VAR (b i) @* Ns i @* tl i) /\
               P @* Ns i @@ VAR (b i) @* tl i == VAR (b i) @* Ns i @* tl i’
         >- (METIS_TAC [lameq_solvable_cong]) \\
         reverse CONJ_TAC >- (MATCH_MP_TAC hreduces_lameq >> rw []) \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> art []) >> Rewr' \\
     Know ‘P @* args' i @* args2 i @* MAP VAR xs = M1 i @* MAP VAR xs ISUB ss’
     >- (REWRITE_TAC [appstar_ISUB, Once EQ_SYM_EQ] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply p2 (M1 i) = P @* args' i @* args2 i’
           (fn th => MP_TAC (MATCH_MP (GSYM (Q.SPEC ‘i’ th))
                                      (ASSUME “i < k :num”))) >> Rewr' \\
         Q.PAT_X_ASSUM ‘!t. apply p2 t = t ISUB ss’ (ONCE_REWRITE_TAC o wrap) \\
         AP_TERM_TAC >> art []) >> Rewr' \\
  (* applying principle_hnf_ISUB_cong *)
     MATCH_MP_TAC principle_hnf_ISUB_cong \\
     CONJ_TAC (* has_hnf #1 *)
     >- (simp [GSYM solvable_iff_has_hnf, GSYM appstar_APPEND] \\
         Know ‘M0 i == M i’
         >- (SIMP_TAC std_ss [Abbr ‘M0’] \\
             MATCH_MP_TAC lameq_principle_hnf' >> rw []) >> DISCH_TAC \\
        ‘M0 i @* (MAP VAR vs ++ MAP VAR xs) ==
          M i @* (MAP VAR vs ++ MAP VAR xs)’ by rw [lameq_appstar_cong] \\
         Suff ‘solvable (M0 i @* (MAP VAR vs ++ MAP VAR xs))’
         >- PROVE_TAC [lameq_solvable_cong] \\
         NTAC 2 (POP_ASSUM K_TAC) \\
         REWRITE_TAC [appstar_APPEND] \\
         qabbrev_tac ‘M0' = M0 i @* MAP VAR vs’ \\
        ‘M0' == M1 i’ by rw [Abbr ‘M0'’] \\
        ‘M0' @* MAP VAR xs == M1 i @* MAP VAR xs’ by rw [lameq_appstar_cong] \\
         Suff ‘solvable (M1 i @* MAP VAR xs)’ >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf #2 *)
     >- (REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Suff ‘solvable (VAR (b i) @* Ns i @* tl i)’
         >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf # 3 *)
     >- (simp [appstar_ISUB] \\
        ‘MAP (\t. t ISUB ss) (args i) = args' i’ by rw [Abbr ‘args'’] \\
         POP_ORW \\
         ASM_SIMP_TAC bool_ss [has_hnf_thm] \\
         Q.EXISTS_TAC ‘VAR (b i) @* Ns i @* tl i’ >> rw [] \\
         rw [hnf_appstar, GSYM appstar_APPEND]) \\
     ASM_SIMP_TAC std_ss [] (* rewrite M1 i *) \\
    ‘MAP VAR vs = TAKE (n i) (MAP VAR vs) ++ DROP (n i) (MAP VAR vs)’
       by rw [TAKE_DROP] \\
     POP_ASSUM
       (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap) \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘A = M i @* TAKE (n i) (MAP VAR vs)’ \\
     qabbrev_tac ‘A' = VAR (y i) @* args i’ \\
     REWRITE_TAC [GSYM appstar_APPEND] \\
     qabbrev_tac ‘C = DROP (n i) (MAP VAR vs) ++ MAP VAR xs’ \\
     qunabbrevl_tac [‘A’, ‘A'’] \\
     REWRITE_TAC [GSYM MAP_TAKE] \\
  (* applying principle_hnf_denude_thm, finally *)
     MATCH_MP_TAC principle_hnf_denude_thm >> simp [] \\
     CONJ_TAC (* ALL_DISTINCT *)
     >- (MATCH_MP_TAC ALL_DISTINCT_TAKE >> art []) \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set vs’ \\
     reverse CONJ_TAC
     >- (rw [SUBSET_DEF] \\
         MATCH_MP_TAC MEM_TAKE >> Q.EXISTS_TAC ‘n i’ >> art []) \\
     MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘Y’ >> art [] \\
     rw [SUBSET_DEF, Abbr ‘Y’] \\
     Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
     Q.EXISTS_TAC ‘M i’ >> art [] \\
     rw [Abbr ‘M’, EL_MEM])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!i. i < k ==> solvable (apply pi (M i))’
 >- (rpt STRIP_TAC \\
     Suff ‘solvable (VAR (b i) @* Ns i @* tl i)’
     >- METIS_TAC [lameq_solvable_cong] \\
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf \\
     rw [hnf_appstar, GSYM appstar_APPEND])
 >> DISCH_TAC
 >> CONJ_TAC (* EVERY is_ready' ... *)
 >- (rpt (Q.PAT_X_ASSUM ‘Boehm_transform _’ K_TAC) \\
     simp [EVERY_EL, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
  (* now expanding ‘is_ready’ using [is_ready_alt] *)
     ASM_SIMP_TAC std_ss [is_ready_alt'] \\
     qexistsl_tac [‘b i’, ‘Ns i ++ tl i’] \\
  (* subgoal: apply pi (M i) -h->* VAR (b i) @* (Ns i ++ tl i) *)
     CONJ_TAC
     >- (REWRITE_TAC [appstar_APPEND] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> principle_hnf (apply pi (M i)) = _’
           (fn th => MP_TAC (MATCH_MP th (ASSUME “i < k:num”))) \\
         rw [principle_hnf_thm']) \\
  (* final goal (is_ready): EVERY (\e. b # e) ... *)
     Q.PAT_X_ASSUM ‘!i. i < k ==> principle_hnf (apply pi (M i)) = _’ K_TAC \\
     ASM_SIMP_TAC list_ss [EVERY_EL] \\
  (* easier goal first *)
     reverse CONJ_TAC (* b i # EL n (tl i) *)
     >- (Q.X_GEN_TAC ‘a’ >> STRIP_TAC \\
         qabbrev_tac ‘l1 = args' i ++ args2 i’ \\
         Know ‘LENGTH l1 <= d_max’
         >- (rw [Abbr ‘l1’, Abbr ‘args'’, Abbr ‘args2’, Abbr ‘d_max’] \\
             MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO >> rw [] \\
             Q.PAT_X_ASSUM ‘!i. i < k ==> m i <= d’ MP_TAC \\
             simp [Abbr ‘m’]) >> DISCH_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply pi (M i) == _’ K_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply p3 _ = _’      K_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply p2 _ = _’      K_TAC \\
         Q.PAT_X_ASSUM ‘a < LENGTH (tl i)’ MP_TAC \\
      (* applying DROP_APPEND2 *)
         Know ‘tl i = DROP (SUC (j i)) (MAP VAR xs)’
         >- (rw [Abbr ‘tl’, Abbr ‘l’] \\
            ‘LENGTH l1 <= SUC d_max’ by rw [] \\
             ASM_SIMP_TAC std_ss [DROP_APPEND2] \\
             Suff ‘SUC d_max - LENGTH l1 = SUC (j i)’ >- rw [] \\
             ASM_SIMP_TAC arith_ss [Abbr ‘j’]) >> Rewr' \\
         simp [] >> DISCH_TAC (* a < d_max + ... *) \\
         Know ‘EL a (DROP (SUC (j i)) (MAP VAR xs :term list)) =
               EL (a + SUC (j i)) (MAP VAR xs)’
         >- (MATCH_MP_TAC EL_DROP >> rw []) >> Rewr' \\
         simp [EL_MAP] \\
        ‘b i = EL (j i) xs’ by rw [] >> POP_ORW \\
         SPOSE_NOT_THEN (STRIP_ASSUME_TAC o REWRITE_RULE []) \\
         Suff ‘EL (j i) xs = EL (a + SUC (j i)) xs <=> j i = a + SUC (j i)’
         >- rw [] \\
         MATCH_MP_TAC ALL_DISTINCT_EL_IMP >> rw []) \\
  (* final goal, only slightly harder *)
     Q.X_GEN_TAC ‘a’ >> DISCH_TAC \\
  (* cleanup useless assumptions and abbreviations *)
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply pi (M i) == _’ K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply p3 _ = _’      K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply p2 _ = _’      K_TAC \\
     Q.PAT_X_ASSUM ‘!t. apply p2 t = t ISUB ss’     K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply p1 _ == _’     K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> P @* Ns i @@ VAR (b i) @* tl i -h->* _’ K_TAC \\
     qunabbrevl_tac [‘pi’, ‘p1’, ‘p2’, ‘p3’] \\
  (* first case *)
     Cases_on ‘a < LENGTH (args' i)’
     >- (Q.PAT_X_ASSUM ‘a < LENGTH (Ns i)’ MP_TAC \\
         simp [Abbr ‘Ns’, LENGTH_TAKE] \\
         DISCH_TAC (* a < d_max *) \\
         simp [EL_TAKE] \\
         Know ‘EL a (l i) = EL a (args' i)’
         >- (SIMP_TAC std_ss [Abbr ‘l’, GSYM APPEND_ASSOC] \\
             MATCH_MP_TAC EL_APPEND1 >> art []) >> Rewr' \\
         Suff ‘b i # EL a (args i)’
         >- (Suff ‘FV (EL a (args' i)) SUBSET FV (EL a (args i))’ >- SET_TAC [] \\
             Q.PAT_X_ASSUM ‘a < LENGTH (args' i)’ MP_TAC \\
             simp [Abbr ‘args'’, EL_MAP] >> DISCH_TAC \\
             MATCH_MP_TAC FV_ISUB_SUBSET >> art []) \\
         Know ‘b i NOTIN Z’
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs) Z’ MP_TAC \\
             rw [DISJOINT_ALT] \\
             POP_ASSUM MATCH_MP_TAC \\
            ‘b i = EL (j i) xs’ by rw [] >> POP_ORW \\
             rw [EL_MEM]) \\
         Suff ‘FV (EL a (args i)) SUBSET Z’ >- SET_TAC [] \\
         Know ‘BIGUNION (IMAGE FV (set (args i))) SUBSET Z’ >- rw [] \\
         REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] \\
         DISCH_THEN MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘EL a (args i)’ >> rw [MEM_EL] \\
         Q.EXISTS_TAC ‘a’ \\
         Q.PAT_X_ASSUM ‘a < LENGTH (args' i)’ MP_TAC \\
         rw [Abbr ‘args'’]) \\
  (* 2nd case *)
     Cases_on ‘a < LENGTH (args' i) + LENGTH (args2 i)’
     >- (Q.PAT_X_ASSUM ‘a < LENGTH (Ns i)’ MP_TAC \\
         simp [Abbr ‘Ns’, LENGTH_TAKE] \\
         DISCH_TAC (* a < d_max *) \\
         simp [EL_TAKE] \\
         Know ‘EL a (l i) = EL (a - LENGTH (args' i)) (args2 i)’
         >- (SIMP_TAC std_ss [Abbr ‘l’, GSYM APPEND_ASSOC] \\
             qabbrev_tac ‘l2 = args2 i ++ MAP VAR xs’ \\
             Know ‘EL a (args' i ++ l2) = EL (a - LENGTH (args' i)) l2’
             >- (MATCH_MP_TAC EL_APPEND2 >> rw []) >> Rewr' \\
             qunabbrev_tac ‘l2’ \\
             MATCH_MP_TAC EL_APPEND1 >> rw []) >> Rewr' \\
         Know ‘b i NOTIN Z’
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs) Z’ MP_TAC \\
             rw [DISJOINT_ALT] \\
             POP_ASSUM MATCH_MP_TAC \\
            ‘b i = EL (j i) xs’ by rw [] >> POP_ORW \\
             rw [EL_MEM]) \\
         qabbrev_tac ‘a' = a - LENGTH (args' i)’ \\
         Suff ‘FV (EL a' (args2 i)) SUBSET Z’ >- SET_TAC [] \\
         Suff ‘FV (EL a' (args2 i)) SUBSET set vs’
         >- (qunabbrev_tac ‘Z’ >> SET_TAC []) \\
        ‘a' < LENGTH (args2 i)’ by rw [Abbr ‘a'’] \\
         Q.PAT_X_ASSUM ‘a < LENGTH (args' i) + LENGTH (args2 i)’ MP_TAC \\
         Q.PAT_X_ASSUM ‘a' < LENGTH (args2 i)’ MP_TAC \\
         qunabbrev_tac ‘args2’ \\
         simp [EL_MAP, LENGTH_DROP] >> NTAC 2 DISCH_TAC \\
         qabbrev_tac ‘a'' = EL a' (DROP (n i) (MAP VAR vs :term list))’ \\
         MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV a''’ \\
         CONJ_TAC >- (MATCH_MP_TAC FV_ISUB_SUBSET >> art []) \\
         qunabbrev_tac ‘a''’ \\
         qabbrev_tac ‘ls = MAP VAR vs’ \\
         Know ‘a' + n i < LENGTH ls’
         >- (‘a' + n i < n_max’ by rw [] \\
             MATCH_MP_TAC LESS_LESS_EQ_TRANS \\
             Q.EXISTS_TAC ‘n_max’ >> art [] \\
             simp [Abbr ‘ls’, Abbr ‘d_max’]) >> DISCH_TAC \\
         Know ‘EL a' (DROP (n i) ls) = EL (a' + n i) ls’
         >- (MATCH_MP_TAC EL_DROP >> art []) >> Rewr' \\
         simp [Abbr ‘ls’, SUBSET_DEF, EL_MAP, EL_MEM]) \\
  (* 3rd case *)
     Q.PAT_X_ASSUM ‘a < LENGTH (Ns i)’ MP_TAC \\
     simp [Abbr ‘Ns’, LENGTH_TAKE] \\
     DISCH_TAC (* a < d_max *) \\
     simp [EL_TAKE] \\
     qabbrev_tac ‘ls = MAP VAR xs’ \\
     Know ‘EL a (l i) = EL (a - LENGTH (args' i ++ args2 i)) ls’
     >- (SIMP_TAC std_ss [Abbr ‘l’] \\
         qabbrev_tac ‘l1 = args' i ++ args2 i’ \\
         MATCH_MP_TAC EL_APPEND2 >> rw [Abbr ‘l1’]) >> Rewr' \\
     simp [] \\
     qabbrev_tac ‘a' = a - (LENGTH (args' i) + LENGTH (args2 i))’ \\
    ‘a' < j i’ by simp [Abbr ‘a'’, Abbr ‘j’] \\
     Know ‘a' < LENGTH xs’
     >- (MATCH_MP_TAC LESS_TRANS \\
         Q.EXISTS_TAC ‘j i’ >> rw []) >> DISCH_TAC \\
     rw [Abbr ‘ls’, EL_MAP] \\
    ‘b i = EL (j i) xs’ by rw [] >> POP_ORW \\
     SPOSE_NOT_THEN (STRIP_ASSUME_TAC o REWRITE_RULE []) \\
     Suff ‘EL (j i) xs = EL a' xs <=> j i = a'’ >- rw [] \\
     MATCH_MP_TAC ALL_DISTINCT_EL_IMP >> rw [])
 (* cleanup *)
 >> Q.PAT_X_ASSUM ‘Boehm_transform p1’            K_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform p2’            K_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform p3’            K_TAC
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> apply p1 _ == _’ K_TAC
 >> Q.PAT_X_ASSUM ‘!t. apply p2 t = t ISUB ss’    K_TAC
 >> Q.PAT_X_ASSUM ‘!t. i < k ==> apply p2 _ = _’  K_TAC
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> apply p3 _ = _’  K_TAC
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> _ -h->* _’       K_TAC
 (* This subgoal was due to modifications of agree_upto_def. It's still kept
    in case this extra subgoal may be later needed.

    NOTE: This subgoal is still true even if the antecedent

      EVERY (\M. subterm X M p r <> NONE) Ms

    is weaken to

      EVERY (\M. p IN ltree_paths (BT' X M r)) Ms
  *)
 >> Know ‘!i. i < k ==> p IN ltree_paths (BT' X (apply pi (M i)) r)’
 >- (rpt STRIP_TAC \\
     simp [BT_def, BT_generator_def, Once ltree_unfold,
           GSYM appstar_APPEND, LAMl_size_appstar, ltree_paths_def,
           LMAP_fromList, MAP_MAP_o] \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> p IN ltree_paths (BT' X (M i) r)’ drule \\
     simp [BT_def, BT_generator_def, Once ltree_unfold, ltree_paths_def,
           LMAP_fromList, MAP_MAP_o] \\
     simp [GSYM BT_def] \\
     qabbrev_tac ‘ys = TAKE (n i) vs’ \\
    ‘ALL_DISTINCT ys’
       by (qunabbrev_tac ‘ys’ >> MATCH_MP_TAC ALL_DISTINCT_TAKE >> art []) \\
    ‘LENGTH ys = n i’
       by (qunabbrev_tac ‘ys’ \\
           MATCH_MP_TAC LENGTH_TAKE >> art [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “(n :num -> num) i”)) ‘X’ \\
     Know ‘DISJOINT (set vs) (set zs)’
     >- (qunabbrev_tac ‘zs’ \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘RANK r’ >> rw [DISJOINT_RANK_RNEWS'] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘ROW 0’ \\
         CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
         MATCH_MP_TAC ROW_SUBSET_RANK >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (set zs)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ >> art [] \\
         rw [Abbr ‘ys’, LIST_TO_SET_TAKE]) >> DISCH_TAC \\
     qabbrev_tac ‘t = VAR (y i) @* args i’ \\
  (* applying for principle_hnf_tpm_reduce *)
     Know ‘principle_hnf (LAMl ys t @* MAP VAR zs) = tpm (ZIP (ys,zs)) t’
     >- (‘hnf t’ by rw [Abbr ‘t’, hnf_appstar] \\
         MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n i’] >> simp [] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘Z’ >> art [] \\
         rw [Abbr ‘t’, FV_appstar]) >> Rewr' \\
     simp [Abbr ‘t’, tpm_appstar] \\
     Cases_on ‘p’ >> fs [] \\
     simp [ltree_lookup, LMAP_fromList, MAP_MAP_o, LNTH_fromList, EL_MAP] \\
     Cases_on ‘h < m i’ >> simp [] \\
     qabbrev_tac ‘pm = ZIP (ys,zs)’ \\
     Know ‘h < LENGTH (Ns i)’
     >- (simp [Abbr ‘Ns’] \\
         Suff ‘m i <= d_max’ >- rw [] \\
         simp [Abbr ‘d_max’] \\
         MATCH_MP_TAC LESS_EQ_TRANS \\
         Q.EXISTS_TAC ‘d’ >> simp []) >> DISCH_TAC \\
     Know ‘EL h (MAP (BT X o (\e. (e,SUC r))) (Ns i) ++
                 MAP (BT X o (\e. (e,SUC r))) (tl i)) =
           EL h (MAP (BT X o (\e. (e,SUC r))) (Ns i))’
     >- (MATCH_MP_TAC EL_APPEND1 >> simp [LENGTH_MAP]) >> Rewr' \\
     simp [EL_MAP] \\
     Know ‘EL h (Ns i) = EL h (args' i)’
     >- (gs [Abbr ‘Ns’, LENGTH_TAKE] \\
         ASM_SIMP_TAC std_ss [EL_TAKE, Abbr ‘l’, GSYM APPEND_ASSOC] \\
         MATCH_MP_TAC EL_APPEND1 >> rw [Abbr ‘args'’]) >> Rewr' \\
     qabbrev_tac ‘N = tpm pm (EL h (args i))’ \\
     qabbrev_tac ‘pm' = REVERSE pm’ \\
    ‘EL h (args' i) = (EL h (args i)) ISUB ss’
       by simp [Abbr ‘args'’, EL_MAP] >> POP_ORW \\
    ‘EL h (args i) = tpm pm' N’ by simp [Abbr ‘pm'’, Abbr ‘N’] >> POP_ORW \\
     Know ‘FV N SUBSET X UNION RANK (SUC r)’
     >- (rw [Abbr ‘N’, Abbr ‘pm'’, FV_tpm, SUBSET_DEF, IN_UNION] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> y i IN Z /\ _’ (MP_TAC o Q.SPEC ‘i’) \\
         rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
         POP_ASSUM (MP_TAC o Q.SPEC ‘lswapstr (REVERSE pm) x’) \\
         impl_tac >- (Q.EXISTS_TAC ‘EL h (args i)’ >> rw [EL_MEM]) \\
         Q.PAT_X_ASSUM ‘lswapstr (REVERSE pm) x IN FV (EL h (args i))’ K_TAC \\
         Know ‘set vs SUBSET RANK (SUC r)’
         >- (qunabbrev_tac ‘vs’ \\
             MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) >> DISCH_TAC \\
         Know ‘set ys SUBSET RANK (SUC r)’
         >- (qunabbrev_tac ‘ys’ \\
             Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
             rw [LIST_TO_SET_TAKE]) >> DISCH_TAC \\
         Know ‘set zs SUBSET RANK (SUC r)’
         >- (qunabbrev_tac ‘zs’ \\
             MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) >> DISCH_TAC \\
         reverse (rw [Abbr ‘Z’, IN_UNION])
      (* lswapstr (REVERSE pm) x IN set vs *)
         >- (DISJ2_TAC \\
             POP_ASSUM MP_TAC >> rw [MEM_EL] \\
             rename1 ‘a < LENGTH vs’ \\
             Know ‘x = lswapstr pm (EL a vs)’
             >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) >> simp []) >> Rewr' \\
             qunabbrev_tac ‘pm’ \\
             MATCH_MP_TAC lswapstr_IN_RANK >> art [] \\
             CONJ_TAC >- (Q.PAT_X_ASSUM ‘set vs SUBSET RANK (SUC r)’ MP_TAC \\
                          rw [SUBSET_DEF, MEM_EL] \\
                          POP_ASSUM MATCH_MP_TAC \\
                          Q.EXISTS_TAC ‘a’ >> art []) \\
             Know ‘set vs SUBSET ROW 0’
             >- (qunabbrev_tac ‘vs’ \\
                 MATCH_MP_TAC RNEWS_SUBSET_ROW >> rw []) >> DISCH_TAC \\
             Know ‘set zs SUBSET ROW r’
             >- (qunabbrev_tac ‘zs’ \\
                 MATCH_MP_TAC RNEWS_SUBSET_ROW >> art []) >> DISCH_TAC \\
             Know ‘DISJOINT (ROW 0) (ROW r)’ >- rw [ROW_DISJOINT] \\
             rw [DISJOINT_ALT] \\
             Suff ‘EL a vs NOTIN ROW r’ >- METIS_TAC [SUBSET_DEF] \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             Suff ‘EL a vs IN set vs’ >- METIS_TAC [SUBSET_DEF] \\
             MATCH_MP_TAC EL_MEM >> art []) \\
      (* lswapstr (REVERSE pm) x IN Y (SUBSET X UNION RANK r) *)
         Know ‘lswapstr (REVERSE pm) x IN X UNION RANK r’ >- ASM_SET_TAC [] \\
         Q.PAT_X_ASSUM ‘lswapstr (REVERSE pm) x IN Y’ K_TAC \\
         RW_TAC std_ss [IN_UNION]
         >- (FULL_SIMP_TAC std_ss [GSYM ssetpm_IN] \\
             DISJ1_TAC \\
             Suff ‘ssetpm pm X = X’ >- DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
             MATCH_MP_TAC ssetpm_14b >> rw [Abbr ‘pm’, MAP_ZIP] \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ >> art [] \\
             rw [Abbr ‘ys’, LIST_TO_SET_TAKE]) \\
         DISJ2_TAC \\
         FULL_SIMP_TAC std_ss [GSYM ssetpm_IN] \\
         qabbrev_tac ‘x' = lswapstr (REVERSE pm) x’ \\
        ‘x = lswapstr pm x'’ by simp [Abbr ‘x'’] >> POP_ORW \\
      (* NOTE: if x' IN set ys (vs, ROW 0), then ‘lswapstr pm x' IN zs’, otherwise
         lswapstr pm x' = x'.
       *)
         Cases_on ‘x' IN set ys’
         >- (qunabbrev_tac ‘pm’ >> MATCH_MP_TAC lswapstr_IN_RANK >> art [] \\
             CONJ_TAC >- METIS_TAC [SUBSET_DEF] \\
             METIS_TAC [DISJOINT_ALT]) \\
         Suff ‘lswapstr pm x' = x'’
         >- (Rewr \\
             Q.PAT_X_ASSUM ‘x IN ssetpm pm (RANK r)’ MP_TAC \\
             simp [Abbr ‘x'’] \\
             Suff ‘RANK r SUBSET RANK (SUC r)’ >- rw [SUBSET_DEF] \\
             rw [RANK_MONO]) \\
         MATCH_MP_TAC lswapstr_14b \\
         POP_ASSUM MP_TAC \\
         Q.PAT_X_ASSUM ‘x IN ssetpm pm (RANK r)’ MP_TAC \\
         simp [Abbr ‘x'’, Abbr ‘pm’, MEM_ZIP, MAP_ZIP] \\
         qabbrev_tac ‘z = lswapstr (REVERSE (ZIP (ys,zs))) x’ \\
         Know ‘DISJOINT (RANK r) (set zs)’ >- rw [Abbr ‘zs’, DISJOINT_RANK_RNEWS] \\
         rw [DISJOINT_ALT]) >> DISCH_TAC \\
  (* applying BT_ltree_paths_tpm *)
     DISCH_TAC \\
     Know ‘ltree_lookup (BT' X (tpm pm' N) (SUC r)) t <> NONE’
     >- (POP_ASSUM MP_TAC \\
         Suff ‘ltree_paths (BT' X N (SUC r)) = ltree_paths (BT' X (tpm pm' N) (SUC r))’
         >- simp [ltree_paths_def, Once EXTENSION] \\
         MATCH_MP_TAC BT_ltree_paths_tpm >> art [] \\
         simp [Abbr ‘pm'’, Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
         reverse CONJ_TAC
         >- (qunabbrev_tac ‘zs’ \\
             MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
         CONJ_TAC >- rw [Abbr ‘ys’, LIST_TO_SET_TAKE] \\
         qunabbrev_tac ‘vs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) \\
     NTAC 2 (POP_ASSUM K_TAC) \\
     fs [Abbr ‘pm'’, Abbr ‘N’] >> T_TAC \\
     qabbrev_tac ‘N = EL h (args i)’ \\
  (* applying BT_ltree_paths_isub_cong *)
    ‘!M. ltree_lookup (BT' X M (SUC r)) t <> NONE <=>
         t IN ltree_paths (BT' X M (SUC r))’ by rw [ltree_paths_def] \\
     POP_ORW >> DISCH_TAC \\
     MATCH_MP_TAC (cj 1 BT_ltree_paths_isub_cong) \\
     qexistsl_tac [‘REVERSE (GENLIST y k)’, ‘P’, ‘d_max’] >> simp [] \\
     CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ \\
         CONJ_TAC
         >- (qunabbrev_tac ‘N’ \\
             Q.PAT_X_ASSUM ‘!i. i < k ==> y i IN Z /\ _’ drule >> STRIP_TAC \\
             Q_TAC (TRANS_TAC SUBSET_TRANS)
                   ‘BIGUNION (IMAGE FV (set (args i)))’ >> art [] \\
             rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
             Q.EXISTS_TAC ‘EL h (args i)’ >> art [] \\
             simp [EL_MEM]) \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ >> art [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘v’ >> simp [MEM_GENLIST] \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘J’ STRIP_ASSUME_TAC) >> POP_ORW \\
         Know ‘y J IN Z’ >- rw [] \\
         Suff ‘Z SUBSET X UNION RANK (SUC r)’ >- rw [SUBSET_DEF] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ >> art [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     CONJ_TAC (* ss = MAP ... *)
     >- (simp [Abbr ‘ss’, Abbr ‘sub’] \\
         simp [MAP_REVERSE, MAP_GENLIST, o_DEF]) \\
  (* current goal: subterm_width N t <= d_max, where
     Abbrev (d_max = d + n_max)
     Abbrev (d = MAX_LIST (MAP (\e. subterm_width e (h::t)) Ms))
   *)
     Know ‘subterm_width (M i) (h::t) <= d’
     >- (qunabbrev_tac ‘d’ \\
         MATCH_MP_TAC MAX_LIST_PROPERTY \\
         rw [MEM_MAP] \\
         Q.EXISTS_TAC ‘M i’ >> rw [Abbr ‘M’] \\
         rw [EL_MEM]) \\
     qabbrev_tac ‘Ms' = args i ++ DROP (n i) (MAP VAR vs)’ \\
  (* applying subterm_width_induction_lemma (the general one) *)
     Suff ‘subterm_width (M i) (h::t) <= d <=>
           m i <= d /\ subterm_width (EL h Ms') t <= d’
     >- (Rewr' \\
         Know ‘EL h Ms' = N’
         >- (simp [Abbr ‘Ms'’, Abbr ‘N’] \\
             MATCH_MP_TAC EL_APPEND1 >> simp []) >> Rewr' \\
         STRIP_TAC \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ >> art [] \\
         simp [Abbr ‘d_max’]) \\
  (* stage work *)
     MATCH_MP_TAC subterm_width_induction_lemma_alt \\
     qexistsl_tac [‘X’, ‘Y’, ‘r’, ‘M0 i’, ‘n i’, ‘n_max’, ‘vs’, ‘M1 i’] \\
     simp [GSYM appstar_APPEND] \\
     CONJ_TAC >- (rw [SUBSET_DEF, Abbr ‘Y’] \\
                  Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
                  Q.EXISTS_TAC ‘M i’ >> art [] \\
                  rw [Abbr ‘M’, EL_MEM]) \\
     MATCH_MP_TAC subterm_imp_ltree_paths >> simp [])
 >> DISCH_TAC
 (* now proving agree_upto *)
 >> (Q.PAT_X_ASSUM ‘agree_upto X Ms p r’ MP_TAC \\
     simp [agree_upto_def, EVERY_MEM] >> STRIP_TAC \\
  (* CONJ_TAC >- (rw [MEM_MAP, MEM_EL] >> rw []) \\ *)
     qx_genl_tac [‘M2'’, ‘N2'’] >> simp [MEM_MAP] \\
     ONCE_REWRITE_TAC [TAUT ‘p /\ q ==> r <=> p ==> q ==> r’] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘M2’ STRIP_ASSUME_TAC) \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘N2’ STRIP_ASSUME_TAC) \\
     Q.PAT_X_ASSUM ‘!M N. MEM M Ms /\ MEM N Ms ==> _’
       (MP_TAC o (Q.SPECL [‘M2’, ‘N2’])) >> simp [] \\
     Q.PAT_X_ASSUM ‘MEM N2 Ms’ MP_TAC \\
     Q.PAT_X_ASSUM ‘MEM M2 Ms’ MP_TAC \\
     simp [MEM_EL] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j1’ STRIP_ASSUME_TAC) \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j2’ STRIP_ASSUME_TAC) \\
     rpt STRIP_TAC (* this asserts q *) \\
     Q.PAT_X_ASSUM ‘!q. q <<= p ==> _’ (MP_TAC o Q.SPEC ‘q’) >> simp [] \\
     Q.PAT_X_ASSUM ‘M2 = M j1’ (rfs o wrap) \\
     Q.PAT_X_ASSUM ‘N2 = M j2’ (rfs o wrap) \\
     Q.PAT_X_ASSUM ‘M2' = apply pi (M j1)’ K_TAC \\
     Q.PAT_X_ASSUM ‘N2' = apply pi (M j2)’ K_TAC \\
     qabbrev_tac ‘M' = \i. apply pi (M i)’ >> simp [] \\
     qabbrev_tac ‘H = \i. VAR (b i) @* Ns i @* tl i’ \\
     Know ‘!i. solvable (H i)’
     >- (rw [Abbr ‘H’, solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) >> DISCH_TAC \\
  (* applying BT_of_principle_hnf *)
     Know ‘BT' X (M' j1) r = BT' X (principle_hnf (M' j1)) r’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_of_principle_hnf \\
         simp [Abbr ‘M'’] \\
         METIS_TAC [lameq_solvable_cong]) >> Rewr' \\
     Know ‘BT' X (M' j2) r = BT' X (principle_hnf (M' j2)) r’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_of_principle_hnf \\
         simp [Abbr ‘M'’] \\
         METIS_TAC [lameq_solvable_cong]) >> Rewr' \\
     simp [Abbr ‘M'’] \\
  (* NOTE: now we are still missing some important connections:
   - ltree_el (BT W M2) q             ~1~ subterm' W M2 q
   - ltree_el (BT W N2) q             ~1~ subterm' W N2 q
   - ltree_el (BT W' (apply pi M2) q  ~1~ subterm' W' (apply pi M2) q
   - ltree_el (BT W' (apply pi N2) q  ~1~ subterm' W' (apply pi N2) q
   - subterm' Z' (apply pi M2) q       ~2~ subterm' W M2 q
   - subterm' Z' (apply pi N2) q       ~2~ subterm' W N2 q

     where the relation ~1~ is to be established by BT_subterm_thm, and ~2~
     follows a similar idea of [Boehm_transform_exists_lemma].

     And the case q = [] is special (and not very easy)
   *)
     Cases_on ‘q = []’
     >- (POP_ORW >> simp [BT_ltree_el_NIL] \\
         Know ‘!i. principle_hnf (H i) = H i’
         >- (rw [Abbr ‘H’] >> MATCH_MP_TAC principle_hnf_reduce \\
             rw [hnf_appstar]) >> Rewr' \\
        ‘!i. LAMl_size (H i) = 0’
           by rw [Abbr ‘H’, GSYM appstar_APPEND, LAMl_size_appstar] \\
         simp [Abbr ‘H’, GSYM appstar_APPEND, hnf_head_appstar] \\
         STRIP_TAC \\
        ‘n j1 = n j2’ by PROVE_TAC [RNEWS_11'] \\
      (* NOTE: It's possible that ‘n j2 = 0’ and thus ys = ys = [] *)
         qabbrev_tac ‘ys = TAKE (n j2) vs’ \\
        ‘ALL_DISTINCT ys’
           by (qunabbrev_tac ‘ys’ \\
               MATCH_MP_TAC ALL_DISTINCT_TAKE >> art []) \\
        ‘LENGTH ys = n j2’
           by (qunabbrev_tac ‘ys’ \\
               MATCH_MP_TAC LENGTH_TAKE >> art [] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
         Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “(n :num -> num) j2”)) ‘X’ \\
         Know ‘DISJOINT (set ys) (set zs)’
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ \\
             reverse CONJ_TAC >- rw [Abbr ‘ys’, LIST_TO_SET_TAKE] \\
             qunabbrev_tac ‘zs’ \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘RANK r’ >> rw [DISJOINT_RANK_RNEWS'] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘ROW 0’ \\
             CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
             MATCH_MP_TAC ROW_SUBSET_RANK >> art []) >> DISCH_TAC \\
         qabbrev_tac ‘t1 = VAR (y j1) @* args j1’ \\
         qabbrev_tac ‘t2 = VAR (y j2) @* args j2’ \\
      (* applying for principle_hnf_tpm_reduce *)
         Know ‘principle_hnf (LAMl ys t1 @* MAP VAR zs) = tpm (ZIP (ys,zs)) t1’
         >- (‘hnf t1’ by rw [Abbr ‘t1’, hnf_appstar] \\
             MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
             MATCH_MP_TAC subterm_disjoint_lemma \\
             qexistsl_tac [‘X’, ‘r’, ‘n j2’] >> simp [] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘Z’ >> art [] \\
             rw [Abbr ‘t1’, FV_appstar]) \\
         DISCH_THEN (fs o wrap) \\
         Know ‘principle_hnf (LAMl ys t2 @* MAP VAR zs) = tpm (ZIP (ys,zs)) t2’
         >- (‘hnf t2’ by rw [Abbr ‘t2’, hnf_appstar] \\
             MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
             MATCH_MP_TAC subterm_disjoint_lemma \\
             qexistsl_tac [‘X’, ‘r’, ‘n j2’] >> simp [] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘Z’ >> art [] \\
             rw [Abbr ‘t2’, FV_appstar]) \\
         DISCH_THEN (fs o wrap) \\
         gs [Abbr ‘t1’, Abbr ‘t2’, tpm_appstar] \\
        ‘LENGTH (l j1) = LENGTH (l j2)’ by rw [Abbr ‘l’] \\
         reverse CONJ_TAC >- simp [Abbr ‘Ns’, Abbr ‘tl’] \\
        ‘b j1 = EL (j j1) xs /\ b j2 = EL (j j2) xs’ by rw [] \\
         NTAC 2 POP_ORW \\
         Suff ‘j j1 = j j2’ >- Rewr \\
         simp [Abbr ‘j’, Abbr ‘args'’, Abbr ‘args2’]) \\
  (* NOTE: ‘solvable (subterm' X (M i) q r)’ only holds when ‘q <<= FRONT p’.
     The case that ‘unsolvable (subterm' X (M i) q r)’ (which implies q = p)
     must be treated specially.

     The plan is to first derive ‘BT' X (M j1) r = bot = BT' X (M j2) r’ and
     then ‘unsolvable (subterm' X (M j2) q r)’. Finally, ‘BT' X t1 r = bot’.

     Anyway, now we have p <> [] /\ q <> [] /\ q <<= p.
   *)
     reverse (Cases_on ‘solvable (subterm' X (M j1) q r)’)
     >- (‘q <<= FRONT p \/ q = p’ by METIS_TAC [IS_PREFIX_FRONT_CASES]
         >- (‘solvable (subterm' X (M j1) q r)’ by METIS_TAC []) \\
         POP_ASSUM (fs o wrap) >> T_TAC \\
         Know ‘unsolvable (subterm' X (M j1) p r) <=>
               ltree_el (BT' X (M j1) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         simp [] >> DISCH_THEN K_TAC \\
         Know ‘unsolvable (subterm' X (M j2) p r) <=>
               ltree_el (BT' X (M j2) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         DISCH_THEN (REWRITE_TAC o wrap o SYM) \\
         DISCH_TAC \\
      (* p <> [] from now on, now applying subterm_isub_cong' *)
         Know ‘!i. i < k ==>
                   subterm X (H i) p r <> NONE /\
                   subterm' X (H i) p r = subterm' X (M i) p r ISUB sub k’
         >- (Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
             Cases_on ‘p’ >> FULL_SIMP_TAC list_ss [] \\
             Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X (H i) (h::t) r’ \\
             Know ‘principle_hnf (H i) = H i’
             >- (MATCH_MP_TAC principle_hnf_reduce \\
                 simp [Abbr ‘H’, GSYM appstar_APPEND, hnf_appstar]) \\
             DISCH_TAC \\
             Know ‘LAMl_size (H i) = 0’
             >- (rw [Abbr ‘H’, LAMl_size_appstar, GSYM appstar_APPEND]) \\
             DISCH_TAC \\
             simp [] \\
             Q.PAT_X_ASSUM ‘!i. i < k ==> h::t IN ltree_paths (BT' X (M i) r)’
                (MP_TAC o Q.SPEC ‘i’) \\
             simp [BT_def, BT_generator_def, Once ltree_unfold] \\
             cheat) >> DISCH_TAC \\
         Know ‘unsolvable (subterm' X (H j1) p r) /\
               unsolvable (subterm' X (H j2) p r)’
         >- (ASM_SIMP_TAC std_ss [] \\
             CONJ_TAC \\ (* 2 subgoals, same tactics *)
             MATCH_MP_TAC unsolvable_ISUB >> art []) >> STRIP_TAC \\
         Know ‘unsolvable (subterm' X (H j1) p r) <=>
               ltree_el (BT' X (H j1) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> art [] \\
             cheat) \\
         simp [] >> DISCH_THEN K_TAC \\
         Know ‘unsolvable (subterm' X (H j2) p r) <=>
               ltree_el (BT' X (H j2) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> art [] \\
             cheat) \\
         simp []) \\
     reverse (Cases_on ‘solvable (subterm' X (M j2) q r)’)
     >- (‘q <<= FRONT p \/ q = p’ by METIS_TAC [IS_PREFIX_FRONT_CASES]
         >- (‘solvable (subterm' X (M j2) q r)’ by METIS_TAC []) \\
         POP_ASSUM (fs o wrap) >> T_TAC \\
         Know ‘unsolvable (subterm' X (M j2) p r) <=>
               ltree_el (BT' X (M j2) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) >> simp [] \\
      (* applying BT_subterm_thm *)
         MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm) \\
         rw [] >> fs [] \\
         rename1 ‘(\(N,r). NONE) z = SOME T’ \\
         Cases_on ‘z’ >> fs []) \\
  (* So they are both solvable. Now comes the dirty assumptions. *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm) \\
     rw [] \\ (* This asserts ‘x’ *)
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     rename1 ‘subterm X (M j1) q r = SOME (N1,r1)’ \\
     rename1 ‘ltree_el (BT' X (M j2) r) q = SOME (SOME (vs1,y1),m1)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs1,y1)’ K_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j2 :num)’, ‘r’] BT_subterm_thm) \\
     rw [] \\ (* This asserts ‘x’ *)
     Cases_on ‘x’ >> fs [] \\
     rename1 ‘subterm X (M j2) q r = SOME (N2,r2)’ \\
     qabbrev_tac ‘n1 = LAMl_size (principle_hnf N1)’ \\
    ‘LAMl_size (principle_hnf N2) = n1’ by PROVE_TAC [RNEWS_11'] \\
     POP_ASSUM (FULL_SIMP_TAC bool_ss o wrap) \\
    ‘n1 = 0 \/ 0 < n1’ by rw []
     >- (POP_ASSUM (fs o wrap) \\
         rfs [Abbr ‘n1’, principle_hnf_stable'] >> T_TAC \\
         qabbrev_tac ‘N1' = principle_hnf N1’ \\
         qabbrev_tac ‘N2' = principle_hnf N2’ \\
         qabbrev_tac ‘y' = hnf_headvar N1'’ \\
         cheat) \\
     cheat)
QED

(*
(* Lemma 10.3.11 (3) [1. p.251]
Theorem agree_upto_lemma_3 :
    !X Ms p. FINITE X /\ EVERY (\e. subterm X e p <> NONE) Ms /\ agree_upto p Ms ==>
             ?pi. Boehm_transform pi /\
                  !M N. MEM M Ns /\ MEM N Ns ==>
                       (subterm_equivalent p M N <=>
                        subterm_equivalent p (apply pi M) (apply pi N))
Proof
    cheat
QED
 *)

(* Definition 10.3.10 (ii) [1, p.251] *)
Definition is_faithful_def :
    is_faithful p Ns pi <=>
      (!X M. MEM M Ns ==>
            (solvable (apply pi M) <=> IS_SOME (ltree_lookup (BT X M) p))) /\
       !M N. MEM M Ns /\ MEM N Ns ==>
            (subterm_equivalent p M N <=> equivalent (apply pi M) (apply pi N))
End

Theorem is_faithful_two :
    !p M N pi.
       is_faithful p [M; N] pi <=>
      (!X. solvable (apply pi M) <=> IS_SOME (ltree_lookup (BT X M) p)) /\
      (!X. solvable (apply pi N) <=> IS_SOME (ltree_lookup (BT X N) p)) /\
      (subterm_equivalent p M N <=> equivalent (apply pi M) (apply pi N))
Proof
    rw [is_faithful_def]
 >> EQ_TAC >> rw [] >> rw [] (* only one goal left *)
 >> MATCH_MP_TAC EQ_TRANS
 >> Q.EXISTS_TAC ‘subterm_equivalent p M M'’
 >> CONJ_TAC
 >- rw [Once subterm_equivalent_comm]
 >> rw [Once equivalent_comm]
QED

(* Proposition 10.3.13 [1, p.253] *)
Theorem agree_upto_thm :
    !Ns p. agree_upto p Ns ==> ?pi. Boehm_transform pi /\ is_faithful p Ns pi
Proof
    cheat
QED
*)

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
 >> qabbrev_tac ‘vs = NEWS (k + 1) (y INSERT FV P UNION FV Q)’
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (y INSERT FV P UNION FV Q)’
      by rw [Abbr ‘vs’, NEWS_def]
 >> qabbrev_tac ‘a = HD vs’
 >> qabbrev_tac ‘bs = DROP 1 vs’
 >> Know ‘LENGTH bs + 1 = LENGTH vs /\ 1 < LENGTH vs’
 >- (‘LENGTH vs = k + 1’ by rw [Abbr ‘vs’, NEWS_def] \\
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
 >> qabbrev_tac ‘Z = NEWS (p + 1) {}’
 >> ‘ALL_DISTINCT Z /\ LENGTH Z = p + 1’ by rw [Abbr ‘Z’, NEWS_def]
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘z = LAST Z’
 >> qabbrev_tac ‘p2 = [[LAMl Z (VAR z)/y]]’
 >> ‘Boehm_transform p2’ by rw [Boehm_transform_def, Abbr ‘p2’]
 >> Know ‘apply p2 (VAR y @* (args1 ++ MAP VAR vs)) == VAR a @* MAP VAR bs’
 >- (simp [Abbr ‘p2’, appstar_SUB] \\
     Know ‘MAP [LAMl Z (VAR z)/y] (MAP VAR vs) = MAP VAR vs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ MP_TAC \\
         rw [DISJOINT_ALT', MEM_EL] >> METIS_TAC []) >> Rewr' \\
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
     rw [GSYM I_thm] \\
     MATCH_MP_TAC lameq_appstar_cong >> rw [lameq_I])
 >> DISCH_TAC
 >> qabbrev_tac ‘b0 = LAST bs’
 >> Know ‘apply p2 (VAR y @* (args2 ++ MAP VAR vs)) == VAR b0’
 >- (simp [Abbr ‘p2’, appstar_SUB] \\
     Know ‘MAP [LAMl Z (VAR z)/y] (MAP VAR vs) = MAP VAR vs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ MP_TAC \\
         rw [DISJOINT_ALT', MEM_EL] >> METIS_TAC []) >> Rewr' \\
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
             MATCH_MP_TAC SNOC_LAST_FRONT' >> rw [Abbr ‘l’]) \\
         MATCH_MP_TAC (GSYM LAST_APPEND_NOT_NIL) >> rw []) >> Rewr' \\
     REWRITE_TAC [appstar_SNOC] \\
     qabbrev_tac ‘t :term = LAM z (VAR z)’ \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘t @@ VAR b0’ \\
     CONJ_TAC >- (MATCH_MP_TAC lameq_APPL \\
                  MATCH_MP_TAC lameq_LAMl_appstar_reduce \\
                  rw [Abbr ‘t’, Abbr ‘args2'’, LENGTH_FRONT] \\
                 ‘LENGTH vs = k + 1’ by rw [Abbr ‘vs’, NEWS_def] >> rw []) \\
     rw [Abbr ‘t’, GSYM I_thm, lameq_I])
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
      CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art []) \\
      rw [Abbr ‘p3’] \\
      MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘f2 P’ \\
      reverse CONJ_TAC >- rw [] \\
      MATCH_MP_TAC solving_transform_lameq >> rw [Abbr ‘f2’],
      (* goal 2 (of 2) *)
      REWRITE_TAC [Boehm_apply_APPEND] \\
      Q.PAT_X_ASSUM ‘apply P1 N1 = _’ (ONCE_REWRITE_TAC o wrap) \\
      MATCH_MP_TAC lameq_TRANS \\
      Q.EXISTS_TAC ‘apply p3 (VAR b0)’ \\
      reverse CONJ_TAC >- rw [Abbr ‘p3’] \\
      MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] ]
QED

Theorem separability_lemma0[local] :
    !M N. solvable (M :term) /\ solvable N /\
          LAMl_size (principle_hnf M) <= LAMl_size (principle_hnf N) ==>
          equivalent M N \/
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    RW_TAC std_ss [equivalent_of_solvables]
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M UNION FV N) /\
     LENGTH vs = MAX n n'’ by rw [Abbr ‘vs’, NEWS_def]
 >> ‘DISJOINT (set vs) (FV M) /\ DISJOINT (set vs) (FV N)’
      by METIS_TAC [DISJOINT_SYM, DISJOINT_UNION]
 (* applying principle_hnf_FV_SUBSET' *)
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs) (FV N0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘FV N’ >> art [] \\
     qunabbrev_tac ‘N0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y1 :string”, “args1 :term list”)) ‘M1’
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs :string list”,
                    “y2 :string”, “args2 :term list”)) ‘N1’
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
 >> ‘VAR y1 = y’  by rw [Abbr ‘y’ , absfree_hnf_head]
 >> ‘VAR y2 = y'’ by rw [Abbr ‘y'’, absfree_hnf_head]
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
     qabbrev_tac ‘Z = NEWS 2 (FV P UNION FV Q)’ \\
    ‘ALL_DISTINCT Z /\ DISJOINT (set Z) (FV P UNION FV Q) /\ LENGTH Z = 2’
       by rw [NEWS_def, Abbr ‘Z’] \\
     qabbrev_tac ‘z1 = EL 0 Z’ \\
     qabbrev_tac ‘z2 = EL 1 Z’ \\
    ‘MEM z1 Z /\ MEM z2 Z’
       by (rw [MEM_EL, Abbr ‘z1’, Abbr ‘z2’] >| (* 2 subgoals *)
           [ Q.EXISTS_TAC ‘0’ >> rw [],
             Q.EXISTS_TAC ‘1’ >> rw [] ]) \\
    ‘z1 <> z2’ by (rw [Abbr ‘z1’, Abbr ‘z2’, ALL_DISTINCT_EL_IMP]) \\
     qabbrev_tac ‘as = NEWS (m + k) (FV P UNION set Z)’ \\
    ‘LENGTH as = m + k /\ DISJOINT (set as) (FV P UNION set Z)’
       by rw [Abbr ‘as’, NEWS_def] \\
     qabbrev_tac ‘as' = NEWS m' (FV Q UNION set Z)’ \\
    ‘LENGTH as' = m' /\ DISJOINT (set as') (FV Q UNION set Z)’
       by rw [Abbr ‘as'’, NEWS_def] \\
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
         Cases_on ‘y2 IN FV P’ \\
         rw [SUBSET_DEF, IN_UNION, Abbr ‘z2’] >> art []) \\
     DISCH_TAC \\
     Know ‘DISJOINT (set as') (FV ([VAR z1/y1] Q))’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV Q UNION set Z’ >> art [] \\
         simp [FV_SUB] \\
         Cases_on ‘y1 IN FV Q’ \\
         rw [SUBSET_DEF, IN_UNION, Abbr ‘z2’] >> art []) \\
     DISCH_TAC \\
  (* stage work *)
     Q.EXISTS_TAC ‘p1 ++ p0’ \\
     CONJ_ASM1_TAC >- rw [Boehm_transform_APPEND] \\
     reverse CONJ_TAC >| (* 2 subgoals, Q part seems easier *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (p1 ++ p0) N0’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘N0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf >> art [GSYM solvable_iff_has_hnf]) \\
    (* eliminating p0 *)
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply p1 N1’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art []) \\
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
       CONJ_TAC
       >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
           POP_ASSUM (REWRITE_TAC o wrap) \\
           qunabbrev_tac ‘M0’ \\
           MATCH_MP_TAC lameq_SYM \\
           MATCH_MP_TAC lameq_principle_hnf >> art [GSYM solvable_iff_has_hnf]) \\
    (* eliminating p0 *)
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply p1 (M1 @* DROP n (MAP VAR vs))’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art []) \\
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
           MATCH_MP_TAC lemma14b >> rw [FV_SUB, IN_UNION] \\
           CCONTR_TAC >> ‘MEM y2 Z’ by METIS_TAC [] \\
           Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
           rw [DISJOINT_ALT'] >> METIS_TAC []) >> Rewr' \\
    (* eliminating f3 *)
       Know ‘f3 ([VAR z2/y2] P) = [VAR z2/y2] P’
       >- (qunabbrev_tac ‘f3’ \\
           MATCH_MP_TAC lemma14b \\
           Suff ‘z1 # P’ >- rw [FV_SUB, IN_UNION] \\
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
      MP_TAC (Q.SPECL [‘y2’, ‘args1'’, ‘args2’, ‘l - m'’]
                      separability_lemma0_case2) \\
      simp [] \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPECL [‘P’, ‘Q’])),
      (* goal 2 (of 2) *)
      MP_TAC (Q.SPECL [‘y2’, ‘args2’, ‘args1'’, ‘m' - l’]
                      separability_lemma0_case2) \\
      simp [] \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPECL [‘Q’, ‘P’])) ]
 (* shared tactics *)
 >> (Q.EXISTS_TAC ‘pi ++ p0’ \\
     CONJ_ASM1_TAC >- rw [Boehm_transform_APPEND] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1.1 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (pi ++ p0) M0’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                    POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘M0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (y' @* args1')’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC Boehm_apply_lameq_cong \\
       Q.PAT_X_ASSUM ‘VAR y2 = y'’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [],
       (* goal 1.2 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (pi ++ p0) N0’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                    POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘N0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (y @* args2)’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC Boehm_apply_lameq_cong \\
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
 >> qabbrev_tac ‘as = NEWS (LENGTH args) (FV P)’
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
 >> CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art [])
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
       by rw [NEWS_def, Abbr ‘as’]
 >> MATCH_MP_TAC lameq_LAMl_appstar_reduce >> rw []
QED

(* Exercise 10.6.9 [1, p.272]. It may avoid using Theorem 10.2.31.

   NOTE: the actual statements have ‘has_benf M /\ has_benf N’
 *)
Theorem distinct_benf_no_subterm_equivalent :
    !M N. benf M /\ benf N /\ M <> N ==> ?p. ~subterm_equivalent p M N
Proof
    cheat
QED

(* Theorem 10.4.2 (i) [1, p.256] *)
Theorem separability_thm :
    !M N. benf M /\ benf N /\ M <> N ==>
         !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    cheat
 (*
    rpt STRIP_TAC
 >> ‘?p. ~subterm_equivalent p M N’
       by METIS_TAC [distinct_benf_no_subterm_equivalent]
 >> Know ‘agree_upto p [M; N]’
 >- (cheat)
 >> DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP agree_upto_thm))
 >> fs [is_faithful_two]
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
  *)
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
 >> CONJ_TAC (* 2 subgoals, same ending tactics *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘apply pi M’ >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘apply pi N’ >> art [] ]
 >> rw [lameq_SYM]
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
 >> MATCH_MP_TAC Boehm_apply_asmlam_cong >> art []
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
Theorem lameta_complete :
    !M N. has_bnf M /\ has_bnf N ==>
          lameta M N \/ ~consistent (conversion (RINSERT (beta RUNION eta) M N))
Proof
    rpt STRIP_TAC
 >> ‘has_benf M /\ has_benf N’ by PROVE_TAC [has_benf_has_bnf]
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
(* NOTE: ‘VAR o renaming s1 s2 r1 r2’ can be used for ‘fsub’.
Definition renaming_def :
    renaming X Y r1 r2 x =
    if x IN X UNION RANK r1 X then
       x
    else
      (let i = index_of X x;
           r = nfst i;
           c = nsnd i;
           r' = r - r1 + r2
       in
         FRESH Y (npair r' c))
End

Theorem renaming_base :
    !X Y r1 r2 M. FV M SUBSET X UNION RANK r1 X ==>
                  fssub (VAR o renaming X Y r1 r2) M = M
Proof
    rw [fssub_def]
 >> MATCH_MP_TAC ssub_14a
 >> rw [FUN_FMAP_DEF]
 >> ‘x IN X UNION RANK r1 X’ by ASM_SET_TAC []
 >> rw [renaming_def]
QED

(* NOTE: Since ‘FV M’ is subset of both X and Y, the new free variables in
  ‘subterm X M p r1’ can (and must) be simultaneously substituted without
   hurting ‘FV M’.

   NOTE: cannot find a suitable statement for induction
 *)
Theorem subterm_renaming_lemma :
    !X Y p M r1 r2.
         FINITE X /\ FV M SUBSET X UNION RANK r1 X /\
         FINITE Y /\ FV M SUBSET Y UNION RANK r2 Y ==>
        (subterm X M p r1 = NONE ==>
         subterm Y (fssub (VAR o renaming X Y r1 r2) M) p r2 = NONE) /\
        (subterm X M p r1 <> NONE ==>
         fssub (VAR o renaming X Y r1 r2) (subterm' X M p r1) =
         subterm' Y (fssub (VAR o renaming X Y r1 r2) M) p r2)
Proof
    qx_genl_tac [‘X’, ‘Y’]
 >> Induct_on ‘p’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (
     simp [subterm_def])
 >> UNBETA_TAC [subterm_alt] “subterm X M (h::p) r1”
 >> UNBETA_TAC [subterm_alt] “subterm Y M (h::p) r2”
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m = m'’ (fs o wrap o SYM)
 >> T_TAC
 >> Cases_on ‘h < m’ >> simp []
 >> qabbrev_tac ‘N  = EL h Ms’
 >> qabbrev_tac ‘N' = EL h Ms'’
 >> ‘FV N  SUBSET X UNION RANK (SUC r1) X /\
     FV N' SUBSET Y UNION RANK (SUC r2) Y’
        by METIS_TAC [subterm_induction_lemma']
 >> Suff ‘fssub (VAR o renaming X Y r1 r2) (subterm' X N p (SUC r1)) =
          fssub (VAR o renaming X Y (SUC r1) (SUC r2))
                (subterm' X N' p (SUC r1))’
 ...
QED
 *)

(*---------------------------------------------------------------------------*
 * FV (free variables) and BV (binding variables) of Boehm trees
 *---------------------------------------------------------------------------*)

(* Definition 10.1.20 [1, p.224]

  ‘BV_of_ltree_node’ directly takes out the binding variable list stored in
   the Boehm tree.

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
val example_10_1_20 = “Branch (SOME ([x; y],z)) [| BT_VAR x; BT_VAR y |]”;

Definition FV_of_ltree_decomp_def :
    FV_of_ltree_decomp (M :boehm_tree) p =
      let node = ltree_el M p in
          if IS_SOME node then
             let (vs,t) = THE (FST (THE node)) in {t} DIFF set vs
          else EMPTY
End

Definition FV_of_ltree_path_def :
    FV_of_ltree_path M p = FV_of_ltree_decomp M p DIFF BV_of_ltree_path M p
End

Definition FV_of_ltree_def :
    FV_of_ltree M = BIGUNION (IMAGE (FV_of_ltree_path M) (ltree_paths M))
End

Overload FV = “FV_of_ltree”

Theorem FV_of_ltree_empty_imp_closed :
    !X M. FV (BT X M) = {} ==> closed M
Proof
    ...
QED
*)

(*---------------------------------------------------------------------------*
 *  Infinite eta reduction for trees
 *---------------------------------------------------------------------------*)

(* A (underlying) "naked" tree has only the structure (i.e. valid paths).

   NOTE: When building an Boehm tree expansion, the naked tree may be used for
   holding the combined set of binding variables up to the current tree node.

Type naked_tree[pp] = “:string set ltree”

(* from a set of ltree paths to a naked ltree.

   NOTE: A typical source of input X is ‘ltree_paths’ of any ltree.
*)
Definition fromPaths_def :
    fromPaths (X :num list set) :naked_tree =
       gen_ltree (\p. ({},SOME (CARD {x | SNOC x p IN X})))
End

(*
Theorem ltree_paths_fromPaths :
    !X. ltree_paths (fromPaths X) = X
Proof
QED

Theorem fromPaths_ltree_paths :
    !(A :naked_tree). fromPaths (ltree_paths A) = A
Proof
QED

(* ‘denude (A :'a ltree)’ (or |A| in textbook) is the underlying naked tree of A *)
Definition denude_def :
    denude = ltree_map (\e. {})
End

Theorem denude_alt :
    !A. denude A = fromPaths (ltree_paths A)
Proof
QED
 *)

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
        SOME (vs,t) =>
         {A' | ?z. ~MEM z vs /\ z NOTIN FV A /\
                   A' = Branch (SOME (SNOC z vs,t)) (LAPPEND ts [| BT_VAR z |])}
      | NONE => {}
End

(* Definition 10.2.10 (i) *)
val _ = set_fixity "extends" (Infixr 490);

Definition extends_def :
    $extends (ts :naked_tree) (A :boehm_tree) <=>
       ltree_paths A SUBSET (ltree_paths ts) /\ finite_branching ts /\
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
    if IS_SOME (ltree_node A) then
       let (vs,t) = THE (ltree_node A);
                Z = ltree_node X;           (* initially empty *)
               as = ltree_children A;
               xs = ltree_children X;
                m = THE (LLENGTH as);            (* never NONE *)
                n = THE (LLENGTH xs);            (* never NONE *)
              vs' = NEWS (n - m) (set vs UNION Z);
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

(* This theorem connects ‘le_eta’ and ‘expansion’ (‘eta_generator’)
Theorem le_eta_expansion :
    !A B ts. ts extends A ==> le_eta A (eta_generate A ts)
Proof
QED
 *)
 *)

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
 >> RW_TAC std_ss [equivalent_of_solvables, principle_hnf_reduce]
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
             MATCH_MP_TAC principle_hnf_beta_reduce1 >> rw []) \\
         MATCH_MP_TAC principle_hnf_beta >> rw [FV_thm] \\
         rfs [FV_thm]) \\
     simp [SUB_THM] >> DISCH_TAC \\
  (* stage work

     N1 = principle_hnf (N0 @@ VAR v0 @@ VAR v1)
        = principle_hnf (LAM v (LAM z (VAR v @@ M @@ N)) @@ VAR v0 @@ VAR v1)
        = principle_hnf (
   *)
     Know ‘N1 = LAM v (LAM z (VAR v @@ M @@ N)) @@ VAR v0 @@ VAR v1’
...
QED
 *)

(*
Overload eta_sub_equiv = “subtree_equivalent”

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

(* Theorem 10.2.31, (i) <=> (iv) [1, p.244]
Theorem tree_eta_equiv_thm :
    !A B. tree_eta_equiv A B <=> !p. subtree_equivalent p A B
Proof
QED
 *)

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
 *)
