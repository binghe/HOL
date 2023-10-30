(*---------------------------------------------------------------------------*
 * boehm_treeScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])         *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory llistTheory
     relationTheory ltreeTheory pathTheory posetTheory hurdUtils;

open basic_swapTheory binderLib termTheory appFOLDLTheory chap2Theory chap3Theory
     head_reductionTheory standardisationTheory solvableTheory pure_dBTheory;

val _ = new_theory "boehm_tree";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)

val (LAM_size_thm, _) = define_recursive_term_function
   ‘(LAM_size (VAR s) = 0) /\
    (LAM_size (t1 @@ t2) = 0) /\
    (LAM_size (LAM v t) = 1 + hnf_prefix_size t)’;

(* appstar_size (((a b) c) d) *)
val (appstar_size_thm, _) = define_recursive_term_function
   ‘(appstar_size (VAR s) = 1) /\
    (appstar_size (t1 @@ t2) = 1 + appstar_size t1) /\
    (appstar_size (LAM v t) = 1)’;

val _ = export_rewrites ["LAM_size_thm", "appstar_size_thm"];

(* Usage: Defn.tgoal (Hol_defn "deep_rator_def" deep_rator_defn) *)
val deep_rator_defn = ‘deep_rator t = if is_comb t then deep_rator (rator t) else t’;
local
  val tactic = WF_REL_TAC ‘measure size’ \\
               rw [is_comb_APP_EXISTS] >> rw [];
in
  val deep_rator_def =
      TotalDefn.tDefine "deep_rator_def" deep_rator_defn tactic;
end;

(* |- !t. deep_rator t = if is_comb t then deep_rator (rator t) else t *)
Theorem deep_rator_thm = fst deep_rator_def;

(* |- !P. (!t. (is_comb t ==> P (rator t)) ==> P t) ==> !v. P v *)
Theorem deep_rator_ind = valOf (snd deep_rator_def);

Theorem deep_rator_appstar :
    !t. ~is_comb t ==> deep_rator (t @* args) = t
Proof
    Induct_on ‘args’ using SNOC_INDUCT
 >> rw [appstar_SNOC, Once deep_rator_thm]
QED

Theorem absfree_hnf_cases :
    !M. hnf M /\ ~is_abs M ==> ?y args. M = VAR y @* args
Proof
    rpt STRIP_TAC
 >> ‘?vs args y. ALL_DISTINCT vs /\ M = LAMl vs (VAR y @* args)’ by METIS_TAC [hnf_cases]
 >> reverse (Cases_on ‘vs = []’) >- fs []
 >> qexistsl_tac [‘y’, ‘args’] >> rw []
QED

Theorem absfree_hnf_deep_rator :
    !M. hnf M /\ ~is_abs M ==> is_var (deep_rator M)
Proof
    rpt STRIP_TAC
 >> ‘?y args. M = VAR y @* args’ by METIS_TAC [absfree_hnf_cases]
 >> POP_ORW
 >> Suff ‘deep_rator (VAR y @* args) = VAR y’ >- rw []
 >> MATCH_MP_TAC deep_rator_appstar >> rw []
QED

Overload hnf_headvar = “\M. THE_VAR (deep_rator M)”

(* A dB-term M is hnf if its corresponding Lambda term is hnf *)
Overload dhnf = “\M. hnf (toTerm M)”

Theorem dhnf_fromTerm[simp] :
    !M. dhnf (fromTerm M) <=> hnf M
Proof
    rw [o_DEF]
QED

(* dB version of hnf_cases (only the ==> direction) *)
Theorem dhnf_cases :
    !M. dhnf M ==> ?n y Ms. M = dABSi n (dV y @* Ms)
Proof
    RW_TAC std_ss [hnf_cases]
 >> qabbrev_tac ‘n = LENGTH vs’
 >> Q.EXISTS_TAC ‘n’
 >> Know ‘fromTerm (toTerm M) = fromTerm (LAMl vs (VAR y @* args))’
 >- (art [fromTerm_11])
 >> Q.PAT_X_ASSUM ‘toTerm M = LAMl vs (VAR y @* args)’ K_TAC
 >> rw [fromTerm_LAMl, fromTerm_appstar]
 >> qabbrev_tac ‘vs' = MAP s2n vs’
 >> qabbrev_tac ‘Ms = MAP fromTerm args’
 >> qabbrev_tac ‘y' = s2n y’
 >> Know ‘dLAMl vs' (dV y' @* Ms) =
          dABSi (LENGTH vs')
            (FOLDL lift (dV y' @* Ms) (GENLIST I (LENGTH vs')) ISUB
             ZIP (GENLIST dV (LENGTH vs'),
                  MAP (\i. i + LENGTH vs') (REVERSE vs')))’
 >- (MATCH_MP_TAC dLAMl_to_dABSi_applied \\
     qunabbrev_tac ‘vs'’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [])
 >> ‘LENGTH vs' = n’ by rw [Abbr ‘vs'’] >> POP_ORW
 >> Rewr'
 >> simp [FOLDL_lift_appstar, isub_appstar]
 >> Know ‘FOLDL lift (dV y') (GENLIST I n) = dV (y' + n)’
 >- (KILL_TAC \\
     Induct_on ‘n’ >> rw [GENLIST, FOLDL_SNOC])
 >> Rewr'
 >> qabbrev_tac ‘Ms' = MAP (\e. FOLDL lift e (GENLIST I n)) Ms’
 >> reverse (Cases_on ‘MEM y vs’)
 >- (‘~MEM y' vs'’ by (rw [Abbr ‘y'’, Abbr ‘vs'’, MEM_MAP]) \\
     ‘~MEM y' (REVERSE vs')’ by PROVE_TAC [MEM_REVERSE] \\
     Suff ‘dV (y' + n) ISUB ZIP (GENLIST dV n,MAP (\i. i + n) (REVERSE vs')) =
           dV (y' + n)’ >- (Rewr' >> METIS_TAC []) \\
     MATCH_MP_TAC isub_dV_fresh \\
     qabbrev_tac ‘l1 = GENLIST dV n’ \\
     qabbrev_tac ‘l2 = MAP (\i. i + n) (REVERSE vs')’ \\
    ‘LENGTH l1 = n’ by rw [Abbr ‘l1’] \\
    ‘LENGTH l2 = n’ by rw [Abbr ‘l2’, Abbr ‘n’, Abbr ‘vs'’] \\
     simp [DOM_ALT_MAP_SND, MAP_ZIP] \\
     rw [Abbr ‘l2’, MEM_MAP])
 (* stage work *)
 >> ‘MEM y' vs'’ by (rw [Abbr ‘y'’, Abbr ‘vs'’, MEM_MAP])
 >> ‘MEM y' (REVERSE vs')’ by PROVE_TAC [MEM_REVERSE]
 >> ‘?j. j < LENGTH (REVERSE vs') /\ y' = EL j (REVERSE vs')’
        by METIS_TAC [MEM_EL]
 >> ‘LENGTH (REVERSE vs') = n’ by rw [Abbr ‘vs'’, Abbr ‘n’]
 >> qabbrev_tac ‘Ns = MAP (\i. i + n) (REVERSE vs')’
 >> ‘LENGTH Ns = n’ by rw [Abbr ‘Ns’]
 >> Know ‘ALL_DISTINCT Ns’
 >- (qunabbrev_tac ‘Ns’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [] \\
     qunabbrev_tac ‘vs'’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [])
 >> DISCH_TAC
 >> Suff ‘dV (y' + n) ISUB ZIP (GENLIST dV n,Ns) = EL j (GENLIST dV n)’
 >- (Rewr' \\
     simp [EL_GENLIST] >> METIS_TAC [])
 >> MATCH_MP_TAC isub_dV_once >> simp []
 >> CONJ_TAC >- (rw [Abbr ‘Ns’, EL_MAP])
 >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC
 >> ‘n <= EL i Ns’ by rw [Abbr ‘Ns’, EL_MAP]
 >> Suff ‘FVS (ZIP (GENLIST dV n,Ns)) = count n’ >- rw []
 >> Q.PAT_X_ASSUM ‘LENGTH Ns = n’ MP_TAC
 >> KILL_TAC >> Q.ID_SPEC_TAC ‘Ns’
 >> Induct_on ‘n’ >> rw [dFVS_def]
 >> ‘Ns <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘LENGTH (FRONT Ns) = n’ by rw [LENGTH_FRONT]
 >> ‘Ns = SNOC (LAST Ns) (FRONT Ns)’
      by (rw [APPEND_FRONT_LAST, SNOC_APPEND]) >> POP_ORW
 >> Q.PAT_X_ASSUM ‘!Ns. LENGTH Ns = n ==> P’ (MP_TAC o (Q.SPEC ‘FRONT Ns’))
 >> rw [GENLIST, COUNT_SUC, dFVS_SNOC, ZIP_SNOC, dFV_def]
 >> SET_TAC []
QED

(* |- ?f f' f''. !M. dhnf M ==> M = dABS (f M) (dV (f' M) @* f'' M) *)
val dhnf_cases' = dhnf_cases
               |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM];

(* |- !M. dhnf M ==> M = dABSi (dABSn' M) (dV (dVn' M) @* dAPPl' M) *)
val dhnf_decompose =
    new_specification ("dhnf_decompose", ["dABSn'", "dVn'", "dAPPl'"], dhnf_cases');

(* Explicit definitions of hnf components (easier to work with) by Michael Norrish:

   1. The number of leading dABS (can be zero):
 *)
Definition dABSn_def :
   (dABSn (dV n)       = 0) /\
   (dABSn (dAPP t1 t2) = 0) /\
   (dABSn (dABS t)     = 1 + dABSn t)
End

(* 2. The head variable of hnf (always exists) *)
Definition dVn_def :
   (dVn (dV n)       = n) /\
   (dVn (dABS t)     = dVn t) /\
   (dVn (dAPP t1 t2) = dVn t1)
End

(* 2. The list of terms after appstar (may be empty) *)
Definition dAPPl_def :
   (dAPPl (dV n)       = []) /\
   (dAPPl (dABS t)     = dAPPl t) /\
   (dAPPl (dAPP t1 t2) = SNOC t2 (dAPPl t1))
End

(* The "main" part of a hnf *)
Definition dhnf_head_def :
    dhnf_head M = dABSi (dABSn M) (dV (dVn M))
End

val _ = export_rewrites ["dABSn_def", "dVn_def", "dAPPl_def"];

Theorem dABSn_dABSi[simp] :
    dABSn (dABSi n t) = n + dABSn t
Proof
    Induct_on ‘n’ >> rw [FUNPOW_SUC]
QED

Theorem dABSn_dV_appstar[simp] :
    dABSn (dV y @* Ns) = 0
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT
 >> rw [appstar_SNOC]
QED

Theorem dVn_dABSi[simp] :
    dVn (dABSi n t) = dVn t
Proof
    Induct_on ‘n’ >> rw [FUNPOW_SUC]
QED

Theorem dVn_appstar[simp] :
    dVn (M @* Ns) = dVn M
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT >> rw []
QED

Theorem dAPPl_dABSi[simp] :
    dAPPl (dABSi n t) = dAPPl t
Proof
    Induct_on ‘n’ >> rw [FUNPOW_SUC]
QED

Theorem dAPPl_dV_appstar[simp] :
    dAPPl (dV y @* Ns) = Ns
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT >> rw [dappstar_APPEND]
QED

Theorem dhnf_thm :
    !M. dhnf M ==> M = dABSi (dABSn M) (dV (dVn M) @* dAPPl M)
Proof
    rpt STRIP_TAC
 >> ‘?n y Ms. M = dABSi n (dV y @* Ms)’ by METIS_TAC [dhnf_cases]
 >> rw []
QED

(* Definition 8.3.20 [1, p.177]

   A term may have several hnf's, e.g. if any of its hnf can still do beta
   reductions, after such reductions the term is still an hnf by definition.
   The (unique) terminating term of head reduction path is called "principle"
   hnf, which is used for defining Boehm trees.
 *)
Definition principle_hnf_def :
    principle_hnf = last o head_reduction_path
End

Overload principle_hnf = “\M. fromTerm (principle_hnf (toTerm M))”

(* not used *)
Definition drator_def :
    drator (dAPP s t) = s
End

(* not used *)
Definition drand_def :
    drand (dAPP s t) = t
End

(* NOTE: this "body" function was unsound for :term *)
Definition dbody_def :
    dbody (dABS s) = s
End

Overload rator    = “drator”
Overload rand     = “drand”
Overload body     = “dbody”
Overload solvable = “\M. (solvable (toTerm M))”

Theorem solvable_principle_hnf :
    !M. solvable (M :pdb) ==> dhnf (principle_hnf M)
Proof
    rw [o_DEF, solvable_iff_has_hnf, principle_hnf_def, head_reduction_path_def,
        corollary11_4_8]
QED

(* The needed unfolding function for ltree_unfold for Boehm Tree *)
Definition BT_generator_def :
    BT_generator (M :pdb) = if solvable M then
                               let M' = principle_hnf M in
                                 (SOME (dhnf_head M'), fromList (dAPPl M'))
                            else
                               (NONE, LNIL)
End

(* The Boehm tree of M, all in dB terms *)
Definition dBT_def :
    dBT = ltree_unfold BT_generator
End

Definition BT_def :
    BT = ltree_map (OPTION_MAP toTerm) o dBT o fromTerm
End

(* The Boehm tree of M, translated back to normal Lambda terms *)
Type boehm_tree[pp] = “:term option ltree”

(* |- ltree_el (Branch a ts) [] = SOME (a,LLENGTH ts) /\
      ltree_el (Branch a ts) (n::ns) =
        case LNTH n ts of NONE => NONE | SOME t => ltree_el t ns

   |- ltree_lookup t [] = SOME t /\
      ltree_lookup (Branch a ts) (n::ns) =
        case LNTH n ts of NONE => NONE | SOME t => ltree_lookup t ns
 *)

(* Remarks 10.1.3 (iii) [1, p.216]: unsolvable terms all have the same Boehm
   tree (‘bot’).
 *)
Overload bot = “Branch NONE (LNIL :boehm_tree llist)”
val _ = Unicode.unicode_version {u = UTF8.chr 0x22A5, tmnm = "bot"};

Theorem unsolvable_BT :
    !M. unsolvable M ==> BT M = bot
Proof
    rw [BT_def, dBT_def, BT_generator_def, ltree_unfold, ltree_map]
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
 *  Comparing Boehm trees
 *---------------------------------------------------------------------------*)

(* “ltree_subset A B” <=> A results from B by cutting off some subtrees *)
Definition ltree_subset_def :
    ltree_subset A B <=> (subtrees A) SUBSET (subtrees B)
End

(* “ltree_paths A” has the type “:num list -> bool” (a set of number lists). *)
Definition ltree_paths_def :
    ltree_paths A = {path | IS_SOME (ltree_lookup A path)}
End

Theorem ltree_subset_alt :
    !A B. ltree_subset A B <=> (ltree_paths A) SUBSET (ltree_paths B)
Proof
    cheat
QED

(*---------------------------------------------------------------------------*
 *  Equivalent terms
 *---------------------------------------------------------------------------*)

(* Definition 10.2.19

   M = dABSi (dABSn M) (dV (dVn M) @* dAPPl M)
   N = dABSi (dABSn N) (dV (dVn N) @* dAPPl N)

   n  = dABSn M, y  = dVn M, m  = LENGTH (dAPPL M)
   n' = dABSn N, y' = dVn N, m' = LENGTH (dAPPL N)

   y = y'
   n - m = n' - m' (possibly negative) <=> n + m' = n' + m (all non-negative)
 *)
Definition equivalent_def :
    equivalent (M :pdb) (N :pdb) =
       if solvable M /\ solvable N then
          dVn M = dVn N /\
          dABSn M + LENGTH (dAPPl N) = dABSn N + LENGTH (dAPPl M)
       else
          ~solvable M /\ ~solvable N
End

Theorem equivalent_alt_solvable :
    !M N. solvable M /\ solvable N ==>
         (equivalent M (N :pdb) <=>
          dVn M = dVn N /\
          dABSn M + LENGTH (dAPPl N) = dABSn N + LENGTH (dAPPl M))
Proof
    rw [equivalent_def]
QED

Theorem unsolvable_imp_equivalent :
    !M N. ~solvable M /\ ~solvable N ==> equivalent M (N :pdb)
Proof
    rw [equivalent_def]
QED

Theorem equivalent_cases :
    !M N. equivalent M (N :pdb) <=>
             solvable M /\ solvable N /\
             dVn M = dVn N /\
             dABSn M + LENGTH (dAPPl N) = dABSn N + LENGTH (dAPPl M)
          \/ ~solvable M /\ ~solvable N
Proof
    rw [equivalent_def]
 >> METIS_TAC []
QED

Theorem not_equivalent_cases :
    !M N. ~equivalent M (N :pdb) <=>
             solvable M /\ ~solvable N
          \/ ~solvable M /\ solvable N
          \/ solvable M /\ solvable N /\
             (dVn M <> dVn N \/
              dABSn M + LENGTH (dAPPl N) <> dABSn N + LENGTH (dAPPl M))
Proof
    rw [equivalent_def]
 >> METIS_TAC []
QED

(* use the same name for equivalence of :term *)
Overload equivalent = “\M N. equivalent (fromTerm M) (fromTerm N)”

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
    head_original (M :pdb) = EVERY (\N. dVn M NOTIN dFV N) (dAPPl M)
End

Overload head_original = “\M. head_original (fromTerm M)”

(* Definition 10.3.5 (ii)

   NOTE: ‘head_original M' /\ ~is_dABS M'’ means m := dV n @* Ns (n not free in Ns)
 *)
Definition is_ready_def :
    is_ready (M :pdb) = (~solvable M \/
                         ~is_dABS (principle_hnf M) /\ head_original (principle_hnf M))
End

Overload is_ready = “\M. is_ready (fromTerm M)”

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

(* Theorem 2.1.40 [1, p.35] (Hilbert-Post completeness of beta+eta) *)
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
