(* ========================================================================== *)
(* FILE    : separabilityScript.sml                                           *)
(* TITLE   : Separability of lambda terms (additional work) [1, Chapter 10.4] *)
(* ========================================================================== *)

Theory separability
Ancestors
  combin option arithmetic pred_set list rich_list llist ltree relation iterate
  topology nomset basic_swap term appFOLDL chap2 chap3 chap4 horeduction
  head_reduction standardisation solvable boehm lameta_complete
Libs
  hurdUtils tautLib numLib listLib NEWLib reductionEval
  head_reductionLib monadsyntax

(* enable basic monad support *)
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

(* These theorems usually give unexpected results, should be applied manually *)
val _ = temp_delsimps [
   "lift_disj_eq", "lift_imp_disj",
   "IN_UNION",     (* |- !s t x. x IN s UNION t <=> x IN s \/ x IN t *)
   "APPEND_ASSOC"  (* |- !l1 l2 l3. l1 ++ (l2 ++ l3) = l1 ++ l2 ++ l3 *)
];

val _ = hide "B";
val _ = hide "C";
val _ = hide "W";
val _ = hide "Y";

(* some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

(* such re-definitions actually change their priorities *)
Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

val _ = temp_clear_overloads_on "fEL"; (* use old EL syntax *)

(*---------------------------------------------------------------------------*
 *  Virtual subterm (vsubterm) of Boehm Trees
 *---------------------------------------------------------------------------*)

(* vsubterm

   ((vs,y),Ms)   vs::[z_0,z_1,z_2,...]
       /\
     /    \      0,   1, .. (j = h - m)
    0 ...  m-1,  m, m+1, .. h
                       (([],z_j),[])
 *)
Definition vsubterm_def :
    vsubterm X M     [] r = SOME (M,r) /\
    vsubterm X M (h::p) r =
    if solvable M then
      let M0 = principal_hnf M;
           n = LAMl_size M0;
          vs = RNEWS r n X;
          M1 = principal_hnf (M0 @* MAP VAR vs);
          Ms = hnf_children M1;
           m = LENGTH Ms;
           j = h - m;
          zs = RNEWS r (n + SUC j) X;
           z = LAST zs;
           N = if h < m then EL h Ms else VAR z
      in
        vsubterm X N p (SUC r)
    else
      NONE
End

Overload vsubterm' = “\X M p r. FST (THE (vsubterm X M p r))”

(* |- vsubterm X M [] r = SOME (M,r) *)
Theorem vsubterm_NIL[simp] = SPEC_ALL (cj 1 vsubterm_def)

Theorem vsubterm_NIL'[simp] :
    vsubterm' X M [] r = M
Proof
    rw [vsubterm_NIL]
QED

Theorem vsubterm_alt_subterm :
    !p X M r. subterm X M p r <> NONE ==> vsubterm X M p r = subterm X M p r
Proof
    Induct_on ‘p’ >> rw [subterm_def, vsubterm_def]
QED

Theorem vsubterm_alt_subterm' :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p IN ltree_paths (BT' X M r) ==>
              vsubterm X M p r = subterm X M p r
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC vsubterm_alt_subterm
 >> simp [GSYM BT_ltree_paths_thm]
QED

(*
Theorem BT_expand_lemma3 :
    !X M p r B N.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M /\
       p IN ltree_paths (BT' X M r) /\
       BT_expand X (BT' X M r) p r = B /\ N = BT_to_term B ==>
       !q. q << p ==> subterm X M q r = subterm X N q r
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ASM_REWRITE_TAC []
 >> Suff ‘!R M r. (?p B. FV M SUBSET X UNION RANK r /\ has_bnf M /\
                         p IN ltree_paths (BT' X M r) /\
                         B = BT_expand X (BT' X M r) p r /\ R = to_rose B) ==>
                   BT' X (rose_to_term R) r = from_rose R /\
                   !q. q << p ==>
                       subterm X M q r = subterm X (rose_to_term R) q r’
 >- (Know ‘from_rose (to_rose B) = B’
     >- (MATCH_MP_TAC to_rose_def \\
         Q.PAT_X_ASSUM ‘_ = B’ (REWRITE_TAC o wrap o SYM) \\
         MATCH_MP_TAC ltree_finite_BT_expand' >> art []) \\
     DISCH_TAC \\
     Know ‘BT' X (BT_to_term B) r = B <=>
           BT' X (BT_to_term B) r = from_rose (to_rose B)’ >- simp [] \\
     Rewr' \\
     DISCH_THEN MATCH_MP_TAC \\
     qexistsl_tac [‘p’, ‘B’] >> art [])
 (* keep only “FINITE X” in assumptions *)
 >> Q.PAT_X_ASSUM ‘FINITE X’ MP_TAC
 >> KILL_TAC >> DISCH_TAC
 (* applying induction on rose tree *)
 >> HO_MATCH_MP_TAC rose_tree_induction
 >> NTAC 2 (rpt GEN_TAC >> STRIP_TAC)
 >> Q.PAT_X_ASSUM ‘Rose a ts = _’ (MP_TAC o SYM)
 >> POP_ORW
 >> DISCH_THEN (MP_TAC o AP_TERM “from_rose :BT_node rose_tree -> boehm_tree”)
 >> simp [to_rose_def, ltree_finite_BT_expand]
 (* stage work *)
 >> simp [from_rose_def]
 >> DISCH_TAC
 >> Q_TAC (UNBETA_TAC [rose_to_term_def, Once rose_reduce_def])
          ‘rose_to_term (Rose a ts)’
 >> simp [GSYM rose_to_term_def]
 (* special case (kind of base case here) *)
 >> Cases_on ‘p’
 >- (POP_ASSUM MP_TAC \\
     simp [BT_expand_def] \\
    ‘solvable M’ by PROVE_TAC [bnf_solvable] \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold])
           ‘BT' X M r’ \\
     simp [GSYM BT_def, ltree_el_def, Abbr ‘l’, LMAP_fromList, LNTH_fromList,
           EL_MAP, ltree_paths_alt_ltree_el] \\
     simp [ltree_insert_NIL] \\
     qunabbrev_tac ‘vs’ \\
     Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
     qunabbrev_tac ‘y’ \\
    ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma'] \\
     Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                     “y :string”, “args :term list”)) ‘M1’ \\
    ‘TAKE n vs = vs’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
     simp [Abbr ‘Ms’] \\
     Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “(SUC n)”)) ‘X’ \\
     qabbrev_tac ‘v = LAST vs'’ \\
     qabbrev_tac ‘m = LENGTH args’ \\
     simp [LNTH_EQ, LNTH_LGENLIST, LNTH_fromList, EL_MAP] \\
     STRIP_TAC \\
     Q.PAT_X_ASSUM ‘_ = a’ (simp o wrap o SYM) \\
     Know ‘!i. i < m ==> from_rose (EL i ts) = BT' X (EL i args) (SUC r)’
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘!(n :num). P’ (MP_TAC o Q.SPEC ‘i’) \\
         simp []) >> DISCH_TAC \\
     Know ‘from_rose (EL m ts) = BT_VAR v’
     >- (Q.PAT_X_ASSUM ‘!n. (if n < m + 1 then _ else NONE) = _’
           (MP_TAC o Q.SPEC ‘m’) \\
         simp []) >> DISCH_TAC \\
     qabbrev_tac ‘m' = LENGTH ts’ \\
     Know ‘m' = m + 1’
     >- (CCONTR_TAC \\
        ‘m' < m + 1 \/ m + 1 < m'’ by rw [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Q.PAT_X_ASSUM ‘!n. (if n < m + 1 then _ else NONE) = _’
             (MP_TAC o Q.SPEC ‘m'’) >> simp [],
           (* goal 2 (of 2) *)
           Q.PAT_X_ASSUM ‘!n. (if n < m + 1 then _ else NONE) = _’
             (MP_TAC o Q.SPEC ‘m + 1’) >> simp [] ]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!n. (if n < m + 1 then _ else NONE) = _’ K_TAC \\
     Know ‘MAP rose_to_term ts = SNOC (VAR v) args’
     >- (simp [LIST_EQ_REWRITE, EL_MAP] \\
         Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
        ‘i = m \/ i < m’ by rw []
         >- (simp [Abbr ‘m’, EL_LENGTH_SNOC] \\
             Q.PAT_X_ASSUM ‘_ = BT_VAR v’
               (MP_TAC o AP_TERM “to_rose :boehm_tree -> BT_node rose_tree”) \\
             simp [to_rose_thm]) \\
         simp [EL_SNOC] \\
         Q.PAT_X_ASSUM ‘!i. i < m ==> from_rose (EL i ts) = _’ drule \\
         DISCH_THEN (MP_TAC o AP_TERM “to_rose :boehm_tree -> BT_node rose_tree”) \\
         simp [to_rose_thm] \\
         DISCH_THEN K_TAC \\
         MATCH_MP_TAC BT_to_term_bnf >> art [] \\
         CONJ_TAC
         >- (MATCH_MP_TAC subterm_induction_lemma' \\
             qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []) \\
         MATCH_MP_TAC hnf_children_bnf \\
         qexistsl_tac [‘vs’, ‘y’] >> art [] \\
         Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) \\
         simp [] \\
         Suff ‘M0 = M’ >- rw [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principal_hnf_bnf >> art []) >> Rewr' \\
     reverse CONJ_TAC
     >- (REWRITE_TAC [GSYM LAMl_SNOC] \\
         qabbrev_tac ‘xs = SNOC v vs’ \\
         qabbrev_tac ‘args' = SNOC (VAR v) args’ \\
         simp [BT_def, BT_generator_def, Once ltree_unfold] \\
         Know ‘principal_hnf (LAMl xs (VAR y @* args')) =
               LAMl xs (VAR y @* args')’
         >- (MATCH_MP_TAC principal_hnf_reduce \\
             simp [hnf_thm, hnf_appstar]) >> Rewr' \\
         simp [Abbr ‘xs’, GSYM ADD1, GSYM BT_def] \\
         REWRITE_TAC [GSYM LAMl_SNOC, GSYM SNOC_APPEND] \\
         Know ‘SNOC v vs = vs'’
         >- (Know ‘vs <<= vs'’ >- rw [Abbr ‘vs’, Abbr ‘vs'’, RNEWS_prefix] \\
             simp [IS_PREFIX_EQ_TAKE] \\
             DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
             Know ‘LENGTH vs = LENGTH (TAKE i vs')’
             >- POP_ASSUM (REWRITE_TAC o wrap) \\
             simp [] >> DISCH_TAC \\
             Know ‘TAKE i vs' = FRONT vs'’
             >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
                ‘i = LENGTH vs' - 1’ by rw [] >> POP_ORW \\
                 MATCH_MP_TAC FRONT_BY_TAKE >> rw [GSYM LENGTH_NON_NIL]) \\
             Rewr' \\
             REWRITE_TAC [GSYM SNOC_APPEND] \\
             qunabbrev_tac ‘v’ \\
             MATCH_MP_TAC SNOC_LAST_FRONT \\
             rw [GSYM LENGTH_NON_NIL]) >> Rewr \\
         simp [principal_hnf_beta_reduce, hnf_appstar] \\
         simp [LMAP_fromList, MAP_MAP_o, o_DEF] \\
         simp [LIST_EQ_REWRITE, Abbr ‘args'’] \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         simp [EL_MAP] \\
        ‘i < m \/ i = m’ by rw [] >- simp [EL_SNOC] \\
        ‘i = LENGTH args’ by rw [] >> POP_ORW \\
         simp [EL_LENGTH_SNOC]) \\
    ‘M = M0’ by METIS_TAC [principal_hnf_bnf] \\
     simp [appstar_SNOC] \\
  (* applying compat_closure rules *)
     MATCH_MP_TAC compat_closure_LAMl \\
     MATCH_MP_TAC compat_closure_R \\
     REWRITE_TAC [eta_def] \\
     Q.EXISTS_TAC ‘v’ >> simp [] \\
     simp [FV_appstar] \\
     Suff ‘{y} UNION BIGUNION (IMAGE FV (set args)) SUBSET FV M UNION set vs’
     >- (DISCH_TAC \\
         Know ‘{y} UNION BIGUNION (IMAGE FV (set args)) SUBSET
               X UNION RANK r UNION set vs’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M UNION set vs’ \\
             POP_ASSUM (REWRITE_TAC o wrap) \\
             Suff ‘FV M SUBSET X UNION RANK r’ >- SET_TAC [] \\
             simp []) >> DISCH_TAC \\
         Suff ‘v NOTIN X UNION RANK r UNION set vs’
         >- (rpt STRIP_TAC \\
             METIS_TAC [SUBSET_DEF]) \\
         NTAC 2 (POP_ASSUM K_TAC) \\
         Know ‘v = EL n vs'’
         >- (‘vs' <> []’ by rw [GSYM LENGTH_NON_NIL] \\
             simp [LAST_EL, Abbr ‘v’]) >> Rewr' \\
         simp [IN_UNION, GSYM CONJ_ASSOC] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs') X’ MP_TAC \\
             rw [DISJOINT_ALT] \\
             POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM]) \\
         CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘r’, ‘SUC n’, ‘X’] DISJOINT_RNEWS_RANK') \\
             simp [] \\
             rw [DISJOINT_ALT] \\
             POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM]) \\
         Know ‘vs <<= vs'’
         >- (qunabbrevl_tac [‘vs’, ‘vs'’] \\
             MATCH_MP_TAC RNEWS_prefix >> rw []) \\
         simp [IS_PREFIX_EQ_TAKE] \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
         simp [] \\
         POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
         simp [LENGTH_TAKE] >> DISCH_THEN (rfs o wrap o SYM) \\
         qabbrev_tac ‘v' = EL n vs'’ (* this is also “v” *) \\
         Know ‘MEM v' (DROP n vs')’
         >- (simp [Abbr ‘v'’, MEM_DROP] \\
             Q.EXISTS_TAC ‘0’ >> simp []) >> DISCH_TAC \\
         CCONTR_TAC \\
         METIS_TAC [ALL_DISTINCT_TAKE_DROP]) \\
     Q.PAT_X_ASSUM ‘M = _’ K_TAC \\
     simp [UNION_SUBSET, SUBSET_DEF] \\
  (* applying subterm_headvar_lemma' *)
     CONJ_TAC
     >- (MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’]
                         subterm_headvar_lemma') >> simp []) \\
  (* applying FV_subterm_lemma *)
     simp [MEM_EL] >> rpt STRIP_TAC \\
     gs [] >> rename1 ‘N = EL i args’ \\
     Q.PAT_X_ASSUM ‘x IN FV (EL i args)’ MP_TAC \\
     Suff ‘FV (EL i args) SUBSET FV M UNION set vs’ >- rw [SUBSET_DEF] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’, ‘args’, ‘i’]
                     FV_subterm_lemma) >> simp [])
 (* stage work *)
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> ‘solvable M’ by PROVE_TAC [bnf_solvable]
 >> Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X M r’
 >> simp [GSYM BT_def, ltree_el_def, Abbr ‘l’, LMAP_fromList, LNTH_fromList,
          EL_MAP, ltree_paths_alt_ltree_el]
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qunabbrev_tac ‘y’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> simp [Abbr ‘Ms’]
 >> qabbrev_tac ‘m = LENGTH args’
 >> Cases_on ‘h < m’ >> simp []
 >> qabbrev_tac ‘N = EL h args’
 >> DISCH_TAC (* ltree_el (BT' X N (SUC r)) t <> NONE *)
 >> simp [BT_expand_def]
 >> qabbrev_tac ‘r' = r + SUC (LENGTH t)’
 >> Know ‘bnf N’
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC hnf_children_bnf \\
     qexistsl_tac [‘vs’, ‘y’] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) >> simp [] \\
     Suff ‘M0 = M’ >- rw [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principal_hnf_bnf >> art [])
 >> DISCH_TAC
 >> Know ‘FV N SUBSET X UNION RANK (SUC r)’
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> DISCH_TAC
 >> simp [ltree_el_def, LNTH_fromList, EL_MAP]
 (* applying BT_ltree_el_cases *)
 >> Know ‘?vs' y' m'. ltree_el (BT' X N (SUC r)) t = SOME (SOME (vs',y'),SOME m')’
 >- (MATCH_MP_TAC BT_ltree_el_cases \\
     simp [ltree_paths_alt_ltree_el])
 >> STRIP_TAC
 >> simp []
 >> qabbrev_tac ‘n1 = SUC (LENGTH vs')’
 >> Q_TAC (RNEWS_TAC (“vs1 :string list”, “r' :num”, “n1 :num”)) ‘X’
 >> simp [MAP_MAP_o, o_DEF]
 >> qabbrev_tac ‘B = BT' X N (SUC r)’
 >> qabbrev_tac ‘f = OPTION_MAP (\(vs,(y :string)). (SNOC (LAST vs1) vs,y))’
 (* applying ltree_insert_CONS *)
 >> qmatch_abbrev_tac ‘ltree_insert f (Branch a' ts') (h::t) t0 = Branch a _ ==> _’
 >> MP_TAC (Q.SPECL [‘f’, ‘a'’, ‘ts'’, ‘h’, ‘t’, ‘B’, ‘t0’]
                    (INST_TYPE [alpha |-> “:BT_node”] ltree_insert_CONS))
 >> impl_tac >- simp [Abbr ‘ts'’, LNTH_fromList, EL_MAP]
 >> simp [] >> DISCH_THEN K_TAC
 >> simp [Abbr ‘ts'’, LLENGTH_fromList, LNTH_fromList, Abbr ‘a'’]
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘_ = a’ (simp o wrap o SYM)
 >> POP_ASSUM MP_TAC (* LGENLIST _ = fromList (MAP from_rose ts) *)
 >> simp [LNTH_EQ, LNTH_fromList, LNTH_LGENLIST]
 >> DISCH_TAC
 >> qabbrev_tac ‘m0 = LENGTH ts’
 >> Know ‘m0 = m’
 >- (CCONTR_TAC \\
    ‘m0 < m \/ m < m0’ by rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM ‘!i. _ = if i < m0 then _ else NONE’ (MP_TAC o Q.SPEC ‘m0’) \\
       simp [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘!i. _ = if i < m0 then _ else NONE’ (MP_TAC o Q.SPEC ‘m’) \\
       simp [] ])
 >> DISCH_TAC
 >> Know ‘!i. i < m ==> from_rose (EL i ts) =
                        if i = h then ltree_insert f B t t0
                        else (BT' X (EL i args) (SUC r))’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. _ = if i < m0 then _ else NONE’ (MP_TAC o Q.SPEC ‘i’) \\
     simp [EL_MAP])
 >> Q.PAT_X_ASSUM ‘!i. _ = if i < m0 then _ else NONE’ K_TAC
 >> qunabbrev_tac ‘m0’
 >> DISCH_TAC
 (* applying to_rose_thm *)
 >> Know ‘!i. i < m ==> EL i ts =
                        if i = h then to_rose (ltree_insert f B t t0)
                        else to_rose (BT' X (EL i args) (SUC r))’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < m ==> from_rose (EL i ts) = _’ drule \\
     DISCH_THEN (MP_TAC o AP_TERM “to_rose :boehm_tree -> BT_node rose_tree”) \\
     simp [to_rose_thm] >> DISCH_THEN K_TAC \\
     Cases_on ‘i = h’ >> simp [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> Know ‘MAP rose_to_term ts =
          GENLIST (\i. if i = h then (BT_to_term (ltree_insert f B t t0))
                       else EL i args) m’
 >- (simp [LIST_EQ_REWRITE, EL_GENLIST, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Cases_on ‘i = h’ >> simp [] \\
     MATCH_MP_TAC BT_to_term_bnf >> art [] \\
     CONJ_TAC
     >- (MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []) \\
     MATCH_MP_TAC hnf_children_bnf \\
     qexistsl_tac [‘vs’, ‘y’] >> art [] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     Suff ‘M0 = M’ >- rw [] \\
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principal_hnf_bnf >> art [])
 >> Rewr'
 >> reverse CONJ_TAC
 >- (qmatch_abbrev_tac ‘BT' X (LAMl vs (VAR y @* args')) r = _’ \\
     simp [BT_def, BT_generator_def, Once ltree_unfold] \\
     Know ‘principal_hnf (LAMl vs (VAR y @* args')) = LAMl vs (VAR y @* args')’
     >- (MATCH_MP_TAC principal_hnf_reduce >> simp []) >> Rewr' \\
     simp [GSYM BT_def, principal_hnf_beta_reduce] \\
     simp [LMAP_fromList, MAP_MAP_o, o_DEF] \\
     simp [Abbr ‘args'’, MAP_GENLIST, o_DEF] \\
     simp [LIST_EQ_REWRITE] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
    ‘i <> h \/ i = h’ by rw []
     >- (simp [EL_MAP, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC to_rose_def \\
         MATCH_MP_TAC ltree_finite_BT_bnf >> art [] \\
         CONJ_TAC
         >- (MATCH_MP_TAC subterm_induction_lemma' \\
             qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []) \\
         MATCH_MP_TAC hnf_children_bnf \\
         qexistsl_tac [‘vs’, ‘y’] >> art [] \\
         Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) \\
         simp [] \\
         Suff ‘M0 = M’ >- rw [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principal_hnf_bnf >> art []) \\
     simp [EL_MAP] \\
  (* apply IH *)
     FIRST_X_ASSUM (irule o cj 2) \\
     reverse CONJ_TAC
     >- (simp [MEM_EL] \\
         Q.EXISTS_TAC ‘i’ >> art [] \\
         Q.PAT_X_ASSUM ‘!i. i < m ==> _’ (MP_TAC o Q.SPEC ‘i’) \\
         simp []) \\
     qabbrev_tac ‘N = EL h args’ \\
     qexistsl_tac [‘N’, ‘t’] >> simp [ltree_paths_alt_ltree_el] \\
     simp [GSYM from_rose_11] \\
     Know ‘from_rose (to_rose (ltree_insert f B t t0)) = ltree_insert f B t t0’
     >- (MATCH_MP_TAC to_rose_def \\
         MATCH_MP_TAC ltree_finite_ltree_insert \\
         simp [Abbr ‘t0’, ltree_paths_alt_ltree_el, Abbr ‘B’] \\
         MATCH_MP_TAC ltree_finite_BT_bnf >> art []) >> Rewr' \\
     Know ‘from_rose (to_rose (BT_expand X B t (SUC r))) =
           BT_expand X B t (SUC r)’
     >- (MATCH_MP_TAC to_rose_def \\
         qunabbrev_tac ‘B’ \\
         MATCH_MP_TAC ltree_finite_BT_expand \\
         simp [ltree_paths_alt_ltree_el]) >> Rewr' \\
     simp [BT_expand_def, Abbr ‘f’] \\
    ‘LENGTH t + SUC r = r'’ by rw [Abbr ‘r'’] >> POP_ORW \\
     simp [])
 >> Know ‘M = M0’
 >- (qunabbrev_tac ‘M0’ \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC principal_hnf_bnf >> art [])
 >> Rewr'
 >> simp []
 >> MATCH_MP_TAC compat_closure_LAMl
 >> MATCH_MP_TAC compat_closure_appstar' >> simp []
 (* applying IH (amazing) *)
 >> FIRST_X_ASSUM (fn th => irule (cj 1 th))
 >> reverse CONJ_TAC
 >- (simp [MEM_EL] >> Q.EXISTS_TAC ‘h’ >> simp [])
 >> qexistsl_tac [‘SUC r’, ‘t’]
 >> simp [ltree_paths_alt_ltree_el, Abbr ‘B’]
 >> ONCE_REWRITE_TAC [GSYM from_rose_11]
 >> Know ‘from_rose (to_rose (BT_expand X (BT' X N (SUC r)) t (SUC r))) =
          BT_expand X (BT' X N (SUC r)) t (SUC r)’
 >- (MATCH_MP_TAC to_rose_def \\
     MATCH_MP_TAC ltree_finite_BT_expand \\
     simp [ltree_paths_alt_ltree_el])
 >> Rewr'
 >> Know ‘from_rose (to_rose (ltree_insert f (BT' X N (SUC r)) t t0)) =
          ltree_insert f (BT' X N (SUC r)) t t0’
 >- (MATCH_MP_TAC to_rose_def \\
     MATCH_MP_TAC ltree_finite_ltree_insert \\
     simp [ltree_finite_BT_bnf, Abbr ‘t0’, ltree_paths_alt_ltree_el])
 >> Rewr'
 >> rw [BT_expand_def]
 >> ‘LENGTH t + SUC r = r'’ by rw [Abbr ‘r'’]
 >> POP_ORW >> simp []
QED
 *)

(* NOTE: eta_expand1 X M p r = BT_to_term (BT_expand X (BT' X M r) p r)
         BT_to_term B = rose_to_term (to_rose B)

Theorem vsubterm_expand_lemma :
    !X M p r m.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M /\
       p IN ltree_paths (BT' X M r) /\
       ltree_branching (BT' X M r) p = SOME m ==>
       vsubterm X M (SNOC m p) r = subterm X (eta_expand1 X M (SNOC m p) r) p r
Proof
    NTAC 2 STRIP_TAC
 >> Induct_on ‘p’ >- simp []
 >> rpt STRIP_TAC
 >> cheat
QED
 *)

val _ = html_theory "separability";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
