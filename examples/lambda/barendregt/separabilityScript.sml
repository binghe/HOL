(* ========================================================================== *)
(* FILE    : separabilityScript.sml                                           *)
(* TITLE   : Separability of lambda terms (additional work) [1, Chapter 10.4] *)
(*                                                                            *)
(* AUTHOR  : Chun Tian (binghe) <binghe.lisp@gmail.com> (2026)                *)
(* ========================================================================== *)

Theory separability
Ancestors
  combin option arithmetic pred_set list rich_list llist ltree relation
  topology nomset basic_swap term appFOLDL chap2 chap3 horeduction
  head_reduction standardisation solvable boehm takahashiS3 lameta_complete
Libs
  hurdUtils tautLib numLib listLib NEWLib reductionEval head_reductionLib
  monadsyntax BasicProvers

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
          M2 = if h < m then EL h Ms else VAR z
      in
        vsubterm X M2 p (SUC r)
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

Theorem vsubterm_of_solvables :
    !X M h p r. solvable M ==>
      vsubterm X M (h::p) r =
      let M0 = principal_hnf M;
           n = LAMl_size M0;
          vs = RNEWS r n X;
          M1 = principal_hnf (M0 @* MAP VAR vs);
          Ms = hnf_children M1;
           m = LENGTH Ms;
           j = h - m;
          zs = RNEWS r (n + SUC j) X;
           z = LAST zs;
          M2 = if h < m then EL h Ms else VAR z
      in
          vsubterm X M2 p (SUC r)
Proof
    RW_TAC std_ss [vsubterm_def]
QED

Theorem vsubterm_of_unsolvables :
    !X M p r. unsolvable M /\ p <> [] ==> vsubterm X M p r = NONE
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p’ >> fs []
 >> RW_TAC std_ss [vsubterm_def]
QED

Theorem vsubterm_of_absfree_hnf :
    !X M h p r. hnf M /\ ~is_abs M ==>
       vsubterm X M (h::p) r =
       let Ms = hnf_children M;
            m = LENGTH Ms;
            j = h - m;
           zs = RNEWS r (SUC j) X;
            z = LAST zs;
           M2 = if h < m then EL h Ms else VAR z
       in
           vsubterm X M2 p (SUC r)
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [vsubterm_of_solvables]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principal_hnf_reduce]
 >> fs [Abbr ‘M0’]
 >> Know ‘n = 0’
 >- (qunabbrev_tac ‘n’ \\
     MATCH_MP_TAC LAMl_size_eq_0 >> art [])
 >> DISCH_THEN (fs o wrap)
 >> fs [Abbr ‘vs’]
 >> Q.PAT_X_ASSUM ‘Ms' = Ms’ (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘m = m'’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M = M1’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘j = j'’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘zs = zs'’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘z = z'’ (rfs o wrap o SYM)
QED

Theorem vsubterm_of_absfree_hnf_explicit :
    !X y Ms h p r.
       vsubterm X (VAR y @* Ms) (h::p) r =
       let m = LENGTH Ms;
           j = h - m;
          zs = RNEWS r (SUC j) X;
           z = LAST zs;
          M2 = if h < m then EL h Ms else VAR z
       in
          vsubterm X M2 p (SUC r)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘VAR y @* Ms’, ‘h’, ‘p’, ‘r’] vsubterm_of_absfree_hnf)
 >> rw [hnf_appstar, is_abs_appstar]
QED

Theorem vsubterm_of_principal_hnf :
    !X M p r. solvable M /\ p <> [] ==>
              vsubterm X (principal_hnf M) p r = vsubterm X M p r
Proof
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> Cases_on ‘p’ >> fs []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> ‘solvable M0’ by PROVE_TAC [solvable_principal_hnf]
 >> RW_TAC std_ss [vsubterm_of_solvables]
 >> ‘M0' = M0’ by rw [Abbr ‘M0'’, Abbr ‘M0’, principal_hnf_stable']
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘n = n'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m = m'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘j = j'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘zs = zs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘z = z'’   (fs o wrap o SYM)
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

Theorem subterm_imp_vsubterm_not_none :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==> vsubterm X M p r <> NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> qid_specl_tac [‘p’, ‘M’, ‘r’]
 >> Induct_on ‘p’ >- simp []
 >> rpt GEN_TAC >> STRIP_TAC
 >> Q_TAC (UNBETA_TAC [subterm_def]) ‘subterm X M (h::p) r’
 >> STRIP_TAC
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::p) r’
 >> ‘n' = n’ by simp [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m = m'’   (fs o wrap o SYM)
 >> simp [Abbr ‘M2’]
 >> FIRST_X_ASSUM irule >> art []
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
 >> simp [Abbr ‘m’, Once EQ_SYM_EQ]
 >> MATCH_MP_TAC hnf_children_size_alt
 >> qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

Theorem vsubterm_imp_subterm_none :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              vsubterm X M p r = NONE ==> subterm X M p r = NONE
Proof
    PROVE_TAC [subterm_imp_vsubterm_not_none]
QED

Theorem vsubterm_var :
    !X y p r. FINITE X /\ p <> [] ==>
              vsubterm X (VAR y) p r =
              SOME (VAR (RNEW (r + LENGTH p - 1) (LAST p) X),r + LENGTH p)
Proof
    Q.X_GEN_TAC ‘X’
 >> Suff ‘FINITE X ==>
            !p y r. p <> [] ==>
                    vsubterm X (VAR y) p r =
                    SOME (VAR (RNEW (r + LENGTH p - 1) (LAST p) X),r + LENGTH p)’
 >- METIS_TAC []
 >> DISCH_TAC
 >> Induct_on ‘p’ >> simp [] (* only one goal is left *)
 >> rpt STRIP_TAC
 >> Cases_on ‘p = []’
 >- (simp [RNEW_def] \\
     RW_TAC std_ss [vsubterm_def, GSYM ADD1] >- simp [solvable_VAR] \\
    ‘hnf (VAR y)’ by simp [hnf_thm] \\
    ‘M0 = VAR y’ by simp [Abbr ‘M0’, principal_hnf_reduce] \\
     POP_ASSUM (fs o wrap) \\
     fs [Abbr ‘M0’, Abbr ‘n’] \\
     fs [Abbr ‘vs’] \\
     fs [Abbr ‘M1’, hnf_children_VAR, Abbr ‘Ms’] \\
     fs [Abbr ‘m’, Abbr ‘j’])
 (* stage work *)
 >> simp [LAST_DEF]
 >> RW_TAC std_ss [vsubterm_def] >- simp [solvable_VAR]
 >> ‘hnf (VAR y)’ by simp [hnf_thm]
 >> ‘M0 = VAR y’ by simp [Abbr ‘M0’, principal_hnf_reduce]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> fs [Abbr ‘M0’, Abbr ‘n’]
 >> fs [Abbr ‘vs’]
 >> fs [Abbr ‘M1’, hnf_children_VAR, Abbr ‘Ms’]
 >> fs [Abbr ‘m’, Abbr ‘j’]
 >> simp [Abbr ‘M2’]
 >> qabbrev_tac ‘m = LENGTH p’
 >> Suff ‘m + SUC r - 1 = r + SUC m - 1’ >- Rewr
 >> simp []
QED

Theorem vsubterm_var' :
    !X y p r. FINITE X /\ p <> [] ==>
              vsubterm' X (VAR y) p r = VAR (RNEW (r + LENGTH p - 1) (LAST p) X)
Proof
    RW_TAC std_ss [vsubterm_var]
QED

(* NOTE: The exact value of ‘x’ is hard to describe, except for it's row/rank. *)
Theorem vsubterm_eq_var :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              vsubterm X M p r <> NONE /\ subterm X M p r = NONE ==>
              ?x. vsubterm X M p r = SOME (VAR x,r + LENGTH p) /\
                  x IN RANK (r + LENGTH p)
Proof
    Q.X_GEN_TAC ‘X’
 >> Suff ‘FINITE X ==>
           !p M r. FV M SUBSET X UNION RANK r /\ vsubterm X M p r <> NONE /\
                   subterm X M p r = NONE ==>
                   ?x. vsubterm X M p r = SOME (VAR x,r + LENGTH p) /\
                       x IN RANK (r + LENGTH p)’
 >- METIS_TAC []
 >> DISCH_TAC
 >> Induct_on ‘p’ >- simp []
 >> rpt GEN_TAC >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (Q.PAT_X_ASSUM ‘vsubterm X M (h::p) r <> NONE’ MP_TAC \\
     simp [vsubterm_def])
 >> Q.PAT_X_ASSUM ‘vsubterm X M (h::p) r <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) r = NONE’ MP_TAC
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::p) r’
 >> Q_TAC (UNBETA_TAC [subterm_def]) ‘subterm X M (h::p) r’
 >> ‘n' = n’ by simp [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m = m'’ (fs o wrap o SYM)
 >> qabbrev_tac ‘l = LENGTH p’
 >> Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
 >- (Cases_on ‘p = []’ >- simp [subterm_def] \\
    ‘r + SUC l = SUC r + l’ by simp [] >> POP_ORW \\
     rpt STRIP_TAC \\
     FIRST_X_ASSUM irule >> art [] \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     SYM_TAC >> qunabbrev_tac ‘m’ \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> Know ‘z IN RANK (SUC r)’
 >- (qunabbrev_tac ‘zs’ \\
     Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
    ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
    ‘MEM z zs’ by simp [Abbr ‘z’, LAST_MEM] \\
     MP_TAC (Q.SPECL [‘r’, ‘SUC r’, ‘n + SUC j’, ‘X’] RNEWS_SUBSET_RANK) \\
     simp [] \\
     rw [SUBSET_DEF])
 >> DISCH_TAC
 >> Cases_on ‘p = []’
 >- simp [vsubterm_def, Abbr ‘l’, GSYM ADD1]
 >> ‘r + SUC l = SUC r + l’ by simp [] >> POP_ORW
 >> DISCH_TAC
 >> FIRST_X_ASSUM irule >> art []
 >> reverse CONJ_TAC
 >- (Suff ‘FV (VAR z) SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [FV_thm, SUBSET_DEF])
 >> ‘solvable (VAR z)’ by simp []
 >> Cases_on ‘p’ >> fs [] >> T_TAC
 >> RW_TAC std_ss [subterm_def]
 >> ‘hnf (VAR z)’ by simp [hnf_thm]
 >> ‘M0' = VAR z’ by simp [Abbr ‘M0'’, principal_hnf_reduce]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> fs [Abbr ‘M0'’, Abbr ‘n'’]
 >> fs [Abbr ‘vs'’]
 >> fs [Abbr ‘M1'’, hnf_children_VAR, Abbr ‘Ms'’]
 >> fs [Abbr ‘m'’]
QED

Theorem vsubterm_eq_var' :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              vsubterm X M p r <> NONE /\ subterm X M p r = NONE ==>
              ?x. vsubterm' X M p r = VAR x /\
                  x IN RANK (r + LENGTH p)
Proof
    rpt GEN_TAC
 >> DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP vsubterm_eq_var))
 >> Q.EXISTS_TAC ‘x’ >> simp []
QED

Theorem vsubterm_var_not_none :
    !X y p r. FINITE X ==> vsubterm X (VAR y) p r <> NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Cases_on ‘p = []’ >- simp [vsubterm_def]
 >> simp [vsubterm_var]
QED

(* cf. lameq_subterm_cong *)
Theorem lameta_vsubterm_cong :
    !X M N p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
                            FV N SUBSET X UNION RANK r /\ M === N
           ==> (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
               (vsubterm X M p r <> NONE ==>
                vsubterm' X M p r === vsubterm' X N p r)
Proof
    Suff ‘!X. FINITE X ==>
              !p M N r. FV M SUBSET X UNION RANK r /\
                        FV N SUBSET X UNION RANK r /\ M === N
          ==> (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
              (vsubterm X M p r <> NONE ==>
               vsubterm' X M p r === vsubterm' X N p r)’ >- METIS_TAC []
 >> NTAC 2 STRIP_TAC
 >> Induct_on ‘p’ >- simp []
 >> rpt GEN_TAC >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by PROVE_TAC [lameta_solvable_cong] \\
     simp [vsubterm_def])
 >> ‘solvable N’ by PROVE_TAC [lameta_solvable_cong]
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::p) r’
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X N (h::p) r’
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> CONJ_TAC
 >- (Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
     >- (MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
         simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC hnf_children_size_alt \\
         qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []) \\
     simp [IN_UNION] >> DISJ2_TAC \\
     Know ‘set zs SUBSET RANK (SUC r)’
     >- (qunabbrev_tac ‘zs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp []) \\
     Suff ‘z IN set zs’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrev_tac ‘z’ \\
     MATCH_MP_TAC LAST_MEM \\
     qunabbrev_tac ‘zs’ \\
     Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
     simp [NOT_NIL_EQ_LENGTH_NOT_0])
 >> CONJ_TAC
 >- (Cases_on ‘h < m'’ >> simp [Abbr ‘M2'’]
     >- (MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘N’, ‘M0'’, ‘n'’, ‘m'’, ‘vs'’, ‘M1'’] >> simp [] \\
         simp [Abbr ‘m'’, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC hnf_children_size_alt \\
         qexistsl_tac [‘X’, ‘N’, ‘r’, ‘n'’, ‘vs'’, ‘M1'’] >> simp []) \\
     simp [IN_UNION] >> DISJ2_TAC \\
     Know ‘set zs' SUBSET RANK (SUC r)’
     >- (qunabbrev_tac ‘zs'’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp []) \\
     Suff ‘z' IN set zs'’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrev_tac ‘z'’ \\
     MATCH_MP_TAC LAST_MEM \\
     qunabbrev_tac ‘zs'’ \\
     Q_TAC (RNEWS_TAC (“zs' :string list”, “r :num”, “n' + SUC j'”)) ‘X’ \\
     simp [NOT_NIL_EQ_LENGTH_NOT_0])
 (* stage work *)
 >> Know ‘M0 === M0'’
 >- (Q_TAC (TRANS_TAC lameta_TRANS) ‘M’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC lameq_imp_lameta \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC lameq_principal_hnf' >> art []) \\
     Q_TAC (TRANS_TAC lameta_TRANS) ‘N’ >> art [] \\
     MATCH_MP_TAC lameq_imp_lameta \\
     qunabbrev_tac ‘M0'’ \\
     MATCH_MP_TAC lameq_SYM \\
     MATCH_MP_TAC lameq_principal_hnf' >> art [])
 >> DISCH_TAC
 >> ‘?Z. M0 -be->* Z /\ M0' -be->* Z’ by METIS_TAC [lameta_CR]
 (*
    M -h->* M0 -be->*
    |       |        \
   ===     ===        Z
    |       |        /
    N -h->* M0'-be->*
  *)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M0)’ K_TAC
 >> ‘TAKE (LAMl_size M0) vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘vs'’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’
 >> ‘DISJOINT (set vs') (FV M0')’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0' :term”, “vs' :string list”,
                    “y'  :string”, “args' :term list”)) ‘M1'’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs') (FV M0')’ K_TAC
 >> ‘TAKE (LAMl_size M0') vs' = vs'’ by rw []
 >> POP_ASSUM (rfs o wrap)
 (* eliminating Ms and Ms' *)
 >> ‘Ms  = args’  by rw [Abbr ‘Ms’]  >> POP_ASSUM (rfs o wrap)
 >> ‘Ms' = args'’ by rw [Abbr ‘Ms'’] >> POP_ASSUM (rfs o wrap)
 >> qunabbrevl_tac [‘Ms’, ‘Ms'’]
 >> Q.PAT_X_ASSUM ‘M0  = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M0' = _’ (ASSUME_TAC o SYM)
 (* applying hnf_bestar_cases *)
 >> MP_TAC (Q.SPECL [‘vs’,  ‘y’,  ‘args’,  ‘Z’] hnf_bestar_cases) >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘i’  STRIP_ASSUME_TAC) (* i  and Ns *)
 >> Q.PAT_X_ASSUM ‘Z = _’ (ASSUME_TAC o SYM)
 >> MP_TAC (Q.SPECL [‘vs'’, ‘y'’, ‘args'’, ‘Z’] hnf_bestar_cases) >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘i'’ STRIP_ASSUME_TAC) (* i' and Ns' *)
 >> Q.PAT_X_ASSUM ‘Z = _’ (ASSUME_TAC o SYM)
 (*
    M -h->* M0 -be->*
    |       |        \
   ===     ===        Z
    |       |        /
    N -h->* M0'-be->*

   M0  = LAMl vs  (VAR y  @* args)
   Z   = LAMl (TAKE (n - i) vs)  (VAR y  @* (TAKE (m - i) Ns)
   Z   = LAMl (TAKE (n'-i') vs') (VAR y' @* (TAKE (m'-i') Ns')
   M0' = LAMl vs' (VAR y' @* args')
 *)
 >> Know ‘n' - i' = n - i’
 >- (Q.PAT_X_ASSUM ‘_ = Z’ (MP_TAC o AP_TERM “LAMl_size”) \\
     REWRITE_TAC [LAMl_size_hnf] \\
     simp [LENGTH_BUTLASTN] >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘_ = Z’ (MP_TAC o AP_TERM “LAMl_size”) \\
     REWRITE_TAC [LAMl_size_hnf] \\
     simp [LENGTH_BUTLASTN])
 >> DISCH_TAC
 (* stage work *)
 >> gs [BUTLASTN_TAKE_UNCOND, LASTN_DROP_UNCOND]
 >> qabbrev_tac ‘n_max = SUC (MAX n n' + MAX j j')’
 >> Know ‘n <= n_max /\ n' <= n_max’
 >- (simp [Abbr ‘n_max’, MAX_DEF] >> numLib.ARITH_TAC)
 >> STRIP_TAC
 >> Q_TAC (RNEWS_TAC (“xs :string list”, “r :num”, “n_max :num”)) ‘X’
 (* applying TAKE_RNEWS (and TAKE_TAKE) *)
 >> Know ‘TAKE (n - i) vs = TAKE (n - i) xs’
 >- (‘vs = TAKE n xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     irule TAKE_TAKE >> simp [])
 >> DISCH_THEN (fs o wrap)
 >> Q.PAT_X_ASSUM ‘LAMl (TAKE (n - i) vs') _ = Z’ MP_TAC
 >> Know ‘TAKE (n' - i') vs' = TAKE (n' - i') xs’
 >- (‘vs' = TAKE n' xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     irule TAKE_TAKE >> simp [])
 >> simp [] >> DISCH_THEN K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl (TAKE (n - i) xs) _ = Z’ (simp o wrap o SYM)
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘y' = y’ (fs o wrap)
 >> Know ‘m' - i' = m - i’
 >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :term list -> num”) \\
     simp [])
 >> DISCH_TAC
 >> Know ‘DROP (n - i) vs = TAKE (n - (n - i)) (DROP (n - i) xs)’
 >- (‘vs = TAKE n xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     REWRITE_TAC [DROP_TAKE])
 >> simp [] >> DISCH_THEN (fs o wrap)
 >> Know ‘DROP (n' - i') vs' = TAKE (n' - (n' - i')) (DROP (n' - i') xs)’
 >- (‘vs' = TAKE n' xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     REWRITE_TAC [DROP_TAKE])
 >> ‘n' - (n' - i') = i'’ by simp [] >> POP_ORW
 >> simp [] >> DISCH_THEN (fs o wrap)
 >> qabbrev_tac ‘xs2 = DROP (n - i) xs’
 (* stage work *)
 >> qunabbrevl_tac [‘M2’, ‘M2'’]
 >> Cases_on ‘h < m’ >> Cases_on ‘h < m'’ >> simp [] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      Q_TAC (TRANS_TAC lameta_TRANS) ‘EL h Ns’ \\
      CONJ_TAC >- simp [bestar_lameta] \\
      Suff ‘EL h Ns = EL h Ns'’
      >- (Rewr' \\
          MATCH_MP_TAC lameta_SYM >> simp [bestar_lameta]) \\
   (* 0       h1       h2  m     m'
      |<------------>+-i-->|     |  Ns
      |<------------>+-----i'--->|  Ns'
                     |
                   m - i (= m' - i')
    *)
      Cases_on ‘h < m - i’
      >- (Q.PAT_X_ASSUM ‘TAKE (m - i) Ns' = TAKE (m - i) Ns’ MP_TAC \\
          simp [LIST_EQ_REWRITE, EL_TAKE]) \\
      qabbrev_tac ‘m_i = m - i’ \\
      REV_FULL_SIMP_TAC std_ss [NOT_LESS] \\
     ‘h = h - m_i + m_i’ by simp [] >> POP_ORW \\
      Know ‘EL (h - m_i + m_i) Ns = EL (h - m_i) (DROP m_i Ns)’
      >- (SYM_TAC >> MATCH_MP_TAC EL_DROP >> simp []) >> Rewr' \\
      Know ‘EL (h - m_i + m_i) Ns' = EL (h - m_i) (DROP m_i Ns')’
      >- (SYM_TAC >> MATCH_MP_TAC EL_DROP >> simp []) >> Rewr' \\
      ASM_SIMP_TAC std_ss [] \\
     ‘h - m_i < i /\ h - m_i < i'’ by simp [Abbr ‘m_i’] \\
      qabbrev_tac ‘l = TAKE i xs2’ \\
      qabbrev_tac ‘l' = TAKE i' xs2’ \\
      Know ‘LENGTH l = i’
      >- (simp [Abbr ‘l’] \\
          MATCH_MP_TAC LENGTH_TAKE \\
          simp [Abbr ‘xs2’, LENGTH_DROP]) >> DISCH_TAC \\
      Know ‘LENGTH l' = i'’
      >- (simp [Abbr ‘l'’] \\
          MATCH_MP_TAC LENGTH_TAKE \\
          simp [Abbr ‘xs2’, LENGTH_DROP]) >> DISCH_TAC \\
      simp [EL_MAP] \\
      simp [Abbr ‘l’, Abbr ‘l'’, EL_TAKE],
      (* goal 2 (of 4) *)
      REV_FULL_SIMP_TAC std_ss [NOT_LESS] \\
   (* 0                    m'   h   m
      |<------------>+-i'->|    z'  |  Ns'
      |<------------>+------i------>|  Ns
                     |
                   m - i (= m' - i')
    *)
     ‘j = 0’ by simp [Abbr ‘j’] \\
      POP_ASSUM (rfs o wrap) \\
      qunabbrevl_tac [‘j’, ‘zs’, ‘z’] \\
      Suff ‘VAR z' = EL h Ns’ >- (Rewr' >> simp [bestar_lameta]) \\
      qabbrev_tac ‘m_i = m - i’ \\
     ‘h = h - m_i + m_i’ by simp [] >> POP_ORW \\
      Know ‘EL (h - m_i + m_i) Ns = EL (h - m_i) (DROP m_i Ns)’
      >- (SYM_TAC >> MATCH_MP_TAC EL_DROP >> simp []) >> Rewr' \\
      ASM_SIMP_TAC std_ss [] \\
     ‘h - m_i < i’ by simp [Abbr ‘m_i’] \\
      qabbrev_tac ‘l = TAKE i xs2’ \\
      Know ‘LENGTH l = i’
      >- (simp [Abbr ‘l’] \\
          MATCH_MP_TAC LENGTH_TAKE \\
          simp [Abbr ‘xs2’, LENGTH_DROP]) >> DISCH_TAC \\
      simp [EL_MAP] \\
      simp [Abbr ‘l’, EL_TAKE, Abbr ‘z'’] \\
      POP_ASSUM K_TAC \\
      Know ‘n' + SUC j' <= n_max’
      >- (simp [Abbr ‘n_max’, MAX_DEF] \\
          numLib.ARITH_TAC) >> DISCH_TAC \\
      qunabbrev_tac ‘zs'’ \\
      Q_TAC (RNEWS_TAC (“zs' :string list”, “r :num”, “n' + SUC j'”)) ‘X’ \\
     ‘zs' <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      simp [LAST_EL] \\
     ‘PRE (n' + SUC j') = n' + j'’ by numLib.ARITH_TAC >> POP_ORW \\
     ‘zs' = TAKE (n' + SUC j') xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
      simp [EL_TAKE] \\
      simp [Abbr ‘xs2’, EL_DROP] \\
     ‘h + n - (i + m_i) = h + (n' - i') - (m' - i')’ by simp [Abbr ‘m_i’] \\
      POP_ORW \\
      qunabbrev_tac ‘m_i’ \\
     ‘h + (n' - i') - (m' - i') = h + n' - m'’ by simp [] >> POP_ORW \\
      simp [Abbr ‘j'’],
      (* goal 3 (of 4) *)
      REV_FULL_SIMP_TAC std_ss [NOT_LESS] \\
   (* 0                    m    h   m'
      |<------------>+-i'->|    z   |  Ns
      |<------------>+------i------>|  Ns'
                     |
                   m - i (= m' - i')
    *)
     ‘j' = 0’ by simp [Abbr ‘j'’] \\
      POP_ASSUM (rfs o wrap) \\
      qunabbrevl_tac [‘j'’, ‘zs'’, ‘z'’] \\
      Suff ‘VAR z = EL h Ns'’
      >- (Rewr' \\
          MATCH_MP_TAC lameta_SYM >> simp [bestar_lameta]) \\
      qabbrev_tac ‘m_i = m - i’ \\
     ‘m_i <= h’ by simp [Abbr ‘m_i’] \\
     ‘h = h - m_i + m_i’ by simp [] >> POP_ORW \\
      Know ‘EL (h - m_i + m_i) Ns' = EL (h - m_i) (DROP m_i Ns')’
      >- (SYM_TAC >> MATCH_MP_TAC EL_DROP >> simp []) >> Rewr' \\
      ASM_SIMP_TAC std_ss [] \\
     ‘h - m_i < i'’ by simp [Abbr ‘m_i’] \\
      qabbrev_tac ‘l = TAKE i' xs2’ \\
      Know ‘LENGTH l = i'’
      >- (simp [Abbr ‘l’] \\
          MATCH_MP_TAC LENGTH_TAKE \\
          simp [Abbr ‘xs2’, LENGTH_DROP]) >> DISCH_TAC \\
      simp [EL_MAP] \\
      simp [Abbr ‘l’, EL_TAKE, Abbr ‘z’] \\
      POP_ASSUM K_TAC \\
      Know ‘n + SUC j <= n_max’
      >- (simp [Abbr ‘n_max’, MAX_DEF] \\
          numLib.ARITH_TAC) >> DISCH_TAC \\
      qunabbrev_tac ‘zs’ \\
      Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
     ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      simp [LAST_EL] \\
     ‘PRE (n + SUC j) = n + j’ by numLib.ARITH_TAC >> POP_ORW \\
     ‘zs = TAKE (n + SUC j) xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
      simp [EL_TAKE] \\
      simp [Abbr ‘xs2’, EL_DROP] \\
      simp [Abbr ‘j’, Abbr ‘m_i’],
      (* goal 4 (of 4) *)
      Suff ‘VAR z = VAR z'’ >- simp [lameta_REFL] \\
      REV_FULL_SIMP_TAC std_ss [NOT_LESS] \\
   (* 0                    m        m'  h
      |<------------>+-i'->|        |   z   Ns
      |<------------>+------i------>|   z'  Ns'
                     |
                   m - i (= m' - i')
    *)
      qunabbrev_tac ‘zs’ \\
      Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
     ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      qunabbrev_tac ‘zs'’ \\
      Q_TAC (RNEWS_TAC (“zs' :string list”, “r :num”, “n' + SUC j'”)) ‘X’ \\
     ‘zs' <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      simp [Abbr ‘z’, Abbr ‘z'’, LAST_EL] \\
     ‘PRE (n  + SUC j)  = n  + j’  by numLib.ARITH_TAC >> POP_ORW \\
     ‘PRE (n' + SUC j') = n' + j'’ by numLib.ARITH_TAC >> POP_ORW \\
      Know ‘n + SUC j <= n_max’
      >- (simp [Abbr ‘n_max’, MAX_DEF] \\
          numLib.ARITH_TAC) >> DISCH_TAC \\
      Know ‘n' + SUC j' <= n_max’
      >- (simp [Abbr ‘n_max’, MAX_DEF] \\
          numLib.ARITH_TAC) >> DISCH_TAC \\
     ‘zs  = TAKE (n  + SUC j)  xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     ‘zs' = TAKE (n' + SUC j') xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
      simp [EL_TAKE] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      qunabbrevl_tac [‘j’, ‘j'’] \\
      Suff ‘h - m + n = h - m' + n'’ >- Rewr \\
      Q.PAT_X_ASSUM ‘n' - i' = n - i’ MP_TAC \\
      Q.PAT_X_ASSUM ‘m' - i' = m - i’ MP_TAC \\
      Q.PAT_X_ASSUM ‘i <= n’   MP_TAC \\
      Q.PAT_X_ASSUM ‘i <= m’   MP_TAC \\
      Q.PAT_X_ASSUM ‘i' <= n'’ MP_TAC \\
      Q.PAT_X_ASSUM ‘i' <= m'’ MP_TAC \\
      Q.PAT_X_ASSUM ‘m <= h’   MP_TAC \\
      Q.PAT_X_ASSUM ‘m' <= h’  MP_TAC \\
      numLib.ARITH_TAC ]
QED

Theorem vsubterm_not_none_bnf :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M ==>
              vsubterm X M p r <> NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> qid_specl_tac [‘p’, ‘M’, ‘r’]
 >> Induct_on ‘p’ >- simp []
 >> rpt GEN_TAC
 >> NTAC 2 DISCH_TAC
 >> ‘solvable M’ by PROVE_TAC [bnf_solvable]
 >> RW_TAC std_ss [vsubterm_def]
 >> Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
 >- (FIRST_X_ASSUM irule \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
         simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC hnf_children_size_alt \\
         qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []) \\
     qunabbrev_tac ‘vs’ \\
     Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
    ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
     Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                     “y :string”, “args :term list”)) ‘M1’ \\
    ‘TAKE n vs = vs’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘Ms = args’ by simp [Abbr ‘Ms’] \\
     POP_ASSUM (rfs o wrap) \\
     qunabbrev_tac ‘Ms’ \\
     MATCH_MP_TAC hnf_children_bnf \\
     qexistsl_tac [‘vs’, ‘y’] \\
     ASM_SIMP_TAC std_ss [] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) \\
     Suff ‘M0 = M’ >- rw [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principal_hnf_bnf >> art [])
 >> Cases_on ‘p = []’ >- simp []
 >> Suff ‘z IN X UNION RANK (SUC r)’
 >- (DISCH_TAC >> simp [vsubterm_var])
 >> simp [Abbr ‘z’, Abbr ‘zs’]
 >> ‘n + SUC j = SUC (n + j)’ by simp [] >> POP_ORW
 >> REWRITE_TAC [GSYM RNEW_def]
 >> MATCH_MP_TAC RNEW_IN_RANK' >> art []
QED

Theorem vsubterm_not_none_has_bnf :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M ==>
              vsubterm X M p r <> NONE
Proof
    rw [has_bnf_thm]
 >> ‘M == N’ by PROVE_TAC [betastar_lameq]
 >> Know ‘FV N SUBSET X UNION RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     MATCH_MP_TAC betastar_FV_SUBSET >> art [])
 >> DISCH_TAC
 >> Know ‘vsubterm X M p r = NONE <=> vsubterm X N p r = NONE’
 >- (MATCH_MP_TAC (cj 1 lameta_vsubterm_cong) >> art [] \\
     MATCH_MP_TAC lameq_imp_lameta >> art [])
 >> Rewr'
 >> MATCH_MP_TAC vsubterm_not_none_bnf >> art []
QED

Theorem lameta_vsubterm_cong_has_bnf :
    !X M N p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
                          FV N SUBSET X UNION RANK r /\
                M === N /\ has_bnf M /\ has_bnf N
            ==> vsubterm' X M p r === vsubterm' X N p r
Proof
    rpt STRIP_TAC
 >> ‘vsubterm X M p r <> NONE /\
     vsubterm X N p r <> NONE’ by PROVE_TAC [vsubterm_not_none_has_bnf]
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘p’, ‘r’] lameta_vsubterm_cong)
 >> simp []
QED

Theorem vsubterm_is_none_inclusive :
    !X M p r. vsubterm X M p r = NONE <=>
              !q. p <<= q ==> vsubterm X M q r = NONE
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- (DISCH_THEN (MP_TAC o (Q.SPEC ‘p’)) >> rw [])
 >> qid_specl_tac [‘p’, ‘X’, ‘M’, ‘r’]
 >> Induct_on ‘p’ >- rw [vsubterm_NIL]
 >> rw [vsubterm_def] (* 3 subgoals, same tactics *)
 >> Cases_on ‘q’ >> fs [vsubterm_def]
QED

Theorem vsubterm_is_none_iff_parent_unsolvable :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
             (vsubterm X M p r = NONE <=>
              p <> [] /\
              (vsubterm X M (FRONT p) r <> NONE ==>
               unsolvable (vsubterm' X M (FRONT p) r)))

Proof
    rpt GEN_TAC
 >> STRIP_TAC >> POP_ASSUM MP_TAC
 >> Suff ‘!p M r. FV M SUBSET X UNION RANK r ==>
                 (vsubterm X M p r = NONE <=>
                  p <> [] /\
                  (vsubterm X M (FRONT p) r <> NONE ==>
                   unsolvable (vsubterm' X M (FRONT p) r)))’ >- METIS_TAC []
 >> Induct_on ‘p’ >- rw [vsubterm_def]
 >> rpt STRIP_TAC
 >> Cases_on ‘p = []’ >> fs []
 >- simp [vsubterm_def]
 >> simp [FRONT_DEF]
 >> reverse (Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::p) r’)
 >- simp [vsubterm_def]
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::FRONT p) r’
 >> ‘n' = n’ by simp [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m = m'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘j = j'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘zs = zs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘z = z'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M2 = M2'’ (fs o wrap o SYM)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> fs [NOT_LESS]
 >> Suff ‘z IN RANK (SUC r)’ >- rw [IN_UNION]
 >> qunabbrev_tac ‘zs’
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’
 >> ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘MEM z zs’ by simp [Abbr ‘z’, LAST_MEM]
 >> MP_TAC (Q.SPECL [‘r’, ‘SUC r’, ‘n + SUC j’, ‘X’] RNEWS_SUBSET_RANK)
 >> simp []
 >> rw [SUBSET_DEF]
QED

Theorem vsubterm_rank_lemma :
    !p X M N r r'. FINITE X /\ FV M SUBSET X UNION RANK r /\
                   vsubterm X M p r = SOME (N,r')
               ==> r' = r + LENGTH p /\ FV N SUBSET X UNION RANK r'
Proof
    Induct_on ‘p’ >- NTAC 2 (rw [])
 >> rpt GEN_TAC
 >> reverse (Cases_on ‘solvable M’) >- rw [vsubterm_def]
 >> UNBETA_TAC [vsubterm_def] “vsubterm X M (h::p) r”
 >> STRIP_TAC
 >> simp []
 >> qabbrev_tac ‘l = LENGTH p’
 >> ‘r + SUC l = SUC r + l’ by simp [] >> POP_ORW
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘M2’ >> art []
 >> Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> fs [NOT_LESS]
 >> Suff ‘z IN RANK (SUC r)’ >- rw [IN_UNION]
 >> qunabbrev_tac ‘zs’
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’
 >> ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘MEM z zs’ by simp [Abbr ‘z’, LAST_MEM]
 >> MP_TAC (Q.SPECL [‘r’, ‘SUC r’, ‘n + SUC j’, ‘X’] RNEWS_SUBSET_RANK)
 >> simp []
 >> rw [SUBSET_DEF]
QED

Theorem FV_vsubterm_upperbound :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              vsubterm X M p r <> NONE ==>
              FV (vsubterm' X M p r) SUBSET X UNION RANK (r + LENGTH p)
Proof
    rpt STRIP_TAC
 >> fs [GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
 >> Cases_on ‘x’
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M’, ‘q’, ‘r’, ‘r'’] vsubterm_rank_lemma)
 >> NTAC 2 (rw [])
QED

(* NOTE: ‘vsubterm_width’ further ensures that it's bigger than every index
   in the path, which may be arbitrarily bigger as a virtual path.

   The SUC in “SUC (MAX_LIST p)” is necessary: for even an index 0 in the path,
   it means the vsubterm at that level has at least one child, making the width
   at least be 1 there.
 *)
Definition vsubterm_width_def :
    vsubterm_width M p = MAX (subterm_width M p) (SUC (MAX_LIST p))
End

Theorem subterm_le_vsubterm_width[simp] :
    subterm_width M p <= vsubterm_width M p
Proof
    rw [vsubterm_width_def]
QED

Theorem vsubterm_width_ge_1[simp] :
    1 <= vsubterm_width M p
Proof
    rw [vsubterm_width_def]
QED

(* NOTE: This is the main purpose of introducing ‘vsubterm_width’. *)
Theorem vsubterm_width_thm :
    !p M e. MEM e p ==> e < vsubterm_width M p
Proof
    rw [vsubterm_width_def]
 >> DISJ2_TAC
 >> Suff ‘e <= MAX_LIST p’ >- simp []
 >> MATCH_MP_TAC MAX_LIST_PROPERTY >> art []
QED

Theorem vsubterm_width_nil :
    !M. vsubterm_width M [] =
        if solvable M then MAX (hnf_children_size (principal_hnf M)) 1 else 1
Proof
    rw [vsubterm_width_def, subterm_width_def]
QED

Theorem vsubterm_width_inclusive :
    !M p q d. q <<= p /\ vsubterm_width M p <= d ==> vsubterm_width M q <= d
Proof
    rpt GEN_TAC
 >> simp [vsubterm_width_def]
 >> STRIP_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC subterm_width_inclusive \\
     Q.EXISTS_TAC ‘p’ >> art [])
 >> Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘SUC (MAX_LIST p)’
 >> simp []
 >> MATCH_MP_TAC MAX_LIST_LE_PREFIX >> art []
QED

Theorem vsubterm_width_induction_lemma :
    !X M h p r M0 n n' m vs' M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         solvable M /\
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\ n <= n' /\
          m = hnf_children_size M0 /\ h < m /\
        vs' = RNEWS r n' X /\
         M1 = principal_hnf (M0 @* MAP VAR vs') /\
         Ms = hnf_children M1 ==>
        (vsubterm_width M (h::p) <= d <=>
         h < d /\ m <= d /\ vsubterm_width (EL h Ms) p <= d)
Proof
    rw [vsubterm_width_def, GSYM LESS_EQ]
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> qabbrev_tac ‘vs = RNEWS r n' X’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘m  = hnf_children_size M0’
 >> qabbrev_tac ‘Ms = hnf_children M1’
 >> Suff ‘subterm_width M (h::p) <= d <=>
          m <= d /\ subterm_width (EL h Ms) p <= d’ >- PROVE_TAC []
 >> MATCH_MP_TAC subterm_width_induction_lemma
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘n'’, ‘vs’, ‘M1’] >> simp []
QED

Theorem vsubterm_width_induction_lemma' :
    !X M h p r M0 n m vs M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         solvable M /\
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\
          m = hnf_children_size M0 /\ h < m /\
         vs = RNEWS r n X /\
         M1 = principal_hnf (M0 @* MAP VAR vs) /\
         Ms = hnf_children M1 ==>
        (vsubterm_width M (h::p) <= d <=>
         h < d /\ m <= d /\ vsubterm_width (EL h Ms) p <= d)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC vsubterm_width_induction_lemma
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

Theorem vsubterm_width_var[simp] :
    vsubterm_width (VAR y) p = SUC (MAX_LIST p)
Proof
    RW_TAC std_ss [vsubterm_width_def, subterm_width_var]
QED

(* NOTE: “~(h < m)” is assumed here. *)
Theorem vsubterm_width_eq_first :
    !X M h p r M0 n m.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         solvable M /\
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\
          m = hnf_children_size M0 /\ ~(h < m) ==>
         vsubterm_width M (h::p) = MAX m (SUC (MAX h (MAX_LIST p)))
Proof
    rw [vsubterm_width_def]
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> qabbrev_tac ‘m  = hnf_children_size M0’
 >> Suff ‘subterm_width M (h::p) = m’ >- Rewr
 >> MATCH_MP_TAC subterm_width_eq_first
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’] >> simp []
QED

Theorem vsubterm_width_le_eq_first :
    !X M h p r M0 n m d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         solvable M /\
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\
          m = hnf_children_size M0 /\ ~(h < m) ==>
        (vsubterm_width M (h::p) <= d <=> m <= d /\ h < d /\ MAX_LIST p < d)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> qabbrev_tac ‘m  = hnf_children_size M0’
 >> Know ‘vsubterm_width M (h::p) = MAX m (SUC (MAX h (MAX_LIST p)))’
 >- (MATCH_MP_TAC vsubterm_width_eq_first \\
     qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’] >> simp [])
 >> Rewr'
 >> simp [GSYM LESS_EQ]
QED

(*---------------------------------------------------------------------------*
 *  "Boehm out" technique for single terms at arbitrary path                 *
 *---------------------------------------------------------------------------*)

(* cf. solvable_subst_permutator. Now we work with vsubterm_width *)
Theorem solvable_subst_permutator' :
    !X M r P v d.
       FINITE X /\ FV M SUBSET X UNION RANK r /\
       v IN X UNION RANK r /\ P = permutator d /\
       solvable M /\ vsubterm_width M [] <= d
   ==> solvable ([P/v] M) /\ vsubterm_width ([P/v] M) [] <= d
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘P = permutator d’ (REWRITE_TAC o wrap)
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by simp []
 >> POP_ASSUM (rfs o wrap)
 >> ‘M0 == M’ by simp [Abbr ‘M0’, lameq_principal_hnf']
 >> ‘[P/v] M0 == [P/v] M’ by simp [lameq_sub_cong]
 >> ‘FV P = {}’ by simp [Abbr ‘P’, FV_permutator]
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
 >> Know ‘LENGTH args <= d’
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘vsubterm_width M []’ >> art [] \\
     Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width M []’ >> simp [] \\
     simp [hnf_children_size_thm, subterm_width_nil])
 >> DISCH_TAC
 >> CONJ_ASM1_TAC
 >- (Suff ‘solvable ([P/v] M0)’ >- PROVE_TAC [lameq_solvable_cong] \\
     simp [LAMl_SUB, appstar_SUB] \\
     reverse (Cases_on ‘y = v’)
     >- (simp [SUB_THM] \\
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
     simp [solvable_iff_has_hnf, has_hnf_thm] \\
     qabbrev_tac ‘args' = MAP [P/v] args’ \\
     qabbrev_tac ‘m = LENGTH args’ \\
    ‘LENGTH args' = m’ by simp [Abbr ‘args'’] \\
    ‘LENGTH args' <= d’ by simp [Abbr ‘args'’] \\
  (* applying hreduce_permutator_thm *)
     MP_TAC (Q.SPECL [‘{}’, ‘d’, ‘args'’] hreduce_permutator_thm) \\
     rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs))’ \\
     rw [hnf_appstar, hnf_thm])
 (* extra goal for induction *)
 >> Q.PAT_X_ASSUM ‘vsubterm_width M [] <= d’ MP_TAC
 >> simp [vsubterm_width_nil]
 >> DISCH_TAC
 (* applying principal_hnf_hreduce, hreduces_hnf_imp_principal_hnf, etc.

    M -h->* M0 = LAMl vs (VAR y @* args)
    [P/v] M -h->* [P/v] (LAMl vs (VAR y @* args))
  *)
 >> Know ‘[P/v] M -h->* [P/v] M0’
 >- (MATCH_MP_TAC hreduce_substitutive \\
     METIS_TAC [principal_hnf_thm'])
 >> simp [LAMl_SUB, appstar_SUB]
 >> reverse (Cases_on ‘y = v’)
 >- (simp [SUB_THM, solvable_iff_has_hnf] \\
     DISCH_TAC \\
     qabbrev_tac ‘args' = MAP [P/v] args’ \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘principal_hnf ([P/v] M) = LAMl vs (VAR y @* args')’
       by METIS_TAC [principal_hnf_thm'] >> POP_ORW \\
     qabbrev_tac ‘m = LENGTH args’ \\
    ‘LENGTH args' = m’ by rw [Abbr ‘args'’] \\
     simp [])
 (* stage work *)
 >> simp []
 >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH args’
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’]
 >> MP_TAC (Q.SPECL [‘{}’, ‘d’, ‘args'’] hreduce_permutator_thm)
 >> simp []
 >> STRIP_TAC
 >> ‘LAMl vs (P @* args') -h->*
     LAMl vs (LAMl xs (LAM y' (VAR y' @* args' @* MAP VAR xs)))’
       by rw [hreduce_LAMl]
 >> Know ‘[P/v] M -h->* LAMl vs (LAMl xs (LAM y' (VAR y' @* args' @* MAP VAR xs)))’
 >- (MATCH_MP_TAC hreduce_TRANS \\
     Q.EXISTS_TAC ‘LAMl vs (P @* args')’ >> art [])
 >> REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND, GSYM LAMl_SNOC]
 >> qabbrev_tac ‘ys = SNOC y' (vs ++ xs)’
 >> qabbrev_tac ‘args2 = args' ++ MAP VAR xs’
 >> DISCH_TAC
 >> ‘hnf (LAMl ys (VAR y' @* args2))’ by rw [hnf_appstar]
 >> ‘principal_hnf ([P/v] M) = LAMl ys (VAR y' @* args2)’
       by METIS_TAC [principal_hnf_thm']
 >> POP_ORW
 >> simp [Abbr ‘args2’]
QED

Theorem solvable_subst_permutator_cong' :
    !X M r P v d.
       FINITE X /\ FV M SUBSET X UNION RANK r /\
       v IN X UNION RANK r /\ P = permutator d /\
       vsubterm_width M [] <= d ==> (solvable ([P/v] M) <=> solvable M)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- PROVE_TAC [unsolvable_subst]
 >> DISCH_TAC
 >> MATCH_MP_TAC (cj 1 solvable_subst_permutator')
 >> qexistsl_tac [‘X’, ‘r’, ‘d’] >> art []
QED

(* NOTE: v, P and d are fixed free variables here *)
Theorem vsubterm_subst_permutator_cong_lemma[local] :
    !X. FINITE X ==>
        !q M p r. q <<= p /\
                  FV M SUBSET X UNION RANK r /\
                  vsubterm X M p r <> NONE /\
                  vsubterm_width M p <= d /\
                  P = permutator d /\ v IN X UNION RANK r
              ==> vsubterm X ([P/v] M) q r <> NONE /\
                  vsubterm_width ([P/v] M) q <= d /\
                  vsubterm' X ([P/v] M) q r = [P/v] (vsubterm' X M q r)
Proof
    NTAC 2 STRIP_TAC
 >> Induct_on ‘q’
 >- (rw [] \\
     qabbrev_tac ‘P = permutator d’ \\
     Know ‘1 <= d’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘vsubterm_width M p’ >> simp []) \\
     DISCH_TAC \\
     Cases_on ‘solvable ([P/v] M)’ \\ (* 2 subgoals, same tactics *)
     rw [vsubterm_width_def, subterm_width_def] \\
  (* only one goal is left *)
    ‘solvable M’ by PROVE_TAC [unsolvable_subst] \\
     qabbrev_tac ‘M0 = principal_hnf M’ \\
     qabbrev_tac ‘n = LAMl_size M0’ \\
     Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
    ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
     qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’ \\
     Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                     “y :string”, “args :term list”)) ‘M1’ \\
    ‘TAKE n vs = vs’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘M -h->* M0’ by METIS_TAC [principal_hnf_thm'] \\
     Know ‘[P/v] M -h->* [P/v] M0’ >- PROVE_TAC [hreduce_substitutive] \\
    ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT', FV_permutator, Abbr ‘P’] \\
     Know ‘~MEM v vs’
     >- (Q.PAT_X_ASSUM ‘v IN X UNION RANK r’ MP_TAC \\
         rw [IN_UNION]
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
             rw [DISJOINT_ALT']) \\
         Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
         qunabbrev_tac ‘vs’ \\
         MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) >> DISCH_TAC \\
     simp [LAMl_SUB, appstar_SUB] \\
     qabbrev_tac ‘args' = MAP [P/v] args’ \\
    ‘LENGTH args' = LENGTH args’ by rw [Abbr ‘args'’] \\
     Know ‘LENGTH args <= d’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘vsubterm_width M p’ >> art [] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width M p’ >> simp [] \\
        ‘LENGTH args = hnf_children_size (principal_hnf M)’ by rw [] \\
         POP_ORW \\
         MATCH_MP_TAC subterm_width_first \\
         qexistsl_tac [‘X’, ‘r’] >> art []) >> DISCH_TAC \\
     reverse (Cases_on ‘v = y’)
     >- (simp [] \\
         DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
        ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
        ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
        ‘principal_hnf ([P/v] M) = LAMl vs (VAR y @* args')’
           by METIS_TAC [principal_hnf_thm'] >> POP_ORW \\
         simp [hnf_children_size_LAMl]) \\
     simp [Abbr ‘P’] \\
     POP_ASSUM (fs o wrap o SYM) >> T_TAC \\
     DISCH_TAC (* [permutator d/y] M -h->* ... *) \\
     MP_TAC (Q.SPECL [‘set vs’, ‘d’, ‘args'’] hreduce_permutator_thm) \\
     simp [] \\
     STRIP_TAC (* this asserts new fresh lists to be renamed: ‘xs’ and ‘y’ *) \\
     Know ‘[permutator d/v] M -h->*
             LAMl vs (LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs)))’
     >- (MATCH_MP_TAC hreduce_TRANS \\
         Q.EXISTS_TAC ‘LAMl vs (permutator d @* args')’ >> rw []) \\
     DISCH_TAC \\
    ‘hnf (LAMl vs (LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs))))’
       by rw [hnf_LAMl, hnf_appstar] \\
     qabbrev_tac ‘P = permutator d’ \\
    ‘principal_hnf ([P/v] M) =
     LAMl vs (LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs)))’
       by METIS_TAC [principal_hnf_thm'] >> POP_ORW \\
     simp [hnf_children_size_LAMl, GSYM appstar_APPEND])
 (* stage work *)
 >> rpt GEN_TAC >> STRIP_TAC
 (* re-define P as abbreviations *)
 >> Q.PAT_X_ASSUM ‘P = permutator d’ (FULL_SIMP_TAC std_ss o wrap)
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘Y = X UNION RANK r’
 >> Cases_on ‘p = []’ >- fs []
 >> qabbrev_tac ‘w = vsubterm_width M p’
 (* decompose ‘p’ and eliminate ‘p <> []’ *)
 >> Cases_on ‘p’ >> fs [] >> T_TAC
 >> Q.PAT_X_ASSUM ‘h = h'’ (fs o wrap o SYM)
 >> Know ‘h < w’
 >- (qunabbrev_tac ‘w’ \\
     MATCH_MP_TAC vsubterm_width_thm >> simp [])
 >> DISCH_TAC
 (* preparing for eliminating ‘vsubterm' X M (h::q)’ *)
 >> Know ‘solvable M’
 >- (CCONTR_TAC \\
     Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC \\
     simp [vsubterm_def])
 >> DISCH_TAC
 >> Know ‘vsubterm X M (h::q) r <> NONE’
 >- (‘h::q <<= h::t’ by simp [] \\
     METIS_TAC [vsubterm_is_none_inclusive])
 >> UNBETA_TAC [vsubterm_of_solvables] “vsubterm X M (h::q) r”
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
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width M (h::t)’ \\
     reverse CONJ_TAC >- simp [Abbr ‘w’] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘r’] subterm_width_first) \\
     rw [Abbr ‘w’])
 >> DISCH_TAC
 (* NOTE: ‘[P/v] M’ is solvable iff ‘[P/v] M0’ is solvable, the latter is either
    already a hnf (v <> y), or can be head-reduced to a hnf (v = y).
  *)
 >> Know ‘solvable ([P/v] M)’
 >- (MATCH_MP_TAC (cj 1 solvable_subst_permutator') \\
     qexistsl_tac [‘X’, ‘r’, ‘d’] >> simp [] \\
     MATCH_MP_TAC vsubterm_width_inclusive \\
     Q.EXISTS_TAC ‘h::t’ >> simp [])
 >> DISCH_TAC
 >> Know ‘~MEM v vs’
 >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     rw [Abbr ‘Y’, IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art [])
 >> DISCH_TAC
 >> ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator]
 >> Know ‘FV ([P/v] M) SUBSET Y’
 >- (simp [FV_SUB] \\
     Cases_on ‘v IN FV M’ >> simp [] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
     SET_TAC [])
 >> DISCH_TAC
 (* Now we need to know the exact form of ‘principal_hnf ([P/v] M)’.

    We know that ‘principal_hnf M = M0 = LAMl vs (VAR y @* args)’, which means
    that ‘M -h->* LAMl vs (VAR y @* args)’. Meanwhile, as -h->* is substitutive,
    thus ‘[P/v] M -h->* [P/v] LAMl vs (VAR y @* args)’. Depending on the nature
    of ‘v’, the ending term ‘[P/v] LAMl vs (VAR y @* args)’ may or may not be
    a hnf. But it has indeed a hnf, since ‘solvable ([P/v] M)’ has been proved.

    Case 1 (MEM v vs): Case unprovable (but is eliminated by adding ‘v IN X’)
    Case 2 (v <> y):   [P/v] LAMl vs (VAR y @* args) = LAMl vs (VAR y @* args')
    Case 3 (v = y):    [P/v] LAMl vs (VAR y @* args) = LAMl vs (P @* args'),
        where LAMl vs (P @* args') -h->*
              LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs))) =
              LAMl (vs ++ xs ++ [Z]) (VAR Z @* args' @* MAP VAR xs), a hnf

    Only Case 3 needs further head-reductions, but the final hnf is already clear
    when proving ‘solvable ([P/v] M)’. Easy.

    In all these cases, ‘h < hnf_children_size (principal_hnf ([P/v] M))’ holds:
    In Case 1 & 2, ‘hnf_children_size (principal_hnf ([P/v] M)) = LENGTH args’.
    In Case 3, ‘hnf_children_size (principal_hnf ([P/v] M)) >= LENGTH args’.
  *)
 >> ‘M -h->* M0’ by METIS_TAC [principal_hnf_thm']
 (* NOTE: we will need to further do head reductions on ‘[P/v] M0’ *)
 >> Know ‘[P/v] M -h->* [P/v] M0’ >- PROVE_TAC [hreduce_substitutive]
 >> ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT', FV_permutator, Abbr ‘P’]
 >> simp [LAMl_SUB, appstar_SUB]
 >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’]
 (* LHS rewriting of args', this will introduce M0' = principal_hnf ([P/v] M)
    and a new set of abbreviations (vs', n', ...).
  *)
 >> CONV_TAC (UNBETA_CONV “vsubterm X ([P/v] M) (h::q) r”)
 >> qmatch_abbrev_tac ‘f _’
 >> ASM_SIMP_TAC std_ss [vsubterm_of_solvables]
 >> LET_ELIM_TAC
 >> simp [Abbr ‘f’, hnf_children_hnf]
 >> Q.PAT_X_ASSUM ‘m = m’ K_TAC (* a bit strange *)
 (* Case 2 (easy: vs = vs' /\ m = m') *)
 >> reverse (Cases_on ‘y = v’)
 >- (simp [LAMl_SUB, appstar_SUB] \\
     DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
     Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM) \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘M0' = LAMl vs (VAR y @* args')’ by METIS_TAC [principal_hnf_thm'] \\
    ‘n = n'’ by rw [Abbr ‘n'’] \\
     POP_ASSUM (rfs o wrap o SYM) >> T_TAC \\
     qunabbrev_tac ‘n'’ \\
     Q.PAT_X_ASSUM ‘vs = vs'’ (rfs o wrap o SYM) \\
    ‘hnf (LAMl vs (VAR y @* args))’ by rw [hnf_appstar] \\
     fs [Abbr ‘M1'’, principal_hnf_beta_reduce] \\
     Q.PAT_X_ASSUM ‘args' = Ms’ (rfs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘m' = m’     (rfs o wrap) \\
     Q.PAT_X_ASSUM ‘j = j'’     (rfs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘zs = zs'’   (rfs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘z = z'’     (rfs o wrap o SYM) \\
     fs [Abbr ‘m'’] >> T_TAC \\
    ‘LENGTH args' = m’ by simp [Abbr ‘args'’] \\
     qunabbrev_tac ‘zs’ \\
     Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
    ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
     reverse (Cases_on ‘h < m’)
     >- (simp [Abbr ‘M2’, Abbr ‘M2'’, vsubterm_var_not_none] \\
         reverse CONJ_TAC
         >- (SYM_TAC >> MATCH_MP_TAC lemma14b \\
             Cases_on ‘q = []’
             >- (simp [vsubterm_def] \\
                 Suff ‘z NOTIN Y’ >- METIS_TAC [] \\
                 qunabbrev_tac ‘Y’ \\
                 Know ‘z = RNEW r (n + j) X’
                 >- (simp [Abbr ‘z’, Abbr ‘zs’, RNEW_def] \\
                    ‘n + SUC j = SUC (j + n)’ by simp [] \\
                     POP_ASSUM (REWRITE_TAC o wrap)) >> Rewr' \\
                 MATCH_MP_TAC RNEW_thm >> art []) \\
             simp [vsubterm_var, FV_thm] \\
             qabbrev_tac ‘l = LENGTH q’ \\
            ‘0 < l’ by simp [Abbr ‘l’, LENGTH_NON_NIL] \\
             qabbrev_tac ‘r' = l + SUC r - 1’ \\
            ‘r < r'’ by simp [Abbr ‘r'’] \\
            ‘RNEW r' (LAST q) X NOTIN X UNION RANK r'’ by simp [RNEW_thm] \\
             Suff ‘v IN X UNION RANK r'’ >- METIS_TAC [] \\
             Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
             qunabbrev_tac ‘Y’ \\
             Suff ‘RANK r SUBSET RANK r'’ >- SET_TAC [] \\
             MATCH_MP_TAC RANK_MONO >> simp []) \\
         Know ‘vsubterm_width ([P/v] M) (h::q) <= d <=>
               m <= d /\ h < d /\ MAX_LIST q < d’
         >- (MATCH_MP_TAC vsubterm_width_le_eq_first \\
             qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n’] >> simp [] \\
             simp [FV_SUB] \\
             Cases_on ‘v IN FV M’ >> simp [] \\
             Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
             SET_TAC []) >> Rewr' \\
         simp [] \\
         Q_TAC (TRANS_TAC LET_TRANS) ‘MAX_LIST t’ \\
         CONJ_TAC >- (MATCH_MP_TAC MAX_LIST_LE_PREFIX >> art []) \\
         Q_TAC (TRANS_TAC LTE_TRANS) ‘w’ >> art [] \\
         simp [Abbr ‘w’, vsubterm_width_def, LESS_EQ]) \\
  (* now we have ‘h < m’ (the regular case) *)
     Q.PAT_X_ASSUM ‘vsubterm X M2 q (SUC r) <> NONE’ MP_TAC \\
     simp [Abbr ‘M2’, Abbr ‘M2'’] \\
  (* applying vsubterm_width_induction_lemma' *)
     Know ‘vsubterm_width ([P/v] M) (h::q) <= d <=>
           h < d /\ m <= d /\ vsubterm_width (EL h args') q <= d’
     >- (MATCH_MP_TAC vsubterm_width_induction_lemma' \\
         qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n’, ‘vs’, ‘VAR y @* args'’] \\
         simp [principal_hnf_beta_reduce]) >> Rewr' \\
     simp [] >> DISCH_TAC \\
  (* now applying IH *)
     fs [Abbr ‘m’, Abbr ‘args'’, EL_MAP] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘t’ >> simp [] \\
     CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM) \\
         Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM) \\
         MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘LENGTH args’, ‘vs’, ‘M1’] >> simp []) \\
     CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC \\
         Q_TAC (unbeta_tac [vsubterm_def]) ‘vsubterm X M (h::t) r’ \\
         Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM) \\
         Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM) \\
         simp []) \\
     reverse CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
         qunabbrev_tac ‘Y’ >> simp [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     Q.PAT_X_ASSUM ‘w <= d’ MP_TAC \\
     qunabbrev_tac ‘w’ \\
     qabbrev_tac ‘m = LENGTH args’ \\
     Suff ‘vsubterm_width M (h::t) <= d <=>
           h < d /\ m <= d /\ vsubterm_width (EL h args) t <= d’ >- simp [] \\
     MATCH_MP_TAC vsubterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’] >> simp [] \\
     Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM) \\
     simp [])
 (* Case 3 (hard, vs <<= vs' *)
 >> Q.PAT_X_ASSUM ‘y = v’ (fs o wrap o SYM)
 >> simp [Abbr ‘P’]
 >> DISCH_TAC (* [permutator d/y] M -h->* ... *)
 (* applying hreduce_permutator_thm with a suitable excluded list

    NOTE: ‘vs'’ is to be proved extending vs (vs' = vs ++ ys), and we will need
          DISJOINT (set (SNOC z xs)) (set ys), thus here ‘set vs'’ is used.

    LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs)))

    The goal is make vs ++ xs ++ [Z] = vs', whose LENGTH is n + d - m + 1
  *)
 >> MP_TAC (Q.SPECL [‘set vs'’, ‘d’, ‘args'’] hreduce_permutator_thm) >> simp []
 >> DISCH_THEN (qx_choosel_then [‘xs’, ‘Z’] STRIP_ASSUME_TAC)
 (* calculating head reductions of ‘[permutator d/y] M’ *)
 >> Know ‘[permutator d/y] M -h->*
            LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs)))’
 >- (MATCH_MP_TAC hreduce_TRANS \\
     Q.EXISTS_TAC ‘LAMl vs (permutator d @* args')’ >> rw [])
 >> DISCH_TAC
 >> Know ‘M0' = LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs)))’
 >- (‘hnf (LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs))))’
       by simp[hnf_LAMl, hnf_appstar] \\
     METIS_TAC [principal_hnf_thm'])
 >> DISCH_TAC
 >> qabbrev_tac ‘P = permutator d’
 >> Q.PAT_X_ASSUM ‘P @* args' -h->* _’                 K_TAC
 >> Q.PAT_X_ASSUM ‘[P/y] M -h->* LAMl vs (P @* args')’ K_TAC
 >> Know ‘LENGTH Ms = hnf_children_size M0'’
 >- (SYM_TAC >> MATCH_MP_TAC hnf_children_size_alt \\
     qabbrev_tac ‘M' = [P/y] M’ \\
     qexistsl_tac [‘X’, ‘M'’, ‘r’, ‘n'’, ‘vs'’, ‘M1'’] >> simp [])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> Know ‘m <= m'’
 >- (qunabbrevl_tac [‘m’, ‘m'’] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [GSYM appstar_APPEND])
 >> DISCH_TAC
 (* 0            h1   m    h2    m' (= d, h < d)
    |<---- args' ---->|<-- xs -->|          M0'
                           d-m
  *)
 >> Know ‘m' = d’
 >- (qunabbrev_tac ‘m'’ \\
     Q.PAT_X_ASSUM ‘_ = LENGTH Ms’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘M0' = _’ (REWRITE_TAC o wrap) \\
     simp [GSYM appstar_APPEND])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘M0 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M0' = LAMl vs _’ (ASSUME_TAC o SYM)
 >> fs []
 >> ‘h < d’ by simp []
 >> fs [Abbr ‘M2'’]
 >> ‘j' = 0’ by simp [Abbr ‘j'’]
 >> POP_ASSUM (fs o wrap)
 >> qunabbrevl_tac [‘j'’, ‘zs'’, ‘z'’]
 (* stage work *)
 >> qunabbrev_tac ‘vs'’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’
 >> Know ‘n' = n + LENGTH xs + 1’
 >- (qunabbrevl_tac [‘n’, ‘n'’] \\
     Q.PAT_X_ASSUM ‘_ = M0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M0'’ (REWRITE_TAC o wrap o SYM) \\
    ‘!t. LAMl vs (LAMl xs (LAM Z t)) = LAMl (vs ++ xs ++ [Z]) t’
        by rw [LAMl_APPEND] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘_ = M1’  (REWRITE_TAC o wrap o SYM) \\
     simp [LAMl_size_LAMl])
 >> DISCH_TAC
 >> Know ‘vs <<= vs'’
 >- (qunabbrevl_tac [‘vs’, ‘vs'’] \\
     MATCH_MP_TAC RNEWS_prefix >> rw [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> rename1 ‘vs' = vs ++ ys’ (* l -> ys *)
 (* stage work *)
 >> gs [MAP_APPEND, appstar_APPEND, LIST_TO_SET_APPEND, ALL_DISTINCT_APPEND]
 (* applying hreduce_BETA_extended *)
 >> Know ‘M0' @* MAP VAR vs @* MAP VAR ys -h->*
          LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs)) @* MAP VAR ys’
 >- (Q.PAT_X_ASSUM ‘_ = M0'’ (REWRITE_TAC o wrap o SYM) \\
     REWRITE_TAC [hreduce_BETA_extended])
 >> REWRITE_TAC [GSYM LAMl_SNOC]
 >> DISCH_TAC
 (* applying hreduce_LAMl_appstar *)
 >> qabbrev_tac ‘xs' = SNOC Z xs’
 >> qabbrev_tac ‘t' = VAR Z @* args' @* MAP VAR xs’
 >> Know ‘LAMl xs' t' @* MAP VAR ys -h->* fromPairs xs' (MAP VAR ys) ' t'’
 >- (MATCH_MP_TAC hreduce_LAMl_appstar >> simp [Abbr ‘xs'’] \\
     rw [EVERY_MEM, MEM_MAP] >> REWRITE_TAC [FV_thm] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set ys’ >> art [] \\
     rw [SUBSET_DEF])
 >> Know ‘LENGTH ys = d - m + 1’
 >- (Q.PAT_X_ASSUM ‘n + LENGTH ys = _’ MP_TAC \\
     Know ‘m <= d’ >- simp [] \\
     numLib.ARITH_TAC)
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘n + LENGTH ys = _’ K_TAC
 >> ‘FDOM (fromPairs xs' (MAP VAR ys)) = set xs'’
      by simp [FDOM_fromPairs, Abbr ‘xs'’]
 >> ASM_SIMP_TAC std_ss [Abbr ‘t'’, ssub_appstar, Abbr ‘xs'’]
 >> qabbrev_tac ‘fm = fromPairs (SNOC Z xs) (MAP VAR ys)’
 >> Know ‘MAP ($' fm) args' = args'’
 >- (simp [LIST_EQ_REWRITE, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC ssub_14b' >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> simp [MEM_EL] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> Rewr'
 >> Know ‘?z'. fm ' (VAR Z) = VAR z'’
 >- (simp [Abbr ‘fm’] \\
     qabbrev_tac ‘ls = SNOC Z xs’ \\
     Know ‘Z = LAST ls’ >- rw [Abbr ‘ls’, LAST_SNOC] \\
    ‘ls <> []’ by rw [Abbr ‘ls’] \\
     simp [LAST_EL] >> DISCH_THEN K_TAC \\
     qabbrev_tac ‘i = PRE (LENGTH ls)’ \\
     Q.EXISTS_TAC ‘EL i ys’ \\
    ‘i < LENGTH ys’ by rw [Abbr ‘i’, Abbr ‘ls’] \\
    ‘VAR (EL i ys) :term = EL i (MAP VAR ys)’ by rw [EL_MAP] >> POP_ORW \\
     MATCH_MP_TAC fromPairs_FAPPLY_EL \\
     simp [Abbr ‘i’, Abbr ‘ls’])
 >> STRIP_TAC >> POP_ORW
 >> qabbrev_tac ‘ls = MAP ($' fm) (MAP VAR xs)’
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
 >> ‘M1' = VAR z' @* (args' ++ ls)’ by METIS_TAC [principal_hnf_thm]
 >> Q.PAT_X_ASSUM ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* _’ K_TAC
 (* applying vsubterm_width_induction_lemma again *)
 >> Know ‘vsubterm_width ([P/y] M) (h::q) <= d <=>
          h < d /\ m' <= d /\ vsubterm_width (EL h Ms) q <= d’
 >- (MATCH_MP_TAC vsubterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n'’, ‘vs'’, ‘M1'’] \\
     simp [appstar_APPEND])
 >> Rewr'
 >> simp []
 (* extra case for vsubterm
    0                 m    h    d/m' (h < d)
    |<---- args' ---->|<-- ls -->|   M1'
                        j  d-m       (j = h - m)
  *)
 >> reverse (Cases_on ‘h < m’)
 >- (simp [Abbr ‘M2’] \\
    ‘Ms = args' ++ ls’ by simp [Abbr ‘Ms’] >> POP_ORW \\
     Know ‘EL h (args' ++ ls) = EL (h - LENGTH args') ls’
     >- (irule EL_APPEND2 >> simp [Abbr ‘args'’]) >> Rewr' \\
     fs [] >> T_TAC \\
    ‘j < LENGTH xs’ by simp [Abbr ‘j’] \\
     simp [Abbr ‘ls’, MAP_MAP_o, EL_MAP, EL_MEM] \\
    ‘EL j xs = EL j (SNOC Z xs)’ by simp [EL_SNOC] >> POP_ORW \\
     Know ‘FAPPLY fm (EL j (SNOC Z xs)) = EL j (MAP VAR ys)’
     >- (qunabbrev_tac ‘fm’ \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     simp [EL_MAP] \\
     qunabbrev_tac ‘zs’ \\
     Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
    ‘zs <> []’ by simp [GSYM LENGTH_NON_NIL] \\
     simp [Abbr ‘z’, LAST_EL] \\
    ‘PRE (n + SUC j) = n + j’ by simp [] >> POP_ORW \\
    ‘EL j ys = EL (n + j) vs'’ by simp [EL_APPEND2] >> POP_ORW \\
     Know ‘zs = TAKE (n + SUC j) vs'’
     >- (qunabbrevl_tac [‘zs’, ‘vs'’] \\
         MATCH_MP_TAC RNEWS_TAKE >> simp []) >> Rewr' \\
     Know ‘EL (n + j) (TAKE (n + SUC j) vs') = EL (n + j) vs'’
     >- (MATCH_MP_TAC EL_TAKE >> simp []) >> Rewr' \\
     qabbrev_tac ‘z = EL (n + j) vs'’ \\
     Q.PAT_X_ASSUM ‘vs' = vs ++ ys’ K_TAC \\
     qunabbrev_tac ‘vs'’ \\
     Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”,
                       “d + (n + 1) - (m :num)”)) ‘X’ \\
     Know ‘DISJOINT (set vs') Y’
     >- (simp [Abbr ‘Y’, DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs'’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> DISCH_TAC \\
     Know ‘y <> z’
     >- (Suff ‘z NOTIN Y’ >- METIS_TAC [] \\
         Suff ‘MEM z vs'’
         >- (POP_ASSUM MP_TAC >> rw [DISJOINT_ALT]) \\
         simp [EL_MEM, Abbr ‘z’]) >> DISCH_TAC \\
     Know ‘SUC (MAX_LIST q) <= d’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘w’ >> art [] \\
         simp [Abbr ‘w’, vsubterm_width_def] \\
         NTAC 2 DISJ2_TAC \\
         MATCH_MP_TAC MAX_LIST_LE_PREFIX >> art []) >> Rewr \\
     Cases_on ‘q = []’ >- simp [vsubterm_def] \\
     simp [vsubterm_var] \\
     SYM_TAC >> MATCH_MP_TAC lemma14b >> simp [FV_thm] \\
     qabbrev_tac ‘r' = LENGTH q + SUC r - 1’ \\
     Suff ‘RNEW r' (LAST q) X NOTIN Y’ >- METIS_TAC [] \\
  (* applying RNEW_thm *)
     qunabbrev_tac ‘Y’ \\
     Know ‘RNEW r' (LAST q) X NOTIN X UNION RANK r'’ >- simp [RNEW_thm] \\
     Suff ‘RANK r SUBSET RANK r'’ >- SET_TAC [] \\
     MATCH_MP_TAC RANK_MONO >> simp [Abbr ‘r'’])
 >> Know ‘EL h Ms = EL h args'’
 >- (simp [Abbr ‘Ms’, hnf_children_hnf] \\
     MATCH_MP_TAC EL_APPEND1 >> art [])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘vsubterm X M2 q (SUC r) <> NONE’ MP_TAC
 >> simp [Abbr ‘args'’, EL_MAP, Abbr ‘M2’]
 >> qabbrev_tac ‘N = EL h args’
 >> DISCH_TAC
 (* applying IH, finally *)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘t’ >> simp []
 >> CONJ_TAC (* FV N SUBSET X UNION RANK (SUC r) *)
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     Q.PAT_X_ASSUM ‘LAMl vs M1 = M0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘VAR y @* args = M1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC \\
     Q_TAC (unbeta_tac [vsubterm_def]) ‘vsubterm X M (h::t) r’ \\
     Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM) \\
     simp [])
 >> reverse CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     qunabbrev_tac ‘Y’ >> simp [] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 >> Q.PAT_X_ASSUM ‘w <= d’ MP_TAC
 >> qunabbrev_tac ‘w’
 >> Suff ‘vsubterm_width M (h::t) <= d <=>
          h < d /\ m <= d /\ vsubterm_width (EL h args) t <= d’ >- simp []
 >> MATCH_MP_TAC vsubterm_width_induction_lemma'
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’] >> simp []
 >> Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM)
 >> simp []
QED

(* This theorem can be repeatedly applied for ‘M ISUB ss’ *)
Theorem vsubterm_subst_permutator_cong :
    !p X M r y P d. FINITE X /\ FV M SUBSET X UNION RANK r /\
                    vsubterm X M p r <> NONE /\
                    P = permutator d /\ y IN X UNION RANK r /\
                    vsubterm_width M p <= d
                ==> vsubterm X ([P/y] M) p r <> NONE /\
                    vsubterm_width ([P/y] M) p <= d /\
                    vsubterm' X ([P/y] M) p r = [P/y] (vsubterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> irule vsubterm_subst_permutator_cong_lemma >> art []
 >> Q.EXISTS_TAC ‘p’ >> rw []
QED

(* NOTE: This reduced version is for applying MATCH_MP_TAC later *)
Theorem vsubterm_subst_permutator_cong'[local] :
    !p X M r y P d. FINITE X /\ FV M SUBSET X UNION RANK r /\
                    vsubterm X M p r <> NONE /\
                    P = permutator d /\ y IN X UNION RANK r /\
                    vsubterm_width M p <= d
                ==> vsubterm X ([P/y] M) p r <> NONE /\
                    vsubterm' X ([P/y] M) p r = [P/y] (vsubterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M’, ‘r’, ‘y’, ‘P’, ‘d’]
                    vsubterm_subst_permutator_cong) >> rw []
QED

(* cf. Boehm_transform_exists_lemma (for subterm) *)
Theorem Boehm_transform_exists_lemma' :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
         ?pi. Boehm_transform pi /\
              is_ready (apply pi M) /\
              FV (apply pi M) SUBSET X UNION RANK (SUC r) /\
              ?v P. closed P /\
                   !q. q <<= p /\ q <> [] /\
                       vsubterm X M q r <> NONE ==>
                       vsubterm X (apply pi M) q r <> NONE /\
                       vsubterm' X (apply pi M) q r = [P/v] (vsubterm' X M q r)
Proof
    rpt STRIP_TAC
 (* trivial case: M is unsolvable *)
 >> reverse (Cases_on ‘solvable M’)
 >- (Q.EXISTS_TAC ‘[]’ >> simp [is_ready_def] \\
     CONJ_TAC
     >- (Suff ‘RANK r SUBSET RANK (SUC r)’ >- ASM_SET_TAC [] \\
         simp [RANK_MONO]) \\
     qabbrev_tac ‘v = RNEW (r + LENGTH p) 0 X’ \\
     qexistsl_tac [‘v’, ‘I’] \\
     simp [closed_def, FV_I] \\
     rpt STRIP_TAC \\
    ‘LENGTH q <= LENGTH p’ by PROVE_TAC [IS_PREFIX_LENGTH] \\
     SYM_TAC >> MATCH_MP_TAC lemma14b \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘q’, ‘r’] FV_vsubterm_upperbound) >> rw [] \\
    ‘v NOTIN X UNION (RANK (r + LENGTH p))’ by PROVE_TAC [RNEW_thm] \\
     CCONTR_TAC >> fs [] \\
    ‘v IN X UNION RANK (r + LENGTH q)’ by PROVE_TAC [SUBSET_DEF] \\
     fs [IN_UNION] >- PROVE_TAC [] \\
     Suff ‘RANK (r + LENGTH q) SUBSET RANK (r + LENGTH p)’ >- ASM_SET_TAC [] \\
     simp [RANK_MONO])
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principal_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 (* applying HNF_TAC *)
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> qabbrev_tac ‘m = LENGTH args’
 (* using ‘subterm_width’ and applying subterm_width_thm *)
 >> qabbrev_tac ‘d = vsubterm_width M p’
 >> Know ‘m <= d’
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width M p’ \\
     simp [Abbr ‘d’] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_first) \\
     simp [])
 >> DISCH_TAC
 (* applying vsubterm_width_thm *)
 >> ‘!e. MEM e p ==> e < d’ by PROVE_TAC [vsubterm_width_thm]
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
 >> Know ‘solvable (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC solvable_appstar' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 (* NOTE: Z contains ‘vs’ in addition to X and FV M *)
 >> qabbrev_tac ‘Z = X UNION FV M UNION set vs’
 >> ‘FINITE Z’ by (rw [Abbr ‘Z’] >> rw [])
 >> Know ‘FV M1 SUBSET Z’
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV M0 UNION set vs’ \\
     reverse CONJ_TAC
     >- (qunabbrev_tac ‘Z’ \\
         Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
     ‘FV M0 UNION set vs = FV (M0 @* MAP VAR vs)’ by rw [FV_appstar_MAP_VAR] \\
      POP_ORW \\
      qunabbrev_tac ‘M1’ \\
      MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 (* NOTE: new method avoiding calling ‘alloc’ directly *)
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + d - m + 1”)) ‘X’
 >> ‘DISJOINT (set zs) (FV M)’ by PROVE_TAC [subterm_disjoint_lemma]
 >> qabbrev_tac ‘l = DROP n zs’
 >> ‘ALL_DISTINCT l’ by PROVE_TAC [ALL_DISTINCT_DROP]
 >> ‘LENGTH l = d - m + 1’ by simp [Abbr ‘l’]
 >> ‘l <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘TAKE n zs = vs’ by simp [Abbr ‘zs’, Abbr ‘vs’, TAKE_RNEWS]
 >> Know ‘DISJOINT (set l) (set vs)’
 >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT zs’ MP_TAC \\
    ‘zs = TAKE n zs ++ DROP n zs’ by simp [TAKE_DROP] >> POP_ORW \\
     POP_ORW \\
     rw [ALL_DISTINCT_APPEND] \\
     rw [DISJOINT_ALT'])
 >> DISCH_TAC
 >> Know ‘set l SUBSET set zs’
 >- (‘zs = TAKE n zs ++ DROP n zs’ by simp [TAKE_DROP] >> POP_ORW \\
     simp [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set l) Z’
 >- (rw [Abbr ‘Z’, DISJOINT_UNION'] >|
     [ MATCH_MP_TAC DISJOINT_SUBSET' \\
       Q.EXISTS_TAC ‘set zs’ >> art [],
       MATCH_MP_TAC DISJOINT_SUBSET' \\
       Q.EXISTS_TAC ‘set zs’ >> art [] ])
 >> DISCH_TAC
 (* now recover the old definition of Y *)
 >> Know ‘DISJOINT (set l) (FV M1)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘Z’ >> art [])
 >> ASM_REWRITE_TAC [FV_appstar, FV_thm]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> Q.PAT_X_ASSUM ‘DISJOINT (set l) {y}’ (* ~MEM y l *)
      (STRIP_ASSUME_TAC o (SIMP_RULE (srw_ss()) [DISJOINT_ALT']))
 >> qabbrev_tac ‘as = FRONT l’
 >> ‘LENGTH as = d - m’ by rw [Abbr ‘as’, LENGTH_FRONT]
 >> qabbrev_tac ‘b = LAST l’
 >> Know ‘l = SNOC b as’
 >- ASM_SIMP_TAC std_ss [Abbr ‘as’, Abbr ‘b’, SNOC_LAST_FRONT]
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
 >> qabbrev_tac ‘pi = p3 ++ p2 ++ p1’
 >> Know ‘apply pi M == VAR b @* args' @* MAP VAR as’
 >- (MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply pi M0’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                  CONJ_TAC >- art [] \\
                  qunabbrev_tac ‘M0’ \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principal_hnf' >> art []) \\
     SIMP_TAC std_ss [Once Boehm_apply_APPEND, Abbr ‘pi’] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply (p3 ++ p2) M1’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] \\
                  MATCH_MP_TAC Boehm_transform_APPEND >> art []) \\
     ONCE_REWRITE_TAC [Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply p3 (P @* args')’ >> art [] \\
     MATCH_MP_TAC Boehm_apply_lameq_cong >> rw [])
 >> DISCH_TAC
 >> Know ‘solvable (apply pi M)’
 >- (Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
     >- METIS_TAC [lameq_solvable_cong] \\
     MATCH_MP_TAC hnf_solvable \\
     simp [GSYM appstar_APPEND, hnf_appstar])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘principal_hnf (apply pi M) = VAR b @* args' @* MAP VAR as’
 >- (Q.PAT_X_ASSUM ‘Boehm_transform pi’         K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p1’         K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p2’         K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p3’         K_TAC \\
     Q.PAT_X_ASSUM ‘apply p1 M0 == M1’          K_TAC \\
     Q.PAT_X_ASSUM ‘apply p2 M1 = P @* args'’   K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’ K_TAC \\
  (* preparing for principal_hnf_denude_thm *)
     Q.PAT_X_ASSUM ‘apply pi M == _’ MP_TAC \\
     simp [Boehm_apply_APPEND, Abbr ‘pi’, Abbr ‘p1’, Abbr ‘p2’, Abbr ‘p3’,
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
  (* applying principal_hnf_permutator *)
     Know ‘VAR b @* args' @* MAP VAR as =
           principal_hnf ([P/y] (VAR y @* args @* MAP VAR (SNOC b as)))’
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
         MATCH_MP_TAC principal_hnf_permutator >> rw []) >> Rewr' \\
  (* applying principal_hnf_SUB_cong *)
     MATCH_MP_TAC principal_hnf_SUB_cong \\
     CONJ_TAC (* has_hnf #1 *)
     >- (simp [GSYM solvable_iff_has_hnf, GSYM appstar_APPEND] \\
        ‘M0 == M’ by rw [lameq_principal_hnf', Abbr ‘M0’] \\
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
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf #2 *)
     >- (REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
         >- PROVE_TAC [lameq_solvable_cong] \\
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
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
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
  (* applying the celebrating principal_hnf_denude_thm

     NOTE: here ‘DISJOINT (set vs) (FV M)’ is required, and this means that
          ‘vs’ must exclude ‘FV M’ instead of just ‘FV M0’.
   *)
     MATCH_MP_TAC principal_hnf_denude_thm >> rw [])
 >> DISCH_TAC
 (* applying is_ready_alt' *)
 >> CONJ_TAC
 >- (simp [is_ready_alt, Abbr ‘pi’] \\
     qexistsl_tac [‘b’, ‘args' ++ MAP VAR as’] \\
     CONJ_TAC
     >- (MP_TAC (Q.SPEC ‘VAR b @* args' @* MAP VAR as’
                   (MATCH_MP principal_hnf_thm'
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
     fs [LIST_TO_SET_SNOC] >> T_TAC \\
     Suff ‘FV e SUBSET Y’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrev_tac ‘Y’ \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘BIGUNION (IMAGE FV (set args'))’ \\
     CONJ_TAC
     >- (rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
         Q.EXISTS_TAC ‘e’ >> art []) \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE, MEM_EL] \\
     rename1 ‘i < LENGTH args'’ \\
     Q.EXISTS_TAC ‘EL i args’ \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘i’ >> art []) \\
     POP_ASSUM MP_TAC \\
     Suff ‘FV (EL i args') SUBSET FV (EL i args)’ >- METIS_TAC [SUBSET_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* extra goal: FV (apply pi M) SUBSET X UNION RANK (SUC r) *)
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘apply pi M == _’                K_TAC \\
     Q.PAT_X_ASSUM ‘principal_hnf (apply pi M) = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’     K_TAC \\
     rpt (Q.PAT_X_ASSUM ‘Boehm_transform _’         K_TAC) \\
     POP_ASSUM MP_TAC (* solvable (apply pi M) *) \\
     simp [Boehm_apply_APPEND, Abbr ‘pi’, Abbr ‘p1’, Abbr ‘p2’, Abbr ‘p3’,
           Boehm_apply_MAP_rightctxt'] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) (* l = SNOC b as *) \\
     DISCH_TAC \\
     reverse CONJ_TAC
     >- (Suff ‘set l SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set zs’ >> art [] \\
         qunabbrev_tac ‘zs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp []) \\
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
 >> qexistsl_tac [‘y’, ‘P’] >> art []
 >> Q.X_GEN_TAC ‘q’
 >> STRIP_TAC (* push ‘q <<= p’ to assumptions *)
 (* LHS rewriting from M to M0 *)
 >> Know ‘vsubterm X (apply pi M) q r =
          vsubterm X (VAR b @* args' @* MAP VAR as) q r’
 >- (Q.PAT_X_ASSUM ‘_ = VAR b @* args' @* MAP VAR as’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     qabbrev_tac ‘t = apply pi M’ \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC vsubterm_of_principal_hnf >> art [])
 >> Rewr'
 (* stage cleanups *)
 >> Q.PAT_X_ASSUM ‘solvable (apply pi M)’          K_TAC
 >> Q.PAT_X_ASSUM ‘principal_hnf (apply pi M) = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘apply pi M == _’                K_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform pi’             K_TAC
 (* stage work, now ‘M’ is eliminated from both sides! *)
 >> Cases_on ‘q’ >- FULL_SIMP_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘h::t <> []’ K_TAC
 >> Know ‘h < d’
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC IS_PREFIX_MEM \\
     Q.EXISTS_TAC ‘h::t’ >> simp [])
 >> DISCH_TAC
 >> REWRITE_TAC [GSYM appstar_APPEND]
 >> qabbrev_tac ‘args2 = args' ++ MAP VAR as’
 >> ‘LENGTH args2 = d’ by simp [Abbr ‘args2’]
 >> Know ‘vsubterm X (VAR b @* args2) (h::t) r =
          vsubterm X (EL h args2) t (SUC r)’
 >- (MP_TAC (Q.SPECL [‘X’, ‘b’, ‘args2’, ‘h’, ‘t’, ‘r’]
                     vsubterm_of_absfree_hnf_explicit) >> simp [])
 >> Rewr'
 >> reverse (Cases_on ‘h < m’)
 >- (Know ‘EL h args2 = EL (h - LENGTH args') (MAP VAR as)’
     >- (qunabbrev_tac ‘args2’ \\
         MATCH_MP_TAC EL_APPEND2 >> simp []) \\
     simp [EL_MAP] >> DISCH_THEN K_TAC \\
  (* 0                m      h    d
     |<---- args' ---->|<---as---->|
     |<---- args  ---->| n, n+1, n+2
   *)
     Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC \\
    ‘hnf_children M1 = args’ by simp [] \\
    ‘hnf_headvar M1 = y’ by simp [] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM) \\
     Q_TAC (unbeta_tac [vsubterm_def]) ‘vsubterm X M (h::t) r’ \\
     reverse (Cases_on ‘t = []’)
     >- (simp [vsubterm_var] \\
         SYM_TAC >> MATCH_MP_TAC lemma14b \\
         simp [FV_thm] \\
         MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’]
                         subterm_headvar_lemma) >> simp [] \\
         Suff ‘RNEW (LENGTH t + SUC r - 1) (LAST t) X NOTIN
               X UNION RANK (SUC r)’ >- METIS_TAC [] \\
         qabbrev_tac ‘r' = LENGTH t + SUC r - 1’ \\
         MP_TAC (Q.SPECL [‘r'’, ‘LAST t’, ‘X’] RNEW_thm) >> simp [] \\
         Suff ‘RANK (SUC r) SUBSET RANK r'’ >- SET_TAC [] \\
         MATCH_MP_TAC RANK_MONO \\
        ‘0 < LENGTH t’ by simp [LENGTH_NON_NIL] \\
         simp [Abbr ‘r'’]) \\
     simp [] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’]
                     subterm_headvar_lemma') >> simp [] >> DISCH_TAC \\
     qabbrev_tac ‘i = n + SUC (h - m)’ \\
     Know ‘RNEWS r i X = TAKE i zs’
     >- (qunabbrev_tac ‘zs’ \\
         MATCH_MP_TAC RNEWS_TAKE >> simp [Abbr ‘i’]) >> Rewr' \\
     Know ‘LAST (TAKE i zs) = EL (i - 1) zs’
     >- (MATCH_MP_TAC (REWRITE_RULE [PRE_SUB1] LAST_TAKE_EL) \\
         simp [Abbr ‘i’]) >> Rewr' \\
     simp [Abbr ‘i’] \\
    ‘n + SUC (h - m) - 1 = n + (h - m)’ by simp [] >> POP_ORW \\
     Know ‘EL (h - m) as = EL (h - m) l’
     >- (qunabbrev_tac ‘as’ \\
         MATCH_MP_TAC EL_FRONT >> simp [NULL_EQ_NIL]) >> Rewr' \\
     Know ‘EL (n + (h - m)) zs = EL (h - m) l’
     >- simp [Abbr ‘l’, EL_DROP] >> Rewr' \\
     SYM_TAC >> MATCH_MP_TAC lemma14b \\
     Q.PAT_X_ASSUM ‘l = SNOC b as’ K_TAC \\
     simp [FV_thm] \\
     reverse (Q.PAT_X_ASSUM ‘y IN FV M UNION set vs’
                (STRIP_ASSUME_TAC o REWRITE_RULE [IN_UNION]))
     >- (CCONTR_TAC >> rfs [] \\
         Q.PAT_X_ASSUM ‘~MEM y l’ MP_TAC \\
         simp [MEM_EL] \\
         Q.EXISTS_TAC ‘h - m’ >> simp []) \\
     simp [Abbr ‘l’, EL_DROP] \\
     qabbrev_tac ‘i = h + n - m’ \\
    ‘n <= i /\ i < LENGTH zs’ by simp [Abbr ‘i’] \\
     Know ‘y IN X UNION RANK r’ >- PROVE_TAC [SUBSET_DEF] \\
     simp [IN_UNION] >> STRIP_TAC
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set zs) X’ MP_TAC \\
         simp [DISJOINT_ALT'] \\
         CCONTR_TAC >> rfs [] \\
         Q.PAT_X_ASSUM ‘!x. x IN X ==> ~MEM x zs’ (MP_TAC o Q.SPEC ‘y’) \\
         simp [MEM_EL] \\
         Q.EXISTS_TAC ‘i’ >> simp []) \\
     MP_TAC (Q.SPECL [‘r’, ‘n + d - m + 1’, ‘X’]
                     DISJOINT_RNEWS_RANK') >> simp [] \\
     simp [DISJOINT_ALT'] \\
     DISCH_THEN (MP_TAC o Q.SPEC ‘y’) >> art [] \\
     DISCH_TAC \\
     CCONTR_TAC >> rfs [] \\
     Q.PAT_X_ASSUM ‘~MEM y zs’ MP_TAC \\
     simp [MEM_EL] \\
     Q.EXISTS_TAC ‘i’ >> simp [])
 (* eliminating ‘MAP VAR as’ *)
 >> Q.PAT_X_ASSUM ‘LENGTH args2 = d’ K_TAC
 >> qunabbrev_tac ‘args2’
 >> Know ‘EL h (args' ++ MAP VAR as) = EL h args'’
 >- (MATCH_MP_TAC EL_APPEND1 >> rw [])
 >> Rewr'
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC
 >> Know ‘vsubterm X M (h::t) r = vsubterm X (EL h args) t (SUC r)’
 >- (‘hnf_children M1 = args’ by simp [] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM) \\
     Q_TAC (unbeta_tac [vsubterm_def]) ‘vsubterm X M (h::t) r’)
 >> Rewr'
 (* Now: subterm' Z (EL h args') t == [P/y] (subterm' Z (EL h args) t)

    First of all, those assumptions about p1,p2,p3 are no more needed.
  *)
 >> qunabbrev_tac ‘pi’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p1’             K_TAC
 >> Q.PAT_X_ASSUM ‘apply p1 M0 == M1’              K_TAC
 >> qunabbrev_tac ‘p1’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p2’             K_TAC
 >> Q.PAT_X_ASSUM ‘apply p2 M1 = P @* args'’       K_TAC
 >> qunabbrev_tac ‘p2’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p3’             K_TAC
 >> Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’     K_TAC
 >> qunabbrev_tac ‘p3’
 >> qabbrev_tac ‘N  = EL h args’
 >> qabbrev_tac ‘N' = EL h args'’
 (* eliminating N' *)
 >> ‘N' = [P/y] N’ by simp [EL_MAP, Abbr ‘m’, Abbr ‘N’, Abbr ‘N'’, Abbr ‘args'’]
 >> POP_ORW >> qunabbrev_tac ‘N'’
 (* cleanup args' *)
 >> Q.PAT_X_ASSUM ‘!i. i < m ==> FV (EL i args') SUBSET FV (EL i args)’ K_TAC
 >> Q.PAT_X_ASSUM ‘LENGTH args' = m’               K_TAC
 >> qunabbrev_tac ‘args'’
 (* cleanup l, as and b *)
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT l’                 K_TAC
 >> NTAC 2 (Q.PAT_X_ASSUM ‘DISJOINT (set l) _’     K_TAC)
 >> Q.PAT_X_ASSUM ‘LENGTH l = q - m + 1’           K_TAC
 >> Q.PAT_X_ASSUM ‘l <> []’                        K_TAC
 >> Q.PAT_X_ASSUM ‘l = SNOC b as’                  K_TAC
 >> Q.PAT_X_ASSUM ‘~MEM y l’                       K_TAC
 >> Q.PAT_X_ASSUM ‘LENGTH as = q - m’              K_TAC
 >> qunabbrevl_tac [‘l’, ‘as’, ‘b’]
 (* applying subterm_headvar_lemma *)
 >> Know ‘hnf_headvar M1 IN X UNION RANK (SUC r)’
 >- (MATCH_MP_TAC subterm_headvar_lemma \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘vs’] >> simp [])
 >> ASM_SIMP_TAC std_ss [hnf_head_hnf, var_name_thm]
 >> DISCH_TAC (* y IN X UNION RANK (SUC r) *)
 >> DISCH_TAC (* vsubterm X N t (SUC r) <> NONE *)
 (* applying vsubterm_subst_permutator_cong *)
 >> MATCH_MP_TAC vsubterm_subst_permutator_cong'
 >> Q.EXISTS_TAC ‘d’
 >> simp [Abbr ‘P’]
 >> CONJ_TAC
 >- (qunabbrev_tac ‘N’ >> MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 (* stage work *)
 >> Know ‘vsubterm_width M (h::t) <= d’
 >- (qunabbrev_tac ‘d’ \\
     MATCH_MP_TAC vsubterm_width_inclusive \\
     Q.EXISTS_TAC ‘p’ >> simp [])
 >> Suff ‘vsubterm_width M (h::t) <= d <=>
          h < d /\ m <= d /\ vsubterm_width (EL h args) t <= d’ >- simp []
 >> MATCH_MP_TAC vsubterm_width_induction_lemma'
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

(*---------------------------------------------------------------------------*
 *  Boehm construction for vsubterm-based "Boehm out" technique
 *---------------------------------------------------------------------------*)

(* NOTE: This version uses ‘vsubterm_width’ instead of ‘subterm_width’. *)
Definition Boehm_construction' :
    Boehm_construction' X (Ms :term list) p =
    let n_max = MAX_LIST (MAP (\e. subterm_length e p) Ms);
        d_max = MAX_LIST (MAP (\e. vsubterm_width e p) Ms) + n_max;
        k     = LENGTH Ms;
        X'    = BIGUNION (IMAGE FV (set Ms));
        vs0   = NEWS (n_max + SUC d_max + k) (X UNION X');
        vs    = TAKE n_max vs0;
        xs    = DROP n_max vs0;
        M0 i  = principal_hnf (EL i Ms);
        M1 i  = principal_hnf (M0 i @* MAP VAR vs);
        y  i  = hnf_headvar (M1 i);
        P  i  = permutator (d_max + i);
        p1    = MAP rightctxt (REVERSE (MAP VAR vs));
        p2    = REVERSE (GENLIST (\i. [P i/y i]) k);
        p3    = MAP rightctxt (REVERSE (MAP VAR xs))
    in
        p3 ++ p2 ++ p1
End

Theorem Boehm_construction_transform' :
    !X Ms p. Boehm_transform (Boehm_construction' X Ms p)
Proof
    RW_TAC std_ss [Boehm_construction']
 >> MATCH_MP_TAC Boehm_transform_APPEND
 >> reverse CONJ_TAC
 >- rw [Abbr ‘p1’, MAP_MAP_o, GSYM MAP_REVERSE]
 >> MATCH_MP_TAC Boehm_transform_APPEND
 >> CONJ_TAC
 >- rw [Abbr ‘p3’, MAP_MAP_o, GSYM MAP_REVERSE]
 >> rw [Boehm_transform_def, Abbr ‘p2’, EVERY_GENLIST]
QED

Theorem FV_apply_Boehm_construction' :
    !X Ms p r.
       FINITE X /\ p <> [] /\ 0 < r /\ Ms <> [] /\
       BIGUNION (IMAGE FV (set Ms)) SUBSET X UNION RANK r ==>
       !M. MEM M Ms ==>
           FV (apply (Boehm_construction' X Ms p) M) SUBSET X UNION RANK r
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Q.X_GEN_TAC ‘N’
 >> DISCH_TAC
 >> UNBETA_TAC [Boehm_construction'] “Boehm_construction' X Ms p”
 >> qunabbrev_tac ‘X'’
 >> qabbrev_tac ‘Y = BIGUNION (IMAGE FV (set Ms))’
 >> ‘FINITE Y’ by (rw [Abbr ‘Y’] >> rw [])
 >> simp [Boehm_apply_APPEND]
 (* eliminate p3 *)
 >> simp [Abbr ‘p3’, Boehm_apply_MAP_rightctxt']
 >> reverse CONJ_TAC
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ \\
     rw [Abbr ‘xs’, LIST_TO_SET_DROP] \\
     Suff ‘set vs0 SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> rw [ROW_SUBSET_RANK] \\
     qunabbrev_tac ‘vs0’ \\
     MATCH_MP_TAC RNEWS_SUBSET_ROW >> rw [])
 (* eliminate p2 *)
 >> qabbrev_tac ‘sub = \k. GENLIST (\i. (P i,y i)) k’
 >> Know ‘!t. apply p2 t = t ISUB sub k’
 >- (simp [Abbr ‘p2’, Abbr ‘sub’] \\
     Q.SPEC_TAC (‘k’, ‘j’) \\
     Induct_on ‘j’ >- rw [] \\
     rw [GENLIST, REVERSE_SNOC, ISUB_SNOC])
 >> DISCH_TAC
 >> simp []
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (apply p1 N) UNION FVS (sub k)’
 >> CONJ_TAC >- rw [FV_ISUB_upperbound]
 >> Know ‘!j. DOM (sub j) = IMAGE y (count j) /\ FVS (sub j) = {}’
 >- (simp [Abbr ‘sub’] \\
     Induct_on ‘j’ >- rw [DOM_DEF, FVS_DEF] \\
     rw [GENLIST, REVERSE_SNOC, DOM_DEF, FVS_DEF, COUNT_SUC, DOM_SNOC, FVS_SNOC]
     >- SET_TAC [] \\
     rw [Abbr ‘P’, FV_permutator])
 >> DISCH_TAC
 >> simp []
 (* eliminate p1 *)
 >> simp [Abbr ‘p1’, Boehm_apply_MAP_rightctxt']
 >> reverse CONJ_TAC
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ \\
     rw [Abbr ‘vs’, LIST_TO_SET_TAKE] \\
     Suff ‘set vs0 SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> rw [ROW_SUBSET_RANK] \\
     qunabbrev_tac ‘vs0’ \\
     MATCH_MP_TAC RNEWS_SUBSET_ROW >> rw [])
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Y’ >> art []
 >> rw [Abbr ‘Y’, SUBSET_DEF]
 >> Q.EXISTS_TAC ‘FV N’ >> art []
 >> Q.EXISTS_TAC ‘N’ >> art []
QED

(* NOTE: In [subtree_equiv_lemma], “subtree_equiv X M N q r” is equivalent to

     equivalent (subterm' X M q r) (subterm' X N q r)

   to avoid accessing their Boehm trees. Then we try to prove this HUGE lemma
   for vsubterm.
 *)
Theorem vsubterm_equivalent_lemma :
    !X Ms p r pi.
           FINITE X /\ p <> [] /\ 0 < r /\ Ms <> [] /\
           BIGUNION (IMAGE FV (set Ms)) SUBSET X UNION RANK r /\
           pi = Boehm_construction' X Ms p
          ==>
          (!M. MEM M Ms ==> is_ready (apply pi M)) /\
          (!q M. MEM M Ms /\ q <<= p /\
                 vsubterm X M q r <> NONE ==>
                 subterm X (apply pi M) q r <> NONE /\
                (solvable (vsubterm' X M q r) <=>
                 solvable (subterm' X (apply pi M) q r))) /\
           !q M N. MEM M Ms /\ MEM N Ms /\ q <<= p /\
                   vsubterm X M q r <> NONE /\
                   vsubterm X N q r <> NONE ==>
                   subterm X (apply pi M) q r <> NONE /\
                   subterm X (apply pi N) q r <> NONE /\
                  (equivalent (vsubterm' X M q r)
                              (vsubterm' X N q r) <=>
                   equivalent (subterm' X (apply pi M) q r)
                              (subterm' X (apply pi N) q r))
Proof
    rpt GEN_TAC >> STRIP_TAC
 (* re-create pi' as abbreviation *)
 >> POP_ORW
 >> qabbrev_tac ‘pi' = Boehm_construction' X Ms p’
 >> ‘Boehm_transform pi'’ by PROVE_TAC [Boehm_construction_transform']
 (* define Y as the set of all FVs from all Ms *)
 >> qabbrev_tac ‘Y = BIGUNION (IMAGE FV (set Ms))’
 >> ‘FINITE Y’ by (rw [Abbr ‘Y’] >> simp [])
 >> cheat
 (* TODO
 >> qabbrev_tac ‘k = LENGTH Ms’
 >> qabbrev_tac ‘M = \i. EL i Ms’ >> fs []
 >> Know ‘!i. i < k ==> FV (M i) SUBSET X UNION RANK r’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘Y SUBSET X UNION RANK r’ MP_TAC \\
     rw [Abbr ‘Y’, SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘M i’ >> art [] \\
     rw [Abbr ‘M’, EL_MEM])
 >> DISCH_TAC
 (* now derive some non-trivial assumptions *)
 >> ‘(!i q. i < k /\ q <<= p ==> subterm X (M i) q r <> NONE) /\
     (!i q. i < k /\ q <<= FRONT p ==> solvable (subterm' X (M i) q r))’
       by METIS_TAC [subterm_solvable_lemma]
 (* In the original antecedents of this theorem, some M may be unsolvable,
    and that's the easy case.
  *)
 >> Know ‘!i. i < k ==> solvable (M i)’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i q. i < k /\ q <<= FRONT p ==> solvable _’
       (MP_TAC o Q.SPECL [‘i’, ‘[]’]) >> simp [])
 >> DISCH_TAC
 >> ‘!i. i < k ==> p IN ltree_paths (BT' X (M i) r)’
      by METIS_TAC [BT_ltree_paths_thm]
 (* define M0 *)
 >> qabbrev_tac ‘M0 = \i. principal_hnf (M i)’
 >> Know ‘!i. i < k ==> hnf (M0 i)’
 >- (rw [Abbr ‘M0’] \\
     MATCH_MP_TAC hnf_principal_hnf \\
     rw [GSYM solvable_iff_has_hnf] >> fs [EVERY_EL])
 >> DISCH_TAC
 >> qabbrev_tac ‘n = \i. LAMl_size (M0 i)’
 (* NOTE: This n_max was redefined from previous ‘MAX_SET (IMAGE n (count k))’ *)
 >> qabbrev_tac ‘n_max = MAX_LIST (MAP (\e. subterm_length e p) Ms)’
 >> Know ‘!i. i < k ==> subterm_length (M i) p <= n_max’
 >- (rw [Abbr ‘n_max’] \\
     MATCH_MP_TAC MAX_LIST_PROPERTY >> rw [MEM_MAP] \\
     Q.EXISTS_TAC ‘M i’ >> rw [EL_MEM, Abbr ‘M’])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> n i <= n_max’
 >- (RW_TAC std_ss [] \\
     Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_length (M i) p’ \\
     MP_TAC (Q.SPECL [‘X’, ‘(M :num -> term) i’, ‘p’, ‘r’] subterm_length_first) \\
     simp [Abbr ‘n’])
 >> DISCH_TAC
 >> qabbrev_tac ‘d = MAX_LIST (MAP (\e. subterm_width e p) Ms)’
 >> Know ‘!i. i < k ==> subterm_width (M i) p <= d’
 >- (rw [Abbr ‘d’] \\
     MATCH_MP_TAC MAX_LIST_PROPERTY >> rw [MEM_MAP] \\
     Q.EXISTS_TAC ‘M i’ >> rw [EL_MEM, Abbr ‘M’])
 >> DISCH_TAC
 >> qabbrev_tac ‘d_max = d + n_max’
 (* ‘vs0’ excludes all free variables in Ms but is in ROW 0, then is divideded
    to vs and xs for constructing p1 and p3, resp.

    NOTE: The basic requirement of ‘vs’ is that it must be disjoint with ‘Y’
    and is at row 0. But if we exclude ‘X UNION Y’, then it also holds that
   ‘set vs SUBSET X UNION RANK r’ just like another part of ‘M’.
  *)
 >> Q_TAC (NEWS_TAC (“vs0 :string list”, “n_max + SUC d_max + k”)) ‘X UNION Y’
 >> Know ‘set vs0 SUBSET X UNION RANK (SUC r)’
 >- (Suff ‘set vs0 SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     qunabbrev_tac ‘vs0’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [])
 >> DISCH_TAC
 >> qabbrev_tac ‘vs = TAKE n_max vs0’
 >> qabbrev_tac ‘xs = DROP n_max vs0’
 >> ‘vs ++ xs = vs0’ by METIS_TAC [TAKE_DROP]
 >> Know ‘set vs SUBSET set vs0 /\ set xs SUBSET set vs0’
 >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     simp [LIST_TO_SET_APPEND])
 >> STRIP_TAC
 >> Know ‘set vs SUBSET X UNION RANK (SUC r)’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs) X /\ DISJOINT (set vs) Y /\
          DISJOINT (set xs) X /\ DISJOINT (set xs) Y’
 >- (rpt CONJ_TAC \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set vs0’ >> art [])
 >> STRIP_TAC
 >> ‘LENGTH vs = n_max’         by rw [Abbr ‘vs’]
 >> ‘LENGTH xs = SUC d_max + k’ by rw [Abbr ‘xs’]
 >> Know ‘ALL_DISTINCT vs /\ ALL_DISTINCT xs /\ DISJOINT (set xs) (set vs)’
 >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs0’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs ++ xs = vs0’ (REWRITE_TAC o wrap o SYM) \\
     simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM])
 >> STRIP_TAC
 >> ‘NEWS n_max (X UNION Y) = vs’ by simp [Abbr ‘vs’, Abbr ‘vs0’, TAKE_RNEWS]
 >> Know ‘set vs SUBSET ROW 0’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ >> art [] \\
     rw [Abbr ‘vs0’, RNEWS_SUBSET_ROW])
 >> DISCH_TAC
 >> Know ‘set vs SUBSET RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> art [] \\
     rw [ROW_SUBSET_RANK])
 >> DISCH_TAC
 (* construct p1 *)
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE (MAP VAR vs))’
 >> ‘Boehm_transform p1’ by rw [Abbr ‘p1’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* decompose M0 by hnf_cases_shared *)
 >> Know ‘!i. i < k ==> ?y args. M0 i = LAMl (TAKE (n i) vs) (VAR y @* args)’
 >- (Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     fs [Abbr ‘n’] \\
     irule (iffLR hnf_cases_shared) >> simp [] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV (EL i Ms)’ \\
     reverse CONJ_TAC
     >- (rw [Abbr ‘M0’] >> MATCH_MP_TAC principal_hnf_FV_SUBSET \\
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
 >> qabbrev_tac ‘M1 = \i. principal_hnf (M0 i @* MAP VAR vs)’
 >> Know ‘!i. i < k ==> M1 i = VAR (y i) @* args i @* DROP (n i) (MAP VAR vs)’
 >- (Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     simp [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR (y i) @* args i’ \\
     simp [GSYM MAP_DROP] \\
     qabbrev_tac ‘vs' = TAKE (n i) vs’ \\
     Know ‘MAP VAR vs = MAP VAR vs' ++ MAP VAR (DROP (n i) vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘vs'’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP (n i) vs)’ \\
     MATCH_MP_TAC principal_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
 >> ‘!i. i < k ==> hnf_headvar (M1 i) = y i’
       by rw [hnf_head_hnf, GSYM appstar_APPEND]
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
 >> Know ‘!i. i < k ==> m i <= d’
 >- (RW_TAC std_ss [] \\
     Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M i) p’ \\
     MP_TAC (Q.SPECL [‘X’, ‘(M :num -> term) i’, ‘p’, ‘r’] subterm_width_first) \\
     simp [Abbr ‘m’])
 >> DISCH_TAC
 (* NOTE: Thus P(d) is not enough to cover M1, whose ‘hnf_children_size’ is
    bounded by ‘d + n_max’. *)
 >> qabbrev_tac ‘P = \i. permutator (d_max + i)’
 (* construct p2 *)
 >> qabbrev_tac ‘p2 = REVERSE (GENLIST (\i. [P i/y i]) k)’
 >> ‘Boehm_transform p2’ by rw [Boehm_transform_def, Abbr ‘p2’, EVERY_GENLIST]
 (* p2 can be rewritten to an ISUB

    NOTE: It's important to make ‘sub’ in increasing ‘P i’ for future uses.
  *)
 >> qabbrev_tac ‘sub = \k. GENLIST (\i. (P i,y i)) k’
 >> Know ‘!t. apply p2 t = t ISUB sub k’
 >- (simp [Abbr ‘p2’, Abbr ‘sub’] \\
     Q.SPEC_TAC (‘k’, ‘j’) \\
     Induct_on ‘j’ >- rw [] \\
     rw [GENLIST, REVERSE_SNOC, ISUB_SNOC])
 >> DISCH_TAC
 (* properties of ‘sub’ (iterated substitution) *)
 >> Know ‘!j. DOM (sub j) = IMAGE y (count j) /\ FVS (sub j) = {}’
 >- (simp [Abbr ‘sub’] \\
     Induct_on ‘j’ >- rw [DOM_DEF, FVS_DEF] \\
     rw [GENLIST, REVERSE_SNOC, DOM_DEF, FVS_DEF, COUNT_SUC, DOM_SNOC, FVS_SNOC]
     >- SET_TAC [] \\
     rw [Abbr ‘P’, FV_permutator])
 >> DISCH_TAC
 (* NOTE: There may be duplicated names among all ‘y i’. The function f maps
    i to the least j such that y j = y i, and P j is the ISUB result.
  *)
 >> Know ‘!i t. i <= k /\ t IN DOM (sub i) ==>
                VAR t ISUB (sub i) = P (LEAST j. y j = t)’
 >- (Induct_on ‘i’ >- rw [Abbr ‘sub’] \\
     rw [] \\
     Know ‘!i j. P i ISUB sub j = P i’
     >- (rw [Abbr ‘sub’] \\
         MATCH_MP_TAC ISUB_unchanged >> simp [Abbr ‘P’]) >> DISCH_TAC \\
    ‘sub (SUC i) = GENLIST (\i. (P i,y i)) (SUC i)’ by rw [] >> POP_ORW \\
     REWRITE_TAC [GENLIST] \\
     simp [DOM_SNOC, ISUB_SNOC, IN_UNION] \\
     Cases_on ‘y x IN DOM (sub i)’
     >- (Q.PAT_X_ASSUM ‘!t. i <= k /\ t IN DOM (sub i) ==> _’
            (MP_TAC o Q.SPEC ‘y (x :num)’) >> rw [] \\
         MATCH_MP_TAC lemma14b >> simp [Abbr ‘P’, FV_permutator]) \\
     Know ‘VAR (y x) ISUB sub i = VAR (y x)’
     >- (MATCH_MP_TAC ISUB_unchanged \\
         Q.PAT_X_ASSUM ‘!j. DOM (sub j) = _ /\ _’ K_TAC \\
         simp [DISJOINT_ALT]) >> Rewr' \\
     POP_ASSUM MP_TAC \\
     simp [] >> DISCH_TAC \\
     Know ‘x = i’
     >- (POP_ASSUM (MP_TAC o Q.SPEC ‘x’) >> rw []) \\
     DISCH_THEN (fs o wrap) >> T_TAC \\
     LEAST_ELIM_TAC \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘i’ >> rw []) \\
     Q.X_GEN_TAC ‘j’ >> rw [Abbr ‘P’] \\
     CCONTR_TAC \\
    ‘i < j \/ j < i’ by rw [] \\ (* 2 subgoals, same tactics *)
     METIS_TAC [])
 >> DISCH_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE arith_ss [] o Q.SPEC ‘k’)
 >> Q.PAT_X_ASSUM ‘!j. DOM (sub j) = IMAGE y (count j) /\ _’
      (STRIP_ASSUME_TAC o Q.SPEC ‘k’)
 >> qabbrev_tac ‘ss = sub k’
 (* NOTE: f is the important injection from index to index *)
 >> qabbrev_tac ‘f = \i. LEAST j. y j = y i’
 >> Know ‘!i. i < k ==> f i < k /\ VAR (y i) ISUB ss = P (f i)’
 >- (rw [Abbr ‘f’] \\
     LEAST_ELIM_TAC \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘i’ >> rw []) \\
     Q.X_GEN_TAC ‘j’ >> rw [] \\
     SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) \\
    ‘i < j’ by rw [] >> METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘!j1 j2. y j1 <> y j2 ==> f j1 <> f j2’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     simp [Abbr ‘f’] \\
     LEAST_ELIM_TAC \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘j1’ >> rw []) \\
     Q.X_GEN_TAC ‘j3’ >> STRIP_TAC \\
     LEAST_ELIM_TAC \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘j2’ >> rw []) \\
     Q.X_GEN_TAC ‘j4’ >> STRIP_TAC \\
     CCONTR_TAC >> METIS_TAC [])
 >> DISCH_TAC
 (* more properties of ISUB ‘ss’ *)
 >> ‘!N. MEM N (MAP FST ss) ==> ?j. j < k /\ N = P j’
       by (rw [Abbr ‘ss’, Abbr ‘sub’, MAP_REVERSE, MAP_GENLIST, MEM_GENLIST])
 (* Now we have a list of M1's whose hnf_children_size is bounded by ‘d_max’.
    In the worst case, ‘P @* M1 i’ will leave ‘SUC d_max’ variable bindings
    at most (in this case, ‘args i = 0 /\ n i = n_max’), and to finally get a
   "is_ready" term, we should apply a fresh list of d_max+1 variables (l).

    After redefining P by (\i. permutator (d_max + i), in the new worst
    case ‘P (f i) @* M1 i’ will leave at most ‘SUC d_max + k’ ending variables.

    NOTE: This list ‘xs’ is now part of vs0, defined as ‘DROP n_max vs0’.

    p3 is the maximal possible fresh list to be applied after the permutator
 *)
 >> qabbrev_tac ‘p3 = MAP rightctxt (REVERSE (MAP VAR xs))’
 >> ‘Boehm_transform p3’ by rw [Abbr ‘p3’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* additional steps for explicit construction *)
 >> Q.PAT_X_ASSUM ‘Boehm_transform pi'’ MP_TAC
 >> Know ‘pi' = p3 ++ p2 ++ p1’
 >- (rw [Abbr ‘pi'’, Boehm_construction_def] \\
     simp [Abbr ‘p2’, LIST_EQ_REWRITE])
 >> Rewr'
 (* “Boehm_construction” is now eliminated, back to old steps *)
 >> qunabbrev_tac ‘pi'’
 >> qabbrev_tac ‘pi = p3 ++ p2 ++ p1’
 >> DISCH_TAC (* Boehm_transform pi *)
 (* NOTE: requirements for ‘Z’

    1. y i IN Z /\ BIGUNION (IMAGE FV (set (args i))) SUBSET Z
    2. DISJOINT (set xs) Z
    3. Z SUBSET X UNION RANK (SUC r)
  *)
 >> qabbrev_tac ‘Z = Y UNION set vs’
 >> ‘FINITE Z’ by rw [Abbr ‘Z’]
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
  (* applying principal_hnf_FV_SUBSET' *)
     Know ‘FV (M0 i) SUBSET FV (M i)’
     >- (SIMP_TAC std_ss [Abbr ‘M0’, o_DEF] \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> rw []) \\
     qunabbrev_tac ‘Z'’ \\
     Suff ‘y i IN FV (M0 i) UNION set vs /\
           BIGUNION (IMAGE FV (set (args i))) SUBSET
           FV (M0 i) UNION set vs’
     >- SET_TAC [] \\
     Know ‘FV (M1 i) SUBSET FV (M0 i @* MAP VAR vs)’
     >- (‘M1 i = principal_hnf (M0 i @* MAP VAR vs)’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' \\
        ‘M0 i @* MAP VAR vs = apply p1 (M0 i)’
            by rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt'] >> POP_ORW \\
         Suff ‘solvable (M1 i)’ >- METIS_TAC [lameq_solvable_cong] \\
         MATCH_MP_TAC hnf_solvable \\
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
 >- (simp [Abbr ‘Z’, UNION_SUBSET] \\
     Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     rw [ROW_SUBSET_RANK])
 >> DISCH_TAC
 (* A better upper bound on ‘y i’ using subterm_headvar_lemma_alt *)
 >> Know ‘!i. i < k ==> y i IN Y UNION set (TAKE (n i) vs)’
 >- (rpt STRIP_TAC \\
     Know ‘FV (M i) SUBSET Y’
     >- (rw [SUBSET_DEF, Abbr ‘Y’] \\
         Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
         Q.EXISTS_TAC ‘M i’ >> simp [Abbr ‘M’, EL_MEM]) >> DISCH_TAC \\
     Suff ‘y i IN FV (M i) UNION set (TAKE (n i) vs)’
     >- (POP_ASSUM MP_TAC >> SET_TAC []) \\
    ‘y i = hnf_headvar (M1 i)’ by simp [GSYM appstar_APPEND] \\
     POP_ORW \\
     MATCH_MP_TAC subterm_headvar_lemma_alt \\
     qexistsl_tac [‘X UNION Y’, ‘0’, ‘M0 (i :num)’, ‘n_max’] >> simp [] \\
     POP_ASSUM MP_TAC >> SET_TAC [])
 >> DISCH_TAC
 >> Know ‘!i h. i < k /\ h < m i ==> FV (EL h (args i)) SUBSET X UNION RANK r’
 >- (rpt STRIP_TAC \\
     qabbrev_tac ‘N = EL h (args i)’ \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> y i IN Z /\ _’ drule \\
     simp [BIGUNION_SUBSET] >> STRIP_TAC \\
     Know ‘FV N SUBSET Z’
     >- (POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘N’ >> simp [Abbr ‘N’, EL_MEM]) \\
     qunabbrev_tac ‘Z’ >> DISCH_TAC \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Y UNION set vs’ \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     simp [UNION_SUBSET])
 >> DISCH_TAC
 (* a better upper bound of BIGUNION (IMAGE FV (set (args i))) *)
 >> Know ‘!i. i < k ==> BIGUNION (IMAGE FV (set (args i))) SUBSET
                        FV (M i) UNION set (TAKE (n i) vs)’
 >- (rpt STRIP_TAC \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (M0 i) UNION set (TAKE (n i) vs)’ \\
     reverse CONJ_TAC
     >- (Suff ‘FV (M0 i) SUBSET FV (M i)’ >- SET_TAC [] \\
         SIMP_TAC std_ss [Abbr ‘M0’] \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> simp []) \\
     qabbrev_tac ‘vs' = TAKE (n i) vs’ \\
    ‘M0 i @* MAP VAR vs' == VAR (y i) @* args i’
       by simp [lameq_LAMl_appstar_VAR] \\
  (* applying principal_hnf_beta_reduce *)
     Know ‘principal_hnf (M0 i @* MAP VAR vs') = VAR (y i) @* args i’
     >- (simp [] \\
         MATCH_MP_TAC principal_hnf_beta_reduce \\
         simp [hnf_appstar]) >> DISCH_TAC \\
     MP_TAC (Q.SPEC ‘M0 (i :num) @* MAP VAR vs'’ principal_hnf_FV_SUBSET') \\
     impl_tac >- (Suff ‘solvable (VAR (y i) @* args i)’
                  >- METIS_TAC [lameq_solvable_cong] \\
                  MATCH_MP_TAC hnf_solvable >> simp [hnf_appstar]) \\
     POP_ORW \\
     REWRITE_TAC [FV_appstar_MAP_VAR, FV_appstar, FV_thm] \\
     SET_TAC [])
 >> DISCH_TAC
 (* NOTE: now, before proving ‘EVERY is_ready' ...’, (for future subgoals) we
    need to calculute the principal_hnf of ‘apply pi (EL i Ms)’ for any i < k.

   ‘args'’ is the possibly substituted version of ‘args’.
  *)
 >> qabbrev_tac ‘args' = \i. MAP (\t. t ISUB ss) (args i)’
 >> ‘!i. LENGTH (args' i) = m i’ by rw [Abbr ‘args'’, Abbr ‘m’]
 (* NOTE: In vs, some elements are replaced by P, thus ‘set vs SUBSET set vs’ *)
 >> qabbrev_tac ‘args1 = MAP (\t. t ISUB ss) (MAP VAR vs)’
 >> ‘LENGTH args1 = n_max’ by rw [Abbr ‘args1’]
 >> Know ‘BIGUNION (IMAGE FV (set args1)) SUBSET set vs’
 >- (simp [Abbr ‘args1’, LIST_TO_SET_MAP, IMAGE_IMAGE] \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     POP_ASSUM MP_TAC \\
     rename1 ‘MEM v vs’ \\
     Cases_on ‘v IN DOM ss’ >- simp [Abbr ‘P’, FV_permutator] \\
     Know ‘VAR v ISUB ss = VAR v’
     >- (MATCH_MP_TAC ISUB_VAR_FRESH' >> art []) >> Rewr' \\
     simp [])
 >> DISCH_TAC
 (* abbreviate the tail term list after applying p2 *)
 >> qabbrev_tac ‘args2 = \i. DROP (n i) args1’
 >> Know ‘!i. BIGUNION (IMAGE FV (set (args2 i))) SUBSET set vs’
 >- (Q.X_GEN_TAC ‘i’ \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set args1))’ >> art [] \\
     Suff ‘set (args2 i) SUBSET set args1’ >- SET_TAC [] \\
     rw [Abbr ‘args2’, LIST_TO_SET_DROP])
 >> DISCH_TAC
 (* calculating ‘apply p2 (M1 i)’ *)
 >> ‘!i. i < k ==> apply p2 (M1 i) = P (f i) @* args' i @* args2 i’
       by rw [Abbr ‘args'’, Abbr ‘args1’, Abbr ‘args2’,
              GSYM appstar_APPEND, MAP_APPEND, appstar_ISUB, MAP_DROP]
 (* calculating ‘apply p2 ...’ until reaching a hnf *)
 >> Know ‘!i. i < k ==> apply p3 (P (f i) @* args' i @* args2 i) =
                        P (f i) @* args' i @* args2 i @* MAP VAR xs’
 >- rw [Abbr ‘p3’, Boehm_apply_MAP_rightctxt']
 (* preparing for permutator_hreduce_more (no DISCH_TAC for above Know) *)
 >> qabbrev_tac ‘l = \i. args' i ++ args2 i ++ MAP VAR xs’
 >> ASM_SIMP_TAC bool_ss [GSYM appstar_APPEND, APPEND_ASSOC]
 (* now l appears in the goal *)
 >> REWRITE_TAC [appstar_APPEND]
 (* stage work *)
 >> ‘!i. LENGTH (l i) = m i + (n_max - n i) + SUC d_max + k’
       by rw [Abbr ‘l’, Abbr ‘m’, Abbr ‘args2’, Abbr ‘d_max’, MAP_DROP]
 >> ‘!i. d_max + k < LENGTH (l i)’ by rw []
 >> DISCH_TAC (* !i. i < k ==> apply p3 _ = P (f i) @* l i *)
 (* applying TAKE_DROP_SUC to break l into 3 pieces

    NOTE: New the segmentation of ‘l’ also depends on ‘i’.
  *)
 >> qabbrev_tac ‘d_max' = \i. d_max + f i’
 >> Know ‘!i. i < k ==> d_max' i < d_max + k’
 >- (rw [Abbr ‘d_max'’] \\
     Q_TAC (TRANS_TAC LESS_TRANS) ‘d_max + k’ >> simp [])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> d_max' i <= LENGTH (l i)’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. LENGTH (l i) = _’ K_TAC \\
     simp [Abbr ‘d_max'’] \\
     MATCH_MP_TAC LT_IMP_LE \\
     Q_TAC (TRANS_TAC LESS_TRANS) ‘d_max + k’ >> simp [])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==>
              apply p3 (P (f i) @* args' i @* args2 i) =
              P (f i) @* (TAKE (d_max' i) (l i) ++ [EL (d_max' i) (l i)] ++
                          DROP (SUC (d_max' i)) (l i))’
 >- (RW_TAC std_ss [] \\
     Suff ‘TAKE (d_max' i) (l i) ++ [EL (d_max' i) (l i)] ++
           DROP (SUC (d_max' i)) (l i) = l i’ >- Rewr \\
     MATCH_MP_TAC TAKE_DROP_SUC \\
     Q.PAT_X_ASSUM ‘!i. LENGTH (l i) = _ + k’ K_TAC \\
     Q_TAC (TRANS_TAC LESS_TRANS) ‘d_max + k’ >> simp [])
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> _ = P (f i) @* l i’ K_TAC
 >> REWRITE_TAC [appstar_APPEND, appstar_SING]
 (* NOTE: The segmentation of list l(i) - apply (p3 ++ p2 ++ p1) (M i)

  |<-- m(i)<= d -->|<-- n_max-n(i) -->|<-------------- SUC d_max + k--------->|
  |----- args' ----+----- args2 ------+-------------- MAP VAR xs -------------|
  |------------------------------------ l ------------------------------------|
  |                                   |<-j->|
  |<--- d_max + f = d + n_max + f(i) ---->|b|
  |------------------- Ns(i) -------------+-+<-------------- tl(i) ---------->|
  |<-------------- d_max + k + 1 ---------->|
  *)
 >> qabbrev_tac ‘Ns = \i. TAKE (d_max' i) (l i)’
 >> qabbrev_tac ‘B  = \i. EL (d_max' i) (l i)’
 >> qabbrev_tac ‘tl = \i. DROP (SUC (d_max' i)) (l i)’
 >> simp [] (* this put Ns, B and tl in use *)
 (* What is j here? The purpose of j is to show that (B i) is a fresh name in
    xs. This j is the offset (d_max' i) of l, translated to offset of xs. *)
 >> qabbrev_tac ‘j = \i. d_max' i - LENGTH (args' i ++ args2 i)’
 (* show that (j i) is valid index of xs *)
 >> Know ‘!i. i < k ==> LENGTH (args' i ++ args2 i) <= d_max' i’
 >- (rpt STRIP_TAC \\
     simp [Abbr ‘j’, Abbr ‘args'’, Abbr ‘args2’, Abbr ‘d_max'’, Abbr ‘d_max’] \\
     MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO >> simp [])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> j i < LENGTH xs’
 >- (rw [Abbr ‘j’, Abbr ‘args'’, Abbr ‘args2’, Abbr ‘d_max'’, Abbr ‘d_max’] \\
    ‘f i < k’ by rw [] \\
     simp [ADD1])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> ?b. EL (j i) xs = b /\ B i = VAR b’
 >- (rw [Abbr ‘B’, Abbr ‘l’] \\
     Suff ‘EL (d_max' i) (args' i ++ args2 i ++ MAP VAR xs) =
           EL (j i) (MAP VAR xs)’ >- rw [EL_MAP] \\
     SIMP_TAC bool_ss [Abbr ‘j’] \\
     MATCH_MP_TAC EL_APPEND2 \\
    ‘f i < k’ by rw [] \\
     rw [Abbr ‘args'’, Abbr ‘args2’, Abbr ‘d_max'’, Abbr ‘d_max’, MAP_DROP] \\
     MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO >> rw [])
 >> simp [EXT_SKOLEM_THM']
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘b’ STRIP_ASSUME_TAC) (* this asserts ‘b’ *)
 >> simp []
 >> DISCH_TAC (* store ‘!i. i < k ==> apply p3 ...’ *)
 (* applying permutator_hreduce_more, it clearly reduces to a hnf *)
 >> Know ‘!i. i < k ==>
              P (f i) @* Ns i @@ VAR (b i) @* tl i -h->* VAR (b i) @* Ns i @* tl i’
 >- (RW_TAC std_ss [Abbr ‘P’] \\
     MATCH_MP_TAC permutator_hreduce_more >> rw [Abbr ‘Ns’, Abbr ‘d_max'’] \\
    ‘f i < k’ by rw [] \\
    ‘d_max + f i <= LENGTH (l i)’ by rw [] \\
     simp [LENGTH_TAKE])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> apply pi (M i) == VAR (b i) @* Ns i @* tl i’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply pi (M0 i)’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] \\
                  SIMP_TAC std_ss [Abbr ‘M0’] \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principal_hnf' >> rw []) \\
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
 (* calculating ‘principal_hnf (apply pi (M i))’ (hard) *)
 >> Know ‘!i. i < k ==>
              principal_hnf (apply pi (M i)) = VAR (b i) @* Ns i @* tl i’
 >- (rpt STRIP_TAC \\
     Know ‘MAP (\t. t ISUB ss) (MAP VAR xs) = MAP VAR xs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC ISUB_VAR_FRESH' >> rw [GSYM DOM_ALT_MAP_SND] \\
         simp [IN_IMAGE, IN_COUNT, Once DISJ_SYM] \\
         STRONG_DISJ_TAC (* push ‘a < k’ *) \\
         rename1 ‘EL x xs <> y a’ \\
         CCONTR_TAC \\
        ‘y a IN Z’ by rw [] \\
         Q.PAT_X_ASSUM ‘DISJOINT (set xs) Z’ MP_TAC \\
         rw [DISJOINT_ALT] \\
         Q.EXISTS_TAC ‘EL x xs’ >> rw [EL_MEM]) >> DISCH_TAC \\
  (* NOTE: This MP_TAC is for applying principal_hnf_denude_thm later. From
     now on, both ‘apply pi M == ...’ and ‘principal_hnf (apply pi M) = ...’
     are simplified in parallel.
   *)
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply pi (M i) == _’ drule \\
     Q.PAT_X_ASSUM ‘Boehm_transform pi’ K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p3’ K_TAC \\
  (* NOTE: No need to unabbrev ‘p2’ here since ‘apply p2 t = t ISUB sub k’ *)
     ASM_SIMP_TAC std_ss [Abbr ‘pi’, Boehm_apply_APPEND, Abbr ‘p1’, Abbr ‘p3’] \\
     FULL_SIMP_TAC bool_ss [Boehm_apply_MAP_rightctxt'] \\
  (* stage work *)
    ‘(M i @* MAP VAR vs ISUB ss) @* MAP VAR xs =
     (M i @* MAP VAR vs @* MAP VAR xs) ISUB ss’ by rw [appstar_ISUB] >> POP_ORW \\
     DISCH_TAC (* store ‘M i @* MAP VAR vs @* MAP VAR xs ISUB sub k == ...’ *) \\
  (* rewriting RHS to principal_hnf of ISUB *)
     Know ‘VAR (b i) @* Ns i @* tl i =
           principal_hnf (P (f i) @* args' i @* args2 i @* MAP VAR xs)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
        ‘hnf (VAR (b i) @* Ns i @* tl i)’
            by rw [GSYM appstar_APPEND, hnf_appstar] \\
         Suff ‘solvable (P (f i) @* args' i @* args2 i @* MAP VAR xs)’
         >- (METIS_TAC [principal_hnf_thm']) \\
         Suff ‘solvable (VAR (b i) @* Ns i @* tl i) /\
               P (f i) @* Ns i @@ VAR (b i) @* tl i == VAR (b i) @* Ns i @* tl i’
         >- (METIS_TAC [lameq_solvable_cong]) \\
         reverse CONJ_TAC >- (MATCH_MP_TAC hreduces_lameq >> rw []) \\
         MATCH_MP_TAC hnf_solvable >> art []) >> Rewr' \\
     Know ‘P (f i) @* args' i @* args2 i @* MAP VAR xs = M1 i @* MAP VAR xs ISUB ss’
     >- (REWRITE_TAC [appstar_ISUB, Once EQ_SYM_EQ] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply p2 (M1 i) = _’
           (drule o GSYM) >> Rewr' \\
         Q.PAT_X_ASSUM ‘!t. apply p2 t = t ISUB ss’ (ONCE_REWRITE_TAC o wrap) \\
         AP_TERM_TAC >> art []) >> Rewr' \\
  (* applying principal_hnf_ISUB_cong *)
     MATCH_MP_TAC principal_hnf_ISUB_cong \\
     CONJ_TAC (* has_hnf #1 *)
     >- (simp [GSYM solvable_iff_has_hnf, GSYM appstar_APPEND] \\
         Know ‘M0 i == M i’
         >- (SIMP_TAC std_ss [Abbr ‘M0’] \\
             MATCH_MP_TAC lameq_principal_hnf' >> rw []) >> DISCH_TAC \\
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
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf #2 *)
     >- (REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Suff ‘solvable (VAR (b i) @* Ns i @* tl i)’
         >- PROVE_TAC [lameq_solvable_cong] \\
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf # 3 *)
     >- (simp [appstar_ISUB, MAP_DROP] \\
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
  (* applying principal_hnf_denude_thm, finally *)
     MATCH_MP_TAC principal_hnf_denude_thm >> simp [] \\
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
     MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar, GSYM appstar_APPEND])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> CONJ_TAC (* EVERY is_ready ... *)
 >- (rpt (Q.PAT_X_ASSUM ‘Boehm_transform _’ K_TAC) \\
     simp [EVERY_EL, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
  (* now expanding ‘is_ready’ using [is_ready_alt] *)
     ASM_SIMP_TAC std_ss [is_ready_alt'] \\
     qexistsl_tac [‘b i’, ‘Ns i ++ tl i’] \\
  (* subgoal: apply pi (M i) -h->* VAR (b i) @* (Ns i ++ tl i) *)
     CONJ_TAC
     >- (REWRITE_TAC [appstar_APPEND] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> principal_hnf (apply pi (M i)) = _’ drule \\
         rw [principal_hnf_thm']) \\
  (* final goal (is_ready): EVERY (\e. b # e) ... *)
     Q.PAT_X_ASSUM ‘!i. i < k ==> principal_hnf (apply pi (M i)) = _’ K_TAC \\
     ASM_SIMP_TAC list_ss [EVERY_EL] \\
  (* easier goal first *)
     reverse CONJ_TAC (* b i # EL n (tl i) *)
     >- (Q.X_GEN_TAC ‘a’ >> DISCH_TAC \\
         qabbrev_tac ‘l1 = args' i ++ args2 i’ \\
         Know ‘LENGTH l1 <= d_max' i’
         >- (rw [Abbr ‘l1’, Abbr ‘args2’, Abbr ‘d_max’, Abbr ‘d_max'’, MAP_DROP] \\
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
            ‘LENGTH l1 <= SUC (d_max' i)’ by rw [] \\
             ASM_SIMP_TAC std_ss [DROP_APPEND2] \\
             Suff ‘SUC (d_max' i) - LENGTH l1 = SUC (j i)’ >- rw [] \\
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
     Q.PAT_X_ASSUM ‘!t. apply p2 t = t ISUB ss’        K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply p1 _ == _’     K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> solvable (apply pi (M i))’ K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> P (f i) @* Ns i @@ _ @* tl i -h->* _’ K_TAC \\
     qunabbrevl_tac [‘pi’, ‘p1’, ‘p2’, ‘p3’] \\
  (* The segmentation of list l(i) - apply (p3 ++ p2 ++ p1) (M i)

   |<-- m(i)<= d -->|<-- n_max-n(i) -->|<------------- SUC d_max + k --------->|
   |----- args' ----+----- args2 ------+-------------- MAP VAR xs -------------|
   |------------------------------------ l ------------------------------------|
   |                                   |<-j->|
   |<--- d_max + f = d + n_max + f(i) ---->|b|
   |------------------- Ns(i) -------------+-+<-------------- tl(i) ---------->|
   |<-------------- d_max + k + 1 ---------->|

     Three cases for proving ‘b i # EL a (Ns i)’, given a < LENGTH (Ns i):
     1) a < m i (= LENGTH (args' i))
     2) m i <= a < m i + LENGTH (args2 i)
     3) m i + LENGTH (args2 i) <= a
   *)
     Cases_on ‘a < m i’
     >- (Q.PAT_X_ASSUM ‘a < LENGTH (Ns i)’ MP_TAC \\
         simp [Abbr ‘Ns’, LENGTH_TAKE] \\
         DISCH_TAC (* a < d_max' i *) \\
         simp [EL_TAKE] \\
         Know ‘EL a (l i) = EL a (args' i)’
         >- (SIMP_TAC std_ss [Abbr ‘l’, GSYM APPEND_ASSOC] \\
             MATCH_MP_TAC EL_APPEND1 >> art []) >> Rewr' \\
         Suff ‘b i # EL a (args i)’
         >- (Suff ‘FV (EL a (args' i)) SUBSET FV (EL a (args i))’ >- SET_TAC [] \\
             Q.PAT_X_ASSUM ‘a < m i’ MP_TAC \\
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
         Q.PAT_X_ASSUM ‘a < m i’ MP_TAC \\
         rw [Abbr ‘args'’]) \\
  (* 2nd case *)
     Cases_on ‘a < m i + LENGTH (args2 i)’
     >- (Q.PAT_X_ASSUM ‘a < LENGTH (Ns i)’ MP_TAC \\
         simp [Abbr ‘Ns’, LENGTH_TAKE] \\
         DISCH_TAC (* a < d_max *) \\
         simp [EL_TAKE] \\
         Know ‘EL a (l i) = EL (a - m i) (args2 i)’
         >- (SIMP_TAC std_ss [Abbr ‘l’, GSYM APPEND_ASSOC] \\
             qabbrev_tac ‘l2 = args2 i ++ MAP VAR xs’ \\
             Know ‘EL a (args' i ++ l2) = EL (a - LENGTH (args' i)) l2’
             >- (MATCH_MP_TAC EL_APPEND2 >> rw []) >> Rewr' \\
             simp [Abbr ‘l2’] \\
             MATCH_MP_TAC EL_APPEND1 >> rw []) >> Rewr' \\
         Know ‘b i NOTIN Z’
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs) Z’ MP_TAC \\
             rw [DISJOINT_ALT] \\
             POP_ASSUM MATCH_MP_TAC \\
            ‘b i = EL (j i) xs’ by rw [] >> POP_ORW \\
             rw [EL_MEM]) \\
         qabbrev_tac ‘a' = a - m i’ \\
         Suff ‘FV (EL a' (args2 i)) SUBSET Z’ >- SET_TAC [] \\
         Suff ‘FV (EL a' (args2 i)) SUBSET set vs’
         >- (qunabbrev_tac ‘Z’ >> SET_TAC []) \\
        ‘a' < LENGTH (args2 i)’ by rw [Abbr ‘a'’] \\
         Q.PAT_X_ASSUM ‘a < m i + LENGTH (args2 i)’ MP_TAC \\
         Q.PAT_X_ASSUM ‘a' < LENGTH (args2 i)’ MP_TAC \\
         simp [Abbr ‘args1’, Abbr ‘args2’, EL_MAP, LENGTH_DROP] \\
         ONCE_REWRITE_TAC [GSYM MAP_DROP] \\
         simp [EL_MAP] \\
         NTAC 2 DISCH_TAC \\
         qabbrev_tac ‘a'' = EL a' (DROP (n i) (MAP VAR vs))’ \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV a''’ \\
         CONJ_TAC >- (MATCH_MP_TAC FV_ISUB_SUBSET >> art []) \\
         qunabbrev_tac ‘a''’ \\
         qabbrev_tac ‘ls = MAP VAR vs’ \\
        ‘a' + n i < LENGTH ls’ by simp [Abbr ‘ls’] \\
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
     qabbrev_tac ‘a' = a - (m i + LENGTH (args2 i))’ \\
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
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
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
     qabbrev_tac ‘vs' = TAKE (n i) vs’ \\
    ‘ALL_DISTINCT vs'’
       by (qunabbrev_tac ‘vs'’ >> MATCH_MP_TAC ALL_DISTINCT_TAKE >> art []) \\
    ‘LENGTH vs' = n i’
       by (qunabbrev_tac ‘vs'’ \\
           MATCH_MP_TAC LENGTH_TAKE >> art [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Q_TAC (RNEWS_TAC (“ys' :string list”, “r :num”, “(n :num -> num) i”)) ‘X’ \\
     Know ‘DISJOINT (set vs) (set ys')’
     >- (qunabbrev_tac ‘ys'’ \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘RANK r’ \\
         simp [DISJOINT_RANK_RNEWS'] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> art [] \\
         rw [ROW_SUBSET_RANK]) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs') (set ys')’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ >> art [] \\
         rw [Abbr ‘vs'’, LIST_TO_SET_TAKE]) >> DISCH_TAC \\
     qabbrev_tac ‘t = VAR (y i) @* args i’ \\
  (* applying for principal_hnf_tpm_reduce *)
     Know ‘principal_hnf (LAMl vs' t @* MAP VAR ys') = tpm (ZIP (vs',ys')) t’
     >- (‘hnf t’ by rw [Abbr ‘t’, hnf_appstar] \\
         MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n i’] >> simp [] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘Z’ >> art [] \\
         rw [Abbr ‘t’, FV_appstar]) >> Rewr' \\
     simp [Abbr ‘t’, tpm_appstar] \\
     Cases_on ‘p’ >> fs [] \\
     simp [ltree_lookup, LMAP_fromList, MAP_MAP_o, LNTH_fromList, EL_MAP] \\
     Cases_on ‘h < m i’ >> simp [] \\
     qabbrev_tac ‘pm = ZIP (vs',ys')’ \\
     Know ‘d_max' i <= LENGTH (l i)’
     >- (Q.PAT_X_ASSUM ‘!i. LENGTH (l i) = _’ K_TAC \\
         simp [Abbr ‘d_max'’] \\
         MATCH_MP_TAC LT_IMP_LE \\
         Q_TAC (TRANS_TAC LESS_TRANS) ‘d_max + k’ >> simp []) >> DISCH_TAC \\
     Know ‘h < LENGTH (Ns i)’
     >- (simp [Abbr ‘Ns’] \\
         Suff ‘m i <= d_max’ >- rw [Abbr ‘d_max'’] \\
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
     >- (simp [Abbr ‘N’, Abbr ‘pm'’, FV_tpm, SUBSET_DEF, IN_UNION] \\
         rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> y i IN Z /\ _’ (MP_TAC o Q.SPEC ‘i’) \\
         simp [SUBSET_DEF, IN_BIGUNION_IMAGE] >> STRIP_TAC \\
         POP_ASSUM (MP_TAC o Q.SPEC ‘lswapstr (REVERSE pm) x’) \\
         impl_tac >- (Q.EXISTS_TAC ‘EL h (args i)’ >> rw [EL_MEM]) \\
         Q.PAT_X_ASSUM ‘lswapstr (REVERSE pm) x IN FV (EL h (args i))’ K_TAC \\
         Know ‘set vs SUBSET RANK (SUC r)’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> art [] \\
             rw [ROW_SUBSET_RANK]) >> DISCH_TAC \\
         Know ‘set vs' SUBSET RANK (SUC r)’
         >- (qunabbrev_tac ‘vs'’ \\
             Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
             rw [LIST_TO_SET_TAKE]) >> DISCH_TAC \\
         Know ‘set ys' SUBSET RANK (SUC r)’
         >- (qunabbrev_tac ‘ys'’ \\
             MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) >> DISCH_TAC \\
         simp [Abbr ‘Z’, IN_UNION] \\
         reverse STRIP_TAC
      (* when “lswapstr (REVERSE pm) x IN set vs” is assumed *)
         >- (DISJ2_TAC >> POP_ASSUM MP_TAC >> simp [MEM_EL] \\
             DISCH_THEN (Q.X_CHOOSE_THEN ‘a’ STRIP_ASSUME_TAC) \\
             Know ‘x = lswapstr pm (EL a vs)’
             >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) >> simp []) >> Rewr' \\
             qunabbrev_tac ‘pm’ \\
             MATCH_MP_TAC lswapstr_IN_RANK >> art [] \\
             CONJ_TAC >- (Q.PAT_X_ASSUM ‘set vs SUBSET RANK (SUC r)’ MP_TAC \\
                          rw [SUBSET_DEF, MEM_EL] \\
                          POP_ASSUM MATCH_MP_TAC \\
                          Q.EXISTS_TAC ‘a’ >> art []) \\
             Know ‘set ys' SUBSET ROW r’
             >- (qunabbrev_tac ‘ys'’ \\
                 MATCH_MP_TAC RNEWS_SUBSET_ROW >> art []) >> DISCH_TAC \\
             Know ‘DISJOINT (ROW 0) (ROW r)’ >- rw [ROW_DISJOINT] \\
             simp [DISJOINT_ALT] >> STRIP_TAC \\
             Suff ‘EL a vs NOTIN ROW r’ >- METIS_TAC [SUBSET_DEF] \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             Suff ‘EL a vs IN set vs’ >- METIS_TAC [SUBSET_DEF] \\
             MATCH_MP_TAC EL_MEM >> art []) \\
      (* lswapstr (REVERSE pm) x IN Y (SUBSET X UNION RANK r) *)
         Know ‘lswapstr (REVERSE pm) x IN X UNION RANK r’ >- ASM_SET_TAC [] \\
         Q.PAT_X_ASSUM ‘lswapstr (REVERSE pm) x IN Y’ K_TAC \\
         simp [IN_UNION] \\
         STRIP_TAC
         >- (FULL_SIMP_TAC std_ss [GSYM ssetpm_IN] \\
             DISJ1_TAC \\
             Suff ‘ssetpm pm X = X’ >- DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
             MATCH_MP_TAC ssetpm_unchanged \\
             simp [Abbr ‘pm’, MAP_ZIP] \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ >> art [] \\
             simp [Abbr ‘vs'’, LIST_TO_SET_TAKE]) \\
         DISJ2_TAC \\
         FULL_SIMP_TAC std_ss [GSYM ssetpm_IN] \\
         qabbrev_tac ‘x' = lswapstr (REVERSE pm) x’ \\
        ‘x = lswapstr pm x'’ by simp [Abbr ‘x'’] >> POP_ORW \\
      (* NOTE: if x' IN set vs' (vs, ROW 0), then ‘lswapstr pm x' IN ys'’,
         otherwise lswapstr pm x' = x'.
       *)
         Cases_on ‘x' IN set vs'’
         >- (qunabbrev_tac ‘pm’ >> MATCH_MP_TAC lswapstr_IN_RANK >> art [] \\
             CONJ_TAC >- METIS_TAC [SUBSET_DEF] \\
             METIS_TAC [DISJOINT_ALT]) \\
         Suff ‘lswapstr pm x' = x'’
         >- (Rewr \\
             Q.PAT_X_ASSUM ‘x IN ssetpm pm (RANK r)’ MP_TAC \\
             simp [Abbr ‘x'’] \\
             Suff ‘RANK r SUBSET RANK (SUC r)’ >- rw [SUBSET_DEF] \\
             rw [RANK_MONO]) \\
         MATCH_MP_TAC lswapstr_unchanged' \\
         POP_ASSUM MP_TAC \\
         Q.PAT_X_ASSUM ‘x IN ssetpm pm (RANK r)’ MP_TAC \\
         simp [Abbr ‘x'’, Abbr ‘pm’, MEM_ZIP, MAP_ZIP] \\
         qabbrev_tac ‘z = lswapstr (REVERSE (ZIP (vs',ys'))) x’ \\
         Know ‘DISJOINT (RANK r) (set ys')’
         >- rw [Abbr ‘ys'’, DISJOINT_RANK_RNEWS] \\
         rw [DISJOINT_ALT]) >> DISCH_TAC \\
  (* applying BT_ltree_paths_tpm *)
     DISCH_TAC \\
     Know ‘ltree_lookup (BT' X (tpm pm' N) (SUC r)) t <> NONE’
     >- (POP_ASSUM MP_TAC \\
         Suff ‘ltree_paths (BT' X N (SUC r)) =
               ltree_paths (BT' X (tpm pm' N) (SUC r))’
         >- simp [ltree_paths_def, Once EXTENSION] \\
         MATCH_MP_TAC BT_ltree_paths_tpm >> art [] \\
         simp [Abbr ‘pm'’, Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
         reverse CONJ_TAC
         >- (qunabbrev_tac ‘ys'’ \\
             MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
         CONJ_TAC >- rw [Abbr ‘vs'’, LIST_TO_SET_TAKE] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> art [] \\
         rw [ROW_SUBSET_RANK]) \\
     NTAC 2 (POP_ASSUM K_TAC) \\
     fs [Abbr ‘pm'’, Abbr ‘N’] >> T_TAC \\
     qabbrev_tac ‘N = EL h (args i)’ \\
  (* applying subterm_width_isub_permutator_cong *)
    ‘!M. ltree_lookup (BT' X M (SUC r)) t <> NONE <=>
         t IN ltree_paths (BT' X M (SUC r))’ by rw [ltree_paths_def] \\
     POP_ORW >> DISCH_TAC \\
     MATCH_MP_TAC (cj 1 subterm_width_isub_permutator_cong_alt) \\
     qexistsl_tac [‘d_max’, ‘y’, ‘k’] >> simp [] \\
     CONJ_TAC
     >- (Suff ‘FV N SUBSET X UNION RANK r’
         >- (Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
             rw [RANK_MONO]) \\
         qunabbrev_tac ‘N’ >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘J’ >> DISCH_TAC \\
         Know ‘y J IN Z’ >- rw [] \\
         Suff ‘Z SUBSET X UNION RANK (SUC r)’ >- rw [SUBSET_DEF] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ >> art [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     Know ‘subterm_width (M i) (h::t) <= d’ >- rw [] \\
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
     rw [SUBSET_DEF, Abbr ‘Y’] \\
     Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
     Q.EXISTS_TAC ‘M i’ >> rw [Abbr ‘M’, EL_MEM])
 >> DISCH_TAC
 (* stage work *)
 >> CONJ_TAC >- (rw [EVERY_EL] >> simp [EL_MAP])
 (* upper bound of all FVs from l (args' ++ args2 ++ xs) *)
 >> Know ‘!i. i < k ==> BIGUNION (IMAGE FV (set (l i))) SUBSET X UNION RANK r’
 >- (simp [Abbr ‘l’] >> rpt STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3): args' *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> art [] \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set (args i)))’ \\
       simp [] \\
       rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
       rename1 ‘x IN FV t’ \\
       Q.PAT_X_ASSUM ‘MEM t (args' i)’ MP_TAC \\
       rw [MEM_EL] >> rename1 ‘h < m i’ \\
       Q.EXISTS_TAC ‘EL h (args i)’ \\
       CONJ_TAC >- (Q.EXISTS_TAC ‘h’ >> art []) \\
       Q.PAT_X_ASSUM ‘x IN FV (EL h (args' i))’ MP_TAC \\
       Suff ‘FV (EL h (args' i)) SUBSET FV (EL h (args i))’ >- rw [SUBSET_DEF] \\
       simp [Abbr ‘args'’, EL_MAP] \\
       qabbrev_tac ‘N = EL h (args i)’ \\
       MP_TAC (Q.SPECL [‘ss’, ‘N’] FV_ISUB_upperbound) >> rw [],
       (* goal 2 (of 3): args2 *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set args1))’ \\
       CONJ_TAC
       >- (MATCH_MP_TAC SUBSET_BIGUNION \\
           MATCH_MP_TAC IMAGE_SUBSET \\
           rw [Abbr ‘args2’, LIST_TO_SET_DROP]) \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ >> art [] \\
       Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
       CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
       MATCH_MP_TAC ROW_SUBSET_RANK >> art [],
       (* goal 3 (of 3): xs *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ \\
       reverse CONJ_TAC >- SET_TAC [] \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
       simp [ROW_SUBSET_RANK] \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ >> art [] \\
       simp [Abbr ‘vs0’, RNEWS_SUBSET_ROW] ])
 >> DISCH_TAC
 (* ‘H i’ is the head reduction of apply pi (M i) *)
 >> qabbrev_tac ‘H = \i. VAR (b i) @* Ns i @* tl i’
 >> Know ‘!i. solvable (H i)’
 >- (rw [Abbr ‘H’] \\
     MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> FV (H i) SUBSET X UNION RANK r’
 >- (simp [Abbr ‘H’, GSYM appstar_APPEND, FV_appstar] \\
     rpt STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3): easier *)
       REWRITE_TAC [IN_UNION] >> DISJ2_TAC \\
       Suff ‘b i IN ROW 0’
       >- (Suff ‘ROW 0 SUBSET RANK r’ >- METIS_TAC [SUBSET_DEF] \\
           rw [ROW_SUBSET_RANK]) \\
       Q.PAT_X_ASSUM ‘!i. i < k ==> EL (j i) xs = b i /\ _’ drule \\
       STRIP_TAC \\
       Q.PAT_X_ASSUM ‘EL (j i) xs = b i’ (REWRITE_TAC o wrap o SYM) \\
       Suff ‘set xs SUBSET ROW 0’
       >- (rw [SUBSET_DEF] \\
           POP_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ >> art [] \\
       simp [Abbr ‘vs0’, RNEWS_SUBSET_ROW],
       (* goal 2 (of 3): hard but now easy *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set (l i)))’ \\
       simp [Abbr ‘Ns’] \\
       MATCH_MP_TAC SUBSET_BIGUNION \\
       MATCH_MP_TAC IMAGE_SUBSET >> rw [LIST_TO_SET_TAKE],
       (* goal 3 (of 3): not that hard *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set (l i)))’ \\
       simp [Abbr ‘tl’] \\
       MATCH_MP_TAC SUBSET_BIGUNION \\
       MATCH_MP_TAC IMAGE_SUBSET >> rw [LIST_TO_SET_DROP] ])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> d_max <= LENGTH (hnf_children (H i))’
 >- (rw [Abbr ‘H’, GSYM appstar_APPEND] \\
     simp [Abbr ‘Ns’] \\
     simp [Abbr ‘d_max'’])
 >> DISCH_TAC
 (* stage work, now connect ‘subterm X (M i) q’ with ‘subterm X (H i) q’ *)
 >> Q_TAC (RNEWS_TAC (“ys :string list”, “r :num”, “n_max :num”)) ‘X’
 >> qabbrev_tac ‘pm = ZIP (vs,ys)’
 >> Know ‘DISJOINT (set vs) (set ys)’
 >- (Q.PAT_X_ASSUM ‘_ = vs’ (REWRITE_TAC o wrap o SYM) \\
     qunabbrev_tac ‘ys’ \\
     MATCH_MP_TAC DISJOINT_RNEWS >> simp [])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 (* Now ‘subterm X (M i) q r <> NONE’ is added into antecedents of the subgoal *)
 >> Know ‘!q. q <<= p /\ q <> [] ==>
              !i. i < k ==> subterm X (H i) q r <> NONE /\
                            subterm' X (H i) q r =
                           (tpm (REVERSE pm) (subterm' X (M i) q r)) ISUB ss’
 >- (Q.X_GEN_TAC ‘q’ >> STRIP_TAC \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i q. i < k /\ q <<= p ==> subterm X (M i) q r <> NONE’
        (MP_TAC o Q.SPECL [‘i’, ‘q’]) >> simp [] \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> subterm_width (M i) p <= d’ drule \\
     Cases_on ‘p’ >> fs [] \\
     Cases_on ‘q’ >> fs [] \\
     Q.PAT_X_ASSUM ‘h' = h’ (fs o wrap) >> T_TAC \\
     simp [subterm_of_solvables] \\
     Know ‘principal_hnf (H i) = H i’
     >- (MATCH_MP_TAC principal_hnf_reduce \\
         simp [Abbr ‘H’, GSYM appstar_APPEND, hnf_appstar]) >> DISCH_TAC \\
    ‘LAMl_size (H i) = 0’
       by rw [Abbr ‘H’, LAMl_size_appstar, GSYM appstar_APPEND] \\
     simp [] \\
     NTAC 2 (POP_ASSUM K_TAC) (* principal_hnf (H i), LAMl_size (H i) *) \\
     DISCH_TAC (* subterm_width (M i) (h::t) <= d *) \\
     Q_TAC (RNEWS_TAC (“ys' :string list”, “r :num”, “(n :num -> num) i”)) ‘X’ \\
     qabbrev_tac ‘vs' = TAKE (n i) vs’ \\
    ‘ALL_DISTINCT vs' /\ LENGTH vs' = n i’
       by rw [ALL_DISTINCT_TAKE, Abbr ‘vs'’] \\
     qabbrev_tac ‘t0 = VAR (y i) @* args i’ \\
  (* prove that ‘ys' = TAKE (n i) ys’ *)
     MP_TAC (Q.SPECL [‘r’, ‘n (i :num)’, ‘n_max’, ‘X’] RNEWS_prefix) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘ni’
                   (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])) \\
     Know ‘ni = n i’
     >- (Know ‘LENGTH ys' = LENGTH (TAKE ni ys)’ >- rw [] \\
         simp [LENGTH_TAKE]) \\
     DISCH_THEN (rfs o wrap) >> T_TAC \\
     Know ‘DISJOINT (set vs) (set ys)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘ROW 0’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘ROW r’ \\
         simp [Abbr ‘ys’, RNEWS_SUBSET_ROW] \\
         rw [Once DISJOINT_SYM, ROW_DISJOINT]) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs') (set ys')’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set ys’ \\
         reverse CONJ_TAC >- rw [LIST_TO_SET_TAKE] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         simp [Abbr ‘vs'’, LIST_TO_SET_TAKE]) >> DISCH_TAC \\
  (* applying for principal_hnf_tpm_reduce *)
     Know ‘principal_hnf (LAMl vs' t0 @* MAP VAR ys') = tpm (ZIP (vs',ys')) t0’
     >- (‘hnf t0’ by rw [Abbr ‘t0’, hnf_appstar] \\
         MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n i’] >> simp [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> art [] \\
         rw [Abbr ‘t0’, FV_appstar]) >> Rewr' \\
     simp [Abbr ‘t0’, tpm_appstar, hnf_children_appstar] \\
     Cases_on ‘h < m i’ >> simp [] \\
     Know ‘h < d_max’
     >- (Q_TAC (TRANS_TAC LESS_LESS_EQ_TRANS) ‘m i’ >> art [] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ >> simp [] \\
         simp [Abbr ‘d_max’]) >> DISCH_TAC \\
    ‘h < d_max' i’ by rw [Abbr ‘d_max'’] \\
     Know ‘h < LENGTH (hnf_children (H i))’
     >- (Q_TAC (TRANS_TAC LESS_LESS_EQ_TRANS) ‘d_max’ \\
         simp []) >> Rewr \\
     Know ‘EL h (hnf_children (H i)) = EL h (Ns i)’
     >- (simp [Abbr ‘H’, GSYM appstar_APPEND] \\
         MATCH_MP_TAC EL_APPEND1 >> simp [Abbr ‘Ns’]) >> Rewr' \\
     Know ‘EL h (Ns i) = EL h (args' i)’
     >- (simp [Abbr ‘Ns’] \\
         Know ‘EL h (TAKE (d_max' i) (l i)) = EL h (l i)’
         >- (MATCH_MP_TAC EL_TAKE >> art []) >> Rewr' \\
         simp [Abbr ‘l’] \\
         REWRITE_TAC [GSYM APPEND_ASSOC] \\
         MATCH_MP_TAC EL_APPEND1 \\
         simp [Abbr ‘args'’]) >> Rewr' \\
     qabbrev_tac ‘N = EL h (args i)’ \\
     fs [Abbr ‘args'’, EL_MAP] >> T_TAC \\
     qabbrev_tac ‘pm' = ZIP (vs',ys')’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs') (set ys')’ K_TAC \\
  (* applying tpm_unchanged *)
     Know ‘tpm pm' N = tpm pm N’ (* (n i) vs. n_max *)
     >- (simp [Abbr ‘pm'’, Abbr ‘vs'’] \\
         Q.PAT_X_ASSUM ‘TAKE (n i) ys = ys'’ (REWRITE_TAC o wrap o SYM) \\
         simp [ZIP_TAKE] \\
        ‘tpm pm N = tpm (TAKE (n i) pm ++ DROP (n i) pm) N’
           by rw [TAKE_DROP] >> POP_ORW \\
         REWRITE_TAC [pmact_append] \\
         Suff ‘tpm (DROP (n i) pm) N = N’ >- rw [] \\
         MATCH_MP_TAC tpm_unchanged \\
         simp [Abbr ‘pm’, GSYM ZIP_DROP, MAP_ZIP] \\
         Q.PAT_X_ASSUM ‘ALL_DISTINCT (TAKE (n i) vs)’ K_TAC \\
         Q.PAT_X_ASSUM ‘LENGTH (TAKE (n i) vs) = n i’ K_TAC \\
         Know ‘FV N SUBSET FV (M i) UNION set (TAKE (n i) vs)’
         >- (Q.PAT_X_ASSUM
               ‘!i. i < k ==> BIGUNION (IMAGE FV (set (args i))) SUBSET _’ drule \\
             rw [SUBSET_DEF] \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘FV N’ >> art [] \\
             Q.EXISTS_TAC ‘N’ >> simp [Abbr ‘N’, EL_MEM]) \\
         DISCH_TAC \\
      (* NOTE: FV (M i) SUBSET Y SUBSET X UNION RANK r *)
         reverse CONJ_TAC (* ys is easier *)
         >- (Know ‘DISJOINT (set ys) (FV (M i))’
             >- (MATCH_MP_TAC subterm_disjoint_lemma \\
                 qexistsl_tac [‘X’, ‘r’, ‘n_max’] >> simp []) \\
             DISCH_TAC \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set ys’ \\
             simp [LIST_TO_SET_DROP] \\
             simp [DISJOINT_ALT'] >> rpt STRIP_TAC \\
             Know ‘x IN FV (M i) UNION set (TAKE (n i) vs)’
             >- METIS_TAC [SUBSET_DEF] \\
             simp [IN_UNION] \\
             CONJ_TAC
             >- (Q.PAT_X_ASSUM ‘DISJOINT (set ys) (FV (M i))’ MP_TAC \\
                 rw [DISJOINT_ALT]) \\
             Suff ‘DISJOINT (set (TAKE (n i) vs)) (set ys)’
             >- rw [DISJOINT_ALT'] \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ >> rw [LIST_TO_SET_TAKE]) \\
      (* vs is slightly harder *)
         simp [DISJOINT_ALT'] >> rpt STRIP_TAC \\
         Know ‘x IN FV (M i) UNION set (TAKE (n i) vs)’
         >- METIS_TAC [SUBSET_DEF] \\
         simp [IN_UNION] \\
         reverse CONJ_TAC
         >- (Know ‘ALL_DISTINCT (TAKE (n i) vs ++ DROP (n i) vs)’
             >- rw [TAKE_DROP] \\
             simp [ALL_DISTINCT_APPEND', DISJOINT_ALT']) \\
         Suff ‘DISJOINT (set (DROP (n i) vs)) (FV (M i))’ >- rw [DISJOINT_ALT] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         simp [LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘Y’ >> art [] \\
         simp [Abbr ‘Y’, SUBSET_DEF] \\
         Q.X_GEN_TAC ‘v’ >> DISCH_TAC \\
         Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
         Q.EXISTS_TAC ‘M i’ >> simp [Abbr ‘M’, EL_MEM]) >> Rewr' \\
     qunabbrev_tac ‘pm'’ \\
  (* some shared subgoals to be used later *)
     Know ‘set ys SUBSET X UNION RANK (SUC r)’
     >- (Suff ‘set ys SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         qunabbrev_tac ‘ys’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp []) >> DISCH_TAC \\
     Know ‘FV N SUBSET X UNION RANK (SUC r)’
     >- (Suff ‘FV N SUBSET X UNION RANK r’
         >- (Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
             rw [RANK_MONO]) \\
         qunabbrev_tac ‘N’ \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (FV (M i))’
     >- (MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n_max’] >> simp []) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (FV N)’
     >- (Q.PAT_X_ASSUM ‘!i. i < k ==> _ SUBSET FV (M i) UNION _’ drule \\
         simp [BIGUNION_SUBSET] >> STRIP_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV (M i) UNION set vs'’ \\
         reverse CONJ_TAC
         >- (POP_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘N’ >> simp [Abbr ‘N’, EL_MEM]) \\
         simp [DISJOINT_UNION'] \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs’ \\
         simp [Once DISJOINT_SYM, Abbr ‘vs'’, LIST_TO_SET_TAKE]) \\
     DISCH_TAC \\
  (* applying subterm_fresh_tpm_cong *)
     DISCH_TAC (* subterm X (tpm pm N) t (SUC r) <> NONE *) \\
     MP_TAC (Q.SPECL [‘pm’, ‘X’, ‘N’, ‘t'’, ‘SUC r’] subterm_fresh_tpm_cong) \\
     impl_tac >- simp [Abbr ‘pm’, MAP_ZIP] \\
     simp [] \\
     STRIP_TAC >> POP_ASSUM K_TAC (* already used *) \\
  (* applying subterm_isub_permutator_cong' *)
     MATCH_MP_TAC subterm_isub_permutator_cong_alt' \\
     qexistsl_tac [‘d_max’, ‘y’, ‘k’] >> simp [] \\
     CONJ_TAC (* easier *)
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> y i IN Z /\ _’ drule \\
         qunabbrev_tac ‘Z’ >> STRIP_TAC \\
         rename1 ‘i' < k’ \\
         Q.PAT_X_ASSUM ‘y i' IN Y UNION set vs’ MP_TAC \\
         Suff ‘Y UNION set vs SUBSET X UNION RANK (SUC r)’ >- SET_TAC [] \\
         rw [UNION_SUBSET] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ >> art [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
  (* subterm_width N t <= d_max *)
     Know ‘subterm_width (M i) (h::t') <= d’
     >- (MATCH_MP_TAC subterm_width_inclusive \\
         Q.EXISTS_TAC ‘h::t’ >> simp []) \\
     qabbrev_tac ‘Ms' = args i ++ DROP (n i) (MAP VAR vs)’ \\
  (* applying subterm_width_induction_lemma (the general one) *)
     Suff ‘subterm_width (M i) (h::t') <= d <=>
           m i <= d /\ subterm_width (EL h Ms') t' <= d’
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
     rw [SUBSET_DEF, Abbr ‘Y’]
     >- (Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
         Q.EXISTS_TAC ‘M i’ >> art [] \\
         rw [Abbr ‘M’, EL_MEM]) \\
     MATCH_MP_TAC ltree_paths_inclusive \\
     Q.EXISTS_TAC ‘h::t’ >> simp [])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> Suff ‘(!M N q.
            MEM M Ms /\ MEM N Ms /\ q <<= p /\
            subtree_equiv X M N q r ==>
            subtree_equiv X (apply pi M) (apply pi N) q r /\
           (solvable (subterm' X M q r) ==>
            solvable (subterm' X (apply pi M) q r))) /\
          (!M N q.
            MEM M Ms /\ MEM N Ms /\ q <<= p /\
            subtree_equiv X (apply pi M) (apply pi N) q r ==>
            subtree_equiv X M N q r /\
           (solvable (subterm' X (apply pi M) q r) ==>
            solvable (subterm' X M q r)))’
 >- (STRIP_TAC \\
     CONJ_TAC (* extra goal *)
     >- (qx_genl_tac [‘q’, ‘t’] >> STRIP_TAC \\
         EQ_TAC >> STRIP_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Q.PAT_X_ASSUM ‘!M N q. MEM M Ms /\ MEM N Ms /\ q <<= p /\
                                  subtree_equiv X M N q r ==> _’
             (MP_TAC o Q.SPECL [‘t’, ‘t’, ‘q’]) >> simp [],
           (* goal 2 (of 2) *)
           Q.PAT_X_ASSUM
             ‘!M N q. MEM M Ms /\ MEM N Ms /\ q <<= p /\
                      subtree_equiv X (apply pi M) (apply pi N) q r ==> _’
             (MP_TAC o Q.SPECL [‘t’, ‘t’, ‘q’]) >> simp [] ]) \\
     METIS_TAC [])
 (* stage work, next goal:

    !M N q. MEM M Ms /\ MEM N Ms /\ q <<= p /\ subtree_equiv X M N q r ==>
            subtree_equiv X (apply pi M) (apply pi N) q r)
  *)
 >> CONJ_ASM1_TAC
 >- (qx_genl_tac [‘M2’, ‘N2’, ‘q’] >> simp [MEM_EL] \\
     ONCE_REWRITE_TAC
       [TAUT ‘p /\ q /\ r /\ s ==> t <=> p ==> q ==> r ==> s ==> t’] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j1’ STRIP_ASSUME_TAC) \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j2’ STRIP_ASSUME_TAC) \\
     DISCH_TAC (* q <<= p *) \\
     Q.PAT_X_ASSUM ‘_ = M j1’ (REWRITE_TAC o wrap) \\
     Q.PAT_X_ASSUM ‘_ = M j2’ (REWRITE_TAC o wrap) \\
     qabbrev_tac ‘M' = \i. apply pi (M i)’ >> simp [] \\
     simp [subtree_equiv_def] \\
  (* applying BT_of_principal_hnf *)
     Know ‘BT' X (M' j1) r = BT' X (principal_hnf (M' j1)) r’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_of_principal_hnf \\
         simp [Abbr ‘M'’] \\
         METIS_TAC [lameq_solvable_cong]) >> Rewr' \\
     Know ‘BT' X (M' j2) r = BT' X (principal_hnf (M' j2)) r’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_of_principal_hnf \\
         simp [Abbr ‘M'’] \\
         METIS_TAC [lameq_solvable_cong]) >> Rewr' \\
     simp [Abbr ‘M'’] \\
  (* NOTE: now we are still missing some important connections:
   - ltree_el (BT X M2) q            ~1~  subterm' X M2 q
   - ltree_el (BT X N2) q            ~1~  subterm' X N2 q
   - ltree_el (BT X (apply pi M2) q  ~1~  subterm' X (apply pi M2) q
   - ltree_el (BT X (apply pi N2) q  ~1~  subterm' X (apply pi N2) q
   - subterm' X (apply pi M2) q      ~2~  subterm' X M2 q
   - subterm' X (apply pi N2) q      ~2~  subterm' X N2 q

     where the relation ~1~ is to be established by BT_subterm_thm, and ~2~
     follows a similar idea of [Boehm_transform_exists_lemma].
   *)
     Cases_on ‘q = []’
     >- (POP_ORW >> simp [BT_ltree_el_NIL] \\
         Know ‘!i. principal_hnf (H i) = H i’
         >- (rw [Abbr ‘H’] >> MATCH_MP_TAC principal_hnf_reduce \\
             rw [hnf_appstar]) >> Rewr' \\
         Q.PAT_X_ASSUM ‘!q. q <<= p /\ q <> [] ==> _’ K_TAC \\
         simp [Abbr ‘H’, GSYM appstar_APPEND, hnf_head_appstar] \\
         simp [head_equivalent_def] \\
         qabbrev_tac ‘vs1 = TAKE (n j1) vs’ \\
         qabbrev_tac ‘vs2 = TAKE (n j2) vs’ \\
        ‘ALL_DISTINCT vs1 /\ ALL_DISTINCT vs2’
           by simp [Abbr ‘vs1’, Abbr ‘vs2’, ALL_DISTINCT_TAKE] \\
        ‘LENGTH vs1 = n j1’
           by (qunabbrev_tac ‘vs1’ \\
               MATCH_MP_TAC LENGTH_TAKE >> art [] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
        ‘LENGTH vs2 = n j2’
           by (qunabbrev_tac ‘vs2’ \\
               MATCH_MP_TAC LENGTH_TAKE >> art [] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
         Q_TAC (RNEWS_TAC (“ys1 :string list”, “r :num”, “(n :num->num) j1”)) ‘X’ \\
         Q_TAC (RNEWS_TAC (“ys2 :string list”, “r :num”, “(n :num->num) j2”)) ‘X’ \\
         Know ‘DISJOINT (set vs1) (set ys1)’
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ \\
             reverse CONJ_TAC >- rw [Abbr ‘vs1’, LIST_TO_SET_TAKE] \\
             qunabbrev_tac ‘ys1’ \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘RANK r’ >> simp [DISJOINT_RANK_RNEWS']) >> DISCH_TAC \\
         Know ‘DISJOINT (set vs2) (set ys2)’
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ \\
             reverse CONJ_TAC >- rw [Abbr ‘vs2’, LIST_TO_SET_TAKE] \\
             qunabbrev_tac ‘ys2’ \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘RANK r’ >> simp [DISJOINT_RANK_RNEWS']) >> DISCH_TAC \\
         qabbrev_tac ‘t1 = VAR (y j1) @* args j1’ \\
         qabbrev_tac ‘t2 = VAR (y j2) @* args j2’ \\
      (* applying for principal_hnf_tpm_reduce *)
         Know ‘principal_hnf (LAMl vs1 t1 @* MAP VAR ys1) = tpm (ZIP (vs1,ys1)) t1’
         >- (‘hnf t1’ by rw [Abbr ‘t1’, hnf_appstar] \\
             MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
             MATCH_MP_TAC subterm_disjoint_lemma \\
             qexistsl_tac [‘X’, ‘r’, ‘n j1’] >> simp [] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘Z’ >> art [] \\
             rw [Abbr ‘t1’, FV_appstar]) >> Rewr' \\
         Know ‘principal_hnf (LAMl vs2 t2 @* MAP VAR ys2) = tpm (ZIP (vs2,ys2)) t2’
         >- (‘hnf t2’ by rw [Abbr ‘t2’, hnf_appstar] \\
             MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
             MATCH_MP_TAC subterm_disjoint_lemma \\
             qexistsl_tac [‘X’, ‘r’, ‘n j2’] >> simp [] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘Z’ >> art [] \\
             rw [Abbr ‘t2’, FV_appstar]) >> Rewr' \\
         simp [Abbr ‘t1’, Abbr ‘t2’, tpm_appstar] >> STRIP_TAC \\
         Know ‘LENGTH (l j1) = LENGTH (l j2)’
         >- (simp [] \\
            ‘n j1 <= n_max /\ n j2 <= n_max’ by rw [] \\
             simp []) >> DISCH_TAC \\
         reverse CONJ_TAC
         >- (simp [Abbr ‘Ns’, Abbr ‘tl’, Abbr ‘d_max'’] \\
            ‘f j1 < k /\ f j2 < k’ by rw [] >> simp []) \\
        ‘b j1 = EL (j j1) xs /\ b j2 = EL (j j2) xs’ by rw [] \\
         NTAC 2 POP_ORW \\
         Suff ‘j j1 = j j2’ >- Rewr \\
         simp [Abbr ‘j’, Abbr ‘args'’, Abbr ‘args2’] \\
        ‘n j1 <= n_max /\ n j2 <= n_max’ by rw [] \\
        ‘f j1 < k /\ f j2 < k’ by rw [] \\
         simp [Abbr ‘d_max'’] \\
         Suff ‘f j1 = f j2’ >- rw [] \\
      (* NOTE: current situation:

        |<--------- vs (n_max) --------->|
        |<--- vs1 ----->|<---- vs1'----->|      y j1  ---+
        |<------ vs2 ------->|<--vs2'--->|      y j2  ---|--+
     ----------------------------------------------------|--|----
        |<--- ys1 ----->|------ys1'----->|      y' <-----+  |
        |<------ ys2 ------->|<--ys2'--->|      y' <--------+

        lswapstr (ZIP (vs, ys))  (y j1) =
        lswapstr (ZIP (vs1,ys1)) (y j1) =
        lswapstr (ZIP (vs2,ys2)) (y j2) =
        lswapstr (ZIP (vs, ys))  (y j2) ==> y j1 = y j2

        P (f j1) = VAR (y j1) ISUB ss = VAR (y j2) ISUB ss = P (f j2)
    ==> permutator (d_max + f j1) = permutator (d_max + f j2)
    ==> d_max + f j1 = d_max + f j2 ==> f j1 = f j2
       *)
         PRINT_TAC "stage work on subtree_equiv_lemma" \\
         Suff ‘y j1 = y j2’
         >- (DISCH_TAC \\
             Know ‘VAR (y j1) ISUB ss = VAR (y j2) ISUB ss’
             >- POP_ASSUM (REWRITE_TAC o wrap) \\
             POP_ASSUM K_TAC \\
             simp [Abbr ‘P’]) (* permutator_11 is used here *) \\
         qabbrev_tac ‘vs1' = DROP (n j1) vs’ \\
         qabbrev_tac ‘vs2' = DROP (n j2) vs’ \\
         Know ‘ys1 <<= ys’
         >- (qunabbrevl_tac [‘ys1’, ‘ys’] \\
             MATCH_MP_TAC RNEWS_prefix >> simp []) \\
         simp [IS_PREFIX_EQ_TAKE] \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
         Know ‘n1' = n j1’
         >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
             simp [LENGTH_TAKE]) >> DISCH_TAC \\
         Q.PAT_X_ASSUM ‘n1' <= n_max’ MP_TAC \\
         Q.PAT_X_ASSUM ‘ys1 = TAKE n1' ys’
           (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
         POP_ORW >> rpt STRIP_TAC \\
         qabbrev_tac ‘ys1' = DROP (n j1) ys’ \\
        ‘vs1 ++ vs1' = vs /\ ys1 ++ ys1' = ys’ by METIS_TAC [TAKE_DROP] \\
         Know ‘ys2 <<= ys’
         >- (qunabbrevl_tac [‘ys2’, ‘ys’] \\
             MATCH_MP_TAC RNEWS_prefix >> simp []) \\
         simp [IS_PREFIX_EQ_TAKE] \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
         Know ‘n2' = n j2’
         >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
             simp [LENGTH_TAKE]) >> DISCH_TAC \\
         Q.PAT_X_ASSUM ‘n2' <= n_max’ MP_TAC \\
         Q.PAT_X_ASSUM ‘ys2 = TAKE n2' ys’
           (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
         POP_ORW >> rpt STRIP_TAC \\
         qabbrev_tac ‘ys2' = DROP (n j2) ys’ \\
        ‘vs2 ++ vs2' = vs /\ ys2 ++ ys2' = ys’ by METIS_TAC [TAKE_DROP] \\
         qabbrev_tac ‘pm1 = ZIP (vs1,ys1)’ \\
         qabbrev_tac ‘pm2 = ZIP (vs2,ys2)’ \\
         Suff ‘lswapstr pm1 (y j1) = lswapstr pm (y j1) /\
               lswapstr pm2 (y j2) = lswapstr pm (y j2)’
         >- (STRIP_TAC \\
             Q.PAT_X_ASSUM ‘lswapstr pm1 (y j1) = lswapstr pm2 (y j2)’ MP_TAC \\
             simp []) \\
         Q.PAT_X_ASSUM ‘lswapstr pm1 (y j1) = lswapstr pm2 (y j2)’ K_TAC \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
          ‘LENGTH vs1' = LENGTH ys1'’ by rw [Abbr ‘vs1'’, Abbr ‘ys1'’] \\
           Know ‘pm = pm1 ++ ZIP (vs1',ys1')’
           >- (simp [Abbr ‘pm’, Abbr ‘pm1’] \\
              ‘LENGTH vs1 = LENGTH ys1’ by rw [Abbr ‘vs1'’] \\
               simp [ZIP_APPEND]) >> Rewr' \\
           simp [lswapstr_append, Once EQ_SYM_EQ] \\
           MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
           reverse CONJ_TAC (* easy goal first *)
           >- (‘y j1 IN X UNION RANK r’ by METIS_TAC [SUBSET_DEF] \\
               Suff ‘DISJOINT (X UNION RANK r) (set ys1')’
               >- (REWRITE_TAC [DISJOINT_ALT] \\
                   DISCH_THEN MATCH_MP_TAC >> art []) \\
               MATCH_MP_TAC DISJOINT_SUBSET \\
               Q.EXISTS_TAC ‘set ys’ \\
               reverse CONJ_TAC >- simp [Abbr ‘ys1'’, LIST_TO_SET_DROP] \\
               simp [DISJOINT_UNION', Once DISJOINT_SYM] \\
               simp [Abbr ‘ys’, Once DISJOINT_SYM, DISJOINT_RNEWS_RANK]) \\
        (* current goal: ~MEM (y j1) vs1'

           M0 i = LAMl (TAKE (n i) vs) (VAR (y i) @* args i)
           Abbrev (M1 = (\i. principal_hnf (M0 i @* MAP VAR vs)))
           M1 i = VAR (y i) @* args i @* DROP (n i) (MAP VAR vs)

           It seems that (y i) at most uses (TAKE (n i) vs).
         *)
          ‘y j1 IN Y UNION set vs1’ by rw [Abbr ‘vs1’] \\
           Suff ‘DISJOINT (Y UNION set vs1) (set vs1')’
           >- (REWRITE_TAC [DISJOINT_ALT] \\
               DISCH_THEN MATCH_MP_TAC >> art []) \\
           REWRITE_TAC [DISJOINT_UNION] \\
           reverse CONJ_TAC (* easy goal first *)
           >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
               Q.PAT_X_ASSUM ‘vs1 ++ vs1' = vs’ (REWRITE_TAC o wrap o SYM) \\
               simp [ALL_DISTINCT_APPEND']) \\
           MATCH_MP_TAC DISJOINT_SUBSET \\
           Q.EXISTS_TAC ‘set vs’ >> simp [Once DISJOINT_SYM] \\
           simp [Abbr ‘vs1'’, LIST_TO_SET_DROP],
           (* goal 2 (of 2) *)
          ‘LENGTH vs2' = LENGTH ys2'’ by rw [Abbr ‘vs2'’, Abbr ‘ys2'’] \\
           Know ‘pm = pm2 ++ ZIP (vs2',ys2')’
           >- (simp [Abbr ‘pm’, Abbr ‘pm2’] \\
              ‘LENGTH vs2 = LENGTH ys2’ by rw [Abbr ‘vs2'’] \\
               simp [ZIP_APPEND]) >> Rewr' \\
           simp [lswapstr_append, Once EQ_SYM_EQ] \\
           MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
           reverse CONJ_TAC (* easy goal first *)
           >- (‘y j2 IN X UNION RANK r’ by METIS_TAC [SUBSET_DEF] \\
               Suff ‘DISJOINT (X UNION RANK r) (set ys2')’
               >- (REWRITE_TAC [DISJOINT_ALT] \\
                   DISCH_THEN MATCH_MP_TAC >> art []) \\
               MATCH_MP_TAC DISJOINT_SUBSET \\
               Q.EXISTS_TAC ‘set ys’ \\
               reverse CONJ_TAC >- simp [Abbr ‘ys2'’, LIST_TO_SET_DROP] \\
               simp [DISJOINT_UNION', Once DISJOINT_SYM] \\
               simp [Abbr ‘ys’, Once DISJOINT_SYM, DISJOINT_RNEWS_RANK]) \\
          ‘y j2 IN Y UNION set vs2’ by rw [Abbr ‘vs2’] \\
           Suff ‘DISJOINT (Y UNION set vs2) (set vs2')’
           >- (REWRITE_TAC [DISJOINT_ALT] \\
               DISCH_THEN MATCH_MP_TAC >> art []) \\
           REWRITE_TAC [DISJOINT_UNION] \\
           reverse CONJ_TAC (* easy goal first *)
           >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
               Q.PAT_X_ASSUM ‘vs2 ++ vs2' = vs’ (REWRITE_TAC o wrap o SYM) \\
               simp [ALL_DISTINCT_APPEND']) \\
           MATCH_MP_TAC DISJOINT_SUBSET \\
           Q.EXISTS_TAC ‘set vs’ >> simp [Once DISJOINT_SYM] \\
           simp [Abbr ‘vs2'’, LIST_TO_SET_DROP] ]) \\
  (* stage work, instantiating the key substitution assumption with q <> [] *)
     Q.PAT_X_ASSUM ‘!q. q <<= p /\ q <> [] ==> _’ drule >> art [] \\
     DISCH_TAC \\
  (* NOTE: ‘solvable (subterm' X (M i) q r)’ only holds when ‘q <<= FRONT p’.
     The case that ‘unsolvable (subterm' X (M j1/j2) q r)’ (p = q) must be
     treated specially. In this case, ltree_el (BT' X (M i) r q = SOME bot.
   *)
     reverse (Cases_on ‘solvable (subterm' X (M j1) q r)’)
     >- (‘q <<= FRONT p \/ q = p’ by METIS_TAC [IS_PREFIX_FRONT_CASES]
         >- (‘solvable (subterm' X (M j1) q r)’ by METIS_TAC []) \\
         POP_ASSUM (fs o wrap) >> T_TAC \\
         Know ‘unsolvable (subterm' X (M j1) p r) <=>
               ltree_el (BT' X (M j1) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         simp [] >> DISCH_THEN K_TAC \\
         DISCH_TAC \\
      (* applying ltree_equiv_bot_eq *)
         Know ‘ltree_el (BT' X (M j2) r) p = SOME bot’
         >- (MATCH_MP_TAC ltree_equiv_some_bot_imp >> simp []) \\
         Know ‘unsolvable (subterm' X (M j2) p r) <=>
               ltree_el (BT' X (M j2) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         DISCH_THEN (REWRITE_TAC o wrap o SYM) \\
         DISCH_TAC (* unsolvable (subterm' X (M j2) p r) *) \\
         Know ‘unsolvable (subterm' X (H j1) p r) /\
               unsolvable (subterm' X (H j2) p r)’
         >- (ASM_SIMP_TAC std_ss [] \\
             CONJ_TAC (* 2 subgoals, same tactics *) \\
             MATCH_MP_TAC unsolvable_ISUB \\
             simp [solvable_tpm]) >> STRIP_TAC \\
         Know ‘unsolvable (subterm' X (H j1) p r) <=>
               ltree_el (BT' X (H j1) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []) \\
         simp [] >> DISCH_THEN K_TAC \\
         Know ‘unsolvable (subterm' X (H j2) p r) <=>
               ltree_el (BT' X (H j2) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []) \\
         simp []) \\
     reverse (Cases_on ‘solvable (subterm' X (M j2) q r)’)
     >- (‘q <<= FRONT p \/ q = p’ by METIS_TAC [IS_PREFIX_FRONT_CASES]
         >- (‘solvable (subterm' X (M j2) q r)’ by METIS_TAC []) \\
         POP_ASSUM (fs o wrap) >> T_TAC \\
         Know ‘unsolvable (subterm' X (M j2) p r) <=>
               ltree_el (BT' X (M j2) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) >> simp [] \\
         NTAC 2 DISCH_TAC \\
         Know ‘ltree_el (BT' X (M j1) r) p = SOME bot’
         >- (MATCH_MP_TAC ltree_equiv_some_bot_imp' >> simp []) \\
      (* applying BT_subterm_thm *)
         MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm) \\
         rw [] >> fs [] \\
         rename1 ‘(\(N,r). NONE) z = SOME T’ \\
         Cases_on ‘z’ >> FULL_SIMP_TAC std_ss []) \\
  (* stage work, now applying BT_subterm_thm on ‘M j1’ *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     qabbrev_tac ‘r1 = r + LENGTH q’ \\
     rename1 ‘subterm X (M j1) q r = SOME (N,r1)’ \\
     qabbrev_tac ‘N0 = principal_hnf N’ \\
     qabbrev_tac ‘m1 = hnf_children_size N0’ \\
     rename1 ‘ltree_el (BT' X (M j1) r) q = SOME (SOME (vs1,y1),SOME m1)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs1,y1)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r1’      K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m1’ K_TAC \\
     qabbrev_tac ‘n1 = LAMl_size N0’ \\
  (* applying BT_subterm_thm again *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j2 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     rename1 ‘subterm X (M j2) q r = SOME (N',r1)’ \\
     qabbrev_tac ‘N0' = principal_hnf N'’ \\
     qabbrev_tac ‘m2 = hnf_children_size N0'’ \\
     rename1 ‘ltree_el (BT' X (M j2) r) q = SOME (SOME (vs2,y2),SOME m2)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs2,y2)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r1’      K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m2’ K_TAC \\
     qabbrev_tac ‘n2 = LAMl_size N0'’ \\
     simp [head_equivalent_def] \\
  (* decompose N *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n1 X = vs1’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs1 :string list”, “r1 :num”, “n1 :num”)) ‘X’ \\
     qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vs1)’ \\
     Q_TAC (HNF_TAC (“N0 :term”, “vs1 :string list”,
                     “y1' :string”, “Ns1 :term list”)) ‘N1’ \\
    ‘TAKE (LAMl_size N0) vs1 = vs1’ by rw [] \\
     POP_ASSUM (rfs o wrap) >> T_TAC \\
    ‘LENGTH Ns1 = m1 /\ hnf_headvar N1 = y1' /\ hnf_children N1 = Ns1’
       by rw [Abbr ‘m1’] \\
     Q.PAT_X_ASSUM ‘N0 = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘N1 = _’ (ASSUME_TAC o SYM) \\
  (* decompose N' *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n2 X = vs2’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs2 :string list”, “r1 :num”, “n2 :num”)) ‘X’ \\
     qabbrev_tac ‘N1' = principal_hnf (N0' @* MAP VAR vs2)’ \\
     Q_TAC (HNF_TAC (“N0' :term”, “vs2 :string list”,
                     “y2' :string”, “Ns2 :term list”)) ‘N1'’ \\
    ‘TAKE (LAMl_size N0') vs2 = vs2’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘LENGTH Ns2 = m2 /\ hnf_headvar N1' = y2' /\ hnf_children N1' = Ns2’
       by rw [Abbr ‘m2’] \\
     Q.PAT_X_ASSUM ‘N0' = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘N1' = _’ (ASSUME_TAC o SYM) \\
     DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [Once EQ_SYM_EQ]) >> gs [] \\
     Q.PAT_X_ASSUM ‘y2' = y1’ (fs o wrap) \\
     Q.PAT_X_ASSUM ‘y1' = y1’ (fs o wrap) \\
  (* stage work, preparing for BT_subterm_thm on ‘H j1’ and ‘H j2’*)
     Know ‘subterm X (H j1) q r <> NONE /\
           subterm X (H j2) q r <> NONE’
     >- ASM_SIMP_TAC std_ss [] >> STRIP_TAC \\
     Know ‘IMAGE y (count k) SUBSET X UNION RANK r1’
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
             rw [RANK_MONO, Abbr ‘r1’]) \\
         rw [SUBSET_DEF] >> rename1 ‘i < k’ \\
         Know ‘y i IN Z’ >- rw [] \\
         Suff ‘Z SUBSET X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         FIRST_X_ASSUM ACCEPT_TAC) >> DISCH_TAC \\
  (* some properties needed by the next "solvable" subgoal *)
     Know ‘set vs SUBSET X UNION RANK r1’
     >- (Suff ‘set vs SUBSET RANK r1’ >- SET_TAC [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> art [] \\
         simp [Abbr ‘r1’, RANK_MONO]) >> DISCH_TAC \\
     Know ‘set ys SUBSET X UNION RANK r1’
     >- (Suff ‘set ys SUBSET RANK r1’ >- SET_TAC [] \\
         qunabbrev_tac ‘ys’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r1’] \\
         rw [LENGTH_NON_NIL]) >> DISCH_TAC \\
     Know ‘FV (tpm (REVERSE pm) N)  SUBSET X UNION RANK r1 /\
           FV (tpm (REVERSE pm) N') SUBSET X UNION RANK r1’
     >- (CONJ_TAC \\
         MATCH_MP_TAC FV_tpm_lemma \\
         Q.EXISTS_TAC ‘r1’ >> simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP]) \\
     STRIP_TAC \\
  (* applying subterm_width_last on N and N' (subterm X (M j) q r) *)
     Know ‘m1 <= d_max’ (* m1 = hnf_children_size N0 *)
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
         reverse CONJ_TAC >- rw [Abbr ‘d_max’] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j1) p’ \\
         reverse CONJ_TAC >- simp [] \\
         qunabbrevl_tac [‘m1’, ‘N0’] \\
        ‘N = subterm' X (M j1) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_width_last >> simp []) >> DISCH_TAC \\
     Know ‘m2 <= d_max’ (* m2 = hnf_children_size N0' *)
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
         reverse CONJ_TAC >- rw [Abbr ‘d_max’] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j2) p’ \\
         reverse CONJ_TAC >- simp [] \\
         qunabbrevl_tac [‘m2’, ‘N0'’] \\
        ‘N' = subterm' X (M j2) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_width_last >> simp []) >> DISCH_TAC \\
     Know ‘solvable (subterm' X (H j1) q r) /\
           solvable (subterm' X (H j2) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
           qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
           simp [subterm_width_nil, principal_hnf_tpm'] \\
           rpt STRIP_TAC \\
           Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
           Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
           simp [Abbr ‘r1’, RANK_MONO],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
           qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
           simp [subterm_width_nil, principal_hnf_tpm'] \\
           rpt STRIP_TAC \\
           Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
           Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
           simp [Abbr ‘r1’, RANK_MONO] ]) >> STRIP_TAC \\
  (* extra goal *)
     reverse CONJ_TAC
     >- (Suff ‘subterm X (apply pi (M j1)) q r = subterm X (H j1) q r’
         >- (Rewr >> art []) \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> principal_hnf (apply pi (M i)) = H i’
           (MP_TAC o Q.SPEC ‘j1’) >> art [] \\
         DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM) \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC subterm_of_principal_hnf >> simp []) \\
  (* stage work *)
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC \\
  (* applying BT_subterm_thm on ‘H j1’ *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j1 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     rename1 ‘subterm X (H j1) q r = SOME (W,r1)’ \\
     qabbrev_tac ‘W0 = principal_hnf W’ \\
     qabbrev_tac ‘m3 = hnf_children_size W0’ \\
     rename1 ‘ltree_el (BT' X (H j1) r) q = SOME (SOME (vs3,y3),SOME m3)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs3,y3)’ K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m3’       K_TAC \\
     qabbrev_tac ‘n3 = LAMl_size W0’ \\
     Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC \\
  (* applying BT_subterm_thm on ‘H j2’ *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j2 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     rename1 ‘subterm X (H j2) q r = SOME (W',r1)’ \\
     qabbrev_tac ‘W0' = principal_hnf W'’ \\
     qabbrev_tac ‘m4 = hnf_children_size W0'’ \\
     rename1 ‘ltree_el (BT' X (H j2) r) q = SOME (SOME (vs4,y4),SOME m4)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs4,y4)’ K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m4’       K_TAC \\
     qabbrev_tac ‘n4 = LAMl_size W0'’ \\
     Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC \\
  (* decompose W *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n3 X = vs3’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs3 :string list”, “r1 :num”, “n3 :num”)) ‘X’ \\
     qabbrev_tac ‘W1 = principal_hnf (W0 @* MAP VAR vs3)’ \\
     Q_TAC (HNF_TAC (“W0 :term”, “vs3 :string list”,
                     “y3' :string”, “Ns3 :term list”)) ‘W1’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs3) (FV W0)’ K_TAC \\
  (* decompose W' *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n4 X = vs4’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs4 :string list”, “r1 :num”, “n4 :num”)) ‘X’ \\
     qabbrev_tac ‘W1' = principal_hnf (W0' @* MAP VAR vs4)’ \\
     Q_TAC (HNF_TAC (“W0' :term”, “vs4 :string list”,
                     “y4' :string”, “Ns4 :term list”)) ‘W1'’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs4) (FV W0')’ K_TAC \\
  (* stage work *)
     Know ‘TAKE (LAMl_size W0) vs3 = vs3 /\ TAKE (LAMl_size W0') vs4 = vs4’
     >- simp [] \\
     DISCH_THEN (rfs o CONJUNCTS) \\
     Q.PAT_X_ASSUM ‘hnf_headvar (principal_hnf (W0 @* MAP VAR vs3)) = y3’ MP_TAC \\
     simp [] (* y3' = y3 *) \\
     DISCH_THEN (rfs o wrap) \\
     Q.PAT_X_ASSUM ‘hnf_headvar (principal_hnf (W0' @* MAP VAR vs4)) = y4’ MP_TAC \\
     simp [] (* y4' = y4 *) \\
     DISCH_THEN (rfs o wrap) \\
  (* properties of W0 *)
    ‘LAMl_size W0 = n3 /\ hnf_children_size W0 = m3 /\ hnf_headvar W1 = y3’
       by rw [] \\
     Q.PAT_X_ASSUM ‘W0 = _’  (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘W1 = _’  (ASSUME_TAC o SYM) \\
  (* properties of W0' *)
    ‘LAMl_size W0' = n4 /\ hnf_children_size W0' = m4 /\ hnf_headvar W1' = y4’
       by rw [] \\
     Q.PAT_X_ASSUM ‘W0' = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘W1' = _’ (ASSUME_TAC o SYM) \\
  (* stage work *)
     Know ‘W = tpm (REVERSE pm) N ISUB ss’
     >- (Q.PAT_X_ASSUM  ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’
           (MP_TAC o Q.SPEC ‘j1’) >> simp []) >> DISCH_TAC \\
     Know ‘W' = tpm (REVERSE pm) N' ISUB ss’
     >- (Q.PAT_X_ASSUM  ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’
           (MP_TAC o Q.SPEC ‘j2’) >> simp []) >> DISCH_TAC \\
  (* applying hreduce_ISUB and tpm_hreduces *)
    ‘N -h->* N0 /\ N' -h->* N0'’ by METIS_TAC [principal_hnf_thm'] \\
     Know ‘W  -h->* tpm (REVERSE pm) N0  ISUB ss /\
           W' -h->* tpm (REVERSE pm) N0' ISUB ss’
     >- simp [hreduce_ISUB, tpm_hreduces] \\
     Q.PAT_X_ASSUM ‘LAMl vs1 _ = N0’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘LAMl vs2 _ = N0'’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = N1’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = N1'’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘W  = tpm (REVERSE pm) N  ISUB ss’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘W' = tpm (REVERSE pm) N' ISUB ss’ (ASSUME_TAC o SYM) \\
     simp [tpm_LAMl, tpm_appstar] \\
     qabbrev_tac ‘y1'  = lswapstr (REVERSE pm) y1’ \\
     qabbrev_tac ‘Ns1' = listpm term_pmact (REVERSE pm) Ns1’ \\
     qabbrev_tac ‘Ns2' = listpm term_pmact (REVERSE pm) Ns2’ \\
  (* pm = ZIP (vs,ys), where ys is in ROW r, vs is in ROW 0.
     vs1 is in ROW r1 = r + LENGTH q > r, as q <> [].
   *)
     Know ‘listpm string_pmact (REVERSE pm) vs1 = vs1’
     >- (simp [Once LIST_EQ_REWRITE] \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         MATCH_MP_TAC lswapstr_unchanged' \\
         simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           POP_ASSUM MP_TAC \\
           Suff ‘DISJOINT (set vs1) (set vs)’
           >- (rw [DISJOINT_ALT] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
           MATCH_MP_TAC DISJOINT_SUBSET \\
           Q.EXISTS_TAC ‘set vs0’ >> art [] \\
           qunabbrevl_tac [‘vs1’, ‘vs0’] \\
           MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’],
           (* goal 2 (of 2) *)
           POP_ASSUM MP_TAC \\
           Suff ‘DISJOINT (set vs1) (set ys)’
           >- (rw [DISJOINT_ALT] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
           qunabbrevl_tac [‘vs1’, ‘ys’] \\
           MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’] ]) >> Rewr' \\
     Know ‘listpm string_pmact (REVERSE pm) vs2 = vs2’
     >- (simp [Once LIST_EQ_REWRITE] \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         MATCH_MP_TAC lswapstr_unchanged' \\
         simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           POP_ASSUM MP_TAC \\
           Suff ‘DISJOINT (set vs2) (set vs)’
           >- (rw [DISJOINT_ALT] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
           MATCH_MP_TAC DISJOINT_SUBSET \\
           Q.EXISTS_TAC ‘set vs0’ >> art [] \\
           qunabbrevl_tac [‘vs2’, ‘vs0’] \\
           MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’],
           (* goal 2 (of 2) *)
           POP_ASSUM MP_TAC \\
           Suff ‘DISJOINT (set vs2) (set ys)’
           >- (rw [DISJOINT_ALT] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
           qunabbrevl_tac [‘vs2’, ‘ys’] \\
           MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’] ]) >> Rewr' \\
  (* NOTE: DOM ss = IMAGE y k, SUBSET Z, SUBSET X UNION RANK r *)
     Know ‘DISJOINT (set vs1) (DOM ss)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> simp [] \\
             rw [SUBSET_DEF] >> simp []) \\
         simp [DISJOINT_UNION', Abbr ‘vs1’] \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs2) (DOM ss)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> simp [] \\
             rw [SUBSET_DEF] >> simp []) \\
         simp [DISJOINT_UNION', Abbr ‘vs2’] \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     simp [LAMl_ISUB, appstar_ISUB] \\
     qabbrev_tac ‘Ns1'' = MAP (\t. t ISUB ss) Ns1'’ \\
     qabbrev_tac ‘Ns2'' = MAP (\t. t ISUB ss) Ns2'’ \\
  (* easy case *)
     reverse (Cases_on ‘y1' IN DOM ss’)
     >- (simp [ISUB_VAR_FRESH'] >> STRIP_TAC \\
        ‘hnf (LAMl vs1 (VAR y1' @* Ns1'')) /\
         hnf (LAMl vs2 (VAR y1' @* Ns2''))’ by rw [hnf_appstar] \\
        ‘LAMl vs1 (VAR y1' @* Ns1'') = W0 /\
         LAMl vs2 (VAR y1' @* Ns2'') = W0'’ by METIS_TAC [principal_hnf_thm'] \\
        ‘LAMl_size W0 = n1 /\ LAMl_size W0' = n2’ by rw [LAMl_size_hnf] \\
        ‘n3 = n1 /\ n4 = n2’ by PROVE_TAC [] \\
         simp [head_equivalent_def] \\
         Know ‘y3 = y1' /\ y4 = y1' /\ Ns1'' = Ns3 /\ Ns2'' = Ns4’
         >- (Q.PAT_X_ASSUM ‘LAMl vs3 _ = W0’ MP_TAC \\
             Q.PAT_X_ASSUM ‘_ = W1’ (REWRITE_TAC o wrap o SYM) \\
             Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
             Q.PAT_X_ASSUM ‘LAMl vs4 _ = W0'’ MP_TAC \\
             Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) \\
             Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
             NTAC 2 (POP_ASSUM (fs o wrap))) >> STRIP_TAC \\
         simp [Abbr ‘m3’, Abbr ‘m4’] \\
         NTAC 2 (POP_ASSUM (REWRITE_TAC o wrap o SYM)) \\
         Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘Ns1'’, Abbr ‘Ns2'’, Abbr ‘Ns1''’, Abbr ‘Ns2''’]) \\
  (* hard case *)
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
     POP_ASSUM MP_TAC >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC) \\
    ‘(LEAST j. y j = y1') = f j3’ by rw [] >> POP_ORW \\
  (* preparing for hreduce_permutator_shared *)
    ‘LENGTH Ns1'' = m1 /\ LENGTH Ns2'' = m2’
       by simp [Abbr ‘Ns1''’, Abbr ‘Ns2''’, Abbr ‘Ns1'’, Abbr ‘Ns2'’] \\
     qabbrev_tac ‘X' = BIGUNION (IMAGE FV (set Ns1'')) UNION
                       BIGUNION (IMAGE FV (set Ns2''))’ \\
    ‘FINITE X'’ by rw [Abbr ‘X'’] \\
  (* NOTE: Here the length of L must be big enough that ‘n3 <= LENGTH L’ can
     be proved later.

     It will be shown that SUC d_max + n1 - m1 = n3 = n4. Depending on the
     independent n1 and m1, either SUC d_max <= n3 or n3 <= SUC d_max.

     Thus ‘MAX n3 (SUC (d_max' j3))’ is the suitable length to be used here.
   *)
     qabbrev_tac ‘d' = MAX n3 (SUC (d_max' j3))’ \\
     Q_TAC (NEWS_TAC (“L :string list”, “d' :num”)) ‘X'’ \\
    ‘d_max' j3 < LENGTH L /\ n3 <= LENGTH L’ by simp [Abbr ‘d'’, MAX_LE] \\
     Know ‘DISJOINT (set L) (set vs1) /\
           DISJOINT (set L) (set vs2) /\
           DISJOINT (set L) (set vs3) /\
           DISJOINT (set L) (set vs4)’
     >- (rw [Abbr ‘L’, Abbr ‘vs1’, Abbr ‘vs2’, Abbr ‘vs3’, Abbr ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘FINITE X'’ K_TAC \\
     Q.PAT_X_ASSUM ‘DISJOINT (set L) X'’ MP_TAC \\
     qunabbrev_tac ‘X'’ \\
     DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DISJOINT_UNION']) \\
     STRIP_TAC (* W -h->* ... /\ W' -h->* ... *) \\
    ‘m1 <= d_max' j3 /\ m2 <= d_max' j3’ by simp [Abbr ‘d_max'’] \\
  (* applying hreduce_permutator_shared *)
     MP_TAC (Q.SPECL [‘Ns1''’, ‘d_max + f (j3 :num)’, ‘L’]
                     hreduce_permutator_shared) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘zs1’ (Q.X_CHOOSE_THEN ‘z1’ STRIP_ASSUME_TAC)) \\
  (* applying hreduce_permutator_shared again *)
     MP_TAC (Q.SPECL [‘Ns2''’, ‘d_max + f (j3 :num)’, ‘L’]
                     hreduce_permutator_shared) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘zs2’ (Q.X_CHOOSE_THEN ‘z2’ STRIP_ASSUME_TAC)) \\
     qabbrev_tac ‘P' = P (f j3)’ \\
     Q.PAT_X_ASSUM ‘P' @* Ns1'' -h->* _’ MP_TAC \\
     Q.PAT_X_ASSUM ‘P' @* Ns2'' -h->* _’ MP_TAC \\
     qabbrev_tac ‘h = LAST L’ (* new shared head variable *) \\
     qabbrev_tac ‘L' = FRONT L’ \\
    ‘L <> []’ by rw [GSYM LENGTH_NON_NIL] \\
     NTAC 2 (Q.PAT_X_ASSUM ‘IS_SUFFIX L _’ MP_TAC) \\
    ‘L = SNOC h L'’ by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
     POP_ORW \\
     simp [IS_SUFFIX] >> NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM ‘z1 = z2’ (simp o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘h  = z1’ (simp o wrap o SYM) \\
     NTAC 2 STRIP_TAC \\
     qabbrev_tac ‘xs1 = SNOC h zs1’ \\ (* suffix of L *)
     qabbrev_tac ‘xs2 = SNOC h zs2’ \\ (* suffix of L *)
     Know ‘IS_SUFFIX L xs1 /\ IS_SUFFIX L xs2’
     >- (‘L = SNOC h L'’
           by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
         POP_ORW \\
         simp [IS_SUFFIX, Abbr ‘xs1’, Abbr ‘xs2’]) >> STRIP_TAC \\
     Know ‘LAMl vs1 (P' @* Ns1'') -h->*
           LAMl vs1 (LAMl zs1 (LAM h (VAR h @* Ns1'' @* MAP VAR zs1))) /\
           LAMl vs2 (P' @* Ns2'') -h->*
           LAMl vs2 (LAMl zs2 (LAM h (VAR h @* Ns2'' @* MAP VAR zs2)))’
     >- simp [hreduce_LAMl] \\
     Q.PAT_X_ASSUM ‘P' @* Ns1'' -h->* _’ K_TAC \\
     Q.PAT_X_ASSUM ‘P' @* Ns2'' -h->* _’ K_TAC \\
     REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND] \\
     qabbrev_tac ‘Ns1x = Ns1'' ++ MAP VAR zs1’ \\
     qabbrev_tac ‘Ns2x = Ns2'' ++ MAP VAR zs2’ \\
     REWRITE_TAC [GSYM LAMl_SNOC] \\
     qabbrev_tac ‘zs1' = SNOC h (vs1 ++ zs1)’ \\
     qabbrev_tac ‘zs2' = SNOC h (vs2 ++ zs2)’ \\
     STRIP_TAC \\
     Know ‘W  -h->* LAMl zs1' (VAR h @* Ns1x) /\
           W' -h->* LAMl zs2' (VAR h @* Ns2x)’
     >- PROVE_TAC [hreduce_TRANS] \\
     NTAC 2 (POP_ASSUM K_TAC) >> STRIP_TAC \\
     Know ‘LAMl zs1' (VAR h @* Ns1x) = W0 /\
           LAMl zs2' (VAR h @* Ns2x) = W0'’
     >- (‘hnf (LAMl zs1' (VAR h @* Ns1x)) /\ hnf (LAMl zs2' (VAR h @* Ns2x))’
            by rw [hnf_appstar] \\
         METIS_TAC [principal_hnf_thm']) >> STRIP_TAC \\
     Know ‘LENGTH zs1' = n3 /\ LENGTH zs2' = n4’
     >- (Q.PAT_X_ASSUM ‘_ = n3’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = n4’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> STRIP_TAC \\
  (* n3 = LENGTH zs1' = 1 + LENGTH (vs1 ++ zs1) = 1 + d_max + n1 - m1 *)
     Know ‘SUC (d_max' j3) + n1 - m1 = n3 /\
           SUC (d_max' j3) + n2 - m2 = n4’
     >- (Q.PAT_X_ASSUM ‘_ = n3’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = n4’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘zs1'’, Abbr ‘zs2'’]) >> STRIP_TAC \\
     Know ‘n4 = n3’
     >- (NTAC 2 (POP_ASSUM (REWRITE_TAC o wrap o SYM)) \\
         simp []) >> DISCH_TAC \\
    ‘vs4 = vs3’ by simp [Abbr ‘vs4’, Abbr ‘vs3’] \\
     simp [head_equivalent_def] \\
     Know ‘m4 = m3’
     >- (Q.PAT_X_ASSUM ‘hnf_children_size W0  = m3’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘hnf_children_size W0' = m4’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘Ns1x’, Abbr ‘Ns2x’]) >> DISCH_TAC \\
     simp [] (* it remains to prove ‘y3 = y4’ *) \\
  (* NOTE: Now we know:

     1. LAMl zs1' (VAR h @* Ns1x) = W0
     2. LAMl zs2' (VAR h @* Ns2x) = W0'
     3. principal_hnf (W0  @* MAP VAR vs3) = VAR y3 @* Ns3 (= W1 )
     4. principal_hnf (W0' @* MAP VAR vs4) = VAR y4 @* Ns4 (= W1')

     Thus y3 and y4 are the same permutation of h, thus is the same. To
     actually prove it, we can use [principal_hnf_tpm_reduce'], which requires
    ‘DISJOINT (set vs3) (FV (VAR z2 @* Ns1x))’, which is explained below:

     We know that vs3 (vs4) is in ROW r1 (r + LENGTH q), on the other hand,

     - zs2 (part of Ns1x), prefix of L, can be chosen to exclude anything;
     - z2, part of L, can be chosen to exclude anything;
     - Ns1'' (part of Ns1x), FV is equal or less than Ns1';
     - Ns1' is tpm (REVERSE pm) of Ns1;
     - pm = ZIP (vs,ys), vs is in ROW 0, ys s in ROW r;

     - FV (Ns1) <= FV (VAR y1 @* Ns1) <= FV (N0 @* MAP VAR vs1)
                <= FV N + vs1 <= X UNION RANK r1 + vs1 (in ROW r1)

     - vs1     = RNEWS r1 n1 X (NOTE: n1 <> n2)
     - vs2     = RNEWS r1 n2 X
     - vs3/vs4 = RNEWS r1 n3/n4 X

                      ----- L -------------->| (LENGTH = SUC d_max)
     zs1' = |<--- vs1 --->|<--- zs1 ------>|h| (ROW 0 & r1)
     vs3  = |<---(vs1)--- vs3 ----(xs1)----->| (ROW r1)
             (n3 = 1 + d_max + n1 - m1 > n1)

                      ----- L -------------->| (LENGTH = SUC d_max)
     zs2' = |<--- vs2 ------>|<-- zs2 ---->|h| (ROW 0 & r1)
     vs3  = |<---(vs2)----- vs4 ---(xs2)---->| (ROW r1)
             (n4 = 1 + d_max + n2 - m2 > n2)

     now applying RNEWS_prefix first:
   *)
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
     Know ‘vs1 <<= vs3’
     >- (qunabbrevl_tac [‘vs1’, ‘vs3’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
    ‘n1' = n1’ by rw [] \\
     Q.PAT_X_ASSUM ‘n1' <= n3’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs1 = TAKE n1' vs3’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> rpt STRIP_TAC \\
     Know ‘vs2 <<= vs3’
     >- (qunabbrevl_tac [‘vs2’, ‘vs3’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
    ‘n2' = n2’ by rw [] \\
     Q.PAT_X_ASSUM ‘n2' <= n3’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs2 = TAKE n2' vs3’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> rpt STRIP_TAC \\
    ‘zs1' = vs1 ++ xs1’ by simp [Abbr ‘zs1'’, Abbr ‘xs1’] \\
    ‘zs2' = vs2 ++ xs2’ by simp [Abbr ‘zs2'’, Abbr ‘xs2’] \\
     qabbrev_tac ‘ys1 = DROP n1 vs3’ \\
     qabbrev_tac ‘ys2 = DROP n2 vs3’ \\
  (* NOTE: xs1 is part of L, which excludes vs3 which drops to ys1 *)
     Know ‘DISJOINT (set xs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys1’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set xs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys2’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs1 = LENGTH ys1 /\ LENGTH xs2 = LENGTH ys2’
       by simp [Abbr ‘xs1’, Abbr ‘ys1’, Abbr ‘xs2’, Abbr ‘ys2’] \\
    ‘vs1 ++ ys1 = vs3 /\ vs2 ++ ys2 = vs3’ by METIS_TAC [TAKE_DROP] \\
  (* applying hreduce_BETA_extended:
     W0 @* MAP VAR vs3
     = LAMl zs1' (VAR h @* Ns1x) @* MAP VAR vs3
     = LAMl (vs1 ++ xs1) (VAR h @* Ns1x) @* MAP VAR (vs1 ++ ys1)
     = LAMl vs1 (LAMl xs1 (VAR h @* Ns1x)) @* MAP VAR vs1 @* MAP VAR ys1
          -h->* (LAMl xs1 (VAR h @* Ns1x)) @* MAP VAR ys1
   *)
     Know ‘W0 @* MAP VAR vs3 -h->* LAMl xs1 (VAR h @* Ns1x) @* MAP VAR ys1’
     >- (Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘zs1' = vs1 ++ xs1’ (REWRITE_TAC o wrap) \\
         Q.PAT_X_ASSUM ‘vs1 ++ ys1 = vs3’ (REWRITE_TAC o wrap o SYM) \\
         REWRITE_TAC [LAMl_APPEND, MAP_APPEND, appstar_APPEND] \\
         REWRITE_TAC [hreduce_BETA_extended]) >> DISCH_TAC \\
     Know ‘W0' @* MAP VAR vs3 -h->* LAMl xs2 (VAR h @* Ns2x) @* MAP VAR ys2’
     >- (Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘zs2' = vs2 ++ xs2’ (REWRITE_TAC o wrap) \\
         Q.PAT_X_ASSUM ‘vs2 ++ ys2 = vs3’ (REWRITE_TAC o wrap o SYM) \\
         REWRITE_TAC [LAMl_APPEND, MAP_APPEND, appstar_APPEND] \\
         REWRITE_TAC [hreduce_BETA_extended]) >> DISCH_TAC \\
  (* NOTE: The following disjointness hold for names from different rows *)
     Know ‘DISJOINT (set vs) (set ys1) /\
           DISJOINT (set vs) (set ys2)’
     >- (CONJ_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         simp [Abbr ‘ys1’, Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> STRIP_TAC \\
     Know ‘DISJOINT (set ys) (set ys1) /\
           DISJOINT (set ys) (set ys2)’
     >- (CONJ_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         simp [Abbr ‘ys1’, Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> STRIP_TAC \\
  (* NOTE: xs1 is part of L, ys1 is part of vs3 *)
     Know ‘DISJOINT (set xs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set xs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘ALL_DISTINCT xs1 /\ ALL_DISTINCT xs2’ by METIS_TAC [IS_SUFFIX_ALL_DISTINCT] \\
    ‘ALL_DISTINCT ys1 /\ ALL_DISTINCT ys2’ by METIS_TAC [ALL_DISTINCT_DROP] \\
  (* applying hreduce_tpm_reduce *)
     Know ‘LAMl xs1 (VAR h @* Ns1x) @* MAP VAR ys1 -h->*
           tpm (ZIP (xs1,ys1)) (VAR h @* Ns1x)’
     >- (MATCH_MP_TAC hreduce_tpm_reduce \\
         simp [hnf_appstar, Abbr ‘Ns1x’] \\
         Know ‘FV (VAR h @* (Ns1'' ++ MAP VAR zs1)) =
               set xs1 UNION BIGUNION (IMAGE FV (set Ns1''))’
         >- (simp [appstar_APPEND, FV_appstar_MAP_VAR] \\
             simp [FV_appstar, Abbr ‘xs1’, LIST_TO_SET_SNOC] \\
             SET_TAC []) >> Rewr' \\
         simp [Once DISJOINT_SYM, DISJOINT_UNION'] \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m1’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns1''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV (EL i Ns1')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns1'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns1'’]) \\
      (* The key is to prove DISJOINT (set vsx) (FV (EL i Ns1)) *)
         POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns1'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] >> DISCH_TAC \\
      (* applying FV_tpm_disjoint *)
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys1) (FV (EL i Ns1)) *)
         Know ‘FV N0 SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N’ >> art [] \\
             qunabbrev_tac ‘N0’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns1) SUBSET FV N UNION set vs1’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0’, ‘n1’, ‘m1’, ‘N1’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N UNION set vs1’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
             Q.PAT_X_ASSUM ‘vs1 ++ ys1 = vs3’ (REWRITE_TAC o wrap o SYM) \\
             simp [ALL_DISTINCT_APPEND, DISJOINT_ALT']) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘vs1 ++ ys1 = vs3’ (REWRITE_TAC o wrap o SYM) \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs3’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> DISCH_TAC \\
  (* applying hreduce_tpm_reduce again, proof is symmetric with the above *)
     Know ‘LAMl xs2 (VAR h @* Ns2x) @* MAP VAR ys2 -h->*
           tpm (ZIP (xs2,ys2)) (VAR h @* Ns2x)’
     >- (MATCH_MP_TAC hreduce_tpm_reduce \\
         simp [hnf_appstar, Abbr ‘Ns2x’] \\
         Know ‘FV (VAR h @* (Ns2'' ++ MAP VAR zs2)) =
               set xs2 UNION BIGUNION (IMAGE FV (set Ns2''))’
         >- (simp [appstar_APPEND, FV_appstar_MAP_VAR] \\
             simp [FV_appstar, Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
             SET_TAC []) >> Rewr' \\
         simp [Once DISJOINT_SYM, DISJOINT_UNION'] \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m2’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns2''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV (EL i Ns2')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns2'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns2'’]) \\
         POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns2'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] >> DISCH_TAC \\
      (* applying FV_tpm_disjoint *)
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys2) (FV (EL i Ns2)) *)
         Know ‘FV N0' SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N'’ >> art [] \\
             qunabbrev_tac ‘N0'’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns2) SUBSET FV N' UNION set vs2’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0'’, ‘n2’, ‘m2’, ‘N1'’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N' UNION set vs2’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
             Q.PAT_X_ASSUM ‘vs2 ++ ys2 = vs3’ (REWRITE_TAC o wrap o SYM) \\
             simp [ALL_DISTINCT_APPEND, DISJOINT_ALT']) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘vs2 ++ ys2 = vs3’ (REWRITE_TAC o wrap o SYM) \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs3’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> DISCH_TAC \\
  (* stage work *)
     qabbrev_tac ‘pm1 = ZIP (xs1,ys1)’ \\
     qabbrev_tac ‘pm2 = ZIP (xs2,ys2)’ \\
    ‘W0  @* MAP VAR vs3 -h->* tpm pm1 (VAR h @* Ns1x) /\
     W0' @* MAP VAR vs3 -h->* tpm pm2 (VAR h @* Ns2x)’
       by PROVE_TAC [hreduce_TRANS] \\
     Q.PAT_X_ASSUM ‘_ -h->* LAMl xs1 (VAR h @* Ns1x) @* MAP VAR ys1’ K_TAC \\
     Q.PAT_X_ASSUM ‘_ -h->* LAMl xs2 (VAR h @* Ns2x) @* MAP VAR ys2’ K_TAC \\
     Q.PAT_X_ASSUM ‘LAMl xs1 (VAR h @* Ns1x) @* MAP VAR ys1 -h->* _’ K_TAC \\
     Q.PAT_X_ASSUM ‘LAMl xs2 (VAR h @* Ns2x) @* MAP VAR ys2 -h->* _’ K_TAC \\
  (* applying hreduces_hnf_imp_principal_hnf *)
     Know ‘W1  = tpm pm1 (VAR h @* Ns1x) /\
           W1' = tpm pm2 (VAR h @* Ns2x)’
     >- (simp [Abbr ‘W1’, Abbr ‘W1'’] \\
         CONJ_TAC (* 2 subgoals, same tactics *) \\
         MATCH_MP_TAC hreduces_hnf_imp_principal_hnf \\
         simp [hnf_appstar]) \\
     Q.PAT_X_ASSUM ‘_ = W1 ’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) \\
     simp [tpm_appstar] \\
     Suff ‘lswapstr pm1 h = lswapstr pm2 h’ >- simp [] \\
  (* NOTE: Now finding a common replacement for pm1 and pm2:

     |<--L--|<------------ ls -------------->|
     zs1' = |<--- xs1'--->|<--- zs1 ------>|h| (ROW 0)
                          |<------ xs1 ----->| (ROW r1)
     vs3  = |<---(vs1)--->|<------(ys1)----->| (ROW r1)
                                   pm1 = ZIP (xs1,ys1)
     |<--L--|<------------ ls -------------->|
     zs2' = |<--- xs2'------>|<-- zs2 ---->|h| (ROW 0)
                             |<--- xs2 ----->| (ROW r1)
     vs3  = |<---(vs2)------>|<---(ys2)----->| (ROW r1)
                                   pm2 = ZIP (xs2,ys2)
   *)
     qabbrev_tac ‘ls = LASTN n3 L’ \\
    ‘LENGTH ls = n3’ by simp [LENGTH_LASTN, Abbr ‘ls’] \\
     Know ‘set ls SUBSET set L’
     >- (SIMP_TAC list_ss [Abbr ‘ls’, SUBSET_DEF] \\
         REWRITE_TAC [MEM_LASTN]) >> DISCH_TAC \\
     qabbrev_tac ‘pm3 = ZIP (ls,vs3)’ \\
  (* applying IS_SUFFIX_IMP_LASTN *)
     Know ‘DROP n1 ls = xs1 /\ DROP n2 ls = xs2’
     >- (PRINT_TAC "stage work on subtree_equiv_lemma" \\
        ‘xs1 = LASTN (LENGTH xs1) L’ by simp [IS_SUFFIX_IMP_LASTN] \\
         POP_ORW \\
        ‘xs2 = LASTN (LENGTH xs2) L’ by simp [IS_SUFFIX_IMP_LASTN] \\
         POP_ORW \\
         MP_TAC (ISPECL [“n1 :num”, “ls :string list”] DROP_LASTN) \\
         MP_TAC (ISPECL [“n2 :num”, “ls :string list”] DROP_LASTN) \\
         simp [Abbr ‘ls’, LENGTH_LASTN] \\
         NTAC 2 (DISCH_THEN K_TAC) \\
         Know ‘LASTN (n3 - n1) (LASTN n3 L) = LASTN (n3 - n1) L’
         >- (irule LASTN_LASTN >> simp []) >> Rewr' \\
         Know ‘LASTN (n3 - n2) (LASTN n3 L) = LASTN (n3 - n2) L’
         >- (irule LASTN_LASTN >> simp []) >> Rewr' \\
         Suff ‘LENGTH ys1 = n3 - n1 /\ LENGTH ys2 = n3 - n2’ >- Rewr \\
         simp [Abbr ‘ys1’, Abbr ‘ys2’, LENGTH_DROP]) >> STRIP_TAC \\
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
  (* preparing for lswapstr_unchanged' *)
     qabbrev_tac ‘xs1' = TAKE n1 ls’ \\
     qabbrev_tac ‘xs2' = TAKE n2 ls’ \\
     Know ‘xs1' ++ xs1 = ls /\ xs2' ++ xs2 = ls’
     >- (Q.PAT_X_ASSUM ‘_ = xs1’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = xs2’ (REWRITE_TAC o wrap o SYM) \\
         simp [TAKE_DROP, Abbr ‘xs1'’, Abbr ‘xs2'’]) >> STRIP_TAC \\
    ‘LENGTH xs1' = n1 /\ LENGTH xs2' = n2’
       by simp [LENGTH_TAKE, Abbr ‘xs1'’, Abbr ‘xs2'’] \\
     Know ‘ZIP (xs1',vs1) ++ pm1 = pm3’
     >- (qunabbrevl_tac [‘pm1’, ‘pm2’, ‘pm3’] \\
         Q.PAT_X_ASSUM ‘xs1' ++ xs1 = ls’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘vs1 ++ ys1 = vs3’ (REWRITE_TAC o wrap o SYM) \\
         MATCH_MP_TAC ZIP_APPEND >> art []) >> DISCH_TAC \\
     Know ‘ZIP (xs2',vs2) ++ pm2 = pm3’
     >- (qunabbrevl_tac [‘pm1’, ‘pm2’, ‘pm3’] \\
         Q.PAT_X_ASSUM ‘xs2' ++ xs2 = ls’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘vs2 ++ ys2 = vs3’ (REWRITE_TAC o wrap o SYM) \\
         MATCH_MP_TAC ZIP_APPEND >> art []) >> DISCH_TAC \\
  (* applying lswapstr_append *)
     Know ‘lswapstr (ZIP (xs1',vs1) ++ pm1) h =
           lswapstr (ZIP (xs2',vs2) ++ pm2) h’ >- rw [] \\
     REWRITE_TAC [lswapstr_append] \\
     qabbrev_tac ‘t1 = lswapstr pm1 h’ \\
     qabbrev_tac ‘t2 = lswapstr pm2 h’ \\
     Suff ‘lswapstr (ZIP (xs1',vs1)) t1 = t1 /\
           lswapstr (ZIP (xs2',vs2)) t2 = t2’ >- Rewr \\
  (* NOTE: The key is to get a upper bound for t1 and t2.

     |<--L--|<------------ ls -------------->|
            |<--- xs1'--->|<--- zs1 ------>|h| (ROW 0)
                          |<------ xs1 ----->| (ROW r1)
     vs3  = |<---(vs1)--->|<------(ys1)----->| (ROW r1)
                                   pm1 = ZIP (xs1,ys1)
     |<--L--|<------------ ls -------------->|
            |<--- xs2'------>|<-- zs2 ---->|h| (ROW 0)
                             |<--- xs2 ----->| (ROW r1)
     vs3  = |<---(vs2)------>|<---(ys2)----->| (ROW r1)
                                   pm2 = ZIP (xs2,ys2)
   *)
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
       Know ‘t1 IN set ys1’
       >- (qunabbrevl_tac [‘t1’, ‘pm1’] \\
           MATCH_MP_TAC MEM_lswapstr >> art [] \\
           simp [Abbr ‘xs1’, LIST_TO_SET_SNOC]) \\
       Suff ‘DISJOINT (set ys1) (set xs1') /\
             DISJOINT (set ys1) (set vs1)’ >- rw [DISJOINT_ALT] \\
       reverse CONJ_TAC
       >- (ONCE_REWRITE_TAC [DISJOINT_SYM] \\
           Know ‘ALL_DISTINCT (vs1 ++ ys1)’ >- art [] \\
           SIMP_TAC bool_ss [ALL_DISTINCT_APPEND']) \\
       MATCH_MP_TAC DISJOINT_SUBSET' >> Q.EXISTS_TAC ‘set vs3’ \\
       reverse CONJ_TAC >- simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
       MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘set ls’ \\
       reverse CONJ_TAC >- simp [Abbr ‘xs1'’, LIST_TO_SET_TAKE] \\
       ONCE_REWRITE_TAC [DISJOINT_SYM] \\
       MATCH_MP_TAC DISJOINT_SUBSET' \\
       Q.EXISTS_TAC ‘set L’ >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
       Know ‘t2 IN set ys2’
       >- (qunabbrevl_tac [‘t2’, ‘pm2’] \\
           MATCH_MP_TAC MEM_lswapstr >> art [] \\
           simp [Abbr ‘xs2’, LIST_TO_SET_SNOC]) \\
       Suff ‘DISJOINT (set ys2) (set xs2') /\
             DISJOINT (set ys2) (set vs2)’ >- rw [DISJOINT_ALT] \\
       reverse CONJ_TAC
       >- (ONCE_REWRITE_TAC [DISJOINT_SYM] \\
           Know ‘ALL_DISTINCT (vs2 ++ ys2)’ >- art [] \\
           SIMP_TAC bool_ss [ALL_DISTINCT_APPEND']) \\
       MATCH_MP_TAC DISJOINT_SUBSET' >> Q.EXISTS_TAC ‘set vs3’ \\
       reverse CONJ_TAC >- simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
       MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘set ls’ \\
       reverse CONJ_TAC >- simp [Abbr ‘xs2'’, LIST_TO_SET_TAKE] \\
       ONCE_REWRITE_TAC [DISJOINT_SYM] \\
       MATCH_MP_TAC DISJOINT_SUBSET' \\
       Q.EXISTS_TAC ‘set L’ >> art [] ])
 (* final goal (before applying MONO_NOT_EQ):

    !M N. MEM M Ms /\ MEM N Ms /\
          subtree_equiv X (apply pi M) (apply pi N) p r ==>
          subtree_equiv' X M N p r
  *)
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> rpt GEN_TAC >> STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> ONCE_REWRITE_TAC [MONO_NOT_EQ]
 (* NOTE: The antecedent “~subtree_equiv' X t1 t2 q r” makes sure that
   ‘n1 + m2 <> n1 + m1’ is always assumed (instead of ‘y1 <> y2’). And
    the goal is to prove ‘y3 <> y4 \/ n3 + m3 <> n4 + m4’.
  *)
 >> NTAC 2 (Q.PAT_X_ASSUM ‘MEM _ Ms’ MP_TAC)
 >> simp [MEM_EL]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j1’ STRIP_ASSUME_TAC)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j2’ STRIP_ASSUME_TAC)
 >> Q.PAT_X_ASSUM ‘_ = M j1’ (REWRITE_TAC o wrap)
 >> Q.PAT_X_ASSUM ‘_ = M j2’ (REWRITE_TAC o wrap)
 >> qabbrev_tac ‘M' = \i. apply pi (M i)’
 (* real goal: ~subtree_equiv X (M j1) (M j2) p r ==>
               ~subtree_equiv X (M' j1) (M' j2) p r
  *)
 >> simp [subtree_equiv_def]
 >> Know ‘BT' X (M' j1) r = BT' X (principal_hnf (M' j1)) r’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_of_principal_hnf \\
     simp [Abbr ‘M'’] \\
     METIS_TAC [lameq_solvable_cong])
 >> Rewr'
 >> Know ‘BT' X (M' j2) r = BT' X (principal_hnf (M' j2)) r’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_of_principal_hnf \\
     simp [Abbr ‘M'’] \\
     METIS_TAC [lameq_solvable_cong])
 >> Rewr'
 >> simp [Abbr ‘M'’] (* now H is involved instead of ‘apply pi ...’ *)
 (* special case: q = [] *)
 >> Cases_on ‘q = []’
 >- (Q.PAT_X_ASSUM ‘!q. q <<= p /\ q <> [] ==> _’ K_TAC \\
     POP_ORW >> simp [BT_ltree_el_NIL] \\
     Know ‘!i. principal_hnf (H i) = H i’
     >- (rw [Abbr ‘H’] >> MATCH_MP_TAC principal_hnf_reduce \\
         rw [hnf_appstar]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!i. solvable (H i)’ K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> FV (H i) SUBSET X UNION RANK r’ K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> d_max <= LENGTH (hnf_children (H i))’ K_TAC \\
     simp [Abbr ‘H’, GSYM appstar_APPEND, hnf_head_appstar] \\
     simp [head_equivalent_def] \\
     qabbrev_tac ‘vs1 = TAKE (n j1) vs’ \\
     qabbrev_tac ‘vs2 = TAKE (n j2) vs’ \\
    ‘ALL_DISTINCT vs1 /\ ALL_DISTINCT vs2’
       by simp [Abbr ‘vs1’, Abbr ‘vs2’, ALL_DISTINCT_TAKE] \\
    ‘LENGTH vs1 = n j1’
       by (qunabbrev_tac ‘vs1’ \\
           MATCH_MP_TAC LENGTH_TAKE >> art [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
    ‘LENGTH vs2 = n j2’
       by (qunabbrev_tac ‘vs2’ \\
           MATCH_MP_TAC LENGTH_TAKE >> art [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Q_TAC (RNEWS_TAC (“ys1 :string list”, “r :num”,
                       “(n :num -> num) j1”)) ‘X’ \\
     Q_TAC (RNEWS_TAC (“ys2 :string list”, “r :num”,
                       “(n :num -> num) j2”)) ‘X’ \\
     Know ‘DISJOINT (set vs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         reverse CONJ_TAC >- rw [Abbr ‘vs1’, LIST_TO_SET_TAKE] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘ys1’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp []) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         reverse CONJ_TAC >- rw [Abbr ‘vs2’, LIST_TO_SET_TAKE] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘ys2’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp []) >> DISCH_TAC \\
     qabbrev_tac ‘t1 = VAR (y j1) @* args j1’ \\
     qabbrev_tac ‘t2 = VAR (y j2) @* args j2’ \\
  (* applying for principal_hnf_tpm_reduce *)
     Know ‘principal_hnf (LAMl vs1 t1 @* MAP VAR ys1) = tpm (ZIP (vs1,ys1)) t1’
     >- (‘hnf t1’ by rw [Abbr ‘t1’, hnf_appstar] \\
         MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n j1’] >> simp [] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘Z’ >> art [] \\
         rw [Abbr ‘t1’, FV_appstar]) >> Rewr' \\
     Know ‘principal_hnf (LAMl vs2 t2 @* MAP VAR ys2) = tpm (ZIP (vs2,ys2)) t2’
     >- (‘hnf t2’ by rw [Abbr ‘t2’, hnf_appstar] \\
         MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n j2’] >> simp [] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘Z’ >> art [] \\
         rw [Abbr ‘t2’, FV_appstar]) >> Rewr' \\
     simp [Abbr ‘t1’, Abbr ‘t2’, tpm_appstar] \\
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
     qabbrev_tac ‘pm1 = ZIP (vs1,ys1)’ \\
     qabbrev_tac ‘pm2 = ZIP (vs2,ys2)’ \\
     qabbrev_tac ‘vs1' = DROP (n j1) vs’ \\
     qabbrev_tac ‘vs2' = DROP (n j2) vs’ \\
  (* current situation:
        |<--------- vs (n_max) --------->|
        |<--- vs1 ----->|<---- vs1'----->|      y j1  ---+
        |<------ vs2 ------->|<--vs2'--->|      y j2  ---|--+
     ----------------------------------------------------|--|----
        |<--- ys1 ----->|------ys1'----->|      y' <-----+  |
        |<------ ys2 ------->|<--ys2'--->|      y' <--------+
   *)
     Know ‘ys1 <<= ys’
     >- (qunabbrevl_tac [‘ys1’, ‘ys’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
     Know ‘n1' = n j1’
     >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
         simp [LENGTH_TAKE]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘n1' <= n_max’ MP_TAC \\
     Q.PAT_X_ASSUM ‘ys1 = TAKE n1' ys’
       (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
     qabbrev_tac ‘ys1' = DROP (n j1) ys’ \\
    ‘vs1 ++ vs1' = vs /\ ys1 ++ ys1' = ys’ by METIS_TAC [TAKE_DROP] \\
     Know ‘ys2 <<= ys’
     >- (qunabbrevl_tac [‘ys2’, ‘ys’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
     Know ‘n2' = n j2’
     >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
         simp [LENGTH_TAKE]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘n2' <= n_max’ MP_TAC \\
     Q.PAT_X_ASSUM ‘ys2 = TAKE n2' ys’
       (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
     qabbrev_tac ‘ys2' = DROP (n j2) ys’ \\
    ‘vs2 ++ vs2' = vs /\ ys2 ++ ys2' = ys’ by METIS_TAC [TAKE_DROP] \\
  (* stage work *)
     Know ‘lswapstr pm1 (y j1) = lswapstr pm (y j1)’
     >- (‘LENGTH vs1' = LENGTH ys1'’ by rw [Abbr ‘vs1'’, Abbr ‘ys1'’] \\
         Know ‘pm = pm1 ++ ZIP (vs1',ys1')’
         >- (simp [Abbr ‘pm’, Abbr ‘pm1’] \\
            ‘LENGTH vs1 = LENGTH ys1’ by rw [Abbr ‘vs1'’] \\
             simp [ZIP_APPEND]) >> Rewr' \\
         simp [lswapstr_append, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
         reverse CONJ_TAC (* easy goal first *)
         >- (‘y j1 IN X UNION RANK r’ by METIS_TAC [SUBSET_DEF] \\
             Suff ‘DISJOINT (X UNION RANK r) (set ys1')’
             >- (REWRITE_TAC [DISJOINT_ALT] \\
                 DISCH_THEN MATCH_MP_TAC >> art []) \\
             MATCH_MP_TAC DISJOINT_SUBSET \\
             Q.EXISTS_TAC ‘set ys’ \\
             reverse CONJ_TAC >- simp [Abbr ‘ys1'’, LIST_TO_SET_DROP] \\
             simp [DISJOINT_UNION', Once DISJOINT_SYM] \\
             simp [Abbr ‘ys’, Once DISJOINT_SYM, DISJOINT_RNEWS_RANK]) \\
        ‘y j1 IN Y UNION set vs1’ by rw [Abbr ‘vs1’] \\
         Suff ‘DISJOINT (Y UNION set vs1) (set vs1')’
         >- (REWRITE_TAC [DISJOINT_ALT] \\
             DISCH_THEN MATCH_MP_TAC >> art []) \\
         REWRITE_TAC [DISJOINT_UNION] \\
         reverse CONJ_TAC (* easy goal first *)
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
             Q.PAT_X_ASSUM ‘vs1 ++ vs1' = vs’ (REWRITE_TAC o wrap o SYM) \\
             simp [ALL_DISTINCT_APPEND']) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs’ >> simp [Once DISJOINT_SYM] \\
         simp [Abbr ‘vs1'’, LIST_TO_SET_DROP]) >> Rewr' \\
     Know ‘lswapstr pm2 (y j2) = lswapstr pm (y j2)’
     >- (‘LENGTH vs2' = LENGTH ys2'’ by rw [Abbr ‘vs2'’, Abbr ‘ys2'’] \\
         Know ‘pm = pm2 ++ ZIP (vs2',ys2')’
         >- (simp [Abbr ‘pm’, Abbr ‘pm2’] \\
            ‘LENGTH vs2 = LENGTH ys2’ by rw [Abbr ‘vs2'’] \\
             simp [ZIP_APPEND]) >> Rewr' \\
         simp [lswapstr_append, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
         reverse CONJ_TAC (* easy goal first *)
         >- (‘y j2 IN X UNION RANK r’ by METIS_TAC [SUBSET_DEF] \\
             Suff ‘DISJOINT (X UNION RANK r) (set ys2')’
             >- (REWRITE_TAC [DISJOINT_ALT] \\
                 DISCH_THEN MATCH_MP_TAC >> art []) \\
             MATCH_MP_TAC DISJOINT_SUBSET \\
             Q.EXISTS_TAC ‘set ys’ \\
             reverse CONJ_TAC >- simp [Abbr ‘ys2'’, LIST_TO_SET_DROP] \\
             simp [DISJOINT_UNION', Once DISJOINT_SYM] \\
             simp [Abbr ‘ys’, Once DISJOINT_SYM, DISJOINT_RNEWS_RANK]) \\
        ‘y j2 IN Y UNION set vs2’ by rw [Abbr ‘vs2’] \\
         Suff ‘DISJOINT (Y UNION set vs2) (set vs2')’
         >- (REWRITE_TAC [DISJOINT_ALT] \\
             DISCH_THEN MATCH_MP_TAC >> art []) \\
         REWRITE_TAC [DISJOINT_UNION] \\
         reverse CONJ_TAC (* easy goal first *)
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
             Q.PAT_X_ASSUM ‘vs2 ++ vs2' = vs’ (REWRITE_TAC o wrap o SYM) \\
             simp [ALL_DISTINCT_APPEND']) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs’ >> simp [Once DISJOINT_SYM] \\
         simp [Abbr ‘vs2'’, LIST_TO_SET_DROP]) >> Rewr' \\
     simp [] \\
    ‘f j1 < k /\ f j2 < k’ by rw [] \\
    ‘b j1 = EL (j j1) xs /\ b j2 = EL (j j2) xs’ by rw [] \\
     NTAC 2 POP_ORW \\
     Know ‘EL (j j1) xs = EL (j j2) xs <=> j j1 = j j2’
     >- (Q.PAT_X_ASSUM ‘!i. i < k ==> EL (j i) xs = b i /\ _’ K_TAC \\
         MATCH_MP_TAC ALL_DISTINCT_EL_IMP >> art [] \\
         simp [Abbr ‘j’, Abbr ‘args2’, Abbr ‘d_max'’]) >> Rewr' \\
  (* !i. i < k ==> LENGTH (args' i ++ args2 i) <= d_max' i *)
     Know ‘LENGTH (args' j1 ++ args2 j1) <= d_max' j1 /\
           LENGTH (args' j2 ++ args2 j2) <= d_max' j2’
     >- simp [] \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> LENGTH (args' i ++ args2 i) <= d_max' i’ K_TAC \\
     simp [Abbr ‘Ns’, Abbr ‘tl’, Abbr ‘d_max'’, Abbr ‘args2’] \\
  (* arithmetic cleanups *)
     Know ‘d_max + (k + (n_max + (f j2 + (m j2 + SUC d_max)))) -
           (n j2 + SUC (d_max + f j2)) =
           d_max + k + n_max + m j2 - n j2’ >- simp [] >> Rewr' \\
     Know ‘d_max + (k + (n_max + (f j1 + (m j1 + SUC d_max)))) -
           (n j1 + SUC (d_max + f j1)) =
           d_max + k + n_max + m j1 - n j1’ >- simp [] >> Rewr' \\
     Know ‘d_max + k + n_max + m j2 - n j2 =
           d_max + k + n_max + m j1 - n j1 <=> m j2 + n j1 = m j1 + n j2’
     >- simp [] >> Rewr' \\
     simp [Abbr ‘j’] \\
     Cases_on ‘y j1 = y j2’ >> simp [] (* only one goal is left *) \\
     Cases_on ‘m j2 + n j1 = m j1 + n j2’ >> simp [] (* 1s left *) \\
    ‘m j1 <= d /\ m j2 <= d’ by rw [] \\
     STRIP_TAC \\
     qabbrev_tac ‘a1 = n_max + m j1’ \\
     qabbrev_tac ‘a2 = n_max + m j2’ \\
     qabbrev_tac ‘b1 = d_max + (f j1 + n j1)’ \\
     qabbrev_tac ‘b2 = d_max + (f j2 + n j2)’ \\
     Know ‘b1 - a1 <> b2 - a2 <=> b1 + a2 <> b2 + a1’ >- simp [] >> Rewr' \\
     qunabbrevl_tac [‘a1’, ‘a2’, ‘b1’, ‘b2’] \\
     Suff ‘f j1 <> f j2’ >- simp [Abbr ‘d_max’] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* instantiating the key substitution assumption with q <> [] *)
 >> Q.PAT_X_ASSUM ‘!q. q <<= p /\ q <> [] ==> _’ (MP_TAC o Q.SPEC ‘q’)
 >> simp [] >> DISCH_TAC
 (* some easy cases *)
 >> reverse (Cases_on ‘solvable (subterm' X (M j1) q r)’)
 >- (Know ‘unsolvable (subterm' X (M j1) q r) <=>
           ltree_el (BT' X (M j1) r) q = SOME bot’
     >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
     simp [] >> DISCH_THEN K_TAC \\
     Know ‘unsolvable (subterm' X (H j1) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC unsolvable_ISUB \\
         simp [solvable_tpm]) >> DISCH_TAC \\
  (* extra goal *)
     Know ‘unsolvable (subterm' X (apply pi (M j1)) q r)’
     >- (Suff ‘subterm X (apply pi (M j1)) q r = subterm X (H j1) q r’
         >- (Rewr >> art []) \\
         FULL_SIMP_TAC std_ss [] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> principal_hnf (apply pi (M i)) = H i’
           (MP_TAC o Q.SPEC ‘j1’) >> art [] \\
         DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM) \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC subterm_of_principal_hnf >> simp []) >> Rewr \\
     reverse (Cases_on ‘solvable (subterm' X (M j2) q r)’)
     >- (Know ‘unsolvable (subterm' X (M j2) q r) <=>
               ltree_el (BT' X (M j2) r) q = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         simp []) \\
     Know ‘unsolvable (subterm' X (H j1) q r) <=>
           ltree_el (BT' X (H j1) r) q = SOME bot’
     >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []) \\
     simp [] >> DISCH_THEN K_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j2 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     qabbrev_tac ‘r2 = r + LENGTH q’ \\
     rename1 ‘subterm X (M j2) q r = SOME (N,r2)’ \\
     qabbrev_tac ‘N0 = principal_hnf N’ \\
     qabbrev_tac ‘m2 = hnf_children_size N0’ \\
     rename1 ‘ltree_el (BT' X (M j2) r) q = SOME (SOME (vs2,y2),SOME m2)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs2,y2)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r2’            K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m2’       K_TAC \\
     qabbrev_tac ‘n2 = LAMl_size N0’ \\
  (* decompose N *)
     Q.PAT_X_ASSUM ‘RNEWS r2 n2 X = vs2’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs2 :string list”, “r2 :num”, “n2 :num”)) ‘X’ \\
     qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vs2)’ \\
     Q_TAC (HNF_TAC (“N0 :term”, “vs2 :string list”,
                     “y2' :string”, “Ns2 :term list”)) ‘N1’ \\
    ‘TAKE (LAMl_size N0) vs2 = vs2’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘subterm X (H j2) q r <> NONE’ by ASM_SIMP_TAC std_ss [] \\
     Know ‘IMAGE y (count k) SUBSET X UNION RANK r2’
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Suff ‘RANK r SUBSET RANK r2’ >- SET_TAC [] \\
             rw [RANK_MONO, Abbr ‘r2’]) \\
         rw [SUBSET_DEF] >> rename1 ‘i < k’ \\
         Know ‘y i IN Z’ >- rw [] \\
         Suff ‘Z SUBSET X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         FIRST_X_ASSUM ACCEPT_TAC) >> DISCH_TAC \\
     Know ‘set vs SUBSET X UNION RANK r2’
     >- (Suff ‘set vs SUBSET RANK r2’ >- SET_TAC [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> art [] \\
         simp [Abbr ‘r2’, RANK_MONO]) >> DISCH_TAC \\
     Know ‘set ys SUBSET X UNION RANK r2’
     >- (Suff ‘set ys SUBSET RANK r2’ >- SET_TAC [] \\
         qunabbrev_tac ‘ys’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r2’] \\
         rw [LENGTH_NON_NIL]) >> DISCH_TAC \\
     Know ‘FV (tpm (REVERSE pm) N) SUBSET X UNION RANK r2’
     >- (MATCH_MP_TAC FV_tpm_lemma \\
         Q.EXISTS_TAC ‘r2’ >> simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP]) \\
     DISCH_TAC \\
     Know ‘m2 <= d_max’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
         reverse CONJ_TAC >- rw [Abbr ‘d_max’] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j2) q’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC subterm_width_inclusive \\
             Q.EXISTS_TAC ‘p’ >> simp []) \\
         qunabbrevl_tac [‘m2’, ‘N0’] \\
        ‘N = subterm' X (M j2) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_width_last >> simp []) >> DISCH_TAC \\
     Know ‘solvable (subterm' X (H j2) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
         qexistsl_tac [‘X’, ‘r2’, ‘d_max’, ‘y’, ‘k’] \\
         simp [subterm_width_nil, principal_hnf_tpm'] \\
         POP_ASSUM MP_TAC >> rw [Abbr ‘m2’] \\
         Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         Suff ‘RANK r SUBSET RANK r2’ >- SET_TAC [] \\
         rw [Abbr ‘r2’, RANK_MONO]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j2 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     simp [head_equivalent_def])
 (* stage work *)
 >> reverse (Cases_on ‘solvable (subterm' X (M j2) q r)’)
 >- (Know ‘unsolvable (subterm' X (M j2) q r) <=>
           ltree_el (BT' X (M j2) r) q = SOME bot’
     >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
     simp [] >> DISCH_THEN K_TAC \\
     reverse (Cases_on ‘solvable (subterm' X (M j1) q r)’)
     >- (Know ‘unsolvable (subterm' X (M j1) q r) <=>
               ltree_el (BT' X (M j1) r) q = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         simp []) \\
     Know ‘unsolvable (subterm' X (H j2) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC unsolvable_ISUB \\
         simp [solvable_tpm]) >> DISCH_TAC \\
     Know ‘unsolvable (subterm' X (H j2) q r) <=>
           ltree_el (BT' X (H j2) r) q = SOME bot’
     >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []) \\
     simp [] >> DISCH_THEN K_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     qabbrev_tac ‘r1 = r + LENGTH q’ \\
     rename1 ‘subterm X (M j1) q r = SOME (N,r1)’ \\
     qabbrev_tac ‘N0 = principal_hnf N’ \\
     qabbrev_tac ‘m1 = hnf_children_size N0’ \\
     rename1 ‘ltree_el (BT' X (M j1) r) q = SOME (SOME (vs1,y1),SOME m1)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs1,y1)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r1’      K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m1’ K_TAC \\
     qabbrev_tac ‘n1 = LAMl_size N0’ \\
  (* decompose N *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n1 X = vs1’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs1 :string list”, “r1 :num”, “n1 :num”)) ‘X’ \\
     qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vs1)’ \\
     Q_TAC (HNF_TAC (“N0 :term”, “vs1 :string list”,
                     “y1' :string”, “Ns1 :term list”)) ‘N1’ \\
    ‘TAKE (LAMl_size N0) vs1 = vs1’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘subterm X (H j1) q r <> NONE’ by ASM_SIMP_TAC std_ss [] \\
     Know ‘IMAGE y (count k) SUBSET X UNION RANK r1’
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
             rw [RANK_MONO, Abbr ‘r1’]) \\
         rw [SUBSET_DEF] >> rename1 ‘i < k’ \\
         Know ‘y i IN Z’ >- rw [] \\
         Suff ‘Z SUBSET X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         FIRST_X_ASSUM ACCEPT_TAC) >> DISCH_TAC \\
     Know ‘set vs SUBSET X UNION RANK r1’
     >- (Suff ‘set vs SUBSET RANK r1’ >- SET_TAC [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> art [] \\
         simp [Abbr ‘r1’, RANK_MONO]) >> DISCH_TAC \\
     Know ‘set ys SUBSET X UNION RANK r1’
     >- (Suff ‘set ys SUBSET RANK r1’ >- SET_TAC [] \\
         qunabbrev_tac ‘ys’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r1’] \\
         rw [LENGTH_NON_NIL]) >> DISCH_TAC \\
     Know ‘FV (tpm (REVERSE pm) N) SUBSET X UNION RANK r1’
     >- (MATCH_MP_TAC FV_tpm_lemma \\
         Q.EXISTS_TAC ‘r1’ >> simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP]) \\
     DISCH_TAC \\
     Know ‘m1 <= d_max’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
         reverse CONJ_TAC >- rw [Abbr ‘d_max’] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j1) q’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC subterm_width_inclusive \\
             Q.EXISTS_TAC ‘p’ >> simp []) \\
         qunabbrevl_tac [‘m1’, ‘N0’] \\
        ‘N = subterm' X (M j1) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_width_last >> simp []) >> DISCH_TAC \\
     Know ‘solvable (subterm' X (H j1) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
         qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
         simp [subterm_width_nil, principal_hnf_tpm'] \\
         POP_ASSUM MP_TAC >> rw [Abbr ‘m1’] \\
         Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
         rw [Abbr ‘r1’, RANK_MONO]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j1 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     simp [head_equivalent_def])
 (* stage work, now “subterm' X (M j1) p r)” and “subterm' X (M j2) p r)”
    are both solvable.
  *)
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> qabbrev_tac ‘r1 = r + LENGTH q’
 >> rename1 ‘subterm X (M j1) q r = SOME (N,r1)’
 >> qabbrev_tac ‘N0 = principal_hnf N’
 >> qabbrev_tac ‘m1 = hnf_children_size N0’
 >> rename1 ‘ltree_el (BT' X (M j1) r) q = SOME (SOME (vs1,y1),SOME m1)’
 >> Q.PAT_X_ASSUM ‘_ = SOME (vs1,y1)’ K_TAC >> gs []
 >> Q.PAT_X_ASSUM ‘_ = r1’            K_TAC
 >> Q.PAT_X_ASSUM ‘_ = SOME m1’       K_TAC
 >> qabbrev_tac ‘n1 = LAMl_size N0’
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j2 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> rename1 ‘subterm X (M j2) q r = SOME (N',r1)’
 >> qabbrev_tac ‘N0' = principal_hnf N'’
 >> qabbrev_tac ‘m2 = hnf_children_size N0'’
 >> rename1 ‘ltree_el (BT' X (M j2) r) q = SOME (SOME (vs2,y2),SOME m2)’
 >> Q.PAT_X_ASSUM ‘_ = SOME (vs2,y2)’ K_TAC >> gs []
 >> Q.PAT_X_ASSUM ‘_ = r1’            K_TAC
 >> Q.PAT_X_ASSUM ‘_ = SOME m2’       K_TAC
 >> qabbrev_tac ‘n2 = LAMl_size N0'’
 >> simp [head_equivalent_def]
 (* decompose N *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n1 X = vs1’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs1 :string list”, “r1 :num”, “n1 :num”)) ‘X’
 >> qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vs1)’
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs1 :string list”,
                    “y1' :string”, “Ns1 :term list”)) ‘N1’
 >> ‘TAKE (LAMl_size N0) vs1 = vs1’ by rw []
 >>  POP_ASSUM (rfs o wrap) >> T_TAC
 >> ‘LENGTH Ns1 = m1 /\ hnf_headvar N1 = y1' /\ hnf_children N1 = Ns1’
       by rw [Abbr ‘m1’]
 >> Q.PAT_X_ASSUM ‘N0 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘N1 = _’ (ASSUME_TAC o SYM)
  (* decompose N' *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n2 X = vs2’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs2 :string list”, “r1 :num”, “n2 :num”)) ‘X’
 >> qabbrev_tac ‘N1' = principal_hnf (N0' @* MAP VAR vs2)’
 >> Q_TAC (HNF_TAC (“N0' :term”, “vs2 :string list”,
                    “y2' :string”, “Ns2 :term list”)) ‘N1'’
 >> ‘TAKE (LAMl_size N0') vs2 = vs2’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘LENGTH Ns2 = m2 /\ hnf_headvar N1' = y2' /\ hnf_children N1' = Ns2’
       by rw [Abbr ‘m2’]
 >> Q.PAT_X_ASSUM ‘N0' = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘N1' = _’ (ASSUME_TAC o SYM)
 >> fs []
 >> Q.PAT_X_ASSUM ‘y2' = y2’ (fs o wrap)
 >> Q.PAT_X_ASSUM ‘y1' = y1’ (fs o wrap)
 >> Know ‘subterm X (H j1) q r <> NONE /\
          subterm X (H j2) q r <> NONE’
 >- ASM_SIMP_TAC std_ss []
 >> STRIP_TAC
 >> Know ‘IMAGE y (count k) SUBSET X UNION RANK r1’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ \\
     reverse CONJ_TAC
     >- (Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
         rw [RANK_MONO, Abbr ‘r1’]) \\
     rw [SUBSET_DEF] >> rename1 ‘i < k’ \\
     Know ‘y i IN Z’ >- rw [] \\
     Suff ‘Z SUBSET X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
     FIRST_X_ASSUM ACCEPT_TAC)
 >> DISCH_TAC
 >> Know ‘set vs SUBSET X UNION RANK r1’
 >- (Suff ‘set vs SUBSET RANK r1’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> art [] \\
     simp [Abbr ‘r1’, RANK_MONO])
 >> DISCH_TAC
 >> Know ‘set ys SUBSET X UNION RANK r1’
 >- (Suff ‘set ys SUBSET RANK r1’ >- SET_TAC [] \\
     qunabbrev_tac ‘ys’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r1’] \\
     rw [LENGTH_NON_NIL])
 >> DISCH_TAC
 >> Know ‘FV (tpm (REVERSE pm) N)  SUBSET X UNION RANK r1 /\
          FV (tpm (REVERSE pm) N') SUBSET X UNION RANK r1’
 >- (CONJ_TAC \\
     MATCH_MP_TAC FV_tpm_lemma \\
     Q.EXISTS_TAC ‘r1’ >> simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP])
 >> STRIP_TAC
 >> Know ‘m1 <= d’ (* m1 = hnf_children_size N0 *)
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j1) q’ \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC subterm_width_inclusive \\
         Q.EXISTS_TAC ‘p’ >> simp []) \\
     simp [Abbr ‘m1’, Abbr ‘N0’] \\
    ‘N = subterm' X (M j1) q r’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC subterm_width_last >> simp [])
 >> DISCH_TAC
 >> Know ‘m1 <= d_max’ (* m1 = hnf_children_size N0 *)
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
     rw [Abbr ‘d_max’])
 >> DISCH_TAC
 >> Know ‘m2 <= d’ (* m2 = hnf_children_size N0' *)
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j2) q’ \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC subterm_width_inclusive \\
         Q.EXISTS_TAC ‘p’ >> simp []) \\
     qunabbrevl_tac [‘m2’, ‘N0'’] \\
    ‘N' = subterm' X (M j2) q r’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC subterm_width_last >> simp [])
 >> DISCH_TAC
 >> Know ‘m2 <= d_max’ (* m2 = hnf_children_size N0' *)
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
     rw [Abbr ‘d_max’])
 >> DISCH_TAC
 >> Know ‘solvable (subterm' X (H j1) q r) /\
          solvable (subterm' X (H j2) q r)’
 >- (ASM_SIMP_TAC std_ss [] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
       qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
       simp [subterm_width_nil, principal_hnf_tpm'] \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘m1’] \\
       Q.PAT_X_ASSUM ‘IMAGE y (count k) SUBSET X UNION RANK r1’ MP_TAC \\
       rw [SUBSET_DEF] \\
       POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘i’ >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
       qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
       simp [subterm_width_nil, principal_hnf_tpm'] \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘m1’] \\
       Q.PAT_X_ASSUM ‘IMAGE y (count k) SUBSET X UNION RANK r1’ MP_TAC \\
       rw [SUBSET_DEF] \\
       POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘i’ >> art [] ])
 >> STRIP_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j1 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> rename1 ‘subterm X (H j1) q r = SOME (W,r1)’
 >> qabbrev_tac ‘W0 = principal_hnf W’
 >> qabbrev_tac ‘m3 = hnf_children_size W0’
 >> rename1 ‘ltree_el (BT' X (H j1) r) q = SOME (SOME (vs3,y3),SOME m3)’
 >> Q.PAT_X_ASSUM ‘_ = SOME (vs3,y3)’ K_TAC
 >> Q.PAT_X_ASSUM ‘_ = SOME m3’       K_TAC
 >> qabbrev_tac ‘n3 = LAMl_size W0’
 >> Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j2 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> rename1 ‘subterm X (H j2) q r = SOME (W',r1)’
 >> qabbrev_tac ‘W0' = principal_hnf W'’
 >> qabbrev_tac ‘m4 = hnf_children_size W0'’
 >> rename1 ‘ltree_el (BT' X (H j2) r) q = SOME (SOME (vs4,y4),SOME m4)’
 >> Q.PAT_X_ASSUM ‘_ = SOME (vs4,y4)’ K_TAC
 >> Q.PAT_X_ASSUM ‘_ = SOME m4’       K_TAC
 >> qabbrev_tac ‘n4 = LAMl_size W0'’
 >> Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC
 (* decompose W *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n3 X = vs3’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs3 :string list”, “r1 :num”, “n3 :num”)) ‘X’
 >> qabbrev_tac ‘W1 = principal_hnf (W0 @* MAP VAR vs3)’
 >> Q_TAC (HNF_TAC (“W0 :term”, “vs3 :string list”,
                    “y3' :string”, “Ns3 :term list”)) ‘W1’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs3) (FV W0)’ K_TAC
  (* decompose W' *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n4 X = vs4’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs4 :string list”, “r1 :num”, “n4 :num”)) ‘X’
 >> qabbrev_tac ‘W1' = principal_hnf (W0' @* MAP VAR vs4)’
 >> Q_TAC (HNF_TAC (“W0' :term”, “vs4 :string list”,
                    “y4' :string”, “Ns4 :term list”)) ‘W1'’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs4) (FV W0')’ K_TAC
  (* decompose W and W' (ending part) *)
 >> Know ‘TAKE (LAMl_size W0) vs3 = vs3 /\ TAKE (LAMl_size W0') vs4 = vs4’
 >- simp []
 >> DISCH_THEN (rfs o CONJUNCTS)
 >> Q.PAT_X_ASSUM ‘hnf_headvar (principal_hnf (W0 @* MAP VAR vs3)) = y3’ MP_TAC
 >> simp [] (* y3' = y3 *)
 >> DISCH_THEN (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘hnf_headvar (principal_hnf (W0' @* MAP VAR vs4)) = y4’ MP_TAC
 >> simp [] (* y4' = y4 *)
 >> DISCH_THEN (rfs o wrap)
 (* properties of W0 *)
 >> ‘LAMl_size W0 = n3 /\ hnf_children_size W0 = m3 /\
     hnf_headvar W1 = y3’ by rw []
 >> Q.PAT_X_ASSUM ‘W0 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘W1 = _’ (ASSUME_TAC o SYM)
 (* properties of W0' *)
 >> ‘LAMl_size W0' = n4 /\ hnf_children_size W0' = m4 /\
     hnf_headvar W1' = y4’ by rw []
 >> Q.PAT_X_ASSUM ‘W0' = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘W1' = _’ (ASSUME_TAC o SYM)
 >> simp [head_equivalent_def]
 (* final shape of the goal:
    y1 <> y2 \/ m2 + n1 <> m1 + n2 ==> y3 <> y4 \/ m4 + n3 <> m3 + n4
  *)
 >> Know ‘W = tpm (REVERSE pm) N ISUB ss’
 >- (Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’
       (MP_TAC o Q.SPEC ‘j1’) >> simp [])
 >> DISCH_TAC
 >> Know ‘W' = tpm (REVERSE pm) N' ISUB ss’
 >- (Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’
       (MP_TAC o Q.SPEC ‘j2’) >> simp [])
 >> DISCH_TAC
 (* applying hreduce_ISUB and tpm_hreduces *)
 >> ‘N -h->* N0 /\ N' -h->* N0'’ by METIS_TAC [principal_hnf_thm']
 >> Know ‘W  -h->* tpm (REVERSE pm) N0  ISUB ss /\
          W' -h->* tpm (REVERSE pm) N0' ISUB ss’
 >- simp [hreduce_ISUB, tpm_hreduces]
 >> Q.PAT_ASSUM ‘LAMl vs1 _ = N0’  (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_ASSUM ‘LAMl vs2 _ = N0'’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_ASSUM ‘_ = N1’  (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_ASSUM ‘_ = N1'’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘W  = tpm (REVERSE pm) N  ISUB ss’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘W' = tpm (REVERSE pm) N' ISUB ss’ (ASSUME_TAC o SYM)
 >> simp [tpm_LAMl, tpm_appstar]
 >> qabbrev_tac ‘y1'  = lswapstr (REVERSE pm) y1’
 >> qabbrev_tac ‘y2'  = lswapstr (REVERSE pm) y2’
 >> qabbrev_tac ‘Ns1' = listpm term_pmact (REVERSE pm) Ns1’
 >> qabbrev_tac ‘Ns2' = listpm term_pmact (REVERSE pm) Ns2’
 >> Know ‘listpm string_pmact (REVERSE pm) vs1 = vs1’
 >- (simp [Once LIST_EQ_REWRITE] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC lswapstr_unchanged' \\
     simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       POP_ASSUM MP_TAC \\
       Suff ‘DISJOINT (set vs1) (set vs)’
       >- (rw [DISJOINT_ALT] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       MATCH_MP_TAC DISJOINT_SUBSET \\
       Q.EXISTS_TAC ‘set vs0’ >> art [] \\
       qunabbrevl_tac [‘vs1’, ‘vs0’] \\
       MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’],
       (* goal 2 (of 2) *)
       POP_ASSUM MP_TAC \\
       Suff ‘DISJOINT (set vs1) (set ys)’
       >- (rw [DISJOINT_ALT] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       qunabbrevl_tac [‘vs1’, ‘ys’] \\
       MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’] ])
 >> Rewr'
 >> Know ‘listpm string_pmact (REVERSE pm) vs2 = vs2’
 >- (simp [Once LIST_EQ_REWRITE] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC lswapstr_unchanged' \\
     simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       POP_ASSUM MP_TAC \\
       Suff ‘DISJOINT (set vs2) (set vs)’
       >- (rw [DISJOINT_ALT] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       MATCH_MP_TAC DISJOINT_SUBSET \\
       Q.EXISTS_TAC ‘set vs0’ >> art [] \\
       qunabbrevl_tac [‘vs2’, ‘vs0’] \\
       MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’],
       (* goal 2 (of 2) *)
       POP_ASSUM MP_TAC \\
       Suff ‘DISJOINT (set vs2) (set ys)’
       >- (rw [DISJOINT_ALT] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       qunabbrevl_tac [‘vs2’, ‘ys’] \\
       MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’] ])
 >> Rewr'
 >> Know ‘DISJOINT (set vs1) (DOM ss)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X UNION RANK r’ \\
     reverse CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> simp [] \\
         rw [SUBSET_DEF] >> simp []) \\
     simp [DISJOINT_UNION', Abbr ‘vs1’] \\
     MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [Abbr ‘r1’])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs2) (DOM ss)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X UNION RANK r’ \\
     reverse CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> simp [] \\
         rw [SUBSET_DEF] >> simp []) \\
     simp [DISJOINT_UNION', Abbr ‘vs2’] \\
     MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [Abbr ‘r1’])
 >> DISCH_TAC
 >> simp [LAMl_ISUB, appstar_ISUB]
 >> qabbrev_tac ‘Ns1'' = MAP (\t. t ISUB ss) Ns1'’
 >> qabbrev_tac ‘Ns2'' = MAP (\t. t ISUB ss) Ns2'’
 >> ‘LENGTH Ns1'' = m1 /\ LENGTH Ns2'' = m2’
      by simp [Abbr ‘Ns1''’, Abbr ‘Ns2''’, Abbr ‘Ns1'’, Abbr ‘Ns2'’]
 (* stage work (before final case analysis)

    N  -h->* LAMl vs1 (VAR y1 @* Ns1) (= N0)
    N' -h->* LAMl vs2 (VAR y2 @* Ns2) (= N0')
   --------------------------------------------
    W  -h->* LAMl vs3 (VAR y3 @* Ns3) (= W0)
    W  -h->* LAMl vs1 ((VAR y1' ISUB ss) @* Ns1'')
   --------------------------------------------
    W' -h->* LAMl vs4 (VAR y4 @* Ns4) (= W0')
    W' -h->* LAMl vs2 ((VAR y2' ISUB ss) @* Ns2'')

    Now, to understand the (alternative) principal_hnf of W and W', we need to
    rewrite ‘VAR y1' ISUB ss’ to either VAR y1' or P, resp., depending on if
   ‘y1' IN DOM ss’ or not (and also on ‘y2' IN DOM ss’ or not).
  *)
 >> Cases_on ‘y1' NOTIN DOM ss’ >> Cases_on ‘y2' NOTIN DOM ss’
 (* Case 1 (of 4): easy

    W  -h->* LAMl vs3 (VAR y3  @* Ns3) (= W0)
    W  -h->* LAMl vs1 (VAR y1' @* Ns1''), thus y3 = y1'
   --------------------------------------------
    W' -h->* LAMl vs4 (VAR y4  @* Ns4) (= W0')
    W' -h->* LAMl vs2 (VAR y2' @* Ns2''), thus y4 = y2'

    Abbrev (y1' = lswapstr (REVERSE pm) y1)
    Abbrev (y2' = lswapstr (REVERSE pm) y2)
  *)
 >- (simp [ISUB_VAR_FRESH'] >> STRIP_TAC \\
    ‘hnf (LAMl vs1 (VAR y1' @* Ns1'')) /\
     hnf (LAMl vs2 (VAR y2' @* Ns2''))’ by rw [hnf_appstar] \\
    ‘LAMl vs1 (VAR y1' @* Ns1'') = W0 /\
     LAMl vs2 (VAR y2' @* Ns2'') = W0'’ by METIS_TAC [principal_hnf_thm'] \\
    ‘LAMl_size W0 = n1 /\ LAMl_size W0' = n2’ by rw [LAMl_size_hnf] \\
    ‘n3 = n1 /\ n4 = n2’ by PROVE_TAC [] \\
     Know ‘y3 = y1' /\ y4 = y2' /\ Ns1'' = Ns3 /\ Ns2'' = Ns4’
     >- (Q.PAT_X_ASSUM ‘LAMl vs3 _ = W0’ MP_TAC \\
         Q.PAT_X_ASSUM ‘_ = W1’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘LAMl vs4 _ = W0'’ MP_TAC \\
         Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         fs []) >> STRIP_TAC \\
     simp [] \\
     qunabbrevl_tac [‘m3’, ‘m4’] \\
     Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
     simp [Abbr ‘y1'’, Abbr ‘y2'’])
 (* Case 2 (of 4): hard, we try to directly prove ‘y1' <> y4’

    N  -h->* LAMl vs1  (VAR y1  @* Ns1) (= N0)
    N' -h->* LAMl vs2  (VAR y2  @* Ns2) (= N0')
   --------------------------------------------
    W  -h->* LAMl vs3  (VAR y3  @* Ns3) (= W0)
           = LAMl vs1  (VAR y1' @* Ns1''), thus y1' = y3
   --------------------------------------------
    W' -h->* LAMl vs4  (VAR y4  @* Ns4) (= W0') --+
    W' -h->* LAMl vs2  (P       @* Ns2'')         |=
       -h->* LAMl zs2' (VAR h   @* Ns2x) ---------+

    Abbrev (y1' = lswapstr (REVERSE pm) y1)

    main goal: y1' <> y4 (y2 seems irrelevant now, same is ‘y1 <> y2’)

    Structure of W0:

    LAMl |<--------- vs3 --------->| VAR y3/y1'

    d_max = d + n_max, where d >= m2 /\ n_max >= n3, thus n3 < n4 /\ vs3 <<= vs4

    Structure of W0':

    LAMl |<---(vs2)--- vs4 ------------>| VAR y4 (= LAST vs4)
    LAMl |<----------- zs2' ----------->| VAR h
    LAMl |<----vs2----->|<----zs2---->|h| VAR h
        n4 =   n2      +  d_max - m2  +1
  *)
 >- (PRINT_TAC "stage work on subtree_equiv_lemma" \\
     POP_ASSUM MP_TAC >> simp [ISUB_VAR_FRESH'] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC) \\
    ‘(LEAST j. y j = y2') = f j3’ by rw [] >> POP_ORW \\
     ONCE_REWRITE_TAC [TAUT ‘p /\ q ==> r <=> p ==> q ==> r’] >> STRIP_TAC \\
    ‘hnf (LAMl vs1 (VAR y1' @* Ns1''))’ by rw [hnf_appstar] \\
    ‘LAMl vs1 (VAR y1' @* Ns1'') = W0’ by METIS_TAC [principal_hnf_thm'] \\
    ‘LAMl_size W0 = n1’ by rw [LAMl_size_hnf] \\
    ‘n3 = n1’ by PROVE_TAC [] \\
     Know ‘y3 = y1' /\ Ns1'' = Ns3’
     >- (Q.PAT_X_ASSUM ‘LAMl vs3 _ = W0’ MP_TAC \\
         Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         simp [] \\
         Q.PAT_X_ASSUM ‘_ = W1’ (REWRITE_TAC o wrap o SYM) \\
         fs []) >> STRIP_TAC \\
     simp [] \\
  (* NOTE: The proof completes if we can just show ‘y3 <> y4’. *)
     qabbrev_tac ‘X' = set vs4 UNION FV W1' UNION
                       BIGUNION (IMAGE FV (set Ns2''))’ \\
    ‘FINITE X'’ by rw [Abbr ‘X'’] \\
     qabbrev_tac ‘d' = MAX n4 (SUC (d_max' j3))’ \\
     Q_TAC (NEWS_TAC (“L :string list”, “d' :num”)) ‘X'’ \\
    ‘d_max' j3 < LENGTH L /\ n4 <= LENGTH L’ by simp [Abbr ‘d'’, MAX_LE] \\
     Know ‘DISJOINT (set L) (set vs2) /\
           DISJOINT (set L) (set vs4)’
     >- (rw [Abbr ‘L’, Abbr ‘vs2’, Abbr ‘vs4’] (* 2 subgoals, same tactics *) \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘FINITE X'’ K_TAC \\
     Q.PAT_X_ASSUM ‘DISJOINT (set L) X'’ MP_TAC \\
     qunabbrev_tac ‘X'’ \\
     DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DISJOINT_UNION']) \\
     STRIP_TAC (* W -h->* ... *) \\
    ‘m2 <= d_max' j3’ by simp [Abbr ‘d_max'’] \\
  (* applying hreduce_permutator_shared *)
     MP_TAC (Q.SPECL [‘Ns2''’, ‘d_max + f (j3 :num)’, ‘L’]
                     hreduce_permutator_shared) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘zs2’ (Q.X_CHOOSE_THEN ‘z2’ STRIP_ASSUME_TAC)) \\
     qabbrev_tac ‘P' = P (f j3)’ \\
     Q.PAT_X_ASSUM ‘P' @* Ns2'' -h->* _’ MP_TAC \\
     qabbrev_tac ‘h = LAST L’ (* the new shared head variable *) \\
     qabbrev_tac ‘L' = FRONT L’ \\
    ‘L <> []’ by rw [GSYM LENGTH_NON_NIL] \\
     Q.PAT_X_ASSUM ‘IS_SUFFIX L _’ MP_TAC \\
    ‘L = SNOC h L'’ by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
     POP_ORW \\
     simp [IS_SUFFIX] >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘h = z2’ (simp o wrap o SYM) \\
     STRIP_TAC (* P @* Ns2'' -h->* ... *) \\
     qabbrev_tac ‘xs2 = SNOC h zs2’ \\ (* suffix of L *)
     Know ‘IS_SUFFIX L xs2’
     >- (‘L = SNOC h L'’
           by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
         POP_ORW \\
         simp [IS_SUFFIX, Abbr ‘xs2’]) >> DISCH_TAC \\
    ‘ALL_DISTINCT xs2’ by PROVE_TAC [IS_SUFFIX_ALL_DISTINCT] \\
     Know ‘LAMl vs2 (P' @* Ns2'') -h->*
           LAMl vs2 (LAMl zs2 (LAM h (VAR h @* Ns2'' @* MAP VAR zs2)))’
     >- simp [hreduce_LAMl] \\
     Q.PAT_X_ASSUM ‘P' @* Ns2'' -h->* _’ K_TAC \\
     REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND] \\
     qabbrev_tac ‘Ns2x = Ns2'' ++ MAP VAR zs2’ \\
     REWRITE_TAC [GSYM LAMl_SNOC] \\
     qabbrev_tac ‘zs2' = SNOC h (vs2 ++ zs2)’ \\
     STRIP_TAC \\
     Know ‘W' -h->* LAMl zs2' (VAR h @* Ns2x)’
     >- PROVE_TAC [hreduce_TRANS] \\
     POP_ASSUM K_TAC >> STRIP_TAC \\
     Know ‘LAMl zs2' (VAR h @* Ns2x) = W0'’
     >- (‘hnf (LAMl zs2' (VAR h @* Ns2x))’ by rw [hnf_appstar] \\
         METIS_TAC [principal_hnf_thm']) >> DISCH_TAC \\
     Know ‘LENGTH zs2' = n4’
     >- (Q.PAT_X_ASSUM ‘_ = n4’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> DISCH_TAC \\
     Know ‘SUC (d_max' j3) + n2 - m2 = n4’
     >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘zs2'’]) >> DISCH_TAC \\
     Know ‘vs2 <<= vs4’
     >- (qunabbrevl_tac [‘vs2’, ‘vs4’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
    ‘n2' = n2’ by rw [] \\
     Q.PAT_X_ASSUM ‘n2' <= n4’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs2 = TAKE n2' vs4’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘zs2' = vs2 ++ xs2’ by simp [Abbr ‘zs2'’, Abbr ‘xs2’] \\
     qabbrev_tac ‘ys2 = DROP n2 vs4’ \\
    ‘ALL_DISTINCT ys2’ by simp [Abbr ‘ys2’, ALL_DISTINCT_DROP] \\
  (* Structure of W0:

     LAMl |<--------- vs3 --------->| VAR y3/y1'

     W -h->* LAMl vs3  (VAR y3  @* Ns3) (= W0)
           = LAMl vs1  (VAR y1' @* Ns1''), thus y1' = y3

           m3 = m1, n3 = n1

     Structure of W0':

     LAMl |<---(vs2)--- vs4 ---(ys2)---->| VAR y4 (= LAST vs4)
   --------------------------------------------------------------
          |<----------- zs2' ----------->|
     LAMl |<----vs2----->|<--- zs2 --->|h| VAR h @* Ns2x = Ns2'' ++ zs2
                         |<---- xs2 ---->|
             n4 = n2 + d_max' - m2 + 1
             m4 = LENGTH Ns2x = LENGTH Ns2'' + LENGTH zs2
                = m2 + d_max - m2 = d_max'

      (m1 + n1 =) d_max + n1 = m1 + n2 + d_max - m2 + 1 (= m3 + n4)
                          n1 = m1 + n2 - m2 + 1
                     m2 + n1 = m1 + n2 + 1 <=/=> m2 + n1 = m1 + n2
   *)
     Know ‘DISJOINT (set xs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys2’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs2 = LENGTH ys2’ by simp [Abbr ‘xs2’, Abbr ‘ys2’] \\
     Know ‘LAMl vs4 (VAR y4 @* Ns4) = LAMl zs2' (VAR h @* Ns2x)’
     >- rw [] \\
    ‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘zs2' = _’ (ONCE_REWRITE_TAC o wrap) \\
     simp [LAMl_APPEND] \\
     qabbrev_tac ‘t = VAR h @* Ns2x’ \\
  (* applying LAMl_ALPHA_ssub *)
     qabbrev_tac ‘pm2 = fromPairs xs2 (MAP VAR ys2)’ \\
  (* NOTE: The following disjointness hold for names from different rows *)
     Know ‘DISJOINT (set vs) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ >> simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ >> simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘LAMl xs2 t = LAMl ys2 (pm2 ' t)’
     >- (simp [Abbr ‘pm2’, fromPairs_def] \\
         MATCH_MP_TAC LAMl_ALPHA_ssub >> art [] \\
      (* goal: DISJOINT (set ys2) (set xs2 UNION FV t) *)
         simp [DISJOINT_UNION'] \\
         CONJ_TAC >- rw [Once DISJOINT_SYM] \\
         simp [Abbr ‘t’, Abbr ‘Ns2x’, appstar_APPEND, FV_appstar_MAP_VAR] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set xs2’ >> art [] \\
             simp [Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
             SET_TAC []) \\
         simp [FV_appstar] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs2) (set ys2)’ MP_TAC \\
             rw [Abbr ‘xs2’, LIST_TO_SET_SNOC, DISJOINT_ALT]) \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m2’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns2''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘FV (EL i Ns2')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns2'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns2'’]) \\
         simp [Abbr ‘Ns2'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] \\
      (* applying FV_tpm_disjoint *)
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys2) (FV (EL i Ns2)) *)
         Know ‘FV N0' SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N'’ >> art [] \\
             qunabbrev_tac ‘N0'’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns2) SUBSET FV N' UNION set vs2’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0'’, ‘n2’, ‘m2’, ‘N1'’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N' UNION set vs2’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs4’ MP_TAC \\
            ‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM]) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs4’ \\
         reverse CONJ_TAC
         >- (‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs4’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> Rewr' \\
    ‘FDOM pm2 = set xs2’ by simp [Abbr ‘pm2’, FDOM_fromPairs] \\
    ‘MEM h xs2’ by simp [Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
     simp [Abbr ‘t’, ssub_appstar] \\
     Know ‘pm2 ' h = VAR (LAST ys2)’
     >- (‘h = LAST xs2’ by rw [Abbr ‘xs2’, LAST_SNOC] >> POP_ORW \\
         ‘xs2 <> []’ by simp [Abbr ‘xs2’] \\
         ‘ys2 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         simp [Abbr ‘pm2’, LAST_EL] \\
         qabbrev_tac ‘j4 = PRE (LENGTH ys2)’ \\
        ‘0 < LENGTH ys2’ by rw [LENGTH_NON_NIL] \\
        ‘j4 < LENGTH ys2’ by rw [Abbr ‘j4’] \\
        ‘VAR (EL j4 ys2) = EL j4 (MAP VAR ys2)’ by simp [EL_MAP] >> POP_ORW \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘_ = W1'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     Know ‘LAST ys2 = LAST vs4’
     >- (‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
         ‘xs2 <> []’ by simp [Abbr ‘xs2’] \\
         ‘ys2 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         rw [LAST_APPEND_NOT_NIL]) >> Rewr' \\
     STRIP_TAC (* y4 = LAST vs4, etc. *) \\
  (* W -h->* LAMl vs3  (VAR y3 @* Ns3) = LAMl vs1 (VAR y1' @* Ns1'')

     Now we show that n1/n3 is strictly smaller than n4. This is only possible
     after using ‘subterm_length’ when constructing the permutator ‘P’:

      LENGTH zs2 = d_max - m2             (assumption)
      d_max = d + n_max >= m2 + n1        (worst case: d = m2)
   => LENGTH zs2 >= m2 + n1 - m2 = n1     (worst case: LENGTH zs2 = n1)
   => n4 = n2 + LENGTH zs2 + 1 > n1       (worst case: n2 = 0 and n4 = n1 + 1)

     Then, y3 is at most another variable in ROW r1. While y4 is LAST v4, thus
     cannot be the same with y3 since ‘ALL_DISTINCT vs4’.
   *)
     Know ‘n1 <= n_max’ (* n1 = LAMl_size N0 *)
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_length (M j1) q’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC subterm_length_inclusive \\
             Q.EXISTS_TAC ‘p’ >> simp []) \\
         qunabbrevl_tac [‘n1’, ‘N0’] \\
        ‘N = subterm' X (M j1) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_length_last >> simp []) >> DISCH_TAC \\
     Know ‘n1 < n4’
     >- (Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘n_max’ >> art [] \\
         Q.PAT_X_ASSUM ‘SUC (d_max' j3) + n2 - m2 = n4’
           (REWRITE_TAC o wrap o SYM) \\
         Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘d_max' j3 + n2 - m2’ \\
         simp [Abbr ‘d_max’, Abbr ‘d_max'’]) >> DISCH_TAC \\
  (* applying subterm_headvar_lemma' on W *)
     Know ‘hnf_headvar W1 IN FV W UNION set vs3’
     >- (MATCH_MP_TAC subterm_headvar_lemma' \\
         qexistsl_tac [‘X’, ‘r1’, ‘W0’, ‘n3’] >> simp []) \\
     Know ‘hnf_headvar W1 = y3’
     >- (Q.PAT_X_ASSUM ‘_ = W1’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> Rewr' >> art [] (* y3 -> y1' *) \\
     DISCH_TAC \\
  (* NOTE: FV W SUBSET X UNION RANK r1 *)
     qabbrev_tac ‘X' = X UNION RANK r1’ \\
     Know ‘y1' IN X' UNION set vs3’
     >- (Q.PAT_X_ASSUM ‘y1' IN _’ MP_TAC \\
         Q.PAT_X_ASSUM ‘FV W SUBSET _’ MP_TAC \\
         SET_TAC []) \\
     Q.PAT_X_ASSUM ‘y1' IN _’ K_TAC >> DISCH_TAC \\
     qunabbrev_tac ‘X'’ \\
    ‘0 < n4 /\ vs4 <> []’ by simp [GSYM LENGTH_NON_NIL] \\
     simp [LAST_EL] \\
     Q.PAT_X_ASSUM ‘y1' IN _’ MP_TAC >> simp [IN_UNION] \\
     STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3): y1' IN X *)
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE []) \\
       Know ‘MEM y1' vs4’
       >- (POP_ORW >> simp [EL_MEM]) >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘DISJOINT (set vs4) X’ MP_TAC \\
       simp [DISJOINT_ALT'] \\
       Q.EXISTS_TAC ‘y1'’ >> art [],
       (* goal 2 (of 3): y1' IN RANK r1 *)
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE []) \\
       Know ‘MEM y1' vs4’
       >- (POP_ORW >> simp [EL_MEM]) >> DISCH_TAC \\
       Know ‘DISJOINT (set vs4) (RANK r1)’
       >- simp [Abbr ‘vs4’, DISJOINT_RNEWS_RANK'] \\
       simp [DISJOINT_ALT] \\
       Q.EXISTS_TAC ‘y1'’ >> art [],
       (* goal 3 (of 3): MEM y1' vs3 *)
       Know ‘vs3 <<= vs4’
       >- (qunabbrevl_tac [‘vs3’, ‘vs4’] \\
           MATCH_MP_TAC RNEWS_prefix >> simp []) \\
       simp [IS_PREFIX_APPEND] \\
       DISCH_THEN (Q.X_CHOOSE_THEN ‘ls’ STRIP_ASSUME_TAC) \\
       Know ‘LENGTH ls = n4 - n1’
       >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
           simp []) >> DISCH_TAC \\
      ‘ls <> []’ by simp [GSYM LENGTH_NON_NIL] \\
       Know ‘EL (PRE n4) vs4 = LAST ls’
       >- (Q.PAT_X_ASSUM ‘vs4 = vs3 ++ ls’ (REWRITE_TAC o wrap) \\
           simp [EL_APPEND2, LAST_EL, PRE_SUB]) >> Rewr' \\
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE []) \\
       Know ‘MEM y1' ls’
       >- (POP_ORW >> simp [MEM_LAST_NOT_NIL]) >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘ALL_DISTINCT vs4’ MP_TAC \\
       Q.PAT_X_ASSUM ‘vs4 = vs3 ++ ls’ (REWRITE_TAC o wrap) \\
       simp [ALL_DISTINCT_APPEND] \\
       DISJ2_TAC >> Q.EXISTS_TAC ‘y1'’ >> art [] ])
 (* Case 3 (of 4): (almost) symmetric with previous Case 2 *)
 >- (PRINT_TAC "stage work on subtree_equiv_lemma" \\
     Q.PAT_X_ASSUM ‘~(y1' NOTIN DOM ss)’ MP_TAC >> simp [ISUB_VAR_FRESH'] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC) \\
    ‘(LEAST j. y j = y1') = f j3’ by rw [] >> POP_ORW \\
     ONCE_REWRITE_TAC [TAUT ‘p /\ q ==> r <=> q ==> p ==> r’] >> STRIP_TAC \\
    ‘hnf (LAMl vs2 (VAR y2' @* Ns2''))’ by rw [hnf_appstar] \\
    ‘LAMl vs2 (VAR y2' @* Ns2'') = W0'’ by METIS_TAC [principal_hnf_thm'] \\
    ‘LAMl_size W0' = n2’ by rw [LAMl_size_hnf] \\
    ‘n4 = n2’ by PROVE_TAC [] \\
     Know ‘y4 = y2' /\ Ns2'' = Ns4’
     >- (Q.PAT_X_ASSUM ‘LAMl vs4 _ = W0'’ MP_TAC \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) >> simp [] \\
         Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) >> fs []) \\
     STRIP_TAC >> simp [] \\
  (* NOTE: The proof completes if we can just show ‘y3 <> y4’. *)
     qabbrev_tac ‘X' = set vs3 UNION FV W1 UNION
                       BIGUNION (IMAGE FV (set Ns1''))’ \\
    ‘FINITE X'’ by rw [Abbr ‘X'’] \\
     qabbrev_tac ‘d' = MAX n3 (SUC (d_max' j3))’ \\
     Q_TAC (NEWS_TAC (“L :string list”, “d' :num”)) ‘X'’ \\
    ‘d_max' j3 < LENGTH L /\ n3 <= LENGTH L’ by simp [Abbr ‘d'’, MAX_LE] \\
     Know ‘DISJOINT (set L) (set vs1) /\
           DISJOINT (set L) (set vs3)’
     >- (rw [Abbr ‘L’, Abbr ‘vs1’, Abbr ‘vs3’] (* 2 subgoals, same tactics *) \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘FINITE X'’ K_TAC \\
     Q.PAT_X_ASSUM ‘DISJOINT (set L) X'’ MP_TAC \\
     qunabbrev_tac ‘X'’ \\
     DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DISJOINT_UNION']) \\
     STRIP_TAC (* W -h->* ... *) \\
    ‘m1 <= d_max' j3’ by simp [Abbr ‘d_max'’] \\
     MP_TAC (Q.SPECL [‘Ns1''’, ‘d_max + f (j3 :num)’, ‘L’]
                     hreduce_permutator_shared) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘zs1’ (Q.X_CHOOSE_THEN ‘z1’ STRIP_ASSUME_TAC)) \\
     qabbrev_tac ‘P' = P (f j3)’ \\
     Q.PAT_X_ASSUM ‘P' @* Ns1'' -h->* _’ MP_TAC \\
     qabbrev_tac ‘h = LAST L’ (* the new shared head variable *) \\
     qabbrev_tac ‘L' = FRONT L’ \\
    ‘L <> []’ by rw [GSYM LENGTH_NON_NIL] \\
     Q.PAT_X_ASSUM ‘IS_SUFFIX L _’ MP_TAC \\
    ‘L = SNOC h L'’ by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
     POP_ORW \\
     simp [IS_SUFFIX] >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘h = z1’ (simp o wrap o SYM) \\
     STRIP_TAC (* P @* Ns1'' -h->* ... *) \\
     qabbrev_tac ‘xs1 = SNOC h zs1’ \\ (* suffix of L *)
     Know ‘IS_SUFFIX L xs1’
     >- (‘L = SNOC h L'’
           by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
         POP_ORW >> simp [IS_SUFFIX, Abbr ‘xs1’]) >> DISCH_TAC \\
    ‘ALL_DISTINCT xs1’ by PROVE_TAC [IS_SUFFIX_ALL_DISTINCT] \\
     Know ‘LAMl vs1 (P' @* Ns1'') -h->*
           LAMl vs1 (LAMl zs1 (LAM h (VAR h @* Ns1'' @* MAP VAR zs1)))’
     >- simp [hreduce_LAMl] \\
     Q.PAT_X_ASSUM ‘P' @* Ns1'' -h->* _’ K_TAC \\
     REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND] \\
     qabbrev_tac ‘Ns1x = Ns1'' ++ MAP VAR zs1’ \\
     REWRITE_TAC [GSYM LAMl_SNOC] \\
     qabbrev_tac ‘zs1' = SNOC h (vs1 ++ zs1)’ >> STRIP_TAC \\
     Know ‘W -h->* LAMl zs1' (VAR h @* Ns1x)’
     >- PROVE_TAC [hreduce_TRANS] \\
     POP_ASSUM K_TAC >> STRIP_TAC \\
     Know ‘LAMl zs1' (VAR h @* Ns1x) = W0’
     >- (‘hnf (LAMl zs1' (VAR h @* Ns1x))’ by rw [hnf_appstar] \\
         METIS_TAC [principal_hnf_thm']) >> DISCH_TAC \\
     Know ‘LENGTH zs1' = n3’
     >- (Q.PAT_X_ASSUM ‘_ = n3’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> DISCH_TAC \\
  (* abandon ‘y1 <> y2 \/ m2 + n1 <> m1 + n2’ *)
     DISCH_THEN K_TAC >> DISJ1_TAC \\
     Know ‘SUC (d_max' j3) + n1 - m1 = n3’
     >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘zs1'’]) >> DISCH_TAC \\
     Know ‘vs1 <<= vs3’
     >- (qunabbrevl_tac [‘vs1’, ‘vs3’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
    ‘n1' = n1’ by rw [] \\
     Q.PAT_X_ASSUM ‘n1' <= n3’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs1 = TAKE n1' vs3’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘zs1' = vs1 ++ xs1’ by simp [Abbr ‘zs1'’, Abbr ‘xs1’] \\
     qabbrev_tac ‘ys1 = DROP n1 vs3’ \\
    ‘ALL_DISTINCT ys1’ by simp [Abbr ‘ys1’, ALL_DISTINCT_DROP] \\
  (* Structure of W0:

     LAMl |<---(vs1)--- vs3 ---(ys1)---->| VAR y3 (= LAST vs3) in ROW r1
   --------------------------------------------------------------
          |<----------- zs1' ----------->|
     LAMl |<----vs1----->|<--- zs1 --->|h| VAR h @* Ns1x = Ns1'' ++ zs1
                         |<---- xs1 ---->|

     LAMl vs3  (VAR y3 @* Ns3) = W0
     LAMl zs1' (VAR h @* Ns1x) = W0
   *)
     Know ‘DISJOINT (set xs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys1’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs1 = LENGTH ys1’ by simp [Abbr ‘xs1’, Abbr ‘ys1’] \\
     Know ‘LAMl vs3 (VAR y3 @* Ns3) = LAMl zs1' (VAR h @* Ns1x)’ >- rw [] \\
    ‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘zs1' = _’ (ONCE_REWRITE_TAC o wrap) \\
     simp [LAMl_APPEND] \\
     qabbrev_tac ‘t = VAR h @* Ns1x’ \\
  (* applying LAMl_ALPHA_ssub *)
     qabbrev_tac ‘pm1 = fromPairs xs1 (MAP VAR ys1)’ \\
  (* NOTE: The following disjointness hold for names from different rows *)
     Know ‘DISJOINT (set vs) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ >> simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ >> simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘LAMl xs1 t = LAMl ys1 (pm1 ' t)’
     >- (simp [Abbr ‘pm1’, fromPairs_def] \\
         MATCH_MP_TAC LAMl_ALPHA_ssub >> art [] \\
         simp [DISJOINT_UNION'] \\
         CONJ_TAC >- rw [Once DISJOINT_SYM] \\
         simp [Abbr ‘t’, Abbr ‘Ns1x’, appstar_APPEND, FV_appstar_MAP_VAR] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set xs1’ >> art [] \\
             simp [Abbr ‘xs1’, LIST_TO_SET_SNOC] >> SET_TAC []) \\
         simp [FV_appstar] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs1) (set ys1)’ MP_TAC \\
             rw [Abbr ‘xs1’, LIST_TO_SET_SNOC, DISJOINT_ALT]) \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m1’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns1''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘FV (EL i Ns1')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns1'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns1'’]) \\
         simp [Abbr ‘Ns1'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] \\
      (* applying FV_tpm_disjoint *)
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys1) (FV (EL i Ns1)) *)
         Know ‘FV N0 SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N’ >> art [] \\
             qunabbrev_tac ‘N0’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns1) SUBSET FV N UNION set vs1’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0’, ‘n1’, ‘m1’, ‘N1’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N UNION set vs1’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
            ‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM]) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC
         >- (‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs3’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> Rewr' \\
    ‘FDOM pm1 = set xs1’ by simp [Abbr ‘pm1’, FDOM_fromPairs] \\
    ‘MEM h xs1’ by simp [Abbr ‘xs1’, LIST_TO_SET_SNOC] \\
     simp [Abbr ‘t’, ssub_appstar] \\
     Know ‘pm1 ' h = VAR (LAST ys1)’
     >- (‘h = LAST xs1’ by rw [Abbr ‘xs1’, LAST_SNOC] >> POP_ORW \\
         ‘xs1 <> []’ by simp [Abbr ‘xs1’] \\
         ‘ys1 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         simp [Abbr ‘pm1’, LAST_EL] \\
         qabbrev_tac ‘j4 = PRE (LENGTH ys1)’ \\
        ‘0 < LENGTH ys1’ by rw [LENGTH_NON_NIL] \\
        ‘j4 < LENGTH ys1’ by rw [Abbr ‘j4’] \\
        ‘VAR (EL j4 ys1) = EL j4 (MAP VAR ys1)’ by simp [EL_MAP] >> POP_ORW \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘_ = W1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     Know ‘LAST ys1 = LAST vs3’
     >- (‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
         ‘xs1 <> []’ by simp [Abbr ‘xs1’] \\
         ‘ys1 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         rw [LAST_APPEND_NOT_NIL]) >> Rewr' \\
     STRIP_TAC (* y4 = LAST vs4, etc. *) \\
  (* stage work *)
     Know ‘n2 <= n_max’ (* n2 = LAMl_size N0' *)
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_length (M j2) q’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC subterm_length_inclusive \\
             Q.EXISTS_TAC ‘p’ >> simp []) \\
         qunabbrevl_tac [‘n2’, ‘N0'’] \\
        ‘N' = subterm' X (M j2) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_length_last >> simp []) >> DISCH_TAC \\
     Know ‘n2 < n3’
     >- (Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘n_max’ >> art [] \\
         Q.PAT_X_ASSUM ‘SUC (d_max' j3) + n1 - m1 = n3’
           (REWRITE_TAC o wrap o SYM) \\
         Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘d_max' j3 + n1 - m1’ \\
         simp [Abbr ‘d_max’, Abbr ‘d_max'’]) >> DISCH_TAC \\
  (* applying subterm_headvar_lemma' on W *)
     Know ‘hnf_headvar W1' IN FV W' UNION set vs4’
     >- (MATCH_MP_TAC subterm_headvar_lemma' \\
         qexistsl_tac [‘X’, ‘r1’, ‘W0'’, ‘n4’] >> simp []) \\
     Know ‘hnf_headvar W1' = y4’
     >- (Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> Rewr' >> art [] (* y3 -> y1' *) \\
     DISCH_TAC \\
  (* NOTE: FV W' SUBSET X UNION RANK r1 *)
     qabbrev_tac ‘X' = X UNION RANK r1’ \\
     Know ‘y2' IN X' UNION set vs4’
     >- (Q.PAT_X_ASSUM ‘y2' IN _’ MP_TAC \\
         Q.PAT_X_ASSUM ‘FV W' SUBSET _’ MP_TAC \\
         SET_TAC []) \\
     Q.PAT_X_ASSUM ‘y2' IN _’ K_TAC >> DISCH_TAC \\
     qunabbrev_tac ‘X'’ \\
    ‘0 < n3 /\ vs3 <> []’ by simp [GSYM LENGTH_NON_NIL] \\
     simp [LAST_EL] \\
     Q.PAT_X_ASSUM ‘y2' IN _’ MP_TAC >> simp [IN_UNION] \\
     STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [Once EQ_SYM_EQ]) \\
       Know ‘MEM y2' vs3’
       >- (POP_ORW >> simp [EL_MEM]) >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘DISJOINT (set vs3) X’ MP_TAC \\
       simp [DISJOINT_ALT'] >> Q.EXISTS_TAC ‘y2'’ >> art [],
       (* goal 2 (of 3) *)
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [Once EQ_SYM_EQ]) \\
       Know ‘MEM y2' vs3’
       >- (POP_ORW >> simp [EL_MEM]) >> DISCH_TAC \\
       Know ‘DISJOINT (set vs3) (RANK r1)’
       >- simp [Abbr ‘vs3’, DISJOINT_RNEWS_RANK'] \\
       simp [DISJOINT_ALT] \\
       Q.EXISTS_TAC ‘y2'’ >> art [],
       (* goal 3 (of 3) *)
       Know ‘vs4 <<= vs3’
       >- (qunabbrevl_tac [‘vs3’, ‘vs4’] \\
           MATCH_MP_TAC RNEWS_prefix >> simp []) \\
       simp [IS_PREFIX_APPEND] \\
       DISCH_THEN (Q.X_CHOOSE_THEN ‘ls’ STRIP_ASSUME_TAC) \\
       Know ‘LENGTH ls = n3 - n2’
       >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
           simp []) >> DISCH_TAC \\
      ‘ls <> []’ by simp [GSYM LENGTH_NON_NIL] \\
       Know ‘EL (PRE n3) vs3 = LAST ls’
       >- (Q.PAT_X_ASSUM ‘vs3 = vs4 ++ ls’ (REWRITE_TAC o wrap) \\
           simp [EL_APPEND2, LAST_EL, PRE_SUB]) >> Rewr' \\
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [Once EQ_SYM_EQ]) \\
       Know ‘MEM y2' ls’
       >- (POP_ORW >> simp [MEM_LAST_NOT_NIL]) >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
       Q.PAT_X_ASSUM ‘vs3 = vs4 ++ ls’ (REWRITE_TAC o wrap) \\
       simp [ALL_DISTINCT_APPEND] \\
       DISJ2_TAC >> Q.EXISTS_TAC ‘y2'’ >> art [] ])
 (* Case 4 (of 4): hardest *)
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> NTAC 2 (POP_ASSUM (MP_TAC o REWRITE_RULE []))
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j4’ STRIP_ASSUME_TAC)
 >> qabbrev_tac ‘X' = set vs3 UNION set vs4 UNION
                      FV W1 UNION FV W1' UNION
                      BIGUNION (IMAGE FV (set Ns1'')) UNION
                      BIGUNION (IMAGE FV (set Ns2''))’
 >> ‘FINITE X'’ by rw [Abbr ‘X'’]
 >> qabbrev_tac ‘d' = MAX (MAX n3 n4)
                          (MAX (SUC (d_max' j3))
                               (SUC (d_max' j4)))’
 >> Q_TAC (NEWS_TAC (“L :string list”, “d' :num”)) ‘X'’
 >> ‘n3 <= LENGTH L /\ n4 <= LENGTH L /\
     d_max' j3 < LENGTH L /\ d_max' j4 < LENGTH L’ by simp [Abbr ‘d'’, MAX_LE]
 >> Know ‘DISJOINT (set L) (set vs1) /\
          DISJOINT (set L) (set vs2) /\
          DISJOINT (set L) (set vs3) /\
          DISJOINT (set L) (set vs4)’
 >- (rw [Abbr ‘L’, Abbr ‘vs1’, Abbr ‘vs2’, Abbr ‘vs3’, Abbr ‘vs4’] \\
     MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’])
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘FINITE X'’ K_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set L) X'’ MP_TAC
 >> qunabbrev_tac ‘X'’
 >> DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DISJOINT_UNION'])
 >> simp [] (* VAR (y j3) ISUB ss = P (f j3), etc. *)
 >> STRIP_TAC (* W -h->* ... *)
 >> ‘m1 <= d_max' j3 /\ m2 <= d_max' j4’ by simp [Abbr ‘d_max'’]
 (* applying hreduce_permutator_shared *)
 >> MP_TAC (Q.SPECL [‘Ns1''’, ‘d_max + f (j3 :num)’, ‘L’] hreduce_permutator_shared)
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘zs1’ (Q.X_CHOOSE_THEN ‘z1’ STRIP_ASSUME_TAC))
 (* applying hreduce_permutator_shared again *)
 >> MP_TAC (Q.SPECL [‘Ns2''’, ‘d_max + f (j4 :num)’, ‘L’] hreduce_permutator_shared)
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘zs2’ (Q.X_CHOOSE_THEN ‘z2’ STRIP_ASSUME_TAC))
 >> qabbrev_tac ‘P3 = P (f j3)’
 >> qabbrev_tac ‘P4 = P (f j4)’
 >> Q.PAT_X_ASSUM ‘P3 @* Ns1'' -h->* _’ MP_TAC
 >> Q.PAT_X_ASSUM ‘P4 @* Ns2'' -h->* _’ MP_TAC
 >> qabbrev_tac ‘h = LAST L’ (* The new shared head variable *)
 >> qabbrev_tac ‘L' = FRONT L’
 >> ‘L <> []’ by rw [GSYM LENGTH_NON_NIL]
 >> NTAC 2 (Q.PAT_X_ASSUM ‘IS_SUFFIX L _’ MP_TAC)
 >> ‘L = SNOC h L'’ by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT]
 >> POP_ORW >> simp [IS_SUFFIX]
 >> NTAC 2 STRIP_TAC
 >> Q.PAT_X_ASSUM ‘z1 = z2’ (simp o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘h  = z1’ (simp o wrap o SYM)
 >> NTAC 2 DISCH_TAC
 >> qabbrev_tac ‘xs1 = SNOC h zs1’ (* suffix of L *)
 >> qabbrev_tac ‘xs2 = SNOC h zs2’ (* suffix of L *)
 >> Know ‘IS_SUFFIX L xs1 /\ IS_SUFFIX L xs2’
 >- (‘L = SNOC h L'’
        by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
     POP_ORW >> simp [IS_SUFFIX, Abbr ‘xs1’, Abbr ‘xs2’])
 >> STRIP_TAC
 >> ‘ALL_DISTINCT xs1 /\ ALL_DISTINCT xs2’ by PROVE_TAC [IS_SUFFIX_ALL_DISTINCT]
 >> Know ‘LAMl vs1 (P3 @* Ns1'') -h->*
          LAMl vs1 (LAMl zs1 (LAM h (VAR h @* Ns1'' @* MAP VAR zs1))) /\
          LAMl vs2 (P4 @* Ns2'') -h->*
          LAMl vs2 (LAMl zs2 (LAM h (VAR h @* Ns2'' @* MAP VAR zs2)))’
 >- simp [hreduce_LAMl]
 >> Q.PAT_X_ASSUM ‘P3 @* Ns1'' -h->* _’ K_TAC
 >> Q.PAT_X_ASSUM ‘P4 @* Ns2'' -h->* _’ K_TAC
 >> REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND]
 >> qabbrev_tac ‘Ns1x = Ns1'' ++ MAP VAR zs1’
 >> qabbrev_tac ‘Ns2x = Ns2'' ++ MAP VAR zs2’
 >> REWRITE_TAC [GSYM LAMl_SNOC]
 >> qabbrev_tac ‘zs1' = SNOC h (vs1 ++ zs1)’
 >> qabbrev_tac ‘zs2' = SNOC h (vs2 ++ zs2)’
 >> STRIP_TAC
 >> Know ‘W  -h->* LAMl zs1' (VAR h @* Ns1x) /\
          W' -h->* LAMl zs2' (VAR h @* Ns2x)’
 >- PROVE_TAC [hreduce_TRANS]
 >> NTAC 2 (POP_ASSUM K_TAC) >> STRIP_TAC
 >> qunabbrevl_tac [‘P3’, ‘P4’]
 >> Know ‘LAMl zs1' (VAR h @* Ns1x) = W0 /\
          LAMl zs2' (VAR h @* Ns2x) = W0'’
 >- (‘hnf (LAMl zs1' (VAR h @* Ns1x)) /\ hnf (LAMl zs2' (VAR h @* Ns2x))’
       by rw [hnf_appstar] \\
     METIS_TAC [principal_hnf_thm'])
 >> STRIP_TAC
 >> Know ‘LENGTH zs1' = n3 /\ LENGTH zs2' = n4’
 >- (Q.PAT_X_ASSUM ‘_ = n3’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = n4’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) >> simp [])
 >> STRIP_TAC
 (* key equations about n3 and n4, m3 and m4 *)
 >> Know ‘d_max' j3 = m3 /\ d_max' j4 = m4’
 >- (Q.PAT_X_ASSUM ‘_ = m3’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = m4’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
     simp [Abbr ‘Ns1x’, Abbr ‘Ns2x’])
 >> STRIP_TAC
 >> Know ‘SUC (d_max' j3) + n1 - m1 = n3 /\
          SUC (d_max' j4) + n2 - m2 = n4’
 >- (Q.PAT_X_ASSUM ‘_ = n3’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = n4’  (REWRITE_TAC o wrap o SYM) \\
     simp [Abbr ‘zs1'’, Abbr ‘zs2'’])
 >> simp [] >> STRIP_TAC
 (* stage work *)
 >> Know ‘LAST vs3 = y3’
 >- (Know ‘vs1 <<= vs3’
     >- (qunabbrevl_tac [‘vs1’, ‘vs3’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
    ‘n1' = n1’ by rw [] \\
     Q.PAT_X_ASSUM ‘n1' <= n3’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs1 = TAKE n1' vs3’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘vs1 ++ xs1 = zs1'’ by simp [Abbr ‘zs1'’, Abbr ‘xs1’] \\
     qabbrev_tac ‘ys1 = DROP n1 vs3’ \\
    ‘ALL_DISTINCT ys1’ by simp [Abbr ‘ys1’, ALL_DISTINCT_DROP] \\
     Know ‘DISJOINT (set xs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys1’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs1 = LENGTH ys1’ by simp [Abbr ‘xs1’, Abbr ‘ys1’] \\
     Know ‘LAMl vs3 (VAR y3 @* Ns3) = LAMl zs1' (VAR h @* Ns1x)’ >- rw [] \\
    ‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘_ = zs1'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [LAMl_APPEND] \\
     qabbrev_tac ‘t = VAR h @* Ns1x’ \\
  (* applying LAMl_ALPHA_ssub *)
     qabbrev_tac ‘pm1 = fromPairs xs1 (MAP VAR ys1)’ \\
  (* NOTE: The following disjointness hold for names from different rows *)
     Know ‘DISJOINT (set vs) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ >> simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ >> simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘LAMl xs1 t = LAMl ys1 (pm1 ' t)’
     >- (simp [Abbr ‘pm1’, fromPairs_def] \\
         MATCH_MP_TAC LAMl_ALPHA_ssub >> art [] \\
         simp [DISJOINT_UNION'] \\
         CONJ_TAC >- rw [Once DISJOINT_SYM] \\
         simp [Abbr ‘t’, Abbr ‘Ns1x’, appstar_APPEND, FV_appstar_MAP_VAR] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set xs1’ >> art [] \\
             simp [Abbr ‘xs1’, LIST_TO_SET_SNOC] >> SET_TAC []) \\
         simp [FV_appstar] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs1) (set ys1)’ MP_TAC \\
             rw [Abbr ‘xs1’, LIST_TO_SET_SNOC, DISJOINT_ALT]) \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m1’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns1''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘FV (EL i Ns1')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns1'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns1'’]) \\
         simp [Abbr ‘Ns1'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] \\
      (* applying FV_tpm_disjoint *)
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys1) (FV (EL i Ns1)) *)
         Know ‘FV N0 SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N’ >> art [] \\
             qunabbrev_tac ‘N0’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns1) SUBSET FV N UNION set vs1’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0’, ‘n1’, ‘m1’, ‘N1’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N UNION set vs1’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
            ‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM]) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC
         >- (‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs3’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> Rewr' \\
    ‘vs1 ++ ys1 = vs3’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
    ‘FDOM pm1 = set xs1’ by simp [Abbr ‘pm1’, FDOM_fromPairs] \\
    ‘MEM h xs1’ by simp [Abbr ‘xs1’, LIST_TO_SET_SNOC] \\
     simp [Abbr ‘t’, ssub_appstar] \\
     Know ‘pm1 ' h = VAR (LAST ys1)’
     >- (‘h = LAST xs1’ by rw [Abbr ‘xs1’, LAST_SNOC] >> POP_ORW \\
         ‘xs1 <> []’ by simp [Abbr ‘xs1’] \\
         ‘ys1 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         simp [Abbr ‘pm1’, LAST_EL] \\
         qabbrev_tac ‘j5 = PRE (LENGTH ys1)’ \\
         ‘0 < LENGTH ys1’ by rw [LENGTH_NON_NIL] \\
         ‘j5 < LENGTH ys1’ by rw [Abbr ‘j5’] \\
         ‘VAR (EL j5 ys1) = EL j5 (MAP VAR ys1)’ by simp [EL_MAP] >> POP_ORW \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘_ = W1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Know ‘LAST ys1 = LAST vs3’
     >- (‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
         ‘xs1 <> []’ by simp [Abbr ‘xs1’] \\
         ‘ys1 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         rw [LAST_APPEND_NOT_NIL]) >> Rewr' \\
     simp [])
 >> DISCH_TAC
 >> Know ‘LAST vs4 = y4’
 >- (Know ‘vs2 <<= vs4’
     >- (qunabbrevl_tac [‘vs2’, ‘vs4’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
    ‘n2' = n2’ by rw [] \\
     Q.PAT_X_ASSUM ‘n2' <= n4’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs2 = TAKE n2' vs4’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘vs2 ++ xs2 = zs2'’ by simp [Abbr ‘zs2'’, Abbr ‘xs2’] \\
     qabbrev_tac ‘ys2 = DROP n2 vs4’ \\
    ‘ALL_DISTINCT ys2’ by simp [Abbr ‘ys2’, ALL_DISTINCT_DROP] \\
     Know ‘DISJOINT (set xs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys2’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs2 = LENGTH ys2’ by simp [Abbr ‘xs2’, Abbr ‘ys2’] \\
     Know ‘LAMl vs4 (VAR y4 @* Ns4) = LAMl zs2' (VAR h @* Ns2x)’ >- rw [] \\
    ‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘_ = zs2'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [LAMl_APPEND] \\
     qabbrev_tac ‘t = VAR h @* Ns2x’ \\
  (* applying LAMl_ALPHA_ssub *)
     qabbrev_tac ‘pm2 = fromPairs xs2 (MAP VAR ys2)’ \\
     Know ‘DISJOINT (set vs) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ >> simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ >> simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘LAMl xs2 t = LAMl ys2 (pm2 ' t)’
     >- (simp [Abbr ‘pm2’, fromPairs_def] \\
         MATCH_MP_TAC LAMl_ALPHA_ssub >> art [] \\
         simp [DISJOINT_UNION'] \\
         CONJ_TAC >- rw [Once DISJOINT_SYM] \\
         simp [Abbr ‘t’, Abbr ‘Ns2x’, appstar_APPEND, FV_appstar_MAP_VAR] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set xs2’ >> art [] \\
             simp [Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
             SET_TAC []) \\
         simp [FV_appstar] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs2) (set ys2)’ MP_TAC \\
             rw [Abbr ‘xs2’, LIST_TO_SET_SNOC, DISJOINT_ALT]) \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m2’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns2''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘FV (EL i Ns2')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns2'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns2'’]) \\
         simp [Abbr ‘Ns2'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] \\
      (* applying FV_tpm_disjoint *)
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys2) (FV (EL i Ns2)) *)
         Know ‘FV N0' SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N'’ >> art [] \\
             qunabbrev_tac ‘N0'’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns2) SUBSET FV N' UNION set vs2’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0'’, ‘n2’, ‘m2’, ‘N1'’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N' UNION set vs2’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs4’ MP_TAC \\
            ‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM]) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs4’ \\
         reverse CONJ_TAC
         >- (‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs4’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> Rewr' \\
    ‘vs2 ++ ys2 = vs4’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
    ‘FDOM pm2 = set xs2’ by simp [Abbr ‘pm2’, FDOM_fromPairs] \\
    ‘MEM h xs2’ by simp [Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
     simp [Abbr ‘t’, ssub_appstar] \\
     Know ‘pm2 ' h = VAR (LAST ys2)’
     >- (‘h = LAST xs2’ by rw [Abbr ‘xs2’, LAST_SNOC] >> POP_ORW \\
         ‘xs2 <> []’ by simp [Abbr ‘xs2’] \\
         ‘ys2 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         simp [Abbr ‘pm2’, LAST_EL] \\
         qabbrev_tac ‘j5 = PRE (LENGTH ys2)’ \\
        ‘0 < LENGTH ys2’ by rw [LENGTH_NON_NIL] \\
        ‘j5 < LENGTH ys2’ by rw [Abbr ‘j5’] \\
        ‘VAR (EL j5 ys2) = EL j5 (MAP VAR ys2)’ by simp [EL_MAP] >> POP_ORW \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘_ = W1'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Know ‘LAST ys2 = LAST vs4’
     >- (‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
         ‘xs2 <> []’ by simp [Abbr ‘xs2’] \\
         ‘ys2 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         rw [LAST_APPEND_NOT_NIL]) >> Rewr' \\
     simp [])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> Know ‘y3 = y4 <=> n3 = n4’
 >- (Q.PAT_X_ASSUM ‘LAST vs3 = y3’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘LAST vs4 = y4’ (REWRITE_TAC o wrap o SYM) \\
     qabbrev_tac ‘n5 = MAX n3 n4’ \\
     Q_TAC (RNEWS_TAC (“vs5 :string list”, “r1 :num”, “n5 :num”)) ‘X’ \\
    ‘n3 <= n5 /\ n4 <= n5’ by simp [Abbr ‘n5’, MAX_LE] \\
     Know ‘vs3 <<= vs5’
     >- (qunabbrevl_tac [‘vs3’, ‘vs5’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n3'’ STRIP_ASSUME_TAC) \\
     Know ‘n3' = n3’
     >- (POP_ASSUM (MP_TAC o (AP_TERM “LENGTH :string list -> num”)) \\
         simp []) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘n3' <= n5’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs3 = TAKE n3' vs5’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
     Know ‘vs4 <<= vs5’
     >- (qunabbrevl_tac [‘vs4’, ‘vs5’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n4'’ STRIP_ASSUME_TAC) \\
     Know ‘n4' = n4’
     >- (POP_ASSUM (MP_TAC o (AP_TERM “LENGTH :string list -> num”)) \\
         simp []) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘n4' <= n5’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs4 = TAKE n4' vs5’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘vs3 <> [] /\ vs4 <> []’ by simp [GSYM LENGTH_NON_NIL] \\
     simp [LAST_EL] \\
     Q.PAT_X_ASSUM ‘TAKE n3 vs5 = vs3’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘TAKE n4 vs5 = vs4’ (REWRITE_TAC o wrap o SYM) \\
     simp [EL_TAKE] \\
  (* applying ALL_DISTINCT_EL_IMP *)
     Know ‘EL (PRE n3) vs5 = EL (PRE n4) vs5 <=> PRE n3 = PRE n4’
     >- (MATCH_MP_TAC ALL_DISTINCT_EL_IMP >> simp []) >> Rewr' \\
     simp [INV_PRE_EQ])
 >> Rewr'
 (* Current situation:

    N  -h->* LAMl vs1  (VAR y1  @* Ns1) (= N0)
    N' -h->* LAMl vs2  (VAR y2  @* Ns2) (= N0')
   --------------------------------------------
    W  -h->* LAMl vs3  (VAR y3  @* Ns3) (= W0) ---+  (y3 = LAST vs3)
    W  -h->* LAMl vs1  (P3      @* Ns1'')         |=
       -h->* LAMl zs1' (VAR h   @* Ns1x) ---------+
   --------------------------------------------
    W' -h->* LAMl vs4  (VAR y4  @* Ns4) (= W0') --+  (y4 = LAST vs4)
    W' -h->* LAMl vs2  (P4      @* Ns2'')         |=
       -h->* LAMl zs2' (VAR h   @* Ns2x) ---------+

    Structure of W0:

    LAMl |<---(vs1)--- vs3 -------(ys1)------->| VAR y3 (= LAST vs3)
    LAMl |<----------- zs1' ------------------>| VAR h
    LAMl |<--- vs1 ---->|<------- zs1 ------>|h| VAR h
                        |<------- xs1 -------->|
        n3 =   n1      +  d_max' j3 - m1 + 1
       (m3 =   m1      +  d_max' j3 - m1   = d_max' j3)

    Structure of W0':

    LAMl |<---(vs2)----- vs4 ----(ys2)--->| VAR y4 (= LAST vs4)
    LAMl |<------------- zs2' ----------->| VAR h
    LAMl |<--- vs2 ----->|<---- zs2 --->|h| VAR h
                         |<---- xs2 ----->|
        n4 =   n2      +  d_max' j4 - m2 + 1
       (m4 =   m2      +  d_max' j4 - m2   = d_max' j4)
  *)
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> Cases_on ‘y1 = y2’ >> simp []
 (* now: y1 <> y2 *)
 >> ‘y1' <> y2'’ by rw [Abbr ‘y1'’, Abbr ‘y2'’]
 >> ‘y j3 <> y j4’ by rw []
 >> Suff ‘m3 <> m4’ >- simp []
 (* final goal (uniqueness of f) *)
 >> Q.PAT_X_ASSUM ‘_ = m3’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘_ = m4’ (REWRITE_TAC o wrap o SYM)
 >> simp [Abbr ‘d_max'’]
 *)
QED

(* END *)
val _ = html_theory "separability";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
