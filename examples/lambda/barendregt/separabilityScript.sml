(* ========================================================================== *)
(* FILE    : separabilityScript.sml                                           *)
(* TITLE   : Separability of lambda terms (additional work) [1, Chapter 10.4] *)
(* ========================================================================== *)

Theory separability
Ancestors
  combin option arithmetic pred_set list rich_list llist ltree relation iterate
  topology nomset basic_swap term appFOLDL chap2 chap3 chap4 horeduction
  head_reduction standardisation solvable boehm takahashiS3 lameta_complete
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

(* |- (VAR s -e-> t <=> F) /\
      (t @@ u -e-> v <=>
       (?t'. v = t' @@ u /\ t -e-> t') \/ ?u'. v = t @@ u' /\ u -e-> u') /\
      (LAM v t -e-> u <=> (?t'. u = LAM v t' /\ t -e-> t') \/ eta (LAM v t) u)
 *)
Theorem cceta_rwt[local] =
        LIST_CONJ ((map SPEC_ALL (CONJUNCTS cc_eta_thm)) @
                   [SPEC_ALL cc_eta_LAM])

Theorem hnf_cceta_appstar[local] :
    !y Ms N. VAR y @* Ms -e-> N /\ Ms <> [] ==>
             ?Ns. N = VAR y @* Ns /\ LENGTH Ns = LENGTH Ms /\
                  !i. i < LENGTH Ms ==> EL i Ms -e->* EL i Ns
Proof
    Q.X_GEN_TAC ‘y’
 >> SNOC_INDUCT_TAC >> rw []
 >> fs [cceta_rwt] (* 2 subgoals *)
 >- (Cases_on ‘Ms = []’ >> fs [cceta_rwt] \\
     rename1 ‘VAR y @* Ms -e-> M'’ \\
     Q.PAT_X_ASSUM ‘!N. P’ (MP_TAC o (Q.SPEC ‘M'’)) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘SNOC x Ns’ >> rw [] \\
    ‘i = LENGTH Ms \/ i < LENGTH Ms’ by rw []
     >- (rw [EL_LENGTH_SNOC] \\
         Q.PAT_X_ASSUM ‘LENGTH Ns = LENGTH Ms’ (REWRITE_TAC o wrap o SYM) \\
         rw [EL_LENGTH_SNOC]) \\
     rw [EL_SNOC])
 (* stage work *)
 >> Cases_on ‘Ms = []’ >> fs [cceta_rwt]
 >- (rename1 ‘N = VAR y @@ N'’ \\
     Q.EXISTS_TAC ‘[N']’ >> rw [])
 >> rename1 ‘N = VAR y @* Ms @@ N'’
 >> Q.EXISTS_TAC ‘SNOC N' Ms’
 >> rw [appstar_SNOC]
 >> ‘i = LENGTH Ms \/ i < LENGTH Ms’ by rw [] >- rw [EL_LENGTH_SNOC]
 >> rw [EL_SNOC]
QED

Theorem cceta_LAM_rwt[local] :
    LAM v t -e-> u <=>
     (?t'. u = LAM v t' /\ t -e-> t') \/ (t = u @@ VAR v /\ v # u)
Proof
    rw [cceta_rwt, eta_def]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 4) *)
      DISJ1_TAC >> Q.EXISTS_TAC ‘t'’ >> art [],
      (* goal 2 (of 4) *)
      DISJ2_TAC \\
      Cases_on ‘v = v'’ >> fs [] \\
      gs [LAM_eq_thm] \\
      MATCH_MP_TAC tpm_fresh >> art [],
      (* goal 3 (of 4) *)
      DISJ1_TAC >> Q.EXISTS_TAC ‘t'’ >> art [],
      (* goal 4 (of 4) *)
      DISJ2_TAC >> Q.EXISTS_TAC ‘v’ >> art [] ]
QED

(* LAMl (vs ++ [v]) (P @@ VAR v) -e-> LAMl vs P *)
Theorem cceta_LAMl_rwt[local] :
    !vs M N. LAMl vs M -e-> N <=>
            (?M'. N = LAMl vs M' /\ M -e-> M') \/
            (vs <> [] /\
             ?P. M = P @@ VAR (LAST vs) /\ N = LAMl (FRONT vs) P /\
                 LAST vs # P)
Proof
    SNOC_INDUCT_TAC >> rw []
 >> KILL_TAC
 >> reverse EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘LAM x M'’ >> rw [cceta_LAM_rwt])
 >- (Q.EXISTS_TAC ‘P’ >> rw [cceta_LAM_rwt])
 >> fs [cceta_LAM_rwt]
QED

Theorem hnf_cceta_cases[local] :
    !Ms vs N. LAMl vs (VAR y @* Ms) -e-> N ==>
             (?Ns. N = LAMl vs (VAR y @* Ns) /\
                   LENGTH Ns = LENGTH Ms /\
                  !i. i < LENGTH Ms ==> EL i Ms -e->* EL i Ns) \/
             (vs <> [] /\ Ms <> [] /\
              N = LAMl (FRONT vs) (VAR y @* FRONT Ms) /\
              LAST Ms = VAR (LAST vs))
Proof
    SNOC_INDUCT_TAC
 >- (simp [] \\
     SNOC_INDUCT_TAC >> rw [] >- fs [cceta_rwt] \\
     fs [cceta_LAMl_rwt] \\
     fs [cceta_LAM_rwt] \\
     fs [cceta_rwt])
 >> qx_genl_tac [‘P’, ‘vs’, ‘N’]
 >> simp [appstar_SNOC]
 >> qabbrev_tac ‘t = VAR y @* Ms’
 >> rw [cceta_LAMl_rwt]
 >> reverse (fs [Abbr ‘t’, cceta_rwt])
 >- (DISJ1_TAC \\
     rename1 ‘M' = VAR y @* Ms @@ N’ \\
     Q.EXISTS_TAC ‘SNOC N Ms’ \\
     rw [appstar_SNOC] \\
     ‘i < LENGTH Ms \/ i = LENGTH Ms’ by simp [] >- simp [EL_SNOC] \\
     simp [EL_LENGTH_SNOC])
 >> Cases_on ‘Ms = []’ >- fs [cceta_rwt]
 (* applying hnf_cceta_appstar *)
 >> rename1 ‘VAR y @* Ms -e-> N’
 >> MP_TAC (Q.SPECL [‘y’, ‘Ms’, ‘N’] hnf_cceta_appstar)
 >> RW_TAC std_ss []
 >> DISJ1_TAC
 >> Q.EXISTS_TAC ‘SNOC P Ns’
 >> rw [appstar_SNOC]
 >> ‘i < LENGTH Ms \/ i = LENGTH Ms’ by simp [] >- simp [EL_SNOC]
 >> simp [EL_LENGTH_SNOC]
 >> Q.PAT_X_ASSUM ‘LENGTH Ns = LENGTH Ms’ (REWRITE_TAC o wrap o SYM)
 >> simp [EL_LENGTH_SNOC]
QED

Theorem hnf_eta_reduction_cases :
    !vs y Ms N. LAMl vs (VAR y @* Ms) -e->* N ==>
                ?Ns n. N = LAMl (BUTLASTN n vs) (VAR y @* (BUTLASTN n Ns)) /\
                       n <= LENGTH vs /\ n <= LENGTH Ns /\
                       LENGTH Ns = LENGTH Ms /\
                       !i. i < LENGTH Ms ==> EL i Ms -e->* EL i Ns
Proof
    NTAC 2 GEN_TAC
 >> Suff ‘!M N. M -e->* N ==>
               !vs Ms. M = LAMl vs (VAR y @* Ms) ==>
                       ?Ns n. N = LAMl (BUTLASTN n vs) (VAR y @* BUTLASTN n Ns) /\
                              n <= LENGTH vs /\ n <= LENGTH Ns /\
                              LENGTH Ns = LENGTH Ms /\
                              !i. i < LENGTH Ms ==> EL i Ms -e->* EL i Ns’
 >- METIS_TAC []
 >> HO_MATCH_MP_TAC RTC_INDUCT >> rw []
 >- (qexistsl_tac [‘Ms’, ‘0’] >> simp [BUTLASTN])
 >> Q.PAT_X_ASSUM ‘LAMl vs (VAR y @* Ms) -e-> M'’
      (STRIP_ASSUME_TAC o MATCH_MP hnf_cceta_cases)
 >- (Q.PAT_X_ASSUM ‘!vs Ms. M' = LAMl vs (VAR y @* Ms) ==> _’
       (MP_TAC o Q.SPECL [‘vs’, ‘Ns’]) \\
     RW_TAC std_ss [] \\
     qexistsl_tac [‘Ns'’, ‘n’] >> rw [] \\
     MATCH_MP_TAC etastar_TRANS \\
     Q.EXISTS_TAC ‘EL i Ns’ >> simp [])
 (* stage work *)
 >> qabbrev_tac ‘vs' = FRONT vs’
 >> qabbrev_tac ‘Ms' = FRONT Ms’
 >> qabbrev_tac ‘v = LAST vs’
 >> qabbrev_tac ‘M = LAST Ms’
 >> ‘vs = SNOC v vs'’ by simp [Abbr ‘v’, Abbr ‘vs'’, SNOC_LAST_FRONT] >> POP_ORW
 >> ‘Ms = SNOC M Ms'’ by simp [Abbr ‘M’, Abbr ‘Ms'’, SNOC_LAST_FRONT] >> POP_ORW
 >> Q.PAT_X_ASSUM ‘!vs Ms. P’ (MP_TAC o Q.SPECL [‘vs'’, ‘Ms'’]) >> rw []
 >> qexistsl_tac [‘SNOC (VAR v) Ns’, ‘SUC n’]
 >> rw [BUTLASTN]
 >> ‘i < LENGTH Ms' \/ i = LENGTH Ms'’ by simp [] >- simp [EL_SNOC]
 >> simp [EL_LENGTH_SNOC]
 >> Q.PAT_X_ASSUM ‘LENGTH Ns = LENGTH Ms'’ (REWRITE_TAC o wrap o SYM)
 >> simp [EL_LENGTH_SNOC]
QED

Theorem lameta_vsubterm_cong_lemma[local] :
    !X. FINITE X ==>
        !p M N r.
           FV M SUBSET X UNION RANK r /\
           FV N SUBSET X UNION RANK r /\ M === N
          ==>
          (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
           vsubterm X M p r <> NONE ==>
           vsubterm' X M p r === vsubterm' X N p r
Proof
    NTAC 2 STRIP_TAC
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
 >> ‘?P.  M0  -b->* P  /\ P  -e->* Z’ by METIS_TAC [takahashi_3_5]
 >> ‘?P'. M0' -b->* P' /\ P' -e->* Z’ by METIS_TAC [takahashi_3_5]
 >> Q.PAT_X_ASSUM ‘M0  -be->* Z’ K_TAC
 >> Q.PAT_X_ASSUM ‘M0' -be->* Z’ K_TAC
 (*
    M -h->* M0 --b->* P -e->*
    |       |                \
   ===     ===                Z
    |       |                /
    N -h->* M0'--b->* P'-e->*
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
 >> qunabbrevl_tac [‘M1’, ‘M1'’, ‘M2’, ‘M2'’]
 >> qabbrev_tac ‘M1  = principal_hnf (M0  @* MAP VAR vs)’
 >> qabbrev_tac ‘M1' = principal_hnf (M0' @* MAP VAR vs')’
 >> ‘args = Ms’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘args' = Ms'’ (fs o wrap o SYM) >> T_TAC
 (* applying hnf_betastar_cases *)
 >> Q.PAT_X_ASSUM ‘LAMl vs (VAR y @* args) -b->* P’
      (STRIP_ASSUME_TAC o MATCH_MP hnf_betastar_cases) (* NS *)
 >> Q.PAT_X_ASSUM ‘LAMl vs' (VAR y' @* args') -b->* P'’
      (STRIP_ASSUME_TAC o MATCH_MP hnf_betastar_cases) (* NS' *)
(*
   M0  = LAMl vs  (VAR y  @* args)
   P   = LAMl vs  (VAR y  @* Ns)    (EL i args  -b->* EL i Ns)
   Z   = LAMl _   (VAR _  @* _)
   P'  = LAMl vs' (VAR y' @* Ns')   (EL i args' -b->* EL i Ns')
   M0' = LAMl vs' (VAR y' @* args')
 *)
 >> cheat
QED

(* NOTE: cf. lameq_subterm_cong *)
Theorem lameta_vsubterm_cong :
    !X M N p r. FINITE X /\
                FV M SUBSET X UNION RANK r /\
                FV N SUBSET X UNION RANK r /\ M === N
           ==> (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
                vsubterm X M p r <> NONE ==>
                vsubterm' X M p r === vsubterm' X N p r
Proof
    PROVE_TAC [lameta_vsubterm_cong_lemma]
QED

val _ = html_theory "separability";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
