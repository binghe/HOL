(* ========================================================================== *)
(* FILE    : separabilityScript.sml                                           *)
(* TITLE   : Separability of lambda terms (additional work) [1, Chapter 10.4] *)
(* ========================================================================== *)

Theory separability
Ancestors
  combin option arithmetic pred_set list rich_list llist ltree relation
  topology nomset basic_swap term appFOLDL chap2 chap3 horeduction
  head_reduction standardisation solvable boehm takahashiS3 lameta_complete
Libs
  hurdUtils tautLib numLib listLib NEWLib reductionEval head_reductionLib
  monadsyntax intLib

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

(* cf. lameq_subterm_cong *)
Theorem lameta_vsubterm_cong :
    !X M N p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
                            FV N SUBSET X UNION RANK r /\ M === N
           ==> (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
                vsubterm X M p r <> NONE ==>
                vsubterm' X M p r === vsubterm' X N p r
Proof
    Suff ‘!X. FINITE X ==>
              !p M N r. FV M SUBSET X UNION RANK r /\
                        FV N SUBSET X UNION RANK r /\ M === N
          ==> (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
               vsubterm X M p r <> NONE ==>
               vsubterm' X M p r === vsubterm' X N p r’ >- METIS_TAC []
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
 >- (simp [Abbr ‘n_max’] >> intLib.ARITH_TAC)
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
      >- (simp [Abbr ‘n_max’] \\
          intLib.ARITH_TAC) >> DISCH_TAC \\
      qunabbrev_tac ‘zs'’ \\
      Q_TAC (RNEWS_TAC (“zs' :string list”, “r :num”, “n' + SUC j'”)) ‘X’ \\
     ‘zs' <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      simp [LAST_EL] \\
     ‘PRE (n' + SUC j') = n' + j'’ by intLib.ARITH_TAC >> POP_ORW \\
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
      >- (simp [Abbr ‘n_max’] \\
          intLib.ARITH_TAC) >> DISCH_TAC \\
      qunabbrev_tac ‘zs’ \\
      Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
     ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      simp [LAST_EL] \\
     ‘PRE (n + SUC j) = n + j’ by intLib.ARITH_TAC >> POP_ORW \\
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
     ‘PRE (n + SUC j) = n + j’     by intLib.ARITH_TAC >> POP_ORW \\
     ‘PRE (n' + SUC j') = n' + j'’ by intLib.ARITH_TAC >> POP_ORW \\
      Know ‘n + SUC j <= n_max’
      >- (simp [Abbr ‘n_max’] \\
          intLib.ARITH_TAC) >> DISCH_TAC \\
      Know ‘n' + SUC j' <= n_max’
      >- (simp [Abbr ‘n_max’] \\
          intLib.ARITH_TAC) >> DISCH_TAC \\
     ‘zs = TAKE (n + SUC j) xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
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

val _ = html_theory "separability";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
