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

(* NOTE: cf. lameq_subterm_cong *)
Theorem lameta_vsubterm_cong :
    !X M N p r. FINITE X /\
                FV M SUBSET X UNION RANK r /\
                FV N SUBSET X UNION RANK r /\ M === N
           ==> (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
                vsubterm X M p r <> NONE ==>
                vsubterm' X M p r === vsubterm' X N p r
Proof
  Suff
   ‘!X. FINITE X ==>
        !p M N r.
           FV M SUBSET X UNION RANK r /\
           FV N SUBSET X UNION RANK r /\ M === N
          ==>
          (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
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
 >> FULL_SIMP_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘P  = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘P' = _’ K_TAC
 (* applying hnf_etastar_cases *)
 >> Q.PAT_X_ASSUM ‘LAMl vs (VAR y @* Ns) -e->* Z’
      (MP_TAC o MATCH_MP hnf_etastar_cases)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ (Q.X_CHOOSE_THEN ‘Ms’ STRIP_ASSUME_TAC))
 >> Q.PAT_X_ASSUM ‘LAMl vs' (VAR y' @* Ns') -e->* Z’
      (MP_TAC o MATCH_MP hnf_etastar_cases)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘i'’ (Q.X_CHOOSE_THEN ‘Ms'’ STRIP_ASSUME_TAC))
(*
   M0  = LAMl vs  (VAR y  @* args)
   P   = LAMl vs  (VAR y  @* Ns)                  (EL i args -b->* EL i Ns)
   Z   = LAMl (BUTLASTN i  vs ) (VAR y  @* Ms )    EL i Ns   -e->* EL i Ms
   Z   = LAMl (BUTLASTN i' vs') (VAR y' @* Ms')    EL i Ns'  -e->* EL i Ms'
   P'  = LAMl vs' (VAR y' @* Ns')                 (EL i args'-b->* EL i Ns')
   M0' = LAMl vs' (VAR y' @* args')
 *)
 >> cheat
QED

val _ = html_theory "separability";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
