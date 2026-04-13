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

(* NOTE: BT_to_term B = rose_to_term (to_rose B) *)
Theorem vsubterm_expand_lemma :
    !X M p r B N m.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M /\
       p IN ltree_paths (BT' X M r) /\
       ltree_branching (BT' X M r) p = SOME m /\
       BT_expand X (BT' X M r) p r = B /\ N = BT_to_term B ==>
       vsubterm X M (SNOC m p) r = subterm X N (SNOC m p) r
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ASM_REWRITE_TAC []
 >> Suff ‘!R M p r m. (?B. FV M SUBSET X UNION RANK r /\ bnf M /\
                           p IN ltree_paths (BT' X M r) /\
                           ltree_branching (BT' X M r) p = SOME m /\
                           B = BT_expand X (BT' X M r) p r /\
                           R = to_rose B) ==>
                      vsubterm X M (SNOC m p) r =
                       subterm X (rose_to_term R) (SNOC m p) r’
 >- (DISCH_THEN MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘B’ >> art [])
 >> Q.PAT_X_ASSUM ‘FINITE X’ MP_TAC
 >> KILL_TAC >> DISCH_TAC
 (* applying induction on rose tree *)
 >> HO_MATCH_MP_TAC rose_tree_induction
 >> NTAC 2 (rpt GEN_TAC >> STRIP_TAC)
 >> cheat
QED

val _ = html_theory "separability";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
