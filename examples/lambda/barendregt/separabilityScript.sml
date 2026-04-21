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

(* Step 1 (by beta_eta_CR):

   M  -h->* M0 ---+ reduction (beta UNION eta)
   |        |      \
 lameta   lameta    P
   |        |      /
   N  -h->* N0 ---+

  Step 2 (by takahashi_3_5)

   M  -h->* M0 --b->* M0' ---+ reduction eta
   |        |                 \
 lameta   lameta               P
   |        |                 /
   N  -h->* N0 --b->* N0' ---+

   M0  = LAMl vs1 (VAR y @* args1)
   M0' = LAMl vs1 (VAR y @* args1')   (EL i args -b->* EL i args')
   P   = LAMl vs  (VAR y @* args)      args1' = args ++ MAP VAR ys1
   N0' = LAMl vs2 (VAR y @* args2')    args2' = args ++ MAP VAR ys2
   N0  = LAMl vs2 (VAR y @* args2)     args2  = _    ++ MAP VAR ys2

   “vsubterm X M p r” directly access ‘args1’ and ‘args2’.
 *)
Theorem lameta_vsubterm_cong :
    !X M N r. FINITE X /\
              FV M SUBSET X UNION RANK r /\
              FV N SUBSET X UNION RANK r /\
              M === N ==> !p. vsubterm X M p r = vsubterm X N p r
Proof
    cheat
QED

val _ = html_theory "separability";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
