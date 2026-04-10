(* ========================================================================== *)
(* FILE    : separabilityScript.sml                                           *)
(* TITLE   : Separability of lambda terms (additional work) [1, Chapter 10.4] *)
(* ========================================================================== *)

Theory separability
Ancestors
  combin arithmetic pred_set list rich_list llist ltree relation
  topology iterate option nomset basic_swap term appFOLDL chap2
  chap3 horeduction solvable takahashiS3 head_reduction
  standardisation boehm
Libs
  hurdUtils tautLib numLib listLib NEWLib reductionEval
  head_reductionLib monadsyntax

(* enable basic monad support *)
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

local open set_relationTheory in
   val rel_to_reln_IS_UNCURRY = rel_to_reln_IS_UNCURRY;
end

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

val PRINT_TAC = goalStack.note_tac

(* Disable some conflicting overloads from labelledTermsTheory *)
Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

val _ = temp_clear_overloads_on "fEL";

(*---------------------------------------------------------------------------*
 *  Virtual subterm (vsubterm) of Boehm Trees
 *---------------------------------------------------------------------------*)

(* vsubterm

   ((vs,y),Ms)   vs::[z_0,z_1,z_2,...]
       /\
     /    \      0,   1, .. (j = h - m)
    0 ...  m-1,  m, m+1, .. h
                       (([],z_j),[])

   NOTE: vsubterm X M p r is equivalent to subterm X M' p r, where M' corresponds
   to an (possibly) infinite eta-expansion of (Boehm tree of) M, thus M === M'.
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

Definition FV_condition_def :
    FV_condition X M r <=> FINITE X /\ FV M SUBSET X UNION RANK r
End

Theorem vsubterm_eq_subterm :
    !X M p r. FV_condition X M r /\ p IN BT_paths M ==>
              vsubterm X M p r = subterm X M p r
Proof
    cheat
QED

val _ = html_theory "separability";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
