(* ========================================================================== *)
(* FILE    : semi_sensibleScript.sml (chap17_1Script.sml)                     *)
(* TITLE   : Semi sensible theories [1, Chapter 17.1]                         *)
(*                                                                            *)
(* AUTHORS : 2025  The Australian National University (Chun Tian)             *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open listTheory numLib hurdUtils;

open chap2Theory chap3Theory boehmTheory lameta_completeTheory;

(* These theorems usually give unexpected results, should be applied manually *)
val _ = temp_delsimps [
   "lift_disj_eq", "lift_imp_disj",
   "IN_UNION",     (* |- !s t x. x IN s UNION t <=> x IN s \/ x IN t *)
   "APPEND_ASSOC", (* |- !l1 l2 l3. l1 ++ (l2 ++ l3) = l1 ++ l2 ++ l3 *)
   "SNOC_APPEND"   (* |- !x l. SNOC x l = l ++ [x] *)
];

val _ = hide "B";
val _ = hide "C";
val _ = hide "W";
val _ = hide "Y";

Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

val _ = new_theory "semi_sensible";

(* Definition 10.4.4 [1, p.256] *)
Definition separable_def :
    separable R Ms <=>
    !Ns. LENGTH Ns = LENGTH Ms ==>
         ?c. ctxt c /\
             !i. i < LENGTH Ms ==>
                 conversion (beta RUNION R) (c (EL i Ms)) (EL i Ns)
End

Overload separable'    = “separable REMPTY”
Overload eta_separable = “separable eta”

(* |- !Ms.
        eta_separable Ms <=>
        !Ns.
          LENGTH Ns = LENGTH Ms ==>
          ?c. ctxt c /\ !i. i < LENGTH Ms ==> lameta (c (EL i Ms)) (EL i Ns)
 *)
Theorem eta_separable_def =
        separable_def |> Q.SPEC ‘eta’
                      |> REWRITE_RULE [beta_eta_lameta]

Theorem eta_separable_thm :
    !M N. has_benf M /\ has_benf N /\ ~(lameta M N) ==> eta_separable [M; N]
Proof
    rw [eta_separable_def]
 >> MP_TAC (Q.SPECL [‘M’, ‘N’] separability_thm_final) >> simp []
 >> DISCH_THEN (MP_TAC o Q.SPECL [‘EL 0 Ns’, ‘EL 1 Ns’])
 >> STRIP_TAC
 (* applying Boehm_transform_lameq_ctxt *)
 >> ‘?c. ctxt c /\ !M. apply pi M == c M’ by PROVE_TAC [Boehm_transform_lameq_ctxt]
 >> Q.EXISTS_TAC ‘c’ >> art []
 >> CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss []))
 >> CONJ_TAC
 >- (Q_TAC (TRANS_TAC lameta_TRANS) ‘apply pi N’ >> art [] \\
     MATCH_MP_TAC lameta_SYM \\
     MATCH_MP_TAC lameq_imp_lameta >> art [])
 >> CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss []))
 >> ASM_SIMP_TAC bool_ss [GSYM EL]
 >> Q_TAC (TRANS_TAC lameta_TRANS) ‘apply pi M’ >> art []
 >> MATCH_MP_TAC lameta_SYM
 >> MATCH_MP_TAC lameq_imp_lameta >> art []
QED

val _ = export_theory ();
val _ = html_theory "semi_sensible";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
