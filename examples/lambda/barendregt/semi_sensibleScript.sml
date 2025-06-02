(* ========================================================================== *)
(* FILE    : semi_sensibleScript.sml (chap17_1Script.sml)                     *)
(* TITLE   : Semi-sensible theories of lambda calculus [Barendregt 17.1]      *)
(*                                                                            *)
(* AUTHORS : 2025  The Australian National University (Chun Tian)             *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open listTheory numLib hurdUtils pred_setTheory pred_setLib relationTheory
     topologyTheory;

open termTheory chap2Theory chap3Theory horeductionTheory boehmTheory
     lameta_completeTheory;

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

(* Definition 10.4.4 [1, p.256], but is generalized with a theory parameter.

   This definition combined the cases of closed and open terms, cf. solvable_def
 *)
Definition separable_def :
    separable R Ms <=>
    let X = BIGUNION (IMAGE FV (set Ms));
       Fs = MAP (LAMl (SET_TO_LIST X)) Ms
    in
      !Ns. LENGTH Ns = LENGTH Ms ==>
           ?f. !i. i < LENGTH Ms ==>
                   conversion (beta RUNION R) (f @@ (EL i Fs)) (EL i Ns)
End

(* Definition 10.4.4 (i) [1, p.256], now an equivalent theorem *)
Theorem separable_alt_closed :
    !R Ms. EVERY closed Ms ==>
          (separable R Ms <=>
           !Ns. LENGTH Ns = LENGTH Ms ==>
                ?f. !i. i < LENGTH Ms ==>
                        conversion (beta RUNION R) (f @@ (EL i Ms)) (EL i Ns))
Proof
    RW_TAC std_ss [EVERY_EL, separable_def]
 >> Know ‘X = {}’
 >- (Cases_on ‘Ms = []’ >- rw [Abbr ‘X’] \\
     rw [Abbr ‘X’, Once EXTENSION] \\
     fs [closed_def] \\
     EQ_TAC >> rw [MEM_EL] >> rw [] \\
    ‘0 < LENGTH Ms’ by rw [LENGTH_NON_NIL] \\
     Q.EXISTS_TAC ‘EL 0 Ms’ >> rw [] \\
     Q.EXISTS_TAC ‘0’ >> rw [])
 >> DISCH_THEN (fs o wrap)
QED

(* Lemma 10.4.5 [1, p.257] or Definition 17.1.3 (ii) [1, p.432]

   NOTE: From now on, one should use this theorem as the canonical definition.
 *)
Theorem separable_alt :
    !R Ms. separable R Ms <=>
           !Ns. LENGTH Ns = LENGTH Ms ==>
                ?c. ctxt c /\
                    !i. i < LENGTH Ms ==>
                        conversion (beta RUNION R) (c (EL i Ms)) (EL i Ns)
Proof
    RW_TAC std_ss [separable_def]
 >> qabbrev_tac ‘vs = SET_TO_LIST X’
 >> EQ_TAC >> rw []
 >- (Q.PAT_X_ASSUM ‘!Ns. LENGTH Ns = LENGTH Ms ==> _’
       (MP_TAC o Q.SPEC ‘Ns’) >> rw [] \\
     Q.EXISTS_TAC ‘\x. f @@ LAMl vs x’ \\
     reverse CONJ_TAC
     >- (POP_ASSUM MP_TAC >> rw [Abbr ‘Fs’, EL_MAP]) \\
     HO_MATCH_MP_TAC ctxt_APPR \\
     HO_MATCH_MP_TAC ctxt_LAMl >> rw [ctxt_I])
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘!Ns. LENGTH Ns = LENGTH Ms ==> _’
      (MP_TAC o Q.SPEC ‘Ns’) >> rw []
 >> Know ‘set vs = X’
 >- (qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC SET_TO_LIST_INV \\
     qunabbrev_tac ‘X’ \\
     MATCH_MP_TAC FINITE_BIGUNION >> rw [] >> rw [])
 >> DISCH_TAC
 >> Know ‘!i. i < LENGTH Ms ==> FV (EL i Ms) SUBSET set vs’
 >- (rw [Abbr ‘vs’] \\
     rw [Abbr ‘X’, SUBSET_DEF] \\
     Q.EXISTS_TAC ‘FV (EL i Ms)’ >> rw [] \\
     Q.EXISTS_TAC ‘EL i Ms’ >> rw [EL_MEM])
 >> DISCH_TAC
 (* applying lameq_ctxt_app_lemma *)
 >> MP_TAC (Q.SPECL [‘vs’, ‘c’] lameq_ctxt_app_lemma) >> rw []
 >> Q.EXISTS_TAC ‘f’
 >> rw [Abbr ‘Fs’, EL_MAP]
 >> Q_TAC (TRANS_TAC conversion_TRANS) ‘c (EL i Ms)’ >> rw []
 >> MATCH_MP_TAC conversion_SYM
 >> irule (REWRITE_RULE [RSUBSET] conversion_monotone)
 >> Q.EXISTS_TAC ‘beta’
 >> simp [RUNION, GSYM lameq_betaconversion]
QED

(* The usual “separable” with empty theory (i.e. with beta-conversion only)
   is now overloaded as “separable'”.
 *)
Overload separable'    = “separable REMPTY”

(* “eta_separable” is another common instance with beta- and eta-conversion. *)
Overload eta_separable = “separable eta”

(* |- !Ms.
        separable eta Ms <=>
        !Ns.
          LENGTH Ns = LENGTH Ms ==>
          ?c. ctxt c /\ !i. i < LENGTH Ms ==> lameta (c (EL i Ms)) (EL i Ns)
 *)
Theorem eta_separable_def =
        separable_alt |> Q.SPEC ‘eta’ |> REWRITE_RULE [beta_eta_lameta]

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
