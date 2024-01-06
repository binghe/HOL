(* ========================================================================== *)
(* FILE          : ExtendedScript.sml                                         *)
(* DESCRIPTION   : Extended Theory of CCS w.r.t. "open" terms                 *)
(*                                                                            *)
(* COPYRIGHTS    : 2023-2024 Australian National University (Chun Tian)       *)
(******************************************************************************)
x
open HolKernel Parse boolLib bossLib;

open pred_setTheory pairTheory relationTheory bisimulationTheory listTheory
     finite_mapTheory;

open CCSLib CCSTheory StrongEQTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val _ = new_theory "Extended";

(*

(* Substitution of free variables to ‘nil’ preserves strong bisimilarity. *)
Theorem STRONG_EQUIV_ssub_lemma :
    !fm E. (!y. y IN FDOM fm ==> fm ' y = nil) ==> STRONG_EQUIV E (fm ' E)
Proof
    Q.X_GEN_TAC ‘fm’
 >> HO_MATCH_MP_TAC CCS_induction
 >> Q.EXISTS_TAC ‘FDOM fm’
 >> rw [] (* 7 subgoals *)
 >| [ (* goal 1 (of 7) *)
      rw [FUN_FMAP_DEF, PROPERTY_STAR, NIL_NO_TRANS, VAR_NO_TRANS],
      (* goal 2 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX >> rw [],
      (* goal 3 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_SUM >> rw [],
      (* goal 4 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> rw [],
      (* goal 5 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> rw [],
      (* goal 6 (of 7) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> rw [],
      (* goal 7 (of 7) *)
      cheat ]
QED

(* Definition 5 of [1, p.98] (see also [2, p.181])

   If any of P and Q is not closed, but all their closed simultaneous
   substitutions are strong bisimular, then so is P and Q.

   NOTE: ‘fm’ is not required to cover all FVs of P and Q, those free vars
         which is not substituted, will be treated as nil (i.e. no transitions).
         Furthermore, if ‘FDOM fm’ is larger than ‘FV P UNION FV Q’, the extra
         keys won't cause any trouble.

   TODO: do we really need to say ‘fm’ is closed substitution?
 *)
Definition StrongEQ_def :
    StrongEQ P Q = !fm. (!y. y IN FDOM fm ==> closed (fm ' y)) ==>
                        STRONG_EQUIV (fm ' P) (fm ' Q)
End

Theorem StrongEQ_alt_closed :
    !P Q. closed P /\ closed Q ==> (StrongEQ P Q <=> STRONG_EQUIV P Q)
Proof
    rw [StrongEQ_def]
QED

Theorem SUBSET_SING[local] :
    !X x. X SUBSET {x} <=> X = {} \/ X = {x}
Proof
    SET_TAC []
QED

(* TODO *)
Theorem StrongEQ_alt_single :
    !X P Q. FV P SUBSET {X} /\ FV Q SUBSET {X} ==>
           (StrongEQ P Q <=> !E. closed E ==> STRONG_EQUIV ([E/X] P) ([E/X] Q))
Proof
    rpt STRIP_TAC
 >> Cases_on ‘closed P /\ closed Q’
 >- (rw [StrongEQ_alt_closed] \\
     Suff ‘!E. closed E ==> [E/X] P = P /\ [E/X] Q = Q’ >- METIS_TAC [] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC lemma14b >> fs [closed_def])
 >> rw [StrongEQ_def]
 (*
 >> ‘FV P UNION FV Q SUBSET {X}’ by ASM_SET_TAC []
 >> Know ‘FV P UNION FV Q = {X}’
 >- (Suff ‘FV P UNION FV Q <> {}’ >- METIS_TAC [SUBSET_SING_CASES] \\
     CCONTR_TAC >> fs [closed_def])
 >> Rewr'
 *)
 >> EQ_TAC
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!fm. _ ==> STRONG_EQUIV (fm ' P) (fm ' Q)’
       (MP_TAC o (Q.SPEC ‘FEMPTY |+ (X,E)’)) \\
     simp [FDOM_FUPDATE] \\
     rw [FEMPTY_update_apply])
 (* stage work *)
 >> rpt STRIP_TAC





 >> qabbrev_tac ‘E = fm ' X’
 >> qabbrev_tac ‘fm' = FEMPTY |+ (X,E)’
 >> Know ‘fm = fm'’
 >- (rw [Abbr ‘fm'’, GSYM fmap_EQ_THM])
 >> Rewr'
 >> Know ‘fm' ' P = [E/X] P /\ fm' ' Q = [E/X] Q’
 >- (rw [Abbr ‘fm'’, FEMPTY_update_apply])
 >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> rw [Abbr ‘E’]
QED

Theorem StrongEQ_alt_subst' :
    !X P Q. FV P SUBSET {X} /\ FV Q SUBSET {X} ==>
           (StrongEQ P Q <=> !E. closed E ==> StrongEQ ([E/X] P) ([E/X] Q))
Proof
    rpt STRIP_TAC
 >> Know ‘StrongEQ P Q <=> !E. closed E ==> STRONG_EQUIV ([E/X] P) ([E/X] Q)’
 >- (MATCH_MP_TAC StrongEQ_alt_subst >> art [])
 >> Rewr'
 >> Suff ‘!E. closed E ==>
             (STRONG_EQUIV ([E/X] P) ([E/X] Q) <=> StrongEQ ([E/X] P) ([E/X] Q))’
 >- METIS_TAC []
 >> rw [closed_def]
 >> Suff ‘closed ([E/X] P) /\ closed ([E/X] Q)’
 >- rw [StrongEQ_alt_closed]
 >> rw [closed_def, FV_SUB]
 >> ASM_SET_TAC []
QED

Theorem StrongEQ_REFL[simp] :
    !E. StrongEQ E E
Proof
    rw [StrongEQ_def]
QED

Theorem StrongEQ_symmetric :
    symmetric StrongEQ
Proof
    rw [symmetric_def, StrongEQ_def]
 >> Cases_on ‘closed x /\ closed y’
 >- (fs [] >> PROVE_TAC [STRONG_EQUIV_SYM])
 >> ‘~(closed y /\ closed x)’ by PROVE_TAC []
 >> simp []
 >> EQ_TAC
 >> rpt STRIP_TAC (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC STRONG_EQUIV_SYM
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> SET_TAC []
QED

(* |- !x y. StrongEQ x y ==> StrongEQ y x *)
Theorem StrongEQ_SYM =
    StrongEQ_symmetric |> REWRITE_RULE [symmetric_def] |> iffLR

Theorem StrongEQ_SYM_EQ :
    !P Q. StrongEQ P Q <=> StrongEQ Q P
Proof
    rpt GEN_TAC >> EQ_TAC >> rw [StrongEQ_SYM]
QED

Theorem StrongEQ_TRANS :
    !E1 E2 E3. StrongEQ E1 E2 /\ StrongEQ E2 E3 ==> StrongEQ E1 E3
Proof
    rw [StrongEQ_def] (* 8 subgoals *)
 >> TRY (PROVE_TAC []) (* 5 goals left *)
 >> fs [closed_def]
 >| [ (* goal 1 (of 12) *)
      MATCH_MP_TAC STRONG_EQUIV_TRANS >> Q.EXISTS_TAC ‘E2’ >> art [],
      (* goal 2 (of 12) *)
      Q.PAT_X_ASSUM ‘!fm :string |-> 'a CCS. P’
        (MP_TAC o (Q.SPEC ‘fm’)) >> rw [] \\
     ‘fm ' E1 = E1 /\ fm ' E2 = E2’ by PROVE_TAC [ssub_value] >> fs [] \\
      MATCH_MP_TAC STRONG_EQUIV_TRANS >> Q.EXISTS_TAC ‘E2’ >> art [],
      (* goal 3 (of 12) *)
      Q.PAT_X_ASSUM ‘!fm :string |-> 'a CCS. P’
        (MP_TAC o (Q.SPEC ‘fm’)) >> rw [] \\
     ‘fm ' E2 = E2 /\ fm ' E3 = E3’ by PROVE_TAC [ssub_value] >> fs [] \\
      MATCH_MP_TAC STRONG_EQUIV_TRANS >> Q.EXISTS_TAC ‘E2’ >> art [],
      (* goal 4 (of 12) *)
      qabbrev_tac ‘fm :string |-> 'a CCS = FUN_FMAP (\e. nil) (FV E2)’ \\
     ‘FDOM fm = FV E2’ by rw [FDOM_FMAP, Abbr ‘fm’] \\
     ‘!x. x IN FV E2 ==> FV (fm ' x) = {}’ by rw [Abbr ‘fm’, FUN_FMAP_DEF] \\
      NTAC 2 (Q.PAT_X_ASSUM ‘!fm. FDOM fm = FV E2 /\ _ ==> _’
                (MP_TAC o (Q.SPEC ‘fm’))) \\
      RW_TAC std_ss [] \\
     ‘fm ' E1 = E1 /\ fm ' E3 = E3’ by PROVE_TAC [ssub_value] >> fs [] \\
      MATCH_MP_TAC STRONG_EQUIV_TRANS >> Q.EXISTS_TAC ‘fm ' E2’ >> art [],
      (* goal 5 (of 12) *)
      cheat 
QED

Theorem StrongEQ_subst_lemma :
    !E. FV E SUBSET {X} /\ closed P /\ closed Q /\ StrongEQ P Q ==>
        StrongEQ ([P/X] E) ([Q/X] E)
Proof
    HO_MATCH_MP_TAC CCS_induction
 >> Q.EXISTS_TAC ‘{X}’
 >> rw [] (* 6 subgoals *)
 >| [ (* goal 1 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX >> rw [],
      (* goal 2 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_SUM >> rw [],
      (* goal 3 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> rw [],
      (* goal 4 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> rw [],
      (* goal 5 (of 6) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> rw [],
      (* goal 6 (of 6) *)
      ALL_TAC ]
 (* stage work *)
 >> rename1 ‘Y <> X’
 >> 
    cheat
QED

(******************************************************************************)
(*                                                                            *)
(*                StrongEQ is preserved by recursive definition               *)
(*                                                                            *)
(******************************************************************************)


Theorem STRONG_EQUIV_PRESD_BY_REC_lemma :
    !G P Q X. FV P SUBSET {X} /\ FV Q SUBSET {X} /\ StrongEQ P Q /\
              FV G SUBSET {X} /\ CCS_Subst G (rec X P) X --u-> E1 ==>
         ?E2. CCS_Subst G (rec X Q) X --u-> E2 /\
              (STRONG_EQUIV O
               (\x y. ?G. FV G SUBSET {X} /\
                          x = CCS_Subst G (rec X P) X /\
                          y = CCS_Subst G (rec X Q) X) O STRONG_EQUIV) E1 E2
Proof
    HO_MATCH_MP_TAC simple_induction
 >> rw [] (* 8 subgoals *)
 >| [ (* goal 1 (of 8) *)
      fs [TRANS_REC_EQ] (* hard but possible *)\\
      cheat,
      (* goal 2 (of 8) *)
      FULL_SIMP_TAC std_ss [CCS_Subst_nil, NIL_NO_TRANS],
      (* goal 3 (of 8) *)
      FULL_SIMP_TAC std_ss [CCS_Subst_def, TRANS_PREFIX_EQ] \\
      rw [O_DEF] \\
      Q.EXISTS_TAC ‘CCS_Subst G (rec X Q) X’ >> rw [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC ‘CCS_Subst G (rec X P) X’ >> rw [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC ‘G’ >> art [],
      (* goal 4 (of 8): SUM *)
      cheat,
      (* goal 5 (of 8): PAR *)
      cheat, (* FULL_SIMP_TAC std_ss [TRANS_PAR_EQ] *)
      (* goal 6 (of 8):  *)
      cheat, (* FULL_SIMP_TAC std_ss [TRANS_RESTR_EQ] *)
      (* goal 7 (of 8) *)
      cheat, (* FULL_SIMP_TAC std_ss [TRANS_RELAB_EQ] *)
      (* goal 8 (of 8) *)
      rename1 ‘FV G DELETE Y SUBSET {X}’ \\
      Cases_on ‘Y = X’ (* trivial case *)
      >- (‘X # rec Y G’ by rw [FV_thm] \\
          gs [CCS_Subst_elim] \\
          Q.EXISTS_TAC ‘E1’ >> rw [O_DEF] \\
          Q.EXISTS_TAC ‘E1’ >> rw [STRONG_EQUIV_REFL] \\
          Q.EXISTS_TAC ‘E1’ >> rw [STRONG_EQUIV_REFL] \\
          Know ‘X # E1’
          >- (CCONTR_TAC >> fs [] \\
             ‘X IN FV (rec X G)’ by METIS_TAC [SUBSET_DEF, TRANS_FV] \\
              fs [FV_thm]) >> DISCH_TAC \\
          Q.EXISTS_TAC ‘E1’ >> ASM_SIMP_TAC std_ss [CCS_Subst_elim] \\
          MATCH_MP_TAC SUBSET_TRANS \\
          Q.EXISTS_TAC ‘FV (rec X G)’ \\
          CONJ_TAC >- (MATCH_MP_TAC TRANS_FV >> Q.EXISTS_TAC ‘u’ >> art []) \\
          rw [FV_thm]) \\
      Know ‘Y # rec X P /\ Y # rec X Q’
      >- (rw [FV_thm] >> PROVE_TAC [FV_SUBSET_lemma]) >> STRIP_TAC \\
      gs [CCS_Subst_rec] \\
      cheat ]
QED

(* Proposition 4.12 of [1, p.99] or Theorem 4.2 of [2, p.182]

   NOTE: The textbook requirement ‘FV P SUBSET {X} /\ FV Q SUBSET {X}’ is
   necessary, because: if P and Q contains unbounded ‘var s’ subterms other
   than ‘var X’, then these ‘var s’, together with ‘var X’ should all have
   no contributions in making transitions (see VAR_NO_TRANS), but further
   wrapping both P and Q with ‘rec X’ may additionally cause more transitions
   on the side with ‘var X’. In another words, let

   P = a..var X and Q = a..var Y

   clearly P ~ Q since they both have just one transitions (--a->). But then

   rec X P := rec X (a..var X)   and
   rec X Q := rec X (a..var Y)   (X <> Y)

   behave differently in bisimilarity tests: ‘rec X P’ has infinite many a-
   transitions, while ‘rec X Q’ still has just one a-transition, thus no more
   bisimilar.

   To prevent this issue, we must at least require that subterms like ‘var Y’
   do not occur, i.e.

      "P contains free variables at most X"  or  FV P SUBSET {X}.

   Note that it doesn't forbid bounded variables, e.g. rec Z (var Z + var X)
 *)
Theorem STRONG_EQUIV_PRESD_BY_REC :
    !X P Q. FV P SUBSET {X} /\ FV Q SUBSET {X} /\ StrongEQ P Q ==>
            STRONG_EQUIV (rec X P) (rec X Q)
Proof
    rpt STRIP_TAC
 (* applying STRONG_EQUIV_BY_BISIM_UPTO *)
 >> MATCH_MP_TAC STRONG_EQUIV_BY_BISIM_UPTO
 >> Q.EXISTS_TAC ‘\x y. ?G. FV G SUBSET {X} /\
                            x = CCS_Subst G (rec X P) X /\
                            y = CCS_Subst G (rec X Q) X’
 >> BETA_TAC
 >> reverse CONJ_TAC
 >- (Q.EXISTS_TAC ‘var X’ >> rw [FV_thm, CCS_Subst_var_fix])
 (* stage work *)
 >> rw [STRONG_BISIM_UPTO]
 (* applying STRONG_EQUIV_PRESD_BY_REC_lemma *)
 >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_REC_lemma >> art [])
 >> Know ‘!E1. (STRONG_EQUIV O (\x y. ?G. FV G SUBSET {X} /\
                                      x = CCS_Subst G (rec X P) X /\
                                      y = CCS_Subst G (rec X Q) X) O
                STRONG_EQUIV) E1 E2 <=>
               (STRONG_EQUIV O (\x y. ?G. FV G SUBSET {X} /\
                                      x = CCS_Subst G (rec X Q) X /\
                                      y = CCS_Subst G (rec X P) X) O
                STRONG_EQUIV) E2 E1’
 >- (rw [O_DEF] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘CCS_Subst G' (rec X P) X’ >> rw [STRONG_EQUIV_SYM] \\
       Q.EXISTS_TAC ‘CCS_Subst G' (rec X Q) X’ >> rw [STRONG_EQUIV_SYM] \\
       Q.EXISTS_TAC ‘G'’ >> art [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘CCS_Subst G' (rec X Q) X’ >> rw [STRONG_EQUIV_SYM] \\
       Q.EXISTS_TAC ‘CCS_Subst G' (rec X P) X’ >> rw [STRONG_EQUIV_SYM] \\
       Q.EXISTS_TAC ‘G'’ >> art [] ])
 >> Rewr'
 (* applying STRONG_EQUIV_PRESD_BY_REC_lemma again *)
 >> MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_REC_lemma
 >> rw [StrongEQ_SYM]
QED

Theorem StrongEQ_preserved_by_rec :
    !X P Q. FV P SUBSET {X} /\ FV Q SUBSET {X} /\ StrongEQ P Q ==>
            StrongEQ (rec X P) (rec X Q)
Proof
    rpt STRIP_TAC
 >> Know ‘StrongEQ (rec X P) (rec X Q) <=> STRONG_EQUIV (rec X P) (rec X Q)’
 >- (MATCH_MP_TAC StrongEQ_alt_closed \\
     rw [closed_def, FV_thm] >> ASM_SET_TAC [])
 >> Rewr'
 >> MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_REC >> art []
QED

*)

(* ONE HOLE CONTEXT (unused)

   NEW: added OH_CONTEXT9 (\t. rec v (c t)) -- Chun Tian, 18 dec 2023
 *)
Inductive OH_CONTEXT :
    (                        OH_CONTEXT (\t. t)) /\              (* OH_CONTEXT1 *)
    (!a c.  OH_CONTEXT c ==> OH_CONTEXT (\t. prefix a (c t))) /\ (* OH_CONTEXT2 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. sum (c t) x)) /\    (* OH_CONTEXT3 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. sum x (c t))) /\    (* OH_CONTEXT4 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. par (c t) x)) /\    (* OH_CONTEXT5 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. par x (c t))) /\    (* OH_CONTEXT6 *)
    (!L c.  OH_CONTEXT c ==> OH_CONTEXT (\t. restr L (c t))) /\  (* OH_CONTEXT7 *)
    (!rf c. OH_CONTEXT c ==> OH_CONTEXT (\t. relab (c t) rf)) /\ (* OH_CONTEXT8 *)
    (!v c.  OH_CONTEXT c ==> OH_CONTEXT (\t. rec v (c t)))       (* OH_CONTEXT9 *)
End

(* renamed following chap2Theory of the lambda example *)
Overload one_hole_context = “OH_CONTEXT”

val [OH_CONTEXT1, OH_CONTEXT2, OH_CONTEXT3, OH_CONTEXT4, OH_CONTEXT5, OH_CONTEXT6,
     OH_CONTEXT7, OH_CONTEXT8, OH_CONTEXT9] =
    map save_thm
        (combine (["OH_CONTEXT1", "OH_CONTEXT2", "OH_CONTEXT3", "OH_CONTEXT4",
                   "OH_CONTEXT5", "OH_CONTEXT6", "OH_CONTEXT7", "OH_CONTEXT8",
                   "OH_CONTEXT9"],
                  CONJUNCTS OH_CONTEXT_rules));

Theorem OH_CONTEXT_combin :
    !c1 c2. OH_CONTEXT c1 /\ OH_CONTEXT c2 ==> OH_CONTEXT (c1 o c2)
Proof
    rpt STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c1`, `c`)
 >> HO_MATCH_MP_TAC OH_CONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> REPEAT STRIP_TAC (* 8 sub-goals here *)
 >| [ FULL_SIMP_TAC std_ss [OH_CONTEXT2],
      FULL_SIMP_TAC std_ss [OH_CONTEXT3],
      FULL_SIMP_TAC std_ss [OH_CONTEXT4],
      FULL_SIMP_TAC std_ss [OH_CONTEXT5],
      FULL_SIMP_TAC std_ss [OH_CONTEXT6],
      FULL_SIMP_TAC std_ss [OH_CONTEXT7],
      FULL_SIMP_TAC std_ss [OH_CONTEXT8],
      FULL_SIMP_TAC std_ss [OH_CONTEXT9] ]
QED

val _ = export_theory ();
val _ = html_theory "Extended";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.
 [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer (2015).
 *)
