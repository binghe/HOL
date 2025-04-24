(* ========================================================================== *)
(* FILE          : open_bisimulationScript.sml                                *)
(* DESCRIPTION   : Open Bisimulation for pi-calculus                          *)
(*                                                                            *)
(* Copyright 2025  The Australian National University (Author: Chun Tian)     *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory set_relationTheory hurdUtils;

open nomsetTheory pi_agentTheory;

val _ = new_theory "open_bisimulation";

(* ----------------------------------------------------------------------
   Pi-calculus as a nominal datatype in HOL4

   HOL4 syntax ('free and 'bound are special type variables (alias of string)

   Nominal_datatype :

           name = Name 'free

           pi   = Nil                      (* 0 *)
                | Tau pi                   (* tau.P *)
                | Input name 'bound pi     (* a(x).P *)
                | Output name name pi      (* {a}b.P *)
                | Match name name pi       (* [a == b] P *)
                | Mismatch name name pi    (* [a <> b] P *)
                | Sum pi pi                (* P + Q *)
                | Par pi pi                (* P | Q *)
                | Res 'bound pi            (* nu x. P *)

       residual = TauR pi
                | InputS name 'bound pi
                | FreeOutput name name pi
                | BoundOutput name 'bound pi
   End

   NOTE: Replication ("!") is not supported.
   ---------------------------------------------------------------------- *)

(* NOTE: We fallback to “:(string # string) -> bool” for the need of permutation
   on pairs in the dist set.
 *)
Type dist[pp] = “:(string # string) -> bool”

(* TODO: move to set_relationTheory *)
Definition symmetric_def :
    symmetric r s <=> !x y. x IN s /\ y IN s ==> ((x,y) IN r <=> (y,x) IN r)
End

Theorem symmetric_union :
    !r1 r2 s. symmetric r1 s /\ symmetric r2 s ==> symmetric (r1 UNION r2) s
Proof
    rw [symmetric_def]
QED

Theorem irreflexive_union :
    !r1 r2 s. irreflexive r1 s /\ irreflexive r2 s ==> irreflexive (r1 UNION r2) s
Proof
    rw [irreflexive_def]
QED

(* TODO: move to set_relationTheory. The idea is following "tc" *)
Inductive sc :
    (!x y. r (x,y) ==> sc r (x,y)) /\
    (!x y. sc r (x,y) ==> sc r (y,x))
End

Theorem sc_rules' :
    !r. (!x y. (x,y) IN r ==> (x,y) IN sc r) /\
         !x y. (x,y) IN sc r ==> (y,x) IN sc r
Proof
    simp [IN_APP]
 >> METIS_TAC [sc_rules]
QED

Theorem sc_cases' :
    !r a0. a0 IN sc r <=> (?x y. a0 = (x,y) /\ (x,y) IN r) \/
                        ?x y. a0 = (y,x) /\ (x,y) IN sc r
Proof
    simp [IN_APP]
 >> METIS_TAC [sc_cases]
QED

Theorem sc_ind' :
    !P r.
        (!x y. (x,y) IN r ==> P (x,y)) /\ (!x y. P (x,y) ==> P (y,x)) ==>
        !x. x IN sc r ==> P x
Proof
    simp [IN_APP]
 >> METIS_TAC [sc_ind]
QED

Theorem sc_thm :
    !x y r. (x,y) IN sc r <=> (y,x) IN sc r
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >> MATCH_MP_TAC (cj 2 sc_rules') >> art []
QED

Theorem sc_symmetric[simp] :
    symmetric (sc r) s
Proof
    rw [symmetric_def, Once sc_thm]
QED

Theorem sc_irreflexive_lemma[local] :
    !x r. (x,x) NOTIN r ==> (x,x) NOTIN sc r
Proof
    rpt GEN_TAC
 >> simp [Once MONO_NOT_EQ]
 >> Suff ‘!z. z IN sc r ==> FST z = SND z ==> z IN r’ >- rw []
 >> HO_MATCH_MP_TAC sc_ind' >> rw []
QED

Theorem sc_irreflexive :
    !r s. irreflexive r s ==> irreflexive (sc r) s
Proof
    rw [irreflexive_def]
 >> MATCH_MP_TAC sc_irreflexive_lemma
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* NOTE: We use uncurried relation (HOL preferred) given in relationTheory *)
Definition distinction_def :
    distinction (D :dist) <=> symmetric D UNIV /\ irreflexive D UNIV
End

Theorem distinction_empty[simp] :
    distinction {}
Proof
    rw [distinction_def, symmetric_def, irreflexive_def]
QED

Theorem distinction_union :
    !D1 D2. distinction D1 /\ distinction D2 ==> distinction (D1 UNION D2)
Proof
    rw [distinction_def]
 >- (MATCH_MP_TAC symmetric_union >> art [])
 >> MATCH_MP_TAC irreflexive_union >> art []
QED

(* NOTE: This is permutation operation on distinction *)
Definition dpm_def :
    dpm pi (D :dist) = IMAGE (pairpm string_pmact string_pmact pi) D
End

(* The original open transition relation *)
Inductive TRANS :
[TAU]
    !P.       TRANS (Tau P) (TauR P)
[INPUT]
    !a x P.   x <> a ==> TRANS (Input (Name a) x P) (InputS (Name a) x P)
[OUTPUT]
    !a b P.   TRANS (Output (Name a) (Name b) P) (FreeOutput (Name a) (Name b) P)
[MATCH]
    !P Rs b.   TRANS P Rs ==> TRANS (Match (Name b) (Name b) P) Rs
[MISMACH]
    !P Rs a b. TRANS P Rs /\ a <> b ==> TRANS (Mismatch (Name a) (Name b) P) Rs

[OPEN]
    !P P' a b. TRANS P (FreeOutput (Name a) (Name b) P') /\ a <> b ==>
               TRANS (Res b P) (BoundOutput (Name a) b P')
[SUM1]
    !P Q Rs. TRANS P Rs ==> TRANS (Sum P Q) Rs
[SUM2]
    !P Q Rs. TRANS Q Rs ==> TRANS (Sum P Q) Rs

[PAR1_I]
    !P P' Q a x.
       TRANS P (InputS (Name a) x P') /\ x # P /\ x # Q /\ x <> a ==>
       TRANS (Par P Q) (InputS (Name a) x (Par P' Q))
[PAR1_BO]
    !P P' Q a x.
       TRANS P (BoundOutput (Name a) x P') /\ x # P /\ x # Q /\ x <> a ==>
       TRANS (Par P Q) (BoundOutput (Name a) x (Par P' Q))
[PAR1_FO]
    !P P' Q a b.
       TRANS P (FreeOutput (Name a) (Name b) P') ==>
       TRANS (Par P Q) (FreeOutput (Name a) (Name b) (Par P' Q))
[PAR1_T]
    !P P' Q. TRANS P (TauR P') ==> TRANS (Par P Q) (TauR (Par P' Q))

[PAR2_I]
    !P Q Q' a x.
       TRANS Q (InputS (Name a) x Q') /\ x # Q /\ x # P /\ x <> a ==>
       TRANS (Par P Q) (InputS (Name a) x (Par P Q'))
[PAR2_BO]
    !P Q Q' a x.
       TRANS Q (BoundOutput (Name a) x Q') /\ x # Q /\ x # P /\ x <> a ==>
       TRANS (Par P Q) (BoundOutput (Name a) x (Par P Q'))
[PAR2_FO]
    !P Q Q' a b.
       TRANS Q (FreeOutput (Name a) (Name b) Q') ==>
       TRANS (Par P Q) (FreeOutput (Name a) (Name b) (Par P Q'))
[PAR2_T]
    !P Q Q'. TRANS Q (TauR Q') ==> TRANS (Par P Q) (TauR (Par P Q'))

[COMM1] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a b x.
       TRANS P (InputS (Name a) x P') /\ TRANS Q (FreeOutput (Name a) (Name b) Q') /\
       x # P /\ x # Q /\ x <> a /\ x <> b /\ x # Q' ==>
       TRANS (Par P Q) (TauR (Par (tpm [(x,b)] P') Q'))
[COMM2] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a b x.
       TRANS P (FreeOutput (Name a) (Name b) P') /\ TRANS Q (InputS (Name a) x Q') /\
       x # Q /\ x # P /\ x <> a /\ x <> b /\ x # P' ==>
       TRANS (Par P Q) (TauR (Par P' (tpm [(x,b)] Q')))
[CLOSE1] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a x y.
       TRANS P (InputS (Name a) x P') /\
       TRANS Q (BoundOutput (Name a) y Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # Q' /\ y <> a /\ y # P' /\ x <> y ==>
       TRANS (Par P Q) (TauR (Res y (Par (tpm [(x,y)] P') Q')))
[CLOSE2] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a x y.
       TRANS P (BoundOutput (Name a) y P') /\
       TRANS Q (InputS (Name a) x Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # P' /\ y <> a /\ y # Q' /\ x <> y ==>
       TRANS (Par P Q) (TauR (Res y (Par P' (tpm [(x,y)] Q'))))
[RES_I]
    !P P' a x y.
       TRANS P (InputS (Name a) x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       TRANS (Res y P) (InputS (Name a) x (Res y P'))
[RES_BO]
    !P P' a x y.
       TRANS P (BoundOutput (Name a) x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       TRANS (Res y P) (BoundOutput (Name a) x (Res y P'))
[RES_FO]
    !P P' a b y.
       TRANS P (FreeOutput (Name a) (Name b) P') /\
       y <> a /\ y <> b ==>
       TRANS (Res y P) (FreeOutput (Name a) (Name b) (Res y P'))
[RES_T]
    !P P' y.
       TRANS P (TauR P') ==> TRANS (Res y P) (TauR (Res y P'))
End

(* Open transition relation w.r.t. distinction *)
Inductive DTRANS :
[DTAU]
    !D P. DTRANS (D :dist) (Tau P) (TauR P)
[DINPUT]
    !D a x P. x <> a ==> DTRANS D (Input (Name a) x P) (InputS (Name a) x P)
[DOUTPUT]
    !D a b P. DTRANS D (Output (Name a) (Name b) P)
                       (FreeOutput (Name a) (Name b) P)
[DMATCH]
    !D P Rs b. DTRANS D P Rs ==> DTRANS D (Match (Name b) (Name b) P) Rs
[DMISMACH]
    !D P Rs a b.
       distinction D /\ (a,b) IN D /\ DTRANS D P Rs ==>
       DTRANS D (Mismatch (Name a) (Name b) P) Rs

[DOPEN]
    !D D' P P' a b.
    (* begin extra antecedents *)
       distinction D /\ b NOTIN (domain D) /\
       D' = D UNION sc {(a,s) | s IN FV (Res b P)} /\
    (* end extra antecedents *)
       DTRANS D' P (FreeOutput (Name a) (Name b) P') /\ a <> b ==>
       DTRANS D (Res b P) (BoundOutput (Name a) b P')
[DSUM1]
    !D P Q Rs. DTRANS D P Rs ==> DTRANS D (Sum P Q) Rs
[DSUM2]
    !D P Q Rs. DTRANS D Q Rs ==> DTRANS D (Sum P Q) Rs

[DPAR1_I]
    !D P P' Q a x.
       DTRANS D P (InputS (Name a) x P') /\ x # P /\ x # Q /\ x <> a ==>
       DTRANS D (Par P Q) (InputS (Name a) x (Par P' Q))
[DPAR1_BO]
    !D P P' Q a x.
       DTRANS D P (BoundOutput (Name a) x P') /\ x # P /\ x # Q /\ x <> a ==>
       DTRANS D (Par P Q) (BoundOutput (Name a) x (Par P' Q))
[DPAR1_FO]
    !D P P' Q a b.
       DTRANS D P (FreeOutput (Name a) (Name b) P') ==>
       DTRANS D (Par P Q) (FreeOutput (Name a) (Name b) (Par P' Q))
[DPAR1_T]
    !D P P' Q. DTRANS D P (TauR P') ==> DTRANS D (Par P Q) (TauR (Par P' Q))

[DPAR2_I]
    !D P Q Q' a x.
       DTRANS D Q (InputS (Name a) x Q') /\ x # Q /\ x # P /\ x <> a ==>
       DTRANS D (Par P Q) (InputS (Name a) x (Par P Q'))
[DPAR2_BO]
    !D P Q Q' a x.
       DTRANS D Q (BoundOutput (Name a) x Q') /\ x # Q /\ x # P /\ x <> a ==>
       DTRANS D (Par P Q) (BoundOutput (Name a) x (Par P Q'))
[DPAR2_FO]
    !D P Q Q' a b.
       DTRANS D Q (FreeOutput (Name a) (Name b) Q') ==>
       DTRANS D (Par P Q) (FreeOutput (Name a) (Name b) (Par P Q'))
[DPAR2_T]
    !D P Q Q'. DTRANS D Q (TauR Q') ==> DTRANS D (Par P Q) (TauR (Par P Q'))

[DCOMM1] (* TODO: tpm should change to SUB *)
    !D P P' Q Q' a b x.
       DTRANS D P (InputS (Name a) x P') /\
       DTRANS D Q (FreeOutput (Name a) (Name b) Q') /\
       x # P /\ x # Q /\ x <> a /\ x <> b /\ x # Q' ==>
       DTRANS D (Par P Q) (TauR (Par (tpm [(x,b)] P') Q'))
[DCOMM2] (* TODO: tpm should change to SUB *)
    !D P P' Q Q' a b x.
       DTRANS D P (FreeOutput (Name a) (Name b) P') /\
       DTRANS D Q (InputS (Name a) x Q') /\
       x # Q /\ x # P /\ x <> a /\ x <> b /\ x # P' ==>
       DTRANS D (Par P Q) (TauR (Par P' (tpm [(x,b)] Q')))
[DCLOSE1] (* TODO: tpm should change to SUB *)
    !D P P' Q Q' a x y.
       DTRANS D P (InputS (Name a) x P') /\
       DTRANS D Q (BoundOutput (Name a) y Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # Q' /\ y <> a /\ y # P' /\ x <> y ==>
       DTRANS D (Par P Q) (TauR (Res y (Par (tpm [(x,y)] P') Q')))
[DCLOSE2] (* TODO: tpm should change to SUB *)
    !D P P' Q Q' a x y.
       DTRANS D P (BoundOutput (Name a) y P') /\
       DTRANS D Q (InputS (Name a) x Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # P' /\ y <> a /\ y # Q' /\ x <> y ==>
       DTRANS D (Par P Q) (TauR (Res y (Par P' (tpm [(x,y)] Q'))))

[DRES_I]
    !D D' P P' a x y.
    (* begin extra antecedents *)
       distinction D /\
       D' = D UNION sc {(y,s) | s IN FV (Res y P)} /\
    (* end extra antecedents *)
       DTRANS D' P (InputS (Name a) x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       DTRANS D (Res y P) (InputS (Name a) x (Res y P'))
[DRES_BO]
    !D D' P P' a x y.
    (* begin extra antecedents *)
       distinction D /\
       D' = D UNION sc {(y,s) | s IN FV (Res y P)} /\
    (* end extra antecedents *)
       DTRANS D' P (BoundOutput (Name a) x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       DTRANS D (Res y P) (BoundOutput (Name a) x (Res y P'))
[DRES_FO]
    !D D' P P' a b y.
    (* begin extra antecedents *)
       distinction D /\
       D' = D UNION sc {(y,s) | s IN FV (Res y P)} /\
    (* end extra antecedents *)
       DTRANS D' P (FreeOutput (Name a) (Name b) P') /\
       y <> a /\ y <> b ==>
       DTRANS D (Res y P) (FreeOutput (Name a) (Name b) (Res y P'))
[DRES_T]
    !D D' P P' y.
    (* begin extra antecedents *)
       distinction D /\
       D' = D UNION sc {(y,s) | s | s IN FV (Res y P)} /\
    (* end extra antecedents *)
       DTRANS D' P (TauR P') ==> DTRANS D (Res y P) (TauR (Res y P'))
End

(* NOTE: "simulation" is a property of 3-way relation R as tuples (P, Q, D), where
   P and Q are pi-agents, D is a distinction.
 *)
Definition dist_simulation_def :
    dist_simulation (R :(pi # pi # dist) set) <=>
    !P Q D. (P,Q,D) IN R /\ distinction D ==>
    (* 1 *)
      (!pi. (tpm pi P, tpm pi Q, dpm pi D) IN R) /\
    (* 2 *)
      (!D'. D SUBSET D' /\ distinction D' ==> (P,Q,D') IN R) /\
    (* 3a *)
      (!P'. DTRANS D P (TauR P') ==>
            ?Q'. DTRANS D Q (TauR Q') /\ (P',Q',D) IN R) /\
    (* 3b *)
      (!a x P'. DTRANS D P (InputS (Name a) x P') /\ x # Q ==>
                ?Q'. DTRANS D Q (InputS (Name a) x Q') /\ (P',Q',D) IN R) /\
    (* 3c *)
      (!a b P'. DTRANS D P (FreeOutput (Name a) (Name b) P') ==>
                ?Q'. DTRANS D Q (FreeOutput (Name a) (Name b) Q') /\
                    (P',Q',D) IN R) /\
    (* 4 *)
      (!b x P'. DTRANS D P (BoundOutput (Name b) x P') ==>
                ?Q' D'. DTRANS D Q (BoundOutput (Name b) x Q') /\
                        D' = D UNION sc {(b, x) | x | x IN FV (Res b Q)} /\
                       (P',Q',D') IN R)
End

Theorem dist_simulation_univ :
    dist_simulation {x | ?P D. x = (P,P,D) /\ distinction D}
Proof
    rw [dist_simulation_def]
 (* distinction (dpm pi D) *)
 >- (fs [distinction_def] \\
     reverse CONJ_TAC (* irreflexive *)
     >- (fs [irreflexive_def] \\
         rw [dpm_def] \\
         rename1 ‘(x,x) = pairpm string_pmact string_pmact pi z’ \\
         Cases_on ‘z’ >> fs [pairpm_thm] \\
         POP_ASSUM (fs o wrap)) \\
  (* symmetric *)
     fs [symmetric_def] \\
     rw [dpm_def] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘(lswapstr (REVERSE pi) y,lswapstr (REVERSE pi) x)’ \\
       simp [pairpm_thm] \\
       rename1 ‘(x,y) = pairpm string_pmact string_pmact pi z’ \\
       Cases_on ‘z’ >> fs [pairpm_thm],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘(lswapstr (REVERSE pi) x,lswapstr (REVERSE pi) y)’ \\
       simp [pairpm_thm] \\
       rename1 ‘(y,x) = pairpm string_pmact string_pmact pi z’ \\
       Cases_on ‘z’ >> fs [pairpm_thm] ])
 (* stage work *)
 >> fs [distinction_def]
 >> reverse CONJ_TAC (* irreflexive *)
 >- (MATCH_MP_TAC irreflexive_union >> art [] \\
     MATCH_MP_TAC sc_irreflexive \\
     rw [irreflexive_def])
 (* symmetric *)
 >> MATCH_MP_TAC symmetric_union >> simp []
QED

Theorem dist_simulation_union :
    !R1 R2. dist_simulation R1 /\ dist_simulation R2 ==>
            dist_simulation (R1 UNION R2)
Proof
    rw [dist_simulation_def] (* 6+6 subgoals *)
 >| [ (* goal 1 (of 12) *)
      DISJ1_TAC \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 2 (of 12) *)
      DISJ1_TAC \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 3 (of 12) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!P'. DTRANS D P (TauR P') ==> _’
        (MP_TAC o Q.SPEC ‘P'’) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 4 (of 12) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!a x P'.
                       DTRANS D P (InputS (Name a) x P') /\ x # Q ==> _’
        (MP_TAC o Q.SPECL [‘a’, ‘x’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 5 (of 12) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!a b P'.
                       DTRANS D P (FreeOutput (Name a) (Name b) P') ==> _’
        (MP_TAC o Q.SPECL [‘a’, ‘b’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 6 (of 12) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!b x P'. DTRANS D P (BoundOutput (Name b) x P') ==> _’
        (MP_TAC o Q.SPECL [‘b’, ‘x’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 7 (of 12) *)
      DISJ2_TAC \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 8 (of 12) *)
      DISJ2_TAC \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 9 (of 12) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!P'. DTRANS D P (TauR P') ==> _’
        (MP_TAC o Q.SPEC ‘P'’) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 10 (of 12) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!a x P'.
                       DTRANS D P (InputS (Name a) x P') /\ x # Q ==> _’
        (MP_TAC o Q.SPECL [‘a’, ‘x’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 11 (of 12) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!a b P'.
                       DTRANS D P (FreeOutput (Name a) (Name b) P') ==> _’
        (MP_TAC o Q.SPECL [‘a’, ‘b’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 12 (of 12) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 /\ distinction D ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!b x P'. DTRANS D P (BoundOutput (Name b) x P') ==> _’
        (MP_TAC o Q.SPECL [‘b’, ‘x’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [] ]
QED

Definition dist_bisimulation_def :
    dist_bisimulation (R :(pi # pi # dist) set) <=>
    dist_simulation R /\ dist_simulation {(Q,P,D) | (P,Q,D) IN R}
End

Definition dist_bisimilar_def :
    dist_bisimilar P Q D <=> ?R. dist_bisimulation R /\ (P,Q,D) IN R
End

Theorem dist_bisimilar_reflexive :
    !P D. distinction D ==> dist_bisimilar P P D
Proof
    rw [dist_bisimilar_def, dist_bisimulation_def]
 >> Q.EXISTS_TAC ‘{x | ?P D. x = (P,P,D) /\ distinction D}’
 >> simp [dist_simulation_univ]
 >> qmatch_abbrev_tac ‘dist_simulation R’
 >> Suff ‘R = {x | (?P D. x = (P,P,D) /\ distinction D)}’
 >- rw [dist_simulation_univ]
 >> rw [Abbr ‘R’, Once EXTENSION]
QED

Theorem dist_bisimilar_symmetric :
    !P Q D. dist_bisimilar P Q D ==> dist_bisimilar Q P D
Proof
    rw [dist_bisimilar_def, dist_bisimulation_def]
 >> qabbrev_tac ‘R' = {(Q,P,D) | (P,Q,D) IN R}’
 >> Q.EXISTS_TAC ‘R UNION R'’
 >> reverse CONJ_TAC
 >- (simp [] \\
     DISJ2_TAC >> rw [Abbr ‘R'’])
 >> CONJ_TAC
 >- (MATCH_MP_TAC dist_simulation_union >> art [])
 >> qmatch_abbrev_tac ‘dist_simulation R2’
 >> Suff ‘R2 = R UNION R'’
 >- (Rewr' \\
     MATCH_MP_TAC dist_simulation_union >> art [])
 >> rw [Once EXTENSION, Abbr ‘R2’, Abbr ‘R'’]
 >> EQ_TAC >> rw []
 >> Cases_on ‘x’
 >> Cases_on ‘r’
 >> rename1 ‘(P',Q',D') IN R’
 >> qexistsl_tac [‘P'’, ‘Q'’, ‘D'’] >> simp []
QED

(* TODO
Theorem dist_bisimilar_transitive :
    !P1 P2 P3 D. dist_bisimilar P1 P2 D /\ dist_bisimilar P2 P3 D ==>
                 dist_bisimilar P1 P3 D
Proof
    cheat
QED
 *)

val _ = export_theory ();
val _ = html_theory "open_bisimulation";
