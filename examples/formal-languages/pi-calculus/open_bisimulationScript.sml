(* ========================================================================== *)
(* FILE          : open_bisimulationScript.sml                                *)
(* DESCRIPTION   : Open bisimulation for the pi-calculus with mismatch        *)
(*                                                                            *)
(* Copyright 2025  The Australian National University (Author: Chun Tian)     *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory set_relationTheory hurdUtils;

open nomsetTheory NEWLib pi_agentTheory;

val _ = new_theory "open_bisimulation";

(* some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

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

Theorem sc_swap :
    !x y r. (x,y) IN sc r <=> (y,x) IN sc r
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >> MATCH_MP_TAC (cj 2 sc_rules') >> art []
QED

Theorem sc_symmetric[simp] :
    symmetric (sc r) s
Proof
    rw [symmetric_def, Once sc_swap]
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

Theorem sc_empty[simp] :
    sc {} = {}
Proof
    rw [Once EXTENSION]
 >> Suff ‘!x. x IN sc {} ==> F’ >- rw []
 >> HO_MATCH_MP_TAC sc_ind'
 >> rw []
QED

Theorem sc_def :
    !r. sc r = {(x,y) | (x,y) IN r \/ (y,x) IN r}
Proof
    rw [Once EXTENSION]
 >> reverse EQ_TAC
 >- (rw [] >- (MATCH_MP_TAC (cj 1 sc_rules') >> art []) \\
     rw [Once sc_swap] \\
     MATCH_MP_TAC (cj 1 sc_rules') >> art [])
 >> qid_spec_tac ‘x’
 >> HO_MATCH_MP_TAC sc_ind' >> NTAC 2 (rw [])
QED

Theorem finite_sc :
    !r. FINITE r ==> FINITE (sc r)
Proof
    rw [sc_def]
 >> qmatch_abbrev_tac ‘FINITE s’
 >> Know ‘s = r UNION (IMAGE (\z. (SND z,FST z)) r)’
 >- (rw [Once EXTENSION, Abbr ‘s’] \\
     PairCases_on ‘x’ >> EQ_TAC >> NTAC 2 (rw []) \\
     DISJ2_TAC \\
     Q.EXISTS_TAC ‘(x1,x0)’ >> rw [])
 >> Rewr'
 >> rw [FINITE_UNION]
QED

(* NOTE: We fallback to “:(string # string) -> bool” for the need of permutation
   on pairs in the dist set.
 *)
Type dist[pp] = “:(string # string) -> bool”

(* NOTE: We use uncurried relation (HOL preferred) given in relationTheory *)
Definition distinction_def :
    distinction (D :dist) <=> FINITE D /\ symmetric D UNIV /\ irreflexive D UNIV
End

Overload FV = “domain :dist -> string set”
Overload "#" = “\v (D :dist). v NOTIN FV D”

Theorem domain_alt :
    !r. domain r = IMAGE FST r
Proof
    rw [Once EXTENSION, in_domain]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘(x,y)’ >> rw [])
 >> rename1 ‘z IN r’
 >> PairCases_on ‘z’
 >> Q.EXISTS_TAC ‘z1’ >> rw []
QED

(* |- !D. FV D = IMAGE FST D *)
Theorem FV_distinction =
        domain_alt |> INST_TYPE [alpha |-> “:string”, beta |-> “:string”]
                   |> Q.SPEC ‘D’ |> GEN_ALL

Theorem FV_distinction_alt :
    !D. distinction D ==> FV D = IMAGE SND D
Proof
    rw [distinction_def, domain_alt, symmetric_def]
 >> simp [Once EXTENSION, EXISTS_PROD]
QED

Theorem finite_domain[simp] :
    distinction D ==> FINITE (FV D)
Proof
    rw [distinction_def, domain_alt]
QED

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
Overload dpm[local] = “setpm (pair_pmact string_pmact string_pmact)”

Theorem distinction_dpm_lemma[local] :
    !pi d. distinction d ==> distinction (dpm pi d)
Proof
    rw [distinction_def]
 >- fs [symmetric_def]
 >> fs [irreflexive_def]
QED

Theorem distinction_dpm[simp] :
    distinction (dpm pi d) <=> distinction d
Proof
    reverse EQ_TAC
 >- rw [distinction_dpm_lemma]
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘REVERSE pi’, ‘dpm pi d’] distinction_dpm_lemma)
 >> simp []
QED

Theorem dpm_unchanged_lemma[local] :
    !D. FINITE D ==> !pi. DISJOINT (set (MAP FST pi)) (IMAGE FST D) /\
                          DISJOINT (set (MAP FST pi)) (IMAGE SND D) /\
                          DISJOINT (set (MAP SND pi)) (IMAGE FST D) /\
                          DISJOINT (set (MAP SND pi)) (IMAGE SND D) ==>
                          dpm pi D = D
Proof
    HO_MATCH_MP_TAC FINITE_INDUCT
 >> rw [pmact_INSERT]
 >> PairCases_on ‘e’ >> fs []
 >> Know ‘lswapstr pi e0 = e0’
 >- (MATCH_MP_TAC lswapstr_unchanged' >> art [])
 >> Rewr'
 >> Know ‘lswapstr pi e1 = e1’
 >- (MATCH_MP_TAC lswapstr_unchanged' >> art [])
 >> Rewr
QED

Theorem dpm_unchanged :
    !D pi. distinction D /\
           DISJOINT (set (MAP FST pi)) (FV D) /\
           DISJOINT (set (MAP SND pi)) (FV D) ==> dpm pi D = D
Proof
    rpt STRIP_TAC
 >> irule dpm_unchanged_lemma
 >> simp [GSYM FV_distinction, GSYM FV_distinction_alt]
 >> fs [distinction_def]
QED

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
       distinction D /\ b # D /\
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
    !P Q D. (P,Q,D) IN R ==>
    (* 0 *)
       distinction D /\
    (* 1 *)
      (!pi. (tpm pi P, tpm pi Q, dpm pi D) IN R) /\
    (* 2 *)
      (!D'. D SUBSET D' /\ distinction D' ==> (P,Q,D') IN R) /\
    (* 3a *)
      (!P'. DTRANS D P (TauR P') ==>
            ?Q'. DTRANS D Q (TauR Q') /\ (P',Q',D) IN R) /\
    (* 3b: enriched with ‘x # D /\ x # P’ *)
      (!a x P'. DTRANS D P (InputS (Name a) x P') /\ x # D /\ x # P /\ x # Q ==>
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

Theorem dist_simulation_id :
    dist_simulation {x | ?P D. x = (P,P,D) /\ distinction D}
Proof
    rw [dist_simulation_def]
 >> MATCH_MP_TAC distinction_union >> art []
 >> rw [distinction_def]
 >- (MATCH_MP_TAC finite_sc \\
     qmatch_abbrev_tac ‘FINITE s’ \\
     irule SUBSET_FINITE \\
     Q.EXISTS_TAC ‘{(b,y) | y | y IN FV P}’ \\
     qunabbrev_tac ‘s’ \\
     reverse CONJ_TAC >- rw [SUBSET_DEF] \\
     qmatch_abbrev_tac ‘FINITE s’ \\
     Know ‘s = IMAGE (\y. (b,y)) (FV P)’
     >- rw [Abbr ‘s’, Once EXTENSION] >> Rewr' \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [])
 >> MATCH_MP_TAC sc_irreflexive
 >> rw [irreflexive_def]
QED

Theorem dist_simulation_union :
    !R1 R2. dist_simulation R1 /\ dist_simulation R2 ==>
            dist_simulation (R1 UNION R2)
Proof
    rw [dist_simulation_def] (* 7+7 subgoals *)
 >| [ (* goal 1 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 2 (of 14) *)
      DISJ1_TAC \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 3 (of 14) *)
      DISJ1_TAC \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 4 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!P'. DTRANS D P (TauR P') ==> _’
        (MP_TAC o Q.SPEC ‘P'’) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 5 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!a x P'.
                       DTRANS D P (InputS (Name a) x P') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘a’, ‘x’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 6 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!a b P'.
                       DTRANS D P (FreeOutput (Name a) (Name b) P') ==> _’
        (MP_TAC o Q.SPECL [‘a’, ‘b’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 7 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!b x P'. DTRANS D P (BoundOutput (Name b) x P') ==> _’
        (MP_TAC o Q.SPECL [‘b’, ‘x’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 8 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 9 (of 14) *)
      DISJ2_TAC \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 10 (of 14) *)
      DISJ2_TAC \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [],
      (* goal 11 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!P'. DTRANS D P (TauR P') ==> _’
        (MP_TAC o Q.SPEC ‘P'’) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 12 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!a x P'.
                       DTRANS D P (InputS (Name a) x P') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘a’, ‘x’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 13 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!a b P'.
                       DTRANS D P (FreeOutput (Name a) (Name b) P') ==> _’
        (MP_TAC o Q.SPECL [‘a’, ‘b’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [],
      (* goal 14 (of 14) *)
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!b x P'. DTRANS D P (BoundOutput (Name b) x P') ==> _’
        (MP_TAC o Q.SPECL [‘b’, ‘x’, ‘P'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [] ]
QED

Theorem dist_simulation_imp_distinction :
    !R P Q D. dist_simulation R /\ (P,Q,D) IN R ==> distinction D
Proof
    rw [dist_simulation_def]
 >> FIRST_X_ASSUM drule >> rw []
QED

Theorem dist_simulation_open_distinction :
    !R P Q D D'. dist_simulation R /\ (P,Q,D) IN R /\ D SUBSET D' /\
                 distinction D' ==> (P,Q,D') IN R
Proof
    rw [dist_simulation_def]
 >> Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R ==> _’ drule >> rw []
QED

Definition dist_bisimulation_def :
    dist_bisimulation (R :(pi # pi # dist) set) <=>
    dist_simulation R /\ dist_simulation {(Q,P,D) | (P,Q,D) IN R}
End

Definition dist_bisimilar :
    dist_bisimilar P Q D <=> ?R. dist_bisimulation R /\ (P,Q,D) IN R
End

(* |- !P Q D.
        dist_bisimilar P Q D <=>
        ?R. (dist_simulation R /\ dist_simulation {(Q,P,D) | (P,Q,D) IN R}) /\
            (P,Q,D) IN R
 *)
Theorem dist_bisimilar_def =
        dist_bisimilar |> REWRITE_RULE [dist_bisimulation_def]

Theorem dist_bisimilar_imp_distinction :
    !P Q D. dist_bisimilar P Q D ==> distinction D
Proof
    rw [dist_bisimilar_def, dist_simulation_def]
 >> FIRST_X_ASSUM drule >> rw []
QED

Theorem dist_bisimilar_reflexive :
    !P D. distinction D ==> dist_bisimilar P P D
Proof
    rw [dist_bisimilar_def]
 >> Q.EXISTS_TAC ‘{x | ?P D. x = (P,P,D) /\ distinction D}’
 >> simp [dist_simulation_id]
 >> qmatch_abbrev_tac ‘dist_simulation R’
 >> Suff ‘R = {x | (?P D. x = (P,P,D) /\ distinction D)}’
 >- rw [dist_simulation_id]
 >> rw [Abbr ‘R’, Once EXTENSION]
QED

Theorem dist_bisimilar_symmetric :
    !P Q D. dist_bisimilar P Q D ==> dist_bisimilar Q P D
Proof
    rw [dist_bisimilar_def]
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
 >> PairCases_on ‘x’ (* this asserts (x0,x1,x2) *)
 >> rename1 ‘(P',Q',D') IN R’
 >> qexistsl_tac [‘P'’, ‘Q'’, ‘D'’] >> simp []
QED

Theorem dist_bisimilar_transitive :
    !P1 P2 P3 D. dist_bisimilar P1 P2 D /\ dist_bisimilar P2 P3 D ==>
                 dist_bisimilar P1 P3 D
Proof
    rw [dist_bisimilar_def]
 >> ‘distinction D’ by PROVE_TAC [dist_simulation_imp_distinction]
 >> Q.EXISTS_TAC ‘{e | ?x y z d. e = (x,z,d) /\ (x,y,d) IN R /\ (y,z,d) IN R'}’
 >> simp []
 >> reverse CONJ_TAC >- (Q.EXISTS_TAC ‘P2’ >> art [])
 >> rw [dist_simulation_def, distinction_dpm] (* 7+7 subgoals *)
 >| [ (* goal 1 (of 14) *)
      MATCH_MP_TAC dist_simulation_imp_distinction \\
      qexistsl_tac [‘R’, ‘P’, ‘y’] >> art [],
      (* goal 2 (of 14) *)
      Q.EXISTS_TAC ‘tpm pi y’ >> CONJ_TAC >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        Q.PAT_X_ASSUM ‘dist_simulation R’
          (MP_TAC o REWRITE_RULE [dist_simulation_def]) \\
        DISCH_THEN (STRIP_ASSUME_TAC o Q.SPECL [‘P’, ‘y’, ‘D'’]) \\
        simp [distinction_dpm],
        (* goal 2.2 (of 2) *)
        Q.PAT_X_ASSUM ‘dist_simulation R'’
          (MP_TAC o REWRITE_RULE [dist_simulation_def]) \\
        DISCH_THEN (STRIP_ASSUME_TAC o Q.SPECL [‘y’, ‘Q’, ‘D'’]) \\
        simp [distinction_dpm] ],
      (* goal 3 (of 14) *)
      Q.EXISTS_TAC ‘y’ \\
      CONJ_TAC \\ (* 2 subgoals, same tactics *)
      MATCH_MP_TAC dist_simulation_open_distinction \\
      Q.EXISTS_TAC ‘D'’ >> art [],
      (* goal 4 (of 14) : DTRANS D' P    (TauR P')
                                    | R        |
                                    y    (TauR y')
                                    | R'       |
                                    Q    (TauR Q')
       *)
      Q.PAT_X_ASSUM ‘dist_simulation R’ MP_TAC >> rw [dist_simulation_def] \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘y’, ‘D'’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!P'. DTRANS D' P (TauR P') ==> _’
        (MP_TAC o Q.SPEC ‘P'’) >> rw [] >> rename1 ‘DTRANS D' y (TauR y')’ \\
      Q.PAT_X_ASSUM ‘dist_simulation R'’ MP_TAC >> rw [dist_simulation_def] \\
      Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R' ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘Q’, ‘D'’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘!P'. DTRANS D' y (TauR P') ==> _’
        (MP_TAC o Q.SPEC ‘y'’) >> rw [] >> rename1 ‘DTRANS D' Q (TauR Q')’ \\
      Q.EXISTS_TAC ‘Q'’ >> art [] \\
      Q.EXISTS_TAC ‘y'’ >> art [],
      (* goal 5 (of 14): DTRANS D' P (InputS (Name a) x P')
                                   |   R              | |
                                   P                  z P''
                                   |   R              | |
                                   y (InputS (Name a) z y')
                                   |   R'             | |
                                   Q (InputS (Name a) z Q')
                                   |                  | |
                                   Q                  x Q''
       *)
      Q.PAT_X_ASSUM ‘dist_simulation R’
        (STRIP_ASSUME_TAC o SIMP_RULE (bool_ss ++ DNF_ss) [dist_simulation_def]) \\
     ‘distinction D'’ by PROVE_TAC [] \\
   (* applying NEW_TAC *)
      qabbrev_tac ‘X = {x} UNION FV D' UNION FV y UNION FV P UNION FV Q UNION FV P'’ \\
     ‘FINITE X’ by rw [Abbr ‘X’] \\
      Q_TAC (NEW_TAC "z") ‘X’ \\
      Q.PAT_X_ASSUM ‘FINITE X’ K_TAC >> fs [Abbr ‘X’] \\
   (* applying InputS_tpm_ALPHA *)
      Know ‘InputS (Name a) x P' = InputS (Name a) z (tpm [(z,x)] P')’
      >- (MATCH_MP_TAC InputS_tpm_ALPHA >> art []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘P'' = tpm [(z,x)] P'’ \\
      Q.PAT_X_ASSUM ‘!P Q D a x P'. (P,Q,D) IN R ==>
                                       DTRANS D P (InputS (Name a) x P') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘y’, ‘D'’, ‘a’, ‘z’, ‘P''’]) >> rw [] \\
      rename1 ‘DTRANS D' y (InputS (Name a) z y')’ \\
   (* stage work *)
      Q.PAT_X_ASSUM ‘dist_simulation R'’
        (STRIP_ASSUME_TAC o SIMP_RULE (bool_ss ++ DNF_ss) [dist_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!P Q D a x P'. (P,Q,D) IN R' ==>
                                       DTRANS D P (InputS (Name a) x P') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘Q’, ‘D'’, ‘a’, ‘z’, ‘y'’]) >> rw [] \\
      Know ‘InputS (Name a) z Q' = InputS (Name a) x (tpm [(x,z)] Q')’
      >- (MATCH_MP_TAC InputS_tpm_ALPHA \\
          cheat) (* possible *) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘Q'' = tpm [(x,z)] Q'’ \\
      Q.EXISTS_TAC ‘Q''’ >> art [] \\
     ‘P' = tpm [(z,x)] P''’ by rw [Abbr ‘P''’] >> POP_ORW \\
     ‘tpm [(z,x)] P'' = tpm [(x,z)] P''’ by rw [Once pmact_flip_args] \\
      POP_ORW \\
      Q.EXISTS_TAC ‘tpm [(x,z)] y'’ >> simp [Abbr ‘Q''’] \\
      Suff ‘D' = dpm [(x,z)] D'’ >- (Rewr' >> simp []) \\
      ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
      MATCH_MP_TAC dpm_unchanged >> simp [],
      (* goal 6 (of 14) *)
      cheat,
      (* goal 7 (of 14) *)
      cheat,
      (* goal 8 (of 14) *)
      cheat,
      (* goal 9 (of 14) *)
      cheat,
      (* goal 10 (of 14) *)
      cheat,
      (* goal 11 (of 14) *)
      cheat,
      (* goal 12 (of 14) *)
      cheat,
      (* goal 13 (of 14) *)
      cheat,
      (* goal 14 (of 14) *)
      cheat ]
QED

val _ = export_theory ();
val _ = html_theory "open_bisimulation";
