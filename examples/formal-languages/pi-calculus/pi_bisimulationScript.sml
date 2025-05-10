(* ========================================================================== *)
(* FILE          : pi_bisimulationScript.sml                                  *)
(* DESCRIPTION   : bisimulation for the pi-calculus (with mismatch)           *)
(*                                                                            *)
(* Copyright 2025  The Australian National University (Author: Chun Tian)     *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory set_relationTheory hurdUtils;

open nomsetTheory NEWLib pi_agentTheory;

val _ = new_theory "pi_bisimulation";

(* some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

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

(*
Definition simulation_def :
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
      (!a x P'. DTRANS D P (InputS (Name a) x P') /\
                x # D /\ x # P /\ x # Q ==>
               ?Q'. DTRANS D Q (InputS (Name a) x Q') /\ (P',Q',D) IN R) /\
    (* 3c *)
      (!a b P'. DTRANS D P (FreeOutput (Name a) (Name b) P') ==>
               ?Q'. DTRANS D Q (FreeOutput (Name a) (Name b) Q') /\
                   (P',Q',D) IN R) /\
    (* 4 *)
      (!b x P'. DTRANS D P (BoundOutput (Name b) x P') /\
                x # D /\ x # P /\ x # Q ==>
                ?Q' D'. DTRANS D Q (BoundOutput (Name b) x Q') /\
                        D' = D UNION sc {(b, x) | x | x IN FV (Res b Q)} /\
                       (P',Q',D') IN R)
End
 *)

val _ = export_theory ();
val _ = html_theory "pi_bisimulation";
