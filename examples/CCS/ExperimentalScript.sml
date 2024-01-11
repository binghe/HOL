(* ========================================================================== *)
(* FILE          : ExperimentalScript.sml                                     *)
(* DESCRIPTION   : Experimental and variant definitions                       *)
(*                                                                            *)
(* COPYRIGHTS    : 2023-2024 Australian National University (Chun Tian)       *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open combinTheory pred_setTheory relationTheory pairTheory sumTheory listTheory
     arithmeticTheory stringTheory;

(* lambda theories *)
open binderLib;

(* local theories *)
open CCSLib CCSTheory CCSSyntax CCSConv;
open StrongEQTheory StrongEQLib StrongLawsTheory;
open WeakEQTheory WeakEQLib WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory;
open CongruenceTheory CoarsestCongrTheory;
open TraceTheory ExpansionTheory ContractionTheory;
open BisimulationUptoTheory UniqueSolutionsTheory;
(* open MultivariateTheory; *)

val _ = new_theory "Experimental";

(******************************************************************************)
(*                                                                            *)
(*         Variants of the transition relation (including coinductive)        *)
(*                                                                            *)
(******************************************************************************)

(* coTRANS is the coinductive version of oTRANS with identical input rules *)
CoInductive coTRANS :
    (!E u.                             coTRANS (prefix u E) u E) /\         (* PREFIX *)
    (!E u E1 E'.    coTRANS E u E1 ==> coTRANS (sum E E') u E1) /\          (* SUM1 *)
    (!E u E1 E'.    coTRANS E u E1 ==> coTRANS (sum E' E) u E1) /\          (* SUM2 *)
    (!E u E1 E'.    coTRANS E u E1 ==> coTRANS (par E E') u (par E1 E')) /\ (* PAR1 *)
    (!E u E1 E'.    coTRANS E u E1 ==> coTRANS (par E' E) u (par E' E1)) /\ (* PAR2 *)
    (!E l E1 E' E2. coTRANS E (label l) E1 /\ coTRANS E' (label (COMPL l)) E2
                ==> coTRANS (par E E') tau (par E1 E2)) /\                  (* PAR3 *)
    (!E u E' l L.   coTRANS E u E' /\ ((u = tau) \/
                                     ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
                ==> coTRANS (restr L E) u (restr L E')) /\                  (* RESTR *)
    (!E u E' rf.    coTRANS E u E'
                ==> coTRANS (relab E rf) (relabel rf u) (relab E' rf)) /\   (* RELABELING *)
    (!E u X E1.     coTRANS (CCS_Subst E (rec X E) X) u E1
                ==> coTRANS (rec X E) u E1)                                 (* REC *)
End

(* The rules for the transition relation TRANS as individual theorems. *)
val [coPREFIX, coSUM1, coSUM2, coPAR1, coPAR2, coPAR3, coRESTR, coRELABELING, coREC] =
    map save_thm
        (combine (["coPREFIX", "coSUM1", "coSUM2", "coPAR1", "coPAR2", "coPAR3",
                   "coRESTR", "coRELABELING", "coREC"],
                  CONJUNCTS coTRANS_rules));

(* Use SUB instead of CCS_Subst *)
Theorem coREC' = REWRITE_RULE [CCS_Subst] coREC

val _ = export_theory ();
val _ = html_theory "Experimental";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.
 [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer (2015).

 *)
