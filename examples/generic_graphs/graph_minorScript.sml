(*---------------------------------------------------------------------------*
 * graph_minorTheory: Theory of Graph Minors                                 *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open hurdUtils pred_setTheory genericGraphTheory;

val _ = new_theory "graph_minor";

Type fmgraph[pp] = “:(unit,finiteEdges,unit,finiteG,unit,SL_OK) udgraph”

(* ----------------------------------------------------------------------
    The NEW constant (learnt from "examples/lambda/basics")
   ---------------------------------------------------------------------- *)

Theorem NEW_exists :
    !ns :('a + num) set. FINITE ns ==> ?n. n NOTIN ns
Proof
    Suff ‘INFINITE univ(:'a + num)’
 >- METIS_TAC [IN_UNIV, IN_INFINITE_NOT_FINITE]
 >> rw [SUM_UNIV]
QED

(* |- !ns. FINITE ns ==> NEW ns NOTIN ns *)
val NEW_def =
    new_specification
      ("NEW_def", ["NEW"],
       SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] NEW_exists);

(* ----------------------------------------------------------------------
    (Edge) division
   ---------------------------------------------------------------------- *)

(* g1:  -- n1 ---- e ---- n2 --
           |              |
           +------ e'-----+

   g2:  -- n1 -e1- n -e2- n2 --
           |              |
           +------ e'-----+
 *)
Definition has_division_def :
    has_division (g1 :fmgraph) (g2 :fmgraph) <=>
    ?e. e IN udedges g1 /\
        let g' = removeEdge (cUDE e) g1;
            ns = incident e;
            n1 = CHOICE ns;
            n2 = if ns DELETE n1 = {} then n1 else CHOICE (ns DELETE n1);
             n = NEW (nodes g1)
        in
            g2 = addUDEdge {n1;n} ()
                   (addUDEdge {n;n2} () g')
End

Definition TX_def :
    TX g1 = {g2 | RTC has_division g1 g2}
End

(* ----------------------------------------------------------------------
    Graph isomorphism and 'subgraph' relation
   ---------------------------------------------------------------------- *)

(* TODO: |- equivalance graphiso *)
Definition graphiso_def :
    graphiso (g1 :fmgraph) (g2 :fmgraph) <=>
    ?f. BIJ f (nodes g1) (nodes g2) /\
        !n1 n2. adjacent g1 n1 n2 <=>
                adjacent g2 (f n1) (f n2) IN udedges g2
End

Definition subgraph_def :
    subgraph (g1 :fmgraph) (g2 :fmgraph) <=>
    ?f. INJ f (nodes g1) (nodes g2) /\
        !n1 n2. adjacent g1 n1 n2 ==>
                adjacent g2 (f n1) (f n2) IN udedges g2
End

(* ----------------------------------------------------------------------
    Topological minor [1, p.19]
   ---------------------------------------------------------------------- *)

Definition topological_minor_def :
    topological_minor g1 g2 <=> ?g. g IN TX g1 /\ subgraph g g2
End

(* ----------------------------------------------------------------------
    Contraction
   ---------------------------------------------------------------------- *)

(* NOTE: In ‘g1 has_contraction g2’, g1 is contracted from g2 *)
Definition IX_def :
    IX (g1 :fmgraph) =
       {g2 | ?R f. BIJ f (nodes g1) (partition R (nodes g2)) /\
                   !n1 n2. adjacent g1 n1 n2 <=>
                           ?n1' n2'. n1' IN f n1 /\ n2' IN f n2 /\
                                     adjacent g2 n1' n2'}
End

(* ----------------------------------------------------------------------
    Minor [1, p.19]
   ---------------------------------------------------------------------- *)

Definition minor_def :
    minor g1 g2 <=> ?g. g IN IX g1 /\ subgraph g g2
End

val _ = export_theory ();
val _ = html_theory "graph_minor";

(* References:

   [1] Diestel, R.: Graph Theory, 5th Electronic Edition. Springer-Verlag, Berlin (2017).
 *)
