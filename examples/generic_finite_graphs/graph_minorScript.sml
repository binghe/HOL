(* ========================================================================== *)
(* FILE          : graph_minorScript.sml                                      *)
(* DESCRIPTION   : Graph Minors                                               *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open genericGraphTheory;

val _ = new_theory "graph_minor";

(* The function division takes a graph as input and returns a set of new graphs,
   each of them is done by removing one edge (m,n,l) from the input graph, adding
   two edges (m,z,l) and (z,n,l) back, where z is a fresh node.

Definition division_def :
    ...
End
 *)

val _ = export_theory();
val _ = html_theory "graph_minor";
