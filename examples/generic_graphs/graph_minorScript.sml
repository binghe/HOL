(*---------------------------------------------------------------------------*
 * graph_minorTheory: Theory of Graph Minors                                 *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open genericGraphTheory;

val _ = new_theory "graph_minor";

Type fmgraph[pp] = “:(unit,finiteEdges,unit,finiteG,unit,SL_OK) udgraph”



val _ = export_theory ();
val _ = html_theory "graph_minor";

(* References:

   [1] Diestel, R.: Graph Theory, 5th Electronic Edition. Springer-Verlag, Berlin (2017).
 *)
