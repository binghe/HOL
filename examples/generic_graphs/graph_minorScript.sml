(*---------------------------------------------------------------------------*
 * graph_minorTheory: Theory of Graph Minors                                 *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open hurdUtils pred_setTheory listTheory;

open genericGraphTheory ;

val _ = new_theory "graph_minor";

(* NOTE: "fmgraph" stands for "Finite Multi-Graphs" *)
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
    ends (endvertices) of edges
   ---------------------------------------------------------------------- *)

Theorem ends_exists[local] :
    !s. FINITE s ==> ?x. if s <> {} /\ CARD s <= 2
                         then s = {FST x; SND x} else x = (ARB,ARB)
Proof
    rpt STRIP_TAC
 >> reverse (Cases_on ‘s <> {} /\ CARD s <= 2’) >> fs []
 >> rfs [CARD_LE2]
 >- (fs [SING_DEF] \\
     Q.EXISTS_TAC ‘(x,x)’ >> rw [])
 >> Q.EXISTS_TAC ‘(m,n)’ >> rw []
QED

(* "The two vertices incident with an edge are its endvertices or ends, and
    an edge joins its ends." [1, p.2]

   |- !s. FINITE s ==>
          if s <> {} /\ CARD s <= 2 then s = {FST (ends s); SND (ends s)}
          else ends s = (ARB,ARB)
 *)
val ends_def =
    new_specification
      ("ends_def", ["ends"],
       SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] ends_exists);

Theorem ends_thm :
    !s a b. FINITE s /\ s <> {} /\ CARD s <= 2 /\ (a,b) = ends s ==>
            s = {a;b}
Proof
    rpt STRIP_TAC
 >> Know ‘a = FST (ends s) /\ b = SND (ends s)’
 >- (POP_ASSUM (rw o wrap o SYM))
 >> rw []
 >> MP_TAC (Q.SPEC ‘s’ ends_def) >> rw []
QED

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
Definition division_def :
    division (g1 :fmgraph) e =
      let g' = removeUDEdge e g1;
          ns = incident e;
          n1 = FST (ends ns);
          n2 = SND (ends ns);
           n = NEW (nodes g1)
      in
         addUDEdge {n1;n} () (addUDEdge {n;n2} () g')
End

Definition has_division_def :
   has_division g1 g2 = ?e. e IN udedges g1 /\ g2 = division g1 e
End

Definition TX_def :
    TX = RTC $has_division
End

Theorem TX_GSPEC :
    !g. TX g = {g' | RTC $has_division g g'}
Proof
    rw [Once EXTENSION, TX_def, IN_APP]
QED

Theorem IN_TX :
    !g g'. g' IN TX g <=> RTC $has_division g g'
Proof
    rw [TX_GSPEC]
QED

(* ----------------------------------------------------------------------
    Graph isomorphism and 'subgraph' relation
   ---------------------------------------------------------------------- *)

(* not used *)
Definition graphiso_def :
    graphiso (g1 :fmgraph) (g2 :fmgraph) <=>
    ?f. BIJ f (nodes g1) (nodes g2) /\
        !n1 n2. adjacent g1 n1 n2 <=> adjacent g2 (f n1) (f n2)
End

Definition subgraph_def :
    subgraph (g1 :fmgraph) (g2 :fmgraph) <=>
    ?f. INJ f (nodes g1) (nodes g2) /\
        !n1 n2. adjacent g1 n1 n2 ==> adjacent g2 (f n1) (f n2)
End
Overload SUBSET = “subgraph”

(* ----------------------------------------------------------------------
    Topological minor [1, p.19]
   ---------------------------------------------------------------------- *)

Definition topological_minor_def :
    topological_minor g1 g2 <=> ?g. g IN TX g1 /\ subgraph g g2
End

(* ----------------------------------------------------------------------
    Contraction
   ---------------------------------------------------------------------- *)

Overload connected_in = “\g ns. connected (projectG ns g)”

(* NOTE: ‘TC (adjacent g n1 n2)’ doesn't work: the two nodes in ns may find
   another path outside of the subgraph ‘projectG ns g’.
 *)
Theorem connected_in :
    !g ns. ns SUBSET nodes g ==>
          (connected (projectG ns g) <=>
           !n1 n2. n1 IN ns /\ n2 IN ns /\ n1 <> n2 ==> TC (adjacent (projectG ns g)) n1 n2)
Proof
    rw [connected_def, nodes_projectG, SUBSET_DEF]
 >> EQ_TAC >> rw []
QED

Definition IX_def :
    IX (g :fmgraph) =
    {g' | ?R f. BIJ f (nodes g) (partition R (nodes g')) /\
               (!ns. ns IN partition R (nodes g') ==> connected_in g' ns) /\
                !n1 n2. adjacent g n1 n2 <=>
                        ?n1' n2'. n1' IN f n1 /\ n2' IN f n2 /\
                                  adjacent g' n1' n2'}
End

(* ----------------------------------------------------------------------
    Minor [1, p.19]
   ---------------------------------------------------------------------- *)

Definition minor_def :
    minor g1 g2 <=> ?g. g IN IX g1 /\ subgraph g g2
End
Overload "<<=" = “minor”

val _ = export_theory ();
val _ = html_theory "graph_minor";

(* References:

   [1] Diestel, R.: Graph Theory, 5th Electronic Edition. Springer-Verlag, Berlin (2017).
 *)
