(*---------------------------------------------------------------------------*
 * graph_minorTheory: Theory of Graph Minors                                 *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open hurdUtils pred_setTheory listTheory;

open genericGraphTheory ;

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

Theorem ends_exists[local] :
    !s. FINITE s /\ 0 < CARD s /\ CARD s <= 2 ==> ?x. s = {FST x; SND x}
Proof
    rpt STRIP_TAC
 >> ‘CARD s = 1 \/ CARD s = 2’ by rw []
 >- (‘SING s’ by rw [SING_IFF_CARD1] \\
     fs [SING_DEF] \\
     Q.EXISTS_TAC ‘(x,x)’ >> rw [])
 >> rfs [CARDEQ2]
 >> Q.EXISTS_TAC ‘(a,b)’ >> rw []
QED

(* |- !s. FINITE s /\ 0 < CARD s /\ CARD s <= 2 ==>
          s = {FST (ends s); SND (ends s)}
 *)
val ends_def =
    new_specification
      ("ends_def", ["ends"],
       SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] ends_exists);

Theorem ends_thm :
    !s a b. FINITE s /\ 0 < CARD s /\ CARD s <= 2 /\ (a,b) = ends s ==>
            s = {a;b}
Proof
    rpt STRIP_TAC
 >> Know ‘a = FST (ends s) /\ b = SND (ends s)’
 >- (POP_ASSUM (rw o wrap o SYM))
 >> rw []
 >> MATCH_MP_TAC ends_def >> art []
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
      let g' = removeEdge (cUDE e) g1;
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

(* NOTE: In ‘g1 has_contraction g2’, g1 is contracted from g2 *)
Definition IX_def :
    IX (g :fmgraph) =
       {g' | ?R f. BIJ f (nodes g) (partition R (nodes g')) /\
                   !n1 n2. adjacent g n1 n2 <=>
                           ?n1' n2'. n1' IN f n1 /\ n2' IN f n2 /\
                                     adjacent g' n1' n2'}
End

Theorem IN_IX :
    !g g'. g' IN IX g <=>
           ?R f. BIJ f (nodes g) (partition R (nodes g')) /\
                   !n1 n2. adjacent g n1 n2 <=>
                           ?n1' n2'. n1' IN f n1 /\ n2' IN f n2 /\
                                     adjacent g' n1' n2'
Proof
    rw [IX_def]
QED

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
