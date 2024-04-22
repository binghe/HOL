(* ------------------------------------------------------------------------- *)
(* Group library                                                             *)
(* ========================================================================= *)
(*  A group is an algebraic structure: a monoid with all its elements        *)
(*  invertible.                                                              *)
(* ------------------------------------------------------------------------- *)
(* Group Theory -- axioms to exponentiation.                                 *)
(* Group Maps                                                                *)
(* ------------------------------------------------------------------------- *)
(* By: (Joseph) Hing-Lun Chan, The Australian National University, 2014-2019 *)
(* ------------------------------------------------------------------------- *)

(*
based on: examples/elliptic/groupScript.sml

The idea behind this script is discussed in (Secton 2.1.1. Groups):

Formalizing Elliptic Curve Cryptography in Higher Order Logic (Joe Hurd)
http://www.gilith.com/research/papers/elliptic.pdf

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "group";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory gcdsetTheory

open numberTheory combinatoricsTheory;

open monoidTheory; (* for G*, monoid_invertibles_is_monoid *)

(* ------------------------------------------------------------------------- *)
(* Group Documentation                                                      *)
(* ------------------------------------------------------------------------- *)
(* Data type (same as monoid):
   The generic symbol for group data is g.
   g.carrier = Carrier set of group, overloaded as G.
   g.op      = Binary operation of group, overloaded as *.
   g.id      = Identity element of group, overloaded as #e.
   g.exp     = Iteration of g.op (added by monoid)
   g.inv     = Inverse of g.op   (added by monoid)
*)
(* Definitions and Theorems (# are exported):

   Definitions:
   Group_def               |- !g. Group g <=> Monoid g /\ (G* = G)
   AbelianGroup_def        |- !g. AbelianGroup g <=> Group g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
   FiniteGroup_def         |- !g. FiniteGroup g <=> Group g /\ FINITE G
   FiniteAbelianGroup_def  |- !g. FiniteAbelianGroup g <=> AbelianGroup g /\ FINITE G

   Extract from definition:
   group_clauses           |- !g. Group g ==> Monoid g /\ (G* = G)
#  group_is_monoid         |- !g. Group g ==> Monoid g
#  group_all_invertible    |- !g. Group g ==> (G* = G)

   Simple theorems:
   monoid_invertibles_is_group   |- !g. Monoid g ==> Group (Invertibles g)
   finite_monoid_invertibles_is_finite_group
                                 |- !g. FiniteMonoid g ==> FiniteGroup (Invertibles g)
   FiniteAbelianGroup_def_alt    |- !g. FiniteAbelianGroup g <=>
                                        FiniteGroup g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
   finite_group_is_group         |- !g. FiniteGroup g ==> Group g
   finite_group_is_monoid        |- !g. FiniteGroup g ==> Monoid g
   finite_group_is_finite_monoid |- !g. FiniteGroup g ==> FiniteMonoid g
   abelian_group_is_abelian_monoid
                                 |- !g. AbelianGroup g ==> AbelianMonoid g
   finite_abelian_group_is_finite_abelian_monoid
                                 |- !g. FiniteAbelianGroup g ==> FiniteAbelianMonoid g

   Group theorems (lift or take from Monoid):
   group_id_element   |- !g. Group g ==> #e IN G
   group_op_element   |- !g. Group g ==> !x y. x IN G /\ y IN G ==> x * y IN G
   group_assoc        |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * y * z = x * (y * z))
   group_lid          |- !g. Group g ==> !x. x IN G ==> (#e * x = x)
   group_rid          |- !g. Group g ==> !x. x IN G ==> (x * #e = x)
   group_id           |- !g. Group g ==> !x. x IN G ==> (#e * x = x) /\ (x * #e = x)
   group_id_id        |- !g. Group g ==> (#e * #e = #e)
   group_exp_element  |- !g. Group g ==> !x. x IN G ==> !n. x ** n IN G
   group_exp_SUC      |- !g x n. x ** SUC n = x * x ** n
   group_exp_suc      |- !g. Group g ==> !x. x IN G ==> !n. x ** SUC n = x ** n * x
   group_exp_0        |- !g x. x ** 0 = #e
   group_exp_1        |- !g. Group g ==> !x. x IN G ==> (x ** 1 = x)
   group_id_exp       |- !g. Group g ==> !n. #e ** n = #e
   group_comm_exp     |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x) ==> !n. x ** n * y = y * x ** n
   group_exp_comm     |- !g. Group g ==> !x. x IN G ==> !n. x ** n * x = x * x ** n
   group_comm_op_exp  |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==> !n. (x * y) ** n = x ** n * y ** n
   group_exp_add      |- !g. Group g ==> !x. x IN G ==> !n k. x ** (n + k) = x ** n * x ** k
   group_exp_mult     |- !g. Group g ==> !x. x IN G ==> !n k. x ** (n * k) = (x ** n) ** k

   Group theorems (from Monoid invertibles).
#  group_inv_element  |- !g. Group g ==> !x. x IN G ==> |/ x IN G
#  group_linv         |- !g. Group g ==> !x. x IN G ==> ( |/ x * x = #e)
#  group_rinv         |- !g. Group g ==> !x. x IN G ==> (x * |/ x = #e)
   group_inv_thm      |- !g. Group g ==> !x. x IN G ==> (x * |/ x = #e) /\ ( |/ x * x = #e)
   group_carrier_nonempty  |- !g. Group g ==> G <> {}

   Group theorems (not from Monoid):
   group_lcancel     |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = x * z) <=> (y = z))
   group_rcancel     |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((y * x = z * x) <=> (y = z))

   Inverses with assocative law:
   group_linv_assoc  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (y = x * ( |/ x * y)) /\ (y = |/ x * (x * y))
   group_rinv_assoc  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (y = y * |/ x * x) /\ (y = y * x * |/ x)
   group_lsolve      |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = z) <=> (x = z * |/ y))
   group_rsolve      |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = z) <=> (y = |/ x * z))
   group_lid_unique  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((y * x = x) <=> (y = #e))
   group_rid_unique  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = x) <=> (y = #e))
   group_id_unique   |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((y * x = x) <=> (y = #e)) /\
                                                                   ((x * y = x) <=> (y = #e))
   group_linv_unique |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = #e) <=> (x = |/ y))
   group_rinv_unique |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = #e) <=> (y = |/ x))
#  group_inv_inv     |- !g. Group g ==> !x. x IN G ==> ( |/ ( |/ x) = x)
#  group_inv_eq      |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x = |/ y) <=> (x = y))
#  group_inv_eq_swap |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x = y) <=> (x = |/ y))
#  group_inv_id      |- !g. Group g ==> ( |/ #e = #e)
   group_inv_eq_id   |- !g. Group g ==> !x. x IN G ==> (( |/ x = #e) <=> (x = #e))
   group_inv_op      |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ( |/ (x * y) = |/ y * |/ x)
   group_pair_reduce |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * z * |/ (y * z) = x * |/ y)
   group_id_fix      |- !g. Group g ==> !x. x IN G ==> ((x * x = x) <=> (x = #e))
   group_op_linv_eq_id  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x * y = #e) <=> (x = y))
   group_op_rinv_eq_id  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((x * |/ y = #e) <=> (x = y))
   group_op_linv_eqn    |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (( |/ x * y = z) <=> (y = x * z))
   group_op_rinv_eqn    |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * |/ y = z) <=> (x = z * y))
   Invertibles_inv      |- !g x. Monoid g /\ x IN G* ==> ((Invertibles g).inv x = |/ x)
   monoid_inv_id        |- !g. Monoid g ==> |/ #e = #e

   Group defintion without explicit mention of Monoid.
   group_def_alt        |- !g. Group g <=>
                            (!x y. x IN G /\ y IN G ==> x * y IN G) /\
                            (!x y z. x IN G /\ y IN G /\ z IN G ==> (x * y * z = x * (y * z))) /\
                            #e IN G /\
                            (!x. x IN G ==> (#e * x = x)) /\ !x. x IN G ==> ?y. y IN G /\ (y * x = #e)
   group_def_by_inverse |- !g. Group g <=> Monoid g /\ !x. x IN G ==> ?y. y IN G /\ (y * x = #e)
   group_alt            |- !g. Group g <=>
                            (!x y::G. x * y IN G) /\ (!x y z::G. x * y * z = x * (y * z)) /\
                            #e IN G /\ (!x::G. #e * x = x) /\ !x::G. |/ x IN G /\ |/ x * x = #e

   Transformation of Group structure by modifying carrier (for field).
   including_def   |- !g z. including g z = <|carrier := G UNION {z}; op := $*; id := #e|>
   excluding_def   |- !g z. excluding g z = <|carrier := G DIFF {z}; op := $*; id := #e|>
   group_including_property
                   |- !g z. ((g including z).op = $* ) /\ ((g including z).id = #e) /\
                      !x. x IN (g including z).carrier ==> x IN G \/ (x = z)
   group_excluding_property
                   |- !g z. ((g excluding z).op = $* ) /\ ((g excluding z).id = #e) /\
                      !x. x IN (g excluding z).carrier ==> x IN G /\ x <> z
   group_including_excluding_property
                   |- !g z. ((g including z excluding z).op = $* ) /\
                            ((g including z excluding z).id = #e) /\
                            (z NOTIN G ==> ((g including z excluding z).carrier = G))
   group_including_excluding_group
                   |- !g z. z NOTIN G ==> (Group g <=> Group (g including z excluding z))
   group_including_excluding_abelian
                   |- !g z. z NOTIN G ==> (AbelianGroup g <=> AbelianGroup (g including z excluding z))
   group_including_excluding_eqn |- !g z.  g including z excluding z =
                   if z IN G then <|carrier := G DELETE z; op := $*; id := #e|> else g
#  group_excluding_op  |- !g z. (g excluding z).op = $*
   group_excluding_exp |- !g z x n. (g excluding z).exp x n = x ** n
   abelian_monoid_invertible_excluding
                       |- !g. AbelianMonoid g ==>
                          !z. z NOTIN G* ==> (monoid_invertibles (g excluding z) = G* )

   Group Exponentiation with Inverses:
   group_exp_inv   |- !g. Group g ==> !x. x IN G ==> !n. |/ (x ** n) = |/ x ** n
   group_inv_exp   |- !g. Group g ==> !x. x IN G ==> !n. |/ x ** n = |/ (x ** n)
   group_exp_eq    |- !g. Group g ==> !x. x IN G ==> !m n. m < n /\ (x ** m = x ** n) ==> (x ** (n - m) = #e)
   group_exp_mult_comm |- !g. Group g ==> !x. x IN G ==> !m n. (x ** m) ** n = (x ** n) ** m
   group_comm_exp_exp  |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
                                          !n m. x ** n * y ** m = y ** m * x ** n

*)

(* ------------------------------------------------------------------------- *)
(* Group Definition.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Set up group type as a record
   A Group has:
   . a carrier set (set = function 'a -> bool, since MEM is a boolean function)
   . an identity element
   . an inverse function (unary operation)
   . a product function called multiplication (binary operation)
*)

(* Monoid and Group share the same type: already defined in monoid.hol
val _ = Hol_datatype`
  group = <| carrier:'a -> bool;
                  id: 'a;
                 inv:'a -> 'a; -- by val _ = add_record_field ("inv", ``monoid_inv``);
                mult:'a -> 'a -> 'a
           |>`;
*)
val _ = type_abbrev ("group", Type `:'a monoid`);

(* Define Group by Monoid

   NOTE:
val _ = overload_on ("G", ``g.carrier``);
val _ = overload_on ("G*", ``monoid_invertibles g``);
 *)
val Group_def = Define`
  Group (g:'a group) <=>
    Monoid g /\ (G* = G)
`;

(* ------------------------------------------------------------------------- *)
(* More Group Defintions.                                                    *)
(* ------------------------------------------------------------------------- *)
(* Abelian Group: a Group with a commutative product: x * y = y * x. *)
val AbelianGroup_def = Define`
  AbelianGroup (g:'a group) <=>
    Group g /\ (!x y. x IN G /\ y IN G ==> (x * y = y * x))
`;

(* Finite Group: a Group with a finite carrier set. *)
val FiniteGroup_def = Define`
  FiniteGroup (g:'a group) <=>
    Group g /\ FINITE G
`;

(* Finite Abelian Group: a Group that is both Finite and Abelian. *)
val FiniteAbelianGroup_def = Define`
  FiniteAbelianGroup (g:'a group) <=>
    AbelianGroup g /\ FINITE G
`;

(* ------------------------------------------------------------------------- *)
(* Basic theorems from definition.                                           *)
(* ------------------------------------------------------------------------- *)

(* Group clauses from definition, internal use *)
val group_clauses = Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> GEN_ALL;
(* > val group_clauses = |- !g. Group g ==> Monoid g /\ (G* = G) *)

(* Theorem: A Group is a Monoid. *)
(* Proof: by definition. *)
val group_is_monoid = save_thm("group_is_monoid",
  Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val group_is_monoid = |- !g. Group g ==> Monoid g : thm *)

val _ = export_rewrites ["group_is_monoid"];

(* Theorem: Group Invertibles is the whole carrier set. *)
(* Proof: by definition. *)
val group_all_invertible = save_thm("group_all_invertible",
  Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val group_all_invertible = |- !g. Group g ==> (G* = G) : thm *)

val _ = export_rewrites ["group_all_invertible"];

(* ------------------------------------------------------------------------ *)
(* Simple Theorems                                                          *)
(* ------------------------------------------------------------------------ *)

(* Theorem: The Invertibles of a monoid form a group. *)
(* Proof: by checking definition. *)
val monoid_invertibles_is_group = store_thm(
  "monoid_invertibles_is_group",
  ``!g. Monoid g ==> Group (Invertibles g)``,
  rw[Group_def, monoid_invertibles_is_monoid] >>
  rw[Invertibles_def, monoid_invertibles_def, EXTENSION, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: FiniteMonoid g ==> FiniteGroup (Invertibles g) *)
(* Proof:
   Note Monoid g /\ FINITE G            by FiniteMonoid_def
   Let s = (Invertibles g).carrier).
   Then s SUBSET G                      by Invertibles_subset
    ==> FINITE s                        by SUBSET_FINITE
   Also Group (Invertibles g)           by monoid_invertibles_is_group
    ==> FiniteGroup (Invertibles g)     by FiniteGroup_def
*)
val finite_monoid_invertibles_is_finite_group = store_thm(
  "finite_monoid_invertibles_is_finite_group",
  ``!g:'a monoid. FiniteMonoid g ==> FiniteGroup (Invertibles g)``,
  metis_tac[monoid_invertibles_is_group, FiniteGroup_def, FiniteMonoid_def,
            Invertibles_subset, SUBSET_FINITE]);

(* Theorem: Finite Abelian Group = Finite Group /\ commutativity. *)
(* Proof: by definitions. *)
val FiniteAbelianGroup_def_alt = store_thm(
  "FiniteAbelianGroup_def_alt",
  ``!g:'a group. FiniteAbelianGroup g <=>
                FiniteGroup g /\ (!x y. x IN G /\ y IN G ==> (x * y = y * x))``,
  rw[FiniteAbelianGroup_def, FiniteGroup_def, AbelianGroup_def, EQ_IMP_THM]);

(* Theorem: FiniteGroup g ==> Group g *)
(* Proof: by FiniteGroup_def *)
val finite_group_is_group = store_thm(
  "finite_group_is_group",
  ``!g:'a group. FiniteGroup g ==> Group g``,
  rw[FiniteGroup_def]);

(* Theorem: FiniteGroup g ==> Monoid g *)
(* Proof: by finite_group_is_group, group_is_monoid *)
val finite_group_is_monoid = store_thm(
  "finite_group_is_monoid",
  ``!g:'a group. FiniteGroup g ==> Monoid g``,
  rw[FiniteGroup_def]);

(* Theorem: For FINITE Group is FINITE monoid. *)
(* Proof: by group_is_monoid. *)
val finite_group_is_finite_monoid = store_thm(
  "finite_group_is_finite_monoid",
  ``!g:'a group. FiniteGroup g ==> FiniteMonoid g``,
  rw[FiniteGroup_def, FiniteMonoid_def, group_is_monoid]);

(* Theorem: AbelianGroup g ==> AbelianMonoid g *)
(* Proof: by AbelianGroup_def, AbelianMonoid_def, group_is_monoid. *)
val abelian_group_is_abelian_monoid = store_thm(
  "abelian_group_is_abelian_monoid[simp]",
  ``!g. AbelianGroup g ==> AbelianMonoid g``,
  rw[AbelianGroup_def, AbelianMonoid_def]);

(* Theorem: FiniteAbelianGroup g ==> FiniteAbelianMonoid g *)
(* Proof: by FiniteAbelianGroup_def, FiniteAbelianMonoid_def, abelian_group_is_abelian_monoid. *)
val finite_abelian_group_is_finite_abelian_monoid = store_thm(
  "finite_abelian_group_is_finite_abelian_monoid",
  ``!g. FiniteAbelianGroup g ==> FiniteAbelianMonoid g``,
  rw_tac std_ss[FiniteAbelianGroup_def, FiniteAbelianMonoid_def, abelian_group_is_abelian_monoid]);

(* ------------------------------------------------------------------------- *)
(* Group theorems (from Monoid).                                             *)
(* ------------------------------------------------------------------------- *)

(* Do Theorem Lifting, but no need to export. *)

(* Manual Lifting:

- show_assums := true;
> val it = () : unit

- monoid_id_element;
> val it =  [] |- !g. Monoid g ==> #e IN G : thm
- monoid_id_element |> SPEC_ALL |> UNDISCH;
> val it =  [Monoid g] |- #e IN G : thm
- monoid_id_element |> SPEC_ALL |> UNDISCH |> PROVE_HYP (group_is_monoid |> SPEC_ALL |> UNDISCH);
> val it =  [Group g] |- #e IN G : thm
- monoid_id_element |> SPEC_ALL |> UNDISCH |> PROVE_HYP (group_is_monoid |> SPEC_ALL |> UNDISCH) |> DISCH_ALL |> GEN_ALL;
> val it =  [] |- !g. Group g ==> #e IN G : thm

or
- group_is_monoid;
> val it =  [] |- !g. Group g ==> Monoid g : thm
- group_is_monoid |> SPEC_ALL |> UNDISCH;
> val it =  [Group g] |- Monoid g : thm
- group_is_monoid |> SPEC_ALL |> UNDISCH |> MP (monoid_id_element |> SPEC_ALL);
> val it =  [Group g] |- #e IN G : thm
- group_is_monoid |> SPEC_ALL |> UNDISCH |> MP (monoid_id_element |> SPEC_ALL) |> DISCH_ALL |> GEN_ALL;
> val it =  [] |- !g. Group g ==> #e IN G : thm

- show_assums := false;
> val it = () : unit
*)

(* Lifting Monoid theorem for Group.
   from: !g:'a monoid. Monoid g ==> ....
     to: !g:'a group.  Group g ==> ....
    via: !g:'a group.  Group g ==> Monoid g
*)
local
val gim = group_is_monoid |> SPEC_ALL |> UNDISCH
in
fun lift_monoid_thm suffix = let
   val mth = DB.fetch "monoid" ("monoid_" ^ suffix)
   val mth' = mth |> SPEC_ALL
in
   save_thm("group_" ^ suffix, gim |> MP mth' |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Theorem: Group identity is an element. *)
val group_id_element = lift_monoid_thm "id_element";
(* > val group_id_element = |- !g. Group g ==> #e IN G : thm *)

(* Theorem: [Group closure] Group product is an element. *)
val group_op_element = lift_monoid_thm "op_element";
(* > val group_op_element = |- !g. Group g ==> !x y. x IN G /\ y IN G ==> x * y IN G : thm *)

(* Theorem: [Group associativity] (x * y) * z = x * (y * z) *)
val group_assoc = lift_monoid_thm "assoc";
(* > val group_assoc = |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * y * z = x * (y * z)) : thm *)

(* Theorem: [Group left identity] #e * x = x *)
val group_lid = lift_monoid_thm "lid";
(* > val group_lid = |- !g. Group g ==> !x. x IN G ==> (#e * x = x) : thm *)

(* Theorem: [Group right identity] x * #e = x *)
val group_rid = lift_monoid_thm "rid";
(* > val group_rid = |- !g. Group g ==> !x. x IN G ==> (x * #e = x) : thm *)

(* Theorem: [Group identities] #e * x = x /\ x * #e = x *)
val group_id = lift_monoid_thm "id";
(* > val group_id = |- !g. Group g ==> !x. x IN G ==> (#e * x = x) /\ (x * #e = x) : thm *)

(* Theorem: #e * #e = #e *)
val group_id_id = lift_monoid_thm "id_id";
(* > val group_id_id = |- !g. Group g ==> (#e * #e = #e) : thm *)

(* Theorem: (x ** n) in G *)
val group_exp_element = lift_monoid_thm "exp_element";
(* > val group_exp_element = |- !g. Group g ==> !x. x IN G ==> !n. x ** n IN G : thm *)

(* Theorem: x ** SUC n = x * x ** n *)
val group_exp_SUC = save_thm("group_exp_SUC", monoid_exp_SUC);
(* > val group_exp_SUC = |- !g x. x ** SUC n = x * x ** n : thm *)

(* Theorem: x ** SUC n = x ** n * x *)
val group_exp_suc = lift_monoid_thm "exp_suc";
(* val group_exp_suc = |- !g. Group g ==> !x. x IN G ==> !n. x ** SUC n = x ** n * x : thm *)

(* Theorem: x ** 0 = #e *)
val group_exp_0 = save_thm("group_exp_0", monoid_exp_0);
(* > val group_exp_0 = |- !g x. x ** 0 = #e : thm *)

(* Theorem: x ** 1 = x *)
val group_exp_1 = lift_monoid_thm "exp_1";
(* > val group_exp_1 = |- !g. Group g ==> !x. x IN G ==> (x ** 1 = x) : thm *)

(* Theorem: (#e ** n) = #e  *)
val group_id_exp = lift_monoid_thm "id_exp";
(* > val group_id_exp = |- !g. Group g ==> !n. #e ** n = #e : thm *)

(* Theorem: For abelian group g,  (x ** n) * y = y * (x ** n) *)
val group_comm_exp = lift_monoid_thm "comm_exp";
(* > val group_comm_exp = |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x) ==> !n. x ** n * y = y * x ** n : thm *)

(* Theorem: (x ** n) * x = x * (x ** n) *)
val group_exp_comm = lift_monoid_thm "exp_comm";
(* > val group_exp_comm = |- !g. Group g ==> !x. x IN G ==> !n. x ** n * x = x * x ** n : thm *)

(* Theorem: For abelian group, (x * y) ** n = (x ** n) * (y ** n) *)
val group_comm_op_exp = lift_monoid_thm "comm_op_exp";
(* > val group_comm_op_exp = |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==> !n. (x * y) ** n = x ** n * y ** n : thm *)

(* Theorem: x ** (m + n) = (x ** m) * (x ** n) *)
val group_exp_add = lift_monoid_thm "exp_add";
(* > val group_exp_add = |- !g. Group g ==> !x. x IN G ==> !n k. x ** (n + k) = x ** n * x ** k : thm *)

(* Theorem: x ** (m * n) = (x ** m) ** n  *)
val group_exp_mult = lift_monoid_thm "exp_mult";
(* > val group_exp_mult = |- !g. Group g ==> !x. x IN G ==> !n k. x ** (n * k) = (x ** n) ** k : thm *)

(* ------------------------------------------------------------------------- *)
(* Group theorems (from Monoid invertibles).                                 *)
(* ------------------------------------------------------------------------- *)

(* val _ = overload_on("|/", ``monoid_inv g``); *)
(* val _ = overload_on("|/", ``reciprocal``); *)

(* Theorem: [Group inverse element] |/ x IN G *)
(* Proof: by Group_def and monoid_inv_def. *)
Theorem group_inv_element[simp]:
  !g:'a group. Group g ==> !x. x IN G ==> |/x IN G
Proof rw[monoid_inv_def]
QED

val gim = Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT1;
val ginv = Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT2;

(* Theorem: [Group left inverse] |/ x * x = #e *)
(* Proof: by Group_def and monoid_inv_def. *)
Theorem group_linv[simp] =
  monoid_inv_def |> SPEC_ALL |> REWRITE_RULE [gim, ginv] |> SPEC_ALL |> UNDISCH_ALL
                 |> CONJUNCT2 |> CONJUNCT2 |> DISCH ``x IN G`` |> GEN ``x`` |> DISCH ``Group g`` |> GEN_ALL
(* > val group_linv = |- !g. Group g ==> !x. x IN G ==> ( |/ x * x = #e) : thm *)

(* Theorem: [Group right inverse] x * |/ x = #e *)
(* Proof: by Group_def and monoid_inv_def. *)
val group_rinv = save_thm("group_rinv",
  monoid_inv_def |> SPEC_ALL |> REWRITE_RULE [gim, ginv] |> SPEC_ALL |> UNDISCH_ALL
                 |> CONJUNCT2 |> CONJUNCT1 |> DISCH ``x IN G`` |> GEN ``x`` |> DISCH ``Group g`` |> GEN_ALL);
(* > val group_rinv = |- !g. Group g ==> !x. x IN G ==> (x * |/ x = #e) : thm *)

(* Maybe good to export ? *)
val _ = export_rewrites ["group_inv_element", "group_linv", "group_rinv"];

(* Theorem: [Group inverses] x * |/ x = #e /\ |/x * x = #e *)
val group_inv_thm = save_thm("group_inv_thm",
  monoid_inv_def |> SPEC_ALL |> REWRITE_RULE [gim, ginv] |> SPEC_ALL |> UNDISCH_ALL
                 |> CONJUNCT2 |> DISCH ``x IN G`` |> GEN ``x`` |> DISCH ``Group g`` |> GEN_ALL);
(* > val group_inv_thm = |- !g. Group g ==> !x. x IN G ==> (x * |/ x = #e) /\ ( |/ x * x = #e) : thm *)

(* Theorem: [Group carrier nonempty] G <> {} *)
val group_carrier_nonempty = lift_monoid_thm "carrier_nonempty";
(* > val group_carrier_nonempty = |- !g. Group g ==> G <> {} : thm *)

(* ------------------------------------------------------------------------- *)
(* Group Theorems (not from Monoid).                                         *)
(* ------------------------------------------------------------------------- *)

(* Just an exercise to show that right inverse can be deduced from left inverse for Group. *)

(* Theorem: [Group right inverse] x * |/ x = #e *)
(* Proof:
     x * |/ x
   = #e  * (x * |/ x)                   by left identity: #e * X = X, where X = (x * |/ x)
   = (#e * x) * |/ x                    by associativity
   = ( |/ ( |/ x) * |/ x) * x) * |/ x   by left inverse: #e = |/ Y * Y, where Y = |/ x
   = ( |/ ( |/ x) * ( |/ x * x)) * |/ x by associativity
   = ( |/ ( |/ x) * #e) * |/ x          by left inverse: |/ Y * Y = #e, where Y = |/ x
   = |/ ( |/ x) * (#e * |/ x)           by associativity
   = |/ ( |/ x) * ( |/ x)               by left identity: #e * Y = Y, where Y = |/ x
   = #e                                 by left inverse: |/ Y * Y = #e, where Y = |/ x
*)

(* Just an exercise to show that right identity can be deduced from left identity for Group. *)

(* Theorem: [Group right identity] x * #e = x *)
(* Proof:
     x * #e
   = x * ( |/ x * x)    by left inverse: |/ Y * Y = #e, where Y = x
   = (x * |/ x) * x     by associativity
   = #e * x             by right inverse: Y * |/ Y = #e, where Y = x
   = x                  by left identity: #e * Y = Y, where Y = x
*)

(* Theorem: [Left cancellation] x * y = x * z <=> y = z *)
(* Proof:
   (wrong proof: note the <=>)
               x * y = x * z
   <=> |/x * (x * y) = |/x * (x * z)    this asssume left-cancellation!
   <=> ( |/x * x) * y = ( |/x * x) * z  by group_assoc
   <=>        #e * y = #e * z           by group_linv
   <=>             y = z                by group_lid
   (correct proof: note the ==>)
   If part: x * y = x * z ==> y = z
               x * y = x * z
   ==> |/x * (x * y) = |/x * (x * z)    by group_inv_element
   ==> ( |/x * x) * y = ( |/x * x) * z  by group_assoc
   ==>        #e * y = #e * z           by group_linv
   ==>             y = z                by group_lid
   Only-if part: true by substitution.
*)
val group_lcancel = store_thm(
  "group_lcancel",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = x * z) = (y = z))``,
  rw[EQ_IMP_THM] >>
  `( |/x * x) * y = ( |/x * x) * z` by rw[group_assoc] >>
  metis_tac[group_linv, group_lid]);

(* Theorem: [Right cancellation] y * x = z * x <=> y = z *)
(* Proof:
   If part: y * x = z * x ==> y = z
       y * x = z * x
   ==> y * x * |/x = z * x * |/x      by group_inv_element
   ==> y * (x * |/x) = z * (x * |/x)  by group_assoc
   ==>         y * #e = z * #e        by group_rinv
   ==>              y = z             by group_rid
   Only-if part: true by substitution.
*)
val group_rcancel = store_thm(
  "group_rcancel",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((y * x = z * x) = (y = z))``,
  rw[EQ_IMP_THM] >>
  `y * (x * |/x) = z * (x * |/x)` by rw[GSYM group_assoc] >>
  metis_tac[group_rinv, group_rid]);

(* ------------------------------------------------------------------------- *)
(* Inverses with assocative law.                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: y = x * ( |/ x * y) /\ y = |/x * (x * y) *)
(* Proof: by group_assoc and group_linv or group_rinv. *)
val group_linv_assoc = store_thm(
  "group_linv_assoc",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (y = x * ( |/ x * y)) /\ (y = |/x * (x * y))``,
  rw[GSYM group_assoc]);

(* Theorem: y = y * |/ x * x /\ y = y * x * |/x *)
(* Proof: by group_assoc and group_linv or group_rinv. *)
val group_rinv_assoc = store_thm(
  "group_rinv_assoc",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (y = y * |/ x * x) /\ (y = y * x * |/x)``,
  rw[group_assoc]);

(* Theorem: [Solve left unknown] x * y = z <=> x = z * |/y *)
(* Proof:
   If part: x * y = z ==> x = z * |/y
     z * |/y
   = (x * y) * |/y   by substituting z
   = x               by group_rinv_assoc
   Only-if part: x = z * |/y ==> x * y = z
     x * y
   = (z * |/y) * y   by substituting x
   = z               by group_rinv_assoc
*)
val group_lsolve = store_thm(
  "group_lsolve",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = z) = (x = z * |/y))``,
  rw[group_rinv_assoc, EQ_IMP_THM]);

(* Theorem: [Solve left unknown] x * y = z <=> x = z * |/y *)
(* Another proof:
   If part: x * y = z ==> x = z * |/y
     x * y = z
           = z * #e           by group_rid
           = z * ( |/y * y)   by group_linv
           = (z * |/y) * y    by group_assc
     hence x = z * |/y        by group_rcancel
   Only-if part: x = z * |/y ==> x * y = z
     x * y = (z * |/y) * y    by substituting x
           = z * ( |/y * y)   by group_assoc
           = z * #e           by group_linv
           = z                by group_rid
*)
(* still, the first proof is easier. *)

(* Theorem: [Solve right unknown] x * y = z <=> y = |/x * z *)
(* Proof:
   If part: x * y = z ==> y = |/x * z
      |/x * z
    = |/x * (x * y)    by substituting z
    = y                by group_linv_assoc
   Only-if part: y = |/x * z ==> x * y = z
      x * y
    = x ( |/x * z)     by substituting y
    = z                by group_linv_assoc
*)
val group_rsolve = store_thm(
  "group_rsolve",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = z) = (y = |/x * z))``,
  rw[group_linv_assoc, EQ_IMP_THM]);

(* Theorem: [Left identity unique] y * x = x <=> y = #e *)
(* Proof:
       y * x = x
   <=> y = x * |/x   by group_lsolve
         = #e        by group_rinv
   Another proof:
       y * x = x = #e * x    by group_lid
           y = #e            by group_rcancel
*)
val group_lid_unique = store_thm(
  "group_lid_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((y * x = x) = (y = #e))``,
  rw[group_lsolve]);

(* Theorem: [Right identity unique] x * y = x <=> y = #e *)
(* Proof:
       x * y = x
   <=> y = |/x * x    by group_rsolve
         = #e         by group_linv
*)
val group_rid_unique = store_thm(
  "group_rid_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = x) = (y = #e))``,
  rw[group_rsolve]);

(* Theorem: Group identity is unique. *)
(* Proof: from group_ild_unique and group_rid_unique. *)
val group_id_unique = store_thm(
  "group_id_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((y * x = x) = (y = #e)) /\ ((x * y = x) = (y = #e))``,
  rw[group_lid_unique, group_rid_unique]);

(* Note: These are stronger claims than monoid_id_unique. *)

(* Theorem: [Left inverse unique] x * y = #e <=> x = |/y *)
(* Proof:
       x * y = #e
   <=> x = #e * |/y    by group_lsolve
         = |/ y        by group_lid
*)
val group_linv_unique = store_thm(
  "group_linv_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = #e) = (x = |/y))``,
  rw[group_lsolve]);

(* Theorem: [Right inverse unique] x * y = #e <=> y = |/x *)
(* Proof:
       x * y = #e
   <=> y = |/x * #e    by group_rsolve
         = |/x         by group_rid
*)
val group_rinv_unique = store_thm(
  "group_rinv_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = #e) = (y = |/x))``,
  rw[group_rsolve]);

(* Theorem: [Inverse of inverse] |/( |/ x) = x *)
(* Proof:
       x * |/x = #e      by group_rinv
   <=> x = |/x ( |/x)    by group_linv_unique
*)
val group_inv_inv = store_thm(
  "group_inv_inv",
  ``!g:'a group. Group g ==> !x. x IN G ==> ( |/( |/x) = x)``,
  metis_tac[group_rinv, group_linv_unique, group_inv_element]);

val _ = export_rewrites ["group_inv_inv"];

(* Theorem: [Inverse equal] |/x = |/y <=> x = y *)
(* Proof:
   Only-if part is trivial.
   For the if part: |/x = |/y ==> x = y
            |/x = |/y
   ==> |/( |/x) = |/( |/y)
   ==>        x = y         by group_inv_inv
*)
val group_inv_eq = store_thm(
  "group_inv_eq",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (( |/x = |/y) = (x = y))``,
  metis_tac[group_inv_inv]);

val _ = export_rewrites ["group_inv_eq"];

(* Theorem: [Inverse equality swap]: |/x = y <=> x = |/y *)
(* Proof:
            |/x = y
   <=> |/( |/x) = |/y
   <=>        x = |/y    by group_inv_inv
*)
val group_inv_eq_swap = store_thm(
  "group_inv_eq_swap",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (( |/x = y) = (x = |/y))``,
  metis_tac[group_inv_inv]);

val _ = export_rewrites ["group_inv_eq_swap"];

(* Theorem: [Inverse of identity] |/#e = #e *)
(* Proof:
       #e * #e = #e    by group_id_id
   <=>      #e = |/#e  by group_linv_unique
*)
val group_inv_id = store_thm(
  "group_inv_id",
  ``!g:'a group. Group g ==> ( |/ #e = #e)``,
  metis_tac[group_lid, group_linv_unique, group_id_element]);

val _ = export_rewrites ["group_inv_id"];

(* Theorem: [Inverse equal identity] |/x = #e <=> x = #e *)
(* Proof:
      |/x = #e = |/#e    by group_inv_id
   <=>  x = #e           by group_inv_eq
*)
val group_inv_eq_id = store_thm(
  "group_inv_eq_id",
  ``!g:'a group. Group g ==> !x. x IN G ==> (( |/x = #e) = (x = #e))``,
  rw[]);

(* Theorem: [Inverse of product] |/(x * y) = |/y * |/x *)
(* Proof:
   First show this product:
     (x * y) * ( |/y * |/x)
   = ((x * y) * |/y) * |/x     by group_assoc
   = (x * (y * |/y)) * |/x     by group_assoc
   = (x * #e) * |/x            by group_rinv
   = x * |/x                   by group_rid
   = #e                        by group_rinv
   Hence |/(x y) = |/y * |/x   by group_rinv_unique.
*)
val group_inv_op = store_thm(
  "group_inv_op",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ( |/(x * y) = |/y * |/x)``,
  rpt strip_tac >>
  `(x * y) * ( |/y * |/x) = x * (y * |/y) * |/x` by rw[group_assoc] >>
  `_ = #e` by rw_tac std_ss[group_rinv, group_rid] >>
  pop_assum mp_tac >>
  rw[group_rinv_unique]);

(* Theorem: [Pair Reduction] Group g ==> (x * z) * |/ (y * z) = x * |/ y *)
(* Proof:
     (x * z) * |/ (y * z)
   = (x * z) * ( |/ z * |/ y)   by group_inv_op
   = ((x * z) * |/ z) * |/ y    by group_assoc
   = (x * (z * |/ z)) * |/ y    by group_assoc
   = (x * #e) * |/ y            by group_rinv
   = x * |/ y                   by group_rid
*)
val group_pair_reduce = store_thm(
  "group_pair_reduce",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * z) * |/ (y * z) = x * |/ y)``,
  rpt strip_tac >>
  `!a. a IN G ==> |/ a IN G` by rw[] >>
  `(x * z) * |/ (y * z) = (x * z) * ( |/ z * |/ y)` by rw_tac std_ss[group_inv_op] >>
  `_ = (x * (z * |/ z)) * |/ y` by rw[group_assoc] >>
  `_ = (x * #e) * |/ y` by rw_tac std_ss[group_rinv] >>
  `_ = x * |/ y` by rw_tac std_ss[group_rid] >>
  metis_tac[]);

(* Theorem: The identity is a fixed point: x * x = x ==> x = #e. *)
(* Proof:
   For the if part:
       x * x = x
   ==> x * x = #e * x     by group_lid
   ==> x = #e             by group_rcancel
   For the only-if part:
       #e * #e = #e       by group_id_id
*)
val group_id_fix = store_thm(
  "group_id_fix",
  ``!g:'a group. Group g ==> !x. x IN G ==> ((x * x = x) = (x = #e))``,
  metis_tac[group_lid, group_rcancel, group_id_element]);

(* Theorem: Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x * y = #e) <=> (x = y)) *)
(* Proof:
   If part: |/ x * y = #e ==> x = y
   Note |/ x IN G                by group_inv_element
   Given  |/ x * y = #e
                 y = |/ ( |/ x)  by group_rinv_unique
                   = x           by group_inv_inv

   Only-if part: x = y ==> |/ x * y = #e
       True by group_linv.
*)
val group_op_linv_eq_id = store_thm(
  "group_op_linv_eq_id",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x * y = #e) <=> (x = y))``,
  rw[EQ_IMP_THM] >>
  metis_tac[group_inv_element, group_rinv_unique, group_inv_inv]);

(* Theorem: Group g ==> !x y. x IN G /\ y IN G ==> ((x * |/ y = #e) <=> (x = y)) *)
(* Proof:
   If part: x * |/ y = #e ==> x = y
   Note |/ x IN G                by group_inv_element
   Given  x * |/ y = #e
                 x = |/ ( |/ y)  by group_linv_unique
                   = y           by group_inv_inv

   Only-if part: x = y ==> x * |/ y = #e
       True by group_rinv.
*)
val group_op_rinv_eq_id = store_thm(
  "group_op_rinv_eq_id",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((x * |/ y = #e) <=> (x = y))``,
  rw[EQ_IMP_THM] >>
  metis_tac[group_inv_element, group_linv_unique, group_inv_inv]);

(* Theorem: Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (( |/ x * y = z) <=> (y = x * z)) *)
(* Proof:
   Note |/ x IN G                     by group_inv_element
                |/ x * y = z
   <=> x * (( |/ x) * y) = x * z      by group_lcancel
   <=>    (x * |/ x) * y = x * z      by group_assoc
   <=>            #e * y = x * z      by group_rinv
   <=>                 y = x * z      by group_lid
*)
val group_op_linv_eqn = store_thm(
  "group_op_linv_eqn",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (( |/ x * y = z) <=> (y = x * z))``,
  rpt strip_tac >>
  `|/ x IN G` by rw[] >>
  `( |/ x * y = z) <=> (x * ( |/ x * y) = x * z)` by rw[group_lcancel] >>
  `_ = ((x * |/ x) * y = x * z)` by rw[group_assoc] >>
  `_ = (y = x * z)` by rw[] >>
  rw[]);

(* Theorem: Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * |/ y = z) <=> (x = z * y)) *)
(* Proof:
   Note |/ y IN G                     by group_inv_element
                x * |/ y = z
   <=>    (x * |/ y) * y = z * y      by group_rcancel
   <=>   x * ( |/ y * y) = z * y      by group_assoc
   <=>           x * #e  = z * y      by group_linv
   <=>                 x = z * y      by group_rid
*)
val group_op_rinv_eqn = store_thm(
  "group_op_rinv_eqn",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * |/ y = z) <=> (x = z * y))``,
  rpt strip_tac >>
  `|/ y IN G` by rw[] >>
  `(x * |/ y = z) <=> ((x * |/ y) * y = z * y)` by rw[group_rcancel] >>
  `_ = (x * ( |/ y * y) = z * y)` by rw[group_assoc] >>
  `_ = (x = z * y)` by rw[] >>
  rw[]);

(* Theorem: Monoid g /\ x IN G* ==> ((Invertibles g).inv x = |/ x) *)
(* Proof:
   Note Group (Invertibles g)             by monoid_invertibles_is_group
    and (Invertibles g).op = g.op         by Invertibles_property
    and (Invertibles g).id = #e           by Invertibles_property
    and (Invertibles g).carrier = G*      by Invertibles_carrier
    Now ( |/ x) IN G*                     by monoid_inv_invertible
    and x * ( |/ x) = #e                  by monoid_inv_def
    ==> |/ x = (Invertibles g).inv x      by group_rinv_unique
*)
val Invertibles_inv = store_thm(
  "Invertibles_inv",
  ``!(g:'a monoid) x. Monoid g /\ x IN G* ==> ((Invertibles g).inv x = |/ x)``,
  rpt strip_tac >>
  `Group (Invertibles g)` by rw[monoid_invertibles_is_group] >>
  `(Invertibles g).carrier = G*` by rw[Invertibles_carrier] >>
  `( |/ x) IN G*` by rw[monoid_inv_invertible] >>
  `x * ( |/ x) = #e` by rw[monoid_inv_def] >>
  metis_tac[group_rinv_unique, Invertibles_property]);

(* Theorem: Monoid g ==> ( |/ #e = #e) *)
(* Proof:
   Note Group (Invertibles g)   by monoid_invertibles_is_group
    and #e IN G*                by monoid_id_invertible
   Thus |/ #e
      = (Invertibles g).inv #e                 by Invertibles_inv
      = (Invertibles g).inv (Invertibles g).id by Invertibles_property
      = (Invertibles g).id                     by group_inv_id
      = #e                                     by by Invertibles_property
*)
val monoid_inv_id = store_thm(
  "monoid_inv_id",
  ``!g:'a monoid. Monoid g ==> ( |/ #e = #e)``,
  rpt strip_tac >>
  `Group (Invertibles g)` by rw[monoid_invertibles_is_group] >>
  `(Invertibles g).id = #e` by rw[Invertibles_property] >>
  `#e IN G*` by rw[monoid_id_invertible] >>
  metis_tac[group_inv_id, Invertibles_inv]);

(* ------------------------------------------------------------------------- *)
(* Group Defintion without explicit mention of Monoid.                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Alternative Definition]
      Group g <=> #e IN G /\
               (!x y::(G). x * y IN G) /\
               (!x::(G). |/x IN G) /\
               (!x::(G). #e * x = x) /\
               (!x::(G). |/x * x = #e) /\
               (!x y z::(G). (x * y) * z = x * (y * z)) *)
(* Proof:
   Monoid needs the right identity:
     x * #e
   = (#e * x) * #e      by #e * x = x          left_identity
   = (x''x')x(x'x)      by #e = x' x = x'' x'  left_inverse
   = x''(x'x)(x'x)      by associativity
   = x''(x'x)           by #e * (x'x) = x'x    left_identity
   = (x''x')x           by associativity
   = #e * x             by #e = x''x'          left_inverse
   = x                  by #e * x = x          left_identity
   monoid_invertibles need right inverse:
     x * x'
   = (#e * x) * x'      by #e * x = x          left_identity
   = (x'' x')* x * x'   by #e = x''x'          left_inverse
   = x'' (x' x) x'      by associativity
   = x'' x'             by #e = x'x            left_inverse
   = #e                 by #e = x''x'          left_inverse
*)
val group_def_alt = store_thm(
  "group_def_alt",
  ``!g:'a group. Group g <=>
        (!x y. x IN G /\ y IN G ==> x * y IN G) /\
        (!x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y) * z = x * (y * z))) /\
         #e IN G /\
        (!x. x IN G ==> (#e * x = x)) /\
        (!x. x IN G ==> ?y. y IN G /\ (y * x = #e))``,
  rw[group_assoc, EQ_IMP_THM] >-
  metis_tac[group_linv, group_inv_element] >>
  rw_tac std_ss[Group_def, Monoid_def, monoid_invertibles_def, EXTENSION, EQ_IMP_THM, GSPECIFICATION] >| [
    `?y. y IN G /\ (y * x = #e)` by metis_tac[] >>
    `?z. z IN G /\ (z * y = #e)` by metis_tac[] >>
    `z * y * x = z * (y * x)` by rw_tac std_ss[],
    `?y. y IN G /\ (y * x = #e)` by metis_tac[] >>
    `?z. z IN G /\ (z * y = #e)` by metis_tac[] >>
    `z * y * x = z * (y * x)` by rw_tac std_ss[] >>
    `z * #e * y = z * (#e * y)` by rw_tac std_ss[]
  ] >> metis_tac[]);

(* Theorem: Group g <=> Monoid g /\ (!x. x IN G ==> ?y. y IN G /\ (y * x = #e)) *)
(* Proof:
   By Group_def and EXTENSION this is to show:
   (1) G* = G /\ x IN G ==> ?y. y IN G /\ (y * x = #e)
       Note x IN G ==> x IN G*          by G* = G
        ==> ?y. y IN G /\ (y * x = #e)  by monoid_invertibles_element
   (2) x IN G* ==> x IN G
       Note x IN G* ==> x IN G          by monoid_invertibles_element
   (3) (!x. x IN G ==> ?y. y IN G /\ (g.op y x = #e)) /\ x IN G ==> x IN G*
       Note ?y. y IN G /\ (y * x = #e)  by x IN G
         so ?z. z IN G /\ (z * y = #e)  by y IN G
            x
          = #e * x                      by monoid_lid
          = (z * y) * x                 by #e = z * y
          = z * (y * x)                 by monoid_assoc
          = z * #e                      by #e = y * x
          = z                           by monoid_rid
       Thus ?y. y * x = #e  /\ x * y = #e
         or x IN G*                     by monoid_invertibles_element
*)
val group_def_by_inverse = store_thm(
  "group_def_by_inverse",
  ``!g:'a group. Group g <=> Monoid g /\ (!x. x IN G ==> ?y. y IN G /\ (y * x = #e))``,
  rw_tac std_ss[Group_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[monoid_invertibles_element] >-
  metis_tac[monoid_invertibles_element] >>
  `?y. y IN G /\ (y * x = #e)` by rw[] >>
  `?z. z IN G /\ (z * y = #e)` by rw[] >>
  `z * y * x = z * (y * x)` by rw_tac std_ss[monoid_assoc] >>
  `x = z` by metis_tac[monoid_lid, monoid_rid] >>
  metis_tac[monoid_invertibles_element]);

(* Alternative concise definition of a group. *)

(* Theorem: Group g <=>
            (!x y::G. x * y IN G) /\
            (!x y z::G. x * y * z = x * (y * z)) /\
             #e IN G /\ (!x::G. #e * x = x) /\
             !x::G. |/ x IN G /\ |/ x * x = #e *)
(* Proof: by group_def_alt, group_inv_element. *)
Theorem group_alt:
  !(g:'a group). Group g <=>
          (!x y::G. x * y IN G) /\ (* closure *)
          (!x y z::G. x * y * z = x * (y * z)) /\ (* associativity *)
          #e IN G /\ (!x::G. #e * x = x) /\ (* identity *)
          !x::G. |/ x IN G /\ |/ x * x = #e
Proof
  rw[group_def_alt, group_inv_element, EQ_IMP_THM] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Transformation of Group structure by modifying carrier.                   *)
(* Useful for Field and Field Instances, include or exclude zero.            *)
(* ------------------------------------------------------------------------- *)

(* Include an element z (zero) for the carrier, usually putting group to monoid. *)
val including_def = zDefine`
   including (g:'a group) (z:'a) :'a monoid =
      <| carrier := G UNION {z};
              op := g.op;
              id := g.id
       |>
`;
val _ = set_fixity "including" (Infixl 600); (* like division / *)
(* > val including_def = |- !g z. including g z = <|carrier := G UNION {z}; op := $*; id := #e|> : thm *)

(* Exclude an element z (zero) from the carrier, usually putting monoid to group. *)
val excluding_def = zDefine`
   excluding (g:'a monoid) (z:'a) :'a group =
      <| carrier := G DIFF {z};
              op := g.op;
              id := g.id
       |>
`;
val _ = set_fixity "excluding" (Infixl 600); (* like division / *)
(* > val excluding_def = |- !g z. excluding g z = <|carrier := G DIFF {z}; op := $*; id := #e|> : thm *)
(*
- type_of ``g including z``;
> val it = ``:'a group`` : hol_type
- type_of ``g excluding z``;
> val it = ``:'a group`` : hol_type
*)

(* Theorem: (g including z).op = g.op /\ (g including z).id = g.id /\
            !x. x IN (g including z).carrier = x IN G \/ (x = z) *)
(* Proof: by IN_UNION, IN_SING. *)
val group_including_property = store_thm(
  "group_including_property",
  ``!g:'a group. !z:'a. ((g including z).op = g.op) /\
                        ((g including z).id = g.id) /\
                        (!x. x IN (g including z).carrier ==> x IN G \/ (x = z))``,
  rw[including_def]);

(* Theorem: (g excluding z).op = g.op /\ (g excluding z).id = g.id /\
            !x. x IN (g excluding z).carrier = x IN G /\ (x <> z) *)
(* Proof: by IN_DIFF, IN_SING. *)
val group_excluding_property = store_thm(
  "group_excluding_property",
  ``!g:'a group. !z:'a. ((g excluding z).op = g.op) /\
                        ((g excluding z).id = g.id) /\
                        (!x. x IN (g excluding z).carrier ==> x IN G /\ (x <> z))``,
  rw[excluding_def]);

(* Theorem: ((g including z) excluding z).op = g.op /\ ((g including z) excluding z).id = g.id /\
            If z NOTIN G, then ((g including z) excluding z).carrier = G. *)
(* Proof:
   If z NOTIN G,
   then G UNION {z} DIFF {z} = G    by IN_UNION, IN_DIFF, IN_SING.
*)
val group_including_excluding_property = store_thm(
  "group_including_excluding_property",
  ``!g:'a group. !z:'a. (((g including z) excluding z).op = g.op) /\
                        (((g including z) excluding z).id = g.id) /\
                        (z NOTIN G ==> (((g including z) excluding z).carrier = G))``,
  rw_tac std_ss[including_def, excluding_def] >>
  rw[EXTENSION, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: If z NOTIN G, then Group g = Group ((g including z) excluding z). *)
(* Proof: by group_including_excluding_property. *)
val group_including_excluding_group = store_thm(
  "group_including_excluding_group",
  ``!g:'a group. !z:'a. z NOTIN G ==> (Group g = Group ((g including z) excluding z))``,
  rw_tac std_ss[group_def_alt, group_including_excluding_property]);

(* Theorem: If z NOTIN G, then AbelianGroup g = AbelianGroup ((g including z) excluding z). *)
(* Proof: by group_including_excluding_property. *)
val group_including_excluding_abelian = store_thm(
  "group_including_excluding_abelian",
  ``!g:'a group. !z:'a. z NOTIN G ==> (AbelianGroup g = AbelianGroup ((g including z) excluding z))``,
  rw_tac std_ss[AbelianGroup_def, group_def_alt, group_including_excluding_property]);

(* Theorem: g including z excluding z explicit expression. *)
(* Proof: by definition. *)
val group_including_excluding_eqn = store_thm(
  "group_including_excluding_eqn",
  ``!g:'a group. !z:'a. g including z excluding z = if z IN G then <| carrier := G DELETE z; op := g.op; id := g.id |> else g``,
  rw[including_def, excluding_def] >| [
    rw[EXTENSION] >>
    metis_tac[],
    rw[monoid_component_equality] >>
    rw[EXTENSION] >>
    metis_tac[]
  ]);
(* better -- Michael's solution *)
Theorem group_including_excluding_eqn[allow_rebind]:
  !g:'a group. !z:'a. g including z excluding z =
                      if z IN G then <| carrier := G DELETE z;
                                        op := g.op;
                                        id := g.id |>
                      else g
Proof
  rw[including_def, excluding_def] >>
  rw[monoid_component_equality] >>
  rw[EXTENSION] >> metis_tac[]
QED

(* Theorem: (g excluding z).op = g.op *)
(* Proof: by definition. *)
val group_excluding_op = store_thm(
  "group_excluding_op",
  ``!g:'a group. !z:'a. (g excluding z).op = g.op``,
  rw_tac std_ss[excluding_def]);

val _ = export_rewrites ["group_excluding_op"];
val _ = computeLib.add_persistent_funs ["group_excluding_op"];

(* Theorem: (g excluding z).exp x n = x ** n *)
(* Proof:
   By induction on n.
   Base: (g excluding z).exp x 0 = x ** 0
           (g excluding z).exp x 0
         = (g excluding z).id            by group_exp_0
         = #e                            by group_excluding_property
         = x ** 0                        by group_exp_0
   Step: (g excluding z).exp x n = x ** n ==> (g excluding z).exp x (SUC n) = x ** SUC n
         (g excluding z).exp x (SUC n)
       = (g excluding z).op x (g excluding z).exp x n   by group_exp_SUC
       = (g excluding z).op x (x ** n)                  by induction hypothesis
       = x * (x ** n)                                   by group_excluding_property
       = x ** SUC n                                     by group_exp_SUC
*)
val group_excluding_exp = store_thm(
  "group_excluding_exp",
  ``!(g:'a group) z x n. (g excluding z).exp x n = x ** n``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[group_excluding_property]);

(* Theorem: AbelianMonoid g ==>
           !z. z NOTIN G* ==> (monoid_invertibles (g excluding z) = G* ) *)
(* Proof:
   By monoid_invertibles_def, excluding_def, EXTENSION, this is to show:
   (1) x IN G /\ y IN G /\ y * x = #e ==> ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)
       True by properties of AbelianMonoid g.
   (2) z NOTIN G* /\ x IN G /\ y IN G /\ x * y = #e /\ y * x = #e ==> x <> z
       Note x IN G*                   by monoid_invertibles_element
       But  z NOTIN G*, so x <> z.
   (3) x IN G /\ y IN G /\ x * y = #e /\ y * x = #e ==> ?y. (y IN G /\ y <> z) /\ (x * y = #e) /\ (y * x = #e)
       Take the same y, then y <> z   by monoid_invertibles_element
*)
val abelian_monoid_invertible_excluding = store_thm(
  "abelian_monoid_invertible_excluding",
  ``!g:'a monoid. AbelianMonoid g ==>
   !z. z NOTIN G* ==> (monoid_invertibles (g excluding z) = G* )``,
  rw_tac std_ss[AbelianMonoid_def] >>
  rw[monoid_invertibles_def, excluding_def, EXTENSION] >>
  rw[EQ_IMP_THM] >-
  metis_tac[] >-
  metis_tac[monoid_invertibles_element] >>
  metis_tac[monoid_invertibles_element]);

(* ------------------------------------------------------------------------- *)
(* Group Exponentiation with Inverses.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Inverse of exponential:  |/(x ** n) = ( |/x) ** n *)
(* Proof:
   By induction on n.
   Base case: |/ (x ** 0) = |/ x ** 0
     |/ (x ** 0)
   = |/ #e            by group_exp_zero
   = #e               by group_inv_id
   = ( |/ #e) ** 0    by group_exp_zero
   Step case: |/ (x ** n) = |/ x ** n ==> |/ (x ** SUC n) = |/ x ** SUC n
     |/ (x ** SUC n)
   = |/ (x * (x ** n))        by group_exp_SUC
   = ( |/ (x ** n)) * ( |/x)  by group_inv_op
   = ( |/x) ** n * ( |/x)     by inductive hypothesis
   = ( |/x) * ( |/x) ** n     by group_exp_comm
   = ( |/x) ** SUC n          by group_exp_SUC
*)
val group_exp_inv = store_thm(
  "group_exp_inv",
  ``!g:'a group. Group g ==> !x. x IN G ==> !n. |/ (x ** n) = ( |/ x) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[group_exp_SUC, group_inv_op, group_exp_comm, group_inv_element, group_exp_element]);

(* Theorem: Exponential of Inverse:  ( |/x) ** n = |/(x ** n) *)
(* Proof: by group_exp_inv. *)
val group_inv_exp = store_thm(
  "group_inv_exp",
  ``!g:'a group. Group g ==> !x. x IN G ==> !n. ( |/ x) ** n = |/ (x ** n)``,
  rw[group_exp_inv]);

(* Theorem: For m < n, x ** m = x ** n ==> x ** (n-m) = #e *)
(* Proof:
     x ** (n-m) * x ** m
   = x ** ((n-m) + m)         by group_exp_add
   = x ** n                   by arithmetic, m < n
   = x ** m                   by given
   Hence x ** (n-m) = #e      by group_lid_unique
*)
val group_exp_eq = store_thm(
  "group_exp_eq",
  ``!g:'a group. Group g ==> !x. x IN G ==> !m n. m < n /\ (x ** m = x ** n) ==> (x ** (n-m) = #e)``,
  rpt strip_tac >>
  `(n-m) + m = n` by decide_tac >>
  `x ** (n-m) * x ** m = x ** ((n-m) + m)` by rw_tac std_ss[group_exp_add] >>
  pop_assum mp_tac >>
  rw_tac std_ss[group_lid_unique, group_exp_element]);

(* Theorem: Group g /\ x IN G ==> (x ** m) ** n = (x ** n) ** m *)
(* Proof:
     (x ** m) ** n
   = x ** (m * n)    by group_exp_mult
   = x ** (n * m)    by MULT_COMM
   = (x ** n) ** m   by group_exp_mult
*)
val group_exp_mult_comm = store_thm(
  "group_exp_mult_comm",
  ``!g:'a group. Group g ==> !x. x IN G ==> !m n. (x ** m) ** n = (x ** n) ** m``,
  metis_tac[group_exp_mult, MULT_COMM]);

(* group_exp_mult is exported, never export a commutative version. *)

(* Theorem: Group /\ x IN G /\ y IN G /\ x * y = y * x ==> (x ** n) * (y ** m) = (y ** m) * (x ** n) *)
(* Proof:
   By inducton on  m.
   Base case: x ** n * y ** 0 = y ** 0 * x ** n
   LHS = x ** n * y ** 0
       = x ** n * #e         by group_exp_0
       = x ** n              by group_rid
       = #e * x ** n         by group_lid
       = y ** 0 * x ** n     by group_exp_0
       = RHS
   Step case: x ** n * y ** m = y ** m * x ** n ==> x ** n * y ** SUC m = y ** SUC m * x ** n
   LHS = x ** n * y ** SUC m
       = x ** n * (y * y ** m)    by group_exp_SUC
       = (x ** n * y) * y ** m    by group_assoc
       = (y * x ** n) * y ** m    by group_comm_exp (with single y)
       = y * (x ** n * y ** m)    by group_assoc
       = y * (y ** m * x ** n)    by induction hypothesis
       = (y * y ** m) * x ** n    by group_assoc
       = y ** SUC m  * x ** n     by group_exp_SUC
       = RHS
*)
val group_comm_exp_exp = store_thm(
  "group_comm_exp_exp",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==> !n m. x ** n * y ** m = y ** m * x ** n``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[] >>
  `x ** n * y ** SUC m = x ** n * (y * y ** m)` by rw[] >>
  `_ = (x ** n * y) * y ** m` by rw[group_assoc] >>
  `_ = (y * x ** n) * y ** m` by metis_tac[group_comm_exp] >>
  `_ = y * (x ** n * y ** m)` by rw[group_assoc] >>
  `_ = y * (y ** m * x ** n)` by metis_tac[] >>
  rw[group_assoc]);

(* ------------------------------------------------------------------------- *)
(* Group Maps Documentation                                                  *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   homo_group g f   = homo_monoid g f
*)
(* Definitions and Theorems (# are exported):

   Homomorphisms, isomorphisms, endomorphisms, automorphisms and subgroups:
   GroupHomo_def   |- !f g h. GroupHomo f g h <=> (!x. x IN G ==> f x IN h.carrier) /\
                                                   !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))
   GroupIso_def    |- !f g h. GroupIso f g h <=> GroupHomo f g h /\ BIJ f G h.carrier
   GroupEndo_def   |- !f g. GroupEndo f g <=> GroupHomo f g g
   GroupAuto_def   |- !f g. GroupAuto f g <=> GroupIso f g g
   subgroup_def    |- !h g. subgroup h g <=> GroupHomo I h g

   Group Homomorphisms:
   group_homo_id       |- !f g h. Group g /\ Group h /\ GroupHomo f g h ==> (f #e = h.id)
   group_homo_element  |- !f g h. GroupHomo f g h ==> !x. x IN G ==> f x IN h.carrier
   group_homo_inv      |- !f g h. Group g /\ Group h /\ GroupHomo f g h ==> !x. x IN G ==> (f ( |/ x) = h.inv (f x))
   group_homo_cong     |- !g h. Group g /\ Group h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
                                (GroupHomo f1 g h <=> GroupHomo f2 g h)
   group_homo_I_refl   |- !g. GroupHomo I g g
   group_homo_trans    |- !g h k f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k
   group_homo_sym      |- !g h f. Group g /\ GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g
   group_homo_compose  |- !g h k f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k
   group_homo_is_monoid_homo
                       |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> MonoidHomo f g h
   group_homo_monoid_homo
                       |- !f g h. GroupHomo f g h /\ f #e = h.id <=> MonoidHomo f g h
   group_homo_exp      |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
                          !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n

   Group Isomorphisms:
   group_iso_property  |- !f g h. GroupIso f g h <=>
                                  GroupHomo f g h /\ !y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)
   group_iso_id        |- !f g h. Group g /\ Group h /\ GroupIso f g h ==> (f #e = h.id)
   group_iso_element   |- !f g h. GroupIso f g h ==> !x. x IN G ==> f x IN h.carrier
   group_iso_I_refl    |- !g. GroupIso I g g
   group_iso_trans     |- !g h k f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k
   group_iso_sym       |- !g h f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g
   group_iso_compose   |- !g h k f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k
   group_iso_is_monoid_iso
                       |- !g h f. Group g /\ Group h /\ GroupIso f g h ==> MonoidIso f g h
   group_iso_monoid_iso|- !f g h. GroupIso f g h /\ f #e = h.id <=> MonoidIso f g h
   group_iso_exp       |- !g h f. Group g /\ Group h /\ GroupIso f g h ==>
                          !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n
   group_iso_order     |- !g h f. Group g /\ Group h /\ GroupIso f g h ==>
                          !x. x IN G ==> (order h (f x) = ord x)
   group_iso_linv_iso  |- !g h f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g
   group_iso_bij       |- !g h f. GroupIso f g h ==> BIJ f G h.carrier
   group_iso_group     |- !g h f. Group g /\ GroupIso f g h /\ (f #e = h.id) ==> Group h
   group_iso_card_eq   |- !g h f. GroupIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)

   Group Automorphisms:
   group_auto_id       |- !f g. Group g /\ GroupAuto f g ==> (f #e = #e)
   group_auto_element  |- !f g. GroupAuto f g ==> !x. x IN G ==> f x IN G
   group_auto_compose  |- !g f1 f2. GroupAuto f1 g /\ GroupAuto f2 g ==> GroupAuto (f1 o f2) g
   group_auto_is_monoid_auto
                       |- !g f. Group g /\ GroupAuto f g ==> MonoidAuto f g
   group_auto_exp      |- !g f. Group g /\ GroupAuto f g ==>
                          !x. x IN G ==> !n. f (x ** n) = f x ** n
   group_auto_order    |- !g f. Group g /\ GroupAuto f g ==>
                          !x. x IN G ==> (ord (f x) = ord x)
   group_auto_I        |- !g. GroupAuto I g
   group_auto_linv_auto|- !g f. Group g /\ GroupAuto f g ==> GroupAuto (LINV f G) g
   group_auto_bij      |- !g f. GroupAuto f g ==> f PERMUTES G

   Subgroups:
   subgroup_eqn             |- !g h. subgroup h g <=> H SUBSET G /\
                               !x y. x IN H /\ y IN H ==> (h.op x y = x * y)
   subgroup_subset          |- !g h. subgroup h g ==> H SUBSET G
   subgroup_homo_homo       |- !g h k f. subgroup h g /\ GroupHomo f g k ==> GroupHomo f h k
   subgroup_reflexive       |- !g. subgroup g g
   subgroup_transitive      |- !g h k. subgroup g h /\ subgroup h k ==> subgroup g k
   subgroup_I_antisym       |- !g h. subgroup h g /\ subgroup g h ==> GroupIso I h g
   subgroup_carrier_antisym |- !g h. subgroup h g /\ G SUBSET H ==> GroupIso I h g
   subgroup_is_submoniod    |- !g h. Group g /\ Group h /\ subgroup h g ==> submonoid h g
   subgroup_order_eqn       |- !g h. Group g /\ Group h /\ subgroup h g ==>
                               !x. x IN H ==> (order h x = ord x)

   Homomorphic Image of a Group:
   homo_group_closure |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==>
                         !x y. x IN fG /\ y IN fG ==> x o y IN fG
   homo_group_assoc   |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==>
                         !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o y o z)
   homo_group_id      |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==> #i IN fG /\
                         !x. x IN fG ==> (#i o x = x) /\ (x o #i = x)
   homo_group_inv     |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==>
                         !x. x IN fG ==> ?z. z IN fG /\ (z o x = #i)
   homo_group_group   |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==> Group (homo_group g f)
   homo_group_comm    |- !g f. AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
                         !x y. x IN fG /\ y IN fG ==> (x o y = y o x)
   homo_group_abelian_group  |- !g f. AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
                                      AbelianGroup (homo_group g f)
   homo_group_by_inj         |- !g f. Group g /\ INJ f G univ(:'b) ==> GroupHomo f g (homo_group g f)

   Injective Image of Group:
   group_inj_image_group           |- !g f. Group g /\ INJ f G univ(:'b) ==> Group (monoid_inj_image g f)
   group_inj_image_abelian_group   |- !g f. AbelianGroup g /\ INJ f G univ(:'b) ==> AbelianGroup (monoid_inj_image g f)
   group_inj_image_excluding_group
                               |- !g f e. Group (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
                                          Group (monoid_inj_image g f excluding f e)
   group_inj_image_excluding_abelian_group
                               |- !g f e. AbelianGroup (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
                                          AbelianGroup (monoid_inj_image g f excluding f e)
   group_inj_image_group_homo  |- !g f. INJ f G univ(:'b) ==> GroupHomo f g (monoid_inj_image g f)
*)

(* ------------------------------------------------------------------------- *)
(* Homomorphisms, isomorphisms, endomorphisms, automorphisms and subgroups.  *)
(* ------------------------------------------------------------------------- *)

(* A function f from g to h is a homomorphism if group properties are preserved. *)
(* For group, no need to ensure that identity is preserved, see group_homo_id.   *)

val GroupHomo_def = Define`
  GroupHomo (f:'a -> 'b) (g:'a group) (h:'b group) <=>
    (!x. x IN G ==> f x IN h.carrier) /\
    (!x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y)))
    (* no requirement for: f #e = h.id *)
`;

(* A function f from g to h is an isomorphism if f is a bijective homomorphism. *)
val GroupIso_def = Define`
  GroupIso f g h <=> GroupHomo f g h /\ BIJ f G h.carrier
`;

(* A group homomorphism from g to g is an endomorphism. *)
val GroupEndo_def = Define `GroupEndo f g <=> GroupHomo f g g`;

(* A group isomorphism from g to g is an automorphism. *)
val GroupAuto_def = Define `GroupAuto f g <=> GroupIso f g g`;

(* A subgroup h of g if identity is a homomorphism from h to g *)
val subgroup_def = Define `subgroup h g <=> GroupHomo I h g`;

(* ------------------------------------------------------------------------- *)
(* Group Homomorphisms                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> f #e = h.id *)
(* Proof:
   Since #e IN G                     by group_id_element,
   f (#e * #e) = h.op (f #e) (f #e)  by GroupHomo_def
   f #e = h.op (f #e) (f #e)         by group_id_id
   ==> f #e = h.id                   by group_id_fix
*)
val group_homo_id = store_thm(
  "group_homo_id",
  ``!f g h. Group g /\ Group h /\ GroupHomo f g h ==> (f #e = h.id)``,
  rw_tac std_ss[GroupHomo_def] >>
  `#e IN G` by rw[] >>
  metis_tac[group_id_fix, group_id_id]);

(* Theorem: GroupHomo f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by GroupHomo_def *)
val group_homo_element = store_thm(
  "group_homo_element",
  ``!f g h. GroupHomo f g h ==> !x. x IN G ==> f x IN h.carrier``,
  rw_tac std_ss[GroupHomo_def]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> f ( |/x) = h.inv (f x) *)
(* Proof:
   Since |/x IN G                      by group_inv_element
   f ( |/x * x) = h.op (f |/x) (f x)   by GroupHomo_def
   f (#e) = h.op (f |/x) (f x)         by group_linv
     h.id = h.op (f |/x) (f x)         by group_homo_id
   ==> f |/x = h.inv (f x)             by group_linv_unique
*)
val group_homo_inv = store_thm(
  "group_homo_inv",
  ``!f g h. Group g /\ Group h /\ GroupHomo f g h ==> !x. x IN G ==> (f ( |/x) = h.inv (f x))``,
  rpt strip_tac >>
  `|/x IN G` by rw_tac std_ss[group_inv_element] >>
  `f x IN h.carrier /\ f ( |/x) IN h.carrier` by metis_tac[GroupHomo_def] >>
  `h.op (f ( |/x)) (f x) = f ( |/x * x)` by metis_tac[GroupHomo_def] >>
  metis_tac[group_linv_unique, group_homo_id, group_linv]);

(* Theorem: Group g /\ Group h /\ (!x. x IN G ==> (f1 x = f2 x)) ==> (GroupHomo f1 g h = GroupHomo f2 g h) *)
(* Proof: by GroupHomo_def, group_op_element *)
val group_homo_cong = store_thm(
  "group_homo_cong",
  ``!(g:'a group) (h:'b group) f1 f2. Group g /\ Group h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
          (GroupHomo f1 g h = GroupHomo f2 g h)``,
  rw_tac std_ss[GroupHomo_def, EQ_IMP_THM] >-
  metis_tac[group_op_element] >>
  metis_tac[group_op_element]);

(* Theorem: GroupHomo I g g *)
(* Proof: by GroupHomo_def. *)
val group_homo_I_refl = store_thm(
  "group_homo_I_refl",
  ``!g:'a group. GroupHomo I g g``,
  rw[GroupHomo_def]);

(* Theorem: GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo f2 o f1 g k *)
(* Proof: true by GroupHomo_def. *)
val group_homo_trans = store_thm(
  "group_homo_trans",
  ``!(g:'a group) (h:'b group) (k:'c group).
    !f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k``,
  rw[GroupHomo_def]);

(* Theorem: Group g /\ GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g *)
(* Proof:
   Note BIJ f G h.carrier
    ==> BIJ (LINV f G) h.carrier G     by BIJ_LINV_BIJ
   By GroupHomo_def, this is to show:
   (1) x IN h.carrier ==> LINV f G x IN G
       With BIJ (LINV f G) h.carrier G
        ==> INJ (LINV f G) h.carrier G           by BIJ_DEF
        ==> x IN h.carrier ==> LINV f G x IN G   by INJ_DEF
   (2) x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       With x IN h.carrier
        ==> ?x1. (x = f x1) /\ x1 IN G           by BIJ_DEF, SURJ_DEF
       With y IN h.carrier
        ==> ?y1. (y = f y1) /\ y1 IN G           by BIJ_DEF, SURJ_DEF
        and x1 * y1 IN G                         by group_op_element
            LINV f G (h.op x y)
          = LINV f G (f (x1 * y1))                  by GroupHomo_def
          = x1 * y1                                 by BIJ_LINV_THM, x1 * y1 IN G
          = (LINV f G (f x1)) * (LINV f G (f y1))   by BIJ_LINV_THM, x1 IN G, y1 IN G
          = (LINV f G x) * (LINV f G y)             by x = f x1, y = f y1.
*)
val group_homo_sym = store_thm(
  "group_homo_sym",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g``,
  rpt strip_tac >>
  `BIJ (LINV f G) h.carrier G` by rw[BIJ_LINV_BIJ] >>
  fs[GroupHomo_def] >>
  rpt strip_tac >-
  metis_tac[BIJ_DEF, INJ_DEF] >>
  `?x1. (x = f x1) /\ x1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `?y1. (y = f y1) /\ y1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `g.op x1 y1 IN G` by rw[] >>
  metis_tac[BIJ_LINV_THM]);

Theorem group_homo_sym_any:
  Group g /\ GroupHomo f g h /\
  (!x. x IN h.carrier ==> i x IN g.carrier /\ f (i x) = x) /\
  (!x. x IN g.carrier ==> i (f x) = x)
  ==>
  GroupHomo i h g
Proof
  rpt strip_tac \\ fs[GroupHomo_def]
  \\ rpt strip_tac
  \\ `h.op x y = f (g.op (i x) (i y))` by metis_tac[]
  \\ pop_assum SUBST1_TAC
  \\ first_assum irule
  \\ PROVE_TAC[group_def_alt]
QED

(* Theorem: GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k *)
(* Proof: by GroupHomo_def *)
val group_homo_compose = store_thm(
  "group_homo_compose",
  ``!(g:'a group) (h:'b group) (k:'c group).
   !f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k``,
  rw_tac std_ss[GroupHomo_def]);
(* This is the same as group_homo_trans. *)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> MonoidHomo f g h *)
(* Proof:
   By MonoidHomo_def, this is to show:
   (1) x IN G ==> f x IN h.carrier, true                           by GroupHomo_def
   (2) x IN G /\ y IN G ==> f (x * y) = h.op (f x) (f y), true     by GroupHomo_def
   (3) Group g /\ Group h /\ GroupHomo f g h ==> f #e = h.id, true by group_homo_id
*)
val group_homo_is_monoid_homo = store_thm(
  "group_homo_is_monoid_homo",
  ``!g:'a group h f. Group g /\ Group h /\ GroupHomo f g h ==> MonoidHomo f g h``,
  rw[MonoidHomo_def] >-
  fs[GroupHomo_def] >-
  fs[GroupHomo_def] >>
  fs[group_homo_id]);

(* Theorem: (GroupHomo f g h /\ f #e = h.id) <=> MonoidHomo f g h *)
(* Proof: by MonoidHomo_def, GroupHomo_def. *)
Theorem group_homo_monoid_homo:
  !f g h. (GroupHomo f g h /\ f #e = h.id) <=> MonoidHomo f g h
Proof
  simp[MonoidHomo_def, GroupHomo_def] >>
  rw[EQ_IMP_THM]
QED

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof:
   Note Monoid g           by group_is_monoid
    and MonoidHomo f g h   by group_homo_is_monoid_homo
    The result follows     by monoid_homo_exp
*)
val group_homo_exp = store_thm(
  "group_homo_exp",
  ``!g:'a group h:'b group f. Group g /\ Group h /\ GroupHomo f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rw[group_is_monoid, group_homo_is_monoid_homo, monoid_homo_exp]);

(* ------------------------------------------------------------------------- *)
(* Group Isomorphisms                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: GroupIso f g h <=> GroupIHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)) *)
(* Proof:
   This is to prove:
   (1) BIJ f G H /\ y IN H ==> ?!x. x IN G /\ (f x = y)
       true by INJ_DEF and SURJ_DEF.
   (2) !y. y IN H /\ GroupHomo f g h ==> ?!x. x IN G /\ (f x = y) ==> BIJ f G H
       true by INJ_DEF and SURJ_DEF, and
       x IN G /\ GroupHomo f g h ==> f x IN H  by GroupHomo_def
*)
val group_iso_property = store_thm(
  "group_iso_property",
  ``!f g h. GroupIso f g h <=> GroupHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y))``,
  rw[GroupIso_def, EQ_IMP_THM] >-
  metis_tac[BIJ_THM] >>
  rw[BIJ_THM] >>
  metis_tac[GroupHomo_def]);

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> f #e = h.id *)
(* Proof:
   Since Group g, Group h ==> Monoid g, Monoid h   by group_is_monoid
   and GroupIso = WeakIso, GroupHomo = WeakHomo,
   this follows by monoid_iso_id.
*)
val group_iso_id = store_thm(
  "group_iso_id",
  ``!f g h. Group g /\ Group h /\ GroupIso f g h ==> (f #e = h.id)``,
  rw[monoid_weak_iso_id, group_is_monoid, GroupIso_def, GroupHomo_def, WeakIso_def, WeakHomo_def]);
(* However,
   this result is worse than (proved earlier):
- group_homo_id;
> val it = |- !f g h. Group g /\ Group h /\ GroupHomo f g h ==> (f #e = h.id) : thm
*)

(* Theorem: GroupIso f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by GroupIso_def, group_homo_element *)
val group_iso_element = store_thm(
  "group_iso_element",
  ``!f g h. GroupIso f g h ==> !x. x IN G ==> f x IN h.carrier``,
  metis_tac[GroupIso_def, group_homo_element]);

(* Theorem: GroupIso I g g *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo I g g, true by group_homo_I_refl
   (2) BIJ I R R, true by BIJ_I_SAME
*)
val group_iso_I_refl = store_thm(
  "group_iso_I_refl",
  ``!g:'a group. GroupIso I g g``,
  rw[GroupIso_def, group_homo_I_refl, BIJ_I_SAME]);

(* Theorem: GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g
       True by group_homo_trans.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE.
*)
val group_iso_trans = store_thm(
  "group_iso_trans",
  ``!(g:'a group) (h:'b group) (k:'c group).
    !f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k``,
  rw[GroupIso_def] >-
  metis_tac[group_homo_trans] >>
  metis_tac[BIJ_COMPOSE]);

(* Theorem: Group g ==> !f. GroupIso f g h ==> GroupIso (LINV f G) h g *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g
       True by group_homo_sym.
   (2) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val group_iso_sym = store_thm(
  "group_iso_sym",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g``,
  rw[GroupIso_def, group_homo_sym, BIJ_LINV_BIJ]);

(* Theorem: GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k
       True by group_homo_compose.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE
*)
val group_iso_compose = store_thm(
  "group_iso_compose",
  ``!(g:'a group) (h:'b group) (k:'c group).
   !f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k``,
  rw_tac std_ss[GroupIso_def] >-
  metis_tac[group_homo_compose] >>
  metis_tac[BIJ_COMPOSE]);
(* This is the same as group_iso_trans. *)

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> MonoidIso f g h *)
(* Proof: by GroupIso_def, MonoidIso_def, group_homo_is_monoid_homo *)
val group_iso_is_monoid_iso = store_thm(
  "group_iso_is_monoid_iso",
  ``!(g:'a group) (h:'b group) f. Group g /\ Group h /\ GroupIso f g h ==> MonoidIso f g h``,
  rw[GroupIso_def, MonoidIso_def] >>
  rw[group_homo_is_monoid_homo]);

(* Theorem: (GroupIso f g h /\ f #e = h.id) <=> MonoidIso f g h *)
(* Proof:
       MonioidIso f g h
   <=> MonoidHomo f g h /\ BIJ f G h.carrier                 by MonoidIso_def
   <=> GroupHomo f g h /\ f #e = h.id /\ BIJ f G h.carrier   by group_homo_monoid_homo
   <=> GroupIso f g h /\ f #e = h.id                         by GroupIso_def
*)
Theorem group_iso_monoid_iso:
  !f g h. (GroupIso f g h /\ f #e = h.id) <=> MonoidIso f g h
Proof
  simp[MonoidIso_def, GroupIso_def] >>
  metis_tac[group_homo_monoid_homo]
QED

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof:
   Note Monoid g           by group_is_monoid
    and MonoidIso f g h    by group_iso_is_monoid_iso
    The result follows     by monoid_iso_exp
*)
val group_iso_exp = store_thm(
  "group_iso_exp",
  ``!g:'a group h:'b group f. Group g /\ Group h /\ GroupIso f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rw[group_is_monoid, group_iso_is_monoid_iso, monoid_iso_exp]);

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> !x. x IN G ==> (order h (f x) = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h                    by group_is_monoid
    and MonoidIso f h g                         by group_iso_is_monoid_iso
   Thus !x. x IN H ==> (order h (f x) = ord x)  by monoid_iso_order
*)
val group_iso_order = store_thm(
  "group_iso_order",
  ``!(g:'a group) (h:'b group) f. Group g /\ Group h /\ GroupIso f g h ==>
    !x. x IN G ==> (order h (f x) = ord x)``,
  rw[group_is_monoid, group_iso_is_monoid_iso, monoid_iso_order]);

(* Theorem: Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g *)
(* Proof:
   By GroupIso_def, GroupHomo_def, this is to show:
   (1) BIJ f G h.carrier /\ x IN h.carrier ==> LINV f G x IN G
       True by BIJ_LINV_ELEMENT
   (2) BIJ f G h.carrier /\ x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       Let x' = LINV f G x, y' = LINV f G y.
       Then x' IN G /\ y' IN G        by BIJ_LINV_ELEMENT
         so x' * y' IN G              by group_op_element
        ==> f (x' * y') = h.op (f x') (f y')    by GroupHomo_def
                        = h.op x y              by BIJ_LINV_THM
       Thus LINV f G (h.op x y)
          = LINV f G (f (x' * y'))    by above
          = x' * y'                   by BIJ_LINV_THM
   (3) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val group_iso_linv_iso = store_thm(
  "group_iso_linv_iso",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g``,
  rw_tac std_ss[GroupIso_def, GroupHomo_def] >-
  metis_tac[BIJ_LINV_ELEMENT] >-
 (qabbrev_tac `x' = LINV f G x` >>
  qabbrev_tac `y' = LINV f G y` >>
  metis_tac[BIJ_LINV_THM, BIJ_LINV_ELEMENT, group_op_element]) >>
  rw_tac std_ss[BIJ_LINV_BIJ]);
(* This is the same as group_iso_sym. *)

(* Theorem: GroupIso f g h ==> BIJ f G h.carrier *)
(* Proof: by GroupIso_def *)
val group_iso_bij = store_thm(
  "group_iso_bij",
  ``!(g:'a group) (h:'b group) f. GroupIso f g h ==> BIJ f G h.carrier``,
  rw_tac std_ss[GroupIso_def]);

(* Note: read the discussion in group_iso_id for the condition: f #e = h.id:
   group_iso_id  |- !f g h. Group g /\ Group h /\ GroupIso f g h ==> (f #e = h.id)
*)
(* Theorem: Group g /\ GroupIso f g h /\ f #e = h.id ==> Group h  *)
(* Proof:
   This is to show:
   (1) x IN h.carrier /\ y IN h.carrier ==> h.op x y IN h.carrier
       Group g ==> Monoid g               by group_is_monoid
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
             ?y'. y' IN G /\ (f y' = y)   by group_iso_property
             h.op x y = f (x' * y')       by GroupHomo_def
       As                  x' * y' IN G   by group_op_element
       hence f (x' * y') IN h.carrier     by GroupHomo_def
   (2) x IN h.carrier /\ y IN h.carrier /\ z IN h.carrier ==> h.op (h.op x y) z = h.op x (h.op y z)
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
             ?y'. y' IN G /\ (f y' = y)   by group_iso_property
             ?z'. z' IN G /\ (f z' = z)   by group_iso_property
       as     x' * y' IN G                by group_op_element
       and f (x' * y') IN h.carrier       by GroupHomo_def
       ?!t. t IN G /\ f t = f (x' * y')   by group_iso_property
       i.e.  t = x' * y'                  by uniqueness
       hence h.op (h.op x y) z = f (x' * y' * z')
                                          by GroupHomo_def
       Similary,
       as     y' * z' IN G                by group_op_element
       and f (y' * z') IN h.carrier       by GroupHomo_def
       ?!s. s IN G /\ f s = f (y' * z')   by group_iso_property
       i.e.  s = y' * z'                  by uniqueness
       and   h.op x (h.op y z) = f (x' * (y' * z'))
                                          by GroupHomo_def
       hence true                         by group_assoc.
   (3) h.id IN h.carrier
       Since #e IN G                      by group_id_element
            (f #e) = h.id IN h.carrier    by GroupHomo_def
   (4) x IN h.carrier ==> h.op h.id x = x
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
       h.id IN h.carrier                  by group_id_element
       ?!e. e IN G /\ f e = h.id = f #e   by group_iso_property
       i.e. e = #e                        by uniqueness
       hence h.op h.id x = f (e * x')     by GroupHomo_def
                         = f (#e * x')
                         = f x'           by group_lid
                         = x
   (5) x IN h.carrier ==> ?y. y IN h.carrier /\ (h.op y x = h.id)
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
       so      |/ x' IN G                 by group_inv_element
       and  f ( |/ x') IN h.carrier       by GroupHomo_def
       Let y = f ( |/ x')
       then h.op y x = f ( |/ x' * x')    by GroupHomo_def
                     = f #e               by group_linv
                     = h.id
*)
val group_iso_group = store_thm(
  "group_iso_group",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupIso f g h /\ (f #e = h.id) ==> Group h``,
  rw[group_iso_property] >>
  `(!x. x IN G ==> f x IN h.carrier) /\ !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))`
    by metis_tac[GroupHomo_def] >>
  rw[group_def_alt] >| [
    metis_tac[group_op_element],
    `?x'. x' IN G /\ (f x' = x)` by metis_tac[] >>
    `?y'. y' IN G /\ (f y' = y)` by metis_tac[] >>
    `?z'. z' IN G /\ (f z' = z)` by metis_tac[] >>
    `?t. t IN G /\ (t = x' * y')` by metis_tac[group_op_element] >>
    `h.op (h.op x y) z = f (x' * y' * z')` by metis_tac[] >>
    `?s. s IN G /\ (s = y' * z')` by metis_tac[group_op_element] >>
    `h.op x (h.op y z) = f (x' * (y' * z'))` by metis_tac[] >>
    `x' * y' * z' = x' * (y' * z')` by rw[group_assoc] >>
    metis_tac[],
    metis_tac[group_id_element, GroupHomo_def],
    metis_tac[group_lid, group_id_element],
    metis_tac[group_linv, group_inv_element]
  ]);

(* Theorem: GroupIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier) *)
(* Proof: by GroupIso_def, FINITE_BIJ_CARD. *)
val group_iso_card_eq = store_thm(
  "group_iso_card_eq",
  ``!g:'a group h:'b group f. GroupIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)``,
  metis_tac[GroupIso_def, FINITE_BIJ_CARD]);

(* ------------------------------------------------------------------------- *)
(* Group Automorphisms                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ GroupAuto f g ==> (f #e = #e) *)
(* Proof: by GroupAuto_def, group_iso_id *)
val group_auto_id = store_thm(
  "group_auto_id",
  ``!f g. Group g /\ GroupAuto f g ==> (f #e = #e)``,
  rw_tac std_ss[GroupAuto_def, group_iso_id]);

(* Theorem: GroupAuto f g ==> !x. x IN G ==> f x IN G *)
(* Proof: by GroupAuto_def, group_iso_element *)
val group_auto_element = store_thm(
  "group_auto_element",
  ``!f g. GroupAuto f g ==> !x. x IN G ==> f x IN G``,
  metis_tac[GroupAuto_def, group_iso_element]);

(* Theorem: GroupAuto f1 g /\ GroupAuto f2 g ==> GroupAuto (f1 o f2) g *)
(* Proof: by GroupAuto_def, group_iso_compose *)
val group_auto_compose = store_thm(
  "group_auto_compose",
  ``!(g:'a group). !f1 f2. GroupAuto f1 g /\ GroupAuto f2 g ==> GroupAuto (f1 o f2) g``,
  metis_tac[GroupAuto_def, group_iso_compose]);

(* Theorem: Group g /\ GroupAuto f g ==> MonoidAuto f g *)
(* Proof: by GroupAuto_def, MonoidAuto_def, group_iso_is_monoid_iso *)
val group_auto_is_monoid_auto = store_thm(
  "group_auto_is_monoid_auto",
  ``!(g:'a group) f. Group g /\ GroupAuto f g ==> MonoidAuto f g``,
  rw[GroupAuto_def, MonoidAuto_def] >>
  rw[group_iso_is_monoid_iso]);

(* Theorem: Group g /\ GroupAuto f g ==> !x. x IN G ==> !n. f (x ** n) = (f x) ** n *)
(* Proof:
   Note Monoid g           by group_is_monoid
    and MonoidAuto f g     by group_auto_is_monoid_auto
    The result follows     by monoid_auto_exp
*)
val group_auto_exp = store_thm(
  "group_auto_exp",
  ``!g:'a group f. Group g /\ GroupAuto f g ==>
   !x. x IN G ==> !n. f (x ** n) = (f x) ** n``,
  rw[group_is_monoid, group_auto_is_monoid_auto, monoid_auto_exp]);

(* Theorem: Group g /\ GroupAuto f g ==> !x. x IN G ==> (order h (f x) = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h                  by group_is_monoid
    and MonoidAuto f h                        by group_auto_is_monoid_auto
   Thus !x. x IN H ==> (ord (f x) = ord x)    by monoid_auto_order
*)
val group_auto_order = store_thm(
  "group_auto_order",
  ``!(g:'a group) f. Group g /\ GroupAuto f g ==>
    !x. x IN G ==> (ord (f x) = ord x)``,
  rw[group_is_monoid, group_auto_is_monoid_auto, monoid_auto_order]);

(* Theorem: GroupAuto I g *)
(* Proof:
       GroupAuto I g
   <=> GroupIso I g g                 by GroupAuto_def
   <=> GroupHomo I g g /\ BIJ f G G   by GroupIso_def
   <=> T /\ BIJ f G G                 by GroupHomo_def, I_THM
   <=> T /\ T                         by BIJ_I_SAME
*)
val group_auto_I = store_thm(
  "group_auto_I",
  ``!(g:'a group). GroupAuto I g``,
  rw_tac std_ss[GroupAuto_def, GroupIso_def, GroupHomo_def, BIJ_I_SAME]);

(* Theorem: Group g /\ GroupAuto f g ==> GroupAuto (LINV f G) g *)
(* Proof:
       GroupAuto I g
   ==> GroupIso I g g                by GroupAuto_def
   ==> GroupIso (LINV f G) g         by group_iso_linv_iso
   ==> GroupAuto (LINV f G) g        by GroupAuto_def
*)
val group_auto_linv_auto = store_thm(
  "group_auto_linv_auto",
  ``!(g:'a group) f. Group g /\ GroupAuto f g ==> GroupAuto (LINV f G) g``,
  rw_tac std_ss[GroupAuto_def, group_iso_linv_iso]);

(* Theorem: GroupAuto f g ==> f PERMUTES G *)
(* Proof: by GroupAuto_def, GroupIso_def *)
val group_auto_bij = store_thm(
  "group_auto_bij",
  ``!g:'a group. !f. GroupAuto f g ==> f PERMUTES G``,
  rw_tac std_ss[GroupAuto_def, GroupIso_def]);

(* ------------------------------------------------------------------------- *)
(* Subgroups                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: subgroup h g <=> H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) *)
(* Proof:
       subgroup h g
   <=> GroupHomo I h g                                              by subgroup_def
   <=> (!x. x IN H ==> I x IN G) /\
       (!x y. x IN H /\ y IN H ==> (I (h.op x y) = (I x) * (I y)))  by GroupHomo_def
   <=> (!x. x IN H ==> x IN G) /\
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))              by I_THM
   <=> H SUBSET G
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))              by SUBSET_DEF
*)
val subgroup_eqn = store_thm(
  "subgroup_eqn",
  ``!(g:'a group) (h:'a group). subgroup h g <=>
     H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))``,
  rw_tac std_ss[subgroup_def, GroupHomo_def, SUBSET_DEF]);

(* Theorem: subgroup h g ==> H SUBSET G *)
(* Proof: by subgroup_eqn *)
val subgroup_subset = store_thm(
  "subgroup_subset",
  ``!(g:'a group) (h:'a group). subgroup h g ==> H SUBSET G``,
  rw_tac std_ss[subgroup_eqn]);

(* Theorem: subgroup h g /\ GroupHomo f g k ==> GroupHomo f h k *)
(* Proof:
   Note H SUBSET G              by subgroup_subset
     or !x. x IN H ==> x IN G   by SUBSET_DEF
   By GroupHomo_def, this is to show:
   (1) x IN H ==> f x IN k.carrier
       True                     by GroupHomo_def, GroupHomo f g k
   (2) x IN H /\ y IN H /\ f (h.op x y) = k.op (f x) (f y)
       Note x IN H ==> x IN G   by above
        and y IN H ==> y IN G   by above
         f (h.op x y)
       = f (x * y)              by subgroup_eqn
       = k.op (f x) (f y)       by GroupHomo_def
*)
val subgroup_homo_homo = store_thm(
  "subgroup_homo_homo",
  ``!(g:'a group) (h:'a group) (k:'b group) f. subgroup h g /\ GroupHomo f g k ==> GroupHomo f h k``,
  rw_tac std_ss[subgroup_def, GroupHomo_def]);

(* Theorem: subgroup g g *)
(* Proof:
   By subgroup_def, this is to show:
   GroupHomo I g g, true by group_homo_I_refl.
*)
val subgroup_reflexive = store_thm(
  "subgroup_reflexive",
  ``!g:'a group. subgroup g g``,
  rw[subgroup_def, group_homo_I_refl]);

(* Theorem: subgroup g h /\ subgroup h k ==> subgroup g k *)
(* Proof:
   By subgroup_def, this is to show:
   GroupHomo I g h /\ GroupHomo I h k ==> GroupHomo I g k
   Since I o I = I       by combinTheory.I_o_ID
   This is true          by group_homo_trans
*)
val subgroup_transitive = store_thm(
  "subgroup_transitive",
  ``!(g h k):'a group. subgroup g h /\ subgroup h k ==> subgroup g k``,
  prove_tac[subgroup_def, combinTheory.I_o_ID, group_homo_trans]);

(* Theorem: subgroup h g /\ subgroup g h ==> GroupIso I h g *)
(* Proof:
   By subgroup_def, GroupIso_def, this is to show:
      GroupHomo I h g /\ GroupHomo I g h ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by subgroup_subset, subgroup h g
   (2) x IN G ==> x IN H, true    by subgroup_subset, subgroup g h
*)
val subgroup_I_antisym = store_thm(
  "subgroup_I_antisym",
  ``!(g:'a monoid) h. subgroup h g /\ subgroup g h ==> GroupIso I h g``,
  rw_tac std_ss[subgroup_def, GroupIso_def] >>
  fs[GroupHomo_def] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: subgroup h g /\ G SUBSET H ==> GroupIso I h g *)
(* Proof:
   By subgroup_def, GroupIso_def, this is to show:
      GroupHomo I h g /\ G SUBSET H ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by subgroup_subset, subgroup h g
   (2) x IN G ==> x IN H, true    by G SUBSET H, given
*)
val subgroup_carrier_antisym = store_thm(
  "subgroup_carrier_antisym",
  ``!(g:'a group) h. subgroup h g /\ G SUBSET H ==> GroupIso I h g``,
  rpt (stripDup[subgroup_def]) >>
  rw_tac std_ss[GroupIso_def] >>
  `H SUBSET G` by rw[subgroup_subset] >>
  fs[GroupHomo_def, SUBSET_DEF] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: Group g /\ Group h /\ subgroup h g ==> submonoid h g *)
(* Proof:
   By subgroup_def, submonoid_def, this is to show:
      Group g /\ Group h /\ GroupHomo I h g ==> MonoidHomo I h g
   This is true by group_homo_is_monoid_homo
*)
val subgroup_is_submoniod = store_thm(
  "subgroup_is_submoniod",
  ``!g:'a group h. Group g /\ Group h /\ subgroup h g ==> submonoid h g``,
  rw[subgroup_def, submonoid_def] >>
  rw[group_homo_is_monoid_homo]);

(* Theorem: Group g /\ Group h /\ subgroup h g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h                  by group_is_monoid
    and submonoid h g                         by subgroup_is_submoniod
   Thus !x. x IN H ==> (order h x = ord x)    by submonoid_order_eqn
*)
val subgroup_order_eqn = store_thm(
  "subgroup_order_eqn",
  ``!g:'a group h. Group g /\ Group h /\ subgroup h g ==>
   !x. x IN H ==> (order h x = ord x)``,
  rw[group_is_monoid, subgroup_is_submoniod, submonoid_order_eqn]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image of a Group.                                             *)
(* ------------------------------------------------------------------------- *)

(* For those same as monoids, use overloading  *)
val _ = overload_on ("homo_group", ``homo_monoid``);

(* Theorem: [Closure] Group g /\ GroupHomo f g (homo_group g f) ==> x IN fG /\ y IN fG ==> x o y IN fG *)
(* Proof:
   x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y))  by homo_monoid_property
   Since   CHOICE (preimage f G x) IN G    by preimage_choice_property
           CHOICE (preimage f G y) IN G    by preimage_choice_property
   hence   CHOICE (preimage f G x) * CHOICE (preimage f G y) IN G      by group_op_element
   so    f (CHOICE (preimage f G x) * CHOICE (preimage f G y)) IN fG   by GroupHomo_def
*)
val homo_group_closure = store_thm(
  "homo_group_closure",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_group g f) ==>
     !x y. x IN fG /\ y IN fG ==> x o y IN fG``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_def, image_op_def] >>
  rw_tac std_ss[preimage_choice_property, group_op_element]);

(* Theorem: [Associative] Group g /\ GroupHomo f g (homo_group g f) ==>
            x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = x o (y o z) *)
(* Proof:
   By GroupHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
           CHOICE (preimage f G y) IN G /\ y = f (CHOICE (preimage f G y))   by preimage_choice_property
           CHOICE (preimage f G z) IN G /\ z = f (CHOICE (preimage f G z))   by preimage_choice_property
     (x o y) o z
   = (f (CHOICE (preimage f G x)) o f (CHOICE (preimage f G y))) o f (CHOICE (preimage f G z))   by expanding x, y, z
   = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)) o f (CHOICE (preimage f G z))         by homo_monoid_property
   = f (CHOICE (preimage f G x) * CHOICE (preimage f G y) * CHOICE (preimage f G z))             by homo_monoid_property
   = f (CHOICE (preimage f G x) * (CHOICE (preimage f G y) * CHOICE (preimage f G z)))           by group_assoc
   = f (CHOICE (preimage f G x)) o f (CHOICE (preimage f G y) * CHOICE (preimage f G z))         by homo_monoid_property
   = f (CHOICE (preimage f G x)) o (f (CHOICE (preimage f G y)) o f (CHOICE (preimage f G z)))   by homo_monoid_property
   = x o (y o z)                                                                                 by contracting x, y, z
*)
val homo_group_assoc = store_thm(
  "homo_group_assoc",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_group g f) ==>
   !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o (y o z))``,
  rw_tac std_ss[GroupHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==>
     (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw_tac std_ss[homo_monoid_property] >>
  `CHOICE (preimage f G x) IN G /\ (f (CHOICE (preimage f G x)) = x)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G y) IN G /\ (f (CHOICE (preimage f G y)) = y)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G z) IN G /\ (f (CHOICE (preimage f G z)) = z)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G x) * CHOICE (preimage f G y) IN G` by rw[] >>
  `CHOICE (preimage f G y) * CHOICE (preimage f G z) IN G` by rw[] >>
  `CHOICE (preimage f G x) * CHOICE (preimage f G y) * CHOICE (preimage f G z) =
   CHOICE (preimage f G x) * (CHOICE (preimage f G y) * CHOICE (preimage f G z))` by rw[group_assoc] >>
  metis_tac[]);

(* Theorem: [Identity] Group g /\ GroupHomo f g (homo_group g f) ==> #i IN fG /\ #i o x = x /\ x o #i = x. *)
(* Proof:
   By homo_monoid_property, #i = f #e, and #i IN fG.
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
   hence  #i o x
        = (f #e) o  f (preimage f G x)
        = f (#e * preimage f G x)       by homo_group_property
        = f (preimage f G x)            by group_lid
        = x
   similarly for x o #i = x             by group_rid
*)
val homo_group_id = store_thm(
  "homo_group_id",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_group g f) ==>
      #i IN fG /\ (!x. x IN fG ==> (#i o x = x) /\ (x o #i = x))``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_property] >| [
    rw[],
    metis_tac[group_lid, group_id_element, preimage_choice_property],
    metis_tac[group_rid, group_id_element, preimage_choice_property]
  ]);

(* Theorem: [Inverse] Group g /\ GroupHomo f g (homo_monoid g f) ==> x IN fG ==> ?z. z IN fG /\ z o x = #i. *)
(* Proof:
   x IN fG ==> CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
   Choose z = f ( |/ (preimage f G x)),
   then   z IN fG since |/ CHOICE (preimage f G x) IN G,
   and    z o x = f ( |/ (CHOICE (preimage f G x))) o f (CHOICE (preimage f G x))
                = f ( |/ (CHOICE (preimage f G x)) * CHOICE (preimage f G x))    by homo_monoid_property
                = f #e                                                           by group_lid
                = #i                                                             by homo_monoid_id
*)
val homo_group_inv = store_thm(
  "homo_group_inv",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_monoid g f) ==>
     !x. x IN fG ==> ?z. z IN fG /\ (z o x = #i)``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_property] >>
  `CHOICE (preimage f G x) IN G /\ (f (CHOICE (preimage f G x)) = x)` by metis_tac[preimage_choice_property] >>
  `|/ (CHOICE (preimage f G x)) IN G /\ ( |/ (CHOICE (preimage f G x)) * CHOICE (preimage f G x) = #e)` by rw[] >>
  qexists_tac `f ( |/ (CHOICE (preimage f G x)))` >>
  metis_tac[]);

(* Theorem: [Commutative] AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
            x IN fG /\ y IN fG ==> (x o y = y o x) *)
(* Proof:
   Note AbelianGroup g ==> Group g and
        !x y. x IN G /\ y IN G ==> (x * y = y * x)          by AbelianGroup_def
   By GroupHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
           CHOICE (preimage f G y) IN G /\ y = f (CHOICE (preimage f G y))   by preimage_choice_property
     x o y
   = f (CHOICE (preimage f G x)) o f (CHOICE (preimage f G y))   by expanding x, y
   = f (CHOICE (preimage f G x) * CHOICE (preimage f G y))       by homo_monoid_property
   = f (CHOICE (preimage f G y) * CHOICE (preimage f G x))       by AbelianGroup_def, above
   = f (CHOICE (preimage f G y)) o f (CHOICE (preimage f G x))   by homo_monoid_property
   = y o x                                                       by contracting x, y
*)
val homo_group_comm = store_thm(
  "homo_group_comm",
  ``!(g:'a group) (f:'a -> 'b). AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
   !x y. x IN fG /\ y IN fG ==> (x o y = y o x)``,
  rw_tac std_ss[AbelianGroup_def, GroupHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==> (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw[homo_monoid_property] >>
  `CHOICE (preimage f G x) IN G /\ (f (CHOICE (preimage f G x)) = x)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G y) IN G /\ (f (CHOICE (preimage f G y)) = y)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G x) * CHOICE (preimage f G y) = CHOICE (preimage f G y) * CHOICE (preimage f G x)` by rw[] >>
  metis_tac[]);

(* Theorem: Homomorphic image of a group is a group.
            Group g /\ GroupHomo f g (homo_monoid g f) ==> Group (homo_monoid g f) *)
(* Proof:
   This is to show each of these:
   (1) x IN fG /\ y IN fG ==> x o y IN fG    true by homo_group_closure
   (2) x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = (x o y) o z    true by homo_group_assoc
   (3) #i IN fG, true by homo_group_id
   (4) x IN fG ==> #i o x = x, true by homo_group_id
   (5) x IN fG ==> ?y. y IN fG /\ (y o x = #i), true by homo_group_inv
*)
val homo_group_group = store_thm(
  "homo_group_group",
  ``!(g:'a group) f. Group g /\ GroupHomo f g (homo_monoid g f) ==> Group (homo_monoid g f)``,
  rpt strip_tac >>
  rw[group_def_alt] >| [
    rw[homo_group_closure],
    rw[homo_group_assoc],
    rw[homo_group_id],
    rw[homo_group_id],
    rw[homo_group_inv]
  ]);

(* Theorem: Homomorphic image of an Abelian group is an Abelian group.
            AbelianGroup g /\ GroupHomo f g (homo_group g f) ==> AbelianGroup (homo_monoid g f) *)
(* Proof:
   Note AbelianGroup g ==> Group g                  by AbelianGroup_def
   By AbelianGroup_def, this is to show:
   (1) Group (homo_group g f), true                 by homo_group_group, Group g
   (2) x IN fG /\ y IN fG ==> x o y = y o x, true   by homo_group_comm, AbelianGroup g
*)
val homo_group_abelian_group = store_thm(
  "homo_group_abelian_group",
  ``!(g:'a group) f. AbelianGroup g /\ GroupHomo f g (homo_group g f) ==> AbelianGroup (homo_monoid g f)``,
  metis_tac[homo_group_group, AbelianGroup_def, homo_group_comm]);

(* Theorem: Group g /\ INJ f G UNIV ==> GroupHomo f g (homo_group g f) *)
(* Proof:
   By GroupHomo_def, homo_monoid_property, this is to show:
   (1) x IN G ==> f x IN IMAGE f G, true                 by IN_IMAGE
   (2) x IN G /\ y IN G ==> f (x * y) = f x o f y, true  by homo_monoid_op_inj
*)
val homo_group_by_inj = store_thm(
  "homo_group_by_inj",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ INJ f G UNIV ==> GroupHomo f g (homo_group g f)``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_property] >-
  rw[] >>
  rw[homo_monoid_op_inj]);

(* ------------------------------------------------------------------------- *)
(* Injective Image of Group.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Idea: Given a Group g, and an injective function f,
   then the image (f G) is a Group, with an induced binary operator:
        op := (\x y. f (f^-1 x * f^-1 y))  *)

(* Define a group injective image for an injective f, with LINV f G. *)
(* Since a group is a monoid, group injective image = monoid injective image *)

(* Theorem: Group g /\ INJ f G univ(:'b) ==> Group (monoid_inj_image g f) *)
(* Proof:
   By Group_def, this is to show:
   (1) Group g ==> Monoid (monoid_inj_image g f)
       Group g ==> Monoid g                            by group_is_monoid
               ==> Monoid (monoid_inj_image g f)       by monoid_inj_image_monoid
   (2) monoid_invertibles (monoid_inj_image g f) = (monoid_inj_image g f).carrier
       By monoid_invertibles_def, monoid_inj_image_def, this is to show:
       z IN G ==> ?y. (?x. (y = f x) /\ x IN G) /\
                  (f (t (f z) * t y) = f #e) /\ (f (t y * t (f z)) = f #e)
                                                       where t = LINV f G
      Note INJ f G univ(:'b) ==> BIJ f G (IMAGE f G)   by INJ_IMAGE_BIJ_ALT
        so !x. x IN G ==> t (f x) = x
       and !x. x IN (IMAGE f G) ==> f (t x) = x        by BIJ_LINV_THM
      Also z IN G ==> |/ z IN G                        by group_inv_element
       Put x = |/ z, and y = f x
      Then  f (t (f z) * t y)
          = f (t (f z) * t (f ( |/ z)))                by y = f ( |/ z)
          = f (z * |/ z)                               by !y. t (f y) = y
          = f #e                                       by group_inv_thm
        and f (t y * t (f z))
          = f (t (f ( |/ z)) * t (f z))                by y = f ( |/ z)
          = f ( |/ z * z)                              by !y. t (f y) = y
          = f #e                                       by group_inv_thm
*)
Theorem group_inj_image_group:
  !(g:'a group) (f:'a -> 'b). Group g /\ INJ f G univ(:'b) ==> Group (monoid_inj_image g f)
Proof
  rpt strip_tac >>
  rw_tac std_ss[Group_def] >-
  rw[monoid_inj_image_monoid] >>
  rw[monoid_invertibles_def, monoid_inj_image_def, EXTENSION, EQ_IMP_THM] >>
  `g.inv x' IN G` by rw[] >>
  qexists_tac `f (g.inv x')` >>
  `BIJ f G (IMAGE f G)` by rw[INJ_IMAGE_BIJ_ALT] >>
  imp_res_tac BIJ_LINV_THM >>
  metis_tac[group_inv_thm]
QED

(* Theorem: AbelianGroup g /\ INJ f G univ(:'b) ==> AbelianGroup (monoid_inj_image g f) *)
(* Proof:
   By AbelianGroup_def, this is to show:
   (1) Group g ==> Group (monoid_inj_image g f)
       True by group_inj_image_group.
   (2) (monoid_inj_image g f).op x y = (monoid_inj_image g f).op y x
       By monoid_inj_image_def, this is to show:
       x' IN G /\ x'' IN G /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
       ==> f (t (f x') * t (f x'')) = f (t (f x'') * t (f x'))  where t = LINV f G
       Note INJ f G univ(:'b) ==> BIJ f G (IMAGE f G)  by INJ_IMAGE_BIJ_ALT
         so !x. x IN G ==> t (f x) = x
        and !x. x IN (IMAGE f G) ==> f (t x) = x       by BIJ_LINV_THM
         f (t (f x') * t (f x''))
       = f (x' * x'')                                  by !y. t (f y) = y
       = f (x'' * x')                                  by commutativity condition
       = f (t (f x'') * t (f x'))                      by !y. t (f y) = y
*)
Theorem group_inj_image_abelian_group:
  !(g:'a group) (f:'a -> 'b). AbelianGroup g /\ INJ f G univ(:'b) ==>
       AbelianGroup (monoid_inj_image g f)
Proof
  rw[AbelianGroup_def] >-
  rw[group_inj_image_group] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[monoid_inj_image_def] >>
  metis_tac[INJ_IMAGE_BIJ_ALT, BIJ_LINV_THM]
QED

(* Theorem: Group (g excluding e) /\ INJ f G univ(:'b) /\ e IN G
            ==> Group (monoid_inj_image g f excluding f e) *)
(* Proof:
   Let h = g excluding e.
   Then H = h.carrier = G DIFF {e}             by excluding_def
    and h.op = g.op /\ h.id = g.id             by excluding_def
    and IMAGE f H = IMAGE f G DIFF {f e}       by IMAGE_DIFF
    and H SUBSET G                             by DIFF_SUBSET
   Let t = LINV f G.
   Then !x. x IN H ==> t (f x) = x             by LINV_SUBSET

   By group_def_alt, monoid_inj_image_def, excluding_def, this is to show:
   (1) x IN IMAGE f H /\ y IN IMAGE f H ==> f (t x * t y) IN IMAGE f H
       Note ?a. (x = f a) /\ a IN H            by IN_IMAGE
            ?b. (y = f b) /\ b IN H            by IN_IMAGE
       Hence  f (t x * t y)
            = f (t (f a) * t (f b))            by x = f a, y = f b
            = f (a * b)                        by !y. t (f y) = y
       Since a * b IN H                        by group_op_element
       hence f (a * b) IN IMAGE f H            by IN_IMAGE
   (2) x IN IMAGE f H /\ y IN IMAGE f H /\ z IN IMAGE f H ==> f (t x * t y * t z) = f (t x * (t y * t z))
       Note ?a. (x = f a) /\ a IN G            by IN_IMAGE
            ?b. (y = f b) /\ b IN G            by IN_IMAGE
            ?c. (z = f c) /\ c IN G            by IN_IMAGE
       Hence  (t x * t y) * t z
            = (t (f a) * t (f b)) * t (f c)    by x = f a, y = f b, z = f c
            = (a * b) * c                      by !y. t (f y) = y
            = a * (b * c)                      by group_assoc
            = t (f a) * (t (f b) * t (f c))    by !y. t (f y) = y
            = t x * (t y * t z)                by x = f a, y = f b, z = f c
       or   f ((t x * t y) * t z) = f (t x * (t y * t z))
   (3) f #e IN IMAGE f H
       Since #e IN H                           by group_id_element
       f #e IN IMAGE f H                       by IN_IMAGE
   (4) x IN IMAGE f H ==> f (t (f #e) * t x) = x
       Note #e IN H                            by group_id_element
        and ?a. (x = f a) /\ a IN H            by IN_IMAGE
       Hence f (t (f #e) * t x)
           = f (#e * t x)                      by !y. t (f y) = y
           = f (#e * t (f a))                  by x = f a
           = f (#e * a)                        by !y. t (f y) = y
           = f a                               by group_id
           = x                                 by x = f a
   (5) x IN IMAGE f H ==> ?y. y IN IMAGE f H /\ f (t y * t x) = f #e
       Note ?a. (x = f a) /\ a IN H            by IN_IMAGE
        and b = (h.inv a) IN H                 by group_inv_element
       Let y = f b.
       Then y IN IMAGE f H                     by IN_IMAGE
        and f (t y * t x)
          = f (t y * t (f a))                  by x = f a
          = f (t (f b)) * t (f a))             by y = f b
          = f (b * a)                          by !y. t (f y) = y
          = f #e                               by group_linv
*)
Theorem group_inj_image_excluding_group:
  !(g:'a group) (f:'a -> 'b) e.
      Group (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
      Group (monoid_inj_image g f excluding f e)
Proof
  rpt strip_tac >>
  qabbrev_tac `h = g excluding e` >>
  `h.carrier = G DIFF {e} /\ h.op = g.op /\ h.id = g.id` by rw[excluding_def, Abbr`h`] >>
  qabbrev_tac `Q = IMAGE f G DIFF {f e}` >>
  `H SUBSET G` by fs[] >>
  imp_res_tac LINV_SUBSET >>
  rw_tac std_ss[group_def_alt, monoid_inj_image_def, excluding_def] >| [
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    metis_tac[group_op_element, IN_IMAGE],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    `?a. (x = f a) /\ a IN H` by rw[GSYM IN_IMAGE] >>
    `?b. (y = f b) /\ b IN H` by rw[GSYM IN_IMAGE] >>
    `?c. (z = f c) /\ c IN H` by rw[GSYM IN_IMAGE] >>
    metis_tac[group_assoc, group_op_element],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    metis_tac[group_id_element, IN_IMAGE],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    metis_tac[group_id_element, group_id, IN_IMAGE],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    `?a. (x = f a) /\ a IN H` by rw[GSYM IN_IMAGE] >>
    `h.inv a IN H` by rw[group_inv_element] >>
    `f (h.inv a) IN Q` by rw[] >>
    metis_tac[group_linv]
  ]
QED

(* Theorem: AbelianGroup (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
            AbelianGroup (monoid_inj_image g f excluding f e) *)
(* Proof:
   By AbelianMonoid_def, this is to show:
   (1) Group (monoid_inj_image g f excluding f e)
       True by group_inj_image_excluding_group.
   (2) x IN IMAGE f H /\ y IN IMAGE f H ==> (monoid_inj_image g f).op x y = (monoid_inj_image g f).op y x
       where H = G DIFF {e}
       Note H SUBSET G                                     by DIFF_SUBSET
         so !x. x IN H ==> LINV f G (f x) = x              by LINV_SUBSET
        and (monoid_inj_image g f excluding f e).carrier
          = (IMAGE f G) DIFF {f e}                         by monoid_inj_image_def, excluding_def
          = IMAGE f (G DIFF {e})                           by IMAGE_DIFF
          = IMAGE f H                                      by notation
       By monoid_inj_image_def, excluding_def, this is to show:
          f (t x * t y) = f (t y * t x)                    where t = LINV f G
       Note ?a. x = f a /\ a IN H                          by IN_IMAGE
            ?b. y = f b /\ b IN H                          by IN_IMAGE
         f (t x * t y)
       = f (t (f a) * t (f b))                             by x = f a, y = f b
       = f (a * b)                                         by !y. t (f y) = y
       = f (b * a)                                         by commutativity condition
       = f (t (f b) * t (f a))                             by !y. t (f y) = y
       = f (t y * t x)                                     by y = f b, x = f a
*)
Theorem group_inj_image_excluding_abelian_group:
  !(g:'a group) (f:'a -> 'b) e.
      AbelianGroup (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
      AbelianGroup (monoid_inj_image g f excluding f e)
Proof
  rw[AbelianGroup_def] >-
  rw[group_inj_image_excluding_group] >>
  qabbrev_tac `h = g excluding e` >>
  `h.carrier = G DIFF {e} /\ h.op = g.op /\ h.id = g.id` by rw[excluding_def, Abbr`h`] >>
  `H SUBSET G` by fs[] >>
  imp_res_tac LINV_SUBSET >>
  `(monoid_inj_image g f excluding f e).carrier = IMAGE f G DIFF {f e}` by rw[monoid_inj_image_def, excluding_def] >>
  `_ = IMAGE f H` by rw[IMAGE_DIFF] >>
  simp[monoid_inj_image_def, excluding_def] >>
  metis_tac[IN_IMAGE]
QED

(* Theorem: INJ f G univ(:'b) ==> GroupHomo f g (monoid_inj_image g f) *)
(* Proof:
   Let s = IMAGE f G.
   Then BIJ f G s                              by INJ_IMAGE_BIJ_ALT
     so INJ f G s                              by BIJ_DEF

   By GroupHomo_def, monoid_inj_image_def, this is to show:
   (1) x IN G ==> f x IN IMAGE f G, true       by IN_IMAGE
   (2) x IN R /\ y IN R ==> f (x * y) = f (LINV f R (f x) * LINV f R (f y))
       Since LINV f R (f x) = x                by BIJ_LINV_THM
         and LINV f R (f y) = y                by BIJ_LINV_THM
       The result is true.
*)
Theorem group_inj_image_group_homo:
  !(g:'a group) f. INJ f G univ(:'b) ==> GroupHomo f g (monoid_inj_image g f)
Proof
  rw[GroupHomo_def, monoid_inj_image_def] >>
  qabbrev_tac `s = IMAGE f G` >>
  `BIJ f G s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f G s` by metis_tac[BIJ_DEF] >>
  metis_tac[BIJ_LINV_THM]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
