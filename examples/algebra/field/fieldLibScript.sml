(* ========================================================================= *)
(*  Field as Type                                                            *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;

open pred_setTheory pred_setLib newtypeTools numLib optionTheory hurdUtils;

open ringTheory ringLibTheory ringLib;
open fieldTheory fieldInstancesTheory;

val _ = new_theory "fieldLib";

val _ = prefer_num ();

val std_ss' = std_ss ++ PRED_SET_ss;

val _ = hide "one"; (* use ‘()’ instead *)

(* ------------------------------------------------------------------------- *)
(*  'a Field as type bijections of a subset of 'a option ring                *)
(* ------------------------------------------------------------------------- *)

Theorem EXISTS_Field[local] :
    ?r :'a option ring. Field r
Proof
    Q.EXISTS_TAC ‘trivial_field NONE (SOME ARB)’
 >> MP_TAC (ISPECL [“NONE :'a option”, “SOME (ARB :'a)”] trivial_field)
 >> rw [FiniteField_def]
QED

(* This defines a new type “:'a Field” *)
val Field_tydef = rich_new_type {tyname = "Field", exthm = EXISTS_Field,
                                 ABS = "toField", REP = "fromField"};

(* |- Field (fromField g) *)
Theorem Field_fromField[simp] = #termP_term_REP Field_tydef

(* |- !r. Field r ==> fromField (toField r) = r *)
Theorem from_toField = #repabs_pseudo_id Field_tydef

(* |- |- !a. toField (fromField a) = a *)
Theorem to_fromField[simp] = #absrep_id Field_tydef

(* |- !g h. fromField g = fromField h <=> g = h *)
Theorem fromField_11 = #term_REP_11 Field_tydef |> Q.GENL [‘g’, ‘h’]

Definition raw_field_def :
    raw_field ((c :'a set),zero,uno,add,mul) =
    raw_ring (IMAGE SOME c,SOME zero,SOME uno,OPTION_MAP2 add,OPTION_MAP2 mul)
End

Definition field_def :
    field = toField o raw_field
End

(* ------------------------------------------------------------------------- *)
(* The field operations, primitive plus subtraction as a derived operation.  *)
(* ------------------------------------------------------------------------- *)

Definition field_carrier_def :
    field_carrier (r :'a Field) = (fromField r).carrier
End

Definition field_0_def :
    field_0 (r :'a Field) = (fromField r).sum.id
End

Definition field_1_def :
    field_1 (r :'a Field) = (fromField r).prod.id
End

Definition field_neg_def :
    field_neg (r :'a Field) = (fromField r).sum.inv
End

Definition field_add_def :
    field_add (r :'a Field) = (fromField r).sum.op
End

Definition field_sub_def :
    field_sub (r :'a Field) = ring$ring_sub (fromField r)
End

Definition field_mul_def :
    field_mul (r :'a Field) = (fromField r).prod.op
End

Definition field_pow_def :
    field_pow (r :'a Field) = (fromField r).prod.exp
End

(* |- !r. field_inv r = Inv (fromField r) *)
Definition field_inv_def :
    field_inv (r :'a Field) = (Invertibles ((fromField r).prod)).inv
End

Definition field_div_def :
    field_div (r :'a Field) a b = field_mul r a (field_inv r b)
End

(* NOTE: The "primed" operators are only useful when NONE is not in the carrier.
   For instance, any field created by ‘field’ constructor is indeed this case.
 *)
Overload field_carrier' = “\(r :'a Field). IMAGE THE (field_carrier r)”
Overload field_0'       = “\(r :'a Field). THE (field_0 r)”
Overload field_1'       = “\(r :'a Field). THE (field_1 r)”
Overload field_neg' = “\(r :'a Field) a.   THE (field_neg r (SOME a))”
Overload field_inv' = “\(r :'a Field) a.   THE (field_inv r (SOME a))”
Overload field_add' = “\(r :'a Field) x y. THE (field_add r (SOME x) (SOME y))”
Overload field_sub' = “\(r :'a Field) x y. THE (field_sub r (SOME x) (SOME y))”
Overload field_mul' = “\(r :'a Field) x y. THE (field_mul r (SOME x) (SOME y))”
Overload field_div' = “\(r :'a Field) x y. THE (field_div r (SOME x) (SOME y))”
Overload field_pow' = “\(r :'a Field) x n. THE (field_pow r (SOME x) n)”

(* ------------------------------------------------------------------------- *)
(* Basic field theorems                                                      *)
(* ------------------------------------------------------------------------- *)

Theorem FIELD_0 :
    !r. field_0 r IN field_carrier (r :'a Field)
Proof
    Q.X_GEN_TAC ‘r0’
 >> Q.ABBREV_TAC ‘r = fromField r0’
 >> rw [field_0_def, field_carrier_def]
 >> MATCH_MP_TAC field_zero_element
 >> rw [Abbr ‘r’]
QED

Theorem FIELD_1 :
    !r. field_1 r IN field_carrier (r :'a Field)
Proof
    Q.X_GEN_TAC ‘r0’
 >> Q.ABBREV_TAC ‘r = fromField r0’
 >> rw [field_1_def, field_carrier_def]
 >> MATCH_MP_TAC field_one_element
 >> rw [Abbr ‘r’]
QED

Theorem FIELD_NE_01 :
    !r. field_0 r <> field_1 r
Proof
    Q.X_GEN_TAC ‘r0’
 >> Q.ABBREV_TAC ‘r = fromField r0’
 >> ‘Field r’ by rw [Abbr ‘r’]
 >> Know ‘IntegralDomain r’ >- rw [field_is_integral_domain]
 >> rw [field_0_def, field_1_def, IntegralDomain_def]
QED

val _ = export_theory();
val _ = html_theory "fieldLib";
