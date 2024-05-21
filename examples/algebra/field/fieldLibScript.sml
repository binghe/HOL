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
(* The ring operations, primitive plus subtraction as a derived operation.   *)
(* ------------------------------------------------------------------------- *)

Definition field_carrier_def :
    field_carrier (r :'a Field) = IMAGE THE (fromField r).carrier
End

Definition field_0_def :
    field_0 (r :'a Field) = THE (fromField r).sum.id
End

Definition field_1_def :
    field_1 (r :'a Field) = THE (fromField r).prod.id
End

Definition field_neg_def :
    field_neg (r :'a Field) x = THE ((fromField r).sum.inv (SOME x))
End

Definition field_add_def :
    field_add (r :'a Field) x y = THE ((fromField r).sum.op (SOME x) (SOME y))
End

Definition field_sub_def :
    field_sub (r :'a Field) x y = THE (ring$ring_sub (fromField r) (SOME x) (SOME y))
End

Definition field_mul_def :
    field_mul (r :'a Field) x y = THE ((fromField r).prod.op (SOME x) (SOME y))
End

Definition field_pow_def :
    field_pow (r :'a Field) x n = THE ((fromField r).prod.exp (SOME x) n)
End

Theorem FIELD_0 :
    !r. field_0 r IN field_carrier (r :'a Field)
Proof
    Q.X_GEN_TAC ‘r0’
 >> Q.ABBREV_TAC ‘r = fromField r0’
 >> rw [field_0_def, field_carrier_def]
 >> Q.EXISTS_TAC ‘r.sum.id’ >> art []
 >> MATCH_MP_TAC field_zero_element
 >> rw [Abbr ‘r’]
QED

Theorem FIELD_1 :
    !r. field_1 r IN field_carrier (r :'a Field)
Proof
    Q.X_GEN_TAC ‘r0’
 >> Q.ABBREV_TAC ‘r = fromField r0’
 >> rw [field_1_def, field_carrier_def]
 >> Q.EXISTS_TAC ‘r.prod.id’ >> art []
 >> MATCH_MP_TAC field_one_element
 >> rw [Abbr ‘r’]
QED

(* NOTE: There's no way to guarantee that the underlying ‘Ring (r :'a option ring)’
   does not use ‘NONE’ as part of its carrier.

Theorem FIELD_01 :
    !r. field_0 r <> field_1 r
Proof
    Q.X_GEN_TAC ‘r0’
 >> Q.ABBREV_TAC ‘r = fromField r0’
 >> ‘Field r’ by rw [Abbr ‘r’]
 >> ‘IntegralDomain r’ by PROVE_TAC [field_is_integral_domain]
 >> rw [field_0_def, field_1_def]
 
 , IntegralDomain_def]
 >> POP_ASSUM (MP_TAC o Q.SPECL [‘r.prod.id’, ‘r.sum.id’])
 >> impl_tac
 >- (CONJ_TAC >|
     [ MATCH_MP_TAC field_one_element >> art [],
       MATCH_MP_TAC field_zero_element >> art [] ])
 >> rw []
 *)

val _ = export_theory();
val _ = html_theory "fieldLib";
