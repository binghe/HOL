(* ========================================================================= *)
(*  Field as Type                                                            *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;

open pred_setTheory pred_setLib newtypeTools numLib;

open ringLibTheory ringLib;

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
Theorem Field_fromField = #termP_term_REP Field_tydef

(* |- !r. Field r ==> fromField (toField r) = r *)
Theorem from_toField = #repabs_pseudo_id Field_tydef

(* |- |- !a. toField (fromField a) = a *)
Theorem to_fromField[simp] = #absrep_id Field_tydef

(* |- !g h. fromField g = fromField h <=> g = h *)
Theorem fromField_11 = #term_REP_11 Field_tydef |> Q.GENL [‘g’, ‘h’]

Definition raw_field_def :
    raw_field ((c :'a set),zero,uno,add,mul) =
      let c' = IMAGE SOME c;
          add' = \x y. SOME (add (THE x) (THE y));
          mul' = \x y. SOME (mul (THE x) (THE y));
      in
          raw_ring (c',SOME zero,SOME uno,add',mul')
End

Definition field_def :
    field = toField o raw_field
End

val _ = export_theory();
val _ = html_theory "fieldLib";
