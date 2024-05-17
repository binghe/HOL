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
(*  'a Field as type bijections of a subset of 'a ring                       *)
(* ------------------------------------------------------------------------- *)

(* NOTE: It must be in form of ‘?r. P r’ *)
Theorem EXISTS_Field[local] :
    ?r :'a ring. (\r. (?zero one :'a. zero <> one) ==> Field r) r
Proof
    RW_TAC std_ss [RIGHT_EXISTS_IMP_THM]
 >> Q.EXISTS_TAC ‘trivial_field zero one’
 >> MP_TAC (Q.SPECL [‘zero’, ‘one’] trivial_field)
 >> rw [FiniteField_def]
QED

(* This defines a new type “:'a Field” *)
val Field_tydef = rich_new_type {tyname = "Field", exthm = EXISTS_Field,
                                 ABS = "toField", REP = "fromField"};

(* |- (?zero one. zero <> one) ==> Field (fromField g) *)
Theorem Field_fromField = #termP_term_REP Field_tydef |> BETA_RULE

(* |- !r. ((?zero one. zero <> one) ==> Field r) ==> fromField (toField r) = r *)
Theorem from_toField = #repabs_pseudo_id Field_tydef |> BETA_RULE

(* |- |- !a. toField (fromField a) = a *)
Theorem to_fromField = #absrep_id Field_tydef

(* |- !g h. fromField g = fromField h <=> g = h *)
Theorem fromField_11 = #term_REP_11 Field_tydef |> Q.GENL [‘g’, ‘h’]



val _ = export_theory();
val _ = html_theory "fieldLib";
