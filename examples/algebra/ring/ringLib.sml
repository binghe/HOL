(* ========================================================================= *)
(*  A decision procedure for the universal theory of rings                   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*                                                                           *)
(* Ported from HOL-Light (Library/ringtheory.ml) by Chun Tian on 29/01/2024  *)
(* ========================================================================= *)

structure ringLib :> ringLib =
struct
  open HolKernel boolLib bossLib cardinalTheory ringTheory ringLibTheory;

(*---------------------------------------------------------------------------*)
(* Establish the required grammar(s) for executing this file                 *)
(*---------------------------------------------------------------------------*)

structure Parse = struct
  open Parse
  val (Type,Term) =
      parse_from_grammars
        (apsnd ParseExtras.grammar_loose_equality ringLib_grammars)
end

open Parse;

(* ------------------------------------------------------------------------- *)
(* Derived rule to take a theorem asserting a monomorphism between r and r'  *)
(* and a term that is some Boolean combination of equations in the ring r    *)
(* and prove it equivalent to a "transferred" version in r' where all the    *)
(* variables x (in r) in the original map to "f x" (in r').                  *)
(* ------------------------------------------------------------------------- *)

(*
let RING_MONOMORPHIC_IMAGE_RULE =
  let pth = prove
   (`!r r' (f:A->B).
          ring_monomorphism(r,r') f
          ==> (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> (x = y <=> x' = y')) /\
              (!x. x IN ring_carrier r
                   ==> x IN ring_carrier r /\ f x = f x) /\
              (ring_0 r IN ring_carrier r /\ f(ring_0 r) = ring_0 r') /\
              (ring_1 r IN ring_carrier r /\ f(ring_1 r) = ring_1 r') /\
              (!n. ring_of_num r n IN ring_carrier r /\
                   f(ring_of_num r n) = ring_of_num r' n) /\
              (!n. ring_of_int r n IN ring_carrier r /\
                   f(ring_of_int r n) = ring_of_int r' n) /\
              (!x x'. x IN ring_carrier r /\ f x = x'
                      ==> ring_neg r x IN ring_carrier r /\
                          f(ring_neg r x) = ring_neg r' x') /\
              (!n x x'.
                  x IN ring_carrier r /\ f x = x'
                  ==> ring_pow r x n IN ring_carrier r /\
                      f(ring_pow r x n) = ring_pow r' x' n) /\
              (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> ring_add r x y IN ring_carrier r /\
                      f(ring_add r x y) = ring_add r' x' y') /\
              (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> ring_sub r x y IN ring_carrier r /\
                      f(ring_sub r x y) = ring_sub r' x' y') /\
              (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> ring_mul r x y IN ring_carrier r /\
                      f(ring_mul r x y) = ring_mul r' x' y')`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ring_monomorphism] THEN
    GEN_REWRITE_TAC LAND_CONV [CONJ_SYM] THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[RING_0; RING_1; RING_OF_NUM; RING_OF_INT; RING_NEG;
              RING_POW; RING_ADD; RING_SUB; RING_MUL;
              RING_HOMOMORPHISM_0; RING_HOMOMORPHISM_1;
              RING_HOMOMORPHISM_RING_OF_NUM; RING_HOMOMORPHISM_RING_OF_INT;
              RING_HOMOMORPHISM_NEG; RING_HOMOMORPHISM_POW;
              RING_HOMOMORPHISM_ADD; RING_HOMOMORPHISM_SUB;
              RING_HOMOMORPHISM_MUL]) in
  fun hth ->
    let [pth_eq; pth_asm;
         pth_0; pth_1; pth_num; pth_int;
         pth_neg; pth_pow;
         pth_add; pth_sub],pth_mul =
      splitlist CONJ_PAIR (MATCH_MP pth hth)
    and htm = rand(concl hth) in
    let rec mterm tm =
      match tm with
        Comb(Const("ring_0",_),_) ->
          pth_0
      | Comb(Const("ring_1",_),_) ->
          pth_1
      | Comb(Comb(Const("ring_of_num",_),_),n) ->
          SPEC n pth_num
      | Comb(Comb(Const("ring_of_int",_),_),n) ->
          SPEC n pth_int
      | Comb(Comb(Const("ring_neg",_),_),s) ->
          let sth = mterm s in
          MATCH_MP pth_neg sth
      | Comb(Comb(Comb(Const("ring_pow",_),_),s),n) ->
          let sth = mterm s in
          MATCH_MP (SPEC n pth_pow) sth
      | Comb(Comb(Comb(Const("ring_add",_),_),s),t) ->
          let sth = mterm s and tth = mterm t in
          MATCH_MP pth_add (CONJ sth tth)
      | Comb(Comb(Comb(Const("ring_sub",_),_),s),t) ->
          let sth = mterm s and tth = mterm t in
          MATCH_MP pth_sub (CONJ sth tth)
      | Comb(Comb(Comb(Const("ring_mul",_),_),s),t) ->
          let sth = mterm s and tth = mterm t in
          MATCH_MP pth_mul (CONJ sth tth)
      | _ -> UNDISCH(SPEC tm pth_asm) in
    let rec mform tm =
      if is_neg tm then
         RAND_CONV mform tm
      else if is_iff tm || is_imp tm || is_conj tm || is_disj tm then
         BINOP_CONV mform tm
      else if is_eq tm then
        let s,t = dest_eq tm in
        let sth = mterm s and tth = mterm t in
        MATCH_MP pth_eq (CONJ sth tth)
      else failwith "RING_MONOMORPHIC_IMAGE_RULE: unhandled formula" in
    mform;;
*)

(* ------------------------------------------------------------------------- *)
(* A decision procedure for the universal theory of rings, mapping           *)
(* momomorphically into a "total" ring to leverage earlier stuff.            *)
(* It will prove either the exact thing you request, or if you omit some     *)
(* carrier membership hypotheses, will add those as an antecedent.           *)
(* ------------------------------------------------------------------------- *)

end (* structure ringLib *)
