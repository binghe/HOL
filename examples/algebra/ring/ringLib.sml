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
  val pth = RING_MONOMORPHIC_IMAGE_THM
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
