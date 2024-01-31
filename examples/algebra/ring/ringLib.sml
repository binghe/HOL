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



(* ------------------------------------------------------------------------- *)
(* A decision procedure for the universal theory of rings, mapping           *)
(* momomorphically into a "total" ring to leverage earlier stuff.            *)
(* It will prove either the exact thing you request, or if you omit some     *)
(* carrier membership hypotheses, will add those as an antecedent.           *)
(* ------------------------------------------------------------------------- *)

end (* structure ringLib *)
