signature ringLib =
sig

   type term = Term.term
   type thm = Thm.thm
   type conv = Abbrev.conv
   type tactic = Abbrev.tactic

   (*
   val RING_RULE          : term -> thm
   val RING_TAC           : tactic
    *)
end
