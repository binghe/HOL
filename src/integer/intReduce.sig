signature intReduce =
sig
  include Abbrev

  val add_int_compset : computeLib.compset -> unit
  val int_compset     : unit -> computeLib.compset

  val REDUCE_CONV : term -> thm
  val RED_CONV    : term -> thm

  val INT_REDUCE_ss : simpLib.ssfrag

  val collect_additive_consts : conv

  (* HOL-Light compatible conversions for int arith *)
  val INT_ADD_CONV : conv
  val INT_MUL_CONV : conv
  val INT_POW_CONV : conv

end
