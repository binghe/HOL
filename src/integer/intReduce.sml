structure intReduce :> intReduce =
struct

open HolKernel boolLib integerTheory intSyntax simpLib Arithconv numeralTheory;

structure Parse = struct
  open Parse arithmeticTheory
  val (Type,Term) = parse_from_grammars integer_grammars
end

open Parse;

val ERR = mk_HOL_ERR "intReduce";
fun failwith function = raise (ERR function "");

(*---------------------------------------------------------------------------*)
(* Integer-specific compset                                                  *)
(*---------------------------------------------------------------------------*)

val elim_thms = [INT_ADD_REDUCE, INT_SUB_REDUCE, INT_MUL_REDUCE,
                 INT_DIV_REDUCE, INT_MOD_REDUCE, INT_EXP_REDUCE,
                 INT_LT_REDUCE, INT_LE_REDUCE, INT_EQ_REDUCE,
                 INT_GT_REDUCE, INT_GE_REDUCE, INT_DIVIDES_REDUCE,
                 INT_ABS_NUM, INT_ABS_NEG, INT_QUOT_REDUCE, INT_REM_REDUCE,
                 INT_MAX, INT_MIN, NUM_OF_INT]

fun add_int_compset cmp = computeLib.add_thms elim_thms cmp

fun int_compset () =
   let
       val cmp = reduceLib.num_compset()
   in
      add_int_compset cmp; cmp
   end

(*---------------------------------------------------------------------------*)
(* Reducer for ground integer expressions                                    *)
(*---------------------------------------------------------------------------*)

val REDUCE_CONV = computeLib.CBV_CONV (int_compset())

(*---------------------------------------------------------------------------*)
(* Add integer reductions to the global compset                              *)
(*---------------------------------------------------------------------------*)

val _ = let open computeLib in add_funs elim_thms end;

(*---------------------------------------------------------------------------*)
(* Ground reduction conversions for integers (suitable for inclusion in      *)
(* simplifier, or as stand-alone                                             *)
(*---------------------------------------------------------------------------*)

local
  val num_ty = numSyntax.num
  val int_ty = intSyntax.int_ty
  val x = mk_var("x",int_ty)
  val y = mk_var("y",int_ty)
  val n = mk_var("n",num_ty)
  val basic_op_terms =
     [plus_tm, minus_tm, mult_tm, div_tm, mod_tm, int_eq_tm,
      less_tm, leq_tm, greater_tm, geq_tm, divides_tm, rem_tm, quot_tm,
      min_tm, max_tm]
  val basic_op_patterns = map (fn t => list_mk_comb(t, [x,y])) basic_op_terms
  val exp_pattern = list_mk_comb(exp_tm, [x,n])
  val abs_patterns = [lhs (#2 (strip_forall (concl INT_ABS_NEG))),
                      lhs (#2 (strip_forall (concl INT_ABS_NUM)))]
  fun reducible t = is_int_literal t orelse numSyntax.is_numeral t
  fun reducer t =
    let val (_, args) = strip_comb t
    in if List.all reducible args then REDUCE_CONV t else Conv.NO_CONV t
    end
  fun mk_conv pat =
     {name = "Integer calculation",
      key = SOME([], pat), trace = 2,
      conv = K (K reducer)}
  val rederr = ERR "RED_CONV" "Term not reducible"
in
val INT_REDUCE_ss = SSFRAG
  {name=SOME"INT_REDUCE",
   convs = map mk_conv (exp_pattern::(abs_patterns @ basic_op_patterns)),
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

fun RED_CONV t =
 let val (f, args) = strip_comb t
     val _ = f ~~ exp_tm orelse tmem f basic_op_terms orelse raise rederr
     val _ = List.all reducible args orelse raise rederr
     val _ = not (Lib.can dom_rng (type_of t)) orelse raise rederr
 in
   REDUCE_CONV t
 end

end (* local *) ;

(*---------------------------------------------------------------------------*)
(* Add reducer to srw_ss                                                     *)
(*---------------------------------------------------------------------------*)

val _ = BasicProvers.logged_addfrags {thyname="integer"} [INT_REDUCE_ss];

(* Accumulate literal additions in integer expressions
    (doesn't do coefficient gathering - just adds up literals, and
     reassociates along the way)
*)
fun collect_additive_consts tm = let
  val summands = strip_plus tm
in
  case summands of
    [] => raise Fail "strip_plus returned [] in collect_additive_consts"
  | [_] => NO_CONV tm
  | _ => let
    in
      case partition is_int_literal summands of
        ([], _) => NO_CONV tm
      | ([_], _) => NO_CONV tm
      | (_, []) => REDUCE_CONV tm
      | (numerals, non_numerals) => let
          val reorder_t = mk_eq(tm,
                           mk_plus(list_mk_plus non_numerals,
                                   list_mk_plus numerals))
          val reorder_thm =
            EQT_ELIM(AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM) reorder_t)
        in
          (K reorder_thm THENC REDUCE_CONV THENC
           TRY_CONV (REWR_CONV INT_ADD_RID)) tm
        end
    end
end

(*-----------------------------------------------------------------------*)
(* INT_ADD_CONV "[x] + [y]" = |- [x] + [y] = [x+y]                       *)
(*-----------------------------------------------------------------------*)

(* NOTE: The following conversions are ported from HOL-Light's "int.ml". *)
local
  open Arbnum;
  val NUM_ADD_CONV = ADD_CONV;
  val neg_tm = negate_tm
  and amp_tm = int_injection
  and add_tm = plus_tm;
  val dest = dest_binop plus_tm (ERR "INT_ADD_CONV" "");
  val dest_numeral = numSyntax.dest_numeral
  and mk_numeral = numSyntax.mk_numeral;
  val m_tm = “m:num” and n_tm = “n:num”;
  val pth0 = prove
   (“(-(&m) + &m = &0) /\
     (&m + -(&m) = &0)”,
    REWRITE_TAC[INT_ADD_LINV, INT_ADD_RINV]);
  val [pth1, pth2, pth3, pth4, pth5, pth6] = (CONJUNCTS o prove)
   (“(-(&m) + -(&n) = -(&(m + n))) /\
     (-(&m) + &(m + n) = &n) /\
     (-(&(m + n)) + &m = -(&n)) /\
     (&(m + n) + -(&m) = &n) /\
     (&m + -(&(m + n)) = -(&n)) /\
     (&m + &n = &(m + n))”,
    REWRITE_TAC[GSYM INT_OF_NUM_ADD, INT_NEG_ADD] THEN
    REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID] THEN
    REWRITE_TAC[INT_ADD_RINV, INT_ADD_LID] THEN
    ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
    REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID] THEN
    REWRITE_TAC[INT_ADD_RINV, INT_ADD_LID]);
in
val INT_ADD_CONV =
  GEN_REWRITE_CONV I empty_rewrites[pth0] ORELSEC
  (fn tm =>
    let val (l,r) = dest tm in
        if rator l ~~ neg_tm then
          if rator r ~~ neg_tm then
            let val th1 = INST [m_tm |-> rand(rand l), n_tm |-> rand(rand r)] pth1;
                val tm1 = rand(rand(rand(concl th1)));
                val th2 = AP_TERM neg_tm (AP_TERM amp_tm (NUM_ADD_CONV tm1))
            in
              TRANS th1 th2
            end
          else (* l: neg, r: pos *)
            let val m = rand(rand l) and n = rand r;
                val m' = dest_numeral m and n' = dest_numeral n in
            if m' <= n' then
              let val p = mk_numeral (n' - m');
                  val th1 = INST [m_tm |-> m, n_tm |-> p] pth2;
                  val th2 = NUM_ADD_CONV (rand(rand(lhand(concl th1))));
                  val th3 = AP_TERM (rator tm) (AP_TERM amp_tm (SYM th2))
              in
                TRANS th3 th1
              end
            else
              let val p = mk_numeral (m' - n');
                  val th1 = INST [m_tm |-> n, n_tm |-> p] pth3;
                  val th2 = NUM_ADD_CONV (rand(rand(lhand(lhand(concl th1)))));
                  val th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2));
                  val th4 = AP_THM (AP_TERM add_tm th3) (rand tm)
              in
                TRANS th4 th1
              end
            end
        else (* l: pos *)
          if rator r ~~ neg_tm then
            let val m = rand l and n = rand(rand r);
                val m' = dest_numeral m and n' = dest_numeral n in
            if n' <= m' then
              let val p = mk_numeral (m' - n');
                  val th1 = INST [m_tm |-> n, n_tm |-> p] pth4;
                  val th2 = NUM_ADD_CONV (rand(lhand(lhand(concl th1))));
                  val th3 = AP_TERM add_tm (AP_TERM amp_tm (SYM th2));
                  val th4 = AP_THM th3 (rand tm)
              in
                TRANS th4 th1
              end
            else
              let val p = mk_numeral (n' - m');
                  val th1 = INST [m_tm |-> m, n_tm |-> p] pth5;
                  val th2 = NUM_ADD_CONV (rand(rand(rand(lhand(concl th1)))));
                  val th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2));
                  val th4 = AP_TERM (rator tm) th3
              in
                TRANS th4 th1
              end
            end
          else
            let val th1 = INST [m_tm |-> rand l, n_tm |-> rand r] pth6;
                val tm1 = rand(rand(concl th1));
                val th2 = AP_TERM amp_tm (NUM_ADD_CONV tm1)
            in
              TRANS th1 th2
            end
    end
    handle HOL_ERR _ => failwith "INT_ADD_CONV")
end (* local *)

(*-----------------------------------------------------------------------*)
(* INT_MUL_CONV "[x] * [y]" = |- [x] * [y] = [x * y]                     *)
(*-----------------------------------------------------------------------*)

local
  val pth0 = prove
     (“(&0 * &x = &0) /\
       (&0 * --(&x) = &0) /\
       (&x * &0 = &0) /\
       (-(&x) * &0 = &0)”,
      REWRITE_TAC[INT_MUL_LZERO, INT_MUL_RZERO]);
  val (pth1,pth2) = (CONJ_PAIR o prove)
     (“((&m * &n = &(m * n)) /\
        (-(&m) * -(&n) = &(m * n))) /\
       ((-(&m) * &n = -(&(m * n))) /\
        (&m * -(&n) = -(&(m * n))))”,
      REWRITE_TAC[INT_MUL_LNEG, INT_MUL_RNEG, INT_NEG_NEG] THEN
      REWRITE_TAC[INT_OF_NUM_MUL]);
  val NUM_MULT_CONV = MUL_CONV;
in
val INT_MUL_CONV =
    FIRST_CONV
     [GEN_REWRITE_CONV I empty_rewrites[pth0],
      GEN_REWRITE_CONV I empty_rewrites[pth1] THENC RAND_CONV NUM_MULT_CONV,
      GEN_REWRITE_CONV I empty_rewrites[pth2] THENC RAND_CONV(RAND_CONV NUM_MULT_CONV)];
end;

(*-----------------------------------------------------------------------*)
(* INT_POW_CONV "[x] EXP [y]" = |- [x] EXP [y] = [x ** y]                *)
(*-----------------------------------------------------------------------*)

local
  val (pth1,pth2) = (CONJ_PAIR o prove)
     (“(&x ** n = &(x ** n)) /\
       ((-(&x)) ** n = if EVEN n then &(x ** n) else -(&(x ** n)))”,
    REWRITE_TAC[INT_OF_NUM_POW, INT_POW_NEG]);
  val tth = prove
   (“((if T then x:int else y) = x) /\ ((if F then x:int else y) = y)”,
    REWRITE_TAC[]);
  val neg_tm = negate_tm;
  val NUM_EXP_CONV = EXP_CONV
  and NUM_EVEN_CONV = EVEN_CONV
in
val INT_POW_CONV =
  (GEN_REWRITE_CONV I empty_rewrites[pth1] THENC RAND_CONV NUM_EXP_CONV) ORELSEC
  (GEN_REWRITE_CONV I empty_rewrites[pth2] THENC
   RATOR_CONV(RATOR_CONV(RAND_CONV NUM_EVEN_CONV)) THENC
   GEN_REWRITE_CONV I empty_rewrites[tth] THENC
   (fn tm => if rator tm ~~ neg_tm then RAND_CONV(RAND_CONV NUM_EXP_CONV) tm
              else RAND_CONV NUM_EXP_CONV tm))
end;

end (* struct *)
