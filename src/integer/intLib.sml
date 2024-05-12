structure intLib :> intLib =
struct

open HolKernel boolLib bossLib;

open integerTheory intSimps Cooper Omega intSyntax intReduce Normalizer Grobner
     hurdUtils;

structure Parse = struct
  open Parse arithmeticTheory
  val (Type,Term) = parse_from_grammars integer_grammars
end

open Parse;

val ERR = mk_HOL_ERR "intLib";
fun failwith function = raise (ERR function "");

val operators = [("+", intSyntax.plus_tm),
                   ("-", intSyntax.minus_tm),
                   ("~", intSyntax.negate_tm),
                   ("numeric_negate", intSyntax.negate_tm),
                   ("*", intSyntax.mult_tm),
                   ("/", intSyntax.div_tm),
                   ("<", intSyntax.less_tm),
                   ("<=", intSyntax.leq_tm),
                   (">", intSyntax.greater_tm),
                   (">=", intSyntax.geq_tm),
                   ("**", intSyntax.exp_tm),
                   (GrammarSpecials.fromNum_str, intSyntax.int_injection),
                   (GrammarSpecials.num_injection, intSyntax.int_injection)];

fun deprecate_int () = let
  fun doit (s, t) =
     let val {Name,Thy,...} = dest_thy_const t in
        Parse.temp_send_to_back_overload s {Name = Name, Thy = Thy}
     end
in
  List.app doit operators
end

fun prefer_int () = let
  fun doit (s, t) =
     let val {Name,Thy,...} = dest_thy_const t in
        Parse.temp_bring_to_front_overload s {Name = Name, Thy = Thy}
     end
in
  List.app doit operators
end

val ARITH_CONV  = OMEGA_CONV;
val ARITH_TAC   = OMEGA_TAC;
val ARITH_PROVE = OMEGA_PROVE;

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer.                                               *)
(* ------------------------------------------------------------------------- *)

local
  val INT_ARITH_TAC = ARITH_TAC;
  val sth = prove
   (“(!x y z. x + (y + z) = (x + y) + z) /\
     (!x y. x + y = y + x) /\
     (!x. &0 + x = x) /\
     (!x y z. x * (y * z) = (x * y) * z) /\
     (!x y. x * y = y * x) /\
     (!x. &1 * x = x) /\
     (!x. &0 * x = &0) /\
     (!x y z. x * (y + z) = x * y + x * z) /\
     (!x. x ** 0 = &1) /\
     (!x n. x ** (SUC n) = x * x ** n)”,
    REWRITE_TAC[INT_POW] THEN INT_ARITH_TAC);
  val rth = prove
   (“(!x. -x = -(&1) * x) /\
     (!x y. x - y = x + -(&1) * y)”,
    INT_ARITH_TAC);
  val is_semiring_constant = is_int_literal
  and SEMIRING_ADD_CONV = INT_ADD_CONV
  and SEMIRING_MUL_CONV = INT_MUL_CONV
  and SEMIRING_POW_CONV = INT_POW_CONV;
  fun term_lt u t = (Term.compare(u,t) = LESS);
  val (_,_,_,_,_,POLY_CONV) =
    SEMIRING_NORMALIZERS_CONV sth rth
     (is_semiring_constant,
      SEMIRING_ADD_CONV,SEMIRING_MUL_CONV,SEMIRING_POW_CONV)
     term_lt
in
  val INT_POLY_CONV = POLY_CONV;
end;

(* ------------------------------------------------------------------------- *)
(* Instantiate the ring and ideal procedures.                                *)
(* ------------------------------------------------------------------------- *)

local
  val INT_ARITH_TAC = ARITH_TAC;
  val INT_INTEGRAL = prove
   (“(!x. &0 * x = &0) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))”,
    REWRITE_TAC[INT_MUL_LZERO, INT_EQ_LADD] THEN
    ONCE_REWRITE_TAC[GSYM INT_SUB_0] THEN
    REWRITE_TAC[GSYM INT_ENTIRE] THEN
    (* INT_ARITH_TAC cannot solve this?! *)
    rpt GEN_TAC \\
    Suff ‘w * y + x * z - (w * z + x * y) = (w - x) * (y - z)’
    >- (Rewr' >> REWRITE_TAC []) \\
    REWRITE_TAC [INT_ADD2_SUB2] \\
    REWRITE_TAC [GSYM INT_SUB_LDISTRIB] \\
   ‘x * (z - y) = -x * (y - z)’
     by (REWRITE_TAC [INT_MUL_LNEG, INT_SUB_LDISTRIB, INT_NEG_SUB]) >> POP_ORW \\
    REWRITE_TAC [GSYM INT_RDISTRIB, GSYM int_sub]);
  val dest_intconst = Arbrat.fromAInt o int_of_term;
  val mk_intconst = term_of_int o Arbrat.toAInt;
  val (pure,ideal) =
    RING_AND_IDEAL_CONV
      (dest_intconst,mk_intconst,INT_EQ_CONV,
       negate_tm, plus_tm, minus_tm,
       genvar bool, mult_tm, genvar bool, exp_tm,
       INT_INTEGRAL,TRUTH,INT_POLY_CONV)
in
  val INT_RING = pure;
  fun int_ideal_cofactors tms tm =
      if forall (fn t => type_of t = int_ty) (tm::tms)
      then ideal tms tm
      else failwith
             "int_ideal_cofactors: not all terms have type :int"
end;

(* ------------------------------------------------------------------------- *)
(* A tactic for simple divisibility/congruence/coprimality goals.            *)
(* ------------------------------------------------------------------------- *)
(*
local
  val INT_POLYEQ_CONV =
    GEN_REWRITE_CONV I empty_rewrites[GSYM INT_SUB_0] THENC LAND_CONV INT_POLY_CONV;
  val INT_ARITH = ARITH_PROVE;
  val ISOLATE_VARIABLE = let
    val pth = INT_ARITH “!a x. a = &0 <=> x = x + a”;
    fun is_defined v t =
      let val mons = HOLset.addList (empty_tmset,striplist(dest_binop "int_add") t) in
        HOLset.member(mons,v) andalso
        forall (fn m => v ~~ m orelse not(free_in v m)) (HOLset.listItems mons)
      end
  in
    fn vars tm =>
      let val th = INT_POLYEQ_CONV tm
          and th' = (SYM_CONV THENC INT_POLYEQ_CONV) tm;
          val (v,th1) =
              (find (fn v => is_defined v (lhand(rand(concl th)))) vars,th')
          with Failure _ ->
              find (fun v -> is_defined v (lhand(rand(concl th')))) vars,th in
      let th2 = TRANS th1 (SPECL [lhs(rand(concl th1)); v] pth) in
      CONV_RULE(RAND_CONV(RAND_CONV INT_POLY_CONV)) th2 in
  let UNWIND_POLYS_CONV tm =
    let vars,bod = strip_exists tm in
    let cjs = conjuncts bod in
    let th1 = tryfind (ISOLATE_VARIABLE vars) cjs in
    let eq = lhand(concl th1) in
    let bod' = list_mk_conj(eq::(subtract cjs [eq])) in
    let th2 = CONJ_ACI_RULE(mk_eq(bod,bod')) in
    let th3 = TRANS th2 (MK_CONJ th1 (REFL(rand(rand(concl th2))))) in
    let v = lhs(lhand(rand(concl th3))) in
    let vars' = (subtract vars [v]) @ [v] in
    let th4 = CONV_RULE(RAND_CONV(REWR_CONV UNWIND_THM2)) (MK_EXISTS v th3) in
    let IMP_RULE v v' =
     DISCH_ALL(itlist SIMPLE_CHOOSE v (itlist SIMPLE_EXISTS v' (ASSUME bod))) in
    let th5 = IMP_ANTISYM_RULE (IMP_RULE vars vars') (IMP_RULE vars' vars) in
    TRANS th5 (itlist MK_EXISTS (subtract vars [v]) th4) in
  let zero_tm = `&0` and one_tm = `&1` in
  let isolate_monomials =
    let mul_tm = `(int_mul)` and add_tm = `(int_add)`
    and neg_tm = `(int_neg)` in
    let dest_mul = dest_binop mul_tm
    and dest_add = dest_binop add_tm
    and mk_mul = mk_binop mul_tm
    and mk_add = mk_binop add_tm in
    let scrub_var v m =
      let ps = striplist dest_mul m in
      let ps' = subtract ps [v] in
      if ps' = [] then one_tm else end_itlist mk_mul ps' in
    let find_multipliers v mons =
      let mons1 = filter (fun m -> free_in v m) mons in
      let mons2 = map (scrub_var v) mons1 in
      if mons2 = [] then zero_tm else end_itlist mk_add mons2 in
    fun vars tm ->
      let cmons,vmons =
         partition (fun m -> intersect (frees m) vars = [])
                   (striplist dest_add tm) in
      let cofactors = map (fun v -> find_multipliers v vmons) vars
      and cnc = if cmons = [] then zero_tm
                else mk_comb(neg_tm,end_itlist mk_add cmons) in
      cofactors,cnc in
  let isolate_variables evs ps eq =
    let vars = filter (fun v -> vfree_in v eq) evs in
    let qs,p = isolate_monomials vars eq in
    let rs = filter (fun t -> type_of t = int_ty) (qs @ ps) in
    let rs = int_ideal_cofactors rs p in
    eq,zip (fst(chop_list(length qs) rs)) vars in
  let subst_in_poly i p = rhs(concl(INT_POLY_CONV (vsubst i p))) in
  let rec solve_idealism evs ps eqs =
    if evs = [] then [] else
    let eq,cfs = tryfind (isolate_variables evs ps) eqs in
    let evs' = subtract evs (map snd cfs)
    and eqs' = map (subst_in_poly cfs) (subtract eqs [eq]) in
    cfs @ solve_idealism evs' ps eqs' in
  let rec GENVAR_EXISTS_CONV tm =
    if not(is_exists tm) then REFL tm else
    let ev,bod = dest_exists tm in
    let gv = genvar(type_of ev) in
    (GEN_ALPHA_CONV gv THENC BINDER_CONV GENVAR_EXISTS_CONV) tm in
  let EXISTS_POLY_TAC (asl,w as gl) =
    let evs,bod = strip_exists w
    and ps = mapfilter (check (fun t -> type_of t = int_ty) o
                        lhs o concl o snd) asl in
    let cfs = solve_idealism evs ps (map lhs (conjuncts bod)) in
    (MAP_EVERY EXISTS_TAC(map (fun v -> rev_assocd v cfs zero_tm) evs) THEN
     REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING) gl in
  let SCRUB_NEQ_TAC = MATCH_MP_TAC o MATCH_MP (MESON[]
    `~(x = y) ==> x = y \/ p ==> p`)
in
val INTEGER_TAC =
  REWRITE_TAC[int_coprime; int_congruent; int_divides] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
              LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM] THEN
  CONV_TAC(REPEATC UNWIND_POLYS_CONV) THEN
  REPEAT(FIRST_X_ASSUM SCRUB_NEQ_TAC) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
              LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN
  REWRITE_TAC[GSYM INT_ENTIRE;
              TAUT `a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT DISCH_TAC THEN CONV_TAC GENVAR_EXISTS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN EXISTS_POLY_TAC;;
val INTEGER_RULE tm = prove(tm,INTEGER_TAC);
end;
*)

val _ = if !Globals.interactive then
          Feedback.HOL_MESG ("intLib loaded.  Use intLib.deprecate_int()"^
                             " to turn off integer parsing")
        else ()

end;
