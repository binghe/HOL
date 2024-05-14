(* ========================================================================= *)
(*    HOL-Light compatibility library                                        *)
(* ========================================================================= *)

structure liteLib :> liteLib =
struct

open HolKernel boolLib Parse;

infix 3 |> thenf orelsef;

(*---------------------------------------------------------------------------
 * Fake for SML/NJ: it does not use Interrupt anyway so it won't ever
 * get raised.
 *---------------------------------------------------------------------------*)

(* exception Interrupt; *)

(*---------------------------------------------------------------------
 *               Exceptions
 *--------------------------------------------------------------------*)

val ERR = mk_HOL_ERR "liteLib"
fun failwith s = raise ERR "?" s

fun STRUCT_ERR s (func,mesg) = raise Feedback.mk_HOL_ERR s func mesg
fun STRUCT_WRAP s (func,exn) = raise Feedback.wrap_exn s func exn

(*---------------------------------------------------------------------
 * options
 *--------------------------------------------------------------------*)

fun the (SOME x) = x
  | the _ = failwith "the: can't take \"the\" of NONE"

fun is_some (SOME x) = true
  | is_some NONE = false

fun is_none NONE = true
  | is_none _ = false

fun option_cases f e (SOME x) = f x
  | option_cases f e NONE = e

fun option_app f (SOME x) = SOME (f x)
  | option_app f NONE = NONE

fun (x |> f) = f x;

fun (f thenf g) x = g(f x);

fun (f orelsef g) x =
  f x handle Interrupt => raise Interrupt
           |         _ => g x;

val repeat = Lib.repeat

fun foldr f e L =
   let fun itl [] = e
         | itl (a::rst) = f (a,itl rst)
   in itl L
   end;

fun foldl f e L =
   let fun rev_it [] e  = e
         | rev_it (a::rst) e = rev_it rst (f (a,e))
   in rev_it L e
   end;

fun end_foldr f =
   let fun endit [] = failwith "end_foldr: list too short"
         | endit alist =
            let val (base,ralist) = case rev alist of
                                      h::t => (h,t)
                                    | _ => raise Bind
            in foldr f base (rev ralist)
            end
   in endit
   end;

val chop_list = Lib.split_after;

fun rotl (a::rst) = rst@[a]
  | rotl [] = failwith "rotl: empty list"

fun rotr lst =
   let val (front,last) = Lib.front_last lst
   in last::front
   end
   handle HOL_ERR _ => failwith "rotr: empty list";

fun replicate (x,n) =
   let fun repl 0 = []
         | repl n = x::repl (n-1)
   in repl n
   end;

fun upto (n,m) = if n >= m then [] else n::upto (n+1,m);

(* ------------------------------------------------------------------------- *)
(* Iterative splitting (list) and stripping (tree) via destructor.           *)
(* ------------------------------------------------------------------------- *)

fun splitlist dest x =
  let val (l,r) = dest x
      val (ls,res) = splitlist dest r
  in (l::ls,res)
  end
  handle Interrupt => raise Interrupt
       | _ => ([],x);;

fun rev_splitlist dest =
  let fun rsplist ls x =
    let val (l,r) = dest x
    in  rsplist (r::ls) l
    end
    handle Interrupt => raise Interrupt
         | _ => (x,ls)
  in
    fn x => rsplist [] x
  end;;

fun striplist dest =
  let fun strip x acc =
    let val (l,r) = dest x
    in strip l (strip r acc)
    end
    handle Interrupt => raise Interrupt
         | _ => x::acc
  in
    fn x => strip x []
  end;;


(*--------------------------------------------------------------------*
 * Associative list functions                                         *
 *--------------------------------------------------------------------*)

val rev_assoc = Lib.rev_assoc;

fun remove_assoc x =
    let fun remove [] = raise ERR "" ""
          | remove ((h as (l,r))::t) = if (x = l) then t else (h::remove t)
    in fn l => (remove l handle HOL_ERR _ => l)
    end;

fun add_assoc (x as (l,r)) ll = x::remove_assoc l ll;

(* ------------------------------------------------------------------------- *)
(* "lazy" objects to delay calculation and avoid recalculation.              *)
(* ------------------------------------------------------------------------- *)

datatype ('a,'b)Lazysum = Unrealized of ('a -> 'b) * 'a
                        | Realized of 'b;

type ('a,'b)lazy = ('a,'b) Lazysum ref;

fun lazy f x = ref(Realized (f x));
fun eager y  = ref(Realized y);;

fun eval r =
  case !r of
    Realized(y) => y
  | Unrealized(f,x) => let val y = f(x) in (r := Realized(y); y) end;;

(*-------------------------------------------------------------------*
 * Orders                                                            *
 *-------------------------------------------------------------------*)

fun ord_of_lt lt (x,y) =
    if lt(x, y) then LESS else
    if lt(y,x) then GREATER else EQUAL;

fun lt_of_ord ord (x,y) = (ord(x, y) = LESS);

val list_ord = Lib.list_compare


(* ===================================================================== *
 * Basic equality reasoning including conversionals.                     *
 * ===================================================================== *)

(*--------------------------------------------------------------------------*
 * General syntax for binary operators (monomorphic constructor only).      *
 *                                                                          *
 * Nb. strip_binop strips only on the right, binops strips both             *
 * left and right (alal conjuncts and disjuncts).                           *
 * -------------------------------------------------------------------------*)

fun mk_binop opr (l,r) =
    Term.list_mk_comb(opr,[l,r]) handle HOL_ERR _ => failwith "mk_binop"

fun list_mk_binop opr = Lib.end_itlist (Lib.curry (mk_binop opr));

fun dest_binop opr tm =
    let val (Rator,rhs) = Term.dest_comb tm
        val (opr',lhs) = Term.dest_comb Rator
    in
        if aconv opr opr' then (lhs,rhs) else fail()
    end
    handle HOL_ERR _ => failwith "dest_binop";

fun strip_binop opr =
    let val dest = dest_binop opr
        fun strip tm =
            let val (l,r) = dest tm
                val (str,rm) = strip r
            in (l::str,rm)
            end
            handle HOL_ERR _ => ([],tm)
    in strip
    end;

fun binops opr =
    let val dest = dest_binop opr
        fun strip tm =
            let val (l,r) = dest tm
            in strip l @ strip r
            end
            handle HOL_ERR _ => [tm]
    in strip
    end;

fun is_binop opr = Lib.can (dest_binop opr)

val is_imp    = is_binop boolSyntax.implication;
val dest_imp  = dest_binop boolSyntax.implication;
val strip_imp = splitlist dest_imp;

(* ------------------------------------------------------------------------- *)
(* Grabbing left operand of a binary operator (or something coextensive!)    *)
(* ------------------------------------------------------------------------- *)

val lhand = Term.rand o Term.rator;;

(* ------------------------------------------------------------------------- *)
(* Like mk_comb, but instantiates type variables in rator if necessary.      *)
(* ------------------------------------------------------------------------- *)

fun mk_icomb(tm1,tm2) =
  let val ty = Lib.fst(Type.dom_rng(Term.type_of tm1))
      val tyins = Type.match_type ty (Term.type_of tm2)
  in
    Term.mk_comb(Term.inst tyins tm1, tm2)
  end;;

(* ------------------------------------------------------------------------- *)
(* Instantiates types for constant c and iteratively makes combination.      *)
(* ------------------------------------------------------------------------- *)

fun list_mk_icomb tm1 args =
   Lib.rev_itlist (Lib.C (Lib.curry mk_icomb)) args tm1;;

(* ------------------------------------------------------------------------- *)
(* Rule allowing easy instantiation of polymorphic proformas.                *)
(* ------------------------------------------------------------------------- *)

fun PINST tyin tmin =
  let val inst_fn = Term.inst tyin
      val tmin' = map (fn {redex,residue} =>
                          {redex=inst_fn redex, residue=residue}) tmin
      val iterm_fn = Thm.INST tmin'
      val itype_fn = Thm.INST_TYPE tyin
  in
      fn th => iterm_fn (itype_fn th) handle HOL_ERR _ => failwith "PINST"
  end;


(* ------------------------------------------------------------------------- *)
(* Really basic stuff for equality.                                          *)
(* ------------------------------------------------------------------------- *)

fun MK_BINOP oper (lth,rth) = MK_COMB(AP_TERM oper lth,rth);

(* ------------------------------------------------------------------------- *)
(* Subterm conversions.                                                      *)
(* ------------------------------------------------------------------------- *)

val LAND_CONV   = Conv.LAND_CONV
val BINDER_CONV = Conv.BINDER_CONV

fun COMB2_CONV lconv rconv tm =
 let val (Rator,Rand) = Term.dest_comb tm
 in MK_COMB(lconv Rator, rconv Rand)
 end;

val COMB_CONV = Lib.W COMB2_CONV;;

val ABS_CONV = Conv.ABS_CONV;

val BODY_CONV =
 let fun dest_quant tm =
       let val (q,atm) = Term.dest_comb tm
           val (v,bod) = Term.dest_abs atm
       in ((q,v),bod)
       end
     val strip_quant = splitlist dest_quant
 in fn conv => fn tm =>
    let val (quants,bod) = strip_quant tm
    in Lib.itlist(fn (q,v) => fn th => AP_TERM q (ABS v th)) quants (conv bod)
    end
 end;

(* ------------------------------------------------------------------------- *)
(* Faster depth conversions using failure rather than returning a REFL.      *)
(* ------------------------------------------------------------------------- *)

val rhs = boolSyntax.rhs;

infix THENQC THENCQC;

fun op THENQC (conv1,conv2) tm =
  let val th1 = conv1 tm
  in let val th2 = conv2(rhs(concl th1))
     in TRANS th1 th2
     end handle HOL_ERR _ => th1
  end
  handle HOL_ERR _ => conv2 tm;


fun op THENCQC (conv1,conv2) tm =
  let val th1 = conv1 tm
  in let val th2 = conv2(rhs(concl th1))
     in TRANS th1 th2
     end
     handle HOL_ERR _ => th1
  end

fun REPEATQC conv tm = (conv THENCQC (REPEATQC conv)) tm;;

fun COMB2_QCONV conv1 conv2 tm =
  let val (l,r) = Term.dest_comb tm
  in let val th1 = conv1 l
     in let val th2 = conv2 r
        in MK_COMB(th1,th2)
        end
        handle HOL_ERR _ => AP_THM th1 r
     end
     handle HOL_ERR _ => AP_TERM l (conv2 r)
  end;

val COMB_QCONV = Lib.W COMB2_QCONV;;

fun SUB_QCONV conv tm =
  if Term.is_abs tm then ABS_CONV conv tm
  else COMB_QCONV conv tm;;

fun ONCE_DEPTH_QCONV conv tm =
  (conv ORELSEC (SUB_QCONV (ONCE_DEPTH_QCONV conv))) tm;;

fun DEPTH_QCONV conv tm =
   ((SUB_QCONV (DEPTH_QCONV conv)) THENQC
    (REPEATQC conv)) tm;;

fun REDEPTH_QCONV conv tm =
   ((SUB_QCONV (REDEPTH_QCONV conv)) THENQC
    (conv THENCQC (REDEPTH_QCONV conv))) tm;;

fun TOP_DEPTH_QCONV conv tm =
   ((REPEATQC conv) THENQC
    (SUB_QCONV (TOP_DEPTH_QCONV conv)
      THENCQC
     (conv THENCQC (TOP_DEPTH_QCONV conv)))) tm;;

fun TOP_SWEEP_QCONV conv tm =
  ((REPEATQC conv) THENQC
   (SUB_QCONV (TOP_SWEEP_QCONV conv))) tm;;

(* ------------------------------------------------------------------------- *)
(* Standard conversions.                                                     *)
(* ------------------------------------------------------------------------- *)

fun TOP_SWEEP_CONV c = TRY_CONV (TOP_SWEEP_QCONV c);;

(* ------------------------------------------------------------------------- *)
(* Apply at leaves of op-tree; NB any failures at leaves cause failure.      *)
(* ------------------------------------------------------------------------- *)

local exception DEST_BINOP
in
fun DEPTH_BINOP_CONV oper conv tm =
  let val (l,r) = dest_binop oper tm handle HOL_ERR _ => raise DEST_BINOP
      val lth = DEPTH_BINOP_CONV oper conv l
      and rth = DEPTH_BINOP_CONV oper conv r
  in MK_COMB(AP_TERM oper lth,rth)
  end
  handle DEST_BINOP => conv tm
end;


(* ------------------------------------------------------------------------- *)
(* Single bottom-up pass, starting at the topmost success!                   *)
(* ------------------------------------------------------------------------- *)

fun SINGLE_DEPTH_CONV conv tm =
  conv tm handle HOL_ERR _
  => (SUB_CONV (SINGLE_DEPTH_CONV conv)
               THENC TRY_CONV conv) tm;;

(*-----------------------------------------------------------------------*)
(* MK_ABS_CONV - Abstract a term by a variable                           *)
(* MK_ABSL_CONV - Abstract a term by a set of variables                  *)
(*                                                                       *)
(* [DRS 96.01.28]                                                        *)
(*-----------------------------------------------------------------------*)

fun MK_ABS_CONV var tm =
  if Term.is_comb tm andalso aconv (Term.rand tm) var
     andalso not (Term.free_in var (Term.rator tm))
  then
    REFL tm
  else
    let
      val rhs = Term.mk_abs(var,tm)
      val newrhs = Term.mk_comb(rhs,var)
    in
      SYM (BETA_CONV newrhs)
    end;

fun MK_ABSL_CONV vars tm =
 let val rhs = boolSyntax.list_mk_abs (vars,tm)
     val newrhs = Term.list_mk_comb(rhs,vars)
     val thm1 = foldr (fn (_,conv) => (RATOR_CONV conv) THENC BETA_CONV)
                      ALL_CONV vars newrhs
 in SYM thm1
 end;

val RIGHT_BETAS =
  Lib.rev_itlist (fn a => CONV_RULE (RAND_CONV BETA_CONV) o Lib.C AP_THM a);;

fun name_of_const tm =
 let val {Name,Thy,...} = Term.dest_thy_const tm in (Name,Thy) end;

fun MK_CONJ eq1 eq2 = MK_COMB(AP_TERM boolSyntax.conjunction eq1,eq2)
fun MK_DISJ eq1 eq2 = MK_COMB(AP_TERM boolSyntax.disjunction eq1,eq2)
fun MK_FORALL v th =
  let val theta = [{redex=Type.alpha, residue=Term.type_of v}]
  in AP_TERM (Term.inst theta boolSyntax.universal) (ABS v th)
  end;
fun MK_EXISTS v th =
  let val theta = [{redex=Type.alpha, residue=Term.type_of v}]
  in AP_TERM (Term.inst theta boolSyntax.existential) (ABS v th)
  end;

fun SIMPLE_DISJ_CASES th1 th2 =
  case (hyp th1, hyp th2)
   of (h1::_, h2::_) => DISJ_CASES (ASSUME(boolSyntax.mk_disj(h1,h2))) th1 th2
    |  _ => raise ERR "SIMPLE_DISJ_CASES" "";

val SIMPLE_CHOOSE = Drule.SIMPLE_CHOOSE

(* ------------------------------------------------------------------------- *)
(*   HOL-Light compatible functions for manipulating function types          *)
(* ------------------------------------------------------------------------- *)

val bool_ty = Type.bool;
val dest_fun_ty = Type.dom_rng;
fun mk_fun_ty ty1 ty2 = Type.--> (ty1,ty2);

val setify_term = let
    fun term_eq x y = (Term.compare (x,y) = EQUAL);
    fun term_le x y = (Term.compare (x,y) <> GREATER);
    fun uniq (x::y::xs) = if term_eq x y then uniq (y::xs) else x::uniq (y::xs)
      | uniq xs = xs
in
    fn s => uniq (Lib.sort term_le s)
end;

(* ------------------------------------------------------------------------- *)
(* HOL-Light compatible tactic names                                         *)
(* ------------------------------------------------------------------------- *)

val ANTS_TAC = impl_tac;

(* ------------------------------------------------------------------------- *)
(* Type of instantiations, with terms, types and higher-order data.          *)
(* ------------------------------------------------------------------------- *)

type instantiation =
    (int * term) list * (term * term) list * (hol_type * hol_type) list;

(* ------------------------------------------------------------------------- *)
(* Alpha conversion term operation.                                          *)
(* ------------------------------------------------------------------------- *)

(* NOTE: this function is name-conflict with Type.alpha *)
fun alpha v tm =
  let
    val (v0,bod) = Term.dest_abs tm
                   handle HOL_ERR _ => failwith "alpha: Not an abstraction"
  in
    if aconv v v0 then tm
    else if not (Term.free_in v bod) then
      Term.mk_abs(v, Term.subst [Lib.|->(v0,v)] bod)
    else failwith "alpha: Invalid new variable"
  end;

(* ------------------------------------------------------------------------- *)
(* Type matching.                                                            *)
(* ------------------------------------------------------------------------- *)

fun type_match vty cty sofar =
  if is_vartype vty then
     if rev_assoc vty sofar = cty then sofar else failwith "type_match"
     handle HOL_ERR _ => (cty,vty)::sofar
  else
     let val (vop,vargs) = dest_type vty
         and (cop,cargs) = dest_type cty
     in
       if vop = cop then itlist2 type_match vargs cargs sofar
       else failwith "type_match"
     end;

(* ------------------------------------------------------------------------- *)
(* Instantiators.                                                            *)
(* ------------------------------------------------------------------------- *)

(* instantiate :instantiation -> term -> term) (ported, but not used)
local
  fun betas n tm =
    let val (args,lam) = funpow n (fn (l,t) => ((rand t)::l,rator t)) ([],tm)
    in
      rev_itlist (fn a => fn l =>
                     let val (v,b) = dest_abs l in subst[v |-> a] b end)
                 args lam
    end;
  fun ho_betas bcs pat tm =
    if is_var pat orelse is_const pat then fail() else
    let val (bv,bod) = dest_abs tm in
        mk_abs(bv,ho_betas bcs (body pat) bod)
    end
    handle HOL_ERR _ =>
    let val (hop,args) = strip_comb pat in
       (let val n = op_rev_assoc aconv hop bcs in
            if length args = n then betas n tm else fail()
        end)
        handle HOL_ERR _ =>
        let val (lpat,rpat) = dest_comb pat;
            val (ltm,rtm) = dest_comb tm
        in
           (let val lth = ho_betas bcs lpat ltm
            in
                let val rth = ho_betas bcs rpat rtm in
                    mk_comb(lth,rth)
                end
                handle HOL_ERR _ =>
                    mk_comb(lth,rtm)
            end)
            handle HOL_ERR _ =>
                let val rth = ho_betas bcs rpat rtm in
                    mk_comb(ltm,rth)
                end
        end
    end
in
  fun instantiate ((bcs,tmin,tyin):instantiation) tm :term =
    let val itm = if null tyin then tm else
                     inst (map (fn (a,b) => b |-> a) tyin) tm
    in
      if null tmin then itm else
      let val ttm = subst (map (fn (a,b) => b |-> a) tmin) itm
      in
        if null bcs then ttm else
        ho_betas bcs itm ttm
        handle HOL_ERR _ => ttm
      end
    end
end; (* local *)
 *)

(* INSTANTIATE :instantiation -> thm -> thm *)
local
  fun BETAS_CONV n tm =
    if n = 1 then TRY_CONV BETA_CONV tm else
    (RATOR_CONV (BETAS_CONV (n-1)) THENC
     TRY_CONV BETA_CONV) tm;
  fun HO_BETAS bcs pat tm =
    if is_var pat orelse is_const pat then fail() else
    let val (bv,bod) = dest_abs tm in
        ABS bv (HO_BETAS bcs (body pat) bod)
    end
    handle HOL_ERR _ =>
    let val (hop,args) = strip_comb pat in
        let val n = op_rev_assoc aconv hop bcs in
            if length args = n then BETAS_CONV n tm else fail()
        end
        handle HOL_ERR _ =>
        let val (lpat,rpat) = dest_comb pat;
            val (ltm,rtm) = dest_comb tm
        in
            let val lth = HO_BETAS bcs lpat ltm
            in
                let val rth = HO_BETAS bcs rpat rtm in
                    MK_COMB(lth,rth)
                end
                handle HOL_ERR _ =>
                    AP_THM lth rtm
            end
            handle HOL_ERR _ =>
                let val rth = HO_BETAS bcs rpat rtm in
                    AP_TERM ltm rth
                end
        end
    end;
    fun coincide tms1 tms2 =
        HOLset.equal(HOLset.addList(empty_tmset,tms1),
                     HOLset.addList(empty_tmset,tms2));
in
fun INSTANTIATE ((bcs,tmin,tyin) :instantiation) th :thm =
    let val ith = if null tyin then th else
                     INST_TYPE (map (fn (a,b) => b |-> a) tyin) th
    in
       if null tmin then ith else
       let val tth = INST (map (fn (a,b) => b |-> a) tmin) ith
       in
          if coincide (hyp tth) (hyp th) then
             if null bcs then tth else
             let val eth = HO_BETAS bcs (concl ith) (concl tth) in
                EQ_MP eth tth
             end
             handle HOL_ERR _ => tth
          else
             failwith "INSTANTIATE: term or type var free in assumptions"
       end
    end
end; (* local *)

(* not used, not ported
let (INSTANTIATE_ALL : instantiation->thm->thm) =
  fun ((_,tmin,tyin) as i) th ->
    if tmin = [] && tyin = [] then th else
    let hyps = hyp th in
    if hyps = [] then INSTANTIATE i th else
    let tyrel,tyiirel =
      if tyin = [] then [],hyps else
      let tvs = itlist (union o tyvars o snd) tyin [] in
      partition (fun tm -> let tvs' = type_vars_in_term tm in
                           not(intersect tvs tvs' = [])) hyps in
    let tmrel,tmirrel =
      if tmin = [] then [],tyiirel else
      let vs = itlist (union o frees o snd) tmin [] in
      partition (fun tm -> let vs' = frees tm in
                           not (intersect vs vs' = [])) tyiirel in
    let rhyps = union tyrel tmrel in
    let th1 = rev_itlist DISCH rhyps th in
    let th2 = INSTANTIATE i th1 in
    funpow (length rhyps) UNDISCH th2;;
 *)

(* ------------------------------------------------------------------------- *)
(* Higher order matching of terms.                                           *)
(*                                                                           *)
(* Note: in the event of spillover patterns, this may return false results;  *)
(* but there's usually an implicit check outside that the match worked       *)
(* anyway. A test could be put in (see if any "env" variables are left in    *)
(* the term after abstracting out the pattern instances) but it'd be slower. *)
(* ------------------------------------------------------------------------- *)

(* term_match :term list -> term -> term -> instantiation, cf. match_term *)
local
  fun safe_insert (n as (y,x)) l =
    let val z = op_rev_assoc aconv x l in
        if y ~~ z then l else failwith "safe_insert"
    end
    handle HOL_ERR _ => n::l;

  fun safe_insert' (n as (y,x)) l =
    let val z = op_rev_assoc aconv x l in
        if y = z then l else failwith "safe_insert'"
    end
    handle HOL_ERR _ => n::l;

  fun safe_insert0 (n as (y,x)) l =
    let val z = rev_assoc x l in
        if y = z then l else failwith "safe_insert'"
    end
    handle HOL_ERR _ => n::l;

  val aty = Type.alpha;
  val mk_dummy =
      let val name = fst(dest_var(genvar aty)) in
        fn ty => mk_var(name,ty)
      end;

  fun term_pmatch lconsts env vtm ctm (sofar as (insts,homs)) =
    if is_var vtm then
       (let val ctm' = op_rev_assoc aconv vtm env
        in
            if ctm' ~~ ctm then sofar
            else failwith "term_pmatch"
        end)
        handle HOL_ERR _ =>
            if op_mem aconv vtm lconsts then
               if ctm ~~ vtm then sofar
               else failwith "term_pmatch: can't instantiate local constant"
            else
               (safe_insert (ctm,vtm) insts,homs)
    else if is_const vtm andalso is_const ctm then
      let val (vname,vty) = dest_const vtm
          and (cname,cty) = dest_const ctm
      in
        if vname = cname then
          if vty = cty then sofar
          else
            (safe_insert (mk_dummy cty,mk_dummy vty) insts,homs)
        else failwith "term_pmatch"
      end
    else if is_abs vtm andalso is_abs ctm then
      let val (vv,vbod) = dest_abs vtm
          and (cv,cbod) = dest_abs ctm;
          val sofar' = (safe_insert
             (mk_dummy(snd(dest_var cv)),mk_dummy(snd(dest_var vv))) insts,homs)
      in
          term_pmatch lconsts ((cv,vv)::env) vbod cbod sofar'
      end
    else
      let val vhop = repeat rator vtm in
        if is_var vhop andalso not (op_mem aconv vhop lconsts) andalso
                       not (can (op_rev_assoc aconv vhop) env)
        then
          let val vty = type_of vtm and cty = type_of ctm;
              val insts' =
                if vty = cty then insts
                else
                   safe_insert (mk_dummy cty,mk_dummy vty) insts
          in
             (insts',(env,ctm,vtm)::homs)
          end
        else
          let val (lv,rv) = dest_comb vtm
              and (lc,rc) = dest_comb ctm;
              val sofar' = term_pmatch lconsts env lv lc sofar
          in
              term_pmatch lconsts env rv rc sofar'
          end
      end;

  fun get_type_insts insts =
    itlist (fn (t,x) => type_match (snd(dest_var x)) (type_of t)) insts;

  fun separate_insts insts = let
      val (realinsts,patterns) = partition (is_var o snd) insts;
      val betacounts =
        if null patterns then [] else
        itlist
          (fn (_,p) => fn sof =>
            let val (hop,args) = strip_comb p in
                safe_insert' (length args,hop) sof
                handle HOL_ERR _ =>
                  (print "Inconsistent patterning in higher order match"; sof)
            end)
          patterns [];
      val tyins = get_type_insts realinsts [];
      val ins = map (fn (a,b) => b |-> a) tyins;
  in
     (betacounts,
      mapfilter (fn (t,x) =>
                    let val (xn,xty) = dest_var x;
                        val x' = mk_var(xn, type_subst ins xty)
                    in
                        if t ~~ x' then fail() else (t,x')
                    end)
                realinsts,
      tyins)
  end;

  fun coincide tms1 tms2 =
        HOLset.equal(HOLset.addList(empty_tmset,tms1),
                     HOLset.addList(empty_tmset,tms2));

  fun term_homatch lconsts tyins (insts,homs) =
    if null homs then insts else
    let val (env,ctm,vtm) = hd homs
    in
      if is_var vtm then
        if ctm ~~ vtm then
           term_homatch lconsts tyins (insts,tl homs)
        else
          let val newtyins = safe_insert0 (type_of ctm,snd(dest_var vtm)) tyins
              and newinsts = (ctm,vtm)::insts
          in
              term_homatch lconsts newtyins (newinsts,tl homs)
          end
      else
        let val (vhop,vargs) = strip_comb vtm;
            val afvs = free_varsl vargs;
            val inst_fn = inst (map (fn (a,b) => b |-> a) tyins)
        in
        (let val tmins = map
                (fn a => ((op_rev_assoc aconv a env
                           handle HOL_ERR _ =>
                             op_rev_assoc aconv a insts
                             handle HOL_ERR _ =>
                               if op_mem aconv a lconsts then a else fail()),
                          inst_fn a)) afvs;
             val pats0 = map inst_fn vargs;
             val pats = map (subst (map (fn (a,b) => b |-> a) tmins)) pats0;
             val vhop' = inst_fn vhop;
             val ni =
               let val (chop,cargs) = strip_comb ctm
               in
                (if coincide cargs pats then
                   (if chop ~~ vhop then insts
                    else safe_insert (chop,vhop) insts)
                 else
                 let val ginsts = map
                          (fn p => ((if is_var p then p else genvar(type_of p)),p)) pats;
                     val ctm' = subst (map (fn (a,b) => b |-> a) ginsts) ctm
                     and gvs = map fst ginsts;
                     val abstm = list_mk_abs(gvs,ctm');
                     val vinsts = safe_insert (abstm,vhop) insts;
                     val icpair = (ctm',list_mk_comb(vhop',gvs))
                 in
                   icpair::vinsts
                 end)
               end; (* ni *)
         in
            term_homatch lconsts tyins (ni,tl homs)
         end)
         handle HOL_ERR _ =>
           let val (lc,rc) = dest_comb ctm
               and (lv,rv) = dest_comb vtm;
               val pinsts_homs' =
                   term_pmatch lconsts env rv rc (insts,(env,lc,lv)::(tl homs));
               val tyins' = get_type_insts (fst pinsts_homs') []
           in
              term_homatch lconsts tyins' pinsts_homs'
           end
        end
    end;
in
  fun term_match (lconsts :term list) vtm ctm :instantiation =
    let val pinsts_homs = term_pmatch lconsts [] vtm ctm ([],[]);
        val tyins = get_type_insts (fst pinsts_homs) [];
        val insts = term_homatch lconsts tyins pinsts_homs
    in
      separate_insts insts
    end
end; (* local *)

(* ------------------------------------------------------------------------- *)
(* Instantiate theorem by matching part of it to a term.                     *)
(* The GEN_PART_MATCH version renames free vars to avoid clashes.            *)
(* ------------------------------------------------------------------------- *)

(* PART_MATCH :(term -> term) -> thm -> term -> thm *)
local
  fun coincide tms1 tms2 =
      HOLset.equal(HOLset.addList(empty_tmset,tms1),
                   HOLset.addList(empty_tmset,tms2));

  fun not_equal (tms1,tms2) = not(coincide tms1 tms2);

  fun PART_MATCH partfn th tm = let
    val sth = SPEC_ALL th;
    val bod = concl sth;
    val pbod = partfn bod;
    val lconsts =
        HOLset.intersection (FVL [concl th] empty_tmset, FVL (hyp th) empty_tmset)
     |> HOLset.listItems;
    val bvms = match_bvs tm pbod [];
    val abod = deep_alpha bvms bod;
    val ath = EQ_MP (ALPHA bod abod) sth;
    val insts = term_match lconsts (partfn abod) tm;
    val fth = INSTANTIATE insts ath;
  in
    if not_equal(hyp fth, hyp ath) then
       failwith "PART_MATCH: instantiated hyps"
    else
    let val tm' = partfn (concl fth) in
      if tm' ~~ tm then fth else
         SUBS[ALPHA tm' tm] fth
         handle HOL_ERR _ => failwith "PART_MATCH: Sanity check failure"
    end
  end
in
  val PART_MATCHL = PART_MATCH;
end; (* local *)

(* not used so far
fun GEN_PART_MATCH partfn th = let
    let sth = SPEC_ALL th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lconsts = intersect (frees (concl th)) (free_varsl(hyp th)) in
    let fvs = subtract (subtract (frees bod) (frees pbod)) lconsts
in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = EQ_MP (ALPHA bod abod) sth in
      let insts = term_match lconsts (partfn abod) tm in
      let eth = INSTANTIATE insts (GENL fvs ath) in
      let fth = itlist (fun v th -> snd(SPEC_VAR th)) fvs eth in
      if hyp fth <> hyp ath then failwith "PART_MATCH: instantiated hyps" else
      let tm' = partfn (concl fth) in
      if Pervasives.compare tm' tm = 0 then fth else
      try SUBS[ALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure"
end;
 *)

end; (* struct *)
