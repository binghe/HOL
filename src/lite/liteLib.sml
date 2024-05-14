(* ========================================================================= *)
(*    HOL-Light compatibility library                                        *)
(* ========================================================================= *)

structure liteLib :> liteLib =
struct

open Feedback Thm Term Drule Conv Abbrev Tactic;

val aconv = Term.aconv

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

(* NOTE: this function is conflict with Type.alpha *)
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
(* Instantiators.                                                            *)
(* ------------------------------------------------------------------------- *)

(*
let (instantiate :instantiation->term->term) =
  let betas n tm =
    let args,lam = funpow n (fun (l,t) -> (rand t)::l,rator t) ([],tm) in
    rev_itlist (fun a l -> let v,b = dest_abs l in vsubst[a,v] b) args lam in
  let rec ho_betas bcs pat tm =
    if is_var pat || is_const pat then fail() else
    try let bv,bod = dest_abs tm in
        mk_abs(bv,ho_betas bcs (body pat) bod)
    with Failure _ ->
        let hop,args = strip_comb pat in
        try let n = rev_assoc hop bcs in
            if length args = n then betas n tm else fail()
        with Failure _ ->
            let lpat,rpat = dest_comb pat in
            let ltm,rtm = dest_comb tm in
            try let lth = ho_betas bcs lpat ltm in
                try let rth = ho_betas bcs rpat rtm in
                    mk_comb(lth,rth)
                with Failure _ ->
                    mk_comb(lth,rtm)
            with Failure _ ->
                let rth = ho_betas bcs rpat rtm in
                mk_comb(ltm,rth) in
  fun (bcs,tmin,tyin) tm ->
    let itm = if tyin = [] then tm else inst tyin tm in
    if tmin = [] then itm else
    let ttm = vsubst tmin itm in
    if bcs = [] then ttm else
    try ho_betas bcs itm ttm with Failure _ -> ttm;;

let (INSTANTIATE : instantiation->thm->thm) =
  let rec BETAS_CONV n tm =
    if n = 1 then TRY_CONV BETA_CONV tm else
    (RATOR_CONV (BETAS_CONV (n-1)) THENC
     TRY_CONV BETA_CONV) tm in
  let rec HO_BETAS bcs pat tm =
    if is_var pat || is_const pat then fail() else
    try let bv,bod = dest_abs tm in
        ABS bv (HO_BETAS bcs (body pat) bod)
    with Failure _ ->
        let hop,args = strip_comb pat in
        try let n = rev_assoc hop bcs in
            if length args = n then BETAS_CONV n tm else fail()
        with Failure _ ->
            let lpat,rpat = dest_comb pat in
            let ltm,rtm = dest_comb tm in
            try let lth = HO_BETAS bcs lpat ltm in
                try let rth = HO_BETAS bcs rpat rtm in
                    MK_COMB(lth,rth)
                with Failure _ ->
                    AP_THM lth rtm
            with Failure _ ->
                let rth = HO_BETAS bcs rpat rtm in
                AP_TERM ltm rth in
  fun (bcs,tmin,tyin) th ->
    let ith = if tyin = [] then th else INST_TYPE tyin th in
    if tmin = [] then ith else
    let tth = INST tmin ith in
    if hyp tth = hyp th then
      if bcs = [] then tth else
      try let eth = HO_BETAS bcs (concl ith) (concl tth) in
          EQ_MP eth tth
      with Failure _ -> tth
    else failwith "INSTANTIATE: term or type var free in assumptions";;

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

(* ------------------------------------------------------------------------- *)
(* Higher order matching of terms.                                           *)
(*                                                                           *)
(* Note: in the event of spillover patterns, this may return false results;  *)
(* but there's usually an implicit check outside that the match worked       *)
(* anyway. A test could be put in (see if any "env" variables are left in    *)
(* the term after abstracting out the pattern instances) but it'd be slower. *)
(* ------------------------------------------------------------------------- *)

let (term_match:term list -> term -> term -> instantiation) =
  let safe_inserta ((y,x) as n) l =
    try let z = rev_assoc x l in
        if aconv y z then l else failwith "safe_inserta"
    with Failure "find" -> n::l in

  let safe_insert ((y,x) as n) l =
    try let z = rev_assoc x l in
        if Pervasives.compare y z = 0 then l else failwith "safe_insert"
    with Failure "find" -> n::l in

  let mk_dummy =
    let name = fst(dest_var(genvar aty)) in
    fun ty -> mk_var(name,ty) in

  let rec term_pmatch lconsts env vtm ctm ((insts,homs) as sofar) =
    match (vtm,ctm) with
      Var(_,_),_ ->
       (try let ctm' = rev_assoc vtm env in
            if Pervasives.compare ctm' ctm = 0 then sofar
            else failwith "term_pmatch"
        with Failure "find" ->
            if mem vtm lconsts then
              if Pervasives.compare ctm vtm = 0 then sofar
              else failwith "term_pmatch: can't instantiate local constant"
            else safe_inserta (ctm,vtm) insts,homs)
    | Const(vname,vty),Const(cname,cty) ->
        if Pervasives.compare vname cname = 0 then
          if Pervasives.compare vty cty = 0 then sofar
          else safe_insert (mk_dummy cty,mk_dummy vty) insts,homs
        else failwith "term_pmatch"
    | Abs(vv,vbod),Abs(cv,cbod) ->
        let sofar' = safe_insert
          (mk_dummy(snd(dest_var cv)),mk_dummy(snd(dest_var vv))) insts,homs in
        term_pmatch lconsts ((cv,vv)::env) vbod cbod sofar'
    | _ ->
      let vhop = repeat rator vtm in
      if is_var vhop && not (mem vhop lconsts) &&
                       not (can (rev_assoc vhop) env) then
        let vty = type_of vtm and cty = type_of ctm in
        let insts' =
          if Pervasives.compare vty cty = 0 then insts
          else safe_insert (mk_dummy cty,mk_dummy vty) insts in
        (insts',(env,ctm,vtm)::homs)
      else
        let lv,rv = dest_comb vtm
        and lc,rc = dest_comb ctm in
        let sofar' = term_pmatch lconsts env lv lc sofar in
        term_pmatch lconsts env rv rc sofar' in

  let get_type_insts insts =
    itlist (fun (t,x) -> type_match (snd(dest_var x)) (type_of t)) insts in

  let separate_insts insts =
      let realinsts,patterns = partition (is_var o snd) insts in
      let betacounts =
        if patterns = [] then [] else
        itlist
          (fun (_,p) sof ->
            let hop,args = strip_comb p in
            try safe_insert (length args,hop) sof with Failure _ ->
            (warn true "Inconsistent patterning in higher order match"; sof))
          patterns [] in
      let tyins = get_type_insts realinsts [] in
      betacounts,
      mapfilter (fun (t,x) ->
        let x' = let xn,xty = dest_var x in
                 mk_var(xn,type_subst tyins xty) in
        if Pervasives.compare t x' = 0 then fail() else (t,x')) realinsts,
      tyins in

  let rec term_homatch lconsts tyins (insts,homs) =
    if homs = [] then insts else
    let (env,ctm,vtm) = hd homs in
    if is_var vtm then
      if Pervasives.compare ctm vtm = 0
       then term_homatch lconsts tyins (insts,tl homs) else
      let newtyins = safe_insert (type_of ctm,snd(dest_var vtm)) tyins
      and newinsts = (ctm,vtm)::insts in
      term_homatch lconsts newtyins (newinsts,tl homs) else
    let vhop,vargs = strip_comb vtm in
    let afvs = freesl vargs in
    let inst_fn = inst tyins in
    try let tmins = map
          (fun a -> (try rev_assoc a env with Failure _ -> try
                         rev_assoc a insts with Failure _ ->
                         if mem a lconsts then a else fail()),
                    inst_fn a) afvs in
        let pats0 = map inst_fn vargs in
        let pats = map (vsubst tmins) pats0 in
        let vhop' = inst_fn vhop in
        let ni =
          let chop,cargs = strip_comb ctm in
          if Pervasives.compare cargs pats = 0 then
            if Pervasives.compare chop vhop = 0
            then insts else safe_inserta (chop,vhop) insts else
          let ginsts = map
            (fun p -> (if is_var p then p else genvar(type_of p)),p) pats in
          let ctm' = subst ginsts ctm
          and gvs = map fst ginsts in
          let abstm = list_mk_abs(gvs,ctm') in
          let vinsts = safe_inserta (abstm,vhop) insts in
          let icpair = ctm',list_mk_comb(vhop',gvs) in
          icpair::vinsts in
        term_homatch lconsts tyins (ni,tl homs)
    with Failure _ ->
        let lc,rc = dest_comb ctm
        and lv,rv = dest_comb vtm in
        let pinsts_homs' =
          term_pmatch lconsts env rv rc (insts,(env,lc,lv)::(tl homs)) in
        let tyins' = get_type_insts (fst pinsts_homs') [] in
        term_homatch lconsts tyins' pinsts_homs' in

  fun lconsts vtm ctm ->
    let pinsts_homs = term_pmatch lconsts [] vtm ctm ([],[]) in
    let tyins = get_type_insts (fst pinsts_homs) [] in
    let insts = term_homatch lconsts tyins pinsts_homs in
    separate_insts insts;;
*)

(* ------------------------------------------------------------------------- *)
(* Instantiate theorem by matching part of it to a term.                     *)
(* The GEN_PART_MATCH version renames free vars to avoid clashes.            *)
(* ------------------------------------------------------------------------- *)

(*
local
  fun match_bvs t1 t2 acc =
    let val (v1,b1) = dest_abs t1
        val (v2,b2) = dest_abs t2;
        val n1 = fst(dest_var v1) and n2 = fst(dest_var v2);
        val newacc = if n1 = n2 then acc else insert (n1,n2) acc
    in
        match_bvs b1 b2 newacc
    end
    handle HOL_ERR _ =>
        let val (l1,r1) = dest_comb t1
            and (l2,r2) = dest_comb t2
        in
            match_bvs l1 l2 (match_bvs r1 r2 acc)
        end
        handle HOL_ERR _ => acc
in
  fun PART_MATCH partfn th = let
    val sth = SPEC_ALL th;
    val bod = concl sth;
    val pbod = partfn bod;
    val lconsts =
        HOLset.intersection (FVL [concl th] empty_tmset, FVL (hyp th) empty_tmset)
     |> HOLset.listItems
  in
    fn tm => let
      val bvms = match_bvs tm pbod [];
      val abod = deep_alpha bvms bod;
      val ath = EQ_MP (ALPHA bod abod) sth;
      let insts = term_match lconsts (partfn abod) tm;
      let fth = INSTANTIATE insts ath;
      if hyp fth <> hyp ath then failwith "PART_MATCH: instantiated hyps" else
      let tm' = partfn (concl fth) in
      if Pervasives.compare tm' tm = 0 then fth else
      try SUBS[ALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure";
  end;

  fun GEN_PART_MATCH partfn th =
    let sth = SPEC_ALL th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lconsts = intersect (frees (concl th)) (freesl(hyp th)) in
    let fvs = subtract (subtract (frees bod) (frees pbod)) lconsts in
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
end; (* local *)
*)

end; (* struct *)
