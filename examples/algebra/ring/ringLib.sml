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

(*
let RING_RULE =
  let RING_WORD_UNIVERSAL =
    let cth = prove
     (`ring_0 r = ring_of_int r (&0) /\
       ring_1 r = ring_of_int r (&1)`,
      REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_0; RING_OF_NUM_1])
    and pth = (UNDISCH o prove)
     (`ring_carrier r = (:A)
       ==> (x = y <=> ring_sub r x y = ring_of_int r (&0))`,
      SIMP_TAC[RING_SUB_EQ_0; IN_UNIV; RING_OF_INT_OF_NUM; RING_OF_NUM_0])
    and bth = REFL `ring_of_int r (&0):A`
    and mth = (UNDISCH o prove)
     (`ring_carrier r = (:A)
       ==> p = ring_of_int r (&0) ==> !c. ring_mul r c p = ring_of_int r (&0)`,
      SIMP_TAC[RING_MUL_RZERO; RING_OF_INT_OF_NUM; RING_OF_NUM_0; IN_UNIV])
    and dth = (UNDISCH o prove)
     (`ring_carrier r = (:A)
       ==> p = ring_of_int r (&0) /\ q = ring_of_int r (&0)
           ==> ring_add r p q = ring_of_int r (&0)`,
      SIMP_TAC[RING_ADD_RZERO; RING_OF_INT_OF_NUM; RING_OF_NUM_0; IN_UNIV]) in
    let decorule =
      GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV)
       [cth; GSYM RING_OF_INT_OF_NUM] o
      PART_MATCH lhand pth in
    fun tm ->
      let avs,bod = strip_forall tm in
      if is_imp bod then
        let ant,con = dest_imp bod in
        let aths =
          mapfilter (CONV_RULE decorule) (CONJUNCTS(ASSUME ant))
        and cth = decorule con in
        let atms = map (lhand o concl) aths
        and ctm = lhand(rand(concl cth)) in
        let ctms = ring_ring_cofactors_universal atms ctm in
        let zths = map2 (fun c th -> SPEC c (MATCH_MP mth th)) ctms aths in
        let zth =
          end_itlist (fun th1 th2 -> MATCH_MP dth (CONJ th1 th2)) zths in
        let eth =
          TRANS (RING_POLY_UNIVERSAL_CONV ctm)
          (SYM(RING_POLY_UNIVERSAL_CONV (lhand(concl zth)))) in
        GENL avs (DISCH ant (EQ_MP (SYM cth) (TRANS eth zth)))
      else
        let th1 = decorule tm in
        let th2 = CONV_RULE
          (RAND_CONV (LAND_CONV RING_POLY_UNIVERSAL_CONV)) th1 in
        EQ_MP (SYM th2) bth in
  let RING_RING_WORD =
    let imp_imp_rule = GEN_REWRITE_RULE I [IMP_IMP]
    and left_exists_rule = GEN_REWRITE_RULE I [LEFT_FORALL_IMP_THM]
    and or_elim_rule =
      GEN_REWRITE_RULE I [TAUT `(p ==> q) /\ (p' ==> q) <=> p \/ p' ==> q`] in
    fun ths tm ->
      let dty = type_of(rand tm) in
      let rty = mk_type("ring",[dty]) in
      let rtms = filter ((=) rty o type_of) (freesl(tm::map concl ths)) in
      if length rtms <> 1
      then failwith "RING_RULE: can't deduce which ring" else
      let rtm = hd rtms in
      let tvs =
        itlist (union o type_vars_in_term o concl) ths
               (type_vars_in_term tm) in
      let dty' = mk_vartype("Z"^itlist ((^) o dest_vartype) tvs "") in
      let rty' = mk_type("ring",[dty']) in
      let avvers = itlist (union o variables o concl) ths (variables tm) in
      let rtm' = variant avvers (mk_var("r'",rty'))
      and htm = variant avvers (mk_var("h",mk_fun_ty dty dty')) in
      let hasm = list_mk_icomb "ring_monomorphism" [mk_pair(rtm,rtm'); htm] in
      let hth = ASSUME hasm in
      let ths' = mapfilter (CONV_RULE(RING_MONOMORPHIC_IMAGE_RULE hth)) ths
      and th' = RING_MONOMORPHIC_IMAGE_RULE hth tm in
      let utm =
        if ths' = [] then rand(concl th')
        else mk_imp(list_mk_conj (map concl ths'),rand(concl th')) in
      let hvs = find_terms
       (fun t -> is_comb t && rator t = htm && is_var(rand t)) utm in
      let gvs = map (genvar o type_of) hvs in
      let vtm = subst (zip gvs hvs) utm in
      let arty = mk_type("ring",[aty]) in
      let atm =
        vsubst [mk_var("r",arty),mk_var(fst(dest_var rtm'),arty)]
               (inst[aty,dty'] vtm) in
      let th1 = RING_WORD_UNIVERSAL atm in
      let th2 = INST_TYPE [dty',aty] th1 in
      let th3 = INST [rtm',mk_var("r",rty')] th2 in
      let th4 = INST (zip hvs gvs) th3 in
      let th5 =
        if ths' = [] then th4 else
        MP th4 (end_itlist CONJ ths') in
      let th6 = itlist PROVE_HYP ths (EQ_MP (SYM th') th5) in
      let ueq = mk_eq(list_mk_icomb "ring_carrier" [rtm'],
                      mk_const("UNIV",[dty',aty])) in
      let th7 = imp_imp_rule (DISCH ueq (DISCH hasm th6)) in
      let th8 = left_exists_rule(GEN htm th7) in
      let th9 = left_exists_rule(GEN rtm' th8) in
      let th10 = ISPEC rtm RING_TOTALIZATION in
      let th11 = CONJ (PART_MATCH lhand th9 (lhand(concl th10)))
                      (PART_MATCH lhand th9 (rand(concl th10))) in
      MP (or_elim_rule th11) th10 in
  let RING_RING_HORN =
    let ddj_conv =
      GEN_REWRITE_CONV (RAND_CONV o DEPTH_CONV)
        [TAUT `~p \/ ~q <=> ~(p /\ q)`] THENC
      GEN_REWRITE_CONV I [TAUT `p \/ ~q <=> q ==> p`] in
    fun tm ->
      if not(is_disj tm) then RING_RING_WORD [] tm else
      let th0 = ddj_conv tm in
      let tm' = rand(concl th0) in
      let abod = lhand tm' in
      let ths = CONJUNCTS(ASSUME abod) in
      let th1 = RING_RING_WORD ths (rand tm') in
      EQ_MP (SYM th0) (DISCH abod (itlist PROVE_HYP ths th1)) in
  let RING_RING_CORE =
    let pth = TAUT `p ==> q <=> (p \/ q <=> q)`
    and ptm = `p:bool` and qtm = `q:bool` in
    fun tm ->
      let negdjs,posdjs = partition is_neg (disjuncts tm) in
      let th = tryfind
       (fun p -> RING_RING_HORN (list_mk_disj(p::negdjs))) posdjs in
      let th1 = INST[concl th,ptm; tm,qtm] pth in
      MP (EQ_MP (SYM th1) (DISJ_ACI_RULE(rand(concl th1)))) th in
  let init_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    CONDS_ELIM_CONV THENC
    NNFC_CONV THENC CNF_CONV THENC
    SKOLEM_CONV THENC PRENEX_CONV THENC
    GEN_REWRITE_CONV REDEPTH_CONV
     [RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM DISJ_ASSOC] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM CONJ_ASSOC] in
  let RING_RULE_BASIC tm =
    let avs,bod = strip_forall tm in
    let th1 = init_conv bod in
    let tm' = rand(concl th1) in
    let avs',bod' = strip_forall tm' in
    let th2 = end_itlist CONJ (map RING_RING_CORE (conjuncts bod')) in
    let th3 = EQ_MP (SYM th1) (GENL avs' th2) in
    let imps = hyp th3 in
    let th4 =
      if imps = [] then th3
      else DISCH_ALL
             (itlist PROVE_HYP (CONJUNCTS(ASSUME(list_mk_conj imps))) th3) in
    GENL avs th4 in
  fun tm ->
    let tvs = type_vars_in_term tm in
    let ty = mk_vartype("Y"^itlist ((^) o dest_vartype) tvs "") in
    let tm' = inst[ty,aty] tm in
    INST_TYPE [aty,ty] (RING_RULE_BASIC tm');;

(* ------------------------------------------------------------------------- *)
(* A naive tactic form, pulling in equations in the assumptions and          *)
(* either solving outright or leaving some ring carrier membership           *)
(* ------------------------------------------------------------------------- *)

let RING_TAC =
  REPEAT GEN_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
  W(fun (asl,w) ->
        let th = RING_RULE w in
        (MATCH_ACCEPT_TAC th ORELSE
         ((fun g -> MATCH_MP_TAC th g) THEN ASM_REWRITE_TAC[])));;
*)

end (* structure ringLib *)
