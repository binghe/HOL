(* ========================================================================= *)
(*  A decision procedure for the universal theory of rings                   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)
(* Ported by Chun Tian. The Australian National University (ANU), 2024       *)
(* ========================================================================= *)

structure ringLib :> ringLib =
struct

open HolKernel boolLib bossLib;

open cardinalTheory ringTheory ringLibTheory Normalizer normalForms tautLib
     Canon Canon_Port;

(* ------------------------------------------------------------------------- *)
(* Establish the required grammar(s) for executing this file                 *)
(* ------------------------------------------------------------------------- *)

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars ringLib_grammars
end

open Parse;

val ERR = mk_HOL_ERR "ringLib";
fun failwith s = raise ERR "?" s

(* |- !P Q. P /\ (?x. Q x) <=> ?x. P /\ Q x *)
val RIGHT_AND_EXISTS_THM = GSYM RIGHT_EXISTS_AND_THM

(* |- !P Q. (?x. P x) /\ Q <=> ?x. P x /\ Q *)
val LEFT_AND_EXISTS_THM = GSYM LEFT_EXISTS_AND_THM

(* |- p ==> q ==> r <=> p /\ q ==> r *)
val IMP_IMP = Q.SPECL [‘p’, ‘q’, ‘r’] AND_IMP_INTRO;

val PRENEX_CONV = Canon.PRENEX_CONV;
val CNF_CONV = Canon.CNF_CONV;

(* A sample input for RING_RULE:

   |- y1 * inv y1 = 1 /\ y2 * inv y2 = 1 /\ x1 * y2 = x2 * y1 ==>
      x1 * inv y1 = x2 * inv y2

   NOTE: RING_RULE doesn't know ‘ring_inv’ and jusst treats ‘ring_inv y y1’ as
         an atom (or single variable).

   val tm =
    ``ring_mul r y1 (ring_inv r y1) = ring_1 r /\
      ring_mul r y2 (ring_inv r y2) = ring_1 r /\
      ring_mul r x1 y2 = ring_mul r x2 y1
      ==> ring_mul r x1 (ring_inv r y1) = ring_mul r x2 (ring_inv r y2)``;

   RING_RULE tm
 *)

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer and ring procedure for the case of a ring      *)
(* "r:A ring" with the whole type A as the carrier. Since all the machinery  *)
(* of the normalizer is designed for such "universal" rings, this is the     *)
(* best we can do, but below we use this to define a general procedure.      *)
(* The RING instantiation is called RING_INTEGRAL_DOMAIN_UNIVERSAL since     *)
(* it in general assumes "integral_domain r" and may also assume that        *)
(* "ring_char r = 0". Later we use the other cofactors function to give      *)
(* a better decision procedure for general rings, but the integral           *)
(* domain one may be independently useful for proofs involving cancellation  *)
(* in such domains.                                                          *)
(* ------------------------------------------------------------------------- *)

(*
let RING_POLY_UNIVERSAL_CONV =
  let pth = (UNDISCH o SPEC_ALL o prove)
   (`!r. ring_carrier r = (:A)
          ==> (!x y z. ring_add r x (ring_add r y z) =
                       ring_add r (ring_add r x y) z) /\
              (!x y. ring_add r x y = ring_add r y x) /\
              (!x. ring_add r (ring_of_int r (&0)) x = x) /\
              (!x y z. ring_mul r x (ring_mul r y z) =
                       ring_mul r (ring_mul r x y) z) /\
              (!x y. ring_mul r x y = ring_mul r y x) /\
              (!x. ring_mul r (ring_of_int r (&1)) x = x) /\
              (!x. ring_mul r (ring_of_int r (&0)) x = ring_of_int r (&0)) /\
              (!x y z. ring_mul r x (ring_add r y z) =
                       ring_add r (ring_mul r x y) (ring_mul r x z)) /\
              (!x. ring_pow r x 0 = ring_of_int r (&1)) /\
              (!x n. ring_pow r x (SUC n) = ring_mul r x (ring_pow r x n))`,
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_1; CONJUNCT1 ring_of_num] THEN
    SIMP_TAC[RING_ADD_LZERO; RING_MUL_LID; RING_MUL_LZERO; IN_UNIV] THEN
    SIMP_TAC[ring_pow; RING_ADD_LDISTRIB; IN_UNIV] THEN
    SIMP_TAC[RING_ADD_AC; RING_MUL_AC; IN_UNIV])
  and sth = (UNDISCH o SPEC_ALL o prove)
   (`!r. ring_carrier r = (:A)
          ==> (!x. ring_neg r x = ring_mul r (ring_of_int r (-- &1)) x) /\
              (!x y. ring_sub r x y =
                     ring_add r x (ring_mul r (ring_of_int r (-- &1)) y))`,
    SIMP_TAC[RING_OF_INT_NEG; RING_MUL_LNEG; IN_UNIV; ring_sub] THEN
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_1; CONJUNCT1 ring_of_num] THEN
    SIMP_TAC[ring_sub; RING_MUL_LNEG; RING_MUL_LID; IN_UNIV])
  and RING_INT_ADD_CONV =
      GEN_REWRITE_CONV I [GSYM RING_OF_INT_ADD] THENC
      RAND_CONV INT_ADD_CONV
  and RING_INT_MUL_CONV =
    GEN_REWRITE_CONV I [GSYM RING_OF_INT_MUL] THENC
    RAND_CONV INT_MUL_CONV
  and RING_INT_POW_CONV =
    GEN_REWRITE_CONV I [GSYM RING_OF_INT_POW] THENC
    RAND_CONV INT_POW_CONV
  and is_ringconst tm =
    match tm with
      Comb(Comb(Const("ring_of_int",_),_),n) -> is_intconst n
    | _ -> false
  and ith = prove
   (`ring_0 r = ring_of_int r (&0) /\
     ring_1 r = ring_of_int r (&1)`,
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_1; CONJUNCT1 ring_of_num]) in
  let _,_,_,_,_,RING_POLY_CONV =
    SEMIRING_NORMALIZERS_CONV pth sth
     (is_ringconst,
      RING_INT_ADD_CONV,RING_INT_MUL_CONV,RING_INT_POW_CONV)
     (<) in
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [ith; GSYM RING_OF_INT_OF_NUM] THENC
  RING_POLY_CONV;;
 *)

(* ------------------------------------------------------------------------- *)
(* Iterative splitting (list) and stripping (tree) via destructor.           *)
(* ------------------------------------------------------------------------- *)

fun splitlist dest x = let
    val (l,r) = dest x;
    val (ls,res) = splitlist dest r
in
    (l::ls,res)
end
handle HOL_ERR _ => ([],x)

(* ------------------------------------------------------------------------- *)
(* Derived rule to take a theorem asserting a monomorphism between r and r'  *)
(* and a term that is some Boolean combination of equations in the ring r    *)
(* and prove it equivalent to a "transferred" version in r' where all the    *)
(* variables x (in r) in the original map to "f x" (in r').                  *)
(* ------------------------------------------------------------------------- *)

(*
fun RING_MONOMORPHIC_IMAGE_RULE hth = let
    val pth = RING_MONOMORPHIC_IMAGE_RULE_THM;
    val ([pth_eq, pth_asm,
          pth_0, pth_1,
          pth_num, pth_int,
          pth_neg, pth_pow,
          pth_add, pth_sub], pth_mul) = splitlist CONJ_PAIR (MATCH_MP pth hth)
    and htm = rand(concl hth);
    fun mterm tm =
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
      | _ -> UNDISCH(SPEC tm pth_asm);
    fun mform tm =
      if is_neg tm then
         RAND_CONV mform tm
      else if is_iff tm || is_imp tm || is_conj tm || is_disj tm then
         BINOP_CONV mform tm
      else if is_eq tm then
        let s,t = dest_eq tm in
        let sth = mterm s and tth = mterm t in
        MATCH_MP pth_eq (CONJ sth tth)
      else failwith "RING_MONOMORPHIC_IMAGE_RULE: unhandled formula"
in
    mform
end
*)

(* ------------------------------------------------------------------------- *)
(* A decision procedure for the universal theory of rings, mapping           *)
(* momomorphically into a "total" ring to leverage earlier stuff.            *)
(* It will prove either the exact thing you request, or if you omit some     *)
(* carrier membership hypotheses, will add those as an antecedent.           *)
(* ------------------------------------------------------------------------- *)

(*
val RING_WORD_UNIVERSAL = let
    val cth = RING_WORD_UNIVERSAL_LEMMA1
    and pth = UNDISCH RING_WORD_UNIVERSAL_LEMMA2
    and bth = REFL “ring_of_int r (&0) :'a”
    and mth = UNDISCH RING_WORD_UNIVERSAL_LEMMA3
    and dth = UNDISCH RING_WORD_UNIVERSAL_LEMMA4;
    val decorule =
      GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
       [cth, GSYM RING_OF_INT_OF_NUM] o
      PART_MATCH lhand pth
in
    fn tm => let
      val (avs,bod) = strip_forall tm in
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
        EQ_MP (SYM th2) bth
    end
end;
 *)

val RING_RING_WORD = let
    val imp_imp_rule = GEN_REWRITE_RULE I empty_rewrites [IMP_IMP]
    and left_exists_rule = GEN_REWRITE_RULE I empty_rewrites [LEFT_FORALL_IMP_THM]
    and or_elim_rule =
      GEN_REWRITE_RULE I empty_rewrites [TAUT `(p ==> q) /\ (p' ==> q) <=> p \/ p' ==> q`]
in
    fn ths tm => let
      val dty = type_of(rand tm);
      val rty = mk_type("Ring",[dty]);
      val rtms = filter (curry (=) rty o type_of) (freesl(tm::map concl ths))
    in
      if length rtms <> 1
      then failwith "RING_RULE: can't deduce which ring" else let
      val rtm = hd rtms;
      val tvs = itlist (union o type_vars_in_term o concl) ths
                       (type_vars_in_term tm);
      val dty' = mk_vartype("Z"^itlist (curry (^) o dest_vartype) tvs "");
      val rty' = mk_type("Ring",[dty']);
      val avvers = HOLset.listItems
                     (itlist (fn th => fn s =>
                                 HOLset.addList (s,all_vars (concl th))) ths
                             (HOLset.addList (empty_tmset, all_vars tm)));
      val rtm' = variant avvers (mk_var("r'",rty'))
      and htm = variant avvers (mk_var("h",dty --> dty'));
      val hasm = list_mk_icomb (“ring_monomorphism”, [mk_pair(rtm,rtm'), htm]);
      val hth = ASSUME hasm;
   (* TODO *)
      val ths' = mapfilter (CONV_RULE(RING_MONOMORPHIC_IMAGE_RULE hth)) ths
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
      MP (or_elim_rule th11) th10 end
    end
end;

val RING_RING_HORN = let
    val ddj_conv =
        GEN_REWRITE_CONV (RAND_CONV o DEPTH_CONV) empty_rewrites
          [TAUT ‘~p \/ ~q <=> ~(p /\ q)’] THENC
        GEN_REWRITE_CONV I empty_rewrites [TAUT ‘p \/ ~q <=> q ==> p’]
in
    fn tm =>
       if not(is_disj tm) then RING_RING_WORD [] tm else
       let val th0 = ddj_conv tm;
           val tm' = rand(concl th0);
           val abod = lhand tm';
           val ths = CONJUNCTS(ASSUME abod);
           val th1 = RING_RING_WORD ths (rand tm')
       in
           EQ_MP (SYM th0) (DISCH abod (itlist PROVE_HYP ths th1))
       end
end;

val RING_RING_CORE = let
    val pth = TAUT ‘p ==> q <=> (p \/ q <=> q)’
    and ptm = “p:bool” and qtm = “q:bool”
in
    fn tm => let
      val (negdjs,posdjs) = partition is_neg (strip_disj tm);
      val th = tryfind
                 (fn p => RING_RING_HORN (list_mk_disj(p::negdjs))) posdjs;
      val th1 = INST [ptm |-> concl th, qtm |-> tm] pth
    in
      MP (EQ_MP (SYM th1) (DISJ_ACI_RULE(rand(concl th1)))) th
end;

val init_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    CONDS_ELIM_CONV THENC
    NNFC_CONV THENC CNF_CONV THENC
    SKOLEM_CONV THENC PRENEX_CONV THENC
    GEN_REWRITE_CONV REDEPTH_CONV empty_rewrites
     [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV empty_rewrites [GSYM DISJ_ASSOC] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV empty_rewrites [GSYM CONJ_ASSOC];

fun RING_RULE_BASIC tm = let
    val (avs,bod) = strip_forall tm;
    val th1 = init_conv bod;
    val tm' = rand(concl th1);
    val (avs',bod') = strip_forall tm';
    val th2 = end_itlist CONJ (map RING_RING_CORE (strip_conj bod'));
    let th3 = EQ_MP (SYM th1) (GENL avs' th2) in
    let imps = hyp th3 in
    let th4 =
      if imps = [] then th3
      else DISCH_ALL
             (itlist PROVE_HYP (CONJUNCTS(ASSUME(list_mk_conj imps))) th3)
in
    GENL avs th4
end;

(* The final version of RULE_RULE only temporarily changes the type variable
   alpha of input term to something fresh and then call RING_RULE_BASIC to
   do the actual job.
 *)
fun RING_RULE tm = let
    val tvs = type_vars_in_term tm;
    val ty = mk_vartype("Y" ^ itlist (curry (^) o dest_vartype) tvs "");
    val tm' = inst [alpha |-> ty] tm;
in
    INST_TYPE [ty |-> alpha] (RING_RULE_BASIC tm')
end;

(* ------------------------------------------------------------------------- *)
(* A naive tactic form, pulling in equations in the assumptions and          *)
(* either solving outright or leaving some ring carrier membership           *)
(* ------------------------------------------------------------------------- *)

(*
let RING_TAC =
  REPEAT GEN_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
  W(fn (asl,w) =>
        let th = RING_RULE w in
        (MATCH_ACCEPT_TAC th ORELSE
         ((fun g -> MATCH_MP_TAC th g) THEN ASM_REWRITE_TAC[])));
 *)

end (* structure ringLib *)
