open HolKernel Parse boolLib bossLib;

open (* BasicProvers *) boolSimps;

local open stringTheory pred_setTheory in end;

val _ = new_theory "basic_swap";

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before
                            export_rewrites [s])

(* ----------------------------------------------------------------------
    swapping over strings
   ---------------------------------------------------------------------- *)

Definition swapstr_def :
    swapstr x y (s:string) = if x = s then y else if y = s then x else s
End

Theorem swapstr_id[simp] :
    swapstr x x s = s
Proof
  SRW_TAC [][swapstr_def]
QED

Theorem swapstr_inverse[simp] :
    swapstr x y (swapstr x y s) = s
Proof
  SRW_TAC [][swapstr_def] THEN METIS_TAC []
QED

Theorem swapstr_eq_left :
    (swapstr x y s = t) <=> (s = swapstr x y t)
Proof
  SRW_TAC [][swapstr_def] THEN METIS_TAC []
QED

Theorem swapstr_11[simp] :
    (swapstr x y s1 = swapstr x y s2) <=> (s1 = s2)
Proof
  SRW_TAC [][swapstr_eq_left]
QED

fun simp_cond_tac (asl, g) = let
  val eqn = find_term (fn t => is_eq t andalso is_var (lhs t) andalso
                               is_var (rhs t)) g
in
  ASM_CASES_TAC eqn THEN TRY (POP_ASSUM SUBST_ALL_TAC) THEN
  ASM_SIMP_TAC bool_ss []
end (asl, g)

Theorem swapstr_swapstr[simp] :
    swapstr (swapstr x y u) (swapstr x y v) (swapstr x y s) =
    swapstr x y (swapstr u v s)
Proof
  REWRITE_TAC [swapstr_def] THEN REPEAT simp_cond_tac
QED

Theorem swapstr_comm[simp] :
    swapstr y x s = swapstr x y s
Proof
  SRW_TAC [][swapstr_def] THEN METIS_TAC []
QED

Theorem swapstr_thm[simp] :
    (swapstr x y x = y) /\ (swapstr x y y = x) /\
    (~(x = a) /\ ~(y = a) ==> (swapstr x y a = a))
Proof
  SRW_TAC [][swapstr_def]
QED

(* ----------------------------------------------------------------------
    swapping lists of pairs over strings (a foldr)
   ---------------------------------------------------------------------- *)

val raw_lswapstr_def = Define`
  (raw_lswapstr [] s = s) /\
  (raw_lswapstr (h::t) s = swapstr (FST h) (SND h) (raw_lswapstr t s))
`;
val _ = export_rewrites ["raw_lswapstr_def"]

val raw_lswapstr_APPEND = store_thm(
  "raw_lswapstr_APPEND",
  ``raw_lswapstr (p1 ++ p2) s = raw_lswapstr p1 (raw_lswapstr p2 s)``,
  Induct_on `p1` THEN SRW_TAC [][raw_lswapstr_def]);

val raw_lswapstr_inverse = store_thm(
  "raw_lswapstr_inverse",
  ``!p s. (raw_lswapstr (REVERSE p) (raw_lswapstr p s) = s) /\
          (raw_lswapstr p (raw_lswapstr (REVERSE p) s) = s)``,
  Induct THEN SRW_TAC [][raw_lswapstr_def, raw_lswapstr_APPEND]);
val _ = export_rewrites ["raw_lswapstr_inverse"]

val raw_lswapstr_11 = store_thm(
  "raw_lswapstr_11",
  ``(raw_lswapstr p s = raw_lswapstr p t) = (s = t)``,
  METIS_TAC [raw_lswapstr_inverse]);
val _ = export_rewrites ["raw_lswapstr_11"]

val raw_lswapstr_eql = store_thm(
  "raw_lswapstr_eql",
  ``(raw_lswapstr p s = t) = (s = raw_lswapstr (REVERSE p) t)``,
  METIS_TAC [raw_lswapstr_inverse]);

val raw_lswapstr_eqr = store_thm(
  "raw_lswapstr_eqr",
  ``(s = raw_lswapstr p t) = (raw_lswapstr (REVERSE p) s =  t)``,
  METIS_TAC [raw_lswapstr_inverse]);

val raw_lswapstr_sing_to_back = store_thm(
  "raw_lswapstr_sing_to_back",
  ``!p u v s. swapstr (raw_lswapstr p u) (raw_lswapstr p v) (raw_lswapstr p s) =
              raw_lswapstr p (swapstr u v s)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

(* ----------------------------------------------------------------------
    NEW constant
   ---------------------------------------------------------------------- *)

Theorem INFINITE_STR_UNIV :
    INFINITE (UNIV : string set)
Proof
  SRW_TAC [][pred_setTheory.INFINITE_UNIV] THEN
  Q.EXISTS_TAC `\st. STRING (CHR 0) st` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `""` THEN SRW_TAC [][]
QED

Theorem new_exists :
    !s : string set. FINITE s ==> ?x. ~(x IN s)
Proof
  Q_TAC SUFF_TAC `INFINITE (UNIV : string set)`
        THEN1 METIS_TAC [pred_setTheory.IN_UNIV,
                         pred_setTheory.IN_INFINITE_NOT_FINITE] THEN
  SRW_TAC [][INFINITE_STR_UNIV]
QED

val NEW_def =
    new_specification
      ("NEW_def", ["NEW"],
       SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] new_exists)

Theorem NEW_ELIM_RULE :
    !P X. FINITE X /\ (!v:string. ~(v IN X) ==> P v) ==>
          P (NEW X)
Proof
  PROVE_TAC [NEW_def]
QED

val _ = export_theory();
val _ = html_theory "basic_swap";
