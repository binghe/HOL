(* ------------------------------------------------------------------------- *)
(* List Range                                                                *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib BasicProvers;

open arithmeticTheory TotalDefn simpLib numSimps numLib listTheory metisLib
     pred_setTheory;

val _ = new_theory "listRange";

val decide_tac = DECIDE_TAC;
val metis_tac = METIS_TAC;
val rw = SRW_TAC [ARITH_ss];

val listRangeINC_def = Define`
  listRangeINC m n = GENLIST (\i. m + i) (n + 1 - m)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "[", TM, HardSpace 1, TOK "..",
                                  BreakSpace(1,1), TM, BreakSpace(0,0),
                                  TOK "]"],
                   term_name = "listRangeINC" }

val listRangeINC_SING = store_thm(
  "listRangeINC_SING",
  ``[m .. m] = [m]``,
  SIMP_TAC (srw_ss()) [listRangeINC_def]);
val _ = export_rewrites ["listRangeINC_SING"]

val MEM_listRangeINC = store_thm(
  "MEM_listRangeINC",
  ``MEM x [m .. n] <=> m <= x /\ x <= n``,
  SIMP_TAC (srw_ss() ++ ARITH_ss)
           [listRangeINC_def, MEM_GENLIST, EQ_IMP_THM] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `x - m` THEN DECIDE_TAC);
val _ = export_rewrites ["MEM_listRangeINC"]

val listRangeINC_CONS = store_thm(
  "listRangeINC_CONS",
  ``m <= n ==> ([m .. n] = m :: [m+1 .. n])``,
  SIMP_TAC (srw_ss()) [listRangeINC_def] THEN STRIP_TAC THEN
  `(n + 1 - m = SUC (n - m)) /\ (n + 1 - (m + 1) = n - m)` by DECIDE_TAC THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [GENLIST_CONS, GENLIST_FUN_EQ]);

val listRangeINC_EMPTY = store_thm(
  "listRangeINC_EMPTY",
  ``n < m ==> ([m .. n] = [])``,
  SRW_TAC [][listRangeINC_def] THEN
  `n + 1 - m = 0` by DECIDE_TAC THEN SRW_TAC[][]);

val listRangeLHI_def = Define`
  listRangeLHI m n = GENLIST (\i. m + i) (n - m)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "[", TM, HardSpace 1, TOK "..<",
                                  BreakSpace(1,1), TM, BreakSpace(0,0),
                                  TOK "]"],
                   term_name = "listRangeLHI" }

val listRangeLHI_EQ = store_thm(
  "listRangeLHI_EQ",
  ``[m ..< m] = []``,
  SRW_TAC[][listRangeLHI_def]);
val _ = export_rewrites ["listRangeLHI_EQ"]

val MEM_listRangeLHI = store_thm(
  "MEM_listRangeLHI",
  ``MEM x [m ..< n] <=> m <= x /\ x < n``,
  SRW_TAC[ARITH_ss][listRangeLHI_def, MEM_GENLIST, EQ_IMP_THM] THEN
  Q.EXISTS_TAC `x - m` THEN DECIDE_TAC);
val _ = export_rewrites ["MEM_listRangeLHI"]

val listRangeLHI_EMPTY = store_thm(
  "listRangeLHI_EMPTY",
  ``hi <= lo ==> ([lo ..< hi] = [])``,
  SRW_TAC[][listRangeLHI_def] THEN
  `hi - lo = 0` by DECIDE_TAC THEN
  SRW_TAC[][]);

val listRangeLHI_CONS = store_thm(
  "listRangeLHI_CONS",
  ``lo < hi ==> ([lo ..< hi] = lo :: [lo + 1 ..< hi])``,
  SRW_TAC[][listRangeLHI_def] THEN
  `hi - lo = SUC (hi - (lo + 1))` by DECIDE_TAC THEN
  SRW_TAC[ARITH_ss][listTheory.GENLIST_CONS, listTheory.GENLIST_FUN_EQ]);

val listRangeLHI_ALL_DISTINCT = store_thm(
  "listRangeLHI_ALL_DISTINCT",
  ``ALL_DISTINCT [lo ..< hi]``,
  Induct_on `hi - lo` THEN SRW_TAC[][listRangeLHI_EMPTY] THEN
  `lo < hi` by DECIDE_TAC THEN
  SRW_TAC[ARITH_ss][listRangeLHI_CONS]);
val _ = export_rewrites ["listRangeLHI_ALL_DISTINCT"]

val LENGTH_listRangeLHI = store_thm(
  "LENGTH_listRangeLHI",
  ``LENGTH [lo ..< hi] = hi - lo``,
  SRW_TAC[][listRangeLHI_def]);
val _ = export_rewrites ["LENGTH_listRangeLHI"]

val EL_listRangeLHI = store_thm(
  "EL_listRangeLHI",
  ``lo + i < hi ==> (EL i [lo ..< hi] = lo + i)``,
  Q.ID_SPEC_TAC `i` THEN Induct_on `hi - lo` THEN
  SRW_TAC[ARITH_ss][listRangeLHI_EMPTY] THEN
  `lo < hi` by DECIDE_TAC THEN
  SRW_TAC[ARITH_ss][listRangeLHI_CONS] THEN
  Cases_on `i` THEN
  SRW_TAC[ARITH_ss][]);

(* Theorem: [m .. n] = [m ..< SUC n] *)
(* Proof:
   = [m .. n]
   = GENLIST (\i. m + i) (n + 1 - m)     by listRangeINC_def
   = [m ..< (n + 1)]                     by listRangeLHI_def
   = [m ..< SUC n]                       by ADD1
*)
Theorem listRangeINC_to_LHI:
  !m n. [m .. n] = [m ..< SUC n]
Proof
  rw[listRangeLHI_def, listRangeINC_def, ADD1]
QED

(* Theorem: set [1 .. n] = IMAGE SUC (count n) *)
(* Proof:
       x IN set [1 .. n]
   <=> 1 <= x /\ x <= n                  by listRangeINC_MEM
   <=> 0 < x /\ PRE x < n                by arithmetic
   <=> 0 < SUC (PRE x) /\ PRE x < n      by SUC_PRE, 0 < x
   <=> x IN IMAGE SUC (count n)          by IN_COUNT, IN_IMAGE
*)
Theorem listRangeINC_SET:
  !n. set [1 .. n] = IMAGE SUC (count n)
Proof
  rw[EXTENSION, EQ_IMP_THM] >>
  `0 < x /\ PRE x < n` by decide_tac >>
  metis_tac[SUC_PRE]
QED

(* Theorem: LENGTH [m .. n] = n + 1 - m *)
(* Proof:
     LENGTH [m .. n]
   = LENGTH (GENLIST (\i. m + i) (n + 1 - m))  by listRangeINC_def
   = n + 1 - m                                 by LENGTH_GENLIST
*)
val listRangeINC_LEN = store_thm(
  "listRangeINC_LEN",
  ``!m n. LENGTH [m .. n] = n + 1 - m``,
  rw[listRangeINC_def]);

(* Theorem: ([m .. n] = []) <=> (n + 1 <= m) *)
(* Proof:
              [m .. n] = []
   <=> LENGTH [m .. n] = 0         by LENGTH_NIL
   <=>       n + 1 - m = 0         by listRangeINC_LEN
   <=>          n + 1 <= m         by arithmetic
*)
val listRangeINC_NIL = store_thm(
  "listRangeINC_NIL",
  ``!m n. ([m .. n] = []) <=> (n + 1 <= m)``,
  metis_tac[listRangeINC_LEN, LENGTH_NIL, DECIDE``(n + 1 - m = 0) <=> (n + 1 <= m)``]);

(* Rename a theorem *)
val listRangeINC_MEM = save_thm("listRangeINC_MEM",
    MEM_listRangeINC |> GEN ``x:num`` |> GEN ``n:num`` |> GEN ``m:num``);
(*
val listRangeINC_MEM = |- !m n x. MEM x [m .. n] <=> m <= x /\ x <= n: thm
*)

(*
EL_listRangeLHI
|- lo + i < hi ==> EL i [lo ..< hi] = lo + i
*)

(* Theorem: m + i <= n ==> (EL i [m .. n] = m + i) *)
(* Proof: by listRangeINC_def *)
val listRangeINC_EL = store_thm(
  "listRangeINC_EL",
  ``!m n i. m + i <= n ==> (EL i [m .. n] = m + i)``,
  rw[listRangeINC_def]);

(* Theorem: EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. MEM x [m .. n] ==> P x      by EVERY_MEM
   <=> !x. m <= x /\ x <= n ==> P x    by MEM_listRangeINC
*)
val listRangeINC_EVERY = store_thm(
  "listRangeINC_EVERY",
  ``!P m n. EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x``,
  rw[EVERY_MEM, MEM_listRangeINC]);


(* Theorem: EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x *)
(* Proof:
       EXISTS P [m .. n]
   <=> ?x. MEM x [m .. n] /\ P x      by EXISTS_MEM
   <=> ?x. m <= x /\ x <= n /\ P e    by MEM_listRangeINC
*)
val listRangeINC_EXISTS = store_thm(
  "listRangeINC_EXISTS",
  ``!P m n. EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x``,
  metis_tac[EXISTS_MEM, MEM_listRangeINC]);

(* Theorem: EVERY P [m .. n] <=> ~(EXISTS ($~ o P) [m .. n]) *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. m <= x /\ x <= n ==> P x        by listRangeINC_EVERY
   <=> ~(?x. m <= x /\ x <= n /\ ~(P x))   by negation
   <=> ~(EXISTS ($~ o P) [m .. m])         by listRangeINC_EXISTS
*)
val listRangeINC_EVERY_EXISTS = store_thm(
  "listRangeINC_EVERY_EXISTS",
  ``!P m n. EVERY P [m .. n] <=> ~(EXISTS ($~ o P) [m .. n])``,
  rw[listRangeINC_EVERY, listRangeINC_EXISTS]);

(* Theorem: EXISTS P [m .. n] <=> ~(EVERY ($~ o P) [m .. n]) *)
(* Proof:
       EXISTS P [m .. n]
   <=> ?x. m <= x /\ x <= m /\ P x           by listRangeINC_EXISTS
   <=> ~(!x. m <= x /\ x <= n ==> ~(P x))    by negation
   <=> ~(EVERY ($~ o P) [m .. n])            by listRangeINC_EVERY
*)
val listRangeINC_EXISTS_EVERY = store_thm(
  "listRangeINC_EXISTS_EVERY",
  ``!P m n. EXISTS P [m .. n] <=> ~(EVERY ($~ o P) [m .. n])``,
  rw[listRangeINC_EXISTS, listRangeINC_EVERY]);

val _ = export_theory();
