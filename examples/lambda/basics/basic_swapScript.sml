open HolKernel Parse boolLib bossLib;

open BasicProvers boolSimps numpairTheory stringTheory pred_setTheory hurdUtils
     listTheory rich_listTheory;

val _ = new_theory "basic_swap";

(* ----------------------------------------------------------------------
    swapping over strings
   ---------------------------------------------------------------------- *)

val swapstr_def = Define`
  swapstr x y (s:string) = if x = s then y else if y = s then x else s
`;

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

val INFINITE_STR_UNIV = store_thm(
  "INFINITE_STR_UNIV",
  ``INFINITE (UNIV : string set)``,
  SRW_TAC [][pred_setTheory.INFINITE_UNIV] THEN
  Q.EXISTS_TAC `\st. STRING (CHR 0) st` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `""` THEN SRW_TAC [][]);

val new_exists = store_thm(
  "new_exists",
  ``!s : string set. FINITE s ==> ?x. ~(x IN s)``,
  Q_TAC SUFF_TAC `INFINITE (UNIV : string set)`
        THEN1 METIS_TAC [pred_setTheory.IN_UNIV,
                         pred_setTheory.IN_INFINITE_NOT_FINITE] THEN
  SRW_TAC [][INFINITE_STR_UNIV]);

(* |- !s. FINITE s ==> NEW s NOTIN s *)
val NEW_def =
    new_specification
      ("NEW_def", ["NEW"],
       SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] new_exists)

val NEW_ELIM_RULE = store_thm(
  "NEW_ELIM_RULE",
  ``!P X. FINITE X /\ (!v:string. ~(v IN X) ==> P v) ==>
          P (NEW X)``,
  PROVE_TAC [NEW_def]);

(* ----------------------------------------------------------------------
    The NEWS constant for allocating a list of fresh variables
   ---------------------------------------------------------------------- *)

(* A number-like system of fresh symbols (excluding a given set of names) *)
Definition Num_def :
    Num s n = NEW (s UNION IMAGE (Num s) (count n))
Termination
    WF_REL_TAC ‘measure SND’ >> simp []
End

(* Num and NEW, but the explicit uses of ‘Num’ should be restricted here. *)
Theorem Num_0[simp] :
    Num s 0 = NEW s
Proof
    rw [Once Num_def]
QED

Theorem Num_thm :
    !s. FINITE s ==>
         (!n. Num s n NOTIN s) /\ (!m n. m <> n ==> Num s m <> Num s n)
Proof
    NTAC 2 STRIP_TAC
 >> CONJ_TAC
 >- (completeInduct_on ‘n’ \\
     rw [Once Num_def] \\
     qabbrev_tac ‘X = s UNION IMAGE (\a. Num s a) (count n)’ \\
    ‘s SUBSET X’ by rw [Abbr ‘X’] \\
     Suff ‘NEW X NOTIN X’ >- METIS_TAC [SUBSET_DEF] \\
     MATCH_MP_TAC NEW_def >> rw [Abbr ‘X’])
 (* stage work *)
 >> Suff ‘!m n. m < n ==> Num s m <> Num s n’
 >- (rpt STRIP_TAC \\
    ‘m < n \/ n < m’ by rw [] >> METIS_TAC [])
 >> NTAC 3 STRIP_TAC
 >> ASSUME_TAC (ONCE_REWRITE_CONV [Num_def] “Num s n”)
 >> POP_ORW
 >> qabbrev_tac ‘X = s UNION IMAGE (\a. Num s a) (count n)’
 >> CCONTR_TAC
 >> Know ‘NEW X NOTIN X’
 >- (MATCH_MP_TAC NEW_def >> rw [Abbr ‘X’])
 >> fs []
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> rw [Abbr ‘X’]
QED

Theorem Num_11 :
    !s m n. FINITE s ==> (Num s m = Num s n <=> m = n)
Proof
    METIS_TAC [Num_thm]
QED

(* ‘NEWS n s’ generates n fresh names from the excluded set ‘s’

   Old definition (Michael Norrish):

Definition NEWS :
    NEWS      0  s = [] /\
    NEWS (SUC n) s = NEW s :: NEWS n (NEW s INSERT s)
End

   New definition (Chun Tian):
 *)
Definition NEWS :
    NEWS n s = GENLIST (Num s) n
End

Theorem NEWS_0[simp] :
    NEWS 0 s = []
Proof
    rw [NEWS]
QED

(* NEWS and NEW *)
Theorem NEWS_1[simp] :
    NEWS 1 s = [NEW s]
Proof
    rw [NEWS]
QED

(* This is actually an alternative recursive definition of ‘NEWS’ *)
Theorem NEWS_SUC :
    !s. NEWS (SUC n) s = SNOC (Num s n) (NEWS n s)
Proof
    rw [NEWS, GENLIST]
QED

(* This is the old equivalent definition of FRESH_list_def *)
Theorem NEWS_def :
    !n s. FINITE s ==>
          ALL_DISTINCT (NEWS n s) /\ DISJOINT (set (NEWS n s)) s /\
          LENGTH (NEWS n s) = n
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on ‘n’ >- rw [NEWS]
 >> simp [NEWS_SUC]
 >> rw [ALL_DISTINCT_SNOC, DISJOINT_ALT]
 >- (rw [NEWS, MEM_GENLIST] \\
     CCONTR_TAC >> ‘n <> m’ by rw [] \\
     METIS_TAC [Num_thm])
 >- METIS_TAC [Num_thm]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem NEWS_prefix :
    !m n s. m <= n ==> NEWS m s <<= NEWS n s
Proof
    rw [NEWS]
 >> MATCH_MP_TAC IS_PREFIX_GENLIST >> art []
QED

(* ----------------------------------------------------------------------
    DNEWS for allocating a ranked list of fresh names

    Each rank (row) contains a mutually-disjoint infinite list of fresh names

  r\i| 0 1 2 3 4 ...
  ---+-----------------
   0 | a b c d e ...
   1 | A B C D E ...
   2 | ...
   ---------------------------------------------------------------------- *)

(* r: rank, n: number, s: the excluded set *)
Definition DNEWS :
    DNEWS r n s = GENLIST (\i. Num s (npair r i)) n
End

Theorem DNEWS_0[simp] :
    DNEWS r 0 s = []
Proof
    rw [DNEWS]
QED

(* DNEWS and NEW *)
Theorem DNEWS_01[simp] :
    DNEWS 0 1 s = [NEW s]
Proof
    rw [DNEWS]
QED

Theorem DNEWS_SUC :
    !s. DNEWS r (SUC n) s = SNOC (Num s (npair r n)) (DNEWS r n s)
Proof
    rw [DNEWS, GENLIST]
QED

(* This basic theorem is compatible with NEWS_def (FRESH_list_def) *)
Theorem DNEWS_def :
    !r n s. FINITE s ==>
            ALL_DISTINCT (DNEWS r n s) /\ DISJOINT (set (DNEWS r n s)) s /\
            LENGTH (DNEWS r n s) = n
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on ‘n’ >- rw [DNEWS]
 >> simp [DNEWS_SUC]
 >> rw [ALL_DISTINCT_SNOC, DISJOINT_ALT]
 >- (rw [DNEWS, MEM_GENLIST] \\
     CCONTR_TAC >> ‘i <> n’ by rw [] \\
     rfs [Num_11])
 >- METIS_TAC [Num_thm]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem DNEWS_prefix :
    !r m n s. m <= n ==> DNEWS r m s <<= DNEWS r n s
Proof
    rw [DNEWS]
 >> MATCH_MP_TAC IS_PREFIX_GENLIST >> art []
QED

Theorem DNEWS_disjoint_ranks :
    !r r' m n s. FINITE s /\ r <> r' ==>
                 DISJOINT (set (DNEWS r m s)) (set (DNEWS r' n s))
Proof
    rw [DNEWS, DISJOINT_ALT, MEM_GENLIST]
 >> rfs [Num_11]
QED

val _ = export_theory();
val _ = html_theory "basic_swap";
