(* ========================================================================== *)
(* FILE    : basic_swapScript.sml                                             *)
(* TITLE   : Some "basic" logic about swapping strings and the "new" operator *)
(*                                                                            *)
(* AUTHORS : 2005-2011 Michael Norrish                                        *)
(*         : 2023-2024 Michael Norrish and Chun Tian                          *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open BasicProvers boolSimps arithmeticTheory stringTheory pred_setTheory
     listTheory rich_listTheory pairTheory numpairTheory hurdUtils numLib
     cardinalTheory whileTheory;

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
  Induct THEN ASM_SIMP_TAC (srw_ss()) [FORALL_PROD]);

(* ----------------------------------------------------------------------
    The FRESH constant for allocating indexed distinct fresh names
   ---------------------------------------------------------------------- *)

Theorem INFINITE_STR_UNIV :
    INFINITE (UNIV : string set)
Proof
  SRW_TAC [][INFINITE_UNIV] THEN
  Q.EXISTS_TAC `\st. STRING (CHR 0) st` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `""` THEN SRW_TAC [][]
QED

Theorem COUNTABLE_STR_UNIV :
    countable univ(:string)
Proof
    MATCH_MP_TAC COUNTABLE_LIST_UNIV'
 >> rw [FINITE_UNIV_char]
QED

Definition FRESH_def :
    FRESH s = enumerate (univ(:string) DIFF s)
End

Theorem FRESH_BIJ :
    !s. FINITE s ==> BIJ (FRESH s) univ(:num) (univ(:string) DIFF s)
Proof
    rw [FRESH_def]
 >> qabbrev_tac ‘t = univ(:string) DIFF s’
 >> ‘countable t’ by METIS_TAC [COUNTABLE_DIFF_FINITE, COUNTABLE_STR_UNIV]
 >> ‘INFINITE t’  by METIS_TAC [INFINITE_DIFF_FINITE, INFINITE_STR_UNIV]
 >> fs [COUNTABLE_ALT_BIJ]
QED

Theorem FRESH_thm :
    !s. FINITE s ==> (!n. FRESH s n NOTIN s) /\ !m n. m <> n ==> FRESH s m <> FRESH s n
Proof
    Q.X_GEN_TAC ‘s’
 >> DISCH_THEN (ASSUME_TAC o MATCH_MP FRESH_BIJ)
 >> qabbrev_tac ‘t = univ(:string) DIFF s’
 >> CONJ_TAC
 >- (Q.X_GEN_TAC ‘n’ \\
     Suff ‘FRESH s n IN t’ >- rw [Abbr ‘t’] \\
     fs [BIJ_ALT, IN_FUNSET])
 >> rpt STRIP_TAC
 >> fs [BIJ_ALT, EXISTS_UNIQUE_THM, IN_FUNSET]
 >> METIS_TAC []
QED

Theorem FRESH_11[simp] :
    !s m n. FINITE s ==> (FRESH s m = FRESH s n <=> m = n)
Proof
    METIS_TAC [FRESH_thm]
QED

(* ----------------------------------------------------------------------
    NEW constant (now based on FRESH)
   ---------------------------------------------------------------------- *)

(* NOTE: This theorem is still used by NEWLib *)
val new_exists = store_thm(
  "new_exists",
  ``!s : string set. FINITE s ==> ?x. ~(x IN s)``,
  Q_TAC SUFF_TAC `INFINITE (UNIV : string set)`
        THEN1 METIS_TAC [pred_setTheory.IN_UNIV,
                         pred_setTheory.IN_INFINITE_NOT_FINITE] THEN
  SRW_TAC [][INFINITE_STR_UNIV]);

Definition NEW :
    NEW s = FRESH s 0
End

(* |- FRESH s 0 = NEW s *)
Theorem FRESH_0[simp] = SPEC_ALL (GSYM NEW)

Theorem NEW_def :
    !s. FINITE s ==> NEW s NOTIN s
Proof
    RW_TAC std_ss [NEW, FRESH_thm]
QED

Theorem NEW_ELIM_RULE :
    !P X. FINITE X /\ (!v:string. ~(v IN X) ==> P v) ==> P (NEW X)
Proof
    METIS_TAC [NEW_def]
QED

(* ----------------------------------------------------------------------
   A number-like system of fresh names excluding a given set (not used)

   NOTE: ‘NEW s’ is the "zero" in this number-like system.
   ---------------------------------------------------------------------- *)

(* NOTE: By FRESH_thm, the existence of ‘i’ is also unique. *)
Theorem FRESH_complete :
    !s. FINITE s ==> !x. x NOTIN s ==> ?i. FRESH s i = x
Proof
    Q.X_GEN_TAC ‘s’
 >> DISCH_THEN (ASSUME_TAC o MATCH_MP FRESH_BIJ)
 >> qabbrev_tac ‘t = univ(:string) DIFF s’
 >> rpt STRIP_TAC
 >> fs [COUNTABLE_ALT_BIJ, BIJ_THM, EXISTS_UNIQUE_THM]
 >> ‘x IN t’ by rw [Abbr ‘t’]
 >> Q.PAT_X_ASSUM ‘!y. y IN t ==> P’ (MP_TAC o Q.SPEC ‘x’)
 >> rw []
 >> rename1 ‘FRESH s y IN t’
 >> Q.EXISTS_TAC ‘y’ >> rw []
QED

(* ‘nSUC s v’ returns the next fresh symbol after ‘v’ *)
Definition nSUC_def :
    nSUC s x = let n = LEAST i. FRESH s i = x
               in FRESH s (SUC n)
End

Theorem nSUC_thm :
    !s x. FINITE s /\ x NOTIN s ==> nSUC s x NOTIN s /\ nSUC s x <> x
Proof
    NTAC 3 STRIP_TAC
 >> simp [nSUC_def]
 >> LEAST_ELIM_TAC
 >> CONJ_TAC
 >- METIS_TAC [FRESH_complete]
 >> rw [FRESH_thm]
 >> CCONTR_TAC >> rfs [FRESH_11]
QED

(* ----------------------------------------------------------------------
    The NEWS constant for allocating a list of fresh names
   ---------------------------------------------------------------------- *)

(* ‘NEWS n s’ generates n fresh names from the excluded set ‘s’

   Old definition (Michael Norrish):

Definition NEWS :
    NEWS      0  s = [] /\
    NEWS (SUC n) s = NEW s :: NEWS n (NEW s INSERT s)
End

   New definition (Chun Tian) based on ‘FRESH’:
 *)
Definition NEWS :
    NEWS n s = GENLIST (FRESH s) n
End

Theorem NEWS_0[simp] :
    NEWS 0 s = []
Proof
    rw [NEWS]
QED

Theorem NEWS_1[simp] :
    NEWS 1 s = [NEW s]
Proof
    RW_TAC list_ss [NEWS, NEW]
QED

(* This is actually an alternative recursive definition of ‘NEWS’ *)
Theorem NEWS_SUC :
    !s. NEWS (SUC n) s = SNOC (FRESH s n) (NEWS n s)
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
     METIS_TAC [FRESH_thm])
 >- METIS_TAC [FRESH_thm]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem NEWS_prefix :
    !m n s. m <= n ==> NEWS m s <<= NEWS n s
Proof
    rw [NEWS]
 >> MATCH_MP_TAC IS_PREFIX_GENLIST >> art []
QED

(* ----------------------------------------------------------------------
    DNEWS for allocating a ranked list of fresh names (Author: Chun Tian)

    Each positive rank (row) contains a disjoint infinite list of fresh names

    NOTE: Rank 0 contains all fresh names (to be compaible with NEWS).

   r\i| 0 1 2 3 4 ...
   ---+-----------------
    0 | a A b B c C d D e E ...
    1 | a b c d e ...
    2 | A B C D E ...
    3 | 1 2 3 4 5 ...
   ---------------------------------------------------------------------- *)

(* r: rank, n: number, s: the excluded set.

   Rank  *)
Definition DNEWS :
    DNEWS       0 n s = NEWS n s /\
    DNEWS (SUC r) n s = GENLIST (\i. FRESH s (npair r i)) n
End

Overload DNEWS' = “\r s. DNEWS (SUC r) s”

(* DNEWS and NEWS *)
Theorem DNEWS_NEWS[simp] :
    DNEWS 0 n s = NEWS n s
Proof
    rw [DNEWS]
QED

Theorem DNEWS_NIL[simp] :
    DNEWS r 0 s = []
Proof
    Cases_on ‘r’ >> rw [DNEWS]
QED

Theorem DNEWS_SUC :
    !r n s. DNEWS (SUC r) (SUC n) s = SNOC (FRESH s (npair r n)) (DNEWS (SUC r) n s)
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
 >> Cases_on ‘r’
 >- rw [DNEWS, NEWS_def]
 >> Induct_on ‘n’ >- rw [DNEWS]
 >> simp [DNEWS_SUC]
 >> rw [ALL_DISTINCT_SNOC, DISJOINT_ALT]
 >- rw [DNEWS, MEM_GENLIST]
 >- METIS_TAC [FRESH_thm]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem DNEWS_prefix :
    !r m n s. m <= n ==> DNEWS r m s <<= DNEWS r n s
Proof
    rpt STRIP_TAC
 >> Cases_on ‘r’
 >- rw [NEWS_prefix]
 >> rw [DNEWS]
 >> MATCH_MP_TAC IS_PREFIX_GENLIST >> art []
QED

Theorem DNEWS_disjoint :
    !r1 r2 m n s. FINITE s /\ r1 <> r2 ==>
                  DISJOINT (set (DNEWS (SUC r1) m s)) (set (DNEWS (SUC r2) n s))
Proof
    rw [DNEWS, DISJOINT_ALT, MEM_GENLIST]
 >> rfs [FRESH_11]
QED

Theorem DNEWS_set :
    !r n s. set (DNEWS (SUC r) n s) = {v | ?j. v = FRESH s (npair r j) /\ j < n}
Proof
    rw [DNEWS, Once EXTENSION, MEM_GENLIST]
 >> METIS_TAC []
QED

(* The (infinite) set of all fresh names lower than the given rank

   NOTE: ‘FRESH_SET (SUC r) s’ is the set of names lower than rank r (instead of SUC r).
   This is to align with ‘DNEWS’ where ‘DNEWS 0 = NEWS’ which is not ranked at all,
   while keeping |- DISJOINT (FRESH_SET r s) (set (DNEWS r n s)) holds perfectly.
 *)
Definition FRESH_SET :
    FRESH_SET       0 s = {} /\
    FRESH_SET (SUC r) s = {v | ?i j. v = FRESH s (npair i j) /\ i < r}
End

Overload FRESH_SET' = “\r s. FRESH_SET (SUC r) s”

Theorem FRESH_SET_0[simp] :
    FRESH_SET 0 s = {} /\ FRESH_SET 1 s = {}
Proof
    rw [FRESH_SET]
 >> REWRITE_TAC [ONE, FRESH_SET]
 >> rw []
QED

Theorem FRESH_SET_MONO :
    !s r1 r2. r1 <= r2 ==> FRESH_SET r1 s SUBSET FRESH_SET r2 s
Proof
    rpt GEN_TAC
 >> Cases_on ‘r1’ >> simp []
 >> Cases_on ‘r2’ >> simp []
 >> rw [FRESH_SET, SUBSET_DEF]
 >> qexistsl_tac [‘i’, ‘j’] >> rw []
QED

Theorem FRESH_SET_DISJOINT :
    !r1 r2 n s. FINITE s /\ r1 <= r2 ==>
                DISJOINT (FRESH_SET r1 s) (set (DNEWS r2 n s))
Proof
    rpt GEN_TAC
 >> Cases_on ‘r1’ >> simp []
 >> Cases_on ‘r2’ >> simp []
 >> rw [DISJOINT_ALT, DNEWS, MEM_GENLIST, FRESH_SET]
 >> rfs [FRESH_11]
QED

Theorem FRESH_SET_DISJOINT' :
    !r n s. FINITE s ==> DISJOINT (FRESH_SET r s) (set (DNEWS r n s))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC FRESH_SET_DISJOINT >> rw []
QED

(* NOTE: ‘set (DNEWS 0 n s) SUBSET FRESH_SET 0 s’ doesn't hold *)
Theorem FRESH_SET_SUBSET :
    !r1 r2 n s. r1 < r2 ==>
                set (DNEWS (SUC r1) n s) SUBSET FRESH_SET (SUC r2) s
Proof
    rw [DNEWS_set, FRESH_SET, SUBSET_DEF]
 >> qexistsl_tac [‘r1’, ‘j’] >> art []
QED

val _ = export_theory ();
val _ = html_theory "basic_swap";
