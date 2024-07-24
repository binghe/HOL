(* ========================================================================== *)
(* FILE    : basic_swapScript.sml                                             *)
(* TITLE   : Some "basic" logic about swapping strings and the "new" operator *)
(*                                                                            *)
(* AUTHORS : 2005-2011 Michael Norrish                                        *)
(*         : 2023-2024 Michael Norrish and Chun Tian                          *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open boolSimps arithmeticTheory stringTheory pred_setTheory numLib hurdUtils
     listTheory rich_listTheory pairTheory numpairTheory cardinalTheory
     string_numTheory;

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

(* NOTE: Another way is to use the existing BIJ (s2n/n2s) in string_numTheory *)
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
    !s. FINITE s ==> (!n. FRESH s n NOTIN s) /\
                      !m n. m <> n ==> FRESH s m <> FRESH s n
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

(* NOTE: This theorem is still used (somehow) by NEWLib *)
Theorem new_exists :
    !s : string set. FINITE s ==> ?x. ~(x IN s)
Proof
  Q_TAC SUFF_TAC `INFINITE (UNIV : string set)`
        THEN1 METIS_TAC [pred_setTheory.IN_UNIV,
                         pred_setTheory.IN_INFINITE_NOT_FINITE] THEN
  SRW_TAC [][INFINITE_STR_UNIV]
QED

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
    index_of - the inverse function of ‘FRESH’ mapping names back to num
   ---------------------------------------------------------------------- *)

(* NOTE: The existence of ‘i’ is also unique, according to FRESH_thm. *)
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

(* NOTE: ‘index_of’ is the inverse function of ‘FRESH’ *)
local
   val lemma = SRULE [EXT_SKOLEM_THM'] FRESH_complete;
in
   val index_of = new_specification ("index_of", ["index_of"], lemma);
end

Theorem index_of_thm :
    !x s. FINITE s /\ x NOTIN s ==> FRESH s (index_of s x) = x
Proof
    METIS_TAC [index_of]
QED

(* ----------------------------------------------------------------------
    rank and ranks - infinite set of all fresh names of certain ranks
   ---------------------------------------------------------------------- *)

Definition rank_def :
    rank s r = IMAGE (\j. FRESH s (npair r j)) UNIV
End

Overload RANK = “\r s. rank s r”

Theorem RANK :
    !s r. rank s r = {v | ?i j. v = FRESH s (npair i j) /\ i = r}
Proof
    rw [Once EXTENSION, rank_def]
QED

Definition ranks_def :
    ranks s r = BIGUNION (IMAGE (rank s) (count r))
End

Overload RANKS = “\r s. ranks s r”

Theorem RANKS :
    !s r. ranks s r = {v | ?i j. v = FRESH s (npair i j) /\ i < r}
Proof
    rw [Once EXTENSION, rank_def, ranks_def]
 >> EQ_TAC >> rw []
 >- (fs [] >> rename1 ‘i < r’ \\
     qexistsl_tac [‘i’, ‘j’] >> art [])
 >> Q.EXISTS_TAC ‘IMAGE (\j. FRESH s (i *, j)) UNIV’
 >> rw []
 >- (Q.EXISTS_TAC ‘j’ >> rw [])
 >> Q.EXISTS_TAC ‘i’ >> rw []
QED

Theorem RANKS_0[simp] :
    ranks s 0 = {}
Proof
    rw [RANKS]
QED

Theorem RANKS_MONO :
    !s r1 r2. r1 <= r2 ==> ranks s r1 SUBSET ranks s r2
Proof
    rw [RANKS, SUBSET_DEF]
 >> qexistsl_tac [‘i’, ‘j’] >> rw []
QED

Theorem RANKS_RANK_DISJOINT :
    !r1 r2 n s. FINITE s /\ r1 <= r2 ==>
                DISJOINT (ranks s r1) (rank s r2)
Proof
    rw [DISJOINT_ALT, RANK, RANKS]
 >> rw [FRESH_11]
QED

Theorem RANKS_RANK_DISJOINT' :
    !r n s. FINITE s ==> DISJOINT (ranks s r) (rank s r)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC RANKS_RANK_DISJOINT >> rw []
QED

Theorem RANKS_RANK_SUBSET :
    !r1 r2 n s. r1 < r2 ==> rank s r1 SUBSET ranks s r2
Proof
    rw [SUBSET_DEF, RANKS, RANK]
 >> qexistsl_tac [‘r1’, ‘j’] >> art []
QED

(* ----------------------------------------------------------------------
    subrank - fresh symbol from a rank excluding additional finite set
   ---------------------------------------------------------------------- *)

Definition subrank_def :
    subrank r s t i =
    let z = if t DIFF s = {} then 0 else
               SUC (MAX_SET (IMAGE (nsnd o index_of s) (t DIFF s)))
    in
       FRESH s (r *, (z + i))
End

Theorem subrank_thm :
    !r s t. FINITE s /\ FINITE t ==>
           (!m n. m <> n ==> subrank r s t m <> subrank r s t n) /\
           (!n. subrank r s t n IN rank s r) /\
           (!n. subrank r s t n NOTIN s) /\
           (!n. subrank r s t n NOTIN t)
Proof
    rw [subrank_def, rank_def, FRESH_thm]
 >- (Know ‘FRESH s (r *, n) NOTIN s’ >- rw [FRESH_thm] \\
     ASM_SET_TAC [])
 >> qabbrev_tac ‘t' = t DIFF s’
 >> ‘FINITE t'’ by rw [Abbr ‘t'’]
 >> qabbrev_tac ‘Z = IMAGE (nsnd o index_of s) t'’
 (* applying MAX_SET_PROPERTY *)
 >> Know ‘!x. x IN Z ==> x <= MAX_SET Z’
 >- (MATCH_MP_TAC MAX_SET_PROPERTY \\
     qunabbrev_tac ‘Z’ \\
     MATCH_MP_TAC IMAGE_FINITE >> art [])
 >> rw [Abbr ‘Z’]
 >> qabbrev_tac ‘Z = IMAGE (nsnd o index_of s) t'’
 >> qabbrev_tac ‘k = n + SUC (MAX_SET Z)’
 >> Suff ‘FRESH s (r *, k) NOTIN t'’
 >- simp [Abbr ‘t'’, FRESH_thm]
 (* applying index_of_thm *)
 >> Know ‘t' = {x | ?y. FRESH s (index_of s y) = x /\ y IN t'}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw []
     >- (Q.EXISTS_TAC ‘x’ >> art [] \\
         MATCH_MP_TAC index_of_thm >> fs [Abbr ‘t'’]) \\
     Suff ‘FRESH s (index_of s y) = y’ >- rw [] \\
     MATCH_MP_TAC index_of_thm >> fs [Abbr ‘t'’])
 >> Rewr'
 >> simp []
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!x. P ==> x <= MAX_SET Z’
      (MP_TAC o (Q.SPEC ‘nsnd (index_of s y)’))
 >> simp [Abbr ‘k’]
 >> Q.EXISTS_TAC ‘y’ >> simp []
QED

Theorem subrank_11[simp] :
    !r1 r2 s t m n. FINITE s /\ FINITE t ==>
                   (subrank r1 s t m = subrank r2 s t n <=> r1 = r2 /\ m = n)
Proof
    rw [subrank_def]
QED

(* ----------------------------------------------------------------------
   RP_NEWS for allocating a list of fresh names at a rank but excluding an
   extra finite set of possibly conflicting symbols
   ---------------------------------------------------------------------- *)

Definition RP_NEWS :
    RP_NEWS r n s t = GENLIST (subrank r s t) n
End

Theorem RP_NEWS_NIL[simp] :
    RP_NEWS r 0 s t = []
Proof
    rw [RP_NEWS]
QED

Theorem RP_NEWS_def :
    !r n s t. FINITE s /\ FINITE t ==>
              ALL_DISTINCT (RP_NEWS r n s t) /\
              DISJOINT (set (RP_NEWS r n s t)) s /\
              DISJOINT (set (RP_NEWS r n s t)) t /\
              LENGTH (RP_NEWS r n s t) = n
Proof
    rw [RP_NEWS]
 >- rw [ALL_DISTINCT_GENLIST]
 (* 2 subgoals, same tactics *)
 >> rw [DISJOINT_ALT, MEM_GENLIST]
 >> rw [subrank_thm]
QED

Theorem RP_NEWS_prefix :
    !r m n s t. m <= n ==> RP_NEWS r m s t <<= RP_NEWS r n s t
Proof
    rw [RP_NEWS]
 >> MATCH_MP_TAC IS_PREFIX_GENLIST >> art []
QED

Theorem RP_NEWS_disjoint :
    !r1 r2 m n s t. FINITE s /\ FINITE t /\ r1 <> r2 ==>
                    DISJOINT (set (RP_NEWS r1 m s t)) (set (RP_NEWS r2 n s t))
Proof
    rw [RP_NEWS, DISJOINT_ALT, MEM_GENLIST]
 >> CCONTR_TAC
 >> gs [subrank_11]
QED

Theorem RP_NEWS_set :
    !r n s t. set (RP_NEWS r n s t) = {v | ?j. v = subrank r s t j /\ j < n}
Proof
    rw [RP_NEWS, Once EXTENSION, MEM_GENLIST]
 >> METIS_TAC []
QED

Theorem RP_NEWS_SUBSET :
    !r n s t. FINITE s /\ FINITE t ==> set (RP_NEWS r n s t) SUBSET rank s r
Proof
    rw [RP_NEWS_set, SUBSET_DEF]
 >> rw [subrank_thm]
QED

Theorem RANKS_DISJOINT_RP_NEWS :
    !r1 r2 n s t. FINITE s /\ FINITE t /\ r1 <= r2 ==>
                  DISJOINT (RANKS r1 s) (set (RP_NEWS r2 n s t))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC DISJOINT_SUBSET
 >> Q.EXISTS_TAC ‘RANK r2 s’
 >> rw [RANKS_RANK_DISJOINT, RP_NEWS_SUBSET]
QED

Theorem RANKS_DISJOINT_RP_NEWS' :
    !r n s t. FINITE s /\ FINITE t ==>
              DISJOINT (RANKS r s) (set (RP_NEWS r n s t))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC RANKS_DISJOINT_RP_NEWS >> rw []
QED

(* ----------------------------------------------------------------------
    RNEWS = RP_NEWS ignoring t
   ---------------------------------------------------------------------- *)

Overload RNEWS = “\r n s. RP_NEWS r n s {}”

Theorem RNEWS :
    !r n s. RNEWS r n s = GENLIST (\i. FRESH s (npair r i)) n
Proof
    rw [RP_NEWS]
 >> Suff ‘subrank r s {} = \i. FRESH s (r *, i)’ >- rw []
 >> rw [FUN_EQ_THM, subrank_def]
QED

(* |- !r n s.
        FINITE s ==>
        ALL_DISTINCT (RNEWS r n s) /\ DISJOINT (set (RNEWS r n s)) s /\
        LENGTH (RNEWS r n s) = n
 *)
Theorem RNEWS_def =
        RP_NEWS_def |> Q.SPECL [‘r’, ‘n’, ‘s’, ‘{}’] |> SRULE []
                    |> Q.GENL [‘r’, ‘n’, ‘s’]

(* |- !r m n s. m <= n ==> RNEWS r m s <<= RNEWS r n s *)
Theorem RNEWS_prefix = 
        RP_NEWS_prefix |> Q.SPECL [‘r’, ‘m’, ‘n’, ‘s’, ‘{}’]
                       |> Q.GENL [‘r’, ‘m’, ‘n’, ‘s’]

(* |- !r1 r2 n s.
        FINITE s /\ r1 <= r2 ==> DISJOINT (RANKS r1 s) (set (RNEWS r2 n s))
 *)
Theorem RANKS_DISJOINT =
        RANKS_DISJOINT_RP_NEWS |> Q.SPECL [‘r1’, ‘r2’, ‘n’, ‘s’, ‘{}’]
                               |> SRULE [] (* eliminate ‘FINITE {}’ *)
                               |> Q.GENL [‘r1’, ‘r2’, ‘n’, ‘s’]

Theorem RANKS_DISJOINT' :
    !r n s. FINITE s ==> DISJOINT (RANKS r s) (set (RNEWS r n s))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC RANKS_DISJOINT >> rw []
QED

Theorem RANKS_SUBSET :
    !r1 r2 n s. FINITE s /\ r1 < r2 ==> set (RNEWS r1 n s) SUBSET RANKS r2 s
Proof
    rw [SUBSET_DEF, RP_NEWS_set, ranks_def]
 >> Q.EXISTS_TAC ‘RANK r1 s’
 >> reverse CONJ_TAC
 >- (Q.EXISTS_TAC ‘r1’ >> art [])
 >> rw [subrank_thm]
QED

(* ----------------------------------------------------------------------
    The old NEWS constant for allocating a list of fresh names
   ---------------------------------------------------------------------- *)

(* ‘NEWS n s’ generates n fresh names from the excluded set ‘s’ *)
Overload NEWS = “RNEWS 0”

Theorem NEWS_1[simp] :
    NEWS 1 s = [NEW s]
Proof
    rw [RNEWS] (* npair00 is used implicitly *)
QED

(* This is the old equivalent definition of FRESH_list_def:

   |- !n s.
        FINITE s ==>
        ALL_DISTINCT (NEWS n s) /\ DISJOINT (set (NEWS n s)) s /\
        LENGTH (NEWS n s) = n
 *)
Theorem NEWS_def = Q.SPEC ‘0’ RNEWS_def

(* |- !m n s. m <= n ==> NEWS m s <<= NEWS n s *)
Theorem NEWS_prefix = Q.SPEC ‘0’ RNEWS_prefix

val _ = export_theory ();
val _ = html_theory "basic_swap";
