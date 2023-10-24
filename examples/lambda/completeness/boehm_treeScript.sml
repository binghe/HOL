(*---------------------------------------------------------------------------*
 * boehm_treeScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])         *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory llistTheory
     ltreeTheory pathTheory posetTheory hurdUtils;

open binderLib termTheory appFOLDLTheory chap2Theory chap3Theory
     head_reductionTheory standardisationTheory solvableTheory pure_dBTheory;

val _ = new_theory "boehm_tree";

val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)

(* A dB-term M is hnf if its corresponding Lambda term is hnf *)
Overload dhnf = “hnf o toTerm”

Theorem dhnf_fromTerm[simp] :
    !M. dhnf (fromTerm M) <=> hnf M
Proof
    rw [o_DEF]
QED

Overload dsolvable = “solvable o toTerm”

(* Definition 8.3.20 [1, p.177]

   A term may have several hnf's, e.g. if any of its hnf can still do beta
   reductions, after such reductions the term is still an hnf by definition.
   The (unique) terminating term of head reduction path is called "principle"
   hnf, which is used for defining Boehm trees.
 *)
Definition phnf_def :
    phnf = last o head_reduction_path
End

Overload dphnf = “fromTerm o phnf o toTerm”

Theorem dsolvable_phnf :
    !M. dsolvable (M :pdb) ==> dhnf (dphnf M)
Proof
    rw [o_DEF, solvable_iff_has_hnf, phnf_def, head_reduction_path_def, corollary11_4_8]
QED

(* not used *)
Definition drator_def :
    drator (dAPP s t) = s
End
Overload rator = “drator”

(* not used *)
Definition drand_def :
    drand (dAPP s t) = t
End
Overload rand = “drand”

(* NOTE: this "body" bfunction is unsound for “:term” type *)
Definition dbody_def :
    dbody (dABS s) = s
End
Overload body = “dbody”

(* Translating from LAMl to dABSi.

   Some samples for guessing out the theorem statements:

> SIMP_CONV arith_ss [dLAM_def, lift_def, sub_def, lift_sub]
                     “dLAM v1 (dLAM v0 t)”;
# val it =
   |- dLAM v1 (dLAM v0 t) =
      dABS (dABS ([dV 1/v1 + 2] ([dV 0/v0 + 2] (lift (lift t 0) 1)))): thm

> SIMP_CONV arith_ss [dLAM_def, lift_def, sub_def, lift_sub]
                     “dLAM v2 (dLAM v1 (dLAM v0 t))”;
# val it =
   |- dLAM v2 (dLAM v1 (dLAM v0 t)) =
      dABS
        (dABS
           (dABS ([dV 2/v2 + 3]
                    ([dV 1/v1 + 3]
                       ([dV 0/v0 + 3]
                          (lift (lift (lift t 0) 1) 2)))))): thm
 *)
Theorem LAMl_to_dABSi :
    !vs. ALL_DISTINCT (vs :num list) ==>
         let n = LENGTH vs;
             body = FOLDL lift t (GENLIST I n);
             st = ZIP (GENLIST dV n, MAP (\i. i + n) (REVERSE vs))
         in LAMl vs t = dABSi n (body ISUB st)
Proof
    Induct_on ‘vs’ >- rw [isub_def]
 >> rw [isub_def, GSYM SNOC_APPEND, MAP_SNOC, FUNPOW_SUC, GENLIST, FOLDL_SNOC, dLAM_def]
 >> fs []
 >> qabbrev_tac ‘n = LENGTH vs’
 >> rw [lift_dABSi]
 >> Q.PAT_X_ASSUM ‘LAMl vs t = _’ K_TAC
 >> qabbrev_tac ‘N = FOLDL lift t (GENLIST I n)’
 >> qabbrev_tac ‘Ms = GENLIST dV n’
 >> qabbrev_tac ‘Vs = MAP (\i. i + n) (REVERSE vs)’
 >> Know ‘lift (N ISUB ZIP (Ms,Vs)) n =
          (lift N n) ISUB (ZIP (MAP (\e. lift e n) Ms,MAP SUC Vs))’
 >- (MATCH_MP_TAC lift_isub \\
     rw [Abbr ‘Ms’, Abbr ‘Vs’, EVERY_MEM, MEM_MAP] >> rw [])
 >> Rewr'
 >> ‘MAP SUC Vs = MAP (\i. i + SUC n) (REVERSE vs)’
       by (rw [LIST_EQ_REWRITE, EL_MAP, Abbr ‘Vs’]) >> POP_ORW
 >> qunabbrev_tac ‘Vs’ (* now useless *)
 >> rw [sub_def, GSYM ADD1]
 >> ‘MAP (\e. lift e n) Ms = Ms’
       by (rw [LIST_EQ_REWRITE, EL_MAP, Abbr ‘Ms’]) >> POP_ORW
 >> qabbrev_tac ‘Ns = MAP (\i. i + SUC n) (REVERSE vs)’
 >> qabbrev_tac ‘N' = lift N n’
 >> Suff ‘N' ISUB ZIP (SNOC (dV n) Ms,SNOC (h + SUC n) Ns) =
          [dV n/h + SUC n] (N' ISUB ZIP (Ms,Ns))’ >- rw []
 >> MATCH_MP_TAC isub_SNOC
 >> rw [Abbr ‘Ms’, Abbr ‘Ns’, MEM_EL, EL_MAP]
 >> rename1 ‘~(i < n)’
 >> ‘LENGTH (REVERSE vs) = n’ by rw [Abbr ‘n’]
 >> CCONTR_TAC >> gs [EL_MAP]
 >> ‘h = EL i (REVERSE vs)’ by rw []
 >> Suff ‘MEM h (REVERSE vs)’ >- rw [MEM_REVERSE]
 >> Q.PAT_X_ASSUM ‘~MEM h vs’ K_TAC
 >> ‘LENGTH (REVERSE vs) = n’ by rw [Abbr ‘n’]
 >> REWRITE_TAC [MEM_EL]
 >> Q.EXISTS_TAC ‘i’ >> art []
QED

(* |- !t vs.
        ALL_DISTINCT vs ==>
        LAMl vs t =
        dABSi (LENGTH vs)
          (FOLDL lift t (GENLIST I (LENGTH vs)) ISUB
           ZIP (GENLIST dV (LENGTH vs),MAP (\i. i + LENGTH vs) (REVERSE vs)))
 *)
Theorem LAMl_to_dABSi_applied = GEN_ALL (SIMP_RULE std_ss [LET_DEF] LAMl_to_dABSi)

(* dB version of hnf_cases (only the ==> direction) *)
Theorem dhnf_cases :
    !M. dhnf M ==> ?n y Ms. M = dABSi n (dV y @* Ms)
Proof
    RW_TAC std_ss [hnf_cases]
 >> qabbrev_tac ‘n = LENGTH vs’
 >> Q.EXISTS_TAC ‘n’
 >> Know ‘fromTerm (toTerm M) = fromTerm (LAMl vs (VAR y @* args))’
 >- (art [fromTerm_11])
 >> Q.PAT_X_ASSUM ‘toTerm M = LAMl vs (VAR y @* args)’ K_TAC
 >> rw [fromTerm_LAMl, fromTerm_appstar]
 >> qabbrev_tac ‘vs' = MAP s2n vs’
 >> qabbrev_tac ‘Ms = MAP fromTerm args’
 >> qabbrev_tac ‘y' = s2n y’
 >> Know ‘LAMl vs' (dV y' @* Ms) =
          dABSi (LENGTH vs')
            (FOLDL lift (dV y' @* Ms) (GENLIST I (LENGTH vs')) ISUB
             ZIP (GENLIST dV (LENGTH vs'),MAP (\i. i + LENGTH vs') (REVERSE vs')))’
 >- (MATCH_MP_TAC LAMl_to_dABSi_applied \\
     qunabbrev_tac ‘vs'’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [])
 >> ‘LENGTH vs' = n’ by rw [Abbr ‘vs'’] >> POP_ORW
 >> Rewr'
 >> simp [FOLDL_lift_appstar, isub_appstar]
 (* applying nipkow_lift_lemma1 and lift_dV_0 *)
 >> Know ‘FOLDL lift (dV y') (GENLIST I n) = dV (y' + n)’
 >- (KILL_TAC \\
     Induct_on ‘n’ >> rw [GENLIST, FOLDL_SNOC])
 >> Rewr'
 >> qabbrev_tac ‘Ms' = MAP (\e. FOLDL lift e (GENLIST I n)) Ms’
 >> Cases_on ‘MEM y vs’
 >| [ (* goal 1 (of 2) *)
     ‘MEM y' vs'’ by (rw [Abbr ‘y'’, Abbr ‘vs'’, MEM_MAP]) \\
     ‘MEM y' (REVERSE vs')’ by PROVE_TAC [MEM_REVERSE] \\
     ‘?j. j < LENGTH (REVERSE vs') /\ y' = EL j (REVERSE vs')’ by METIS_TAC [MEM_EL] \\
     ‘LENGTH (REVERSE vs') = n’ by rw [Abbr ‘vs'’, Abbr ‘n’] \\
      qabbrev_tac ‘Ns = MAP (\i. i + n) (REVERSE vs')’ \\
     ‘LENGTH Ns = n’ by rw [Abbr ‘Ns’] \\
      Know ‘ALL_DISTINCT Ns’
      >- (qunabbrev_tac ‘Ns’ \\
          MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [] \\
          qunabbrev_tac ‘vs'’ \\
          MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw []) >> DISCH_TAC \\
      Know ‘dV (y' + n) ISUB ZIP (GENLIST dV n,Ns) = EL j (GENLIST dV n)’
      >- (MATCH_MP_TAC isub_dV_once >> simp [] \\
          CONJ_TAC >- (rw [Abbr ‘Ns’, EL_MAP]) \\
          Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         ‘n <= EL i Ns’ by rw [Abbr ‘Ns’, EL_MAP] \\
          Suff ‘FVS (ZIP (GENLIST dV n,Ns)) = count n’ >- rw [] \\
          Q.PAT_X_ASSUM ‘LENGTH Ns = n’ MP_TAC \\
          KILL_TAC >> Q.ID_SPEC_TAC ‘Ns’ \\
          Induct_on ‘n’ >> rw [dFVS_def] \\
         ‘Ns <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0] \\
         ‘LENGTH (FRONT Ns) = n’ by rw [LENGTH_FRONT] \\
         ‘Ns = SNOC (LAST Ns) (FRONT Ns)’ by rw [APPEND_FRONT_LAST, SNOC_APPEND] \\
          POP_ORW \\
          Q.PAT_X_ASSUM ‘!Ns. LENGTH Ns = n ==> P’ (MP_TAC o (Q.SPEC ‘FRONT Ns’)) \\              
          rw [GENLIST, COUNT_SUC, dFVS_SNOC, ZIP_SNOC, dFV_def] \\
          SET_TAC []) >> Rewr' \\
      simp [EL_GENLIST] \\
      qexistsl_tac [‘j’, ‘MAP (\t. t ISUB ZIP (GENLIST dV n,Ns)) Ms'’] >> rw [],
      (* goal 2 (of 2) *)
      cheat ]
QED

(* |- ?f f' f''. !M. dhnf M ==> M = dABS (f M) (dV (f' M) @* f'' M) *)
val dhnf_cases' = dhnf_cases
               |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM];

(* |- !M. dhnf M ==> M = dABSi (dABSn' M) (dV (dVn' M) @* dAPPl' M) *)
val dhnf_decompose =
    new_specification ("dhnf_decompose", ["dABSn'", "dVn'", "dAPPl'"], dhnf_cases');

(* Explicit definitions of hnf components (easier to work with) by Michael Norrish:

   1. The number of leading dABS (can be zero):
 *)
Definition dABSn_def :
   (dABSn (dV n)       = 0) /\
   (dABSn (dAPP t1 t2) = 0) /\
   (dABSn (dABS t)     = 1 + dABSn t)
End

(* 2. The head variable of hnf (always exists) *)
Definition dVn_def :
   (dVn (dV n)       = n) /\
   (dVn (dABS t)     = dVn t) /\
   (dVn (dAPP t1 t2) = dVn t1)
End

(* 2. The list of terms after appstar (may be empty) *)
Definition dAPPl_def :
   (dAPPl (dV n)       = []) /\
   (dAPPl (dABS t)     = dAPPl t) /\
   (dAPPl (dAPP t1 t2) = SNOC t2 (dAPPl t1))
End

(* The "main" part of a hnf *)
Definition dhnf_main_def :
    dhnf_main M = dABSi (dABSn M) (dV (dVn M))
End

val _ = export_rewrites ["dABSn_def", "dVn_def", "dAPPl_def"];

Theorem dABSn_dABSi[simp] :
    dABSn (dABSi n t) = n + dABSn t
Proof
    Induct_on ‘n’ >> rw [FUNPOW_SUC]
QED

Theorem dABSn_dV_appstar[simp] :
    dABSn (dV y @* Ns) = 0
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT
 >> rw [appstar_SNOC]
QED

Theorem dVn_dABSi[simp] :
    dVn (dABSi n t) = dVn t
Proof
    Induct_on ‘n’ >> rw [FUNPOW_SUC]
QED

Theorem dVn_appstar[simp] :
    dVn (M @* Ns) = dVn M
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT >> rw []
QED

Theorem dAPPl_dABSi[simp] :
    dAPPl (dABSi n t) = dAPPl t
Proof
    Induct_on ‘n’ >> rw [FUNPOW_SUC]
QED

Theorem dAPPl_dV_appstar[simp] :
    dAPPl (dV y @* Ns) = Ns
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT >> rw [dappstar_APPEND]
QED

Theorem dhnf_thm :
    !M. dhnf M ==> M = dABSi (dABSn M) (dV (dVn M) @* dAPPl M)
Proof
    rpt STRIP_TAC
 >> ‘?n y Ms. M = dABSi n (dV y @* Ms)’ by METIS_TAC [dhnf_cases]
 >> rw []
QED

(* The needed unfolding function for ltree_unfold for Boehm Tree *)
Definition BT_generator_def :
    BT_generator (M :pdb) = if dsolvable M then
                               let M' = dphnf M in
                                 (SOME (dhnf_main M'), fromList (dAPPl M'))
                            else
                               (NONE, LNIL)
End

(* The Boehm tree of M, all in dB terms. *)
Definition dBT_def :
    dBT (M :pdb) = ltree_unfold BT_generator M
End

(* The Boehm tree of M, translated back to normal Lambda terms *)
Definition BT_def :
    BT = ltree_map (OPTION_MAP toTerm) o dBT o fromTerm
End

Theorem unsolvable_BT :
    !M. unsolvable M ==> BT M = Branch NONE LNIL
Proof
    rw [BT_def, dBT_def, BT_generator_def, ltree_unfold, ltree_map]
QED

Type boehm_tree[pp] = “:term option ltree”

Overload bot = “Branch NONE (LNIL :term option ltree llist)”
val _ = Unicode.unicode_version {u = UTF8.chr 0x22A5, tmnm = "bot"};

(* All unsolvable terms have the same Boehm tree. *)
Theorem unsolvable_BT_EQ :
    !M N. unsolvable M /\ unsolvable N ==> BT M = BT N
Proof
    rw [unsolvable_BT]
QED

val _ = export_theory ();
val _ = html_theory "boehm_tree";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
