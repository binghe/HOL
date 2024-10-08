(******************************************************************************)
(* Formalized Runtime Verification (RV) in HOL4                               *)
(*                                                                            *)
(* Copyright 2020-2022 Chun Tian (binghe) <binghe.lisp@gmail.com>             *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

(* standard libraries & utilities *)
open pairTheory optionTheory listTheory pred_setTheory rich_listTheory
     arithmeticTheory hurdUtils combinTheory;

(* local theories *)
open prop_logicTheory xprop_logicTheory full_ltlTheory translationsLib
     symbolic_kripke_structureTheory symbolic_semi_automatonTheory
     automaton_formulaTheory ltl_to_automaton_formulaTheory
     omega_automaton_translationsTheory temporal_deep_mixedTheory;

(* Tuerk's translations between different LTL syntax (unused)
open ltl_translationsTheory;
 *)

open Sanity;

val _ = hide "S";
val _ = hide "I";
val _ = hide "K";

val _ = new_theory "runtime_verification";

(* NuSMV-compatible names for LTL past operators *)
Overload LTL_PREV  = “LTL_PSNEXT”
Overload LTL_SINCE = “LTL_PSUNTIL”

(******************************************************************************)
(* LTL semantics over finite trace (LTL3)                                     *)
(******************************************************************************)

Type LTL3 = “:bool option”

Overload LTL3_T = “SOME T”     (* conclusive true *)
Overload LTL3_F = “SOME F”     (* conclusive false *)
Overload LTL3_U = “NONE :LTL3” (* inconclusive/unknown *)

(* ABRV-LTL *)
Type ABRV_LTL[pp] = “:LTL3 option”

Overload true    = “SOME LTL3_T”
Overload false   = “SOME LTL3_F”
Overload unknown = “SOME LTL3_U”
Overload error   = “NONE :ABRV_LTL”

Theorem THE_LTL3 :
   (THE LTL3_T = T) /\ (THE LTL3_F = F)
Proof
   RW_TAC std_ss []
QED

Theorem LTL3_nchotomy :
    !a. (a = LTL3_T) \/ (a = LTL3_F) \/ (a = LTL3_U)
Proof
    GEN_TAC
 >> Suff `a <> LTL3_U ==> (a = LTL3_T) \/ (a = LTL3_F)` >- PROVE_TAC []
 >> DISCH_TAC
 >> ASSUME_TAC (Q.SPEC `a` (INST_TYPE [``:'a`` |-> ``:bool``] option_nchotomy))
 >> `?x. a = SOME x` by PROVE_TAC []
 >> Cases_on `x` >> PROVE_TAC []
QED

Theorem LTL3_distinct :
    LTL3_T <> LTL3_F /\ LTL3_T <> LTL3_U /\ LTL3_F <> LTL3_U
Proof
    rpt CONJ_TAC
 >- METIS_TAC [SOME_11]
 >> METIS_TAC [NOT_SOME_NONE]
QED

Theorem LTL3_NOT_U :
    !x. x <> LTL3_U <=> (x = LTL3_T) \/ (x = LTL3_F)
Proof
    METIS_TAC [LTL3_nchotomy, LTL3_distinct]
QED

(* The concatenation of finite and infinite traces is another infinite trace

   PSLPath.CAL is similar, but the result is of type ``:'a path`` that
   cannot be used by LTL_SEM_TIME. Also cf. FinitePSLPath.CONCAT .
 *)
Definition concat_def :
   concat (u :'a list) (v :num -> 'a) =
     \i. if i < LENGTH u then EL i u else (v (i - LENGTH u))
End

val _ = overload_on ("++", ``concat``);

Theorem concat_assoc :
    !(u :'a list) (v :'a list) (w :num -> 'a). (u ++ v) ++ w = u ++ (v ++ w)
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [concat_def]
 >> ONCE_REWRITE_TAC [FUN_EQ_THM]
 >> GEN_TAC >> BETA_TAC
 >> REWRITE_TAC [LENGTH_APPEND]
 >> Cases_on `x < LENGTH u`
 >- (`x < LENGTH u + LENGTH v` by RW_TAC arith_ss [] \\
     RW_TAC arith_ss [EL_APPEND_EQN])
 >> Cases_on `x < LENGTH u + LENGTH v`
 >- RW_TAC arith_ss [EL_APPEND_EQN]
 >> RW_TAC arith_ss []
QED

(* access of the finite part of a concatenation *)
Theorem concat_finite :
    !i u w. i < LENGTH u ==> (u ++ w) i = EL i u
Proof
    RW_TAC std_ss [concat_def]
QED

(* LTL3 semantics [1] *)
Definition LTL3_SEM_TIME_def :
    LTL3_SEM_TIME t (u :'a set list) f =
             if (!w.  LTL_SEM_TIME t (concat u w) f) then LTL3_T
        else if (!w. ~LTL_SEM_TIME t (concat u w) f) then LTL3_F
        else LTL3_U
End

Definition LTL3_SEM_def :
    LTL3_SEM u f = LTL3_SEM_TIME 0 u f
End

Theorem LTL3_SEM_TIME_T :
    !t u f. (LTL3_SEM_TIME t u f = LTL3_T) <=> !v. LTL_SEM_TIME t (u ++ v) f
Proof
    RW_TAC std_ss [LTL3_SEM_TIME_def]
QED

Theorem LTL3_SEM_TIME_F :
    !t u f. (LTL3_SEM_TIME t u f = LTL3_F) <=> !v. ~LTL_SEM_TIME t (u ++ v) f
Proof
    RW_TAC std_ss [LTL3_SEM_TIME_def]
QED

(* full definition of LTL3_SEM *)
Theorem LTL3_SEM_DEF :
    !u f. LTL3_SEM u f = if (!v.  LTL_SEM (u ++ v) f) then LTL3_T
                    else if (!v. ~LTL_SEM (u ++ v) f) then LTL3_F
                    else LTL3_U
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [LTL3_SEM_def, LTL3_SEM_TIME_def, GSYM LTL_SEM_def]
QED

(* |- !u f. (LTL3_SEM u f = LTL3_T) <=> !v. LTL_SEM (u ++ v) f *)
Theorem LTL3_SEM_T =
    REWRITE_RULE [GSYM LTL3_SEM_def, GSYM LTL_SEM_def]
                 (Q.SPEC `0` LTL3_SEM_TIME_T)

(* |- !u f. (LTL3_SEM u f = LTL3_F) <=> !v. ~LTL_SEM (u ++ v) f *)
Theorem LTL3_SEM_F =
    REWRITE_RULE [GSYM LTL3_SEM_def, GSYM LTL_SEM_def]
                 (Q.SPEC `0` LTL3_SEM_TIME_F)

Theorem LTL3_SEM_TIME_MONO_T :
    !t u f. (LTL3_SEM_TIME t u f = LTL3_T) ==>
            !v. (LTL3_SEM_TIME t (u ++ v) f = LTL3_T)
Proof
    RW_TAC std_ss [LTL3_SEM_TIME_T] >> art [concat_assoc]
QED

Theorem LTL3_SEM_TIME_MONO_F :
    !t u f. (LTL3_SEM_TIME t u f = LTL3_F) ==>
            !v. (LTL3_SEM_TIME t (u ++ v) f = LTL3_F)
Proof
    RW_TAC std_ss [LTL3_SEM_TIME_F] >> art [concat_assoc]
QED

(* main theorem on the monotonicity of LTL3 *)
Theorem LTL3_SEM_TIME_MONO :
    !t u f. (LTL3_SEM_TIME t u f <> LTL3_U) ==>
        !v. (LTL3_SEM_TIME t (u ++ v) f = LTL3_SEM_TIME t u f)
Proof
    RW_TAC std_ss [LTL3_NOT_U]
 >- PROVE_TAC [LTL3_SEM_TIME_MONO_T]
 >> PROVE_TAC [LTL3_SEM_TIME_MONO_F]
QED

(* |- !u f. LTL3_SEM u f ++ LTL3_U ==> !v. LTL3_SEM (u ++ v) f = LTL3_SEM u f *)
Theorem LTL3_SEM_MONO =
    REWRITE_RULE [GSYM LTL3_SEM_def] (Q.SPEC `0` LTL3_SEM_TIME_MONO)

(* Standard semantics of ptLTL [2] *)
Definition PTLTL_SEM_def :
   (PTLTL_SEM u (LTL_PROP p)        = (P_SEM (LAST u) p)) /\
   (PTLTL_SEM u (LTL_NOT f)         = ~PTLTL_SEM u f) /\
   (PTLTL_SEM u (LTL_AND (f1,f2))   = (PTLTL_SEM u f1 /\ PTLTL_SEM u f2)) /\
   (PTLTL_SEM u (LTL_PREV f)        =
     if (1 < LENGTH u) then PTLTL_SEM (BUTLASTN 1 u) f
                       else PTLTL_SEM u f) /\
   (PTLTL_SEM u (LTL_SINCE (f1,f2)) =
     ?k. k < LENGTH u /\ PTLTL_SEM (BUTLASTN k u) f2 /\
         !j. j < k ==> PTLTL_SEM (BUTLASTN j u) f1)
End

(* Alternative semantics of ptLTL [2], the only difference is at LTL_PREV *)
Definition PTLTL_SEM_ALT_def :
   (PTLTL_SEM_ALT u (LTL_PROP p)        = (P_SEM (LAST u) p)) /\
   (PTLTL_SEM_ALT u (LTL_NOT f)         = ~PTLTL_SEM_ALT u f) /\
   (PTLTL_SEM_ALT u (LTL_AND (f1,f2))   = (PTLTL_SEM_ALT u f1 /\
                                           PTLTL_SEM_ALT u f2)) /\
   (PTLTL_SEM_ALT u (LTL_PREV f)        =
     (1 < LENGTH u /\ PTLTL_SEM_ALT (BUTLASTN 1 u) f)) /\
   (PTLTL_SEM_ALT u (LTL_SINCE (f1,f2)) =
     ?k. k < LENGTH u /\ PTLTL_SEM_ALT (BUTLASTN k u) f2 /\
         (!j. j < k  ==>  PTLTL_SEM_ALT (BUTLASTN j u) f1))
End

(* key result: PTLTL doesn't access the future part of the trace *)
Theorem PTLTL_SEM_THM :
    !u w w' i. i < LENGTH u ==>
           !f. IS_PAST_LTL f ==>
              (LTL_SEM_TIME i (u ++ w) f = LTL_SEM_TIME i (u ++ w') f)
Proof
    NTAC 3 GEN_TAC
 >> completeInduct_on `i` >> DISCH_TAC
 >> HO_MATCH_MP_TAC ltl_induct
 >> RW_TAC std_ss [LTL_SEM_TIME_def, IS_PAST_LTL_def, concat_finite, PRE_SUB1]
 >> Cases_on `i` >> RW_TAC arith_ss []
 >> EQ_TAC >> rpt STRIP_TAC (* 2 subgoals, shared tactics *)
 >> ( Q.EXISTS_TAC `k` \\
      CONJ_TAC >- art [] \\
     `k < LENGTH u` by PROVE_TAC [LESS_EQ_LESS_TRANS] \\
      CONJ_TAC >- (`(k = SUC n) \/ k < SUC n` by RW_TAC arith_ss [] \\
                   METIS_TAC []) \\
      rpt STRIP_TAC \\
     `j < LENGTH u` by PROVE_TAC [LESS_EQ_LESS_TRANS] \\
     `(j = SUC n) \/ j < SUC n` by RW_TAC arith_ss [] \\
      METIS_TAC [] )
QED

Definition LTL3_IS_CONCL_def :
    LTL3_IS_CONCL x = ((x = LTL3_T) \/ (x = LTL3_F))
End

(* LTL3 semantic of ptLTL is always conclusive *)
Theorem PTLTL_SEM_LTL3_CONCL :
    !f u i. i < LENGTH u /\ IS_PAST_LTL f ==> LTL3_IS_CONCL (LTL3_SEM_TIME i u f)
Proof
    RW_TAC std_ss [LTL3_IS_CONCL_def, LTL3_SEM_TIME_def]
 >> METIS_TAC [PTLTL_SEM_THM]
QED

Theorem PTLTL_SEM_LTL3_AND :
    !i u f1 f2. i < LENGTH u /\ IS_PAST_LTL f1 /\ IS_PAST_LTL f2 ==>
               (THE (LTL3_SEM_TIME i u (LTL_AND (f1,f2))) <=>
                THE (LTL3_SEM_TIME i u f1) /\ THE (LTL3_SEM_TIME i u f2))
Proof
    rpt STRIP_TAC
 >> `LTL3_IS_CONCL (LTL3_SEM_TIME i u f1) /\
     LTL3_IS_CONCL (LTL3_SEM_TIME i u f2)` by PROVE_TAC [PTLTL_SEM_LTL3_CONCL]
 >> fs [LTL3_IS_CONCL_def, LTL3_SEM_TIME_def, LTL_SEM_TIME_def]
 >| [ (* goal 1 (of 4) *)
      `!w. LTL_SEM_TIME i (u ++ w) f1` by METIS_TAC [LTL3_distinct] \\
      `!w. LTL_SEM_TIME i (u ++ w) f2` by METIS_TAC [LTL3_distinct],
      (* goal 2 (of 4) *)
      `!w. LTL_SEM_TIME i (u ++ w) f1` by METIS_TAC [LTL3_distinct] \\
      `!w. ~LTL_SEM_TIME i (u ++ w) f2` by METIS_TAC [LTL3_distinct],
      (* goal 3 (of 4) *)
      `!w. ~LTL_SEM_TIME i (u ++ w) f1` by METIS_TAC [LTL3_distinct] \\
      `!w. LTL_SEM_TIME i (u ++ w) f2` by METIS_TAC [LTL3_distinct],
      (* goal 4 (of 4) *)
      `!w. ~LTL_SEM_TIME i (u ++ w) f1` by METIS_TAC [LTL3_distinct] \\
      `!w. ~LTL_SEM_TIME i (u ++ w) f2` by METIS_TAC [LTL3_distinct] ]
 >> fs []
QED

(* target result: alternative ptLTL semantics expressed in LTL3 semantics *)
Theorem PTLTL_SEM_ALT_LTL3 :
    !f u. IS_PAST_LTL f /\ 0 < LENGTH u ==>
         (PTLTL_SEM_ALT u f = THE (LTL3_SEM_TIME (LENGTH u - 1) u f))
Proof
 (* 0. adjusting the order of quantifiers for induction *)
    Suff `!u. 0 < LENGTH u ==>
              !f. IS_PAST_LTL f ==>
                 (PTLTL_SEM_ALT u f = THE (LTL3_SEM_TIME (LENGTH u - 1) u f))`
 >- METIS_TAC []
 (* 1. outer induction on the length of `u`, only needed by PPEV and SINCE *)
 >> measureInduct_on `LENGTH (u :'a set list)`
 >> DISCH_TAC
 (* 2. preliminary *)
 >> `u <> []` by PROVE_TAC [NOT_NIL_EQ_LENGTH_NOT_0]
 >> `LAST u = EL (LENGTH u - 1) u`
     by RW_TAC arith_ss [LAST_EL, PRE_SUB1]
 >> Know `!w. (u ++ w) (LENGTH u - 1) = EL (LENGTH u - 1) u`
 >- (MATCH_MP_TAC concat_finite >> RW_TAC arith_ss [])
 >> DISCH_TAC
 (* 3. inner induction on LTL *)
 >> HO_MATCH_MP_TAC ltl_induct
 >> RW_TAC std_ss [IS_PAST_LTL_def] (* 5 subgoals left *)
 (* goal 1 (of 5): LTL_PROP *)
 >- (RW_TAC std_ss [PTLTL_SEM_ALT_def, LTL3_SEM_TIME_def, LTL_SEM_TIME_def])
 (* goal 2 (of 5): LTL_NOT *)
 >- (RW_TAC std_ss [PTLTL_SEM_ALT_def, LTL3_SEM_TIME_def, LTL_SEM_TIME_def] \\
     fs [] >> `LENGTH u - 1 < LENGTH u` by RW_TAC arith_ss [] \\
     METIS_TAC [PTLTL_SEM_THM])
 (* goal 3 (of 5): LTL_AND *)
 >- (RW_TAC std_ss [PTLTL_SEM_ALT_def] \\
    `LENGTH u - 1 < LENGTH u` by RW_TAC arith_ss [] \\
     PROVE_TAC [PTLTL_SEM_LTL3_AND])
 (* goal 4 (of 5): LTL_PREV *)
 >- (Q.PAT_X_ASSUM `IS_PAST_LTL f ==> _` K_TAC \\ (* IH2 unused *)
    `(LENGTH u = 1) \/ 1 < LENGTH u` by RW_TAC arith_ss []
     >- (rw [PTLTL_SEM_ALT_def, LTL3_SEM_TIME_def, LTL_SEM_TIME_def]) \\
     rw [PTLTL_SEM_ALT_def] \\
     Q.PAT_X_ASSUM `!y. LENGTH y < LENGTH u ==> _` (* IH1 *)
       (MP_TAC o (Q.SPEC `BUTLASTN 1 u`)) \\
     RW_TAC arith_ss [LENGTH_BUTLASTN] \\
     POP_ASSUM K_TAC \\ (* IH1 leftover removed *)
     Know `LTL3_IS_CONCL (LTL3_SEM_TIME (LENGTH u − 1) u (LTL_PREV f))`
     >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw [IS_PAST_LTL_def]) \\
     Know `LTL3_IS_CONCL (LTL3_SEM_TIME (LENGTH u − 2) (BUTLASTN 1 u) f)`
     >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw [LENGTH_BUTLASTN]) \\
     (* 4 combinations of LTL3_T and LTL3_F *)
     RW_TAC (bool_ss ++ ARITH_ss)
            [LTL3_IS_CONCL_def, LTL3_SEM_TIME_def, LTL_SEM_TIME_def, PRE_SUB1] >|
     (* 2 impossible cases left *)
     [ (* goal 4.1 (of 2) *)
       Q.PAT_X_ASSUM `!w. LTL_SEM_TIME (LENGTH u - 2) _ f`
         (MP_TAC o (REWRITE_RULE [GSYM concat_assoc]) o
          (Q.SPEC `LASTN 1 u ++ (\i. {})`)) \\
       rw [APPEND_BUTLASTN_LASTN],
       (* goal 4.2 (of 2) *)
       Q.PAT_X_ASSUM `!w. ~LTL_SEM_TIME (LENGTH u - 2) _ f`
         (MP_TAC o (REWRITE_RULE [GSYM concat_assoc]) o
          (Q.SPEC `LASTN 1 u ++ (\i. {})`)) \\
       rw [APPEND_BUTLASTN_LASTN] ])
 (* goal 5 (of 5): LTL_SINCE *)
 >> RW_TAC std_ss [PTLTL_SEM_ALT_def]
 >> Know `LTL3_IS_CONCL (LTL3_SEM_TIME (LENGTH u - 1) u (LTL_SINCE (f,f')))`
 >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL \\
     CONJ_TAC >- RW_TAC arith_ss [] \\
     PROVE_TAC [IS_PAST_LTL_def])
 >> RW_TAC std_ss (* or: (bool_ss ++ ARITH_ss) to see things more clearly *)
          [LTL3_SEM_TIME_def, LTL_SEM_TIME_def, LTL3_IS_CONCL_def]
 >| [ (* goal 5.1 (of 2) *)
      POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `\i. {}`)) \\
      Q.EXISTS_TAC `LENGTH u - 1 - k` (* `j + 1` in paper notation *) \\
      CONJ_TAC >- RW_TAC arith_ss [] \\
      CONJ_TAC (* PTLTL_SEM_ALT (BUTLASTN (LENGTH u - 1 - k) u) f' *)
      >- (`(k = LENGTH u - 1) \/ k < LENGTH u - 1` by RW_TAC arith_ss []
          >- (fs [BUTLASTN] \\
              Know `LTL3_IS_CONCL (LTL3_SEM_TIME (LENGTH u - 1) u f')`
              >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw []) \\
              rw [LTL3_SEM_TIME_def, LTL3_IS_CONCL_def] >> fs []) \\
          (* now `k < LENGTH u - 1` *)
          Q.PAT_X_ASSUM `!y. LENGTH y < LENGTH u ==> _`
             (MP_TAC o (Q.SPEC `BUTLASTN (LENGTH u - 1 - k) u`)) \\
          RW_TAC arith_ss [LENGTH_BUTLASTN] \\
          POP_ASSUM (MP_TAC o (Q.SPEC `f'`)) >> RW_TAC std_ss [] \\
          POP_ASSUM K_TAC (* cleanup *) \\
          Know `LTL3_IS_CONCL (LTL3_SEM_TIME k (BUTLASTN (LENGTH u - (k + 1)) u) f')`
          >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw [LENGTH_BUTLASTN]) \\
          rw [LTL3_SEM_TIME_def, LTL3_IS_CONCL_def] \\
          POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [GSYM concat_assoc]) o
                     (Q.SPEC `(LASTN (LENGTH u - (k + 1)) u) ++ (\i. {})`)) \\
          rw [APPEND_BUTLASTN_LASTN]) \\
      (* !j. j < LENGTH u - 1 - k ==> PTLTL_SEM_ALT (BUTLASTN j u) f *)
      rpt STRIP_TAC \\
     `(j = 0) \/ 0 < j` by RW_TAC arith_ss [] (* `i = n \/ i < n` in paper *)
      >- (rw [BUTLASTN] \\
          Know `LTL3_IS_CONCL (LTL3_SEM_TIME (LENGTH u - 1) u f)`
          >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw []) \\
          rw [LTL3_SEM_TIME_def, LTL3_IS_CONCL_def] \\
          Q.PAT_X_ASSUM `!j. k < j /\ j <= LENGTH u - 1 ==> _`
             (MP_TAC o (Q.SPEC `LENGTH (u :'a set list) - 1`)) \\
          RW_TAC arith_ss []) \\
      (* now `0 < j` (`k + 1 < i < n` in paper notation) *)
      Q.PAT_X_ASSUM `!y. LENGTH y < LENGTH u ==> _`
         (MP_TAC o (Q.SPEC `BUTLASTN j u`)) >> rw [LENGTH_BUTLASTN] \\
      POP_ASSUM K_TAC (* cleanup *) \\
      Know `LTL3_IS_CONCL (LTL3_SEM_TIME (LENGTH u − (j + 1)) (BUTLASTN j u) f)`
      >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw [LENGTH_BUTLASTN]) \\
      rw [LTL3_SEM_TIME_def, LTL3_IS_CONCL_def] \\
      Q.PAT_X_ASSUM `!j. k < j /\ j <= LENGTH u - 1 ==> _`
         (MP_TAC o (Q.SPEC `LENGTH (u :'a set list) - (j + 1)`)) \\
      RW_TAC arith_ss [] \\
      POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [GSYM concat_assoc]) o
                 (Q.SPEC `(LASTN j u) ++ (\i. EMPTY)`)) \\
      rw [APPEND_BUTLASTN_LASTN],
      (* goal 5.2 (of 2) *)
      NTAC 2 STRONG_DISJ_TAC >> fs [] \\
      Q.PAT_X_ASSUM `!w k. ~(k <= LENGTH u - 1) \/ _`
         (ASSUME_TAC o (Q.SPEC `\i. {}`)) \\
     `(k = 0) \/ 0 < k` by RW_TAC arith_ss []
      >- (fs [BUTLASTN] \\
          Know `LTL3_IS_CONCL (LTL3_SEM_TIME (LENGTH u − 1) u f')`
          >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw []) \\
          Q.PAT_X_ASSUM `THE (LTL3_SEM_TIME (LENGTH u − 1) u f')` MP_TAC \\
          rw [LTL3_SEM_TIME_def, LTL3_IS_CONCL_def] \\
          Q.PAT_X_ASSUM `!k. ~(k <= LENGTH u - 1) \/ _`
             (MP_TAC o (Q.SPEC `LENGTH (u :'a set list) - 1`)) \\
          RW_TAC arith_ss []) \\
      Know `PTLTL_SEM_ALT (BUTLASTN k u) f' =
            THE (LTL3_SEM_TIME (LENGTH (BUTLASTN k u) − 1) (BUTLASTN k u) f')`
      >- (FIRST_X_ASSUM irule (* IH *) >> rw [LENGTH_BUTLASTN]) \\
      rw [LENGTH_BUTLASTN] \\
      POP_ASSUM MP_TAC \\
      Know `LTL3_IS_CONCL (LTL3_SEM_TIME (LENGTH u − (k + 1)) (BUTLASTN k u) f')`
      >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw [LENGTH_BUTLASTN]) \\
      rw [LTL3_SEM_TIME_def, LTL3_IS_CONCL_def] \\
      POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [GSYM concat_assoc]) o
                 (Q.SPEC `(LASTN k u) ++ (\i. {})`)) \\
      rw [APPEND_BUTLASTN_LASTN] \\
      Q.PAT_X_ASSUM `!k. ~(k <= LENGTH u - 1) \/ _`
         (MP_TAC o (Q.SPEC `LENGTH (u :'a set list) - (k + 1)`)) \\
      RW_TAC arith_ss [] \\
     `(j = LENGTH u - 1) \/ (j < LENGTH u - 1)` by RW_TAC arith_ss []
      >- (Q.EXISTS_TAC `0` >> rw [BUTLASTN] \\
          Know `LTL3_IS_CONCL (LTL3_SEM_TIME (LENGTH u − 1) u f)`
          >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw []) \\
          rw [LTL3_SEM_TIME_def, LTL3_IS_CONCL_def] >> fs []) \\
      (* final part *)
      Q.EXISTS_TAC `LENGTH u - (j + 1)` >> rw [] \\
      Q.PAT_X_ASSUM `!y. LENGTH y < LENGTH u ==> _`
         (MP_TAC o (Q.SPEC `BUTLASTN (LENGTH u - (j + 1)) u`)) \\
      rw [LENGTH_BUTLASTN] \\
      POP_ASSUM K_TAC (* cleanup *) \\
      Know `LTL3_IS_CONCL (LTL3_SEM_TIME j (BUTLASTN (LENGTH u − (j + 1)) u) f)`
      >- (MATCH_MP_TAC PTLTL_SEM_LTL3_CONCL >> rw [LENGTH_BUTLASTN]) \\
      rw [LTL3_SEM_TIME_def, LTL3_IS_CONCL_def] \\
      POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [GSYM concat_assoc]) o
                  (Q.SPEC `(LASTN (LENGTH u - (j + 1)) u) ++ (\i. {})`)) \\
      rw [APPEND_BUTLASTN_LASTN] ]
QED

(* -------------------------------------------------------------------------- *)
(*   LTL3 and PTLTL monitors (abstract version)                               *)
(* -------------------------------------------------------------------------- *)

val _ = set_fixity "extends" (Infix(NONASSOC, 450));

Definition extends_def : (* no partial observability *)
    (i extends u) = ?c. i = concat u c
End

Definition LTL3_output_def :
   (LTL3_output T T = LTL3_U) /\
   (LTL3_output T F = LTL3_T) /\
   (LTL3_output F T = LTL3_F)
End

Definition ABRV_output_def : (* not used, for comparison only *)
   (ABRV_output T T = unknown) /\
   (ABRV_output T F = true) /\
   (ABRV_output F T = false) /\
   (ABRV_output F F = error)
End

(* "belief run" after taking a finite trace u *)
Definition LTL3_belief_run_def :
    LTL3_belief_run l u = {i | i extends u /\ LTL_SEM i l}
End

(* LTL3 monitor (abstract version) *)
Definition LTL3_monitor_def :
    LTL3_monitor l u = LTL3_output (LTL3_belief_run l           u <> EMPTY)
                                   (LTL3_belief_run (LTL_NOT l) u <> EMPTY)
End

(* correctness of LTL3 monitor, an abstract version *)
Theorem LTL3_monitor_thm :
    !l u. LTL3_monitor l u = LTL3_SEM u l
Proof
    RW_TAC std_ss [LTL3_monitor_def, LTL3_SEM_def]
 >> Cases_on `LTL3_belief_run          l  u = {}`
 >> Cases_on `LTL3_belief_run (LTL_NOT l) u = {}`
 >> fs [LTL3_output_def] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      fs [LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_def, LTL_SEM_TIME_def] \\
      Q.ABBREV_TAC `i = u ++ (\n. {})` \\
     `i extends u` by PROVE_TAC [extends_def] \\
      METIS_TAC [],
      (* goal 2 (of 4) *)
      RW_TAC std_ss [Once EQ_SYM_EQ, LTL3_SEM_def, LTL3_SEM_TIME_F] \\
      Q.PAT_X_ASSUM `LTL3_belief_run (LTL_NOT l) u <> {}` K_TAC \\
      fs [LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_def, LTL_SEM_TIME_def] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `u ++ v`)) \\
     `u ++ v extends u` by PROVE_TAC [extends_def] \\
      METIS_TAC [],
      (* goal 3 (of 4) *)
      RW_TAC std_ss [Once EQ_SYM_EQ, LTL3_SEM_def, LTL3_SEM_TIME_T] \\
      Q.PAT_X_ASSUM `LTL3_belief_run l u <> {}` K_TAC \\
      fs [LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_def, LTL_SEM_TIME_def] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `u ++ v`)) \\
     `u ++ v extends u` by PROVE_TAC [extends_def] \\
      METIS_TAC [],
      (* goal 4 (of 4) *)
      RW_TAC std_ss [Once EQ_SYM_EQ, LTL3_SEM_def, LTL3_SEM_TIME_def] >|
      [ (* goal 4.1 (of 2) *)
        Q.PAT_X_ASSUM `LTL3_belief_run l u <> {}` K_TAC \\
        fs [LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
            LTL_SEM_def, LTL_SEM_TIME_def, extends_def] \\
        POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `c`)) \\
        METIS_TAC [],
        (* goal 4.2 (of 2) *)
        Q.PAT_X_ASSUM `~!w. P` K_TAC \\
        Q.PAT_X_ASSUM `LTL3_belief_run (LTL_NOT l) u <> {}` K_TAC \\
        fs [LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
            LTL_SEM_def, LTL_SEM_TIME_def, extends_def] \\
        POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `c`)) \\
        METIS_TAC [] ] ]
QED

Definition GEN_LTL3_belief_run_def :
    GEN_LTL3_belief_run l u t = {i | i extends u /\ LTL_SEM_TIME t i l}
End

(* alternative definition *)
Theorem LTL3_belief_run_alt :
    !l u. LTL3_belief_run l u = GEN_LTL3_belief_run l u 0
Proof
    RW_TAC std_ss [GEN_LTL3_belief_run_def, LTL3_belief_run_def, LTL_SEM_def]
QED

(* LTL3 monitor (abstract version) *)
Definition GEN_LTL3_monitor_def :
    GEN_LTL3_monitor l u t =
        LTL3_output (GEN_LTL3_belief_run l           u t <> EMPTY)
                    (GEN_LTL3_belief_run (LTL_NOT l) u t <> EMPTY)
End

(* alternative definition *)
Theorem LTL3_monitor_alt :
    !l u. LTL3_monitor l u = GEN_LTL3_monitor l u 0
Proof
    RW_TAC std_ss [GEN_LTL3_monitor_def, GSYM LTL3_belief_run_alt,
                   LTL3_monitor_def]
QED

(* correctness of LTL3 monitor, an abstract version *)
Theorem GEN_LTL3_monitor_thm :
    !l u t. GEN_LTL3_monitor l u t = LTL3_SEM_TIME t u l
Proof
    RW_TAC std_ss [GEN_LTL3_monitor_def]
 >> Cases_on `GEN_LTL3_belief_run          l  u t = {}`
 >> Cases_on `GEN_LTL3_belief_run (LTL_NOT l) u t = {}`
 >> fs [LTL3_output_def] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      fs [GEN_LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_TIME_def] \\
      Q.ABBREV_TAC `i = u ++ (\n. {})` \\
     `i extends u` by PROVE_TAC [extends_def] \\
      METIS_TAC [],
      (* goal 2 (of 4) *)
      RW_TAC std_ss [Once EQ_SYM_EQ, LTL3_SEM_TIME_F] \\
      Q.PAT_X_ASSUM `GEN_LTL3_belief_run (LTL_NOT l) u t <> {}` K_TAC \\
      fs [GEN_LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_TIME_def] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `u ++ v`)) \\
     `u ++ v extends u` by PROVE_TAC [extends_def] \\
      METIS_TAC [],
      (* goal 3 (of 4) *)
      RW_TAC std_ss [Once EQ_SYM_EQ, LTL3_SEM_TIME_T] \\
      Q.PAT_X_ASSUM `GEN_LTL3_belief_run l u t <> {}` K_TAC \\
      fs [GEN_LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_TIME_def] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `u ++ v`)) \\
     `u ++ v extends u` by PROVE_TAC [extends_def] \\
      METIS_TAC [],
      (* goal 4 (of 4) *)
      RW_TAC std_ss [Once EQ_SYM_EQ, LTL3_SEM_TIME_def] >|
      [ (* goal 4.1 (of 2) *)
        Q.PAT_X_ASSUM `GEN_LTL3_belief_run l u t <> {}` K_TAC \\
        fs [GEN_LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
            LTL_SEM_TIME_def, extends_def] \\
        POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `c`)) \\
        METIS_TAC [],
        (* goal 4.2 (of 2) *)
        Q.PAT_X_ASSUM `~!w. P` K_TAC \\
        Q.PAT_X_ASSUM `GEN_LTL3_belief_run (LTL_NOT l) u t <> {}` K_TAC \\
        fs [GEN_LTL3_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
            LTL_SEM_TIME_def, extends_def] \\
        POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `c`)) \\
        METIS_TAC [] ] ]
QED

(* PTLTL monitor *)
Theorem PTLTL_monitor_thm :
    !f u. IS_PAST_LTL f /\ 0 < LENGTH u ==>
         (PTLTL_SEM_ALT u f = THE (GEN_LTL3_monitor f u (LENGTH u - 1)))
Proof
    RW_TAC std_ss [PTLTL_SEM_ALT_LTL3, GEN_LTL3_monitor_thm]
QED

(* -------------------------------------------------------------------------- *)
(*   ABRV monitor (abstract version)                                          *)
(* -------------------------------------------------------------------------- *)

Definition compatible_def :
    compatible u K = ?c. concat u c IN K
End

Definition LTL4_output_def :
   (LTL4_output T T = unknown) /\
   (LTL4_output T F = true) /\
   (LTL4_output F T = false) /\
   (LTL4_output F F = error)
End

Definition LTL4_SEM_TIME_def :
    LTL4_SEM_TIME K phi (u :'a set list) t =
    if ~compatible u K then error
    else if compatible u K /\
           (!w. (concat u w) IN K ==> LTL_SEM_TIME t (concat u w) phi) then true
    else if compatible u K /\
           (!w. (concat u w) IN K ==> ~LTL_SEM_TIME t (concat u w) phi) then false
    else unknown
End

Definition GEN_LTL4_belief_run_def :
    GEN_LTL4_belief_run K phi u t =
      {i | i extends u /\ LTL_SEM_TIME t i phi /\ i IN K}
End

Definition ABRV_monitor_def :
    ABRV_monitor K phi u t =
    LTL4_output (GEN_LTL4_belief_run K phi           u t <> EMPTY)
                (GEN_LTL4_belief_run K (LTL_NOT phi) u t <> EMPTY)
End

Theorem ABRV_monitor_thm :
    !K phi u t. ABRV_monitor K phi u t = LTL4_SEM_TIME K phi u t
Proof
    RW_TAC std_ss [ABRV_monitor_def]
 >> Cases_on `GEN_LTL4_belief_run K phi           u t = {}`
 >> Cases_on `GEN_LTL4_belief_run K (LTL_NOT phi) u t = {}`
 >> RW_TAC std_ss [LTL4_output_def] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      fs [GEN_LTL4_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_TIME_def] \\
      rw [LTL4_SEM_TIME_def, compatible_def] >| (* 3 subgoals *)
      [ (* goal 1.1 (of 3) *)
        CCONTR_TAC \\
        Q.PAT_X_ASSUM `!w. u ++ w IN K ==> _` (MP_TAC o Q.SPEC `c`) >> rw [] \\
       `u ++ c extends u` by METIS_TAC [extends_def] \\
        METIS_TAC [],
        (* goal 1.2 (of 3) *)
        CCONTR_TAC >> fs [] \\
       `u ++ w extends u` by METIS_TAC [extends_def] \\
        METIS_TAC [],
        (* goal 1.3 (of 3) *)
        CCONTR_TAC >> fs [] \\
       `u ++ w extends u` by METIS_TAC [extends_def] \\
        METIS_TAC [] ],
      (* goal 2 (of 4) *)
      fs [GEN_LTL4_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_TIME_def] \\
      rw [LTL4_SEM_TIME_def, compatible_def] >| (* 3 subgoals *)
      [ (* goal 2.1 (of 3) *)
       `?c. x = u ++ c` by METIS_TAC [extends_def] \\
        Q.PAT_X_ASSUM `!w. u ++ w IN K ==> _` (MP_TAC o (Q.SPEC `c`)) >> rw [],
        (* goal 2.2 (of 3) *)
        fs [] >> Q.EXISTS_TAC `w` >> rw [],
        (* goal 2.3 (of 3) *)
        fs [] >> `u ++ w' extends u` by METIS_TAC [extends_def] \\
        METIS_TAC [] ],
      (* goal 3 (of 4) *)
      fs [GEN_LTL4_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_TIME_def] \\
      rw [LTL4_SEM_TIME_def, compatible_def] >| (* 3 subgoals *)
      [ (* goal 3.1 (of 3) *)
       `?c. x = u ++ c` by METIS_TAC [extends_def] \\
        Q.EXISTS_TAC `c` >> rw [],
        (* goal 3.2 (of 3) *)
        fs [] \\
        Q.PAT_X_ASSUM `!w. u ++ w IN K ==> _` (MP_TAC o (Q.SPEC `w`)) >> rw [] \\
       `u ++ w extends u` by METIS_TAC [extends_def] \\
        METIS_TAC [],
        (* goal 2.3 (of 3) *)
        fs [] >> `u ++ w extends u` by METIS_TAC [extends_def] \\
        METIS_TAC [] ],
      (* goal 4 (of 4) *)
      fs [GEN_LTL4_belief_run_def, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION,
          LTL_SEM_TIME_def] \\
      rw [LTL4_SEM_TIME_def, compatible_def] >| (* 3 subgoals *)
      [ (* goal 4.1 (of 3) *)
       `?c. x' = u ++ c` by METIS_TAC [extends_def] \\
        Q.PAT_X_ASSUM `!w. u ++ w IN K ==> _` (MP_TAC o (Q.SPEC `c`)) >> rw [],
        (* goal 4.2 (of 3) *)
        fs [] >> `?c. x = u ++ c` by METIS_TAC [extends_def] \\
        Q.PAT_X_ASSUM `!w. u ++ w IN K ==> _` (MP_TAC o (Q.SPEC `c`)) >> rw [],
        (* goal 4.3 (of 3) *)
        fs [] >> Q.EXISTS_TAC `w` >> rw [] ] ]
QED

(* -------------------------------------------------------------------------- *)
(*   ABRV monitors (concrete versions)                                        *)
(* -------------------------------------------------------------------------- *)



val _ = export_theory ();

(* References:

  [1] Bauer, A., Leucker, M., Schallhart, C.: Runtime Verification for LTL
      and TLTL. ACM Transactions on Software Engineering and
      Methodology (ACM TOSEM.) 20, 14–64 (2011).
      https://doi.org/10.1145/2000799.2000800

  [2] Havelund, K., Rosu, G.: Synthesizing Monitors for Safety Properties.
      In: Katoen, J.-P. and Stevens, P. (eds.) LNCS 2280 -
      Tools and Algorithms for the Construction and Analysis of Systems
      (TACAS 2002). pp. 342–356. Springer, Berlin, Heidelberg (2002).
      https://doi.org/10.1007/3-540-46002-0_24

 *)
