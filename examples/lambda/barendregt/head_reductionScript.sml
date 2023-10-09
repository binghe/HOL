open HolKernel Parse boolLib bossLib;

open boolSimps relationTheory pred_setTheory listTheory finite_mapTheory
     arithmeticTheory pathTheory hurdUtils BasicProvers;

open termTheory appFOLDLTheory chap2Theory chap3Theory nomsetTheory binderLib
     term_posnsTheory finite_developmentsTheory;

val _ = new_theory "head_reduction"

val _ = ParseExtras.temp_loose_equality()

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

Inductive hreduce1 :
  (∀v M N. hreduce1 (LAM v M @@ N) ([N/v]M)) ∧
[~LAM:]
  (∀v M1 M2. hreduce1 M1 M2 ⇒ hreduce1 (LAM v M1) (LAM v M2)) ∧
[~APP:]
  (∀M1 M2 N. hreduce1 M1 M2 ∧ ¬is_abs M1 ⇒ hreduce1 (M1 @@ N) (M2 @@ N))
End

val _ = set_fixity "-h->" (Infix(NONASSOC, 450))
val _ = overload_on ("-h->", ``hreduce1``)

val _ = set_fixity "-h->*" (Infix(NONASSOC, 450))
val _ = overload_on ("-h->*", ``hreduce1^*``)

val hreduce_ccbeta = store_thm(
  "hreduce_ccbeta",
  ``∀M N. M -h-> N ⇒ M -β-> N``,
  HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][cc_beta_thm] THEN
  METIS_TAC []);

val hreduce1_FV = store_thm(
  "hreduce1_FV",
  ``∀M N. M -h-> N ⇒ ∀v. v ∈ FV N ⇒ v ∈ FV M``,
  METIS_TAC [SUBSET_DEF, hreduce_ccbeta, cc_beta_FV_SUBSET]);


val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT,2)),
                       fixity = Infix(NONASSOC, 950),
                       paren_style = OnlyIfNecessary,
                       pp_elements = [TOK "·", BreakSpace(0,0)],
                       term_name = "apply_perm"}
val _ = temp_overload_on ("apply_perm", ``λp M. tpm [p] M``)
val _ = temp_overload_on ("apply_perm", ``tpm``)

val tpm_hreduce_I = store_thm(
  "tpm_hreduce_I",
  ``∀M N. M -h-> N ⇒ ∀π. π·M -h-> π·N``,
  HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][tpm_subst, hreduce1_rules]);

Theorem tpm_hreduce[simp] :
    ∀M N π. π·M -h-> π·N ⇔ M -h-> N
Proof
  METIS_TAC [pmact_inverse, tpm_hreduce_I]
QED

val hreduce1_rwts = store_thm(
  "hreduce1_rwts",
  ``(VAR s -h-> M ⇔ F) ∧
    (¬is_abs M ⇒ (M @@ N -h-> P ⇔ ∃M'. (P = M' @@ N) ∧ M -h-> M')) ∧
    (LAM v M -h-> N ⇔ ∃M'. (N = LAM v M') ∧ M -h-> M') ∧
    (LAM v M @@ N -h-> P ⇔ (P = [N/v]M))``,
  REPEAT STRIP_TAC THENL [
    SRW_TAC [][Once hreduce1_cases],
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [hreduce1_cases])) THEN
    SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `∀v N. M ≠ LAM v N` THEN1 METIS_TAC [] THEN
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [],
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [hreduce1_cases])) THEN
    SRW_TAC [DNF_ss][LAM_eq_thm, tpm_eqr] THEN EQ_TAC THEN
    SRW_TAC [][] THEN1 SRW_TAC [][] THEN
    Q.EXISTS_TAC `(v,v')·M2` THEN
    SRW_TAC [][] THENL [
      `v # (v,v')·M` by SRW_TAC [][] THEN
      `v # M2` by METIS_TAC [hreduce1_FV] THEN
      SRW_TAC [][GSYM tpm_ALPHA],

      METIS_TAC [pmact_sing_inv, tpm_hreduce_I]
    ],

    SRW_TAC [DNF_ss][Once hreduce1_cases, LAM_eq_thm] THEN
    SRW_TAC [][EQ_IMP_THM, tpm_eqr] THEN
    METIS_TAC [lemma15a, pmact_flip_args, fresh_tpm_subst]
  ]);

val hreduce1_unique = store_thm(
  "hreduce1_unique",
  ``∀M N1 N2. M -h-> N1 ∧ M -h-> N2 ⇒ (N1 = N2)``,
  Q_TAC SUFF_TAC `∀M N. M -h-> N ⇒ ∀P. M -h-> P ⇒ (N = P)`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC hreduce1_ind THEN
  SIMP_TAC (srw_ss() ++ DNF_ss) [hreduce1_rwts]);

Theorem hreduce1_gen_bvc_ind :
  !P f. (!x. FINITE (f x)) /\
        (!v M N x. v NOTIN f x ==> P (LAM v M @@ N) ([N/v] M) x) /\
        (!v M1 M2 x. M1 -h-> M2 /\ v NOTIN f x /\ (!z. P M1 M2 z) ==>
                     P (LAM v M1) (LAM v M2) x) /\
        (!M1 M2 N x. M1 -h-> M2 /\ (!z. P M1 M2 z) /\ ~is_abs M1 ==>
                     P (M1 @@ N) (M2 @@ N) x)
    ==> !M N. M -h-> N ==> !x. P M N x
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Suff ‘!M N. M -h-> N ==> !p x. P (tpm p M) (tpm p N) x’
 >- METIS_TAC [pmact_nil]
 >> HO_MATCH_MP_TAC hreduce1_strongind
 >> reverse (rw []) (* easy goal first *)
 >- (Q.ABBREV_TAC ‘u = lswapstr p v’ \\
     Q_TAC (NEW_TAC "z") ‘(f x) UNION {v} UNION FV (tpm p M) UNION FV (tpm p N)’ \\
    ‘(LAM u (tpm p M) = LAM z (tpm ([(z,u)] ++ p) M)) /\
     (LAM u (tpm p N) = LAM z (tpm ([(z,u)] ++ p) N))’
       by rw [tpm_ALPHA, pmact_decompose] >> rw [])
 (* stage work *)
 >> Q.ABBREV_TAC ‘u = lswapstr p v’
 >> Q_TAC (NEW_TAC "z") ‘(f x) UNION {v} UNION FV (tpm p M) UNION FV (tpm p N)’
 >> ‘LAM u (tpm p M) = LAM z (tpm ([(z,u)] ++ p) M)’ by rw [tpm_ALPHA, pmact_decompose]
 >> POP_ORW
 >> Q.ABBREV_TAC ‘M1 = apply_perm ([(z,u)] ++ p) M’
 >> Suff ‘tpm p ([N/v] M) = [tpm p N/z] M1’ >- rw []
 >> rw [tpm_subst, Abbr ‘M1’]
 >> simp [Once tpm_CONS, fresh_tpm_subst]
 >> simp [lemma15a]
QED

(* |- !P X.
        FINITE X /\ (!v M N. v NOTIN X ==> P (LAM v M @@ N) ([N/v] M)) /\
        (!v M1 M2. M1 -h-> M2 /\ v NOTIN X /\ P M1 M2 ==> P (LAM v M1) (LAM v M2)) /\
        (!M1 M2 N. M1 -h-> M2 /\ P M1 M2 /\ ~is_abs M1 ==> P (M1 @@ N) (M2 @@ N)) ==>
        !M N. M -h-> N ==> P M N
 *)
Theorem hreduce1_bvcX_ind =
  hreduce1_gen_bvc_ind |> Q.SPECL [`λM N x. P' M N`, `λx. X`]
                       |> SIMP_RULE (srw_ss()) []
                       |> Q.INST [`P'` |-> `P`]
                       |> Q.GEN `X` |> Q.GEN `P`

(* Lemma 8.3.12 [1, p.174] *)
Theorem hreduce1_substitutive :
    !M N. M -h-> N ==> [P/v] M -h-> [P/v] N
Proof
    HO_MATCH_MP_TAC hreduce1_bvcX_ind
 >> Q.EXISTS_TAC ‘FV P UNION {v}’ >> rw [hreduce1_rules]
 >- METIS_TAC [substitution_lemma, hreduce1_rules]
 >> ‘is_comb M \/ is_var M’ by METIS_TAC [term_cases]
 >- (MATCH_MP_TAC hreduce1_APP >> art [] \\
     gs [is_comb_APP_EXISTS, is_abs_thm])
 >> gs [is_var_cases, hreduce1_rwts]
QED

(* This form is useful for ‘|- substitutive R ==> ...’ theorems (chap3Theory) *)
Theorem substitutive_hreduce1 :
    substitutive (-h->)
Proof
    rw [substitutive_def, hreduce1_substitutive]
QED

Theorem hreduce_substitutive :
    !M N. M -h->* N ==> [P/v] M -h->* [P/v] N
Proof
    HO_MATCH_MP_TAC RTC_INDUCT >> rw []
 >> METIS_TAC [RTC_RULES, hreduce1_substitutive]
QED

Theorem substitutive_hreduce :
    substitutive (-h->*)
Proof
    rw [substitutive_def, hreduce_substitutive]
QED

(* ----------------------------------------------------------------------
    Head normal form (hnf)
   ---------------------------------------------------------------------- *)

val hnf_def = Define`hnf M = ∀N. ¬(M -h-> N)`;
val hnf_thm = Store_thm(
  "hnf_thm",
  ``(hnf (VAR s) ⇔ T) ∧
    (hnf (M @@ N) ⇔ hnf M ∧ ¬is_abs M) ∧
    (hnf (LAM v M) ⇔ hnf M)``,
  SRW_TAC [][hnf_def, hreduce1_rwts] THEN
  Cases_on `is_abs M` THEN SRW_TAC [][hreduce1_rwts] THEN
  Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
  FULL_SIMP_TAC (srw_ss()) [hreduce1_rwts]);

val hnf_tpm = Store_thm(
  "hnf_tpm",
  ``∀M π. hnf (π·M) = hnf M``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

val strong_cc_ind = IndDefLib.derive_strong_induction (compat_closure_rules,
                                                       compat_closure_ind)

val hnf_ccbeta_preserved = store_thm(
  "hnf_ccbeta_preserved",
  ``∀M N. compat_closure beta M N ∧ hnf M ⇒ hnf N``,
  Q_TAC SUFF_TAC
        `∀M N. compat_closure beta M N ⇒ hnf M ⇒ hnf N`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC strong_cc_ind THEN SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [beta_def] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [],

    Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [cc_beta_thm] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
  ]);

Theorem hnf_I :
    hnf I
Proof
    RW_TAC std_ss [hnf_thm, I_def]
QED

Theorem hnf_LAMl[simp] :
    hnf (LAMl vs M) <=> hnf M
Proof
    Induct_on ‘vs’ >> rw []
QED

Theorem hnf_appstar :
    !M Ns. hnf (M @* Ns) <=> hnf M /\ (is_abs M ⇒ (Ns = []))
Proof
  Induct_on ‘Ns’ using SNOC_INDUCT >> simp[appstar_SNOC] >>
  dsimp[SF CONJ_ss] >> metis_tac[]
QED

(* FIXME: can we put ‘ALL_DISTINCT vs’ into RHS? cf. bnf_characterisation *)
Theorem hnf_cases :
  !M : term. hnf M <=> ?vs args y. M = LAMl vs (VAR y @* args)
Proof
  simp[FORALL_AND_THM, EQ_IMP_THM] >> conj_tac
  >- (gen_tac >> MP_TAC (Q.SPEC ‘M’ strange_cases)
      >> RW_TAC std_ss []
      >- (FULL_SIMP_TAC std_ss [size_1_cases] \\
          qexistsl_tac [‘vs’, ‘[]’, ‘y’] >> rw [])
      >> FULL_SIMP_TAC std_ss [hnf_LAMl]
      >> ‘hnf t /\ ~is_abs t’ by PROVE_TAC [hnf_appstar]
      >> ‘is_var t’ by METIS_TAC [term_cases]
      >> FULL_SIMP_TAC std_ss [is_var_cases]
      >> qexistsl_tac [‘vs’, ‘args’, ‘y’] >> art []) >>
  simp[PULL_EXISTS, hnf_appstar]
QED

(* ----------------------------------------------------------------------
    Weak head reductions (weak_head or -w->)
   ---------------------------------------------------------------------- *)

Inductive weak_head :
  (∀v M N :term. weak_head (LAM v M @@ N) ([N/v]M)) ∧
  (∀M₁ M₂ N. weak_head M₁ M₂ ⇒ weak_head (M₁ @@ N) (M₂ @@ N))
End

val _ = set_fixity "-w->" (Infix(NONASSOC, 450))
val _ = overload_on ("-w->", ``weak_head``)

val wh_is_abs = store_thm(
  "wh_is_abs",
  ``∀M N. M -w-> N ⇒ ¬is_abs M``,
  HO_MATCH_MP_TAC weak_head_ind THEN SRW_TAC [][]);

val wh_lam = Store_thm(
  "wh_lam",
  ``∀v M N. ¬(LAM v M -w-> N)``,
  ONCE_REWRITE_TAC [weak_head_cases] THEN SRW_TAC [][]);

val wh_head = store_thm(
  "wh_head",
  ``∀M N. M -w-> N ⇒ M -h-> N``,
    HO_MATCH_MP_TAC weak_head_strongind
 >> METIS_TAC [wh_is_abs, hreduce1_rules]);

val _ = set_fixity "-w->*" (Infix(NONASSOC, 450))
val _ = overload_on ("-w->*", ``RTC (-w->)``)

val whead_FV = store_thm(
  "whead_FV",
  ``∀M N. M -w-> N ⇒ v ∈ FV N ⇒ v ∈ FV M``,
  HO_MATCH_MP_TAC weak_head_ind THEN SRW_TAC [][FV_SUB] THEN
  METIS_TAC []);
val whstar_FV = store_thm(
  "whstar_FV",
  ``∀M N. M -w->* N ⇒ v ∈ FV N ⇒ v ∈ FV M``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  METIS_TAC [relationTheory.RTC_RULES, whead_FV]);


val _ = reveal "Y"
val whY1 = store_thm(
  "whY1",
  ``Y @@ f -w-> Yf f``,
  SRW_TAC [][chap2Theory.Y_def, chap2Theory.Yf_def, LET_THM,
             Once weak_head_cases] THEN
  NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  SRW_TAC [DNF_ss][LAM_eq_thm] THEN DISJ1_TAC THEN
  SRW_TAC [][chap2Theory.SUB_LAM_RWT, LET_THM] THEN NEW_ELIM_TAC THEN
  SRW_TAC [][LAM_eq_thm, tpm_fresh]);

val whY2 = store_thm(
  "whY2",
  ``Yf f -w-> f @@ Yf f``,
  SRW_TAC [][chap2Theory.Yf_def, LET_THM, Once weak_head_cases] THEN
  NEW_ELIM_TAC THEN SRW_TAC [DNF_ss][LAM_eq_thm, lemma14b]);

val wh_unique = store_thm(
  "wh_unique",
  ``M -w-> N₁ ∧ M -w-> N₂ ⇒ (N₁ = N₂)``,
  METIS_TAC [hreduce1_unique, wh_head]);

val whnf_def = Define`
  whnf M = ∀N. ¬(M -w-> N)
`;

val hnf_whnf = store_thm(
  "hnf_whnf",
  ``hnf M ⇒ whnf M``,
  METIS_TAC [hnf_def, whnf_def, wh_head]);

val bnf_hnf = store_thm(
  "bnf_hnf",
  ``bnf M ⇒ hnf M``,
  METIS_TAC [hnf_def, beta_normal_form_bnf, corollary3_2_1, hreduce_ccbeta]);

val bnf_whnf = store_thm(
  "bnf_whnf",
  ``bnf M ⇒ whnf M``,
  METIS_TAC [hnf_whnf, bnf_hnf]);

val whnf_thm = Store_thm(
  "whnf_thm",
  ``whnf (VAR s) ∧
    (whnf (M @@ N) ⇔ ¬is_abs M ∧ whnf M) ∧
    whnf (LAM v M)``,
  REPEAT CONJ_TAC THEN SRW_TAC [][whnf_def, Once weak_head_cases] THEN
  EQ_TAC THEN SRW_TAC [][FORALL_AND_THM] THENL [
    Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN SRW_TAC [][] THEN
    METIS_TAC [],
    Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val wh_weaken_cong = store_thm(
  "wh_weaken_cong",
  ``whnf N ⇒ M₁ -w->* M₂ ⇒ (M₁ -w->* N = M₂ -w->* N)``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, IMP_CONJ_THM] THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `∀M N. M -w->* N ⇒ ∀N'. M -w->* N' ∧ whnf N' ⇒ N -w->* N'`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN
    METIS_TAC [relationTheory.RTC_CASES1, whnf_def, wh_unique],

    METIS_TAC [relationTheory.RTC_CASES_RTC_TWICE]
  ]);

val wh_app_congL = store_thm(
  "wh_app_congL",
  ``M -w->* M' ==> M @@ N -w->* M' @@ N``,
  STRIP_TAC THEN Q.ID_SPEC_TAC `N` THEN POP_ASSUM MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`M'`, `M`] THEN
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [relationTheory.RTC_RULES, weak_head_rules]);

val tpm_whead_I = store_thm(
  "tpm_whead_I",
  ``∀M N. M -w-> N ⇒ π·M -w-> π·N``,
  HO_MATCH_MP_TAC weak_head_ind THEN SRW_TAC [][weak_head_rules, tpm_subst]);

val whead_gen_bvc_ind = store_thm(
  "whead_gen_bvc_ind",
  ``∀P f. (∀x. FINITE (f x)) ∧
          (∀v M N x. v ∉ f x ⇒ P (LAM v M @@ N) ([N/v]M) x) ∧
          (∀M₁ M₂ N x. (∀z. P M₁ M₂ z) ⇒ P (M₁ @@ N) (M₂ @@ N) x)
        ⇒
          ∀M N. M -w-> N ⇒ ∀x. P M N x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `∀M N. M -w-> N ⇒ ∀π x. P (π·M) (π·N) x`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC weak_head_ind THEN SRW_TAC [][tpm_subst] THEN
  Q_TAC (NEW_TAC "z") `{lswapstr π v} ∪ FV (π·M) ∪ FV (π·N) ∪ f x` THEN
  `LAM (lswapstr π v) (π·M) = LAM z ([VAR z/lswapstr π v](π·M))`
     by SRW_TAC [][SIMPLE_ALPHA] THEN
  `[π·N/lswapstr π v](π·M) = [π·N/z] ([VAR z/lswapstr π v](π·M))`
     by SRW_TAC [][lemma15a] THEN
  SRW_TAC [][]);

val whead_bvcX_ind = save_thm(
  "whead_bvcX_ind",
  whead_gen_bvc_ind |> Q.SPECL [`λM N x. P' M N`, `λx. X`]
                    |> SIMP_RULE (srw_ss()) []
                    |> Q.INST [`P'` |-> `P`]
                    |> Q.GEN `X` |> Q.GEN `P`);

val wh_substitutive = store_thm(
  "wh_substitutive",
  ``∀M N. M -w-> N ⇒ [P/v]M -w-> [P/v]N``,
  HO_MATCH_MP_TAC whead_bvcX_ind THEN Q.EXISTS_TAC `FV P ∪ {v}` THEN
  SRW_TAC [][weak_head_rules] THEN
  METIS_TAC [chap2Theory.substitution_lemma, weak_head_rules]);

val whstar_substitutive = store_thm(
  "whstar_substitutive",
  ``∀M N. M -w->* N ⇒ [P/v]M -w->* [P/v]N``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [relationTheory.RTC_RULES, wh_substitutive]);

val whstar_betastar = store_thm(
  "whstar_betastar",
  ``∀M N. M -w->* N ⇒ M -β->* N``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [relationTheory.RTC_RULES, wh_head, hreduce_ccbeta]);

val whstar_lameq = store_thm(
  "whstar_lameq",
  ``M -w->* N ⇒ M == N``,
  METIS_TAC [betastar_lameq, whstar_betastar]);

val whstar_abs = Store_thm(
  "whstar_abs",
  ``LAM v M -w->* N ⇔ (N = LAM v M)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [Once relationTheory.RTC_CASES1,
                            Once weak_head_cases]);

(* ----------------------------------------------------------------------
    has_whnf
   ---------------------------------------------------------------------- *)

(* definition of has_hnf in standardisationScript has == rather than -h->*
   as the relation on the RHS.  This means that has_bnf automatically implies
   has_hnf, but makes the corollary to the standardisation theorem interesting
   to prove... *)
val has_whnf_def = Define`
  has_whnf M = ∃N. M -w->* N ∧ whnf N
`;

val has_whnf_APP_E = store_thm(
  "has_whnf_APP_E",
  ``has_whnf (M @@ N) ⇒ has_whnf M``,
  simp_tac (srw_ss())[has_whnf_def] >>
  Q_TAC SUFF_TAC
     `∀M N. M -w->* N ⇒ ∀M0 M1. (M = M0 @@ M1) ∧ whnf N ⇒
                                 ∃N'. M0 -w->* N' ∧ whnf N'`
     >- metis_tac [] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> conj_tac
    >- (simp_tac (srw_ss()) [] >> metis_tac [relationTheory.RTC_RULES]) >>
  srw_tac [][] >> Cases_on `is_abs M0`
    >- (Q.SPEC_THEN `M0` FULL_STRUCT_CASES_TAC term_CASES >>
        full_simp_tac (srw_ss()) [] >>
        metis_tac [relationTheory.RTC_RULES, whnf_thm]) >>
  full_simp_tac (srw_ss()) [Once weak_head_cases] >>
  metis_tac [relationTheory.RTC_RULES])

val hreduce_weak_or_strong = store_thm(
  "hreduce_weak_or_strong",
  ``∀M N. M -h-> N ⇒ whnf M ∨ M -w-> N``,
  ho_match_mp_tac simple_induction >> simp_tac (srw_ss()) [] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) [Once hreduce1_cases] >>
  simp_tac (srw_ss() ++ DNF_ss) [] >> conj_tac
    >- metis_tac [weak_head_rules] >>
  srw_tac [][] >> metis_tac [weak_head_rules]);

val head_reductions_have_weak_prefixes = store_thm(
  "head_reductions_have_weak_prefixes",
  ``∀M N. M -h->* N ⇒ hnf N ⇒
          ∃N0. M -w->* N0 ∧ whnf N0 ∧ N0 -h->* N``,
   ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT >> conj_tac
     >- metis_tac [hnf_whnf, relationTheory.RTC_RULES] >>
   metis_tac [relationTheory.RTC_RULES, hreduce_weak_or_strong]);

(* ----------------------------------------------------------------------
    Head redex
   ---------------------------------------------------------------------- *)

val _ = add_infix ("is_head_redex", 760, NONASSOC)

Inductive is_head_redex :
    (!v (t:term) u. [] is_head_redex (LAM v t @@ u)) /\
    (!v t p. p is_head_redex t ==> (In::p) is_head_redex (LAM v t)) /\
    (!t u v p. p is_head_redex (t @@ u) ==>
               (Lt::p) is_head_redex (t @@ u) @@ v)
End

val ihr_bvc_ind = store_thm(
  "ihr_bvc_ind",
  ``!P X. FINITE X /\
          (!v M N. ~(v IN X) /\ ~(v IN FV N) ==> P [] (LAM v M @@ N)) /\
          (!v M p. ~(v IN X) /\ P p M ==> P (In::p) (LAM v M)) /\
          (!M N L p. P p (M @@ N) ==> P (Lt::p) ((M @@ N) @@ L)) ==>
          !p M. p is_head_redex M ==> P p M``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!p M. p is_head_redex M ==> !pi. P p (tpm pi M)`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC is_head_redex_ind THEN
  SRW_TAC [][is_head_redex_rules] THENL [
    Q.MATCH_ABBREV_TAC `P [] (LAM vv MM @@ NN)` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    Q_TAC (NEW_TAC "z") `FV MM UNION FV NN UNION X` THEN
    `LAM vv MM = LAM z (tpm [(z,vv)] MM)` by SRW_TAC [][tpm_ALPHA] THEN
    SRW_TAC [][],
    Q.MATCH_ABBREV_TAC `P (In::p) (LAM vv MM)` THEN
    Q_TAC (NEW_TAC "z") `FV MM UNION X` THEN
    `LAM vv MM = LAM z (tpm [(z,vv)] MM)` by SRW_TAC [][tpm_ALPHA] THEN
    SRW_TAC [][GSYM pmact_decompose, Abbr`MM`]
  ]);

val is_head_redex_subst_invariant = store_thm(
  "is_head_redex_subst_invariant",
  ``!p t u v. p is_head_redex t ==> p is_head_redex [u/v] t``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`t`, `p`] THEN
  HO_MATCH_MP_TAC ihr_bvc_ind THEN Q.EXISTS_TAC `v INSERT FV u` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, is_head_redex_rules]);

Theorem is_head_redex_tpm_invariant[simp] :
    p is_head_redex (tpm pi t) = p is_head_redex t
Proof
  Q_TAC SUFF_TAC `!p t. p is_head_redex t ==> !pi. p is_head_redex (tpm pi t)`
        THEN1 METIS_TAC [pmact_inverse] THEN
  HO_MATCH_MP_TAC is_head_redex_ind THEN SRW_TAC [][is_head_redex_rules]
QED

val is_head_redex_unique = store_thm(
  "is_head_redex_unique",
  ``!t p1 p2. p1 is_head_redex t /\ p2 is_head_redex t ==> (p1 = p2)``,
  Q_TAC SUFF_TAC
        `!p1 t. p1 is_head_redex t ==> !p2. p2 is_head_redex t ==> (p1 = p2)`
        THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC is_head_redex_ind THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [is_head_redex_cases] THEN
  SRW_TAC [][LAM_eq_thm]);

val is_head_redex_thm = store_thm(
  "is_head_redex_thm",
  ``(p is_head_redex (LAM v t) = ?p0. (p = In::p0) /\ p0 is_head_redex t) /\
    (p is_head_redex (t @@ u) = (p = []) /\ is_abs t \/
                                ?p0. (p = Lt::p0) /\ is_comb t /\
                                          p0 is_head_redex t) /\
    (p is_head_redex (VAR v) = F)``,
  REPEAT CONJ_TAC THEN
  SRW_TAC [][Once is_head_redex_cases, SimpLHS, LAM_eq_thm] THEN
  SRW_TAC [][EQ_IMP_THM] THENL [
    PROVE_TAC [],
    PROVE_TAC [is_abs_thm, term_CASES],
    METIS_TAC [is_comb_thm, term_CASES]
  ]);

val head_redex_leftmost = store_thm(
  "head_redex_leftmost",
  ``!p t. p is_head_redex t ==>
          !p'. p' IN redex_posns t ==> (p = p') \/ p < p'``,
  HO_MATCH_MP_TAC is_head_redex_ind THEN
  SRW_TAC [][redex_posns_thm, DISJ_IMP_THM]);

val hnf_no_head_redex = store_thm(
  "hnf_no_head_redex",
  ``!t. hnf t = !p. ~(p is_head_redex t)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][hnf_thm, is_head_redex_thm] THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][is_head_redex_thm]);

val head_redex_is_redex = store_thm(
  "head_redex_is_redex",
  ``!p t. p is_head_redex t ==> p IN redex_posns t``,
  HO_MATCH_MP_TAC is_head_redex_ind THEN
  SRW_TAC [][redex_posns_thm]);

val is_head_redex_vsubst_invariant = store_thm(
  "is_head_redex_vsubst_invariant",
  ``!t v x p. p is_head_redex ([VAR v/x] t) = p is_head_redex t``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`p`, `t`] THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{x;v}` THEN
  SRW_TAC [][is_head_redex_thm, SUB_THM, SUB_VAR]);

val head_redex_preserved = store_thm(
  "head_redex_preserved",
  ``!M p N.
      labelled_redn beta M p N ==>
      !h. h is_head_redex M /\ ~(h = p) ==> h is_head_redex N``,
  HO_MATCH_MP_TAC strong_labelled_redn_ind THEN
  SRW_TAC [][is_head_redex_thm, beta_def] THENL [
    FULL_SIMP_TAC (srw_ss()) [is_head_redex_thm],
    `?v t. M = LAM v t` by PROVE_TAC [is_abs_thm, term_CASES] THEN
    FULL_SIMP_TAC (srw_ss()) [labelled_redn_lam],
    `?f x. M = f @@ x` by PROVE_TAC [is_comb_APP_EXISTS] THEN
    SRW_TAC [][] THEN
    Q.PAT_X_ASSUM `labelled_redn beta _ _ _` MP_TAC THEN
    ONCE_REWRITE_TAC [labelled_redn_cases] THEN
    FULL_SIMP_TAC (srw_ss()) [is_head_redex_thm, beta_def] THEN
    PROVE_TAC [is_comb_thm]
  ]);

val is_head_reduction_def = Define`
  is_head_reduction s = okpath (labelled_redn beta) s /\
                        !i. i + 1 IN PL s ==>
                            nth_label i s is_head_redex el i s
`;

Theorem is_head_reduction_thm[simp] :
    (is_head_reduction (stopped_at x) = T) /\
    (is_head_reduction (pcons x r p) =
       labelled_redn beta x r (first p) /\ r is_head_redex x /\
       is_head_reduction p)
Proof
  SRW_TAC [][is_head_reduction_def, GSYM ADD1,
             EQ_IMP_THM]
  THENL [
    POP_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][],
    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [],
    Cases_on `i` THEN SRW_TAC [][]
  ]
QED

val _ = add_infix ("head_reduces", 760, NONASSOC)
val head_reduces_def = Define`
  M head_reduces N = ?s. finite s /\ (first s = M) /\ (last s = N) /\
                         is_head_reduction s
`;


val head_reduce1_def = store_thm(
  "head_reduce1_def",
  ``M -h-> N = (?r. r is_head_redex M /\ labelled_redn beta M r N)``,
  EQ_TAC THENL [
    Q_TAC SUFF_TAC `!M N. M -h-> N ==>
                          ?r. r is_head_redex M /\ labelled_redn beta M r N`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][] THENL [
      METIS_TAC [beta_def, is_head_redex_rules, labelled_redn_rules],
      METIS_TAC [is_head_redex_rules, labelled_redn_rules],
      Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THENL [
        FULL_SIMP_TAC (srw_ss()) [Once labelled_redn_cases, beta_def],
        METIS_TAC [is_head_redex_rules, labelled_redn_rules],
        FULL_SIMP_TAC (srw_ss()) []
      ]
    ],
    Q_TAC SUFF_TAC `!M r N. labelled_redn beta M r N ==>
                            r is_head_redex M ==> M -h-> N`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC labelled_redn_ind THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [beta_def, is_head_redex_thm,
                                   Once is_comb_APP_EXISTS, hreduce1_rwts]
  ]);

val head_reduces_RTC_hreduce1 = store_thm(
  "head_reduces_RTC_hreduce1",
  ``(head_reduces) = RTC (-h->)``,
  SIMP_TAC (srw_ss()) [head_reduces_def, FUN_EQ_THM, GSYM LEFT_FORALL_IMP_THM,
                       FORALL_AND_THM, EQ_IMP_THM] THEN
  CONJ_TAC THENL [
    Q_TAC SUFF_TAC `!s. finite s ==>
                        is_head_reduction s ==>
                        RTC (-h->) (first s) (last s)` THEN1
          PROVE_TAC [] THEN
    HO_MATCH_MP_TAC pathTheory.finite_path_ind THEN
    SIMP_TAC (srw_ss()) [relationTheory.RTC_RULES] THEN
    MAP_EVERY Q.X_GEN_TAC [`x`,`r`,`p`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) THEN
    Q.EXISTS_TAC `first p` THEN SRW_TAC [][head_reduce1_def] THEN
    PROVE_TAC [],
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
    SRW_TAC [][head_reduce1_def] THENL [
      Q.EXISTS_TAC `stopped_at x` THEN SRW_TAC [][],
      Q.EXISTS_TAC `pcons x r s` THEN SRW_TAC [][]
    ]
  ]);

val head_reduces_reduction_beta = store_thm(
  "head_reduces_reduction_beta",
  ``!M N. M head_reduces N ==> reduction beta M N``,
  SIMP_TAC (srw_ss()) [head_reduces_RTC_hreduce1] THEN
  MATCH_MP_TAC relationTheory.RTC_MONOTONE THEN
  METIS_TAC [head_reduce1_def, labelled_redn_cc]);

val head_reduces_TRANS = store_thm(
  "head_reduces_TRANS",
  ``!M N P. M head_reduces N /\ N head_reduces P ==> M head_reduces P``,
  METIS_TAC [relationTheory.RTC_RTC, head_reduces_RTC_hreduce1]);

val has_hnf_def = Define`
  has_hnf M = ?N. M == N /\ hnf N
`;

val has_bnf_hnf = store_thm(
  "has_bnf_hnf",
  ``has_bnf M ⇒ has_hnf M``,
  SRW_TAC [][has_hnf_def, chap2Theory.has_bnf_def] THEN
  METIS_TAC [bnf_hnf]);

val head_reduct_def = Define`
  head_reduct M = if ?r. r is_head_redex M then
                    SOME (@N. M -h-> N)
                  else NONE
`;

val head_reduct_unique = store_thm(
  "head_reduct_unique",
  ``!M N. M -h-> N ==> (head_reduct M = SOME N)``,
  SRW_TAC [][head_reduce1_def, head_reduct_def] THEN1 METIS_TAC [] THEN
  SELECT_ELIM_TAC THEN METIS_TAC [is_head_redex_unique, labelled_redn_det]);

val head_reduct_NONE = store_thm(
  "head_reduct_NONE",
  ``(head_reduct M = NONE) = !N. ~(M -h-> N)``,
  SRW_TAC [][head_reduct_def, head_reduce1_def] THEN
  METIS_TAC [head_redex_is_redex, IN_term_IN_redex_posns,
             is_redex_occurrence_def]);

val head_reduct_SOME = store_thm(
  "head_reduct_SOME",
  ``(head_reduct M = SOME N) = M -h-> N``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, head_reduct_unique] THEN
  SRW_TAC [][head_reduct_def] THEN SELECT_ELIM_TAC THEN
  SRW_TAC [][head_reduce1_def] THEN
  METIS_TAC [head_redex_is_redex, IN_term_IN_redex_posns,
             is_redex_occurrence_def]);

val is_head_reduction_coind = store_thm(
  "is_head_reduction_coind",
  ``(!x r q. P (pcons x r q) ==>
             labelled_redn beta x r (first q) /\
             r is_head_redex x /\ P q) ==>
    !p. P p ==> is_head_reduction p``,
  SIMP_TAC (srw_ss()) [is_head_reduction_def, IMP_CONJ_THM,
                       FORALL_AND_THM] THEN CONJ_TAC
  THENL [
    STRIP_TAC THEN HO_MATCH_MP_TAC okpath_co_ind THEN METIS_TAC [],
    STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    Q_TAC SUFF_TAC `!i. i + 1 IN PL p ==> nth_label i p is_head_redex el i p /\
                                          P (drop (i + 1) p)` THEN1
          METIS_TAC [] THEN
    Induct THEN FULL_SIMP_TAC (srw_ss()) [GSYM ADD1] THENL [
      Q.ISPEC_THEN `p` FULL_STRUCT_CASES_TAC path_cases THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
      STRIP_TAC THEN
      `SUC i IN PL p`
         by METIS_TAC [PL_downward_closed, DECIDE ``x < SUC x``] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Q.ISPEC_THEN `p` FULL_STRUCT_CASES_TAC path_cases THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `?y s q'. drop i q = pcons y s q'` by METIS_TAC [drop_not_stopped] THEN
      `labelled_redn beta y s (first q') /\ s is_head_redex y /\ P q'`
          by METIS_TAC [stopped_at_not_pcons, pcons_11] THEN
      `el 0 (drop i q) = el i q` by SRW_TAC [][] THEN
      `el i q = y` by METIS_TAC [el_def, first_thm] THEN
      `nth_label 0 (drop i q) = nth_label i q` by SRW_TAC [][] THEN
      `nth_label i q = s` by METIS_TAC [nth_label_def, first_label_def] THEN
      SRW_TAC [][drop_tail_commute]
    ]
  ]);

val head_reduction_path_uexists = prove(
  ``!M. ?!p. (first p = M) /\ is_head_reduction p /\
             (finite p ==> hnf (last p))``,
  GEN_TAC THEN
  Q.ISPEC_THEN `\M. (M, OPTION_MAP (\N. ((@r. r is_head_redex M), N))
                                  (head_reduct M))`
               STRIP_ASSUME_TAC path_Axiom THEN
  `!M. first (g M) = M`
      by (POP_ASSUM (fn th => SRW_TAC [][Once th]) THEN
          Cases_on `head_reduct M` THEN SRW_TAC [][]) THEN
  `!M. is_head_reduction (g M)`
      by (Q_TAC SUFF_TAC
                `!p. (?M. p = g M) ==> is_head_reduction p` THEN1
                METIS_TAC [] THEN
          HO_MATCH_MP_TAC is_head_reduction_coind THEN
          Q.PAT_X_ASSUM `!x:term. g x = Z`
                          (fn th => SIMP_TAC (srw_ss())
                                             [Once th, SimpL ``(==>)``]) THEN
          REPEAT GEN_TAC THEN STRIP_TAC THEN
          Cases_on `head_reduct M` THEN
          FULL_SIMP_TAC (srw_ss()) [head_reduct_SOME, head_reduce1_def] THEN
          REPEAT VAR_EQ_TAC THEN SELECT_ELIM_TAC THEN
          METIS_TAC [is_head_redex_unique]) THEN
  `!p. finite p ==> !M. (p = g M) ==> hnf (last p)`
      by (HO_MATCH_MP_TAC finite_path_ind THEN
          SIMP_TAC (srw_ss()) [] THEN CONJ_TAC THEN REPEAT GEN_TAC THENL [
            Q.PAT_X_ASSUM `!x:term. g x = Z`
                        (fn th => ONCE_REWRITE_TAC [th]) THEN
            Cases_on `head_reduct M` THEN SRW_TAC [][] THEN
            FULL_SIMP_TAC (srw_ss()) [hnf_no_head_redex, head_reduct_NONE,
                                      head_reduce1_def] THEN
            METIS_TAC [head_redex_is_redex, IN_term_IN_redex_posns,
                       is_redex_occurrence_def],
            STRIP_TAC THEN GEN_TAC THEN
            Q.PAT_X_ASSUM `!x:term. g x = Z`
                        (fn th => ONCE_REWRITE_TAC [th]) THEN
            Cases_on `head_reduct M` THEN SRW_TAC [][]
          ]) THEN
  SIMP_TAC (srw_ss()) [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [
    Q.EXISTS_TAC `g M` THEN
    Q.PAT_X_ASSUM `!x:term. g x = Z` (K ALL_TAC) THEN METIS_TAC [],
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [path_bisimulation] THEN
    Q.EXISTS_TAC `\p1 p2. is_head_reduction p1 /\ is_head_reduction p2 /\
                          (first p1 = first p2) /\
                          (finite p1 ==> hnf (last p1)) /\
                          (finite p2 ==> hnf (last p2))` THEN
    SRW_TAC [][] THEN
    Q.ISPEC_THEN `q1` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                 path_cases THEN
    Q.ISPEC_THEN `q2` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                 path_cases THEN FULL_SIMP_TAC (srw_ss()) []
    THENL [
      METIS_TAC [hnf_no_head_redex],
      METIS_TAC [hnf_no_head_redex],
      METIS_TAC [is_head_redex_unique, labelled_redn_det]
    ]
  ]);

val head_reduction_path_def = new_specification(
  "head_reduction_path_def",
  ["head_reduction_path"],
  CONJUNCT1 ((SIMP_RULE bool_ss [EXISTS_UNIQUE_THM] o
              SIMP_RULE bool_ss [UNIQUE_SKOLEM_THM])
             head_reduction_path_uexists));

val head_reduction_path_unique = store_thm(
  "head_reduction_path_unique",
  ``!M p. (first p = M) /\ is_head_reduction p /\
          (finite p ==> hnf (last p)) ==>
          (head_reduction_path M = p)``,
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `M` (ASSUME_TAC o CONJUNCT2 o
                   SIMP_RULE bool_ss [EXISTS_UNIQUE_THM])
              head_reduction_path_uexists THEN
  METIS_TAC [head_reduction_path_def]);

val _ = export_theory()
val _ = html_theory "head_reduction";
