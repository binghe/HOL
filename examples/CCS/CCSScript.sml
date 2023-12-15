(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna, Italy (Author: Chun Tian)
 * Copyright 2018-2019  Fondazione Bruno Kessler, Italy (Author: Chun Tian)
 * Copyright 2023-2024  The Australian National University (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib relationTheory optionTheory listTheory CCSLib
     rich_listTheory;

open LabelTheory;

val _ = new_theory "CCS";

val set_ss = std_ss ++ PRED_SET_ss;

(******************************************************************************)
(*                                                                            *)
(*             Syntax of pure CCS ('a, 'b) (general formalization)            *)
(*                                                                            *)
(******************************************************************************)

(* Define the type of (pure) CCS agent expressions. *)
Datatype: CCS = nil
              | var 'a
              | prefix ('b Action) CCS
              | sum CCS CCS
              | par CCS CCS
              | restr (('b Label) set) CCS
              | relab CCS ('b Relabeling)
              | rec 'a CCS
End

val _ = TeX_notation { hol = "nil", TeX = ("\\ensuremath{\\mathbf{0}}", 1) };

(* compact representation for single-action restriction *)
val _ = overload_on ("nu", ``\(n :'b) P. restr {name n} P``);
val _ = overload_on ("nu", ``restr``);

val _ = add_rule {term_name = "nu", fixity = Closefix,
                  pp_elements = [TOK ("(" ^ UnicodeChars.nu), TM, TOK ")"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

val _ = TeX_notation { hol = "(" ^ UnicodeChars.nu,
                       TeX = ("\\ensuremath{(\\nu}", 1) };

(* TODO: send to HOL's boolTheory *)
val _ = TeX_notation { hol = "(", TeX = ("\\ensuremath{(}", 1) };
val _ = TeX_notation { hol = ")", TeX = ("\\ensuremath{)}", 1) };
val _ = TeX_notation { hol = "=", TeX = ("\\ensuremath{=}", 1) };

(* disabled: this "\mu" is conflict with the \mu action used in CCS papers
val _ = overload_on ("mu", ``rec``);
val _ = Unicode.unicode_version { u = UnicodeChars.mu, tmnm = "mu" };
val _ = TeX_notation { hol = "mu", TeX = ("\\ensuremath{\\mu}", 1) };
 *)

val _ = overload_on ("+", ``sum``); (* priority: 500 *)
val _ = TeX_notation { hol = "+", TeX = ("\\ensuremath{+}", 1) };

val _ = set_mapped_fixity { fixity = Infixl 600,
                            tok = "||", term_name = "par" };

(* val _ = Unicode.unicode_version {u = UTF8.chr 0x007C, tmnm = "par"}; *)
val _ = TeX_notation { hol = "||", TeX = ("\\ensuremath{\\mid}", 1) };

val _ =
    add_rule { term_name = "prefix", fixity = Infixr 700,
        pp_elements = [ BreakSpace(0,0), TOK "..", BreakSpace(0,0) ],
        paren_style = OnlyIfNecessary,
        block_style = (AroundSamePrec, (PP.CONSISTENT, 0)) };

val _ = TeX_notation { hol = "..", TeX = ("\\ensuremath{\\ldotp}", 1) };

(* Define structural induction on CCS agent expressions. *)
val CCS_induction = TypeBase.induction_of ``:('a, 'b) CCS``;

(* The structural cases theorem for the type CCS. *)
val CCS_cases = TypeBase.nchotomy_of ``:('a, 'b) CCS``;

(* Prove that the constructors of the type CCS are distinct. *)
val CCS_distinct = TypeBase.distinct_of ``:('a, 'b) CCS``;

(* size definition *)
val (CCS_size_tm, CCS_size_def) = TypeBase.size_of ``:('a, 'b) CCS``;

local
    val thm = CONJUNCTS CCS_distinct;
    val CCS_distinct_LIST = thm @ (map GSYM thm);
in
    val CCS_distinct' = save_thm ("CCS_distinct'", LIST_CONJ CCS_distinct_LIST);
end

Theorem CCS_distinct_exists :
    !p :('a, 'b) CCS. ?q. q <> p
Proof
    GEN_TAC >> Cases_on `p` >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `prefix a nil` >> REWRITE_TAC [CCS_distinct'])
 >> Q.EXISTS_TAC `nil`
 >> REWRITE_TAC [CCS_distinct]
QED

(* Prove that the constructors of the type CCS are one-to-one. *)
val CCS_11 = TypeBase.one_one_of ``:('a, 'b) CCS``;

(* Given any agent expression, define the substitution of an agent expression
   E' for an agent variable X.

   This works under the hypothesis that the Barendregt convention holds.
 *)
Definition CCS_Subst_def :
   (CCS_Subst nil          E' X = nil) /\
   (CCS_Subst (prefix u E) E' X = prefix u (CCS_Subst E E' X)) /\
   (CCS_Subst (sum E1 E2)  E' X = sum (CCS_Subst E1 E' X)
                                      (CCS_Subst E2 E' X)) /\
   (CCS_Subst (par E1 E2)  E' X = par (CCS_Subst E1 E' X)
                                      (CCS_Subst E2 E' X)) /\
   (CCS_Subst (restr L E)  E' X = restr L (CCS_Subst E E' X)) /\
   (CCS_Subst (relab E rf) E' X = relab   (CCS_Subst E E' X) rf) /\
   (CCS_Subst (var Y)      E' X = if (Y = X) then E' else (var Y)) /\
   (CCS_Subst (rec Y E)    E' X = if (Y = X) then (rec Y E)
                                  else (rec Y (CCS_Subst E E' X)))
End

val [CCS_Subst_nil,   CCS_Subst_prefix, CCS_Subst_sum, CCS_Subst_par,
     CCS_Subst_restr, CCS_Subst_relab,  CCS_Subst_var, CCS_Subst_rec] =
    map save_thm
        (combine (["CCS_Subst_nil",   "CCS_Subst_prefix",
                   "CCS_Subst_sum",   "CCS_Subst_par",
                   "CCS_Subst_restr", "CCS_Subst_relab",
                   "CCS_Subst_var",   "CCS_Subst_rec"],
                  CONJUNCTS CCS_Subst_def));

(* `[E'/X] E`, learnt from <holdir>/examples/lambda/basics/termScript.sml *)
val _ = overload_on ("SUB", ``\E' X E. CCS_Subst E E' X``);

val _ = TeX_notation { hol = "[", TeX = ("\\ensuremath{[}", 1) };
val _ = TeX_notation { hol = "/", TeX = ("\\ensuremath{/}", 1) };
val _ = TeX_notation { hol = "]", TeX = ("\\ensuremath{]}", 1) };

(* Note that in the rec clause, if Y = X then all occurrences of Y in E are X
   and bound, so there exist no free variables X in E to be replaced with E'.
   Hence, the term rec Y E is returned.

   Below are two typical cases by CCS_Subst: *)

(* !X E E'. CCS_Subst (rec X E) E' X = rec X E (1st fixed point of CCS_Subst) *)
val CCS_Subst_rec_fix = save_thm (
   "CCS_Subst_rec_fix[simp]",
    Q.GENL [`X`, `E`, `E'`]
           (REWRITE_CONV [CCS_Subst_def] ``CCS_Subst (rec X E) E' X``));

(* !X E. CCS_Subst (var X) E X = E             (2nd fixed point of CCS_Subst) *)
val CCS_Subst_var_fix = save_thm (
   "CCS_Subst_var_fix[simp]",
    Q.GENL [`X`, `E`]
           (REWRITE_CONV [CCS_Subst_def] ``CCS_Subst (var X) E X``));

Theorem CCS_Subst_self[simp] :                    (* (3rd fixed point of CCS_Subst) *)
    !X E. CCS_Subst E (var X) X = E
Proof
    GEN_TAC >> Induct_on `E` >> RW_TAC std_ss [CCS_Subst_def]
QED

(* !t1 t2. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2) *)
val CCS_COND_CLAUSES = save_thm (
   "CCS_COND_CLAUSES", INST_TYPE [``:'a`` |-> ``:('a, 'b) CCS``] COND_CLAUSES);

(******************************************************************************)
(*                                                                            *)
(*            Definition of the transition relation for pure CCS              *)
(*                                                                            *)
(******************************************************************************)

val _ = type_abbrev_pp ("transition",
      ``:('a, 'b) CCS -> 'b Action -> ('a, 'b) CCS -> bool``);

(* Inductive definition of the transition relation TRANS for CCS.
   TRANS: CCS -> Action -> CCS -> bool
 *)
Inductive TRANS :
    (!E u.                           TRANS (prefix u E) u E) /\         (* PREFIX *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (sum E E') u E1) /\          (* SUM1 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (sum E' E) u E1) /\          (* SUM2 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (par E E') u (par E1 E')) /\ (* PAR1 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (par E' E) u (par E' E1)) /\ (* PAR2 *)
    (!E l E1 E' E2. TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2
                ==> TRANS (par E E') tau (par E1 E2)) /\                (* PAR3 *)
    (!E u E' l L.   TRANS E u E' /\ ((u = tau) \/
                                     ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
                ==> TRANS (restr L E) u (restr L E')) /\                (* RESTR *)
    (!E u E' rf.    TRANS E u E'
                ==> TRANS (relab E rf) (relabel rf u) (relab E' rf)) /\ (* RELABELING *)
    (!E u X E1.     TRANS (CCS_Subst E (rec X E) X) u E1
                ==> TRANS (rec X E) u E1)                               (* REC *)
End

val _ =
    add_rule { term_name = "TRANS", fixity = Infix (NONASSOC, 450),
        pp_elements = [ BreakSpace(1,0), TOK "--", HardSpace 0, TM, HardSpace 0,
                        TOK "->", BreakSpace(1,0) ],
        paren_style = OnlyIfNecessary,
        block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

val _ = TeX_notation { hol = "--", TeX = ("\\HOLTokenTransBegin", 1) };
val _ = TeX_notation { hol = "->", TeX = ("\\HOLTokenTransEnd", 1) };

(* The rules for the transition relation TRANS as individual theorems. *)
val [PREFIX, SUM1, SUM2, PAR1, PAR2, PAR3, RESTR, RELABELING, REC] =
    map save_thm
        (combine (["PREFIX", "SUM1", "SUM2", "PAR1", "PAR2", "PAR3", "RESTR",
                   "RELABELING", "REC"],
                  CONJUNCTS TRANS_rules));

val TRANS_IND = save_thm ("TRANS_IND",
    TRANS_ind |> (Q.SPEC `P`) |> GEN_ALL);

(* The process nil has no transitions.
   !u E. ~TRANS nil u E
 *)
val NIL_NO_TRANS = save_thm ("NIL_NO_TRANS",
    Q.GENL [`u`, `E`]
           (REWRITE_RULE [CCS_distinct]
                         (SPECL [``nil``, ``u :'b Action``, ``E :('a, 'b) CCS``] TRANS_cases)));

(* !u E. nil --u-> E <=> F *)
val NIL_NO_TRANS_EQF = save_thm (
   "NIL_NO_TRANS_EQF",
    Q.GENL [`u`, `E`] (EQF_INTRO (SPEC_ALL NIL_NO_TRANS)));

(* If a process can do an action, the process is not `nil`. *)
Theorem TRANS_IMP_NO_NIL :
    !E u E'. TRANS E u E' ==> E <> nil
Proof
    PROVE_TAC [NIL_NO_TRANS]
QED

(* An recursion variable has no transition.
   !X u E. ~TRANS (var X) u E
 *)
val VAR_NO_TRANS = save_thm ("VAR_NO_TRANS",
    Q.GENL [`X`, `u`, `E`]
           (REWRITE_RULE [CCS_distinct', CCS_11]
                         (Q.SPECL [`var X`, `u`, `E`] TRANS_cases)));

(* !u E u' E'. TRANS (prefix u E) u' E' = (u' = u) /\ (E' = E) *)
val TRANS_PREFIX_EQ = save_thm (
   "TRANS_PREFIX_EQ",
  ((Q.GENL [`u`, `E`, `u'`, `E'`]) o
   (ONCE_REWRITE_RHS_RULE [EQ_SYM_EQ]) o
   SPEC_ALL o
   (REWRITE_RULE [CCS_distinct', CCS_11]))
      (SPECL [``prefix (u :'b Action) E``, ``u' :'b Action``, ``E' :('a, 'b) CCS``]
             TRANS_cases));

(* !u E u' E'. u..E --u'-> E' ==> (u' = u) /\ (E' = E) *)
val TRANS_PREFIX = save_thm (
   "TRANS_PREFIX", EQ_IMP_LR TRANS_PREFIX_EQ);

(******************************************************************************)
(*                                                                            *)
(*                The transitions of a binary summation                       *)
(*                                                                            *)
(******************************************************************************)

(* !P P' u P''.
         P + P' --u-> P'' <=>
         (?E E'. (P = E /\ P' = E') /\ E --u-> P'') \/
          ?E E'. (P = E' /\ P' = E) /\ E --u-> P''
 *)
val SUM_cases_EQ = save_thm (
   "SUM_cases_EQ",
    Q.GENL [`P`, `P'`, `u`, `P''`]
         (REWRITE_RULE [CCS_distinct', CCS_11]
                       (SPECL [``sum P P'``, ``u :'b Action``, ``P'' :('a, 'b) CCS``]
                              TRANS_cases)));

val SUM_cases = save_thm (
   "SUM_cases", EQ_IMP_LR SUM_cases_EQ);

Theorem TRANS_SUM_EQ :
    !E E' u E''. TRANS (sum E E') u E'' <=> TRANS E u E'' \/ TRANS E' u E''
Proof
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC SUM_cases >> art [],
      (* goal 2 (of 2) *)
      STRIP_TAC >| (* 2 sub-goals here *)
      [ MATCH_MP_TAC SUM1 >> art [],
        MATCH_MP_TAC SUM2 >> art [] ] ]
QED

(* for CCS_TRANS_CONV *)
val TRANS_SUM_EQ' = store_thm (
   "TRANS_SUM_EQ'",
  ``!E1 E2 u E. TRANS (sum E1 E2) u E <=> TRANS E1 u E \/ TRANS E2 u E``,
    REWRITE_TAC [TRANS_SUM_EQ]);

val TRANS_SUM = save_thm (
   "TRANS_SUM", EQ_IMP_LR TRANS_SUM_EQ);

val TRANS_COMM_EQ = store_thm ("TRANS_COMM_EQ",
  ``!E E' E'' u. TRANS (sum E E') u E'' <=> TRANS (sum E' E) u E''``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ MATCH_MP_TAC SUM2, MATCH_MP_TAC SUM1 ] \\
      art [],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ MATCH_MP_TAC SUM2, MATCH_MP_TAC SUM1 ] \\
      art [] ]);

val TRANS_ASSOC_EQ = store_thm ("TRANS_ASSOC_EQ",
  ``!E E' E'' E1 u. TRANS (sum (sum E E') E'') u E1 <=> TRANS (sum E (sum E' E'')) u E1``,
    rpt GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC TRANS_SUM >| (* 4 sub-goals here *)
        [ MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM2 >> MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM2 >> MATCH_MP_TAC SUM1 ] \\
        art [],
        (* goal 1.2 (of 2) *)
        MATCH_MP_TAC SUM2 >> MATCH_MP_TAC SUM2 \\
        art [] ],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM1 \\
        art [],
        IMP_RES_TAC TRANS_SUM >| (* 4 sub-goals here *)
        [ MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM2,
          MATCH_MP_TAC SUM2,
          MATCH_MP_TAC SUM2 ] >> art [] ] ]);

val TRANS_ASSOC_RL = save_thm (
   "TRANS_ASSOC_RL", EQ_IMP_RL TRANS_ASSOC_EQ);

val TRANS_SUM_NIL_EQ = store_thm (
   "TRANS_SUM_NIL_EQ",
  ``!E u E'. TRANS (sum E nil) u E' <=> TRANS E u E'``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM \\
      IMP_RES_TAC NIL_NO_TRANS,
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      MATCH_MP_TAC SUM1 >> art [] ]);

(* !E u E'. E + nil --u-> E' ==> E --u-> E' *)
val TRANS_SUM_NIL = save_thm ("TRANS_SUM_NIL", EQ_IMP_LR TRANS_SUM_NIL_EQ);

val TRANS_P_SUM_P_EQ = store_thm ("TRANS_P_SUM_P_EQ",
  ``!E u E'. TRANS (sum E E) u E' = TRANS E u E'``,
    rpt GEN_TAC
 >> EQ_TAC
 >| [ DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM,
      DISCH_TAC \\
      MATCH_MP_TAC SUM1 >> art [] ]);

val TRANS_P_SUM_P = save_thm
  ("TRANS_P_SUM_P", EQ_IMP_LR TRANS_P_SUM_P_EQ);

val PAR_cases_EQ = save_thm ("PAR_cases_EQ",
    Q.GENL [`P`, `P'`, `u`, `P''`]
        (REWRITE_RULE [CCS_distinct', CCS_11]
                      (Q.SPECL [`par P P'`, `u`, `P''`] TRANS_cases)));

val PAR_cases = save_thm ("PAR_cases", EQ_IMP_LR PAR_cases_EQ);

(* NOTE: the shape of this theorem can be easily derived from above definition
   by replacing REWRITE_RULE with SIMP_RULE, however the inner existential
   variable (E1) has a different name. *)
Theorem TRANS_PAR_EQ :
    !E E' u E''. TRANS (par E E') u E'' <=>
                 (?E1. (E'' = par E1 E') /\ TRANS E u E1) \/
                 (?E1. (E'' = par E E1) /\ TRANS E' u E1) \/
                 (?E1 E2 l. (u = tau) /\ (E'' = par E1 E2) /\
                            TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2)
Proof
    rpt GEN_TAC >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* case 1 (LR) *)
      STRIP_TAC \\
      IMP_RES_TAC PAR_cases >| (* 3 sub-goals here *)
      [ (* goal 1.1 *)
        DISJ1_TAC \\
        Q.EXISTS_TAC `E1` >> art [],
        (* goal 1.2 *)
        DISJ2_TAC >> DISJ1_TAC \\
        Q.EXISTS_TAC `E1` >> art [],
        (* goal 1.3 *)
        DISJ2_TAC >> DISJ2_TAC \\
        take [`E1`, `E2`, `l`] >> art [] ],
      (* case 2 (RL) *)
      STRIP_TAC >> art [] (* 3 sub-goals, same initial tactics *)
   >| [ MATCH_MP_TAC PAR1 >> art [],
        MATCH_MP_TAC PAR2 >> art [],
        MATCH_MP_TAC PAR3 \\
        Q.EXISTS_TAC `l` >> art [] ] ]
QED

val TRANS_PAR = save_thm ("TRANS_PAR", EQ_IMP_LR TRANS_PAR_EQ);

val TRANS_PAR_P_NIL = store_thm ("TRANS_PAR_P_NIL",
  ``!E u E'. TRANS (par E nil) u E' ==> (?E''. TRANS E u E'' /\ (E' = par E'' nil))``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR
 >| [ Q.EXISTS_TAC `E1` >> art [],
      IMP_RES_TAC NIL_NO_TRANS,
      IMP_RES_TAC NIL_NO_TRANS ]);

val TRANS_PAR_NO_SYNCR = store_thm ("TRANS_PAR_NO_SYNCR",
  ``!(l :'b Label) l'. l <> COMPL l' ==>
        !E E' E''. ~(TRANS (par (prefix (label l) E) (prefix (label l') E')) tau E'')``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR (* 3 sub-goals here *)
 >| [ IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_11 \\
      CHECK_ASSUME_TAC
        (REWRITE_RULE [SYM (ASSUME ``(l'' :'b Label) = l``),
                       SYM (ASSUME ``COMPL (l'' :'b Label) = l'``), COMPL_COMPL_LAB]
                      (ASSUME ``~(l = COMPL (l' :'b Label))``)) \\
      RW_TAC bool_ss [] ]);

val RESTR_cases_EQ = save_thm (
   "RESTR_cases_EQ",
    Q.GENL [`P'`, `u`, `L`, `P`]
           (REWRITE_RULE [CCS_distinct', CCS_11, Action_distinct, Action_11]
                         (Q.SPECL [`restr L P`, `u`, `P'`] TRANS_cases)));

val RESTR_cases = save_thm (
   "RESTR_cases", EQ_IMP_LR RESTR_cases_EQ);

Theorem TRANS_RESTR_EQ :
    !E L u E'.
     TRANS (restr L E) u E' <=>
     ?E'' l. (E' = restr L E'') /\ TRANS E u E'' /\
             ((u = tau) \/ ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
Proof
  let val a1 = ASSUME ``(u :'b Action) = tau``
      and a2 = ASSUME ``u = label (l :'b Label)``
      and a3 = ASSUME ``TRANS E'' u E'''``
      and a4 = ASSUME ``TRANS E u E''``
  in
    rpt GEN_TAC
 >> EQ_TAC >| (* two goals here *)
    [ (* case 1 (LR) *)
      STRIP_TAC \\
      IMP_RES_TAC RESTR_cases \\ (* two sub-goals here, first two steps are shared *)
      take [`E'''`, `l`] >|
      [ (* goal 1.1 *)
        art [REWRITE_RULE [a1] a3],
        (* goal 1.2 *)
        art [REWRITE_RULE [a2] a3] ],
      (* case 2 (RL) *)
      STRIP_TAC >> art [] >| (* two sub-goals here *)
      [ (* sub-goal 2.1 *)
        MATCH_MP_TAC RESTR \\
        art [REWRITE_RULE [a1] a4],
        (* sub-goal 2.2 *)
        MATCH_MP_TAC RESTR \\
        Q.EXISTS_TAC `l` \\
        art [REWRITE_RULE [a2] a4] ] ]
  end
QED

val TRANS_RESTR = save_thm (
   "TRANS_RESTR", EQ_IMP_LR TRANS_RESTR_EQ);

val TRANS_P_RESTR = store_thm (
   "TRANS_P_RESTR",
  ``!E u E' L. TRANS (restr L E) u (restr L E') ==> TRANS E u E'``,
  let
      val thm = REWRITE_RULE [CCS_11] (ASSUME ``restr (L :'b Label set) E' = restr L E''``)
  in
      rpt STRIP_TAC \\
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ FILTER_ASM_REWRITE_TAC (fn t => t !~ ``(u :'b Action) = tau``) [thm],
        FILTER_ASM_REWRITE_TAC (fn t => t !~ ``(u :'b Action) = label l``) [thm]
      ]
  end);

val RESTR_NIL_NO_TRANS = store_thm ("RESTR_NIL_NO_TRANS",
  ``!(L :'b Label set) u E. ~(TRANS (restr L nil) u E)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RESTR (* two sub-goals here, but same proofs *)
 >> IMP_RES_TAC NIL_NO_TRANS);

val TRANS_IMP_NO_RESTR_NIL = store_thm ("TRANS_IMP_NO_RESTR_NIL",
  ``!E u E'. TRANS E u E' ==> !L. ~(E = restr L nil)``,
    rpt STRIP_TAC
 >> ASSUME_TAC (REWRITE_RULE [ASSUME ``E = restr L nil``]
                             (ASSUME ``TRANS E u E'``))
 >> IMP_RES_TAC RESTR_NIL_NO_TRANS);

val TRANS_RESTR_NO_NIL = store_thm ("TRANS_RESTR_NO_NIL",
  ``!E L u E'. TRANS (restr L E) u (restr L E') ==> ~(E = nil)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RESTR
 >> ASSUME_TAC (REWRITE_RULE [ASSUME ``E = nil``]
                             (ASSUME ``TRANS E u E''``))
 >> IMP_RES_TAC NIL_NO_TRANS);

val RESTR_LABEL_NO_TRANS = store_thm ("RESTR_LABEL_NO_TRANS",
  ``!(l :'b Label) L. (l IN L) \/ ((COMPL l) IN L) ==>
                      (!E u E'. ~(TRANS (restr L (prefix (label l) E)) u E'))``,
    rpt STRIP_TAC (* 2 goals here *)
 >| [ (* goal 1 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 1.1 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME ``(u :'b Action) = tau``, Action_distinct]
                        (ASSUME ``(u :'b Action) = label l``)),
        (* goal 1.2 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (MP (REWRITE_RULE
                [REWRITE_RULE [ASSUME ``(u :'b Action) = label l'``, Action_11]
                              (ASSUME ``(u :'b Action) = label l``)]
                (ASSUME ``~((l' :'b Label) IN L)``))
              (ASSUME ``(l :'b Label) IN L``)) ],
      (* goal 2 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 2.1 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME ``(u :'b Action) = tau``, Action_distinct]
                        (ASSUME ``(u :'b Action) = label l``)),
        (* goal 2.2 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (MP (REWRITE_RULE
                [REWRITE_RULE [ASSUME ``(u :'b Action) = label l'``, Action_11]
                              (ASSUME ``(u :'b Action) = label l``)]
                (ASSUME ``~((COMPL (l' :'b Label)) IN L)``))
              (ASSUME ``(COMPL (l :'b Label)) IN L``)) ] ]);

(* |- !E rf u P.
         relab E rf --u-> P <=>
         ?E' u' E'' rf'.
             ((E = E') /\ (rf = rf')) /\ (u = relabel rf' u') /\
             (P = relab E'' rf') /\ E' --u'-> E''
 *)
val RELAB_cases_EQ = save_thm
  ("RELAB_cases_EQ",
    TRANS_cases |> (Q.SPEC `relab E rf`)
                |> (REWRITE_RULE [CCS_distinct', CCS_11])
                |> (Q.SPECL [`u`, `P`])
                |> (Q.GENL [`E`, `rf`, `u`, `P`]));

val RELAB_cases = save_thm ("RELAB_cases", EQ_IMP_LR RELAB_cases_EQ);

Theorem TRANS_RELAB_EQ :
    !E rf u E'. TRANS (relab E rf) u E' <=>
                ?u' E''. (u = relabel rf u') /\
                         (E' = relab E'' rf) /\ TRANS E u' E''
Proof
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC RELAB_cases \\
      take [`u'`, `E'''`] >> art [],
      (* goal 2 (of 2) *)
      STRIP_TAC \\
      PURE_ONCE_ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC RELABELING \\
      PURE_ONCE_ASM_REWRITE_TAC [] ]
QED

val TRANS_RELAB = save_thm ("TRANS_RELAB", EQ_IMP_LR TRANS_RELAB_EQ);

val TRANS_RELAB_labl = save_thm ("TRANS_RELAB_labl",
    Q.GENL [`E`, `labl`] (Q.SPECL [`E`, `RELAB labl`] TRANS_RELAB));

val RELAB_NIL_NO_TRANS = store_thm ("RELAB_NIL_NO_TRANS",
  ``!(rf :'b Relabeling) u E. ~(TRANS (relab nil rf) u E)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RELAB
 >> IMP_RES_TAC NIL_NO_TRANS);

(* |- !X E u E'.
         rec X E --u-> E' <=>
         ?E'' X'. ((X = X') /\ (E = E'')) /\ [rec X' E''/X'] E'' --u-> E'
 *)
val REC_cases_EQ = save_thm
  ("REC_cases_EQ",
    TRANS_cases |> (Q.SPEC `rec X E`)
                |> (REWRITE_RULE [CCS_distinct', CCS_11])
                |> (Q.SPECL [`u`, `E'`])
                |> (Q.GENL [`X`, `E`, `u`, `E'`]));

val REC_cases = save_thm ("REC_cases", EQ_IMP_LR REC_cases_EQ);

Theorem TRANS_REC_EQ :
    !X E u E'. TRANS (rec X E) u E' <=> TRANS (CCS_Subst E (rec X E) X) u E'
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      PURE_ONCE_REWRITE_TAC [REC_cases_EQ] \\
      rpt STRIP_TAC \\
      PURE_ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [REC] ]
QED

val TRANS_REC = save_thm ("TRANS_REC", EQ_IMP_LR TRANS_REC_EQ);

val _ = export_theory ();
val _ = html_theory "CCS";
