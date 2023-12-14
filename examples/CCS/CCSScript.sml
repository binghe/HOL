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

val _ = export_theory ();
val _ = html_theory "CCS";
