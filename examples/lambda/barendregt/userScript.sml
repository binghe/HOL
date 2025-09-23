open HolKernel Parse boolLib bossLib;

open basic_swapTheory termTheory appFOLDLTheory chap2Theory chap3Theory
     chap4Theory head_reductionTheory solvableTheory boehmTheory
     semi_sensibleTheory lameta_completeTheory;

val _ = new_theory "user";

Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”
Overload LAM = “term$LAM”
Overload APP = “term$APP”

Theorem term_is_norminal :
    LAM "x" (VAR "x") = LAM "y" (VAR "y")
Proof
    rw [LAM_eq_thm]
QED

val _ = export_theory ();
