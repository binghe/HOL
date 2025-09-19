open HolKernel Parse boolLib bossLib;

open nomsetTheory basic_swapTheory NEWLib termTheory appFOLDLTheory chap2Theory
     chap3Theory horeductionTheory reductionEval solvableTheory takahashiS3Theory
     head_reductionTheory head_reductionLib standardisationTheory boehmTheory
     chap4Theory;

val _ = new_theory "user";

Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”
Overload LAM = “term$LAM”

Theorem term_is_norminal :
    LAM "x" (VAR "x") = LAM "y" (VAR "y")
Proof
    rw [LAM_eq_thm]
QED

val _ = export_theory ();
