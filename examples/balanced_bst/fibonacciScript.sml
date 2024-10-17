(* ------------------------------------------------------------------------- *)
(*  The Fibonacci sequence                                                   *)
(*     (see also https://en.wikipedia.org/wiki/Fibonacci_sequence)           *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory hurdUtils numLib realTheory realLib;

val _ = new_theory "fibonacci";

val num_INDUCTION = numTheory.INDUCTION;
val ARITH_RULE    = numLib.DECIDE;

(* The symbol name "fib" is HOL-Light compatible (Examples/gcdrecurrence.ml) *)
Definition fib_def :
    fib (n :num) = if n = 0 then (0 :num) else
                   if n = 1 then 1 else fib (n - 1) + fib (n - 2)
End

Overload Fibonacci[inferior] = “fib”

Theorem fib :
    fib 0 = 0 /\ fib 1 = 1 /\ !n. fib(n + 2) = fib(n + 1) + fib(n)
Proof
    rpt STRIP_TAC
 >> rw [Once fib_def]
QED

Theorem FIB_EQ_0 :
    !n. fib n = 0 <=> n = 0
Proof
  HO_MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[fib] THEN
  HO_MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[fib, ARITH_RULE “SUC(SUC n) = n + 2”, ADD_EQ_0] THEN
  SIMP_TAC arith_ss[ADD1, ADD_EQ_0, fib]
QED

Theorem FIB_MONO_SUC :
    !n. fib n <= fib (SUC n)
Proof
    rpt STRIP_TAC
 >> ‘n = 0 \/ 0 < n’ by rw []
 >- simp [fib]
 >> qabbrev_tac ‘k = n - 1’
 >> ‘n = k + 1’ by rw [Abbr ‘k’]
 >> rw [ADD1, fib]
QED

(* The Golden Ratio *)
Definition golden_ratio_def :
    golden_ratio = (1 + sqrt 5) / 2
End

Overload phi[local] = “golden_ratio”

(*
Theorem Fibonacci_lower_bound :
    !n. 2 <= n ==> phi pow (n - 2) <= &fib n
Proof
    completeInduct_on ‘n’
 >> rpt STRIP_TAC
 (* special cases *) 
 >> ‘n = 2 \/ n = 3 \/ 3 < n’ by rw []
 >- (POP_ASSUM (fs o wrap) \\
     cheat)
 >> qabbrev_tac ‘k = n - 1’
 >> ‘n = k + 1’ by rw [Abbr ‘k’]
 >> POP_ASSUM (fs o wrap)
 >> POP_ASSUM K_TAC (* T *)
 >> ‘1 <= k’ by rw []
 >> Q.PAT_X_ASSUM ‘2 <= k + 1’ K_TAC

 
 >> Know ‘fib (k + 1) = fib k + fib (k - 1)’
 >- (simp [Once fib_def])
 >> Rewr
 >> ‘k <= 3 \/ 3 < k’ by rw []
 >- (‘k = 1 \/ k = 2 \/ k = 3’ by rw []
     cheat)
 >> Q_TAC (TRANS_TAC REAL_LE_TRANS)
         ‘phi pow (k - 2) + phi pow (k - 1 - 2)’
 >> reverse CONJ_TAC
 >- (‘&(fib k + fib (k - 1)) = &fib k + &fib (k - 1)’ by rw [REAL_ADD] \\
     (* POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) *)
     POP_ORW \\
     MATCH_MP_TAC REAL_LE_ADD2 \\
     CONJ_TAC
     >- (LAST_X_ASSUM irule \\
         cheat
     ...)

 >> ...
QED
 *)

Theorem Fibonacci_upper_bound :
    !n. 2 <= n ==> &fib n <= phi pow (n - 1)
Proof
    cheat
QED

(* Upper and Lower Bound of Fibonacci Number [1] *)
Theorem Fibonacci_upper_lower_bound :
    !n. 2 <= n ==> phi pow (n - 2) <= &fib n /\ &fib n <= phi pow (n - 1)
Proof
    cheat
QED

val _ = export_theory ();

(* References:

   [1] https://proofwiki.org/wiki/Upper_and_Lower_Bound_of_Fibonacci_Number

 *)
