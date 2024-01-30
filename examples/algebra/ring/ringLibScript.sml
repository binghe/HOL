(* ========================================================================= *)
(*  HOL-Light's ringtheory.ml (partial, for ringLib.RING_RULE)               *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*                                                                           *)
(*  Ported to HOL4 by Chun Tian                                              *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;

open pred_setTheory cardinalTheory arithmeticTheory integerTheory hurdUtils;

open ringTheory ringMapTheory groupMapTheory monoidMapTheory;

val _ = new_theory "ringLib";

(* ------------------------------------------------------------------------- *)
(*   Translations from HOL4's ringTheory to HOL-Light's ringtheory.ml        *)
(* ------------------------------------------------------------------------- *)

Overload ring_carrier[local]      = “\r. r.carrier”
Overload ring_0[local]            = “\r. r.sum.id”
Overload ring_1[local]            = “\r. r.prod.id”
Overload ring_neg[local]          = “\r x. r.sum.inv x”
Overload ring_add[local]          = “\r x y. r.sum.op x y”
Overload ring_mul[local]          = “\r x y. r.prod.op x y”
Overload ring_pow[local]          = “\r x n. r.prod.exp x n”

Overload ring_homomorphism[local] = “\(r,s) (f :'a -> 'b). RingHomo f r s”

(* NOTE: This theorem is a definition in HOL-Light (ringtheory.ml, L4708) *)
Theorem ring_homomorphism :
   !f r r'. Ring r /\ Ring r' ==>
       (ring_homomorphism (r,r') (f :'a -> 'b) <=>
        IMAGE f (ring_carrier r) SUBSET ring_carrier r' /\
        f (ring_0 r) = ring_0 r' /\
        f (ring_1 r) = ring_1 r' /\
        (!x. x IN ring_carrier r
             ==> f(ring_neg r x) = ring_neg r' (f x)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r
               ==> f(ring_add r x y) = ring_add r' (f x) (f y)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r
               ==> f(ring_mul r x y) = ring_mul r' (f x) (f y)))
Proof
    RW_TAC std_ss [RingHomo_def]
 >> EQ_TAC >> STRIP_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      CONJ_TAC >- (rw [SUBSET_DEF] >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     ‘Group r.sum /\ Group r'.sum’ by PROVE_TAC [ring_add_group] \\
      MP_TAC (Q.SPECL [‘f’, ‘r.sum’, ‘r'.sum’] group_homo_id) >> simp [] \\
      MP_TAC (Q.SPECL [‘f’, ‘r.sum’, ‘r'.sum’] group_homo_inv) >> simp [] \\
      fs [GroupHomo_def, MonoidHomo_def],
      (* goal 2 (of 2) *)
      fs [SUBSET_DEF] \\
      CONJ_TAC >- (rpt STRIP_TAC \\
                   FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘x’ >> art []) \\
      CONJ_TAC >- (rw [GroupHomo_def] \\
                   FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘x’ >> art []) \\
      rw [MonoidHomo_def] \\
      FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘x’ >> art [] ]
QED

Definition ring_monomorphism :
    ring_monomorphism (r,r') (f :'a -> 'b) <=>
        ring_homomorphism (r,r') f /\
        !x y. x IN ring_carrier r /\ y IN ring_carrier r /\ f x = f y ==> x = y
End

(* ------------------------------------------------------------------------- *)
(* Mapping natural numbers and integers into a ring in the obvious way.      *)
(* ------------------------------------------------------------------------- *)

Overload ring_of_num[local] = “\r n. r.sum.exp (ring_1 r) n” (* ##n *)

Theorem ring_of_num :
   !r. Ring r ==> ring_of_num r (0 :num) = ring_0 r /\
                  !n. ring_of_num r (SUC n) =
                      ring_add r (ring_of_num r n) (ring_1 r)
Proof
    RW_TAC std_ss [ring_num_0]
 >> Know ‘ring_add r (ring_of_num r n) (ring_1 r) =
          ring_add r (ring_1 r) (ring_of_num r n)’
 >- (irule ring_add_comm >> rw [])
 >> Rewr'
 >> MATCH_MP_TAC ring_num_SUC >> art []
QED

Overload num_of_int[local] = “integer$Num”

Definition ring_of_int :
    ring_of_int (r :'a ring) (n :int) =
        if &0 <= n then ring_of_num r (num_of_int n)
        else ring_neg r (ring_of_num r (num_of_int (-n)))
End

val _ = export_theory();
val _ = html_theory "ringLib";
