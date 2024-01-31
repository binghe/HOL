(* ========================================================================= *)
(*  HOL-Light's ringtheory.ml (partial, for ringLib.RING_RULE)               *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*                                                                           *)
(*  Ported to HOL4 by Chun Tian                                              *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;

open pred_setTheory cardinalTheory arithmeticTheory integerTheory intLib
     hurdUtils;

open ringTheory ringMapTheory groupMapTheory monoidMapTheory;

val _ = new_theory "ringLib";

val _ = deprecate_int ();
val INT_ARITH = intLib.ARITH_PROVE;

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

Theorem ring_homomorphism_def :
    !(f :'a -> 'b) r r'. ring_homomorphism (r,r') f <=> RingHomo f r r'
Proof
    rw []
QED

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

(* |- !r. Ring r ==> ring_0 r IN ring_carrier r *)
Theorem RING_0 = ring_zero_element

(* |- !r. Ring r ==> ring_1 r IN ring_carrier r *)
Theorem RING_1 = ring_one_element

(* |- !r. Ring r ==> !x. x IN R ==> ring_neg r x IN ring_carrier r *)
Theorem RING_NEG = ring_neg_element

(* |- !r. Ring r ==> ring_neg r (ring_0 r) = ring_0 r *)
Theorem RING_NEG_0 = ring_neg_zero

(* |- !r. Ring r ==>
          !x. x IN ring_carrier r ==> !n. ring_pow r x n IN ring_carrier r
 *)
Theorem RING_POW = ring_exp_element

(* |- !r. Ring r ==>
          !x y. x IN ring_carrier r /\ y IN ring_carrier r ==>
                ring_add r x y IN ring_carrier r
 *)
Theorem RING_ADD = ring_add_element

(* |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> x - y IN R *)
Theorem RING_SUB = ring_sub_element

(* |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ring_mul r x y IN R *)
Theorem RING_MUL = ring_mult_element

Theorem RING_HOMOMORPHISM_0 :
    !r r' (f :'a -> 'b). Ring r /\ Ring r' /\ ring_homomorphism(r,r') f ==>
                         f(ring_0 r) = ring_0 r'
Proof
    rw [ring_homo_zero]
QED

Theorem RING_HOMOMORPHISM_1 :
    !r r' (f :'a -> 'b). Ring r /\ Ring r' /\ ring_homomorphism(r,r') f ==>
                         f(ring_1 r) = ring_1 r'
Proof
    rw [ring_homo_one]
QED

Theorem RING_HOMOMORPHISM_NEG :
    !r r' (f :'a -> 'b).
        Ring r /\ Ring r' /\ ring_homomorphism(r,r') f
        ==> !x. x IN ring_carrier r
                ==> f(ring_neg r x) = ring_neg r' (f x)
Proof
    rw [ring_homo_neg]
QED

Theorem RING_HOMOMORPHISM_ADD :
    !r r' (f :'a -> 'b).
        Ring r /\ Ring r' /\ ring_homomorphism(r,r') f
        ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r
                  ==> f(ring_add r x y) = ring_add r' (f x) (f y)
Proof
    rw [ring_homo_add]
QED

Theorem RING_HOMOMORPHISM_MUL :
    !r r' (f :'a -> 'b).
        Ring r /\ Ring r' /\ ring_homomorphism(r,r') f
        ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r
                  ==> f(ring_mul r x y) = ring_mul r' (f x) (f y)
Proof
    rw [ring_homo_mult]
QED

Theorem RING_HOMOMORPHISM_SUB :
    !r r' (f :'a -> 'b).
        Ring r /\ Ring r' /\ ring_homomorphism(r,r') f
        ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r
                  ==> f(ring_sub r x y) = ring_sub r' (f x) (f y)
Proof
    rw [ring_homo_sub]
QED

Theorem RING_HOMOMORPHISM_POW :
    !r r' (f :'a -> 'b).
        Ring r /\ Ring r' /\ ring_homomorphism(r,r') f
        ==> !x n. x IN ring_carrier r
                  ==> f(ring_pow r x n) = ring_pow r' (f x) n
Proof
    rw [ring_homo_exp]
QED

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

(* |- !r. Ring r ==> !n. ring_of_num r n IN R *)
Theorem RING_OF_NUM = ring_num_element

Theorem RING_OF_INT :
     !(r:'a ring) n. Ring r ==> ring_of_int r n IN ring_carrier r
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_of_int] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [RING_NEG, RING_OF_NUM]
QED

(* |- !n. num_of_int(&n) = n *)
val NUM_OF_INT_OF_NUM = NUM_OF_INT;

Theorem RING_OF_INT_OF_NUM :
    !(r :'a ring) n. ring_of_int r (&n) = ring_of_num r n
Proof
  REWRITE_TAC[ring_of_int, INT_POS, NUM_OF_INT_OF_NUM]
QED

Theorem RING_HOMOMORPHISM_RING_OF_NUM :
    !r r' (f :'a -> 'b).
        Ring r /\ Ring r' /\ ring_homomorphism(r,r') f
        ==> !n. f(ring_of_num r n) = ring_of_num r' n
Proof
    rw [ring_homo_num]
QED

(* |- |- !x. --x = x *)
val INT_NEG_NEG = INT_NEGNEG;

(* |- !m n. &m = &n <=> m = n *)
val INT_OF_NUM_EQ = INT_INJ;

Theorem RING_OF_INT_CASES :
   (!(r :'a ring) n. ring_of_int r (&n) = ring_of_num r n) /\
   (!(r :'a ring) n. Ring r ==> ring_of_int r (-&n) = ring_neg r (ring_of_num r n))
Proof
    rpt STRIP_TAC
 >- REWRITE_TAC[RING_OF_INT_OF_NUM]
 >> REWRITE_TAC[ring_of_int, INT_ARITH ``&0:int <= - &n <=> &n:int = &0``]
 >> SIMP_TAC std_ss [INT_NEG_NEG, INT_OF_NUM_EQ, INT_NEG_0, NUM_OF_INT_OF_NUM]
 >> COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [ring_of_num, RING_NEG_0]
QED

Theorem RING_HOMOMORPHISM_RING_OF_INT :
    !r r' (f :'a -> 'b).
        Ring r /\ Ring r' /\ ring_homomorphism(r,r') f
        ==> !n. f(ring_of_int r n) = ring_of_int r' n
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ASM_SIMP_TAC std_ss [FORALL_INT_CASES, RING_OF_INT_CASES]
 >> Know ‘Ring r /\ Ring r' /\ ring_homomorphism (r,r') f’ >- art []
 >> DISCH_THEN (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_NEG))
 >> Know ‘Ring r /\ Ring r' /\ ring_homomorphism (r,r') f’ >- art []
 >> DISCH_THEN (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM))
 >> ASM_SIMP_TAC std_ss [RING_NEG, RING_OF_NUM]
QED

val _ = export_theory();
val _ = html_theory "ringLib";
