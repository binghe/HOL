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
     hurdUtils mesonLib;

open ringTheory ringMapTheory groupMapTheory monoidTheory monoidMapTheory
     monoidOrderTheory;

val _ = new_theory "ringLib";

val _ = deprecate_int ();
val INT_ARITH = intLib.ARITH_PROVE;

(* ------------------------------------------------------------------------- *)
(* The ring operations, primitive plus subtraction as a derived operation.   *)
(* ------------------------------------------------------------------------- *)

Overload ring_carrier[local]      = “\r. r.carrier”
Overload ring_0[local]            = “\r. r.sum.id”
Overload ring_1[local]            = “\r. r.prod.id”
Overload ring_neg[local]          = “\r x. r.sum.inv x”
Overload ring_add[local]          = “\r x y. r.sum.op x y”
Overload ring_mul[local]          = “\r x y. r.prod.op x y”
Overload ring_pow[local]          = “\r x n. r.prod.exp x n”

(* |- !r. Ring r ==> ring_0 r IN ring_carrier r *)
Theorem RING_0 = ring_zero_element

(* |- !r. Ring r ==> ring_1 r IN ring_carrier r *)
Theorem RING_1 = ring_one_element

(* |- !r. Ring r ==> !x. x IN R ==> ring_neg r x IN ring_carrier r *)
Theorem RING_NEG = ring_neg_element

(* |- !r. Ring r ==> ring_neg r (ring_0 r) = ring_0 r *)
Theorem RING_NEG_0 = ring_neg_zero

(* |- !r. Ring r ==> !x. x IN R ==> !n. ring_pow r x n IN R *)
Theorem RING_POW = ring_exp_element

(* |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ring_add r x y IN R *)
Theorem RING_ADD = ring_add_element

(* |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> x - y IN R *)
Theorem RING_SUB = ring_sub_element

(* |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ring_mul r x y IN R *)
Theorem RING_MUL = ring_mult_element

(* |- !r. Ring r ==> !x. x IN R ==> ring_add r #0 x = x *)
Theorem RING_ADD_LZERO = ring_add_lzero

(* |- !r. Ring r ==> !x. x IN R ==> ring_mul r #1 x = x *)
Theorem RING_MUL_LID = ring_mult_lone

(* |- !r. Ring r ==> !x. x IN R ==> ring_mul r #0 x = #0 *)
Theorem RING_MUL_LZERO = ring_mult_lzero

(* ------------------------------------------------------------------------- *)
(* Homomorphisms etc.                                                        *)
(* ------------------------------------------------------------------------- *)

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

Theorem RING_MONOMORPHIC_IMAGE_THM :
    !r r' (f :'a -> 'b).
          Ring r /\ Ring r' /\ ring_monomorphism(r,r') f
          ==> (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> (x = y <=> x' = y')) /\
              (!x. x IN ring_carrier r
                   ==> x IN ring_carrier r /\ f x = f x) /\
              (ring_0 r IN ring_carrier r /\ f(ring_0 r) = ring_0 r') /\
              (ring_1 r IN ring_carrier r /\ f(ring_1 r) = ring_1 r') /\
              (!n. ring_of_num r n IN ring_carrier r /\
                   f(ring_of_num r n) = ring_of_num r' n) /\
              (!n. ring_of_int r n IN ring_carrier r /\
                   f(ring_of_int r n) = ring_of_int r' n) /\
              (!x x'. x IN ring_carrier r /\ f x = x'
                      ==> ring_neg r x IN ring_carrier r /\
                          f(ring_neg r x) = ring_neg r' x') /\
              (!n x x'.
                  x IN ring_carrier r /\ f x = x'
                  ==> ring_pow r x n IN ring_carrier r /\
                      f(ring_pow r x n) = ring_pow r' x' n) /\
              (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> ring_add r x y IN ring_carrier r /\
                      f(ring_add r x y) = ring_add r' x' y') /\
              (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> ring_sub r x y IN ring_carrier r /\
                      f(ring_sub r x y) = ring_sub r' x' y') /\
              (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> ring_mul r x y IN ring_carrier r /\
                      f(ring_mul r x y) = ring_mul r' x' y')
Proof
    rpt GEN_TAC >> REWRITE_TAC[ring_monomorphism]
 >> ONCE_REWRITE_TAC [DECIDE “(a /\ b /\ c /\ d ==> e) <=>
                              (d /\ a /\ b /\ c ==> e)”]
 >> MATCH_MP_TAC MONO_AND
 >> CONJ_TAC >- MESON_TAC[]
 >> METIS_TAC[RING_0, RING_1, RING_OF_NUM, RING_OF_INT, RING_NEG,
              RING_POW, RING_ADD, RING_SUB, RING_MUL,
              RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1,
              RING_HOMOMORPHISM_RING_OF_NUM, RING_HOMOMORPHISM_RING_OF_INT,
              RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_POW,
              RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_SUB,
              RING_HOMOMORPHISM_MUL]
QED

(* ------------------------------------------------------------------------- *)
(* Charaterizing trivial (zero) rings.                                       *)
(* ------------------------------------------------------------------------- *)

Definition trivial_ring :
    trivial_ring r <=> Ring r /\ ring_carrier r = {ring_0 r}
End

Theorem TRIVIAL_RING_10 :
    !r :'a ring. trivial_ring r <=> Ring r /\ ring_1 r = ring_0 r
Proof
  REWRITE_TAC[trivial_ring, EXTENSION, IN_SING] THEN
  MESON_TAC[RING_1, RING_0, RING_MUL_LID, RING_MUL_LZERO]
QED

(* ------------------------------------------------------------------------- *)
(* "Extensional" functions, mapping to a fixed value ARB outside the domain. *)
(* Even though these are still total, they're a conveniently better model    *)
(* of the partial function space (e.g. the space has the right cardinality). *)
(* ------------------------------------------------------------------------- *)

Definition EXTENSIONAL :
    EXTENSIONAL s = {f :'a -> 'b | !x. ~(x IN s) ==> f x = ARB}
End

(* ------------------------------------------------------------------------- *)
(* Restriction of a function to an EXTENSIONAL one on a subset.              *)
(* ------------------------------------------------------------------------- *)

Definition RESTRICTION :
    RESTRICTION s (f :'a -> 'b) x = if x IN s then f x else ARB
End

(* ------------------------------------------------------------------------- *)
(* General Cartesian product / dependent function space.                     *)
(* ------------------------------------------------------------------------- *)

Definition cartesian_product :
    cartesian_product k s =
        {f :'k -> 'a | EXTENSIONAL k f /\ !i. i IN k ==> f i IN s i}
End

(* ------------------------------------------------------------------------- *)

(* The negation operation (\x. RESTRICTION k (\i. ring_neg (r i) (x i))) needs
   a proof.
 *)
Definition product_ring :
    product_ring k (r :'k -> 'a ring) =
        let c = cartesian_product k (\i. ring_carrier(r i));
            g = <| carrier := c;
                   op := (\x y. RESTRICTION k (\i. ring_add (r i) (x i) (y i)));
                   id := RESTRICTION k (\i. ring_0 (r i)) |>;
            m = <| carrier := c;
                   op := (\x y. RESTRICTION k (\i. ring_mul (r i) (x i) (y i)));
                   id := RESTRICTION k (\i. ring_1 (r i)) |>
        in
          <| carrier := c; sum := g; prod := m |>
End

(*
Theorem RING_TOTALIZATION_lemma :
    !r :'a ring.
            ~(trivial_ring r) /\ INFINITE univ(:'b) /\ univ(:'a) <=_c univ(:'b)
            ==> ring_carrier(product_ring (:'b) (\i. r)) =_c univ(:'b -> bool)
Proof
      REPEAT STRIP_TAC THEN REWRITE_TAC[PRODUCT_RING] THEN
      REWRITE_TAC[CARTESIAN_PRODUCT_CONST; GSYM CARD_EXP_UNIV] THEN
      MATCH_MP_TAC CARD_EXP_ABSORB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [TRANS_TAC CARD_LE_TRANS `{ring_0 r:A,ring_1 r:A}` THEN
        CONJ_TAC THENL
         [SIMP_TAC[CARD_LE_CARD; FINITE_INSERT; FINITE_EMPTY; FINITE_BOOL;
                   CARD_BOOL; CARD_CLAUSES] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[TRIVIAL_RING_10]) THEN
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          CONV_TAC NUM_REDUCE_CONV;
          MATCH_MP_TAC CARD_LE_SUBSET THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; RING_0; RING_1]];
        TRANS_TAC CARD_LE_TRANS `(:A)` THEN
        ASM_SIMP_TAC[CARD_LE_SUBSET; SUBSET_UNIV] THEN
        TRANS_TAC CARD_LE_TRANS `(:B)` THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[CARD_EXP_CANTOR; CARD_LT_IMP_LE]])
QED

Theorem RING_TOTALIZATION :
    !r :'a ring.
          (?r' f. ring_carrier r' = (:1) /\
                  ring_monomorphism(r,r') f) \/
          (?r' f. ring_carrier r' = (:num#A->bool) /\
                  ring_monomorphism(r,r') f)
Proof
    GEN_TAC THEN ASM_CASES_TAC `trivial_ring(r:A ring)` THENL
     [DISJ1_TAC THEN EXISTS_TAC `singleton_ring one` THEN
      EXISTS_TAC `(\x. one):A->1` THEN
      ASM_SIMP_TAC[RING_MONOMORPHISM_FROM_TRIVIAL_RING;
                   RING_HOMOMORPHISM_FROM_TRIVIAL_RING] THEN
      ASM_SIMP_TAC[TRIVIAL_RING_SINGLETON_RING; SINGLETON_RING] THEN
      REWRITE_TAC[IMAGE_CONST; RING_CARRIER_NONEMPTY] THEN
      REWRITE_TAC[EXTENSION; IN_UNIV; IN_SING; FORALL_ONE_THM];
      DISJ2_TAC] THEN
    MP_TAC(snd(EQ_IMP_RULE(ISPECL
     [`product_ring (:num#A) (\i. (r:A ring))`; `(:num#A->bool)`]
     ISOMORPHIC_COPY_OF_RING))) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC lemma THEN
      ASM_REWRITE_TAC[GSYM MUL_C_UNIV; INFINITE; CARD_MUL_FINITE_EQ] THEN
      REWRITE_TAC[UNIV_NOT_EMPTY; DE_MORGAN_THM; GSYM INFINITE] THEN
      REWRITE_TAC[num_INFINITE; MUL_C_UNIV] THEN
      REWRITE_TAC[le_c] THEN EXISTS_TAC `\x:A. 0,x` THEN
      REWRITE_TAC[IN_UNIV; PAIR_EQ];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r':(num#A->bool)ring` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [isomorphic_ring]) THEN
    DISCH_THEN(X_CHOOSE_TAC `f:(num#A->A)->num#A->bool`) THEN
    EXISTS_TAC `(f:(num#A->A)->num#A->bool) o (\x i. x)` THEN
    MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN
    EXISTS_TAC `product_ring (:num#A) (\i. (r:A ring))` THEN
    REWRITE_TAC[RING_MONOMORPHISM_DIAGONAL_UNIV] THEN
    ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_MONOMORPHISM]) in
*)

val _ = export_theory();
val _ = html_theory "ringLib";