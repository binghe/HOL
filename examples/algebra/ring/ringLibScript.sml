(* ========================================================================= *)
(*  HOL-Light's ringtheory.ml (partial)                                      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*                                                                           *)
(*  Ported to HOL4 by Chun Tian (March 2024)                                 *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;

open combinTheory pred_setTheory pred_setLib arithmeticTheory integerTheory
     intLib mesonLib hurdUtils cardinalTheory oneTheory newtypeTools;

open monoidTheory;
open groupTheory groupMapTheory ringTheory ringMapTheory;

val _ = new_theory "ringLib";

val _ = deprecate_int ();
val INT_ARITH = intLib.ARITH_PROVE;

val std_ss' = std_ss ++ PRED_SET_ss;

(* ------------------------------------------------------------------------- *)
(*  'a Ring as type bijections of a subset of 'a ring                        *)
(* ------------------------------------------------------------------------- *)

(* NOTE: The ring construction here follows ring_tybij in ringtheory.ml *)
Theorem EXISTS_Ring[local] :
    ?r. Ring r
Proof
    Q.EXISTS_TAC ‘<| carrier := {ARB};
                         sum := <| carrier := {ARB};
                                        op := (\x y. ARB);
                                        id := ARB |>;
                        prod := <| carrier := {ARB};
                                        op := (\x y. ARB);
                                        id := ARB |> |>’
 >> RW_TAC std_ss [Ring_def]
 >| [ (* goal 1 (of 2) *)
      RW_TAC std_ss [AbelianGroup_def, Group_def, Monoid_def, IN_SING,
                     monoid_invertibles_def] \\
      simp [],
      (* goal 2 (of 2) *)
      RW_TAC std_ss [AbelianMonoid_def, Monoid_def, IN_SING] ]
QED

(* This defines a new type “:'a Ring” *)
val Ring_tydef = rich_new_type {tyname = "Ring",
                                exthm = EXISTS_Ring,
                                ABS = "toRing",
                                REP = "fromRing"};

(* |- Ring (fromRing g) *)
Theorem Ring_fromRing[simp] = #termP_term_REP Ring_tydef

(* |- !r. Ring r ==> fromRing (toRing r) = r *)
Theorem from_toRing = #repabs_pseudo_id Ring_tydef

(* |- !g h. fromRing g = fromRing h <=> g = h *)
Theorem fromRing_11 = #term_REP_11 Ring_tydef |> Q.GENL [‘g’, ‘h’]

(* NOTE: this is the old Ring_tybij, returned by define_new_type_bijections. *)
val Ring_ABSREP = DB.fetch "-" "Ring_ABSREP";

(* ------------------------------------------------------------------------- *)
(* The ring operations, primitive plus subtraction as a derived operation.   *)
(* ------------------------------------------------------------------------- *)

Overload ring_carrier[local]      = “\r.     (fromRing r).carrier”
Overload ring_0[local]            = “\r.     (fromRing r).sum.id”
Overload ring_1[local]            = “\r.     (fromRing r).prod.id”
Overload ring_neg[local]          = “\r x.   (fromRing r).sum.inv x”
Overload ring_add[local]          = “\r x y. (fromRing r).sum.op x y”
Overload ring_mul[local]          = “\r x y. (fromRing r).prod.op x y”
Overload ring_pow[local]          = “\r x n. (fromRing r).prod.exp x n”
Overload ring_sub[local]          = “\r.     ring$ring_sub (fromRing r)”

(* NOTE: Now the following theorems have exactly the same statements with their
         corresponding theorems in HOL-Light.
 *)
Theorem RING_0 :
    !r. ring_0 r IN ring_carrier r
Proof
    Q.X_GEN_TAC ‘r0’
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> MATCH_MP_TAC ring_zero_element
 >> rw [Abbr ‘r’]
QED

Theorem RING_1 :
    !r. ring_1 r IN ring_carrier r
Proof
    Q.X_GEN_TAC ‘r0’
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> MATCH_MP_TAC ring_one_element
 >> rw [Abbr ‘r’]
QED

Theorem RING_NEG :
    !r x. x IN ring_carrier r ==> ring_neg r x IN ring_carrier r
Proof
    Q.X_GEN_TAC ‘r0’
 >> GEN_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> MATCH_MP_TAC ring_neg_element
 >> rw [Abbr ‘r’]
QED

Theorem RING_NEG_0 :
    !r. ring_neg r (ring_0 r) = ring_0 r
Proof
    Q.X_GEN_TAC ‘r0’
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> MATCH_MP_TAC ring_neg_zero
 >> rw [Abbr ‘r’]
QED

Theorem RING_POW :
    !r x n. x IN ring_carrier r ==> ring_pow r x n IN ring_carrier r
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_exp_element
 >> rw [Abbr ‘r’]
QED

Theorem RING_ADD :
    !r x y. x IN ring_carrier r /\ y IN ring_carrier r ==>
            ring_add r x y IN ring_carrier r
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_add_element
 >> rw [Abbr ‘r’]
QED

Theorem RING_SUB :
    !r x y. x IN ring_carrier r /\ y IN ring_carrier r ==>
            ring_sub r x y IN ring_carrier r
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_sub_element
 >> rw [Abbr ‘r’]
QED

Theorem RING_MUL :
    !r x y. x IN ring_carrier r /\ y IN ring_carrier r ==>
            ring_mul r x y IN ring_carrier r
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_mult_element
 >> rw [Abbr ‘r’]
QED

Theorem RING_ADD_LZERO :
    !r x. x IN ring_carrier r ==> ring_add r (ring_0 r) x = x
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_add_lzero
 >> rw [Abbr ‘r’]
QED

Theorem RING_ADD_SYM :
    !r x y. x IN ring_carrier r /\ y IN ring_carrier r
             ==> ring_add r x y = ring_add r y x
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_add_comm
 >> rw [Abbr ‘r’]
QED

Theorem RING_ADD_LNEG :
    !r x. x IN ring_carrier r ==> ring_add r (ring_neg r x) x = ring_0 r
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_add_lneg
 >> rw [Abbr ‘r’]
QED

Theorem RING_ADD_RNEG :
    !r x. x IN ring_carrier r ==> ring_add r x (ring_neg r x) = ring_0 r
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_add_rneg
 >> rw [Abbr ‘r’]
QED

Theorem RING_ADD_ASSOC :
    !r x y z.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> ring_add r x (ring_add r y z) = ring_add r (ring_add r x y) z
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule (GSYM ring_add_assoc)
 >> rw [Abbr ‘r’]
QED

Theorem RING_MUL_LID :
    !r x. x IN ring_carrier r ==> ring_mul r (ring_1 r) x = x
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_mult_lone
 >> rw [Abbr ‘r’]
QED

Theorem RING_MUL_LZERO :
    !r x. x IN ring_carrier r ==> ring_mul r (ring_0 r) x = ring_0 r
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_mult_lzero
 >> rw [Abbr ‘r’]
QED

Theorem RING_MUL_SYM :
    !r x y. x IN ring_carrier r /\ y IN ring_carrier r
             ==> ring_mul r x y = ring_mul r y x
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule ring_mult_comm
 >> rw [Abbr ‘r’]
QED

Theorem RING_MUL_ASSOC :
    !r x y z.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> ring_mul r x (ring_mul r y z) = ring_mul r (ring_mul r x y) z
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> irule (GSYM ring_mult_assoc)
 >> rw [Abbr ‘r’]
QED

Theorem RING_ADD_EQ_0 :
    !r x y.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_add r x y = ring_0 r <=> ring_neg r x = y)
Proof
    Q.X_GEN_TAC ‘r0’
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> ‘-x = y <=> y = -x’ by PROVE_TAC [] >> POP_ORW
 >> irule ring_add_eq_zero
 >> rw [Abbr ‘r’]
QED

Theorem RING_LNEG_UNIQUE :
    !r x y.
        x IN ring_carrier r /\ y IN ring_carrier r /\ ring_add r x y = ring_0 r
        ==> ring_neg r x = y
Proof
  MESON_TAC[RING_ADD_EQ_0]
QED

Theorem RING_RNEG_UNIQUE :
    !r x y.
        x IN ring_carrier r /\ y IN ring_carrier r /\ ring_add r x y = ring_0 r
        ==> ring_neg r y = x
Proof
  MESON_TAC[RING_ADD_EQ_0, RING_ADD_SYM]
QED

(* ------------------------------------------------------------------------- *)
(* Homomorphisms etc.                                                        *)
(* ------------------------------------------------------------------------- *)

Overload ring_homomorphism[local] =
        “\(r,s) (f :'a -> 'b). RingHomo f (fromRing r) (fromRing s)”

Theorem ring_homomorphism_def :
    !(f :'a -> 'b) r r'. ring_homomorphism (r,r') f <=>
                         RingHomo f (fromRing r) (fromRing r')
Proof
    rw []
QED

(* NOTE: This theorem is a definition in HOL-Light (ringtheory.ml, L4708) *)
Theorem ring_homomorphism :
    !f r r'.
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
    qx_genl_tac [‘f’, ‘r0’, ‘r1’]
 >> RW_TAC std_ss [RingHomo_def]
 >> Q.ABBREV_TAC ‘r  = fromRing r0’
 >> Q.ABBREV_TAC ‘r' = fromRing r1’
 >> ‘Ring r /\ Ring r'’ by rw [Abbr ‘r’, Abbr ‘r'’]
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
      CONJ_TAC >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        rw [GroupHomo_def] \\
        FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘x’ >> art [],
        (* goal 2.2 (of 2) *)
        rw [MonoidHomo_def] \\
        FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘x’ >> art [] ] ]
QED

Theorem RING_HOMOMORPHISM_0 :
    !r r' (f :'a -> 'b). ring_homomorphism(r,r') f ==> f(ring_0 r) = ring_0 r'
Proof
    qx_genl_tac [‘r0’, ‘r1’, ‘f’]
 >> rw [ring_homomorphism_def]
 >> Q.ABBREV_TAC ‘r  = fromRing r0’
 >> Q.ABBREV_TAC ‘r' = fromRing r1’
 >> ‘Ring r /\ Ring r'’ by rw [Abbr ‘r’, Abbr ‘r'’]
 >> MATCH_MP_TAC ring_homo_zero >> rw []
QED

Theorem RING_HOMOMORPHISM_1 :
    !r r' (f :'a -> 'b). ring_homomorphism(r,r') f ==> f(ring_1 r) = ring_1 r'
Proof
    qx_genl_tac [‘r0’, ‘r1’, ‘f’]
 >> rw [ring_homomorphism_def]
 >> Q.ABBREV_TAC ‘r  = fromRing r0’
 >> Q.ABBREV_TAC ‘r' = fromRing r1’
 >> ‘Ring r /\ Ring r'’ by rw [Abbr ‘r’, Abbr ‘r'’]
 >> MATCH_MP_TAC ring_homo_one >> rw []
QED

Theorem RING_HOMOMORPHISM_NEG :
    !r r' (f :'a -> 'b). ring_homomorphism(r,r') f
        ==> !x. x IN ring_carrier r
                ==> f(ring_neg r x) = ring_neg r' (f x)
Proof
    qx_genl_tac [‘r0’, ‘r1’, ‘f’]
 >> rw [ring_homomorphism_def]
 >> Q.ABBREV_TAC ‘r  = fromRing r0’
 >> Q.ABBREV_TAC ‘r' = fromRing r1’
 >> ‘Ring r /\ Ring r'’ by rw [Abbr ‘r’, Abbr ‘r'’]
 >> irule ring_homo_neg >> art []
QED

Theorem RING_HOMOMORPHISM_ADD :
    !r r' (f :'a -> 'b). ring_homomorphism(r,r') f
        ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r
                  ==> f(ring_add r x y) = ring_add r' (f x) (f y)
Proof
    qx_genl_tac [‘r0’, ‘r1’, ‘f’]
 >> rw [ring_homomorphism_def]
 >> Q.ABBREV_TAC ‘r  = fromRing r0’
 >> Q.ABBREV_TAC ‘r' = fromRing r1’
 >> ‘Ring r /\ Ring r'’ by rw [Abbr ‘r’, Abbr ‘r'’]
 >> irule ring_homo_add >> art []
QED

Theorem RING_HOMOMORPHISM_MUL :
    !r r' (f :'a -> 'b). ring_homomorphism(r,r') f
        ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r
                  ==> f(ring_mul r x y) = ring_mul r' (f x) (f y)
Proof
    qx_genl_tac [‘r0’, ‘r1’, ‘f’]
 >> rw [ring_homomorphism_def]
 >> Q.ABBREV_TAC ‘r  = fromRing r0’
 >> Q.ABBREV_TAC ‘r' = fromRing r1’
 >> ‘Ring r /\ Ring r'’ by rw [Abbr ‘r’, Abbr ‘r'’]
 >> irule ring_homo_mult >> art []
QED

Theorem RING_HOMOMORPHISM_SUB :
    !r r' (f :'a -> 'b). ring_homomorphism(r,r') f
        ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r
                  ==> f(ring_sub r x y) = ring_sub r' (f x) (f y)
Proof
    qx_genl_tac [‘r0’, ‘r1’, ‘f’]
 >> rw [ring_homomorphism_def]
 >> Q.ABBREV_TAC ‘r  = fromRing r0’
 >> Q.ABBREV_TAC ‘r' = fromRing r1’
 >> ‘Ring r /\ Ring r'’ by rw [Abbr ‘r’, Abbr ‘r'’]
 >> irule (REWRITE_RULE [ring_sub_def] ring_homo_sub) >> art []
QED

Theorem RING_HOMOMORPHISM_POW :
    !r r' (f :'a -> 'b). ring_homomorphism(r,r') f
        ==> !x n. x IN ring_carrier r
                  ==> f(ring_pow r x n) = ring_pow r' (f x) n
Proof
    qx_genl_tac [‘r0’, ‘r1’, ‘f’]
 >> rw [ring_homomorphism_def]
 >> Q.ABBREV_TAC ‘r  = fromRing r0’
 >> Q.ABBREV_TAC ‘r' = fromRing r1’
 >> ‘Ring r /\ Ring r'’ by rw [Abbr ‘r’, Abbr ‘r'’]
 >> irule ring_homo_exp >> art []
QED

Definition ring_monomorphism :
    ring_monomorphism (r,r') (f :'a -> 'b) <=>
        ring_homomorphism (r,r') f /\
        !x y. x IN ring_carrier r /\ y IN ring_carrier r /\ f x = f y ==> x = y
End

(* ------------------------------------------------------------------------- *)
(* Mapping natural numbers and integers into a ring in the obvious way.      *)
(* ------------------------------------------------------------------------- *)

Overload ring_of_num[local] =
        “\r n. (fromRing r).sum.exp (ring_1 r) n” (* ##n *)

Theorem ring_of_num :
    !r. ring_of_num r (0 :num) = ring_0 r /\
        !n. ring_of_num r (SUC n) = ring_add r (ring_of_num r n) (ring_1 r)
Proof
    Q.X_GEN_TAC ‘r0’
 >> RW_TAC std_ss [ring_num_0]
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> ‘Ring r’ by rw [Abbr ‘r’]
 >> Know ‘##n + #1 = #1 + ##n’
 >- (irule ring_add_comm >> rw [])
 >> Rewr'
 >> MATCH_MP_TAC ring_num_SUC >> art []
QED

Definition ring_of_int :
    ring_of_int (r :'a Ring) (n :int) =
        if &0 <= n then ring_of_num r (num_of_int n)
        else ring_neg r (ring_of_num r (num_of_int (-n)))
End

Theorem RING_OF_NUM :
    !r n. ring_of_num r n IN ring_carrier r
Proof
    qx_genl_tac [‘r0’, ‘n’]
 >> Q.ABBREV_TAC ‘r = fromRing r0’
 >> MATCH_MP_TAC ring_num_element
 >> rw [Abbr ‘r’]
QED

Theorem RING_OF_INT :
     !r n. ring_of_int r n IN ring_carrier r
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_of_int] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [RING_NEG, RING_OF_NUM]
QED

(* |- !n. num_of_int(&n) = n *)
Theorem NUM_OF_INT_OF_NUM = NUM_OF_INT;

Theorem RING_OF_INT_OF_NUM :
    !r n. ring_of_int r (&n) = ring_of_num r n
Proof
  REWRITE_TAC[ring_of_int, INT_POS, NUM_OF_INT_OF_NUM]
QED

Theorem RING_HOMOMORPHISM_RING_OF_NUM :
    !r r' (f :'a -> 'b). ring_homomorphism(r,r') f
        ==> !n. f(ring_of_num r n) = ring_of_num r' n
Proof
    qx_genl_tac [‘r0’, ‘r1’, ‘f’]
 >> rw [ring_homomorphism_def]
 >> Q.ABBREV_TAC ‘r  = fromRing r0’
 >> Q.ABBREV_TAC ‘r' = fromRing r1’
 >> ‘Ring r /\ Ring r'’ by rw [Abbr ‘r’, Abbr ‘r'’]
 >> irule ring_homo_num >> art []
QED

(* |- |- !x. --x = x *)
Theorem INT_NEG_NEG = INT_NEGNEG

(* |- !m n. &m = &n <=> m = n *)
Theorem INT_OF_NUM_EQ = INT_INJ

(* NOTE: The proof is a direct translation from OCaml to SML *)
Theorem RING_OF_INT_CASES :
   (!r n. ring_of_int r (&n) = ring_of_num r n) /\
   (!r n. ring_of_int r (-&n) = ring_neg r (ring_of_num r n))
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[RING_OF_INT_OF_NUM] THEN
  REWRITE_TAC[ring_of_int, INT_ARITH “0:int <= - &n <=> &n:int = &0”] THEN
  SIMP_TAC std_ss[INT_NEG_NEG, INT_OF_NUM_EQ, INT_NEG_0, NUM_OF_INT_OF_NUM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ring_of_num, RING_NEG_0]
QED

(* NOTE: The proof is a direct translation from OCaml to SML *)
Theorem RING_HOMOMORPHISM_RING_OF_INT :
    !r r' (f :'a -> 'b). ring_homomorphism(r,r') f
        ==> !n. f(ring_of_int r n) = ring_of_int r' n
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC std_ss [FORALL_INT_CASES, RING_OF_INT_CASES] THEN
  FIRST_ASSUM(fn th => ASM_SIMP_TAC std_ss
   [RING_NEG, RING_OF_NUM, MATCH_MP RING_HOMOMORPHISM_NEG th]) THEN
  FIRST_ASSUM(fn th =>
   ASM_SIMP_TAC std_ss [MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th])
QED

(* NOTE: This theorem was part of HOL-Light's RING_MONOMORPHIC_IMAGE_RULE *)
Theorem RING_MONOMORPHIC_IMAGE_RULE_THM :
    !r r' (f :'a -> 'b).
          ring_monomorphism(r,r') f
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
 >> GEN_REWRITE_TAC LAND_CONV empty_rewrites [CONJ_SYM]
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
    trivial_ring r <=> ring_carrier r = {ring_0 r}
End

Theorem TRIVIAL_RING_10 :
    !r. trivial_ring r <=> ring_1 r = ring_0 r
Proof
  REWRITE_TAC[trivial_ring, EXTENSION, IN_SING] THEN
  MESON_TAC[RING_1, RING_0, RING_MUL_LID, RING_MUL_LZERO]
QED

(* ------------------------------------------------------------------------- *)
(* General Cartesian product / dependent function space (from sets.ml)       *)
(* ------------------------------------------------------------------------- *)

Definition cartesian_product :
    cartesian_product k s =
        {f :'k -> 'a | EXTENSIONAL k f /\ !i. i IN k ==> f i IN s i}
End

Theorem IN_CARTESIAN_PRODUCT :
    !k s (x :'k -> 'a).
        x IN cartesian_product k s <=>
        EXTENSIONAL k x /\ (!i. i IN k ==> x i IN s i)
Proof
    RW_TAC std_ss' [cartesian_product]
QED

Theorem RESTRICTION_IN_CARTESIAN_PRODUCT :
    !k s (f :'k -> 'a).
        RESTRICTION k f IN cartesian_product k s <=>
        !i. i IN k ==> (f i) IN (s i)
Proof
    RW_TAC std_ss' [RESTRICTION, cartesian_product, EXTENSIONAL]
QED

(* ------------------------------------------------------------------------- *)
(* Direct products of rings                                                  *)
(* ------------------------------------------------------------------------- *)

Definition raw_product_ring_def :
    raw_product_ring k (r :'k -> 'a Ring) =
        let c = cartesian_product k (\i. ring_carrier ((r :'k -> 'a Ring) i));
            g = <| carrier := c;
                   op := (\x y. RESTRICTION k (\i. ring_add (r i) (x i) (y i)));
                   id := RESTRICTION k (\i. ring_0 (r i)) |>;
            m = <| carrier := c;
                   op := (\x y. RESTRICTION k (\i. ring_mul (r i) (x i) (y i)));
                   id := RESTRICTION k (\i. ring_1 (r i)) |>
        in
           <| carrier := c; sum := g; prod := m |>
End

Theorem Ring_raw_product_ring[local] :
    !k (r :'k -> 'a Ring). Ring (raw_product_ring k r)
Proof
    rw [raw_product_ring_def]
 >> simp [Once Ring_def]
 >> ONCE_REWRITE_TAC [CONJ_ASSOC]
 >> reverse CONJ_TAC
 >- (rw [IN_CARTESIAN_PRODUCT] \\
     rw [RESTRICTION_EXTENSION] \\
     rw [RESTRICTION_DEFINED])
 (* AbelianMonoid ... (easier) *)
 >> reverse CONJ_TAC
 >- (simp [AbelianMonoid_def] \\
     reverse CONJ_TAC
     >- (rw [IN_CARTESIAN_PRODUCT, RESTRICTION_EXTENSION] \\
         MATCH_MP_TAC RING_MUL_SYM >> rw []) \\
     rw [Once Monoid_def, IN_CARTESIAN_PRODUCT, EXTENSIONAL_RESTRICTION] >| (* 5 subgoals *)
     [ (* goal 1 (of 5) *)
       rw [RESTRICTION_DEFINED],
       (* goal 2 (of 5) *)
       rw [RESTRICTION_EXTENSION] \\
       rw [RESTRICTION_DEFINED] \\
       MATCH_MP_TAC (GSYM RING_MUL_ASSOC) >> rw [],
       (* goal 3 (of 5) *)
       rw [RESTRICTION_DEFINED],
       (* goal 4 (of 5) *)
       simp [RESTRICTION, FUN_EQ_THM] \\
       Q.X_GEN_TAC ‘i’ \\
       Cases_on ‘i IN k’ >> fs [EXTENSIONAL_def],
       (* goal 5 (of 5) *)
       simp [RESTRICTION, FUN_EQ_THM] \\
       Q.X_GEN_TAC ‘i’ \\
       Cases_on ‘i IN k’ >> fs [EXTENSIONAL_def] ])
 (* AbelianMonoid ... (harder) *)
 >> simp [AbelianGroup_def, Group_def]
 >> reverse CONJ_TAC
 >- (rw [IN_CARTESIAN_PRODUCT] \\
     rw [RESTRICTION_EXTENSION] \\
     MATCH_MP_TAC RING_ADD_SYM >> rw [])
 >> CONJ_TAC (* Monoid ... *)
 >- (rw [Once Monoid_def, IN_CARTESIAN_PRODUCT, EXTENSIONAL_RESTRICTION] >| (* 5 subgoals *)
     [ (* goal 1 (of 5) *)
       rw [RESTRICTION_DEFINED],
       (* goal 2 (of 5) *)
       rw [RESTRICTION_EXTENSION] \\
       rw [RESTRICTION_DEFINED] \\
       MATCH_MP_TAC (GSYM RING_ADD_ASSOC) >> rw [],
       (* goal 3 (of 5) *)
       rw [RESTRICTION_DEFINED],
       (* goal 4 (of 5) *)
       simp [RESTRICTION, FUN_EQ_THM] \\
       Q.X_GEN_TAC ‘i’ \\
       Cases_on ‘i IN k’ >> fs [EXTENSIONAL_def],
       (* goal 5 (of 5) *)
       simp [RESTRICTION, FUN_EQ_THM] \\
       Q.X_GEN_TAC ‘i’ \\
       Cases_on ‘i IN k’ >> fs [EXTENSIONAL_def] ])
 (* monoid_invertibles *)
 >> rw [monoid_invertibles_def] (* key *)
 >> rw [Once EXTENSION, IN_CARTESIAN_PRODUCT]
 >> EQ_TAC >> rw [] (* one goal left *)
 >> Q.EXISTS_TAC ‘RESTRICTION k (\i. ring_neg (r i) (x i))’
 >> rw [RESTRICTION_EXTENSION, EXTENSIONAL_RESTRICTION] (* 3 subgoals, same tactic *)
 >> rw [RESTRICTION_DEFINED]
QED

Definition product_ring :
    product_ring k (r :'k -> 'a Ring) = toRing (raw_product_ring k r)
End

Theorem PRODUCT_RING_NO_NEG :
   (!k (r :'k -> 'a Ring).
        ring_carrier(product_ring k r) =
          cartesian_product k (\i. ring_carrier(r i))) /\
   (!k (r :'k -> 'a Ring).
        ring_0 (product_ring k r) =
          RESTRICTION k (\i. ring_0 (r i))) /\
   (!k (r :'k -> 'a Ring).
        ring_1 (product_ring k r) =
          RESTRICTION k (\i. ring_1 (r i))) /\
   (!k (r :'k -> 'a Ring).
        ring_add (product_ring k r) =
          (\x y. RESTRICTION k (\i. ring_add (r i) (x i) (y i)))) /\
   (!k (r :'k -> 'a Ring).
        ring_mul (product_ring k r) =
          (\x y. RESTRICTION k (\i. ring_mul (r i) (x i) (y i))))
Proof
    rw [product_ring] (* 5 subgoals, same initial tactics *)
 >> ‘fromRing (toRing (raw_product_ring k r)) = raw_product_ring k r’
       by (MATCH_MP_TAC from_toRing \\
           rw [Ring_raw_product_ring])
 >> POP_ORW
 >> MP_TAC (Q.SPECL [‘k’, ‘r’] Ring_raw_product_ring)
 >> rw [raw_product_ring_def]
QED

Theorem PRODUCT_RING_NEG :
    !k (r :'k -> 'a Ring).
       !x. x IN ring_carrier (product_ring k r) ==>
           ring_neg (product_ring k r) x =
           RESTRICTION k (\i. ring_neg (r i) (x i))
Proof
    rw [product_ring]
 >> ‘fromRing (toRing (raw_product_ring k r)) = raw_product_ring k r’
       by (MATCH_MP_TAC from_toRing \\
           rw [Ring_raw_product_ring])
 >> POP_ASSUM (fs o wrap)
 >> POP_ASSUM MP_TAC
 >> MP_TAC (Q.SPECL [‘k’, ‘r’] Ring_raw_product_ring)
 >> rw [raw_product_ring_def]
 (* stage work *)
 >> fs [Once Ring_def]
 (* cleanup irrelevant assumptions *)
 >> Q.PAT_X_ASSUM ‘!x y z. P’       K_TAC
 >> Q.PAT_X_ASSUM ‘AbelianMonoid _’ K_TAC
 >> fs [AbelianGroup_def]
 (* cleanup irrelevant assumptions *)
 >> Q.PAT_X_ASSUM ‘!x y. P’         K_TAC
 >> Q.ABBREV_TAC
     ‘g = <|carrier := cartesian_product k (\i. ring_carrier (r i));
            op := (\x y. RESTRICTION k (\i. ring_add (r i) (x i) (y i)));
            id := RESTRICTION k (\i. ring_0 (r i))|>’
 (* now we know ‘x IN cartesian_product k (\i. ring_carrier (r i))’ *)
 >> fs [Group_def]
 (* applying monoid_inv_def *)
 >> MP_TAC (Q.SPECL [‘g’, ‘x’]
                    (INST_TYPE [“:'a” |-> “:'k -> 'a”] monoid_inv_def))
 >> simp []
 >> ‘g.carrier = cartesian_product k (\i. ring_carrier (r i))’
       by rw [Abbr ‘g’] >> POP_ORW
 >> rw []
 >> Q.PAT_X_ASSUM ‘g.op x (g.inv x) = g.id’ MP_TAC
 >> ‘g.op = (\x y. RESTRICTION k (\i. ring_add (r i) (x i) (y i)))’
       by rw [Abbr ‘g’] >> POP_ORW
 >> ‘g.id = RESTRICTION k (\i. ring_0 (r i))’
       by rw [Abbr ‘g’] >> POP_ORW
 >> rw [RESTRICTION_EXTENSION]
 >> fs [EXTENSIONAL_def, IN_CARTESIAN_PRODUCT]
 >> simp [FUN_EQ_THM]
 >> Q.X_GEN_TAC ‘i’
 >> reverse (Cases_on ‘i IN k’) >- rw [RESTRICTION]
 >> rw [RESTRICTION_DEFINED]
 >> Q.PAT_X_ASSUM ‘!i. i IN k ==> ring_add (r i) (x i) (g.inv x i) = ring_0 (r i)’
      (MP_TAC o (Q.SPEC ‘i’))
 >> rw []
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC RING_LNEG_UNIQUE >> rw []
QED

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
          (?r' f. ring_carrier r' = univ(:(num # 'a) -> bool)/\
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
