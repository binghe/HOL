(* ------------------------------------------------------------------------- *)
(* Extended Real Numbers - Basic Theory                                      *)
(*                                                                           *)
(* Original Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar (2013, 2015)   *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Updated and further enriched by Chun Tian (2018 - 2023)                   *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open combinTheory pairTheory tautLib arithmeticTheory hurdUtils numLib;

open realTheory realLib iterateTheory;

val _ = new_theory "extreal_base";

Datatype : (* extreal_TY_DEF *)
    extreal = NegInf | PosInf | Normal real
End

(* INFINITY, the vertical position of UTF8.chr 0x2212 is better than "-" *)
val _ = Unicode.unicode_version {u = "+" ^ UTF8.chr 0x221E,
                                 tmnm = "PosInf"};
val _ = Unicode.unicode_version {u = UTF8.chr 0x2212 ^ UTF8.chr 0x221E,
                                 tmnm = "NegInf"};

val _ = TeX_notation {hol = "+" ^ UTF8.chr 0x221E,
                      TeX = ("\\ensuremath{+\\infty}", 1)};

val _ = TeX_notation {hol = "-" ^ UTF8.chr 0x221E,
                      TeX = ("\\ensuremath{-\\infty}", 1)};

Definition extreal_of_num_def :
    extreal_of_num n = Normal (&n)
End

(* from now on, ``0x`` is intepreted as ``0 :extreal`` *)
val _ = add_numeral_form (#"x", SOME "extreal_of_num");

Definition real_def :
    real x = if (x = NegInf) \/ (x = PosInf) then (0 :real)
             else @r. x = Normal r
End

Theorem real_normal[simp] :
    !x. real (Normal x) = x
Proof
    RW_TAC std_ss [real_def]
QED

Theorem normal_real :
    !x. x <> NegInf /\ x <> PosInf ==> (Normal (real x) = x)
Proof
    RW_TAC std_ss [real_def]
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss []
 >> Cases_on `x`
 >> METIS_TAC []
QED

Theorem extreal_cases :
    !x. (x = NegInf) \/ (x = PosInf) \/ (?r. x = Normal r)
Proof
    Cases >> RW_TAC std_ss []
QED

Theorem extreal_not_infty[simp] :
    !x. (Normal x <> NegInf) /\ (Normal x <> PosInf)
Proof
    RW_TAC std_ss []
QED

Theorem extreal_11[simp] :
    !a a'. (Normal a = Normal a') <=> (a = a')
Proof
    RW_TAC std_ss []
QED

val extreal_distinct = DB.fetch "-" "extreal_distinct";

Theorem extreal_eq_zero[simp] :
    !x. (Normal x = 0) <=> (x = 0)
Proof
    RW_TAC std_ss [extreal_of_num_def]
QED

Theorem num_not_infty[simp] :
    !n. (&n <> NegInf) /\ (&n <> PosInf)
Proof
    RW_TAC std_ss [extreal_of_num_def]
QED

Theorem real_0[simp] :
    real 0 = 0
Proof
    rw [extreal_of_num_def]
QED

(* ********************************************* *)
(*     Definitions of Arithmetic Operations      *)
(* ********************************************* *)

(* old definition, which (wrongly) allows `PosInf + NegInf = PosInf`:

val extreal_add_def = Define
  `(extreal_add (Normal x) (Normal y) = Normal (x + y)) /\
   (extreal_add PosInf a = PosInf) /\
   (extreal_add a PosInf = PosInf) /\
   (extreal_add NegInf b = NegInf) /\
   (extreal_add c NegInf = NegInf)`;

   new definition:
 *)
Definition extreal_add_def :
   (extreal_add (Normal x) (Normal y) = Normal (x + y)) /\
   (extreal_add (Normal _) a = a) /\
   (extreal_add b (Normal _) = b) /\
   (extreal_add NegInf NegInf = NegInf) /\
   (extreal_add PosInf PosInf = PosInf)
End

(* This definition never changed but is moved here to be used by extreal_sub *)
Definition extreal_ainv_def :
   (extreal_ainv NegInf = PosInf) /\
   (extreal_ainv PosInf = NegInf) /\
   (extreal_ainv (Normal x) = Normal (- x))
End

(* old definition, which (wrongly) allows `PosInf - PosInf = PosInf` and
   `NegInf - NegInf = PosInf`:

val extreal_sub_def = Define
  `(extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub PosInf a = PosInf) /\
   (extreal_sub b PosInf = NegInf) /\
   (extreal_sub NegInf NegInf = PosInf) /\
   (extreal_sub NegInf c = NegInf) /\
   (extreal_sub c NegInf = PosInf)`;

   new definition:
 *)
Definition extreal_sub :
    extreal_sub x y = extreal_add x (extreal_ainv y)
End

(* The previous definition now becomes a theorem *)
Theorem extreal_sub_def :
   (extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub PosInf (Normal x) = PosInf) /\
   (extreal_sub NegInf (Normal x) = NegInf) /\
   (extreal_sub (Normal x) NegInf = PosInf) /\
   (extreal_sub (Normal x) PosInf = NegInf) /\
   (extreal_sub NegInf PosInf = NegInf) /\
   (extreal_sub PosInf NegInf = PosInf)
Proof
   rw [extreal_sub, extreal_add_def, extreal_ainv_def, real_sub]
QED

Definition extreal_le_def :
   (extreal_le (Normal x) (Normal y) = (x <= y)) /\
   (extreal_le NegInf _ = T) /\
   (extreal_le _ PosInf = T) /\
   (extreal_le _ NegInf = F) /\
   (extreal_le PosInf _ = F)
End

Definition extreal_lt_def :
   extreal_lt x y = ~extreal_le y x
End

(* "The rationaly behind our definitions is to understand PosInf (or
    NegInf) in every instance as the limit of some (possibly each time
    different) sequence, and '0' as a bona fide zero. Then

       `0 * PosInf (or NegInf) = 0 * lim a_n = lim (0 * a_n) = lim 0 = 0`

    while expressions of the type `PosInf - PosInf` or `PosInf / PosInf`
    become `lim (a_n - b_n)` or `lim a_n / lim b_n` where two
    sequences compete and do not lead to unique results." [1, p.58]
 *)
Definition extreal_mul_def :
   (extreal_mul NegInf NegInf = PosInf) /\
   (extreal_mul NegInf PosInf = NegInf) /\
   (extreal_mul PosInf NegInf = NegInf) /\
   (extreal_mul PosInf PosInf = PosInf) /\
   (extreal_mul (Normal x) NegInf =
       (if x = 0 then (Normal 0) else (if 0 < x then NegInf else PosInf))) /\
   (extreal_mul NegInf (Normal y) =
       (if y = 0 then (Normal 0) else (if 0 < y then NegInf else PosInf))) /\
   (extreal_mul (Normal x) PosInf =
       (if x = 0 then (Normal 0) else (if 0 < x then PosInf else NegInf))) /\
   (extreal_mul PosInf (Normal y) =
       (if y = 0 then (Normal 0) else (if 0 < y then PosInf else NegInf))) /\
   (extreal_mul (Normal x) (Normal y) = Normal (x * y))
End

Overload "+"  = “extreal_add”
Overload "-"  = “extreal_sub”
Overload "*"  = “extreal_mul”
Overload "<=" = “extreal_le”

(* old definition, which allows `extreal_inv (Normal 0) = Normal 0`:

val extreal_inv_def = Define
  `(extreal_inv NegInf = Normal 0) /\
   (extreal_inv PosInf = Normal 0) /\
   (extreal_inv (Normal x) = Normal (inv x)`;

   new definition, where `extreal_inv 0` is *unspecified*:
 *)
local
  val thm = Q.prove (
     `?f. (f NegInf = Normal 0) /\
          (f PosInf = Normal 0) /\
          (!r. r <> 0 ==> (f (Normal r) = Normal (inv r)))`,
   (* proof *)
      Q.EXISTS_TAC `\x. if (x = PosInf) \/ (x = NegInf) then Normal 0
                        else if x = Normal 0 then ARB
                        else Normal (inv (real x))` \\
      RW_TAC std_ss [extreal_not_infty, real_normal]);
in
  (* |- extreal_inv NegInf = Normal 0 /\
        extreal_inv PosInf = Normal 0 /\
        !r. r <> 0 ==> extreal_inv (Normal r) = Normal (inv r)
   *)
  val extreal_inv_def = new_specification
    ("extreal_inv_def", ["extreal_inv"], thm);
end;

(* old definition, which "deliberately" allows `0 / 0 = 0` [3]
val extreal_div_def = Define
   `extreal_div x y = extreal_mul x (extreal_inv y)`;

   new definition, where `x / 0`, `PosInf / PosInf` and `NegInf / NegInf`
   are all *unspecified*:
 *)
local
  val thm = Q.prove (
     `?f. (!r. f (Normal r) PosInf = Normal 0) /\
          (!r. f (Normal r) NegInf = Normal 0) /\
          (!x r. r <> 0 ==> (f x (Normal r) = extreal_mul x (extreal_inv (Normal r))))`,
   (* proof *)
      Q.EXISTS_TAC `\x y.
        if ((y = PosInf) \/ (y = NegInf)) /\ (?r. x = Normal r) then Normal 0
        else if y = Normal 0 then ARB
        else extreal_mul x (extreal_inv y)` \\
      RW_TAC std_ss [extreal_not_infty, real_normal]);
in
  (* |- (!r. extreal_div (Normal r) PosInf = Normal 0) /\
        (!r. extreal_div (Normal r) NegInf = Normal 0) /\
        !x r. r <> 0 ==> extreal_div x (Normal r) = x * extreal_inv (Normal r)
   *)
  val extreal_div_def = new_specification
    ("extreal_div_def", ["extreal_div"], thm);
end;

Definition extreal_abs_def :
   (extreal_abs (Normal x) = Normal (abs x)) /\
   (extreal_abs _ = PosInf)
End

Definition extreal_pow_def :
   (extreal_pow (Normal a) n = Normal (a pow n)) /\
   (extreal_pow PosInf n = (if n = 0 then Normal 1 else PosInf)) /\
   (extreal_pow NegInf n =
       (if n = 0 then Normal 1 else (if (EVEN n) then PosInf else NegInf)))
End

Definition extreal_sqrt_def :
   (extreal_sqrt (Normal x) = Normal (sqrt x)) /\
   (extreal_sqrt PosInf = PosInf)
End

Overload "/"            = “extreal_div”
Overload "<"            = “extreal_lt”
Overload "~"            = “extreal_ainv”
Overload numeric_negate = “extreal_ainv”
Overload "~"            = “bool$~”
Overload "¬"            = “bool$~” (* UOK *)
Overload inv            = “extreal_inv”
Overload realinv        = “extreal_inv”
Overload abs            = “extreal_abs”
Overload pow            = “extreal_pow”
Overload sqrt           = “extreal_sqrt”

(* pow-2 integrals appear in Variances and many other probability lemmas *)
val _ = overload_on (UnicodeChars.sup_2, “\x :extreal. x pow 2”);

(* pow-3 integrals appear in Liapounov's form of the central limit theorem *)
val _ = overload_on (UnicodeChars.sup_3, “\x :extreal. x pow 3”);

(* pow-4 integrals appear in Cantelli's Strong Law of Large Numbers *)
val _ = add_rule {fixity = Suffix 2100,
                  term_name = UnicodeChars.sup_4,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK UnicodeChars.sup_4]};

val _ = overload_on (UnicodeChars.sup_4, “\x :extreal. x pow 4”);
val _ = TeX_notation {hol = UnicodeChars.sup_4,
                      TeX = ("\\HOLTokenSupFour{}", 1)};

(***************)
(*   Addition  *)
(***************)

Theorem extreal_add_eq :
    !x y. Normal x + Normal y = Normal (x + y)
Proof
    rw [extreal_add_def]
QED

(* added two antecedents due to new definition of ``extreal_add``, excluded cases are:
   1. x = NegInf /\ y = PosInf
   2. x = PosInf /\ y = NegInf *)
Theorem add_comm :
    !x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==>
          (x + y = y + x)
Proof
    Cases >> Cases_on `y`
 >> RW_TAC std_ss [extreal_add_def, REAL_ADD_COMM]
QED

Theorem add_comm_normal :
    !x y. Normal x + y = y + Normal x
Proof
    rpt STRIP_TAC
 >> Cases_on `y`
 >> RW_TAC std_ss [extreal_add_def, REAL_ADD_COMM]
QED

(* added two antecedents due to new definition of ``extreal_add``, excluded cases are:
   - all mixes of PosInf and NegInf in x, y and z.
 *)
Theorem add_assoc :
    !x y z. (x <> NegInf /\ y <> NegInf /\ z <> NegInf) \/
            (x <> PosInf /\ y <> PosInf /\ z <> PosInf) ==>
            (x + (y + z) = x + y + z)
Proof
    Cases >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_add_def, REAL_ADD_ASSOC]
QED

Theorem add_rzero[simp] :
    !x :extreal. x + 0 = x
Proof
    Cases >> METIS_TAC [extreal_add_def, extreal_of_num_def, REAL_ADD_RID]
QED

Theorem add_lzero[simp] :
    !x :extreal. 0 + x = x
Proof
    Cases >> METIS_TAC [extreal_add_def, extreal_of_num_def, REAL_ADD_LID]
QED

(* added one antecedent in the first part due to new definition of ``extreal_add`` *)
Theorem add_infty :
    (!x. x <> NegInf ==> ((x + PosInf = PosInf) /\ (PosInf + x = PosInf))) /\
    (!x. x <> PosInf ==> ((x + NegInf = NegInf) /\ (NegInf + x = NegInf)))
Proof
    RW_TAC std_ss [] >> Cases_on `x`
 >> RW_TAC std_ss [extreal_add_def, extreal_not_infty]
QED

Theorem add_not_infty :
    !x y. (x <> NegInf /\ y <> NegInf ==> x + y <> NegInf) /\
          (x <> PosInf /\ y <> PosInf ==> x + y <> PosInf)
Proof
    NTAC 2 Cases >> RW_TAC std_ss [extreal_add_def]
QED

Theorem EXTREAL_EQ_LADD :
    !x y z. x <> NegInf /\ x <> PosInf ==> ((x + y = x + z) <=> (y = z))
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_add_def, REAL_EQ_LADD]
QED

Theorem EXTREAL_EQ_RADD :
    !x y z. z <> NegInf /\ z <> PosInf ==> ((x + z = y + z) <=> (x = y))
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_add_def, REAL_EQ_RADD]
QED

Theorem extreal_double : (* cf. realTheory.REAL_DOUBLE *)
    !(x :extreal). x + x = 2 * x
Proof
    Cases
 >> rw [extreal_of_num_def, extreal_add_def, extreal_mul_def, REAL_DOUBLE]
QED

(***************)
(*    Order    *)
(***************)

Theorem extreal_not_lt :
    !x y:extreal. ~(x < y) <=> y <= x
Proof
    REWRITE_TAC [TAUT `(~a <=> b) <=> (a <=> ~b)`] THEN
    SIMP_TAC std_ss [extreal_lt_def]
QED

Theorem extreal_lt_eq :
    !x y. Normal x < Normal y <=> x < y
Proof
    METIS_TAC [extreal_lt_def, extreal_le_def, real_lt]
QED

Theorem extreal_le_eq :
    !x y. Normal x <= Normal y <=> x <= y
Proof
    METIS_TAC [extreal_le_def]
QED

Theorem le_refl[simp] :
    !x:extreal. x <= x
Proof
    Cases >> RW_TAC std_ss [extreal_le_def, REAL_LE_REFL]
QED

Theorem lt_refl[simp] :
    !x:extreal. ~(x < x)
Proof
    RW_TAC std_ss [extreal_lt_def, le_refl]
QED

Theorem le_infty :
   (!x. NegInf <= x /\ x <= PosInf) /\
   (!x. x <= NegInf <=> (x = NegInf)) /\
   (!x. PosInf <= x <=> (x = PosInf))
Proof
    RW_TAC std_ss []
 >> Cases_on `x`
 >> RW_TAC std_ss [extreal_le_def]
QED

(* NOTE: The statements of this theorem were slightly refined when moving
         here from extrealTheory. Old statements:

   |- !x y. NegInf < Normal y /\ Normal y < PosInf /\
            NegInf < PosInf /\ ~(x < NegInf) /\ ~(PosInf < x) /\
           (x <> PosInf <=> x < PosInf) /\ (x <> NegInf <=> NegInf < x)
 *)
Theorem lt_infty :
    NegInf < PosInf /\
   (!x. NegInf < Normal x /\ Normal x < PosInf) /\
   (!x. ~(x < NegInf) /\ ~(PosInf < x)) /\
   (!x. x <> PosInf <=> x < PosInf) /\
   (!x. x <> NegInf <=> NegInf < x)
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, lt_refl]
 >> Cases_on ‘x’
 >> fs [extreal_lt_def, extreal_le_def, lt_refl]
QED

Theorem lt_imp_le :
    !x y :extreal. x < y ==> x <= y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt, REAL_LT_IMP_LE]
QED

Theorem lt_imp_ne :
    !x y :extreal. x < y ==> x <> y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt, REAL_LT_IMP_NE]
QED

Theorem le_trans :
    !x y z :extreal. x <= y /\ y <= z ==> x <= z
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_le_def,le_refl]
 >> METIS_TAC [REAL_LE_TRANS]
QED

Theorem lt_trans :
    !x y z :extreal. x < y /\ y < z ==> x < z
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_lt_def, lt_refl, extreal_le_def, le_refl, GSYM real_lt]
 >> METIS_TAC [REAL_LT_TRANS]
QED

Theorem let_trans :
    !x y z:extreal. x <= y /\ y < z ==> x < z
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt,REAL_LET_TRANS]
QED

Theorem le_antisym :
    !x y :extreal. (x <= y /\ y <= x) <=> (x = y)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, le_refl, REAL_LE_ANTISYM]
QED

Theorem lt_antisym :
    !x y. ~(x < y /\ y < x)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [lt_infty, extreal_lt_eq]
 >> METIS_TAC [REAL_LT_ANTISYM, DE_MORGAN_THM]
QED

Theorem lte_trans :
    !x y z:extreal. x < y /\ y <= z ==> x < z
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt, REAL_LTE_TRANS]
QED

Theorem let_antisym :
    !x y. ~(x < y /\ y <= x)
Proof
    rpt GEN_TAC
 >> CCONTR_TAC >> fs []
 >> `x < x` by PROVE_TAC [lte_trans]
 >> PROVE_TAC [lt_refl]
QED

(* This is proved by REAL_MEAN, SIMP_REAL_ARCH and SIMP_REAL_ARCH_NEG *)
Theorem extreal_mean :
    !x y :extreal. x < y ==> ?z. x < z /\ z < y
Proof
    rpt STRIP_TAC
 >> Cases_on `y` >- fs [lt_infty]
 >- (Cases_on `x`
     >- (Q.EXISTS_TAC `Normal 0` >> REWRITE_TAC [lt_infty])
     >- fs [lt_infty] \\
     STRIP_ASSUME_TAC (Q.SPEC `r` SIMP_REAL_ARCH) \\
     Q.EXISTS_TAC `&SUC n` >> REWRITE_TAC [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC `&n` >> art [] \\
     SIMP_TAC real_ss [])
 >> Cases_on `x`
 >- (STRIP_ASSUME_TAC (Q.SPEC `r` SIMP_REAL_ARCH_NEG) \\
     Q.EXISTS_TAC `-&SUC n` \\
    `-&SUC n = Normal (-&(SUC n))` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def] \\
     POP_ORW >> REWRITE_TAC [lt_infty, extreal_lt_eq] \\
     MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC `-&n` >> art [] \\
     SIMP_TAC real_ss [])
 >- fs [lt_infty]
 >> rename1 `Normal a < Normal b`
 >> `a < b` by PROVE_TAC [extreal_lt_eq]
 >> POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP REAL_MEAN))
 >> Q.EXISTS_TAC `Normal z` >> art [extreal_lt_eq]
QED

(* NOTE: The statements of this theorem were slightly refined when moving
         here from extrealTheory. Old statements:

   |- !x. (0 <= x ==> x <> NegInf) /\ (x <= 0 ==> x <> PosInf)
*)
Theorem le_not_infty :
   (!x. 0 <= x ==> x <> NegInf) /\
   (!x. x <= 0 ==> x <> PosInf)
Proof
    NTAC 3 STRIP_TAC
 >> ONCE_REWRITE_TAC [lt_infty]
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC (Q.SPECL [`NegInf`, `0`, `x`] lte_trans) \\
      PROVE_TAC [lt_infty, num_not_infty],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC (Q.SPECL [`x`, `0`, `PosInf`] let_trans) \\
      PROVE_TAC [lt_infty, num_not_infty] ]
QED

(* |- !x. 0 <= x ==> x <> NegInf, very useful in measureTheory *)
Theorem pos_not_neginf = CONJUNCT1 le_not_infty

(* |- !x. x <= 0 ==> x <> PosInf *)
Theorem neg_not_posinf = CONJUNCT2 le_not_infty

Theorem le_total :
    !x y. x <= y \/ y <= x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, REAL_LE_TOTAL]
QED

Theorem lt_total :
    !x y. (x = y) \/ x < y \/ y < x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_lt_def, GSYM real_lt, REAL_LT_TOTAL]
QED

Theorem le_01[simp] : 0 <= 1
Proof
    RW_TAC std_ss [extreal_of_num_def, extreal_le_eq, REAL_LE_01]
QED

Theorem lt_01[simp] : 0 < 1
Proof
    RW_TAC std_ss [extreal_of_num_def, extreal_lt_eq, REAL_LT_01]
QED

Theorem ne_01[simp] : 0 <> 1
Proof
    RW_TAC std_ss [extreal_of_num_def, REAL_10]
QED

Theorem le_02[simp] : 0 <= 2
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_le_eq]
QED

Theorem lt_02[simp] : 0 < 2
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]
QED

Theorem lt_10[simp] : -1 < 0
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq, extreal_ainv_def]
QED

Theorem ne_02[simp] : 0 <> 2
Proof
    RW_TAC real_ss [extreal_of_num_def]
QED

(* NOTE: added [simp] when moving here from extrealTheory *)
Theorem le_num[simp] :
    !n:num. 0 <= &n
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_le_def]
QED

Theorem num_lt_infty[simp] :
    !n:num. &n < PosInf
Proof
    RW_TAC std_ss [extreal_of_num_def, lt_infty]
QED

Theorem lt_le :
    !x y. x < y <=> (x <= y /\ x <> y)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, lt_infty, le_infty, REAL_LT_LE]
QED

Theorem le_lt :
    !x y. (x <= y) <=> x < y \/ (x = y)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, lt_infty, le_infty, REAL_LE_LT]
QED

Theorem le_neg :
    !x y. -x <= -y <=> y <= x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, extreal_ainv_def, lt_infty, le_infty,
                   REAL_LE_NEG]
QED

Theorem lt_neg :
    !x y. -x < -y <=> y < x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, extreal_ainv_def,  lt_infty,le_infty,
                   REAL_LT_NEG]
QED

Theorem le_add :
    !x y :extreal. 0 <= x /\ 0 <= y ==> 0 <= x + y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_of_num_def, REAL_LE_ADD]
QED

Theorem lt_add :
    !x y :extreal. 0 < x /\ 0 < y ==> 0 < x + y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LT_ADD]
QED

Theorem let_add :
    !x y:extreal. 0 <= x /\ 0 < y ==> 0 < x + y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LET_ADD]
QED

Theorem lte_add :
    !x y:extreal. 0 < x /\ 0 <= y ==> 0 < x + y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LTE_ADD]
QED

Theorem le_add2 :
    !w x y z. w <= x /\ y <= z ==> w + y <= x + z
Proof
    NTAC 4 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, le_infty, le_refl]
 >> METIS_TAC [REAL_LE_ADD2]
QED

Theorem lt_add2 :
    !w x y z. w < x /\ y < z ==> w + y < x + z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_lt_eq, lt_infty, REAL_LT_ADD2]
QED

Theorem let_add2 :
    !w x y z. w <> NegInf /\ w <> PosInf /\ w <= x /\ y < z ==> w + y < x + z
Proof
    NTAC 4 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_lt_def, extreal_add_def, le_infty, le_refl]
 >> METIS_TAC [real_lt, REAL_LET_ADD2]
QED

Theorem let_add2_alt :
    !w x y z. x <> NegInf /\ x <> PosInf /\ w <= x /\ y < z ==> w + y < x + z
Proof
    NTAC 4 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_lt_def, extreal_add_def, le_infty, le_refl]
 >> METIS_TAC [real_lt, REAL_LET_ADD2]
QED

(* This theorem is newly added in extreal_baseTheory *)
Theorem le_addl :
    !x y. y <> NegInf /\ y <> PosInf ==> (y <= x + y <=> (0 <= x))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                   extreal_not_infty, REAL_LE_ADDL]
QED

Theorem le_addr :
    !x y. x <> NegInf /\ x <> PosInf ==> (x <= x + y <=> (0 <= y))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                   extreal_not_infty, REAL_LE_ADDR]
QED

Theorem le_addl_imp :
    !x y. 0 <= x ==> y <= x + y
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                   extreal_not_infty, REAL_LE_ADDL]
QED

Theorem le_addr_imp :
    !x y. 0 <= y ==> x <= x + y
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                   extreal_not_infty, REAL_LE_ADDR]
QED

Theorem le_ladd :
    !x y z. x <> NegInf /\ x <> PosInf ==> (x + y <= x + z <=> y <= z)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_LADD]
QED

Theorem le_radd :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y + x <= z + x <=> y <= z)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_RADD]
QED

Theorem le_radd_imp :
    !x y z. y <= z ==> y + x <= z + x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_RADD, le_infty, le_refl]
QED

Theorem le_ladd_imp :
    !x y z. y <= z ==> x + y <= x + z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_LADD, le_infty, le_refl]
QED

Theorem lt_ladd :
    !x y z. x <> NegInf /\ x <> PosInf ==> (x + y < x + z <=> y < z)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, extreal_lt_def, REAL_LE_LADD]
QED

Theorem lt_radd :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y + x < z + x <=> y < z)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, extreal_lt_def, REAL_LE_RADD]
QED

Theorem lt_addl :
    !x y. y <> NegInf /\ y <> PosInf ==> (y < x + y <=> 0 < x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_lt_def, extreal_le_def,
                   le_infty, extreal_of_num_def, extreal_not_infty]
 >> REAL_ARITH_TAC
QED

(* This theorem is newly added in extreal_baseTheory *)
Theorem lt_addr :
    !x y. x <> NegInf /\ x <> PosInf ==> (x < x + y <=> 0 < y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_lt_def, extreal_le_def,
                   le_infty, extreal_of_num_def, extreal_not_infty]
 >> REAL_ARITH_TAC
QED

(* NOTE: two antecedents were added due to new definitions of ‘extreal_add’ *)
Theorem le_lneg :
    !x y. ((x <> NegInf /\ y <> NegInf) \/
           (x <> PosInf /\ y <> PosInf)) ==> (-x <= y <=> 0 <= x + y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_ainv_def, extreal_le_def, extreal_add_def, extreal_sub_def,
                   le_infty, extreal_of_num_def, extreal_not_infty, REAL_LE_LNEG]
QED

Theorem let_total :
    !x y :extreal. x <= y \/ y < x
Proof
    rpt GEN_TAC
 >> STRIP_ASSUME_TAC (Q.SPECL [`x`, `y`] lt_total)
 >- (DISJ1_TAC >> REWRITE_TAC [le_lt] >> art [])
 >- (DISJ1_TAC >> MATCH_MP_TAC lt_imp_le >> art [])
 >> DISJ2_TAC >> art []
QED

Theorem lte_total :
    !x y :extreal. x < y \/ y <= x
Proof
    rpt GEN_TAC
 >> STRIP_ASSUME_TAC (Q.SPECL [`x`, `y`] lt_total)
 >- (DISJ2_TAC >> REWRITE_TAC [le_lt] >> art [])
 >- (DISJ1_TAC >> art [])
 >> DISJ2_TAC >> MATCH_MP_TAC lt_imp_le >> art []
QED

(* |- !x y. x <= 0 /\ y <= 0 ==> x + y <= 0 *)
Theorem le_add_neg =
   (Q.GENL [`x`, `y`] (REWRITE_RULE [add_rzero] (Q.SPECL [`x`, `0`, `y`, `0`] le_add2)))

(* |- !x y. x < 0 /\ y < 0 ==> x + y < 0 *)
Theorem lt_add_neg =
   (Q.GENL [`x`, `y`] (REWRITE_RULE [add_rzero] (Q.SPECL [`x`, `0`, `y`, `0`] lt_add2)))

(* |- !x y. x <> NegInf /\ x <> PosInf /\ 0 < y ==> x < x + y *)
Theorem lt_addr_imp =
   (Q.GENL [`x`, `y`]
      (REWRITE_RULE [le_refl, add_rzero] (Q.SPECL [`x`, `x`, `0`, `y`] let_add2)))

(* ------------------------------------------------------------------------- *)
(*   Substraction (often with order)                                         *)
(* ------------------------------------------------------------------------- *)

Theorem extreal_sub_eq :
    !x y. Normal x - Normal y = Normal (x - y)
Proof
    rw [extreal_sub_def]
QED

Theorem sub_rzero[simp] :
    !x :extreal. x - 0 = x
Proof
    Cases >> METIS_TAC [extreal_sub_def, extreal_of_num_def, REAL_SUB_RZERO]
QED

Theorem sub_lzero[simp] :
    !x :extreal. 0 - x = -x
Proof
    Cases
 >> METIS_TAC [extreal_ainv_def, extreal_sub_def, extreal_of_num_def, REAL_SUB_LZERO]
QED

Theorem sub_le_imp :
    !x y z. x <> NegInf /\ x <> PosInf /\ y <= z + x ==> y - x <= z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_RADD]
QED

Theorem sub_le_imp2 :
    !x y z. y <> NegInf /\ y <> PosInf /\ y <= z + x ==> y - x <= z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_RADD]
QED

Theorem le_sub_imp :
    !x y z. x <> NegInf /\ x <> PosInf /\ y + x <= z ==> y <= z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_LADD]
QED

Theorem le_sub_imp2 : (* new *)
    !x y z. z <> NegInf /\ z <> PosInf /\ y + x <= z ==> y <= z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_LADD]
QED

Theorem lt_sub_imp :
    !x y z. x <> NegInf /\ y <> NegInf /\ y + x < z ==> y < z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_ADD_SUB]
QED

Theorem lt_sub_imp' :
    !x y z. x <> PosInf /\ y <> PosInf /\ y + x < z ==> y < z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_ADD_SUB]
QED

Theorem lt_sub_imp2 : (* new *)
    !x y z. x <> NegInf /\ x <> PosInf /\ y + x < z ==> y < z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_ADD_SUB]
QED

Theorem sub_lt_imp :
    !x y z. x <> NegInf /\ x <> PosInf /\ y < z + x ==> y - x < z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_SUB_RADD]
QED

Theorem sub_lt_eq :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y - x < z <=> y < z + x)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- PROVE_TAC [sub_lt_imp]
 >> Cases_on `x` >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_SUB_RADD]
QED

Theorem sub_lt_imp2 :
    !x y z. z <> NegInf /\ z <> PosInf /\ y < z + x ==> y - x < z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_SUB_RADD]
QED

Theorem sub_zero_lt :
    !x y. x < y ==> 0 < y - x
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_SUB_LT]
QED

Theorem sub_zero_lt2 :
    !x y. x <> NegInf /\ x <> PosInf /\ 0 < y - x ==> x < y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_SUB_LT]
QED

Theorem sub_lt_zero :
    !x y. x < y ==> x - y < 0
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_SUB_RADD]
QED

Theorem sub_lt_zero2 :
    !x y. y <> NegInf /\ y <> PosInf /\ x - y < 0 ==> x < y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_SUB_RADD]
QED

(* more antecedents added *)
Theorem sub_zero_le :
    !x y. x <> NegInf /\ x <> PosInf ==> (x <= y <=> 0 <= y - x)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_SUB_LE]
QED

Theorem sub_le_zero :
    !x y. y <> NegInf /\ y <> PosInf ==> (x <= y <=> x - y <= 0)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_LE_SUB_RADD]
QED

Theorem le_sub_eq :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y <= z - x <=> y + x <= z)
Proof
    METIS_TAC [le_sub_imp, sub_lt_imp, extreal_lt_def]
QED

Theorem le_sub_eq2 :
    !x y z. z <> NegInf /\ z <> PosInf /\ x <> NegInf /\ y <> NegInf ==>
           (y <= z - x <=> y + x <= z)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, lt_infty,
                    extreal_of_num_def, extreal_not_infty, REAL_LE_SUB_LADD]
QED

Theorem sub_le_eq :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y - x <= z <=> y <= z + x)
Proof
    METIS_TAC [sub_le_imp, lt_sub_imp2, extreal_lt_def]
QED

Theorem sub_le_eq2 :
    !x y z. y <> NegInf /\ y <> PosInf /\ x <> NegInf /\ z <> NegInf ==>
           (y - x <= z <=> y <= z + x)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, lt_infty,
                    extreal_of_num_def, extreal_not_infty, REAL_LE_SUB_RADD]
QED

Theorem sub_le_switch :
    !x y z. x <> NegInf /\ x <> PosInf /\ z <> NegInf /\ z <> PosInf ==>
           (y - x <= z <=> y - z <= x)
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_le_def, le_infty, lt_infty]
 >> REAL_ARITH_TAC
QED

Theorem sub_le_switch2 :
    !x y z. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
           (y - x <= z <=> y - z <= x)
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_le_def, le_infty, lt_infty]
 >> REAL_ARITH_TAC
QED

(* more antecedents ‘x <> NegInf /\ y <> NegInf’ added *)
Theorem lt_sub :
    !x y z. x <> NegInf /\ y <> NegInf /\ z <> NegInf /\ z <> PosInf ==>
           (y + x < z <=> y < z - x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, le_infty]
 >> METIS_TAC [REAL_LE_SUB_RADD]
QED

Theorem lt_sub' :
    !x y z. x <> PosInf /\ y <> PosInf /\ z <> NegInf /\ z <> PosInf ==>
           (y + x < z <=> y < z - x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, le_infty]
 >> METIS_TAC [REAL_LE_SUB_RADD]
QED

Theorem sub_add2 :
    !x y. x <> NegInf /\ x <> PosInf ==> (x + (y - x) = y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def, REAL_SUB_ADD2]
QED

Theorem add_sub :
    !x y. y <> NegInf /\ y <> PosInf ==> (x + y - y = x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, REAL_ADD_SUB_ALT]
QED

Theorem add_sub_normal[simp] :
    !x r. x + Normal r - Normal r = x
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC add_sub
 >> REWRITE_TAC [extreal_not_infty]
QED

Theorem add_sub2 :
    !x y. y <> NegInf /\ y <> PosInf ==> (y + x - y = x)
Proof
   rpt Cases
>> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                  extreal_sub_def, REAL_ADD_SUB]
QED

Theorem sub_add :
    !x y. y <> NegInf /\ y <> PosInf ==> (x - y + y = x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, REAL_SUB_ADD]
QED

Theorem sub_add_normal[simp] :
    !x r. x - Normal r + Normal r = x
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC sub_add
 >> REWRITE_TAC [extreal_not_infty]
QED

(* NOTE: this theorem is for compatibility purposes only, cf. extreal_sub *)
Theorem extreal_sub_add :
    !x y. (x <> NegInf /\ y <> PosInf) \/ (x <> PosInf /\ y <> NegInf) ==>
          (x - y = x + -y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_ainv_def, extreal_sub_def, extreal_add_def, real_sub]
QED

Theorem sub_0 :
    !x y :extreal. (x - y = 0) ==> (x = y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, num_not_infty, extreal_of_num_def, extreal_11,
                   REAL_SUB_0]
QED

Theorem sub_eq_0 :
    !x y. x <> PosInf /\ x <> NegInf /\ (x = y) ==> (x - y = 0)
Proof
    RW_TAC std_ss []
 >> `?a. x = Normal a` by METIS_TAC [extreal_cases]
 >> ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_sub_def,
                         extreal_11, REAL_SUB_REFL]
QED

Theorem sub_not_infty :
    !x y. (x <> NegInf /\ y <> PosInf ==> x - y <> NegInf) /\
          (x <> PosInf /\ y <> NegInf ==> x - y <> PosInf)
Proof
    rpt Cases >> RW_TAC std_ss [extreal_sub_def]
QED

(* ------------------------------------------------------------------------- *)
(*   Negation                                                                *)
(* ------------------------------------------------------------------------- *)

Theorem neg_neg[simp] :
    !x. --x = x
Proof
    Cases >> RW_TAC std_ss [extreal_ainv_def, REAL_NEG_NEG]
QED

Theorem neg_0[simp] :
    -0 = 0
Proof
    RW_TAC real_ss [extreal_ainv_def, extreal_of_num_def]
QED

Theorem neg_eq0[simp] :
    !x :extreal. (-x = 0) <=> (x = 0)
Proof
    Cases
 >> RW_TAC std_ss [extreal_ainv_def, extreal_of_num_def, REAL_NEG_EQ0]
QED

Theorem eq_neg[simp] :
    !x y :extreal. (-x = -y) <=> (x = y)
Proof
    NTAC 2 Cases >> RW_TAC std_ss [extreal_ainv_def, REAL_EQ_NEG]
QED

(* NOTE: using this theorem directly in any rewriting tactics will cause a self loop,
         while (GSYM neg_minus1) is more useful in turning ‘-1 * x’ to -x.
 *)
Theorem neg_minus1 :
    !x. -x = -1 * x
Proof
    Cases
 >> RW_TAC real_ss [extreal_ainv_def, extreal_of_num_def, extreal_mul_def]
QED

(* NOTE: the original unconditional statement is recovered *)
Theorem sub_rneg :
    !x y :extreal. x - -y = x + y
Proof
    rw [extreal_sub, neg_neg]
QED

Theorem sub_lneg :
    !x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==>
          (-x - y = -(x + y))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def, REAL_SUB_LNEG]
QED

Theorem neg_add :
    !x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==>
          (-(x + y) = -x + -y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def, REAL_NEG_ADD]
QED

Theorem neg_sub :
    !x y. (x <> NegInf /\ x <> PosInf) \/ (y <> NegInf /\ y <> PosInf) ==>
          (-(x - y) = y - x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_ainv_def, REAL_NEG_SUB]
QED

Theorem le_lsub_imp :
    !x y z. y <= z ==> x - z <= x - y
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl]
 >> METIS_TAC [real_sub, REAL_LE_ADD2, REAL_LE_NEG, REAL_LE_REFL]
QED

Theorem lt_lsub_imp :
    !x y z. x <> PosInf /\ x <> NegInf /\ y < z ==> x - z < x - y
Proof
    rpt STRIP_TAC
 >> ‘?r. x = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (fs o wrap)
 >> Cases_on ‘y’ >> Cases_on ‘z’
 >> rw [extreal_sub_def, lt_infty]
 >> fs [lt_infty, lt_refl, extreal_lt_eq]
 >> RealArith.REAL_ASM_ARITH_TAC
QED

Theorem le_rsub_imp :
    !x y z. x <= y ==> x - z <= y - z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl]
 >> METIS_TAC [real_sub, REAL_LE_ADD2, REAL_LE_NEG, REAL_LE_REFL]
QED

Theorem lt_rsub_imp :
    !x y z. z <> PosInf /\ z <> NegInf /\ x < y ==> x - z < y - z
Proof
    rpt STRIP_TAC
 >> ‘?r. z = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (fs o wrap)
 >> Cases_on ‘x’ >> Cases_on ‘y’
 >> rw [extreal_sub_def, lt_infty]
 >> fs [lt_infty, lt_refl, extreal_lt_eq]
 >> RealArith.REAL_ASM_ARITH_TAC
QED

Theorem eq_sub_ladd_normal :
    !x y z. (x = y - Normal z) <=> (x + Normal z = y)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl,
                   extreal_add_def, REAL_EQ_SUB_LADD]
QED

Theorem eq_sub_radd :
    !x y z. y <> NegInf /\ y <> PosInf ==> ((x - y = z) <=> (x = z + y))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_sub_def, REAL_EQ_SUB_RADD]
QED

Theorem eq_sub_ladd :
    !x y z. z <> NegInf /\ z <> PosInf ==> ((x = y - z) <=> (x + z = y))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_sub_def, REAL_EQ_SUB_LADD]
QED

Theorem eq_sub_switch :
    !x y z. (x = Normal z - y) <=> (y = Normal z - x)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl, extreal_add_def]
 >> REAL_ARITH_TAC
QED

Theorem eq_add_sub_switch :
    !a b c d. b <> NegInf /\ b <> PosInf /\ c <> NegInf /\ c <> PosInf ==>
             ((a + b = c + d) <=> (a - c = d - b))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def,extreal_sub_def]
 >> REAL_ARITH_TAC
QED

Theorem sub_refl :
    !x. x <> NegInf /\ x <> PosInf ==> x - x = 0
Proof
    Cases >> RW_TAC real_ss [extreal_sub_def, extreal_of_num_def]
QED

Theorem sub_infty :
   (!x. x <> NegInf ==> (x - NegInf = PosInf)) /\
   (!x. x <> PosInf ==> (x - PosInf = NegInf)) /\
   (!x. x <> PosInf ==> (PosInf - x = PosInf)) /\
   (!x. x <> NegInf ==> (NegInf - x = NegInf))
Proof
    RW_TAC std_ss []
 >> Cases_on `x` >> FULL_SIMP_TAC std_ss [extreal_sub_def]
QED

(* ********************************************* *)
(*     Multiplication                            *)
(* ********************************************* *)

Theorem extreal_mul_eq :
    !x y. extreal_mul (Normal x) (Normal y) = Normal (x * y)
Proof
    rw [extreal_mul_def]
QED

Theorem mul_comm :
    !x y:extreal. x * y = y * x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_mul_def, REAL_MUL_COMM]
QED

Theorem mul_assoc :
    !x y z:extreal. x * (y * z) = x * y * z
Proof
    NTAC 3 Cases
 >> RW_TAC real_ss [extreal_mul_def, REAL_MUL_ASSOC, REAL_MUL_LZERO,
                    REAL_MUL_RZERO, REAL_ENTIRE, REAL_LT_LMUL_0, REAL_POS_NZ,
                    DE_MORGAN_THM]
 >> FULL_SIMP_TAC real_ss [DE_MORGAN_THM, REAL_NOT_LT, REAL_LT_LMUL_0, GSYM REAL_LT_LE]
 >> METIS_TAC [REAL_LT_LMUL_0_NEG, REAL_LT_RMUL_0_NEG, REAL_LT_RMUL_NEG_0,
               REAL_LT_LE, REAL_LT_GT, REAL_ENTIRE, REAL_LT_LMUL_NEG_0,
               REAL_LT_LMUL_NEG_0_NEG, REAL_LT_RMUL_0, REAL_LT_LMUL_0,
               REAL_LT_RMUL_NEG_0_NEG]
QED

Theorem mul_rzero[simp] :
    !x :extreal. x * 0 = 0
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_RZERO]
QED

Theorem mul_lzero[simp] :
    !x :extreal. 0 * x = 0
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_LZERO]
QED

Theorem mul_rone[simp] :
    !x :extreal. x * 1 = x
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_RID]
QED

Theorem mul_lone[simp] :
    !x :extreal. 1 * x = x
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_LID]
QED

Theorem entire[simp] : (* was: mul2_zero *)
    !x y :extreal. (x * y = 0) <=> (x = 0) \/ (y = 0)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_mul_def, num_not_infty, extreal_of_num_def,
                   extreal_11, REAL_ENTIRE]
QED

Theorem le_mul :
    !x y :extreal. 0 <= x /\ 0 <= y ==> 0 <= x * y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                   REAL_LE_MUL, GSYM real_lt]
 >> METIS_TAC [REAL_LT_LE, real_lte]
QED

Theorem let_mul :
    !x y :extreal. 0 <= x /\ 0 < y ==> 0 <= x * y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_le_def, extreal_lt_eq, lt_infty,
                    le_infty, le_refl, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LT_LE, REAL_LT_IMP_LE, REAL_LE_MUL]
QED

Theorem lte_mul :
    !x y :extreal. 0 < x /\ 0 <= y ==> 0 <= x * y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_le_def, extreal_lt_eq,
                    lt_infty, le_infty, le_refl, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LT_LE, REAL_LT_IMP_LE, REAL_LE_MUL]
QED

Theorem le_mul_neg :
    !x y :extreal. x <= 0 /\ y <= 0 ==> 0 <= x * y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                   REAL_LE_MUL, GSYM real_lt]
 >> METIS_TAC [REAL_LE_NEG, REAL_NEG_0, REAL_NEG_MUL2, REAL_MUL_RZERO,
               REAL_LE_MUL]
QED

Theorem mul_le :
    !x y :extreal. 0 <= x /\ y <= 0 ==> x * y <= 0
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                   REAL_LE_MUL, GSYM real_lt]
 >- METIS_TAC [REAL_LT_LE, real_lt]
 >> `0 <= -r'` by METIS_TAC [REAL_LE_NEG, REAL_NEG_0]
 >> METIS_TAC [REAL_LE_NEG, REAL_NEG_0, REAL_LE_MUL, REAL_MUL_RNEG]
QED

Theorem lt_mul :
    !x y:extreal. 0 < x /\ 0 < y ==> 0 < x * y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                   REAL_LT_MUL, lt_infty]
QED

Theorem lt_mul_neg :
    !x y :extreal. x < 0 /\ y < 0 ==> 0 < x * y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq, lt_infty, extreal_mul_def]
 >> METIS_TAC [REAL_LT_LE, real_lt, REAL_LT_NEG, REAL_NEG_0, REAL_NEG_MUL2,
               REAL_LT_MUL]
QED

Theorem mul_lt :
    !x y:extreal. 0 < x /\ y < 0 ==> x * y < 0
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                   REAL_LT_MUL, lt_infty]
 >- METIS_TAC [REAL_LT_LE, real_lt]
 >> `0 < -r'` by METIS_TAC [REAL_LT_NEG, REAL_NEG_0]
 >> METIS_TAC [REAL_MUL_RNEG, REAL_LT_MUL, REAL_LT_NEG, REAL_NEG_0]
QED

Theorem mul_let :
    !x y :extreal. 0 <= x /\ y < 0 ==> x * y <= 0
Proof
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                    lt_infty, extreal_le_def, le_refl, le_infty]
 >> METIS_TAC [REAL_LT_NEG, REAL_LT_IMP_LE, REAL_NEG_0, REAL_LE_MUL, real_lt,
               REAL_MUL_RNEG, REAL_NEG_NEG, REAL_LE_NEG, REAL_LT_LE]
QED

Theorem mul_lte :
    !x y :extreal. 0 < x /\ y <= 0 ==> x * y <= 0
Proof
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                    lt_infty, extreal_le_def, le_refl, le_infty]
 >> METIS_TAC [REAL_LT_NEG, REAL_LT_IMP_LE, REAL_NEG_0, REAL_LE_MUL,
               REAL_MUL_RNEG, REAL_NEG_NEG, REAL_LE_NEG, real_lt, REAL_LT_LE]
QED

Theorem lt_rmul :
    !x y z. 0 < z /\ z <> PosInf ==> (x * z < y * z <=> x < y)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, le_infty, lt_infty,
                    REAL_LT_REFL, REAL_LT_RMUL, extreal_of_num_def]
QED

Theorem lt_rmul_imp :
    !x y z. x < y /\ 0 < z /\ z <> PosInf ==> x * z < y * z
Proof
    METIS_TAC [lt_rmul]
QED

Theorem le_rmul :
    !x y z. 0 < z /\ z <> PosInf ==> (x * z <= y * z <=> x <= y)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_eq, extreal_mul_def, le_infty, extreal_of_num_def,
                    REAL_LE_REFL, REAL_LE_RMUL, lt_infty, extreal_lt_eq]
QED

Theorem le_rmul_imp :
    !x y z :extreal. 0 <= z /\ x <= y ==> x * z <= y * z
Proof
    RW_TAC std_ss []
 >> Cases_on `z = 0` >- RW_TAC std_ss [mul_rzero, le_refl]
 >> `0 < z` by METIS_TAC [lt_le]
 >> reverse (Cases_on ‘z = PosInf’) >- METIS_TAC [le_rmul]
 >> fs [le_infty, lt_infty, extreal_of_num_def]
 >> Cases_on `x` >> Cases_on `y`
 >> RW_TAC real_ss [extreal_le_def, extreal_lt_eq, extreal_mul_def,
                    REAL_LE_REFL, REAL_LT_REFL, GSYM real_lte, GSYM real_lt,
                    le_infty, lt_infty, extreal_of_num_def, REAL_LT_IMP_LE]
 >> FULL_SIMP_TAC std_ss [le_infty, extreal_not_infty]
 >> METIS_TAC [REAL_LT_LE, REAL_LTE_TRANS, extreal_le_eq, REAL_LET_ANTISYM]
QED

Theorem lt_mul2 :
    !x1 x2 y1 y2. 0 <= x1 /\ 0 <= y1 /\ x1 <> PosInf /\ y1 <> PosInf /\
                  x1 < x2 /\ y1 < y2 ==> x1 * y1 < x2 * y2
Proof
    RW_TAC std_ss []
 >> `0 < x2 /\ 0 < y2` by METIS_TAC [let_trans]
 >> Cases_on `x1` >> Cases_on `y1`
 >> Cases_on `x2` >> Cases_on `y2`
 >> FULL_SIMP_TAC real_ss [extreal_lt_eq, extreal_le_def, extreal_mul_def,
                           le_infty, lt_infty, real_lte, REAL_LT_MUL2,
                           extreal_of_num_def, extreal_not_infty]
 >> METIS_TAC [extreal_not_infty,lt_infty]
QED

Theorem mul_lposinf :
    !x. 0 < x ==> (PosInf * x = PosInf)
Proof
   Cases >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, lt_infty,
                            num_not_infty, extreal_lt_eq]
QED

Theorem mul_rposinf :
    !x. 0 < x ==> (x * PosInf = PosInf)
Proof
   Cases >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, lt_infty,
                            num_not_infty, extreal_lt_eq]
QED

Theorem mul_infty :
    !x. 0 < x ==> (PosInf * x = PosInf) /\ (x * PosInf = PosInf) /\
                  (NegInf * x = NegInf) /\ (x * NegInf = NegInf)
Proof
    GEN_TAC >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (Cases_on ‘x’ >> rw [extreal_mul_def] \\
     fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     PROVE_TAC [REAL_LT_ANTISYM])
 >> DISCH_TAC
 >> CONJ_TAC >- art [Once mul_comm]
 >> STRONG_CONJ_TAC
 >- (Cases_on ‘x’ >> rw [extreal_mul_def] \\
     fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     PROVE_TAC [REAL_LT_ANTISYM])
 >> REWRITE_TAC [Once mul_comm]
QED

Theorem mul_infty' :
    !x. x < 0 ==> (PosInf * x = NegInf) /\ (x * PosInf = NegInf) /\
                  (NegInf * x = PosInf) /\ (x * NegInf = PosInf)
Proof
    GEN_TAC >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (Cases_on ‘x’ >> rw [extreal_mul_def] \\
     fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     PROVE_TAC [REAL_LT_ANTISYM])
 >> DISCH_TAC
 >> CONJ_TAC >- art [Once mul_comm]
 >> STRONG_CONJ_TAC
 >- (Cases_on ‘x’ >> rw [extreal_mul_def] \\
     fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     PROVE_TAC [REAL_LT_ANTISYM])
 >> REWRITE_TAC [Once mul_comm]
QED

Theorem mul_not_infty :
   (!c y. 0 <= c /\ y <> NegInf ==> Normal (c) * y <> NegInf) /\
   (!c y. 0 <= c /\ y <> PosInf ==> Normal (c) * y <> PosInf) /\
   (!c y. c <= 0 /\ y <> NegInf ==> Normal (c) * y <> PosInf) /\
   (!c y. c <= 0 /\ y <> PosInf ==> Normal (c) * y <> NegInf)
Proof
    RW_TAC std_ss [] >> Cases_on `y`
 >> RW_TAC std_ss [extreal_mul_def, extreal_le_def]
 >> METIS_TAC [real_lte, REAL_LE_ANTISYM]
QED

Theorem mul_not_infty2 :
    !x y. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
         (x * y <> NegInf) /\ (x * y <> PosInf)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_mul_def, extreal_not_infty]
QED

(* ------------------------------------------------------------------------- *)
(*   abs-related theorems                                                    *)
(* ------------------------------------------------------------------------- *)

Theorem abs_0[simp] :
    extreal_abs 0 = 0
Proof
    METIS_TAC [extreal_abs_def, extreal_of_num_def, extreal_11, ABS_0]
QED

Theorem abs_pos[simp] :
    !x :extreal. 0 <= abs x
Proof
    Cases
 >> RW_TAC std_ss [extreal_abs_def, ABS_POS, extreal_le_def,
                   extreal_of_num_def, le_infty]
QED

Theorem abs_neg :
    !x :extreal. x < 0 ==> (abs x = -x)
Proof
    RW_TAC std_ss [extreal_lt_def]
 >> Cases_on `x`
 >- REWRITE_TAC [extreal_abs_def, extreal_ainv_def]
 >- fs [extreal_of_num_def, le_infty]
 >> fs [extreal_abs_def, extreal_of_num_def, extreal_le_eq, abs, extreal_ainv_def]
QED

(* an enhanced version of abs_neg *)
Theorem abs_neg' :
    !x :extreal. x <= 0 ==> (abs x = -x)
Proof
    RW_TAC std_ss [le_lt]
 >- (MATCH_MP_TAC abs_neg >> art [])
 >> REWRITE_TAC [abs_0, neg_0]
QED

Theorem abs_refl :
    !x :extreal. (abs x = x) <=> (0 <= x)
Proof
    Cases
 >> RW_TAC std_ss [extreal_abs_def, le_infty, extreal_of_num_def,
                   extreal_le_def, ABS_REFL]
QED

Theorem abs_abs[simp]:
    !x :extreal. abs(abs(x)) = abs(x)
Proof
    RW_TAC std_ss [abs_refl, abs_pos]
QED

Theorem abs_real :
    !x. x <> PosInf /\ x <> NegInf ==> abs (real x) = real (abs x)
Proof
    Cases >> rw [extreal_abs_def, real_normal]
QED

Theorem abs_bounds :
    !x k :extreal. abs x <= k <=> -k <= x /\ x <= k
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_abs_def, extreal_le_def, lt_infty,
                   le_infty, extreal_ainv_def, ABS_BOUNDS]
QED

Theorem abs_bounds_lt :
    !x k :extreal. abs x < k <=> -k < x /\ x < k
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_abs_def, extreal_lt_eq, lt_infty, le_infty,
                   extreal_ainv_def, ABS_BOUNDS_LT]
QED

Theorem lt_abs_bounds :
   !k x :extreal. k < abs x <=> x < -k \/ k < x
Proof
    RW_TAC std_ss [extreal_lt_def]
 >> PROVE_TAC [abs_bounds]
QED

Theorem le_abs_bounds :
   !k x :extreal. k <= abs x <=> x <= -k \/ k <= x
Proof
   METIS_TAC [extreal_lt_def, abs_bounds_lt]
QED

Theorem abs_not_infty :
    !x. x <> PosInf /\ x <> NegInf ==> abs x <> PosInf /\ abs x <> NegInf
Proof
    Q.X_GEN_TAC ‘x’ >> STRIP_TAC
 >> `?c. x = Normal c` by PROVE_TAC [extreal_cases]
 >> ASM_REWRITE_TAC [extreal_abs_def, extreal_not_infty]
QED

(* NOTE: cf. le_abs_bounds for a better version without antecedents *)
Theorem abs_unbounds :
    !x k :extreal. 0 <= k ==> (k <= abs x <=> x <= -k \/ k <= x)
Proof
    rw [le_abs_bounds]
QED

Theorem le_abs :
    !x :extreal. x <= abs x /\ -x <= abs x
Proof
    GEN_TAC
 >> `0 <= x \/ x < 0` by PROVE_TAC [let_total]
 >| [ (* goal 1 (of 2) *)
      `abs x = x` by PROVE_TAC [GSYM abs_refl] >> POP_ORW \\
      rw [le_refl] \\
      MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `0` >> art [] \\
      POP_ASSUM (REWRITE_TAC o wrap o
                  (REWRITE_RULE [Once (GSYM le_neg), neg_0])),
      (* goal 2 (of 2) *)
      IMP_RES_TAC abs_neg >> POP_ORW \\
      rw [le_refl] \\
      MATCH_MP_TAC lt_imp_le \\
      MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC `0` >> art [] \\
      POP_ASSUM (REWRITE_TAC o wrap o
                  (REWRITE_RULE [Once (GSYM lt_neg), neg_0])) ]
QED

Theorem abs_eq_0[simp] :
    !x. (abs x = 0) <=> (x = 0)
Proof
    GEN_TAC
 >> reverse EQ_TAC >- rw [abs_0]
 >> `0 <= abs x` by PROVE_TAC [abs_pos]
 >> rw [Once (GSYM le_antisym)]
 >> fs [REWRITE_RULE [neg_0, le_antisym] (Q.SPECL [`x`, `0`] abs_bounds)]
QED

Theorem abs_not_zero :
    !x. abs x <> 0 <=> x <> 0
Proof
    PROVE_TAC [abs_eq_0]
QED

Theorem abs_le_0[simp] :
    !x. abs x <= 0 <=> (x = 0)
Proof
    METIS_TAC [abs_pos, abs_eq_0, le_antisym]
QED

Theorem abs_gt_0[simp] :
    !x. 0 < abs x <=> x <> 0
Proof
    RW_TAC std_ss [Once (GSYM abs_eq_0)]
 >> STRIP_ASSUME_TAC (REWRITE_RULE [le_lt] (Q.SPEC `x` abs_pos))
 >- fs [lt_le]
 >> FULL_SIMP_TAC std_ss [lt_refl]
QED

Theorem abs_triangle :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x + y) <= abs(x) + abs(y)
Proof
    RW_TAC std_ss []
 >> Cases_on `x` >> Cases_on `y`
 >> rw [extreal_abs_def, extreal_add_def, extreal_le_eq, ABS_TRIANGLE]
QED

(* NOTE: although is possible that ‘x + y’ may be unspecific, this unspecific
         value is indeed <= PosInf
 *)
Theorem abs_triangle_full :
    !x y. abs(x + y) <= abs(x) + abs(y)
Proof
    rpt GEN_TAC
 >> Cases_on ‘x <> PosInf /\ x <> NegInf’
 >- (Cases_on ‘y <> PosInf /\ y <> NegInf’
     >- (MATCH_MP_TAC abs_triangle >> art []) \\
    ‘abs y = PosInf’ by fs [extreal_abs_def] >> POP_ORW \\
     Suff ‘abs x + PosInf = PosInf’ >- rw [le_infty] \\
     Suff ‘abs x <> NegInf’ >- METIS_TAC [add_infty] \\
     MATCH_MP_TAC pos_not_neginf >> rw [abs_pos])
 >> ‘abs x = PosInf’ by fs [extreal_abs_def] >> POP_ORW
 >> Suff ‘PosInf + abs y = PosInf’ >- rw [le_infty]
 >> Suff ‘abs y <> NegInf’ >- METIS_TAC [add_infty]
 >> MATCH_MP_TAC pos_not_neginf >> rw [abs_pos]
QED

Theorem abs_triangle_sub :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x) <= abs(y) + abs(x - y)
Proof
    RW_TAC std_ss []
 >> Cases_on `x` >> Cases_on `y`
 >> rw [extreal_abs_def, extreal_add_def, extreal_sub_def, extreal_le_eq,
        ABS_TRIANGLE_SUB]
QED

Theorem abs_triangle_sub_full :
    !x y. abs(x) <= abs(y) + abs(x - y)
Proof
    rpt GEN_TAC
 >> Cases_on ‘x <> PosInf /\ x <> NegInf’
 >- (Cases_on ‘y <> PosInf /\ y <> NegInf’
     >- (MATCH_MP_TAC abs_triangle_sub >> art []) \\
    ‘abs y = PosInf’ by fs [extreal_abs_def] >> POP_ORW \\
     Suff ‘PosInf + abs (x - y) = PosInf’ >- rw [le_infty] \\
     Suff ‘abs (x - y) <> NegInf’ >- METIS_TAC [add_infty] \\
     MATCH_MP_TAC pos_not_neginf >> rw [abs_pos])
 >> ‘abs x = PosInf’ by fs [extreal_abs_def] >> POP_ORW
 >> Cases_on ‘y’
 >> fs [extreal_abs_def, extreal_sub_def, extreal_add_def] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      Suff ‘PosInf + abs (NegInf - NegInf) = PosInf’ >- rw [le_infty] \\
      Suff ‘abs (NegInf - NegInf) <> NegInf’ >- METIS_TAC [add_infty] \\
      MATCH_MP_TAC pos_not_neginf >> rw [abs_pos],
      (* goal 2 (of 2) *)
      Suff ‘PosInf + abs (PosInf - PosInf) = PosInf’ >- rw [le_infty] \\
      Suff ‘abs (PosInf - PosInf) <> NegInf’ >- METIS_TAC [add_infty] \\
      MATCH_MP_TAC pos_not_neginf >> rw [abs_pos] ]
QED

Theorem abs_sub :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x - y) = abs(y - x)
Proof
    RW_TAC std_ss []
 >> Cases_on `x` >> Cases_on `y`
 >> rw [ABS_SUB, extreal_abs_def, extreal_sub_eq]
QED

Theorem abs_sub' :
    !x y. abs(x - y) = abs(y - x)
Proof
    rpt GEN_TAC
 >> Cases_on `x` >> Cases_on `y`
 >> rw [abs_sub, extreal_abs_def, extreal_sub_def, extreal_add_def]
QED

Theorem abs_triangle_sub' :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x) <= abs(y) + abs(y - x)
Proof
    rpt STRIP_TAC
 >> Know ‘abs (y - x) = abs (x - y)’
 >- (MATCH_MP_TAC abs_sub >> art [])
 >> Rewr'
 >> MATCH_MP_TAC abs_triangle_sub >> art []
QED

Theorem abs_triangle_sub_full' :
    !x y. abs(x) <= abs(y) + abs(y - x)
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [abs_sub']
 >> REWRITE_TAC [abs_triangle_sub_full]
QED

Theorem abs_neg_eq[simp] :
    !x :extreal. abs (-x) = abs x
Proof
    GEN_TAC
 >> ‘0 <= x \/ x < 0’ by METIS_TAC [let_total]
 >- (‘abs x = x’ by PROVE_TAC [abs_refl] >> POP_ORW \\
     fs [le_lt] >> MP_TAC (Q.SPEC ‘-x’ abs_neg) \\
    ‘-x < 0’ by METIS_TAC [lt_neg, neg_0] >> rw [neg_neg])
 >> rw [abs_neg, abs_refl]
 >> rw [Once (GSYM le_neg), neg_0]
 >> MATCH_MP_TAC lt_imp_le >> art []
QED

(* cf. realTheory.ABS_TRIANGLE_NEG *)
Theorem abs_triangle_neg :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x - y) <= abs(x) + abs(y)
Proof
    rpt STRIP_TAC
 >> Know ‘x - y = x + -y’
 >- (MATCH_MP_TAC extreal_sub_add >> art [])
 >> Rewr'
 >> ‘abs y = abs (-y)’ by rw [] >> POP_ORW
 >> MATCH_MP_TAC abs_triangle >> art []
 >> Cases_on ‘y’ >> rw [extreal_ainv_def]
QED

Theorem abs_triangle_neg_full :
    !x y. abs(x - y) <= abs(x) + abs(y)
Proof
    rpt GEN_TAC
 >> Cases_on ‘x <> PosInf /\ x <> NegInf’
 >- (Cases_on ‘y <> PosInf /\ y <> NegInf’
     >- (MATCH_MP_TAC abs_triangle_neg >> art []) \\
    ‘abs y = PosInf’ by fs [extreal_abs_def] >> POP_ORW \\
     Suff ‘abs x + PosInf = PosInf’ >- rw [le_infty] \\
     Suff ‘abs x <> NegInf’ >- METIS_TAC [add_infty] \\
     MATCH_MP_TAC pos_not_neginf >> rw [abs_pos])
 >> ‘abs x = PosInf’ by fs [extreal_abs_def] >> POP_ORW
 >> Suff ‘PosInf + abs y = PosInf’ >- rw [le_infty]
 >> Suff ‘abs y <> NegInf’ >- METIS_TAC [add_infty]
 >> MATCH_MP_TAC pos_not_neginf >> rw [abs_pos]
QED

val _ = export_theory();
