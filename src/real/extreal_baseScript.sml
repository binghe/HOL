(* ------------------------------------------------------------------------- *)
(* Extended Real Numbers - The base arithmetics                              *)
(*                                                                           *)
(* Original Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar (2013, 2015)   *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Updated and further enriched by Chun Tian (2018 - 2023)                   *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open metisLib combinTheory pred_setTheory res_quanTools pairTheory jrhUtils
     prim_recTheory arithmeticTheory tautLib pred_setLib hurdUtils numLib;

open realTheory realLib;

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

(* ********************************************* *)
(*     Properties of Arithmetic Operations       *)
(* ********************************************* *)

Theorem mul_rzero[simp] :
    !x :extreal. x * 0 = 0
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def,extreal_of_num_def,REAL_MUL_RZERO]
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

(*****************)
(*    Ceiling    *)
(*****************)

Definition ceiling_def :
    ceiling (Normal x) = LEAST (n:num). x <= &n
End

Theorem CEILING_LBOUND :
    !x. Normal x <= &(ceiling (Normal x))
Proof
    RW_TAC std_ss [ceiling_def]
 >> LEAST_ELIM_TAC
 >> REWRITE_TAC [SIMP_REAL_ARCH]
 >> METIS_TAC [extreal_of_num_def, extreal_le_def]
QED

Theorem CEILING_UBOUND :
    !x. (0 <= x) ==> &(ceiling (Normal x)) < (Normal x) + 1
Proof
    RW_TAC std_ss [ceiling_def, extreal_of_num_def, extreal_add_def, extreal_lt_eq]
 >> LEAST_ELIM_TAC
 >> REWRITE_TAC [SIMP_REAL_ARCH]
 >> RW_TAC real_ss []
 >> FULL_SIMP_TAC real_ss [GSYM real_lt]
 >> PAT_X_ASSUM ``!m. P`` (MP_TAC o Q.SPEC `n-1`)
 >> RW_TAC real_ss []
 >> Cases_on `n = 0` >- METIS_TAC [REAL_LET_ADD2, REAL_LT_01, REAL_ADD_RID]
 >> `0 < n` by RW_TAC real_ss []
 >> `&(n - 1) < x:real` by RW_TAC real_ss []
 >> `0 <= n-1` by RW_TAC real_ss []
 >> `0:real <= (&(n-1))` by RW_TAC real_ss []
 >> `0 < x` by METIS_TAC [REAL_LET_TRANS]
 >> Cases_on `n = 1`
 >- METIS_TAC [REAL_LE_REFL, REAL_ADD_RID, REAL_LTE_ADD2, REAL_ADD_COMM]
 >> `0 <> n-1` by RW_TAC real_ss []
 >> `&n - 1 < x` by RW_TAC real_ss [REAL_SUB]
 >> FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]
QED

val _ = export_theory();
