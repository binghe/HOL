(*===========================================================================*)
(*  The Data Encryption Standard (DES) in HOL                                *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory sortingTheory pred_setTheory;

(*  DES with round function components; the bit expansion E, the S-boxes S,
    and the bit permutation P.

    +-----+                             +-----+
    | KS  | <--- KEY       MESSAGE ---> | IP  |
    +--+--+    (56-bit)    (64-bit)     +--+--+
       |                                   |
       |   u_0      (32-bit)         +-----+-----+       (32-bit)       v_0
       |    +------------------------+   split   +-----------------------+
       |    |                        +-----+-----+                       |
       +----|------------------------------------------+ k_1             |
       |   \|/      +---+      +---+      +----+      \|/      +----+    |
       |   (+) <--- | P | <--- | S | <--- | E2 | <--- (+) <--- | E1 | <--+
       |    |       +---+   ^  +---+   ^  +----+            ^  +----+    |
       |     \           (32-bit)   (48-bit)             (48-bit)       /
       |  v_1 +--------------------------+  +--------------------------+ u_1
       |                                  \/
       |                                  /\
       |  u_1 +--------------------------+  +--------------------------+ v_1
       |     /                                                          \
       +----|------------------------------------------+ k_2             |
       |   \|/      +---+      +---+      +----+      \|/      +----+    |
       |   (+) <--- | P | <--- | S | <--- | E2 | <--- (+) <--- | E1 | <--+
       |    |       +---+      +---+      +----+               +----+    |
       |     \  \-------------------- f(v_1,k_2) --------------------/  /
       |  v_2 +--------------------------+  +--------------------------+ u_2
       |                                  \/
       |                                  /\
       |      +--------------------------+  +--------------------------+
       |     /                                                          \
       |    |       - v_i = u_{i-1} (+) f(v_{i-1}, k_i)                  |
       |    .       - u_i = v_{i-1}              (i = 1 ... r - 1)       .
       |    .       - u_r = u_{r-1} (+) f(v_{r-1}, k_r)                  .
       |    .       - v_r = v_{r-1}                       (r = 16)       .
       |    |                                                            |
       +----|------------------------------------------+ k_r             |
           \|/      +---+      +---+      +----+      \|/      +----+    |
           (+) <--- | P | <--- | S | <--- | E2 | <--- (+) <--- | E1 | <--+
            |       +---+      +---+      +----+               +----+    |
            |                        +-----------+                       |
            +------------------------+   join    +-----------------------+
           u_r       (32-bit)        +-----+-----+       (32-bit)       v_r
                                           |
                                       +---+---+
                                       | IP^-1 | ---> CIPHERTEXT
                                       +-------+       (64-bit)
 *)

val _ = new_theory "des";
val _ = hide "S";

(*---------------------------------------------------------------------------*)
(* Type abbreviations                                                        *)
(*---------------------------------------------------------------------------*)

(* DES is a block cipher that operates on 64-bit blocks. Using two word32, we
   can easily *split* them into two word32 for round operations.
 *)
Type block[pp] = “:word32 # word32”

(* It uses a 56-bit key, but this is often embedded within a 64-bit block where
   one bit in eight is used as a parity bit. Using eight word8, we can easily
   retrieve 7 bits from each 8-bit group.
 *)
Type key[pp] = “:word8 # word8 # word8 # word8 # word8 # word8 # word8 # word8”

(* The 32-bit input is expanded to a 48-bit intermediate value, to be split into
   eight groups of six, and used as inputs to eight different S-boxes
 *)
Type expansion[pp] = “:word6 # word6 # word6 # word6 #
                       word6 # word6 # word6 # word6”

(* Each S-box returns four bits which, when concatenated together, give a
   32-bit intermediate quantity.
 *)
Type sbox[pp] = “:word6 -> word4”

(* DES round function *)
Type roundop[pp] = “:word32 -> word32”

(*---------------------------------------------------------------------------*)
(* Tables and S-Boxes                                                        *)
(*---------------------------------------------------------------------------*)

(* The bitwise expansion E (values are directly copied from PDF [1, p.18])

   The tables should be interpreted (as those for IP and IP^−1) in that the
   first bit of the output of E is taken from the 32nd bit of the input.

   NOTE: these "raw" data assumes the bits are 1-indexed but we use 0-indexing.
 *)
Definition E_data_def : (* 48 elements *)
    E_data = [32;  1;  2;  3;  4;  5;
               4;  5;  6;  7;  8;  9;
               8;  9; 10; 11; 12; 13;
              12; 13; 14; 15; 16; 17;
              16; 17; 18; 19; 20; 21;
              20; 21; 22; 23; 24; 25;
              24; 25; 26; 27; 28; 29;
              28; 29; 30; 31; 32;  1]
End

(* The bitwise permutation P (values are directly copied from PDF [1, p.18])

   The tables should be interpreted in that the first bit of the output of P
   is taken from the 16th bit of the input.

   NOTE: these "raw" data assumes the bits are 1-indexed but we need 0-indexing.
 *)
Definition P_data_def : (* 32 elements *)
    P_data = [16;  7; 20; 21; 29; 12; 28; 17;
               1; 15; 23; 26;  5; 18; 31; 10;
               2;  8; 24; 14; 32; 27;  3;  9;
              19; 13; 30;  6; 22; 11;  4; 25]
End

(* The DES S-boxes given in hexadecimal notation (raw values are directly
   copied from PDF [1, p.23] (then use ";0x" in place of whitespaces)

   The S-box consists of four rows labeled p0 through to p3. Each row has 16
   entries and the numbers 0 through to 15 occur once, and only once.
   Therefore each row represents a permutation of the numbers {0, ... ,15}.

   The six-bit input is split into two parts. The outer two bits are used to
   choose a row of the S-box and the inner four bits are used to pick a column
   of the S-box. The entry identified in this way gives the four bits of output
   from the S-box. see also SBox_def.
 *)
Definition S1_data_def :
    S1_data =
         [[0xe;0x4;0xd;0x1;0x2;0xf;0xb;0x8;0x3;0xa;0x6;0xc;0x5;0x9;0x0;0x7];
          [0x0;0xf;0x7;0x4;0xe;0x2;0xd;0x1;0xa;0x6;0xc;0xb;0x9;0x5;0x3;0x8];
          [0x4;0x1;0xe;0x8;0xd;0x6;0x2;0xb;0xf;0xc;0x9;0x7;0x3;0xa;0x5;0x0];
          [0xf;0xc;0x8;0x2;0x4;0x9;0x1;0x7;0x5;0xb;0x3;0xe;0xa;0x0;0x6;0xd]]
End

Definition S2_data_def :
    S2_data =
         [[0xf;0x1;0x8;0xe;0x6;0xb;0x3;0x4;0x9;0x7;0x2;0xd;0xc;0x0;0x5;0xa];
          [0x3;0xd;0x4;0x7;0xf;0x2;0x8;0xe;0xc;0x0;0x1;0xa;0x6;0x9;0xb;0x5];
          [0x0;0xe;0x7;0xb;0xa;0x4;0xd;0x1;0x5;0x8;0xc;0x6;0x9;0x3;0x2;0xf];
          [0xd;0x8;0xa;0x1;0x3;0xf;0x4;0x2;0xb;0x6;0x7;0xc;0x0;0x5;0xe;0x9]]
End

Definition S3_data_def :
    S3_data =
         [[0xa;0x0;0x9;0xe;0x6;0x3;0xf;0x5;0x1;0xd;0xc;0x7;0xb;0x4;0x2;0x8];
          [0xd;0x7;0x0;0x9;0x3;0x4;0x6;0xa;0x2;0x8;0x5;0xe;0xc;0xb;0xf;0x1];
          [0xd;0x6;0x4;0x9;0x8;0xf;0x3;0x0;0xb;0x1;0x2;0xc;0x5;0xa;0xe;0x7];
          [0x1;0xa;0xd;0x0;0x6;0x9;0x8;0x7;0x4;0xf;0xe;0x3;0xb;0x5;0x2;0xc]]
End

Definition S4_data_def :
    S4_data =
         [[0x7;0xd;0xe;0x3;0x0;0x6;0x9;0xa;0x1;0x2;0x8;0x5;0xb;0xc;0x4;0xf];
          [0xd;0x8;0xb;0x5;0x6;0xf;0x0;0x3;0x4;0x7;0x2;0xc;0x1;0xa;0xe;0x9];
          [0xa;0x6;0x9;0x0;0xc;0xb;0x7;0xd;0xf;0x1;0x3;0xe;0x5;0x2;0x8;0x4];
          [0x3;0xf;0x0;0x6;0xa;0x1;0xd;0x8;0x9;0x4;0x5;0xb;0xc;0x7;0x2;0xe]]
End

Definition S5_data_def :
    S5_data =
         [[0x2;0xc;0x4;0x1;0x7;0xa;0xb;0x6;0x8;0x5;0x3;0xf;0xd;0x0;0xe;0x9];
          [0xe;0xb;0x2;0xc;0x4;0x7;0xd;0x1;0x5;0x0;0xf;0xa;0x3;0x9;0x8;0x6];
          [0x4;0x2;0x1;0xb;0xa;0xd;0x7;0x8;0xf;0x9;0xc;0x5;0x6;0x3;0x0;0xe];
          [0xb;0x8;0xc;0x7;0x1;0xe;0x2;0xd;0x6;0xf;0x0;0x9;0xa;0x4;0x5;0x3]]
End

Definition S6_data_def :
    S6_data =
         [[0xc;0x1;0xa;0xf;0x9;0x2;0x6;0x8;0x0;0xd;0x3;0x4;0xe;0x7;0x5;0xb];
          [0xa;0xf;0x4;0x2;0x7;0xc;0x9;0x5;0x6;0x1;0xd;0xe;0x0;0xb;0x3;0x8];
          [0x9;0xe;0xf;0x5;0x2;0x8;0xc;0x3;0x7;0x0;0x4;0xa;0x1;0xd;0xb;0x6];
          [0x4;0x3;0x2;0xc;0x9;0x5;0xf;0xa;0xb;0xe;0x1;0x7;0x6;0x0;0x8;0xd]]
End

Definition S7_data_def :
    S7_data =
         [[0x4;0xb;0x2;0xe;0xf;0x0;0x8;0xd;0x3;0xc;0x9;0x7;0x5;0xa;0x6;0x1];
          [0xd;0x0;0xb;0x7;0x4;0x9;0x1;0xa;0xe;0x3;0x5;0xc;0x2;0xf;0x8;0x6];
          [0x1;0x4;0xb;0xd;0xc;0x3;0x7;0xe;0xa;0xf;0x6;0x8;0x0;0x5;0x9;0x2];
          [0x6;0xb;0xd;0x8;0x1;0x4;0xa;0x7;0x9;0x5;0x0;0xf;0xe;0x2;0x3;0xc]]
End

Definition S8_data_def :
    S8_data =
         [[0xd;0x2;0x8;0x4;0x6;0xf;0xb;0x1;0xa;0x9;0x3;0xe;0x5;0x0;0xc;0x7];
          [0x1;0xf;0xd;0x8;0xa;0x3;0x7;0x4;0xc;0x5;0x6;0xb;0x0;0xe;0x9;0x2];
          [0x7;0xb;0x4;0x1;0x9;0xc;0xe;0x2;0x0;0x6;0xa;0xd;0xf;0x3;0x5;0x8];
          [0x2;0x1;0xe;0x7;0x4;0xa;0x8;0xd;0xf;0xc;0x9;0x0;0x3;0x5;0x6;0xb]]
End

(*---------------------------------------------------------------------------*)
(*  DES Round Functions                                                      *)
(*---------------------------------------------------------------------------*)

(* The first part of E searches the expansion table given by E_data

   The purpose of ‘-1’ is to convert 1-indexed E values to 0-indexed.
 *)
Definition E1_def :
    E1 (block :word32) :word48 = FCP i. block ' (EL i E_data - 1)
End

(* The second part of E split the 48 bits into 8 groups of 6 bits

   NOTE: the lowest 6 bits are sent to S1, the next 6 bits to S2, etc.
 *)
Definition E2_def :
    E2 (block :word48) :expansion = (
      (5  ><  0) block, (* for S1 *)
      (11 ><  6) block, (* for S2 *)
      (17 >< 12) block, (* for S3 *)
      (23 >< 18) block, (* for S4 *)
      (29 >< 24) block, (* for S5 *)
      (35 >< 30) block, (* for S6 *)
      (41 >< 36) block, (* for S7 *)
      (47 >< 42) block  (* for S8 *)
    )
End

(* The purpose of ‘-1’ is to convert 1-indexed P values to 0-indexed. *)
Definition P_def :
    P (block :word32) :word32 = FCP i. block ' (EL i P_data - 1)
End

Definition SBox_def :
    SBox data :sbox =
      (\w. let row = w2n ((((6 >< 6)w :word1) @@ ((0 >< 0)w :word1)) :word2);
               col = w2n ((4 >< 1)w :word4)
           in n2w (EL col (EL row data)))
End

Overload S1 = “SBox S1_data”
Overload S2 = “SBox S2_data”
Overload S3 = “SBox S3_data”
Overload S4 = “SBox S4_data”
Overload S5 = “SBox S5_data”
Overload S6 = “SBox S6_data”
Overload S7 = “SBox S7_data”
Overload S8 = “SBox S8_data”

(* This example is from [1, p.23] *)
Theorem S5_001101_IS_1101 :
    S5 (n2w 0b001101) = (n2w 0b1101)
Proof
    EVAL_TAC
QED

(* This gives the same example above *)
Theorem S5_001101_IS_1101' = EVAL “S5 13w”

(* Basic S-Box criteria (not used so far) *)
Definition IS_SBOX :
    IS_SBOX (data :num list list) =
      (LENGTH data = 4 /\ EVERY (\l. PERM l (GENLIST I 16)) data)
End

(* A trivial S-Box (not used so far) *)
Theorem EXISTS_SBOX :
    ?d. IS_SBOX d
Proof
    Q.EXISTS_TAC ‘[GENLIST I 16; GENLIST I 16; GENLIST I 16; GENLIST I 16]’
 >> rw [IS_SBOX]
QED




val _ = export_theory();
val _ = html_theory "des";

(* References:

 [1] Knudsen, L.R., Robshaw, M.J.B.: The Block Cipher Companion. Springer
     Publishing Company, Incorporated, Berlin, Heidelberg (2011).
 *)
