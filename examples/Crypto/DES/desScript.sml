(*===========================================================================*)
(*  The Data Encryption Standard (DES) in HOL                                *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory sortingTheory pred_setTheory hurdUtils;

(*  DES with round function components; the bit expansion E, the S-boxes S,
    and the bit permutation P [1, p.16]

    +-----+                           +-----+
    | KS  | <--- KEY     MESSAGE ---> | IP  |
    +--+--+    (56-bit)  (64-bit)     +--+--+
       |                                 |
       |   u_0      (32-bit)       +-----+-----+       (32-bit)      v_0
       |    +----------------------+   split   +----------------------+
       |    |                      +-----+-----+                      |
       +----|------------------------------------+ k_1                |
       |   \|/      +---+          +---+        \|/          +---+    |
       |   (+) <--- | P | <------- | S | <===== (+) <======= | E | <--+
       |    |       +---+ (32-bit) +---+            (48-bit) +---+    |
       |     \                                                       /
       |  v_1 +-------------------------+  +------------------------+ u_1
       |                                 \/
       |                                 /\
       |  u_1 +-------------------------+  +------------------------+ v_1
       |     /                                                       \
       +----|------------------------------------+ k_1                |
       |   \|/      +---+          +---+        \|/          +---+    |
       |   (+) <--- | P | <------- | S | <===== (+) <======= | E | <--+
       |    |       +---+          +---+                     +---+    |
       |     \                                                       /
       |  v_2 +--------------------------+  +-----------------------+ u_2
       |                                  \/
       |                                  /\
       |      +--------------------------+  +-----------------------+
       |     /                                                       \
       |    |       - v_i = u_{i-1} (+) f(v_{i-1}, k_i)               |
       .    .       - u_i = v_{i-1}              (i = 1 ... r - 1)    .
       .    .       - u_r = u_{r-1} (+) f(v_{r-1}, k_r)               .
       .    .       - v_r = v_{r-1}                       (r = 16)    .
       |    |                                                         |
       +----|------------------------------------+ k_r                |
           \|/      +---+          +---+        \|/          +---+    |
           (+) <--- | P | <------- | S | <===== (+) <======= | E | <--+
            |       +---+          +---+                     +---+    |
            |                      +-----------+                      |
            +--------------------> |   join    | <--------------------+
           u_r       (32-bit)      +-----+-----+      (32-bit)       v_r
                                         |
                                      +--+--+
                                      | IIP | ---> CIPHERTEXT
                                      +-----+       (64-bit)
 *)
val _ = new_theory "des";

val _ = hide "S"; (* “S” is reused as the (overall) S-box function here *)
val _ = guessing_word_lengths := true;
val fcp_ss = std_ss ++ fcpLib.FCP_ss;

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
Type sbox[pp]   = “:word6 -> word4”
Type sboxes[pp] = “:word48 -> word32”

(* DES round function *)
Type roundop[pp] = “:word32 -> word32”

(*---------------------------------------------------------------------------*)
(* Data Tables. All values are directly copied from PDF pages [1]            *)
(*---------------------------------------------------------------------------*)

(* The bitwise expansion E

   The tables should be interpreted (as those for IP and IP^−1) in that the
   first bit of the output of E is taken from the 32nd bit of the input.

   NOTE: all "raw" index data assume the bits are 1-indexed.
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

(* The bitwise permutation P

   The tables should be interpreted in that the first bit of the output of P
   is taken from the 16th bit of the input.
 *)
Definition P_data_def : (* 32 elements *)
    P_data = [16;  7; 20; 21; 29; 12; 28; 17;
               1; 15; 23; 26;  5; 18; 31; 10;
               2;  8; 24; 14; 32; 27;  3;  9;
              19; 13; 30;  6; 22; 11;  4; 25]
End

(* The DES initial permutation IP and its inverse IIP
 *)
Definition IP_data_def : (* 64 elements *)
    IP_data = [58; 50; 42; 34; 26; 18; 10; 2;
               60; 52; 44; 36; 28; 20; 12; 4;
               62; 54; 46; 38; 30; 22; 14; 6;
               64; 56; 48; 40; 32; 24; 16; 8;
               57; 49; 41; 33; 25; 17;  9; 1;
               59; 51; 43; 35; 27; 19; 11; 3;
               61; 53; 45; 37; 29; 21; 13; 5;
               63; 55; 47; 39; 31; 23; 15; 7]
End

Definition IIP_data_def : (* 64 elements *)
    IIP_data = [40; 8; 48; 16; 56; 24; 64; 32;
                39; 7; 47; 15; 55; 23; 63; 31;
                38; 6; 46; 14; 54; 22; 62; 30;
                37; 5; 45; 13; 53; 21; 61; 29;
                36; 4; 44; 12; 52; 20; 60; 28;
                35; 3; 43; 11; 51; 19; 59; 27;
                34; 2; 42; 10; 50; 18; 58; 26;
                33; 1; 41;  9; 49; 17; 57; 25]
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

(* The bitwise expansion function E

   NOTE: the purpose of ‘-1’ is to convert 1-indexed E values to 0-indexed.
 *)
Definition E_def :
    E (block :word32) :word48 = FCP i. block ' (EL i E_data - 1)
End

(* The purpose of ‘-1’ is to convert 1-indexed P values to 0-indexed. *)
Definition P_def :
    P (block :word32) :word32 = FCP i. block ' (EL i P_data - 1)
End

Definition IP_def :
    IP (block :word64) :word64 = FCP i. block ' (EL i IP_data - 1)
End

Definition IIP_def :
    IIP (block :word64) :word64 = FCP i. block ' (EL i IIP_data - 1)
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
Definition IS_SBox_def :
    IS_SBox (data :num list list) =
      (LENGTH data = 4 /\ EVERY (\l. PERM l (GENLIST I 16)) data)
End

(* A trivial S-Box (not used so far) *)
Theorem EXISTS_SBox :
    ?d. IS_SBox d
Proof
    Q.EXISTS_TAC ‘[GENLIST I 16; GENLIST I 16; GENLIST I 16; GENLIST I 16]’
 >> rw [IS_SBox_def]
QED

(* The bitsecond part of E split the 48 bits into 8 groups of 6 bits

   NOTE: the lowest 6 bits are sent to S1, the next 6 bits to S2, etc.
 *)
Definition S_def :
    S (block :word48) :expansion =
     ((5  ><  0) block, (* for S1 *)
      (11 ><  6) block, (* for S2 *)
      (17 >< 12) block, (* for S3 *)
      (23 >< 18) block, (* for S4 *)
      (29 >< 24) block, (* for S5 *)
      (35 >< 30) block, (* for S6 *)
      (41 >< 36) block, (* for S7 *)
      (47 >< 42) block) (* for S8 *)
End

(*---------------------------------------------------------------------------*)
(*  Basic Properties of DES Functions                                        *)
(*---------------------------------------------------------------------------*)

Theorem LENGTH_IP_data[local] :
    LENGTH IP_data = 64
Proof
    rw [IP_data_def, LENGTH]
QED

Theorem LENGTH_IIP_data[local] :
    LENGTH IIP_data = 64
Proof
    rw [IIP_data_def, LENGTH]
QED

Theorem EVERY_IP_data[local] :
    EVERY (\n. n <= 64) IP_data
Proof
    rw [IP_data_def, EVERY_DEF]
QED

Theorem EVERY_IIP_data[local] :
    EVERY (\n. n <= 64) IIP_data
Proof
    rw [IIP_data_def, EVERY_DEF]
QED

Theorem IIP_IP_Inversion :
    !w. IIP (IP w) = w
Proof
    RW_TAC fcp_ss [IIP_def, IP_def]
 >> Q.ABBREV_TAC ‘j = EL i IIP_data − 1’
 >> Know ‘j < dimindex(:64)’
 >- (fs [Abbr ‘j’, dimindex_64] \\
     Suff ‘EL i IIP_data <= 64’ >- rw [] \\
     MATCH_MP_TAC (SIMP_RULE std_ss [EVERY_IIP_data, LENGTH_IIP_data]
                     (Q.ISPECL [‘IIP_data’, ‘\n. n <= 64’] EVERY_EL)) >> art [])
 >> DISCH_TAC
 >> RW_TAC fcp_ss []
 >> Suff ‘EL j IP_data − 1 = i’ >- rw []
 >> fs [Abbr ‘j’, dimindex_64]
 >> Cases_on ‘i = 0’
 >- rw [IIP_data_def, IP_data_def]
 >> cheat
QED

val _ = export_theory();
val _ = html_theory "des";

(* References:

 [1] Knudsen, L.R., Robshaw, M.J.B.: The Block Cipher Companion. Springer
     Publishing Company, Incorporated, Berlin, Heidelberg (2011).
 *)
