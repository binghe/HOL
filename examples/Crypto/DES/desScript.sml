(*===========================================================================*)
(*  The Data Encryption Standard (DES) in HOL                                *)
(*                                                                           *)
(*  Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2023)                *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory listLib sortingTheory pred_setTheory combinTheory hurdUtils;

(*  DES with round function components; the bit expansion E, the S-boxes S,
    and the bit permutation P [1, p.16]

    +-----+                           +-----+
    | KS  | <--- KEY     MESSAGE ---> | IP  |
    +--+--+    (56-bit)  (64-bit)     +--+--+
       |                                \|/
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
                                        \|/
                                      +--+--+
                                      | IIP | ---> CIPHERTEXT
                                      +-----+       (64-bit)
 *)
val _ = new_theory "des"; (* the lower-case name is following aesTheory *)

val _ = guessing_word_lengths := true;
val _ = hide "S"; (* reused for S-box *)

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

(* DES round key *)
Type roundkey[pp] = “:word28 # word28”

(*---------------------------------------------------------------------------*)
(* Data Tables. All values are directly copied from PDF pages [1]            *)
(*---------------------------------------------------------------------------*)

(* The DES initial permutation IP

   NOTE: all "raw" index data below assume 1-indexing bits and the first bit is
         the most significant bit !!!
 *)
Definition IP_data : (* 64 elements *)
    IP_data = [58; 50; 42; 34; 26; 18; 10; 2;
               60; 52; 44; 36; 28; 20; 12; 4;
               62; 54; 46; 38; 30; 22; 14; 6;
               64; 56; 48; 40; 32; 24; 16; 8;
               57; 49; 41; 33; 25; 17;  9; 1;
               59; 51; 43; 35; 27; 19; 11; 3;
               61; 53; 45; 37; 29; 21; 13; 5;
               63; 55; 47; 39; 31; 23; 15; 7]
End

(* The final permutation Inverse IP, see IP_Inverse for its relation with IP *)
Definition IIP_data : (* 64 elements *)
    IIP_data = [40; 8; 48; 16; 56; 24; 64; 32;
                39; 7; 47; 15; 55; 23; 63; 31;
                38; 6; 46; 14; 54; 22; 62; 30;
                37; 5; 45; 13; 53; 21; 61; 29;
                36; 4; 44; 12; 52; 20; 60; 28;
                35; 3; 43; 11; 51; 19; 59; 27;
                34; 2; 42; 10; 50; 18; 58; 26;
                33; 1; 41;  9; 49; 17; 57; 25]
End

(* The bitwise expansion E

   The tables should be interpreted (as those for IP and IP^−1) in that the
   first bit of the output of E is taken from the 32nd bit of the input.
 *)
Definition E_data : (* 48 elements *)
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
Definition P_data : (* 32 elements *)
    P_data = [16;  7; 20; 21; 29; 12; 28; 17;
               1; 15; 23; 26;  5; 18; 31; 10;
               2;  8; 24; 14; 32; 27;  3;  9;
              19; 13; 30;  6; 22; 11;  4; 25]
End

(* Permuted Choice 1 (PC1), parity bits (e.g. 8) of 64-bit keys do not occur

   NOTE: PC1 is a permutation of all non-parity bit indexes.
 *)
Definition PC1_data : (* 2 * 28 = 56 elements *)
    PC1_data = [57; 49; 41; 33; 25; 17;  9;
                 1; 58; 50; 42; 34; 26; 18; 
                10;  2; 59; 51; 43; 35; 27; 
                19; 11;  3; 60; 52; 44; 36; (* above is for C *)
            (* ----------------------------- *)
                63; 55; 47; 39; 31; 23; 15;
                 7; 62; 54; 46; 38; 30; 22; 
                14;  6; 61; 53; 45; 37; 29; 
                21; 13;  5; 28; 20; 12;  4] (* above is for D *)
End

(* Permuted Choice 2 (PC2) *)
Definition PC2_data : (* 48 elements *)
    PC2_data = [14; 17; 11; 24;  1;  5;
                 3; 28; 15;  6; 21; 10;
                23; 19; 12;  4; 26;  8;
                16;  7; 27; 20; 13;  2;
                41; 52; 31; 37; 47; 55;
                30; 40; 51; 45; 33; 48;
                44; 49; 39; 56; 34; 53;
                46; 42; 50; 36; 29; 32]
End

(* The round-dependent rotation values *)
Definition R_data : (* 16 elements *)
    R_data = [1; 1; 2; 2; 2; 2; 2; 2; 1; 2; 2; 2; 2; 2; 2; 1]
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
Definition S1_data :
    S1_data =
         [[0xe;0x4;0xd;0x1;0x2;0xf;0xb;0x8;0x3;0xa;0x6;0xc;0x5;0x9;0x0;0x7];
          [0x0;0xf;0x7;0x4;0xe;0x2;0xd;0x1;0xa;0x6;0xc;0xb;0x9;0x5;0x3;0x8];
          [0x4;0x1;0xe;0x8;0xd;0x6;0x2;0xb;0xf;0xc;0x9;0x7;0x3;0xa;0x5;0x0];
          [0xf;0xc;0x8;0x2;0x4;0x9;0x1;0x7;0x5;0xb;0x3;0xe;0xa;0x0;0x6;0xd]]
End

Definition S2_data :
    S2_data =
         [[0xf;0x1;0x8;0xe;0x6;0xb;0x3;0x4;0x9;0x7;0x2;0xd;0xc;0x0;0x5;0xa];
          [0x3;0xd;0x4;0x7;0xf;0x2;0x8;0xe;0xc;0x0;0x1;0xa;0x6;0x9;0xb;0x5];
          [0x0;0xe;0x7;0xb;0xa;0x4;0xd;0x1;0x5;0x8;0xc;0x6;0x9;0x3;0x2;0xf];
          [0xd;0x8;0xa;0x1;0x3;0xf;0x4;0x2;0xb;0x6;0x7;0xc;0x0;0x5;0xe;0x9]]
End

Definition S3_data :
    S3_data =
         [[0xa;0x0;0x9;0xe;0x6;0x3;0xf;0x5;0x1;0xd;0xc;0x7;0xb;0x4;0x2;0x8];
          [0xd;0x7;0x0;0x9;0x3;0x4;0x6;0xa;0x2;0x8;0x5;0xe;0xc;0xb;0xf;0x1];
          [0xd;0x6;0x4;0x9;0x8;0xf;0x3;0x0;0xb;0x1;0x2;0xc;0x5;0xa;0xe;0x7];
          [0x1;0xa;0xd;0x0;0x6;0x9;0x8;0x7;0x4;0xf;0xe;0x3;0xb;0x5;0x2;0xc]]
End

Definition S4_data :
    S4_data =
         [[0x7;0xd;0xe;0x3;0x0;0x6;0x9;0xa;0x1;0x2;0x8;0x5;0xb;0xc;0x4;0xf];
          [0xd;0x8;0xb;0x5;0x6;0xf;0x0;0x3;0x4;0x7;0x2;0xc;0x1;0xa;0xe;0x9];
          [0xa;0x6;0x9;0x0;0xc;0xb;0x7;0xd;0xf;0x1;0x3;0xe;0x5;0x2;0x8;0x4];
          [0x3;0xf;0x0;0x6;0xa;0x1;0xd;0x8;0x9;0x4;0x5;0xb;0xc;0x7;0x2;0xe]]
End

Definition S5_data :
    S5_data =
         [[0x2;0xc;0x4;0x1;0x7;0xa;0xb;0x6;0x8;0x5;0x3;0xf;0xd;0x0;0xe;0x9];
          [0xe;0xb;0x2;0xc;0x4;0x7;0xd;0x1;0x5;0x0;0xf;0xa;0x3;0x9;0x8;0x6];
          [0x4;0x2;0x1;0xb;0xa;0xd;0x7;0x8;0xf;0x9;0xc;0x5;0x6;0x3;0x0;0xe];
          [0xb;0x8;0xc;0x7;0x1;0xe;0x2;0xd;0x6;0xf;0x0;0x9;0xa;0x4;0x5;0x3]]
End

Definition S6_data :
    S6_data =
         [[0xc;0x1;0xa;0xf;0x9;0x2;0x6;0x8;0x0;0xd;0x3;0x4;0xe;0x7;0x5;0xb];
          [0xa;0xf;0x4;0x2;0x7;0xc;0x9;0x5;0x6;0x1;0xd;0xe;0x0;0xb;0x3;0x8];
          [0x9;0xe;0xf;0x5;0x2;0x8;0xc;0x3;0x7;0x0;0x4;0xa;0x1;0xd;0xb;0x6];
          [0x4;0x3;0x2;0xc;0x9;0x5;0xf;0xa;0xb;0xe;0x1;0x7;0x6;0x0;0x8;0xd]]
End

Definition S7_data :
    S7_data =
         [[0x4;0xb;0x2;0xe;0xf;0x0;0x8;0xd;0x3;0xc;0x9;0x7;0x5;0xa;0x6;0x1];
          [0xd;0x0;0xb;0x7;0x4;0x9;0x1;0xa;0xe;0x3;0x5;0xc;0x2;0xf;0x8;0x6];
          [0x1;0x4;0xb;0xd;0xc;0x3;0x7;0xe;0xa;0xf;0x6;0x8;0x0;0x5;0x9;0x2];
          [0x6;0xb;0xd;0x8;0x1;0x4;0xa;0x7;0x9;0x5;0x0;0xf;0xe;0x2;0x3;0xc]]
End

Definition S8_data :
    S8_data =
         [[0xd;0x2;0x8;0x4;0x6;0xf;0xb;0x1;0xa;0x9;0x3;0xe;0x5;0x0;0xc;0x7];
          [0x1;0xf;0xd;0x8;0xa;0x3;0x7;0x4;0xc;0x5;0x6;0xb;0x0;0xe;0x9;0x2];
          [0x7;0xb;0x4;0x1;0x9;0xc;0xe;0x2;0x0;0x6;0xa;0xd;0xf;0x3;0x5;0x8];
          [0x2;0x1;0xe;0x7;0x4;0xa;0x8;0xd;0xf;0xc;0x9;0x0;0x3;0x5;0x6;0xb]]
End

(*---------------------------------------------------------------------------*)
(*  Expansion and Permutation Functions                                      *)
(*---------------------------------------------------------------------------*)

(* This definition is dedicated to DES raw index tables where the "first bit"
   is considered as the highest (most sigificant) bit with the index "1".

   NOTE: This definition is the only one where ‘FCP i.’ is explicitly used.
 *)
Definition bitwise_perm_def :
    bitwise_perm (w :bool['a]) table :bool['b] =
       FCP i. w ' (dimindex(:'a) - EL (dimindex(:'b) - 1 - i) table)
End

(* The bitwise expansion function E

   NOTE: the purpose of ‘-1’ is to convert 1-indexed E values to 0-indexed.
 *)
Definition E_def :
    E (w :word32) :word48 = bitwise_perm w E_data
End

(* The purpose of ‘-1’ is to convert 1-indexed P values to 0-indexed. *)
Definition P_def :
    P (w :word32) :word32 = bitwise_perm w P_data
End

Definition IP_def :
    IP (w :word64) :word64 = bitwise_perm w IP_data
End

Definition IIP_def :
    IIP (w :word64) :word64 = bitwise_perm w IIP_data
End

Theorem LENGTH_IP_data :
    LENGTH IP_data = 64
Proof
    rw [LENGTH, IP_data]
QED

Theorem LENGTH_IIP_data :
    LENGTH IIP_data = 64
Proof
    rw [LENGTH, IIP_data]
QED

Theorem IIP_IP_Inversion :
    !w. IIP (IP w) = w
Proof
    RW_TAC fcp_ss [IIP_def, IP_def, bitwise_perm_def, dimindex_64]
 >> Q.ABBREV_TAC ‘j = 64 - EL (63 - i) IIP_data’
 >> Know ‘j < dimindex(:64)’
 >- (fs [Abbr ‘j’, dimindex_64] \\
     POP_ASSUM MP_TAC \\
     Q.SPEC_TAC (‘i’, ‘n’) \\
  (* This numLib.BOUNDED_FORALL_CONV was learnt from Konrad Slind *)
     rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [IIP_data]))) \\
     REWRITE_TAC [])
 >> DISCH_TAC
 >> RW_TAC fcp_ss []
 >> Suff ‘64 - EL (63 - j) IP_data = i’ >- rw []
 >> FULL_SIMP_TAC list_ss [Abbr ‘j’, dimindex_64]
 >> Q.PAT_X_ASSUM ‘0 < EL (63 - i) IIP_data’ K_TAC
 >> Q.PAT_X_ASSUM ‘i < 64’ MP_TAC
 >> Q.SPEC_TAC (‘i’, ‘n’)
 >> rpt (CONV_TAC (BOUNDED_FORALL_CONV
                    (SIMP_CONV list_ss [IP_data, IIP_data])))
 >> REWRITE_TAC []
QED

(*---------------------------------------------------------------------------*)
(*  S-Box Functions                                                          *)
(*---------------------------------------------------------------------------*)

Definition SBox_def :
    SBox box (w :word6) :word4 =
      let row = w2n ((((5 >< 5)w :word1) @@ ((0 >< 0)w :word1)) :word2);
          col = w2n ((4 >< 1)w :word4)
      in n2w (EL col (EL row box))
End

(* abbreviations when using "standard" S-boxes *)
Overload S1 = “SBox S1_data”
Overload S2 = “SBox S2_data”
Overload S3 = “SBox S3_data”
Overload S4 = “SBox S4_data”
Overload S5 = “SBox S5_data”
Overload S6 = “SBox S6_data”
Overload S7 = “SBox S7_data”
Overload S8 = “SBox S8_data”

(* Basic S-Box criteria (not used so far) *)
Definition IS_SBox_def :
    IS_SBox (box :num list list) =
      (LENGTH box = 4 /\ EVERY (\l. PERM l (GENLIST I 16)) box)
End

(* A trivial S-Box (not used so far) *)
Theorem EXISTS_SBox[local] :
    ?box. IS_SBox box
Proof
    Q.EXISTS_TAC ‘[GENLIST I 16; GENLIST I 16; GENLIST I 16; GENLIST I 16]’
 >> rw [IS_SBox_def]
QED

(* The overall S-box function splits the 48 bits into 8 groups of 6 bits, call
   each S-boxes, and concatenate the results.

   NOTE: The first element of concat_word_list will be at the lowest bits, while
         the order of bits S1(B1)S2(B2)S3(B3)S4(B4)S5(B5)S6(B6)S7(B7)S8(B8) has
         the natural bit order (from high to low). Thus S1 takes 47 >< 42, etc.
 *)
Definition S_def :
    S (w :word48) :word32 =
      concat_word_list [S8 ((5  ><  0) w);
                        S7 ((11 ><  6) w);
                        S6 ((17 >< 12) w);
                        S5 ((23 >< 18) w);
                        S4 ((29 >< 24) w);
                        S3 ((35 >< 30) w);
                        S2 ((41 >< 36) w);
                        S1 ((47 >< 42) w)]
End

(*---------------------------------------------------------------------------*)
(*  Key Scheduling                                                           *)
(*---------------------------------------------------------------------------*)

Definition PC1_def :
    PC1 (k :word64) :roundkey =
      let (key :word56) = bitwise_perm k PC1_data
      in ((55 >< 28) key, (27 >< 0) key)
End

Definition PC2_def :
    PC2 ((c,d) :roundkey) :word48 = bitwise_perm ((c @@ d) :word56) PC2_data
End

(* The sum of the rotation amounts for the C and D registers is equal to 28.
   This is no coincidence and at the end of an encryption the registers C and D
   are back at their initial state. The registers are ready for the next
   encryption. [1, p.26]
 *)
Theorem SUM_R_data : (* not needed anywhere *)
    SUM R_data = 28
Proof
    EVAL_TAC
QED

(* RoundKey returns a list of roundkeys as (c,d)-pairs, later keys occur first

   NOTE: there are ‘r + 1’ elements returned by ‘RoundKey r key’. When r = 16,
         the first and last roundkey are the same (see SUM_R_data), which is
         the base roundkey returned by ‘PC1 key’.
 *)
Definition RoundKey_def :
    RoundKey 0 (key :word64) :roundkey list = [PC1 key] /\
    RoundKey (SUC n) (key :word64) =
      let keys = RoundKey n key; r = EL n R_data; (c,d) = HD keys
      in (c #<< r, d #<< r)::keys
End

(* This is the final roundkey as ‘:word48 list’ for DES round functions *)
Definition RoundKeys_def :
    RoundKeys n key = MAP PC2 (FRONT (RoundKey n key))
End

(*---------------------------------------------------------------------------*)
(*  Round Function and DES Encryption                                        *)
(*---------------------------------------------------------------------------*)

(* This is DES Round Operation (Function) combining P, S and E *)
Definition RoundOp_def :
    RoundOp (v :word32) (k :word48) = P (S (E v ?? k))
End

(* ‘Round n r ks (u,v)’ returns the (u,v) pair after n rounds, each time one round
   key from the HD of ks (thus is reversely ordered) gets consumed. The size of ks
   must be bigger than n.
 *)
Definition Round_def :
    Round 0 r (ks :word48 list) (pair :block) = pair /\
    Round (SUC n) r (k::ks) pair =
      let (u',v') = Round n r ks pair in
        if SUC n = r then
          (u' ?? RoundOp v' k, v')
        else
          (v', u' ?? RoundOp v' k)
End

Definition Split_def :
    Split (w :word64) :block = ((63 >< 32)w, (31 >< 0)w)
End

(* NOTE: This function is given a reversed order of pairs returned by Round. *)
Definition Join_def :
   Join ((u,v):block) :word64 = u @@ v
End

Theorem Join_Split_Inversion :
    !w. Join (Split w) = w
Proof
    rw [Join_def, Split_def]
 >> WORD_DECIDE_TAC
QED

(* This is the core of DES (no key scheduling) with parameterized rounds

   NOTE: It takes about 7 seconds to finish full 16 rounds of computation.
 *)
Definition DES_def :
    DES n ks = IIP o Join o (Round n n ks) o Split o IP
End

Definition DESEnc_def :
    DESEnc n key = DES n (RoundKeys n key)
End

(* Full DES = DES of full 16 rounds *)
Overload FullDES    = “DES 16”
Overload FullDESEnc = “DESEnc 16”

(*---------------------------------------------------------------------------*)
(*  DES Decryption                                                           *)
(*---------------------------------------------------------------------------*)

(* The decryption process is identical to encryption provided the round keys
   are taken in reverse order. [1, p.16]

   It is also interesting to note that the key schedule can be reversed for
   decryption, with the register rotations being applied in the opposite
   directions (to the right). [1, p. 26]

   NOTE: The equivalence of the above two notes are not obvious, we shall prove
         the second one by a modified RoundKey function.

   NOTE: This definition may be wrong for r < 16 because there's ‘r + 1’ roundkeys
 *)
Definition DESDec_def :
    DESDec n key = DES n (REVERSE (RoundKeys n key))
End

Overload FullDESDec = “DESDec 16”

(* The main difference w.r.t. RoundKey is the uses of "#>>" instead of "#<<"

   The extra parameter ‘r’ is used to get the correct rotation values for
   DES with reduced rounds.
 *)
Definition RoundKeyRev_def :
    RoundKeyRev 0 r (key :word64) :roundkey list = [PC1 key] /\
    RoundKeyRev (SUC n) r (key :word64) =
      let keys = RoundKeyRev n r key; (c,d) = HD keys;
          i = EL (r - 1 - n) R_data;
      in (c #>> i, d #>> i)::keys
End

(*---------------------------------------------------------------------------*)
(*  Basic Properties of DES Functions                                        *)
(*---------------------------------------------------------------------------*)

(* Zero-round DES doesn't change the message at all *)
Theorem DES_0 :
    !ks w. DES 0 ks w = w
Proof
    rw [DES_def, o_DEF, Round_def, IIP_IP_Inversion, Join_Split_Inversion]
QED

val _ = export_theory();
val _ = html_theory "des";

(* References:

 [1] Knudsen, L.R., Robshaw, M.J.B.: The Block Cipher Companion. Springer
     Publishing Company, Incorporated, Berlin, Heidelberg (2011).
 [2] Grabbe, J.O.: The DES Algorithm Illustrated,
     https://page.math.tu-berlin.de/~kant/teaching/hess/krypto-ws2006/des.htm.
 *)