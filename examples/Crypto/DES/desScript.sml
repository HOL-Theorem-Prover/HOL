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
       .    .                                                         .
       .    .                                                         .
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

Type block[pp] = “:word32 # word32”
Type roundkey  = “:word28 # word28”

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

Theorem IIP_IP_Inverse :
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
 >> FULL_SIMP_TAC std_ss [Abbr ‘j’, dimindex_64]
 >> Q.PAT_X_ASSUM ‘0 < EL (63 - i) IIP_data’ K_TAC
 >> Q.PAT_X_ASSUM ‘i < 64’ MP_TAC
 >> Q.SPEC_TAC (‘i’, ‘n’)
 >> rpt (CONV_TAC (BOUNDED_FORALL_CONV
                    (SIMP_CONV list_ss [IP_data, IIP_data])))
 >> REWRITE_TAC []
QED

Theorem IP_IIP_Inverse :
    !w. IP (IIP w) = w
Proof
    RW_TAC fcp_ss [IIP_def, IP_def, bitwise_perm_def, dimindex_64]
 >> Q.ABBREV_TAC ‘j = 64 - EL (63 - i) IP_data’
 >> Know ‘j < dimindex(:64)’
 >- (fs [Abbr ‘j’, dimindex_64] \\
     POP_ASSUM MP_TAC \\
     Q.SPEC_TAC (‘i’, ‘n’) \\
     rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [IP_data]))) \\
     REWRITE_TAC [])
 >> DISCH_TAC
 >> RW_TAC fcp_ss []
 >> Suff ‘64 - EL (63 - j) IIP_data = i’ >- rw []
 >> FULL_SIMP_TAC std_ss [Abbr ‘j’, dimindex_64]
 >> Q.PAT_X_ASSUM ‘0 < EL (63 - i) IP_data’ K_TAC
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
      let (k' :word56) = bitwise_perm k PC1_data
      in ((55 >< 28) k', (27 >< 0) k')
End

Definition PC2_def :
    PC2 (w :roundkey) :word48 =
      bitwise_perm ((FST w @@ SND w) :word56) PC2_data
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
    RoundKey      0  (k :word64) :roundkey list = [PC1 k] /\
    RoundKey (SUC n) (k :word64) =
      let ks = RoundKey n k; (c,d) = HD ks; r = EL n R_data
      in (c #<< r, d #<< r)::ks
End

Theorem LENGTH_RoundKey[local] :
    !k n. LENGTH (RoundKey n k) = n + 1
Proof
    Q.X_GEN_TAC ‘k’
 >> Induct_on ‘n’
 >- rw [RoundKey_def]
 >> rw [RoundKey_def]
 >> Q.ABBREV_TAC ‘ks = RoundKey n k’
 >> Cases_on ‘ks’ >- fs []
 >> rw []
 >> Cases_on ‘h’ >> rw []
QED

(* This is the final roundkeys with correct number and order *)
Definition KS_def :
    KS k n = MAP PC2 (TL (REVERSE (RoundKey n k)))
End

Theorem LENGTH_KS :
    !k n. LENGTH (KS k n) = n
Proof
    rw [KS_def, RoundKey_def]
 >> Know ‘LENGTH (TL (REVERSE (RoundKey n k))) =
          LENGTH (REVERSE (RoundKey n k)) - 1’
 >- (MATCH_MP_TAC LENGTH_TL \\
     rw [LENGTH_REVERSE, LENGTH_RoundKey])
 >> rw [LENGTH_REVERSE, LENGTH_RoundKey]
QED

(*---------------------------------------------------------------------------*)
(*  Split and Join                                                           *)
(*---------------------------------------------------------------------------*)

(* This is the initial split right after IP. cf. Join_def *)
Definition Split_def :
    Split (w :word64) :block = ((63 >< 32)w, (31 >< 0)w)
End

Definition Join_def :
   Join ((u,v):block) :word64 = u @@ v
End

Theorem Join_Split_Inverse :
    !w. Join (Split w) = w
Proof
    rw [Join_def, Split_def]
 >> WORD_DECIDE_TAC
QED

Theorem Split_Join_Inverse :
    !w. Split (Join w) = w
Proof
    Cases_on ‘w’
 >> rw [Join_def, Split_def]
 >> WORD_DECIDE_TAC
QED

(* This extra step is needed for DES_alt in which Round (instead of RoundSwap)
   is used. *)
Definition Swap_def :
   Swap ((v,u):block) :block = (u,v)
End

Theorem Swap_Inverse :
    !w. Swap (Swap w) = w
Proof
    Cases_on ‘w’ >> rw [Swap_def]
QED

(*---------------------------------------------------------------------------*)
(*  Round Function and DES Encryption                                        *)
(*---------------------------------------------------------------------------*)

(* This is DES Round Operation (Function) combining P, S and E *)
Definition RoundOp_def :
    RoundOp (w :word32) (k :word48) = P (S (E w ?? k))
End

(* ‘RoundSwap n r ks (u,v)’ returns the (u,v) pair after n rounds, each time
   one round key from the HD of ks (thus is reversely ordered) is consumed.
   At the last round, the pair is swapped for the final join [1, p.16].

   NOTE: This version is necessary for DES_0 (zero round gives the cleartext).
 *)
Definition RoundSwap_def :
    RoundSwap      0  r ks w = (w :block) /\
    RoundSwap (SUC n) r ks w =
      let (u,v) = RoundSwap n r ks w; k = EL n ks in
        if SUC n = r then (u ?? RoundOp v k, v)
        else           (v, u ?? RoundOp v k)
End

(* ‘Round r ks (u,v)’ returns the block after n rounds, no final swapping.

   NOTE: This version is simpler for proving DES properties but requires an
         extra Swap before Join.
 *)
Definition Round_def :
    Round      0  ks w = (w :block) /\
    Round (SUC n) ks w =
      let (u,v) = Round n ks w; k = EL n ks in (v, u ?? RoundOp v k)
End

Theorem RoundSwap_and_Round :
    !ks w r n. n < r ==> RoundSwap n r ks w = Round n ks w
Proof
    NTAC 3 GEN_TAC
 >> Induct_on ‘n’ >> rw [RoundSwap_def, Round_def]
QED

Theorem RoundSwap_and_Round' :
    !ks w r. 0 < r ==> RoundSwap r r ks w = Swap (Round r ks w)
Proof
    NTAC 2 GEN_TAC
 >> Cases_on ‘r’ >> rw [RoundSwap_def, Round_def]
 >> Know ‘RoundSwap n (SUC n) ks w = Round n ks w’
 >- (MATCH_MP_TAC RoundSwap_and_Round >> rw [])
 >> Rewr'
 >> Q.ABBREV_TAC ‘pair = Round n ks w’
 >> Cases_on ‘pair’ >> rw [Swap_def]
QED

(* This is the core of DES (no key scheduling) possibly reduced to r rounds *)
Definition DESCore_def :
    DESCore r ks = IIP o Join o (RoundSwap r r ks) o Split o IP
End

(* Zero-round DES doesn't change the message at all *)
Theorem DESCore_0 :
    !ks w. DESCore 0 ks w = w
Proof
    rw [o_DEF, DESCore_def, RoundSwap_def, IIP_IP_Inverse,
        Join_Split_Inverse]
QED

Theorem DESCore_alt :
    !ks r. 0 < r ==>
           DESCore r ks = IIP o Join o Swap o (Round r ks) o Split o IP
Proof
    rw [o_DEF, FUN_EQ_THM, DESCore_def, RoundSwap_and_Round']
QED

(* The decryption process is identical to encryption provided the round keys
   are taken in reverse order. [1, p.16]
 *)
Definition DES_def :
   DES r key = let keys = KS key r in (DESCore r keys, DESCore r (REVERSE keys))
End

(* Full DES = DES of full 16 rounds *)
Overload FullDES = “DES 16”

(*---------------------------------------------------------------------------*)
(* Basic theorem about encryption/decryption                                 *)
(*---------------------------------------------------------------------------*)

(* The plaintext message halves and intermediate message halves m0 ~ m16 [3] *)
Definition half_message_def :
    half_message f ((u,v) :block) (ks :word48 list) n =
      if n = 0 then u
      else if n = 1 then v
      else (half_message f (u,v) ks (n - 2)) ??
           (f (half_message f (u,v) ks (n - 1)) (EL (n - 2) ks))
End

Theorem half_message :
    !f u v ks. half_message f (u,v) ks 0 = u /\
               half_message f (u,v) ks 1 = v /\
              (!n. 2 <= n ==>
                   half_message f (u,v) ks n =
                     (half_message f (u,v) ks (n - 2)) ??
                     (f (half_message f (u,v) ks (n - 1)) (EL (n - 2) ks)))
Proof
    rpt STRIP_TAC
 >- rw [Once half_message_def]
 >- rw [Once half_message_def]
 >> ‘n <> 0 /\ n <> 1’ by rw []
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [half_message_def]
 >> simp []
QED

Theorem half_message' :
    !f uv ks. half_message f uv ks 0 = FST uv /\
             half_message f uv ks 1 = SND uv /\
            (!n. 2 <= n ==>
                 half_message f uv ks n =
                  (half_message f uv ks (n - 2)) ??
                  (f (half_message f uv ks (n - 1)) (EL (n - 2) ks)))
Proof
    rpt GEN_TAC >> Cases_on ‘uv’ >> REWRITE_TAC [half_message]
QED

(* This is half_message specialized for DES *)
Overload M = “half_message RoundOp”

Theorem Round_alt_half_message :
    !u v ks n. Round n ks (u,v) = (M (u,v) ks n, M (u,v) ks (SUC n))
Proof
    NTAC 3 GEN_TAC
 >> Induct_on ‘n’ >- rw [Round_def, half_message]
 >> rw [Round_def]
 >> Q.ABBREV_TAC ‘m0 = M (u,v) ks n’
 >> Q.ABBREV_TAC ‘m1 = M (u,v) ks (SUC n)’
 >> simp [half_message, ARITH_PROVE “SUC (SUC n) - 2 = n”]
QED

Theorem Round_alt_half_message' :
    !ks uv n. Round n ks uv = (M uv ks n, M uv ks (SUC n))
Proof
    rpt GEN_TAC >> Cases_on ‘uv’
 >> REWRITE_TAC [Round_alt_half_message]
QED

(* FullDES can be expressed by just M16 and M17 *)
Theorem DESCore_alt_half_message :
    !r ks plaintext. 0 < r ==>
         DESCore r ks plaintext =
           let uv = Split (IP plaintext) in
             IIP (Join (M uv ks (SUC r), M uv ks r))
Proof
    rw [DESCore_alt, Round_alt_half_message', Swap_def]
QED

(* The key idea of this proof is from [3] based on half_message_def *)
Theorem DESCore_CORRECT :
    !keys r plaintext. LENGTH keys = r ==>
       DESCore r (REVERSE keys) (DESCore r keys plaintext) = plaintext
Proof
    Q.X_GEN_TAC ‘ks’
 >> rpt STRIP_TAC
 >> Cases_on ‘r = 0’ >- rw [DESCore_0]
 >> ‘0 < r’ by rw []
 >> Know ‘DESCore r ks plaintext =
          let uv = Split (IP plaintext) in
            IIP (Join (M uv ks (SUC r), M uv ks r))’
 >- rw [DESCore_alt_half_message]
 >> Rewr'
 >> rw [DESCore_def, IP_IIP_Inverse, Split_Join_Inverse,
        RoundSwap_and_Round']
 >> Q.ABBREV_TAC ‘uv = Split (IP plaintext)’
 >> Q.ABBREV_TAC ‘r = LENGTH ks’
 (* applying Round_def *)
 >> Suff ‘Round r (REVERSE ks) (M uv ks (SUC r),M uv ks r) = (M uv ks 1,M uv ks 0)’
 >- (Rewr' \\
     rw [Abbr ‘uv’, half_message', Swap_def, Join_Split_Inverse, IIP_IP_Inverse])
 >> Suff ‘!n. n <= r ==>
              Round n (REVERSE ks) (M uv ks (SUC r),M uv ks r) =
              (M uv ks (SUC r - n),M uv ks (r - n))’
 >- (DISCH_THEN (MP_TAC o (Q.SPEC ‘r’)) >> rw [])
 >> Induct_on ‘n’ >- rw [Round_def]
 >> rw [Round_def]
 >> Q.PAT_X_ASSUM ‘n <= r ==> _’ K_TAC
 (* we have 3 numbers: ‘SUC r - n’, ‘r - n’ and ‘r - SUC n’, which is bigger? *)
 >> Q.ABBREV_TAC ‘i = SUC r - n’
 >> ‘r - n = i - 1’ by rw [Abbr ‘i’] >> POP_ORW
 >> ‘r - SUC n = i - 2’ by rw [Abbr ‘i’] >> POP_ORW
 >> ‘2 <= i’ by rw [Abbr ‘i’]
 >> Know ‘M uv ks i =
          M uv ks (i - 2) ?? (RoundOp (M uv ks (i - 1)) (EL (i - 2) ks))’
 >- METIS_TAC [half_message']
 >> Rewr'
 >> Suff ‘EL n (REVERSE ks) = EL (i - 2) ks’ >- rw []
 >> rw [Abbr ‘i’, Abbr ‘r’, EL_REVERSE]
 >> Q.ABBREV_TAC ‘r = LENGTH ks’
 >> Suff ‘PRE (r - n) = SUC r - (n + 2)’ >- Rewr
 >> ARITH_TAC
QED

Theorem FullDES_CORRECT :
    !key plaintext. ((encrypt,decrypt) = FullDES key) ==>
                    (decrypt (encrypt plaintext) = plaintext)
Proof
    rw [DES_def, DESCore_CORRECT, LENGTH_KS]
QED

val _ = export_theory();
val _ = html_theory "des";

(* References:

 [1] Knudsen, L.R., Robshaw, M.J.B.: The Block Cipher Companion. Springer
     Publishing Company, Incorporated, Berlin, Heidelberg (2011).
 [2] Grabbe, J.O.: The DES Algorithm Illustrated,
     https://page.math.tu-berlin.de/~kant/teaching/hess/krypto-ws2006/des.htm.
 [3] Coopersmith, D.: The Data Encryption Standard (DES) and its strength against
     attacks. IBM J. 38, 243–250 (1994).
 *)
