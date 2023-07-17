(*===========================================================================*)
(*  The Data Encryption Standard (DES) in HOL - Test Vectors                 *)
(*                                                                           *)
(*  Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2023)                *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory listLib combinTheory hurdUtils;

open desTheory;

val _ = new_theory "des_test";

val fcp_ss = std_ss ++ fcpLib.FCP_ss;

(*---------------------------------------------------------------------------*)
(*  S-box tests                                                              *)
(*---------------------------------------------------------------------------*)

(* This example is from [1, p.23] *)
Theorem S5_001101 :
    S5 (n2w 0b001101) = (n2w 0b1101)
Proof
    EVAL_TAC
QED

(* This example is from [2] *)
Theorem S1_011011 :
    S1 (n2w 0b011011) = (n2w 0b0101)
Proof
    EVAL_TAC
QED

(* This example is also from [2], ever exposed a bug in SBox_def *)
Theorem S4_111010 :
    S4 (n2w 0b111010) = (n2w 0b0010)
Proof
    EVAL_TAC
QED

(*---------------------------------------------------------------------------*)
(*  Running tests of DES computations [2]                                    *)
(*---------------------------------------------------------------------------*)

val _ = output_words_as_padded_bin();

(* A test key
   |- Test_K = 0b1001100110100010101110111100110011011101111001101111111110001w
 *)
Definition Test_K :
   Test_K :word64 = 0x133457799BBCDFF1w
End

(* EVAL “PC1 Test_K” *)
Theorem Test_K_by_PC1:
    PC1 Test_K = (0b1111000011001100101010101111w,0b101010101100110011110001111w)
Proof
    EVAL_TAC
QED

(* EVAL “REVERSE (RoundKey 16 Test_K)”

   NOTE: All literal values copied as theorem statements are correct w.r.t. [2]
 *)
Theorem Test_K_RoundKey_16 :
    REVERSE (RoundKey 16 Test_K) =
    [(0b1111000011001100101010101111w,0b0101010101100110011110001111w); (* CD0 *)
     (0b1110000110011001010101011111w,0b1010101011001100111100011110w); (* CD1 *)
     (0b1100001100110010101010111111w,0b0101010110011001111000111101w); (* CD2 *)
     (0b0000110011001010101011111111w,0b0101011001100111100011110101w); (* CD3 *)
     (0b0011001100101010101111111100w,0b0101100110011110001111010101w); (* CD4 *)
     (0b1100110010101010111111110000w,0b0110011001111000111101010101w); (* CD5 *)
     (0b0011001010101011111111000011w,0b1001100111100011110101010101w); (* CD6 *)
     (0b1100101010101111111100001100w,0b0110011110001111010101010110w); (* CD7 *)
     (0b0010101010111111110000110011w,0b1001111000111101010101011001w); (* CD8 *)
     (0b0101010101111111100001100110w,0b0011110001111010101010110011w); (* CD9 *)
     (0b0101010111111110000110011001w,0b1111000111101010101011001100w); (* CD10 *)
     (0b0101011111111000011001100101w,0b1100011110101010101100110011w); (* CD11 *)
     (0b0101111111100001100110010101w,0b0001111010101010110011001111w); (* CD12 *)
     (0b0111111110000110011001010101w,0b0111101010101011001100111100w); (* CD13 *)
     (0b1111111000011001100101010101w,0b1110101010101100110011110001w); (* CD14 *)
     (0b1111100001100110010101010111w,0b1010101010110011001111000111w); (* CD15 *)
     (0b1111000011001100101010101111w,0b0101010101100110011110001111w)] (* CD16 *)
Proof
    EVAL_TAC
QED

(* EVAL “KS Test_K” *)
Theorem Test_K_KS[compute] :
    KS Test_K 16 =
      [0b000110110000001011101111111111000111000001110010w; (* K1 *)
       0b011110011010111011011001110110111100100111100101w; (* K2 *)
       0b010101011111110010001010010000101100111110011001w; (* K3 *)
       0b011100101010110111010110110110110011010100011101w; (* K4 *)
       0b011111001110110000000111111010110101001110101000w; (* K5 *)
       0b011000111010010100111110010100000111101100101111w; (* K6 *)
       0b111011001000010010110111111101100001100010111100w; (* K7 *)
       0b111101111000101000111010110000010011101111111011w; (* K8 *)
       0b111000001101101111101011111011011110011110000001w; (* K9 *)
       0b101100011111001101000111101110100100011001001111w; (* K10 *)
       0b001000010101111111010011110111101101001110000110w; (* K11 *)
       0b011101010111000111110101100101000110011111101001w; (* K12 *)
       0b100101111100010111010001111110101011101001000001w; (* K13 *)
       0b010111110100001110110111111100101110011100111010w; (* K14 *)
       0b101111111001000110001101001111010011111100001010w; (* K15 *)
       0b110010110011110110001011000011100001011111110101w] (* K16 *)
Proof
    EVAL_TAC
QED

Definition Test_KS :
    Test_KS = KS Test_K 16
End

(* A test message (cleartext)
   |- Test_M = 0b100100011010001010110011110001001101010111100110111101111w
 *)
Definition Test_M :
    Test_M :word64 = 0x0123456789ABCDEFw
End

Theorem Test_M_by_IP :
    IP Test_M = 0b1100110000000000110011001111111111110000101010101111000010101010w
Proof
    EVAL_TAC
QED

(* EVAL “Round 0 16 Test_KS (Split (IP Test_M))” *)
Theorem Test_Round_0[compute] :
    Round 0 Test_KS (Split (IP Test_M)) =
      (0b11001100000000001100110011111111w, (* L0 *)
       0b11110000101010101111000010101010w) (* R0 *)
Proof
    EVAL_TAC
QED

(* These two values are taken from Test_Round_0 *)
Definition L0_def :
    L0 :word32 = 0b11001100000000001100110011111111w
End

Definition R0_def :
    R0 :word32 = 0b11110000101010101111000010101010w
End

Theorem Test_E_R0 :
    E R0 = 0b11110100001010101010101011110100001010101010101w
Proof
    EVAL_TAC
QED

Definition K1_def :
    K1 :word48 = 0b000110110000001011101111111111000111000001110010w
End

Theorem Test_K1_X_E_R0 :
    K1 ?? E R0 = 0b11000010001011110111010100001100110010100100111w
Proof
    EVAL_TAC
QED

(* EVAL “S (K1 ?? E R0)” *)
Theorem Test_S_K1_X_E_R0 :
    S (K1 ?? E R0) = 0b01011100100000101011010110010111w
Proof
    EVAL_TAC
QED

(* EVAL “P (S (K1 ?? E R0))” *)
Theorem Test_P_S_K1_X_E_R0[compute] :
    P (S (K1 ?? E R0)) = 0b00100011010010101010100110111011w
Proof
    EVAL_TAC
QED

(* EVAL “Round 1 16 Test_KS (Split (IP Test_M))” *)
Theorem Test_Round_1[compute] :
    Round 1 Test_KS (Split (IP Test_M)) =
      (0b11110000101010101111000010101010w, (* L1 = R0 *)
       0b11101111010010100110010101000100w) (* R1 *)
Proof
    EVAL_TAC
QED

Definition R1_def :
    R1 :word32 = 0b11101111010010100110010101000100w
End

Theorem Test_R1[compute] :
    R1 = L0 ?? P (S (K1 ?? E R0))
Proof
    EVAL_TAC
QED

(* EVAL “Round 2 16 Test_KS (Split (IP Test_M))” *)
Theorem Test_Round_2[compute] :
    Round 2 Test_KS (Split (IP Test_M)) =
      (0b11101111010010100110010101000100w, (* L2 = R1 *)
       0b11001100000000010111011100001001w) (* R2 *)
Proof
    EVAL_TAC
QED

(* EVAL “Round 16 16 Test_KS (Split (IP Test_M))”

   L16 = 0100 0011 0100 0010 0011 0010 0011 0100
   R16 = 0000 1010 0100 1100 1101 1001 1001 0101
 *)
Theorem Test_Round_16[compute] :
    Round 16 Test_KS (Split (IP Test_M)) =
      (0b01000011010000100011001000110100w, (* L16 *)
       0b00001010010011001101100110010101w) (* R16 *)
Proof
    EVAL_TAC
QED

(* EVAL “FullDESEnc Test_K Test_M”

   FullDESEnc Test_K Test_M = IIP(R16 @@ L16) =
     10000101 11101000 00010011 01010100 00001111 00001010 10110100 00000101
 *)
Definition Test_C :
    Test_C :word64 =
      0b1000010111101000000100110101010000001111000010101011010000000101w
End

Theorem Test_FullDES_K_M :
    let (encrypt,decrypt) = FullDES Test_K in encrypt Test_M = Test_C
Proof
    EVAL_TAC
QED

(* EVAL “FullDESDec Test_K Test_C” *)
Theorem Test_FullDES_K_C :
    let (encrypt,decrypt) = FullDES Test_K in decrypt Test_C = Test_M
Proof
    EVAL_TAC
QED

(* Go back to HEX (padded) outputs, also for theory exporting purposes *)
val _ = output_words_as_padded_hex();

(* EVAL “FullDESEnc 0w 0w”, Encrypted text: "8c a6 4d e9 c1 b1 23 a7" [3] *)
Theorem Test_FullDES_0 :
    let (encrypt,decrypt) = FullDES 0w in encrypt 0w = 0x8CA64DE9C1B123A7w
Proof
    EVAL_TAC
QED

Theorem Test_FullDES_0' :
    let (encrypt,decrypt) = FullDES 0w in decrypt 0x8CA64DE9C1B123A7w = 0w
Proof
    EVAL_TAC
QED

(* DES reduced to 4 rounds *)
Theorem Test_DES_4 :
    let (encrypt,decrypt) = DES 4 Test_K in decrypt (encrypt 0w) = 0w
Proof
    EVAL_TAC
QED

(* DES reduced to 5 rounds (thus odd round also works) *)
Theorem Test_DES_5 :
    let (encrypt,decrypt) = DES 4 Test_K in decrypt (encrypt 0w) = 0w
Proof
    EVAL_TAC
QED

val _ = export_theory();
val _ = html_theory "des_test";

(* References:

 [1] Knudsen, L.R., Robshaw, M.J.B.: The Block Cipher Companion. Springer
     Publishing Company, Incorporated, Berlin, Heidelberg (2011).
 [2] Grabbe, J.O.: The DES Algorithm Illustrated,
     https://page.math.tu-berlin.de/~kant/teaching/hess/krypto-ws2006/des.htm.
 [3] DES - Symmetric Ciphers Online. http://des.online-domain-tools.com

 *)
