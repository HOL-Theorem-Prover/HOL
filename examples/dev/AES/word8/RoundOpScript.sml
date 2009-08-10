(*---------------------------------------------------------------------------*)
(* Operations performed in a round:                                          *)
(*                                                                           *)
(*    - applying Sboxes                                                      *)
(*    - shifting rows                                                        *)
(*    - mixing columns                                                       *)
(*    - adding round keys                                                    *)
(*                                                                           *)
(* We prove "inversion" theorems for each of these                           *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

(* For interactive work
  quietdec := true;
  app load ["MultTheory", "tablesTheory", "wordsLib"];
  quietdec := false;
*)

open HolKernel Parse boolLib bossLib;
open pairTheory wordsTheory MultTheory wordsLib;

(*---------------------------------------------------------------------------*)
(* Make bindings to pre-existing stuff                                       *)
(*---------------------------------------------------------------------------*)

val RESTR_EVAL_TAC = computeLib.RESTR_EVAL_TAC;

val Sbox_Inversion = tablesTheory.Sbox_Inversion;

(*---------------------------------------------------------------------------*)
(* Create the theory.                                                        *)
(*---------------------------------------------------------------------------*)

val _ = new_theory "RoundOp";

(*---------------------------------------------------------------------------*)
(* A block is 16 bytes. A state also has that type, although states have     *)
(* a special format.                                                         *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("block",
                    Type`:word8 # word8 # word8 # word8 #
                          word8 # word8 # word8 # word8 #
                          word8 # word8 # word8 # word8 #
                          word8 # word8 # word8 # word8`);

val _ = type_abbrev("state", Type`:block`);
val _ = type_abbrev("key",   Type`:state`);
val _ = type_abbrev("w8x4",  Type`:word8 # word8 # word8 # word8`);


val ZERO_BLOCK_def =
 Define
   `ZERO_BLOCK = (0w,0w,0w,0w,
                  0w,0w,0w,0w,
                  0w,0w,0w,0w,
                  0w,0w,0w,0w) : block`;

(*---------------------------------------------------------------------------*)
(* Case analysis on a block.                                                 *)
(*---------------------------------------------------------------------------*)

val FORALL_BLOCK = Q.store_thm
("FORALL_BLOCK",
 `(!b:block. P b) =
   !w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16.
    P (w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16)`,
 SIMP_TAC std_ss [FORALL_PROD]);

(*---------------------------------------------------------------------------*)
(* XOR on blocks. Definition and algebraic properties.                       *)
(*---------------------------------------------------------------------------*)

val XOR_BLOCK_def = Define
 `XOR_BLOCK ((a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15):block)
            ((b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15):block)
       =
      (a0 ?? b0,   a1 ?? b1,   a2 ?? b2,   a3 ?? b3,
       a4 ?? b4,   a5 ?? b5,   a6 ?? b6,   a7 ?? b7,
       a8 ?? b8,   a9 ?? b9,   a10 ?? b10, a11 ?? b11,
       a12 ?? b12, a13 ?? b13, a14 ?? b14, a15 ?? b15)`;

val XOR_BLOCK_ZERO = Q.store_thm
("XOR_BLOCK_ZERO",
 `!x:block. XOR_BLOCK x ZERO_BLOCK = x`,
 SIMP_TAC std_ss
   [FORALL_BLOCK,XOR_BLOCK_def, ZERO_BLOCK_def, WORD_XOR_CLAUSES]);

val XOR_BLOCK_INV = Q.store_thm
("XOR_BLOCK_INV",
 `!x:block. XOR_BLOCK x x = ZERO_BLOCK`,
 SIMP_TAC std_ss
   [FORALL_BLOCK,XOR_BLOCK_def, ZERO_BLOCK_def, WORD_XOR_CLAUSES]);

val XOR_BLOCK_AC = Q.store_thm
("XOR_BLOCK_AC",
 `(!x y z:block. XOR_BLOCK (XOR_BLOCK x y) z = XOR_BLOCK x (XOR_BLOCK y z)) /\
  (!x y:block. XOR_BLOCK x y = XOR_BLOCK y x)`,
 SIMP_TAC (srw_ss()) [FORALL_BLOCK,XOR_BLOCK_def]);

val XOR_BLOCK_IDEM = Q.store_thm
("XOR_BLOCK_IDEM",
 `(!v u. XOR_BLOCK (XOR_BLOCK v u) u = v) /\
  (!v u. XOR_BLOCK v (XOR_BLOCK v u) = u)`,
 METIS_TAC [XOR_BLOCK_INV,XOR_BLOCK_AC,XOR_BLOCK_ZERO]);

(*---------------------------------------------------------------------------*)
(*    Moving data into and out of a state                                    *)
(*---------------------------------------------------------------------------*)

val to_state_def = Define
 `to_state ((b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15) :block)
                =
            (b0,b4,b8,b12,
             b1,b5,b9,b13,
             b2,b6,b10,b14,
             b3,b7,b11,b15) : state`;

val from_state_def = Define
 `from_state((b0,b4,b8,b12,
              b1,b5,b9,b13,
              b2,b6,b10,b14,
              b3,b7,b11,b15) :state)
 = (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15) : block`;


val to_state_Inversion = Q.store_thm
  ("to_state_Inversion",
   `!s:state. from_state(to_state s) = s`,
   SIMP_TAC std_ss [FORALL_BLOCK, from_state_def, to_state_def]);


val from_state_Inversion = Q.store_thm
  ("from_state_Inversion",
   `!s:state. to_state(from_state s) = s`,
   SIMP_TAC std_ss [FORALL_BLOCK, from_state_def, to_state_def]);


(*---------------------------------------------------------------------------*)
(*    Apply an Sbox to the state                                             *)
(*---------------------------------------------------------------------------*)

val _ = Parse.hide "S";   (* to make parameter S a variable *)

val genSubBytes_def = try Define
  `genSubBytes S ((b00,b01,b02,b03,
                   b10,b11,b12,b13,
                   b20,b21,b22,b23,
                   b30,b31,b32,b33) :state)
                          =
             (S b00, S b01, S b02, S b03,
              S b10, S b11, S b12, S b13,
              S b20, S b21, S b22, S b23,
              S b30, S b31, S b32, S b33) :state`;

val _ = Parse.reveal "S";

val SubBytes_def    = Define `SubBytes = genSubBytes Sbox`;
val InvSubBytes_def = Define `InvSubBytes = genSubBytes InvSbox`;

val SubBytes_Inversion = Q.store_thm
("SubBytes_Inversion",
 `!s:state. genSubBytes InvSbox (genSubBytes Sbox s) = s`,
 SIMP_TAC std_ss [FORALL_BLOCK,genSubBytes_def,Sbox_Inversion]);


(*---------------------------------------------------------------------------
    Left-shift the first row not at all, the second row by 1, the
    third row by 2, and the last row by 3. And the inverse operation.
 ---------------------------------------------------------------------------*)

val ShiftRows_def = Define
  `ShiftRows ((b00,b01,b02,b03,
               b10,b11,b12,b13,
               b20,b21,b22,b23,
               b30,b31,b32,b33) :state)
                     =
             (b00,b01,b02,b03,
              b11,b12,b13,b10,
              b22,b23,b20,b21,
              b33,b30,b31,b32) :state`;

val InvShiftRows_def = Define
  `InvShiftRows ((b00,b01,b02,b03,
                  b11,b12,b13,b10,
                  b22,b23,b20,b21,
                  b33,b30,b31,b32) :state)
                     =
                (b00,b01,b02,b03,
                 b10,b11,b12,b13,
                 b20,b21,b22,b23,
                 b30,b31,b32,b33) :state`;

(*---------------------------------------------------------------------------
        InvShiftRows inverts ShiftRows
 ---------------------------------------------------------------------------*)

val ShiftRows_Inversion = Q.store_thm
("ShiftRows_Inversion",
 `!s:state. InvShiftRows (ShiftRows s) = s`,
 SIMP_TAC std_ss [FORALL_BLOCK] THEN REPEAT STRIP_TAC THEN EVAL_TAC);


(*---------------------------------------------------------------------------*)
(* For alternative decryption scheme                                         *)
(*---------------------------------------------------------------------------*)

val ShiftRows_SubBytes_Commute = Q.store_thm
 ("ShiftRows_SubBytes_Commute",
  `!s. ShiftRows (SubBytes s) = SubBytes (ShiftRows s)`,
 SIMP_TAC std_ss [FORALL_BLOCK] THEN REPEAT STRIP_TAC THEN EVAL_TAC);


val InvShiftRows_InvSubBytes_Commute = Q.store_thm
 ("InvShiftRows_InvSubBytes_Commute",
  `!s. InvShiftRows (InvSubBytes s) = InvSubBytes (InvShiftRows s)`,
 SIMP_TAC std_ss [FORALL_BLOCK] THEN REPEAT STRIP_TAC THEN EVAL_TAC);


(*---------------------------------------------------------------------------
        Column multiplication and its inverse
 ---------------------------------------------------------------------------*)

val MultCol_def = Define
 `MultCol (a,b,c,d) =
   ((2w ** a) ?? (3w ** b) ??  c        ?? d,
     a        ?? (2w ** b) ?? (3w ** c) ?? d,
     a        ??  b        ?? (2w ** c) ?? (3w ** d),
    (3w ** a) ??  b        ??  c        ?? (2w ** d))`;

val InvMultCol_def = Define
 `InvMultCol (a,b,c,d) =
   ((0xEw ** a) ?? (0xBw ** b) ?? (0xDw ** c) ?? (9w   ** d),
    (9w   ** a) ?? (0xEw ** b) ?? (0xBw ** c) ?? (0xDw ** d),
    (0xDw ** a) ?? (9w   ** b) ?? (0xEw ** c) ?? (0xBw ** d),
    (0xBw ** a) ?? (0xDw ** b) ?? (9w   ** c) ?? (0xEw ** d))`;

(*---------------------------------------------------------------------------*)
(* Inversion lemmas for column multiplication. Proved with an ad-hoc tactic  *)
(*---------------------------------------------------------------------------*)

val BYTE_CASES_TAC =
  Cases
    THEN FULL_SIMP_TAC std_ss [wordsTheory.dimword_8,
           CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM]
    THEN RW_TAC std_ss [fetch "Mult" "mult_tables"]
    THEN REWRITE_TAC [fetch "Mult" "mult_tables"]
    THEN WORD_EVAL_TAC;


val lemma_a1 = Count.apply Q.prove
(`!a. 0xEw ** (2w ** a) ?? 0xBw ** a ?? 0xDw ** a ?? 9w ** (3w ** a) = a`,
 BYTE_CASES_TAC);

val lemma_a2 = Count.apply Q.prove
(`!b. 0xEw ** (3w ** b) ?? 0xBw ** (2w ** b) ?? 0xDw ** b ?? 9w  ** b = 0w`,
 BYTE_CASES_TAC);

val lemma_a3 = Count.apply Q.prove
(`!c. 0xEw ** c ?? 0xBw ** (3w ** c) ?? 0xDw ** (2w ** c) ?? 9w ** c = 0w`,
 BYTE_CASES_TAC);

val lemma_a4 = Count.apply Q.prove
(`!d. 0xEw ** d ?? 0xBw ** d ?? 0xDw ** (3w ** d) ?? 9w ** (2w ** d) = 0w`,
 BYTE_CASES_TAC);

val lemma_b1 = Count.apply Q.prove
(`!a. 9w ** (2w ** a) ?? 0xEw ** a ?? 0xBw ** a ?? 0xDw  ** (3w ** a) = 0w`,
 BYTE_CASES_TAC);

val lemma_b2 = Count.apply Q.prove
(`!b. 9w ** (3w ** b) ?? 0xEw ** (2w ** b) ?? 0xBw ** b ?? 0xDw ** b = b`,
 BYTE_CASES_TAC);

val lemma_b3 = Count.apply Q.prove
(`!c. 9w ** c ?? 0xEw ** (3w ** c) ?? 0xBw ** (2w ** c) ?? 0xDw ** c = 0w`,
 BYTE_CASES_TAC);

val lemma_b4 = Count.apply Q.prove
(`!d. 9w ** d ?? 0xEw ** d ?? 0xBw ** (3w ** d) ?? 0xDw ** (2w ** d) = 0w`,
 BYTE_CASES_TAC);

val lemma_c1 = Count.apply Q.prove
(`!a. 0xDw ** (2w ** a) ?? 9w ** a ?? 0xEw ** a ?? 0xBw  ** (3w ** a) = 0w`,
 BYTE_CASES_TAC THEN EVAL_TAC);

val lemma_c2 = Count.apply Q.prove
(`!b. 0xDw ** (3w ** b) ?? 9w ** (2w ** b) ?? 0xEw ** b ?? 0xBw ** b = 0w`,
 BYTE_CASES_TAC);

val lemma_c3 = Count.apply Q.prove
(`!c. 0xDw ** c ?? 9w ** (3w ** c) ?? 0xEw ** (2w ** c) ?? 0xBw ** c = c`,
 BYTE_CASES_TAC);

val lemma_c4 = Count.apply Q.prove
(`!d. 0xDw ** d ?? 9w ** d ?? 0xEw ** (3w ** d) ?? 0xBw ** (2w ** d) = 0w`,
 BYTE_CASES_TAC);

val lemma_d1 = Count.apply Q.prove
(`!a. 0xBw ** (2w ** a) ?? 0xDw ** a ?? 9w ** a ?? 0xEw  ** (3w ** a) = 0w`,
 BYTE_CASES_TAC);

val lemma_d2 = Count.apply Q.prove
(`!b. 0xBw ** (3w ** b) ?? 0xDw ** (2w ** b) ?? 9w ** b ?? 0xEw ** b = 0w`,
 BYTE_CASES_TAC);

val lemma_d3 = Count.apply Q.prove
(`!c. 0xBw ** c ?? 0xDw ** (3w ** c) ?? 9w ** (2w ** c) ?? 0xEw ** c = 0w`,
 BYTE_CASES_TAC THEN EVAL_TAC);

val lemma_d4 = Count.apply Q.prove
(`!d. 0xBw ** d ?? 0xDw ** d ?? 9w ** (3w ** d) ?? 0xEw ** (2w ** d) = d`,
 BYTE_CASES_TAC);

(*---------------------------------------------------------------------------*)
(* The following lemma is hideous to prove without permutative rewriting     *)
(*---------------------------------------------------------------------------*)

val rearrange_xors = Q.prove
(`(a1 ?? b1 ?? c1 ?? d1) ??
  (a2 ?? b2 ?? c2 ?? d2) ??
  (a3 ?? b3 ?? c3 ?? d3) ??
  (a4 ?? b4 ?? c4 ?? d4)
     =
  (a1 ?? a2 ?? a3 ?? a4) ??
  (b1 ?? b2 ?? b3 ?? b4) ??
  (c1 ?? c2 ?? c3 ?? c4) ??
  (d1 ?? d2 ?? d3 ?? d4)`,
 SRW_TAC [] []);

val mix_lemma1 = Q.prove
(`!a b c d.
   (0xEw ** ((2w ** a) ?? (3w ** b) ?? c ?? d)) ??
   (0xBw ** (a ?? (2w ** b) ?? (3w ** c) ?? d)) ??
   (0xDw ** (a ?? b ?? (2w ** c) ?? (3w ** d))) ??
   (9w  ** ((3w ** a) ?? b ?? c ?? (2w ** d)))
      = a`,
 RW_TAC std_ss [ConstMultDistrib]
   THEN ONCE_REWRITE_TAC [rearrange_xors]
   THEN RW_TAC std_ss [lemma_a1,lemma_a2,lemma_a3,lemma_a4,WORD_XOR_CLAUSES]);

val mix_lemma2 = Q.prove
(`!a b c d.
   (9w  ** ((2w ** a) ?? (3w ** b) ?? c ?? d)) ??
   (0xEw ** (a ?? (2w ** b) ?? (3w ** c) ?? d)) ??
   (0xBw ** (a ?? b ?? (2w ** c) ?? (3w ** d))) ??
   (0xDw ** ((3w ** a) ?? b ?? c ?? (2w ** d)))
     = b`,
 RW_TAC std_ss [ConstMultDistrib]
   THEN ONCE_REWRITE_TAC [rearrange_xors]
   THEN RW_TAC std_ss [lemma_b1,lemma_b2,lemma_b3,lemma_b4,WORD_XOR_CLAUSES]);

val mix_lemma3 = Q.prove
(`!a b c d.
   (0xDw ** ((2w ** a) ?? (3w ** b) ?? c ?? d)) ??
   (9w  ** (a ?? (2w ** b) ?? (3w ** c) ?? d)) ??
   (0xEw ** (a ?? b ?? (2w ** c) ?? (3w ** d))) ??
   (0xBw ** ((3w ** a) ?? b ?? c ?? (2w ** d)))
     = c`,
 RW_TAC std_ss [ConstMultDistrib]
   THEN ONCE_REWRITE_TAC [rearrange_xors]
   THEN RW_TAC std_ss [lemma_c1,lemma_c2,lemma_c3,lemma_c4,WORD_XOR_CLAUSES]);

val mix_lemma4 = Q.prove
(`!a b c d.
   (0xBw ** ((2w ** a) ?? (3w ** b) ?? c ?? d)) ??
   (0xDw ** (a ?? (2w ** b) ?? (3w ** c) ?? d)) ??
   (9w  ** (a ?? b ?? (2w ** c) ?? (3w ** d))) ??
   (0xEw ** ((3w ** a) ?? b ?? c ?? (2w ** d)))
     = d`,
 RW_TAC std_ss [ConstMultDistrib]
   THEN ONCE_REWRITE_TAC [rearrange_xors]
   THEN RW_TAC std_ss [lemma_d1,lemma_d2,lemma_d3,lemma_d4,WORD_XOR_CLAUSES]);

(*---------------------------------------------------------------------------*)
(* Get the constants of various definitions                                  *)
(*---------------------------------------------------------------------------*)

val mult = Term `Mult$**`;
val n2w = Term `n2w`;

(*---------------------------------------------------------------------------*)
(* Mixing columns                                                            *)
(*---------------------------------------------------------------------------*)

val genMixColumns_def = Define
 `genMixColumns MC ((b00,b01,b02,b03,
                     b10,b11,b12,b13,
                     b20,b21,b22,b23,
                     b30,b31,b32,b33) :state)
 = let (b00', b10', b20', b30') = MC (b00,b10,b20,b30) in
   let (b01', b11', b21', b31') = MC (b01,b11,b21,b31) in
   let (b02', b12', b22', b32') = MC (b02,b12,b22,b32) in
   let (b03', b13', b23', b33') = MC (b03,b13,b23,b33)
   in
    (b00', b01', b02', b03',
     b10', b11', b12', b13',
     b20', b21', b22', b23',
     b30', b31', b32', b33') : state`;


val MixColumns_def    = Define `MixColumns    = genMixColumns MultCol`;
val InvMixColumns_def = Define `InvMixColumns = genMixColumns InvMultCol`;

val MixColumns_Inversion = Q.store_thm
("MixColumns_Inversion",
 `!s. genMixColumns InvMultCol (genMixColumns MultCol s) = s`,
 SIMP_TAC std_ss [FORALL_BLOCK]
  THEN RESTR_EVAL_TAC [mult,n2w]
  THEN RW_TAC std_ss [mix_lemma1,mix_lemma2,mix_lemma3,mix_lemma4]);


(*---------------------------------------------------------------------------
    Pairwise XOR the state with the round key
 ---------------------------------------------------------------------------*)

val AddRoundKey_def = Define `AddRoundKey = XOR_BLOCK`;

(*---------------------------------------------------------------------------*)
(* For alternative decryption scheme                                         *)
(*---------------------------------------------------------------------------*)

val InvMixColumns_Distrib = Q.store_thm
("InvMixColumns_Distrib",
 `!s k. InvMixColumns (AddRoundKey s k)
            =
        AddRoundKey (InvMixColumns s) (InvMixColumns k)`,
 SIMP_TAC std_ss [FORALL_BLOCK] THEN
 SRW_TAC [] [XOR_BLOCK_def, AddRoundKey_def, InvMixColumns_def, LET_THM,
             genMixColumns_def, InvMultCol_def, ConstMultDistrib]);


val _ = export_theory();
