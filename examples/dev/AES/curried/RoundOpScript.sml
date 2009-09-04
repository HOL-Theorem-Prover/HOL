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
  app load ["metisLib","MultTheory"];
  open word8Theory pairTheory metisLib;
  quietdec := false;
*)

open HolKernel Parse boolLib bossLib
     metisLib pairTheory word8Theory tablesTheory MultTheory;

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


val ZERO_BLOCK_def = Define
 `ZERO_BLOCK = (ZERO,ZERO,ZERO,ZERO,ZERO,ZERO,ZERO,ZERO,
                ZERO,ZERO,ZERO,ZERO,ZERO,ZERO,ZERO,ZERO) : block`;

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
      (a0 # b0,   a1 # b1,   a2 # b2,   a3 # b3,
       a4 # b4,   a5 # b5,   a6 # b6,   a7 # b7,
       a8 # b8,   a9 # b9,   a10 # b10, a11 # b11,
       a12 # b12, a13 # b13, a14 # b14, a15 # b15)`;

val XOR_BLOCK_ZERO = Q.store_thm
("XOR_BLOCK_ZERO",
 `!x:block. XOR_BLOCK x ZERO_BLOCK = x`,
 SIMP_TAC std_ss [FORALL_BLOCK,XOR_BLOCK_def, ZERO_BLOCK_def, XOR8_ZERO]);

val XOR_BLOCK_INV = Q.store_thm
("XOR_BLOCK_INV",
 `!x:block. XOR_BLOCK x x = ZERO_BLOCK`,
 SIMP_TAC std_ss [FORALL_BLOCK,XOR_BLOCK_def, ZERO_BLOCK_def, XOR8_INV]);

val XOR_BLOCK_AC = Q.store_thm
("XOR_BLOCK_AC",
 `(!x y z:block. XOR_BLOCK (XOR_BLOCK x y) z = XOR_BLOCK x (XOR_BLOCK y z)) /\
  (!x y:block. XOR_BLOCK x y = XOR_BLOCK y x)`,
 SIMP_TAC std_ss [FORALL_BLOCK,XOR_BLOCK_def, XOR8_AC]);

val [a,c] = CONJUNCTS XOR8_AC;

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
   ((TWO ** a)   # (THREE ** b) #  c           # d,
     a           # (TWO ** b)   # (THREE ** c) # d,
     a           #  b           # (TWO ** c)   # (THREE ** d),
    (THREE ** a) #  b           #  c           # (TWO ** d))`;

val InvMultCol_def = Define
 `InvMultCol (a,b,c,d) =
   ((E_HEX ** a) # (B_HEX ** b) # (D_HEX ** c) # (NINE  ** d),
    (NINE  ** a) # (E_HEX ** b) # (B_HEX ** c) # (D_HEX ** d),
    (D_HEX ** a) # (NINE  ** b) # (E_HEX ** c) # (B_HEX ** d),
    (B_HEX ** a) # (D_HEX ** b) # (NINE  ** c) # (E_HEX ** d))`;

(*---------------------------------------------------------------------------*)
(* Table-lookup versions of MultCol and InvMultCol.Faster to use, but        *)
(* require tables (consume space).                                           *)
(*---------------------------------------------------------------------------*)

val TabledMultCol = Q.store_thm
("TabledMultCol",
 `MultCol(a,b,c,d) =
    (GF256_by_2 a # GF256_by_3 b # c # d,
     a # GF256_by_2 b # GF256_by_3 c # d,
     a # b # GF256_by_2 c # GF256_by_3 d,
     GF256_by_3 a # b # c # GF256_by_2 d)`,
 SIMP_TAC std_ss [MultCol_def] THEN
 SIMP_TAC std_ss (tcm_thm::map SYM (CONJUNCTS (SPEC_ALL MultEquiv))));

val TabledInvMultCol =
 Q.store_thm
 ("TabledInvMultCol",
  `InvMultCol (a,b,c,d) =
    (GF256_by_14 a # GF256_by_11 b # GF256_by_13 c # GF256_by_9 d,
     GF256_by_9 a # GF256_by_14 b # GF256_by_11 c # GF256_by_13 d,
     GF256_by_13 a # GF256_by_9 b # GF256_by_14 c # GF256_by_11 d,
     GF256_by_11 a # GF256_by_13 b # GF256_by_9 c # GF256_by_14 d)`,
 SIMP_TAC std_ss [InvMultCol_def] THEN
 SIMP_TAC std_ss (tcm_thm::map SYM (CONJUNCTS (SPEC_ALL MultEquiv))));


(*---------------------------------------------------------------------------*)
(* Inversion lemmas for column multiplication. Proved with an ad-hoc tactic  *)
(*                                                                           *)
(* Note: could just use case analysis with Sbox_ind, then EVAL_TAC, but      *)
(* that's far slower.                                                        *)
(*---------------------------------------------------------------------------*)

val BYTE_CASES_TAC =
  SIMP_TAC std_ss (tcm_thm::map SYM (CONJUNCTS (SPEC_ALL MultEquiv)))
    THEN Ho_Rewrite.ONCE_REWRITE_TAC [FORALL_BYTE_BITS]
    THEN EVAL_TAC;

val lemma_a1 = Count.apply Q.prove
(`!a. E_HEX ** (TWO ** a) # B_HEX ** a # D_HEX ** a # NINE ** (THREE ** a) = a`,
 BYTE_CASES_TAC);

val lemma_a2 = Count.apply Q.prove
(`!b. E_HEX ** (THREE ** b) # B_HEX ** (TWO ** b) # D_HEX ** b # NINE  ** b = ZERO`,
 BYTE_CASES_TAC);

val lemma_a3 = Count.apply Q.prove
(`!c. E_HEX ** c # B_HEX ** (THREE ** c) # D_HEX ** (TWO ** c) # NINE ** c = ZERO`,
 BYTE_CASES_TAC);

val lemma_a4 = Count.apply Q.prove
(`!d. E_HEX ** d # B_HEX ** d # D_HEX ** (THREE ** d) # NINE ** (TWO ** d) = ZERO`,
 BYTE_CASES_TAC);

val lemma_b1 = Count.apply Q.prove
(`!a. NINE ** (TWO ** a) # E_HEX ** a # B_HEX ** a # D_HEX  ** (THREE ** a) = ZERO`,
 BYTE_CASES_TAC);

val lemma_b2 = Count.apply Q.prove
(`!b. NINE ** (THREE ** b) # E_HEX ** (TWO ** b) # B_HEX ** b # D_HEX ** b = b`,
 BYTE_CASES_TAC);

val lemma_b3 = Count.apply Q.prove
(`!c. NINE ** c # E_HEX ** (THREE ** c) # B_HEX ** (TWO ** c) # D_HEX ** c = ZERO`,
 BYTE_CASES_TAC);

val lemma_b4 = Count.apply Q.prove
(`!d. NINE ** d # E_HEX ** d # B_HEX ** (THREE ** d) # D_HEX ** (TWO ** d) = ZERO`,
 BYTE_CASES_TAC);

val lemma_c1 = Count.apply Q.prove
(`!a. D_HEX ** (TWO ** a) # NINE ** a # E_HEX ** a # B_HEX  ** (THREE ** a) = ZERO`,
 BYTE_CASES_TAC THEN EVAL_TAC);

val lemma_c2 = Count.apply Q.prove
(`!b. D_HEX ** (THREE ** b) # NINE ** (TWO ** b) # E_HEX ** b # B_HEX ** b = ZERO`,
 BYTE_CASES_TAC);

val lemma_c3 = Count.apply Q.prove
(`!c. D_HEX ** c # NINE ** (THREE ** c) # E_HEX ** (TWO ** c) # B_HEX ** c = c`,
 BYTE_CASES_TAC);

val lemma_c4 = Count.apply Q.prove
(`!d. D_HEX ** d # NINE ** d # E_HEX ** (THREE ** d) # B_HEX ** (TWO ** d) = ZERO`,
 BYTE_CASES_TAC);

val lemma_d1 = Count.apply Q.prove
(`!a. B_HEX ** (TWO ** a) # D_HEX ** a # NINE ** a # E_HEX  ** (THREE ** a) = ZERO`,
 BYTE_CASES_TAC);

val lemma_d2 = Count.apply Q.prove
(`!b. B_HEX ** (THREE ** b) # D_HEX ** (TWO ** b) # NINE ** b # E_HEX ** b = ZERO`,
 BYTE_CASES_TAC);

val lemma_d3 = Count.apply Q.prove
(`!c. B_HEX ** c # D_HEX ** (THREE ** c) # NINE ** (TWO ** c) # E_HEX ** c = ZERO`,
 BYTE_CASES_TAC THEN EVAL_TAC);

val lemma_d4 = Count.apply Q.prove
(`!d. B_HEX ** d # D_HEX ** d # NINE ** (THREE ** d) # E_HEX ** (TWO ** d) = d`,
 BYTE_CASES_TAC);

(*---------------------------------------------------------------------------*)
(* The following lemma is hideous to prove without permutative rewriting     *)
(*---------------------------------------------------------------------------*)

val rearrange_xors = Q.prove
(`(a1 # b1 # c1 # d1) #
  (a2 # b2 # c2 # d2) #
  (a3 # b3 # c3 # d3) #
  (a4 # b4 # c4 # d4)
     =
  (a1 # a2 # a3 # a4) #
  (b1 # b2 # b3 # b4) #
  (c1 # c2 # c3 # c4) #
  (d1 # d2 # d3 # d4)`,
 RW_TAC std_ss [AC a c]);

val mix_lemma1 = Q.prove
(`!a b c d.
   (E_HEX ** ((TWO ** a) # (THREE ** b) # c # d)) #
   (B_HEX ** (a # (TWO ** b) # (THREE ** c) # d)) #
   (D_HEX ** (a # b # (TWO ** c) # (THREE ** d))) #
   (NINE  ** ((THREE ** a) # b # c # (TWO ** d)))
      = a`,
 RW_TAC std_ss [ConstMultDistrib]
   THEN ONCE_REWRITE_TAC [rearrange_xors]
   THEN RW_TAC std_ss [lemma_a1,lemma_a2,lemma_a3,lemma_a4,XOR8_ZERO]);

val mix_lemma2 = Q.prove
(`!a b c d.
   (NINE  ** ((TWO ** a) # (THREE ** b) # c # d)) #
   (E_HEX ** (a # (TWO ** b) # (THREE ** c) # d)) #
   (B_HEX ** (a # b # (TWO ** c) # (THREE ** d))) #
   (D_HEX ** ((THREE ** a) # b # c # (TWO ** d)))
     = b`,
 RW_TAC std_ss [ConstMultDistrib]
   THEN ONCE_REWRITE_TAC [rearrange_xors]
   THEN RW_TAC std_ss [lemma_b1,lemma_b2,lemma_b3,lemma_b4,
                       XOR8_ZERO, ONCE_REWRITE_RULE [XOR8_AC] XOR8_ZERO]);

val mix_lemma3 = Q.prove
(`!a b c d.
   (D_HEX ** ((TWO ** a) # (THREE ** b) # c # d)) #
   (NINE  ** (a # (TWO ** b) # (THREE ** c) # d)) #
   (E_HEX ** (a # b # (TWO ** c) # (THREE ** d))) #
   (B_HEX ** ((THREE ** a) # b # c # (TWO ** d)))
     = c`,
 RW_TAC std_ss [ConstMultDistrib]
   THEN ONCE_REWRITE_TAC [rearrange_xors]
   THEN RW_TAC std_ss [lemma_c1,lemma_c2,lemma_c3,lemma_c4,
                       XOR8_ZERO, ONCE_REWRITE_RULE [XOR8_AC] XOR8_ZERO]);

val mix_lemma4 = Q.prove
(`!a b c d.
   (B_HEX ** ((TWO ** a) # (THREE ** b) # c # d)) #
   (D_HEX ** (a # (TWO ** b) # (THREE ** c) # d)) #
   (NINE  ** (a # b # (TWO ** c) # (THREE ** d))) #
   (E_HEX ** ((THREE ** a) # b # c # (TWO ** d)))
     = d`,
 RW_TAC std_ss [ConstMultDistrib]
   THEN ONCE_REWRITE_TAC [rearrange_xors]
   THEN RW_TAC std_ss [lemma_d1,lemma_d2,lemma_d3,lemma_d4,
                       XOR8_ZERO, ONCE_REWRITE_RULE [XOR8_AC] XOR8_ZERO]);

(*---------------------------------------------------------------------------*)
(* Get the constants of various definitions                                  *)
(*---------------------------------------------------------------------------*)

val [mult]     = decls "**";
val [TWO]      = decls "TWO";
val [THREE]    = decls "THREE";
val [NINE]     = decls "NINE";
val [B_HEX]    = decls "B_HEX";
val [D_HEX]    = decls "D_HEX";
val [E_HEX]    = decls "E_HEX";

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
  THEN RESTR_EVAL_TAC [mult,B_HEX,D_HEX,E_HEX,TWO,THREE,NINE]
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
 RW_TAC std_ss [XOR_BLOCK_def, AddRoundKey_def, InvMixColumns_def, LET_THM,
                genMixColumns_def, InvMultCol_def, ConstMultDistrib, AC a c]);


val _ = export_theory();
