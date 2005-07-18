(*                                   Twofish Block Cipher
                                        -- implemented in Standard ML

Twofish is a 128-bit block cipher that accepts a variable-length key
up to 256 bits. The cipher is a 16-round Feistel network with a
bijective F function made up of four key-dependent 8-by-8-bit S-boxes,
a fixed 4-by-4 maximum distance separable matrix over GF(28), a
pseudo-Hadamard transform, bitwise rotations, and a carefully designed
key schedule. For more information, please refer to
        web site: http://www.counterpane.com/twofish.html
*)

(* For interactive work
  quietdec := true;
  app load ["arithmeticTheory","metisLib","word8Lib","word32Lib"];
  open arithmeticTheory word8Theory word32Theory 
       pairTheory metisLib bitsTheory word8Lib;
  quietdec := false;
*)

open HolKernel Parse boolLib bossLib
     arithmeticTheory word8Theory word32Theory 
     pairTheory metisLib bitsTheory word8Lib;

(*---------------------------------------------------------------------------*)
(* Make bindings to pre-existing stuff                                       *)
(*---------------------------------------------------------------------------*)

val RESTR_EVAL_TAC = computeLib.RESTR_EVAL_TAC;
val ARW_TAC = RW_TAC arith_ss;

(*---------------------------------------------------------------------------*)
(* Create the theory.                                                        *)
(*---------------------------------------------------------------------------*)

val _ = new_theory "twofish";

(*---------------------------------------------------------------------------*)
(* Type Definitions                                                          *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("block", ``:word32 # word32 # word32 # word32``);
val _ = type_abbrev("key",   ``:word32 # word32``);

val _ = type_abbrev("initkeys", 
        ``:word8 # word8 # word8 # word8 # word8 # word8 # word8 # word8 #
           word8 # word8 # word8 # word8 # word8 # word8 # word8 # word8 #
           word8 # word8 # word8 # word8 # word8 # word8 # word8 # word8 #
           word8 # word8 # word8 # word8 # word8 # word8 # word8 # word8``);

val _ = type_abbrev("keysched", 
   ``:word32 # word32 # word32 # word32 # word32 # word32 # word32 # word32 #
      word32 # word32 # word32 # word32 # word32 # word32 # word32 # word32 # 
      word32 # word32 # word32 # word32 # word32 # word32 # word32 # word32 # 
      word32 # word32 # word32 # word32 # word32 # word32 # word32 # word32 # 
      word32 # word32 # word32 # word32 # word32 # word32 # word32 # word32``);


(*---------------------------------------------------------------------------*)
(* Case analysis on a block and a pair of keys.                              *)
(*---------------------------------------------------------------------------*)

val FORALL_BLOCK = Q.store_thm
  ("FORALL_BLOCK", 
    `(!b:block. P b) = !v0 v1 v2 v3. P (v0,v1,v2,v3)`,
    SIMP_TAC std_ss [FORALL_PROD]);

val FORALL_KEY = Q.store_thm
  ("FORALL_KEY",
    `(!b:key. P b) = !k0 k1. P (k0,k1)`,
    SIMP_TAC std_ss [FORALL_PROD]);

(*---------------------------------------------------------------------------*)
(* Operations on word8, word32 and word4.                                    *)
(*---------------------------------------------------------------------------*)

val W8_ROL_def = Define `W8_ROL (x:word8) n =  word8$word_ror x (word8$WL - n)`;
val _ = overload_on ("#<<<",Term`$W8_ROL`);
val _ = overload_on ("#>>>",Term`word8$word_ror`);  (* Word8_ROR *)
val _ = set_fixity "#<<<" (Infixl 650);
val _ = set_fixity "#>>>" (Infixl 650);
val _ = overload_on ("##",Term`word8$bitwise_eor`);
val _ = set_fixity "##" (Infixl 640);

val W32_ROL_def = Define `W32_ROL (x:word32) n =  word32$word_ror x (word32$WL - n)`;
val _ = overload_on ("<<<<",Term`$W32_ROL`)
val _ = overload_on (">>>>",Term`word32$word_ror`);  (* Word32_ROR *)
val _ = set_fixity "<<<<" (Infixl 630);
val _ = set_fixity ">>>>" (Infixl 630);
val _ = overload_on ("###",Term`word32$bitwise_eor`);
val _ = set_fixity "###" (Infixl 620);


val Word32_SHIFT_Inversion = Q.store_thm
  ("Word32_SHIFT_Inversion",
  `!s n. n < word32$WL ==> ((s >>>> n <<<< n = s) /\ (s <<<< n >>>> n = s))`,
  REWRITE_TAC [W32_ROL_def,ROR_ADD] THEN ARW_TAC [SUB_LEFT_ADD] THEN
  METIS_TAC [ROR_CYCLE, MULT_CLAUSES]);


(* Word4 shifting operators *)
val ROR4_def = Define `ROR4(x:word8, n) = (x >> n) & ((x << (4 - n)) & 0xffffw)`;
val ROL4_def = Define `ROR4(x:word8, n) = (x << n) & ((x >> (4 - n)) & 0xffffw)`;


(* Conversion between word8*word8*word8*word8 and word32 *)
val toLarge_def = Define `toLarge (a3:word8,a2:word8,a1:word8,a0:word8) = 
	word32$n2w(w2n(a3)) << 24 + word32$n2w(w2n(a2)) << 16 + 
	word32$n2w(w2n(a1)) << 8 + word32$n2w(w2n(a0)) : word32`;
val fromLarge_def = Define `fromLarge (a:word32) = (word8$n2w(w2n(a >> 24)), 
	word8$n2w(w2n((a >> 16) & 0xffw)), word8$n2w(w2n((a >> 8) & 0xffw)),
	word8$n2w(w2n(a & 0xffw))) : word8 # word8 # word8 # word8 `;


(*---------------------------------------------------------------------------*)
(* Multiply a byte representing a polynomial by x. 			     *)
(*---------------------------------------------------------------------------*)

(* For MDS multiplication, v(x) = x^8 + x^6 + x^5 + x^3 + 1 , i.e. 0wx165    *)
val xtime1_def = Define
  `xtime1 (w : word8) =
     if MSB w then w << 1 ## 0x165w
              else w << 1`;

val _ = set_fixity "**" (Infixl 675);

val (Mult1_def,Mult1_ind) =
 Defn.tprove
  (Hol_defn "Mult1"
     `b1 ** b2 =
        if b1 = 0w then 0w else
        if LSB b1
           then b2 # ((word8$word_lsr b1 1) ** xtime1 b2)
           else      (word8$word_lsr b1 1) ** xtime1 b2`,
   WF_REL_TAC `measure (word8$w2n o FST)` THEN
   STRIP_TAC THEN word8CasesLib.word8Cases_on `b1` THEN
   RW_TAC std_ss [] THEN REPEAT (POP_ASSUM MP_TAC) THEN WORD_TAC);

val _ = save_thm("Mult1_def",Mult1_def);
val _ = save_thm("Mult1_ind",Mult1_ind);

(* For RS multiplication, v(x) = x^8 + x^6 + x^3 + x^2 + 1 , i.e. 0wx14D*)
val xtime2_def = Define
  `xtime2 (w : word8) =
     if MSB w then w << 1 ## 0x14Dw
     else w << 1`;

val _ = set_fixity "***" (Infixl 675);

val (Mult2_def,Mult2_ind) =
 Defn.tprove
  (Hol_defn "Mult2"
     `b1 *** b2 =
        if b1 = 0w then 0w else
        if LSB b1
           then b2 # ((word8$word_lsr b1 1) *** xtime2 b2)
           else      (word8$word_lsr b1 1) *** xtime2 b2`,
   WF_REL_TAC `measure (word8$w2n o FST)` THEN
   STRIP_TAC THEN word8CasesLib.word8Cases_on `b1` THEN
   RW_TAC std_ss [] THEN REPEAT (POP_ASSUM MP_TAC) THEN WORD_TAC);

val _ = save_thm("Mult2_def",Mult2_def);
val _ = save_thm("Mult2_ind",Mult2_ind);

(*-------------------------------------------------------------------------------*)
(* Matrix Column Multiplication 						 *)
(*-------------------------------------------------------------------------------*)

val InvW_def = Define `
    InvW (m0,m1,m2,m3): (word8 # word8 # word8 # word8) = (m3,m2,m1,m0)`;

(* Multiply the MDS matrix *)
val MDSMul_def = Define `MDSMul(m0,m1,m2,m3) =
  ((0x01w ** m0) ## (0xEFw ** m1) ## (0x5Bw ** m2) ## (0x5Bw ** m3),
   (0x5Bw ** m0) ## (0xEFw ** m1) ## (0xEFw ** m2) ## (0x01w ** m3),
   (0xEFw ** m0) ## (0x5Bw ** m1) ## (0x01w ** m2) ## (0xEFw ** m3),
   (0xEFw ** m0) ## (0x01w ** m1) ## (0xEFw ** m2) ## (0x5Bw ** m3))`;

(* Multiply the RS matrix *)
val RSMul_def = Define `RSMul(m0,m1,m2,m3,m4,m5,m6,m7) =
  ((0x01w *** m0) ## (0xA4w *** m1) ## (0x55w *** m2) ## (0x87w *** m3) ##
   (0x5Aw *** m4) ## (0x58w *** m5) ## (0xDBw *** m6) ## (0x9Ew *** m7),
   (0xA4w *** m0) ## (0x56w *** m1) ## (0x82w *** m2) ## (0xF3w *** m3) ##
   (0x1Ew *** m4) ## (0xC6w *** m5) ## (0x68w *** m6) ## (0xE5w *** m7),
   (0x02w *** m0) ## (0xA1w *** m1) ## (0xFCw *** m2) ## (0xC1w *** m3) ##
   (0x47w *** m4) ## (0xAEw *** m5) ## (0x3Dw *** m6) ## (0x19w *** m7),
   (0xA4w *** m0) ## (0x55w *** m1) ## (0x87w *** m2) ## (0x5Aw *** m3) ##
   (0x58w *** m4) ## (0xDBw *** m5) ## (0x9Ew *** m6) ## (0x03w *** m7))`;


(*---------------------------------------------------------------------------*)
(* The permutations q0 and q1 are fixed permutations on 8-bit values.	     *)
(* They are constructed from four different 4-bit permutations each. 	     *)
(*---------------------------------------------------------------------------*)

(* The 4-bit S-boxes For the permutation q0 *)
val t00_def = Define ` 
  t00 (x:word8) = 
    case x of 
    0w -> 0x8w || 1w -> 0x1w || 2w -> 0x7w || 3w -> 0xDw ||
    4w -> 0x6w || 5w -> 0xFw || 6w -> 0x3w || 7w -> 0x2w ||
    8w -> 0x0w || 9w -> 0xBw || 10w -> 0x5w || 11w -> 0x9w ||
    12w -> 0xEw || 13w -> 0xCw || 14w -> 0xAw || 15w -> 0x4w : word8`;

val t01_def = Define `
  t01 (x:word8) =
    case x of
    0w -> 0xEw || 1w -> 0xCw || 2w -> 0xBw || 3w -> 0x8w ||
    4w -> 0x1w || 5w -> 0x2w || 6w -> 0x3w || 7w -> 0x5w ||
    8w -> 0xFw || 9w -> 0x4w || 10w -> 0xAw || 11w -> 0x6w ||
    12w -> 0x7w || 13w -> 0x0w || 14w -> 0x9w || 15w -> 0xDw : word8`;

val t02_def = Define `
  t02 (x:word8) =
    case x of
    0w -> 0xBw || 1w -> 0xAw || 2w -> 0x5w || 3w -> 0xEw ||
    4w -> 0x6w || 5w -> 0xDw || 6w -> 0x9w || 7w -> 0x0w ||
    8w -> 0xCw || 9w -> 0x8w || 10w -> 0xFw || 11w -> 0x3w ||
    12w -> 0x2w || 13w -> 0x4w || 14w -> 0x7w || 15w -> 0x1w : word8`;

val t03_def = Define `
  t03 (x:word8) =
    case x of
    0w -> 0xDw || 1w -> 0x7w || 2w -> 0xFw || 3w -> 0x4w ||
    4w -> 0x1w || 5w -> 0x2w || 6w -> 0x6w || 7w -> 0xEw ||
    8w -> 0x9w || 9w -> 0xBw || 10w -> 0x3w || 11w -> 0x0w ||
    12w -> 0x8w || 13w -> 0x5w || 14w -> 0xCw || 15w -> 0xAw : word8`;


(* The 4-bit S-boxes For the permutation q1 *)
val t10_def = Define `
  t10 (x:word8) =
    case x of
    0w -> 0x2w || 1w -> 0x8w || 2w -> 0xBw || 3w -> 0xDw ||
    4w -> 0xFw || 5w -> 0x7w || 6w -> 0x6w || 7w -> 0xEw ||
    8w -> 0x3w || 9w -> 0x1w || 10w -> 0x9w || 11w -> 0x4w ||
    12w -> 0x0w || 13w -> 0xAw || 14w -> 0xCw || 15w -> 0x5w : word8`;

val t11_def = Define `
  t11 (x:word8) =
    case x of
    0w -> 0x1w || 1w -> 0xEw || 2w -> 0x2w || 3w -> 0xBw ||
    4w -> 0x4w || 5w -> 0xCw || 6w -> 0x3w || 7w -> 0x7w ||
    8w -> 0x6w || 9w -> 0xDw || 10w -> 0xAw || 11w -> 0x5w ||
    12w -> 0xFw || 13w -> 0x9w || 14w -> 0x0w || 15w -> 0x8w : word8`;

val t12_def = Define `
  t12 (x:word8) =
    case x of
    0w -> 0x4w || 1w -> 0xCw || 2w -> 0x7w || 3w -> 0x5w ||
    4w -> 0x1w || 5w -> 0x6w || 6w -> 0x9w || 7w -> 0xAw ||
    8w -> 0x0w || 9w -> 0xEw || 10w -> 0xDw || 11w -> 0x8w ||
    12w -> 0x2w || 13w -> 0xBw || 14w -> 0x3w || 15w -> 0xFw : word8`;

val t13_def = Define `
  t13 (x:word8) =
    case x of
    0w -> 0xBw || 1w -> 0x9w || 2w -> 0x5w || 3w -> 0x1w ||
    4w -> 0xCw || 5w -> 0x3w || 6w -> 0x3w || 7w -> 0x7w ||
    8w -> 0x6w || 9w -> 0x4w || 10w -> 0x7w || 11w -> 0xFw ||
    12w -> 0x2w || 13w -> 0x0w || 14w -> 0x8w || 15w -> 0xAw : word8`;


(*  First, the byte is split into two nibbles. These are combined in a bijective mixing   *)
(*  step. Each nibble is then passed through its own 4-bit fixed S-box. This is followed  *)
(*  by another mixing step and S-box lookup. Finally, the two nibbles are recombined into *)
(*  a byte. 										  *)
val qq_def = Define `
  qq t0 t1 t2 t3 (x:word8) =
    let (a0, b0) = ((x >> 4) & 0xfw, x & 0xfw) in
    let (a1, b1) = (a0 ## b0, a0 ## ROR4(b0,1) ## (8w*a0 & 0xfw)) in
    let (a2, b2) = (t0(a1), t1(b1)) in
    let (a3, b3) = (a2 ## a2, a0 ## ROR4(b2,1) ## (8w*a2 & 0xfw)) in
    let (a4, b4) = (t2(a3), t3(b3))
    in 16w * b4 + a4 : word8`;

val q0_def = Define `q0 = qq t00 t01 t02 t03`;
val q1_def = Define `q1 = qq t10 t11 t12 t13`;

(*----------------------------------------------------------------------------------------*)
(* Function h takes two inputs--a 32-bit word X and a list L = (L0,...,Lk ) (here k = 4)  *)
(* of 32-bit words of and produces one word of output. This function works in k stages.   *)
(* In each stage, the four bytes are each passed through a fixed S-box, and               *)
(* xored with a byte derived from the list. Finally, the bytes are once again passed      *)
(* through a fixed Sbox, and the four bytes are multiplied by the MDS matrix.             *)
(*----------------------------------------------------------------------------------------*)

val fun_h_def = Define `
  fun_h((x3,x2,x1,x0), ((l33,l32,l31,l30),(l23,l22,l21,l20),(l13,l12,l11,l10),(l03,l02,l01,l00)))
  = let (y0,y1,y2,y3) = (x0,x1,x2,x3) in
    let (y0,y1,y2,y3) = (q1(y0) ## l30, q0(y1) ## l31, q0(y2) ## l32, q1(y3) ## l33) in (* k=4 *)
    let (y0,y1,y2,y3) = (q1(y0) ## l20, q1(y1) ## l21, q0(y2) ## l22, q0(y3) ## l23) in (* k=3 *)
    let (y0,y1,y2,y3) = (q1(q0(q0(y0) ## l10) ## l00), q0(q0(q1(y1) ## l11) ## l01),
                         q1(q1(q0(y2) ## l12) ## l02), q0(q1(q1(y3) ## l13) ## l03)) in (* k=2 *)
    let (y0,y1,y2,y3) = (q1(q0(q0(y0) ## l10) ## l00), q0(q0(q1(y1) ## l11) ## l01),
                         q1(q1(q0(y2) ## l12) ## l02), q0(q1(q1(y3) ## l13) ## l03))    (* k=1 *)
    in InvW(MDSMul(y0,y1,y2,y3))`;

(*----------------------------------------------------------------------------------------*)
(* Take the key bytes in groups of 8, interpreting them as a vector over                  *)
(* GF(2^8), and multiplying them by a 4bytes 8 matrix derived from an RS code.            *)
(*----------------------------------------------------------------------------------------*)

val genM_def = Define `
  genM ((m31,m30,m29,m28,m27,m26,m25,m24,m23,m22,m21,m20,m19,m18,m17,m16,m15,
        m14,m13,m12,m11,m10,m9,m8,m7,m6,m5,m4,m3,m2,m1,m0):initkeys)
  =  let Me = ((m3,m2,m1,m0),(m11,m10,m9,m8),(m19,m18,m17,m16),(m27,m26,m25,m24)) in
     let Mo = ((m7,m6,m5,m4),(m15,m14,m13,m12),(m23,m22,m21,m20),(m31,m30,m29,m28))
     in (Me, Mo)`;

val genS_def = Define `
  genS ((m31,m30,m29,m28,m27,m26,m25,m24,m23,m22,m21,m20,m19,m18,m17,m16,m15,
        m14,m13,m12,m11,m10,m9,m8,m7,m6,m5,m4,m3,m2,m1,m0):initkeys)
  =
     (InvW(RSMul(m24,m25,m26,m27,m28,m29,m30,m31)), InvW(RSMul(m16,m17,m18,m19,m20,m21,m22,m23)),
      InvW(RSMul(m8,m9,m10,m11,m12,m13,m14,m15)), InvW(RSMul(m0,m1,m2,m3,m4,m5,m6,m7)))`;

(*----------------------------------------------------------------------------------------*)
(* The words of the expanded key are defined using the h function. For Ai the byte values *)
(* are 2i, and the second argument of h is Me. Bi is computed similarly using 2i + 1 as   *)
(* the byte value and Mo as the second argument, with an extra rotate over 8 bits.        *)
(* The values Ai and Bi are combined in a PHT. One of the results is further              *)
(* rotated by 9 bits.                                                                     *)
(*----------------------------------------------------------------------------------------*)

val e_rnd_def = Define `
  e_rnd(Me,Mo,i) =
    let i = word8$n2w i in
    let Ai = toLarge(fun_h((2w*i, 2w*i, 2w*i, 2w*i), Me)) in
    let Bi = toLarge(fun_h((2w*i+1w, 2w*i+1w, 2w*i+1w, 2w*i+1w), Mo)) <<<< 8 in
    let K2i = word32$bitwise_and (Ai + Bi) 0xffffffffw in
    let K2i_1 = (word32$bitwise_and (Ai + 2w * Bi) 0xffffffffw) <<<< 9
    in (K2i, K2i_1)`;

val expandKeys_def = Define `
  expandKeys(Me,Mo) = (
    FST(e_rnd(Me,Mo,0)), SND(e_rnd(Me,Mo,0)), FST(e_rnd(Me,Mo,1)), SND(e_rnd(Me,Mo,1)),
    FST(e_rnd(Me,Mo,2)), SND(e_rnd(Me,Mo,2)), FST(e_rnd(Me,Mo,3)), SND(e_rnd(Me,Mo,3)),
    FST(e_rnd(Me,Mo,4)), SND(e_rnd(Me,Mo,4)), FST(e_rnd(Me,Mo,5)), SND(e_rnd(Me,Mo,5)),
    FST(e_rnd(Me,Mo,6)), SND(e_rnd(Me,Mo,6)), FST(e_rnd(Me,Mo,7)), SND(e_rnd(Me,Mo,7)),
    FST(e_rnd(Me,Mo,8)), SND(e_rnd(Me,Mo,8)), FST(e_rnd(Me,Mo,9)), SND(e_rnd(Me,Mo,9)),
    FST(e_rnd(Me,Mo,10)), SND(e_rnd(Me,Mo,10)),FST(e_rnd(Me,Mo,11)), SND(e_rnd(Me,Mo,11)),
    FST(e_rnd(Me,Mo,12)), SND(e_rnd(Me,Mo,12)), FST(e_rnd(Me,Mo,13)), SND(e_rnd(Me,Mo,13)),
    FST(e_rnd(Me,Mo,14)), SND(e_rnd(Me,Mo,14)), FST(e_rnd(Me,Mo,15)), SND(e_rnd(Me,Mo,15)),
    FST(e_rnd(Me,Mo,16)), SND(e_rnd(Me,Mo,16)), FST(e_rnd(Me,Mo,17)), SND(e_rnd(Me,Mo,17)),
    FST(e_rnd(Me,Mo,18)), SND(e_rnd(Me,Mo,18)), FST(e_rnd(Me,Mo,19)), SND(e_rnd(Me,Mo,19)))`;

(*----------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------*)

val ROTKEYS_def = Define `
  ROTKEYS ((k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,
        k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39):keysched)
  =  (k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,
      k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39,k0,k1)`;

val ROTKEYS8_def = Define `
  ROTKEYS8 ((k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,
        k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39):keysched)
  =  (k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,k20,k21,k22,k23,k24,k25,k26,k27,k28,
        k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39,k0,k1,k2,k3,k4,k5,k6,k7)`;

val GETKEYS_def = Define `
  GETKEYS ((k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,
        k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39):keysched)
  =  (k0,k1)`;

val FORALL_INITKEYS = Q.prove
(`(!x:initkeys. P x) = !k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 
	k17 k18 k19 k20 k21 k22 k23 k24 k25 k26 k27 k28 k29 k30 k31.
        P(k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,k20,
          k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31)`,
  SIMP_TAC std_ss [FORALL_PROD]);

val FORALL_KEYSCHEDS = Q.prove
(`(!x:keysched. P x) = !k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20
             k21 k22 k23 k24 k25 k26 k27 k28 k29 k30 k31 k32 k33 k34 k35 k36 k37 k38 k39.
             P(k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,k20,
             k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39)`,
  SIMP_TAC std_ss [FORALL_PROD]);

(*---------------------------------------------------------------------------*)
(* Sanity check                                                              *)
(*---------------------------------------------------------------------------*)

val toList_def = Define `
  toList (k:keysched) = 
   let (k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,
        k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39) = k in
     [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14;k15;k16;k17;k18;k19;
      k20;k21;k22;k23;k24;k25;k26;k27;k28;k29;k30;k31;k32;k33;k34;k35;k36;k37;k38;k39]`;

val keysched_length = Count.apply Q.prove
(`!Me Mo. LENGTH (toList(expandKeys(Me,Mo))) = 40`,
 SIMP_TAC std_ss [expandKeys_def, toList_def]
  THEN REPEAT GEN_TAC
  THEN EVAL_TAC);


(*---------------------------------------------------------------------------*)
(* The Key-dependent S-boxes *)
(*---------------------------------------------------------------------------*)

val fun_g_def = Define `
  fun_g(x, SS) = toLarge(fun_h(x,SS))`;


(*---------------------------------------------------------------------------*)
(* The function FF is a key-dependent permutation on 64-bit values *)
(*---------------------------------------------------------------------------*)

val FF_def = Define `
  FF((R0,R1),(K0,K1),SS) =
  let T0 = fun_g(fromLarge(R0),SS) in
  let T1 = fun_g(fromLarge(R1 <<<< 8),SS) in
  let F0 = word32$bitwise_and (T0 + T1 + K0) 0xffffffffw in
  let F1 = word32$bitwise_and (T0 + 2w*T1+ K1) 0xffffffffw
  in (F0,F1)`;

(*----------------------------------------------------------------------------------*)
(*-------------Forward round used by the encrypting function------------------------*)
(*----------------------------------------------------------------------------------*)

(* The operation in each of the 16 rounds *)
val Round_Op_def = Define `
  Round_Op((R0,R1,R2,R3),k,ss) =
  let (F0, F1) = FF((R0,R1),GETKEYS(k), ss) in
  let R0' = (R2 ### F0) >>>> 1 in
  let R1' = (R3 <<<< 1) ### F1
  in (R0', R1', R0, R1)`;

val  (en_rnd_def, en_rnd_ind)  = Defn.tprove (
    Hol_defn "en_rnd"
    `en_rnd i (b:block) k ss =
     if i=0 then b
     else en_rnd (i-1) (Round_Op(b,k,ss)) (ROTKEYS(k)) ss`,
  WF_REL_TAC `measure FST`);

val _ = save_thm ("en_rnd_def", en_rnd_def);
val _ = save_thm ("en_rnd_ind", en_rnd_ind);

val  fwd_def = Define `
   fwd(b,k,s) = en_rnd 16 b k s`;

(*----------------------------------------------------------------------------------*)
(*-------------Backward round used by the decrypting function------------------------*)
(*----------------------------------------------------------------------------------*)

(* Decryption. Note that (R2,R3) at round r+1 = (R0,R1) at round r *)
val InvRound_Op_def = Define `
  InvRound_Op((R0,R1,R2,R3),k,ss) =
  let (F0, F1) = FF((R2,R3),GETKEYS(k),ss) in
  let R0' = (R0 <<<< 1) ### F0 in
  let R1' = (R1 ### F1) >>>> 1
  in (R2, R3, R0', R1')`;
                      
val  (de_rnd_def, de_rnd_ind)  = Defn.tprove (
    Hol_defn "de_rnd"
    `de_rnd i (b:block) k ss =
     if i=0 then b
     else InvRound_Op(de_rnd (i-1) b (ROTKEYS(k)) ss, k, ss)`,
  WF_REL_TAC `measure FST`);

val _ = save_thm ("en_rnd_def", en_rnd_def);
val _ = save_thm ("de_rnd__ind", de_rnd_ind);

val  bwd_def = Define `
   bwd(b,k,s) = de_rnd 16 b k s`;

(* ------------------------------------------------------------------------------*)
(*-------------Forward and backward round operation inversion lemmas-------------*)
(*-------------------------------------------------------------------------------*)

val Round_Inversion = Q.store_thm
  ("Round_Inversion",
  `!b k s. InvRound_Op(Round_Op(b,k,s),k,s) = b`,
  SIMP_TAC std_ss [FORALL_BLOCK, FORALL_KEY] THEN RW_TAC std_ss [Round_Op_def] THEN
  RW_TAC std_ss [InvRound_Op_def] THEN Q.UNABBREV_TAC `R0'` THEN Q.UNABBREV_TAC `R1'` 
  THEN `1 < WL` by ARW_TAC [WL_def, HB_def] THEN
  METIS_TAC [WORD_EOR_ASSOC, WORD_EOR_INV, WORD_EOR_ID, Word32_SHIFT_Inversion]
 );
 
val [Round_Op] = decls "Round_Op";
val [InvRound_Op] = decls "InvRound_Op";

val Round_Inversion_LEMMA = Q.store_thm
("Round_Inversion_LEMMA",
 `!b k s. bwd(fwd(b,k,s),k,s) = b`,
   SIMP_TAC std_ss [FORALL_BLOCK] THEN RESTR_EVAL_TAC [Round_Op, InvRound_Op] THEN
   RW_TAC std_ss [Round_Inversion]);
                                                                                                                                               
(*---------------------------------------------------------------------------*)
(* Input whitening and output whitening                                      *)
(*---------------------------------------------------------------------------*)

val In_Whiten_def = Define `
  In_Whiten(b:block, k) =
    let (R0,R1,R2,R3) = b in
    (R0 ### FST(GETKEYS(k)), R1 ### SND(GETKEYS(k)),
     R2 ### FST(GETKEYS(ROTKEYS(k))), R3 ### SND(GETKEYS(ROTKEYS(k))))`;

val Out_Whiten_def = Define `
  Out_Whiten(b:block, k) =
    let (R0,R1,R2,R3) = b in
    (R0 ### FST(GETKEYS(ROTKEYS(ROTKEYS(k)))), R1 ### SND(GETKEYS(ROTKEYS(ROTKEYS(k)))),
     R2 ### FST(GETKEYS(ROTKEYS(ROTKEYS(ROTKEYS(k))))), R3 ### SND(GETKEYS(ROTKEYS(ROTKEYS(ROTKEYS(k))))))`;

val WHITENING_LEMMA = Q.store_thm
("WHITENING_LEMMA",
 `!(b:block) (k:keysched).
  (Out_Whiten(Out_Whiten(b,k),k) = b) /\ (In_Whiten(In_Whiten(b,k),k) = b)`,
  RW_TAC std_ss [Out_Whiten_def, In_Whiten_def] THEN
  METIS_TAC [WORD_EOR_ASSOC, WORD_EOR_INV, WORD_EOR_ID]);

(*---------------------------------------------------------------------------*)
(* Encrypt and Decrypt                                                       *)
(*---------------------------------------------------------------------------*)
(*  In the input whitening step, these words are xored
    with 4 words of the expanded key. Then goes the 16 rounds.
    Finally the output whitening step undoes the `swap' of the
    last round, and xors the data words with 4 words of the expanded key.*)

val TwofishEncrypt_def = Define `
  TwofishEncrypt initM b =
  let (k, ss) = (expandKeys(genM(initM)), genS(initM))
  in  Out_Whiten(fwd(In_Whiten(b,k),ROTKEYS8(k),ss), k)`;

val TwofishDecrypt_def = Define `
  TwofishDecrypt initM b =
  let (k, ss) = (expandKeys(genM(initM)), genS(initM))
  in  In_Whiten(bwd(Out_Whiten(b,k),ROTKEYS8(k),ss), k)`;

(*---------------------------------------------------------------------------*)
(* Main Lemma				                                     *)
(*---------------------------------------------------------------------------*)

val TWOFISH_LEMMA = Q.store_thm
("TWOFISH_LEMMA",
 `!(plaintext:block) (keys:initkeys).
     TwofishDecrypt keys (TwofishEncrypt keys plaintext) = plaintext`,
   RW_TAC std_ss [TwofishEncrypt_def] THEN RW_TAC std_ss [TwofishDecrypt_def] THEN
   RW_TAC std_ss [WHITENING_LEMMA, Round_Inversion_LEMMA]);

(*---------------------------------------------------------------------------*)
(* Basic theorem about encryption/decryption                                 *)
(*---------------------------------------------------------------------------*)

val TWOFISH_def = Define
 `TWOFISH (keys) = 
  (TwofishEncrypt keys,  TwofishDecrypt keys)`;
                                                                                                
val TWOFISH_CORRECT = Q.store_thm
  ("TWOFISH_CORRECT",
   `!key plaintext.
       ((encrypt,decrypt) = TWOFISH key)
       ==>
       (decrypt (encrypt plaintext) = plaintext)`,
         RW_TAC std_ss [TWOFISH_def,LET_THM,TWOFISH_LEMMA]);
                                                                                                         
val _ = export_theory();
