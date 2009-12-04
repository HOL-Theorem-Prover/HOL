
open HolKernel boolLib bossLib Parse;
open wordsTheory stringTheory stringLib listTheory stringSimps listLib fcpTheory arithmeticTheory;
open rich_listTheory;

val _ = new_theory "bit_list";


(* conversions between ``:bool list`` and ``:num`` *)

val bits2num_def = Define `
  (bits2num [] = 0) /\
  (bits2num (T::bs) = 1 + 2 * bits2num bs) /\
  (bits2num (F::bs) = 0 + 2 * bits2num bs)` ;

val n2bits_def = Define `
  n2bits i n = if i = 0 then [] else (n MOD 2 = 1) :: n2bits (i-1) (n DIV 2)`;

val w2bits_def = Define `
  w2bits (w:'a word) = n2bits (dimindex(:'a)) (w2n w)`;

val b2w_def = Define `b2w v x = n2w (bits2num (v x))`;


(* parsing hex numbers represented by strings *)

val is_hex_def = Define `
  is_hex s = EVERY (\n. ORD #"0" <= n /\ n <= ORD #"9" \/ ORD #"A" <= n /\ n <= ORD #"F")
                   (MAP ORD (EXPLODE s))`;

val char2num_def = Define `
  char2num c = let n = ORD c in if n <= ORD #"9" then n - ORD #"0" else n - ORD #"A" + 10`;

val hex2num_aux_def = Define `
  (hex2num_aux [] = 0) /\
  (hex2num_aux (c::cs) = char2num c + 16 * hex2num_aux cs)`;

val hex2num_def = Define `
  hex2num s = hex2num_aux (REVERSE (EXPLODE s))`;

val hex2word_def = Define `
  hex2word s = n2w (hex2num s) :'a word`;

(* EVAL ``hex2num "F8"`` gives ``242`` *)


(* converting between bytes and words *)

val bytes2word_def = Define `
  (bytes2word [] = 0w:'a word) /\
  (bytes2word (x:word8 ::xs) = w2w x !! (bytes2word xs << 8))`;

val word2bytes_def = Define `
  word2bytes n (w:'a word) =
    if n = 0 then [] else (((7 >< 0) w):word8) :: word2bytes (n-1) (w >> 8)`;

val address_aligned_def = Define `
  address_aligned n a =
    if n = 2  then (a && 1w = 0w) else
    if n = 4  then (a && 3w = 0w) else
    if n = 8  then (a && 7w = 0w) else
    if n = 16 then (a && 15w = 0w) else
    if n = 32 then (a && 31w = 0w) else T`;

val bytes2word_lem = SIMP_RULE (std_ss++wordsLib.SIZES_ss) []
  (CONJ (INST_TYPE [``:'b``|->``:32``] (CONJ w2w FCP_BETA))
        (INST_TYPE [``:'b``|->``:8``] (CONJ w2w FCP_BETA)));

val bytes2word_lemma = prove(
  ``!w:word32. bytes2word [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] = w``,
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [bytes2word_def,word_extract_def]
  THEN SIMP_TAC (std_ss++wordsLib.SIZES_ss) [bytes2word_def,DECIDE ``n <= m = ~(m < n:num)``,
     word_lsl_def,FCP_ETA,word_or_def,w2w,FCP_BETA,word_extract_def,CART_EQ]
  THEN REPEAT STRIP_TAC
  THEN `i - 8 < 32 /\ i - 16 < 32 /\ i - 24 < 32 /\ i < 40 /\ i < 48 /\ i < 56` by DECIDE_TAC
  THEN Cases_on `i < 8`
  THEN1 ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_bits_def,bytes2word_lem,
    DECIDE ``i < 8 ==> i < 16 /\ i < 24 /\ (i <= 7) /\ (i <= 31)``]
  THEN Cases_on `i < 16` THEN1
   (`i - 8 < 8 /\ (i - 8 + 8 = i) /\ i < 24 /\ i < 40 /\ i <= 15 /\ i <= 31` by DECIDE_TAC
    THEN ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_bits_def,bytes2word_lem])
  THEN Cases_on `i < 24` THEN1
   (`i - 16 < 8 /\ (i - 16 + 16 = i) /\ i < 48 /\ i <= 23 /\ i <= 31` by DECIDE_TAC
    THEN ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_bits_def,bytes2word_lem])
  THEN `i - 24 < 8 /\ (i - 24 + 24 = i) /\ i < 56 /\ i <= 31` by DECIDE_TAC
  THEN ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_bits_def,bytes2word_lem]);

val _ = wordsLib.guess_lengths();
val bytes2word_INTRO = store_thm("bytes2word_INTRO", 
  ``!x1 x2 x3 x4.
      (($@@ :word8 -> word24 -> word32)
                  (x1 :word8)
                      (($@@ :word8 -> word16 -> word24)
                         (x2 :word8)
                         (($@@ :word8 -> word8 -> word16)
                            (x3 :word8) (x4 :word8) :
                            word16) :word24) :word32) =
      bytes2word [x4;x3;x2;x1]``,
 SRW_TAC [wordsLib.WORD_EXTRACT_ss] [bytes2word_def]);

val bytes2word_thm = store_thm("bytes2word_thm",
  ``!w:word32 x.
      (bytes2word [(7 >< 0) w; (7 >< 0) (w >> 8); (7 >< 0) (w >> 16); (7 >< 0) (w >> 24)] = w) /\
      (bytes2word [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] = w) /\
      (bytes2word [x] = (w2w x):'a word)``,
  REWRITE_TAC [bytes2word_def,wordsTheory.ZERO_SHIFT,wordsTheory.WORD_OR_CLAUSES]
  THEN REWRITE_TAC [bytes2word_lemma]
  THEN SIMP_TAC (std_ss++wordsLib.WORD_EXTRACT_ss++wordsLib.SIZES_ss)
         [WORD_OR_CLAUSES,bytes2word_lemma]);

val bits2num_n2bits = store_thm("bits2num_n2bits",
  ``!i n. bits2num (n2bits i n) = n MOD 2**i``,
  Induct THEN ONCE_REWRITE_TAC [n2bits_def] THEN REPEAT STRIP_TAC
  THEN SIMP_TAC std_ss [bits2num_def,DECIDE ``~(SUC i = 0)``]
  THEN `0<2` by DECIDE_TAC
  THEN `n MOD 2 < 2 /\ (n DIV 2 * 2 + n MOD 2 = n)` by METIS_TAC [DIVISION]
  THEN Cases_on `n MOD 2 = 0` THENL [
    ASM_SIMP_TAC std_ss [MOD_COMMON_FACTOR,ZERO_LT_EXP,bits2num_def]
    THEN FULL_SIMP_TAC std_ss [EXP,AC MULT_COMM MULT_ASSOC],
    `n MOD 2 = 1` by DECIDE_TAC
    THEN ASM_SIMP_TAC std_ss [bits2num_def]
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN SIMP_TAC std_ss [DIV_MOD_MOD_DIV,GSYM EXP]
    THEN `1 = n MOD 2 ** SUC i MOD 2` by ASM_SIMP_TAC std_ss [EXP,MOD_MULT_MOD]
    THEN ONCE_ASM_REWRITE_TAC []
    THEN ONCE_REWRITE_TAC [MULT_COMM]
    THEN SIMP_TAC std_ss [MATCH_MP (GSYM DIVISION) (DECIDE ``0<2``)]]);

val bits2num_w2bits = store_thm("bits2num_w2bits",
  ``!w:'a word. bits2num (w2bits w) = w2n w``,
  Cases THEN FULL_SIMP_TAC std_ss [w2bits_def,bits2num_n2bits,w2n_n2w,dimword_def]);

val w2bits_word32 = save_thm("w2bits_word32",
  SIMP_RULE std_ss [DIV_DIV_DIV_MULT] (EVAL ``w2bits (w:word32)``));

val w2bits_word8 = save_thm("w2bits_word8",
  SIMP_RULE std_ss [DIV_DIV_DIV_MULT] (EVAL ``w2bits (w:word8)``));

val bits2num_LESS = store_thm("bits2num_LESS",
  ``!xs. bits2num xs < 2 ** (LENGTH xs)``,
  Induct THEN SIMP_TAC std_ss [bits2num_def]
  THEN Cases THEN SIMP_TAC std_ss [bits2num_def,LENGTH,EXP] THEN DECIDE_TAC);

val n2bits_bits2num = store_thm("n2bits_bits2num",
  ``!xs. n2bits (LENGTH xs) (bits2num xs) = xs``,
  Induct THEN ONCE_REWRITE_TAC [n2bits_def]
  THEN SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  THEN Cases
  THEN ASM_SIMP_TAC std_ss [bits2num_def,
         ONCE_REWRITE_RULE [ADD_COMM] (ONCE_REWRITE_RULE [MULT_COMM]
           (CONJ DIV_MULT (CONJ MOD_EQ_0 (CONJ MULT_DIV MOD_MULT))))]);

val w2bits_b2w_word32 = store_thm("w2bits_b2w_word32",
  ``w2bits ((b2w I [x1;x2;x3;x4;x5;x6;x7;x8]):word8) = [x1;x2;x3;x4;x5;x6;x7;x8]``,
  SIMP_TAC std_ss [w2bits_def,b2w_def,w2n_n2w]
  THEN ASSUME_TAC (Q.SPEC `[x1;x2;x3;x4;x5;x6;x7;x8]` bits2num_LESS)
  THEN ASSUME_TAC (Q.SPEC `[x1;x2;x3;x4;x5;x6;x7;x8]` n2bits_bits2num)
  THEN FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [LENGTH]);

val bits2num_MOD = store_thm("bits2num_MOD",
  ``!i xs. bits2num xs MOD 2 ** i = bits2num (TAKE i xs)``,
  Induct THEN Cases THEN ONCE_REWRITE_TAC [TAKE_def]
  THEN SIMP_TAC std_ss [bits2num_def,DECIDE ``~(SUC n = 0)``]
  THEN Tactical.REVERSE (Cases_on `h`) THEN SIMP_TAC std_ss [bits2num_def]
  THEN ASM_SIMP_TAC std_ss [GSYM MOD_COMMON_FACTOR,EXP]
  THEN POP_ASSUM (fn th => SIMP_TAC std_ss [GSYM th])
  THEN ONCE_REWRITE_TAC [ADD_COMM]
  THEN ASM_SIMP_TAC std_ss [MOD_COMMON_FACTOR,GSYM EXP]
  THEN `0 < 2 ** SUC i` by SIMP_TAC std_ss [bitTheory.MOD_ADD_1,ZERO_LT_EXP]
  THEN IMP_RES_TAC bitTheory.MOD_ADD_1
  THEN POP_ASSUM MATCH_MP_TAC
  THEN IMP_RES_TAC bitTheory.MOD_PLUS_1
  THEN ASM_SIMP_TAC std_ss []
  THEN SIMP_TAC std_ss [EXP,GSYM MOD_COMMON_FACTOR]
  THEN `0 < 2 ** i` by SIMP_TAC std_ss [bitTheory.MOD_ADD_1,ZERO_LT_EXP]
  THEN IMP_RES_TAC DIVISION
  THEN `bits2num t MOD 2 ** i < 2 ** i` by METIS_TAC []
  THEN DECIDE_TAC);

val COLLECT_BYTES_n2w_bits2num = store_thm("COLLECT_BYTES_n2w_bits2num",
  ``!imm32:word32 imm8:word8. 
      ((b2w I
            [w2n imm32 MOD 2 = 1; (w2n imm32 DIV 2) MOD 2 = 1;
             (w2n imm32 DIV 4) MOD 2 = 1; (w2n imm32 DIV 8) MOD 2 = 1;
             (w2n imm32 DIV 16) MOD 2 = 1; (w2n imm32 DIV 32) MOD 2 = 1;
             (w2n imm32 DIV 64) MOD 2 = 1; (w2n imm32 DIV 128) MOD 2 = 1]) =
       (w2w imm32):word8) /\
      ((b2w I
            [(w2n imm32 DIV 256) MOD 2 = 1;
             (w2n imm32 DIV 512) MOD 2 = 1; (w2n imm32 DIV 1024) MOD 2 = 1;
             (w2n imm32 DIV 2048) MOD 2 = 1; (w2n imm32 DIV 4096) MOD 2 = 1;
             (w2n imm32 DIV 8192) MOD 2 = 1; (w2n imm32 DIV 16384) MOD 2 = 1;
             (w2n imm32 DIV 32768) MOD 2 = 1]) =
       (w2w (imm32 >>> 8)):word8) /\
      ((b2w I
            [(w2n imm32 DIV 65536) MOD 2 = 1;
             (w2n imm32 DIV 131072) MOD 2 = 1; (w2n imm32 DIV 262144) MOD 2 = 1;
             (w2n imm32 DIV 524288) MOD 2 = 1; (w2n imm32 DIV 1048576) MOD 2 = 1;
             (w2n imm32 DIV 2097152) MOD 2 = 1; (w2n imm32 DIV 4194304) MOD 2 = 1;
             (w2n imm32 DIV 8388608) MOD 2 = 1]) =
       (w2w (imm32 >>> 16)):word8) /\
      ((b2w I
            [(w2n imm32 DIV 16777216) MOD 2 = 1;
             (w2n imm32 DIV 33554432) MOD 2 = 1; (w2n imm32 DIV 67108864) MOD 2 = 1;
             (w2n imm32 DIV 134217728) MOD 2 = 1; (w2n imm32 DIV 268435456) MOD 2 = 1;
             (w2n imm32 DIV 536870912) MOD 2 = 1; (w2n imm32 DIV 1073741824) MOD 2 = 1;
             (w2n imm32 DIV 2147483648) MOD 2 = 1]) =
       (w2w (imm32 >>> 24)):word8) /\
      (b2w I (w2bits imm8) = imm8)``,
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [w2w_def,b2w_def]
  THEN CONV_TAC (RAND_CONV (REWRITE_CONV [GSYM bits2num_w2bits]))
  THEN SIMP_TAC std_ss [w2bits_word32,n2w_11,dimword_def]
  THEN SIMP_TAC (bool_ss++wordsLib.SIZES_ss) []
  THEN SIMP_TAC bool_ss [bits2num_MOD]
  THEN SIMP_TAC std_ss [TAKE_def,w2n_lsr,DIV_DIV_DIV_MULT]
  THEN Q.SPEC_TAC (`imm8`,`x`) THEN wordsLib.Cases_word
  THEN FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2bits_def,w2n_n2w,bits2num_n2bits]);


val _ = export_theory ();
