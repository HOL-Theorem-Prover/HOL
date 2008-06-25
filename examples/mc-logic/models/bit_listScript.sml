open HolKernel boolLib bossLib Parse;
open wordsTheory stringTheory stringLib listTheory stringSimps listLib fcpTheory;

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

val bytes2word_thm = store_thm("bytes2word_thm",
  ``!w:word32. 
      (bytes2word [(7 >< 0) w; (7 >< 0) (w >> 8); (7 >< 0) (w >> 16); (7 >< 0) (w >> 24)] = w) /\ 
      (bytes2word [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] = w)``,
  REWRITE_TAC [bytes2word_lemma]
  THEN SIMP_TAC (std_ss++wordsLib.WORD_EXTRACT_ss++wordsLib.SIZES_ss) 
         [WORD_OR_CLAUSES,bytes2word_lemma]);

val _ = export_theory ();
