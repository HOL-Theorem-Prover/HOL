(* For interactive use
app load ["gcdTheory", "wordsLib", "intLib", "ExtendedEuclidTheory"];
quietdec := true;
open gcdTheory dividesTheory arithmeticTheory
     pairTheory intLib integerTheory
     wordsTheory wordsLib
     ExtendedEuclidTheory;
quietdec := false;
*)

open HolKernel Parse boolLib bossLib ExtendedEuclidTheory
   gcdTheory dividesTheory arithmeticTheory
   pairTheory wordsTheory wordsLib intLib integerTheory;

val _ = new_theory "ideaMult";

val ARW = RW_TAC arith_ss;
val ASP = FULL_SIMP_TAC arith_ss;

(*---------------------------------------------------------------------------*)
(* To be proved, or assumed, but will assert this well-known fact for now.   *)
(*---------------------------------------------------------------------------*)

val _ = intLib.prefer_int();

val prime_axiom = new_axiom("prime_axiom", ``prime 65537n``);

val minv_Lemma1 = Q.store_thm
("minv_Lemma1",
 ` !a b. b < a ==> ~(0 < b) \/ ~divides a b`,
 ARW [] THEN `!a b. ~(a <= b) ==> ~(0 < b /\ divides a b)`
   by METIS_TAC [MONO_NOT,DIVIDES_LE] THEN
 `~(0 < b /\ divides a b) = ~(0 < b) \/ ~(divides a b)`
   by METIS_TAC [DE_MORGAN_THM] THEN
 `(b < a) ==> (~(0 < b) \/ ~divides a b)`
   by METIS_TAC [NOT_LESS_EQUAL] THEN METIS_TAC []);

val minv_Lemma2 = Q.store_thm
("minv_Lemma2",
 `!x:num. ((0 < x) /\ (x < 65537)) ==> ~(divides 65537 x)`,
 ARW [] THEN IMP_RES_TAC minv_Lemma1);

val minv_Lemma3 = Q.store_thm
("minv_Lemma3",
 `!x:num. ((0 < x) /\ (x < 65537)) ==> ((gcd x 65537) = 1)`,
 ARW [] THEN ASSUME_TAC prime_axiom THEN IMP_RES_TAC PRIME_GCD THEN
 `divides 65537 x \/ (gcd 65537 x = 1)` by  METIS_TAC [] THENL
 [METIS_TAC [minv_Lemma2], METIS_TAC [GCD_SYM]]);

val gcd_Lemma1 = Q.store_thm
("gcd_Lemma1",
 `!a b. b <= a ==> (gcd (a-b) b = gcd a b)`,
 ARW [] THEN `is_gcd (a-b) b (gcd (a-b) b)` by ARW [GCD_IS_GCD] THEN
 IMP_RES_TAC IS_GCD_MINUS_L THEN
 `is_gcd a b (gcd a b)` by ARW [GCD_IS_GCD] THEN
 IMP_RES_TAC IS_GCD_UNIQUE);

val gcd_Lemma2 = Q.store_thm
("gcd_Lemma2",
 `!a b. a <= b ==> (gcd a (b-a) = gcd a b)`,
 ARW [] THEN `is_gcd a (b-a) (gcd a (b-a))` by ARW [GCD_IS_GCD] THEN
 IMP_RES_TAC IS_GCD_MINUS_R THEN
 `is_gcd a b (gcd a b)` by ARW [GCD_IS_GCD] THEN
 IMP_RES_TAC IS_GCD_UNIQUE);

val minv_Lemma4 = Q.store_thm
("minv_Lemma4",
 `!r1:num r2:num u1:int u2:int v1:int v2:int. gcd r1 r2 =
   gcd (FST(dec(r1, r2, u1, u2, v1, v2)))
       (FST(SND(dec(r1, r2, u1, u2,v1, v2))))`,
  ARW [dec_def] THENL [METIS_TAC [LESS_IMP_LESS_OR_EQ, gcd_Lemma2],
  METIS_TAC [NOT_LESS, gcd_Lemma1]]);

val minv_Lemma5 = Q.store_thm
("minv_Lemma5",
`!r1 r2 u1 u2 v1 v2.
   (~((FST (dec (r1,r2,u1,u2,v1,v2)) = 1) \/
      (FST (SND (dec (r1,r2,u1,u2,v1,v2))) = 1) \/
      (FST (dec (r1,r2,u1,u2,v1,v2)) = 0) \/
      (FST (SND (dec (r1,r2,u1,u2,v1,v2))) = 0)))
  ==> (inv (dec (r1,r2,u1,u2,v1,v2)) = inv (dec (dec (r1,r2,u1,u2,v1,v2))))`,
  REWRITE_TAC [dec_def] THEN RW_TAC arith_ss [inv_def]);

val minv_Lemma6 = Q.store_thm
("minv_Lemma6",
 `!r1:num r2:num u1:int u2:int v1:int v2:int. gcd r1 r2 =
  gcd (FST(inv(r1, r2, u1, u2, v1, v2)))
      (FST(SND(inv(r1, r2, u1, u2,v1, v2))))`,
  FULL_SIMP_TAC arith_ss [inv_def] THEN
  recInduct inv_ind THEN ARW [] THENL[
    UNDISCH_TAC ``FST (dec (r1,r2,u1,u2,v1,v2)) = 1`` THEN
    ARW [dec_def] THEN ARW [inv_def] THEN
    IMP_RES_TAC NOT_LESS THEN METIS_TAC [gcd_Lemma1],
    UNDISCH_TAC ``FST (SND (dec (r1,r2,u1,u2,v1,v2))) = 1`` THEN
    ARW [dec_def] THEN ARW [inv_def] THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    METIS_TAC [gcd_Lemma2],
    UNDISCH_TAC ``FST (dec (r1,r2,u1,u2,v1,v2)) = 0`` THEN
    ARW [dec_def] THEN IMP_RES_TAC NOT_LESS THEN
    IMP_RES_TAC LESS_EQUAL_ANTISYM THEN
    `r1-r2=0` by DECIDE_TAC THEN
    `inv (r1 - r2,r2,u1 - u2,u2,v1 - v2,v2) = inv (0,r2,u1 - u2,u2,v1 - v2,v2)`
     by METIS_TAC [] THEN
    ARW [inv_def] THEN METIS_TAC [gcd_Lemma1],
    UNDISCH_TAC ``FST (SND (dec (r1,r2,u1,u2,v1,v2))) = 0`` THEN ARW [dec_def],
    `inv (dec (r1,r2,u1,u2,v1,v2))=inv (dec (dec (r1,r2,u1,u2,v1,v2)))`
     by ARW [minv_Lemma5] THEN
    `gcd (FST (inv (dec (dec (r1,r2,u1,u2,v1,v2)))))
         (FST (SND (inv (dec (dec (r1,r2,u1,u2,v1,v2)))))) =
     gcd (FST (inv (dec (r1,r2,u1,u2,v1,v2))))
         (FST (SND (inv (dec (r1,r2,u1,u2,v1,v2)))))` by METIS_TAC [] THEN
    `gcd (FST (dec (r1,r2,u1,u2,v1,v2)))
         (FST (SND (dec (r1,r2,u1,u2,v1,v2)))) =
     gcd (FST (inv (dec (r1,r2,u1,u2,v1,v2))))
            (FST (SND (inv (dec (r1,r2,u1,u2,v1,v2)))))` by METIS_TAC [] THEN
    METIS_TAC [minv_Lemma4]]);

val minv_Lemma7 = Q.store_thm
("minv_Lemma7",
 `!x. gcd (ir1 x) (ir2 x) = gcd x 65537`,
  ARW [ir1_def, ir2_def] THEN ARW [minv_Lemma6]);

val minv_Lemma8 = Q.store_thm
("minv_Lemma8",
 `!x. ((0 < x) /\ (x < 65537)) ==> (((ir1 x) = 1) \/ ((ir2 x) = 1))`,
 ARW [] THEN `gcd (ir1 x) (ir2 x) = 1` by ARW [minv_Lemma7, minv_Lemma3] THEN
 `((ir1 x) = 1) \/ ((ir1 x) = 0) \/ ((ir2 x) = 1) \/ ((ir2 x) =0)`
    by ARW [i16_Lemma6] THENL[
   ARW [],
   `gcd 0 (ir2 x) = 1` by METIS_TAC [] THEN METIS_TAC [GCD_0L],
   ARW [],
   ` gcd (ir1 x) 0 = 1` by METIS_TAC [] THEN
   METIS_TAC [GCD_0R]]);

val minv_Lemma9 = Q.store_thm
("minv_Lemma9",
 `!x. ((0 < x) /\ (x < 65537)) ==>
   (((int_of_num x) * (iu1 x)) % 65537 = 1) \/
   (((int_of_num x) * (iu2 x)) % 65537 = 1)`,
 `~(65537i = 0)`
      by intLib.ARITH_TAC THEN ARW [] THEN
 `($& (ir1 x) % 65537 = (iu1 x * $& x) % 65537) /\
  ($& (ir2 x) % 65537 = (iu2 x * $& x) % 65537)`
      by RW_TAC arith_ss [i16_Lemma8] THEN
 `(((ir1 x) = 1) \/ ((ir2 x) = 1))`
      by ARW [minv_Lemma8] THENL
 [`$& 1 % 65537 = (iu1 x * $& x) % 65537`
      by METIS_TAC [] THEN
  `1 % 65537 = $& (1 MOD 65537)`
      by METIS_TAC [INT_MOD_CALCULATE] THEN
  `1n < 65537n`
      by ARW [] THEN
  `1 MOD 65537 = 1`
      by METIS_TAC [LESS_MOD] THEN
  `1 = (iu1 x * $& x) % 65537`
      by METIS_TAC [] THEN
  `$& x * iu1 x = iu1 x * $& x`
      by RW_TAC arith_ss [INT_MUL_COMM],
  `$&1 % 65537 = (iu2 x * $& x) % 65537`
      by METIS_TAC [] THEN
  `$&1 % 65537 = $& (1 MOD 65537)`
      by METIS_TAC [INT_MOD_CALCULATE] THEN
  `1n < 65537n`
      by ARW [] THEN
  `1 MOD 65537 = 1`
      by METIS_TAC [LESS_MOD] THEN
  `1 = (iu2 x * $& x) % 65537`
      by METIS_TAC [] THEN
  `$& x * iu2 x = iu2 x * $& x`
      by RW_TAC arith_ss [INT_MUL_COMM]] THEN
   ARW []);

val mode_Lemma1 = Q.store_thm
("mode_Lemma1",
 `!a c. (~(c=0) /\ (a % c = 0)) ==> (~a % c = 0)`,
 ARW [] THEN IMP_RES_TAC INT_MOD_EQ0 THEN
 `~a = ~(k *c)` by METIS_TAC [] THEN
 `~a = ~k * c` by METIS_TAC [INT_NEG_LMUL] THEN
 METIS_TAC [INT_MOD_COMMON_FACTOR]);

val mode_Lemma2 = Q.store_thm
("mode_Lemma2",
`!a b c. ~(c=0) ==> ((a * b % c) % c = (a * b) % c)`,
RW_TAC arith_ss [int_mod] THEN ARW [INT_SUB_LDISTRIB] THEN
`a * (b / c * c) = a * (b / c) * c` by METIS_TAC [INT_MUL_ASSOC] THEN
 ARW [] THEN
`(a * (b / c) * c) % c = 0` by METIS_TAC [INT_MOD_COMMON_FACTOR] THEN
`(a * b - a * (b / c) * c) / c = a * b / c - a * (b / c) * c / c`
 by ARW [INT_SUB_CALCULATE, INT_ADD_DIV]
THENL [`~(a * (b / c) * c) % c = 0` by METIS_TAC [mode_Lemma1] THEN
  ARW [INT_ADD_DIV] THEN ARW [INT_NEG_LMUL, INT_DIV_RMUL],
  ARW [INT_DIV_RMUL] THEN ARW [INT_SUB_RDISTRIB] THEN
  ARW [INT_SUB_CALCULATE] THEN
  `~(a * b / c * c + ~(a * (b / c) * c)) =
   ~(a * b / c * c) - ( ~(a * (b / c) * c))` by ARW [INT_SUB_LNEG] THEN
  ARW [] THEN ARW [INT_SUB_RNEG] THEN ARW [INT_ADD_ASSOC] THEN
  `a * b + ~(a * (b / c) * c) + ~(a * b / c * c) + a * (b / c) * c =
   a * b + (~(a * (b / c) * c) + ~(a * b / c * c) + a * (b / c) * c)`
  by METIS_TAC [INT_ADD_ASSOC] THEN ARW [] THEN
  `~(a * (b / c) * c) + ~(a * b / c * c) + a * (b / c) * c =
   ~(a * (b / c) * c) + (~(a * b / c * c) + a * (b / c) * c)`
  by METIS_TAC [INT_ADD_ASSOC] THEN ARW [] THEN
  `~(a * (b / c) * c) + (~(a * b / c * c) + a * (b / c) * c) =
  (~(a * b / c * c) + a * (b / c) * c) + ~(a * (b / c) * c)`
  by METIS_TAC [INT_ADD_COMM] THEN ARW [] THEN
  `~(a * b / c * c) + a * (b / c) * c + ~(a * (b / c) * c) =
   ~(a * b / c * c) + (a * (b / c) * c + ~(a * (b / c) * c))`
  by METIS_TAC [INT_ADD_ASSOC] THEN ARW [] THEN
  `a * (b / c) * c + ~(a * (b / c) * c) = 0` by METIS_TAC [INT_ADD_RINV] THEN
  ARW [] THEN
  METIS_TAC [INT_ADD_RID]]);

val piu1_def = Define `piu1 x = (iu1 x) % 65537`;
val piu2_def = Define `piu2 x = (iu2 x) % 65537`;

val minv_Lemma10 = Q.store_thm
("minv_Lemma10",
 `!x. ((0 < x) /\ (x < 65537)) ==>
  (((int_of_num x) * (piu1 x)) % 65537 = 1) \/
  (((int_of_num x) * (piu2 x)) % 65537 = 1)`,
 RW_TAC arith_ss [piu1_def, piu2_def] THEN
 `~(65537i = 0)` by intLib.ARITH_TAC THEN
 ASSUME_TAC minv_Lemma9 THEN
 METIS_TAC [mode_Lemma2]);

val minv_def =
  Define `minv x =
    if ((int_of_num x) * (piu1 x)) % 65537 = 1
        then piu1 x
        else if ((int_of_num x) * (piu2 x)) % 65537 = 1
          then piu2 x
          else 0`;

val minv_Theorem = Q.store_thm
("minv_Theorem",
 `!x. ((0 < x) /\ (x < 65537)) ==> (((int_of_num x) * (minv x)) % 65537 = 1)`,
 ARW [minv_def] THEN
 IMP_RES_TAC minv_Lemma10);

val piu_Lemma1 = Q.store_thm
("piu_Lemma1",
 `!x. (0 <= piu1 x) /\ (piu1 x < 65537)`,
 ASP [piu1_def] THEN
 `~(65537 < 0)` by intLib.ARITH_TAC THEN
 `~(65537i = 0)` by intLib.ARITH_TAC THEN
 STRIP_TAC THEN METIS_TAC [INT_MOD_BOUNDS]);

val piu_Lemma2 = Q.store_thm
("piu_Lemma2",
 `!x. (0 <= piu2 x) /\ (piu2 x < 65537)`,
 ASP [piu2_def] THEN
 `~(65537 < 0)` by intLib.ARITH_TAC THEN
 `~(65537i = 0)` by intLib.ARITH_TAC THEN
 STRIP_TAC THEN METIS_TAC [INT_MOD_BOUNDS]);

val minv_Corollary1 = Q.store_thm
("minv_Corollary1",
`!x. ((0 < x) /\ (x < 65537)) ==> ((0 <= (minv x)) /\ ((minv x) < 65537))`,
 STRIP_TAC THEN STRIP_TAC THEN
 `((minv x = piu1 x) \/ (minv x = piu2 x))`
   by METIS_TAC [minv_def, minv_Lemma10]
 THENL [ARW [piu_Lemma1], ARW [piu_Lemma2]]);

val minv_Corollary2 = Q.store_thm
("minv_Corollary2",
 `!x. ((0 < x) /\ (x < 65537)) ==> ~((minv x) = 0)`,
 `~(65537i = 0)` by intLib.ARITH_TAC THEN
 SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
 IMP_RES_TAC minv_Theorem THEN
 `($& x * 0) % 65537 = 1` by METIS_TAC [] THEN
 `$& x * 0 = 0` by METIS_TAC [INT_MUL_RZERO] THEN
 `0 % 65537 = 1` by METIS_TAC [] THEN
 `0 % 65537 = 0` by METIS_TAC [INT_MOD0] THEN
 `0 = 1` by METIS_TAC [] THEN
 `~(1n = 0n)` by ARW [] THEN
 METIS_TAC [INT_INJ]);

val minv_Corollary3 = Q.store_thm
("minv_Corollary3",
 `!x. ((0 < x) /\ (x < 65537)) ==> ((0 < (minv x)) /\ ((minv x) < 65537))`,
 STRIP_TAC THEN STRIP_TAC THEN
 IMP_RES_TAC minv_Corollary1 THEN
 IMP_RES_TAC minv_Corollary2 THEN ARW [] THEN
 `(0 < (minv x)) \/ (0 = (minv x))` by METIS_TAC [INT_LE_LT] THEN
 `minv x = 0` by METIS_TAC []);

val encode_def = Define `encode x:num = if x = 0n then 65536n else x`;
val decode_def = Define `decode x:num = if x = 65536n then 0n else x`;

val encode_Lemma1 = Q.store_thm
("encode_Lemma1",
 `!x. (x < 65536) ==> ((0 < (encode x)) /\ ((encode x) < 65537))`,
 ARW [encode_def]);

val encode_Lemma2 = Q.store_thm
("encode_Lemma2",
 `!x. (x < 65536) ==>
   (((int_of_num (encode x)) * (minv (encode x))) % 65537 = 1)`,
 ARW [encode_Lemma1, minv_Theorem]);

val decode_Lemma1 = Q.store_thm
("decode_Lemma1",
 `!x. ((0 < x) /\ (x < 65537)) ==> ((decode x) < 65536)`,
 ARW [decode_def]);

val decode_Lemma2 = Q.store_thm
("decode_Lemma2",
 `!x. ((0 < x) /\ (x < 65537)) ==> ((encode (decode x)) = x)`,
 ARW [encode_def, decode_def]);

val decode_Lemma3 = Q.store_thm
("decode_Lemma3",
 `!x. (x < 65536) ==> ((decode (encode x)) = x)`,
 ARW [encode_def, decode_def]);

(*---------------------------------------------------------------------------*)
(* Now phrase in terms of word16                                             *)
(*---------------------------------------------------------------------------*)

val encode_Lemma3 = Q.store_thm
("encode_Lemma3",
 `!w:word16. ((0 < (encode (w2n w))) /\ ((encode (w2n w)) < 65537))`,
 STRIP_TAC THEN
 `w2n w < 65536n` by WORD_DECIDE_TAC THEN
 ARW [encode_Lemma1]);

val wmul_Lemma1 = Q.store_thm
("wmul_Lemma1",
 `!w:word16.
   (int_of_num (encode (w2n w)) * minv (encode (w2n w))) % 65537 = 1`,
 ARW [] THEN
 `w2n w < 65536n` by WORD_DECIDE_TAC THEN
 METIS_TAC [encode_Lemma2]);

val winv_def =
 Define
   `winv (w:word16) = n2w (decode (Num (minv (encode (w2n w))))) : word16`;

val wmul_def =
 Define
   `wmul (x:word16) (y:word16) =
      n2w (decode (Num (((int_of_num (encode (w2n x))) *
                       (int_of_num (encode (w2n y)))) % 65537))) : word16`;

val _ = set_fixity "wmul"  (Infixr 350);

val Num_Lemma1 = Q.store_thm
("Num_Lemma1",
 `!x y. ((0 <= x) /\ (0 <= y) /\ (x < y)) ==> ((Num x) < (Num y))`,
 SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
 `Num y <= Num x` by METIS_TAC [NOT_LESS] THEN
 `(int_of_num (Num y)) <= (int_of_num (Num x))` by METIS_TAC [INT_LE] THEN
 IMP_RES_TAC INT_OF_NUM THEN
 `y <= x` by METIS_TAC [] THEN
 METIS_TAC [INT_NOT_LT]);

val wmul_Lemma2 = Q.store_thm
("wmul_Lemma2",
 `!x. ((0 < x) /\ (x < 65537)) ==>
      (int_of_num (encode (w2n (n2w (decode (Num x)) : word16))) = x)`,
 SRW_TAC [] [] THEN
 `0 <= x` by METIS_TAC [INT_LT_IMP_LE] THEN
 `0i <= 0i` by ARITH_TAC THEN
 `0i <= 65537i` by ARITH_TAC THEN
 `(Num 0) < (Num x)` by METIS_TAC [Num_Lemma1] THEN
 `(Num x) < (Num 65537)` by METIS_TAC [Num_Lemma1] THEN
 `Num ($& 0) = 0` by METIS_TAC [NUM_OF_INT] THEN
 `Num ($& 65537) = 65537` by METIS_TAC [NUM_OF_INT] THEN
 `0 < Num x` by METIS_TAC [] THEN
 `Num x < 65537` by METIS_TAC [] THEN
 `decode (Num x) MOD 65536 = decode (Num x)` by RES_TAC THENL [
   `decode (Num x) < 65536n` by METIS_TAC [decode_Lemma1] THEN
   METIS_TAC [LESS_MOD],
   ARW [decode_Lemma2, INT_OF_NUM]]);

val wmul_Theorem = Q.store_thm
("wmul_Theorem",
 `!w:word16. w wmul winv(w) = 1w`,
 ARW [wmul_def, winv_def] THEN
 `w2n w < 65536n` by WORD_DECIDE_TAC THEN
 `(0 < (encode (w2n w))) /\ ((encode (w2n w)) < 65537)`
    by METIS_TAC [encode_Lemma1] THEN
 `(0 < (minv (encode (w2n w)))) /\ ((minv (encode (w2n w))) < 65537)`
    by METIS_TAC [minv_Corollary3] THEN
 `($& (encode (w2n (n2w (decode (Num (minv (encode (w2n w))))):word16)))) =
  (minv (encode (w2n w)))`
    by METIS_TAC [wmul_Lemma2] THEN ARW [] THEN
 `(($& (encode (w2n w)) * minv (encode (w2n w))) % 65537) = 1`
    by METIS_TAC [wmul_Lemma1] THEN ARW [] THEN
 `Num ($& 1) = 1` by METIS_TAC [NUM_OF_INT] THEN ARW [] THEN ARW [decode_def]);

val wmul_Lemma3 = Q.store_thm
("wmul_Lemma3",
 `!x:word16. ~(($& (encode (w2n x))) = 0)`,
 SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
 `encode (w2n x) = 0n` by METIS_TAC [INT_INJ] THEN
 `w2n x < 65536n` by WORD_DECIDE_TAC THEN
 `0 < encode (w2n x)` by METIS_TAC [encode_Lemma1] THEN
 ARW []);

val MOD_EQ0 =
  SIMP_RULE arith_ss [] (BETA_RULE (Q.SPEC `\x. x=0` MOD_P));
(* !p q. 0 < q ==> ((p MOD q = 0) = ?k. p = k * q) *)

val wmul_Lemma4 = Q.store_thm
("wmul_Lemma4",
 `!x:word16 y:word16.
     ~((($& (encode (w2n x)) * $& (encode (w2n y))) % 65537) = 0)`,
 `~(65537i = 0)` by intLib.ARITH_TAC THEN
 SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
 `($& (encode (w2n x)) * $& (encode (w2n y))) =
   $&((encode (w2n x)) * (encode (w2n y)))` by METIS_TAC [INT_MUL] THEN
 `($& (encode (w2n x) * encode (w2n y))) % 65537 = 0` by METIS_TAC [] THEN
 `$& (encode (w2n x) * encode (w2n y)) % 65537 =
  $& ((encode (w2n x) * encode (w2n y)) MOD 65537)` by METIS_TAC [INT_MOD] THEN
 `$& ((encode (w2n x) * encode (w2n y)) MOD 65537) = 0` by METIS_TAC [] THEN
 `(encode (w2n x) * encode (w2n y)) MOD 65537 = 0` by METIS_TAC [INT_INJ] THEN
 `0n < 65537n`  by ARW [] THEN
 IMP_RES_TAC MOD_EQ0 THEN
 `divides 65537 (encode (w2n x) * encode (w2n y))`
    by METIS_TAC [divides_def] THEN
 `((0 < (encode (w2n x))) /\ ((encode (w2n x)) < 65537))`
    by METIS_TAC [encode_Lemma3] THEN
 `gcd (encode (w2n x)) 65537 = 1` by METIS_TAC [minv_Lemma3] THEN
 `divides 65537 (encode (w2n y))` by METIS_TAC [L_EUCLIDES] THEN
 `((0 < (encode (w2n y))) /\ ((encode (w2n y)) < 65537))`
    by METIS_TAC [encode_Lemma3] THEN
 `65537 <= (encode (w2n y))` by METIS_TAC [DIVIDES_LE] THEN
 ARW [NOT_LESS]);

val wmul_ASSOC = Q.store_thm
("wmul_ASSOC",
 `!x:word16 y:word16 z:word16. (x wmul y) wmul z = x wmul (y wmul z)`,
 ARW [wmul_def] THEN
 `~(65537 < 0)` by intLib.ARITH_TAC THEN
 `~(65537i = 0)` by intLib.ARITH_TAC THEN
 `(0 <= (($& (encode (w2n x)) * $& (encode (w2n y))) % 65537)) /\
  ((($& (encode (w2n x)) * $& (encode (w2n y))) % 65537) < 65537)`
    by METIS_TAC [INT_MOD_BOUNDS] THEN
 `(0 <= (($& (encode (w2n y)) * $& (encode (w2n z))) % 65537)) /\
  ((($& (encode (w2n y)) * $& (encode (w2n z))) % 65537) < 65537)`
    by METIS_TAC [INT_MOD_BOUNDS] THEN
 `~((($& (encode (w2n x)) * $& (encode (w2n y))) % 65537) = 0)`
    by METIS_TAC [wmul_Lemma4] THEN
 `~((($& (encode (w2n y)) * $& (encode (w2n z))) % 65537) = 0)`
    by METIS_TAC [wmul_Lemma4] THEN
 `0 < (($& (encode (w2n x)) * $& (encode (w2n y))) % 65537)`
    by METIS_TAC [INT_LE_LT] THEN
 `0 < (($& (encode (w2n y)) * $& (encode (w2n z))) % 65537)`
    by METIS_TAC [INT_LE_LT] THEN
 `($& (encode (w2n (n2w (decode
    (Num (($& (encode (w2n x)) * $& (encode (w2n y))) % 65537))):word16)))) =
  (($& (encode (w2n x)) * $& (encode (w2n y))) % 65537)`
    by METIS_TAC [wmul_Lemma2] THEN
 ARW [] THEN
 `($& (encode (w2n (n2w (decode
    (Num (($& (encode (w2n y)) * $& (encode (w2n z))) % 65537))):word16)))) =
  (($& (encode (w2n y)) * $& (encode (w2n z))) % 65537)`
    by METIS_TAC [wmul_Lemma2] THEN
 ARW [] THEN
 `(($& (encode (w2n x)) * ($& (encode (w2n y)) *
    $& (encode (w2n z))) % 65537) % 65537) =
 (($& (encode (w2n x)) * ($& (encode (w2n y)) * $& (encode (w2n z)))) % 65537)`
    by METIS_TAC [mode_Lemma2] THEN
 ARW [] THEN
 `($& (encode (w2n x)) * $& (encode (w2n y))) % 65537 * $& (encode (w2n z)) =
   $& (encode (w2n z)) * ($& (encode (w2n x)) * $& (encode (w2n y))) % 65537`
    by METIS_TAC [INT_MUL_COMM] THEN
 ARW [] THEN
 `(($& (encode (w2n z)) * ($& (encode (w2n x)) *
    $& (encode (w2n y))) % 65537) % 65537) =
  (($& (encode (w2n z)) * ($& (encode (w2n x)) * $& (encode (w2n y)))) % 65537)`
    by METIS_TAC [mode_Lemma2] THEN
 ARW [] THEN
 METIS_TAC [INT_MUL_COMM, INT_MUL_ASSOC]);

val wmul_Mul1 = Q.store_thm
("wmul_Mul1",
 `!w:word16. w wmul 1w = w`,
 `~(65537i = 0)` by intLib.ARITH_TAC THEN ARW [wmul_def] THEN
 `($& (encode (w2n w)) * $& (encode (w2n (1w:word16)))) =
   $&((encode (w2n w)) * (encode (w2n (1w:word16))))`
 by METIS_TAC [INT_MUL] THEN ARW [] THEN
 `$& (encode (w2n w) * encode (w2n (1w:word16))) % 65537 =
  $& ((encode (w2n w) * encode (w2n (1w:word16))) MOD 65537)`
    by METIS_TAC [INT_MOD] THEN ARW [] THEN
 ARW [word_1_n2w] THEN
 `encode 1 = 1` by ARW [encode_def] THEN ARW [] THEN
 `(encode (w2n w)) < 65537` by METIS_TAC [encode_Lemma3] THEN
 `(encode (w2n w) MOD 65537) = (encode (w2n w))`
    by METIS_TAC [LESS_MOD] THEN ARW [NUM_OF_INT] THEN
 `w2n w < 65536n` by WORD_DECIDE_TAC THEN
 SRW_TAC [] [decode_Lemma3]);

val () = export_theory();
