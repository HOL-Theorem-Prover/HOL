(* ==================================================================
   TITLE: Developing the theory of complex number

   DESCRIPTION : Definitions and properties of the complex data type
      and arithmetic operations of complex numbers, and many
      properties organized in terms of group, field and R-module.
      Moreover, definitions and properties of complex conjugate,
      modulus and argument principal value of complex, the operation
      of nature numbers power of complex numbers, the polar form and
      exponential form of complex numbers.

   AUTHORS  : (Copyright) Yong Guan, Liming Li, Minhua Wu  and
              Zhiping Shi
              Beijing Engineering Research Center of High Reliable
              Emmbedded System, Capital Normal University, China
   DATE  : 2011.04.23
   REFERENCES  : John Harrison, realScript.sml and complex.ml
   ================================================================== *)

open HolKernel boolLib Parse bossLib
open arithmeticTheory numLib pairTheory realTheory realLib transcTheory
open tautLib AC
open boolSimps

val _ = new_theory "complex";

(* ------------------------------------------------------------------ *)
(* Definition of complex number type.                                 *)
(* ------------------------------------------------------------------ *)

val _ = type_abbrev ("complex", ``: real # real``);

(*--------------------------------------------------------------------*)
(* Now prove 2 lemmas.                                                *)
(*--------------------------------------------------------------------*)

val COMPLEX_LEMMA1= store_thm("COMPLEX_LEMMA1",
  ``!a:real b:real c:real d:real.
     (a * c- b * d) pow 2 + (a * d + b * c) pow 2 =
              (a pow 2 + b pow 2) * (c pow 2 + d pow 2)``,
  REWRITE_TAC[POW_2] THEN REAL_ARITH_TAC);

val COMPLEX_LEMMA2 = store_thm("COMPLEX_LEMMA2",
  ``!x y : real. abs x <= sqrt (x pow 2 + y pow 2)``,
  REPEAT GEN_TAC THEN `0 <= abs x` by PROVE_TAC[ABS_POS] THEN
  `abs x = sqrt (abs x pow 2)` by PROVE_TAC[POW_2_SQRT] THEN
  ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW2_ABS] THEN
  `0 <= x pow 2 /\ 0 <= y pow 2` by PROVE_TAC[REAL_LE_POW2] THEN
  ` x pow 2 <= x pow 2 + y pow 2` by PROVE_TAC[REAL_LE_ADDR] THEN
  PROVE_TAC[SQRT_MONO_LE]);

(*--------------------------------------------------------------------*)
(* Now define real part and imaginary part of complex number.         *)
(*--------------------------------------------------------------------*)

val RE = new_definition("RE",``RE (z:complex) = FST z``);

val IM = new_definition("IM",``IM (z:complex) = SND z``);

val COMPLEX = store_thm("COMPLEX",
  ``!z:complex. (RE z,IM z) = z``,
  REWRITE_TAC[RE,IM]);

val COMPLEX_RE_IM_EQ = store_thm("COMPLEX_RE_IM_EQ",
  ``!z:complex w:complex. (z = w) = (RE z = RE w) /\ (IM z = IM w)``,
  REWRITE_TAC[RE,IM, PAIR_FST_SND_EQ]);



(*--------------------------------------------------------------------*)
(* Now define the inclusion homomorphism: real->complex               *)
(*                                      : num->complex                *)
(*--------------------------------------------------------------------*)

val complex_of_real = new_definition("complex_of_real",
  ``complex_of_real (x:real) = (x,&0)``);

val RE_COMPLEX_OF_REAL = store_thm("RE_COMPLEX_OF_REAL",
  ``!x:real. RE (complex_of_real x) = x``,
  REWRITE_TAC [complex_of_real,RE]);

val IM_COMPLEX_OF_REAL = store_thm("IM_COMPLEX_OF_REAL",
  ``!x:real. IM (complex_of_real x) = &0``,
  REWRITE_TAC [complex_of_real, IM]);

val complex_of_num = new_definition
             ( "complex_of_num",
 ``complex_of_num (n:num) = complex_of_real (real_of_num n)``);

val _ = add_numeral_form(#"c", SOME "complex_of_num");

val COMPLEX_0 = store_thm("COMPLEX_0",
  ``0 = complex_of_real &0``,
  REWRITE_TAC[complex_of_num]);

val COMPLEX_1 = store_thm("COMPLEX_1",
  ``1 = complex_of_real 1``,
  REWRITE_TAC[complex_of_num]);

val COMPLEX_10 = store_thm("COMPLEX_10",
  ``~(1 = 0)``,
  REWRITE_TAC[complex_of_num, complex_of_real, COMPLEX_RE_IM_EQ, RE, IM,
              REAL_10]);

val COMPLEX_0_THM = store_thm("COMPLEX_0_THM",
  ``!z:complex. (z = 0) = (RE z pow 2 + IM z pow 2 = &0)``,
  REWRITE_TAC [complex_of_num, complex_of_real,RE, IM, PAIR_FST_SND_EQ, POW_2,
               REAL_SUMSQ]);

(* ------------------------------------------------------------------ *)
(* Imaginary unit                                                     *)
(* ------------------------------------------------------------------ *)

val i = new_definition ("i", ``i = (0r,1r)``);

(* ------------------------------------------------------------------ *)
(* Arithmetic operations.                                             *)
(* ------------------------------------------------------------------ *)

val complex_add = new_definition
("complex_add",
``complex_add (z:complex) (w:complex) = (RE z + RE w,IM z + IM w)``);

val complex_neg = new_definition
("complex_neg",
    ``complex_neg (z:complex) = (-RE z, -IM z)``);

val complex_mul = new_definition
("complex_mul",
    ``complex_mul (z:complex) (w:complex) =
              (RE z * RE w - IM z * IM w, RE z * IM w + IM z * RE w)``);

val complex_inv = new_definition
 ("complex_inv",
   ``complex_inv (z:complex) =
         (RE z / ((RE z) pow 2 + (IM z) pow 2),
                              -IM z / ((RE z) pow 2 + (IM z) pow 2))``);

val _ = overload_on ("+",  Term`$complex_add`);
val _ = overload_on ("~",  Term`$complex_neg`);
val _ = overload_on ("*",  Term`$complex_mul`);
val _ = overload_on ("inv",  Term`$complex_inv`);
val _ = overload_on ("numeric_negate", ``$~ : complex->complex``);

val complex_sub = new_definition
("complex_sub",
 ``complex_sub (z:complex) (w:complex) = z + ~w``);

val complex_div = new_definition
("complex_div",
 ``complex_div (z:complex) (w:complex) = z * inv w``);

val _ = overload_on ("-",  Term`$complex_sub`);
val _ = overload_on (GrammarSpecials.decimal_fraction_special, ``complex_div``)
val _ = overload_on ("/",  Term`complex_div`);

val _ =
    add_user_printer
       ("(DecimalFractionPP.fraction{Thy=\"complex\",Division=\"complex_div\",\
        \fromNum=\"complex_of_num\"})",
        ``&(NUMERAL x) / &(NUMERAL y)``,
        DecimalFractionPP.fraction{Thy="complex",Division="complex_div",
                                   fromNum="complex_of_num"})


(*--------------------------------------------------------------------*)
(* Prove lots of field theorems                                       *)
(*--------------------------------------------------------------------*)

val COMPLEX_ADD_COMM = store_thm("COMPLEX_ADD_COMM",
  ``!z:complex w:complex. z + w = w + z``,
  REWRITE_TAC [complex_add, RE, IM] THEN PROVE_TAC [REAL_ADD_COMM]);

val COMPLEX_ADD_ASSOC = store_thm("COMPLEX_ADD_ASSOC",
  ``!z:complex w:complex v:complex. z + (w + v) = z + w + v``,
  REWRITE_TAC [complex_add, RE, IM] THEN PROVE_TAC [REAL_ADD_ASSOC]);

val COMPLEX_ADD_RID = store_thm("COMPLEX_ADD_RID",
  ``!z:complex. z + 0 = z``,
  REWRITE_TAC [complex_of_num,complex_of_real, complex_add, REAL_ADD_RID,
               RE, IM]);

val COMPLEX_ADD_LID = store_thm("COMPLEX_ADD_LID",
  ``!z:complex. 0 + z = z``,
  PROVE_TAC [COMPLEX_ADD_COMM, COMPLEX_ADD_RID]);

val COMPLEX_ADD_RINV = store_thm("COMPLEX_ADD_RINV",
  ``!z:complex. z + -z = 0``,
  REWRITE_TAC [complex_of_num, complex_of_real, complex_add, complex_neg,
               REAL_ADD_RINV, RE, IM]);

val COMPLEX_ADD_LINV = store_thm("COMPLEX_ADD_LINV",
  ``!z:complex. -z + z = 0``,
  PROVE_TAC [COMPLEX_ADD_COMM, COMPLEX_ADD_RINV]);

val COMPLEX_MUL_COMM = store_thm("COMPLEX_MUL_COMM",
  ``!z:complex w:complex. z * w = w * z ``,
  REPEAT GEN_TAC THEN REWRITE_TAC [complex_mul,RE,IM] THEN
  PROVE_TAC[REAL_MUL_COMM,REAL_ADD_COMM]);

val COMPLEX_MUL_ASSOC = store_thm("COMPLEX_MUL_ASSOC",
  ``!z:complex w:complex v:complex. z * (w * v) = z * w * v``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [complex_mul, RE, IM, REAL_SUB_LDISTRIB, REAL_ADD_LDISTRIB,
               REAL_SUB_RDISTRIB, REAL_ADD_RDISTRIB, REAL_MUL_ASSOC] THEN
  REWRITE_TAC [real_sub, REAL_NEG_ADD] THEN RW_TAC std_ss[] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val COMPLEX_MUL_RID = store_thm("COMPLEX_MUL_RID",
  ``!z:complex. z * 1 = z``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [complex_of_num, complex_of_real, complex_mul, REAL_MUL_RZERO,
               REAL_MUL_RID, REAL_SUB_RZERO, REAL_ADD_LID,RE,IM]);

val COMPLEX_MUL_LID = store_thm("COMPLEX_MUL_LID",
  ``!z:complex. 1 * z = z``,
  PROVE_TAC[COMPLEX_MUL_COMM, COMPLEX_MUL_RID]);

val COMPLEX_MUL_RINV = store_thm("COMPLEX_MUL_RINV",
  ``!z:complex. ~(z = 0) ==> (z * inv z = 1)``,
  REWRITE_TAC [complex_of_num, complex_of_real, COMPLEX_0_THM, complex_inv,
               complex_mul, RE, IM, POW_2] THEN
  RW_TAC std_ss[] THEN
  `1 = (FST z * FST z + SND z * SND z) / (FST z * FST z + SND z * SND z)`
     by RW_TAC real_ss[REAL_DIV_REFL] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC [real_div] THEN REAL_ARITH_TAC);

val COMPLEX_MUL_LINV = store_thm("COMPLEX_MUL_LINV",
  ``!z:complex. ~(z = 0) ==> (inv z * z = 1)``,
  PROVE_TAC[COMPLEX_MUL_COMM,COMPLEX_MUL_RINV]);

val COMPLEX_ADD_LDISTRIB = store_thm("COMPLEX_ADD_LDISTRIB",
  ``!z:complex w:complex v:complex. z * (w + v) = z * w + z * v``,
  REWRITE_TAC [complex_mul,complex_add,RE,IM,REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC [real_sub, REAL_NEG_ADD] THEN RW_TAC std_ss[] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val COMPLEX_ADD_RDISTRIB = store_thm("COMPLEX_ADD_RDISTRIB",
  ``!z:complex w:complex v:complex. (z + w) * v = z * v + w * v``,
  PROVE_TAC [COMPLEX_MUL_COMM,COMPLEX_ADD_LDISTRIB]);

val COMPLEX_EQ_LADD = store_thm("COMPLEX_EQ_LADD",
  ``!z:complex w:complex v:complex. (z + w = z + v) = (w = v)``,
  REWRITE_TAC[complex_add, PAIR_EQ, REAL_EQ_LADD, GSYM COMPLEX_RE_IM_EQ]);

val COMPLEX_EQ_RADD = store_thm("COMPLEX_EQ_RADD",
  ``!z:complex w:complex v:complex. (z + v = w + v) = (z = w)``,
  ONCE_REWRITE_TAC [COMPLEX_ADD_COMM] THEN REWRITE_TAC [COMPLEX_EQ_LADD]);

val COMPLEX_ADD_RID_UNIQ = store_thm("COMPLEX_ADD_RID_UNIQ",
  ``!z:complex w:complex. (z + w = z) = (w = 0)``,
  REWRITE_TAC [complex_of_num, complex_of_real, complex_add, COMPLEX_RE_IM_EQ,
               RE, IM, REAL_ADD_RID_UNIQ]);

val COMPLEX_ADD_LID_UNIQ = store_thm("COMPLEX_ADD_LID_UNIQ",
  ``!z:complex w:complex. (z + w = w) = (z = 0)``,
  ONCE_REWRITE_TAC [COMPLEX_ADD_COMM] THEN
  REWRITE_TAC [COMPLEX_ADD_RID_UNIQ]);

val COMPLEX_NEGNEG = store_thm("COMPLEX_NEGNEG",
  ``!z:complex. --z = z``,
  REWRITE_TAC [complex_neg, RE, IM, REAL_NEGNEG]);

val COMPLEX_NEG_EQ = store_thm("COMPLEX_NEG_EQ",
  ``!z:complex w:complex. (-z = w) = (z = -w)``,
  REWRITE_TAC [complex_neg, COMPLEX_RE_IM_EQ, RE, IM, REAL_NEG_EQ]);

val COMPLEX_EQ_NEG = store_thm("COMPLEX_EQ_NEG",
  ``!z:complex w:complex. (-z = -w) = (z = w)``,
 REWRITE_TAC [COMPLEX_NEG_EQ, COMPLEX_NEGNEG]);

val COMPLEX_RNEG_UNIQ = store_thm("COMPLEX_RNEG_UNIQ",
  ``!z:complex w:complex. (z + w = 0) = (w = -z) ``,
  REWRITE_TAC [complex_of_num, complex_of_real, GSYM COMPLEX_ADD_RINV] THEN
  PROVE_TAC [COMPLEX_ADD_COMM, COMPLEX_EQ_LADD]);

val COMPLEX_LNEG_UNIQ = store_thm("COMPLEX_LNEG_UNIQ",
  ``!z:complex w:complex. (z + w = 0) = (z = -w) ``,
  PROVE_TAC[COMPLEX_RNEG_UNIQ,COMPLEX_NEG_EQ]);

val COMPLEX_NEG_ADD = store_thm("COMPLEX_NEG_ADD",
  ``!z:complex w:complex. -(z + w) = -z + -w ``,
  REWRITE_TAC[complex_neg,complex_add ,RE,IM, REAL_NEG_ADD]);

val COMPLEX_MUL_RZERO = store_thm("COMPLEX_MUL_RZERO",
  ``!z:complex. z * 0 = 0``,
  REWRITE_TAC [complex_of_num, complex_of_real, complex_mul, REAL_MUL_RZERO,
               REAL_ADD_RID, REAL_SUB_RZERO, RE,IM]);

val COMPLEX_MUL_LZERO = store_thm("COMPLEX_MUL_LZERO",
  ``!z:complex. 0 * z = 0``,
  PROVE_TAC[COMPLEX_MUL_COMM, COMPLEX_MUL_RZERO]);

val COMPLEX_NEG_LMUL = store_thm("COMPLEX_NEG_LMUL",
  ``!z:complex w:complex. -(z * w) = -z * w ``,
  REWRITE_TAC [complex_neg, complex_mul, RE,IM, real_sub, REAL_NEG_ADD,
               REAL_NEG_LMUL]);

val COMPLEX_NEG_RMUL = store_thm("COMPLEX_NEG_RMUL",
  ``!z:complex w:complex. -(z * w) = z * -w ``,
  PROVE_TAC [COMPLEX_NEG_LMUL, COMPLEX_MUL_COMM]);

val COMPLEX_NEG_MUL2 = store_thm("COMPLEX_NEG_MUL2",
  ``!z:complex w:complex. -z * -w = z * w ``,
  REWRITE_TAC [GSYM COMPLEX_NEG_LMUL, GSYM COMPLEX_NEG_RMUL, COMPLEX_NEGNEG]);

val COMPLEX_ENTIRE = store_thm("COMPLEX_ENTIRE",
  ``!z:complex w:complex.
            (z * w = 0) = (z = 0) \/ (w = 0)``,
  REWRITE_TAC[complex_of_num, complex_of_real, COMPLEX_0_THM, complex_mul,
              RE,IM,COMPLEX_LEMMA1,REAL_ENTIRE]);

val COMPLEX_NEG_0 = store_thm("COMPLEX_NEG_0",
  ``-0 = 0``,
  REWRITE_TAC [complex_of_num, complex_of_real, complex_neg, RE, IM,
               REAL_NEG_0]);

val COMPLEX_NEG_EQ0 = store_thm("COMPLEX_NEG_EQ0",
  ``!z:complex. (-z = 0) = (z = 0)``,
  REWRITE_TAC[COMPLEX_NEG_EQ,COMPLEX_NEG_0]);

val COMPLEX_SUB_REFL = store_thm("COMPLEX_SUB_REFL",
  ``!z:complex. z - z = 0``,
  REPEAT GEN_TAC THEN REWRITE_TAC [complex_sub, COMPLEX_ADD_RINV]);

val COMPLEX_SUB_RZERO = store_thm("COMPLEX_SUB_RZERO",
  ``!z:complex. z - 0 = z``,
  REWRITE_TAC [complex_sub, COMPLEX_NEG_0, COMPLEX_ADD_RID]);

val COMPLEX_SUB_LZERO = store_thm("COMPLEX_SUB_LZERO",
  ``!z:complex. 0 - z = -z``,
  REWRITE_TAC [complex_sub, COMPLEX_ADD_LID]);

val COMPLEX_SUB_LNEG = store_thm("COMPLEX_SUB_LNEG",
  ``!z:complex w:complex. -z - w = -(z + w)``,
  REPEAT GEN_TAC THEN REWRITE_TAC [complex_sub, COMPLEX_NEG_ADD]);

val COMPLEX_SUB_NEG2 = store_thm("COMPLEX_SUB_NEG2",
  ``!z:complex w:complex. -z - -w = w - z``,
  REWRITE_TAC[complex_sub, COMPLEX_NEGNEG] THEN PROVE_TAC [COMPLEX_ADD_COMM]);

val COMPLEX_NEG_SUB = store_thm("COMPLEX_NEG_SUB",
  ``!z:complex w:complex. -(z - w) = w - z ``,
  REWRITE_TAC[complex_sub, COMPLEX_NEG_ADD, COMPLEX_NEGNEG] THEN
  PROVE_TAC [COMPLEX_ADD_COMM]);

val COMPLEX_SUB_RNEG = store_thm("COMPLEX_SUB_RNEG",
  ``!z:complex w:complex. z - -w = z + w``,
  REPEAT GEN_TAC THEN REWRITE_TAC [complex_sub, COMPLEX_NEGNEG]);

val COMPLEX_SUB_ADD = store_thm ("COMPLEX_SUB_ADD",
  (``!z:complex w:complex. (z - w) + w = z``),
  REWRITE_TAC [complex_sub, GSYM COMPLEX_ADD_ASSOC, COMPLEX_ADD_LINV,
               COMPLEX_ADD_RID]);

val COMPLEX_SUB_ADD2 = store_thm("COMPLEX_SUB_ADD2",
  (``!z:complex w:complex. w + (z - w) = z``),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COMPLEX_ADD_COMM] THEN
  MATCH_ACCEPT_TAC COMPLEX_SUB_ADD);

val COMPLEX_ADD_SUB = store_thm ("COMPLEX_ADD_SUB",
  (``!z:complex w:complex. (z + w) - z = w``),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COMPLEX_ADD_COMM] THEN
  REWRITE_TAC[complex_sub, GSYM COMPLEX_ADD_ASSOC, COMPLEX_ADD_RINV,
              COMPLEX_ADD_RID]);

val COMPLEX_SUB_SUB = store_thm ("COMPLEX_SUB_SUB",
  ``!z:complex w:complex. (z - w) - z = -w ``,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_sub] THEN
  REWRITE_TAC[GSYM COMPLEX_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[COMPLEX_ADD_COMM] THEN
  REWRITE_TAC[GSYM COMPLEX_ADD_ASSOC] THEN
  REWRITE_TAC[COMPLEX_ADD_LINV, COMPLEX_ADD_RID]);

val COMPLEX_SUB_SUB2 = store_thm("COMPLEX_SUB_SUB2",
  ``!z:complex w:complex. z - (z - w) = w``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM COMPLEX_NEGNEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[COMPLEX_NEG_SUB, COMPLEX_SUB_SUB]);

val COMPLEX_ADD_SUB2 = store_thm("COMPLEX_ADD_SUB2",
   ``!z:complex w:complex. z - (z + w) = -w``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM COMPLEX_NEG_SUB] THEN
  AP_TERM_TAC THEN REWRITE_TAC[COMPLEX_ADD_SUB]);

val COMPLEX_ADD2_SUB2 = store_thm("COMPLEX_ADD2_SUB2",
  ``!z:complex w:complex u:complex v:complex.
(z + w) - (u + v) = (z - u) + (w - v)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_sub, COMPLEX_NEG_ADD] THEN
  CONV_TAC(AC_CONV(COMPLEX_ADD_ASSOC,COMPLEX_ADD_COMM)));

val COMPLEX_SUB_TRIANGLE = store_thm("COMPLEX_SUB_TRIANGLE",
  ``!z:complex w:complex v:complex. (z - w) + (w - v) = z - v``,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_sub] THEN
  ONCE_REWRITE_TAC[AC(COMPLEX_ADD_ASSOC,COMPLEX_ADD_COMM)
    ``(a + b) + (c + d) = (b + c) + (a + d)``] THEN
  REWRITE_TAC[COMPLEX_ADD_LINV, COMPLEX_ADD_LID]);

val COMPLEX_SUB_0 = store_thm("COMPLEX_SUB_0",
  ``!z:complex w:complex. (z - w = 0) = (z = w)``,
  REWRITE_TAC [complex_sub, COMPLEX_LNEG_UNIQ , COMPLEX_NEGNEG]);

val COMPLEX_EQ_SUB_LADD = store_thm("COMPLEX_EQ_SUB_LADD",
  ``!z:complex w:complex v:complex. (z = w - v) = (z + v = w)``,
  REPEAT GEN_TAC THEN
  Q.SPECL_THEN [`z`, `w-v`, `v`] (SUBST1_TAC o SYM) COMPLEX_EQ_RADD THEN
  REWRITE_TAC[COMPLEX_SUB_ADD]);

val COMPLEX_EQ_SUB_RADD = store_thm("COMPLEX_EQ_SUB_RADD",
  ``!z:complex w:complex v:complex. (z - w = v) = (z = v + w)``,
  REPEAT GEN_TAC THEN
  CONV_TAC(SUB_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC COMPLEX_EQ_SUB_LADD);

val COMPLEX_MUL_RNEG = store_thm("COMPLEX_MUL_RNEG",
  ``! z:complex w:complex. z * -w = -(z * w)``,
  REWRITE_TAC[COMPLEX_NEG_RMUL]);

val COMPLEX_MUL_LNEG = store_thm("COMPLEX_MUL_LNEG",
  ``! z:complex w:complex. -z * w = -(z * w)``,
  REWRITE_TAC[COMPLEX_NEG_LMUL]);

val COMPLEX_SUB_LDISTRIB = store_thm("COMPLEX_SUB_LDISTRIB",
  ``!z:complex w:complex v:complex. z * (w - v) = z * w - z * v``,
  REWRITE_TAC [complex_sub, COMPLEX_ADD_LDISTRIB, GSYM COMPLEX_NEG_RMUL]);

val COMPLEX_SUB_RDISTRIB = store_thm("COMPLEX_SUB_RDISTRIB",
  ``!z:complex w:complex v:complex. (z - w) * v = z * v - w * v``,
  PROVE_TAC [COMPLEX_MUL_COMM,COMPLEX_SUB_LDISTRIB]);

val COMPLEX_DIFFSQ = store_thm("COMPLEX_DIFFSQ",
  ``!z:complex w:complex. (z + w) * (z - w) = z * z - w * w ``,
  REWRITE_TAC[COMPLEX_ADD_RDISTRIB, COMPLEX_SUB_LDISTRIB, complex_sub,
              GSYM COMPLEX_ADD_ASSOC, COMPLEX_EQ_LADD] THEN
  REWRITE_TAC [COMPLEX_ADD_ASSOC, COMPLEX_ADD_LID_UNIQ]  THEN
  PROVE_TAC [COMPLEX_ADD_COMM, COMPLEX_MUL_COMM, COMPLEX_ADD_RINV]);

val COMPLEX_EQ_LMUL = store_thm("COMPLEX_EQ_LMUL",
  ``!z:complex w:complex v:complex.
           (z * w = z * v) = (z = 0) \/ (w = v)``,
  ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_0] THEN
  REWRITE_TAC [GSYM COMPLEX_SUB_LDISTRIB, COMPLEX_ENTIRE, COMPLEX_SUB_RZERO]);

val COMPLEX_EQ_RMUL = store_thm("COMPLEX_EQ_RMUL",
  ``!z:complex w:complex v:complex.
               (z * v = w * v) = (v = 0) \/ (z = w)``,
  PROVE_TAC[COMPLEX_MUL_COMM, COMPLEX_EQ_LMUL]);

val COMPLEX_EQ_LMUL2 = store_thm("COMPLEX_EQ_LMUL2",
  ``!z:complex w:complex v:complex.
          ~(z = 0) ==> ((w = v) = (z * w = z * v))``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  Q.SPECL_THEN [`z`, `w`, `v`] MP_TAC COMPLEX_EQ_LMUL THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC);

val COMPLEX_EQ_RMUL_IMP = store_thm("COMPLEX_EQ_RMUL_IMP",
  ``!z:complex w:complex v:complex.
              ~(z = 0) /\ (w * z = v * z)==> (w = v)``,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[COMPLEX_EQ_RMUL]);

val COMPLEX_EQ_LMUL_IMP = store_thm("COMPLEX_EQ_LMUL_IMP",
   ``!z:complex w:complex v:complex.
           ~(z = 0) /\ (z * w = z * v)==> (w = v)``,
  ONCE_REWRITE_TAC[COMPLEX_MUL_COMM] THEN
  MATCH_ACCEPT_TAC COMPLEX_EQ_RMUL_IMP);

val COMPLEX_NEG_INV = store_thm("COMPLEX_NEG_INV",
  ``!z: complex. ~(z = 0) ==> (inv (-z) = -(inv z))``,
  REWRITE_TAC [COMPLEX_0_THM,complex_inv,complex_neg,RE,IM,POW_2] THEN
  RW_TAC real_ss[real_div]);

val COMPLEX_INV_MUL = store_thm("COMPLEX_INV_MUL",
  ``!z:complex w:complex.
        (z <> 0 /\ w <> 0) ==> (inv (z * w) = inv z * inv w)``,
  REWRITE_TAC [complex_inv,COMPLEX_0_THM, complex_mul, RE,IM] THEN
  RW_TAC real_ss[real_div,COMPLEX_LEMMA1,REAL_INV_MUL] THEN REAL_ARITH_TAC);

val COMPLEX_INVINV = store_thm("COMPLEX_INVINV",
  ``!z: complex. (z <> 0) ==> (inv (inv z) = z)``,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_MUL_RINV) THEN
  Q.ASM_CASES_TAC `inv z = 0` THENL[
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO, GSYM COMPLEX_10],
    Q.SPECL_THEN [`inv(inv z)`, `z`, `inv z`] MP_TAC COMPLEX_EQ_RMUL THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC COMPLEX_MUL_LINV THEN
    FIRST_ASSUM ACCEPT_TAC
  ]);

val COMPLEX_LINV_UNIQ = store_thm("COMPLEX_LINV_UNIQ",
  ``!z:complex w:complex. (z * w = 1) ==> (z = inv w)``,
  REPEAT GEN_TAC THEN ASM_CASES_TAC (``z = 0``) THENL [
    ASM_REWRITE_TAC [COMPLEX_MUL_LZERO, GSYM COMPLEX_10],
    DISCH_THEN(MP_TAC o AP_TERM (``$* (inv z:complex) ``)) THEN
    REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
    FIRST_ASSUM (fn th=> REWRITE_TAC [MATCH_MP COMPLEX_MUL_LINV th]) THEN
    REWRITE_TAC [COMPLEX_MUL_LID, COMPLEX_MUL_RID] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
    POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC COMPLEX_INVINV
  ]);

val COMPLEX_RINV_UNIQ = store_thm("COMPLEX_RINV_UNIQ",
  ``!z:complex w:complex. (z * w = 1) ==> (w = inv z)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COMPLEX_MUL_COMM] THEN
  MATCH_ACCEPT_TAC COMPLEX_LINV_UNIQ);

val COMPLEX_INV_0 = store_thm("COMPLEX_INV_0",
  ``inv 0 = 0c``,
   RW_TAC real_ss [complex_of_num, complex_of_real, complex_inv, RE, IM,
                   POW_2, real_div, REAL_INV_0]);

val COMPLEX_INV1 = store_thm("COMPLEX_INV1",
  ``inv 1c = 1``,
  RW_TAC real_ss [complex_of_num, complex_of_real, complex_inv, RE, IM,
                  POW_2, real_div, REAL_INV1]);

val COMPLEX_INV_INV = store_thm("COMPLEX_INV_INV",
  ``!z: complex. inv (inv z) = z ``,
  GEN_TAC THEN Q.ASM_CASES_TAC `z = 0` THENL [
    ASM_REWRITE_TAC [COMPLEX_INV_0],
    MATCH_MP_TAC COMPLEX_INVINV THEN ASM_REWRITE_TAC[]
  ]);

val COMPLEX_INV_NEG = store_thm("COMPLEX_INV_NEG",
  ``!z: complex. inv (-z) = -inv z``,
  GEN_TAC THEN Q.ASM_CASES_TAC `z = 0` THEN
  ASM_REWRITE_TAC [COMPLEX_INV_0, COMPLEX_NEG_0] THEN
  MATCH_MP_TAC COMPLEX_NEG_INV THEN ASM_REWRITE_TAC[]);

val COMPLEX_INV_EQ_0 = store_thm ("COMPLEX_INV_EQ_0",
 ``!z: complex. (inv z = 0) = (z = 0)``,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_INV_0] THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_INV_INV] THEN
  ASM_REWRITE_TAC[COMPLEX_INV_0]);

val COMPLEX_INV_NZ = store_thm ("COMPLEX_INV_NZ",
  ``!z:complex. z <> 0 ==> inv z <> 0``,
  REWRITE_TAC[COMPLEX_INV_EQ_0]);

val COMPLEX_INV_INJ = store_thm("COMPLEX_INV_INJ",
  ``!z: complex w: complex. (inv z = inv w) = (z = w)``,
  PROVE_TAC[COMPLEX_INV_INV] );

val COMPLEX_NEG_LDIV= store_thm("COMPLEX_NEG_LDIV",
  ``!z w : complex. -(z / w) = -z / w``,
  REWRITE_TAC[complex_div, COMPLEX_NEG_LMUL]);

val COMPLEX_NEG_RDIV= store_thm("COMPLEX_NEG_RDIV",
  ``!z w : complex. -(z / w) = z / -w``,
  REWRITE_TAC[complex_div, COMPLEX_INV_NEG, COMPLEX_NEG_RMUL]);

val COMPLEX_NEG_DIV2= store_thm("COMPLEX_NEG_DIV2",
  ``!z w : complex. -z / -w = z / w ``,
  REWRITE_TAC[complex_div, COMPLEX_INV_NEG, COMPLEX_NEG_MUL2]);

val COMPLEX_INV_1OVER= store_thm("COMPLEX_INV_1OVER",
  ``!z: complex. inv z = 1 / z ``,
  REWRITE_TAC[complex_div, COMPLEX_MUL_LID]);

val COMPLEX_DIV1= store_thm("COMPLEX_DIV1",
  ``!z: complex. z / 1 = z ``,
  REWRITE_TAC[complex_div, COMPLEX_INV1,COMPLEX_MUL_RID]);

val COMPLEX_DIV_ADD = store_thm("COMPLEX_DIV_ADD",
  ``!z w v :complex. z / v + w / v = (z + w) / v``,
  REWRITE_TAC[complex_div, GSYM COMPLEX_ADD_RDISTRIB]);

val COMPLEX_DIV_SUB = store_thm("COMPLEX_DIV_SUB",
  ``!z w v :complex. z / v - w / v = (z - w) / v ``,
  REWRITE_TAC[complex_div, GSYM COMPLEX_SUB_RDISTRIB]);

val COMPLEX_DIV_RMUL_CANCEL = store_thm ("COMPLEX_DIV_RMUL_CANCEL",
  ``!v:complex z w. ~(v = 0) ==> ((z * v) / (w * v) = z / w)``,
  RW_TAC bool_ss [complex_div] THEN
  Cases_on `w = 0` THEN
  RW_TAC bool_ss [COMPLEX_MUL_LZERO, COMPLEX_INV_0, COMPLEX_INV_MUL,
                            COMPLEX_MUL_RZERO, COMPLEX_EQ_LMUL,
                            GSYM COMPLEX_MUL_ASSOC] THEN
  DISJ2_TAC THEN ONCE_REWRITE_TAC [COMPLEX_MUL_COMM] THEN
  ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
  RW_TAC bool_ss [COMPLEX_MUL_LINV, COMPLEX_MUL_RID]);

val COMPLEX_DIV_LMUL_CANCEL = store_thm("COMPLEX_DIV_LMUL_CANCEL",
   ``!v:complex z w. ~(v = 0) ==> ((v * z) / (v * w) = z / w)``,
   METIS_TAC [COMPLEX_DIV_RMUL_CANCEL, COMPLEX_MUL_COMM]);

val COMPLEX_DIV_DENOM_CANCEL = store_thm("COMPLEX_DIV_DENOM_CANCEL",
  ``!z:complex w v. ~(z = 0) ==> ((w / z) / (v / z) = w / v)``,
  RW_TAC bool_ss [complex_div] THEN
  Cases_on `w = 0` THEN1 RW_TAC bool_ss [COMPLEX_MUL_LZERO] THEN
  Cases_on `v = 0`
    THEN1 RW_TAC bool_ss [COMPLEX_INV_0, COMPLEX_MUL_RZERO,
                                    COMPLEX_MUL_LZERO] THEN
  RW_TAC bool_ss [COMPLEX_INV_MUL, COMPLEX_INV_EQ_0,
                            COMPLEX_INVINV] THEN
  REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
  RW_TAC bool_ss [COMPLEX_EQ_LMUL] THEN
  ONCE_REWRITE_TAC [COMPLEX_MUL_COMM] THEN
  REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
  RW_TAC bool_ss [COMPLEX_MUL_RINV, COMPLEX_MUL_RID]);

val COMPLEX_DIV_INNER_CANCEL = store_thm("COMPLEX_DIV_INNER_CANCEL",
   ``!z:complex w v. ~(z = 0) ==> ((w / z) * (z / v) = w / v)``,
  RW_TAC bool_ss [complex_div] THEN
  Cases_on `w = 0` THEN1 RW_TAC bool_ss [COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  RW_TAC bool_ss [COMPLEX_EQ_LMUL] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  RW_TAC bool_ss [COMPLEX_MUL_LINV, COMPLEX_MUL_LID]);

val COMPLEX_DIV_OUTER_CANCEL = store_thm("COMPLEX_DIV_OUTER_CANCEL",
   ``!z:complex w v. ~(z = 0) ==> ((z /w) * (v / z) = v / w)``,
  ONCE_REWRITE_TAC[COMPLEX_MUL_COMM] THEN
  REWRITE_TAC[COMPLEX_DIV_INNER_CANCEL]);

val COMPLEX_DIV_MUL2 = store_thm("COMPLEX_DIV_MUL2",
  ``!z:complex w.
      ~(z = 0) /\ ~(w = 0) ==> !v. v / w = (z * v) / (z * w)``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  RW_TAC bool_ss [COMPLEX_DIV_LMUL_CANCEL]);

val COMPLEX_ADD_RAT = store_thm ("COMPLEX_ADD_RAT",
   ``!z:complex w u v.
       ~(w = 0) /\ ~(v = 0) ==>
         (z / w + u / v = (z * v + w * u) / (w * v))``,
   RW_TAC bool_ss [GSYM COMPLEX_DIV_ADD, COMPLEX_DIV_RMUL_CANCEL,
                   COMPLEX_DIV_LMUL_CANCEL]);

val COMPLEX_SUB_RAT = store_thm ("COMPLEX_SUB_RAT",
  ``!z:complex w u v.
       ~(w = 0) /\ ~(v = 0) ==>
       (z / w - u / v = (z * v - w * u) / (w * v))``,
   RW_TAC bool_ss [complex_sub, COMPLEX_NEG_LDIV]
   THEN METIS_TAC [COMPLEX_ADD_RAT, COMPLEX_NEG_LMUL, COMPLEX_NEG_RMUL]);

val COMPLEX_DIV_LZERO = store_thm("COMPLEX_DIV_LZERO",
  ``!z:complex. 0 / z = 0``,
  REWRITE_TAC[complex_div, COMPLEX_MUL_LZERO]);

val COMPLEX_DIV_REFL = store_thm("COMPLEX_DIV_REFL",
  ``!z:complex. ~(z = 0) ==> (z / z = 1)``,
  REWRITE_TAC[complex_div, COMPLEX_MUL_RINV] );

val COMPLEX_SUB_INV2 = store_thm("COMPLEX_SUB_INV2",
  ``!z:complex w.
        (z <> 0 /\ w <> 0) ==>
              (inv z - inv w = (w - z) / (z * w))``,
  REWRITE_TAC[complex_div] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC COMPLEX_INV_MUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC [COMPLEX_SUB_RDISTRIB, COMPLEX_MUL_ASSOC] THEN
  IMP_RES_TAC COMPLEX_MUL_RINV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC [COMPLEX_MUL_LID, GSYM COMPLEX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC [COMPLEX_MUL_COMM] THEN
  REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
  FIRST_ASSUM (fn th=> REWRITE_TAC [MATCH_MP COMPLEX_MUL_LINV th]) THEN
  REWRITE_TAC[COMPLEX_MUL_RID]);

val COMPLEX_EQ_RDIV_EQ = store_thm("COMPLEX_EQ_RDIV_EQ",
  ``!z:complex w:complex v:complex.
                   ~(v = 0) ==> ((z = w / v) = (z * v= w))``,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_div] THEN
  DISCH_TAC THEN EQ_TAC THENL [
    DISCH_THEN(MP_TAC o AP_TERM ``$* (v:complex)``) THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_COMM] THEN
    RW_TAC bool_ss [COMPLEX_MUL_COMM, GSYM COMPLEX_MUL_ASSOC,
                    COMPLEX_MUL_LINV, COMPLEX_MUL_RID],
    DISCH_THEN(MP_TAC o AP_TERM ``$* (inv v:complex)``) THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_COMM] THEN
    RW_TAC bool_ss [COMPLEX_MUL_COMM, GSYM COMPLEX_MUL_ASSOC,
                    COMPLEX_MUL_RINV, COMPLEX_MUL_RID]
  ]);

val COMPLEX_EQ_LDIV_EQ = store_thm("COMPLEX_EQ_LDIV_EQ",
  ``!z:complex w:complex v:complex.
                ~(v = 0) ==> ((z / v = w) = (z = w * v))``,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_div] THEN
  DISCH_TAC THEN EQ_TAC THENL [
    DISCH_THEN(MP_TAC o AP_TERM (``$* (v:complex)``)) THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_COMM] THEN
    RW_TAC bool_ss [COMPLEX_MUL_COMM, GSYM COMPLEX_MUL_ASSOC,
                    COMPLEX_MUL_LINV, COMPLEX_MUL_RID],
    DISCH_THEN(MP_TAC o AP_TERM (``$* (inv v:complex)``)) THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_COMM] THEN
    RW_TAC bool_ss [COMPLEX_MUL_COMM, GSYM COMPLEX_MUL_ASSOC, COMPLEX_MUL_RINV,
                    COMPLEX_MUL_RID]
  ]);

(* ------------------------------------------------------------------ *)
(* Homomorphic embedding properties for complex_of_real mapping.      *)
(* ------------------------------------------------------------------ *)

val COMPLEX_OF_REAL_EQ = store_thm("COMPLEX_OF_REAL_EQ",
  ``!x:real y:real.
         (complex_of_real x = complex_of_real y) = (x = y)``,
  REWRITE_TAC[complex_of_real, COMPLEX_RE_IM_EQ, RE, IM]);

val COMPLEX_OF_REAL_ADD = store_thm("COMPLEX_OF_REAL_ADD",
  ``!x:real y:real.
     complex_of_real x + complex_of_real y = complex_of_real (x + y)``,
  REWRITE_TAC [complex_of_real,complex_add,RE,IM,REAL_ADD_RID]);

val COMPLEX_OF_REAL_NEG = store_thm("COMPLEX_OF_REAL_NEG",
  ``!x:real. -complex_of_real x = complex_of_real (-x)``,
  REWRITE_TAC [complex_of_real,complex_neg,RE,IM,REAL_NEG_0]);

val COMPLEX_OF_REAL_MUL = store_thm("COMPLEX_OF_REAL_MUL",
  ``!x:real y:real.
 complex_of_real x * complex_of_real y = complex_of_real (x * y)``,
  REWRITE_TAC [complex_of_real, complex_mul, RE, IM, REAL_MUL_RZERO,
               REAL_MUL_LZERO, REAL_SUB_RZERO, REAL_ADD_RID]);

val COMPLEX_OF_REAL_INV = store_thm("COMPLEX_OF_REAL_INV",
  ``!x:real. inv (complex_of_real x) = complex_of_real (inv x)``,
  GEN_TAC THEN ASM_CASES_TAC (``x = 0r``) THEN
  RW_TAC real_ss [complex_inv, complex_of_real, REAL_INV_0, RE, IM, POW_2,
                  REAL_MUL_RZERO, REAL_ADD_RID, real_div, REAL_MUL_LZERO,
                  REAL_NEG_0, REAL_INV_MUL, REAL_MUL_ASSOC, REAL_MUL_RINV,
                  REAL_MUL_LID]);

val COMPLEX_OF_REAL_SUB = store_thm("COMPLEX_OF_REAL_SUB",
  ``!x:real y:real.
      complex_of_real x - complex_of_real y = complex_of_real (x - y)``,
  REWRITE_TAC [real_sub, COMPLEX_OF_REAL_ADD, COMPLEX_OF_REAL_NEG,
               complex_sub]);

val COMPLEX_OF_REAL_DIV = store_thm("COMPLEX_OF_REAL_DIV",
  ``!x:real y:real.
      complex_of_real x / complex_of_real y =  complex_of_real (x / y)``,
  REWRITE_TAC [real_div, COMPLEX_OF_REAL_MUL, COMPLEX_OF_REAL_INV,
               complex_div]);

(* ------------------------------------------------------------------ *)
(* Homomorphic embedding properties for complex_of_num mapping.       *)
(* ------------------------------------------------------------------ *)

val COMPLEX_OF_NUM_EQ = store_thm("COMPLEX_OF_NUM_EQ",
``!m:num n:num. (complex_of_num m = complex_of_num n) = (m = n)``,
  REWRITE_TAC[complex_of_num, COMPLEX_OF_REAL_EQ,REAL_OF_NUM_EQ]);

val COMPLEX_OF_NUM_ADD = store_thm("COMPLEX_OF_NUM_ADD",
  ``!m:num n:num.
     complex_of_num m + complex_of_num n = complex_of_num (m + n)``,
  REWRITE_TAC [complex_of_num, REAL_OF_NUM_ADD, COMPLEX_OF_REAL_ADD]);

val COMPLEX_OF_NUM_MUL = store_thm("COMPLEX_OF_NUM_MUL",
  ``!m:num n:num.
 complex_of_num m * complex_of_num n = complex_of_num (m * n)``,
  REWRITE_TAC [complex_of_num, REAL_OF_NUM_MUL, COMPLEX_OF_REAL_MUL]);

(* ------------------------------------------------------------------ *)
(* A tactical to automate very simple algebraic equivalences.         *)
(* ------------------------------------------------------------------ *)

val SIMPLE_COMPLEX_ARITH_TAC =
  REWRITE_TAC[COMPLEX_RE_IM_EQ, RE, IM, complex_of_real, complex_add,
              complex_neg, complex_sub, complex_mul] THEN REAL_ARITH_TAC;

(*--------------------------------------------------------------------*)
(* Define the left scalar multiplication                              *)
(* and right scalar multiplication                                    *)
(*--------------------------------------------------------------------*)

val complex_scalar_lmul = new_definition
("complex_scalar_lmul",
``complex_scalar_lmul (k:real) (z:complex) = (k * RE z,k * IM z)``);

val complex_scalar_rmul = new_definition
("complex_scalar_rmul",
``complex_scalar_rmul (z:complex) (k:real) = (RE z * k,IM z * k)``);

val _ = overload_on ("*",  Term`$complex_scalar_lmul`);
val _ = overload_on ("*",  Term`$complex_scalar_rmul`);

(*--------------------------------------------------------------------*)
(* The properities of R-module                                        *)
(*--------------------------------------------------------------------*)


val COMPLEX_SCALAR_LMUL = store_thm("COMPLEX_SCALAR_LMUL",
  ``!k:real l:real z:complex. k * (l * z) = k * l * z``,
  REWRITE_TAC[complex_scalar_lmul, RE,IM,REAL_MUL_ASSOC]);

val COMPLEX_SCALAR_LMUL_NEG = store_thm("COMPLEX_SCALAR_LMUL_NEG",
  ``!k:real z:complex. -(k * z) = -k * z``,
  REWRITE_TAC[complex_scalar_lmul,complex_neg,RE,IM,REAL_NEG_LMUL]);

val COMPLEX_NEG_SCALAR_LMUL = store_thm("COMPLEX_NEG_SCALAR_LMUL",
  ``!k:real z:complex. k * (-z) = -k * z``,
  REWRITE_TAC [complex_neg, complex_scalar_lmul, RE, IM, REAL_MUL_LNEG,
               REAL_MUL_RNEG]);

val COMPLEX_SCALAR_LMUL_ADD = store_thm("COMPLEX_SCALAR_LMUL_ADD",
  ``!k:real l:real z:complex. (k + l) * z = k * z + l * z``,
  REWRITE_TAC[complex_add,complex_scalar_lmul,RE,IM,GSYM REAL_ADD_RDISTRIB]);

val COMPLEX_SCALAR_LMUL_SUB = store_thm("COMPLEX_SCALAR_LMUL_SUB",
  ``!k:real l:real z:complex. (k - l) * z = k * z - l * z``,
  REWRITE_TAC [complex_sub, COMPLEX_SCALAR_LMUL_NEG,
               GSYM COMPLEX_SCALAR_LMUL_ADD, real_sub]);

val COMPLEX_ADD_SCALAR_LMUL = store_thm("COMPLEX_ADD_SCALAR_LMUL",
  ``!k:real z:complex w:complex. k * (z + w) = k * z + k * w``,
  REWRITE_TAC[complex_add, complex_scalar_lmul, RE, IM,
              GSYM REAL_ADD_LDISTRIB]);

val COMPLEX_SUB_SCALAR_LMUL = store_thm("COMPLEX_SUB_SCALAR_LMUL",
  ``!k:real z:complex w:complex. k * (z - w) = k * z - k * w``,
  REWRITE_TAC[complex_sub, COMPLEX_ADD_SCALAR_LMUL, COMPLEX_NEG_SCALAR_LMUL,
              COMPLEX_SCALAR_LMUL_NEG]);

val COMPLEX_MUL_SCALAR_LMUL2 = store_thm("COMPLEX_MUL_SCALAR_LMUL2",
  ``!k:real l:real z:complex w:complex.
                (k * z) * (l * w) = (k * l) * (z * w)``,
  REWRITE_TAC [complex_mul, complex_scalar_lmul, RE, IM, PAIR_EQ] THEN
  REAL_ARITH_TAC);

val COMPLEX_LMUL_SCALAR_LMUL = store_thm("COMPLEX_LMUL_SCALAR_LMUL",
  ``!k:real z:complex w:complex. (k * z) * w = k * (z * w)``,
  REWRITE_TAC [complex_mul, complex_scalar_lmul, RE, IM, PAIR_EQ] THEN
  REAL_ARITH_TAC);

val COMPLEX_RMUL_SCALAR_LMUL = store_thm("COMPLEX_RMUL_SCALAR_LMUL",
  ``!k:real z:complex w:complex. z * (k * w) = k * (z * w)``,
  PROVE_TAC[COMPLEX_MUL_COMM, COMPLEX_LMUL_SCALAR_LMUL]);

val COMPLEX_SCALAR_LMUL_ZERO = store_thm("COMPLEX_SCALAR_LMUL_ZERO",
  ``!z:complex. 0r * z = 0``,
  REWRITE_TAC[complex_of_num, complex_of_real, complex_scalar_lmul,
              REAL_MUL_LZERO]);

val COMPLEX_ZERO_SCALAR_LMUL = store_thm("COMPLEX_ZERO_SCALAR_LMUL",
  ``!k:real. k * 0c = 0``,
  REWRITE_TAC[complex_of_num, complex_of_real, complex_scalar_lmul, RE, IM,
              REAL_MUL_RZERO]);

val COMPLEX_SCALAR_LMUL_ONE = store_thm("COMPLEX_SCALAR_LMUL_ONE",
  ``!z:complex. 1r * z = z``,
  REWRITE_TAC[complex_scalar_lmul, REAL_MUL_LID,RE,IM]);

val COMPLEX_SCALAR_LMUL_NEG1 = store_thm ("COMPLEX_SCALAR_LMUL_NEG1",
  ``!z:complex. -1r * z = -z``,
  GEN_TAC THEN REWRITE_TAC[GSYM COMPLEX_SCALAR_LMUL_NEG] THEN
  REWRITE_TAC[COMPLEX_SCALAR_LMUL_ONE]);

val COMPLEX_DOUBLE = store_thm ("COMPLEX_DOUBLE",
  ``!z:complex. z + z = &2 * z``,
  GEN_TAC THEN REWRITE_TAC[num_CONV ``2:num``, REAL] THEN
  REWRITE_TAC[COMPLEX_SCALAR_LMUL_ADD, COMPLEX_SCALAR_LMUL_ONE]);

val COMPLEX_SCALAR_LMUL_ENTIRE = store_thm("COMPLEX_SCALAR_LMUL_ENTIRE",
  ``!k:real z:complex. (k * z = 0) = (k = 0) \/ (z = 0)``,
  REWRITE_TAC[COMPLEX_0_THM, complex_scalar_lmul, RE,IM, POW_2, REAL_SUMSQ,
              REAL_ENTIRE, GSYM LEFT_OR_OVER_AND]);

val COMPLEX_EQ_SCALAR_LMUL = store_thm("COMPLEX_EQ_SCALAR_LMUL",
  ``!k:real z:complex w:complex. (k * z = k * w) = (k = 0) \/ (z = w)``,
  ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_0] THEN
  REWRITE_TAC [GSYM COMPLEX_SUB_SCALAR_LMUL, COMPLEX_SCALAR_LMUL_ENTIRE]);

val COMPLEX_SCALAR_LMUL_EQ = store_thm("COMPLEX_SCALAR_LMUL_EQ",
  ``!k:real l:real z:complex.
                    (k * z = l * z) = (k = l) \/ (z = 0)``,
  ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_0] THEN
  REWRITE_TAC [GSYM COMPLEX_SCALAR_LMUL_SUB, COMPLEX_SCALAR_LMUL_ENTIRE,
               COMPLEX_SUB_RZERO, REAL_SUB_0]);

val COMPLEX_SCALAR_LMUL_EQ1 = store_thm("COMPLEX_SCALAR_LMUL_EQ1",
  ``!k:real z:complex. (k * z = z) = (k = 1) \/ (z = 0)``,
  PROVE_TAC[COMPLEX_SCALAR_LMUL_ONE,COMPLEX_SCALAR_LMUL_EQ]);

val COMPLEX_INV_SCALAR_LMUL = store_thm("COMPLEX_INV_SCALAR_LMUL",
  ``!k:real z:complex.
          k <> 0 /\ z <> 0 ==> (inv (k * z) = inv k * inv z)``,
  REWRITE_TAC [COMPLEX_0_THM, complex_inv,complex_scalar_lmul,RE,IM, POW_MUL,
               GSYM REAL_ADD_LDISTRIB, real_div, REAL_INV_MUL] THEN
  REPEAT STRIP_TAC THEN
  `k pow 2 <> 0` by RW_TAC real_ss[POW_2, REAL_ENTIRE] THEN
  RW_TAC real_ss[REAL_INV_MUL] THEN
  `inv (k pow 2) = inv k * inv k` by RW_TAC real_ss[POW_2, REAL_INV_MUL] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC] THENL[
    `k * FST z * inv k * inv k = inv k * k * FST z * inv k` by REAL_ARITH_TAC,
    `k * SND z * inv k * inv k = inv k * k * SND z * inv k` by REAL_ARITH_TAC
  ] THEN
  ASM_REWRITE_TAC[] THEN RW_TAC real_ss[REAL_MUL_LINV,REAL_MUL_COMM]);

val COMPLEX_SCALAR_LMUL_DIV2 = store_thm("COMPLEX_SCALAR_LMUL_DIV2",
  ``!k l :real z w :complex.
   (l <> 0 /\ w <> 0) ==> ((k * z) / (l * w) = (k / l) * (z / w))``,
  REWRITE_TAC [complex_div] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC COMPLEX_INV_SCALAR_LMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC [COMPLEX_MUL_SCALAR_LMUL2, real_div]);

val COMPLEX_SCALAR_MUL_COMM = store_thm("COMPLEX_SCALAR_MUL_COMM",
  ``!k:real z:complex. k * z = z * k ``,
  PROVE_TAC[complex_scalar_lmul, complex_scalar_rmul, REAL_MUL_COMM]);

val COMPLEX_SCALAR_RMUL = store_thm("COMPLEX_SCALAR_RMUL",
  ``!k:real l:real z:complex. z * k * l = z * (k * l)``,
  RW_TAC bool_ss [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_SCALAR_LMUL,
                  REAL_MUL_COMM]);

val COMPLEX_SCALAR_RMUL_NEG = store_thm("COMPLEX_SCALAR_RMUL_NEG",
  ``!k:real z:complex. -(z * k) = z * -k ``,
  REWRITE_TAC [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_SCALAR_LMUL_NEG]);

val COMPLEX_NEG_SCALAR_RMUL = store_thm("COMPLEX_NEG_SCALAR_RMUL",
  ``!k:real z:complex. (-z) * k = z * -k``,
  REWRITE_TAC [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_NEG_SCALAR_LMUL]);

val COMPLEX_SCALAR_RMUL_ADD = store_thm("COMPLEX_SCALAR_RMUL_ADD",
  ``!k:real l:real z:complex. z * (k + l) = z * k + z * l``,
  REWRITE_TAC [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_SCALAR_LMUL_ADD]);

val COMPLEX_SCALAR_RMUL_SUB = store_thm("COMPLEX_RSCALAR_RMUL_SUB",
  ``!k: real l:real z:complex. z * (k - l) = z * k - z * l ``,
  REWRITE_TAC [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_SCALAR_LMUL_SUB]);

val COMPLEX_ADD_SCALAR_RMUL = store_thm("COMPLEX_ADD_RSCALAR_RMUL",
  ``!k:real z:complex w:complex. (z + w) * k = z * k + w * k``,
  REWRITE_TAC [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_ADD_SCALAR_LMUL]);

val COMPLEX_SUB_SCALAR_RMUL = store_thm("COMPLEX_SUB_SCALAR_RMUL",
  ``!k:real z:complex w:complex. (z - w) * k = z * k - w * k ``,
  REWRITE_TAC [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_SUB_SCALAR_LMUL]);

val COMPLEX_SCALAR_RMUL_ZERO = store_thm("COMPLEX_SCALAR_RMUL_ZERO",
  ``!z:complex. z * 0r = 0``,
  REWRITE_TAC[complex_of_num, complex_of_real, complex_scalar_rmul,
              REAL_MUL_RZERO]);

val COMPLEX_ZERO_SCALAR_RMUL = store_thm("COMPLEX_ZERO_SCALAR_RMUL",
  ``!k:real. 0 * k = 0``,
  REWRITE_TAC [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_ZERO_SCALAR_LMUL]);

val COMPLEX_SCALAR_RMUL_ONE = store_thm("COMPLEX_SCALAR_RMUL_ONE",
  ``!z:complex. z * 1r = z``,
  REWRITE_TAC [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_SCALAR_LMUL_ONE]);

val COMPLEX_SCALAR_RMUL_NEG1 = store_thm ("COMPLEX_SCALAR_RMUL_NEG1",
  ``!z:complex. z * -1r = -z``,
  REWRITE_TAC [GSYM COMPLEX_SCALAR_MUL_COMM, COMPLEX_SCALAR_LMUL_NEG1]);

(*--------------------------------------------------------------------*)
(* Complex conjugate                                                  *)
(*--------------------------------------------------------------------*)

val conj = new_definition
     ("conj", ``conj (z:complex) = (RE z, -IM z)``);

val CONJ_REAL_REFL= store_thm("CONJ_REAL_REFL",
  ``!x:real. conj (complex_of_real x) = complex_of_real x``,
  REWRITE_TAC[complex_of_real,conj, RE,IM, REAL_NEG_0]);

val CONJ_NUM_REFL= store_thm("CONJ_NUM_REFL",
  ``!n:num. conj (complex_of_num n) = complex_of_num n``,
  REWRITE_TAC[complex_of_num,CONJ_REAL_REFL]);

val CONJ_ADD = store_thm("CONJ_ADD",
  ``!z:complex w:complex. conj (z + w) = conj z + conj w``,
  REWRITE_TAC [conj,complex_add,RE,IM,REAL_NEG_ADD]);

val CONJ_NEG = store_thm("CONJ_NEG",
  ``!z:complex. conj (-z) = -conj z ``,
  REWRITE_TAC [complex_neg, conj,RE,IM]);

val CONJ_SUB = store_thm("CONJ_SUB",
  ``!z:complex w:complex. conj (z - w) = conj z - conj w``,
  REWRITE_TAC [complex_sub, CONJ_NEG, CONJ_ADD]);

val CONJ_MUL = store_thm("CONJ_MUL",
  ``!z:complex w:complex. conj (z * w) = conj z * conj w``,
  REWRITE_TAC [conj,complex_mul, RE,IM,REAL_NEG_ADD, REAL_NEG_MUL2,
               GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL]);

val CONJ_INV = store_thm("CONJ_INV",
  ``!z: complex. conj (inv z) = inv (conj z)``,
  RW_TAC real_ss [conj, complex_inv, RE, IM, POW_2, real_div]);

val CONJ_DIV= store_thm("CONJ_DIV",
  ``!z:complex w. conj (z / w) = conj z / conj w``,
  REWRITE_TAC[complex_div, CONJ_MUL, CONJ_INV]);

val CONJ_SCALAR_LMUL = store_thm("CONJ_SCALAR_LMUL",
  ``!k:real z:complex. conj (k * z) = k * conj z``,
  REWRITE_TAC [conj,complex_scalar_lmul, RE,IM,REAL_MUL_RNEG]);

val CONJ_CONJ = store_thm("CONJ_CONJ",
  ``!z:complex. conj (conj z) = z``,
  REWRITE_TAC[conj, RE,IM,REAL_NEGNEG]);

val CONJ_EQ = store_thm("CONJ_EQ",
  ``!z:complex w:complex. (conj z = w) = (z = conj w)``,
  REWRITE_TAC [conj, COMPLEX_RE_IM_EQ, RE, IM, REAL_NEG_EQ]);

val CONJ_EQ2 = store_thm("CONJ_EQ2",
  ``!z:complex w:complex. (conj z = conj w) = (z = w)``,
  REWRITE_TAC [CONJ_EQ, CONJ_CONJ]);

val COMPLEX_MUL_RCONJ = store_thm("COMPLEX_MUL_RCONJ",
  ``!z:complex.
         z * conj z = complex_of_real ((RE z) pow 2 + (IM z) pow 2)``,
  REWRITE_TAC [complex_mul, conj, complex_of_real, RE, IM, REAL_MUL_RNEG,
               REAL_SUB_RNEG] THEN
  PROVE_TAC [POW_2, REAL_MUL_COMM, REAL_ADD_LINV]);

val COMPLEX_MUL_LCONJ = store_thm("COMPLEX_MUL_RCONJ",
  ``!z:complex.
         conj z * z = complex_of_real ((RE z) pow 2 + (IM z) pow 2)``,
  PROVE_TAC [COMPLEX_MUL_COMM, COMPLEX_MUL_RCONJ]);

val CONJ_ZERO = store_thm("CONJ_ZERO",
  ``conj 0 = 0``,
  REWRITE_TAC [CONJ_NUM_REFL]);

(*--------------------------------------------------------------------*)
(* Define modulus and  argument principal value of complex            *)
(*--------------------------------------------------------------------*)

val modu = new_definition("modu",
  ``modu (z:complex) = sqrt( RE z pow 2 + IM z pow 2)``);

val arg = new_definition("arg",
  ``arg z =
       if 0 <= IM z then acs (RE z / modu z)
       else -acs (RE z / modu z) + 2 * pi``);

(*--------------------------------------------------------------------*)
(* The properities of  modulus and  argument principal value          *)
(*--------------------------------------------------------------------*)

val MODU_POW2 = store_thm("MODU_POW2",
  ``!z:complex. modu z pow 2 = RE z pow 2 + IM z pow 2 ``,
  REWRITE_TAC[modu] THEN
  PROVE_TAC [REAL_LE_POW2, REAL_LE_ADD, SQRT_POW_2]);

val RE_IM_LE_MODU= store_thm("RE_IM_LE_MODU",
  ``!z:complex. abs (RE z) <= modu z /\ abs (IM z) <= modu z``,
  REWRITE_TAC [modu] THEN GEN_TAC THEN CONJ_TAC THENL
  [REWRITE_TAC [COMPLEX_LEMMA2],
  ONCE_REWRITE_TAC [REAL_ADD_COMM] THEN REWRITE_TAC [COMPLEX_LEMMA2]]);

val MODU_POS= store_thm("MODU_POS",
  ``!z:complex. 0 <= modu z``,
  GEN_TAC THEN REWRITE_TAC[modu] THEN MATCH_MP_TAC SQRT_POS_LE THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW2]);

val COMPLEX_MUL_RCONJ1 = store_thm("COMPLEX_MUL_RCONJ1",
  ``!z:complex. z * conj z = complex_of_real ((modu z) pow 2)``,
  REWRITE_TAC[COMPLEX_MUL_RCONJ, MODU_POW2]);

val COMPLEX_MUL_LCONJ1 = store_thm("COMPLEX_MUL_LCONJ1",
  ``!z:complex. conj z * z = complex_of_real ((modu z) pow 2)``,
  REWRITE_TAC[COMPLEX_MUL_LCONJ, MODU_POW2]);

val MODU_NEG = store_thm("MODU_NEG",
  ``!z:complex. modu (-z) = modu z``,
  REWRITE_TAC[modu,complex_neg,RE,IM,POW_2,REAL_NEG_MUL2]);

val MODU_SUB = store_thm("MODU_SUB",
  ``!z:complex w:complex. modu (z - w) = modu (w - z)``,
  REPEAT GEN_TAC THEN
  `w - z = -(z - w)` by REWRITE_TAC[COMPLEX_NEG_SUB] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[MODU_NEG]);

val MODU_CONJ = store_thm("MODU_CONJ",
  ``!z:complex. modu (conj z) = modu z ``,
  REWRITE_TAC[modu, conj,RE,IM,POW_2,REAL_NEG_MUL2]);

val MODU_MUL = store_thm("MODU_MUL",
  ``!z:complex w:complex. modu (z * w) = modu z * modu w``,
  REWRITE_TAC [modu, complex_mul, RE, IM, COMPLEX_LEMMA1] THEN
  PROVE_TAC [REAL_LE_POW2, REAL_LE_ADD, SQRT_MUL]);

val MODU_0 = store_thm("MODU_0",
  ``modu 0 = 0 ``,
  REWRITE_TAC[complex_of_num,complex_of_real, modu, RE, IM, POW_2,
              REAL_MUL_RZERO, REAL_ADD_RID, SQRT_0]);

val MODU_1 = store_thm("MODU_1",
  ``modu 1 = 1 ``,
  REWRITE_TAC[complex_of_num,complex_of_real, modu, RE, IM, POW_2,
              REAL_MUL_RID, REAL_MUL_RZERO, REAL_ADD_RID, SQRT_1]);

val MODU_COMPLEX_INV = store_thm("MODU_COMPLEX_INV",
  ``!z: complex. z <> 0 ==> (modu (inv z) = inv (modu z))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[GSYM MODU_MUL] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP COMPLEX_MUL_LINV th]) THEN
  REWRITE_TAC [MODU_1]);

val MODU_DIV = store_thm("MODU_DIV",
  ``!z w : complex. (w <> 0) ==> (modu(z / w) = modu z / modu w) ``,
  REWRITE_TAC[complex_div, MODU_MUL] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP MODU_COMPLEX_INV th]) THEN
  REWRITE_TAC[real_div]);

val MODU_SCALAR_LMUL = store_thm("MODU_SCALAR_LMUL",
  ``!k:real z:complex. modu (k * z) = abs k * modu z``,
  REWRITE_TAC [modu, complex_scalar_lmul, RE, IM, POW_MUL,
               GSYM REAL_ADD_LDISTRIB] THEN
  ONCE_REWRITE_TAC [GSYM REAL_POW2_ABS] THEN
  PROVE_TAC[REAL_ABS_POS,REAL_LE_POW2,REAL_LE_ADD,SQRT_MUL,POW_2_SQRT]);

val MODU_REAL = store_thm("MODU_REAL",
  ``!x:real. modu (complex_of_real x) = abs x``,
  REWRITE_TAC [complex_of_real, modu, RE, IM, POW_2, REAL_MUL_RZERO,
               REAL_ADD_RID] THEN
  REWRITE_TAC [GSYM POW_2] THEN
  ONCE_REWRITE_TAC [GSYM REAL_POW2_ABS] THEN GEN_TAC THEN
  `0 <= abs x` by PROVE_TAC [REAL_ABS_POS] THEN
  FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP POW_2_SQRT th]));

val MODU_NUM = store_thm("MODU_NUM",
  ``!n:num. modu (complex_of_num n) = &n``,
  REWRITE_TAC [complex_of_num, MODU_REAL, ABS_N]);

val MODU_ZERO = store_thm("MODU_ZERO",
  ``!z:complex. (z = 0) = (modu z = 0)``,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[MODU_0, COMPLEX_0_THM, GSYM MODU_POW2,
                  num_CONV (``2:num``), POW_0]);

val MODU_NZ = store_thm("MODU_NZ",
  ``!z:complex. (z <> 0) = 0 < modu z``,
  GEN_TAC THEN EQ_TAC THENL [
    REWRITE_TAC[MODU_ZERO] THEN
    DISCH_TAC THEN
    PROVE_TAC[REAL_LE_LT, MODU_POS],
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MODU_0, REAL_LT_REFL]
  ]);

val MODU_CASES = store_thm("MODU_CASES",
  ``!z:complex. (z = 0) \/ 0 < modu z``,
  GEN_TAC THEN REWRITE_TAC[GSYM MODU_NZ] THEN
  Cases_on `z = 0` THEN ASM_REWRITE_TAC[]);

val RE_DIV_MODU_BOUNDS = store_thm("RE_DIV_MODU_BOUNDS",
  ``!z:complex.
       z <> 0 ==> (-1 <= RE z / modu z /\ RE z / modu z <= 1)``,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [
    MATCH_MP_TAC REAL_LE_RDIV THEN CONJ_TAC THENL [
      PROVE_TAC[MODU_NZ],
      REWRITE_TAC[REAL_MUL_LNEG,REAL_MUL_LID] THEN
      PROVE_TAC[RE_IM_LE_MODU,ABS_BOUNDS]
    ],
    MATCH_MP_TAC REAL_LE_LDIV THEN CONJ_TAC THENL [
      PROVE_TAC[MODU_NZ],
      REWRITE_TAC[REAL_MUL_LNEG,REAL_MUL_LID] THEN
      PROVE_TAC[RE_IM_LE_MODU,ABS_BOUNDS]
    ]
  ]);

val IM_DIV_MODU_BOUNDS = store_thm("IM_DIV_MODU_BOUNDS",
  ``!z:complex.
       z <> 0 ==> (-1 <= IM z / modu z /\ IM z / modu z <= 1)``,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [
    MATCH_MP_TAC REAL_LE_RDIV THEN CONJ_TAC THENL [
      PROVE_TAC[MODU_NZ],
      REWRITE_TAC[REAL_MUL_LNEG,REAL_MUL_LID] THEN
      PROVE_TAC[RE_IM_LE_MODU,ABS_BOUNDS]
    ],
    MATCH_MP_TAC REAL_LE_LDIV THEN CONJ_TAC THENL [
      PROVE_TAC[MODU_NZ],
      REWRITE_TAC[REAL_MUL_LID] THEN
      PROVE_TAC[RE_IM_LE_MODU,ABS_BOUNDS]
    ]
  ]);

val RE_DIV_MODU_ACS_BOUNDS = store_thm("RE_DIV_MODU_ACS_BOUNDS",
  ``!z:complex.
    z <> 0 ==>
        (0 <=acs (RE z / modu z) /\ acs (RE z / modu z) <= pi)``,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ACS_BOUNDS THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC RE_DIV_MODU_BOUNDS);

val IM_DIV_MODU_ASN_BOUNDS = store_thm("IM_DIV_MODU_ASN_BOUNDS",
  ``!z:complex.
   z <> 0 ==>
   (-(pi/2) <= asn (IM z / modu z) /\ asn (IM z / modu z) <= pi/2)``,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ASN_BOUNDS THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC IM_DIV_MODU_BOUNDS);

val RE_DIV_MODU_ACS_COS = store_thm("RE_DIV_MODU_ACS_COS",
  ``!z:complex.
  z <> 0 ==> (cos ( acs (RE z / modu z)) = RE z / modu z)``,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ACS_COS THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC RE_DIV_MODU_BOUNDS );

val IM_DIV_MODU_ASN_SIN = store_thm("IM_DIV_MODU_ASN_SIN",
  ``!z:complex.
       z <> 0 ==> (sin ( asn (IM z / modu z)) = IM z / modu z)``,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ASN_SIN THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC IM_DIV_MODU_BOUNDS);

val ARG_COS = store_thm("ARG_COS",
  ``!z:complex. z <> 0 ==> (cos (arg z) = RE z / modu z)``,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[arg] THEN COND_CASES_TAC THEN
  REWRITE_TAC[COS_PERIODIC, COS_NEG] THEN
  MATCH_MP_TAC RE_DIV_MODU_ACS_COS THEN ASM_REWRITE_TAC[]);

val ARG_SIN = store_thm("ARG_SIN",
  ``!z:complex. z <> 0 ==> (sin (arg z) = IM z / modu z)``,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[arg] THEN COND_CASES_TAC THENL [
    Q.SUBGOAL_THEN
      `sin (acs (RE z / modu z)) = sqrt (1 - cos (acs (RE z / modu z)) pow 2)`
      ASSUME_TAC
    THENL [
      MATCH_MP_TAC SIN_COS_SQ THEN
      MATCH_MP_TAC RE_DIV_MODU_ACS_BOUNDS THEN
      ASM_REWRITE_TAC[],
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP RE_DIV_MODU_ACS_COS th]) THEN
      Q.SUBGOAL_THEN `1 - (RE z / modu z) pow 2 = (IM z / modu z) pow 2 `
                     ASSUME_TAC
      THENL [
        REWRITE_TAC[REAL_EQ_SUB_RADD, REAL_POW_DIV, REAL_DIV_ADD] THEN
        ONCE_REWRITE_TAC[REAL_ADD_COMM] THEN
        REWRITE_TAC[GSYM MODU_POW2] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC REAL_DIV_REFL THEN
        ASM_REWRITE_TAC[MODU_POW2, GSYM COMPLEX_0_THM],
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POW_2_SQRT THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[MODU_POS]
      ]
    ],
    REWRITE_TAC[SIN_PERIODIC,SIN_NEG, REAL_NEG_EQ] THEN
    Q.SUBGOAL_THEN
      `sin (acs (RE z / modu z)) = sqrt (1 - cos (acs (RE z / modu z)) pow 2)`
      ASSUME_TAC
    THENL [
      MATCH_MP_TAC SIN_COS_SQ THEN
      MATCH_MP_TAC RE_DIV_MODU_ACS_BOUNDS THEN
      ASM_REWRITE_TAC[],
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP RE_DIV_MODU_ACS_COS th]) THEN
      `1 - (RE z / modu z) pow 2 = (IM z / modu z) pow 2`
        by (REWRITE_TAC[REAL_EQ_SUB_RADD, REAL_POW_DIV, REAL_DIV_ADD] THEN
            ONCE_REWRITE_TAC[REAL_ADD_COMM] THEN
            REWRITE_TAC[GSYM MODU_POW2] THEN CONV_TAC SYM_CONV THEN
            MATCH_MP_TAC REAL_DIV_REFL THEN
            ASM_REWRITE_TAC[MODU_POW2, GSYM COMPLEX_0_THM]) THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
      REWRITE_TAC[REAL_POW2_ABS] THEN
      MATCH_MP_TAC POW_2_SQRT THEN
      REWRITE_TAC[real_div, REAL_NEG_LMUL] THEN
      REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN
      PROVE_TAC [MODU_POS, REAL_NOT_LE, REAL_NEG_GT0, REAL_LT_IMP_LE]
    ]
  ]);

val RE_MODU_ARG = store_thm("RE_MODU_ARG",
  ``!z:complex. RE z = modu z * cos (arg z)``,
  GEN_TAC THEN ASM_CASES_TAC (``z = 0``) THENL
  [ASM_REWRITE_TAC[MODU_0] THEN
  REWRITE_TAC[complex_of_num,complex_of_real,RE,REAL_MUL_LZERO],
  FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP ARG_COS th]) THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC  REAL_DIV_LMUL THEN
  ASM_REWRITE_TAC[GSYM MODU_ZERO]
  ]);

val IM_MODU_ARG = store_thm("IM_MODU_ARG",
  ``!z:complex. IM z = modu z * sin (arg z)``,
  GEN_TAC THEN ASM_CASES_TAC (``z = 0``) THENL [
    ASM_REWRITE_TAC[MODU_0] THEN
    REWRITE_TAC[complex_of_num,complex_of_real,IM,REAL_MUL_LZERO],
    FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP ARG_SIN th]) THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC  REAL_DIV_LMUL THEN
    ASM_REWRITE_TAC[GSYM MODU_ZERO]
  ]);

val COMPLEX_TRIANGLE = store_thm("COMPLEX_TRIANGLE",
  ``!z:complex. modu z * (cos (arg z),sin (arg z)) = z``,
  REWRITE_TAC[complex_scalar_lmul, RE, IM, GSYM RE_MODU_ARG, GSYM IM_MODU_ARG]);

val COMPLEX_MODU_ARG_EQ = store_thm("COMPLEX_MODU_ARG_EQ",
  ``!z:complex w. (z = w) = ((modu z = modu w) /\ (arg z = arg w))``,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_RE_IM_EQ,RE_MODU_ARG,IM_MODU_ARG]);

val MODU_UNIT = store_thm("MODU_UNIT",
  ``!x:real y. modu (cos x,sin x) = 1``,
  REWRITE_TAC [modu, RE, IM] THEN ONCE_REWRITE_TAC[REAL_ADD_COMM]
  THEN REWRITE_TAC[SIN_CIRCLE, SQRT_1]);

val COMPLEX_MUL_ARG = store_thm("COMPLEX_MUL_ARG",
  ``!x:real y:real.
         (cos x,sin x) * (cos y, sin y) = (cos (x + y),sin (x + y))``,
  REWRITE_TAC [complex_mul, RE, IM, SIN_ADD, COS_ADD] THEN
  PROVE_TAC [REAL_ADD_COMM]);

val COMPLEX_INV_ARG = store_thm("COMPLEX_INV_ARG",
  ``!x:real. inv (cos x,sin x) = (cos (-x),sin (-x))``,
  REWRITE_TAC [complex_inv, RE, IM] THEN
  ONCE_REWRITE_TAC [REAL_ADD_COMM] THEN
  REWRITE_TAC[SIN_CIRCLE, real_div, REAL_INV1,REAL_MUL_RID, COS_NEG, SIN_NEG]);

val COMPLEX_DIV_ARG = store_thm("COMPLEX_DIV_ARG",
  ``!x:real y.
      (cos x,sin x) / (cos y, sin y) = (cos(x - y),sin(x - y))``,
  REWRITE_TAC[complex_div,COMPLEX_INV_ARG,COMPLEX_MUL_ARG,real_sub]);

(*--------------------------------------------------------------------*)
(* The operation of nature numbers power of complex numbers           *)
(*--------------------------------------------------------------------*)

val complex_pow = Define
`(complex_pow (z:complex) 0 = 1) /\
      (complex_pow (z:complex) (SUC n) = z * (complex_pow z n))`;

val _ = overload_on ("pow",  Term`$complex_pow`);

val COMPLEX_POW_0 = store_thm("COMPLEX_POW_0",
  ``!n:num. 0 pow (SUC n) = 0``,
  INDUCT_TAC THEN REWRITE_TAC[complex_pow, COMPLEX_MUL_LZERO]);

val COMPLEX_POW_NZ = store_thm("COMPLEX_POW_NZ",
  ``!z:complex n:num. (z <> 0) ==> (z pow n <> 0)``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC((``n:num``),(``n:num``)) THEN  INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow, COMPLEX_10, COMPLEX_ENTIRE]);

val COMPLEX_POWINV = store_thm("COMPLEX_POWINV",
  ``!z:complex.
         ~(z = 0) ==> !n:num. (inv(z pow n) = (inv z) pow n)``,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[complex_pow, COMPLEX_INV1] THEN
  MP_TAC(SPECL [(``z:complex``), (``z pow n``)] COMPLEX_INV_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (``~(z pow n = 0)``) ASSUME_TAC THENL
  [MATCH_MP_TAC COMPLEX_POW_NZ THEN ASM_REWRITE_TAC[], ALL_TAC]
  THEN  ASM_REWRITE_TAC[]);

val MODU_COMPLEX_POW = store_thm("MODU_COMPLEX_POW",
  ``!z:complex n:num. modu (z pow n) = modu z pow n``,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow,pow, MODU_1, MODU_MUL]);

val COMPLEX_POW_ADD = store_thm("COMPLEX_POW_ADD",
  ``!z:complex m:num n. z pow (m + n) = (z pow m) * (z pow n)``,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow, ADD_CLAUSES, COMPLEX_MUL_RID] THEN
  CONV_TAC(AC_CONV(COMPLEX_MUL_ASSOC,COMPLEX_MUL_COMM)));

val COMPLEX_POW_1 = store_thm("COMPLEX_POW_1",
  ``!z:complex. z pow 1 = z``,
  GEN_TAC THEN REWRITE_TAC[num_CONV (``1:num``)] THEN
  REWRITE_TAC[complex_pow, COMPLEX_MUL_RID]);

val COMPLEX_POW_2 = store_thm("COMPLEX_POW_2",
  ``!z:complex. z pow 2 = z * z``,
  GEN_TAC THEN REWRITE_TAC[num_CONV ``2:num``] THEN
  REWRITE_TAC[complex_pow, COMPLEX_POW_1]);

val COMPLEX_POW_ONE = store_thm("COMPLEX_POW_ONE",
  ``!n:num. 1 pow n = 1``,
  INDUCT_TAC THEN ASM_REWRITE_TAC[complex_pow, COMPLEX_MUL_LID]);

val COMPLEX_POW_MUL = store_thm("COMPLEX_POW_MUL",
  ``!n:num z:complex w:complex. (z * w) pow n = (z pow n) * (w pow n)``,
  INDUCT_TAC THEN REWRITE_TAC[complex_pow, COMPLEX_MUL_LID] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(COMPLEX_MUL_ASSOC,COMPLEX_MUL_COMM)));

val COMPLEX_POW_INV = store_thm("COMPLEX_POW_INV",
  ``!z:complex n:num. (inv z) pow n = inv (z pow n)``,
  Induct_on `n` THEN REWRITE_TAC [complex_pow] THENL
  [REWRITE_TAC [COMPLEX_INV1],
   GEN_TAC THEN Cases_on `z = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC
     THEN REWRITE_TAC [COMPLEX_INV_0,COMPLEX_MUL_LZERO],
    `~(z pow n = 0)` by PROVE_TAC [COMPLEX_POW_NZ] THEN
    IMP_RES_TAC COMPLEX_INV_MUL THEN ASM_REWRITE_TAC []]]);

val COMPLEX_POW_DIV = store_thm("COMPLEX_POW_DIV",
  ``!z:complex w:complex n:num. (z / w) pow n = (z pow n) / (w pow n)``,
  REWRITE_TAC[complex_div, COMPLEX_POW_MUL, COMPLEX_POW_INV]);

val COMPLEX_POW_SCALAR_LMUL = store_thm("COMPLEX_POW_L",
  ``!n:num k:real z:complex. (k * z) pow n = (k pow n) * (z pow n)``,
  INDUCT_TAC THEN
  REWRITE_TAC[complex_pow, pow, COMPLEX_SCALAR_LMUL_ONE] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_MUL_SCALAR_LMUL2]);

val COMPLEX_POW_ZERO = store_thm("COMPLEX_POW_ZERO",
  ``!n:num z:complex. (z pow n = 0) ==> (z = 0)``,
  INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[complex_pow] THEN
  REWRITE_TAC[COMPLEX_10, COMPLEX_ENTIRE] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);

val COMPLEX_POW_ZERO_EQ = store_thm("COMPLEX_POW_ZERO_EQ",
  ``!n:num z:complex. (z pow (SUC n) = 0) = (z = 0)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  REWRITE_TAC[COMPLEX_POW_ZERO] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COMPLEX_POW_0]);

val COMPLEX_POW_POW = store_thm("COMPLEX_POW_POW",
  ``!z:complex m:num n:num. (z pow m) pow n = z pow (m * n)``,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow, MULT_CLAUSES, COMPLEX_POW_ADD]);

val DE_MOIVRE_LEMMA = store_thm("DE_MOIVRE_LEMMA",
  ``!x:real n:num. (cos x, sin x) pow n = (cos (&n * x), sin(&n * x))``,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC [complex_pow, REAL_MUL_LZERO, COS_0, SIN_0, complex_of_num,
                   complex_of_real, COMPLEX_MUL_ARG] THEN
  ONCE_REWRITE_TAC [REAL_ADD_COMM] THEN
  REWRITE_TAC[REAL, REAL_ADD_RDISTRIB, REAL_MUL_LID]);

val DE_MOIVRE_THM = store_thm("DE_MOIVRE_THM",
  ``!z:complex n:num.
     (modu z * (cos (arg z),sin (arg z))) pow n =
          modu z pow n * (cos (&n * arg z),sin(&n * arg z))``,
  REWRITE_TAC[COMPLEX_POW_SCALAR_LMUL, DE_MOIVRE_LEMMA]);

(*--------------------------------------------------------------------*)
(*Exponential form of complex numbers                                 *)
(*--------------------------------------------------------------------*)

val complex_exp = new_definition("complex_exp",
  ``complex_exp (z:complex) = exp(RE z) * (cos (IM z),sin (IM z))``);

val _ = overload_on ("exp",  Term`$complex_exp`);

val EXP_IMAGINARY = store_thm("EXP_IMAGINARY",
  ``!x:real. exp (i * x) = (cos x,sin x)``,
  REWRITE_TAC[complex_exp, i, complex_scalar_rmul, RE, IM, REAL_MUL_LZERO,
              REAL_MUL_LID, EXP_0, COMPLEX_SCALAR_LMUL_ONE]);

val EULER_FORMULE = store_thm("EULER_FORMULE",
  ``!z:complex. modu z * exp (i * arg z) = z``,
  REWRITE_TAC[complex_exp, i, complex_scalar_rmul, RE, IM, REAL_MUL_LZERO,
              REAL_MUL_LID, EXP_0, COMPLEX_SCALAR_LMUL_ONE, COMPLEX_TRIANGLE]);

val COMPLEX_EXP_ADD = store_thm("COMPLEX_EXP_ADD",
  ``!z:complex w:complex. exp (z + w) = exp z * exp w``,
  REWRITE_TAC[complex_exp, COMPLEX_MUL_SCALAR_LMUL2, GSYM EXP_ADD,
              COMPLEX_MUL_ARG, complex_add, RE, IM]);

val COMPLEX_EXP_NEG = store_thm("COMPLEX_EXP_NEG",
  ``!z:complex. exp (-z) = inv (exp z)``,
  GEN_TAC THEN
  REWRITE_TAC [complex_exp, complex_neg, RE, IM, EXP_NEG,
               GSYM COMPLEX_INV_ARG] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPLEX_INV_SCALAR_LMUL THEN
  REWRITE_TAC[EXP_NZ, MODU_NZ, MODU_UNIT, REAL_LT_01]);

val COMPLEX_EXP_SUB = store_thm("COMPLEX_EXP_SUB",
  ``!z:complex w:complex. exp (z - w) = exp z / exp w``,
  REWRITE_TAC[complex_sub,COMPLEX_EXP_ADD,COMPLEX_EXP_NEG,complex_div]);

val COMPLEX_EXP_N = store_thm("COMPLEX_EXP_N",
  ``!z:complex n:num. exp (&n : real * z) = exp z pow n``,
  REWRITE_TAC[complex_scalar_lmul] THEN
  REWRITE_TAC[complex_exp, RE, IM, EXP_N, GSYM DE_MOIVRE_LEMMA,
              COMPLEX_POW_SCALAR_LMUL]);

val COMPLEX_EXP_N2 = store_thm("COMPLEX_EXP_N2",
  ``!z:complex n:num. exp (&n :complex * z) = exp z pow n``,
  REWRITE_TAC[complex_mul, complex_of_num, RE_COMPLEX_OF_REAL,
              IM_COMPLEX_OF_REAL, REAL_MUL_LZERO, REAL_ADD_RID,REAL_SUB_RZERO,
              GSYM complex_scalar_lmul, COMPLEX_EXP_N]);

val COMPLEX_EXP_0 = store_thm("COMPLEX_EXP_0",
  ``exp 0c = 1``,
  REWRITE_TAC[complex_of_num, complex_of_real, complex_exp, RE, IM, EXP_0,
              COS_0, SIN_0, COMPLEX_SCALAR_LMUL_ONE]);

val COMPLEX_EXP_NZ = store_thm("COMPLEX_EXP_NZ",
  ``!z:complex. exp z <> 0``,
  REWRITE_TAC[complex_exp, COMPLEX_SCALAR_LMUL_ENTIRE] THEN
  REWRITE_TAC[EXP_NZ, MODU_NZ, MODU_UNIT, REAL_LT_01]);

val COMPLEX_EXP_ADD_MUL = store_thm("COMPLEX_EXP_ADD_MUL",
  ``!z:complex w:complex. exp (z + w) * exp (-z) = exp w``,
  REWRITE_TAC[GSYM COMPLEX_EXP_ADD, GSYM complex_sub, COMPLEX_ADD_SUB]);

val COMPLEX_EXP_NEG_MUL = store_thm("COMPLEX_EXP_NEG_MUL",
  ``!z:complex. exp z * exp (-z) = 1``,
  REWRITE_TAC[GSYM COMPLEX_EXP_ADD, COMPLEX_ADD_RINV, COMPLEX_EXP_0]);

val COMPLEX_EXP_NEG_MUL2 = store_thm("COMPLEX_EXP_NEG_MUL2",
 ``!z:complex. exp (-z) * exp z = 1``,
  ONCE_REWRITE_TAC[COMPLEX_MUL_COMM] THEN
  MATCH_ACCEPT_TAC COMPLEX_EXP_NEG_MUL);

val _ = export_theory()
