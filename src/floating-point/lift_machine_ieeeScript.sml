Theory lift_machine_ieee
Ancestors
  machine_ieee lift_ieee
Libs
  wordsLib

(* --------------------------------------------------------------------- *)

Definition interval_def:   interval a b = {x : real | a <= x /\ x < b}
End

val lb = UTF8.chr 0x298B
  (* square bracket with underbar, reminiscent of the way < gets an underbar
     to include equality *)
val cm = UTF8.chr 0x2B1D (* square dot *)
val rp = UTF8.chr 0x27EF (* "flattened" right parenthesis *)

val _ = add_rule {
  term_name = "interval" , fixity = Closefix,
  pp_elements = [TOK lb, PPBlock([TM, HardSpace 1, TOK cm, BreakSpace(1,0), TM],
                                 (PP.CONSISTENT, 1)), TOK rp],
  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
  paren_style = OnlyIfNecessary};

(* I.e., [1,2) looks like ⦋1 ⬝ 2⟯ *)
(* which is perhaps a bit gross really *)

(* --------------------------------------------------------------------- *)

val rule =
  wordsLib.WORD_EVAL_RULE o
  REWRITE_RULE
    [normalizes_def, binary_ieeeTheory.threshold_def, realTheory.REAL_INV_1OVER,
     GSYM (SIMP_CONV (srw_ss()) [interval_def] ``a IN interval x y``)]

Theorem word_msb16[local]:
   !a: word16. ~word_msb a = ((fp16_to_float a).Sign = 0w)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [fp16_to_float_def]
QED

Theorem word_msb32[local]:
   !a: word32. ~word_msb a = ((fp32_to_float a).Sign = 0w)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [fp32_to_float_def]
QED

Theorem word_msb64[local]:
   !a: word64. ~word_msb a = ((fp64_to_float a).Sign = 0w)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [fp64_to_float_def]
QED

val tac =
  simp_tac std_ss
     [fp16_to_real_def, fp16_isFinite_def, fp16_isZero_def, word_msb16,
      fp16_add_def, fp16_sub_def, fp16_mul_def, fp16_div_def, fp16_sqrt_def,
      fp16_mul_add_def, fp16_mul_sub_def, fp16_to_float_float_to_fp16,
      fp32_to_real_def, fp32_isFinite_def, fp32_isZero_def, word_msb32,
      fp32_add_def, fp32_sub_def, fp32_mul_def, fp32_div_def, fp32_sqrt_def,
      fp32_mul_add_def, fp32_mul_sub_def, fp32_to_float_float_to_fp32,
      fp64_to_real_def, fp64_isFinite_def,fp64_isZero_def, word_msb64,
      fp64_add_def, fp64_sub_def, fp64_mul_def, fp64_div_def, fp64_sqrt_def,
      fp64_mul_add_def, fp64_mul_sub_def, fp64_to_float_float_to_fp64,
      float_add_relative, float_sub_relative,
      float_mul_relative, float_div_relative,
      float_mul_add_relative, float_mul_sub_relative, float_sqrt_relative]

(* --------------------------------------------------------------------- *)

Theorem fp16_float_add_relative[local]:
   !a b.
      fp16_isFinite a /\ fp16_isFinite b /\
      normalizes (:10 # 5) (fp16_to_real a + fp16_to_real b) ==>
      fp16_isFinite (fp16_add roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real (fp16_add roundTiesToEven a b) =
           (fp16_to_real a + fp16_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp16_float_sub_relative[local]:
   !a b.
      fp16_isFinite a /\ fp16_isFinite b /\
      normalizes (:10 # 5) (fp16_to_real a - fp16_to_real b) ==>
      fp16_isFinite (fp16_sub roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real (fp16_sub roundTiesToEven a b) =
           (fp16_to_real a - fp16_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp16_float_mul_relative[local]:
   !a b.
      fp16_isFinite a /\ fp16_isFinite b /\
      normalizes (:10 # 5) (fp16_to_real a * fp16_to_real b) ==>
      fp16_isFinite (fp16_mul roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real (fp16_mul roundTiesToEven a b) =
           (fp16_to_real a * fp16_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp16_float_mul_add_relative[local]:
   !a b c.
      fp16_isFinite a /\ fp16_isFinite b /\ fp16_isFinite c /\
      normalizes (:10 # 5)
       (fp16_to_real a * fp16_to_real b + fp16_to_real c) ==>
      fp16_isFinite (fp16_mul_add roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real (fp16_mul_add roundTiesToEven a b c) =
           (fp16_to_real a * fp16_to_real b +
            fp16_to_real c) * (1 + e))
Proof
  tac
QED

Theorem fp16_float_mul_sub_relative[local]:
   !a b c.
      fp16_isFinite a /\ fp16_isFinite b /\ fp16_isFinite c /\
      normalizes (:10 # 5)
       (fp16_to_real a * fp16_to_real b - fp16_to_real c) ==>
      fp16_isFinite (fp16_mul_sub roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real (fp16_mul_sub roundTiesToEven a b c) =
           (fp16_to_real a * fp16_to_real b -
            fp16_to_real c) * (1 + e))
Proof
  tac
QED

Theorem fp16_float_div_relative[local]:
   !a b.
      fp16_isFinite a /\ fp16_isFinite b /\ ~fp16_isZero b /\
      normalizes (:10 # 5) (fp16_to_real a / fp16_to_real b) ==>
      fp16_isFinite (fp16_div roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real (fp16_div roundTiesToEven a b) =
           (fp16_to_real a / fp16_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp16_float_sqrt_relative[local]:
   !a.
      fp16_isFinite a /\ (~word_msb a \/ a = INT_MINw) /\
      normalizes (:10 # 5) (sqrt (fp16_to_real a)) ==>
      fp16_isFinite (fp16_sqrt roundTiesToEven a) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real (fp16_sqrt roundTiesToEven a) =
           (sqrt (fp16_to_real a)) * (1 + e))
Proof
  tac >> gen_tac >> strip_tac >> irule float_sqrt_relative >>
  simp[sqrtable_def] >>
  simp[fp16_to_float_def, binary_ieeeTheory.float_minus_zero_def,
      binary_ieeeTheory.float_negate_def, binary_ieeeTheory.float_plus_zero_def]
QED

Theorem fp16_float_add_relative =
  rule fp16_float_add_relative

Theorem fp16_float_sub_relative =
  rule fp16_float_sub_relative

Theorem fp16_float_mul_relative =
  rule fp16_float_mul_relative

Theorem fp16_float_mul_add_relative =
  rule fp16_float_mul_add_relative

Theorem fp16_float_mul_sub_relative =
  rule fp16_float_mul_sub_relative

Theorem fp16_float_div_relative =
  rule fp16_float_div_relative

Theorem fp16_float_sqrt_relative =
  rule fp16_float_sqrt_relative

(* --------------------------------------------------------------------- *)

Theorem fp32_float_add_relative[local]:
   !a b.
      fp32_isFinite a /\ fp32_isFinite b /\
      normalizes (:23 # 8) (fp32_to_real a + fp32_to_real b) ==>
      fp32_isFinite (fp32_add roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real (fp32_add roundTiesToEven a b) =
           (fp32_to_real a + fp32_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp32_float_sub_relative[local]:
   !a b.
      fp32_isFinite a /\ fp32_isFinite b /\
      normalizes (:23 # 8) (fp32_to_real a - fp32_to_real b) ==>
      fp32_isFinite (fp32_sub roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real (fp32_sub roundTiesToEven a b) =
           (fp32_to_real a - fp32_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp32_float_mul_relative[local]:
   !a b.
      fp32_isFinite a /\ fp32_isFinite b /\
      normalizes (:23 # 8) (fp32_to_real a * fp32_to_real b) ==>
      fp32_isFinite (fp32_mul roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real (fp32_mul roundTiesToEven a b) =
           (fp32_to_real a * fp32_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp32_float_mul_add_relative[local]:
   !a b c.
      fp32_isFinite a /\ fp32_isFinite b /\ fp32_isFinite c /\
      normalizes (:23 # 8)
       (fp32_to_real a * fp32_to_real b + fp32_to_real c) ==>
      fp32_isFinite (fp32_mul_add roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real (fp32_mul_add roundTiesToEven a b c) =
           (fp32_to_real a * fp32_to_real b +
            fp32_to_real c) * (1 + e))
Proof
  tac
QED

Theorem fp32_float_mul_sub_relative[local]:
   !a b c.
      fp32_isFinite a /\ fp32_isFinite b /\ fp32_isFinite c /\
      normalizes (:23 # 8)
       (fp32_to_real a * fp32_to_real b - fp32_to_real c) ==>
      fp32_isFinite (fp32_mul_sub roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real (fp32_mul_sub roundTiesToEven a b c) =
           (fp32_to_real a * fp32_to_real b -
            fp32_to_real c) * (1 + e))
Proof
  tac
QED

Theorem fp32_float_div_relative[local]:
   !a b.
      fp32_isFinite a /\ fp32_isFinite b /\ ~fp32_isZero b /\
      normalizes (:23 # 8) (fp32_to_real a / fp32_to_real b) ==>
      fp32_isFinite (fp32_div roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real (fp32_div roundTiesToEven a b) =
           (fp32_to_real a / fp32_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp32_float_sqrt_relative[local]:
   !a.
      fp32_isFinite a /\ (~word_msb a \/ a = INT_MINw) /\
      normalizes (:23 # 8) (sqrt (fp32_to_real a)) ==>
      fp32_isFinite (fp32_sqrt roundTiesToEven a) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real (fp32_sqrt roundTiesToEven a) =
           (sqrt (fp32_to_real a)) * (1 + e))
Proof
  tac >> gen_tac >> strip_tac >> irule float_sqrt_relative >>
  simp[sqrtable_def] >>
  simp[fp32_to_float_def, binary_ieeeTheory.float_minus_zero_def,
      binary_ieeeTheory.float_negate_def, binary_ieeeTheory.float_plus_zero_def]
QED

Theorem fp32_float_add_relative =
  rule fp32_float_add_relative

Theorem fp32_float_sub_relative =
  rule fp32_float_sub_relative

Theorem fp32_float_mul_relative =
  rule fp32_float_mul_relative

Theorem fp32_float_mul_add_relative =
  rule fp32_float_mul_add_relative

Theorem fp32_float_mul_sub_relative =
  rule fp32_float_mul_sub_relative

Theorem fp32_float_div_relative =
  rule fp32_float_div_relative

Theorem fp32_float_sqrt_relative =
  rule fp32_float_sqrt_relative

(* --------------------------------------------------------------------- *)

Theorem fp64_float_add_relative[local]:
   !a b.
      fp64_isFinite a /\ fp64_isFinite b /\
      normalizes (:52 # 11) (fp64_to_real a + fp64_to_real b) ==>
      fp64_isFinite (fp64_add roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real (fp64_add roundTiesToEven a b) =
           (fp64_to_real a + fp64_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp64_float_sub_relative[local]:
   !a b.
      fp64_isFinite a /\ fp64_isFinite b /\
      normalizes (:52 # 11) (fp64_to_real a - fp64_to_real b) ==>
      fp64_isFinite (fp64_sub roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real (fp64_sub roundTiesToEven a b) =
           (fp64_to_real a - fp64_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp64_float_mul_relative[local]:
   !a b.
      fp64_isFinite a /\ fp64_isFinite b /\
      normalizes (:52 # 11) (fp64_to_real a * fp64_to_real b) ==>
      fp64_isFinite (fp64_mul roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real (fp64_mul roundTiesToEven a b) =
           (fp64_to_real a * fp64_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp64_float_mul_add_relative[local]:
   !a b c.
      fp64_isFinite a /\ fp64_isFinite b /\ fp64_isFinite c /\
      normalizes (:52 # 11)
       (fp64_to_real a * fp64_to_real b + fp64_to_real c) ==>
      fp64_isFinite (fp64_mul_add roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real (fp64_mul_add roundTiesToEven a b c) =
           (fp64_to_real a * fp64_to_real b +
            fp64_to_real c) * (1 + e))
Proof
  tac
QED

Theorem fp64_float_mul_sub_relative[local]:
   !a b c.
      fp64_isFinite a /\ fp64_isFinite b /\ fp64_isFinite c /\
      normalizes (:52 # 11)
       (fp64_to_real a * fp64_to_real b - fp64_to_real c) ==>
      fp64_isFinite (fp64_mul_sub roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real (fp64_mul_sub roundTiesToEven a b c) =
           (fp64_to_real a * fp64_to_real b -
            fp64_to_real c) * (1 + e))
Proof
  tac
QED

Theorem fp64_float_div_relative[local]:
   !a b.
      fp64_isFinite a /\ fp64_isFinite b /\ ~fp64_isZero b /\
      normalizes (:52 # 11) (fp64_to_real a / fp64_to_real b) ==>
      fp64_isFinite (fp64_div roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real (fp64_div roundTiesToEven a b) =
           (fp64_to_real a / fp64_to_real b) * (1 + e))
Proof
  tac
QED

Theorem fp64_float_sqrt_relative[local]:
   !a.
      fp64_isFinite a /\ (~word_msb a \/ a = INT_MINw) /\
      normalizes (:52 # 11) (sqrt (fp64_to_real a)) ==>
      fp64_isFinite (fp64_sqrt roundTiesToEven a) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real (fp64_sqrt roundTiesToEven a) =
           (sqrt (fp64_to_real a)) * (1 + e))
Proof
  tac >> gen_tac >> strip_tac >> irule float_sqrt_relative >>
  simp[sqrtable_def] >>
  simp[fp64_to_float_def, binary_ieeeTheory.float_minus_zero_def,
       binary_ieeeTheory.float_negate_def,
       binary_ieeeTheory.float_plus_zero_def]
QED

Theorem fp64_float_add_relative =
  rule fp64_float_add_relative

Theorem fp64_float_sub_relative =
  rule fp64_float_sub_relative

Theorem fp64_float_mul_relative =
  rule fp64_float_mul_relative

Theorem fp64_float_mul_add_relative =
  rule fp64_float_mul_add_relative

Theorem fp64_float_mul_sub_relative =
  rule fp64_float_mul_sub_relative

Theorem fp64_float_div_relative =
  rule fp64_float_div_relative

Theorem fp64_float_sqrt_relative =
  rule fp64_float_sqrt_relative

(* --------------------------------------------------------------------- *)
