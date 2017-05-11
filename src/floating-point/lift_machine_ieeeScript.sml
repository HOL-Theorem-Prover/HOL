open HolKernel Parse boolLib bossLib
open machine_ieeeTheory lift_ieeeTheory wordsLib;

val () = new_theory "lift_machine_ieee";

(* --------------------------------------------------------------------- *)

val interval_def = Define `interval a b = {x : real | a <= x /\ x < b}`

val () = ( Parse.add_infix ("..", 350, HOLgrammars.NONASSOC)
         ; Parse.overload_on ("..", ``interval``)
         )

val fp16_to_real_value_def = Define`
  fp16_to_real_value = float_to_real o fp16_to_float`

val fp32_to_real_value_def = Define`
  fp32_to_real_value = float_to_real o fp32_to_float`

val fp64_to_real_value_def = Define`
  fp64_to_real_value = float_to_real o fp64_to_float`

(* --------------------------------------------------------------------- *)

val rule =
  wordsLib.WORD_EVAL_RULE o
  REWRITE_RULE
    [normalizes_def, binary_ieeeTheory.threshold_def, realTheory.REAL_INV_1OVER,
     GSYM (SIMP_CONV (srw_ss()) [interval_def] ``a IN (x .. y)``)]

val word_msb16 = Q.prove(
  `!a: word16. ~word_msb a = ((fp16_to_float a).Sign = 0w)`,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [fp16_to_float_def])

val word_msb32 = Q.prove(
  `!a: word32. ~word_msb a = ((fp32_to_float a).Sign = 0w)`,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [fp32_to_float_def])

val word_msb64 = Q.prove(
  `!a: word64. ~word_msb a = ((fp64_to_float a).Sign = 0w)`,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [fp64_to_float_def])

val tac =
  simp_tac std_ss
     [fp16_to_real_value_def, fp16_isFinite_def, fp16_isZero_def, word_msb16,
      fp16_add_def, fp16_sub_def, fp16_mul_def, fp16_div_def, fp16_sqrt_def,
      fp16_mul_add_def, fp16_mul_sub_def, fp16_to_float_float_to_fp16,
      fp32_to_real_value_def, fp32_isFinite_def, fp32_isZero_def, word_msb32,
      fp32_add_def, fp32_sub_def, fp32_mul_def, fp32_div_def, fp32_sqrt_def,
      fp32_mul_add_def, fp32_mul_sub_def, fp32_to_float_float_to_fp32,
      fp64_to_real_value_def, fp64_isFinite_def,fp64_isZero_def, word_msb64,
      fp64_add_def, fp64_sub_def, fp64_mul_def, fp64_div_def, fp64_sqrt_def,
      fp64_mul_add_def, fp64_mul_sub_def, fp64_to_float_float_to_fp64,
      float_add_relative, float_sub_relative,
      float_mul_relative, float_div_relative,
      float_mul_add_relative, float_mul_sub_relative, float_sqrt_relative]

(* --------------------------------------------------------------------- *)

val fp16_float_add_relative = Q.prove(
  `!a b.
      fp16_isFinite a /\ fp16_isFinite b /\
      normalizes (:10 # 5) (fp16_to_real_value a + fp16_to_real_value b) ==>
      fp16_isFinite (fp16_add roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real_value (fp16_add roundTiesToEven a b) =
           (fp16_to_real_value a + fp16_to_real_value b) * (1 + e))`,
  tac
  )

val fp16_float_sub_relative = Q.prove(
  `!a b.
      fp16_isFinite a /\ fp16_isFinite b /\
      normalizes (:10 # 5) (fp16_to_real_value a - fp16_to_real_value b) ==>
      fp16_isFinite (fp16_sub roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real_value (fp16_sub roundTiesToEven a b) =
           (fp16_to_real_value a - fp16_to_real_value b) * (1 + e))`,
  tac
  )

val fp16_float_mul_relative = Q.prove(
  `!a b.
      fp16_isFinite a /\ fp16_isFinite b /\
      normalizes (:10 # 5) (fp16_to_real_value a * fp16_to_real_value b) ==>
      fp16_isFinite (fp16_mul roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real_value (fp16_mul roundTiesToEven a b) =
           (fp16_to_real_value a * fp16_to_real_value b) * (1 + e))`,
  tac
  )

val fp16_float_mul_add_relative = Q.prove(
  `!a b c.
      fp16_isFinite a /\ fp16_isFinite b /\ fp16_isFinite c /\
      normalizes (:10 # 5)
       (fp16_to_real_value a * fp16_to_real_value b + fp16_to_real_value c) ==>
      fp16_isFinite (fp16_mul_add roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real_value (fp16_mul_add roundTiesToEven a b c) =
           (fp16_to_real_value a * fp16_to_real_value b +
            fp16_to_real_value c) * (1 + e))`,
  tac
  )

val fp16_float_mul_sub_relative = Q.prove(
  `!a b c.
      fp16_isFinite a /\ fp16_isFinite b /\ fp16_isFinite c /\
      normalizes (:10 # 5)
       (fp16_to_real_value a * fp16_to_real_value b - fp16_to_real_value c) ==>
      fp16_isFinite (fp16_mul_sub roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real_value (fp16_mul_sub roundTiesToEven a b c) =
           (fp16_to_real_value a * fp16_to_real_value b -
            fp16_to_real_value c) * (1 + e))`,
  tac
  )

val fp16_float_div_relative = Q.prove(
  `!a b.
      fp16_isFinite a /\ fp16_isFinite b /\ ~fp16_isZero b /\
      normalizes (:10 # 5) (fp16_to_real_value a / fp16_to_real_value b) ==>
      fp16_isFinite (fp16_div roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real_value (fp16_div roundTiesToEven a b) =
           (fp16_to_real_value a / fp16_to_real_value b) * (1 + e))`,
  tac
  )

val fp16_float_sqrt_relative = Q.prove(
  `!a.
      fp16_isFinite a /\ ~word_msb a /\
      normalizes (:10 # 5) (sqrt (fp16_to_real_value a)) ==>
      fp16_isFinite (fp16_sqrt roundTiesToEven a) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:10) + 1) /\
          (fp16_to_real_value (fp16_sqrt roundTiesToEven a) =
           (sqrt (fp16_to_real_value a)) * (1 + e))`,
  tac
  )

val fp16_float_add_relative = save_thm("fp16_float_add_relative",
  rule fp16_float_add_relative)

val fp16_float_sub_relative = save_thm("fp16_float_sub_relative",
  rule fp16_float_sub_relative)

val fp16_float_mul_relative = save_thm("fp16_float_mul_relative",
  rule fp16_float_mul_relative)

val fp16_float_mul_add_relative = save_thm("fp16_float_mul_add_relative",
  rule fp16_float_mul_add_relative)

val fp16_float_mul_sub_relative = save_thm("fp16_float_mul_sub_relative",
  rule fp16_float_mul_sub_relative)

val fp16_float_div_relative = save_thm("fp16_float_div_relative",
  rule fp16_float_div_relative)

val fp16_float_sqrt_relative = save_thm("fp16_float_sqrt_relative",
  rule fp16_float_sqrt_relative)

(* --------------------------------------------------------------------- *)

val fp32_float_add_relative = Q.prove(
  `!a b.
      fp32_isFinite a /\ fp32_isFinite b /\
      normalizes (:23 # 8) (fp32_to_real_value a + fp32_to_real_value b) ==>
      fp32_isFinite (fp32_add roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real_value (fp32_add roundTiesToEven a b) =
           (fp32_to_real_value a + fp32_to_real_value b) * (1 + e))`,
  tac
  )

val fp32_float_sub_relative = Q.prove(
  `!a b.
      fp32_isFinite a /\ fp32_isFinite b /\
      normalizes (:23 # 8) (fp32_to_real_value a - fp32_to_real_value b) ==>
      fp32_isFinite (fp32_sub roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real_value (fp32_sub roundTiesToEven a b) =
           (fp32_to_real_value a - fp32_to_real_value b) * (1 + e))`,
  tac
  )

val fp32_float_mul_relative = Q.prove(
  `!a b.
      fp32_isFinite a /\ fp32_isFinite b /\
      normalizes (:23 # 8) (fp32_to_real_value a * fp32_to_real_value b) ==>
      fp32_isFinite (fp32_mul roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real_value (fp32_mul roundTiesToEven a b) =
           (fp32_to_real_value a * fp32_to_real_value b) * (1 + e))`,
  tac
  )

val fp32_float_mul_add_relative = Q.prove(
  `!a b c.
      fp32_isFinite a /\ fp32_isFinite b /\ fp32_isFinite c /\
      normalizes (:23 # 8)
       (fp32_to_real_value a * fp32_to_real_value b + fp32_to_real_value c) ==>
      fp32_isFinite (fp32_mul_add roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real_value (fp32_mul_add roundTiesToEven a b c) =
           (fp32_to_real_value a * fp32_to_real_value b +
            fp32_to_real_value c) * (1 + e))`,
  tac
  )

val fp32_float_mul_sub_relative = Q.prove(
  `!a b c.
      fp32_isFinite a /\ fp32_isFinite b /\ fp32_isFinite c /\
      normalizes (:23 # 8)
       (fp32_to_real_value a * fp32_to_real_value b - fp32_to_real_value c) ==>
      fp32_isFinite (fp32_mul_sub roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real_value (fp32_mul_sub roundTiesToEven a b c) =
           (fp32_to_real_value a * fp32_to_real_value b -
            fp32_to_real_value c) * (1 + e))`,
  tac
  )

val fp32_float_div_relative = Q.prove(
  `!a b.
      fp32_isFinite a /\ fp32_isFinite b /\ ~fp32_isZero b /\
      normalizes (:23 # 8) (fp32_to_real_value a / fp32_to_real_value b) ==>
      fp32_isFinite (fp32_div roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real_value (fp32_div roundTiesToEven a b) =
           (fp32_to_real_value a / fp32_to_real_value b) * (1 + e))`,
  tac
  )

val fp32_float_sqrt_relative = Q.prove(
  `!a.
      fp32_isFinite a /\ ~word_msb a /\
      normalizes (:23 # 8) (sqrt (fp32_to_real_value a)) ==>
      fp32_isFinite (fp32_sqrt roundTiesToEven a) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:23) + 1) /\
          (fp32_to_real_value (fp32_sqrt roundTiesToEven a) =
           (sqrt (fp32_to_real_value a)) * (1 + e))`,
  tac
  )

val fp32_float_add_relative = save_thm("fp32_float_add_relative",
  rule fp32_float_add_relative)

val fp32_float_sub_relative = save_thm("fp32_float_sub_relative",
  rule fp32_float_sub_relative)

val fp32_float_mul_relative = save_thm("fp32_float_mul_relative",
  rule fp32_float_mul_relative)

val fp32_float_mul_add_relative = save_thm("fp32_float_mul_add_relative",
  rule fp32_float_mul_add_relative)

val fp32_float_mul_sub_relative = save_thm("fp32_float_mul_sub_relative",
  rule fp32_float_mul_sub_relative)

val fp32_float_div_relative = save_thm("fp32_float_div_relative",
  rule fp32_float_div_relative)

val fp32_float_sqrt_relative = save_thm("fp32_float_sqrt_relative",
  rule fp32_float_sqrt_relative)

(* --------------------------------------------------------------------- *)

val fp64_float_add_relative = Q.prove(
  `!a b.
      fp64_isFinite a /\ fp64_isFinite b /\
      normalizes (:52 # 11) (fp64_to_real_value a + fp64_to_real_value b) ==>
      fp64_isFinite (fp64_add roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real_value (fp64_add roundTiesToEven a b) =
           (fp64_to_real_value a + fp64_to_real_value b) * (1 + e))`,
  tac
  )

val fp64_float_sub_relative = Q.prove(
  `!a b.
      fp64_isFinite a /\ fp64_isFinite b /\
      normalizes (:52 # 11) (fp64_to_real_value a - fp64_to_real_value b) ==>
      fp64_isFinite (fp64_sub roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real_value (fp64_sub roundTiesToEven a b) =
           (fp64_to_real_value a - fp64_to_real_value b) * (1 + e))`,
  tac
  )

val fp64_float_mul_relative = Q.prove(
  `!a b.
      fp64_isFinite a /\ fp64_isFinite b /\
      normalizes (:52 # 11) (fp64_to_real_value a * fp64_to_real_value b) ==>
      fp64_isFinite (fp64_mul roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real_value (fp64_mul roundTiesToEven a b) =
           (fp64_to_real_value a * fp64_to_real_value b) * (1 + e))`,
  tac
  )

val fp64_float_mul_add_relative = Q.prove(
  `!a b c.
      fp64_isFinite a /\ fp64_isFinite b /\ fp64_isFinite c /\
      normalizes (:52 # 11)
       (fp64_to_real_value a * fp64_to_real_value b + fp64_to_real_value c) ==>
      fp64_isFinite (fp64_mul_add roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real_value (fp64_mul_add roundTiesToEven a b c) =
           (fp64_to_real_value a * fp64_to_real_value b +
            fp64_to_real_value c) * (1 + e))`,
  tac
  )

val fp64_float_mul_sub_relative = Q.prove(
  `!a b c.
      fp64_isFinite a /\ fp64_isFinite b /\ fp64_isFinite c /\
      normalizes (:52 # 11)
       (fp64_to_real_value a * fp64_to_real_value b - fp64_to_real_value c) ==>
      fp64_isFinite (fp64_mul_sub roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real_value (fp64_mul_sub roundTiesToEven a b c) =
           (fp64_to_real_value a * fp64_to_real_value b -
            fp64_to_real_value c) * (1 + e))`,
  tac
  )

val fp64_float_div_relative = Q.prove(
  `!a b.
      fp64_isFinite a /\ fp64_isFinite b /\ ~fp64_isZero b /\
      normalizes (:52 # 11) (fp64_to_real_value a / fp64_to_real_value b) ==>
      fp64_isFinite (fp64_div roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real_value (fp64_div roundTiesToEven a b) =
           (fp64_to_real_value a / fp64_to_real_value b) * (1 + e))`,
  tac
  )

val fp64_float_sqrt_relative = Q.prove(
  `!a.
      fp64_isFinite a /\ ~word_msb a /\
      normalizes (:52 # 11) (sqrt (fp64_to_real_value a)) ==>
      fp64_isFinite (fp64_sqrt roundTiesToEven a) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:52) + 1) /\
          (fp64_to_real_value (fp64_sqrt roundTiesToEven a) =
           (sqrt (fp64_to_real_value a)) * (1 + e))`,
  tac
  )

val fp64_float_add_relative = save_thm("fp64_float_add_relative",
  rule fp64_float_add_relative)

val fp64_float_sub_relative = save_thm("fp64_float_sub_relative",
  rule fp64_float_sub_relative)

val fp64_float_mul_relative = save_thm("fp64_float_mul_relative",
  rule fp64_float_mul_relative)

val fp64_float_mul_add_relative = save_thm("fp64_float_mul_add_relative",
  rule fp64_float_mul_add_relative)

val fp64_float_mul_sub_relative = save_thm("fp64_float_mul_sub_relative",
  rule fp64_float_mul_sub_relative)

val fp64_float_div_relative = save_thm("fp64_float_div_relative",
  rule fp64_float_div_relative)

val fp64_float_sqrt_relative = save_thm("fp64_float_sqrt_relative",
  rule fp64_float_sqrt_relative)

(* --------------------------------------------------------------------- *)

val () = export_theory ()
