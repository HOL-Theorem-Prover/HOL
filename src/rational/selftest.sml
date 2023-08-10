open HolKernel Parse bossLib boolLib;

open ratLib ratReduce ratRingLib;

open testutils;

fun mkt s c (t1, t2) i =
  (s ^ "(" ^ StringCvt.padLeft #"0" 2 (Int.toString i) ^ ")", c, t1, t2)

val rmc = mkt "RAT_MUL_CONV" RAT_MUL_CONV
val rac = mkt "RAT_ADD_CONV" RAT_ADD_CONV

val _ = Lib.appi (fn i => fn p => convtest (rmc p i)) [
  (“2q * 3”,        “6q”),
  (“2q * -3”,       “-6q”),
  (“-2q * 3”,       “-6q”),
  (“-2q * -3”,      “6q”),
  (“2q/3 * 10”,     “20q/3”),
  (“2q/3 * -10”,    “-20q/3”),
  (“2q/3 * 9”,      “6q”),
  (“2q/3 * -9”,     “-6q”),
  (“2q/3 * -9”,     “-6q”),
  (“2q/3 * (3/4)”,  “1q/2”),
  (“2q/-3 * (3/4)”, “-1q/2”),
  (“2q/-3 * 0”,     “0q”)
]

val _ = Lib.appi (fn i => fn p => convtest (rac p i)) [
  (“1q + 2”,       “3q”),
  (“1q + -2”,      “-1q”),
  (“-1q + 2”,      “1q”),
  (“-1q + -2”,      “-3q”),
  (“1q + 2/3”,     “5/3q”),
  (“1q + -2/3”,    “1/3q”),
  (“-1q + 2/3”,    “-1/3q”),
  (“-1q + -2/3”,    “-5/3q”),
  (“2/3q + 4”,     “14/3q”),
  (“2/3q + -4/6”,  “0q”)
]

(* check prefer/deprecate rat *)
val grammars = (type_grammar(),term_grammar());

val _ = ratLib.prefer_rat();
val _ = tprint "Checking parse of 0 < x gives rats when rats are preferred";
val expected1 = ratSyntax.mk_rat_les(ratSyntax.rat_0_tm,
                                     mk_var("x", ratSyntax.rat_ty));

val _ = require_msg (check_result (aconv expected1)) term_to_string
                    (quietly Parse.Term) ‘0 < x’

(* val _ = temp_set_grammars grammars *)

val _ = ratLib.deprecate_rat();
val _ = tprint "Checking parse of 0 < x gives ints when rats deprecated"

val expected2 = intSyntax.mk_less(intSyntax.zero_tm,
                                  mk_var("x", intSyntax.int_ty))
val _ = require_msg (check_result (aconv expected2)) term_to_string
                    (quietly Parse.Term) ‘0 < x’

val _ = intLib.deprecate_int();
val _ = tprint "Checking parse of 0 < x gives nats when ints deprecated too"

val expected3 = numSyntax.mk_less(numSyntax.zero_tm,
                                  mk_var("x", numSyntax.num))

val _ = require_msg (check_result (aconv expected3)) term_to_string
                    (quietly Parse.Term) ‘0 < x’

val _ = temp_set_grammars grammars;

(* check ring norm code *)
val _ = convtest ("RAT_RING_NORM_CONV (01)",
                  RAT_RING_NORM_CONV,
                  “2q * q + 3 * r - 6 * q”, “-4q * q + 3 * r”);
val _ = convtest ("RAT_RING_NORM_CONV (02)",
                  RAT_RING_NORM_CONV,
                  “2q * q + 3 * r - 2 * q”, “3 * r”);
val _ = convtest ("RAT_RING_NORM_CONV (03)",
                  RAT_RING_NORM_CONV,
                  “-2 * r + 2q * q + 3 * r - 2 * q - r ”, “0q”);
val _ = convtest ("RAT_RING_NORM_CONV (04)",
                  RAT_RING_NORM_CONV,
                  “(r:rat) * 1 + 3 * r”, “4q * r”);

val _ = Process.exit Process.success
