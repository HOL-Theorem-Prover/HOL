open testutils
open ratLib ratReduce

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
