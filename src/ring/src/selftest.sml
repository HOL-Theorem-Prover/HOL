open testutils

open EVAL_numRingLib

fun ntest (i,out) =
  convtest ("NUM_NORM_CONV " ^ Parse.term_to_string i, NUM_NORM_CONV, i, out)

val _ = List.app ntest [
      (``2n * x + y + x``, ``3n * x + y``),
      (``10 + 3n * (x + 2 * y) + z``, ``10 + (3n * x + (6 * y + z))``)
    ]

fun rtest (i,b) =
  convtest ("NUM_RING_CONV " ^ Parse.term_to_string i, NUM_RING_CONV, i,
            if b then boolSyntax.T else boolSyntax.F)

val _ = List.app rtest [
      (``x + y + x = y + 2n * x``, true)
    ]
