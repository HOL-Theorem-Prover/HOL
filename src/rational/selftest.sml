open testutils
open ratLib ratReduce

val _ = List.app convtest [
  ("RAT_MUL_CONV(01)", RAT_MUL_CONV, ``2q * 3``, ``6q``),
  ("RAT_MUL_CONV(02)", RAT_MUL_CONV, ``2q * -3``, ``-6q``),
  ("RAT_MUL_CONV(03)", RAT_MUL_CONV, ``-2q * 3``, ``-6q``),
  ("RAT_MUL_CONV(04)", RAT_MUL_CONV, ``-2q * -3``, ``6q``),
  ("RAT_MUL_CONV(05)", RAT_MUL_CONV, ``2q/3 * 10``, ``20q/3``),
  ("RAT_MUL_CONV(06)", RAT_MUL_CONV, ``2q/3 * -10``, ``-20q/3``),
  ("RAT_MUL_CONV(07)", RAT_MUL_CONV, ``2q/3 * 9``, ``6q``),
  ("RAT_MUL_CONV(08)", RAT_MUL_CONV, ``2q/3 * -9``, ``-6q``),
  ("RAT_MUL_CONV(09)", RAT_MUL_CONV, ``2q/3 * -9``, ``-6q``),
  ("RAT_MUL_CONV(10)", RAT_MUL_CONV, ``2q/3 * (3/4)``, ``1q/2``),
  ("RAT_MUL_CONV(11)", RAT_MUL_CONV, ``2q/-3 * (3/4)``, ``-1q/2``),
  ("RAT_MUL_CONV(12)", RAT_MUL_CONV, ``2q/-3 * 0``, ``0q``)
]
