open testutils

local open combinTheory in end

val EVAL = computeLib.CBV_CONV computeLib.the_compset

val _ = app convtest [
      ("EVAL K x o K y", EVAL,
       “(K (x:'a) : 'a -> 'a) o K (y:'a) : 'b -> 'a”, “K (x:'a) : 'b -> 'a”)
    ]

val _ = app tpp [
      "f⦇a ↦ b⦈",
      "f⦇a ↦ b⦈ x",
      "f⦇a ↦ b; c ↦ d⦈",
      "f⦇a ↦ b; c ↦ d⦈ x"
    ]
