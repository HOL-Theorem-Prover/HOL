open HolKernel boolLib testutils

open combinSyntax
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
  "f⦇a ↦ b; c ↦ d⦈ x",
  "g ∘ f⦇a ↦ c⦈",
  "(g ∘ f)⦇a ↦ c⦈",
  "f⦇\n\
  \  kkkk1 ↦ vvvvv1; kkkkk2 ↦ vvvvvv2; kkkkk3 ↦ vvvvv3; kkkkkk4 ↦ vvvvv4;\n\
  \  kkkkkk5 ↦ v5\n\
  \⦈",
  "g ∘\n\
  \f⦇\n\
  \  kkkk1 ↦ vvvvv1; kkkkk2 ↦ vvvvvv2; kkkkk3 ↦ vvvvv3; kkkkkk4 ↦ vvvvv4;\n\
  \  kkkkkk5 ↦ v5\n\
  \⦈",
  "(g ∘ f)⦇\n\
  \  kkkk1 ↦ vvvvv1; kkkkk2 ↦ vvvvvv2; kkkkk3 ↦ vvvvv3; kkkkkk4 ↦ vvvvv4;\n\
  \  kkkkkk5 ↦ v5\n\
  \⦈",
  "(fffff xxxxx yyyyy zzzzz aaaaaa bbbbbbb cccccccc dddddddd eeeeeeee ggggg)⦇\n\
  \  kkkkkkkkk ↦ vvvvvv\n\
  \⦈",
  "P\n\
  \  (fffff xxxxx yyyy zzzzz aaaaaa bbbbbbb cccccccc ddddddd eeeeeeee ggggg)⦇\n\
  \    kkkkkkkkk ↦ vvvvvv\n\
  \  ⦈"

];

local
val a = mk_var("a", alpha)
val f1 = mk_var("f1", alpha --> bool)
val b = mk_var("b", beta)
val baboolf = mk_var("g", beta --> (alpha --> bool))

val map1 = mk_comb(mk_update(a, T), f1)
val map2 = mk_comb(mk_update(b, map1), baboolf)
val s = "g⦇(b:'b) ↦ (f1:'a -> bool)⦇a ↦ T⦈ ⦈"
in
val _ = tprint ("Parsing nested updates: "^ s)
val _ = require_msg (check_result (aconv map2))
                    (trace ("types", 2) term_to_string)
                    Parse.Term
                    [QUOTE s]
end
