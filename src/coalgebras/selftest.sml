open testutils

local open llistTheory in end

val _ = app tpp [
      "[|1; 2; 3|]",
      "[|aaaa; bbbb; cccc; dddd; eeee; ffff; gggg; hhhh; iiii; jjjj; kkkk; \
        \llll; mmmm;\n\
      \  nnnn; oooo|]"
    ]

val _ = app convtest [
      ("EVAL LTL_HD", bossLib.EVAL, “LTL_HD [|3;4|]”, “SOME ([|4|], 3)”),
      ("EVAL LTL LNIL", bossLib.EVAL, “LTL ([||] : num llist)”,
       “NONE : num llist option”),
      ("EVAL LTL LCONS", bossLib.EVAL, “LTL [|2;3|]”, “SOME [|3|]”)
   ]
