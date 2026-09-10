open testutils

local open llistTheory pathTheory in end

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
      ("EVAL LTL LCONS", bossLib.EVAL, “LTL [|2;3|]”, “SOME [|3|]”),
      ("simplify path_case stopped_at",
       bossLib.SIMP_CONV (bossLib.srw_ss()) [],
       “path_case (stopped_at 3 : (num,bool) path) (\x. x + 1)
                  (\x r p. x)”, “4”),
      ("simplify path_case pcons", bossLib.SIMP_CONV (bossLib.srw_ss()) [],
       “path_case (pcons 3 T (stopped_at 4) : (num,bool) path) (\x. 0)
                  (\x r p. if r then x else 0)”, “3”),
      ("simplify path case syntax", bossLib.SIMP_CONV (bossLib.srw_ss()) [],
       “case (pcons 3 T (stopped_at 4) : (num,bool) path) of
          stopped_at x => 0
        | pcons x r p => x”, “3”)
   ]

val _ = tprint "path TypeBase registration"
val _ =
  if Term.same_const (TypeBase.case_const_of “:(num,bool) path”)
                     “path_case”
  then OK ()
  else die "path_case is not registered as the path case constant"
