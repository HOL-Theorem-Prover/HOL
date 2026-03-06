Theory cpsExamples
Ancestors
  cps
Libs
  cpsLib

Theorem CPS_REVERSE =
kREVERSE_def |> SPEC_ALL
             |> SRULE [GSYM contify_cwc, Once REVERSE_EQN]
             |> CONV_RULE
                (TOP_DEPTH_CONV
                 (contify_CONV [contify_list_case]))
             |> SRULE [cwcp “APPEND”, cwcp “CONS”]
             |> SRULE [GSYM kREVERSE_def]
             |> SRULE [cwc_def]

Theorem REVERSEk_EQN =
        Q.SPECL [‘l’] kREVERSE_def
          |> INST_TYPE [alpha |-> “:'b list”]
          |> Q.SPEC ‘λx.x’
          |> SRULE [cwc_def]
          |> SYM

Datatype: rk = rkID | rkC 'a rk
End

Definition applyrk_def:
  applyrk rkID l = l /\
  applyrk (rkC a k) l = applyrk k (l ++ [a])
End



