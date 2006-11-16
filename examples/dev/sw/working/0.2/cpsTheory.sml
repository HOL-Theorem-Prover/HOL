structure cpsTheory :> cpsTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading cpsTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open listTheory
  in end;
  val _ = Theory.link_parents
          ("cps",Arbnum.fromString "1162365431",Arbnum.fromString "585853")
          [("list",
           Arbnum.fromString "1157050827",
           Arbnum.fromString "489338")];
  val _ = Theory.incorporate_types "cps" [];
  val _ = Theory.incorporate_consts "cps"
     [("CPS2",
       (((beta --> bool) -->
         ((bool --> alpha) --> ((bool --> alpha) --> (beta --> alpha)))))),
      ("Seq",
       (((alpha --> beta) --> ((beta --> gamma) --> (alpha --> gamma))))),
      ("Rec",
       (((alpha --> bool) -->
         ((alpha --> beta) -->
          ((alpha --> alpha) --> (alpha --> beta)))))),
      ("Par",
       (((alpha --> beta) -->
         ((alpha --> gamma) -->
          (alpha --> T"prod" "pair" [beta, gamma]))))),
      ("Ite",
       (((alpha --> bool) -->
         ((alpha --> beta) --> ((alpha --> beta) --> (alpha --> beta)))))),
      ("CPS_SEQ",
       ((((delta --> U"'e") --> (beta --> gamma)) -->
         ((alpha --> (delta --> U"'e")) -->
          (alpha --> (beta --> gamma)))))),
      ("CPS_REC",
       ((((delta --> delta) --> (gamma --> bool)) -->
         (((U"'e" --> U"'e") --> (gamma --> alpha)) -->
          (((U"'f" --> U"'f") --> (gamma --> gamma)) -->
           ((alpha --> beta) --> (gamma --> beta))))))),
      ("CPS_PAR",
       ((((alpha --> U"'f") --> (delta --> U"'e")) -->
         (((beta --> gamma) --> (delta --> U"'f")) -->
          ((T"prod" "pair" [alpha, beta] --> gamma) -->
           (delta --> U"'e")))))),
      ("CPS",
       (((gamma --> alpha) --> ((alpha --> beta) --> (gamma --> beta))))),
      ("CPS_ITE",
       ((((bool --> delta) --> (beta --> gamma)) -->
         ((alpha --> (beta --> delta)) -->
          ((alpha --> (beta --> delta)) -->
           (alpha --> (beta --> gamma)))))))];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool" ((((alpha --> beta) --> bool) --> bool)),
   V"f1" ((alpha --> beta)),
   C"!" "bool" ((((beta --> gamma) --> bool) --> bool)),
   V"f2" ((beta --> gamma)),
   C"=" "min" (((alpha --> gamma) --> ((alpha --> gamma) --> bool))),
   C"Seq" "cps"
    (((alpha --> beta) --> ((beta --> gamma) --> (alpha --> gamma)))),
   V"x" (alpha), C"!" "bool" ((((alpha --> gamma) --> bool) --> bool)),
   V"f2" ((alpha --> gamma)),
   C"=" "min"
    (((alpha --> T"prod" "pair" [beta, gamma]) -->
      ((alpha --> T"prod" "pair" [beta, gamma]) --> bool))),
   C"Par" "cps"
    (((alpha --> beta) -->
      ((alpha --> gamma) --> (alpha --> T"prod" "pair" [beta, gamma])))),
   C"," "pair" ((beta --> (gamma --> T"prod" "pair" [beta, gamma]))),
   C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"f1" ((alpha --> bool)), V"f2" ((alpha --> beta)),
   V"f3" ((alpha --> beta)),
   C"=" "min" (((alpha --> beta) --> ((alpha --> beta) --> bool))),
   C"Ite" "cps"
    (((alpha --> bool) -->
      ((alpha --> beta) --> ((alpha --> beta) --> (alpha --> beta))))),
   C"COND" "bool" ((bool --> (beta --> (beta --> beta)))),
   C"!" "bool" ((((alpha --> alpha) --> bool) --> bool)),
   V"f3" ((alpha --> alpha)),
   C"Rec" "cps"
    (((alpha --> bool) -->
      ((alpha --> beta) --> ((alpha --> alpha) --> (alpha --> beta))))),
   C"WFREC" "relation"
    (((alpha --> (alpha --> bool)) -->
      (((alpha --> beta) --> (alpha --> beta)) --> (alpha --> beta)))),
   C"@" "min"
    ((((alpha --> (alpha --> bool)) --> bool) -->
      (alpha --> (alpha --> bool)))), V"R" ((alpha --> (alpha --> bool))),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"WF" "relation" (((alpha --> (alpha --> bool)) --> bool)),
   C"!" "bool" (((alpha --> bool) --> bool)),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"~" "bool" ((bool --> bool)), V"Rec" ((alpha --> beta)), V"a" (alpha),
   C"I" "combin" ((beta --> beta)),
   C"!" "bool" ((((gamma --> alpha) --> bool) --> bool)),
   V"f" ((gamma --> alpha)),
   C"=" "min"
    ((((alpha --> beta) --> (gamma --> beta)) -->
      (((alpha --> beta) --> (gamma --> beta)) --> bool))),
   C"CPS" "cps"
    (((gamma --> alpha) --> ((alpha --> beta) --> (gamma --> beta)))),
   V"k" ((alpha --> beta)), V"arg" (gamma),
   C"!" "bool" ((((beta --> bool) --> bool) --> bool)),
   V"f" ((beta --> bool)),
   C"=" "min"
    ((((bool --> alpha) --> ((bool --> alpha) --> (beta --> alpha))) -->
      (((bool --> alpha) --> ((bool --> alpha) --> (beta --> alpha))) -->
       bool))),
   C"CPS2" "cps"
    (((beta --> bool) -->
      ((bool --> alpha) --> ((bool --> alpha) --> (beta --> alpha))))),
   V"k1" ((bool --> alpha)), V"k2" ((bool --> alpha)), V"arg" (beta),
   C"COND" "bool" ((bool --> (alpha --> (alpha --> alpha)))),
   C"T" "bool" (bool), C"F" "bool" (bool),
   C"!" "bool"
    (((((delta --> U"'e") --> (beta --> gamma)) --> bool) --> bool)),
   V"f" (((delta --> U"'e") --> (beta --> gamma))),
   C"!" "bool" ((((alpha --> (delta --> U"'e")) --> bool) --> bool)),
   V"g" ((alpha --> (delta --> U"'e"))),
   C"=" "min"
    (((alpha --> (beta --> gamma)) -->
      ((alpha --> (beta --> gamma)) --> bool))),
   C"CPS_SEQ" "cps"
    ((((delta --> U"'e") --> (beta --> gamma)) -->
      ((alpha --> (delta --> U"'e")) --> (alpha --> (beta --> gamma))))),
   V"k" (alpha), V"ret" (delta),
   C"!" "bool"
    (((((alpha --> U"'f") --> (delta --> U"'e")) --> bool) --> bool)),
   V"f" (((alpha --> U"'f") --> (delta --> U"'e"))),
   C"!" "bool"
    (((((beta --> gamma) --> (delta --> U"'f")) --> bool) --> bool)),
   V"g" (((beta --> gamma) --> (delta --> U"'f"))),
   C"=" "min"
    ((((T"prod" "pair" [alpha, beta] --> gamma) --> (delta --> U"'e")) -->
      (((T"prod" "pair" [alpha, beta] --> gamma) --> (delta --> U"'e")) -->
       bool))),
   C"CPS_PAR" "cps"
    ((((alpha --> U"'f") --> (delta --> U"'e")) -->
      (((beta --> gamma) --> (delta --> U"'f")) -->
       ((T"prod" "pair" [alpha, beta] --> gamma) --> (delta --> U"'e"))))),
   V"k" ((T"prod" "pair" [alpha, beta] --> gamma)), V"arg" (delta),
   V"ret2" (alpha), V"ret" (beta),
   C"," "pair" ((alpha --> (beta --> T"prod" "pair" [alpha, beta]))),
   C"!" "bool"
    (((((bool --> delta) --> (beta --> gamma)) --> bool) --> bool)),
   V"e" (((bool --> delta) --> (beta --> gamma))),
   C"!" "bool" ((((alpha --> (beta --> delta)) --> bool) --> bool)),
   V"f" ((alpha --> (beta --> delta))),
   V"g" ((alpha --> (beta --> delta))),
   C"CPS_ITE" "cps"
    ((((bool --> delta) --> (beta --> gamma)) -->
      ((alpha --> (beta --> delta)) -->
       ((alpha --> (beta --> delta)) --> (alpha --> (beta --> gamma)))))),
   V"ret" (bool),
   C"LET" "bool" (((alpha --> delta) --> (alpha --> delta))),
   V"k2" (alpha),
   C"COND" "bool" ((bool --> (delta --> (delta --> delta)))),
   C"!" "bool"
    (((((delta --> delta) --> (gamma --> bool)) --> bool) --> bool)),
   V"e" (((delta --> delta) --> (gamma --> bool))),
   C"!" "bool"
    (((((U"'e" --> U"'e") --> (gamma --> alpha)) --> bool) --> bool)),
   V"f" (((U"'e" --> U"'e") --> (gamma --> alpha))),
   C"!" "bool"
    (((((U"'f" --> U"'f") --> (gamma --> gamma)) --> bool) --> bool)),
   V"g" (((U"'f" --> U"'f") --> (gamma --> gamma))),
   C"CPS_REC" "cps"
    ((((delta --> delta) --> (gamma --> bool)) -->
      (((U"'e" --> U"'e") --> (gamma --> alpha)) -->
       (((U"'f" --> U"'f") --> (gamma --> gamma)) -->
        ((alpha --> beta) --> (gamma --> beta)))))),
   C"Rec" "cps"
    (((gamma --> bool) -->
      ((gamma --> alpha) --> ((gamma --> gamma) --> (gamma --> alpha))))),
   V"x" (delta), V"x" (U"'e"), V"x" (U"'f"), V"P" ((alpha --> bool)),
   V"v" (alpha), C"=" "min" ((beta --> (beta --> bool))),
   C"=" "min"
    ((((alpha --> beta) --> (alpha --> beta)) -->
      (((alpha --> beta) --> (alpha --> beta)) --> bool))),
   C"CPS" "cps"
    (((alpha --> alpha) --> ((alpha --> beta) --> (alpha --> beta)))),
   V"x" (gamma), V"c" (alpha),
   C"CPS" "cps"
    (((alpha --> gamma) --> ((gamma --> beta) --> (alpha --> beta)))),
   V"f" ((alpha --> gamma)), V"k" ((gamma --> beta)), V"arg" (alpha),
   C"LET" "bool" (((gamma --> beta) --> (gamma --> beta))), V"z" (gamma),
   C"!" "bool"
    (((((alpha --> alpha) --> (beta --> alpha)) --> bool) --> bool)),
   V"f" (((alpha --> alpha) --> (beta --> alpha))),
   C"!" "bool" ((((beta --> alpha) --> bool) --> bool)),
   V"g" ((beta --> alpha)),
   C"=" "min"
    ((((alpha --> alpha) --> (beta --> alpha)) -->
      (((alpha --> alpha) --> (beta --> alpha)) --> bool))),
   C"CPS" "cps"
    (((beta --> alpha) --> ((alpha --> alpha) --> (beta --> alpha)))),
   C"!" "bool" ((((gamma --> delta) --> bool) --> bool)),
   V"f" ((gamma --> delta)), C"=" "min" ((delta --> (delta --> bool))),
   C"CPS" "cps"
    (((gamma --> delta) --> ((delta --> delta) --> (gamma --> delta)))),
   C"!" "bool"
    (((((bool --> bool) --> ((bool --> bool) --> (alpha --> bool))) -->
       bool) --> bool)),
   V"f" (((bool --> bool) --> ((bool --> bool) --> (alpha --> bool)))),
   C"?" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"f'" ((alpha --> bool)),
   C"=" "min"
    ((((bool --> bool) --> ((bool --> bool) --> (alpha --> bool))) -->
      (((bool --> bool) --> ((bool --> bool) --> (alpha --> bool))) -->
       bool))),
   C"CPS2" "cps"
    (((alpha --> bool) -->
      ((bool --> bool) --> ((bool --> bool) --> (alpha --> bool))))),
   V"x" (bool), C"=" "min" ((bool --> (bool --> bool))),
   C"CPS2" "cps"
    (((beta --> bool) -->
      ((bool --> bool) --> ((bool --> bool) --> (beta --> bool))))),
   V"f" ((alpha --> beta)), V"g" ((beta --> gamma)),
   C"=" "min"
    ((((gamma --> delta) --> (alpha --> delta)) -->
      (((gamma --> delta) --> (alpha --> delta)) --> bool))),
   C"CPS" "cps"
    (((alpha --> gamma) --> ((gamma --> delta) --> (alpha --> delta)))),
   C"CPS_SEQ" "cps"
    ((((beta --> delta) --> (alpha --> delta)) -->
      (((gamma --> delta) --> (beta --> delta)) -->
       ((gamma --> delta) --> (alpha --> delta))))),
   C"CPS" "cps"
    (((alpha --> beta) --> ((beta --> delta) --> (alpha --> delta)))),
   C"CPS" "cps"
    (((beta --> gamma) --> ((gamma --> delta) --> (beta --> delta)))),
   V"g" ((alpha --> gamma)),
   C"=" "min"
    ((((T"prod" "pair" [beta, gamma] --> delta) --> (alpha --> delta)) -->
      (((T"prod" "pair" [beta, gamma] --> delta) --> (alpha --> delta)) -->
       bool))),
   C"CPS" "cps"
    (((alpha --> T"prod" "pair" [beta, gamma]) -->
      ((T"prod" "pair" [beta, gamma] --> delta) --> (alpha --> delta)))),
   C"CPS_PAR" "cps"
    ((((beta --> delta) --> (alpha --> delta)) -->
      (((gamma --> delta) --> (alpha --> delta)) -->
       ((T"prod" "pair" [beta, gamma] --> delta) --> (alpha --> delta))))),
   V"e" ((alpha --> bool)), V"g" ((alpha --> beta)),
   C"=" "min"
    ((((beta --> gamma) --> (alpha --> gamma)) -->
      (((beta --> gamma) --> (alpha --> gamma)) --> bool))),
   C"CPS" "cps"
    (((alpha --> beta) --> ((beta --> gamma) --> (alpha --> gamma)))),
   C"CPS_ITE" "cps"
    ((((bool --> gamma) --> (alpha --> gamma)) -->
      (((beta --> gamma) --> (alpha --> gamma)) -->
       (((beta --> gamma) --> (alpha --> gamma)) -->
        ((beta --> gamma) --> (alpha --> gamma)))))),
   C"CPS" "cps"
    (((alpha --> bool) --> ((bool --> gamma) --> (alpha --> gamma)))),
   V"g" ((alpha --> alpha)),
   C"CPS_REC" "cps"
    ((((bool --> bool) --> (alpha --> bool)) -->
      (((beta --> beta) --> (alpha --> beta)) -->
       (((alpha --> alpha) --> (alpha --> alpha)) -->
        ((beta --> gamma) --> (alpha --> gamma)))))),
   C"CPS" "cps"
    (((alpha --> bool) --> ((bool --> bool) --> (alpha --> bool)))),
   C"CPS" "cps"
    (((alpha --> beta) --> ((beta --> beta) --> (alpha --> beta)))),
   C"CPS" "cps"
    (((alpha --> alpha) --> ((alpha --> alpha) --> (alpha --> alpha)))),
   C"?" "bool" ((((alpha --> (alpha --> bool)) --> bool) --> bool)),
   C"!" "bool" (((gamma --> bool) --> bool)), V"M" (gamma),
   V"N" ((gamma --> alpha)),
   C"LET" "bool" (((gamma --> alpha) --> (gamma --> alpha))), V"M" (alpha),
   C"LET" "bool"
    ((((alpha --> beta) --> beta) --> ((alpha --> beta) --> beta)))]
  val DT = Thm.disk_thm share_table
  in
  val Seq_def =
    DT([], [],
       `(%0 (\%1. (%2 (\%3. ((%4 ((%5 $1) $0)) (\%6. ($1 ($2 $0))))))))`)
  val Par_def =
    DT([], [],
       `(%0 (\%1. (%7 (\%8. ((%9 ((%10 $1) $0)) (\%6. ((%11 ($2 $0)) ($1
       $0))))))))`)
  val Ite_def =
    DT([], [],
       `(%12 (\%13. (%0 (\%14. (%0 (\%15. ((%16 (((%17 $2) $1) $0)) (\%6.
       (((%18 ($3 $0)) ($2 $0)) ($1 $0))))))))))`)
  val Rec_primitive_def =
    DT([], [],
       `(%12 (\%13. (%0 (\%14. (%19 (\%20. ((%16 (((%21 $2) $1) $0)) ((%22
       (%23 (\%24. ((%25 (%26 $0)) (%27 (\%6. ((%28 (%29 ($4 $0))) (($1 ($2
       $0)) $0)))))))) (\%30. (\%31. (%32 (((%18 ($4 $0)) ($3 $0)) ($1 ($2
       $0))))))))))))))`)
  val CPS_def =
    DT([], [],
       `(%33 (\%34. ((%35 (%36 $0)) (\%37. (\%38. ($1 ($2 $0)))))))`)
  val CPS2_def =
    DT([], [],
       `(%39 (\%40. ((%41 (%42 $0)) (\%43. (\%44. (\%45. (((%46 ($3 $0))
       ($2 %47)) ($1 %48))))))))`)
  val CPS_SEQ_def =
    DT([], [],
       `(%49 (\%50. (%51 (\%52. ((%53 ((%54 $1) $0)) (\%55. (\%45. (($3
       (\%56. (($3 $2) $0))) $0))))))))`)
  val CPS_PAR_def =
    DT([], [],
       `(%57 (\%58. (%59 (\%60. ((%61 ((%62 $1) $0)) (\%63. (\%64. (($3
       (\%65. (($3 (\%66. ($3 ((%67 $1) $0)))) $1))) $0))))))))`)
  val CPS_ITE_def =
    DT([], [],
       `(%68 (\%69. (%70 (\%71. (%70 (\%72. ((%53 (((%73 $2) $1) $0))
       (\%55. (\%45. (($4 (\%74. ((%75 (\%76. (((%77 $1) (($5 $0) $2)) (($4
       $0) $2)))) $2))) $0))))))))))`)
  val CPS_REC_def =
    DT([], [],
       `(%78 (\%79. (%80 (\%81. (%82 (\%83. ((%35 (((%84 $2) $1) $0))
       (\%37. (\%38. ($1 ((((%85 ($4 (\%86. $0))) ($3 (\%87. $0))) ($2
       (\%88. $0))) $0)))))))))))`)
  val Rec_ind =
    DT(["DISK_THM"],
       [`(%27 (\%6. ((%28 (%29 (%13 $0))) ((%24 (%20 $0)) $0))))`,
        `(%26 %24)`],
       `(%12 (\%89. ((%28 (%27 (\%6. ((%28 ((%28 (%29 (%13 $0))) ($1 (%20
       $0)))) ($1 $0))))) (%27 (\%90. ($1 $0))))))`)
  val Rec_def =
    DT(["DISK_THM"],
       [`(%27 (\%6. ((%28 (%29 (%13 $0))) ((%24 (%20 $0)) $0))))`,
        `(%26 %24)`],
       `((%91 ((((%21 %13) %14) %20) %6)) (((%18 (%13 %6)) (%14 %6))
       ((((%21 %13) %14) %20) (%20 %6))))`)
  val CPS_ID =
    DT(["DISK_THM"], [], `((%92 (%93 (\%6. $0))) (\%37. (\%6. ($1 $0))))`)
  val CPS_CONST =
    DT(["DISK_THM"], [],
       `((%35 (%36 (\%94. %95))) (\%37. (\%94. ($1 %95))))`)
  val UNCPS =
    DT(["DISK_THM"], [],
       `((%16 ((%96 %97) %98)) (\%99. ((%100 (\%101. (%98 $0))) (%97
       $0))))`)
  val CPS_INV =
    DT(["DISK_THM"], [],
       `((%25 (%102 (\%103. (%104 (\%105. ((%28 ((%106 $1) (%107 $0)))
       ((%106 $1) (%107 (\%45. (($2 (\%6. $0)) $0)))))))))) (%108 (\%109.
       ((%110 ($0 %38)) (((%111 $0) (\%86. $0)) %38)))))`)
  val CPS2_INV =
    DT(["DISK_THM"], [],
       `((%25 (%112 (\%113. ((%28 (%114 (\%115. ((%116 $1) (%117 $0)))))
       ((%116 $0) (%117 (\%99. ((($1 (\%118. $0)) (\%118. $0)) $0))))))))
       (%39 (\%40. ((%119 ($0 %45)) ((((%120 $0) (\%118. $0)) (\%118. $0))
       %45)))))`)
  val CPS_SEQ_INTRO =
    DT(["DISK_THM"], [],
       `(%0 (\%121. (%2 (\%122. ((%123 (%124 ((%5 $1) $0))) ((%125 (%126
       $1)) (%127 $0)))))))`)
  val CPS_PAR_INTRO =
    DT(["DISK_THM"], [],
       `(%0 (\%121. (%7 (\%128. ((%129 (%130 ((%10 $1) $0))) ((%131 (%126
       $1)) (%124 $0)))))))`)
  val CPS_ITE_INTRO =
    DT(["DISK_THM"], [],
       `(%12 (\%132. (%0 (\%121. (%0 (\%133. ((%134 (%135 (((%17 $2) $1)
       $0))) (((%136 (%137 $2)) (%135 $1)) (%135 $0)))))))))`)
  val CPS_REC_INTRO =
    DT(["DISK_THM"], [],
       `(%12 (\%132. (%0 (\%121. (%19 (\%138. ((%134 (%135 (((%21 $2) $1)
       $0))) (((%139 (%140 $2)) (%141 $1)) (%142 $0)))))))))`)
  val Rec_INTRO =
    DT(["DISK_THM"], [],
       `(%0 (\%121. (%12 (\%13. (%0 (\%14. (%19 (\%20. ((%28 (%27 (\%6.
       ((%91 ($4 $0)) (((%18 ($3 $0)) ($2 $0)) ($4 ($1 $0))))))) ((%28
       (%143 (\%24. ((%25 (%26 $0)) (%27 (\%6. ((%28 (%29 ($4 $0))) (($1
       ($2 $0)) $0)))))))) ((%16 $3) (((%21 $2) $1) $0))))))))))))`)
  val MY_LET_RAND =
    DT(["DISK_THM"], [],
       `(%0 (\%121. (%144 (\%145. (%33 (\%146. ((%91 ((%100 (\%94. ($3 ($1
       $0)))) $1)) ($2 ((%147 (\%94. ($1 $0))) $1)))))))))`)
  val UNLET =
    DT(["DISK_THM"], [],
       `(%0 (\%121. (%27 (\%148. ((%91 ((%149 (\%14. ($0 $1))) $1)) ($1
       $0))))))`)
  end
  val _ = DB.bindl "cps"
  [("Seq_def",Seq_def,DB.Def), ("Par_def",Par_def,DB.Def),
   ("Ite_def",Ite_def,DB.Def),
   ("Rec_primitive_def",Rec_primitive_def,DB.Def),
   ("CPS_def",CPS_def,DB.Def), ("CPS2_def",CPS2_def,DB.Def),
   ("CPS_SEQ_def",CPS_SEQ_def,DB.Def), ("CPS_PAR_def",CPS_PAR_def,DB.Def),
   ("CPS_ITE_def",CPS_ITE_def,DB.Def), ("CPS_REC_def",CPS_REC_def,DB.Def),
   ("Rec_ind",Rec_ind,DB.Thm), ("Rec_def",Rec_def,DB.Thm),
   ("CPS_ID",CPS_ID,DB.Thm), ("CPS_CONST",CPS_CONST,DB.Thm),
   ("UNCPS",UNCPS,DB.Thm), ("CPS_INV",CPS_INV,DB.Thm),
   ("CPS2_INV",CPS2_INV,DB.Thm), ("CPS_SEQ_INTRO",CPS_SEQ_INTRO,DB.Thm),
   ("CPS_PAR_INTRO",CPS_PAR_INTRO,DB.Thm),
   ("CPS_ITE_INTRO",CPS_ITE_INTRO,DB.Thm),
   ("CPS_REC_INTRO",CPS_REC_INTRO,DB.Thm), ("Rec_INTRO",Rec_INTRO,DB.Thm),
   ("MY_LET_RAND",MY_LET_RAND,DB.Thm), ("UNLET",UNLET,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("listTheory.list_grammars",
                          listTheory.list_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "Seq")
        {Name = "Seq", Thy = "cps"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Par")
        {Name = "Par", Thy = "cps"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Ite")
        {Name = "Ite", Thy = "cps"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Rec")
        {Name = "Rec", Thy = "cps"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CPS")
        {Name = "CPS", Thy = "cps"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CPS2")
        {Name = "CPS2", Thy = "cps"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CPS_SEQ")
        {Name = "CPS_SEQ", Thy = "cps"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CPS_PAR")
        {Name = "CPS_PAR", Thy = "cps"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CPS_ITE")
        {Name = "CPS_ITE", Thy = "cps"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CPS_REC")
        {Name = "CPS_REC", Thy = "cps"}
  val cps_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [Seq_def];  
  
  val _ = computeLib.add_funs [Par_def];  
  
  val _ = computeLib.add_funs [Ite_def];  
  
  val _ = computeLib.add_funs [CPS_def];  
  
  val _ = computeLib.add_funs [CPS2_def];  
  
  val _ = computeLib.add_funs [CPS_SEQ_def];  
  
  val _ = computeLib.add_funs [CPS_PAR_def];  
  
  val _ = computeLib.add_funs [CPS_ITE_def];  
  
  val _ = computeLib.add_funs [CPS_REC_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
