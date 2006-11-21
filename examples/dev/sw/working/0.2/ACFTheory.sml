structure ACFTheory :> ACFTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading ACFTheory ... " else ()
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
          ("ACF",Arbnum.fromString "1164098271",Arbnum.fromString "461267")
          [("list",
           Arbnum.fromString "1157050827",
           Arbnum.fromString "489338")];
  val _ = Theory.incorporate_types "ACF" [];
  val _ = Theory.incorporate_consts "ACF"
     [("tr",
       (((alpha --> bool) --> ((alpha --> alpha) --> (alpha --> alpha))))),
      ("sc",
       (((alpha --> beta) --> ((beta --> gamma) --> (alpha --> gamma))))),
      ("cj",
       (((alpha --> bool) -->
         ((alpha --> beta) -->
          ((alpha --> beta) --> (alpha --> beta))))))];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool" ((((alpha --> beta) --> bool) --> bool)),
   V"f1" ((alpha --> beta)),
   C"!" "bool" ((((beta --> gamma) --> bool) --> bool)),
   V"f2" ((beta --> gamma)),
   C"=" "min" (((alpha --> gamma) --> ((alpha --> gamma) --> bool))),
   C"sc" "ACF"
    (((alpha --> beta) --> ((beta --> gamma) --> (alpha --> gamma)))),
   V"x" (alpha), C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"f1" ((alpha --> bool)), V"f2" ((alpha --> beta)),
   V"f3" ((alpha --> beta)),
   C"=" "min" (((alpha --> beta) --> ((alpha --> beta) --> bool))),
   C"cj" "ACF"
    (((alpha --> bool) -->
      ((alpha --> beta) --> ((alpha --> beta) --> (alpha --> beta))))),
   C"COND" "bool" ((bool --> (beta --> (beta --> beta)))),
   C"!" "bool" ((((alpha --> alpha) --> bool) --> bool)),
   V"f2" ((alpha --> alpha)),
   C"=" "min" (((alpha --> alpha) --> ((alpha --> alpha) --> bool))),
   C"tr" "ACF"
    (((alpha --> bool) --> ((alpha --> alpha) --> (alpha --> alpha)))),
   C"WFREC" "relation"
    (((alpha --> (alpha --> bool)) -->
      (((alpha --> alpha) --> (alpha --> alpha)) --> (alpha --> alpha)))),
   C"@" "min"
    ((((alpha --> (alpha --> bool)) --> bool) -->
      (alpha --> (alpha --> bool)))), V"R" ((alpha --> (alpha --> bool))),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"WF" "relation" (((alpha --> (alpha --> bool)) --> bool)),
   C"!" "bool" (((alpha --> bool) --> bool)),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"~" "bool" ((bool --> bool)), V"tr" ((alpha --> alpha)), V"a" (alpha),
   C"I" "combin" ((alpha --> alpha)),
   C"COND" "bool" ((bool --> (alpha --> (alpha --> alpha)))),
   V"P" ((alpha --> bool)), V"v" (alpha),
   C"=" "min" ((alpha --> (alpha --> bool))), V"f" ((alpha --> alpha)),
   C"?" "bool" ((((alpha --> (alpha --> bool)) --> bool) --> bool)),
   V"f" ((alpha --> beta)), V"f3" ((alpha --> alpha)),
   C"=" "min" ((beta --> (beta --> bool))),
   C"sc" "ACF"
    (((alpha --> alpha) --> ((alpha --> beta) --> (alpha --> beta))))]
  val DT = Thm.disk_thm share_table
  in
  val sc_def =
    DT([], [],
       `(%0 (\%1. (%2 (\%3. ((%4 ((%5 $1) $0)) (\%6. ($1 ($2 $0))))))))`)
  val cj_def =
    DT([], [],
       `(%7 (\%8. (%0 (\%9. (%0 (\%10. ((%11 (((%12 $2) $1) $0)) (\%6.
       (((%13 ($3 $0)) ($2 $0)) ($1 $0))))))))))`)
  val tr_primitive_def =
    DT([], [],
       `(%7 (\%8. (%14 (\%15. ((%16 ((%17 $1) $0)) ((%18 (%19 (\%20. ((%21
       (%22 $0)) (%23 (\%6. ((%24 (%25 ($3 $0))) (($1 ($2 $0)) $0))))))))
       (\%26. (\%27. (%28 (((%29 ($3 $0)) $0) ($1 ($2 $0))))))))))))`)
  val tr_ind =
    DT(["DISK_THM"],
       [`(%23 (\%6. ((%24 (%25 (%8 $0))) ((%20 (%15 $0)) $0))))`,
        `(%22 %20)`],
       `(%7 (\%30. ((%24 (%23 (\%6. ((%24 ((%24 (%25 (%8 $0))) ($1 (%15
       $0)))) ($1 $0))))) (%23 (\%31. ($1 $0))))))`)
  val tr_def =
    DT(["DISK_THM"],
       [`(%23 (\%6. ((%24 (%25 (%8 $0))) ((%20 (%15 $0)) $0))))`,
        `(%22 %20)`],
       `((%32 (((%17 %8) %15) %6)) (((%29 (%8 %6)) %6) (((%17 %8) %15) (%15
       %6))))`)
  val tr_INTRO =
    DT(["DISK_THM"], [],
       `(%14 (\%33. (%7 (\%8. (%14 (\%15. ((%24 (%23 (\%6. ((%32 ($3 $0))
       (((%29 ($2 $0)) $0) ($3 ($1 $0))))))) ((%24 (%34 (\%20. ((%21 (%22
       $0)) (%23 (\%6. ((%24 (%25 ($3 $0))) (($1 ($2 $0)) $0)))))))) ((%16
       $2) ((%17 $1) $0))))))))))`)
  val rec_INTRO =
    DT(["DISK_THM"], [],
       `(%0 (\%35. (%7 (\%8. (%0 (\%9. (%14 (\%36. ((%24 (%23 (\%6. ((%37
       ($4 $0)) (((%13 ($3 $0)) ($2 $0)) ($4 ($1 $0))))))) ((%24 (%34
       (\%20. ((%21 (%22 $0)) (%23 (\%6. ((%24 (%25 ($4 $0))) (($1 ($2 $0))
       $0)))))))) ((%11 $3) ((%38 ((%17 $2) $0)) $1))))))))))))`)
  end
  val _ = DB.bindl "ACF"
  [("sc_def",sc_def,DB.Def), ("cj_def",cj_def,DB.Def),
   ("tr_primitive_def",tr_primitive_def,DB.Def), ("tr_ind",tr_ind,DB.Thm),
   ("tr_def",tr_def,DB.Thm), ("tr_INTRO",tr_INTRO,DB.Thm),
   ("rec_INTRO",rec_INTRO,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("listTheory.list_grammars",
                          listTheory.list_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "sc")
        {Name = "sc", Thy = "ACF"}
  val _ = update_grms
       (temp_overload_on_by_nametype "cj")
        {Name = "cj", Thy = "ACF"}
  val _ = update_grms
       (temp_overload_on_by_nametype "tr")
        {Name = "tr", Thy = "ACF"}
  val ACF_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [sc_def];  
  
  val _ = computeLib.add_funs [cj_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
