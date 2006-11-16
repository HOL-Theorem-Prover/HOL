structure simplifierTheory :> simplifierTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading simplifierTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open finite_mapTheory
  in end;
  val _ = Theory.link_parents
          ("simplifier",
          Arbnum.fromString "1163213580",
          Arbnum.fromString "80264")
          [("finite_map",
           Arbnum.fromString "1157051022",
           Arbnum.fromString "797566")];
  val _ = Theory.incorporate_types "simplifier" [];
  val _ = Theory.incorporate_consts "simplifier" [];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool"
    (((T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool) --> bool)),
   V"f" (T"fmap" "finite_map" [T"num" "num" [], alpha]),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"a" (T"num" "num" []), C"!" "bool" (((alpha --> bool) --> bool)),
   V"b" (alpha), V"c" (T"num" "num" []), V"d" (alpha),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"=" "min"
    ((T"fmap" "finite_map" [T"num" "num" [], alpha] -->
      (T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool))),
   C"FUPDATE" "finite_map"
    ((T"fmap" "finite_map" [T"num" "num" [], alpha] -->
      (T"prod" "pair" [T"num" "num" [], alpha] -->
       T"fmap" "finite_map" [T"num" "num" [], alpha]))),
   C"," "pair"
    ((T"num" "num" [] -->
      (alpha --> T"prod" "pair" [T"num" "num" [], alpha])))]
  val DT = Thm.disk_thm share_table
  in
  val FUPDATE_LT_COMMUTES =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%2 (\%3. (%4 (\%5. (%2 (\%6. (%4 (\%7. ((%8 ((%9 $1)
       $3)) ((%10 ((%11 ((%11 $4) ((%12 $3) $2))) ((%12 $1) $0))) ((%11
       ((%11 $4) ((%12 $1) $0))) ((%12 $3) $2))))))))))))))`)
  end
  val _ = DB.bindl "simplifier"
  [("FUPDATE_LT_COMMUTES",FUPDATE_LT_COMMUTES,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("finite_mapTheory.finite_map_grammars",
                          finite_mapTheory.finite_map_grammars)]
  val _ = List.app (update_grms reveal) []
  
  val simplifier_grammars = Parse.current_lgrms()
  end
  
  
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
