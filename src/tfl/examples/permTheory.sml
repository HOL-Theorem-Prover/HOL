structure permTheory :> permTheory =
struct
  type thm = Thm.thm
  val pty = Parse.type_parser
  fun C s q = Term.mk_const{Name=s,Ty=pty q}
  fun V s q = Term.mk_var{Name=s,Ty=pty q}
  
  (*  Parents *)
  local open listXTheory
  in end;
  val _ = Theory.link_parents
          ("perm",922903232,776926)
          [("listX",922903215,411142)];
  val _ = Theory.incorporate_types "perm" [];
  val _ = Theory.incorporate_consts "perm"
     [("perm",pty`:'a list -> 'a list -> bool`,Term.Prefix)];
  
  local
  val share_table = Vector.fromList
  [C "!" `:('a list -> bool) -> bool`, V "L1" `:'a list`, V "L2" `:'a list`,
   C "=" `:bool -> bool -> bool`, C "perm" `:'a list -> 'a list -> bool`,
   C "!" `:('a -> bool) -> bool`, V "x" `:'a`,
   C "=" `:'a list -> 'a list -> bool`,
   C "filter" `:('a -> bool) -> 'a list -> 'a list`,
   C "=" `:'a -> 'a -> bool`, V "L" `:'a list`, V "x" `:'a list`,
   V "y" `:'a list`, C "==>" `:bool -> bool -> bool`,
   C "transitive" `:('a list -> 'a list -> bool) -> bool`, V "z" `:'a list`,
   C "/\\" `:bool -> bool -> bool`, V "l1" `:'a list`, V "l2" `:'a list`,
   V "L3" `:'a list`, V "L4" `:'a list`,
   C "APPEND" `:'a list -> 'a list -> 'a list`,
   C "CONS" `:'a -> 'a list -> 'a list`, C "NIL" `:'a list`, V "M" `:'a list`,
   V "N" `:'a list`, V "A" `:'a list`, V "B" `:'a list`, V "C" `:'a list`,
   C "!" `:(('a -> bool) -> bool) -> bool`, V "P" `:'a -> bool`,
   V "l" `:'a list`, C "o" `:(bool -> bool) -> ('a -> bool) -> 'a -> bool`,
   C "~" `:bool -> bool`, C "=" `:num -> num -> bool`,
   C "LENGTH" `:'a list -> num`]
  val DT = Thm.disk_thm share_table
  in
  val perm_def =
    DT("", [],
       `(%0 (\%1. (%0 (\%2. ((%3 ((%4 $1) $0)) (%5 (\%6. ((%7 ((%8 (%9 $0))
       $2)) ((%8 (%9 $0)) $1)))))))))`)
  val perm_refl = DT("", [], `(%0 (\%10. ((%4 $0) $0)))`)
  val perm_intro =
    DT("", [], `(%0 (\%11. (%0 (\%12. ((%13 ((%7 $1) $0)) ((%4 $1) $0))))))`)
  val perm_trans = DT("", [], `(%14 %4)`)
  val trans_permute =
    DT("", [],
       `(%0 (\%11. (%0 (\%12. (%0 (\%15. ((%13 ((%16 ((%4 $2) $1)) ((%4 $1)
       $0))) ((%4 $2) $0))))))))`)
  val perm_sym =
    DT("", [], `(%0 (\%17. (%0 (\%18. ((%3 ((%4 $1) $0)) ((%4 $0) $1))))))`)
  val perm_cong =
    DT("", [],
       `(%0 (\%1. (%0 (\%2. (%0 (\%19. (%0 (\%20. ((%13 ((%16 ((%4 $3) $1))
       ((%4 $2) $0))) ((%4 ((%21 $3) $2)) ((%21 $1) $0)))))))))))`)
  val perm_mono =
    DT("", [],
       `(%0 (\%17. (%0 (\%18. (%5 (\%6. ((%13 ((%4 $2) $1)) ((%4 ((%22 $0)
       $2)) ((%22 $0) $1)))))))))`)
  val perm_cons_iff =
    DT("", [],
       `(%0 (\%18. (%0 (\%17. (%5 (\%6. ((%3 ((%4 ((%22 $0) $1)) ((%22 $0)
       $2))) ((%4 $1) $2))))))))`)
  val perm_nil =
    DT("", [],
       `(%0 (\%10. ((%16 ((%3 ((%4 $0) %23)) ((%7 $0) %23))) ((%3 ((%4 %23)
       $0)) ((%7 $0) %23)))))`)
  val perm_append =
    DT("", [], `(%0 (\%17. (%0 (\%18. ((%4 ((%21 $1) $0)) ((%21 $0) $1))))))`)
  val cons_perm =
    DT("", [],
       `(%5 (\%6. (%0 (\%10. (%0 (\%24. (%0 (\%25. ((%13 ((%4 $2) ((%21 $1)
       $0))) ((%4 ((%22 $3) $2)) ((%21 $1) ((%22 $3) $0))))))))))))`)
  val append_perm_sym =
    DT("", [],
       `(%0 (\%26. (%0 (\%27. (%0 (\%28. ((%13 ((%4 ((%21 $2) $1)) $0)) ((%4
       ((%21 $1) $2)) $0))))))))`)
  val perm_split =
    DT("", [],
       `(%29 (\%30. (%0 (\%31. ((%4 $0) ((%21 ((%8 $1) $0)) ((%8 ((%32 %33)
       $1)) $0)))))))`)
  val perm_length =
    DT("", [],
       `(%0 (\%17. (%0 (\%18. ((%13 ((%4 $1) $0)) ((%34 (%35 $1)) (%35
       $0)))))))`)
  end
  val _ = DB.bindl "perm"
  [("perm_def",perm_def,DB.Def), ("perm_refl",perm_refl,DB.Thm),
   ("perm_intro",perm_intro,DB.Thm), ("perm_trans",perm_trans,DB.Thm),
   ("trans_permute",trans_permute,DB.Thm), ("perm_sym",perm_sym,DB.Thm),
   ("perm_cong",perm_cong,DB.Thm), ("perm_mono",perm_mono,DB.Thm),
   ("perm_cons_iff",perm_cons_iff,DB.Thm), ("perm_nil",perm_nil,DB.Thm),
   ("perm_append",perm_append,DB.Thm), ("cons_perm",cons_perm,DB.Thm),
   ("append_perm_sym",append_perm_sym,DB.Thm),
   ("perm_split",perm_split,DB.Thm), ("perm_length",perm_length,DB.Thm)]
  
  
end
