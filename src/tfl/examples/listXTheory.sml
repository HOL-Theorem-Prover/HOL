structure listXTheory :> listXTheory =
struct
  type thm = Thm.thm
  val pty = Parse.type_parser
  fun C s q = Term.mk_const{Name=s,Ty=pty q}
  fun V s q = Term.mk_var{Name=s,Ty=pty q}
  
  (*  Parents *)
  local open WFTheory optionTheory rec_typeTheory
  in end;
  val _ = Theory.link_parents
          ("listX",927258083,938096)
          [("option",927222864,902058), ("rec_type",927222918,415281),
           ("WF",927222990,444400)];
  val _ = Theory.incorporate_types "listX" [];
  val _ = Theory.incorporate_consts "listX"
     [("mem",pty`:'a -> 'a list -> bool`,Term.Prefix),
      ("filter",pty`:('a -> bool) -> 'a list -> 'a list`,Term.Prefix)];
  
  local
  val share_table = Vector.fromList
  [C "/\\" `:bool -> bool -> bool`, C "!" `:('a -> bool) -> bool`,
   V "x" `:'a`, C "=" `:bool -> bool -> bool`,
   C "mem" `:'a -> 'a list -> bool`, C "NIL" `:'a list`, C "F" `:bool`,
   C "!" `:('a list -> bool) -> bool`, V "L" `:'a list`, V "y" `:'a`,
   C "CONS" `:'a -> 'a list -> 'a list`, C "\\/" `:bool -> bool -> bool`,
   C "=" `:'a -> 'a -> bool`, C "!" `:(('a -> bool) -> bool) -> bool`,
   V "P" `:'a -> bool`, C "=" `:'a list -> 'a list -> bool`,
   C "filter" `:('a -> bool) -> 'a list -> 'a list`,
   C "COND" `:bool -> 'a list -> 'a list -> 'a list`,
   C "o" `:(bool -> bool) -> ('a -> bool) -> 'a -> bool`,
   C "~" `:bool -> bool`, C "<=" `:num -> num -> bool`,
   C "LENGTH" `:'a list -> num`, C "==>" `:bool -> bool -> bool`,
   V "Q" `:'a -> bool`, C "=" `:num -> num -> bool`, V "M" `:'a list`,
   C "APPEND" `:'a list -> 'a list -> 'a list`, V "l" `:'a list`,
   V "l1" `:'a list`, V "l2" `:'a list`, V "h" `:'a`,
   C "+" `:num -> num -> num`]
  val DT = Thm.disk_thm share_table
  in
  val mem_def =
    DT("", [],
       `((%0 (%1 (\%2. ((%3 ((%4 $0) %5)) %6)))) (%1 (\%2. (%7 (\%8. (%1 (\%9.
       ((%3 ((%4 $2) ((%10 $0) $1))) ((%11 ((%12 $2) $0)) ((%4 $2)
       $1))))))))))`)
  val filter_def =
    DT("", [],
       `((%0 (%13 (\%14. ((%15 ((%16 $0) %5)) %5)))) (%13 (\%14. (%7 (\%8. (%1
       (\%2. ((%15 ((%16 $2) ((%10 $0) $1))) (((%17 ($2 $0)) ((%10 $0) ((%16
       $2) $1))) ((%16 $2) $1))))))))))`)
  val mem_filter =
    DT("", [],
       `(%13 (\%14. (%7 (\%8. (%1 (\%2. ((%3 ((%4 $0) ((%16 $2) $1))) ((%0 ($2
       $0)) ((%4 $0) $1)))))))))`)
  val mem_filter_lemma =
    DT("", [],
       `(%13 (\%14. (%7 (\%8. (%1 (\%2. ((%3 ((%4 $0) $1)) ((%11 ((%4 $0)
       ((%16 $2) $1))) ((%4 $0) ((%16 ((%18 %19) $2)) $1))))))))))`)
  val length_filter =
    DT("", [],
       `(%7 (\%8. (%13 (\%14. ((%20 (%21 ((%16 $0) $1))) (%21 $1))))))`)
  val length_filter_subset =
    DT("", [],
       `((%22 (%1 (\%9. ((%22 (%14 $0)) (%23 $0))))) (%7 (\%8. ((%20 (%21
       ((%16 %14) $0))) (%21 ((%16 %23) $0))))))`)
  val length_filter_stable =
    DT("", [],
       `(%7 (\%8. (%13 (\%14. ((%22 ((%24 (%21 ((%16 $0) $1))) (%21 $1)))
       ((%15 ((%16 $0) $1)) $1))))))`)
  val mem_of_append =
    DT("", [],
       `(%1 (\%9. (%7 (\%8. (%7 (\%25. ((%3 ((%4 $2) ((%26 $1) $0))) ((%11
       ((%4 $2) $1)) ((%4 $2) $0)))))))))`)
  val APPEND =
    DT("", [],
       `((%0 (%7 (\%8. ((%15 ((%26 $0) %5)) $0)))) ((%0 (%7 (\%27. ((%15 ((%26
       %5) $0)) $0)))) (%7 (\%28. (%7 (\%29. (%1 (\%30. ((%15 ((%26 ((%10 $0)
       $2)) $1)) ((%10 $0) ((%26 $2) $1)))))))))))`)
  val filter_append_distrib =
    DT("", [],
       `(%13 (\%14. (%7 (\%8. (%7 (\%25. ((%15 ((%16 $2) ((%26 $1) $0))) ((%26
       ((%16 $2) $1)) ((%16 $2) $0)))))))))`)
  val length_append_comm =
    DT("", [],
       `(%7 (\%8. (%7 (\%25. ((%24 (%21 ((%26 $1) $0))) (%21 ((%26 $0)
       $1)))))))`)
  val length_append_distrib =
    DT("", [],
       `(%7 (\%8. (%7 (\%25. ((%24 (%21 ((%26 $1) $0))) ((%31 (%21 $1)) (%21
       $0)))))))`)
  val length_append_filter =
    DT("", [],
       `(%7 (\%8. ((%24 (%21 $0)) (%21 ((%26 ((%16 %14) $0)) ((%16 ((%18 %19)
       %14)) $0))))))`)
  val filters_compose =
    DT("", [],
       `(%13 (\%14. (%13 (\%23. (%7 (\%8. ((%15 ((%16 $2) ((%16 $1) $0)))
       ((%16 (\%2. ((%0 ($3 $0)) ($2 $0)))) $0))))))))`)
  val filters_commute =
    DT("", [],
       `(%13 (\%14. (%13 (\%23. (%7 (\%8. ((%15 ((%16 $2) ((%16 $1) $0)))
       ((%16 $1) ((%16 $2) $0)))))))))`)
  end
  val _ = DB.bindl "listX"
  [("mem_def",mem_def,DB.Def), ("filter_def",filter_def,DB.Def),
   ("mem_filter",mem_filter,DB.Thm),
   ("mem_filter_lemma",mem_filter_lemma,DB.Thm),
   ("length_filter",length_filter,DB.Thm),
   ("length_filter_subset",length_filter_subset,DB.Thm),
   ("length_filter_stable",length_filter_stable,DB.Thm),
   ("mem_of_append",mem_of_append,DB.Thm), ("APPEND",APPEND,DB.Thm),
   ("filter_append_distrib",filter_append_distrib,DB.Thm),
   ("length_append_comm",length_append_comm,DB.Thm),
   ("length_append_distrib",length_append_distrib,DB.Thm),
   ("length_append_filter",length_append_filter,DB.Thm),
   ("filters_compose",filters_compose,DB.Thm),
   ("filters_commute",filters_commute,DB.Thm)]
  
  
end
