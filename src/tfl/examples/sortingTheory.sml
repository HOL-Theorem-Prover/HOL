structure sortingTheory :> sortingTheory =
struct
  type thm = Thm.thm
  val pty = Parse.type_parser
  fun C s q = Term.mk_const{Name=s,Ty=pty q}
  fun V s q = Term.mk_var{Name=s,Ty=pty q}
  
  (*  Parents *)
  local open permTheory
  in end;
  val _ = Theory.link_parents
          ("sorting",922903251,260283)
          [("perm",922903232,776926)];
  val _ = Theory.incorporate_types "sorting" [];
  val _ = Theory.incorporate_consts "sorting"
     [("performs_sorting",
       pty`:(('a -> 'a -> bool) -> 'a list -> 'a list) ->
            ('a -> 'a -> bool) -> bool`,Term.Prefix),
      ("tupled_sorted",pty`:('a -> 'a -> bool) # 'a list -> bool`,
       Term.Prefix),
      ("sorted",pty`:('a -> 'a -> bool) -> 'a list -> bool`,Term.Prefix)];
  
  local
  val share_table = Vector.fromList
  [C "="
     `:(('a -> 'a -> bool) # 'a list -> bool) ->
       (('a -> 'a -> bool) # 'a list -> bool) -> bool`,
   C "tupled_sorted" `:('a -> 'a -> bool) # 'a list -> bool`,
   C "WFREC"
     `:(('a -> 'a -> bool) # 'a list -> ('a -> 'a -> bool) # 'a list ->
       bool) ->
       ((('a -> 'a -> bool) # 'a list -> bool) ->
       ('a -> 'a -> bool) # 'a list -> bool) ->
       ('a -> 'a -> bool) # 'a list -> bool`,
   C "@"
     `:((('a -> 'a -> bool) # 'a list -> ('a -> 'a -> bool) # 'a list ->
        bool) -> bool) -> ('a -> 'a -> bool) # 'a list ->
       ('a -> 'a -> bool) # 'a list -> bool`,
   V "R'"
     `:('a -> 'a -> bool) # 'a list -> ('a -> 'a -> bool) # 'a list -> bool`,
   C "/\\" `:bool -> bool -> bool`,
   C "WF"
     `:(('a -> 'a -> bool) # 'a list -> ('a -> 'a -> bool) # 'a list ->
       bool) -> bool`, C "!" `:(('a -> 'a -> bool) -> bool) -> bool`,
   V "R" `:'a -> 'a -> bool`, C "!" `:('a -> bool) -> bool`, V "y" `:'a`,
   C "!" `:('a list -> bool) -> bool`, V "rst" `:'a list`, V "x" `:'a`,
   C "," `:('a -> 'a -> bool) -> 'a list -> ('a -> 'a -> bool) # 'a list`,
   C "CONS" `:'a -> 'a list -> 'a list`,
   V "tupled_sorted" `:('a -> 'a -> bool) # 'a list -> bool`,
   V "a" `:('a -> 'a -> bool) # 'a list`,
   C "pair_case"
     `:(('a -> 'a -> bool) -> 'a list -> bool) ->
       ('a -> 'a -> bool) # 'a list -> bool`, V "v" `:'a -> 'a -> bool`,
   V "v1" `:'a list`,
   C "list_case" `:bool -> ('a -> 'a list -> bool) -> 'a list -> bool`,
   C "T" `:bool`, V "v2" `:'a`, V "v3" `:'a list`, V "v4" `:'a`,
   V "v5" `:'a list`, V "x" `:'a -> 'a -> bool`, V "x'" `:'a list`,
   C "=" `:bool -> bool -> bool`,
   C "sorted" `:('a -> 'a -> bool) -> 'a list -> bool`,
   C "!" `:((('a -> 'a -> bool) -> 'a list -> 'a list) -> bool) -> bool`,
   V "f" `:('a -> 'a -> bool) -> 'a list -> 'a list`,
   C "performs_sorting"
     `:(('a -> 'a -> bool) -> 'a list -> 'a list) -> ('a -> 'a -> bool) ->
       bool`, V "l" `:'a list`, C "perm" `:'a list -> 'a list -> bool`,
   C "NIL" `:'a list`,
   C "!" `:((('a -> 'a -> bool) -> 'a list -> bool) -> bool) -> bool`,
   V "P" `:('a -> 'a -> bool) -> 'a list -> bool`,
   C "==>" `:bool -> bool -> bool`, V "L" `:'a list`,
   C "transitive" `:('a -> 'a -> bool) -> bool`,
   C "mem" `:'a -> 'a list -> bool`, V "L1" `:'a list`, V "L2" `:'a list`,
   C "APPEND" `:'a list -> 'a list -> 'a list`]
  val DT = Thm.disk_thm share_table
  in
  val tupled_sorted_def =
    DT("", [],
       `((%0 %1) ((%2 (%3 (\%4. ((%5 (%6 $0)) (%7 (\%8. (%9 (\%10. (%11 (\%12.
       (%9 (\%13. (($4 ((%14 $3) ((%15 $2) $1))) ((%14 $3) ((%15 $0) ((%15 $2)
       $1)))))))))))))))) (\%16. (\%17. ((%18 (\%19. (\%20. (((%21 %22) (\%23.
       (\%24. (((%21 %22) (\%25. (\%26. ((%5 (($5 $3) $1)) ($7 ((%14 $5) ((%15
       $1) $0))))))) $0)))) $0)))) $0)))))`)
  val sorted_def =
    DT("", [],
       `(%7 (\%27. (%11 (\%28. ((%29 ((%30 $1) $0)) (%1 ((%14 $1) $0)))))))`)
  val performs_sorting_def =
    DT("", [],
       `(%31 (\%32. (%7 (\%8. ((%29 ((%33 $1) $0)) (%11 (\%34. ((%5 ((%35 $0)
       (($2 $1) $0))) ((%30 $1) (($2 $1) $0))))))))))`)
  val sorted_def_thm =
    DT("", [],
       `((%5 ((%5 ((%29 ((%30 %8) %36)) %22)) ((%5 ((%29 ((%30 %8) ((%15 %13)
       %36))) %22)) ((%29 ((%30 %8) ((%15 %13) ((%15 %10) %12)))) ((%5 ((%8
       %13) %10)) ((%30 %8) ((%15 %10) %12))))))) (%37 (\%38. ((%39 ((%5 (%7
       (\%8. (($1 $0) %36)))) ((%5 (%7 (\%8. (%9 (\%13. (($2 $1) ((%15 $0)
       %36))))))) (%7 (\%8. (%9 (\%13. (%9 (\%10. (%11 (\%12. ((%39 (($4 $3)
       ((%15 $1) $0))) (($4 $3) ((%15 $2) ((%15 $1) $0))))))))))))))) (%7
       (\%19. (%11 (\%20. (($2 $1) $0)))))))))`)
  val sorted_eqns =
    DT("", [],
       `((%5 ((%29 ((%30 %8) %36)) %22)) ((%5 ((%29 ((%30 %8) ((%15 %13)
       %36))) %22)) ((%29 ((%30 %8) ((%15 %13) ((%15 %10) %12)))) ((%5 ((%8
       %13) %10)) ((%30 %8) ((%15 %10) %12))))))`)
  val sorted_induction =
    DT("", [],
       `(%37 (\%38. ((%39 ((%5 (%7 (\%8. (($1 $0) %36)))) ((%5 (%7 (\%8. (%9
       (\%13. (($2 $1) ((%15 $0) %36))))))) (%7 (\%8. (%9 (\%13. (%9 (\%10.
       (%11 (\%12. ((%39 (($4 $3) ((%15 $1) $0))) (($4 $3) ((%15 $2) ((%15 $1)
       $0))))))))))))))) (%7 (\%19. (%11 (\%20. (($2 $1) $0))))))))`)
  val sorted_eq =
    DT("", [],
       `(%7 (\%8. (%11 (\%40. (%9 (\%13. ((%39 (%41 $2)) ((%29 ((%30 $2) ((%15
       $0) $1))) ((%5 ((%30 $2) $1)) (%9 (\%10. ((%39 ((%42 $0) $2)) (($3 $1)
       $0)))))))))))))`)
  val sorted_append =
    DT("", [],
       `(%7 (\%8. (%11 (\%43. (%11 (\%44. ((%39 ((%5 (%41 $2)) ((%5 ((%30 $2)
       $1)) ((%5 ((%30 $2) $0)) (%9 (\%13. (%9 (\%10. ((%39 ((%5 ((%42 $1)
       $3)) ((%42 $0) $2))) (($4 $1) $0)))))))))) ((%30 $2) ((%45 $1)
       $0)))))))))`)
  end
  val _ = DB.bindl "sorting"
  [("tupled_sorted_def",tupled_sorted_def,DB.Def),
   ("sorted_def",sorted_def,DB.Def),
   ("performs_sorting_def",performs_sorting_def,DB.Def),
   ("sorted_def_thm",sorted_def_thm,DB.Thm),
   ("sorted_eqns",sorted_eqns,DB.Thm),
   ("sorted_induction",sorted_induction,DB.Thm),
   ("sorted_eq",sorted_eq,DB.Thm), ("sorted_append",sorted_append,DB.Thm)]
  
  
end
