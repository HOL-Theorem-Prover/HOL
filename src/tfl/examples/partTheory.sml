structure partTheory :> partTheory =
struct
  type thm = Thm.thm
  val pty = Parse.type_parser
  fun C s q = Term.mk_const{Name=s,Ty=pty q}
  fun V s q = Term.mk_var{Name=s,Ty=pty q}
  
  (*  Parents *)
  local open permTheory
  in end;
  val _ = Theory.link_parents
          ("part",922903267,653251)
          [("perm",922903232,776926)];
  val _ = Theory.incorporate_types "part" [];
  val _ = Theory.incorporate_consts "part"
     [("partition",pty`:('a -> bool) -> 'a list -> 'a list # 'a list`,
       Term.Prefix),
      ("part",
       pty`:('a -> bool) -> 'a list -> 'a list -> 'a list ->
            'a list # 'a list`,Term.Prefix)];
  
  local
  val share_table = Vector.fromList
  [C "/\\" `:bool -> bool -> bool`, C "!" `:(('a -> bool) -> bool) -> bool`,
   V "P" `:'a -> bool`, C "!" `:('a list -> bool) -> bool`, V "l1" `:'a list`,
   V "l2" `:'a list`, C "=" `:'a list # 'a list -> 'a list # 'a list -> bool`,
   C "part"
     `:('a -> bool) -> 'a list -> 'a list -> 'a list -> 'a list # 'a list`,
   C "NIL" `:'a list`, C "," `:'a list -> 'a list -> 'a list # 'a list`,
   C "!" `:('a -> bool) -> bool`, V "h" `:'a`, V "rst" `:'a list`,
   C "CONS" `:'a -> 'a list -> 'a list`,
   C "COND"
     `:bool -> 'a list # 'a list -> 'a list # 'a list -> 'a list # 'a list`,
   V "L" `:'a list`,
   C "partition" `:('a -> bool) -> 'a list -> 'a list # 'a list`,
   V "p" `:'a list`, V "q" `:'a list`, C "==>" `:bool -> bool -> bool`,
   C "=" `:num -> num -> bool`, C "+" `:num -> num -> num`,
   C "LENGTH" `:'a list -> num`, C "<=" `:num -> num -> bool`,
   V "a1" `:'a list`, V "a2" `:'a list`, V "x" `:'a`,
   C "=" `:bool -> bool -> bool`, C "mem" `:'a -> 'a list -> bool`,
   C "APPEND" `:'a list -> 'a list -> 'a list`,
   C "perm" `:'a list -> 'a list -> bool`, V "A" `:'a list`, V "B" `:'a list`,
   C "~" `:bool -> bool`, V "z" `:'a`]
  val DT = Thm.disk_thm share_table
  in
  val part_def =
    DT("", [],
       `((%0 (%1 (\%2. (%3 (\%4. (%3 (\%5. ((%6 ((((%7 $2) %8) $1) $0)) ((%9
       $1) $0))))))))) (%1 (\%2. (%10 (\%11. (%3 (\%12. (%3 (\%4. (%3 (\%5.
       ((%6 ((((%7 $4) ((%13 $3) $2)) $1) $0)) (((%14 ($4 $3)) ((((%7 $4) $2)
       ((%13 $3) $1)) $0)) ((((%7 $4) $2) $1) ((%13 $3) $0)))))))))))))))`)
  val partition_def =
    DT("", [],
       `(%1 (\%2. (%3 (\%15. ((%6 ((%16 $1) $0)) ((((%7 $1) $0) %8) %8))))))`)
  val part_length =
    DT("", [],
       `(%1 (\%2. (%3 (\%15. (%3 (\%4. (%3 (\%5. (%3 (\%17. (%3 (\%18. ((%19
       ((%6 ((%9 $1) $0)) ((((%7 $5) $4) $3) $2))) ((%20 ((%21 (%22 $4)) ((%21
       (%22 $3)) (%22 $2)))) ((%21 (%22 $1)) (%22 $0))))))))))))))))`)
  val part_length_lem =
    DT("", [],
       `(%1 (\%2. (%3 (\%15. (%3 (\%4. (%3 (\%5. (%3 (\%17. (%3 (\%18. ((%19
       ((%6 ((%9 $1) $0)) ((((%7 $5) $4) $3) $2))) ((%0 ((%23 (%22 $1)) ((%21
       (%22 $4)) ((%21 (%22 $3)) (%22 $2))))) ((%23 (%22 $0)) ((%21 (%22 $4))
       ((%21 (%22 $3)) (%22 $2))))))))))))))))))`)
  val part_mem =
    DT("", [],
       `(%1 (\%2. (%3 (\%15. (%3 (\%24. (%3 (\%25. (%3 (\%4. (%3 (\%5. ((%19
       ((%6 ((%9 $3) $2)) ((((%7 $5) $4) $1) $0))) (%10 (\%26. ((%27 ((%28 $0)
       ((%29 $5) ((%29 $2) $1)))) ((%28 $0) ((%29 $4) $3))))))))))))))))))`)
  val part_perm_lem =
    DT("", [],
       `(%1 (\%2. (%3 (\%15. (%3 (\%24. (%3 (\%25. (%3 (\%4. (%3 (\%5. ((%19
       ((%6 ((%9 $3) $2)) ((((%7 $5) $4) $1) $0))) ((%30 ((%29 $4) ((%29 $1)
       $0))) ((%29 $3) $2)))))))))))))))`)
  val parts_have_prop =
    DT("", [],
       `(%1 (\%2. (%3 (\%15. (%3 (\%31. (%3 (\%32. (%3 (\%4. (%3 (\%5. ((%19
       ((%0 ((%6 ((%9 $3) $2)) ((((%7 $5) $4) $1) $0))) ((%0 (%10 (\%26. ((%19
       ((%28 $0) $2)) ($6 $0))))) (%10 (\%26. ((%19 ((%28 $0) $1)) (%33 ($6
       $0)))))))) ((%0 (%10 (\%34. ((%19 ((%28 $0) $4)) ($6 $0))))) (%10
       (\%34. ((%19 ((%28 $0) $3)) (%33 ($6 $0)))))))))))))))))))`)
  end
  val _ = DB.bindl "part"
  [("part_def",part_def,DB.Def), ("partition_def",partition_def,DB.Def),
   ("part_length",part_length,DB.Thm),
   ("part_length_lem",part_length_lem,DB.Thm), ("part_mem",part_mem,DB.Thm),
   ("part_perm_lem",part_perm_lem,DB.Thm),
   ("parts_have_prop",parts_have_prop,DB.Thm)]
  
  
end
