structure HSL2CFLTheory :> HSL2CFLTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading HSL2CFLTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open HSLTheory bigInstTheory
  in end;
  val _ = Theory.link_parents
          ("HSL2CFL",
          Arbnum.fromString "1163556657",
          Arbnum.fromString "643367")
          [("bigInst",
           Arbnum.fromString "1163556424",
           Arbnum.fromString "258382"),
           ("HSL",
           Arbnum.fromString "1163548760",
           Arbnum.fromString "851649")];
  val _ = Theory.incorporate_types "HSL2CFL" [];
  val _ = Theory.incorporate_consts "HSL2CFL"
     [("correspond",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> (T"num" "num" [] --> bool))))),
      ("translate_assgn",((T"TOPER" "HSL" [] --> T"DOPER" "CFL" []))),
      ("same_base_regs",((T"HSL_STRUCTURE" "HSL" [] --> bool))),
      ("sem_preserve",((T"HSL_STRUCTURE" "HSL" [] --> bool))),
      ("translate_TCND",
       ((T"prod" "pair"
          [T"TREG" "HSL" [], T"prod" "pair" [alpha, T"TROC" "HSL" []]] -->
         T"prod" "pair"
          [T"MREG" "CFL" [], T"prod" "pair" [alpha, T"MEXP" "CFL" []]]))),
      ("conv_roc",((T"TROC" "HSL" [] --> T"MEXP" "CFL" []))),
      ("translate_hsl",
       ((T"HSL_STRUCTURE" "HSL" [] --> T"CTL_STRUCTURE" "CFL" []))),
      ("toLocn",
       ((T"num" "num" [] -->
         T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]))),
      ("Well_Formed",((T"HSL_STRUCTURE" "HSL" [] --> bool)))];
  
  local
  val share_table = Vector.fromList
  [C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"TREG" "HSL" [] --> bool) --> bool)),
   V"r" (T"TREG" "HSL" []),
   C"=" "min" ((T"MEXP" "CFL" [] --> (T"MEXP" "CFL" [] --> bool))),
   C"conv_roc" "HSL2CFL" ((T"TROC" "HSL" [] --> T"MEXP" "CFL" [])),
   C"Rg" "HSL" ((T"TREG" "HSL" [] --> T"TROC" "HSL" [])),
   C"MR" "CFL" ((T"MREG" "CFL" [] --> T"MEXP" "CFL" [])),
   C"conv_reg" "HSL" ((T"TREG" "HSL" [] --> T"MREG" "CFL" [])),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"v" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"Cn" "HSL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TROC" "HSL" [])),
   C"MC" "CFL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" [])),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"i" (T"num" "num" []),
   C"=" "min"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool))),
   C"toLocn" "HSL2CFL"
    ((T"num" "num" [] -->
      T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []])),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"OFFSET" "preARM" [] -->
       T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]))),
   C"fp" "CFL" (T"num" "num" []),
   C"NEG" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"=" "min"
    (((T"TOPER" "HSL" [] --> T"DOPER" "CFL" []) -->
      ((T"TOPER" "HSL" [] --> T"DOPER" "CFL" []) --> bool))),
   C"translate_assgn" "HSL2CFL"
    ((T"TOPER" "HSL" [] --> T"DOPER" "CFL" [])),
   C"WFREC" "relation"
    (((T"TOPER" "HSL" [] --> (T"TOPER" "HSL" [] --> bool)) -->
      (((T"TOPER" "HSL" [] --> T"DOPER" "CFL" []) -->
        (T"TOPER" "HSL" [] --> T"DOPER" "CFL" [])) -->
       (T"TOPER" "HSL" [] --> T"DOPER" "CFL" [])))),
   C"@" "min"
    ((((T"TOPER" "HSL" [] --> (T"TOPER" "HSL" [] --> bool)) --> bool) -->
      (T"TOPER" "HSL" [] --> (T"TOPER" "HSL" [] --> bool)))),
   V"R" ((T"TOPER" "HSL" [] --> (T"TOPER" "HSL" [] --> bool))),
   C"WF" "relation"
    (((T"TOPER" "HSL" [] --> (T"TOPER" "HSL" [] --> bool)) --> bool)),
   V"translate_assgn" ((T"TOPER" "HSL" [] --> T"DOPER" "CFL" [])),
   V"a" (T"TOPER" "HSL" []),
   C"TOPER_case" "HSL"
    (((T"TREG" "HSL" [] --> (T"num" "num" [] --> T"DOPER" "CFL" [])) -->
      ((T"num" "num" [] --> (T"TREG" "HSL" [] --> T"DOPER" "CFL" [])) -->
       ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> T"DOPER" "CFL" [])) -->
        ((T"TREG" "HSL" [] -->
          (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"DOPER" "CFL" [])))
         -->
         ((T"TREG" "HSL" [] -->
           (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"DOPER" "CFL" [])))
          -->
          ((T"TREG" "HSL" [] -->
            (T"TROC" "HSL" [] -->
             (T"TROC" "HSL" [] --> T"DOPER" "CFL" []))) -->
           ((T"TREG" "HSL" [] -->
             (T"TROC" "HSL" [] -->
              (T"TROC" "HSL" [] --> T"DOPER" "CFL" []))) -->
            ((T"TREG" "HSL" [] -->
              (T"TROC" "HSL" [] -->
               (T"TROC" "HSL" [] --> T"DOPER" "CFL" []))) -->
             ((T"TREG" "HSL" [] -->
               (T"TROC" "HSL" [] -->
                (T"TROC" "HSL" [] --> T"DOPER" "CFL" []))) -->
              ((T"TREG" "HSL" [] -->
                (T"TROC" "HSL" [] -->
                 (T"TROC" "HSL" [] --> T"DOPER" "CFL" []))) -->
               ((T"TREG" "HSL" [] -->
                 (T"TROC" "HSL" [] -->
                  (T"cart" "fcp" [bool, T"i5" "words" []] -->
                   T"DOPER" "CFL" []))) -->
                ((T"TREG" "HSL" [] -->
                  (T"TROC" "HSL" [] -->
                   (T"cart" "fcp" [bool, T"i5" "words" []] -->
                    T"DOPER" "CFL" []))) -->
                 ((T"TREG" "HSL" [] -->
                   (T"TROC" "HSL" [] -->
                    (T"cart" "fcp" [bool, T"i5" "words" []] -->
                     T"DOPER" "CFL" []))) -->
                  ((T"TREG" "HSL" [] -->
                    (T"TROC" "HSL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] -->
                      T"DOPER" "CFL" []))) -->
                   (T"TOPER" "HSL" [] -->
                    T"DOPER" "CFL" [])))))))))))))))),
   V"dst_reg" (T"TREG" "HSL" []), V"src_mem" (T"num" "num" []),
   C"I" "combin" ((T"DOPER" "CFL" [] --> T"DOPER" "CFL" [])),
   C"MLDR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"DOPER" "CFL" []))), V"dst_mem" (T"num" "num" []),
   V"src_reg" (T"TREG" "HSL" []),
   C"MSTR" "CFL"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "CFL" [] --> T"DOPER" "CFL" []))),
   V"dst" (T"TREG" "HSL" []), V"src" (T"TROC" "HSL" []),
   C"MMOV" "CFL"
    ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))),
   V"dst'" (T"TREG" "HSL" []), V"v10" (T"TROC" "HSL" []),
   V"src'" (T"TROC" "HSL" []),
   C"TROC_case" "HSL"
    (((T"TREG" "HSL" [] --> T"DOPER" "CFL" []) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"DOPER" "CFL" []) -->
       (T"TROC" "HSL" [] --> T"DOPER" "CFL" [])))),
   C"MADD" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   V"r'" (T"TREG" "HSL" []),
   V"v2" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_add" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"dst''" (T"TREG" "HSL" []), V"v13" (T"TROC" "HSL" []),
   V"src''" (T"TROC" "HSL" []), V"r''" (T"TREG" "HSL" []),
   C"MSUB" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   V"v'" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"r'''" (T"TREG" "HSL" []),
   C"MRSB" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   V"v2'" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_sub" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"dst'''" (T"TREG" "HSL" []), V"v16" (T"TROC" "HSL" []),
   V"src'''" (T"TROC" "HSL" []), V"r''''" (T"TREG" "HSL" []),
   V"v''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"r'''''" (T"TREG" "HSL" []),
   V"v2''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"dst''''" (T"TREG" "HSL" []), V"v19" (T"TROC" "HSL" []),
   V"src''''" (T"TROC" "HSL" []), V"r''''''" (T"TREG" "HSL" []),
   C"MMUL" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   V"v'''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"r'''''''" (T"TREG" "HSL" []),
   V"v2'''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_mul" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"dst'''''" (T"TREG" "HSL" []), V"v22" (T"TROC" "HSL" []),
   V"src'''''" (T"TROC" "HSL" []), V"r''''''''" (T"TREG" "HSL" []),
   C"MAND" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   V"v''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"r'''''''''" (T"TREG" "HSL" []),
   V"v2''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_and" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"dst''''''" (T"TREG" "HSL" []), V"v25" (T"TROC" "HSL" []),
   V"src''''''" (T"TROC" "HSL" []), V"r''''''''''" (T"TREG" "HSL" []),
   C"MORR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   V"v'''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"r'''''''''''" (T"TREG" "HSL" []),
   V"v2'''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_or" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"dst'''''''" (T"TREG" "HSL" []), V"v28" (T"TROC" "HSL" []),
   V"src'''''''" (T"TROC" "HSL" []), V"r''''''''''''" (T"TREG" "HSL" []),
   C"MEOR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   V"v''''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"r'''''''''''''" (T"TREG" "HSL" []),
   V"v2''''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_xor" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"dst''''''''" (T"TREG" "HSL" []), V"v31" (T"TROC" "HSL" []),
   V"src2_num" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"r''''''''''''''" (T"TREG" "HSL" []),
   C"MLSL" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   V"v'''''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_lsl" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"w2n" "words"
    ((T"cart" "fcp" [bool, T"i5" "words" []] --> T"num" "num" [])),
   V"dst'''''''''" (T"TREG" "HSL" []), V"v34" (T"TROC" "HSL" []),
   V"src2_num'" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"r'''''''''''''''" (T"TREG" "HSL" []),
   C"MLSR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   V"v''''''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_lsr" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"dst''''''''''" (T"TREG" "HSL" []), V"v37" (T"TROC" "HSL" []),
   V"src2_num''" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"r''''''''''''''''" (T"TREG" "HSL" []),
   C"MASR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   V"v'''''''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_asr" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"dst'''''''''''" (T"TREG" "HSL" []), V"v40" (T"TROC" "HSL" []),
   V"src2_num'''" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"r'''''''''''''''''" (T"TREG" "HSL" []),
   C"MROR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   V"v''''''''''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_ror" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"!" "bool" (((alpha --> bool) --> bool)), V"c" (alpha),
   C"!" "bool" (((T"TROC" "HSL" [] --> bool) --> bool)),
   V"e" (T"TROC" "HSL" []),
   C"=" "min"
    ((T"prod" "pair"
       [T"MREG" "CFL" [], T"prod" "pair" [alpha, T"MEXP" "CFL" []]] -->
      (T"prod" "pair"
        [T"MREG" "CFL" [], T"prod" "pair" [alpha, T"MEXP" "CFL" []]] -->
       bool))),
   C"translate_TCND" "HSL2CFL"
    ((T"prod" "pair"
       [T"TREG" "HSL" [], T"prod" "pair" [alpha, T"TROC" "HSL" []]] -->
      T"prod" "pair"
       [T"MREG" "CFL" [], T"prod" "pair" [alpha, T"MEXP" "CFL" []]])),
   C"," "pair"
    ((T"TREG" "HSL" [] -->
      (T"prod" "pair" [alpha, T"TROC" "HSL" []] -->
       T"prod" "pair"
        [T"TREG" "HSL" [], T"prod" "pair" [alpha, T"TROC" "HSL" []]]))),
   C"," "pair"
    ((alpha -->
      (T"TROC" "HSL" [] --> T"prod" "pair" [alpha, T"TROC" "HSL" []]))),
   C"," "pair"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair" [alpha, T"MEXP" "CFL" []] -->
       T"prod" "pair"
        [T"MREG" "CFL" [], T"prod" "pair" [alpha, T"MEXP" "CFL" []]]))),
   C"," "pair"
    ((alpha -->
      (T"MEXP" "CFL" [] --> T"prod" "pair" [alpha, T"MEXP" "CFL" []]))),
   C"!" "bool" (((T"list" "list" [T"TOPER" "HSL" []] --> bool) --> bool)),
   V"stmL" (T"list" "list" [T"TOPER" "HSL" []]),
   C"=" "min"
    ((T"CTL_STRUCTURE" "CFL" [] --> (T"CTL_STRUCTURE" "CFL" [] --> bool))),
   C"translate_hsl" "HSL2CFL"
    ((T"HSL_STRUCTURE" "HSL" [] --> T"CTL_STRUCTURE" "CFL" [])),
   C"Blk" "HSL"
    ((T"list" "list" [T"TOPER" "HSL" []] --> T"HSL_STRUCTURE" "HSL" [])),
   C"BLK" "CFL"
    ((T"list" "list" [T"DOPER" "CFL" []] --> T"CTL_STRUCTURE" "CFL" [])),
   C"MAP" "list"
    (((T"TOPER" "HSL" [] --> T"DOPER" "CFL" []) -->
      (T"list" "list" [T"TOPER" "HSL" []] -->
       T"list" "list" [T"DOPER" "CFL" []]))),
   C"!" "bool" (((T"HSL_STRUCTURE" "HSL" [] --> bool) --> bool)),
   V"S1" (T"HSL_STRUCTURE" "HSL" []), V"S2" (T"HSL_STRUCTURE" "HSL" []),
   C"Sc" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))),
   C"SC" "CFL"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))),
   C"!" "bool"
    (((T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] --> bool)
      --> bool)),
   V"cond"
    (T"prod" "pair"
      [T"TREG" "HSL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]]),
   V"Strue" (T"HSL_STRUCTURE" "HSL" []),
   V"Sfalse" (T"HSL_STRUCTURE" "HSL" []),
   C"Cj" "HSL"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])))),
   C"CJ" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] -->
       (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])))),
   C"translate_TCND" "HSL2CFL"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]])),
   V"Sbody" (T"HSL_STRUCTURE" "HSL" []),
   C"Tr" "HSL"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))),
   C"TR" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))),
   C"!" "bool"
    (((T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool) --> bool)),
   V"rg"
    (T"fmap" "finite_map"
      [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"!" "bool"
    (((T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool) --> bool)),
   V"sk"
    (T"fmap" "finite_map"
      [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"!" "bool"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) --> bool)),
   V"st"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"m" (T"num" "num" []), C"=" "min" ((bool --> (bool --> bool))),
   C"correspond" "HSL2CFL"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"num" "num" [] --> bool)))),
   C"," "pair"
    ((T"fmap" "finite_map"
       [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"FAPPLY" "finite_map"
    ((T"fmap" "finite_map"
       [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"TREG" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"read" "preARM"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"EXP" "preARM" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"REG" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   C"data_reg_index" "HSL" ((T"TREG" "HSL" [] --> T"num" "num" [])),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"FAPPLY" "finite_map"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"MEM" "preARM"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"EXP" "preARM" [])), V"S_hsl" (T"HSL_STRUCTURE" "HSL" []),
   C"same_base_regs" "HSL2CFL" ((T"HSL_STRUCTURE" "HSL" [] --> bool)),
   C"LET" "bool"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   V"st'"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"FP" "preARM" (T"EXP" "preARM" []),
   C"IP" "preARM" (T"EXP" "preARM" []),
   C"SP" "preARM" (T"EXP" "preARM" []),
   C"LR" "preARM" (T"EXP" "preARM" []),
   C"run_cfl" "CFL"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"Well_Formed" "HSL2CFL" ((T"HSL_STRUCTURE" "HSL" [] --> bool)),
   C"WELL_FORMED" "CFL" ((T"CTL_STRUCTURE" "CFL" [] --> bool)),
   C"sem_preserve" "HSL2CFL" ((T"HSL_STRUCTURE" "HSL" [] --> bool)),
   C"!" "bool"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) --> bool)),
   V"s"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"run_hsl" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"!" "bool" ((((T"TOPER" "HSL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"TOPER" "HSL" [] --> bool)),
   C"TLDR" "HSL"
    ((T"TREG" "HSL" [] --> (T"num" "num" [] --> T"TOPER" "HSL" []))),
   C"TSTR" "HSL"
    ((T"num" "num" [] --> (T"TREG" "HSL" [] --> T"TOPER" "HSL" []))),
   C"TMOV" "HSL"
    ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))),
   C"TADD" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   V"v1" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"TSUB" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"TRSB" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"TMUL" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"TAND" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"TORR" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"TEOR" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i5" "words" []] --> bool) --> bool)),
   C"TLSL" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))),
   C"TLSR" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))),
   C"TASR" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))),
   C"TROR" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))),
   C"!" "bool" (((T"TOPER" "HSL" [] --> bool) --> bool)),
   V"v" (T"TOPER" "HSL" []),
   C"=" "min" ((T"DOPER" "CFL" [] --> (T"DOPER" "CFL" [] --> bool))),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"index_of_reg" "CFL" ((T"MREG" "CFL" [] --> T"num" "num" [])),
   C"=" "min" ((T"TREG" "HSL" [] --> (T"TREG" "HSL" [] --> bool))),
   C"~" "bool" ((bool --> bool)),
   V"x" (T"cart" "fcp" [bool, T"i32" "words" []]), V"k" (T"num" "num" []),
   C"locate_ge" "bigInst"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> bool))), V"j" (T"num" "num" []),
   C"-" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"w2n" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"num" "num" [])),
   V"T'" (T"TREG" "HSL" []), V"T0" (T"num" "num" []),
   C"valid_assgn" "HSL"
    ((T"TOPER" "HSL" [] --> (T"num" "num" [] --> bool))),
   C"tdecode" "HSL"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"TOPER" "HSL" [] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"mdecode" "CFL"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"DOPER" "CFL" [] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   V"T'" (T"num" "num" []), V"T0" (T"TREG" "HSL" []),
   V"stm" (T"TOPER" "HSL" []),
   C"valid_struct" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] --> (T"num" "num" [] --> bool))),
   V"stm" (alpha), V"m" (alpha),
   C"=" "min" ((T"EXP" "preARM" [] --> (T"EXP" "preARM" [] --> bool))),
   C"toREG" "CFL" ((T"MREG" "CFL" [] --> T"EXP" "preARM" [])),
   C"eval_TCND" "HSL"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   C"eval_il_cond" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool)))]
  val DT = Thm.disk_thm share_table
  in
  val conv_roc_def =
    DT(["DISK_THM"], [],
       `((%0 (%1 (\%2. ((%3 (%4 (%5 $0))) (%6 (%7 $0)))))) (%8 (\%9. ((%3
       (%4 (%10 $0))) (%11 $0)))))`)
  val toLocn_def =
    DT([], [],
       `(%12 (\%13. ((%14 (%15 $0)) ((%16 %17) (%18 ((%19 (%20 (%21 (%22
       (%21 %23))))) $0))))))`)
  val translate_assgn_primitive_def =
    DT([], [],
       `((%24 %25) ((%26 (%27 (\%28. (%29 $0)))) (\%30. (\%31.
       (((((((((((((((%32 (\%33. (\%34. (%35 ((%36 (%7 $1)) (%15 $0))))))
       (\%37. (\%38. (%35 ((%39 (%15 $1)) (%7 $0)))))) (\%40. (\%41. (%35
       ((%42 (%7 $1)) (%4 $0)))))) (\%43. (\%44. (\%45. (((%46 (\%2. (%35
       (((%47 (%7 $3)) (%7 $0)) (%4 $1))))) (\%9. (((%46 (\%48. (%35 (((%47
       (%7 $4)) (%7 $0)) (%11 $1))))) (\%49. (%35 ((%42 (%7 $4)) (%11 ((%50
       $1) $0)))))) $1))) $1))))) (\%51. (\%52. (\%53. (((%46 (\%54. (%35
       (((%55 (%7 $3)) (%7 $0)) (%4 $1))))) (\%56. (((%46 (\%57. (%35
       (((%58 (%7 $4)) (%7 $0)) (%11 $1))))) (\%59. (%35 ((%42 (%7 $4))
       (%11 ((%60 $1) $0)))))) $1))) $1))))) (\%61. (\%62. (\%63. (((%46
       (\%64. (%35 (((%58 (%7 $3)) (%7 $0)) (%4 $1))))) (\%65. (((%46
       (\%66. (%35 (((%55 (%7 $4)) (%7 $0)) (%11 $1))))) (\%67. (%35 ((%42
       (%7 $4)) (%11 ((%60 $0) $1)))))) $1))) $1))))) (\%68. (\%69. (\%70.
       (((%46 (\%71. (%35 (((%72 (%7 $3)) (%7 $0)) (%4 $1))))) (\%73.
       (((%46 (\%74. (%35 (((%72 (%7 $4)) (%7 $0)) (%11 $1))))) (\%75. (%35
       ((%42 (%7 $4)) (%11 ((%76 $1) $0)))))) $1))) $1))))) (\%77. (\%78.
       (\%79. (((%46 (\%80. (%35 (((%81 (%7 $3)) (%7 $0)) (%4 $1)))))
       (\%82. (((%46 (\%83. (%35 (((%81 (%7 $4)) (%7 $0)) (%11 $1)))))
       (\%84. (%35 ((%42 (%7 $4)) (%11 ((%85 $1) $0)))))) $1))) $1)))))
       (\%86. (\%87. (\%88. (((%46 (\%89. (%35 (((%90 (%7 $3)) (%7 $0)) (%4
       $1))))) (\%91. (((%46 (\%92. (%35 (((%90 (%7 $4)) (%7 $0)) (%11
       $1))))) (\%93. (%35 ((%42 (%7 $4)) (%11 ((%94 $1) $0)))))) $1)))
       $1))))) (\%95. (\%96. (\%97. (((%46 (\%98. (%35 (((%99 (%7 $3)) (%7
       $0)) (%4 $1))))) (\%100. (((%46 (\%101. (%35 (((%99 (%7 $4)) (%7
       $0)) (%11 $1))))) (\%102. (%35 ((%42 (%7 $4)) (%11 ((%103 $1)
       $0)))))) $1))) $1))))) (\%104. (\%105. (\%106. (((%46 (\%107. (%35
       (((%108 (%7 $3)) (%7 $0)) $1)))) (\%109. (%35 ((%42 (%7 $3)) (%11
       ((%110 $0) (%111 $1))))))) $1))))) (\%112. (\%113. (\%114. (((%46
       (\%115. (%35 (((%116 (%7 $3)) (%7 $0)) $1)))) (\%117. (%35 ((%42 (%7
       $3)) (%11 ((%118 $0) (%111 $1))))))) $1))))) (\%119. (\%120. (\%121.
       (((%46 (\%122. (%35 (((%123 (%7 $3)) (%7 $0)) $1)))) (\%124. (%35
       ((%42 (%7 $3)) (%11 ((%125 $0) (%111 $1))))))) $1))))) (\%126.
       (\%127. (\%128. (((%46 (\%129. (%35 (((%130 (%7 $3)) (%7 $0)) $1))))
       (\%131. (%35 ((%42 (%7 $3)) (%11 ((%132 $0) (%111 $1))))))) $1)))))
       $0)))))`)
  val translate_TCND_def =
    DT(["DISK_THM"], [],
       `(%1 (\%2. (%133 (\%134. (%135 (\%136. ((%137 (%138 ((%139 $2)
       ((%140 $1) $0)))) ((%141 (%7 $2)) ((%142 $1) (%4 $0))))))))))`)
  val translate_hsl_def =
    DT(["DISK_THM"], [],
       `((%0 (%143 (\%144. ((%145 (%146 (%147 $0))) (%148 ((%149 %25)
       $0)))))) ((%0 (%150 (\%151. (%150 (\%152. ((%145 (%146 ((%153 $1)
       $0))) ((%154 (%146 $1)) (%146 $0)))))))) ((%0 (%155 (\%156. (%150
       (\%157. (%150 (\%158. ((%145 (%146 (((%159 $2) $1) $0))) (((%160
       (%161 $2)) (%146 $1)) (%146 $0)))))))))) (%155 (\%156. (%150 (\%162.
       ((%145 (%146 ((%163 $1) $0))) ((%164 (%161 $1)) (%146 $0))))))))))`)
  val correspond_def =
    DT(["DISK_THM"], [],
       `(%165 (\%166. (%167 (\%168. (%169 (\%170. (%12 (\%171. ((%172
       (((%173 ((%174 $3) $2)) $1) $0)) ((%0 (%1 (\%2. ((%175 ((%176 $4)
       $0)) ((%177 $2) (%178 (%179 $0))))))) (%12 (\%13. ((%180 ((%181 $0)
       $1)) ((%175 ((%182 $3) $0)) ((%177 $2) (%183 (%15
       $0)))))))))))))))))`)
  val same_base_regs_def =
    DT([], [],
       `(%150 (\%184. ((%172 (%185 $0)) (%169 (\%170. ((%186 (\%187. ((%0
       ((%175 ((%177 $1) %188)) ((%177 $0) %188))) ((%0 ((%175 ((%177 $1)
       %189)) ((%177 $0) %189))) ((%0 ((%175 ((%177 $1) %190)) ((%177 $0)
       %190))) ((%175 ((%177 $1) %191)) ((%177 $0) %191))))))) ((%192 (%146
       $1)) $0)))))))`)
  val Well_Formed_def =
    DT([], [], `(%150 (\%184. ((%172 (%193 $0)) (%194 (%146 $0)))))`)
  val sem_preserve_def =
    DT([], [],
       `(%150 (\%184. ((%172 (%195 $0)) (%196 (\%197. (%169 (\%170. (%12
       (\%171. ((%180 (((%173 $2) $1) $0)) (((%173 ((%198 $3) $2)) ((%192
       (%146 $3)) $1)) $0)))))))))))`)
  val translate_assgn_ind =
    DT(["DISK_THM"], [],
       `(%199 (\%200. ((%180 ((%0 (%1 (\%33. (%12 (\%34. ($2 ((%201 $1)
       $0))))))) ((%0 (%12 (\%37. (%1 (\%38. ($2 ((%202 $1) $0))))))) ((%0
       (%1 (\%40. (%135 (\%41. ($2 ((%203 $1) $0))))))) ((%0 (%1 (\%40. (%1
       (\%2. (%135 (\%41. ($3 (((%204 $2) (%5 $1)) $0))))))))) ((%0 (%1
       (\%40. (%8 (\%9. (%1 (\%2. ($3 (((%204 $2) (%10 $1)) (%5
       $0)))))))))) ((%0 (%1 (\%40. (%8 (\%205. (%8 (\%49. ($3 (((%204 $2)
       (%10 $1)) (%10 $0)))))))))) ((%0 (%1 (\%40. (%1 (\%2. (%135 (\%41.
       ($3 (((%206 $2) (%5 $1)) $0))))))))) ((%0 (%1 (\%40. (%8 (\%9. (%1
       (\%2. ($3 (((%206 $2) (%10 $1)) (%5 $0)))))))))) ((%0 (%1 (\%40. (%8
       (\%205. (%8 (\%49. ($3 (((%206 $2) (%10 $1)) (%10 $0)))))))))) ((%0
       (%1 (\%40. (%1 (\%2. (%135 (\%41. ($3 (((%207 $2) (%5 $1))
       $0))))))))) ((%0 (%1 (\%40. (%8 (\%9. (%1 (\%2. ($3 (((%207 $2) (%10
       $1)) (%5 $0)))))))))) ((%0 (%1 (\%40. (%8 (\%205. (%8 (\%49. ($3
       (((%207 $2) (%10 $1)) (%10 $0)))))))))) ((%0 (%1 (\%40. (%1 (\%2.
       (%135 (\%41. ($3 (((%208 $2) (%5 $1)) $0))))))))) ((%0 (%1 (\%40.
       (%8 (\%9. (%1 (\%2. ($3 (((%208 $2) (%10 $1)) (%5 $0)))))))))) ((%0
       (%1 (\%40. (%8 (\%205. (%8 (\%49. ($3 (((%208 $2) (%10 $1)) (%10
       $0)))))))))) ((%0 (%1 (\%40. (%1 (\%2. (%135 (\%41. ($3 (((%209 $2)
       (%5 $1)) $0))))))))) ((%0 (%1 (\%40. (%8 (\%9. (%1 (\%2. ($3 (((%209
       $2) (%10 $1)) (%5 $0)))))))))) ((%0 (%1 (\%40. (%8 (\%205. (%8
       (\%49. ($3 (((%209 $2) (%10 $1)) (%10 $0)))))))))) ((%0 (%1 (\%40.
       (%1 (\%2. (%135 (\%41. ($3 (((%210 $2) (%5 $1)) $0))))))))) ((%0 (%1
       (\%40. (%8 (\%9. (%1 (\%2. ($3 (((%210 $2) (%10 $1)) (%5
       $0)))))))))) ((%0 (%1 (\%40. (%8 (\%205. (%8 (\%49. ($3 (((%210 $2)
       (%10 $1)) (%10 $0)))))))))) ((%0 (%1 (\%40. (%1 (\%2. (%135 (\%41.
       ($3 (((%211 $2) (%5 $1)) $0))))))))) ((%0 (%1 (\%40. (%8 (\%9. (%1
       (\%2. ($3 (((%211 $2) (%10 $1)) (%5 $0)))))))))) ((%0 (%1 (\%40. (%8
       (\%205. (%8 (\%49. ($3 (((%211 $2) (%10 $1)) (%10 $0)))))))))) ((%0
       (%1 (\%40. (%1 (\%2. (%212 (\%106. ($3 (((%213 $2) (%5 $1))
       $0))))))))) ((%0 (%1 (\%40. (%8 (\%9. (%212 (\%106. ($3 (((%213 $2)
       (%10 $1)) $0))))))))) ((%0 (%1 (\%40. (%1 (\%2. (%212 (\%106. ($3
       (((%214 $2) (%5 $1)) $0))))))))) ((%0 (%1 (\%40. (%8 (\%9. (%212
       (\%106. ($3 (((%214 $2) (%10 $1)) $0))))))))) ((%0 (%1 (\%40. (%1
       (\%2. (%212 (\%106. ($3 (((%215 $2) (%5 $1)) $0))))))))) ((%0 (%1
       (\%40. (%8 (\%9. (%212 (\%106. ($3 (((%215 $2) (%10 $1)) $0)))))))))
       ((%0 (%1 (\%40. (%1 (\%2. (%212 (\%106. ($3 (((%216 $2) (%5 $1))
       $0))))))))) (%1 (\%40. (%8 (\%9. (%212 (\%106. ($3 (((%216 $2) (%10
       $1)) $0)))))))))))))))))))))))))))))))))))))))) (%217 (\%218. ($1
       $0))))))`)
  val translate_assgn_def =
    DT(["DISK_THM"], [],
       `((%0 ((%219 (%25 ((%201 %33) %34))) ((%36 (%7 %33)) (%15 %34))))
       ((%0 ((%219 (%25 ((%202 %37) %38))) ((%39 (%15 %37)) (%7 %38))))
       ((%0 ((%219 (%25 ((%203 %40) %41))) ((%42 (%7 %40)) (%4 %41)))) ((%0
       ((%219 (%25 (((%204 %40) (%5 %2)) %41))) (((%47 (%7 %40)) (%7 %2))
       (%4 %41)))) ((%0 ((%219 (%25 (((%204 %40) (%10 %9)) (%5 %2))))
       (((%47 (%7 %40)) (%7 %2)) (%11 %9)))) ((%0 ((%219 (%25 (((%204 %40)
       (%10 %205)) (%10 %49)))) ((%42 (%7 %40)) (%11 ((%50 %205) %49)))))
       ((%0 ((%219 (%25 (((%206 %40) (%5 %2)) %41))) (((%55 (%7 %40)) (%7
       %2)) (%4 %41)))) ((%0 ((%219 (%25 (((%206 %40) (%10 %9)) (%5 %2))))
       (((%58 (%7 %40)) (%7 %2)) (%11 %9)))) ((%0 ((%219 (%25 (((%206 %40)
       (%10 %205)) (%10 %49)))) ((%42 (%7 %40)) (%11 ((%60 %205) %49)))))
       ((%0 ((%219 (%25 (((%207 %40) (%5 %2)) %41))) (((%58 (%7 %40)) (%7
       %2)) (%4 %41)))) ((%0 ((%219 (%25 (((%207 %40) (%10 %9)) (%5 %2))))
       (((%55 (%7 %40)) (%7 %2)) (%11 %9)))) ((%0 ((%219 (%25 (((%207 %40)
       (%10 %205)) (%10 %49)))) ((%42 (%7 %40)) (%11 ((%60 %49) %205)))))
       ((%0 ((%219 (%25 (((%208 %40) (%5 %2)) %41))) (((%72 (%7 %40)) (%7
       %2)) (%4 %41)))) ((%0 ((%219 (%25 (((%208 %40) (%10 %9)) (%5 %2))))
       (((%72 (%7 %40)) (%7 %2)) (%11 %9)))) ((%0 ((%219 (%25 (((%208 %40)
       (%10 %205)) (%10 %49)))) ((%42 (%7 %40)) (%11 ((%76 %205) %49)))))
       ((%0 ((%219 (%25 (((%209 %40) (%5 %2)) %41))) (((%81 (%7 %40)) (%7
       %2)) (%4 %41)))) ((%0 ((%219 (%25 (((%209 %40) (%10 %9)) (%5 %2))))
       (((%81 (%7 %40)) (%7 %2)) (%11 %9)))) ((%0 ((%219 (%25 (((%209 %40)
       (%10 %205)) (%10 %49)))) ((%42 (%7 %40)) (%11 ((%85 %205) %49)))))
       ((%0 ((%219 (%25 (((%210 %40) (%5 %2)) %41))) (((%90 (%7 %40)) (%7
       %2)) (%4 %41)))) ((%0 ((%219 (%25 (((%210 %40) (%10 %9)) (%5 %2))))
       (((%90 (%7 %40)) (%7 %2)) (%11 %9)))) ((%0 ((%219 (%25 (((%210 %40)
       (%10 %205)) (%10 %49)))) ((%42 (%7 %40)) (%11 ((%94 %205) %49)))))
       ((%0 ((%219 (%25 (((%211 %40) (%5 %2)) %41))) (((%99 (%7 %40)) (%7
       %2)) (%4 %41)))) ((%0 ((%219 (%25 (((%211 %40) (%10 %9)) (%5 %2))))
       (((%99 (%7 %40)) (%7 %2)) (%11 %9)))) ((%0 ((%219 (%25 (((%211 %40)
       (%10 %205)) (%10 %49)))) ((%42 (%7 %40)) (%11 ((%103 %205) %49)))))
       ((%0 ((%219 (%25 (((%213 %40) (%5 %2)) %106))) (((%108 (%7 %40)) (%7
       %2)) %106))) ((%0 ((%219 (%25 (((%213 %40) (%10 %9)) %106))) ((%42
       (%7 %40)) (%11 ((%110 %9) (%111 %106)))))) ((%0 ((%219 (%25 (((%214
       %40) (%5 %2)) %106))) (((%116 (%7 %40)) (%7 %2)) %106))) ((%0 ((%219
       (%25 (((%214 %40) (%10 %9)) %106))) ((%42 (%7 %40)) (%11 ((%118 %9)
       (%111 %106)))))) ((%0 ((%219 (%25 (((%215 %40) (%5 %2)) %106)))
       (((%123 (%7 %40)) (%7 %2)) %106))) ((%0 ((%219 (%25 (((%215 %40)
       (%10 %9)) %106))) ((%42 (%7 %40)) (%11 ((%125 %9) (%111 %106))))))
       ((%0 ((%219 (%25 (((%216 %40) (%5 %2)) %106))) (((%130 (%7 %40)) (%7
       %2)) %106))) ((%219 (%25 (((%216 %40) (%10 %9)) %106))) ((%42 (%7
       %40)) (%11 ((%132 %9) (%111
       %106))))))))))))))))))))))))))))))))))))`)
  val data_reg_lem_1 =
    DT(["DISK_THM"], [], `(%1 (\%2. ((%220 (%221 (%7 $0))) (%179 $0))))`)
  val data_reg_lem_2 =
    DT(["DISK_THM"], [],
       `(%1 (\%2. (%1 (\%54. ((%172 ((%220 (%179 $1)) (%179 $0))) ((%222
       $1) $0))))))`)
  val data_reg_lem_3 =
    DT(["DISK_THM"], [],
       `(%1 (\%2. ((%0 ((%181 (%179 $0)) (%20 (%22 (%21 (%22 %23)))))) ((%0
       (%223 ((%220 (%179 $0)) (%20 (%21 (%21 (%22 %23))))))) ((%0 (%223
       ((%220 (%179 $0)) (%20 (%22 (%22 (%21 %23))))))) ((%0 (%223 ((%220
       (%179 $0)) (%20 (%21 (%22 (%21 %23))))))) ((%0 (%223 ((%220 (%179
       $0)) (%20 (%22 (%21 (%21 %23))))))) (%223 ((%220 (%179 $0)) (%20
       (%21 (%21 (%21 %23)))))))))))))`)
  val locate_ge_lem_3 =
    DT(["DISK_THM"], [],
       `(%8 (\%224. (%12 (\%225. ((%180 ((%226 $1) ((%19 (%20 (%21 (%22
       (%21 %23))))) $0))) (%12 (\%13. (%12 (\%227. ((%180 ((%0 (%223
       ((%220 $1) $0))) ((%0 ((%181 $1) $2)) ((%181 $0) $2)))) (%223 ((%220
       ((%228 (%229 $3)) ((%19 (%20 (%21 (%22 (%21 %23))))) $1))) ((%228
       (%229 $3)) ((%19 (%20 (%21 (%22 (%21 %23))))) $0))))))))))))))`)
  val LDR_CORRESPOND_LEM =
    DT(["DISK_THM"], [],
       `(%165 (\%166. (%167 (\%168. (%169 (\%170. (%1 (\%230. (%12 (\%231.
       (%12 (\%171. ((%180 ((%0 ((%232 ((%201 $2) $1)) $0)) (((%173 ((%174
       $5) $4)) $3) $0))) (((%173 ((%233 ((%174 $5) $4)) ((%201 $2) $1)))
       ((%234 $3) (%25 ((%201 $2) $1)))) $0))))))))))))))`)
  val STR_CORRESPOND_LEM =
    DT(["DISK_THM"], [],
       `(%165 (\%166. (%167 (\%168. (%169 (\%170. (%12 (\%235. (%1 (\%236.
       (%12 (\%171. ((%180 ((%0 ((%232 ((%202 $2) $1)) $0)) ((%0 ((%226
       ((%177 $3) %188)) ((%19 (%20 (%21 (%22 (%21 %23))))) $0))) (((%173
       ((%174 $5) $4)) $3) $0)))) (((%173 ((%233 ((%174 $5) $4)) ((%202 $2)
       $1))) ((%234 $3) (%25 ((%202 $2) $1)))) $0))))))))))))))`)
  val ASSGN_CORRESPOND =
    DT(["DISK_THM"], [],
       `(%165 (\%166. (%167 (\%168. (%169 (\%170. (%217 (\%237. (%12
       (\%171. ((%180 ((%0 ((%232 $1) $0)) ((%0 ((%226 ((%177 $2) %188))
       ((%19 (%20 (%21 (%22 (%21 %23))))) $0))) (((%173 ((%174 $4) $3)) $2)
       $0)))) (((%173 ((%233 ((%174 $4) $3)) $1)) ((%234 $2) (%25 $1)))
       $0))))))))))))`)
  val ASSGN_SAME_BASE_REGS =
    DT(["DISK_THM"], [],
       `(%217 (\%237. (%169 (\%170. ((%186 (\%187. ((%0 ((%175 ((%177 $1)
       %188)) ((%177 $0) %188))) ((%0 ((%175 ((%177 $1) %189)) ((%177 $0)
       %189))) ((%0 ((%175 ((%177 $1) %190)) ((%177 $0) %190))) ((%175
       ((%177 $1) %191)) ((%177 $0) %191))))))) ((%234 $0) (%25 $1)))))))`)
  val BLK_CORRESPONDENCE =
    DT(["DISK_THM"], [],
       `(%165 (\%166. (%167 (\%168. (%169 (\%170. (%143 (\%144. (%12
       (\%171. ((%180 ((%0 ((%238 (%147 $1)) $0)) ((%0 ((%226 ((%177 $2)
       %188)) ((%19 (%20 (%21 (%22 (%21 %23))))) $0))) (((%173 ((%174 $4)
       $3)) $2) $0)))) (((%173 ((%198 (%147 $1)) ((%174 $4) $3))) ((%192
       (%146 (%147 $1))) $2)) $0))))))))))))`)
  val BLK_SAME_BASE_REGS =
    DT(["DISK_THM"], [], `(%133 (\%239. (%185 (%147 %144))))`)
  val WELL_FORMED_SC =
    DT(["DISK_THM"], [],
       `(%150 (\%151. (%150 (\%152. ((%172 (%193 ((%153 $1) $0))) ((%0
       (%193 $1)) (%193 $0)))))))`)
  val SC_SEM_PRESERVE =
    DT(["DISK_THM"], [],
       `(%150 (\%151. (%150 (\%152. (%133 (\%240. ((%180 (%193 ((%153 $2)
       $1))) ((%180 ((%0 (%195 $2)) (%195 $1))) (%195 ((%153 $2)
       $1))))))))))`)
  val SC_SAME_BASE_REGS =
    DT(["DISK_THM"], [],
       `(%150 (\%151. (%150 (\%152. ((%180 ((%0 (%185 $1)) ((%0 (%185 $0))
       ((%0 (%193 $1)) (%193 $0))))) (%185 ((%153 $1) $0)))))))`)
  val conv_reg_lem_1 =
    DT(["DISK_THM"], [],
       `(%1 (\%2. ((%241 (%242 (%7 $0))) (%178 (%179 $0)))))`)
  val EVAL_TCND_THM =
    DT(["DISK_THM"], [],
       `(%155 (\%156. (%196 (\%197. (%169 (\%170. (%12 (\%171. ((%180
       (((%173 $2) $1) $0)) ((%172 ((%243 $3) $2)) ((%244 (%161 $3))
       $1)))))))))))`)
  val CJ_SEM_PRESERVE =
    DT(["DISK_THM"], [],
       `(%155 (\%156. (%150 (\%151. (%150 (\%152. ((%180 (%193 (((%159 $2)
       $1) $0))) ((%180 ((%0 (%195 $1)) (%195 $0))) (%195 (((%159 $2) $1)
       $0))))))))))`)
  end
  val _ = DB.bindl "HSL2CFL"
  [("conv_roc_def",conv_roc_def,DB.Def), ("toLocn_def",toLocn_def,DB.Def),
   ("translate_assgn_primitive_def",translate_assgn_primitive_def,DB.Def),
   ("translate_TCND_def",translate_TCND_def,DB.Def),
   ("translate_hsl_def",translate_hsl_def,DB.Def),
   ("correspond_def",correspond_def,DB.Def),
   ("same_base_regs_def",same_base_regs_def,DB.Def),
   ("Well_Formed_def",Well_Formed_def,DB.Def),
   ("sem_preserve_def",sem_preserve_def,DB.Def),
   ("translate_assgn_ind",translate_assgn_ind,DB.Thm),
   ("translate_assgn_def",translate_assgn_def,DB.Thm),
   ("data_reg_lem_1",data_reg_lem_1,DB.Thm),
   ("data_reg_lem_2",data_reg_lem_2,DB.Thm),
   ("data_reg_lem_3",data_reg_lem_3,DB.Thm),
   ("locate_ge_lem_3",locate_ge_lem_3,DB.Thm),
   ("LDR_CORRESPOND_LEM",LDR_CORRESPOND_LEM,DB.Thm),
   ("STR_CORRESPOND_LEM",STR_CORRESPOND_LEM,DB.Thm),
   ("ASSGN_CORRESPOND",ASSGN_CORRESPOND,DB.Thm),
   ("ASSGN_SAME_BASE_REGS",ASSGN_SAME_BASE_REGS,DB.Thm),
   ("BLK_CORRESPONDENCE",BLK_CORRESPONDENCE,DB.Thm),
   ("BLK_SAME_BASE_REGS",BLK_SAME_BASE_REGS,DB.Thm),
   ("WELL_FORMED_SC",WELL_FORMED_SC,DB.Thm),
   ("SC_SEM_PRESERVE",SC_SEM_PRESERVE,DB.Thm),
   ("SC_SAME_BASE_REGS",SC_SAME_BASE_REGS,DB.Thm),
   ("conv_reg_lem_1",conv_reg_lem_1,DB.Thm),
   ("EVAL_TCND_THM",EVAL_TCND_THM,DB.Thm),
   ("CJ_SEM_PRESERVE",CJ_SEM_PRESERVE,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("bigInstTheory.bigInst_grammars",
                          bigInstTheory.bigInst_grammars),
                         ("HSLTheory.HSL_grammars",HSLTheory.HSL_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "conv_roc")
        {Name = "conv_roc", Thy = "HSL2CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "toLocn")
        {Name = "toLocn", Thy = "HSL2CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "translate_assgn")
        {Name = "translate_assgn", Thy = "HSL2CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "translate_TCND")
        {Name = "translate_TCND", Thy = "HSL2CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "translate_hsl")
        {Name = "translate_hsl", Thy = "HSL2CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "correspond")
        {Name = "correspond", Thy = "HSL2CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "same_base_regs")
        {Name = "same_base_regs", Thy = "HSL2CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Well_Formed")
        {Name = "Well_Formed", Thy = "HSL2CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "sem_preserve")
        {Name = "sem_preserve", Thy = "HSL2CFL"}
  val HSL2CFL_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [conv_roc_def];  
  
  val _ = computeLib.add_funs [toLocn_def];  
  
  val _ = computeLib.add_funs [translate_assgn_def];  
  
  val _ = computeLib.add_funs [translate_TCND_def];  
  
  val _ = computeLib.add_funs [translate_hsl_def];  
  
  val _ = computeLib.add_funs [correspond_def];  
  
  val _ = computeLib.add_funs [same_base_regs_def];  
  
  val _ = computeLib.add_funs [Well_Formed_def];  
  
  val _ = computeLib.add_funs [sem_preserve_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
