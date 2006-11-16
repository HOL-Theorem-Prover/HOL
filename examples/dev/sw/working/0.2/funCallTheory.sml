structure funCallTheory :> funCallTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading funCallTheory ... " else ()
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
          ("funCall",
          Arbnum.fromString "1163561051",
          Arbnum.fromString "5786")
          [("bigInst",
           Arbnum.fromString "1163556424",
           Arbnum.fromString "258382"),
           ("HSL",
           Arbnum.fromString "1163548760",
           Arbnum.fromString "851649")];
  val _ = Theory.incorporate_types "funCall" [];
  val _ = Theory.incorporate_consts "funCall"
     [("same_content",
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
      ("standard_frame",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"num" "num" [] --> bool)))),
      ("mov_pointers",(T"list" "list" [T"DOPER" "CFL" []])),
      ("pre_call",
       ((T"prod" "pair"
          [T"list" "list" [T"CFL_EXP" "bigInst" []],
           T"list" "list" [T"CFL_EXP" "bigInst" []]] -->
         (T"num" "num" [] -->
          (T"num" "num" [] --> T"list" "list" [T"DOPER" "CFL" []]))))),
      ("valid_MEXP_1",
       ((T"CFL_EXP" "bigInst" [] --> (T"num" "num" [] --> bool)))),
      ("saved_regs_list",(T"list" "list" [T"CFL_EXP" "bigInst" []])),
      ("conv_exp",((T"TEXP" "HSL" [] --> T"CFL_EXP" "bigInst" []))),
      ("valid_MEXP",
       ((T"CFL_EXP" "bigInst" [] --> (T"num" "num" [] --> bool))))];
  
  local
  val share_table = Vector.fromList
  [C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"TREG" "HSL" [] --> bool) --> bool)),
   V"r" (T"TREG" "HSL" []),
   C"=" "min"
    ((T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool))),
   C"conv_exp" "funCall" ((T"TEXP" "HSL" [] --> T"CFL_EXP" "bigInst" [])),
   C"inR" "HSL" ((T"TREG" "HSL" [] --> T"TEXP" "HSL" [])),
   C"isR" "bigInst" ((T"num" "num" [] --> T"CFL_EXP" "bigInst" [])),
   C"data_reg_index" "HSL" ((T"TREG" "HSL" [] --> T"num" "num" [])),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"c" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"inC" "HSL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TEXP" "HSL" [])),
   C"isC" "bigInst"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      T"CFL_EXP" "bigInst" [])),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"v" (T"num" "num" []),
   C"inE" "HSL" ((T"num" "num" [] --> T"TEXP" "HSL" [])),
   C"isV" "bigInst" ((T"num" "num" [] --> T"CFL_EXP" "bigInst" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
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
   C"same_content" "funCall"
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
   C"reade" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))), V"i" (T"num" "num" []),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"FAPPLY" "finite_map"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"=" "min"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool))),
   C"saved_regs_list" "funCall" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   C"CONS" "list"
    ((T"CFL_EXP" "bigInst" [] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] -->
       T"list" "list" [T"CFL_EXP" "bigInst" []]))),
   C"0" "num" (T"num" "num" []), C"fp" "CFL" (T"num" "num" []),
   C"ip" "CFL" (T"num" "num" []), C"lr" "CFL" (T"num" "num" []),
   C"NIL" "list" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   C"=" "min"
    ((T"list" "list" [T"DOPER" "CFL" []] -->
      (T"list" "list" [T"DOPER" "CFL" []] --> bool))),
   C"mov_pointers" "funCall" (T"list" "list" [T"DOPER" "CFL" []]),
   C"CONS" "list"
    ((T"DOPER" "CFL" [] -->
      (T"list" "list" [T"DOPER" "CFL" []] -->
       T"list" "list" [T"DOPER" "CFL" []]))),
   C"MMOV" "CFL"
    ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))),
   C"R12" "CFL" (T"MREG" "CFL" []),
   C"MR" "CFL" ((T"MREG" "CFL" [] --> T"MEXP" "CFL" [])),
   C"R13" "CFL" (T"MREG" "CFL" []),
   C"MSUB" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"R11" "CFL" (T"MREG" "CFL" []),
   C"MC" "CFL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" [])),
   C"n2w" "words"
    ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []])),
   C"NIL" "list" (T"list" "list" [T"DOPER" "CFL" []]),
   C"!" "bool"
    (((T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool) --> bool)),
   V"caller_i" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   V"callee_i" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   V"k" (T"num" "num" []), V"n" (T"num" "num" []),
   C"pre_call" "funCall"
    ((T"prod" "pair"
       [T"list" "list" [T"CFL_EXP" "bigInst" []],
        T"list" "list" [T"CFL_EXP" "bigInst" []]] -->
      (T"num" "num" [] -->
       (T"num" "num" [] --> T"list" "list" [T"DOPER" "CFL" []])))),
   C"," "pair"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] -->
       T"prod" "pair"
        [T"list" "list" [T"CFL_EXP" "bigInst" []],
         T"list" "list" [T"CFL_EXP" "bigInst" []]]))),
   C"APPEND" "list"
    ((T"list" "list" [T"DOPER" "CFL" []] -->
      (T"list" "list" [T"DOPER" "CFL" []] -->
       T"list" "list" [T"DOPER" "CFL" []]))),
   C"push_list" "bigInst"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
      T"list" "list" [T"DOPER" "CFL" []])),
   C"APPEND" "list"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] -->
       T"list" "list" [T"CFL_EXP" "bigInst" []]))),
   C"MADD" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"pop_list" "bigInst"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
      T"list" "list" [T"DOPER" "CFL" []])), V"bound" (T"num" "num" []),
   C"valid_MEXP" "funCall"
    ((T"CFL_EXP" "bigInst" [] --> (T"num" "num" [] --> bool))),
   C"within_bound" "HSL"
    ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"r" (T"num" "num" []),
   C"valid_regs" "bigInst" ((T"num" "num" [] --> bool)),
   C"T" "bool" (bool),
   C"isM" "bigInst" ((T"num" "num" [] --> T"CFL_EXP" "bigInst" [])),
   C"F" "bool" (bool),
   C"valid_MEXP_1" "funCall"
    ((T"CFL_EXP" "bigInst" [] --> (T"num" "num" [] --> bool))),
   C"valid_exp_1" "bigInst" ((T"CFL_EXP" "bigInst" [] --> bool)),
   C"standard_frame" "funCall"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"num" "num" [] --> bool))),
   C"<=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"w2n" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"num" "num" [])),
   C"read" "preARM"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"EXP" "preARM" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"SP" "preARM" (T"EXP" "preARM" []),
   C"-" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"FP" "preARM" (T"EXP" "preARM" []),
   C"locate_ge" "bigInst"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> bool))),
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
   C"!" "bool" (((T"TEXP" "HSL" [] --> bool) --> bool)),
   V"x" (T"TEXP" "HSL" []),
   C"valid_TEXP" "HSL" ((T"TEXP" "HSL" [] --> (T"num" "num" [] --> bool))),
   C"tread" "HSL"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"TEXP" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"EVERY" "list"
    (((T"TEXP" "HSL" [] --> bool) -->
      (T"list" "list" [T"TEXP" "HSL" []] --> bool))),
   V"lst" (T"list" "list" [T"TEXP" "HSL" []]),
   C"=" "min"
    ((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool))),
   C"MAP" "list"
    (((T"TEXP" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
      (T"list" "list" [T"TEXP" "HSL" []] -->
       T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]]))),
   C"o" "combin"
    (((T"CFL_EXP" "bigInst" [] --> T"cart" "fcp" [bool, T"i32" "words" []])
      -->
      ((T"TEXP" "HSL" [] --> T"CFL_EXP" "bigInst" []) -->
       (T"TEXP" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []])))),
   C"valid_arg_list" "HSL"
    ((T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]]]] --> bool)),
   C"," "pair"
    ((T"list" "list" [T"TEXP" "HSL" []] -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]] -->
       T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]]]]))),
   V"caller_i" (T"list" "list" [T"TEXP" "HSL" []]),
   C"," "pair"
    ((T"list" "list" [T"TEXP" "HSL" []] -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] -->
       T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]]))),
   V"caller_o" (T"list" "list" [T"TEXP" "HSL" []]),
   C"," "pair"
    ((T"list" "list" [T"TEXP" "HSL" []] -->
      (T"list" "list" [T"TEXP" "HSL" []] -->
       T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]]))),
   V"callee_i" (T"list" "list" [T"TEXP" "HSL" []]),
   V"callee_o" (T"list" "list" [T"TEXP" "HSL" []]),
   C"WELL_FORMED" "CFL" ((T"CTL_STRUCTURE" "CFL" [] --> bool)),
   C"SC" "CFL"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))),
   V"pre" (T"CTL_STRUCTURE" "CFL" []), V"body" (T"CTL_STRUCTURE" "CFL" []),
   V"post" (T"CTL_STRUCTURE" "CFL" []),
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
   C"transfer" "HSL"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"," "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
   C"empty_s" "HSL"
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
   V"S_hsl" (T"HSL_STRUCTURE" "HSL" []),
   C"Fc" "HSL"
    ((T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"list" "list" [T"TEXP" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]] -->
        T"HSL_STRUCTURE" "HSL" [])))),
   C"!" "bool" (((alpha --> bool) --> bool)), V"x" (alpha),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"l" (T"list" "list" [alpha]),
   C"!" "bool" ((((alpha --> beta) --> bool) --> bool)),
   V"f" ((alpha --> beta)), V"g" ((alpha --> beta)),
   C"MEM" "list" ((alpha --> (T"list" "list" [alpha] --> bool))),
   C"=" "min"
    ((T"list" "list" [beta] --> (T"list" "list" [beta] --> bool))),
   C"MAP" "list"
    (((alpha --> beta) -->
      (T"list" "list" [alpha] --> T"list" "list" [beta]))),
   C"=" "min" ((beta --> (beta --> bool))), C"~" "bool" ((bool --> bool)),
   C"MEM" "list"
    ((T"TEXP" "HSL" [] --> (T"list" "list" [T"TEXP" "HSL" []] --> bool))),
   C"LENGTH" "list" ((T"list" "list" [alpha] --> T"num" "num" [])),
   C"EL" "list" ((T"num" "num" [] --> (T"list" "list" [alpha] --> alpha))),
   V"l" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   C"EVERY" "list"
    (((T"CFL_EXP" "bigInst" [] --> bool) -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool))),
   V"x" (T"CFL_EXP" "bigInst" []),
   C"valid_exp_3" "bigInst" ((T"CFL_EXP" "bigInst" [] --> bool)),
   C"!" "bool" (((T"list" "list" [T"TEXP" "HSL" []] --> bool) --> bool)),
   V"l" (T"list" "list" [T"TEXP" "HSL" []]),
   C"MAP" "list"
    (((T"TEXP" "HSL" [] --> T"CFL_EXP" "bigInst" []) -->
      (T"list" "list" [T"TEXP" "HSL" []] -->
       T"list" "list" [T"CFL_EXP" "bigInst" []]))),
   C"valid_exp" "bigInst" ((T"CFL_EXP" "bigInst" [] --> bool)),
   C"LENGTH" "list"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] --> T"num" "num" [])),
   C"legal_push_exp" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] --> (T"num" "num" [] --> bool)))),
   C"EL" "list"
    ((T"num" "num" [] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] -->
       T"CFL_EXP" "bigInst" []))),
   C"PRE" "prim_rec" ((T"num" "num" [] --> T"num" "num" [])),
   C"BLK" "CFL"
    ((T"list" "list" [T"DOPER" "CFL" []] --> T"CTL_STRUCTURE" "CFL" [])),
   C">" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"addr_in_range" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] -->
       (T"prod" "pair" [T"num" "num" [], T"num" "num" []] --> bool)))),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"num" "num" [] -->
       T"prod" "pair" [T"num" "num" [], T"num" "num" []]))),
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
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"unique_list" "HSL" ((T"list" "list" [T"TEXP" "HSL" []] --> bool)),
   C"unique_exp_list" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool))),
   C"grow_lt" "bigInst"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> bool))),
   V"x" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_add" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"notC" "HSL" ((T"TEXP" "HSL" [] --> bool)),
   C"o" "combin"
    (((bool --> bool) -->
      ((T"CFL_EXP" "bigInst" [] --> bool) -->
       (T"CFL_EXP" "bigInst" [] --> bool)))),
   C"is_C" "bigInst" ((T"CFL_EXP" "bigInst" [] --> bool)),
   C"LENGTH" "list"
    ((T"list" "list" [T"TEXP" "HSL" []] --> T"num" "num" [])),
   V"l'" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" []))]
  val DT = Thm.disk_thm share_table
  in
  val conv_exp_def =
    DT(["DISK_THM"], [],
       `((%0 (%1 (\%2. ((%3 (%4 (%5 $0))) (%6 (%7 $0)))))) ((%0 (%8 (\%9.
       ((%3 (%4 (%10 $0))) (%11 $0))))) (%12 (\%13. ((%3 (%4 (%14 $0)))
       (%15 ((%16 (%17 (%18 (%19 (%18 %20))))) $0)))))))`)
  val same_content_def =
    DT(["DISK_THM"], [],
       `(%21 (\%22. (%23 (\%24. (%25 (\%26. (%12 (\%27. ((%28 (((%29 ((%30
       $3) $2)) $1) $0)) ((%0 (%1 (\%2. ((%31 ((%32 $4) $0)) ((%33 $2) (%4
       (%5 $0))))))) (%12 (\%34. ((%35 ((%36 $0) $1)) ((%31 ((%37 $3) $0))
       ((%33 $2) (%4 (%14 $0)))))))))))))))))`)
  val saved_regs_list_def =
    DT([], [],
       `((%38 %39) ((%40 (%6 %41)) ((%40 (%6 (%17 (%19 %20)))) ((%40 (%6
       (%17 (%18 %20)))) ((%40 (%6 (%17 (%19 (%19 %20))))) ((%40 (%6 (%17
       (%18 (%19 %20))))) ((%40 (%6 (%17 (%19 (%18 %20))))) ((%40 (%6 (%17
       (%18 (%18 %20))))) ((%40 (%6 (%17 (%19 (%19 (%19 %20)))))) ((%40 (%6
       (%17 (%18 (%19 (%19 %20)))))) ((%40 (%6 %42)) ((%40 (%6 %43)) ((%40
       (%6 %44)) %45)))))))))))))`)
  val mov_pointers_def =
    DT([], [],
       `((%46 %47) ((%48 ((%49 %50) (%51 %52))) ((%48 (((%53 %54) %50) (%55
       (%56 (%17 (%19 %20)))))) %57)))`)
  val pre_call_def =
    DT(["DISK_THM"], [],
       `(%58 (\%59. (%58 (\%60. (%12 (\%61. (%12 (\%62. ((%46 (((%63 ((%64
       $3) $2)) $1) $0)) ((%65 ((%65 ((%65 ((%65 ((%48 (((%53 %52) %52)
       (%55 (%56 $1)))) (%66 ((%67 %39) $3)))) ((%48 (((%68 %52) %52) (%55
       (%56 (%17 (%18 (%19 (%18 %20)))))))) %57))) %47)) (%69 $2))) ((%48
       (((%53 %52) %54) (%55 (%56 ((%16 (%17 (%18 (%19 (%18 %20)))))
       $0))))) %57)))))))))))`)
  val valid_MEXP_def =
    DT(["DISK_THM"], [],
       `((%0 (%12 (\%34. (%12 (\%70. ((%28 ((%71 (%15 $1)) $0)) ((%72 $1)
       ((%16 (%17 (%18 (%19 (%18 %20))))) $0)))))))) ((%0 (%12 (\%73. (%12
       (\%70. ((%28 ((%71 (%6 $1)) $0)) (%74 $1))))))) ((%0 (%8 (\%9. (%12
       (\%70. ((%28 ((%71 (%11 $1)) $0)) %75)))))) (%12 (\%27. (%12 (\%70.
       ((%28 ((%71 (%76 $1)) $0)) %77))))))))`)
  val valid_MEXP_1_def =
    DT(["DISK_THM"], [],
       `((%0 (%12 (\%34. (%12 (\%70. ((%28 ((%78 (%15 $1)) $0)) ((%72 $1)
       ((%16 (%17 (%18 (%19 (%18 %20))))) $0)))))))) ((%0 (%12 (\%73. (%12
       (\%70. ((%28 ((%78 (%6 $1)) $0)) (%79 (%6 $1)))))))) ((%0 (%8 (\%9.
       (%12 (\%70. ((%28 ((%78 (%11 $1)) $0)) %75)))))) (%12 (\%27. (%12
       (\%70. ((%28 ((%78 (%76 $1)) $0)) %77))))))))`)
  val standard_frame_def =
    DT([], [],
       `(%25 (\%26. (%12 (\%27. ((%28 ((%80 $1) $0)) ((%0 ((%81 (%82 ((%83
       $1) %84))) ((%85 (%82 ((%83 $1) %86))) ((%16 (%17 (%18 (%19 (%18
       %20))))) $0)))) ((%87 ((%83 $1) %86)) ((%16 (%17 (%18 (%19 (%18
       %20))))) $0))))))))`)
  val same_content_htm =
    DT(["DISK_THM"], [],
       `(%88 (\%89. (%25 (\%26. (%12 (\%27. ((%28 (((%29 $2) $1) $0)) (%90
       (\%91. ((%35 ((%92 $0) $1)) ((%31 ((%93 $3) $0)) ((%33 $2) (%4
       $0)))))))))))))`)
  val same_content_read =
    DT(["DISK_THM"], [],
       `(%88 (\%89. (%25 (\%26. (%12 (\%27. ((%35 ((%0 (((%29 $2) $1) $0))
       ((%94 (\%91. ((%92 $0) $1))) %95))) ((%96 ((%97 (%93 $2)) %95))
       ((%97 ((%98 (%33 $1)) %4)) %95)))))))))`)
  val FC_OUTPUT_LEM =
    DT(["DISK_THM"], [],
       `(%88 (\%89. (%25 (\%26. (%12 (\%27. ((%35 ((%0 (%99 ((%100 %101)
       ((%102 %103) ((%104 %105) %106))))) ((%0 (%107 ((%108 ((%108 %109)
       %110)) %111))) ((%0 ((%94 (\%91. ((%92 $0) $1))) %106)) ((%0 (%25
       (\%26. ((%96 ((%97 ((%98 (%33 $0)) %4)) %101)) ((%97 ((%98 (%33
       ((%112 %109) $0))) %4)) %105))))) ((%0 (%88 (\%89. (%25 (\%26. ((%35
       (((%29 $1) $0) $2)) (((%29 ((%113 ((%114 %115) $1)) ((%104 %105)
       %101))) ((%112 %109) $0)) $2))))))) ((%0 (%88 (\%89. (%25 (\%26.
       ((%35 (((%29 $1) $0) $2)) (((%29 ((%116 %117) $1)) ((%112 %110) $0))
       $2))))))) ((%0 (%25 (\%26. ((%96 ((%97 ((%98 (%33 $0)) %4)) %106))
       ((%97 ((%98 (%33 ((%112 %111) $0))) %4)) %103))))) (((%29 $2) $1)
       $0))))))))) ((%96 ((%97 (%93 ((%116 (((%118 ((%104 %101) %105))
       %117) ((%104 %103) %106))) $2))) %103)) ((%97 ((%98 (%33 ((%112
       ((%108 ((%108 %109) %110)) %111)) $1))) %4)) %103)))))))))`)
  val MAP_LEM_1 =
    DT(["DISK_THM"], [],
       `(%119 (\%120. (%121 (\%122. (%123 (\%124. (%123 (\%125. ((%35 ((%0
       ((%126 $3) $2)) ((%127 ((%128 $1) $2)) ((%128 $0) $2)))) ((%129 ($1
       $3)) ($0 $3)))))))))))`)
  val FC_SUFFICIENT_COND =
    DT(["DISK_THM"], [],
       `(%88 (\%89. (%25 (\%26. (%12 (\%27. ((%35 ((%0 (%99 ((%100 %101)
       ((%102 %103) ((%104 %105) %106))))) ((%0 (%107 ((%108 ((%108 %109)
       %110)) %111))) ((%0 ((%94 (\%91. ((%92 $0) $1))) %106)) ((%0 (%25
       (\%26. ((%96 ((%97 ((%98 (%33 $0)) %4)) %101)) ((%97 ((%98 (%33
       ((%112 %109) $0))) %4)) %105))))) ((%0 (%88 (\%89. (%25 (\%26. ((%35
       (((%29 $1) $0) $2)) (((%29 ((%113 ((%114 %115) $1)) ((%104 %105)
       %101))) ((%112 %109) $0)) $2))))))) ((%0 (%88 (\%89. (%25 (\%26.
       ((%35 (((%29 $1) $0) $2)) (((%29 ((%116 %117) $1)) ((%112 %110) $0))
       $2))))))) ((%0 (%25 (\%26. ((%96 ((%97 ((%98 (%33 $0)) %4)) %106))
       ((%97 ((%98 (%33 ((%112 %111) $0))) %4)) %103))))) (%90 (\%91. ((%35
       ((%0 (%130 ((%131 $0) %103))) ((%92 $0) $1))) ((%31 ((%33 ((%112
       ((%108 ((%108 %109) %110)) %111)) $2)) (%4 $0))) ((%33 $2) (%4
       $0)))))))))))))) ((%35 (((%29 $2) $1) $0)) (((%29 ((%116 (((%118
       ((%104 %101) %105)) %117) ((%104 %103) %106))) $2)) ((%112 ((%108
       ((%108 %109) %110)) %111)) $1)) $0)))))))))`)
  val MAP_LEM_2 =
    DT(["DISK_THM"], [],
       `(%121 (\%122. (%123 (\%124. (%123 (\%125. ((%28 ((%127 ((%128 $1)
       $2)) ((%128 $0) $2))) (%12 (\%34. ((%35 ((%36 $0) (%132 $3))) ((%129
       ($2 ((%133 $0) $3))) ($1 ((%133 $0) $3)))))))))))))`)
  val VALID_MEXP_1_exp_3 =
    DT(["DISK_THM"], [],
       `(%12 (\%27. (%58 (\%134. ((%35 ((%135 (\%136. ((%78 $0) $2))) $0))
       ((%135 %137) $0))))))`)
  val VALID_TEXP_MEXP_1 =
    DT(["DISK_THM"], [],
       `(%138 (\%139. (%12 (\%27. ((%35 ((%94 (\%91. ((%92 $0) $1))) $1))
       ((%135 (\%136. ((%78 $0) $1))) ((%140 %4) $1)))))))`)
  val VALID_TEXP_MEXP =
    DT(["DISK_THM"], [],
       `(%138 (\%139. (%12 (\%27. ((%35 ((%94 (\%91. ((%92 $0) $1))) $1))
       ((%135 (\%136. ((%71 $0) $1))) ((%140 %4) $1)))))))`)
  val VALID_MEXP_exp =
    DT(["DISK_THM"], [],
       `(%58 (\%134. (%12 (\%27. ((%35 ((%135 (\%136. ((%71 $0) $1))) $1))
       ((%135 %141) $1))))))`)
  val LEGAL_PUSH_EXP_LEM =
    DT(["DISK_THM"], [],
       `(%25 (\%26. (%58 (\%134. (%12 (\%27. ((%35 ((%0 ((%80 $2) $0))
       ((%135 (\%136. ((%78 $0) $1))) $1))) (%12 (\%34. ((%35 ((%36 $0)
       (%142 $2))) (((%143 $3) ((%144 $0) $2)) ((%85 (%145 (%142 $2)))
       $0))))))))))))`)
  val PRE_CALL_PUSH_ARGUMENTS =
    DT(["DISK_THM"], [],
       `(%25 (\%26. (%58 (\%134. (%12 (\%27. (%12 (\%61. ((%35 ((%0 ((%87
       ((%83 $3) %84)) ((%16 $0) (%142 $2)))) ((%0 ((%80 $3) $1)) ((%135
       (\%136. ((%78 $0) $2))) $2)))) (%12 (\%34. ((%35 ((%36 $0) (%142
       $3))) ((%31 ((%33 ((%112 (%146 ((%48 (((%53 %52) %52) (%55 (%56
       $1)))) (%66 $3)))) $4)) (%76 ((%16 ((%85 ((%85 (%82 ((%83 $4) %84)))
       $1)) (%145 (%142 $3)))) $0)))) ((%33 $4) ((%144 $0)
       $3)))))))))))))))`)
  val above_lem_1 =
    DT(["DISK_THM"], [],
       `(%25 (\%26. (%12 (\%62. ((%35 ((%147 %34) (%82 ((%83 $1) %84))))
       (%130 (((%148 $1) (%76 %34)) ((%149 (%82 ((%83 $1) %84))) ((%85 (%82
       ((%83 $1) %84))) $0)))))))))`)
  val PRE_CALL_SANITY_1 =
    DT(["DISK_THM"], [],
       `(%25 (\%26. (%58 (\%134. (%12 (\%61. (%12 (\%27. ((%35 ((%0 ((%87
       ((%83 $3) %84)) ((%16 $1) (%142 $2)))) ((%135 (\%136. ((%78 $0)
       $1))) $2))) ((%150 (\%151. (%12 (\%34. ((%35 ((%147 $0) (%82 ((%83
       $5) %84)))) ((%0 ((%31 ((%33 $5) (%76 $0))) ((%33 $1) (%76 $0))))
       ((%152 (%82 ((%83 $1) %84))) ((%85 (%82 ((%83 $5) %84))) ((%16 $3)
       (%142 $4)))))))))) ((%112 (%146 ((%48 (((%53 %52) %52) (%55 (%56
       $1)))) (%66 $2)))) $3)))))))))))`)
  val LEGAL_POP_EXP_LEM =
    DT(["DISK_THM"], [],
       `(%25 (\%26. (%138 (\%139. (%12 (\%27. ((%35 ((%0 ((%81 (%82 ((%83
       $2) %86))) (%82 ((%83 $2) %84)))) ((%94 (\%91. ((%92 $0) $1))) $1)))
       ((%135 (\%136. (%130 (((%148 $3) $0) ((%149 ((%16 (%82 ((%83 $3)
       %84))) (%142 ((%140 %4) $2)))) (%82 ((%83 $3) %84))))))) ((%140 %4)
       $1)))))))))`)
  val UNIQUE_LIST_11 =
    DT(["DISK_THM"], [],
       `(%138 (\%139. (%25 (\%26. ((%35 ((%0 ((%87 ((%83 $0) %86)) ((%16
       (%17 (%18 (%19 (%18 %20))))) %27))) ((%0 ((%94 (\%91. ((%92 $0)
       %27))) $1)) (%153 $1)))) ((%154 $0) ((%140 %4) $1)))))))`)
  val grow_lt_lem_2 =
    DT(["DISK_THM"], [],
       `((%35 ((%155 %156) %61)) (%12 (\%34. ((%35 ((%81 $0) %61)) ((%152
       (%82 ((%157 %156) (%56 $0)))) ((%16 (%82 %156)) $0))))))`)
  val notC_LEM =
    DT(["DISK_THM"], [],
       `(%138 (\%139. ((%35 ((%94 %158) $0)) ((%135 ((%159 %130) %160))
       ((%140 %4) $0)))))`)
  val PRE_CALL_POP_ARGUMENTS =
    DT(["DISK_THM"], [],
       `(%25 (\%26. (%138 (\%139. (%12 (\%27. ((%35 ((%0 ((%155 ((%83 $2)
       %84)) ((%16 (%17 (%18 (%19 (%18 %20))))) (%161 $1)))) ((%0 ((%87
       ((%83 $2) %84)) ((%16 $0) (%17 (%19 %20))))) ((%0 ((%94 %158) $1))
       ((%0 (%153 $1)) ((%0 ((%94 (\%91. ((%92 $0) $1))) $1)) ((%38 ((%140
       %4) $1)) %162))))))) (%12 (\%34. ((%35 ((%36 $0) (%142 %162))) ((%31
       ((%33 ((%112 (%146 ((%65 ((%65 ((%48 (((%68 %52) %52) (%55 (%56 (%17
       (%18 (%19 (%18 %20)))))))) %57)) %47)) (%69 %162)))) $3)) ((%144 $0)
       %162))) ((%33 $3) (%76 ((%16 ((%16 (%17 (%18 (%19 (%18 %20))))) (%82
       ((%83 $3) %84)))) (%163 $0)))))))))))))))`)
  end
  val _ = DB.bindl "funCall"
  [("conv_exp_def",conv_exp_def,DB.Def),
   ("same_content_def",same_content_def,DB.Def),
   ("saved_regs_list_def",saved_regs_list_def,DB.Def),
   ("mov_pointers_def",mov_pointers_def,DB.Def),
   ("pre_call_def",pre_call_def,DB.Def),
   ("valid_MEXP_def",valid_MEXP_def,DB.Def),
   ("valid_MEXP_1_def",valid_MEXP_1_def,DB.Def),
   ("standard_frame_def",standard_frame_def,DB.Def),
   ("same_content_htm",same_content_htm,DB.Thm),
   ("same_content_read",same_content_read,DB.Thm),
   ("FC_OUTPUT_LEM",FC_OUTPUT_LEM,DB.Thm), ("MAP_LEM_1",MAP_LEM_1,DB.Thm),
   ("FC_SUFFICIENT_COND",FC_SUFFICIENT_COND,DB.Thm),
   ("MAP_LEM_2",MAP_LEM_2,DB.Thm),
   ("VALID_MEXP_1_exp_3",VALID_MEXP_1_exp_3,DB.Thm),
   ("VALID_TEXP_MEXP_1",VALID_TEXP_MEXP_1,DB.Thm),
   ("VALID_TEXP_MEXP",VALID_TEXP_MEXP,DB.Thm),
   ("VALID_MEXP_exp",VALID_MEXP_exp,DB.Thm),
   ("LEGAL_PUSH_EXP_LEM",LEGAL_PUSH_EXP_LEM,DB.Thm),
   ("PRE_CALL_PUSH_ARGUMENTS",PRE_CALL_PUSH_ARGUMENTS,DB.Thm),
   ("above_lem_1",above_lem_1,DB.Thm),
   ("PRE_CALL_SANITY_1",PRE_CALL_SANITY_1,DB.Thm),
   ("LEGAL_POP_EXP_LEM",LEGAL_POP_EXP_LEM,DB.Thm),
   ("UNIQUE_LIST_11",UNIQUE_LIST_11,DB.Thm),
   ("grow_lt_lem_2",grow_lt_lem_2,DB.Thm), ("notC_LEM",notC_LEM,DB.Thm),
   ("PRE_CALL_POP_ARGUMENTS",PRE_CALL_POP_ARGUMENTS,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("bigInstTheory.bigInst_grammars",
                          bigInstTheory.bigInst_grammars),
                         ("HSLTheory.HSL_grammars",HSLTheory.HSL_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "conv_exp")
        {Name = "conv_exp", Thy = "funCall"}
  val _ = update_grms
       (temp_overload_on_by_nametype "same_content")
        {Name = "same_content", Thy = "funCall"}
  val _ = update_grms
       (temp_overload_on_by_nametype "saved_regs_list")
        {Name = "saved_regs_list", Thy = "funCall"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mov_pointers")
        {Name = "mov_pointers", Thy = "funCall"}
  val _ = update_grms
       (temp_overload_on_by_nametype "pre_call")
        {Name = "pre_call", Thy = "funCall"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_MEXP")
        {Name = "valid_MEXP", Thy = "funCall"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_MEXP_1")
        {Name = "valid_MEXP_1", Thy = "funCall"}
  val _ = update_grms
       (temp_overload_on_by_nametype "standard_frame")
        {Name = "standard_frame", Thy = "funCall"}
  val funCall_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [conv_exp_def];  
  
  val _ = computeLib.add_funs [same_content_def];  
  
  val _ = computeLib.add_funs [saved_regs_list_def];  
  
  val _ = computeLib.add_funs [mov_pointers_def];  
  
  val _ = computeLib.add_funs [pre_call_def];  
  
  val _ = computeLib.add_funs [valid_MEXP_def];  
  
  val _ = computeLib.add_funs [valid_MEXP_1_def];  
  
  val _ = computeLib.add_funs [standard_frame_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
