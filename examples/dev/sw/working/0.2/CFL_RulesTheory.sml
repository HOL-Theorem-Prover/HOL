structure CFL_RulesTheory :> CFL_RulesTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading CFL_RulesTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open CFLTheory
  in end;
  val _ = Theory.link_parents
          ("CFL_Rules",
          Arbnum.fromString "1163238573",
          Arbnum.fromString "280635")
          [("CFL",
           Arbnum.fromString "1163238460",
           Arbnum.fromString "586624")];
  val _ = Theory.incorporate_types "CFL_Rules"
       [("REXP",0), ("VEXP",0), ("prodCFL_Rules7",0),
        ("prodCFL_Rules0",0)];
  val _ = Theory.incorporate_consts "CFL_Rules"
     [("dest_VEXP",
       ((T"VEXP" "CFL_Rules" [] -->
         T"recspace" "ind_type"
          [T"cart" "fcp" [bool, T"i32" "words" []]]))),
      ("P_intact",
       ((T"prod" "pair" [(alpha --> bool), (alpha --> bool)] -->
         (T"prod" "pair" [(alpha --> beta), (alpha --> gamma)] -->
          bool)))),
      ("mk_prodCFL_Rules7",
       ((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]
         --> T"prodCFL_Rules7" "CFL_Rules" []))),
      ("mk_prodCFL_Rules0",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
         T"prodCFL_Rules0" "CFL_Rules" []))),
      ("readv",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"REXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])))),
      ("dest_REXP",
       ((T"REXP" "CFL_Rules" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
      ("mk_VEXP",
       ((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]
         --> T"VEXP" "CFL_Rules" []))),
      ("valid_push",
       ((T"prod" "pair"
          [(alpha --> beta),
           T"prod" "pair"
            [(alpha --> gamma),
             T"prod" "pair" [(gamma --> delta), (alpha --> delta)]]] -->
         (T"prod" "pair"
           [(alpha --> U"'e"),
            T"prod" "pair"
             [(alpha --> U"'f"),
              T"prod" "pair" [(U"'f" --> U"'g"), (alpha --> U"'g")]]] -->
          bool)))),
      ("push",
       ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha])))),
      ("CFL_Rules11",
       ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []]
         --> T"VEXP" "CFL_Rules" []))),
      ("CFL_Rules10",
       ((T"VEXP" "CFL_Rules" [] -->
         (T"VEXP" "CFL_Rules" [] --> T"prodCFL_Rules7" "CFL_Rules" [])))),
      ("mk_REXP",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
         T"REXP" "CFL_Rules" []))),
      ("PSPEC",
       ((T"CTL_STRUCTURE" "CFL" [] -->
         (T"prod" "pair"
           [(T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
             --> bool),
            (T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
             --> bool)] -->
          ((T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> alpha) -->
           (T"prod" "pair"
             [(T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]] --> beta),
              T"prod" "pair"
               [(beta --> gamma),
                (T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]] --> gamma)]]
            --> bool)))))),
      ("HSPEC",
       (((T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool) -->
         (T"CTL_STRUCTURE" "CFL" [] -->
          ((T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> bool) --> bool))))),
      ("proper",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         bool))),
      ("VEXP_case",
       (((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
         ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []]
           --> alpha) --> (T"VEXP" "CFL_Rules" [] --> alpha))))),
      ("REXP1_size",
       ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]
         --> T"num" "num" []))),
      ("mread",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"REXP" "CFL_Rules" [] -->
          T"cart" "fcp" [bool, T"i32" "words" []])))),
      ("REXP_case",
       (((T"MREG" "CFL" [] --> alpha) -->
         ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
           alpha) -->
          ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
           ((T"prod" "pair"
              [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] --> alpha)
            --> (T"REXP" "CFL_Rules" [] --> alpha))))))),
      ("VSPEC",
       ((T"CTL_STRUCTURE" "CFL" [] -->
         (T"prod" "pair"
           [(T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
             --> bool),
            (T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
             --> bool)] -->
          (T"list" "list" [T"REXP" "CFL_Rules" []] -->
           (T"prod" "pair"
             [T"REXP" "CFL_Rules" [],
              T"prod" "pair"
               [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
                T"REXP" "CFL_Rules" []]] --> bool)))))),
      ("dest_prodCFL_Rules7",
       ((T"prodCFL_Rules7" "CFL_Rules" [] -->
         T"recspace" "ind_type"
          [T"cart" "fcp" [bool, T"i32" "words" []]]))),
      ("dest_prodCFL_Rules0",
       ((T"prodCFL_Rules0" "CFL_Rules" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
      ("VEXP_size",((T"VEXP" "CFL_Rules" [] --> T"num" "num" []))),
      ("VEXP1_size",
       ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []]
         --> T"num" "num" []))),
      ("VT",
       ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []]
         --> T"VEXP" "CFL_Rules" []))),
      ("top",((T"list" "list" [alpha] --> alpha))),
      ("RR",((T"MREG" "CFL" [] --> T"REXP" "CFL_Rules" []))),
      ("RM",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         T"REXP" "CFL_Rules" []))),
      ("SG",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"VEXP" "CFL_Rules" []))),
      ("PR",
       ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]
         --> T"REXP" "CFL_Rules" []))),
      ("CFL_Rules9",
       ((T"prodCFL_Rules7" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []))),
      ("CFL_Rules8",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"VEXP" "CFL_Rules" []))),
      ("RC",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"REXP" "CFL_Rules" []))),
      ("CFL_Rules6",
       ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]
         --> T"REXP" "CFL_Rules" []))),
      ("CFL_Rules5",
       ((T"REXP" "CFL_Rules" [] -->
         (T"REXP" "CFL_Rules" [] --> T"prodCFL_Rules0" "CFL_Rules" [])))),
      ("CFL_Rules4",
       ((T"prodCFL_Rules0" "CFL_Rules" [] --> T"REXP" "CFL_Rules" []))),
      ("CFL_Rules3",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"REXP" "CFL_Rules" []))),
      ("CFL_Rules2",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         T"REXP" "CFL_Rules" []))),
      ("CFL_Rules1",((T"MREG" "CFL" [] --> T"REXP" "CFL_Rules" []))),
      ("readv_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"REXP" "CFL_Rules" []] --> T"VEXP" "CFL_Rules" []))),
      ("pop",((T"list" "list" [alpha] --> T"list" "list" [alpha]))),
      ("V_intact",
       ((T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> bool),
           T"prod" "pair"
            [(T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] --> bool),
             T"REXP" "CFL_Rules" []]] --> bool))),
      ("REXP_size",((T"REXP" "CFL_Rules" [] --> T"num" "num" [])))];
  
  local
  val share_table = Vector.fromList
  [C"?" "bool"
    ((((T"REXP" "CFL_Rules" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"cart" "fcp" [bool, T"i32" "words" []]]]]) --> bool) -->
      bool)),
   V"rep"
    ((T"REXP" "CFL_Rules" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"cart" "fcp" [bool, T"i32" "words" []]]]] --> bool) -->
      ((T"REXP" "CFL_Rules" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"cart" "fcp" [bool, T"i32" "words" []]]]]) --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"cart" "fcp" [bool, T"i32" "words" []]]]] --> bool) -->
       bool) --> bool)),
   V"'REXP'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]] --> bool)),
   V"'prodCFL_Rules0'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]] --> bool)),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"cart" "fcp" [bool, T"i32" "words" []]]]] --> bool) -->
      bool)), C"\\/" "bool" ((bool --> (bool --> bool))),
   C"?" "bool" (((T"MREG" "CFL" [] --> bool) --> bool)),
   V"a" (T"MREG" "CFL" []),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"cart" "fcp" [bool, T"i32" "words" []]]]] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"cart" "fcp" [bool, T"i32" "words" []]]]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"cart" "fcp" [bool, T"i32" "words" []]]]])))),
   C"0" "num" (T"num" "num" []),
   C"," "pair"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"cart" "fcp" [bool, T"i32" "words" []]] -->
       T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"," "pair"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"cart" "fcp" [bool, T"i32" "words" []]]))),
   C"@" "min"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []])),
   V"v" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"T" "bool" (bool),
   C"@" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) -->
      T"cart" "fcp" [bool, T"i32" "words" []])),
   V"v" (T"cart" "fcp" [bool, T"i32" "words" []]), V"n" (T"num" "num" []),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"?" "bool"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> bool)),
   V"a" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"@" "min" (((T"MREG" "CFL" [] --> bool) --> T"MREG" "CFL" [])),
   V"v" (T"MREG" "CFL" []),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"a" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"?" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"cart" "fcp" [bool, T"i32" "words" []]]]] --> bool) -->
      bool)),
   V"a"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"FCONS" "ind_type"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      ((T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"cart" "fcp" [bool, T"i32" "words" []]]]]) -->
       (T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"cart" "fcp" [bool, T"i32" "words" []]]]])))),
   V"a1'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   V"a1"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"!" "bool" (((T"REXP" "CFL_Rules" [] --> bool) --> bool)),
   V"a" (T"REXP" "CFL_Rules" []),
   C"=" "min"
    ((T"REXP" "CFL_Rules" [] --> (T"REXP" "CFL_Rules" [] --> bool))),
   C"mk_REXP" "CFL_Rules"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      T"REXP" "CFL_Rules" [])),
   C"dest_REXP" "CFL_Rules"
    ((T"REXP" "CFL_Rules" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"=" "min" ((bool --> (bool --> bool))),
   C"?" "bool"
    ((((T"prodCFL_Rules0" "CFL_Rules" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"cart" "fcp" [bool, T"i32" "words" []]]]]) --> bool) -->
      bool)),
   V"rep"
    ((T"prodCFL_Rules0" "CFL_Rules" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"cart" "fcp" [bool, T"i32" "words" []]]]] --> bool) -->
      ((T"prodCFL_Rules0" "CFL_Rules" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"cart" "fcp" [bool, T"i32" "words" []]]]]) --> bool))),
   C"!" "bool" (((T"prodCFL_Rules0" "CFL_Rules" [] --> bool) --> bool)),
   V"a" (T"prodCFL_Rules0" "CFL_Rules" []),
   C"=" "min"
    ((T"prodCFL_Rules0" "CFL_Rules" [] -->
      (T"prodCFL_Rules0" "CFL_Rules" [] --> bool))),
   C"mk_prodCFL_Rules0" "CFL_Rules"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      T"prodCFL_Rules0" "CFL_Rules" [])),
   C"dest_prodCFL_Rules0" "CFL_Rules"
    ((T"prodCFL_Rules0" "CFL_Rules" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"cart" "fcp" [bool, T"i32" "words" []]]]])),
   C"=" "min"
    (((T"MREG" "CFL" [] --> T"REXP" "CFL_Rules" []) -->
      ((T"MREG" "CFL" [] --> T"REXP" "CFL_Rules" []) --> bool))),
   C"CFL_Rules1" "CFL_Rules"
    ((T"MREG" "CFL" [] --> T"REXP" "CFL_Rules" [])),
   C"=" "min"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"REXP" "CFL_Rules" []) -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        T"REXP" "CFL_Rules" []) --> bool))),
   C"CFL_Rules2" "CFL_Rules"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"REXP" "CFL_Rules" [])),
   C"=" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> T"REXP" "CFL_Rules" [])
      -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"REXP" "CFL_Rules" [])
       --> bool))),
   C"CFL_Rules3" "CFL_Rules"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"REXP" "CFL_Rules" [])),
   C"=" "min"
    (((T"prodCFL_Rules0" "CFL_Rules" [] --> T"REXP" "CFL_Rules" []) -->
      ((T"prodCFL_Rules0" "CFL_Rules" [] --> T"REXP" "CFL_Rules" []) -->
       bool))),
   C"CFL_Rules4" "CFL_Rules"
    ((T"prodCFL_Rules0" "CFL_Rules" [] --> T"REXP" "CFL_Rules" [])),
   C"=" "min"
    (((T"REXP" "CFL_Rules" [] -->
       (T"REXP" "CFL_Rules" [] --> T"prodCFL_Rules0" "CFL_Rules" [])) -->
      ((T"REXP" "CFL_Rules" [] -->
        (T"REXP" "CFL_Rules" [] --> T"prodCFL_Rules0" "CFL_Rules" [])) -->
       bool))),
   C"CFL_Rules5" "CFL_Rules"
    ((T"REXP" "CFL_Rules" [] -->
      (T"REXP" "CFL_Rules" [] --> T"prodCFL_Rules0" "CFL_Rules" []))),
   V"a0" (T"REXP" "CFL_Rules" []), V"a1" (T"REXP" "CFL_Rules" []),
   C"=" "min"
    (((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
       T"REXP" "CFL_Rules" []) -->
      ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
        T"REXP" "CFL_Rules" []) --> bool))),
   C"CFL_Rules6" "CFL_Rules"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      T"REXP" "CFL_Rules" [])),
   V"a" (T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]),
   C"@" "min"
    ((((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
        T"prodCFL_Rules0" "CFL_Rules" []) --> bool) -->
      (T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
       T"prodCFL_Rules0" "CFL_Rules" []))),
   V"fn"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      T"prodCFL_Rules0" "CFL_Rules" [])), V"x" (T"REXP" "CFL_Rules" []),
   V"y" (T"REXP" "CFL_Rules" []),
   C"," "pair"
    ((T"REXP" "CFL_Rules" [] -->
      (T"REXP" "CFL_Rules" [] -->
       T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]))),
   C"RR" "CFL_Rules" ((T"MREG" "CFL" [] --> T"REXP" "CFL_Rules" [])),
   C"RM" "CFL_Rules"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"REXP" "CFL_Rules" [])),
   C"RC" "CFL_Rules"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"REXP" "CFL_Rules" [])),
   C"PR" "CFL_Rules"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      T"REXP" "CFL_Rules" [])),
   C"!" "bool" ((((T"MREG" "CFL" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"MREG" "CFL" [] --> alpha)),
   C"!" "bool"
    ((((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha)
       --> bool) --> bool)),
   V"f1"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha)),
   C"!" "bool"
    ((((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) --> bool) -->
      bool)), V"f2" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   C"!" "bool"
    ((((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
        alpha) --> bool) --> bool)),
   V"f3"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      alpha)), C"!" "bool" (((T"MREG" "CFL" [] --> bool) --> bool)),
   C"=" "min" ((alpha --> (alpha --> bool))),
   C"REXP_case" "CFL_Rules"
    (((T"MREG" "CFL" [] --> alpha) -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha)
       -->
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
        ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]
          --> alpha) --> (T"REXP" "CFL_Rules" [] --> alpha)))))),
   C"!" "bool"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> bool)),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   C"!" "bool"
    (((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
       bool) --> bool)),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"REXP_size" "CFL_Rules" ((T"REXP" "CFL_Rules" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"MREG_size" "CFL" ((T"MREG" "CFL" [] --> T"num" "num" [])),
   C"UNCURRY" "pair"
    (((T"num" "num" [] --> (T"OFFSET" "preARM" [] --> T"num" "num" [])) -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"num" "num" []))), V"x" (T"num" "num" []),
   V"y" (T"OFFSET" "preARM" []),
   C"OFFSET_size" "preARM" ((T"OFFSET" "preARM" [] --> T"num" "num" [])),
   C"REXP1_size" "CFL_Rules"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      T"num" "num" [])),
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
   V"r" (T"MREG" "CFL" []),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"mread" "CFL_Rules"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"REXP" "CFL_Rules" [] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"read" "preARM"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"EXP" "preARM" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"toREG" "CFL" ((T"MREG" "CFL" [] --> T"EXP" "preARM" [])),
   V"m" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"toMEM" "CFL"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"EXP" "preARM" [])), V"c" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"=" "min"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool) --> bool))),
   C"proper" "CFL_Rules"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   C"UNCURRY" "pair"
    (((T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       (T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
        bool)) -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   V"regs"
    (T"fmap" "finite_map"
      [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   V"mem"
    (T"fmap" "finite_map"
      [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"FAPPLY" "finite_map"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"n2w" "words"
    ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []])),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool) --> bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   C"!" "bool" (((T"CTL_STRUCTURE" "CFL" [] --> bool) --> bool)),
   V"S_cfl" (T"CTL_STRUCTURE" "CFL" []),
   V"Q"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   C"HSPEC" "CFL_Rules"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      (T"CTL_STRUCTURE" "CFL" [] -->
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         bool) --> bool)))),
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
   V"ir" (T"CTL_STRUCTURE" "CFL" []),
   V"pre_p"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   V"post_p"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        alpha) --> bool) --> bool)),
   V"stk_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      alpha)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        beta) --> bool) --> bool)),
   V"in_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      beta)), C"!" "bool" ((((beta --> gamma) --> bool) --> bool)),
   V"f" ((beta --> gamma)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma) --> bool) --> bool)),
   V"out_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      gamma)),
   C"PSPEC" "CFL_Rules"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)] -->
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         alpha) -->
        (T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> beta),
           T"prod" "pair"
            [(beta --> gamma),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] --> gamma)]]
         --> bool))))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool) -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)]))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       beta) -->
      (T"prod" "pair"
        [(beta --> gamma),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> gamma)] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta),
         T"prod" "pair"
          [(beta --> gamma),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> gamma)]]))),
   C"," "pair"
    (((beta --> gamma) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma) -->
       T"prod" "pair"
        [(beta --> gamma),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> gamma)]))), C"!" "bool" (((beta --> bool) --> bool)),
   V"v" (beta), C"!" "bool" (((alpha --> bool) --> bool)), V"x" (alpha),
   C"=" "min" ((beta --> (beta --> bool))),
   C"=" "min" ((gamma --> (gamma --> bool))),
   C"!" "bool" ((((alpha --> beta) --> bool) --> bool)),
   V"stk_f" ((alpha --> beta)),
   C"!" "bool" ((((alpha --> gamma) --> bool) --> bool)),
   V"in_f" ((alpha --> gamma)),
   C"!" "bool" ((((gamma --> delta) --> bool) --> bool)),
   V"f" ((gamma --> delta)),
   C"!" "bool" ((((alpha --> delta) --> bool) --> bool)),
   V"out_f" ((alpha --> delta)),
   C"!" "bool" ((((alpha --> U"'e") --> bool) --> bool)),
   V"stk_f'" ((alpha --> U"'e")),
   C"!" "bool" ((((alpha --> U"'f") --> bool) --> bool)),
   V"in_f'" ((alpha --> U"'f")),
   C"!" "bool" ((((U"'f" --> U"'g") --> bool) --> bool)),
   V"g" ((U"'f" --> U"'g")),
   C"!" "bool" ((((alpha --> U"'g") --> bool) --> bool)),
   V"out_f'" ((alpha --> U"'g")),
   C"valid_push" "CFL_Rules"
    ((T"prod" "pair"
       [(alpha --> beta),
        T"prod" "pair"
         [(alpha --> gamma),
          T"prod" "pair" [(gamma --> delta), (alpha --> delta)]]] -->
      (T"prod" "pair"
        [(alpha --> U"'e"),
         T"prod" "pair"
          [(alpha --> U"'f"),
           T"prod" "pair" [(U"'f" --> U"'g"), (alpha --> U"'g")]]] -->
       bool))),
   C"," "pair"
    (((alpha --> beta) -->
      (T"prod" "pair"
        [(alpha --> gamma),
         T"prod" "pair" [(gamma --> delta), (alpha --> delta)]] -->
       T"prod" "pair"
        [(alpha --> beta),
         T"prod" "pair"
          [(alpha --> gamma),
           T"prod" "pair" [(gamma --> delta), (alpha --> delta)]]]))),
   C"," "pair"
    (((alpha --> gamma) -->
      (T"prod" "pair" [(gamma --> delta), (alpha --> delta)] -->
       T"prod" "pair"
        [(alpha --> gamma),
         T"prod" "pair" [(gamma --> delta), (alpha --> delta)]]))),
   C"," "pair"
    (((gamma --> delta) -->
      ((alpha --> delta) -->
       T"prod" "pair" [(gamma --> delta), (alpha --> delta)]))),
   C"," "pair"
    (((alpha --> U"'e") -->
      (T"prod" "pair"
        [(alpha --> U"'f"),
         T"prod" "pair" [(U"'f" --> U"'g"), (alpha --> U"'g")]] -->
       T"prod" "pair"
        [(alpha --> U"'e"),
         T"prod" "pair"
          [(alpha --> U"'f"),
           T"prod" "pair" [(U"'f" --> U"'g"), (alpha --> U"'g")]]]))),
   C"," "pair"
    (((alpha --> U"'f") -->
      (T"prod" "pair" [(U"'f" --> U"'g"), (alpha --> U"'g")] -->
       T"prod" "pair"
        [(alpha --> U"'f"),
         T"prod" "pair" [(U"'f" --> U"'g"), (alpha --> U"'g")]]))),
   C"," "pair"
    (((U"'f" --> U"'g") -->
      ((alpha --> U"'g") -->
       T"prod" "pair" [(U"'f" --> U"'g"), (alpha --> U"'g")]))),
   V"st" (alpha), V"st'" (alpha),
   C"=" "min" ((delta --> (delta --> bool))),
   C"=" "min" ((U"'e" --> (U"'e" --> bool))),
   C"=" "min" ((U"'g" --> (U"'g" --> bool))),
   C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"P" ((alpha --> bool)), V"Q" ((alpha --> bool)),
   V"stk_g" ((alpha --> gamma)),
   C"P_intact" "CFL_Rules"
    ((T"prod" "pair" [(alpha --> bool), (alpha --> bool)] -->
      (T"prod" "pair" [(alpha --> beta), (alpha --> gamma)] --> bool))),
   C"," "pair"
    (((alpha --> bool) -->
      ((alpha --> bool) -->
       T"prod" "pair" [(alpha --> bool), (alpha --> bool)]))),
   C"," "pair"
    (((alpha --> beta) -->
      ((alpha --> gamma) -->
       T"prod" "pair" [(alpha --> beta), (alpha --> gamma)]))),
   C"?" "bool"
    ((((T"VEXP" "CFL_Rules" [] -->
        T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])
       --> bool) --> bool)),
   V"rep"
    ((T"VEXP" "CFL_Rules" [] -->
      T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool) -->
      ((T"VEXP" "CFL_Rules" [] -->
        T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])
       --> bool))),
   V"a0'"
    (T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"!" "bool"
    ((((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]
        --> bool) --> bool) --> bool)),
   V"'VEXP'"
    ((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
      bool)),
   V"'prodCFL_Rules7'"
    ((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
      bool)),
   C"!" "bool"
    (((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool) --> bool)),
   C"=" "min"
    ((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])
        -->
        T"recspace" "ind_type"
         [T"cart" "fcp" [bool, T"i32" "words" []]])))),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"?" "bool"
    (((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool) --> bool)),
   V"a" (T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"FCONS" "ind_type"
    ((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
      ((T"num" "num" [] -->
        T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])
       -->
       (T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"cart" "fcp" [bool, T"i32" "words" []]])))),
   V"a1'"
    (T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]),
   V"a0"
    (T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]),
   V"a1"
    (T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"!" "bool" (((T"VEXP" "CFL_Rules" [] --> bool) --> bool)),
   V"a" (T"VEXP" "CFL_Rules" []),
   C"=" "min"
    ((T"VEXP" "CFL_Rules" [] --> (T"VEXP" "CFL_Rules" [] --> bool))),
   C"mk_VEXP" "CFL_Rules"
    ((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
      T"VEXP" "CFL_Rules" [])),
   C"dest_VEXP" "CFL_Rules"
    ((T"VEXP" "CFL_Rules" [] -->
      T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])),
   V"r" (T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"?" "bool"
    ((((T"prodCFL_Rules7" "CFL_Rules" [] -->
        T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])
       --> bool) --> bool)),
   V"rep"
    ((T"prodCFL_Rules7" "CFL_Rules" [] -->
      T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool) -->
      ((T"prodCFL_Rules7" "CFL_Rules" [] -->
        T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])
       --> bool))),
   C"!" "bool" (((T"prodCFL_Rules7" "CFL_Rules" [] --> bool) --> bool)),
   V"a" (T"prodCFL_Rules7" "CFL_Rules" []),
   C"=" "min"
    ((T"prodCFL_Rules7" "CFL_Rules" [] -->
      (T"prodCFL_Rules7" "CFL_Rules" [] --> bool))),
   C"mk_prodCFL_Rules7" "CFL_Rules"
    ((T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
      T"prodCFL_Rules7" "CFL_Rules" [])),
   C"dest_prodCFL_Rules7" "CFL_Rules"
    ((T"prodCFL_Rules7" "CFL_Rules" [] -->
      T"recspace" "ind_type" [T"cart" "fcp" [bool, T"i32" "words" []]])),
   C"=" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> T"VEXP" "CFL_Rules" [])
      -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"VEXP" "CFL_Rules" [])
       --> bool))),
   C"CFL_Rules8" "CFL_Rules"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"VEXP" "CFL_Rules" [])),
   C"=" "min"
    (((T"prodCFL_Rules7" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []) -->
      ((T"prodCFL_Rules7" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []) -->
       bool))),
   C"CFL_Rules9" "CFL_Rules"
    ((T"prodCFL_Rules7" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])),
   C"=" "min"
    (((T"VEXP" "CFL_Rules" [] -->
       (T"VEXP" "CFL_Rules" [] --> T"prodCFL_Rules7" "CFL_Rules" [])) -->
      ((T"VEXP" "CFL_Rules" [] -->
        (T"VEXP" "CFL_Rules" [] --> T"prodCFL_Rules7" "CFL_Rules" [])) -->
       bool))),
   C"CFL_Rules10" "CFL_Rules"
    ((T"VEXP" "CFL_Rules" [] -->
      (T"VEXP" "CFL_Rules" [] --> T"prodCFL_Rules7" "CFL_Rules" []))),
   V"a0" (T"VEXP" "CFL_Rules" []), V"a1" (T"VEXP" "CFL_Rules" []),
   C"=" "min"
    (((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
       T"VEXP" "CFL_Rules" []) -->
      ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
        T"VEXP" "CFL_Rules" []) --> bool))),
   C"CFL_Rules11" "CFL_Rules"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      T"VEXP" "CFL_Rules" [])),
   V"a" (T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []]),
   C"@" "min"
    ((((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
        T"prodCFL_Rules7" "CFL_Rules" []) --> bool) -->
      (T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
       T"prodCFL_Rules7" "CFL_Rules" []))),
   V"fn"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      T"prodCFL_Rules7" "CFL_Rules" [])), V"x" (T"VEXP" "CFL_Rules" []),
   V"y" (T"VEXP" "CFL_Rules" []),
   C"," "pair"
    ((T"VEXP" "CFL_Rules" [] -->
      (T"VEXP" "CFL_Rules" [] -->
       T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []]))),
   C"SG" "CFL_Rules"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"VEXP" "CFL_Rules" [])),
   C"VT" "CFL_Rules"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      T"VEXP" "CFL_Rules" [])),
   V"f" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   C"!" "bool"
    ((((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
        alpha) --> bool) --> bool)),
   V"f1"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      alpha)),
   C"VEXP_case" "CFL_Rules"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
      ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
        alpha) --> (T"VEXP" "CFL_Rules" [] --> alpha)))),
   C"!" "bool"
    (((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
       bool) --> bool)),
   C"VEXP_size" "CFL_Rules" ((T"VEXP" "CFL_Rules" [] --> T"num" "num" [])),
   C"VEXP1_size" "CFL_Rules"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      T"num" "num" [])),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"REXP" "CFL_Rules" []] --> T"VEXP" "CFL_Rules" []) -->
      ((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"REXP" "CFL_Rules" []] --> T"VEXP" "CFL_Rules" []) --> bool))),
   C"readv_tupled" "CFL_Rules"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"REXP" "CFL_Rules" []] --> T"VEXP" "CFL_Rules" [])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"REXP" "CFL_Rules" []] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"REXP" "CFL_Rules" []] --> bool)) -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"REXP" "CFL_Rules" []] --> T"VEXP" "CFL_Rules" []) -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"REXP" "CFL_Rules" []] --> T"VEXP" "CFL_Rules" [])) -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"REXP" "CFL_Rules" []] --> T"VEXP" "CFL_Rules" [])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"REXP" "CFL_Rules" []] -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"REXP" "CFL_Rules" []] --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"REXP" "CFL_Rules" []] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"REXP" "CFL_Rules" []] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"REXP" "CFL_Rules" []] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"REXP" "CFL_Rules" []] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"REXP" "CFL_Rules" []] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"REXP" "CFL_Rules" []] --> bool)) --> bool)),
   V"b" (T"REXP" "CFL_Rules" []),
   C"," "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"REXP" "CFL_Rules" [] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"REXP" "CFL_Rules" []]))),
   V"readv_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"REXP" "CFL_Rules" []] --> T"VEXP" "CFL_Rules" [])),
   V"a'"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
       T"REXP" "CFL_Rules" []]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"REXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"REXP" "CFL_Rules" []] --> T"VEXP" "CFL_Rules" []))),
   V"v1" (T"REXP" "CFL_Rules" []),
   C"REXP_case" "CFL_Rules"
    (((T"MREG" "CFL" [] --> T"VEXP" "CFL_Rules" []) -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        T"VEXP" "CFL_Rules" []) -->
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"VEXP" "CFL_Rules" []) -->
        ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]
          --> T"VEXP" "CFL_Rules" []) -->
         (T"REXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])))))),
   V"v6" (T"MREG" "CFL" []),
   C"I" "combin" ((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])),
   V"v7" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"v8" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v9" (T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]),
   C"pair_case" "pair"
    (((T"REXP" "CFL_Rules" [] -->
       (T"REXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])) -->
      (T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
       T"VEXP" "CFL_Rules" []))),
   V"x"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"x1" (T"REXP" "CFL_Rules" []),
   C"readv" "CFL_Rules"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"REXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []))),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"stk" (T"list" "list" [alpha]),
   C"=" "min"
    ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool))),
   C"push" "CFL_Rules"
    ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"CONS" "list"
    ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"=" "min"
    (((T"list" "list" [alpha] --> alpha) -->
      ((T"list" "list" [alpha] --> alpha) --> bool))),
   C"top" "CFL_Rules" ((T"list" "list" [alpha] --> alpha)),
   C"HD" "list" ((T"list" "list" [alpha] --> alpha)),
   C"=" "min"
    (((T"list" "list" [alpha] --> T"list" "list" [alpha]) -->
      ((T"list" "list" [alpha] --> T"list" "list" [alpha]) --> bool))),
   C"pop" "CFL_Rules"
    ((T"list" "list" [alpha] --> T"list" "list" [alpha])),
   C"TL" "list" ((T"list" "list" [alpha] --> T"list" "list" [alpha])),
   C"!" "bool"
    (((T"list" "list" [T"REXP" "CFL_Rules" []] --> bool) --> bool)),
   V"stk" (T"list" "list" [T"REXP" "CFL_Rules" []]),
   V"iv" (T"REXP" "CFL_Rules" []),
   C"!" "bool"
    ((((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []) --> bool) -->
      bool)), V"f" ((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])),
   V"ov" (T"REXP" "CFL_Rules" []),
   C"VSPEC" "CFL_Rules"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)] -->
       (T"list" "list" [T"REXP" "CFL_Rules" []] -->
        (T"prod" "pair"
          [T"REXP" "CFL_Rules" [],
           T"prod" "pair"
            [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
             T"REXP" "CFL_Rules" []]] --> bool))))),
   C"," "pair"
    ((T"REXP" "CFL_Rules" [] -->
      (T"prod" "pair"
        [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
         T"REXP" "CFL_Rules" []] -->
       T"prod" "pair"
        [T"REXP" "CFL_Rules" [],
         T"prod" "pair"
          [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
           T"REXP" "CFL_Rules" []]]))),
   C"," "pair"
    (((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []) -->
      (T"REXP" "CFL_Rules" [] -->
       T"prod" "pair"
        [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
         T"REXP" "CFL_Rules" []]))),
   C"PSPEC" "CFL_Rules"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)] -->
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         T"list" "list" [T"VEXP" "CFL_Rules" []]) -->
        (T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> T"VEXP" "CFL_Rules" []),
           T"prod" "pair"
            [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] -->
              T"VEXP" "CFL_Rules" [])]] --> bool))))),
   C"MAP" "list"
    (((T"REXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []) -->
      (T"list" "list" [T"REXP" "CFL_Rules" []] -->
       T"list" "list" [T"VEXP" "CFL_Rules" []]))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"VEXP" "CFL_Rules" []) -->
      (T"prod" "pair"
        [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> T"VEXP" "CFL_Rules" [])] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> T"VEXP" "CFL_Rules" []),
         T"prod" "pair"
          [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> T"VEXP" "CFL_Rules" [])]]))),
   C"," "pair"
    (((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        T"VEXP" "CFL_Rules" []) -->
       T"prod" "pair"
        [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> T"VEXP" "CFL_Rules" [])]))), V"e" (T"REXP" "CFL_Rules" []),
   C"V_intact" "CFL_Rules"
    ((T"prod" "pair"
       [(T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         bool),
        T"prod" "pair"
         [(T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
           --> bool), T"REXP" "CFL_Rules" []]] --> bool)),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool), T"REXP" "CFL_Rules" []] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> bool), T"REXP" "CFL_Rules" []]]))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      (T"REXP" "CFL_Rules" [] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool), T"REXP" "CFL_Rules" []]))),
   C"?" "bool" (((T"VEXP" "CFL_Rules" [] --> bool) --> bool)),
   C"DATATYPE" "bool" ((bool --> bool)),
   V"REXP"
    (((T"MREG" "CFL" [] --> T"REXP" "CFL_Rules" []) -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        T"REXP" "CFL_Rules" []) -->
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"REXP" "CFL_Rules" []) -->
        ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]
          --> T"REXP" "CFL_Rules" []) --> bool))))),
   V"a'" (T"MREG" "CFL" []),
   C"=" "min" ((T"MREG" "CFL" [] --> (T"MREG" "CFL" [] --> bool))),
   V"a'" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"=" "min"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool))),
   V"a'" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"a'" (T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]),
   C"=" "min"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      (T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
       bool))), C"~" "bool" ((bool --> bool)),
   V"M" (T"REXP" "CFL_Rules" []), V"M'" (T"REXP" "CFL_Rules" []),
   V"f'" ((T"MREG" "CFL" [] --> alpha)),
   V"f1'"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha)),
   V"f2'" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   V"f3'"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      alpha)), V"R" (T"REXP" "CFL_Rules" []), V"M" (T"MREG" "CFL" []),
   V"p" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"?" "bool"
    (((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
       bool) --> bool)),
   V"p" (T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []]),
   V"f0" ((T"MREG" "CFL" [] --> alpha)),
   C"!" "bool"
    ((((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
        (beta --> alpha)) --> bool) --> bool)),
   V"f3"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      (beta --> alpha))),
   C"!" "bool"
    ((((T"REXP" "CFL_Rules" [] -->
        (T"REXP" "CFL_Rules" [] --> (alpha --> (alpha --> beta)))) -->
       bool) --> bool)),
   V"f4"
    ((T"REXP" "CFL_Rules" [] -->
      (T"REXP" "CFL_Rules" [] --> (alpha --> (alpha --> beta))))),
   C"?" "bool" ((((T"REXP" "CFL_Rules" [] --> alpha) --> bool) --> bool)),
   V"fn0" ((T"REXP" "CFL_Rules" [] --> alpha)),
   C"?" "bool"
    ((((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
        beta) --> bool) --> bool)),
   V"fn1"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      beta)),
   C"!" "bool" ((((T"REXP" "CFL_Rules" [] --> bool) --> bool) --> bool)),
   V"P0" ((T"REXP" "CFL_Rules" [] --> bool)),
   C"!" "bool"
    ((((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
        bool) --> bool) --> bool)),
   V"P1"
    ((T"prod" "pair" [T"REXP" "CFL_Rules" [], T"REXP" "CFL_Rules" []] -->
      bool)), V"R0" (T"REXP" "CFL_Rules" []),
   V"R"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)), V"S1" (T"CTL_STRUCTURE" "CFL" []),
   V"S2" (T"CTL_STRUCTURE" "CFL" []),
   C"WELL_FORMED" "CFL" ((T"CTL_STRUCTURE" "CFL" [] --> bool)),
   C"SC" "CFL"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))),
   C"!" "bool" (((T"DOPER" "CFL" [] --> bool) --> bool)),
   V"stm" (T"DOPER" "CFL" []),
   C"!" "bool" (((T"list" "list" [T"DOPER" "CFL" []] --> bool) --> bool)),
   V"stmL" (T"list" "list" [T"DOPER" "CFL" []]),
   C"=" "min"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   C"BLK" "CFL"
    ((T"list" "list" [T"DOPER" "CFL" []] --> T"CTL_STRUCTURE" "CFL" [])),
   C"CONS" "list"
    ((T"DOPER" "CFL" [] -->
      (T"list" "list" [T"DOPER" "CFL" []] -->
       T"list" "list" [T"DOPER" "CFL" []]))),
   C"NIL" "list" (T"list" "list" [T"DOPER" "CFL" []]),
   C"SNOC" "rich_list"
    ((T"DOPER" "CFL" [] -->
      (T"list" "list" [T"DOPER" "CFL" []] -->
       T"list" "list" [T"DOPER" "CFL" []]))),
   C"!" "bool"
    (((T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] --> bool)
      --> bool)),
   V"cond"
    (T"prod" "pair"
      [T"MREG" "CFL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]),
   C"eval_il_cond" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   C"CJ" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] -->
       (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])))),
   V"S_body" (T"CTL_STRUCTURE" "CFL" []), V"Q" (alpha),
   C"WF_TR" "ARMComposition"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"EXP" "preARM" [],
          T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
        T"list" "list"
         [T"prod" "pair"
           [T"prod" "pair"
             [T"OPERATOR" "preARM" [],
              T"prod" "pair"
               [T"option" "option" [T"COND" "preARM" []], bool]],
            T"prod" "pair"
             [T"option" "option" [T"EXP" "preARM" []],
              T"prod" "pair"
               [T"list" "list" [T"EXP" "preARM" []],
                T"option" "option" [T"OFFSET" "preARM" []]]]]]] --> bool)),
   C"," "pair"
    ((T"prod" "pair"
       [T"EXP" "preARM" [],
        T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
      (T"list" "list"
        [T"prod" "pair"
          [T"prod" "pair"
            [T"OPERATOR" "preARM" [],
             T"prod" "pair"
              [T"option" "option" [T"COND" "preARM" []], bool]],
           T"prod" "pair"
            [T"option" "option" [T"EXP" "preARM" []],
             T"prod" "pair"
              [T"list" "list" [T"EXP" "preARM" []],
               T"option" "option" [T"OFFSET" "preARM" []]]]]] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
         T"list" "list"
          [T"prod" "pair"
            [T"prod" "pair"
              [T"OPERATOR" "preARM" [],
               T"prod" "pair"
                [T"option" "option" [T"COND" "preARM" []], bool]],
             T"prod" "pair"
              [T"option" "option" [T"EXP" "preARM" []],
               T"prod" "pair"
                [T"list" "list" [T"EXP" "preARM" []],
                 T"option" "option" [T"OFFSET" "preARM" []]]]]]]))),
   C"translate_condition" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      T"prod" "pair"
       [T"EXP" "preARM" [],
        T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]])),
   C"translate" "CFL"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      T"list" "list"
       [T"prod" "pair"
         [T"prod" "pair"
           [T"OPERATOR" "preARM" [],
            T"prod" "pair"
             [T"option" "option" [T"COND" "preARM" []], bool]],
          T"prod" "pair"
           [T"option" "option" [T"EXP" "preARM" []],
            T"prod" "pair"
             [T"list" "list" [T"EXP" "preARM" []],
              T"option" "option" [T"OFFSET" "preARM" []]]]]])),
   C"TR" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))),
   C"WF" "relation" (((alpha --> (alpha --> bool)) --> bool)),
   V"R" ((alpha --> (alpha --> bool))),
   C"?" "bool" (((alpha --> bool) --> bool)), V"w" (alpha), V"min" (alpha),
   V"b" (alpha),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool)) --> bool)),
   V"st1"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"st0"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"prj_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      alpha)), C"!" "bool" ((((alpha --> alpha) --> bool) --> bool)),
   V"f" ((alpha --> alpha)), V"cond_f" ((alpha --> bool)), V"t1" (alpha),
   V"t0" (alpha),
   C"?" "bool" ((((alpha --> (alpha --> bool)) --> bool) --> bool)),
   V"t1" (beta), V"shuffle_f" ((gamma --> delta)),
   C"PSPEC" "CFL_Rules"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)] -->
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         alpha) -->
        (T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> beta),
           T"prod" "pair"
            [(beta --> delta),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] --> delta)]]
         --> bool))))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       beta) -->
      (T"prod" "pair"
        [(beta --> delta),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> delta)] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta),
         T"prod" "pair"
          [(beta --> delta),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> delta)]]))),
   C"," "pair"
    (((beta --> delta) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        delta) -->
       T"prod" "pair"
        [(beta --> delta),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> delta)]))),
   C"o" "combin"
    (((gamma --> delta) --> ((beta --> gamma) --> (beta --> delta)))),
   C"o" "combin"
    (((gamma --> delta) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma) -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        delta)))), C"!" "bool" ((((delta --> gamma) --> bool) --> bool)),
   V"g" ((delta --> gamma)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        delta) --> bool) --> bool)),
   V"in_f'"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      delta)),
   C"=" "min"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       gamma) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma) --> bool))),
   C"o" "combin"
    (((delta --> gamma) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        delta) -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma)))),
   C"o" "combin"
    (((beta --> gamma) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        beta) -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma)))),
   C"PSPEC" "CFL_Rules"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)] -->
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         alpha) -->
        (T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> delta),
           T"prod" "pair"
            [(delta --> gamma),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] --> gamma)]]
         --> bool))))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       delta) -->
      (T"prod" "pair"
        [(delta --> gamma),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> gamma)] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> delta),
         T"prod" "pair"
          [(delta --> gamma),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> gamma)]]))),
   C"," "pair"
    (((delta --> gamma) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma) -->
       T"prod" "pair"
        [(delta --> gamma),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> gamma)]))), V"ir1" (T"CTL_STRUCTURE" "CFL" []),
   V"ir2" (T"CTL_STRUCTURE" "CFL" []),
   V"pre_p1"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   V"post_p1"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   V"post_p2"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   V"in_f1"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      beta)), V"f1" ((beta --> gamma)), V"f2" ((gamma --> delta)),
   V"out_f1"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      gamma)),
   V"out_f2"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      delta)),
   C"PSPEC" "CFL_Rules"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)] -->
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         alpha) -->
        (T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> gamma),
           T"prod" "pair"
            [(gamma --> delta),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] --> delta)]]
         --> bool))))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       gamma) -->
      (T"prod" "pair"
        [(gamma --> delta),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> delta)] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> gamma),
         T"prod" "pair"
          [(gamma --> delta),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> delta)]]))),
   C"," "pair"
    (((gamma --> delta) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        delta) -->
       T"prod" "pair"
        [(gamma --> delta),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> delta)]))), V"ir_t" (T"CTL_STRUCTURE" "CFL" []),
   V"ir_f" (T"CTL_STRUCTURE" "CFL" []),
   C"!" "bool" ((((beta --> bool) --> bool) --> bool)),
   V"cond_f" ((beta --> bool)), V"f2" ((beta --> gamma)),
   C"COND" "bool" ((bool --> (gamma --> (gamma --> gamma)))),
   V"prj_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      beta)), C"!" "bool" ((((beta --> beta) --> bool) --> bool)),
   V"f" ((beta --> beta)),
   C"PSPEC" "CFL_Rules"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)] -->
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         alpha) -->
        (T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> beta),
           T"prod" "pair"
            [(beta --> beta),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] --> beta)]] -->
         bool))))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       beta) -->
      (T"prod" "pair"
        [(beta --> beta),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta)] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta),
         T"prod" "pair"
          [(beta --> beta),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> beta)]]))),
   C"," "pair"
    (((beta --> beta) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        beta) -->
       T"prod" "pair"
        [(beta --> beta),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta)]))),
   C"WHILE" "while"
    (((beta --> bool) --> ((beta --> beta) --> (beta --> beta)))),
   C"o" "combin"
    (((bool --> bool) --> ((beta --> bool) --> (beta --> bool)))),
   C"?" "bool" ((((beta --> (beta --> bool)) --> bool) --> bool)),
   V"R" ((beta --> (beta --> bool))),
   C"WF" "relation" (((beta --> (beta --> bool)) --> bool)), V"t0" (beta),
   C"!" "bool" (((gamma --> bool) --> bool)), V"t1" (gamma),
   V"pre_p'"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   V"post_p'"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   V"stk_f'"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      delta)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        U"'e") --> bool) --> bool)),
   V"in_f'"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      U"'e")), C"!" "bool" ((((U"'e" --> U"'f") --> bool) --> bool)),
   V"g" ((U"'e" --> U"'f")),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        U"'f") --> bool) --> bool)),
   V"out_f'"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      U"'f")),
   C"valid_push" "CFL_Rules"
    ((T"prod" "pair"
       [(T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         alpha),
        T"prod" "pair"
         [(T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
           --> beta),
          T"prod" "pair"
           [(beta --> gamma),
            (T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
             --> gamma)]]] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> delta),
         T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> U"'e"),
           T"prod" "pair"
            [(U"'e" --> U"'f"),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] --> U"'f")]]]
       --> bool))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       alpha) -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta),
         T"prod" "pair"
          [(beta --> gamma),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> gamma)]] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha),
         T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> beta),
           T"prod" "pair"
            [(beta --> gamma),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] -->
              gamma)]]]))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       delta) -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> U"'e"),
         T"prod" "pair"
          [(U"'e" --> U"'f"),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> U"'f")]] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> delta),
         T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> U"'e"),
           T"prod" "pair"
            [(U"'e" --> U"'f"),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] -->
              U"'f")]]]))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       U"'e") -->
      (T"prod" "pair"
        [(U"'e" --> U"'f"),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> U"'f")] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> U"'e"),
         T"prod" "pair"
          [(U"'e" --> U"'f"),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> U"'f")]]))),
   C"," "pair"
    (((U"'e" --> U"'f") -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        U"'f") -->
       T"prod" "pair"
        [(U"'e" --> U"'f"),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> U"'f")]))),
   C"PSPEC" "CFL_Rules"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)] -->
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         delta) -->
        (T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> U"'e"),
           T"prod" "pair"
            [(U"'e" --> U"'f"),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] --> U"'f")]]
         --> bool))))), C"!" "bool" (((delta --> bool) --> bool)),
   V"e_f" (delta),
   V"stk_g"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      U"'e")),
   C"P_intact" "CFL_Rules"
    ((T"prod" "pair"
       [(T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         bool),
        (T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         bool)] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> U"'e")] --> bool))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       alpha) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        U"'e") -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> U"'e")]))),
   C"PSPEC" "CFL_Rules"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)] -->
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         U"'e") -->
        (T"prod" "pair"
          [(T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> beta),
           T"prod" "pair"
            [(beta --> gamma),
             (T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]] --> gamma)]]
         --> bool))))),
   V"VEXP"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> T"VEXP" "CFL_Rules" [])
      -->
      ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
        T"VEXP" "CFL_Rules" []) --> bool))),
   V"a'" (T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []]),
   C"=" "min"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      (T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
       bool))), V"M" (T"VEXP" "CFL_Rules" []),
   V"M'" (T"VEXP" "CFL_Rules" []),
   V"f'" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   V"f1'"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      alpha)), V"V" (T"VEXP" "CFL_Rules" []),
   C"?" "bool"
    (((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
       bool) --> bool)),
   V"p" (T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []]),
   V"f0" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   C"!" "bool"
    ((((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
        (beta --> alpha)) --> bool) --> bool)),
   V"f1"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      (beta --> alpha))),
   C"!" "bool"
    ((((T"VEXP" "CFL_Rules" [] -->
        (T"VEXP" "CFL_Rules" [] --> (alpha --> (alpha --> beta)))) -->
       bool) --> bool)),
   V"f2"
    ((T"VEXP" "CFL_Rules" [] -->
      (T"VEXP" "CFL_Rules" [] --> (alpha --> (alpha --> beta))))),
   C"?" "bool" ((((T"VEXP" "CFL_Rules" [] --> alpha) --> bool) --> bool)),
   V"fn0" ((T"VEXP" "CFL_Rules" [] --> alpha)),
   C"?" "bool"
    ((((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
        beta) --> bool) --> bool)),
   V"fn1"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      beta)),
   C"!" "bool" ((((T"VEXP" "CFL_Rules" [] --> bool) --> bool) --> bool)),
   V"P0" ((T"VEXP" "CFL_Rules" [] --> bool)),
   C"!" "bool"
    ((((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
        bool) --> bool) --> bool)),
   V"P1"
    ((T"prod" "pair" [T"VEXP" "CFL_Rules" [], T"VEXP" "CFL_Rules" []] -->
      bool)), V"V0" (T"VEXP" "CFL_Rules" []),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        (T"REXP" "CFL_Rules" [] --> bool)) --> bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"REXP" "CFL_Rules" [] --> bool))),
   V"v4" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v3" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"v2" (T"MREG" "CFL" []),
   V"v"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"g" ((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])),
   V"iv'" (T"REXP" "CFL_Rules" []), V"vi1" (T"REXP" "CFL_Rules" []),
   V"f1" ((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])),
   V"vo1" (T"REXP" "CFL_Rules" []),
   V"f2" ((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])),
   V"vo2" (T"REXP" "CFL_Rules" []),
   C"o" "combin"
    (((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []) -->
      ((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []) -->
       (T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])))),
   V"cond_f" ((T"VEXP" "CFL_Rules" [] --> bool)),
   V"v" (T"VEXP" "CFL_Rules" []),
   C"COND" "bool"
    ((bool -->
      (T"VEXP" "CFL_Rules" [] -->
       (T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])))),
   C"WHILE" "while"
    (((T"VEXP" "CFL_Rules" [] --> bool) -->
      ((T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []) -->
       (T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" [])))),
   C"o" "combin"
    (((bool --> bool) -->
      ((T"VEXP" "CFL_Rules" [] --> bool) -->
       (T"VEXP" "CFL_Rules" [] --> bool)))),
   V"stk"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      alpha)),
   V"iv"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      beta)),
   V"ov"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      gamma)),
   C"CONS" "list"
    ((T"REXP" "CFL_Rules" [] -->
      (T"list" "list" [T"REXP" "CFL_Rules" []] -->
       T"list" "list" [T"REXP" "CFL_Rules" []]))), V"context_f" (alpha)]
  val DT = Thm.disk_thm share_table
  in
  val REXP_TY_DEF =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (\%3. (%4 (\%5. (%4 (\%6. ((%7 ((%8 (%9 (\%3. ((%7
       ((%10 (%11 (\%12. ((%13 $1) ((\%12. (((%14 %15) ((%16 $0) ((%17 (%18
       (\%19. %20))) (%21 (\%22. %20))))) (\%23. %24))) $0))))) ((%10 (%25
       (\%26. ((%13 $1) ((\%26. (((%14 (%27 %15)) ((%16 (%28 (\%29. %20)))
       ((%17 $0) (%21 (\%22. %20))))) (\%23. %24))) $0))))) ((%10 (%30
       (\%31. ((%13 $1) ((\%31. (((%14 (%27 (%27 %15))) ((%16 (%28 (\%29.
       %20))) ((%17 (%18 (\%19. %20))) $0))) (\%23. %24))) $0))))) (%32
       (\%33. ((%8 ((%13 $1) ((\%33. (((%14 (%27 (%27 (%27 %15)))) ((%16
       (%28 (\%29. %20))) ((%17 (%18 (\%19. %20))) (%21 (\%22. %20)))))
       ((%34 $0) (\%23. %24)))) $0))) ($2 $0)))))))) ($2 $0))))) (%9 (\%35.
       ((%7 (%32 (\%36. (%32 (\%37. ((%8 ((%13 $2) (((\%36. (\%37. (((%14
       (%27 (%27 (%27 (%27 %15))))) ((%16 (%28 (\%29. %20))) ((%17 (%18
       (\%19. %20))) (%21 (\%22. %20))))) ((%34 $1) ((%34 $0) (\%23.
       %24)))))) $1) $0))) ((%8 ($4 $1)) ($4 $0)))))))) ($1 $0)))))) ($1
       $2)))))))) $0)))`)
  val REXP_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%38 (\%39. ((%40 (%41 (%42 $0))) $0)))) (%9 (\%43. ((%44
       ((\%3. (%4 (\%5. (%4 (\%6. ((%7 ((%8 (%9 (\%3. ((%7 ((%10 (%11
       (\%12. ((%13 $1) ((\%12. (((%14 %15) ((%16 $0) ((%17 (%18 (\%19.
       %20))) (%21 (\%22. %20))))) (\%23. %24))) $0))))) ((%10 (%25 (\%26.
       ((%13 $1) ((\%26. (((%14 (%27 %15)) ((%16 (%28 (\%29. %20))) ((%17
       $0) (%21 (\%22. %20))))) (\%23. %24))) $0))))) ((%10 (%30 (\%31.
       ((%13 $1) ((\%31. (((%14 (%27 (%27 %15))) ((%16 (%28 (\%29. %20)))
       ((%17 (%18 (\%19. %20))) $0))) (\%23. %24))) $0))))) (%32 (\%33.
       ((%8 ((%13 $1) ((\%33. (((%14 (%27 (%27 (%27 %15)))) ((%16 (%28
       (\%29. %20))) ((%17 (%18 (\%19. %20))) (%21 (\%22. %20))))) ((%34
       $0) (\%23. %24)))) $0))) ($2 $0)))))))) ($2 $0))))) (%9 (\%35. ((%7
       (%32 (\%36. (%32 (\%37. ((%8 ((%13 $2) (((\%36. (\%37. (((%14 (%27
       (%27 (%27 (%27 %15))))) ((%16 (%28 (\%29. %20))) ((%17 (%18 (\%19.
       %20))) (%21 (\%22. %20))))) ((%34 $1) ((%34 $0) (\%23. %24)))))) $1)
       $0))) ((%8 ($4 $1)) ($4 $0)))))))) ($1 $0)))))) ($1 $2))))))) $0))
       ((%13 (%42 (%41 $0))) $0)))))`)
  val prodCFL_Rules0_TY_DEF =
    DT(["DISK_THM"], [],
       `(%45 (\%46. ((%47 (\%35. (%4 (\%5. (%4 (\%6. ((%7 ((%8 (%9 (\%3.
       ((%7 ((%10 (%11 (\%12. ((%13 $1) ((\%12. (((%14 %15) ((%16 $0) ((%17
       (%18 (\%19. %20))) (%21 (\%22. %20))))) (\%23. %24))) $0))))) ((%10
       (%25 (\%26. ((%13 $1) ((\%26. (((%14 (%27 %15)) ((%16 (%28 (\%29.
       %20))) ((%17 $0) (%21 (\%22. %20))))) (\%23. %24))) $0))))) ((%10
       (%30 (\%31. ((%13 $1) ((\%31. (((%14 (%27 (%27 %15))) ((%16 (%28
       (\%29. %20))) ((%17 (%18 (\%19. %20))) $0))) (\%23. %24))) $0)))))
       (%32 (\%33. ((%8 ((%13 $1) ((\%33. (((%14 (%27 (%27 (%27 %15))))
       ((%16 (%28 (\%29. %20))) ((%17 (%18 (\%19. %20))) (%21 (\%22.
       %20))))) ((%34 $0) (\%23. %24)))) $0))) ($2 $0)))))))) ($2 $0)))))
       (%9 (\%35. ((%7 (%32 (\%36. (%32 (\%37. ((%8 ((%13 $2) (((\%36.
       (\%37. (((%14 (%27 (%27 (%27 (%27 %15))))) ((%16 (%28 (\%29. %20)))
       ((%17 (%18 (\%19. %20))) (%21 (\%22. %20))))) ((%34 $1) ((%34 $0)
       (\%23. %24)))))) $1) $0))) ((%8 ($4 $1)) ($4 $0)))))))) ($1 $0))))))
       ($0 $2)))))))) $0)))`)
  val prodCFL_Rules0_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%48 (\%49. ((%50 (%51 (%52 $0))) $0)))) (%9 (\%43. ((%44
       ((\%35. (%4 (\%5. (%4 (\%6. ((%7 ((%8 (%9 (\%3. ((%7 ((%10 (%11
       (\%12. ((%13 $1) ((\%12. (((%14 %15) ((%16 $0) ((%17 (%18 (\%19.
       %20))) (%21 (\%22. %20))))) (\%23. %24))) $0))))) ((%10 (%25 (\%26.
       ((%13 $1) ((\%26. (((%14 (%27 %15)) ((%16 (%28 (\%29. %20))) ((%17
       $0) (%21 (\%22. %20))))) (\%23. %24))) $0))))) ((%10 (%30 (\%31.
       ((%13 $1) ((\%31. (((%14 (%27 (%27 %15))) ((%16 (%28 (\%29. %20)))
       ((%17 (%18 (\%19. %20))) $0))) (\%23. %24))) $0))))) (%32 (\%33.
       ((%8 ((%13 $1) ((\%33. (((%14 (%27 (%27 (%27 %15)))) ((%16 (%28
       (\%29. %20))) ((%17 (%18 (\%19. %20))) (%21 (\%22. %20))))) ((%34
       $0) (\%23. %24)))) $0))) ($2 $0)))))))) ($2 $0))))) (%9 (\%35. ((%7
       (%32 (\%36. (%32 (\%37. ((%8 ((%13 $2) (((\%36. (\%37. (((%14 (%27
       (%27 (%27 (%27 %15))))) ((%16 (%28 (\%29. %20))) ((%17 (%18 (\%19.
       %20))) (%21 (\%22. %20))))) ((%34 $1) ((%34 $0) (\%23. %24)))))) $1)
       $0))) ((%8 ($4 $1)) ($4 $0)))))))) ($1 $0)))))) ($0 $2))))))) $0))
       ((%13 (%52 (%51 $0))) $0)))))`)
  val CFL_Rules1_def =
    DT([], [],
       `((%53 %54) (\%12. (%41 ((\%12. (((%14 %15) ((%16 $0) ((%17 (%18
       (\%19. %20))) (%21 (\%22. %20))))) (\%23. %24))) $0))))`)
  val CFL_Rules2_def =
    DT([], [],
       `((%55 %56) (\%26. (%41 ((\%26. (((%14 (%27 %15)) ((%16 (%28 (\%29.
       %20))) ((%17 $0) (%21 (\%22. %20))))) (\%23. %24))) $0))))`)
  val CFL_Rules3_def =
    DT([], [],
       `((%57 %58) (\%31. (%41 ((\%31. (((%14 (%27 (%27 %15))) ((%16 (%28
       (\%29. %20))) ((%17 (%18 (\%19. %20))) $0))) (\%23. %24))) $0))))`)
  val CFL_Rules4_def =
    DT([], [],
       `((%59 %60) (\%49. (%41 ((\%33. (((%14 (%27 (%27 (%27 %15)))) ((%16
       (%28 (\%29. %20))) ((%17 (%18 (\%19. %20))) (%21 (\%22. %20)))))
       ((%34 $0) (\%23. %24)))) (%52 $0)))))`)
  val CFL_Rules5_def =
    DT([], [],
       `((%61 %62) (\%63. (\%64. (%51 (((\%36. (\%37. (((%14 (%27 (%27 (%27
       (%27 %15))))) ((%16 (%28 (\%29. %20))) ((%17 (%18 (\%19. %20))) (%21
       (\%22. %20))))) ((%34 $1) ((%34 $0) (\%23. %24)))))) (%42 $1)) (%42
       $0))))))`)
  val CFL_Rules6 =
    DT([], [],
       `((%65 %66) (\%67. (%60 ((%68 (\%69. (%38 (\%70. (%38 (\%71. ((%50
       ($2 ((%72 $1) $0))) ((%62 $1) $0)))))))) $0))))`)
  val RR = DT([], [], `((%53 %73) %54)`)
  val RM = DT([], [], `((%55 %74) %56)`)
  val RC = DT([], [], `((%57 %75) %58)`)
  val PR = DT([], [], `((%65 %76) %66)`)
  val REXP_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%77 (\%78. (%79 (\%80. (%81 (\%82. (%83 (\%84. (%85 (\%12.
       ((%86 (((((%87 $4) $3) $2) $1) (%73 $0))) ($4 $0))))))))))))) ((%8
       (%77 (\%78. (%79 (\%80. (%81 (\%82. (%83 (\%84. (%88 (\%26. ((%86
       (((((%87 $4) $3) $2) $1) (%74 $0))) ($3 $0))))))))))))) ((%8 (%77
       (\%78. (%79 (\%80. (%81 (\%82. (%83 (\%84. (%89 (\%31. ((%86
       (((((%87 $4) $3) $2) $1) (%75 $0))) ($2 $0))))))))))))) (%77 (\%78.
       (%79 (\%80. (%81 (\%82. (%83 (\%84. (%90 (\%67. ((%86 (((((%87 $4)
       $3) $2) $1) (%76 $0))) ($1 $0)))))))))))))))`)
  val REXP_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%85 (\%12. ((%91 (%92 (%73 $0))) ((%93 (%94 (%95 %96))) (%97
       $0)))))) ((%8 (%88 (\%26. ((%91 (%92 (%74 $0))) ((%93 (%94 (%95
       %96))) ((%98 (\%99. (\%100. ((%93 ((\%99. $0) $1)) (%101 $0)))))
       $0)))))) ((%8 (%89 (\%31. ((%91 (%92 (%75 $0))) (%94 (%95 %96))))))
       ((%8 (%90 (\%67. ((%91 (%92 (%76 $0))) ((%93 (%94 (%95 %96))) (%102
       $0)))))) (%38 (\%63. (%38 (\%64. ((%91 (%102 ((%72 $1) $0))) ((%93
       (%94 (%95 %96))) ((%93 (%92 $1)) (%92 $0))))))))))))`)
  val mread_def =
    DT(["DISK_THM"], [],
       `((%8 (%103 (\%104. (%85 (\%105. ((%106 ((%107 $1) (%73 $0))) ((%108
       $1) (%109 $0)))))))) ((%8 (%103 (\%104. (%88 (\%110. ((%106 ((%107
       $1) (%74 $0))) ((%108 $1) (%111 $0)))))))) (%103 (\%104. (%89
       (\%112. ((%106 ((%107 $1) (%75 $0))) $0)))))))`)
  val proper_def =
    DT([], [],
       `((%113 %114) (%115 (\%116. (\%117. ((%8 ((%106 ((%118 $1) (%94 (%95
       (%95 (%119 %96)))))) (%120 (%94 (%119 (%95 (%119 (%95 (%95 (%119
       %96)))))))))) ((%106 ((%118 $1) (%94 (%95 (%119 (%119 %96))))))
       (%120 (%94 (%119 (%95 (%119 (%95 (%95 (%119 %96))))))))))))))`)
  val HSPEC_def =
    DT([], [],
       `(%121 (\%122. (%123 (\%124. (%121 (\%125. ((%44 (((%126 $2) $1)
       $0)) (%103 (\%104. ((%7 ($3 $0)) ($1 ((%127 $2) $0))))))))))))`)
  val PSPEC_def =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%131 (\%132. (%133
       (\%134. (%135 (\%136. (%137 (\%138. ((%44 ((((%139 $6) ((%140 $5)
       $4)) $3) ((%141 $2) ((%142 $1) $0)))) (%143 (\%144. (%145 (\%146.
       (((%126 (\%104. ((%8 ($8 $0)) ((%8 ((%86 ($6 $0)) $1)) ((%147 ($5
       $0)) $2))))) $8) (\%104. ((%8 ($7 $0)) ((%8 ((%86 ($6 $0)) $1))
       ((%148 ($3 $0)) ($4 $2)))))))))))))))))))))))))`)
  val valid_push_def =
    DT(["DISK_THM"], [],
       `(%149 (\%150. (%151 (\%152. (%153 (\%154. (%155 (\%156. (%157
       (\%158. (%159 (\%160. (%161 (\%162. (%163 (\%164. ((%44 ((%165
       ((%166 $7) ((%167 $6) ((%168 $5) $4)))) ((%169 $3) ((%170 $2) ((%171
       $1) $0))))) (%145 (\%172. (%145 (\%173. ((%7 ((%8 ((%147 ($9 $0))
       ($9 $1))) ((%174 ($6 $0)) ($7 ($8 $1))))) ((%8 ((%175 ($5 $0)) ($5
       $1))) ((%176 ($2 $0)) ($3 ($4 $1))))))))))))))))))))))))))`)
  val P_intact_def =
    DT(["DISK_THM"], [],
       `(%177 (\%178. (%177 (\%179. (%149 (\%150. (%151 (\%180. ((%44
       ((%181 ((%182 $3) $2)) ((%183 $1) $0))) (%145 (\%172. (%145 (\%173.
       ((%7 ((%8 ((%147 ($3 $0)) ($3 $1))) ((%8 ($5 $1)) ($4 $0)))) ((%148
       ($2 $0)) ($2 $1))))))))))))))))`)
  val VEXP_TY_DEF =
    DT(["DISK_THM"], [],
       `(%184 (\%185. ((%186 (\%187. (%188 (\%189. (%188 (\%190. ((%7 ((%8
       (%191 (\%187. ((%7 ((%10 (%30 (\%31. ((%192 $1) ((\%31. (((%193 %15)
       $0) (\%23. %194))) $0))))) (%195 (\%196. ((%8 ((%192 $1) ((\%196.
       (((%193 (%27 %15)) (%21 (\%22. %20))) ((%197 $0) (\%23. %194))))
       $0))) ($2 $0)))))) ($2 $0))))) (%191 (\%198. ((%7 (%195 (\%199.
       (%195 (\%200. ((%8 ((%192 $2) (((\%199. (\%200. (((%193 (%27 (%27
       %15))) (%21 (\%22. %20))) ((%197 $1) ((%197 $0) (\%23. %194))))))
       $1) $0))) ((%8 ($4 $1)) ($4 $0)))))))) ($1 $0)))))) ($1 $2))))))))
       $0)))`)
  val VEXP_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%201 (\%202. ((%203 (%204 (%205 $0))) $0)))) (%191 (\%206.
       ((%44 ((\%187. (%188 (\%189. (%188 (\%190. ((%7 ((%8 (%191 (\%187.
       ((%7 ((%10 (%30 (\%31. ((%192 $1) ((\%31. (((%193 %15) $0) (\%23.
       %194))) $0))))) (%195 (\%196. ((%8 ((%192 $1) ((\%196. (((%193 (%27
       %15)) (%21 (\%22. %20))) ((%197 $0) (\%23. %194)))) $0))) ($2
       $0)))))) ($2 $0))))) (%191 (\%198. ((%7 (%195 (\%199. (%195 (\%200.
       ((%8 ((%192 $2) (((\%199. (\%200. (((%193 (%27 (%27 %15))) (%21
       (\%22. %20))) ((%197 $1) ((%197 $0) (\%23. %194)))))) $1) $0))) ((%8
       ($4 $1)) ($4 $0)))))))) ($1 $0)))))) ($1 $2))))))) $0)) ((%192 (%205
       (%204 $0))) $0)))))`)
  val prodCFL_Rules7_TY_DEF =
    DT(["DISK_THM"], [],
       `(%207 (\%208. ((%209 (\%198. (%188 (\%189. (%188 (\%190. ((%7 ((%8
       (%191 (\%187. ((%7 ((%10 (%30 (\%31. ((%192 $1) ((\%31. (((%193 %15)
       $0) (\%23. %194))) $0))))) (%195 (\%196. ((%8 ((%192 $1) ((\%196.
       (((%193 (%27 %15)) (%21 (\%22. %20))) ((%197 $0) (\%23. %194))))
       $0))) ($2 $0)))))) ($2 $0))))) (%191 (\%198. ((%7 (%195 (\%199.
       (%195 (\%200. ((%8 ((%192 $2) (((\%199. (\%200. (((%193 (%27 (%27
       %15))) (%21 (\%22. %20))) ((%197 $1) ((%197 $0) (\%23. %194))))))
       $1) $0))) ((%8 ($4 $1)) ($4 $0)))))))) ($1 $0)))))) ($0 $2))))))))
       $0)))`)
  val prodCFL_Rules7_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%210 (\%211. ((%212 (%213 (%214 $0))) $0)))) (%191 (\%206.
       ((%44 ((\%198. (%188 (\%189. (%188 (\%190. ((%7 ((%8 (%191 (\%187.
       ((%7 ((%10 (%30 (\%31. ((%192 $1) ((\%31. (((%193 %15) $0) (\%23.
       %194))) $0))))) (%195 (\%196. ((%8 ((%192 $1) ((\%196. (((%193 (%27
       %15)) (%21 (\%22. %20))) ((%197 $0) (\%23. %194)))) $0))) ($2
       $0)))))) ($2 $0))))) (%191 (\%198. ((%7 (%195 (\%199. (%195 (\%200.
       ((%8 ((%192 $2) (((\%199. (\%200. (((%193 (%27 (%27 %15))) (%21
       (\%22. %20))) ((%197 $1) ((%197 $0) (\%23. %194)))))) $1) $0))) ((%8
       ($4 $1)) ($4 $0)))))))) ($1 $0)))))) ($0 $2))))))) $0)) ((%192 (%214
       (%213 $0))) $0)))))`)
  val CFL_Rules8_def =
    DT([], [],
       `((%215 %216) (\%31. (%204 ((\%31. (((%193 %15) $0) (\%23. %194)))
       $0))))`)
  val CFL_Rules9_def =
    DT([], [],
       `((%217 %218) (\%211. (%204 ((\%196. (((%193 (%27 %15)) (%21 (\%22.
       %20))) ((%197 $0) (\%23. %194)))) (%214 $0)))))`)
  val CFL_Rules10_def =
    DT([], [],
       `((%219 %220) (\%221. (\%222. (%213 (((\%199. (\%200. (((%193 (%27
       (%27 %15))) (%21 (\%22. %20))) ((%197 $1) ((%197 $0) (\%23.
       %194)))))) (%205 $1)) (%205 $0))))))`)
  val CFL_Rules11 =
    DT([], [],
       `((%223 %224) (\%225. (%218 ((%226 (\%227. (%201 (\%228. (%201
       (\%229. ((%212 ($2 ((%230 $1) $0))) ((%220 $1) $0)))))))) $0))))`)
  val SG = DT([], [], `((%215 %231) %216)`)
  val VT = DT([], [], `((%223 %232) %224)`)
  val VEXP_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%81 (\%233. (%234 (\%235. (%89 (\%31. ((%86 (((%236 $2) $1)
       (%231 $0))) ($2 $0))))))))) (%81 (\%233. (%234 (\%235. (%237 (\%225.
       ((%86 (((%236 $2) $1) (%232 $0))) ($1 $0)))))))))`)
  val VEXP_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%89 (\%31. ((%91 (%238 (%231 $0))) (%94 (%95 %96)))))) ((%8
       (%237 (\%225. ((%91 (%238 (%232 $0))) ((%93 (%94 (%95 %96))) (%239
       $0)))))) (%201 (\%221. (%201 (\%222. ((%91 (%239 ((%230 $1) $0)))
       ((%93 (%94 (%95 %96))) ((%93 (%238 $1)) (%238 $0))))))))))`)
  val readv_tupled_primitive_def =
    DT([], [],
       `((%240 %241) ((%242 (%243 (\%244. ((%8 (%245 $0)) ((%8 (%38 (\%246.
       (%38 (\%39. (%103 (\%104. (($3 ((%247 $0) $1)) ((%247 $0) (%76 ((%72
       $1) $2))))))))))) (%38 (\%39. (%38 (\%246. (%103 (\%104. (($3 ((%247
       $0) $1)) ((%247 $0) (%76 ((%72 $2) $1))))))))))))))) (\%248. (\%249.
       ((%250 (\%104. (\%251. (((((%252 (\%253. (%254 (%231 ((%107 $2) (%73
       $0)))))) (\%255. (%254 (%231 ((%107 $2) (%74 $0)))))) (\%256. (%254
       (%231 ((%107 $2) (%75 $0)))))) (\%257. ((%258 (\%39. (\%246. (%254
       (%232 ((%230 ($6 ((%247 $4) $1))) ($6 ((%247 $4) $0)))))))) $0)))
       $0)))) $0)))))`)
  val readv_curried_def =
    DT([], [],
       `(%103 (\%259. (%38 (\%260. ((%203 ((%261 $1) $0)) (%241 ((%247 $1)
       $0)))))))`)
  val push_def =
    DT([], [],
       `(%145 (\%146. (%262 (\%263. ((%264 ((%265 $1) $0)) ((%266 $1)
       $0))))))`)
  val top_def = DT([], [], `((%267 %268) %269)`)
  val pop_def = DT([], [], `((%270 %271) %272)`)
  val VSPEC_def =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%273 (\%274. (%38
       (\%275. (%276 (\%277. (%38 (\%278. ((%44 ((((%279 $6) ((%140 $5)
       $4)) $3) ((%280 $2) ((%281 $1) $0)))) ((((%282 $6) ((%140 $5) $4))
       (\%104. ((%283 (%261 $0)) $4))) ((%284 (\%104. ((%261 $0) $3)))
       ((%285 $1) (\%104. ((%261 $0) $1))))))))))))))))))))`)
  val V_intact_def =
    DT(["DISK_THM"], [],
       `(%121 (\%122. (%121 (\%125. (%38 (\%286. ((%44 (%287 ((%288 $2)
       ((%289 $1) $0)))) (%290 (\%228. ((%8 (%103 (\%104. ((%7 ($4 $0))
       ((%203 ((%261 $0) $2)) $1))))) (%103 (\%104. ((%7 ($3 $0)) ((%203
       ((%261 $0) $2)) $1))))))))))))))`)
  val datatype_REXP =
    DT(["DISK_THM"], [], `(%291 ((((%292 %73) %74) %75) %76))`)
  val REXP_11 =
    DT(["DISK_THM"], [],
       `((%8 (%85 (\%12. (%85 (\%293. ((%44 ((%40 (%73 $1)) (%73 $0)))
       ((%294 $1) $0))))))) ((%8 (%88 (\%26. (%88 (\%295. ((%44 ((%40 (%74
       $1)) (%74 $0))) ((%296 $1) $0))))))) ((%8 (%89 (\%31. (%89 (\%297.
       ((%44 ((%40 (%75 $1)) (%75 $0))) ((%106 $1) $0))))))) (%90 (\%67.
       (%90 (\%298. ((%44 ((%40 (%76 $1)) (%76 $0))) ((%299 $1)
       $0)))))))))`)
  val REXP_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%88 (\%295. (%85 (\%12. (%300 ((%40 (%73 $0)) (%74 $1))))))))
       ((%8 (%89 (\%297. (%85 (\%12. (%300 ((%40 (%73 $0)) (%75 $1))))))))
       ((%8 (%90 (\%298. (%85 (\%12. (%300 ((%40 (%73 $0)) (%76 $1))))))))
       ((%8 (%89 (\%297. (%88 (\%26. (%300 ((%40 (%74 $0)) (%75 $1))))))))
       ((%8 (%90 (\%298. (%88 (\%26. (%300 ((%40 (%74 $0)) (%76 $1))))))))
       (%90 (\%298. (%89 (\%31. (%300 ((%40 (%75 $0)) (%76 $1))))))))))))`)
  val REXP_case_cong =
    DT(["DISK_THM"], [],
       `(%38 (\%301. (%38 (\%302. (%77 (\%78. (%79 (\%80. (%81 (\%82. (%83
       (\%84. ((%7 ((%8 ((%40 $5) $4)) ((%8 (%85 (\%12. ((%7 ((%40 $5) (%73
       $0))) ((%86 ($4 $0)) (%303 $0)))))) ((%8 (%88 (\%26. ((%7 ((%40 $5)
       (%74 $0))) ((%86 ($3 $0)) (%304 $0)))))) ((%8 (%89 (\%31. ((%7 ((%40
       $5) (%75 $0))) ((%86 ($2 $0)) (%305 $0)))))) (%90 (\%67. ((%7 ((%40
       $5) (%76 $0))) ((%86 ($1 $0)) (%306 $0)))))))))) ((%86 (((((%87 $3)
       $2) $1) $0) $5)) (((((%87 %303) %304) %305) %306)
       $4)))))))))))))))`)
  val REXP_nchotomy =
    DT(["DISK_THM"], [],
       `(%38 (\%307. ((%10 (%11 (\%308. ((%40 $1) (%73 $0))))) ((%10 (%25
       (\%309. ((%40 $1) (%74 $0))))) ((%10 (%30 (\%112. ((%40 $1) (%75
       $0))))) (%310 (\%311. ((%40 $1) (%76 $0)))))))))`)
  val REXP_Axiom =
    DT(["DISK_THM"], [],
       `(%77 (\%312. (%79 (\%80. (%81 (\%82. (%313 (\%314. (%315 (\%316.
       (%317 (\%318. (%319 (\%320. ((%8 (%85 (\%12. ((%86 ($2 (%73 $0)))
       ($7 $0))))) ((%8 (%88 (\%26. ((%86 ($2 (%74 $0))) ($6 $0))))) ((%8
       (%89 (\%31. ((%86 ($2 (%75 $0))) ($5 $0))))) ((%8 (%90 (\%67. ((%86
       ($2 (%76 $0))) (($4 $0) ($1 $0)))))) (%38 (\%63. (%38 (\%64. ((%147
       ($2 ((%72 $1) $0))) (((($4 $1) $0) ($3 $1)) ($3
       $0)))))))))))))))))))))))))`)
  val REXP_induction =
    DT(["DISK_THM"], [],
       `(%321 (\%322. (%323 (\%324. ((%7 ((%8 (%85 (\%308. ($2 (%73 $0)))))
       ((%8 (%88 (\%309. ($2 (%74 $0))))) ((%8 (%89 (\%112. ($2 (%75
       $0))))) ((%8 (%90 (\%311. ((%7 ($1 $0)) ($2 (%76 $0)))))) (%38
       (\%307. (%38 (\%325. ((%7 ((%8 ($3 $1)) ($3 $0))) ($2 ((%72 $1)
       $0)))))))))))) ((%8 (%38 (\%307. ($2 $0)))) (%90 (\%311. ($1
       $0)))))))))`)
  val CFL_SC_RULE =
    DT(["DISK_THM"], [],
       `(%121 (\%122. (%121 (\%125. (%121 (\%326. (%123 (\%327. (%123
       (\%328. ((%7 ((%8 (%329 $1)) ((%8 (%329 $0)) ((%8 (((%126 $4) $1)
       $3)) (((%126 $3) $0) $2))))) (((%126 $4) ((%330 $1) $0))
       $2))))))))))))`)
  val BLK_EQ_SC =
    DT(["DISK_THM"], [],
       `(%331 (\%332. (%333 (\%334. (%103 (\%104. ((%8 ((%335 ((%127 (%336
       ((%337 $2) $1))) $0)) ((%127 ((%330 (%336 ((%337 $2) %338))) (%336
       $1))) $0))) ((%335 ((%127 (%336 ((%339 $2) $1))) $0)) ((%127 ((%330
       (%336 $1)) (%336 ((%337 $2) %338)))) $0)))))))))`)
  val EMPTY_BLK_AXIOM =
    DT(["DISK_THM"], [],
       `(%121 (\%122. (%121 (\%125. ((%7 (%103 (\%104. ((%7 ($2 $0)) ($1
       $0))))) (((%126 $1) (%336 %338)) $0))))))`)
  val BLK_RULE =
    DT(["DISK_THM"], [],
       `(%121 (\%122. (%121 (\%125. (%121 (\%326. (%331 (\%332. (%333
       (\%334. ((%7 ((%8 (((%126 $3) (%336 ((%337 $1) %338))) $2)) (((%126
       $4) (%336 $0)) $3))) (((%126 $4) (%336 ((%339 $1) $0)))
       $2))))))))))))`)
  val CFL_CJ_RULE =
    DT(["DISK_THM"], [],
       `(%121 (\%122. (%121 (\%125. (%340 (\%341. (%123 (\%327. (%123
       (\%328. (%145 (\%172. ((%7 ((%8 (%329 $2)) ((%8 (%329 $1)) ((%8
       (((%126 (\%104. ((%8 ((%342 $4) $0)) ($6 $0)))) $2) $4)) (((%126
       (\%104. ((%8 (%300 ((%342 $4) $0))) ($6 $0)))) $1) $4))))) (((%126
       $5) (((%343 $3) $2) $1)) $4))))))))))))))`)
  val CFL_CJ_RULE_2 =
    DT(["DISK_THM"], [],
       `(%121 (\%122. (%121 (\%125. (%340 (\%341. (%123 (\%327. (%123
       (\%328. (%145 (\%172. ((%7 ((%8 (%329 $2)) ((%8 (%329 $1)) ((%8
       (((%126 $5) $2) $4)) (((%126 $5) $1) $4))))) (((%126 $5) (((%343 $3)
       $2) $1)) $4))))))))))))))`)
  val CFL_TR_RULE =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%344. (%121 (\%122. (%145 (\%345. ((%7 ((%8
       (%329 $2)) ((%8 (%346 ((%347 (%348 $3)) (%349 $2)))) (((%126 $1) $2)
       $1)))) (((%126 $1) ((%350 $3) $2)) $1))))))))))`)
  val WF_DEF_2 =
    DT(["DISK_THM"], [],
       `((%44 (%351 %352)) (%177 (\%178. ((%7 (%353 (\%354. ($1 $0))))
       (%353 (\%355. ((%8 ($1 $0)) (%145 (\%356. ((%7 ((%352 $0) $1)) (%300
       ($2 $0))))))))))))`)
  val WF_TR_LEM_1 =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%128. (%145 (\%172. ((%7 ((%8 (%329 $1))
       (%357 (\%358. (\%359. ((%8 (%300 ((%342 $4) $0))) ((%335 $1) ((%127
       $3) $0)))))))) (%346 ((%347 (%348 $2)) (%349 $1))))))))))`)
  val WF_TR_LEM_2 =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%128. (%131 (\%360. (%361 (\%362. (%177
       (\%363. ((%7 ((%8 (%103 (\%104. ((%44 ($1 ($3 $0))) ((%342 $5)
       $0))))) ((%8 (%103 (\%104. ((%86 ($3 ((%127 $4) $0))) ($2 ($3
       $0)))))) (%351 (\%364. (\%365. ((%8 (%300 ($2 $0))) ((%86 $1) ($3
       $0))))))))) (%357 (\%358. (\%359. ((%8 (%300 ((%342 $6) $0))) ((%335
       $1) ((%127 $5) $0)))))))))))))))))`)
  val WF_TR_LEM_3 =
    DT(["DISK_THM"], [],
       `(%177 (\%363. (%361 (\%362. ((%7 (%366 (\%352. ((%8 (%351 $0))
       (%145 (\%365. (%143 (\%367. ((%7 (%300 ($4 $1))) (($2 ($3 $1))
       $1)))))))))) (%351 (\%364. (\%365. ((%8 (%300 ($3 $0))) ((%86 $1)
       ($2 $0)))))))))))`)
  val WF_TR_THM_1 =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%128. (%131 (\%360. (%361 (\%362. (%177
       (\%363. (%121 (\%129. ((%7 ((%8 (%103 (\%104. ((%44 ($2 ($4 $0)))
       ((%342 $6) $0))))) ((%8 (%103 (\%104. ((%7 ($1 $0)) ((%86 ($4 ((%127
       $5) $0))) ($3 ($4 $0))))))) (%351 (\%364. (\%365. ((%8 (%300 ($3
       $0))) ((%86 $1) ($4 $0))))))))) (%357 (\%358. (\%359. ((%8 ($2 $0))
       ((%8 (%300 ((%342 $7) $0))) ((%335 $1) ((%127 $6)
       $0))))))))))))))))))))`)
  val PSPEC_STACK =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%131 (\%132. (%133
       (\%134. (%135 (\%136. (%137 (\%138. (%145 (\%146. ((%7 ((((%139 $7)
       ((%140 $6) $5)) $4) ((%141 $3) ((%142 $2) $1)))) (((%126 (\%104.
       ((%8 ($7 $0)) ((%86 ($5 $0)) $1)))) $7) (\%104. ((%8 ($6 $0)) ((%86
       ($5 $0)) $1)))))))))))))))))))))`)
  val PSPEC_CHARACTERISTIC =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%131 (\%132. (%133
       (\%134. (%135 (\%136. (%137 (\%138. ((%7 ((((%139 $6) ((%140 $5)
       $4)) $3) ((%141 $2) ((%142 $1) $0)))) (((%126 (\%104. ((%8 ($6 $0))
       ((%147 ($3 $0)) %144)))) $6) (\%104. ((%8 ($5 $0)) ((%148 ($1 $0))
       ($2 %144))))))))))))))))))))`)
  val PRJ_SHUFFLE_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%131 (\%132. (%133
       (\%134. (%135 (\%136. (%137 (\%138. (%153 (\%368. ((%7 ((((%139 $7)
       ((%140 $6) $5)) $4) ((%141 $3) ((%142 $2) $1)))) ((((%369 $7) ((%140
       $6) $5)) $4) ((%370 $3) ((%371 ((%372 $0) $2)) ((%373 $0)
       $1)))))))))))))))))))))`)
  val PRJ_SHUFFLE_RULE2 =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%131 (\%132. (%133
       (\%134. (%135 (\%136. (%137 (\%138. (%374 (\%375. (%376 (\%377. ((%7
       ((%8 ((((%139 $8) ((%140 $7) $6)) $5) ((%141 $4) ((%142 $3) $2))))
       ((%378 ((%379 $1) $0)) ((%380 $3) $4)))) ((((%381 $8) ((%140 $7)
       $6)) $5) ((%382 $0) ((%383 $1) $2))))))))))))))))))))))`)
  val PRJ_SC_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%384. (%123 (\%385. (%121 (\%386. (%121 (\%387. (%121
       (\%388. (%131 (\%132. (%133 (\%389. (%135 (\%390. (%153 (\%391.
       (%137 (\%392. (%376 (\%393. ((%7 ((%8 (%329 $10)) ((%8 (%329 $9))
       ((%8 ((((%139 $10) ((%140 $8) $7)) $5) ((%141 $4) ((%142 $3) $1))))
       ((((%394 $9) ((%140 $7) $6)) $5) ((%395 $1) ((%396 $2) $0)))))))
       ((((%369 ((%330 $10) $9)) ((%140 $8) $6)) $5) ((%370 $4) ((%371
       ((%372 $2) $3)) $0))))))))))))))))))))))))))`)
  val PRJ_CJ_RULE =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%397. (%123 (\%398. (%121 (\%129. (%121
       (\%130. (%131 (\%132. (%399 (\%400. (%133 (\%134. (%135 (\%390.
       (%135 (\%401. (%137 (\%138. ((%7 ((%8 (%329 $9)) ((%8 (%329 $8))
       ((%8 ((((%139 $9) ((%140 $7) $6)) $5) ((%141 $3) ((%142 $2) $0))))
       ((%8 ((((%139 $8) ((%140 $7) $6)) $5) ((%141 $3) ((%142 $1) $0))))
       (%103 (\%104. ((%44 ($5 ($4 $0))) ((%342 $11) $0))))))))) ((((%139
       (((%343 $10) $9) $8)) ((%140 $7) $6)) $5) ((%141 $3) ((%142 (\%144.
       (((%402 ($5 $0)) ($3 $0)) ($2 $0)))) $0))))))))))))))))))))))))))`)
  val PRJ_TR_RULE =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%128. (%121 (\%129. (%131 (\%132. (%399
       (\%400. (%133 (\%403. (%404 (\%405. ((%7 ((%8 (%329 $5)) ((%8 (%357
       (\%358. (\%359. ((%8 (%300 ((%342 $8) $0))) ((%335 $1) ((%127 $7)
       $0))))))) ((%8 (%103 (\%104. ((%44 ($3 ($2 $0))) ((%342 $7) $0)))))
       ((((%406 $5) ((%140 $4) $4)) $3) ((%407 $1) ((%408 $0) $1)))))))
       ((((%406 ((%350 $6) $5)) ((%140 $4) $4)) $3) ((%407 $1) ((%408
       ((%409 ((%410 %300) $2)) $0)) $1))))))))))))))))))`)
  val PRJ_TR_RULE_2 =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%128. (%131 (\%132. (%399 (\%400. (%133
       (\%403. (%404 (\%405. ((%7 ((%8 (%329 $4)) ((%8 (%103 (\%104. ((%44
       ($3 ($2 $0))) ((%342 $6) $0))))) ((%8 (%411 (\%412. ((%8 (%413 $0))
       (%143 (\%414. (%415 (\%416. ((%7 (%300 ($5 $1))) (($2 ($3 $1))
       $1)))))))))) ((((%406 $4) ((%140 (\%104. %20)) (\%104. %20))) $3)
       ((%407 $1) ((%408 $0) $1))))))) ((((%406 ((%350 $5) $4)) ((%140
       (\%104. %20)) (\%104. %20))) $3) ((%407 $1) ((%408 ((%409 ((%410
       %300) $2)) $0)) $1))))))))))))))))`)
  val PRJ_STRENGTHEN_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%417. (%121 (\%130. (%131
       (\%132. (%133 (\%134. (%135 (\%136. (%137 (\%138. ((%7 ((%8 (%329
       $7)) ((%8 ((((%139 $7) ((%140 $6) $4)) $3) ((%141 $2) ((%142 $1)
       $0)))) (%103 (\%104. ((%7 ($6 $0)) ($7 $0))))))) ((((%139 $7) ((%140
       $5) $4)) $3) ((%141 $2) ((%142 $1) $0))))))))))))))))))))`)
  val PRJ_WEAKEN_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%121 (\%418. (%131
       (\%132. (%133 (\%134. (%135 (\%136. (%137 (\%138. ((%7 ((%8 (%329
       $7)) ((%8 ((((%139 $7) ((%140 $6) $5)) $3) ((%141 $2) ((%142 $1)
       $0)))) (%103 (\%104. ((%7 ($6 $0)) ($5 $0))))))) ((((%139 $7) ((%140
       $6) $4)) $3) ((%141 $2) ((%142 $1) $0))))))))))))))))))))`)
  val PRJ_POP_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%131 (\%132. (%133
       (\%134. (%135 (\%136. (%137 (\%138. (%376 (\%419. (%420 (\%421.
       (%422 (\%423. (%424 (\%425. ((%7 ((%8 ((((%139 $10) ((%140 $9) $8))
       $7) ((%141 $6) ((%142 $5) $4)))) ((%426 ((%427 $7) ((%141 $6) ((%142
       $5) $4)))) ((%428 $3) ((%429 $2) ((%430 $1) $0)))))) ((((%431 $10)
       ((%140 $9) $8)) $3) ((%429 $2) ((%430 $1)
       $0))))))))))))))))))))))))))`)
  val PRJ_PUSH_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%131 (\%132. (%133
       (\%134. (%135 (\%136. (%137 (\%138. (%432 (\%433. (%420 (\%434. ((%7
       ((%8 ((((%139 $8) ((%140 $7) $6)) $5) ((%141 $4) ((%142 $3) $2))))
       ((%435 ((%140 $7) $6)) ((%436 $5) $0)))) ((((%437 $8) ((%140 $7)
       $6)) $0) ((%141 $4) ((%142 $3) $2))))))))))))))))))))))`)
  val datatype_VEXP = DT(["DISK_THM"], [], `(%291 ((%438 %231) %232))`)
  val VEXP_11 =
    DT(["DISK_THM"], [],
       `((%8 (%89 (\%31. (%89 (\%297. ((%44 ((%203 (%231 $1)) (%231 $0)))
       ((%106 $1) $0))))))) (%237 (\%225. (%237 (\%439. ((%44 ((%203 (%232
       $1)) (%232 $0))) ((%440 $1) $0)))))))`)
  val VEXP_distinct =
    DT(["DISK_THM"], [],
       `(%237 (\%439. (%89 (\%31. (%300 ((%203 (%231 $0)) (%232 $1)))))))`)
  val VEXP_case_cong =
    DT(["DISK_THM"], [],
       `(%201 (\%441. (%201 (\%442. (%81 (\%233. (%234 (\%235. ((%7 ((%8
       ((%203 $3) $2)) ((%8 (%89 (\%31. ((%7 ((%203 $3) (%231 $0))) ((%86
       ($2 $0)) (%443 $0)))))) (%237 (\%225. ((%7 ((%203 $3) (%232 $0)))
       ((%86 ($1 $0)) (%444 $0)))))))) ((%86 (((%236 $1) $0) $3)) (((%236
       %443) %444) $2)))))))))))`)
  val VEXP_nchotomy =
    DT(["DISK_THM"], [],
       `(%201 (\%445. ((%10 (%30 (\%112. ((%203 $1) (%231 $0))))) (%446
       (\%447. ((%203 $1) (%232 $0)))))))`)
  val VEXP_Axiom =
    DT(["DISK_THM"], [],
       `(%81 (\%448. (%449 (\%450. (%451 (\%452. (%453 (\%454. (%455
       (\%456. ((%8 (%89 (\%31. ((%86 ($2 (%231 $0))) ($5 $0))))) ((%8
       (%237 (\%225. ((%86 ($2 (%232 $0))) (($4 $0) ($1 $0)))))) (%201
       (\%221. (%201 (\%222. ((%147 ($2 ((%230 $1) $0))) (((($4 $1) $0) ($3
       $1)) ($3 $0)))))))))))))))))))`)
  val VEXP_induction =
    DT(["DISK_THM"], [],
       `(%457 (\%458. (%459 (\%460. ((%7 ((%8 (%89 (\%112. ($2 (%231
       $0))))) ((%8 (%237 (\%447. ((%7 ($1 $0)) ($2 (%232 $0)))))) (%201
       (\%445. (%201 (\%461. ((%7 ((%8 ($3 $1)) ($3 $0))) ($2 ((%230 $1)
       $0)))))))))) ((%8 (%201 (\%445. ($2 $0)))) (%237 (\%447. ($1
       $0)))))))))`)
  val readv_ind =
    DT(["DISK_THM"], [],
       `(%462 (\%463. ((%7 ((%8 (%103 (\%104. (%38 (\%39. (%38 (\%246. ((%7
       ((%8 (($3 $2) $1)) (($3 $2) $0))) (($3 $2) (%76 ((%72 $1)
       $0))))))))))) ((%8 (%103 (\%104. (%89 (\%464. (($2 $1) (%75
       $0))))))) ((%8 (%103 (\%104. (%88 (\%465. (($2 $1) (%74 $0)))))))
       (%103 (\%104. (%85 (\%466. (($2 $1) (%73 $0)))))))))) (%103 (\%467.
       (%38 (\%251. (($2 $1) $0))))))))`)
  val readv_def =
    DT(["DISK_THM"], [],
       `((%8 ((%203 ((%261 %104) (%76 ((%72 %39) %246)))) (%232 ((%230
       ((%261 %104) %39)) ((%261 %104) %246))))) ((%8 ((%203 ((%261 %104)
       (%75 %464))) (%231 ((%107 %104) (%75 %464))))) ((%8 ((%203 ((%261
       %104) (%74 %465))) (%231 ((%107 %104) (%74 %465))))) ((%203 ((%261
       %104) (%73 %466))) (%231 ((%107 %104) (%73 %466)))))))`)
  val V_SHUFFLE_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%273 (\%274. (%38 (\%275. (%276 (\%277. (%38 (\%278.
       (%276 (\%468. (%38 (\%469. ((%7 ((%8 ((((%279 $6) ((%140 %129)
       %130)) $5) ((%280 $4) ((%281 $3) $2)))) (%103 (\%104. ((%203 ($2
       ((%261 $0) $1))) ($4 ((%261 $0) $5))))))) ((((%279 $6) ((%140 %129)
       %130)) $5) ((%280 $0) ((%281 $1) $2))))))))))))))))))`)
  val V_SC_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%384. (%123 (\%385. (%121 (\%386. (%121 (\%387. (%121
       (\%388. (%273 (\%274. (%38 (\%470. (%276 (\%471. (%38 (\%472. (%276
       (\%473. (%38 (\%474. ((%7 ((%8 (%329 $10)) ((%8 (%329 $9)) ((%8
       ((((%279 $10) ((%140 $8) $7)) $5) ((%280 $4) ((%281 $3) $2))))
       ((((%279 $9) ((%140 $7) $6)) $5) ((%280 $2) ((%281 $1) $0)))))))
       ((((%279 ((%330 $10) $9)) ((%140 $8) $6)) $5) ((%280 $4) ((%281
       ((%475 $1) $3)) $0))))))))))))))))))))))))))`)
  val V_CJ_RULE =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%397. (%123 (\%398. (%121 (\%129. (%121
       (\%130. (%273 (\%274. (%457 (\%476. (%38 (\%275. (%276 (\%471. (%276
       (\%473. (%38 (\%278. ((%7 ((%8 (%329 $9)) ((%8 (%329 $8)) ((%8
       ((((%279 $9) ((%140 $7) $6)) $5) ((%280 $3) ((%281 $2) $0)))) ((%8
       ((((%279 $8) ((%140 $7) $6)) $5) ((%280 $3) ((%281 $1) $0)))) (%103
       (\%104. ((%44 ($5 ((%261 $0) $4))) ((%342 $11) $0))))))))) ((((%279
       (((%343 $10) $9) $8)) ((%140 $7) $6)) $5) ((%280 $3) ((%281 (\%477.
       (((%478 ($5 $0)) ($3 $0)) ($2 $0)))) $0))))))))))))))))))))))))))`)
  val V_TR_RULE =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%128. (%121 (\%129. (%273 (\%274. (%457
       (\%476. (%38 (\%275. (%276 (\%277. ((%7 ((%8 (%329 $5)) ((%8 (%357
       (\%358. (\%359. ((%8 (%300 ((%342 $8) $0))) ((%335 $1) ((%127 $7)
       $0))))))) ((%8 (%103 (\%104. ((%44 ($3 ((%261 $0) $2))) ((%342 $7)
       $0))))) ((((%279 $5) ((%140 $4) $4)) $3) ((%280 $1) ((%281 $0)
       $1))))))) ((((%279 ((%350 $6) $5)) ((%140 $4) $4)) $3) ((%280 $1)
       ((%281 ((%479 ((%480 %300) $2)) $0)) $1))))))))))))))))))`)
  val V_STRENGTHEN_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%417. (%121 (\%130. (%273
       (\%274. (%38 (\%275. (%276 (\%277. (%38 (\%278. ((%7 ((%8 (%329 $7))
       ((%8 ((((%279 $7) ((%140 $6) $4)) $3) ((%280 $2) ((%281 $1) $0))))
       (%103 (\%104. ((%7 ($6 $0)) ($7 $0))))))) ((((%279 $7) ((%140 $5)
       $4)) $3) ((%280 $2) ((%281 $1) $0))))))))))))))))))))`)
  val V_WEAKEN_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%121 (\%418. (%131
       (\%481. (%133 (\%482. (%135 (\%136. (%137 (\%483. ((%7 ((%8 (%329
       $7)) ((%8 ((((%139 $7) ((%140 $6) $5)) $3) ((%141 $2) ((%142 $1)
       $0)))) (%103 (\%104. ((%7 ($6 $0)) ($5 $0))))))) ((((%139 $7) ((%140
       $6) $4)) $3) ((%141 $2) ((%142 $1) $0))))))))))))))))))))`)
  val V_POP_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%273 (\%274. (%38
       (\%275. (%276 (\%277. (%38 (\%278. (%38 (\%286. (%276 (\%468. ((%7
       ((%8 ((((%279 $8) ((%140 $7) $6)) ((%484 $1) $5)) ((%280 $4) ((%281
       $3) $2)))) (%103 (\%104. ((%203 ($1 ((%261 $0) (%76 ((%72 $5)
       $2))))) (%232 ((%230 ($4 ((%261 $0) $5))) ((%261 $0) $2))))))))
       ((((%279 $8) ((%140 $7) $6)) $5) ((%280 (%76 ((%72 $4) $1))) ((%281
       $0) (%76 ((%72 $2) $1))))))))))))))))))))))))`)
  val V_PUSH_RULE =
    DT(["DISK_THM"], [],
       `(%123 (\%128. (%121 (\%129. (%121 (\%130. (%273 (\%274. (%38
       (\%275. (%276 (\%277. (%38 (\%278. (%38 (\%286. ((%7 ((%8 ((((%279
       $7) ((%140 $6) $5)) $4) ((%280 $3) ((%281 $2) $1)))) (%287 ((%288
       $6) ((%289 $5) $0))))) ((((%279 $7) ((%140 $6) $5)) ((%484 $0) $4))
       ((%280 $3) ((%281 $2) $1))))))))))))))))))))`)
  val WELL_FORMED_TR_RULE =
    DT(["DISK_THM"], [],
       `(%340 (\%341. (%123 (\%128. (%145 (\%485. ((%7 ((%8 (%329 $1))
       (%357 (\%358. (\%359. ((%8 (%300 ((%342 $4) $0))) ((%335 $1) ((%127
       $3) $0)))))))) (%329 ((%350 $2) $1)))))))))`)
  end
  val _ = DB.bindl "CFL_Rules"
  [("REXP_TY_DEF",REXP_TY_DEF,DB.Def), ("REXP_repfns",REXP_repfns,DB.Def),
   ("prodCFL_Rules0_TY_DEF",prodCFL_Rules0_TY_DEF,DB.Def),
   ("prodCFL_Rules0_repfns",prodCFL_Rules0_repfns,DB.Def),
   ("CFL_Rules1_def",CFL_Rules1_def,DB.Def),
   ("CFL_Rules2_def",CFL_Rules2_def,DB.Def),
   ("CFL_Rules3_def",CFL_Rules3_def,DB.Def),
   ("CFL_Rules4_def",CFL_Rules4_def,DB.Def),
   ("CFL_Rules5_def",CFL_Rules5_def,DB.Def),
   ("CFL_Rules6",CFL_Rules6,DB.Def), ("RR",RR,DB.Def), ("RM",RM,DB.Def),
   ("RC",RC,DB.Def), ("PR",PR,DB.Def),
   ("REXP_case_def",REXP_case_def,DB.Def),
   ("REXP_size_def",REXP_size_def,DB.Def), ("mread_def",mread_def,DB.Def),
   ("proper_def",proper_def,DB.Def), ("HSPEC_def",HSPEC_def,DB.Def),
   ("PSPEC_def",PSPEC_def,DB.Def),
   ("valid_push_def",valid_push_def,DB.Def),
   ("P_intact_def",P_intact_def,DB.Def),
   ("VEXP_TY_DEF",VEXP_TY_DEF,DB.Def), ("VEXP_repfns",VEXP_repfns,DB.Def),
   ("prodCFL_Rules7_TY_DEF",prodCFL_Rules7_TY_DEF,DB.Def),
   ("prodCFL_Rules7_repfns",prodCFL_Rules7_repfns,DB.Def),
   ("CFL_Rules8_def",CFL_Rules8_def,DB.Def),
   ("CFL_Rules9_def",CFL_Rules9_def,DB.Def),
   ("CFL_Rules10_def",CFL_Rules10_def,DB.Def),
   ("CFL_Rules11",CFL_Rules11,DB.Def), ("SG",SG,DB.Def), ("VT",VT,DB.Def),
   ("VEXP_case_def",VEXP_case_def,DB.Def),
   ("VEXP_size_def",VEXP_size_def,DB.Def),
   ("readv_tupled_primitive_def",readv_tupled_primitive_def,DB.Def),
   ("readv_curried_def",readv_curried_def,DB.Def),
   ("push_def",push_def,DB.Def), ("top_def",top_def,DB.Def),
   ("pop_def",pop_def,DB.Def), ("VSPEC_def",VSPEC_def,DB.Def),
   ("V_intact_def",V_intact_def,DB.Def),
   ("datatype_REXP",datatype_REXP,DB.Thm), ("REXP_11",REXP_11,DB.Thm),
   ("REXP_distinct",REXP_distinct,DB.Thm),
   ("REXP_case_cong",REXP_case_cong,DB.Thm),
   ("REXP_nchotomy",REXP_nchotomy,DB.Thm),
   ("REXP_Axiom",REXP_Axiom,DB.Thm),
   ("REXP_induction",REXP_induction,DB.Thm),
   ("CFL_SC_RULE",CFL_SC_RULE,DB.Thm), ("BLK_EQ_SC",BLK_EQ_SC,DB.Thm),
   ("EMPTY_BLK_AXIOM",EMPTY_BLK_AXIOM,DB.Thm),
   ("BLK_RULE",BLK_RULE,DB.Thm), ("CFL_CJ_RULE",CFL_CJ_RULE,DB.Thm),
   ("CFL_CJ_RULE_2",CFL_CJ_RULE_2,DB.Thm),
   ("CFL_TR_RULE",CFL_TR_RULE,DB.Thm), ("WF_DEF_2",WF_DEF_2,DB.Thm),
   ("WF_TR_LEM_1",WF_TR_LEM_1,DB.Thm), ("WF_TR_LEM_2",WF_TR_LEM_2,DB.Thm),
   ("WF_TR_LEM_3",WF_TR_LEM_3,DB.Thm), ("WF_TR_THM_1",WF_TR_THM_1,DB.Thm),
   ("PSPEC_STACK",PSPEC_STACK,DB.Thm),
   ("PSPEC_CHARACTERISTIC",PSPEC_CHARACTERISTIC,DB.Thm),
   ("PRJ_SHUFFLE_RULE",PRJ_SHUFFLE_RULE,DB.Thm),
   ("PRJ_SHUFFLE_RULE2",PRJ_SHUFFLE_RULE2,DB.Thm),
   ("PRJ_SC_RULE",PRJ_SC_RULE,DB.Thm), ("PRJ_CJ_RULE",PRJ_CJ_RULE,DB.Thm),
   ("PRJ_TR_RULE",PRJ_TR_RULE,DB.Thm),
   ("PRJ_TR_RULE_2",PRJ_TR_RULE_2,DB.Thm),
   ("PRJ_STRENGTHEN_RULE",PRJ_STRENGTHEN_RULE,DB.Thm),
   ("PRJ_WEAKEN_RULE",PRJ_WEAKEN_RULE,DB.Thm),
   ("PRJ_POP_RULE",PRJ_POP_RULE,DB.Thm),
   ("PRJ_PUSH_RULE",PRJ_PUSH_RULE,DB.Thm),
   ("datatype_VEXP",datatype_VEXP,DB.Thm), ("VEXP_11",VEXP_11,DB.Thm),
   ("VEXP_distinct",VEXP_distinct,DB.Thm),
   ("VEXP_case_cong",VEXP_case_cong,DB.Thm),
   ("VEXP_nchotomy",VEXP_nchotomy,DB.Thm),
   ("VEXP_Axiom",VEXP_Axiom,DB.Thm),
   ("VEXP_induction",VEXP_induction,DB.Thm),
   ("readv_ind",readv_ind,DB.Thm), ("readv_def",readv_def,DB.Thm),
   ("V_SHUFFLE_RULE",V_SHUFFLE_RULE,DB.Thm),
   ("V_SC_RULE",V_SC_RULE,DB.Thm), ("V_CJ_RULE",V_CJ_RULE,DB.Thm),
   ("V_TR_RULE",V_TR_RULE,DB.Thm),
   ("V_STRENGTHEN_RULE",V_STRENGTHEN_RULE,DB.Thm),
   ("V_WEAKEN_RULE",V_WEAKEN_RULE,DB.Thm),
   ("V_POP_RULE",V_POP_RULE,DB.Thm), ("V_PUSH_RULE",V_PUSH_RULE,DB.Thm),
   ("WELL_FORMED_TR_RULE",WELL_FORMED_TR_RULE,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("CFLTheory.CFL_grammars",CFLTheory.CFL_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms temp_add_type "REXP"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_REXP")
        {Name = "dest_REXP", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_REXP")
        {Name = "mk_REXP", Thy = "CFL_Rules"}
  val _ = update_grms temp_add_type "prodCFL_Rules0"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_prodCFL_Rules0")
        {Name = "dest_prodCFL_Rules0", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_prodCFL_Rules0")
        {Name = "mk_prodCFL_Rules0", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules1")
        {Name = "CFL_Rules1", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules2")
        {Name = "CFL_Rules2", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules3")
        {Name = "CFL_Rules3", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules4")
        {Name = "CFL_Rules4", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules5")
        {Name = "CFL_Rules5", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules6")
        {Name = "CFL_Rules6", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "RR")
        {Name = "RR", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "RM")
        {Name = "RM", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "RC")
        {Name = "RC", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "PR")
        {Name = "PR", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "REXP_case")
        {Name = "REXP_case", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "REXP_size")
        {Name = "REXP_size", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "REXP1_size")
        {Name = "REXP1_size", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mread")
        {Name = "mread", Thy = "CFL_Rules"}
  val _ = update_grms
       temp_add_rule
       {term_name = "mread", fixity = Suffix 60,
pp_elements = [TOK "<", TM, TOK ">"],
paren_style = OnlyIfNecessary,
block_style = (AroundSameName, (INCONSISTENT, 0))}
  val _ = update_grms
       (temp_overload_on_by_nametype "proper")
        {Name = "proper", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSPEC")
        {Name = "HSPEC", Thy = "CFL_Rules"}
  val _ = update_grms
       temp_type_abbrev
       ("HSPEC_TYPE", ((T"prod" "pair"
   [T"fmap" "finite_map"
     [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
    T"fmap" "finite_map"
     [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
  bool) -->
 (T"CTL_STRUCTURE" "CFL" [] -->
  ((T"prod" "pair"
     [T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
      T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
    bool) --> bool))))
  val _ = update_grms
       (temp_overload_on_by_nametype "PSPEC")
        {Name = "PSPEC", Thy = "CFL_Rules"}
  val _ = update_grms
       temp_type_abbrev
       ("PSPEC_TYPE", (T"CTL_STRUCTURE" "CFL" [] -->
 (T"prod" "pair"
   [(T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
     bool),
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
     bool)] -->
  ((T"prod" "pair"
     [T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
      T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
    alpha) -->
   (T"prod" "pair"
     [(T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
       --> beta),
      T"prod" "pair"
       [(beta --> gamma),
        (T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
         --> gamma)]] --> bool)))))
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_push")
        {Name = "valid_push", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "P_intact")
        {Name = "P_intact", Thy = "CFL_Rules"}
  val _ = update_grms temp_add_type "VEXP"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_VEXP")
        {Name = "dest_VEXP", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_VEXP")
        {Name = "mk_VEXP", Thy = "CFL_Rules"}
  val _ = update_grms temp_add_type "prodCFL_Rules7"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_prodCFL_Rules7")
        {Name = "dest_prodCFL_Rules7", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_prodCFL_Rules7")
        {Name = "mk_prodCFL_Rules7", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules8")
        {Name = "CFL_Rules8", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules9")
        {Name = "CFL_Rules9", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules10")
        {Name = "CFL_Rules10", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_Rules11")
        {Name = "CFL_Rules11", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SG")
        {Name = "SG", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "VT")
        {Name = "VT", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "VEXP_case")
        {Name = "VEXP_case", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "VEXP_size")
        {Name = "VEXP_size", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "VEXP1_size")
        {Name = "VEXP1_size", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "readv_tupled")
        {Name = "readv_tupled", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "readv")
        {Name = "readv", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "push")
        {Name = "push", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "top")
        {Name = "top", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "pop")
        {Name = "pop", Thy = "CFL_Rules"}
  val _ = update_grms
       (temp_overload_on_by_nametype "VSPEC")
        {Name = "VSPEC", Thy = "CFL_Rules"}
  val _ = update_grms
       temp_type_abbrev
       ("VSPEC_TYPE", (T"CTL_STRUCTURE" "CFL" [] -->
 (T"prod" "pair"
   [(T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
     bool),
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
     bool)] -->
  (T"list" "list" [T"REXP" "CFL_Rules" []] -->
   (T"prod" "pair"
     [T"REXP" "CFL_Rules" [],
      T"prod" "pair"
       [(T"VEXP" "CFL_Rules" [] --> T"VEXP" "CFL_Rules" []),
        T"REXP" "CFL_Rules" []]] --> bool)))))
  val _ = update_grms
       (temp_overload_on_by_nametype "V_intact")
        {Name = "V_intact", Thy = "CFL_Rules"}
  val CFL_Rules_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG REXP_Axiom,
           case_def=REXP_case_def,
           case_cong=REXP_case_cong,
           induction=ORIG REXP_induction,
           nchotomy=REXP_nchotomy,
           size=SOME(Parse.Term`(CFL_Rules$REXP_size) :(CFL_Rules$REXP) -> (num$num)`,
                     ORIG REXP_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME REXP_11,
           distinct=SOME REXP_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[]}
        val tyinfo0 = tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];
  
  
  val _ = computeLib.add_funs [mread_def];  
  
  val _ = computeLib.add_funs [proper_def];  
  
  val _ = computeLib.add_funs [HSPEC_def];  
  
  val _ = computeLib.add_funs [PSPEC_def];  
  
  val _ = computeLib.add_funs [valid_push_def];  
  
  val _ = computeLib.add_funs [P_intact_def];  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG VEXP_Axiom,
           case_def=VEXP_case_def,
           case_cong=VEXP_case_cong,
           induction=ORIG VEXP_induction,
           nchotomy=VEXP_nchotomy,
           size=SOME(Parse.Term`(CFL_Rules$VEXP_size) :(CFL_Rules$VEXP) -> (num$num)`,
                     ORIG VEXP_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME VEXP_11,
           distinct=SOME VEXP_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[]}
        val tyinfo0 = tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];
  
  
  val _ = computeLib.add_funs [readv_def];  
  
  val _ = computeLib.add_funs [push_def];  
  
  val _ = computeLib.add_funs [top_def];  
  
  val _ = computeLib.add_funs [pop_def];  
  
  val _ = computeLib.add_funs [VSPEC_def];  
  
  val _ = computeLib.add_funs [V_intact_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
