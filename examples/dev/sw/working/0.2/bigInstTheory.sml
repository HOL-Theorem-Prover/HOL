structure bigInstTheory :> bigInstTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading bigInstTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open CFLTheory simplifierTheory
  in end;
  val _ = Theory.link_parents
          ("bigInst",
          Arbnum.fromString "1163556424",
          Arbnum.fromString "258382")
          [("CFL",
           Arbnum.fromString "1163238460",
           Arbnum.fromString "586624"),
           ("simplifier",
           Arbnum.fromString "1163213580",
           Arbnum.fromString "80264")];
  val _ = Theory.incorporate_types "bigInst" [("CFL_EXP",0)];
  val _ = Theory.incorporate_consts "bigInst"
     [("eq_exp_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] -->
         bool))),
      ("store_one",
       ((T"CFL_EXP" "bigInst" [] -->
         (T"OFFSET" "preARM" [] --> T"list" "list" [T"DOPER" "CFL" []])))),
      ("pop_one",
       ((T"CFL_EXP" "bigInst" [] --> T"list" "list" [T"DOPER" "CFL" []]))),
      ("reade",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"CFL_EXP" "bigInst" [] -->
          T"cart" "fcp" [bool, T"i32" "words" []])))),
      ("addr_in_range",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"CFL_EXP" "bigInst" [] -->
          (T"prod" "pair" [T"num" "num" [], T"num" "num" []] --> bool))))),
      ("dest_CFL_EXP",
       ((T"CFL_EXP" "bigInst" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
      ("sr_list",
       ((T"prod" "pair"
          [T"list" "list" [T"CFL_EXP" "bigInst" []],
           T"prod" "pair"
            [T"list" "list" [T"DOPER" "CFL" []],
             T"list" "list" [T"CFL_EXP" "bigInst" []]]] -->
         T"list" "list" [T"DOPER" "CFL" []]))),
      ("CFL_EXP_size",((T"CFL_EXP" "bigInst" [] --> T"num" "num" []))),
      ("valid_regs",((T"num" "num" [] --> bool))),
      ("copy_list",
       ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
         (T"list" "list" [T"CFL_EXP" "bigInst" []] -->
          T"list" "list" [T"DOPER" "CFL" []])))),
      ("valid_exp",((T"CFL_EXP" "bigInst" [] --> bool))),
      ("unique_exp_list",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool)))),
      ("pop_list",
       ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
         T"list" "list" [T"DOPER" "CFL" []]))),
      ("grow_lt",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         (T"num" "num" [] --> bool)))),
      ("is_C",((T"CFL_EXP" "bigInst" [] --> bool))),
      ("addr_in_range_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [],
             T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] -->
         bool))),
      ("in_range",
       ((T"num" "num" [] -->
         (T"prod" "pair" [T"num" "num" [], T"num" "num" []] --> bool)))),
      ("addr_of",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"CFL_EXP" "bigInst" [] --> T"num" "num" [])))),
      ("push_list",
       ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
         T"list" "list" [T"DOPER" "CFL" []]))),
      ("legal_pop_exp",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"CFL_EXP" "bigInst" [] -->
          (T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool))))),
      ("eq_exp",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"CFL_EXP" "bigInst" [] -->
          (T"CFL_EXP" "bigInst" [] --> bool))))),
      ("load_one",
       ((T"CFL_EXP" "bigInst" [] -->
         (T"OFFSET" "preARM" [] --> T"list" "list" [T"DOPER" "CFL" []])))),
      ("legal_push_exp",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"CFL_EXP" "bigInst" [] --> (T"num" "num" [] --> bool))))),
      ("mk_CFL_EXP",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         T"CFL_EXP" "bigInst" []))),
      ("CFL_EXP_case",
       (((T"num" "num" [] --> alpha) -->
         ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
          ((T"num" "num" [] --> alpha) -->
           ((T"num" "num" [] --> alpha) -->
            (T"CFL_EXP" "bigInst" [] --> alpha))))))),
      ("writee_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
      ("bigInst3",((T"num" "num" [] --> T"CFL_EXP" "bigInst" []))),
      ("bigInst2",((T"num" "num" [] --> T"CFL_EXP" "bigInst" []))),
      ("bigInst1",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"CFL_EXP" "bigInst" []))),
      ("bigInst0",((T"num" "num" [] --> T"CFL_EXP" "bigInst" []))),
      ("eq_addr",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"CFL_EXP" "bigInst" [] -->
          (T"CFL_EXP" "bigInst" [] --> bool))))),
      ("locate_ge",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         (T"num" "num" [] --> bool)))),
      ("push_one",
       ((T"CFL_EXP" "bigInst" [] --> T"list" "list" [T"DOPER" "CFL" []]))),
      ("isV",((T"num" "num" [] --> T"CFL_EXP" "bigInst" []))),
      ("isR",((T"num" "num" [] --> T"CFL_EXP" "bigInst" []))),
      ("isM",((T"num" "num" [] --> T"CFL_EXP" "bigInst" []))),
      ("isC",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"CFL_EXP" "bigInst" []))),
      ("writee",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"cart" "fcp" [bool, T"i32" "words" []]] -->
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]])))),
      ("valid_exp_3",((T"CFL_EXP" "bigInst" [] --> bool))),
      ("valid_exp_2",((T"CFL_EXP" "bigInst" [] --> bool))),
      ("valid_exp_1",((T"CFL_EXP" "bigInst" [] --> bool)))];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) --> bool)),
   V"x"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"!" "bool" (((T"CFL_EXP" "bigInst" [] --> bool) --> bool)),
   V"x1" (T"CFL_EXP" "bigInst" []), V"x2" (T"CFL_EXP" "bigInst" []),
   C"=" "min" ((bool --> (bool --> bool))),
   C"eq_exp" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool)))),
   C"eq_exp_tupled" "bigInst"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]
      --> bool)),
   C"," "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]
       -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]))),
   C"," "pair"
    ((T"CFL_EXP" "bigInst" [] -->
      (T"CFL_EXP" "bigInst" [] -->
       T"prod" "pair"
        [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]
       --> bool) -->
      ((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] --> bool)
       --> bool))),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] --> bool))
      -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] --> bool)
        -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] --> bool))
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] -->
        bool)))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] --> bool))
       --> bool) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] -->
        bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]
      -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]] --> bool))
      --> bool)),
   V"eq_exp_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]
      --> bool)),
   V"a"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
       T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]
        --> bool)) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]]
       --> bool))),
   V"st"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"v5"
    (T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]),
   C"pair_case" "pair"
    (((T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool)) -->
      (T"prod" "pair" [T"CFL_EXP" "bigInst" [], T"CFL_EXP" "bigInst" []]
       --> bool))), V"v6" (T"CFL_EXP" "bigInst" []),
   V"v7" (T"CFL_EXP" "bigInst" []),
   C"CFL_EXP_case" "bigInst"
    (((T"num" "num" [] --> bool) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) -->
       ((T"num" "num" [] --> bool) -->
        ((T"num" "num" [] --> bool) -->
         (T"CFL_EXP" "bigInst" [] --> bool)))))), V"r1" (T"num" "num" []),
   V"r2" (T"num" "num" []), C"I" "combin" ((bool --> bool)),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"v21" (T"cart" "fcp" [bool, T"i32" "words" []]), C"F" "bool" (bool),
   V"v22" (T"num" "num" []), V"v23" (T"num" "num" []),
   V"c1" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v28" (T"num" "num" []),
   V"c2" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   V"v30" (T"num" "num" []), V"v31" (T"num" "num" []),
   V"v1" (T"num" "num" []), V"v36" (T"num" "num" []),
   V"v37" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v2" (T"num" "num" []),
   C"eq_addr" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool)))),
   C"isV" "bigInst" ((T"num" "num" [] --> T"CFL_EXP" "bigInst" [])),
   V"m" (T"num" "num" []),
   C"isM" "bigInst" ((T"num" "num" [] --> T"CFL_EXP" "bigInst" [])),
   V"m1" (T"num" "num" []), V"v44" (T"num" "num" []),
   V"v45" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v" (T"num" "num" []), V"m2" (T"num" "num" []),
   V"addr1" (T"CFL_EXP" "bigInst" []), V"addr2" (T"CFL_EXP" "bigInst" []),
   C"addr_of" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] --> T"num" "num" []))),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   C"-" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"w2n" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"num" "num" [])),
   C"read" "preARM"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"EXP" "preARM" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"FP" "preARM" (T"EXP" "preARM" []),
   C"!" "bool"
    (((T"prod" "pair"
        [T"CFL_EXP" "bigInst" [], T"cart" "fcp" [bool, T"i32" "words" []]]
       --> bool) --> bool)),
   V"x1"
    (T"prod" "pair"
      [T"CFL_EXP" "bigInst" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
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
   C"writee" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"prod" "pair"
        [T"CFL_EXP" "bigInst" [], T"cart" "fcp" [bool, T"i32" "words" []]]
       -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"writee_tupled" "bigInst"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair"
         [T"CFL_EXP" "bigInst" [],
          T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"," "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"prod" "pair"
        [T"CFL_EXP" "bigInst" [], T"cart" "fcp" [bool, T"i32" "words" []]]
       -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
      ((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
       bool))),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"cart" "fcp" [bool, T"i32" "words" []]]] --> bool)) -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
        -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]] --> bool)) --> bool)
      -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"cart" "fcp" [bool, T"i32" "words" []]]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair"
         [T"CFL_EXP" "bigInst" [],
          T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"cart" "fcp" [bool, T"i32" "words" []]]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"cart" "fcp" [bool, T"i32" "words" []]]] --> bool)) -->
      bool)),
   V"writee_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair"
         [T"CFL_EXP" "bigInst" [],
          T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   V"a"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
       T"prod" "pair"
        [T"CFL_EXP" "bigInst" [],
         T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"prod" "pair"
         [T"CFL_EXP" "bigInst" [], T"cart" "fcp" [bool, T"i32" "words" []]]
        -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
      -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   V"v2"
    (T"prod" "pair"
      [T"CFL_EXP" "bigInst" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"pair_case" "pair"
    (((T"CFL_EXP" "bigInst" [] -->
       (T"cart" "fcp" [bool, T"i32" "words" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
      -->
      (T"prod" "pair"
        [T"CFL_EXP" "bigInst" [], T"cart" "fcp" [bool, T"i32" "words" []]]
       -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   V"v3" (T"CFL_EXP" "bigInst" []),
   V"v" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"CFL_EXP_case" "bigInst"
    (((T"num" "num" [] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
       ((T"num" "num" [] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
        -->
        ((T"num" "num" [] -->
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
         -->
         (T"CFL_EXP" "bigInst" [] -->
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]])))))),
   V"r" (T"num" "num" []),
   C"I" "combin"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"write" "preARM"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"EXP" "preARM" [] -->
       (T"cart" "fcp" [bool, T"i32" "words" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"REG" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   V"c" (T"cart" "fcp" [bool, T"i32" "words" []]), V"k" (T"num" "num" []),
   C"MEM" "preARM"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"EXP" "preARM" [])),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"OFFSET" "preARM" [] -->
       T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]))),
   C"fp" "CFL" (T"num" "num" []),
   C"NEG" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"," "pair"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"FST" "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]])),
   C"FUPDATE" "finite_map"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"prod" "pair"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]))),
   C"SND" "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]])),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"prod" "pair"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]))),
   C"reade" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"isR" "bigInst" ((T"num" "num" [] --> T"CFL_EXP" "bigInst" [])),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   C"isC" "bigInst"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      T"CFL_EXP" "bigInst" [])),
   C"FAPPLY" "finite_map"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"a" (T"num" "num" []),
   C"CFL_EXP_size" "bigInst"
    ((T"CFL_EXP" "bigInst" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   V"a" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"!" "bool" ((((T"num" "num" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"num" "num" [] --> alpha)),
   C"!" "bool"
    ((((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) --> bool) -->
      bool)), V"f1" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   V"f2" ((T"num" "num" [] --> alpha)),
   V"f3" ((T"num" "num" [] --> alpha)),
   C"=" "min" ((alpha --> (alpha --> bool))),
   C"CFL_EXP_case" "bigInst"
    (((T"num" "num" [] --> alpha) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
       ((T"num" "num" [] --> alpha) -->
        ((T"num" "num" [] --> alpha) -->
         (T"CFL_EXP" "bigInst" [] --> alpha)))))),
   C"=" "min"
    (((T"num" "num" [] --> T"CFL_EXP" "bigInst" []) -->
      ((T"num" "num" [] --> T"CFL_EXP" "bigInst" []) --> bool))),
   C"bigInst3" "bigInst" ((T"num" "num" [] --> T"CFL_EXP" "bigInst" [])),
   C"bigInst2" "bigInst" ((T"num" "num" [] --> T"CFL_EXP" "bigInst" [])),
   C"=" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> T"CFL_EXP" "bigInst" [])
      -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] -->
        T"CFL_EXP" "bigInst" []) --> bool))),
   C"bigInst1" "bigInst"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      T"CFL_EXP" "bigInst" [])),
   C"bigInst0" "bigInst" ((T"num" "num" [] --> T"CFL_EXP" "bigInst" [])),
   C"mk_CFL_EXP" "bigInst"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      T"CFL_EXP" "bigInst" [])),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
        -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"0" "num" (T"num" "num" []),
   C"@" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) -->
      T"cart" "fcp" [bool, T"i32" "words" []])), C"T" "bool" (bool),
   V"n" (T"num" "num" []),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"@" "min" (((T"num" "num" [] --> bool) --> T"num" "num" [])),
   V"a" (T"CFL_EXP" "bigInst" []),
   C"=" "min"
    ((T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool))),
   C"dest_CFL_EXP" "bigInst"
    ((T"CFL_EXP" "bigInst" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) --> bool)),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool) --> bool) --> bool)),
   V"'CFL_EXP'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)), C"==>" "min" ((bool --> (bool --> bool))),
   C"\\/" "bool" ((bool --> (bool --> bool))),
   C"?" "bool" (((T"num" "num" [] --> bool) --> bool)),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   C"?" "bool"
    ((((T"CFL_EXP" "bigInst" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
       bool) --> bool)),
   V"rep"
    ((T"CFL_EXP" "bigInst" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      ((T"CFL_EXP" "bigInst" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
       bool))),
   C"=" "min"
    (((T"CFL_EXP" "bigInst" [] --> bool) -->
      ((T"CFL_EXP" "bigInst" [] --> bool) --> bool))),
   C"is_C" "bigInst" ((T"CFL_EXP" "bigInst" [] --> bool)),
   C"WFREC" "relation"
    (((T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool)) -->
      (((T"CFL_EXP" "bigInst" [] --> bool) -->
        (T"CFL_EXP" "bigInst" [] --> bool)) -->
       (T"CFL_EXP" "bigInst" [] --> bool)))),
   C"@" "min"
    ((((T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool)) -->
       bool) -->
      (T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool)))),
   V"R" ((T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool))),
   C"WF" "relation"
    (((T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool)) -->
      bool)), V"is_C" ((T"CFL_EXP" "bigInst" [] --> bool)),
   V"v4" (T"num" "num" []), V"v6" (T"num" "num" []),
   V"v7" (T"num" "num" []),
   C"=" "min"
    (((T"num" "num" [] --> bool) -->
      ((T"num" "num" [] --> bool) --> bool))),
   C"valid_regs" "bigInst" ((T"num" "num" [] --> bool)),
   C"WFREC" "relation"
    (((T"num" "num" [] --> (T"num" "num" [] --> bool)) -->
      (((T"num" "num" [] --> bool) --> (T"num" "num" [] --> bool)) -->
       (T"num" "num" [] --> bool)))),
   C"@" "min"
    ((((T"num" "num" [] --> (T"num" "num" [] --> bool)) --> bool) -->
      (T"num" "num" [] --> (T"num" "num" [] --> bool)))),
   V"R" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"WF" "relation"
    (((T"num" "num" [] --> (T"num" "num" [] --> bool)) --> bool)),
   V"valid_regs" ((T"num" "num" [] --> bool)),
   C"~" "bool" ((bool --> bool)),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"index_of_reg" "CFL" ((T"MREG" "CFL" [] --> T"num" "num" [])),
   C"from_reg_index" "CFL" ((T"num" "num" [] --> T"MREG" "CFL" [])),
   C"valid_exp" "bigInst" ((T"CFL_EXP" "bigInst" [] --> bool)),
   V"valid_exp" ((T"CFL_EXP" "bigInst" [] --> bool)),
   V"v5" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"valid_exp_1" "bigInst" ((T"CFL_EXP" "bigInst" [] --> bool)),
   V"valid_exp_1" ((T"CFL_EXP" "bigInst" [] --> bool)),
   C"valid_exp_2" "bigInst" ((T"CFL_EXP" "bigInst" [] --> bool)),
   V"valid_exp_2" ((T"CFL_EXP" "bigInst" [] --> bool)),
   C"valid_exp_3" "bigInst" ((T"CFL_EXP" "bigInst" [] --> bool)),
   V"valid_exp_3" ((T"CFL_EXP" "bigInst" [] --> bool)),
   V"x" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"locate_ge" "bigInst"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> bool))),
   C"<=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"ubound" (T"num" "num" []), V"lbound" (T"num" "num" []),
   C"in_range" "bigInst"
    ((T"num" "num" [] -->
      (T"prod" "pair" [T"num" "num" [], T"num" "num" []] --> bool))),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"num" "num" [] -->
       T"prod" "pair" [T"num" "num" [], T"num" "num" []]))),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool)
      -->
      ((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool)
       --> bool))),
   C"addr_in_range_tupled" "bigInst"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair"
         [T"CFL_EXP" "bigInst" [],
          T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool)),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool))
      -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [],
             T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool)
        -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [],
             T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool))
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] -->
        bool)))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"CFL_EXP" "bigInst" [],
             T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool))
       --> bool) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] -->
        bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair"
         [T"CFL_EXP" "bigInst" [],
          T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"CFL_EXP" "bigInst" [],
            T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool))
      --> bool)),
   V"addr_in_range_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"prod" "pair"
         [T"CFL_EXP" "bigInst" [],
          T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool)),
   V"a"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
       T"prod" "pair"
        [T"CFL_EXP" "bigInst" [],
         T"prod" "pair" [T"num" "num" [], T"num" "num" []]]]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"prod" "pair"
         [T"CFL_EXP" "bigInst" [],
          T"prod" "pair" [T"num" "num" [], T"num" "num" []]] --> bool)) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"prod" "pair" [T"num" "num" [], T"num" "num" []]]] --> bool))),
   V"v2"
    (T"prod" "pair"
      [T"CFL_EXP" "bigInst" [],
       T"prod" "pair" [T"num" "num" [], T"num" "num" []]]),
   C"pair_case" "pair"
    (((T"CFL_EXP" "bigInst" [] -->
       (T"prod" "pair" [T"num" "num" [], T"num" "num" []] --> bool)) -->
      (T"prod" "pair"
        [T"CFL_EXP" "bigInst" [],
         T"prod" "pair" [T"num" "num" [], T"num" "num" []]] --> bool))),
   V"bound" (T"prod" "pair" [T"num" "num" [], T"num" "num" []]),
   V"v9" (T"num" "num" []),
   V"v10" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"!" "bool"
    (((T"prod" "pair" [T"num" "num" [], T"num" "num" []] --> bool) -->
      bool)), V"x2" (T"prod" "pair" [T"num" "num" [], T"num" "num" []]),
   C"addr_in_range" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] -->
       (T"prod" "pair" [T"num" "num" [], T"num" "num" []] --> bool)))),
   C"," "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"prod" "pair"
        [T"CFL_EXP" "bigInst" [],
         T"prod" "pair" [T"num" "num" [], T"num" "num" []]] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"prod" "pair" [T"num" "num" [], T"num" "num" []]]]))),
   C"," "pair"
    ((T"CFL_EXP" "bigInst" [] -->
      (T"prod" "pair" [T"num" "num" [], T"num" "num" []] -->
       T"prod" "pair"
        [T"CFL_EXP" "bigInst" [],
         T"prod" "pair" [T"num" "num" [], T"num" "num" []]]))),
   C"!" "bool" (((T"OFFSET" "preARM" [] --> bool) --> bool)),
   V"offset" (T"OFFSET" "preARM" []),
   C"=" "min"
    ((T"list" "list" [T"DOPER" "CFL" []] -->
      (T"list" "list" [T"DOPER" "CFL" []] --> bool))),
   C"store_one" "bigInst"
    ((T"CFL_EXP" "bigInst" [] -->
      (T"OFFSET" "preARM" [] --> T"list" "list" [T"DOPER" "CFL" []]))),
   C"CONS" "list"
    ((T"DOPER" "CFL" [] -->
      (T"list" "list" [T"DOPER" "CFL" []] -->
       T"list" "list" [T"DOPER" "CFL" []]))),
   C"MSTR" "CFL"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "CFL" [] --> T"DOPER" "CFL" []))),
   C"NIL" "list" (T"list" "list" [T"DOPER" "CFL" []]),
   C"MMOV" "CFL"
    ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))),
   C"R9" "CFL" (T"MREG" "CFL" []),
   C"MC" "CFL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" [])),
   C"MLDR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"DOPER" "CFL" []))),
   C"load_one" "bigInst"
    ((T"CFL_EXP" "bigInst" [] -->
      (T"OFFSET" "preARM" [] --> T"list" "list" [T"DOPER" "CFL" []]))),
   C"push_one" "bigInst"
    ((T"CFL_EXP" "bigInst" [] --> T"list" "list" [T"DOPER" "CFL" []])),
   C"MSUB" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"R13" "CFL" (T"MREG" "CFL" []),
   C"n2w" "words"
    ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []])),
   C"pop_one" "bigInst"
    ((T"CFL_EXP" "bigInst" [] --> T"list" "list" [T"DOPER" "CFL" []])),
   C"POS" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"MADD" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"push_list" "bigInst"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
      T"list" "list" [T"DOPER" "CFL" []])),
   C"NIL" "list" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   V"x" (T"CFL_EXP" "bigInst" []),
   C"!" "bool"
    (((T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool) --> bool)),
   V"xs" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   C"CONS" "list"
    ((T"CFL_EXP" "bigInst" [] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] -->
       T"list" "list" [T"CFL_EXP" "bigInst" []]))),
   C"APPEND" "list"
    ((T"list" "list" [T"DOPER" "CFL" []] -->
      (T"list" "list" [T"DOPER" "CFL" []] -->
       T"list" "list" [T"DOPER" "CFL" []]))),
   V"e" (T"CFL_EXP" "bigInst" []),
   C"legal_push_exp" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] --> (T"num" "num" [] --> bool)))),
   C"SP" "preARM" (T"EXP" "preARM" []),
   C"pop_list" "bigInst"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
      T"list" "list" [T"DOPER" "CFL" []])),
   C"grow_lt" "bigInst"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> bool))),
   C"dimword" "words"
    ((T"itself" "bool" [T"i32" "words" []] --> T"num" "num" [])),
   C"the_value" "bool" (T"itself" "bool" [T"i32" "words" []]),
   V"l" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   C"legal_pop_exp" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] -->
       (T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool)))),
   C"EVERY" "list"
    (((T"CFL_EXP" "bigInst" [] --> bool) -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool))),
   V"h" (T"CFL_EXP" "bigInst" []),
   C"unique_exp_list" "bigInst"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] --> bool))),
   V"dstL" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   V"srcL" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   C"copy_list" "bigInst"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] -->
       T"list" "list" [T"DOPER" "CFL" []]))),
   C"!" "bool" (((T"list" "list" [T"DOPER" "CFL" []] --> bool) --> bool)),
   V"l" (T"list" "list" [T"DOPER" "CFL" []]),
   C"sr_list" "bigInst"
    ((T"prod" "pair"
       [T"list" "list" [T"CFL_EXP" "bigInst" []],
        T"prod" "pair"
         [T"list" "list" [T"DOPER" "CFL" []],
          T"list" "list" [T"CFL_EXP" "bigInst" []]]] -->
      T"list" "list" [T"DOPER" "CFL" []])),
   C"," "pair"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] -->
      (T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"list" "list" [T"CFL_EXP" "bigInst" []]] -->
       T"prod" "pair"
        [T"list" "list" [T"CFL_EXP" "bigInst" []],
         T"prod" "pair"
          [T"list" "list" [T"DOPER" "CFL" []],
           T"list" "list" [T"CFL_EXP" "bigInst" []]]]))),
   C"," "pair"
    ((T"list" "list" [T"DOPER" "CFL" []] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] -->
       T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"list" "list" [T"CFL_EXP" "bigInst" []]]))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        (T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool)))
       --> bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] --> (T"CFL_EXP" "bigInst" [] --> bool)))),
   V"v11" (T"num" "num" []),
   V"v41" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v40" (T"num" "num" []), V"v10" (T"num" "num" []),
   V"v33" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v32" (T"num" "num" []),
   V"v9" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v27" (T"num" "num" []), V"v26" (T"num" "num" []),
   V"v24" (T"num" "num" []), V"v8" (T"num" "num" []),
   V"v19" (T"num" "num" []), V"v18" (T"num" "num" []),
   V"v17" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"v1" (T"CFL_EXP" "bigInst" []), V"v2" (T"CFL_EXP" "bigInst" []),
   C"," "pair"
    ((T"CFL_EXP" "bigInst" [] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"prod" "pair"
        [T"CFL_EXP" "bigInst" [],
         T"cart" "fcp" [bool, T"i32" "words" []]]))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        (T"prod" "pair"
          [T"CFL_EXP" "bigInst" [],
           T"cart" "fcp" [bool, T"i32" "words" []]] --> bool)) --> bool)
      --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"prod" "pair"
        [T"CFL_EXP" "bigInst" [], T"cart" "fcp" [bool, T"i32" "words" []]]
       --> bool))), V"v2" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"!" "bool" ((((T"CFL_EXP" "bigInst" [] --> bool) --> bool) --> bool)),
   V"P" ((T"CFL_EXP" "bigInst" [] --> bool)),
   V"C" (T"CFL_EXP" "bigInst" []), V"f0" ((T"num" "num" [] --> alpha)),
   C"?" "bool" ((((T"CFL_EXP" "bigInst" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"CFL_EXP" "bigInst" [] --> alpha)),
   V"M" (T"CFL_EXP" "bigInst" []), V"M'" (T"CFL_EXP" "bigInst" []),
   V"f'" ((T"num" "num" [] --> alpha)),
   V"f1'" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   V"f2'" ((T"num" "num" [] --> alpha)),
   V"f3'" ((T"num" "num" [] --> alpha)),
   V"a'" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"a'" (T"num" "num" []), C"DATATYPE" "bool" ((bool --> bool)),
   V"CFL_EXP"
    (((T"num" "num" [] --> T"CFL_EXP" "bigInst" []) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] -->
        T"CFL_EXP" "bigInst" []) -->
       ((T"num" "num" [] --> T"CFL_EXP" "bigInst" []) -->
        ((T"num" "num" [] --> T"CFL_EXP" "bigInst" []) --> bool))))),
   V"v3" (T"num" "num" []), V"v" (T"CFL_EXP" "bigInst" []),
   V"e1" (T"CFL_EXP" "bigInst" []), V"e2" (T"CFL_EXP" "bigInst" []),
   C"!" "bool" ((((T"num" "num" [] --> bool) --> bool) --> bool)),
   V"P" ((T"num" "num" [] --> bool)),
   V"v1" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"!" "bool" (((alpha --> bool) --> bool)), V"e" (alpha),
   C"COND" "bool"
    ((bool -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       (T"cart" "fcp" [bool, T"i32" "words" []] -->
        T"cart" "fcp" [bool, T"i32" "words" []])))),
   C"w2n" "words" ((T"cart" "fcp" [bool, alpha] --> T"num" "num" [])),
   V"i" (T"cart" "fcp" [bool, alpha]), V"k" (T"cart" "fcp" [bool, alpha]),
   C"word_sub" "words"
    ((T"cart" "fcp" [bool, alpha] -->
      (T"cart" "fcp" [bool, alpha] --> T"cart" "fcp" [bool, alpha]))),
   V"i" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_sub" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"j" (T"cart" "fcp" [bool, T"i32" "words" []]), V"j" (T"num" "num" []),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        (T"CFL_EXP" "bigInst" [] -->
         (T"prod" "pair" [T"num" "num" [], T"num" "num" []] --> bool))) -->
       bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"CFL_EXP" "bigInst" [] -->
       (T"prod" "pair" [T"num" "num" [], T"num" "num" []] --> bool)))),
   V"v6" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"v1" (T"prod" "pair" [T"num" "num" [], T"num" "num" []]),
   V"v5" (T"num" "num" []),
   V"v2" (T"prod" "pair" [T"num" "num" [], T"num" "num" []]),
   V"x" (T"num" "num" []), V"i" (T"num" "num" []),
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
   C"BLK" "CFL"
    ((T"list" "list" [T"DOPER" "CFL" []] --> T"CTL_STRUCTURE" "CFL" [])),
   V"l1" (T"list" "list" [T"DOPER" "CFL" []]),
   V"l2" (T"list" "list" [T"DOPER" "CFL" []]),
   C"sp" "CFL" (T"num" "num" []),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"l" (T"list" "list" [alpha]),
   C"LENGTH" "list" ((T"list" "list" [alpha] --> T"num" "num" [])),
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
   V"st1"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"x" (alpha),
   C"LENGTH" "list"
    ((T"list" "list" [T"CFL_EXP" "bigInst" []] --> T"num" "num" [])),
   V"st'"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"EL" "list"
    ((T"num" "num" [] -->
      (T"list" "list" [T"CFL_EXP" "bigInst" []] -->
       T"CFL_EXP" "bigInst" []))),
   C"PRE" "prim_rec" ((T"num" "num" [] --> T"num" "num" [])),
   C"word_add" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"k" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   V"x'" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"l1" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   V"l2" (T"list" "list" [T"CFL_EXP" "bigInst" []]),
   C"o" "combin"
    (((bool --> bool) -->
      ((T"CFL_EXP" "bigInst" [] --> bool) -->
       (T"CFL_EXP" "bigInst" [] --> bool))))]
  val DT = Thm.disk_thm share_table
  in
  val eq_exp_curried_def =
    DT([], [],
       `(%0 (\%1. (%2 (\%3. (%2 (\%4. ((%5 (((%6 $2) $1) $0)) (%7 ((%8 $2)
       ((%9 $1) $0))))))))))`)
  val eq_exp_tupled_primitive_def =
    DT([], [],
       `((%10 %7) ((%11 (%12 (\%13. (%14 $0)))) (\%15. (\%16. ((%17 (\%18.
       (\%19. ((%20 (\%21. (\%22. (((((%23 (\%24. (((((%23 (\%25. (%26
       ((%27 $1) $0)))) (\%28. (%26 %29))) (\%30. (%26 %29))) (\%31. (%26
       %29))) $1))) (\%32. (((((%23 (\%33. (%26 %29))) (\%34. (%26 ((%35
       $1) $0)))) (\%36. (%26 %29))) (\%37. (%26 %29))) $1))) (\%38.
       (((((%23 (\%39. (%26 %29))) (\%40. (%26 %29))) (\%41. (%26 (((%42
       $5) (%43 $1)) (%43 $0))))) (\%44. (%26 (((%42 $5) (%43 $1)) (%45
       $0))))) $1))) (\%46. (((((%23 (\%47. (%26 %29))) (\%48. (%26 %29)))
       (\%49. (%26 (((%42 $5) (%45 $1)) (%43 $0))))) (\%50. (%26 (((%42 $5)
       (%45 $1)) (%45 $0))))) $1))) $1)))) $0)))) $0)))))`)
  val eq_addr_def =
    DT([], [],
       `(%0 (\%18. (%2 (\%51. (%2 (\%52. ((%5 (((%42 $2) $1) $0)) ((%27
       ((%53 $2) $1)) ((%53 $2) $0)))))))))`)
  val addr_of_def =
    DT(["DISK_THM"], [],
       `((%54 (%0 (\%18. (%55 (\%44. ((%27 ((%53 $1) (%45 $0))) $0))))))
       (%0 (\%18. (%55 (\%49. ((%27 ((%53 $1) (%43 $0))) ((%56 (%57 ((%58
       $1) %59))) $0)))))))`)
  val writee_curried_def =
    DT([], [],
       `(%0 (\%1. (%60 (\%61. ((%62 ((%63 $1) $0)) (%64 ((%65 $1)
       $0)))))))`)
  val writee_tupled_primitive_def =
    DT([], [],
       `((%66 %64) ((%67 (%68 (\%69. (%70 $0)))) (\%71. (\%72. ((%73 (\%18.
       (\%74. ((%75 (\%76. (\%77. (((((%78 (\%79. (%80 (((%81 $4) (%82 $0))
       $1)))) (\%83. (%80 $4))) (\%84. (%80 (((%81 $4) (%85 ((%86 %87) (%88
       $0)))) $1)))) (\%44. (%80 ((%89 (%90 $4)) ((%91 (%92 $4)) ((%93 $0)
       $1)))))) $1)))) $0)))) $0)))))`)
  val reade_def =
    DT(["DISK_THM"], [],
       `((%54 (%0 (\%18. (%55 (\%79. ((%35 ((%94 $1) (%95 $0))) ((%58 $1)
       (%82 $0)))))))) ((%54 (%0 (\%18. (%96 (\%83. ((%35 ((%94 $1) (%97
       $0))) $0)))))) ((%54 (%0 (\%18. (%55 (\%84. ((%35 ((%94 $1) (%43
       $0))) ((%58 $1) (%85 ((%86 %87) (%88 $0)))))))))) (%0 (\%18. (%55
       (\%44. ((%35 ((%94 $1) (%45 $0))) ((%98 (%92 $1)) $0)))))))))`)
  val CFL_EXP_size_def =
    DT(["DISK_THM"], [],
       `((%54 (%55 (\%99. ((%27 (%100 (%95 $0))) ((%101 (%102 (%103 %104)))
       $0))))) ((%54 (%96 (\%105. ((%27 (%100 (%97 $0))) (%102 (%103
       %104)))))) ((%54 (%55 (\%99. ((%27 (%100 (%43 $0))) ((%101 (%102
       (%103 %104))) $0))))) (%55 (\%99. ((%27 (%100 (%45 $0))) ((%101
       (%102 (%103 %104))) $0)))))))`)
  val CFL_EXP_case_def =
    DT(["DISK_THM"], [],
       `((%54 (%106 (\%107. (%108 (\%109. (%106 (\%110. (%106 (\%111. (%55
       (\%99. ((%112 (((((%113 $4) $3) $2) $1) (%95 $0))) ($4
       $0))))))))))))) ((%54 (%106 (\%107. (%108 (\%109. (%106 (\%110.
       (%106 (\%111. (%96 (\%105. ((%112 (((((%113 $4) $3) $2) $1) (%97
       $0))) ($3 $0))))))))))))) ((%54 (%106 (\%107. (%108 (\%109. (%106
       (\%110. (%106 (\%111. (%55 (\%99. ((%112 (((((%113 $4) $3) $2) $1)
       (%43 $0))) ($2 $0))))))))))))) (%106 (\%107. (%108 (\%109. (%106
       (\%110. (%106 (\%111. (%55 (\%99. ((%112 (((((%113 $4) $3) $2) $1)
       (%45 $0))) ($1 $0)))))))))))))))`)
  val isM = DT([], [], `((%114 %45) %115)`)
  val isV = DT([], [], `((%114 %43) %116)`)
  val isC = DT([], [], `((%117 %97) %118)`)
  val isR = DT([], [], `((%114 %95) %119)`)
  val bigInst3_def =
    DT([], [],
       `((%114 %115) (\%99. (%120 ((\%99. (((%121 (%122 (%122 (%122
       %123)))) ((%93 $0) (%124 (\%77. %125)))) (\%126. %127))) $0))))`)
  val bigInst2_def =
    DT([], [],
       `((%114 %116) (\%99. (%120 ((\%99. (((%121 (%122 (%122 %123))) ((%93
       $0) (%124 (\%77. %125)))) (\%126. %127))) $0))))`)
  val bigInst1_def =
    DT([], [],
       `((%117 %118) (\%105. (%120 ((\%105. (((%121 (%122 %123)) ((%93
       (%128 (\%49. %125))) $0)) (\%126. %127))) $0))))`)
  val bigInst0_def =
    DT([], [],
       `((%114 %119) (\%99. (%120 ((\%99. (((%121 %123) ((%93 $0) (%124
       (\%77. %125)))) (\%126. %127))) $0))))`)
  val CFL_EXP_repfns =
    DT(["DISK_THM"], [],
       `((%54 (%2 (\%129. ((%130 (%120 (%131 $0))) $0)))) (%132 (\%133.
       ((%5 ((\%134. (%135 (\%136. ((%137 (%132 (\%134. ((%137 ((%138 (%139
       (\%99. ((%140 $1) ((\%99. (((%121 %123) ((%93 $0) (%124 (\%77.
       %125)))) (\%126. %127))) $0))))) ((%138 (%141 (\%105. ((%140 $1)
       ((\%105. (((%121 (%122 %123)) ((%93 (%128 (\%49. %125))) $0))
       (\%126. %127))) $0))))) ((%138 (%139 (\%99. ((%140 $1) ((\%99.
       (((%121 (%122 (%122 %123))) ((%93 $0) (%124 (\%77. %125)))) (\%126.
       %127))) $0))))) (%139 (\%99. ((%140 $1) ((\%99. (((%121 (%122 (%122
       (%122 %123)))) ((%93 $0) (%124 (\%77. %125)))) (\%126. %127)))
       $0)))))))) ($1 $0))))) ($0 $1))))) $0)) ((%140 (%131 (%120 $0)))
       $0)))))`)
  val CFL_EXP_TY_DEF =
    DT(["DISK_THM"], [],
       `(%142 (\%143. ((%144 (\%134. (%135 (\%136. ((%137 (%132 (\%134.
       ((%137 ((%138 (%139 (\%99. ((%140 $1) ((\%99. (((%121 %123) ((%93
       $0) (%124 (\%77. %125)))) (\%126. %127))) $0))))) ((%138 (%141
       (\%105. ((%140 $1) ((\%105. (((%121 (%122 %123)) ((%93 (%128 (\%49.
       %125))) $0)) (\%126. %127))) $0))))) ((%138 (%139 (\%99. ((%140 $1)
       ((\%99. (((%121 (%122 (%122 %123))) ((%93 $0) (%124 (\%77. %125))))
       (\%126. %127))) $0))))) (%139 (\%99. ((%140 $1) ((\%99. (((%121
       (%122 (%122 (%122 %123)))) ((%93 $0) (%124 (\%77. %125)))) (\%126.
       %127))) $0)))))))) ($1 $0))))) ($0 $1)))))) $0)))`)
  val is_C_primitive_def =
    DT([], [],
       `((%145 %146) ((%147 (%148 (\%149. (%150 $0)))) (\%151. (\%129.
       (((((%23 (\%152. (%26 %29))) (\%83. (%26 %125))) (\%153. (%26 %29)))
       (\%154. (%26 %29))) $0)))))`)
  val valid_regs_primitive_def =
    DT([], [],
       `((%155 %156) ((%157 (%158 (\%159. (%160 $0)))) (\%161. (\%99. (%26
       ((%54 (%162 ((%27 $0) (%102 (%103 (%163 (%103 %104))))))) ((%54
       (%162 ((%27 $0) (%102 (%163 (%163 (%103 %104))))))) ((%54 (%162
       ((%27 $0) (%102 (%103 (%103 (%163 %104))))))) ((%54 (%162 ((%27 $0)
       (%102 (%163 (%103 (%163 %104))))))) ((%54 (%162 ((%27 $0) (%102
       (%103 (%163 (%163 %104))))))) ((%54 (%162 ((%27 $0) (%102 (%163
       (%163 (%163 %104))))))) ((%54 (%162 ((%27 $0) (%102 (%103 (%103
       (%103 (%103 %104)))))))) ((%27 (%164 (%165 $0))) $0)))))))))))))`)
  val valid_exp_primitive_def =
    DT([], [],
       `((%145 %166) ((%147 (%148 (\%149. (%150 $0)))) (\%167. (\%129.
       (((((%23 (\%79. (%26 (%156 $0)))) (\%168. (%26 %125))) (\%153. (%26
       %125))) (\%44. (%26 %29))) $0)))))`)
  val valid_exp_1_primitive_def =
    DT([], [],
       `((%145 %169) ((%147 (%148 (\%149. (%150 $0)))) (\%170. (\%129.
       (((((%23 (\%79. (%26 ((%54 (%162 ((%27 $0) (%102 (%103 (%163 (%163
       %104))))))) ((%54 (%162 ((%27 $0) (%102 (%103 (%163 (%103
       %104))))))) ((%27 (%164 (%165 $0))) $0)))))) (\%168. (%26 %125)))
       (\%153. (%26 %125))) (\%44. (%26 %125))) $0)))))`)
  val valid_exp_2_primitive_def =
    DT([], [],
       `((%145 %171) ((%147 (%148 (\%149. (%150 $0)))) (\%172. (\%129.
       (((((%23 (\%79. (%26 (%156 $0)))) (\%168. (%26 %125))) (\%153. (%26
       %125))) (\%44. (%26 %125))) $0)))))`)
  val valid_exp_3_primitive_def =
    DT([], [],
       `((%145 %173) ((%147 (%148 (\%149. (%150 $0)))) (\%174. (\%129.
       (((((%23 (\%79. (%26 ((%27 (%164 (%165 $0))) $0)))) (\%168. (%26
       %125))) (\%153. (%26 %125))) (\%44. (%26 %29))) $0)))))`)
  val locate_ge_def =
    DT([], [],
       `(%96 (\%175. (%55 (\%84. ((%5 ((%176 $1) $0)) ((%177 $0) (%57
       $1)))))))`)
  val in_range_def =
    DT(["DISK_THM"], [],
       `(%55 (\%84. (%55 (\%178. (%55 (\%179. ((%5 ((%180 $2) ((%181 $1)
       $0))) ((%54 ((%177 $2) $1)) ((%182 $0) $2)))))))))`)
  val addr_in_range_tupled_primitive_def =
    DT([], [],
       `((%183 %184) ((%185 (%186 (\%187. (%188 $0)))) (\%189. (\%190.
       ((%191 (\%18. (\%192. ((%193 (\%76. (\%194. (((((%23 (\%195. (%26
       %29))) (\%196. (%26 %29))) (\%84. (%26 ((%180 ((%53 $4) (%43 $0)))
       $1)))) (\%44. (%26 ((%180 $0) $1)))) $1)))) $0)))) $0)))))`)
  val addr_in_range_curried_def =
    DT([], [],
       `(%0 (\%1. (%2 (\%3. (%197 (\%198. ((%5 (((%199 $2) $1) $0)) (%184
       ((%200 $2) ((%201 $1) $0))))))))))`)
  val store_one_def =
    DT(["DISK_THM"], [],
       `((%54 (%55 (\%79. (%202 (\%203. ((%204 ((%205 (%95 $1)) $0)) ((%206
       ((%207 ((%86 (%102 (%103 (%163 (%163 %104))))) $0)) (%165 $1)))
       %208))))))) ((%54 (%96 (\%83. (%202 (\%203. ((%204 ((%205 (%97 $1))
       $0)) ((%206 ((%209 %210) (%211 $1))) ((%206 ((%207 ((%86 (%102 (%103
       (%163 (%163 %104))))) $0)) %210)) %208)))))))) (%55 (\%84. (%202
       (\%203. ((%204 ((%205 (%43 $1)) $0)) ((%206 ((%212 %210) ((%86 %87)
       (%88 $1)))) ((%206 ((%207 ((%86 (%102 (%103 (%163 (%163 %104)))))
       $0)) %210)) %208)))))))))`)
  val load_one_def =
    DT(["DISK_THM"], [],
       `((%54 (%55 (\%79. (%202 (\%203. ((%204 ((%213 (%95 $1)) $0)) ((%206
       ((%212 (%165 $1)) ((%86 (%102 (%103 (%163 (%163 %104))))) $0)))
       %208))))))) ((%54 (%96 (\%83. (%202 (\%203. ((%204 ((%213 (%97 $1))
       $0)) %208)))))) (%55 (\%84. (%202 (\%203. ((%204 ((%213 (%43 $1))
       $0)) ((%206 ((%212 %210) ((%86 (%102 (%103 (%163 (%163 %104)))))
       $0))) ((%206 ((%207 ((%86 %87) (%88 ((%101 (%102 (%163 (%103 (%163
       %104))))) $1)))) %210)) %208)))))))))`)
  val push_one_def =
    DT(["DISK_THM"], [],
       `((%54 (%55 (\%79. ((%204 (%214 (%95 $0))) ((%206 ((%207 ((%86 (%102
       (%103 (%163 (%163 %104))))) (%88 %123))) (%165 $0))) ((%206 (((%215
       %216) %216) (%211 (%217 (%102 (%103 %104)))))) %208)))))) ((%54 (%96
       (\%83. ((%204 (%214 (%97 $0))) ((%206 ((%209 %210) (%211 $0)))
       ((%206 ((%207 ((%86 (%102 (%103 (%163 (%163 %104))))) (%88 %123)))
       %210)) ((%206 (((%215 %216) %216) (%211 (%217 (%102 (%103 %104))))))
       %208))))))) ((%54 (%55 (\%84. ((%204 (%214 (%43 $0))) ((%206 ((%212
       %210) ((%86 %87) (%88 $0)))) ((%206 ((%207 ((%86 (%102 (%103 (%163
       (%163 %104))))) (%88 %123))) %210)) ((%206 (((%215 %216) %216) (%211
       (%217 (%102 (%103 %104)))))) %208))))))) (%55 (\%44. ((%204 (%214
       (%45 $0))) ((%206 (((%215 %216) %216) (%211 (%217 (%102 (%103
       %104)))))) %208)))))))`)
  val pop_one_def =
    DT(["DISK_THM"], [],
       `((%54 (%55 (\%79. ((%204 (%218 (%95 $0))) ((%206 ((%212 (%165 $0))
       ((%86 (%102 (%103 (%163 (%163 %104))))) (%219 (%102 (%103 %104))))))
       ((%206 (((%220 %216) %216) (%211 (%217 (%102 (%103 %104))))))
       %208)))))) ((%54 (%96 (\%83. ((%204 (%218 (%97 $0))) ((%206 (((%220
       %216) %216) (%211 (%217 (%102 (%103 %104)))))) %208))))) ((%54 (%55
       (\%84. ((%204 (%218 (%43 $0))) ((%206 ((%212 %210) ((%86 (%102 (%103
       (%163 (%163 %104))))) (%219 (%102 (%103 %104)))))) ((%206 ((%207
       ((%86 %87) (%88 $0))) %210)) ((%206 (((%220 %216) %216) (%211 (%217
       (%102 (%103 %104)))))) %208))))))) (%55 (\%44. ((%204 (%218 (%45
       $0))) ((%206 (((%220 %216) %216) (%211 (%217 (%102 (%103 %104))))))
       %208)))))))`)
  val push_list_def =
    DT(["DISK_THM"], [],
       `((%54 ((%204 (%221 %222)) %208)) (%2 (\%223. (%224 (\%225. ((%204
       (%221 ((%226 $1) $0))) ((%227 (%221 $0)) (%214 $1))))))))`)
  val legal_push_exp_def =
    DT([], [],
       `(%0 (\%18. (%2 (\%228. (%55 (\%84. ((%5 (((%229 $2) $1) $0)) ((%54
       (%162 (((%199 $2) $1) ((%181 (%57 ((%58 $2) %230))) ((%56 (%57 ((%58
       $2) %230))) $0))))) (%169 $1)))))))))`)
  val pop_list_def =
    DT(["DISK_THM"], [],
       `((%54 ((%204 (%231 %222)) %208)) (%2 (\%223. (%224 (\%225. ((%204
       (%231 ((%226 $1) $0))) ((%227 (%218 $1)) (%231 $0))))))))`)
  val grow_lt_def =
    DT([], [],
       `(%96 (\%175. (%55 (\%84. ((%5 ((%232 $1) $0)) ((%182 ((%101 (%57
       $1)) $0)) (%233 %234)))))))`)
  val legal_pop_exp_def =
    DT([], [],
       `(%0 (\%18. (%2 (\%228. (%224 (\%235. ((%5 (((%236 $2) $1) $0))
       ((%54 ((%237 (\%223. (%162 (((%6 $3) $2) $0)))) $0)) ((%54 (%162
       (%146 $1))) (%166 $1))))))))))`)
  val unique_exp_list_def =
    DT(["DISK_THM"], [],
       `((%54 (%0 (\%18. (%2 (\%238. (%224 (\%235. ((%5 ((%239 $2) ((%226
       $1) $0))) ((%54 ((%237 (\%223. (%162 (((%6 $3) $2) $0)))) $0))
       ((%239 $2) $0)))))))))) (%0 (\%18. ((%5 ((%239 $0) %222)) %125))))`)
  val copy_list_def =
    DT([], [],
       `(%224 (\%240. (%224 (\%241. ((%204 ((%242 $1) $0)) ((%227 (%221
       $0)) (%231 $1)))))))`)
  val sr_list_def =
    DT(["DISK_THM"], [],
       `(%224 (\%240. (%243 (\%244. (%224 (\%241. ((%204 (%245 ((%246 $2)
       ((%247 $1) $0)))) ((%227 ((%227 (%221 $0)) $1)) (%231 $2)))))))))`)
  val eq_exp_ind =
    DT(["DISK_THM"], [],
       `(%248 (\%249. ((%137 ((%54 (%0 (\%18. (%55 (\%24. (%55 (\%25. ((($3
       $2) (%95 $1)) (%95 $0))))))))) ((%54 (%0 (\%18. (%96 (\%32. (%96
       (\%34. ((($3 $2) (%97 $1)) (%97 $0))))))))) ((%54 (%0 (\%18. (%55
       (\%38. (%55 (\%41. ((($3 $2) (%43 $1)) (%43 $0))))))))) ((%54 (%0
       (\%18. (%55 (\%46. (%55 (\%50. ((($3 $2) (%45 $1)) (%45 $0)))))))))
       ((%54 (%0 (\%18. (%55 (\%44. (%55 (\%49. ((($3 $2) (%45 $1)) (%43
       $0))))))))) ((%54 (%0 (\%18. (%55 (\%49. (%55 (\%44. ((($3 $2) (%43
       $1)) (%45 $0))))))))) ((%54 (%0 (\%18. (%55 (\%250. (%96 (\%251.
       ((($3 $2) (%45 $1)) (%97 $0))))))))) ((%54 (%0 (\%18. (%55 (\%250.
       (%55 (\%252. ((($3 $2) (%45 $1)) (%95 $0))))))))) ((%54 (%0 (\%18.
       (%55 (\%253. (%96 (\%254. ((($3 $2) (%43 $1)) (%97 $0))))))))) ((%54
       (%0 (\%18. (%55 (\%253. (%55 (\%255. ((($3 $2) (%43 $1)) (%95
       $0))))))))) ((%54 (%0 (\%18. (%96 (\%256. (%55 (\%257. ((($3 $2)
       (%97 $1)) (%45 $0))))))))) ((%54 (%0 (\%18. (%96 (\%256. (%55
       (\%258. ((($3 $2) (%97 $1)) (%43 $0))))))))) ((%54 (%0 (\%18. (%96
       (\%256. (%55 (\%259. ((($3 $2) (%97 $1)) (%95 $0))))))))) ((%54 (%0
       (\%18. (%55 (\%260. (%55 (\%261. ((($3 $2) (%95 $1)) (%45
       $0))))))))) ((%54 (%0 (\%18. (%55 (\%260. (%55 (\%262. ((($3 $2)
       (%95 $1)) (%43 $0))))))))) (%0 (\%18. (%55 (\%260. (%96 (\%263.
       ((($3 $2) (%95 $1)) (%97 $0)))))))))))))))))))))))) (%0 (\%264. (%2
       (\%265. (%2 (\%266. ((($3 $2) $1) $0))))))))))`)
  val writee_def =
    DT(["DISK_THM"], [],
       `((%54 ((%62 ((%63 %18) ((%267 (%95 %79)) %77))) (((%81 %18) (%82
       %79)) %77))) ((%54 ((%62 ((%63 %18) ((%267 (%97 %83)) %77))) %18))
       ((%54 ((%62 ((%63 %18) ((%267 (%43 %84)) %77))) (((%81 %18) (%85
       ((%86 %87) (%88 %84)))) %77))) ((%62 ((%63 %18) ((%267 (%45 %44))
       %77))) ((%89 (%90 %18)) ((%91 (%92 %18)) ((%93 %44) %77)))))))`)
  val writee_ind =
    DT(["DISK_THM"], [],
       `(%268 (\%269. ((%137 ((%54 (%0 (\%18. (%55 (\%79. (%96 (\%77. (($3
       $2) ((%267 (%95 $1)) $0))))))))) ((%54 (%0 (\%18. (%96 (\%83. (%96
       (\%77. (($3 $2) ((%267 (%97 $1)) $0))))))))) ((%54 (%0 (\%18. (%55
       (\%84. (%96 (\%77. (($3 $2) ((%267 (%43 $1)) $0))))))))) (%0 (\%18.
       (%55 (\%44. (%96 (\%77. (($3 $2) ((%267 (%45 $1)) $0)))))))))))) (%0
       (\%264. (%2 (\%265. (%96 (\%270. (($3 $2) ((%267 $1) $0)))))))))))`)
  val CFL_EXP_induction =
    DT(["DISK_THM"], [],
       `(%271 (\%272. ((%137 ((%54 (%55 (\%126. ($1 (%95 $0))))) ((%54 (%96
       (\%83. ($1 (%97 $0))))) ((%54 (%55 (\%126. ($1 (%43 $0))))) (%55
       (\%126. ($1 (%45 $0)))))))) (%2 (\%273. ($1 $0))))))`)
  val CFL_EXP_Axiom =
    DT(["DISK_THM"], [],
       `(%106 (\%274. (%108 (\%109. (%106 (\%110. (%106 (\%111. (%275
       (\%276. ((%54 (%55 (\%99. ((%112 ($1 (%95 $0))) ($5 $0))))) ((%54
       (%96 (\%105. ((%112 ($1 (%97 $0))) ($4 $0))))) ((%54 (%55 (\%99.
       ((%112 ($1 (%43 $0))) ($3 $0))))) (%55 (\%99. ((%112 ($1 (%45 $0)))
       ($2 $0)))))))))))))))))`)
  val CFL_EXP_nchotomy =
    DT(["DISK_THM"], [],
       `(%2 (\%273. ((%138 (%139 (\%126. ((%130 $1) (%95 $0))))) ((%138
       (%141 (\%83. ((%130 $1) (%97 $0))))) ((%138 (%139 (\%126. ((%130 $1)
       (%43 $0))))) (%139 (\%126. ((%130 $1) (%45 $0)))))))))`)
  val CFL_EXP_case_cong =
    DT(["DISK_THM"], [],
       `(%2 (\%277. (%2 (\%278. (%106 (\%107. (%108 (\%109. (%106 (\%110.
       (%106 (\%111. ((%137 ((%54 ((%130 $5) $4)) ((%54 (%55 (\%99. ((%137
       ((%130 $5) (%95 $0))) ((%112 ($4 $0)) (%279 $0)))))) ((%54 (%96
       (\%105. ((%137 ((%130 $5) (%97 $0))) ((%112 ($3 $0)) (%280 $0))))))
       ((%54 (%55 (\%99. ((%137 ((%130 $5) (%43 $0))) ((%112 ($2 $0)) (%281
       $0)))))) (%55 (\%99. ((%137 ((%130 $5) (%45 $0))) ((%112 ($1 $0))
       (%282 $0)))))))))) ((%112 (((((%113 $3) $2) $1) $0) $5)) (((((%113
       %279) %280) %281) %282) $4)))))))))))))))`)
  val CFL_EXP_distinct =
    DT(["DISK_THM"], [],
       `((%54 (%96 (\%283. (%55 (\%99. (%162 ((%130 (%95 $0)) (%97
       $1)))))))) ((%54 (%55 (\%284. (%55 (\%99. (%162 ((%130 (%95 $0))
       (%43 $1)))))))) ((%54 (%55 (\%284. (%55 (\%99. (%162 ((%130 (%95
       $0)) (%45 $1)))))))) ((%54 (%55 (\%284. (%96 (\%105. (%162 ((%130
       (%97 $0)) (%43 $1)))))))) ((%54 (%55 (\%284. (%96 (\%105. (%162
       ((%130 (%97 $0)) (%45 $1)))))))) (%55 (\%284. (%55 (\%99. (%162
       ((%130 (%43 $0)) (%45 $1))))))))))))`)
  val CFL_EXP_11 =
    DT(["DISK_THM"], [],
       `((%54 (%55 (\%99. (%55 (\%284. ((%5 ((%130 (%95 $1)) (%95 $0)))
       ((%27 $1) $0))))))) ((%54 (%96 (\%105. (%96 (\%283. ((%5 ((%130 (%97
       $1)) (%97 $0))) ((%35 $1) $0))))))) ((%54 (%55 (\%99. (%55 (\%284.
       ((%5 ((%130 (%43 $1)) (%43 $0))) ((%27 $1) $0))))))) (%55 (\%99.
       (%55 (\%284. ((%5 ((%130 (%45 $1)) (%45 $0))) ((%27 $1)
       $0)))))))))`)
  val datatype_CFL_EXP =
    DT(["DISK_THM"], [], `(%285 ((((%286 %95) %97) %43) %45))`)
  val eq_exp_def =
    DT(["DISK_THM"], [],
       `((%54 ((%5 (((%6 %18) (%95 %24)) (%95 %25))) ((%27 %24) %25)))
       ((%54 ((%5 (((%6 %18) (%97 %32)) (%97 %34))) ((%35 %32) %34))) ((%54
       ((%5 (((%6 %18) (%43 %38)) (%43 %41))) (((%42 %18) (%43 %38)) (%43
       %41)))) ((%54 ((%5 (((%6 %18) (%45 %46)) (%45 %50))) (((%42 %18)
       (%45 %46)) (%45 %50)))) ((%54 ((%5 (((%6 %18) (%45 %44)) (%43 %49)))
       (((%42 %18) (%45 %44)) (%43 %49)))) ((%54 ((%5 (((%6 %18) (%43 %49))
       (%45 %44))) (((%42 %18) (%43 %49)) (%45 %44)))) ((%54 ((%5 (((%6
       %18) (%45 %250)) (%97 %251))) %29)) ((%54 ((%5 (((%6 %18) (%45
       %250)) (%95 %252))) %29)) ((%54 ((%5 (((%6 %18) (%43 %253)) (%97
       %254))) %29)) ((%54 ((%5 (((%6 %18) (%43 %253)) (%95 %255))) %29))
       ((%54 ((%5 (((%6 %18) (%97 %256)) (%45 %257))) %29)) ((%54 ((%5
       (((%6 %18) (%97 %256)) (%43 %258))) %29)) ((%54 ((%5 (((%6 %18) (%97
       %256)) (%95 %259))) %29)) ((%54 ((%5 (((%6 %18) (%95 %260)) (%45
       %261))) %29)) ((%54 ((%5 (((%6 %18) (%95 %260)) (%43 %262))) %29))
       ((%5 (((%6 %18) (%95 %260)) (%97 %263))) %29))))))))))))))))`)
  val is_C_ind =
    DT(["DISK_THM"], [],
       `(%271 (\%272. ((%137 ((%54 (%96 (\%83. ($1 (%97 $0))))) ((%54 (%55
       (\%287. ($1 (%45 $0))))) ((%54 (%55 (\%41. ($1 (%43 $0))))) (%55
       (\%49. ($1 (%95 $0)))))))) (%2 (\%288. ($1 $0))))))`)
  val is_C_def =
    DT(["DISK_THM"], [],
       `((%54 ((%5 (%146 (%97 %83))) %125)) ((%54 ((%5 (%146 (%45 %287)))
       %29)) ((%54 ((%5 (%146 (%43 %41))) %29)) ((%5 (%146 (%95 %49)))
       %29))))`)
  val eq_exp_SYM =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%289. (%2 (\%290. ((%5 (((%6 $2) $1) $0)) (((%6
       $2) $0) $1))))))))`)
  val NOT_EQ_isR_LEM =
    DT(["DISK_THM"], [],
       `(%2 (\%228. (%55 (\%79. ((%5 (%162 ((%130 $1) (%95 $0)))) (%0
       (\%18. (%162 (((%6 $0) (%95 $1)) $2)))))))))`)
  val valid_regs_ind =
    DT(["DISK_THM"], [],
       `(%291 (\%292. ((%137 (%55 (\%79. ($1 $0)))) (%55 (\%49. ($1
       $0))))))`)
  val valid_regs_def =
    DT(["DISK_THM"], [],
       `((%5 (%156 %79)) ((%54 (%162 ((%27 %79) (%102 (%103 (%163 (%103
       %104))))))) ((%54 (%162 ((%27 %79) (%102 (%163 (%163 (%103
       %104))))))) ((%54 (%162 ((%27 %79) (%102 (%103 (%103 (%163
       %104))))))) ((%54 (%162 ((%27 %79) (%102 (%163 (%103 (%163
       %104))))))) ((%54 (%162 ((%27 %79) (%102 (%103 (%163 (%163
       %104))))))) ((%54 (%162 ((%27 %79) (%102 (%163 (%163 (%163
       %104))))))) ((%54 (%162 ((%27 %79) (%102 (%103 (%103 (%103 (%103
       %104)))))))) ((%27 (%164 (%165 %79))) %79)))))))))`)
  val valid_regs_lem =
    DT(["DISK_THM"], [],
       `(%55 (\%79. ((%137 (%156 $0)) ((%54 (%162 ((%27 $0) (%102 (%103
       (%163 (%163 %104))))))) ((%54 (%162 ((%27 $0) (%102 (%103 (%163
       (%103 %104))))))) ((%54 (%162 ((%27 $0) (%102 (%103 (%103 (%163
       %104))))))) ((%27 (%164 (%165 $0))) $0)))))))`)
  val valid_exp_ind =
    DT(["DISK_THM"], [],
       `(%271 (\%272. ((%137 ((%54 (%55 (\%79. ($1 (%95 $0))))) ((%54 (%55
       (\%44. ($1 (%45 $0))))) ((%54 (%55 (\%41. ($1 (%43 $0))))) (%96
       (\%293. ($1 (%97 $0)))))))) (%2 (\%288. ($1 $0))))))`)
  val valid_exp_def =
    DT(["DISK_THM"], [],
       `((%54 ((%5 (%166 (%95 %79))) (%156 %79))) ((%54 ((%5 (%166 (%45
       %44))) %29)) ((%54 ((%5 (%166 (%43 %41))) %125)) ((%5 (%166 (%97
       %293))) %125))))`)
  val valid_exp_1_ind =
    DT(["DISK_THM"], [],
       `(%271 (\%272. ((%137 ((%54 (%55 (\%79. ($1 (%95 $0))))) ((%54 (%55
       (\%44. ($1 (%45 $0))))) ((%54 (%55 (\%41. ($1 (%43 $0))))) (%96
       (\%293. ($1 (%97 $0)))))))) (%2 (\%288. ($1 $0))))))`)
  val valid_exp_1_def =
    DT(["DISK_THM"], [],
       `((%54 ((%5 (%169 (%95 %79))) ((%54 (%162 ((%27 %79) (%102 (%103
       (%163 (%163 %104))))))) ((%54 (%162 ((%27 %79) (%102 (%103 (%163
       (%103 %104))))))) ((%27 (%164 (%165 %79))) %79))))) ((%54 ((%5 (%169
       (%45 %44))) %125)) ((%54 ((%5 (%169 (%43 %41))) %125)) ((%5 (%169
       (%97 %293))) %125))))`)
  val valid_exp_2_ind =
    DT(["DISK_THM"], [],
       `(%271 (\%272. ((%137 ((%54 (%55 (\%79. ($1 (%95 $0))))) ((%54 (%55
       (\%44. ($1 (%45 $0))))) ((%54 (%55 (\%41. ($1 (%43 $0))))) (%96
       (\%293. ($1 (%97 $0)))))))) (%2 (\%288. ($1 $0))))))`)
  val valid_exp_2_def =
    DT(["DISK_THM"], [],
       `((%54 ((%5 (%171 (%95 %79))) (%156 %79))) ((%54 ((%5 (%171 (%45
       %44))) %125)) ((%54 ((%5 (%171 (%43 %41))) %125)) ((%5 (%171 (%97
       %293))) %125))))`)
  val valid_exp_3_ind =
    DT(["DISK_THM"], [],
       `(%271 (\%272. ((%137 ((%54 (%55 (\%79. ($1 (%95 $0))))) ((%54 (%55
       (\%44. ($1 (%45 $0))))) ((%54 (%55 (\%41. ($1 (%43 $0))))) (%96
       (\%293. ($1 (%97 $0)))))))) (%2 (\%288. ($1 $0))))))`)
  val valid_exp_3_def =
    DT(["DISK_THM"], [],
       `((%54 ((%5 (%173 (%95 %79))) ((%27 (%164 (%165 %79))) %79))) ((%54
       ((%5 (%173 (%45 %44))) %29)) ((%54 ((%5 (%173 (%43 %41))) %125))
       ((%5 (%173 (%97 %293))) %125))))`)
  val valid_exp_thm =
    DT(["DISK_THM"], [],
       `(%2 (\%228. ((%137 (%166 $0)) ((%54 (%169 $0)) ((%54 (%171 $0))
       (%173 $0))))))`)
  val VALID_EXP_LEM =
    DT(["DISK_THM"], [],
       `(%224 (\%235. ((%137 ((%237 %166) $0)) ((%54 ((%237 %169) $0))
       ((%54 ((%237 %171) $0)) ((%237 %173) $0))))))`)
  val READE_WRITEE =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%228. (%96 (\%77. ((%137 (%162 (%146 $1))) ((%35
       ((%94 ((%63 $2) ((%267 $1) $0))) $1)) $0))))))))`)
  val READE_WRITEE_THM =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%294 (\%295. (%96 (\%77. ((%137 ((%54 (%162 (%146
       %289))) (%166 %289))) ((%35 ((%94 ((%63 $2) ((%267 %289) $0)))
       %290)) (((%296 (((%6 $2) %289) %290)) $0) ((%94 $2) %290))))))))))`)
  val READE_WRITEE_THM_2 =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%294 (\%295. (%96 (\%77. ((%137 ((%54 (%162 (((%6 $2)
       %289) %290))) (%162 ((%130 %289) (%95 %87))))) ((%35 ((%94 ((%63 $2)
       ((%267 %289) $0))) %290)) ((%94 $2) %290)))))))))`)
  val WRITEE_EQ =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%228. (%96 (\%293. (%96 (\%270. ((%62 ((%63 ((%63
       $3) ((%267 $2) $1))) ((%267 $2) $0))) ((%63 $3) ((%267 $2)
       $0)))))))))))`)
  val WRITEE_COMMUTES =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%289. (%2 (\%290. (%96 (\%293. (%96 (\%270. ((%137
       ((%54 (%162 (((%6 $4) $3) $2))) ((%54 (%166 $3)) (%166 $2)))) ((%62
       ((%63 ((%63 $4) ((%267 $3) $1))) ((%267 $2) $0))) ((%63 ((%63 $4)
       ((%267 $2) $0))) ((%267 $3) $1))))))))))))))`)
  val w2n_sub_lem =
    DT(["DISK_THM"], [],
       `((%137 ((%177 (%297 %298)) (%297 %299))) ((%27 (%297 ((%300 %299)
       %298))) ((%56 (%297 %299)) (%297 %298))))`)
  val locate_ge_lem_1 =
    DT(["DISK_THM"], [],
       `((%137 ((%176 %175) %84)) (%96 (\%301. ((%137 ((%177 (%57 $0))
       %84)) ((%27 (%57 ((%302 %175) $0))) ((%56 (%57 %175)) (%57
       $0)))))))`)
  val locate_ge_lem_2 =
    DT(["DISK_THM"], [],
       `((%137 ((%176 %175) %84)) ((%54 (%96 (\%301. (%96 (\%303. ((%137
       ((%54 (%162 ((%35 $1) $0))) ((%54 ((%177 (%57 $1)) %84)) ((%177 (%57
       $0)) %84)))) (%162 ((%27 (%57 ((%302 %175) $1))) (%57 ((%302 %175)
       $0)))))))))) (%55 (\%304. ((%137 ((%177 (%102 (%103 %104))) (%57
       %175))) ((%27 ((%101 ((%56 (%57 %175)) (%102 (%103 %104)))) ((%101
       $0) (%102 (%163 %104))))) ((%101 (%57 %175)) (%122 $0))))))))`)
  val locate_ge_thm =
    DT(["DISK_THM"], [],
       `(%96 (\%175. (%55 (\%84. ((%137 ((%176 $1) (%122 $0))) ((%54 ((%176
       $1) (%102 (%103 %104)))) ((%176 $1) $0)))))))`)
  val addr_in_range_ind =
    DT(["DISK_THM"], [],
       `(%305 (\%306. ((%137 ((%54 (%0 (\%18. (%55 (\%44. (%197 (\%194.
       ((($3 $2) (%45 $1)) $0)))))))) ((%54 (%0 (\%18. (%55 (\%84. (%197
       (\%194. ((($3 $2) (%43 $1)) $0)))))))) ((%54 (%0 (\%18. (%96 (\%307.
       (%197 (\%308. ((($3 $2) (%97 $1)) $0)))))))) (%0 (\%18. (%55 (\%309.
       (%197 (\%308. ((($3 $2) (%95 $1)) $0))))))))))) (%0 (\%264. (%2
       (\%265. (%197 (\%310. ((($3 $2) $1) $0))))))))))`)
  val addr_in_range_def =
    DT(["DISK_THM"], [],
       `((%54 ((%5 (((%199 %18) (%45 %44)) %194)) ((%180 %44) %194))) ((%54
       ((%5 (((%199 %18) (%43 %84)) %194)) ((%180 ((%53 %18) (%43 %84)))
       %194))) ((%54 ((%5 (((%199 %18) (%97 %307)) %308)) %29)) ((%5
       (((%199 %18) (%95 %309)) %308)) %29))))`)
  val ADDR_IN_RANGE_OUTSIDE =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%228. (%55 (\%311. (%55 (\%312. ((%137 ((%54 (%162
       (((%199 $3) $2) ((%181 $1) ((%56 $1) (%122 $0)))))) ((%177 (%122
       $0)) $1))) (%162 (((%6 $3) $2) (%45 ((%56 $1) $0)))))))))))))`)
  val ADDR_IN_RANGE_OUTSIDE_2 =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%228. (%55 (\%312. (%55 (\%84. ((%137 ((%54 (%162
       (((%199 $3) $2) ((%181 ((%101 $0) %311)) %311)))) ((%182 $1) $0)))
       (%162 (((%6 $3) $2) (%45 ((%101 (%122 $1)) %311)))))))))))))`)
  val ADDR_IN_RANGE_INDUCT_1 =
    DT(["DISK_THM"], [],
       `(%55 (\%311. (%55 (\%84. (%2 (\%228. ((%137 (%162 (((%199 %18) $0)
       ((%181 $2) ((%56 $2) (%122 $1)))))) (%162 (((%199 %18) $0) ((%181
       $2) ((%56 $2) $1)))))))))))`)
  val RUN_CFL_BLK_APPEND =
    DT(["DISK_THM"], [],
       `((%54 (%0 (\%18. ((%62 ((%313 (%314 %208)) $0)) $0)))) (%0 (\%18.
       (%243 (\%315. (%243 (\%316. ((%62 ((%313 (%314 ((%227 $1) $0))) $2))
       ((%313 (%314 $0)) ((%313 (%314 $1)) $2))))))))))`)
  val push_one_lem =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%228. ((%137 (%173 $0)) ((%138 ((%62 ((%313 (%314
       (%214 $0))) $1)) ((%63 ((%63 $1) ((%267 (%45 (%57 ((%58 $1) %230))))
       ((%94 $1) $0)))) ((%267 (%95 %317)) ((%302 ((%94 $1) (%95 %317)))
       (%217 (%102 (%103 %104)))))))) (%141 (\%77. ((%62 ((%313 (%314 (%214
       $1))) $2)) ((%63 ((%63 ((%63 $2) ((%267 (%45 (%57 ((%58 $2) %230))))
       ((%94 $2) $1)))) ((%267 (%95 (%102 (%103 (%163 (%103 %104))))))
       $0))) ((%267 (%95 %317)) ((%302 ((%94 $2) (%95 %317))) (%217 (%102
       (%103 %104)))))))))))))))`)
  val PUSH_ONE_SANITY =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%238. (%318 (\%319. ((%137 ((%54 (%173 $1)) ((%176
       ((%58 $2) %230)) (%122 (%320 $0))))) ((%321 (\%322. ((%176 ((%58 $0)
       %230)) (%320 $1)))) ((%313 (%314 (%214 $1))) $2)))))))))`)
  val PUSH_LIST_SP_FP =
    DT(["DISK_THM"], [],
       `(%224 (\%235. (%0 (\%18. (%294 (\%323. ((%137 ((%176 ((%58 $1)
       %230)) (%324 $2))) ((%321 (\%325. ((%54 ((%27 (%57 ((%58 $0) %230)))
       ((%56 (%57 ((%58 $2) %230))) (%324 $3)))) ((%27 (%57 ((%58 $0)
       %59))) (%57 ((%58 $2) %59)))))) ((%313 (%314 (%221 $2)))
       $1)))))))))`)
  val PUSH_LIST_EXP_INTACT =
    DT(["DISK_THM"], [],
       `(%224 (\%235. (%0 (\%18. (%2 (\%223. (%2 (\%228. ((%137 ((%176
       ((%58 $2) %230)) (%324 $3))) ((%5 (((%6 $2) $0) $1)) (((%6 ((%313
       (%314 (%221 $3))) $2)) $0) $1)))))))))))`)
  val PUSH_LIST_SANITY =
    DT(["DISK_THM"], [],
       `(%224 (\%235. (%0 (\%18. (%294 (\%323. ((%137 ((%54 ((%237 %173)
       $2)) ((%176 ((%58 $1) %230)) (%324 $2)))) (%2 (\%228. ((%137 ((%54
       (%162 (((%199 $2) $0) ((%181 (%57 ((%58 $2) %230))) ((%56 (%57 ((%58
       $2) %230))) (%324 $3)))))) (%169 $0))) ((%35 ((%94 ((%313 (%314
       (%221 $3))) $2)) $0)) ((%94 $2) $0))))))))))))`)
  val PUSH_LIST_FUNCTIONALITY =
    DT(["DISK_THM"], [],
       `(%224 (\%235. (%0 (\%18. ((%137 ((%54 ((%237 %173) $1)) ((%176
       ((%58 $0) %230)) (%324 $1)))) (%55 (\%312. ((%137 ((%54 ((%182 $0)
       (%324 $2))) (((%229 $1) ((%326 $0) $2)) ((%56 (%327 (%324 $2)))
       $0)))) ((%35 ((%94 ((%313 (%314 (%221 $2))) $1)) (%45 ((%101 ((%56
       (%57 ((%58 $1) %230))) (%327 (%324 $2)))) $0)))) ((%94 $1) ((%326
       $0) $2)))))))))))`)
  val pop_one_lem =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%228. ((%137 (%166 $0)) ((%138 ((%62 ((%313 (%314
       (%218 $0))) $1)) ((%63 ((%63 $1) ((%267 $0) ((%94 $1) (%45 ((%101
       (%57 ((%58 $1) %230))) (%102 (%103 %104)))))))) ((%267 (%95 %317))
       ((%328 ((%94 $1) (%95 %317))) (%217 (%102 (%103 %104)))))))) (%141
       (\%77. ((%62 ((%313 (%314 (%218 $1))) $2)) ((%63 ((%63 ((%63 $2)
       ((%267 $1) ((%94 $2) (%45 ((%101 (%57 ((%58 $2) %230))) (%102 (%103
       %104)))))))) ((%267 (%95 (%102 (%103 (%163 (%103 %104)))))) $0)))
       ((%267 (%95 %317)) ((%328 ((%94 $2) (%95 %317))) (%217 (%102 (%103
       %104)))))))))))))))`)
  val grow_lt_lem_1 =
    DT(["DISK_THM"], [],
       `((%137 ((%232 %175) %84)) ((%27 (%57 ((%328 %175) (%217 %84))))
       ((%101 (%57 %175)) %84)))`)
  val grow_lt_thm =
    DT(["DISK_THM"], [],
       `((%137 ((%232 %175) (%122 %84))) ((%54 ((%232 %175) (%102 (%103
       %104)))) ((%232 %175) %84)))`)
  val LEGAL_POP_EXP_NOT_FP_SP =
    DT(["DISK_THM"], [],
       `(%2 (\%228. (%0 (\%18. (%224 (\%329. ((%137 (((%236 $1) $2) $0))
       ((%54 (%162 ((%130 $2) (%95 (%102 (%103 (%163 (%103 %104))))))))
       (%162 ((%130 $2) (%95 (%102 (%103 (%163 (%163 %104)))))))))))))))`)
  val POP_ONE_SANITY =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%228. (%2 (\%238. (%318 (\%319. ((%137 ((%54 (%171
       $2)) ((%54 (%166 $1)) ((%54 ((%232 ((%58 $3) %230)) (%122 (%320
       $0)))) (%162 (((%6 $3) $2) $1)))))) ((%321 (\%322. ((%54 ((%232
       ((%58 $0) %230)) (%320 $1))) ((%35 ((%94 $0) $3)) ((%94 $4) $3)))))
       ((%313 (%314 (%218 $1))) $3)))))))))))`)
  val POP_ONE_SANITY_2 =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%2 (\%238. (%318 (\%319. ((%137 ((%54 (%171 %228))
       ((%54 (%166 $1)) ((%232 ((%58 $2) %230)) (%122 (%320 $0)))))) ((%321
       (\%322. ((%232 ((%58 $0) %230)) (%320 $1)))) ((%313 (%314 (%218
       $1))) $2)))))))))`)
  val POP_ONE_ADDR_IN_RANGE =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%294 (\%295. (%2 (\%238. (%224 (\%235. ((%137 ((%54
       ((%237 %166) $0)) ((%54 (%166 $1)) ((%54 ((%232 ((%58 $3) %230))
       (%122 (%324 $0)))) ((%237 (\%223. (%162 (((%199 $4) $0) ((%181
       ((%101 (%57 ((%58 $4) %230))) (%122 (%324 $1)))) (%57 ((%58 $4)
       %230))))))) $0))))) ((%321 (\%325. ((%237 (\%223. (%162 (((%199 $1)
       $0) ((%181 ((%101 (%57 ((%58 $1) %230))) (%324 $2))) (%57 ((%58 $1)
       %230))))))) $1))) ((%313 (%314 (%218 $1))) $3)))))))))))`)
  val POP_LIST_SP_FP =
    DT(["DISK_THM"], [],
       `(%224 (\%235. (%0 (\%18. (%294 (\%323. ((%137 ((%54 ((%232 ((%58
       $1) %230)) (%324 $2))) ((%237 %166) $2))) ((%321 (\%325. ((%54 ((%27
       (%57 ((%58 $0) %230))) ((%101 (%57 ((%58 $2) %230))) (%324 $3))))
       ((%27 (%57 ((%58 $0) %59))) (%57 ((%58 $2) %59)))))) ((%313 (%314
       (%231 $2))) $1)))))))))`)
  val POP_ONE_EXP_LEM_1 =
    DT(["DISK_THM"], [],
       `(%2 (\%238. (%0 (\%18. (%55 (\%312. ((%137 ((%54 ((%232 ((%58 $1)
       %230)) (%102 (%103 %104)))) ((%54 (%166 $2)) (%162 (((%6 $1) $2)
       (%45 ((%101 (%122 $0)) (%57 ((%58 $1) %230))))))))) ((%321 (\%325.
       ((%35 ((%94 $2) (%45 ((%101 (%122 $1)) (%57 ((%58 $2) %230))))))
       ((%94 $0) (%45 ((%101 $1) (%57 ((%58 $0) %230)))))))) ((%313 (%314
       (%218 $2))) $1)))))))))`)
  val POP_LIST_EXP_INTACT =
    DT(["DISK_THM"], [],
       `(%224 (\%235. (%0 (\%18. (%2 (\%223. (%2 (\%228. ((%137 ((%54
       ((%232 ((%58 $2) %230)) (%324 $3))) ((%237 %166) $3))) ((%5 (((%6
       $2) $0) $1)) (((%6 ((%313 (%314 (%231 $3))) $2)) $0) $1)))))))))))`)
  val POP_ONE_EXP_INTACT =
    DT(["DISK_THM"], [],
       `(%224 (\%235. (%0 (\%18. (%2 (\%228. (%2 (\%238. ((%137 ((%54
       ((%232 ((%58 $2) %230)) (%102 (%103 %104)))) ((%54 (%166 $0)) ((%237
       (\%223. (%162 (((%6 $3) $2) $0)))) $3)))) ((%237 (\%223. (%162 (((%6
       ((%313 (%314 (%218 $1))) $3)) $2) $0)))) $3))))))))))`)
  val unique_exp_list_lem_1 =
    DT(["DISK_THM"], [],
       `(%55 (\%312. (%2 (\%238. (%224 (\%235. ((%137 ((%54 ((%182 $2)
       (%324 $0))) ((%237 (\%223. (%162 (((%6 %18) $2) $0)))) $0))) (%162
       (((%6 %18) ((%326 $2) $0)) $1)))))))))`)
  val unique_exp_list_lem_2 =
    DT(["DISK_THM"], [],
       `((%137 ((%54 ((%239 %18) %235)) ((%54 ((%237 %166) %235)) ((%54
       (%166 %238)) ((%232 ((%58 %18) %230)) (%102 (%103 %104))))))) ((%239
       ((%313 (%314 (%218 %238))) %18)) %235))`)
  val POP_LIST_SANITY =
    DT(["DISK_THM"], [],
       `(%224 (\%235. (%0 (\%18. (%294 (\%323. ((%137 ((%54 ((%237 %166)
       $2)) ((%232 ((%58 $1) %230)) (%324 $2)))) (%2 (\%228. ((%137 ((%54
       ((%237 (\%223. (%162 (((%6 $3) $1) $0)))) $3)) (%171 $0))) ((%35
       ((%94 ((%313 (%314 (%231 $3))) $2)) $0)) ((%94 $2) $0))))))))))))`)
  val POP_LIST_FUNCTIONALITY =
    DT(["DISK_THM"], [],
       `(%224 (\%235. (%0 (\%18. ((%137 ((%54 ((%237 %166) $1)) ((%54
       ((%232 ((%58 $0) %230)) (%324 $1))) ((%54 ((%239 $0) $1)) ((%237
       (\%223. (%162 (((%199 $1) $0) ((%181 ((%101 (%57 ((%58 $1) %230)))
       (%324 $2))) (%57 ((%58 $1) %230))))))) $1))))) (%55 (\%312. ((%137
       ((%54 ((%182 $0) (%324 $2))) ((%54 (%162 (%146 ((%326 $0) $2))))
       (%166 ((%326 $0) $2))))) ((%35 ((%94 ((%313 (%314 (%231 $2))) $1))
       ((%326 $0) $2))) ((%94 $1) (%45 ((%101 (%57 ((%58 $1) %230))) (%122
       $0)))))))))))))`)
  val LOCATE_GE_GROW_LT =
    DT(["DISK_THM"], [],
       `((%137 ((%54 ((%176 %175) %84)) ((%27 (%57 %330)) ((%56 (%57 %175))
       %84)))) ((%232 %330) %84))`)
  val LEGAL_PUSH_EXP_DSTATE =
    DT(["DISK_THM"], [],
       `((%137 ((%54 (((%236 %18) %228) %235)) ((%27 (%57 ((%58 %18) %59)))
       (%57 ((%58 %325) %59))))) (((%236 %325) %228) %235))`)
  val PUSH_LIST_ADDR_IN_RANGE =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%224 (\%331. (%224 (\%332. ((%137 ((%54 ((%237 %166)
       $1)) ((%54 ((%176 ((%58 $2) %230)) (%324 $1))) ((%237 (\%223. (%162
       (((%199 $3) $0) ((%181 (%57 ((%58 $3) %230))) ((%56 (%57 ((%58 $3)
       %230))) (%324 $2))))))) $0)))) ((%321 (\%325. ((%237 (\%223. (%162
       (((%199 $1) $0) ((%181 ((%101 (%57 ((%58 $1) %230))) (%324 $3)))
       (%57 ((%58 $1) %230))))))) $1))) ((%313 (%314 (%221 $1)))
       $2)))))))))`)
  val UNIEQUE_LIST_THM =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%0 (\%325. ((%137 ((%54 ((%35 ((%58 $1) %59)) ((%58 $0)
       %59))) ((%239 $1) %235))) ((%239 $0) %235))))))`)
  val ADDR_IN_RANGE_LEGAL_EXP =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%224 (\%235. ((%137 ((%54 ((%237 %166) $0)) ((%54
       ((%237 ((%333 %162) %146)) $0)) ((%54 ((%176 ((%58 $1) %230)) (%324
       $0))) ((%237 (\%223. (%162 (((%199 $2) $0) ((%181 (%57 ((%58 $2)
       %230))) ((%56 (%57 ((%58 $2) %230))) (%324 $1))))))) $0))))) (%55
       (\%312. ((%137 ((%182 $0) (%324 $1))) (((%229 $2) ((%326 $0) $1))
       ((%56 (%327 (%324 $1))) $0))))))))))`)
  val COPY_LIST_SANITY =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%224 (\%240. (%224 (\%241. ((%137 ((%54 ((%237 %166)
       $1)) ((%54 ((%237 %166) $0)) ((%54 ((%27 (%324 $0)) (%324 $1)))
       ((%176 ((%58 $2) %230)) (%324 $0)))))) (%2 (\%228. ((%137 ((%54
       (((%229 $3) $0) (%324 $2))) (((%236 $3) $0) $2))) ((%35 ((%94 ((%313
       (%314 ((%242 $2) $1))) $3)) $0)) ((%94 $3) $0))))))))))))`)
  val COPY_LIST_FUNCTIONALITY =
    DT(["DISK_THM"], [],
       `(%0 (\%18. (%224 (\%240. (%224 (\%241. ((%137 ((%54 ((%237 %166)
       $0)) ((%54 ((%237 ((%333 %162) %146)) $0)) ((%54 ((%237 ((%333 %162)
       %146)) $1)) ((%54 ((%237 %166) $1)) ((%54 ((%176 ((%58 $2) %230))
       (%324 $0))) ((%54 ((%239 $2) $1)) ((%54 ((%237 (\%223. (%162 (((%199
       $3) $0) ((%181 (%57 ((%58 $3) %230))) ((%56 (%57 ((%58 $3) %230)))
       (%324 $1))))))) $0)) ((%54 ((%237 (\%223. (%162 (((%199 $3) $0)
       ((%181 (%57 ((%58 $3) %230))) ((%56 (%57 ((%58 $3) %230))) (%324
       $2))))))) $1)) ((%27 (%324 $1)) (%324 $0))))))))))) (%55 (\%312.
       ((%137 ((%182 $0) (%324 $2))) ((%35 ((%94 ((%313 (%314 ((%242 $2)
       $1))) $3)) ((%326 $0) $2))) ((%94 $3) ((%326 $0) $1)))))))))))))`)
  end
  val _ = DB.bindl "bigInst"
  [("eq_exp_curried_def",eq_exp_curried_def,DB.Def),
   ("eq_exp_tupled_primitive_def",eq_exp_tupled_primitive_def,DB.Def),
   ("eq_addr_def",eq_addr_def,DB.Def), ("addr_of_def",addr_of_def,DB.Def),
   ("writee_curried_def",writee_curried_def,DB.Def),
   ("writee_tupled_primitive_def",writee_tupled_primitive_def,DB.Def),
   ("reade_def",reade_def,DB.Def),
   ("CFL_EXP_size_def",CFL_EXP_size_def,DB.Def),
   ("CFL_EXP_case_def",CFL_EXP_case_def,DB.Def), ("isM",isM,DB.Def),
   ("isV",isV,DB.Def), ("isC",isC,DB.Def), ("isR",isR,DB.Def),
   ("bigInst3_def",bigInst3_def,DB.Def),
   ("bigInst2_def",bigInst2_def,DB.Def),
   ("bigInst1_def",bigInst1_def,DB.Def),
   ("bigInst0_def",bigInst0_def,DB.Def),
   ("CFL_EXP_repfns",CFL_EXP_repfns,DB.Def),
   ("CFL_EXP_TY_DEF",CFL_EXP_TY_DEF,DB.Def),
   ("is_C_primitive_def",is_C_primitive_def,DB.Def),
   ("valid_regs_primitive_def",valid_regs_primitive_def,DB.Def),
   ("valid_exp_primitive_def",valid_exp_primitive_def,DB.Def),
   ("valid_exp_1_primitive_def",valid_exp_1_primitive_def,DB.Def),
   ("valid_exp_2_primitive_def",valid_exp_2_primitive_def,DB.Def),
   ("valid_exp_3_primitive_def",valid_exp_3_primitive_def,DB.Def),
   ("locate_ge_def",locate_ge_def,DB.Def),
   ("in_range_def",in_range_def,DB.Def),
   ("addr_in_range_tupled_primitive_def",
    addr_in_range_tupled_primitive_def,
    DB.Def),
   ("addr_in_range_curried_def",addr_in_range_curried_def,DB.Def),
   ("store_one_def",store_one_def,DB.Def),
   ("load_one_def",load_one_def,DB.Def),
   ("push_one_def",push_one_def,DB.Def),
   ("pop_one_def",pop_one_def,DB.Def),
   ("push_list_def",push_list_def,DB.Def),
   ("legal_push_exp_def",legal_push_exp_def,DB.Def),
   ("pop_list_def",pop_list_def,DB.Def),
   ("grow_lt_def",grow_lt_def,DB.Def),
   ("legal_pop_exp_def",legal_pop_exp_def,DB.Def),
   ("unique_exp_list_def",unique_exp_list_def,DB.Def),
   ("copy_list_def",copy_list_def,DB.Def),
   ("sr_list_def",sr_list_def,DB.Def), ("eq_exp_ind",eq_exp_ind,DB.Thm),
   ("writee_def",writee_def,DB.Thm), ("writee_ind",writee_ind,DB.Thm),
   ("CFL_EXP_induction",CFL_EXP_induction,DB.Thm),
   ("CFL_EXP_Axiom",CFL_EXP_Axiom,DB.Thm),
   ("CFL_EXP_nchotomy",CFL_EXP_nchotomy,DB.Thm),
   ("CFL_EXP_case_cong",CFL_EXP_case_cong,DB.Thm),
   ("CFL_EXP_distinct",CFL_EXP_distinct,DB.Thm),
   ("CFL_EXP_11",CFL_EXP_11,DB.Thm),
   ("datatype_CFL_EXP",datatype_CFL_EXP,DB.Thm),
   ("eq_exp_def",eq_exp_def,DB.Thm), ("is_C_ind",is_C_ind,DB.Thm),
   ("is_C_def",is_C_def,DB.Thm), ("eq_exp_SYM",eq_exp_SYM,DB.Thm),
   ("NOT_EQ_isR_LEM",NOT_EQ_isR_LEM,DB.Thm),
   ("valid_regs_ind",valid_regs_ind,DB.Thm),
   ("valid_regs_def",valid_regs_def,DB.Thm),
   ("valid_regs_lem",valid_regs_lem,DB.Thm),
   ("valid_exp_ind",valid_exp_ind,DB.Thm),
   ("valid_exp_def",valid_exp_def,DB.Thm),
   ("valid_exp_1_ind",valid_exp_1_ind,DB.Thm),
   ("valid_exp_1_def",valid_exp_1_def,DB.Thm),
   ("valid_exp_2_ind",valid_exp_2_ind,DB.Thm),
   ("valid_exp_2_def",valid_exp_2_def,DB.Thm),
   ("valid_exp_3_ind",valid_exp_3_ind,DB.Thm),
   ("valid_exp_3_def",valid_exp_3_def,DB.Thm),
   ("valid_exp_thm",valid_exp_thm,DB.Thm),
   ("VALID_EXP_LEM",VALID_EXP_LEM,DB.Thm),
   ("READE_WRITEE",READE_WRITEE,DB.Thm),
   ("READE_WRITEE_THM",READE_WRITEE_THM,DB.Thm),
   ("READE_WRITEE_THM_2",READE_WRITEE_THM_2,DB.Thm),
   ("WRITEE_EQ",WRITEE_EQ,DB.Thm),
   ("WRITEE_COMMUTES",WRITEE_COMMUTES,DB.Thm),
   ("w2n_sub_lem",w2n_sub_lem,DB.Thm),
   ("locate_ge_lem_1",locate_ge_lem_1,DB.Thm),
   ("locate_ge_lem_2",locate_ge_lem_2,DB.Thm),
   ("locate_ge_thm",locate_ge_thm,DB.Thm),
   ("addr_in_range_ind",addr_in_range_ind,DB.Thm),
   ("addr_in_range_def",addr_in_range_def,DB.Thm),
   ("ADDR_IN_RANGE_OUTSIDE",ADDR_IN_RANGE_OUTSIDE,DB.Thm),
   ("ADDR_IN_RANGE_OUTSIDE_2",ADDR_IN_RANGE_OUTSIDE_2,DB.Thm),
   ("ADDR_IN_RANGE_INDUCT_1",ADDR_IN_RANGE_INDUCT_1,DB.Thm),
   ("RUN_CFL_BLK_APPEND",RUN_CFL_BLK_APPEND,DB.Thm),
   ("push_one_lem",push_one_lem,DB.Thm),
   ("PUSH_ONE_SANITY",PUSH_ONE_SANITY,DB.Thm),
   ("PUSH_LIST_SP_FP",PUSH_LIST_SP_FP,DB.Thm),
   ("PUSH_LIST_EXP_INTACT",PUSH_LIST_EXP_INTACT,DB.Thm),
   ("PUSH_LIST_SANITY",PUSH_LIST_SANITY,DB.Thm),
   ("PUSH_LIST_FUNCTIONALITY",PUSH_LIST_FUNCTIONALITY,DB.Thm),
   ("pop_one_lem",pop_one_lem,DB.Thm),
   ("grow_lt_lem_1",grow_lt_lem_1,DB.Thm),
   ("grow_lt_thm",grow_lt_thm,DB.Thm),
   ("LEGAL_POP_EXP_NOT_FP_SP",LEGAL_POP_EXP_NOT_FP_SP,DB.Thm),
   ("POP_ONE_SANITY",POP_ONE_SANITY,DB.Thm),
   ("POP_ONE_SANITY_2",POP_ONE_SANITY_2,DB.Thm),
   ("POP_ONE_ADDR_IN_RANGE",POP_ONE_ADDR_IN_RANGE,DB.Thm),
   ("POP_LIST_SP_FP",POP_LIST_SP_FP,DB.Thm),
   ("POP_ONE_EXP_LEM_1",POP_ONE_EXP_LEM_1,DB.Thm),
   ("POP_LIST_EXP_INTACT",POP_LIST_EXP_INTACT,DB.Thm),
   ("POP_ONE_EXP_INTACT",POP_ONE_EXP_INTACT,DB.Thm),
   ("unique_exp_list_lem_1",unique_exp_list_lem_1,DB.Thm),
   ("unique_exp_list_lem_2",unique_exp_list_lem_2,DB.Thm),
   ("POP_LIST_SANITY",POP_LIST_SANITY,DB.Thm),
   ("POP_LIST_FUNCTIONALITY",POP_LIST_FUNCTIONALITY,DB.Thm),
   ("LOCATE_GE_GROW_LT",LOCATE_GE_GROW_LT,DB.Thm),
   ("LEGAL_PUSH_EXP_DSTATE",LEGAL_PUSH_EXP_DSTATE,DB.Thm),
   ("PUSH_LIST_ADDR_IN_RANGE",PUSH_LIST_ADDR_IN_RANGE,DB.Thm),
   ("UNIEQUE_LIST_THM",UNIEQUE_LIST_THM,DB.Thm),
   ("ADDR_IN_RANGE_LEGAL_EXP",ADDR_IN_RANGE_LEGAL_EXP,DB.Thm),
   ("COPY_LIST_SANITY",COPY_LIST_SANITY,DB.Thm),
   ("COPY_LIST_FUNCTIONALITY",COPY_LIST_FUNCTIONALITY,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("CFLTheory.CFL_grammars",CFLTheory.CFL_grammars),
                         ("simplifierTheory.simplifier_grammars",
                          simplifierTheory.simplifier_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms temp_add_type "CFL_EXP"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_CFL_EXP")
        {Name = "dest_CFL_EXP", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_CFL_EXP")
        {Name = "mk_CFL_EXP", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "bigInst0")
        {Name = "bigInst0", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "bigInst1")
        {Name = "bigInst1", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "bigInst2")
        {Name = "bigInst2", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "bigInst3")
        {Name = "bigInst3", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "isR")
        {Name = "isR", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "isC")
        {Name = "isC", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "isV")
        {Name = "isV", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "isM")
        {Name = "isM", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_EXP_case")
        {Name = "CFL_EXP_case", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL_EXP_size")
        {Name = "CFL_EXP_size", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "reade")
        {Name = "reade", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "writee_tupled")
        {Name = "writee_tupled", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "writee")
        {Name = "writee", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "''")
        {Name = "reade", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "|#")
        {Name = "writee", Thy = "bigInst"}
  val _ = update_grms (temp_set_fixity "''") (Infix(HOLgrammars.LEFT, 500))
  val _ = update_grms (temp_set_fixity "|#") (Infix(HOLgrammars.LEFT, 600))
  val _ = update_grms
       (temp_overload_on_by_nametype "addr_of")
        {Name = "addr_of", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eq_addr")
        {Name = "eq_addr", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eq_exp_tupled")
        {Name = "eq_exp_tupled", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eq_exp")
        {Name = "eq_exp", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eq_exp_tupled")
        {Name = "eq_exp_tupled", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eq_exp")
        {Name = "eq_exp", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "is_C")
        {Name = "is_C", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_regs")
        {Name = "valid_regs", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_exp")
        {Name = "valid_exp", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_exp_1")
        {Name = "valid_exp_1", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_exp_2")
        {Name = "valid_exp_2", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_exp_3")
        {Name = "valid_exp_3", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "locate_ge")
        {Name = "locate_ge", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "in_range")
        {Name = "in_range", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "addr_in_range_tupled")
        {Name = "addr_in_range_tupled", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "addr_in_range")
        {Name = "addr_in_range", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "store_one")
        {Name = "store_one", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "load_one")
        {Name = "load_one", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "push_one")
        {Name = "push_one", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "pop_one")
        {Name = "pop_one", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "push_list")
        {Name = "push_list", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "legal_push_exp")
        {Name = "legal_push_exp", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "pop_list")
        {Name = "pop_list", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "grow_lt")
        {Name = "grow_lt", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "legal_pop_exp")
        {Name = "legal_pop_exp", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "unique_exp_list")
        {Name = "unique_exp_list", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "copy_list")
        {Name = "copy_list", Thy = "bigInst"}
  val _ = update_grms
       (temp_overload_on_by_nametype "sr_list")
        {Name = "sr_list", Thy = "bigInst"}
  val bigInst_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG CFL_EXP_Axiom,
           case_def=CFL_EXP_case_def,
           case_cong=CFL_EXP_case_cong,
           induction=ORIG CFL_EXP_induction,
           nchotomy=CFL_EXP_nchotomy,
           size=SOME(Parse.Term`(bigInst$CFL_EXP_size) :(bigInst$CFL_EXP) -> (num$num)`,
                     ORIG CFL_EXP_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME CFL_EXP_11,
           distinct=SOME CFL_EXP_distinct,
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
  
  
  val _ = computeLib.add_funs [reade_def];  
  
  val _ = computeLib.add_funs [writee_def];  
  
  val _ = computeLib.add_funs [addr_of_def];  
  
  val _ = computeLib.add_funs [eq_addr_def];  
  
  val _ = computeLib.add_funs [eq_exp_def];  
  
  val _ = computeLib.add_funs [eq_exp_def];  
  
  val _ = computeLib.add_funs [is_C_def];  
  
  val _ = computeLib.add_funs [valid_regs_def];  
  
  val _ = computeLib.add_funs [valid_exp_def];  
  
  val _ = computeLib.add_funs [valid_exp_1_def];  
  
  val _ = computeLib.add_funs [valid_exp_2_def];  
  
  val _ = computeLib.add_funs [valid_exp_3_def];  
  
  val _ = computeLib.add_funs [locate_ge_def];  
  
  val _ = computeLib.add_funs [in_range_def];  
  
  val _ = computeLib.add_funs [addr_in_range_def];  
  
  val _ = computeLib.add_funs [store_one_def];  
  
  val _ = computeLib.add_funs [load_one_def];  
  
  val _ = computeLib.add_funs [push_one_def];  
  
  val _ = computeLib.add_funs [pop_one_def];  
  
  val _ = computeLib.add_funs [push_list_def];  
  
  val _ = computeLib.add_funs [legal_push_exp_def];  
  
  val _ = computeLib.add_funs [pop_list_def];  
  
  val _ = computeLib.add_funs [grow_lt_def];  
  
  val _ = computeLib.add_funs [legal_pop_exp_def];  
  
  val _ = computeLib.add_funs [unique_exp_list_def];  
  
  val _ = computeLib.add_funs [copy_list_def];  
  
  val _ = computeLib.add_funs [sr_list_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
