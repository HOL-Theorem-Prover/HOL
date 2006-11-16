structure HSLTheory :> HSLTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading HSLTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open ACFTheory CFLTheory
  in end;
  val _ = Theory.link_parents
          ("HSL",Arbnum.fromString "1163548760",Arbnum.fromString "851649")
          [("CFL",
           Arbnum.fromString "1163238460",
           Arbnum.fromString "586624"),
           ("ACF",
           Arbnum.fromString "1162972712",
           Arbnum.fromString "509220")];
  val _ = Theory.incorporate_types "HSL"
       [("HSL_STRUCTURE",0), ("TROC",0), ("TOPER",0), ("TREG",0),
        ("PTR",0), ("TEXP",0)];
  val _ = Theory.incorporate_consts "HSL"
     [("TOPER_case",
       (((T"TREG" "HSL" [] --> (T"num" "num" [] --> alpha)) -->
         ((T"num" "num" [] --> (T"TREG" "HSL" [] --> alpha)) -->
          ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)) -->
           ((T"TREG" "HSL" [] -->
             (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
            ((T"TREG" "HSL" [] -->
              (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
             ((T"TREG" "HSL" [] -->
               (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
              ((T"TREG" "HSL" [] -->
                (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
               ((T"TREG" "HSL" [] -->
                 (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
                ((T"TREG" "HSL" [] -->
                  (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
                 ((T"TREG" "HSL" [] -->
                   (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
                  ((T"TREG" "HSL" [] -->
                    (T"TROC" "HSL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                   -->
                   ((T"TREG" "HSL" [] -->
                     (T"TROC" "HSL" [] -->
                      (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                    -->
                    ((T"TREG" "HSL" [] -->
                      (T"TROC" "HSL" [] -->
                       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                     -->
                     ((T"TREG" "HSL" [] -->
                       (T"TROC" "HSL" [] -->
                        (T"cart" "fcp" [bool, T"i5" "words" []] -->
                         alpha))) -->
                      (T"TOPER" "HSL" [] --> alpha))))))))))))))))),
      ("dest_TOPER",
       ((T"TOPER" "HSL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"TROC" "HSL" [],
                 T"prod" "pair"
                  [T"TROC" "HSL" [],
                   T"cart" "fcp" [bool, T"i5" "words" []]]]]]]))),
      ("twrite_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
             T"fmap" "finite_map" [T"num" "num" [], alpha]],
           T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
         T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]]))),
      ("dest_TEXP",
       ((T"TEXP" "HSL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []],
               T"num" "num" []]]]))), ("TTP",(T"PTR" "HSL" [])),
      ("TSP",(T"PTR" "HSL" [])),
      ("transfer",
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
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         -->
         (T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]] -->
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]])))),
      ("TLR",(T"PTR" "HSL" [])),
      ("mk_TROC",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
         --> T"TROC" "HSL" []))), ("TIP",(T"PTR" "HSL" [])),
      ("THP",(T"PTR" "HSL" [])), ("TFP",(T"PTR" "HSL" [])),
      ("Blk",
       ((T"list" "list" [T"TOPER" "HSL" []] -->
         T"HSL_STRUCTURE" "HSL" []))),
      ("PTR_size",((T"PTR" "HSL" [] --> T"num" "num" []))),
      ("valid_assgn_tupled",
       ((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool))),
      ("mk_TEXP",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]]
         --> T"TEXP" "HSL" []))),
      ("run_hsl_tupled",
       ((T"prod" "pair"
          [T"HSL_STRUCTURE" "HSL" [],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
      ("run_hsl",
       ((T"HSL_STRUCTURE" "HSL" [] -->
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          -->
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]])))),
      ("num2PTR",((T"num" "num" [] --> T"PTR" "HSL" []))),
      ("TREG_size",((T"TREG" "HSL" [] --> T"num" "num" []))),
      ("TREG2num",((T"TREG" "HSL" [] --> T"num" "num" []))),
      ("TEXP_size",((T"TEXP" "HSL" [] --> T"num" "num" []))),
      ("notC",((T"TEXP" "HSL" [] --> bool))),
      ("HSL_STRUCTURE_case",
       (((T"list" "list" [T"TOPER" "HSL" []] --> alpha) -->
         ((T"HSL_STRUCTURE" "HSL" [] -->
           (T"HSL_STRUCTURE" "HSL" [] --> alpha)) -->
          ((T"prod" "pair"
             [T"TREG" "HSL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
            (T"HSL_STRUCTURE" "HSL" [] -->
             (T"HSL_STRUCTURE" "HSL" [] --> alpha))) -->
           ((T"prod" "pair"
              [T"TREG" "HSL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
             (T"HSL_STRUCTURE" "HSL" [] --> alpha)) -->
            ((T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]] -->
              (T"HSL_STRUCTURE" "HSL" [] -->
               (T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]] --> alpha))) -->
             (T"HSL_STRUCTURE" "HSL" [] --> alpha)))))))),
      ("HSL19",
       ((T"list" "list" [T"TOPER" "HSL" []] -->
         T"HSL_STRUCTURE" "HSL" []))),
      ("HSL18",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"TOPER" "HSL" []))))),
      ("HSL23",
       ((T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] -->
          (T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]] -->
           T"HSL_STRUCTURE" "HSL" []))))),
      ("HSL17",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"TOPER" "HSL" []))))),
      ("run_hsl_tupled_aux",
       (((T"prod" "pair"
           [T"HSL_STRUCTURE" "HSL" [],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
          -->
          (T"prod" "pair"
            [T"HSL_STRUCTURE" "HSL" [],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]] --> bool)) -->
         (T"prod" "pair"
           [T"HSL_STRUCTURE" "HSL" [],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
          -->
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]])))),
      ("HSL22",
       ((T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])))),
      ("HSL16",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"TOPER" "HSL" []))))),
      ("HSL21",
       ((T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] -->
          (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))))),
      ("HSL15",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"TOPER" "HSL" []))))),
      ("HSL20",
       ((T"HSL_STRUCTURE" "HSL" [] -->
         (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])))),
      ("HSL14",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("HSL13",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("HSL12",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("HSL11",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("HSL10",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("valid_arg_list",
       ((T"prod" "pair"
          [T"list" "list" [alpha],
           T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []], T"list" "list" [beta]]]]
         --> bool))),
      ("transfer_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]],
           T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]]] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
      ("TOPER_size",((T"TOPER" "HSL" [] --> T"num" "num" []))),
      ("TSTR",
       ((T"num" "num" [] --> (T"TREG" "HSL" [] --> T"TOPER" "HSL" [])))),
      ("tread",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"TEXP" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []])))),
      ("TSUB",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("TROC_case",
       (((T"TREG" "HSL" [] --> alpha) -->
         ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
          (T"TROC" "HSL" [] --> alpha))))),
      ("TROR",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"TOPER" "HSL" []))))),
      ("TRSB",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("data_reg_index",((T"TREG" "HSL" [] --> T"num" "num" []))),
      ("TORR",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("conv_reg",((T"TREG" "HSL" [] --> T"MREG" "CFL" []))),
      ("TMUL",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("TMOV",
       ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
      ("TLSR",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"TOPER" "HSL" []))))),
      ("TLSL",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"TOPER" "HSL" []))))),
      ("valid_TEXP",((T"TEXP" "HSL" [] --> (T"num" "num" [] --> bool)))),
      ("TLDR",
       ((T"TREG" "HSL" [] --> (T"num" "num" [] --> T"TOPER" "HSL" [])))),
      ("data_reg_name",((T"num" "num" [] --> T"TREG" "HSL" []))),
      ("TEOR",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("twrite",
       ((T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]] -->
         (T"TEXP" "HSL" [] -->
          (alpha -->
           T"prod" "pair"
            [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
             T"fmap" "finite_map" [T"num" "num" [], alpha]]))))),
      ("valid_assgn",((T"TOPER" "HSL" [] --> (T"num" "num" [] --> bool)))),
      ("TASR",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"TOPER" "HSL" []))))),
      ("tread_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"TEXP" "HSL" []] -->
         T"cart" "fcp" [bool, T"i32" "words" []]))),
      ("TAND",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("mk_TOPER",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"TROC" "HSL" [],
                 T"prod" "pair"
                  [T"TROC" "HSL" [],
                   T"cart" "fcp" [bool, T"i5" "words" []]]]]]] -->
         T"TOPER" "HSL" []))),
      ("TADD",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("unique_list",((T"list" "list" [alpha] --> bool))),
      ("toPTR",((T"PTR" "HSL" [] --> T"num" "num" []))),
      ("r8",(T"TREG" "HSL" [])), ("r7",(T"TREG" "HSL" [])),
      ("r6",(T"TREG" "HSL" [])),
      ("roc_2_exp",((T"TROC" "HSL" [] --> T"TEXP" "HSL" []))),
      ("r5",(T"TREG" "HSL" [])), ("r4",(T"TREG" "HSL" [])),
      ("r3",(T"TREG" "HSL" [])), ("r2",(T"TREG" "HSL" [])),
      ("r1",(T"TREG" "HSL" [])), ("r0",(T"TREG" "HSL" [])),
      ("match",
       (((T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha) -->
         (T"list" "list" [T"TEXP" "HSL" []] -->
          ((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
            alpha) --> bool))))),
      ("dest_HSL_STRUCTURE",
       ((T"HSL_STRUCTURE" "HSL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"TOPER" "HSL" []],
             T"prod" "pair"
              [T"prod" "pair"
                [T"TREG" "HSL" [],
                 T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
               T"prod" "pair"
                [T"prod" "pair"
                  [T"list" "list" [T"TEXP" "HSL" []],
                   T"list" "list" [T"TEXP" "HSL" []]],
                 T"prod" "pair"
                  [T"list" "list" [T"TEXP" "HSL" []],
                   T"list" "list" [T"TEXP" "HSL" []]]]]]]))),
      ("HSL_STRUCTURE_size",
       ((T"HSL_STRUCTURE" "HSL" [] --> T"num" "num" []))),
      ("Tr",
       ((T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])))),
      ("PTR2num",((T"PTR" "HSL" [] --> T"num" "num" []))),
      ("Sc",
       ((T"HSL_STRUCTURE" "HSL" [] -->
         (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])))),
      ("Rg",((T"TREG" "HSL" [] --> T"TROC" "HSL" []))),
      ("PTR_case",
       ((alpha -->
         (alpha -->
          (alpha -->
           (alpha -->
            (alpha --> (alpha --> (T"PTR" "HSL" [] --> alpha))))))))),
      ("within_bound",((T"num" "num" [] --> (T"num" "num" [] --> bool)))),
      ("valid_struct",
       ((T"HSL_STRUCTURE" "HSL" [] --> (T"num" "num" [] --> bool)))),
      ("Fc",
       ((T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] -->
          (T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]] -->
           T"HSL_STRUCTURE" "HSL" []))))),
      ("Cn",
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TROC" "HSL" []))),
      ("Cj",
       ((T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] -->
          (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))))),
      ("eval_TCND_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool))),
      ("tdecode",
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
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]])))),
      ("HSL9",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("HSL8",
       ((T"TREG" "HSL" [] -->
         (T"TROC" "HSL" [] -->
          (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))))),
      ("HSL7",
       ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
      ("HSL6",
       ((T"num" "num" [] --> (T"TREG" "HSL" [] --> T"TOPER" "HSL" [])))),
      ("HSL5",
       ((T"TREG" "HSL" [] --> (T"num" "num" [] --> T"TOPER" "HSL" [])))),
      ("HSL4",
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TROC" "HSL" []))),
      ("HSL3",((T"TREG" "HSL" [] --> T"TROC" "HSL" []))),
      ("HSL2",((T"num" "num" [] --> T"TEXP" "HSL" []))),
      ("TROC_size",((T"TROC" "HSL" [] --> T"num" "num" []))),
      ("HSL1",
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TEXP" "HSL" []))),
      ("HSL0",((T"TREG" "HSL" [] --> T"TEXP" "HSL" []))),
      ("TREG_case",
       ((alpha -->
         (alpha -->
          (alpha -->
           (alpha -->
            (alpha -->
             (alpha -->
              (alpha -->
               (alpha -->
                (alpha --> (T"TREG" "HSL" [] --> alpha)))))))))))),
      ("TEXP_case",
       (((T"TREG" "HSL" [] --> alpha) -->
         ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
          ((T"num" "num" [] --> alpha) -->
           (T"TEXP" "HSL" [] --> alpha)))))),
      ("mk_HSL_STRUCTURE",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"TOPER" "HSL" []],
             T"prod" "pair"
              [T"prod" "pair"
                [T"TREG" "HSL" [],
                 T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
               T"prod" "pair"
                [T"prod" "pair"
                  [T"list" "list" [T"TEXP" "HSL" []],
                   T"list" "list" [T"TEXP" "HSL" []]],
                 T"prod" "pair"
                  [T"list" "list" [T"TEXP" "HSL" []],
                   T"list" "list" [T"TEXP" "HSL" []]]]]]] -->
         T"HSL_STRUCTURE" "HSL" []))),
      ("inR",((T"TREG" "HSL" [] --> T"TEXP" "HSL" []))),
      ("inE",((T"num" "num" [] --> T"TEXP" "HSL" []))),
      ("inC",
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TEXP" "HSL" []))),
      ("num2TREG",((T"num" "num" [] --> T"TREG" "HSL" []))),
      ("empty_s",
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
      ("CSPEC",
       ((T"HSL_STRUCTURE" "HSL" [] -->
         (T"prod" "pair"
           [(T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
             --> alpha),
            T"prod" "pair"
             [(alpha --> beta),
              (T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"TREG" "HSL" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]] --> beta)]]
          --> bool)))),
      ("from_MEXP",((T"MEXP" "CFL" [] --> T"TEXP" "HSL" []))),
      ("eval_TCND",
       ((T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)))),
      ("dest_TROC",
       ((T"TROC" "HSL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]])))];
  
  local
  val share_table = Vector.fromList
  [C"?" "bool"
    ((((T"PTR" "HSL" [] --> T"num" "num" []) --> bool) --> bool)),
   V"rep" ((T"PTR" "HSL" [] --> T"num" "num" [])),
   C"TYPE_DEFINITION" "bool"
    (((T"num" "num" [] --> bool) -->
      ((T"PTR" "HSL" [] --> T"num" "num" []) --> bool))),
   V"n" (T"num" "num" []),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"PTR" "HSL" [] --> bool) --> bool)),
   V"a" (T"PTR" "HSL" []),
   C"=" "min" ((T"PTR" "HSL" [] --> (T"PTR" "HSL" [] --> bool))),
   C"num2PTR" "HSL" ((T"num" "num" [] --> T"PTR" "HSL" [])),
   C"PTR2num" "HSL" ((T"PTR" "HSL" [] --> T"num" "num" [])),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"r" (T"num" "num" []), C"=" "min" ((bool --> (bool --> bool))),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"TTP" "HSL" (T"PTR" "HSL" []), C"0" "num" (T"num" "num" []),
   C"THP" "HSL" (T"PTR" "HSL" []),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"TFP" "HSL" (T"PTR" "HSL" []), C"TIP" "HSL" (T"PTR" "HSL" []),
   C"TSP" "HSL" (T"PTR" "HSL" []), C"TLR" "HSL" (T"PTR" "HSL" []),
   V"x" (T"PTR" "HSL" []),
   C"PTR_size" "HSL" ((T"PTR" "HSL" [] --> T"num" "num" [])),
   C"!" "bool" (((alpha --> bool) --> bool)), V"v0" (alpha), V"v1" (alpha),
   V"v2" (alpha), V"v3" (alpha), V"v4" (alpha), V"v5" (alpha),
   C"=" "min" ((alpha --> (alpha --> bool))),
   C"PTR_case" "HSL"
    ((alpha -->
      (alpha -->
       (alpha -->
        (alpha -->
         (alpha --> (alpha --> (T"PTR" "HSL" [] --> alpha)))))))),
   V"m" (T"num" "num" []),
   C"COND" "bool" ((bool --> (alpha --> (alpha --> alpha)))),
   C"toPTR" "HSL" ((T"PTR" "HSL" [] --> T"num" "num" [])),
   C"tp" "CFL" (T"num" "num" []), C"gp" "CFL" (T"num" "num" []),
   C"fp" "CFL" (T"num" "num" []), C"ip" "CFL" (T"num" "num" []),
   C"sp" "CFL" (T"num" "num" []), C"lr" "CFL" (T"num" "num" []),
   C"?" "bool"
    ((((T"TREG" "HSL" [] --> T"num" "num" []) --> bool) --> bool)),
   V"rep" ((T"TREG" "HSL" [] --> T"num" "num" [])),
   C"TYPE_DEFINITION" "bool"
    (((T"num" "num" [] --> bool) -->
      ((T"TREG" "HSL" [] --> T"num" "num" []) --> bool))),
   C"!" "bool" (((T"TREG" "HSL" [] --> bool) --> bool)),
   V"a" (T"TREG" "HSL" []),
   C"=" "min" ((T"TREG" "HSL" [] --> (T"TREG" "HSL" [] --> bool))),
   C"num2TREG" "HSL" ((T"num" "num" [] --> T"TREG" "HSL" [])),
   C"TREG2num" "HSL" ((T"TREG" "HSL" [] --> T"num" "num" [])),
   C"r0" "HSL" (T"TREG" "HSL" []), C"r1" "HSL" (T"TREG" "HSL" []),
   C"r2" "HSL" (T"TREG" "HSL" []), C"r3" "HSL" (T"TREG" "HSL" []),
   C"r4" "HSL" (T"TREG" "HSL" []), C"r5" "HSL" (T"TREG" "HSL" []),
   C"r6" "HSL" (T"TREG" "HSL" []), C"r7" "HSL" (T"TREG" "HSL" []),
   C"r8" "HSL" (T"TREG" "HSL" []), V"x" (T"TREG" "HSL" []),
   C"TREG_size" "HSL" ((T"TREG" "HSL" [] --> T"num" "num" [])),
   V"v6" (alpha), V"v7" (alpha), V"v8" (alpha),
   C"TREG_case" "HSL"
    ((alpha -->
      (alpha -->
       (alpha -->
        (alpha -->
         (alpha -->
          (alpha -->
           (alpha -->
            (alpha --> (alpha --> (T"TREG" "HSL" [] --> alpha))))))))))),
   C"data_reg_index" "HSL" ((T"TREG" "HSL" [] --> T"num" "num" [])),
   V"i" (T"num" "num" []),
   C"data_reg_name" "HSL" ((T"num" "num" [] --> T"TREG" "HSL" [])),
   C"COND" "bool"
    ((bool -->
      (T"TREG" "HSL" [] --> (T"TREG" "HSL" [] --> T"TREG" "HSL" [])))),
   C"=" "min"
    (((T"TREG" "HSL" [] --> T"MREG" "CFL" []) -->
      ((T"TREG" "HSL" [] --> T"MREG" "CFL" []) --> bool))),
   C"conv_reg" "HSL" ((T"TREG" "HSL" [] --> T"MREG" "CFL" [])),
   C"o" "combin"
    (((T"num" "num" [] --> T"MREG" "CFL" []) -->
      ((T"TREG" "HSL" [] --> T"num" "num" []) -->
       (T"TREG" "HSL" [] --> T"MREG" "CFL" [])))),
   C"from_reg_index" "CFL" ((T"num" "num" [] --> T"MREG" "CFL" [])),
   C"?" "bool"
    ((((T"TEXP" "HSL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]])
       --> bool) --> bool)),
   V"rep"
    ((T"TEXP" "HSL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]]
       --> bool) -->
      ((T"TEXP" "HSL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]])
       --> bool))),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]]
        --> bool) --> bool) --> bool)),
   V"'TEXP'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]] -->
      bool)), C"==>" "min" ((bool --> (bool --> bool))),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]]
       --> bool) --> bool)), C"\\/" "bool" ((bool --> (bool --> bool))),
   C"?" "bool" (((T"TREG" "HSL" [] --> bool) --> bool)),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]]
       --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]])
        -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []],
              T"num" "num" []]]])))),
   C"," "pair"
    ((T"TREG" "HSL" [] -->
      (T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []] -->
       T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]))),
   C"," "pair"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] -->
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]))),
   C"@" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) -->
      T"cart" "fcp" [bool, T"i32" "words" []])),
   V"v" (T"cart" "fcp" [bool, T"i32" "words" []]), C"T" "bool" (bool),
   C"@" "min" (((T"num" "num" [] --> bool) --> T"num" "num" [])),
   V"v" (T"num" "num" []),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]]),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"a" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"@" "min" (((T"TREG" "HSL" [] --> bool) --> T"TREG" "HSL" [])),
   V"v" (T"TREG" "HSL" []),
   C"?" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"a" (T"num" "num" []),
   C"!" "bool" (((T"TEXP" "HSL" [] --> bool) --> bool)),
   V"a" (T"TEXP" "HSL" []),
   C"=" "min" ((T"TEXP" "HSL" [] --> (T"TEXP" "HSL" [] --> bool))),
   C"mk_TEXP" "HSL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]] -->
      T"TEXP" "HSL" [])),
   C"dest_TEXP" "HSL"
    ((T"TEXP" "HSL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []], T"num" "num" []]]]),
   C"=" "min"
    (((T"TREG" "HSL" [] --> T"TEXP" "HSL" []) -->
      ((T"TREG" "HSL" [] --> T"TEXP" "HSL" []) --> bool))),
   C"HSL0" "HSL" ((T"TREG" "HSL" [] --> T"TEXP" "HSL" [])),
   C"=" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TEXP" "HSL" []) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TEXP" "HSL" []) -->
       bool))),
   C"HSL1" "HSL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TEXP" "HSL" [])),
   C"=" "min"
    (((T"num" "num" [] --> T"TEXP" "HSL" []) -->
      ((T"num" "num" [] --> T"TEXP" "HSL" []) --> bool))),
   C"HSL2" "HSL" ((T"num" "num" [] --> T"TEXP" "HSL" [])),
   C"inR" "HSL" ((T"TREG" "HSL" [] --> T"TEXP" "HSL" [])),
   C"inC" "HSL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TEXP" "HSL" [])),
   C"inE" "HSL" ((T"num" "num" [] --> T"TEXP" "HSL" [])),
   C"!" "bool" ((((T"TREG" "HSL" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"TREG" "HSL" [] --> alpha)),
   C"!" "bool"
    ((((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) --> bool) -->
      bool)), V"f1" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   C"!" "bool" ((((T"num" "num" [] --> alpha) --> bool) --> bool)),
   V"f2" ((T"num" "num" [] --> alpha)),
   C"TEXP_case" "HSL"
    (((T"TREG" "HSL" [] --> alpha) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
       ((T"num" "num" [] --> alpha) --> (T"TEXP" "HSL" [] --> alpha))))),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   C"TEXP_size" "HSL" ((T"TEXP" "HSL" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"?" "bool"
    ((((T"TROC" "HSL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
       --> bool) --> bool)),
   V"rep"
    ((T"TROC" "HSL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      ((T"TROC" "HSL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
       --> bool))),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool) --> bool) --> bool)),
   V"'TROC'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) --> bool)),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
        -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"," "pair"
    ((T"TREG" "HSL" [] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"prod" "pair"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]))),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"!" "bool" (((T"TROC" "HSL" [] --> bool) --> bool)),
   V"a" (T"TROC" "HSL" []),
   C"=" "min" ((T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> bool))),
   C"mk_TROC" "HSL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      T"TROC" "HSL" [])),
   C"dest_TROC" "HSL"
    ((T"TROC" "HSL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"=" "min"
    (((T"TREG" "HSL" [] --> T"TROC" "HSL" []) -->
      ((T"TREG" "HSL" [] --> T"TROC" "HSL" []) --> bool))),
   C"HSL3" "HSL" ((T"TREG" "HSL" [] --> T"TROC" "HSL" [])),
   C"=" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TROC" "HSL" []) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TROC" "HSL" []) -->
       bool))),
   C"HSL4" "HSL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TROC" "HSL" [])),
   C"Rg" "HSL" ((T"TREG" "HSL" [] --> T"TROC" "HSL" [])),
   C"Cn" "HSL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TROC" "HSL" [])),
   C"TROC_case" "HSL"
    (((T"TREG" "HSL" [] --> alpha) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
       (T"TROC" "HSL" [] --> alpha)))),
   C"TROC_size" "HSL" ((T"TROC" "HSL" [] --> T"num" "num" [])),
   V"r" (T"TREG" "HSL" []),
   C"roc_2_exp" "HSL" ((T"TROC" "HSL" [] --> T"TEXP" "HSL" [])),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"TEXP" "HSL" []] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
      ((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"TEXP" "HSL" []] --> T"cart" "fcp" [bool, T"i32" "words" []])
       --> bool))),
   C"tread_tupled" "HSL"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"TEXP" "HSL" []] --> T"cart" "fcp" [bool, T"i32" "words" []])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"TEXP" "HSL" []] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"TEXP" "HSL" []] --> bool)) -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"TEXP" "HSL" []] --> T"cart" "fcp" [bool, T"i32" "words" []])
        -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"TEXP" "HSL" []] --> T"cart" "fcp" [bool, T"i32" "words" []]))
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"TEXP" "HSL" []] -->
        T"cart" "fcp" [bool, T"i32" "words" []])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"TEXP" "HSL" []] -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"TEXP" "HSL" []] --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"TEXP" "HSL" []] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"TEXP" "HSL" []] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"TEXP" "HSL" []] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"TEXP" "HSL" []] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"TEXP" "HSL" []] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"TEXP" "HSL" []] --> bool)) --> bool)),
   V"tread_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"TEXP" "HSL" []] --> T"cart" "fcp" [bool, T"i32" "words" []])),
   V"a"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
       T"TEXP" "HSL" []]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"TEXP" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []])) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"TEXP" "HSL" []] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"v1"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"v2" (T"TEXP" "HSL" []),
   C"pair_case" "pair"
    (((T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       (T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
        T"cart" "fcp" [bool, T"i32" "words" []])) -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"rg"
    (T"fmap" "finite_map"
      [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   V"sk"
    (T"fmap" "finite_map"
      [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"TEXP_case" "HSL"
    (((T"TREG" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] -->
        T"cart" "fcp" [bool, T"i32" "words" []]) -->
       ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
        (T"TEXP" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))))),
   C"I" "combin"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      T"cart" "fcp" [bool, T"i32" "words" []])),
   C"FAPPLY" "finite_map"
    ((T"fmap" "finite_map"
       [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"TREG" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"FAPPLY" "finite_map"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"!" "bool"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) --> bool)),
   V"x"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"x1" (T"TEXP" "HSL" []),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"tread" "HSL"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"TEXP" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"," "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"TEXP" "HSL" [] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"TEXP" "HSL" []]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]],
         T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
       T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]]) -->
      ((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
            T"fmap" "finite_map" [T"num" "num" [], alpha]],
          T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
        T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]]) --> bool))),
   C"twrite_tupled" "HSL"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]],
        T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
      T"prod" "pair"
       [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
        T"fmap" "finite_map" [T"num" "num" [], alpha]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]],
         T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
            T"fmap" "finite_map" [T"num" "num" [], alpha]],
          T"prod" "pair" [T"TEXP" "HSL" [], alpha]] --> bool)) -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
             T"fmap" "finite_map" [T"num" "num" [], alpha]],
           T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
         T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]]) -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
             T"fmap" "finite_map" [T"num" "num" [], alpha]],
           T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
         T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]])) -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
            T"fmap" "finite_map" [T"num" "num" [], alpha]],
          T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
        T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
            T"fmap" "finite_map" [T"num" "num" [], alpha]],
          T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
             T"fmap" "finite_map" [T"num" "num" [], alpha]],
           T"prod" "pair" [T"TEXP" "HSL" [], alpha]] --> bool)) --> bool)
      -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]],
         T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
            T"fmap" "finite_map" [T"num" "num" [], alpha]],
          T"prod" "pair" [T"TEXP" "HSL" [], alpha]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]],
        T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]],
         T"prod" "pair" [T"TEXP" "HSL" [], alpha]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]],
         T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
            T"fmap" "finite_map" [T"num" "num" [], alpha]],
          T"prod" "pair" [T"TEXP" "HSL" [], alpha]] --> bool)) --> bool)),
   V"twrite_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]],
        T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
      T"prod" "pair"
       [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
        T"fmap" "finite_map" [T"num" "num" [], alpha]])),
   V"a"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]],
       T"prod" "pair" [T"TEXP" "HSL" [], alpha]]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]] -->
       (T"prod" "pair" [T"TEXP" "HSL" [], alpha] -->
        T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]])) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]],
         T"prod" "pair" [T"TEXP" "HSL" [], alpha]] -->
       T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]]))),
   V"v1"
    (T"prod" "pair"
      [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
       T"fmap" "finite_map" [T"num" "num" [], alpha]]),
   V"v2" (T"prod" "pair" [T"TEXP" "HSL" [], alpha]),
   C"pair_case" "pair"
    (((T"fmap" "finite_map" [T"TREG" "HSL" [], alpha] -->
       (T"fmap" "finite_map" [T"num" "num" [], alpha] -->
        T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]])) -->
      (T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]] -->
       T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]]))),
   V"rg" (T"fmap" "finite_map" [T"TREG" "HSL" [], alpha]),
   V"sk" (T"fmap" "finite_map" [T"num" "num" [], alpha]),
   C"pair_case" "pair"
    (((T"TEXP" "HSL" [] -->
       (alpha -->
        T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]])) -->
      (T"prod" "pair" [T"TEXP" "HSL" [], alpha] -->
       T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]]))),
   V"v5" (T"TEXP" "HSL" []), V"v" (alpha),
   C"TEXP_case" "HSL"
    (((T"TREG" "HSL" [] -->
       T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]]) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]]) -->
       ((T"num" "num" [] -->
         T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]]) -->
        (T"TEXP" "HSL" [] -->
         T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]]))))),
   C"I" "combin"
    ((T"prod" "pair"
       [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
        T"fmap" "finite_map" [T"num" "num" [], alpha]] -->
      T"prod" "pair"
       [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
        T"fmap" "finite_map" [T"num" "num" [], alpha]])),
   C"," "pair"
    ((T"fmap" "finite_map" [T"TREG" "HSL" [], alpha] -->
      (T"fmap" "finite_map" [T"num" "num" [], alpha] -->
       T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]]))),
   C"FUPDATE" "finite_map"
    ((T"fmap" "finite_map" [T"TREG" "HSL" [], alpha] -->
      (T"prod" "pair" [T"TREG" "HSL" [], alpha] -->
       T"fmap" "finite_map" [T"TREG" "HSL" [], alpha]))),
   C"," "pair"
    ((T"TREG" "HSL" [] -->
      (alpha --> T"prod" "pair" [T"TREG" "HSL" [], alpha]))),
   V"v0" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"FUPDATE" "finite_map"
    ((T"fmap" "finite_map" [T"num" "num" [], alpha] -->
      (T"prod" "pair" [T"num" "num" [], alpha] -->
       T"fmap" "finite_map" [T"num" "num" [], alpha]))),
   C"," "pair"
    ((T"num" "num" [] -->
      (alpha --> T"prod" "pair" [T"num" "num" [], alpha]))),
   C"!" "bool"
    (((T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]] --> bool) -->
      bool)),
   V"x"
    (T"prod" "pair"
      [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
       T"fmap" "finite_map" [T"num" "num" [], alpha]]), V"x2" (alpha),
   C"=" "min"
    ((T"prod" "pair"
       [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
        T"fmap" "finite_map" [T"num" "num" [], alpha]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
         T"fmap" "finite_map" [T"num" "num" [], alpha]] --> bool))),
   C"twrite" "HSL"
    ((T"prod" "pair"
       [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
        T"fmap" "finite_map" [T"num" "num" [], alpha]] -->
      (T"TEXP" "HSL" [] -->
       (alpha -->
        T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]])))),
   C"," "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
        T"fmap" "finite_map" [T"num" "num" [], alpha]] -->
      (T"prod" "pair" [T"TEXP" "HSL" [], alpha] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
           T"fmap" "finite_map" [T"num" "num" [], alpha]],
         T"prod" "pair" [T"TEXP" "HSL" [], alpha]]))),
   C"," "pair"
    ((T"TEXP" "HSL" [] -->
      (alpha --> T"prod" "pair" [T"TEXP" "HSL" [], alpha]))),
   C"!" "bool" (((T"MREG" "CFL" [] --> bool) --> bool)),
   V"r" (T"MREG" "CFL" []),
   C"from_MEXP" "HSL" ((T"MEXP" "CFL" [] --> T"TEXP" "HSL" [])),
   C"MR" "CFL" ((T"MREG" "CFL" [] --> T"MEXP" "CFL" [])),
   C"index_of_reg" "CFL" ((T"MREG" "CFL" [] --> T"num" "num" [])),
   C"MC" "CFL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" [])),
   C"?" "bool"
    ((((T"TOPER" "HSL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"TROC" "HSL" [],
                T"prod" "pair"
                 [T"TROC" "HSL" [],
                  T"cart" "fcp" [bool, T"i5" "words" []]]]]]]) --> bool)
      --> bool)),
   V"rep"
    ((T"TOPER" "HSL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"TROC" "HSL" [],
              T"prod" "pair"
               [T"TROC" "HSL" [],
                T"cart" "fcp" [bool, T"i5" "words" []]]]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"TROC" "HSL" [],
               T"prod" "pair"
                [T"TROC" "HSL" [],
                 T"cart" "fcp" [bool, T"i5" "words" []]]]]]] --> bool) -->
      ((T"TOPER" "HSL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"TROC" "HSL" [],
                T"prod" "pair"
                 [T"TROC" "HSL" [],
                  T"cart" "fcp" [bool, T"i5" "words" []]]]]]]) --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"TROC" "HSL" [],
             T"prod" "pair"
              [T"TROC" "HSL" [],
               T"cart" "fcp" [bool, T"i5" "words" []]]]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"TROC" "HSL" [],
                T"prod" "pair"
                 [T"TROC" "HSL" [],
                  T"cart" "fcp" [bool, T"i5" "words" []]]]]]] --> bool) -->
       bool) --> bool)),
   V"'TOPER'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"TROC" "HSL" [],
              T"prod" "pair"
               [T"TROC" "HSL" [],
                T"cart" "fcp" [bool, T"i5" "words" []]]]]]] --> bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"TROC" "HSL" [],
               T"prod" "pair"
                [T"TROC" "HSL" [],
                 T"cart" "fcp" [bool, T"i5" "words" []]]]]]] --> bool) -->
      bool)), V"a0" (T"TREG" "HSL" []), V"a1" (T"num" "num" []),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"TROC" "HSL" [],
              T"prod" "pair"
               [T"TROC" "HSL" [],
                T"cart" "fcp" [bool, T"i5" "words" []]]]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"TROC" "HSL" [],
               T"prod" "pair"
                [T"TROC" "HSL" [],
                 T"cart" "fcp" [bool, T"i5" "words" []]]]]]] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"TROC" "HSL" [],
             T"prod" "pair"
              [T"TROC" "HSL" [], T"cart" "fcp" [bool, T"i5" "words" []]]]]]
       -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"TROC" "HSL" [],
                 T"prod" "pair"
                  [T"TROC" "HSL" [],
                   T"cart" "fcp" [bool, T"i5" "words" []]]]]]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"TROC" "HSL" [],
                T"prod" "pair"
                 [T"TROC" "HSL" [],
                  T"cart" "fcp" [bool, T"i5" "words" []]]]]]])))),
   C"," "pair"
    ((T"TREG" "HSL" [] -->
      (T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"TROC" "HSL" [],
           T"prod" "pair"
            [T"TROC" "HSL" [], T"cart" "fcp" [bool, T"i5" "words" []]]]]
       -->
       T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"TROC" "HSL" [],
             T"prod" "pair"
              [T"TROC" "HSL" [],
               T"cart" "fcp" [bool, T"i5" "words" []]]]]]))),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"TROC" "HSL" [],
         T"prod" "pair"
          [T"TROC" "HSL" [], T"cart" "fcp" [bool, T"i5" "words" []]]] -->
       T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"TROC" "HSL" [],
           T"prod" "pair"
            [T"TROC" "HSL" [],
             T"cart" "fcp" [bool, T"i5" "words" []]]]]))),
   C"," "pair"
    ((T"TROC" "HSL" [] -->
      (T"prod" "pair"
        [T"TROC" "HSL" [], T"cart" "fcp" [bool, T"i5" "words" []]] -->
       T"prod" "pair"
        [T"TROC" "HSL" [],
         T"prod" "pair"
          [T"TROC" "HSL" [], T"cart" "fcp" [bool, T"i5" "words" []]]]))),
   C"@" "min" (((T"TROC" "HSL" [] --> bool) --> T"TROC" "HSL" [])),
   V"v" (T"TROC" "HSL" []),
   C"," "pair"
    ((T"TROC" "HSL" [] -->
      (T"cart" "fcp" [bool, T"i5" "words" []] -->
       T"prod" "pair"
        [T"TROC" "HSL" [], T"cart" "fcp" [bool, T"i5" "words" []]]))),
   C"@" "min"
    (((T"cart" "fcp" [bool, T"i5" "words" []] --> bool) -->
      T"cart" "fcp" [bool, T"i5" "words" []])),
   V"v" (T"cart" "fcp" [bool, T"i5" "words" []]),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"TROC" "HSL" [],
             T"prod" "pair"
              [T"TROC" "HSL" [],
               T"cart" "fcp" [bool, T"i5" "words" []]]]]]]),
   V"a0" (T"num" "num" []), V"a1" (T"TREG" "HSL" []),
   C"?" "bool" (((T"TROC" "HSL" [] --> bool) --> bool)),
   V"a1" (T"TROC" "HSL" []), V"a2" (T"TROC" "HSL" []),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i5" "words" []] --> bool) --> bool)),
   V"a2" (T"cart" "fcp" [bool, T"i5" "words" []]),
   C"!" "bool" (((T"TOPER" "HSL" [] --> bool) --> bool)),
   V"a" (T"TOPER" "HSL" []),
   C"=" "min" ((T"TOPER" "HSL" [] --> (T"TOPER" "HSL" [] --> bool))),
   C"mk_TOPER" "HSL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"TROC" "HSL" [],
              T"prod" "pair"
               [T"TROC" "HSL" [],
                T"cart" "fcp" [bool, T"i5" "words" []]]]]]] -->
      T"TOPER" "HSL" [])),
   C"dest_TOPER" "HSL"
    ((T"TOPER" "HSL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"TROC" "HSL" [],
              T"prod" "pair"
               [T"TROC" "HSL" [],
                T"cart" "fcp" [bool, T"i5" "words" []]]]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"TROC" "HSL" [],
             T"prod" "pair"
              [T"TROC" "HSL" [],
               T"cart" "fcp" [bool, T"i5" "words" []]]]]]]),
   C"=" "min"
    (((T"TREG" "HSL" [] --> (T"num" "num" [] --> T"TOPER" "HSL" [])) -->
      ((T"TREG" "HSL" [] --> (T"num" "num" [] --> T"TOPER" "HSL" [])) -->
       bool))),
   C"HSL5" "HSL"
    ((T"TREG" "HSL" [] --> (T"num" "num" [] --> T"TOPER" "HSL" []))),
   C"=" "min"
    (((T"num" "num" [] --> (T"TREG" "HSL" [] --> T"TOPER" "HSL" [])) -->
      ((T"num" "num" [] --> (T"TREG" "HSL" [] --> T"TOPER" "HSL" [])) -->
       bool))),
   C"HSL6" "HSL"
    ((T"num" "num" [] --> (T"TREG" "HSL" [] --> T"TOPER" "HSL" []))),
   C"=" "min"
    (((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])) -->
      ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])) -->
       bool))),
   C"HSL7" "HSL"
    ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))),
   C"=" "min"
    (((T"TREG" "HSL" [] -->
       (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))) -->
      ((T"TREG" "HSL" [] -->
        (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))
       --> bool))),
   C"HSL8" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"HSL9" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"HSL10" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"HSL11" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"HSL12" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"HSL13" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"HSL14" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
   C"=" "min"
    (((T"TREG" "HSL" [] -->
       (T"TROC" "HSL" [] -->
        (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))
      -->
      ((T"TREG" "HSL" [] -->
        (T"TROC" "HSL" [] -->
         (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))
       --> bool))),
   C"HSL15" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))),
   C"HSL16" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))),
   C"HSL17" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))),
   C"HSL18" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"TOPER" "HSL" [])))),
   C"TLDR" "HSL"
    ((T"TREG" "HSL" [] --> (T"num" "num" [] --> T"TOPER" "HSL" []))),
   C"TSTR" "HSL"
    ((T"num" "num" [] --> (T"TREG" "HSL" [] --> T"TOPER" "HSL" []))),
   C"TMOV" "HSL"
    ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))),
   C"TADD" "HSL"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))),
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
   C"!" "bool"
    ((((T"TREG" "HSL" [] --> (T"num" "num" [] --> alpha)) --> bool) -->
      bool)), V"f" ((T"TREG" "HSL" [] --> (T"num" "num" [] --> alpha))),
   C"!" "bool"
    ((((T"num" "num" [] --> (T"TREG" "HSL" [] --> alpha)) --> bool) -->
      bool)), V"f1" ((T"num" "num" [] --> (T"TREG" "HSL" [] --> alpha))),
   C"!" "bool"
    ((((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)) --> bool) -->
      bool)), V"f2" ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))),
   C"!" "bool"
    ((((T"TREG" "HSL" [] -->
        (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) --> bool) -->
      bool)),
   V"f3"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f4"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f5"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f6"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f7"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f8"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f9"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   C"!" "bool"
    ((((T"TREG" "HSL" [] -->
        (T"TROC" "HSL" [] -->
         (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha))) --> bool) -->
      bool)),
   V"f10"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f11"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f12"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f13"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   C"TOPER_case" "HSL"
    (((T"TREG" "HSL" [] --> (T"num" "num" [] --> alpha)) -->
      ((T"num" "num" [] --> (T"TREG" "HSL" [] --> alpha)) -->
       ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)) -->
        ((T"TREG" "HSL" [] -->
          (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
         ((T"TREG" "HSL" [] -->
           (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
          ((T"TREG" "HSL" [] -->
            (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
           ((T"TREG" "HSL" [] -->
             (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
            ((T"TREG" "HSL" [] -->
              (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
             ((T"TREG" "HSL" [] -->
               (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
              ((T"TREG" "HSL" [] -->
                (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))) -->
               ((T"TREG" "HSL" [] -->
                 (T"TROC" "HSL" [] -->
                  (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha))) -->
                ((T"TREG" "HSL" [] -->
                  (T"TROC" "HSL" [] -->
                   (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha))) -->
                 ((T"TREG" "HSL" [] -->
                   (T"TROC" "HSL" [] -->
                    (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                  -->
                  ((T"TREG" "HSL" [] -->
                    (T"TROC" "HSL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                   --> (T"TOPER" "HSL" [] --> alpha)))))))))))))))),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i5" "words" []] --> bool) --> bool)),
   C"TOPER_size" "HSL" ((T"TOPER" "HSL" [] --> T"num" "num" [])),
   C"?" "bool"
    ((((T"HSL_STRUCTURE" "HSL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"TOPER" "HSL" []],
            T"prod" "pair"
             [T"prod" "pair"
               [T"TREG" "HSL" [],
                T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
              T"prod" "pair"
               [T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]],
                T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]]]]]]) --> bool) -->
      bool)),
   V"rep"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"TOPER" "HSL" []],
          T"prod" "pair"
           [T"prod" "pair"
             [T"TREG" "HSL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
            T"prod" "pair"
             [T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]],
              T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]]]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"TOPER" "HSL" []],
           T"prod" "pair"
            [T"prod" "pair"
              [T"TREG" "HSL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
             T"prod" "pair"
              [T"prod" "pair"
                [T"list" "list" [T"TEXP" "HSL" []],
                 T"list" "list" [T"TEXP" "HSL" []]],
               T"prod" "pair"
                [T"list" "list" [T"TEXP" "HSL" []],
                 T"list" "list" [T"TEXP" "HSL" []]]]]]] --> bool) -->
      ((T"HSL_STRUCTURE" "HSL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"TOPER" "HSL" []],
            T"prod" "pair"
             [T"prod" "pair"
               [T"TREG" "HSL" [],
                T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
              T"prod" "pair"
               [T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]],
                T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]]]]]]) --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"TOPER" "HSL" []],
         T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]],
             T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]]]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"TOPER" "HSL" []],
            T"prod" "pair"
             [T"prod" "pair"
               [T"TREG" "HSL" [],
                T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
              T"prod" "pair"
               [T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]],
                T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]]]]]] --> bool) -->
       bool) --> bool)),
   V"'HSL_STRUCTURE'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"TOPER" "HSL" []],
          T"prod" "pair"
           [T"prod" "pair"
             [T"TREG" "HSL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
            T"prod" "pair"
             [T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]],
              T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]]]]]] --> bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"TOPER" "HSL" []],
           T"prod" "pair"
            [T"prod" "pair"
              [T"TREG" "HSL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
             T"prod" "pair"
              [T"prod" "pair"
                [T"list" "list" [T"TEXP" "HSL" []],
                 T"list" "list" [T"TEXP" "HSL" []]],
               T"prod" "pair"
                [T"list" "list" [T"TEXP" "HSL" []],
                 T"list" "list" [T"TEXP" "HSL" []]]]]]] --> bool) -->
      bool)),
   C"?" "bool" (((T"list" "list" [T"TOPER" "HSL" []] --> bool) --> bool)),
   V"a" (T"list" "list" [T"TOPER" "HSL" []]),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"TOPER" "HSL" []],
          T"prod" "pair"
           [T"prod" "pair"
             [T"TREG" "HSL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
            T"prod" "pair"
             [T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]],
              T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]]]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"TOPER" "HSL" []],
           T"prod" "pair"
            [T"prod" "pair"
              [T"TREG" "HSL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
             T"prod" "pair"
              [T"prod" "pair"
                [T"list" "list" [T"TEXP" "HSL" []],
                 T"list" "list" [T"TEXP" "HSL" []]],
               T"prod" "pair"
                [T"list" "list" [T"TEXP" "HSL" []],
                 T"list" "list" [T"TEXP" "HSL" []]]]]]] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"TOPER" "HSL" []],
         T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]],
             T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]]]]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"TOPER" "HSL" []],
             T"prod" "pair"
              [T"prod" "pair"
                [T"TREG" "HSL" [],
                 T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
               T"prod" "pair"
                [T"prod" "pair"
                  [T"list" "list" [T"TEXP" "HSL" []],
                   T"list" "list" [T"TEXP" "HSL" []]],
                 T"prod" "pair"
                  [T"list" "list" [T"TEXP" "HSL" []],
                   T"list" "list" [T"TEXP" "HSL" []]]]]]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"TOPER" "HSL" []],
            T"prod" "pair"
             [T"prod" "pair"
               [T"TREG" "HSL" [],
                T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
              T"prod" "pair"
               [T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]],
                T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]]]]]])))),
   C"," "pair"
    ((T"list" "list" [T"TOPER" "HSL" []] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
         T"prod" "pair"
          [T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]],
           T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]]]] -->
       T"prod" "pair"
        [T"list" "list" [T"TOPER" "HSL" []],
         T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]],
             T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]]]]]))),
   C"," "pair"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
         T"prod" "pair"
          [T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]],
           T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]]]]))),
   C"@" "min"
    (((T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] --> bool)
      -->
      T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]])),
   V"v"
    (T"prod" "pair"
      [T"TREG" "HSL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]]),
   C"," "pair"
    ((T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"list" "list" [T"TEXP" "HSL" []]] -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]]))),
   C"@" "min"
    (((T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] --> bool) -->
      T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"list" "list" [T"TEXP" "HSL" []]])),
   V"v"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"TOPER" "HSL" []],
         T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]],
             T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]]]]]]),
   C"?" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"TOPER" "HSL" []],
           T"prod" "pair"
            [T"prod" "pair"
              [T"TREG" "HSL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
             T"prod" "pair"
              [T"prod" "pair"
                [T"list" "list" [T"TEXP" "HSL" []],
                 T"list" "list" [T"TEXP" "HSL" []]],
               T"prod" "pair"
                [T"list" "list" [T"TEXP" "HSL" []],
                 T"list" "list" [T"TEXP" "HSL" []]]]]]] --> bool) -->
      bool)),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"TOPER" "HSL" []],
         T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]],
             T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]]]]]]),
   V"a1"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"TOPER" "HSL" []],
         T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]],
             T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]]]]]]),
   C"@" "min"
    (((T"list" "list" [T"TOPER" "HSL" []] --> bool) -->
      T"list" "list" [T"TOPER" "HSL" []])),
   V"v" (T"list" "list" [T"TOPER" "HSL" []]),
   C"FCONS" "ind_type"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"TOPER" "HSL" []],
          T"prod" "pair"
           [T"prod" "pair"
             [T"TREG" "HSL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
            T"prod" "pair"
             [T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]],
              T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]]]]]] -->
      ((T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"TOPER" "HSL" []],
            T"prod" "pair"
             [T"prod" "pair"
               [T"TREG" "HSL" [],
                T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
              T"prod" "pair"
               [T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]],
                T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]]]]]]) -->
       (T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"TOPER" "HSL" []],
            T"prod" "pair"
             [T"prod" "pair"
               [T"TREG" "HSL" [],
                T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
              T"prod" "pair"
               [T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]],
                T"prod" "pair"
                 [T"list" "list" [T"TEXP" "HSL" []],
                  T"list" "list" [T"TEXP" "HSL" []]]]]]])))),
   C"?" "bool"
    (((T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] --> bool)
      --> bool)),
   V"a0"
    (T"prod" "pair"
      [T"TREG" "HSL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]]),
   V"a2"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"TOPER" "HSL" []],
         T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]],
             T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]]]]]]),
   C"?" "bool"
    (((T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] --> bool) --> bool)),
   V"a0"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   V"a2"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   C"!" "bool" (((T"HSL_STRUCTURE" "HSL" [] --> bool) --> bool)),
   V"a" (T"HSL_STRUCTURE" "HSL" []),
   C"=" "min"
    ((T"HSL_STRUCTURE" "HSL" [] --> (T"HSL_STRUCTURE" "HSL" [] --> bool))),
   C"mk_HSL_STRUCTURE" "HSL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"TOPER" "HSL" []],
          T"prod" "pair"
           [T"prod" "pair"
             [T"TREG" "HSL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
            T"prod" "pair"
             [T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]],
              T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]]]]]] -->
      T"HSL_STRUCTURE" "HSL" [])),
   C"dest_HSL_STRUCTURE" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"TOPER" "HSL" []],
          T"prod" "pair"
           [T"prod" "pair"
             [T"TREG" "HSL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
            T"prod" "pair"
             [T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]],
              T"prod" "pair"
               [T"list" "list" [T"TEXP" "HSL" []],
                T"list" "list" [T"TEXP" "HSL" []]]]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"TOPER" "HSL" []],
         T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]],
             T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]]]]]]),
   C"=" "min"
    (((T"list" "list" [T"TOPER" "HSL" []] --> T"HSL_STRUCTURE" "HSL" [])
      -->
      ((T"list" "list" [T"TOPER" "HSL" []] --> T"HSL_STRUCTURE" "HSL" [])
       --> bool))),
   C"HSL19" "HSL"
    ((T"list" "list" [T"TOPER" "HSL" []] --> T"HSL_STRUCTURE" "HSL" [])),
   C"=" "min"
    (((T"HSL_STRUCTURE" "HSL" [] -->
       (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])) -->
      ((T"HSL_STRUCTURE" "HSL" [] -->
        (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])) -->
       bool))),
   C"HSL20" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))),
   V"a0" (T"HSL_STRUCTURE" "HSL" []), V"a1" (T"HSL_STRUCTURE" "HSL" []),
   C"=" "min"
    (((T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
       (T"HSL_STRUCTURE" "HSL" [] -->
        (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))) -->
      ((T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
        (T"HSL_STRUCTURE" "HSL" [] -->
         (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))) -->
       bool))),
   C"HSL21" "HSL"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])))),
   V"a2" (T"HSL_STRUCTURE" "HSL" []),
   C"=" "min"
    (((T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
       (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])) -->
      ((T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
        (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])) -->
       bool))),
   C"HSL22" "HSL"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))),
   C"=" "min"
    (((T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] -->
       (T"HSL_STRUCTURE" "HSL" [] -->
        (T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]] -->
         T"HSL_STRUCTURE" "HSL" []))) -->
      ((T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]] -->
        (T"HSL_STRUCTURE" "HSL" [] -->
         (T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]] -->
          T"HSL_STRUCTURE" "HSL" []))) --> bool))),
   C"HSL23" "HSL"
    ((T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"list" "list" [T"TEXP" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]] -->
        T"HSL_STRUCTURE" "HSL" [])))),
   C"Blk" "HSL"
    ((T"list" "list" [T"TOPER" "HSL" []] --> T"HSL_STRUCTURE" "HSL" [])),
   C"Sc" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))),
   C"Cj" "HSL"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])))),
   C"Tr" "HSL"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))),
   C"Fc" "HSL"
    ((T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"list" "list" [T"TEXP" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]] -->
        T"HSL_STRUCTURE" "HSL" [])))),
   C"!" "bool"
    ((((T"list" "list" [T"TOPER" "HSL" []] --> alpha) --> bool) --> bool)),
   V"f" ((T"list" "list" [T"TOPER" "HSL" []] --> alpha)),
   C"!" "bool"
    ((((T"HSL_STRUCTURE" "HSL" [] -->
        (T"HSL_STRUCTURE" "HSL" [] --> alpha)) --> bool) --> bool)),
   V"f1"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"HSL_STRUCTURE" "HSL" [] --> alpha))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
        (T"HSL_STRUCTURE" "HSL" [] -->
         (T"HSL_STRUCTURE" "HSL" [] --> alpha))) --> bool) --> bool)),
   V"f2"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"HSL_STRUCTURE" "HSL" [] --> alpha)))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
        (T"HSL_STRUCTURE" "HSL" [] --> alpha)) --> bool) --> bool)),
   V"f3"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] --> alpha))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]] -->
        (T"HSL_STRUCTURE" "HSL" [] -->
         (T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]] --> alpha))) --> bool) -->
      bool)),
   V"f4"
    ((T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"list" "list" [T"TEXP" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]] --> alpha)))),
   C"!" "bool" (((T"list" "list" [T"TOPER" "HSL" []] --> bool) --> bool)),
   C"HSL_STRUCTURE_case" "HSL"
    (((T"list" "list" [T"TOPER" "HSL" []] --> alpha) -->
      ((T"HSL_STRUCTURE" "HSL" [] -->
        (T"HSL_STRUCTURE" "HSL" [] --> alpha)) -->
       ((T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] -->
          (T"HSL_STRUCTURE" "HSL" [] --> alpha))) -->
        ((T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
          (T"HSL_STRUCTURE" "HSL" [] --> alpha)) -->
         ((T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]] -->
           (T"HSL_STRUCTURE" "HSL" [] -->
            (T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]] --> alpha))) -->
          (T"HSL_STRUCTURE" "HSL" [] --> alpha))))))),
   C"!" "bool"
    (((T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] --> bool)
      --> bool)),
   C"!" "bool"
    (((T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] --> bool) --> bool)),
   C"HSL_STRUCTURE_size" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] --> T"num" "num" [])),
   C"list_size" "list"
    (((T"TOPER" "HSL" [] --> T"num" "num" []) -->
      (T"list" "list" [T"TOPER" "HSL" []] --> T"num" "num" []))),
   C"UNCURRY" "pair"
    (((T"TREG" "HSL" [] -->
       (T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []] -->
        T"num" "num" [])) -->
      (T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
       T"num" "num" []))),
   V"y" (T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]),
   C"UNCURRY" "pair"
    (((T"COND" "preARM" [] --> (T"TROC" "HSL" [] --> T"num" "num" [])) -->
      (T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []] -->
       T"num" "num" []))), V"x" (T"COND" "preARM" []),
   V"y" (T"TROC" "HSL" []),
   C"COND_size" "preARM" ((T"COND" "preARM" [] --> T"num" "num" [])),
   C"UNCURRY" "pair"
    (((T"list" "list" [T"TEXP" "HSL" []] -->
       (T"list" "list" [T"TEXP" "HSL" []] --> T"num" "num" [])) -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] --> T"num" "num" []))),
   V"x" (T"list" "list" [T"TEXP" "HSL" []]),
   V"y" (T"list" "list" [T"TEXP" "HSL" []]),
   C"list_size" "list"
    (((T"TEXP" "HSL" [] --> T"num" "num" []) -->
      (T"list" "list" [T"TEXP" "HSL" []] --> T"num" "num" []))),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool) -->
      ((T"prod" "pair"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool) --> bool))),
   C"eval_TCND_tupled" "HSL"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      bool)),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool) -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool)) -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"TREG" "HSL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)) --> bool)),
   V"eval_TCND_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      bool)),
   V"a"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool)) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool))),
   V"s"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"pair_case" "pair"
    (((T"TREG" "HSL" [] -->
       (T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []] --> bool))
      -->
      (T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
       bool))), V"v1" (T"TREG" "HSL" []),
   V"v5" (T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]),
   C"pair_case" "pair"
    (((T"COND" "preARM" [] --> (T"TROC" "HSL" [] --> bool)) -->
      (T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []] --> bool))),
   V"v6" (T"COND" "preARM" []), V"v2" (T"TROC" "HSL" []),
   C"COND_case" "preARM"
    ((bool -->
      (bool -->
       (bool -->
        (bool -->
         (bool -->
          (bool -->
           (bool -->
            (bool -->
             (bool -->
              (bool -->
               (bool -->
                (bool -->
                 (bool -->
                  (bool -->
                   (bool -->
                    (bool -->
                     (T"COND" "preARM" [] --> bool)))))))))))))))))),
   C"I" "combin" ((bool --> bool)),
   C"word_hs" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"LET" "bool"
    (((T"prod" "pair"
        [bool, T"prod" "pair" [bool, T"prod" "pair" [bool, bool]]] -->
       bool) -->
      (T"prod" "pair"
        [bool, T"prod" "pair" [bool, T"prod" "pair" [bool, bool]]] -->
       bool))),
   C"UNCURRY" "pair"
    (((bool -->
       (T"prod" "pair" [bool, T"prod" "pair" [bool, bool]] --> bool)) -->
      (T"prod" "pair"
        [bool, T"prod" "pair" [bool, T"prod" "pair" [bool, bool]]] -->
       bool))), V"n" (bool),
   C"UNCURRY" "pair"
    (((bool --> (T"prod" "pair" [bool, bool] --> bool)) -->
      (T"prod" "pair" [bool, T"prod" "pair" [bool, bool]] --> bool))),
   V"z" (bool),
   C"UNCURRY" "pair"
    (((bool --> (bool --> bool)) -->
      (T"prod" "pair" [bool, bool] --> bool))), V"c" (bool), V"v" (bool),
   C"nzcv" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"prod" "pair"
        [bool, T"prod" "pair" [bool, T"prod" "pair" [bool, bool]]]))),
   C"word_hi" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"word_ge" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"word_gt" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"~" "bool" ((bool --> bool)),
   C"word_lo" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"word_ls" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"word_lt" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"word_le" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"F" "bool" (bool),
   V"x"
    (T"prod" "pair"
      [T"TREG" "HSL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]]),
   V"x1"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
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
   C"," "pair"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
      ((T"prod" "pair"
         [T"prod" "pair"
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
                T"cart" "fcp" [bool, T"i32" "words" []]]]],
          T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
       bool))),
   C"transfer_tupled" "HSL"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
        T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]]] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]] -->
       (T"prod" "pair"
         [T"prod" "pair"
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
                T"cart" "fcp" [bool, T"i32" "words" []]]]],
          T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]]] --> bool)) -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]],
           T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]]] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
        -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]],
           T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]]] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
       -->
       (T"prod" "pair"
         [T"prod" "pair"
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
                T"cart" "fcp" [bool, T"i32" "words" []]]]],
          T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
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
                T"cart" "fcp" [bool, T"i32" "words" []]]]],
          T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]]] -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]],
           T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]]] --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]] -->
       (T"prod" "pair"
         [T"prod" "pair"
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
                T"cart" "fcp" [bool, T"i32" "words" []]]]],
          T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
        T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]]] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]] -->
       (T"prod" "pair"
         [T"prod" "pair"
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
                T"cart" "fcp" [bool, T"i32" "words" []]]]],
          T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []],
            T"list" "list" [T"TEXP" "HSL" []]]] --> bool)) --> bool)),
   C"!" "bool" (((T"list" "list" [T"TEXP" "HSL" []] --> bool) --> bool)),
   V"srcL" (T"list" "list" [T"TEXP" "HSL" []]),
   V"dstL" (T"list" "list" [T"TEXP" "HSL" []]), V"src" (T"TEXP" "HSL" []),
   V"s0"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"dst" (T"TEXP" "HSL" []),
   V"s1"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"," "pair"
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
        [T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]]))),
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
   C"twrite" "HSL"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"TEXP" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i32" "words" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"," "pair"
    ((T"list" "list" [T"TEXP" "HSL" []] -->
      (T"list" "list" [T"TEXP" "HSL" []] -->
       T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]]))),
   C"CONS" "list"
    ((T"TEXP" "HSL" [] -->
      (T"list" "list" [T"TEXP" "HSL" []] -->
       T"list" "list" [T"TEXP" "HSL" []]))),
   V"transfer_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
        T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]]] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   V"a"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
       T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]]]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
      -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   V"v"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   V"v1"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   C"pair_case" "pair"
    (((T"prod" "pair"
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
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
      -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"pair_case" "pair"
    (((T"list" "list" [T"TEXP" "HSL" []] -->
       (T"list" "list" [T"TEXP" "HSL" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
      -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   V"v4" (T"list" "list" [T"TEXP" "HSL" []]),
   V"v5" (T"list" "list" [T"TEXP" "HSL" []]),
   C"list_case" "list"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      ((T"TEXP" "HSL" [] -->
        (T"list" "list" [T"TEXP" "HSL" []] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
       -->
       (T"list" "list" [T"TEXP" "HSL" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"I" "combin"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   V"v8" (T"TEXP" "HSL" []), V"v9" (T"list" "list" [T"TEXP" "HSL" []]),
   C"ARB" "bool"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"!" "bool"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool) --> bool)),
   V"x"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   V"x1"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   C"=" "min"
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
       bool))),
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
   V"hs"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"dst" (T"TREG" "HSL" []), V"src" (T"num" "num" []),
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
   V"dst" (T"num" "num" []), V"src" (T"TREG" "HSL" []),
   V"src" (T"TROC" "HSL" []), V"src1" (T"TROC" "HSL" []),
   V"src2" (T"TROC" "HSL" []),
   C"word_add" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_sub" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"src2_reg" (T"TROC" "HSL" []),
   C"word_mul" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_and" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_or" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_xor" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"src2_num" (T"cart" "fcp" [bool, T"i5" "words" []]),
   C"word_lsl" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"w2n" "words"
    ((T"cart" "fcp" [bool, T"i5" "words" []] --> T"num" "num" [])),
   C"word_lsr" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_asr" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_ror" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"empty_s" "HSL"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
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
   C"FEMPTY" "finite_map"
    (T"fmap" "finite_map"
      [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"FEMPTY" "finite_map"
    (T"fmap" "finite_map"
      [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"HSL_STRUCTURE" "HSL" [],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        -->
        (T"prod" "pair"
          [T"HSL_STRUCTURE" "HSL" [],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool)) --> bool) --> bool)),
   V"R"
    ((T"prod" "pair"
       [T"HSL_STRUCTURE" "HSL" [],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      (T"prod" "pair"
        [T"HSL_STRUCTURE" "HSL" [],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool))),
   C"=" "min"
    (((T"prod" "pair"
        [T"HSL_STRUCTURE" "HSL" [],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
      ((T"prod" "pair"
         [T"HSL_STRUCTURE" "HSL" [],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
       bool))),
   C"run_hsl_tupled_aux" "HSL"
    (((T"prod" "pair"
        [T"HSL_STRUCTURE" "HSL" [],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"HSL_STRUCTURE" "HSL" [],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)) -->
      (T"prod" "pair"
        [T"HSL_STRUCTURE" "HSL" [],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"HSL_STRUCTURE" "HSL" [],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"HSL_STRUCTURE" "HSL" [],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"HSL_STRUCTURE" "HSL" [],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
        -->
        (T"prod" "pair"
          [T"HSL_STRUCTURE" "HSL" [],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
       -->
       (T"prod" "pair"
         [T"HSL_STRUCTURE" "HSL" [],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   V"run_hsl_tupled"
    ((T"prod" "pair"
       [T"HSL_STRUCTURE" "HSL" [],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   V"a"
    (T"prod" "pair"
      [T"HSL_STRUCTURE" "HSL" [],
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"pair_case" "pair"
    (((T"HSL_STRUCTURE" "HSL" [] -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
      -->
      (T"prod" "pair"
        [T"HSL_STRUCTURE" "HSL" [],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   V"v" (T"HSL_STRUCTURE" "HSL" []),
   C"HSL_STRUCTURE_case" "HSL"
    (((T"list" "list" [T"TOPER" "HSL" []] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
      ((T"HSL_STRUCTURE" "HSL" [] -->
        (T"HSL_STRUCTURE" "HSL" [] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
       -->
       ((T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] -->
          (T"HSL_STRUCTURE" "HSL" [] -->
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]))) -->
        ((T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
          (T"HSL_STRUCTURE" "HSL" [] -->
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
         -->
         ((T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]] -->
           (T"HSL_STRUCTURE" "HSL" [] -->
            (T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]] -->
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"TREG" "HSL" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]))) -->
          (T"HSL_STRUCTURE" "HSL" [] -->
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]))))))),
   V"v2" (T"list" "list" [T"TOPER" "HSL" []]),
   C"list_case" "list"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      ((T"TOPER" "HSL" [] -->
        (T"list" "list" [T"TOPER" "HSL" []] -->
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
       -->
       (T"list" "list" [T"TOPER" "HSL" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   V"stm" (T"TOPER" "HSL" []),
   V"stmL" (T"list" "list" [T"TOPER" "HSL" []]),
   C"," "pair"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"HSL_STRUCTURE" "HSL" [],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
   V"S1" (T"HSL_STRUCTURE" "HSL" []), V"S2" (T"HSL_STRUCTURE" "HSL" []),
   V"cond"
    (T"prod" "pair"
      [T"TREG" "HSL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]]),
   V"S1'" (T"HSL_STRUCTURE" "HSL" []), V"S2'" (T"HSL_STRUCTURE" "HSL" []),
   C"COND" "bool"
    ((bool -->
      (T"prod" "pair"
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
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   V"cond'"
    (T"prod" "pair"
      [T"TREG" "HSL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]]),
   V"S1''" (T"HSL_STRUCTURE" "HSL" []),
   C"WHILE" "while"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   V"s'"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"a"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"v10"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   V"S_hsl" (T"HSL_STRUCTURE" "HSL" []),
   V"v12"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   V"caller_i" (T"list" "list" [T"TEXP" "HSL" []]),
   V"callee_i" (T"list" "list" [T"TEXP" "HSL" []]),
   V"caller_o" (T"list" "list" [T"TEXP" "HSL" []]),
   V"callee_o" (T"list" "list" [T"TEXP" "HSL" []]),
   C"LET" "bool"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
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
   V"s2"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"run_hsl_tupled" "HSL"
    ((T"prod" "pair"
       [T"HSL_STRUCTURE" "HSL" [],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"@" "min"
    ((((T"prod" "pair"
         [T"HSL_STRUCTURE" "HSL" [],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        -->
        (T"prod" "pair"
          [T"HSL_STRUCTURE" "HSL" [],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"HSL_STRUCTURE" "HSL" [],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"HSL_STRUCTURE" "HSL" [],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"HSL_STRUCTURE" "HSL" [],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"HSL_STRUCTURE" "HSL" [],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)) --> bool)),
   C"CONS" "list"
    ((T"TOPER" "HSL" [] -->
      (T"list" "list" [T"TOPER" "HSL" []] -->
       T"list" "list" [T"TOPER" "HSL" []]))),
   V"x" (T"HSL_STRUCTURE" "HSL" []),
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
   V"bound" (T"num" "num" []),
   C"within_bound" "HSL"
    ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"valid_TEXP" "HSL" ((T"TEXP" "HSL" [] --> (T"num" "num" [] --> bool))),
   C"=" "min"
    (((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool) -->
      ((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool) -->
       bool))),
   C"valid_assgn_tupled" "HSL"
    ((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool)),
   C"WFREC" "relation"
    (((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] -->
       (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool)) -->
      (((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool) -->
        (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool)) -->
       (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool)))),
   C"@" "min"
    ((((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] -->
        (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool)) -->
       bool) -->
      (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] -->
       (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool)))),
   V"R"
    ((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] -->
      (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] -->
       (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool)) -->
      bool)),
   V"valid_assgn_tupled"
    ((T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool)),
   V"a" (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []]),
   C"pair_case" "pair"
    (((T"TOPER" "HSL" [] --> (T"num" "num" [] --> bool)) -->
      (T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []] --> bool))),
   V"v" (T"TOPER" "HSL" []),
   C"TOPER_case" "HSL"
    (((T"TREG" "HSL" [] --> (T"num" "num" [] --> bool)) -->
      ((T"num" "num" [] --> (T"TREG" "HSL" [] --> bool)) -->
       ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> bool)) -->
        ((T"TREG" "HSL" [] -->
          (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> bool))) -->
         ((T"TREG" "HSL" [] -->
           (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> bool))) -->
          ((T"TREG" "HSL" [] -->
            (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> bool))) -->
           ((T"TREG" "HSL" [] -->
             (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> bool))) -->
            ((T"TREG" "HSL" [] -->
              (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> bool))) -->
             ((T"TREG" "HSL" [] -->
               (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> bool))) -->
              ((T"TREG" "HSL" [] -->
                (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> bool))) -->
               ((T"TREG" "HSL" [] -->
                 (T"TROC" "HSL" [] -->
                  (T"cart" "fcp" [bool, T"i5" "words" []] --> bool))) -->
                ((T"TREG" "HSL" [] -->
                  (T"TROC" "HSL" [] -->
                   (T"cart" "fcp" [bool, T"i5" "words" []] --> bool))) -->
                 ((T"TREG" "HSL" [] -->
                   (T"TROC" "HSL" [] -->
                    (T"cart" "fcp" [bool, T"i5" "words" []] --> bool))) -->
                  ((T"TREG" "HSL" [] -->
                    (T"TROC" "HSL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] --> bool)))
                   --> (T"TOPER" "HSL" [] --> bool)))))))))))))))),
   V"m'" (T"num" "num" []), V"r'" (T"TREG" "HSL" []),
   V"v45" (T"TREG" "HSL" []), V"v46" (T"TROC" "HSL" []),
   V"v47" (T"TREG" "HSL" []), V"v48" (T"TROC" "HSL" []),
   V"v49" (T"TROC" "HSL" []), V"v50" (T"TREG" "HSL" []),
   V"v51" (T"TROC" "HSL" []), V"v52" (T"TROC" "HSL" []),
   V"v53" (T"TREG" "HSL" []), V"v54" (T"TROC" "HSL" []),
   V"v55" (T"TROC" "HSL" []), V"v56" (T"TREG" "HSL" []),
   V"v57" (T"TROC" "HSL" []), V"v58" (T"TROC" "HSL" []),
   V"v59" (T"TREG" "HSL" []), V"v60" (T"TROC" "HSL" []),
   V"v61" (T"TROC" "HSL" []), V"v62" (T"TREG" "HSL" []),
   V"v63" (T"TROC" "HSL" []), V"v64" (T"TROC" "HSL" []),
   V"v65" (T"TREG" "HSL" []), V"v66" (T"TROC" "HSL" []),
   V"v67" (T"TROC" "HSL" []), V"v68" (T"TREG" "HSL" []),
   V"v69" (T"TROC" "HSL" []),
   V"v70" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"v71" (T"TREG" "HSL" []), V"v72" (T"TROC" "HSL" []),
   V"v73" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"v74" (T"TREG" "HSL" []), V"v75" (T"TROC" "HSL" []),
   V"v76" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"v77" (T"TREG" "HSL" []), V"v78" (T"TROC" "HSL" []),
   V"v79" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"x" (T"TOPER" "HSL" []), V"x1" (T"num" "num" []),
   C"valid_assgn" "HSL"
    ((T"TOPER" "HSL" [] --> (T"num" "num" [] --> bool))),
   C"," "pair"
    ((T"TOPER" "HSL" [] -->
      (T"num" "num" [] -->
       T"prod" "pair" [T"TOPER" "HSL" [], T"num" "num" []]))),
   C"valid_struct" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] --> (T"num" "num" [] --> bool))),
   C"EVERY" "list"
    (((T"TOPER" "HSL" [] --> bool) -->
      (T"list" "list" [T"TOPER" "HSL" []] --> bool))),
   V"S_t" (T"HSL_STRUCTURE" "HSL" []), V"S_f" (T"HSL_STRUCTURE" "HSL" []),
   V"S_body" (T"HSL_STRUCTURE" "HSL" []),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        alpha) --> bool) --> bool)),
   V"in_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      alpha)), C"!" "bool" ((((alpha --> beta) --> bool) --> bool)),
   V"acf" ((alpha --> beta)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        beta) --> bool) --> bool)),
   V"out_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      beta)),
   C"CSPEC" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha),
         T"prod" "pair"
          [(alpha --> beta),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> beta)]] --> bool))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       alpha) -->
      (T"prod" "pair"
        [(alpha --> beta),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta)] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha),
         T"prod" "pair"
          [(alpha --> beta),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> beta)]]))),
   C"," "pair"
    (((alpha --> beta) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        beta) -->
       T"prod" "pair"
        [(alpha --> beta),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta)]))), C"=" "min" ((beta --> (beta --> bool))),
   V"h" (alpha),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"l" (T"list" "list" [alpha]),
   C"unique_list" "HSL" ((T"list" "list" [alpha] --> bool)),
   C"CONS" "list"
    ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"EVERY" "list"
    (((alpha --> bool) --> (T"list" "list" [alpha] --> bool))),
   V"x" (alpha), C"NIL" "list" (T"list" "list" [alpha]),
   C"=" "min"
    (((T"TEXP" "HSL" [] --> bool) -->
      ((T"TEXP" "HSL" [] --> bool) --> bool))),
   C"notC" "HSL" ((T"TEXP" "HSL" [] --> bool)),
   C"WFREC" "relation"
    (((T"TEXP" "HSL" [] --> (T"TEXP" "HSL" [] --> bool)) -->
      (((T"TEXP" "HSL" [] --> bool) --> (T"TEXP" "HSL" [] --> bool)) -->
       (T"TEXP" "HSL" [] --> bool)))),
   C"@" "min"
    ((((T"TEXP" "HSL" [] --> (T"TEXP" "HSL" [] --> bool)) --> bool) -->
      (T"TEXP" "HSL" [] --> (T"TEXP" "HSL" [] --> bool)))),
   V"R" ((T"TEXP" "HSL" [] --> (T"TEXP" "HSL" [] --> bool))),
   C"WF" "relation"
    (((T"TEXP" "HSL" [] --> (T"TEXP" "HSL" [] --> bool)) --> bool)),
   V"notC" ((T"TEXP" "HSL" [] --> bool)),
   C"TEXP_case" "HSL"
    (((T"TREG" "HSL" [] --> bool) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) -->
       ((T"num" "num" [] --> bool) --> (T"TEXP" "HSL" [] --> bool))))),
   V"v3" (T"TREG" "HSL" []),
   V"c" (T"cart" "fcp" [bool, T"i32" "words" []]), V"v5" (T"num" "num" []),
   V"f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      alpha)), V"lst" (T"list" "list" [T"TEXP" "HSL" []]),
   C"!" "bool"
    ((((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] --> alpha)
       --> bool) --> bool)),
   V"g"
    ((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] --> alpha)),
   C"match" "HSL"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       alpha) -->
      (T"list" "list" [T"TEXP" "HSL" []] -->
       ((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
         alpha) --> bool)))),
   C"MAP" "list"
    (((T"TEXP" "HSL" [] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
      (T"list" "list" [T"TEXP" "HSL" []] -->
       T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]]))),
   V"caller_i" (T"list" "list" [alpha]),
   C"!" "bool" (((T"list" "list" [beta] --> bool) --> bool)),
   V"callee_o" (T"list" "list" [beta]),
   C"valid_arg_list" "HSL"
    ((T"prod" "pair"
       [T"list" "list" [alpha],
        T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"prod" "pair"
           [T"list" "list" [T"TEXP" "HSL" []], T"list" "list" [beta]]]] -->
      bool)),
   C"," "pair"
    ((T"list" "list" [alpha] -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []], T"list" "list" [beta]]] -->
       T"prod" "pair"
        [T"list" "list" [alpha],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [beta]]]]))),
   C"," "pair"
    ((T"list" "list" [T"TEXP" "HSL" []] -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []], T"list" "list" [beta]] -->
       T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []], T"list" "list" [beta]]]))),
   C"," "pair"
    ((T"list" "list" [T"TEXP" "HSL" []] -->
      (T"list" "list" [beta] -->
       T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []], T"list" "list" [beta]]))),
   C"unique_list" "HSL" ((T"list" "list" [T"TEXP" "HSL" []] --> bool)),
   C"LENGTH" "list" ((T"list" "list" [alpha] --> T"num" "num" [])),
   C"LENGTH" "list"
    ((T"list" "list" [T"TEXP" "HSL" []] --> T"num" "num" [])),
   C"LENGTH" "list" ((T"list" "list" [beta] --> T"num" "num" [])),
   C"EVERY" "list"
    (((T"TEXP" "HSL" [] --> bool) -->
      (T"list" "list" [T"TEXP" "HSL" []] --> bool))),
   V"r'" (T"num" "num" []), V"a'" (T"PTR" "HSL" []),
   C"?" "bool" (((T"PTR" "HSL" [] --> bool) --> bool)),
   C"DATATYPE" "bool" ((bool --> bool)),
   V"PTR"
    ((T"PTR" "HSL" [] -->
      (T"PTR" "HSL" [] -->
       (T"PTR" "HSL" [] -->
        (T"PTR" "HSL" [] -->
         (T"PTR" "HSL" [] --> (T"PTR" "HSL" [] --> bool))))))),
   V"M" (T"PTR" "HSL" []), V"M'" (T"PTR" "HSL" []), V"v0'" (alpha),
   V"v1'" (alpha), V"v2'" (alpha), V"v3'" (alpha), V"v4'" (alpha),
   V"v5'" (alpha), V"x0" (alpha), V"x1" (alpha), V"x3" (alpha),
   V"x4" (alpha), V"x5" (alpha),
   C"?" "bool" ((((T"PTR" "HSL" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"PTR" "HSL" [] --> alpha)),
   C"!" "bool" ((((T"PTR" "HSL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"PTR" "HSL" [] --> bool)), V"p" (T"PTR" "HSL" []),
   V"a'" (T"TREG" "HSL" []),
   V"TREG"
    ((T"TREG" "HSL" [] -->
      (T"TREG" "HSL" [] -->
       (T"TREG" "HSL" [] -->
        (T"TREG" "HSL" [] -->
         (T"TREG" "HSL" [] -->
          (T"TREG" "HSL" [] -->
           (T"TREG" "HSL" [] -->
            (T"TREG" "HSL" [] --> (T"TREG" "HSL" [] --> bool)))))))))),
   V"M" (T"TREG" "HSL" []), V"M'" (T"TREG" "HSL" []), V"v6'" (alpha),
   V"v7'" (alpha), V"v8'" (alpha), V"x6" (alpha), V"x7" (alpha),
   V"x8" (alpha),
   C"?" "bool" ((((T"TREG" "HSL" [] --> alpha) --> bool) --> bool)),
   C"!" "bool" ((((T"TREG" "HSL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"TREG" "HSL" [] --> bool)),
   C"=" "min" ((T"MREG" "CFL" [] --> (T"MREG" "CFL" [] --> bool))),
   C"R0" "CFL" (T"MREG" "CFL" []), C"R1" "CFL" (T"MREG" "CFL" []),
   C"R2" "CFL" (T"MREG" "CFL" []), C"R3" "CFL" (T"MREG" "CFL" []),
   C"R4" "CFL" (T"MREG" "CFL" []), C"R5" "CFL" (T"MREG" "CFL" []),
   C"R6" "CFL" (T"MREG" "CFL" []), C"R7" "CFL" (T"MREG" "CFL" []),
   C"R8" "CFL" (T"MREG" "CFL" []),
   V"P"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   C"!" "bool"
    (((T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool) --> bool)),
   C"!" "bool"
    (((T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool) --> bool)),
   V"TEXP"
    (((T"TREG" "HSL" [] --> T"TEXP" "HSL" []) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TEXP" "HSL" []) -->
       ((T"num" "num" [] --> T"TEXP" "HSL" []) --> bool)))),
   V"a'" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"a'" (T"num" "num" []), V"M" (T"TEXP" "HSL" []),
   V"M'" (T"TEXP" "HSL" []), V"f'" ((T"TREG" "HSL" [] --> alpha)),
   V"f1'" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   V"f2'" ((T"num" "num" [] --> alpha)), V"T" (T"TEXP" "HSL" []),
   V"T" (T"TREG" "HSL" []), V"f0" ((T"TREG" "HSL" [] --> alpha)),
   C"?" "bool" ((((T"TEXP" "HSL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"TEXP" "HSL" [] --> alpha)),
   C"!" "bool" ((((T"TEXP" "HSL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"TEXP" "HSL" [] --> bool)),
   V"TROC"
    (((T"TREG" "HSL" [] --> T"TROC" "HSL" []) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"TROC" "HSL" []) -->
       bool))), V"M" (T"TROC" "HSL" []), V"M'" (T"TROC" "HSL" []),
   V"T" (T"TROC" "HSL" []),
   C"?" "bool" ((((T"TROC" "HSL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"TROC" "HSL" [] --> alpha)),
   C"!" "bool" ((((T"TROC" "HSL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"TROC" "HSL" [] --> bool)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        (T"TEXP" "HSL" [] --> bool)) --> bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"TEXP" "HSL" [] --> bool))),
   V"v"
    (T"fmap" "finite_map"
      [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   V"v1"
    (T"fmap" "finite_map"
      [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
          T"fmap" "finite_map" [T"num" "num" [], alpha]] -->
        (T"TEXP" "HSL" [] --> (alpha --> bool))) --> bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"fmap" "finite_map" [T"TREG" "HSL" [], alpha],
        T"fmap" "finite_map" [T"num" "num" [], alpha]] -->
      (T"TEXP" "HSL" [] --> (alpha --> bool)))),
   C"!" "bool"
    (((T"fmap" "finite_map" [T"TREG" "HSL" [], alpha] --> bool) --> bool)),
   C"!" "bool"
    (((T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool) --> bool)),
   V"v" (T"fmap" "finite_map" [T"TREG" "HSL" [], alpha]),
   V"v1" (T"fmap" "finite_map" [T"num" "num" [], alpha]),
   V"TOPER"
    (((T"TREG" "HSL" [] --> (T"num" "num" [] --> T"TOPER" "HSL" [])) -->
      ((T"num" "num" [] --> (T"TREG" "HSL" [] --> T"TOPER" "HSL" [])) -->
       ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])) -->
        ((T"TREG" "HSL" [] -->
          (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))
         -->
         ((T"TREG" "HSL" [] -->
           (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> T"TOPER" "HSL" [])))
          -->
          ((T"TREG" "HSL" [] -->
            (T"TROC" "HSL" [] -->
             (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))) -->
           ((T"TREG" "HSL" [] -->
             (T"TROC" "HSL" [] -->
              (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))) -->
            ((T"TREG" "HSL" [] -->
              (T"TROC" "HSL" [] -->
               (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))) -->
             ((T"TREG" "HSL" [] -->
               (T"TROC" "HSL" [] -->
                (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))) -->
              ((T"TREG" "HSL" [] -->
                (T"TROC" "HSL" [] -->
                 (T"TROC" "HSL" [] --> T"TOPER" "HSL" []))) -->
               ((T"TREG" "HSL" [] -->
                 (T"TROC" "HSL" [] -->
                  (T"cart" "fcp" [bool, T"i5" "words" []] -->
                   T"TOPER" "HSL" []))) -->
                ((T"TREG" "HSL" [] -->
                  (T"TROC" "HSL" [] -->
                   (T"cart" "fcp" [bool, T"i5" "words" []] -->
                    T"TOPER" "HSL" []))) -->
                 ((T"TREG" "HSL" [] -->
                   (T"TROC" "HSL" [] -->
                    (T"cart" "fcp" [bool, T"i5" "words" []] -->
                     T"TOPER" "HSL" []))) -->
                  ((T"TREG" "HSL" [] -->
                    (T"TROC" "HSL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] -->
                      T"TOPER" "HSL" []))) --> bool))))))))))))))),
   V"a0'" (T"TREG" "HSL" []), V"a1'" (T"num" "num" []),
   V"a0'" (T"num" "num" []), V"a1'" (T"TREG" "HSL" []),
   V"a1'" (T"TROC" "HSL" []), V"a2'" (T"TROC" "HSL" []),
   V"a2'" (T"cart" "fcp" [bool, T"i5" "words" []]),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i5" "words" []] -->
      (T"cart" "fcp" [bool, T"i5" "words" []] --> bool))),
   V"M" (T"TOPER" "HSL" []), V"M'" (T"TOPER" "HSL" []),
   V"f'" ((T"TREG" "HSL" [] --> (T"num" "num" [] --> alpha))),
   V"f1'" ((T"num" "num" [] --> (T"TREG" "HSL" [] --> alpha))),
   V"f2'" ((T"TREG" "HSL" [] --> (T"TROC" "HSL" [] --> alpha))),
   V"f3'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f4'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f5'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f6'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f7'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f8'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f9'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] --> (T"TROC" "HSL" [] --> alpha)))),
   V"f10'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f11'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f12'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f13'"
    ((T"TREG" "HSL" [] -->
      (T"TROC" "HSL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"T" (T"TOPER" "HSL" []), V"T0" (T"TROC" "HSL" []),
   V"T1" (T"TROC" "HSL" []), V"c" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"f0" ((T"TREG" "HSL" [] --> (T"num" "num" [] --> alpha))),
   C"?" "bool" ((((T"TOPER" "HSL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"TOPER" "HSL" [] --> alpha)),
   C"!" "bool" ((((T"TOPER" "HSL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"TOPER" "HSL" [] --> bool)),
   V"HSL_STRUCTURE"
    (((T"list" "list" [T"TOPER" "HSL" []] --> T"HSL_STRUCTURE" "HSL" [])
      -->
      ((T"HSL_STRUCTURE" "HSL" [] -->
        (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])) -->
       ((T"prod" "pair"
          [T"TREG" "HSL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] -->
          (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" []))) -->
        ((T"prod" "pair"
           [T"TREG" "HSL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
          (T"HSL_STRUCTURE" "HSL" [] --> T"HSL_STRUCTURE" "HSL" [])) -->
         ((T"prod" "pair"
            [T"list" "list" [T"TEXP" "HSL" []],
             T"list" "list" [T"TEXP" "HSL" []]] -->
           (T"HSL_STRUCTURE" "HSL" [] -->
            (T"prod" "pair"
              [T"list" "list" [T"TEXP" "HSL" []],
               T"list" "list" [T"TEXP" "HSL" []]] -->
             T"HSL_STRUCTURE" "HSL" []))) --> bool)))))),
   V"a'" (T"list" "list" [T"TOPER" "HSL" []]),
   C"=" "min"
    ((T"list" "list" [T"TOPER" "HSL" []] -->
      (T"list" "list" [T"TOPER" "HSL" []] --> bool))),
   V"a0'" (T"HSL_STRUCTURE" "HSL" []), V"a1'" (T"HSL_STRUCTURE" "HSL" []),
   V"a0'"
    (T"prod" "pair"
      [T"TREG" "HSL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]]),
   V"a2'" (T"HSL_STRUCTURE" "HSL" []),
   C"=" "min"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
       bool))),
   V"a0'"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   V"a2'"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   C"=" "min"
    ((T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"list" "list" [T"TEXP" "HSL" []]] -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] --> bool))),
   V"M" (T"HSL_STRUCTURE" "HSL" []), V"M'" (T"HSL_STRUCTURE" "HSL" []),
   V"f'" ((T"list" "list" [T"TOPER" "HSL" []] --> alpha)),
   V"f1'"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"HSL_STRUCTURE" "HSL" [] --> alpha))),
   V"f2'"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"HSL_STRUCTURE" "HSL" [] --> alpha)))),
   V"f3'"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] --> alpha))),
   V"f4'"
    ((T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"list" "list" [T"TEXP" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]] --> alpha)))),
   V"H" (T"HSL_STRUCTURE" "HSL" []),
   V"l" (T"list" "list" [T"TOPER" "HSL" []]),
   C"?" "bool" (((T"HSL_STRUCTURE" "HSL" [] --> bool) --> bool)),
   V"H0" (T"HSL_STRUCTURE" "HSL" []),
   V"p"
    (T"prod" "pair"
      [T"TREG" "HSL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]]),
   V"p0"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   V"p"
    (T"prod" "pair"
      [T"list" "list" [T"TEXP" "HSL" []],
       T"list" "list" [T"TEXP" "HSL" []]]),
   V"f0" ((T"list" "list" [T"TOPER" "HSL" []] --> alpha)),
   C"!" "bool"
    ((((T"HSL_STRUCTURE" "HSL" [] -->
        (T"HSL_STRUCTURE" "HSL" [] --> (alpha --> (alpha --> alpha)))) -->
       bool) --> bool)),
   V"f1"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"HSL_STRUCTURE" "HSL" [] --> (alpha --> (alpha --> alpha))))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
        (T"HSL_STRUCTURE" "HSL" [] -->
         (T"HSL_STRUCTURE" "HSL" [] --> (alpha --> (alpha --> alpha)))))
       --> bool) --> bool)),
   V"f2"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] -->
       (T"HSL_STRUCTURE" "HSL" [] --> (alpha --> (alpha --> alpha)))))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
        (T"HSL_STRUCTURE" "HSL" [] --> (alpha --> alpha))) --> bool) -->
      bool)),
   V"f3"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"HSL_STRUCTURE" "HSL" [] --> (alpha --> alpha)))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"list" "list" [T"TEXP" "HSL" []],
          T"list" "list" [T"TEXP" "HSL" []]] -->
        (T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]] -->
         (T"HSL_STRUCTURE" "HSL" [] --> (alpha --> alpha)))) --> bool) -->
      bool)),
   V"f4"
    ((T"prod" "pair"
       [T"list" "list" [T"TEXP" "HSL" []],
        T"list" "list" [T"TEXP" "HSL" []]] -->
      (T"prod" "pair"
        [T"list" "list" [T"TEXP" "HSL" []],
         T"list" "list" [T"TEXP" "HSL" []]] -->
       (T"HSL_STRUCTURE" "HSL" [] --> (alpha --> alpha))))),
   C"?" "bool"
    ((((T"HSL_STRUCTURE" "HSL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"HSL_STRUCTURE" "HSL" [] --> alpha)),
   C"!" "bool"
    ((((T"HSL_STRUCTURE" "HSL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"HSL_STRUCTURE" "HSL" [] --> bool)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"TREG" "HSL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
        (T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         bool)) --> bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"TREG" "HSL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   C"," "pair"
    ((T"TREG" "HSL" [] -->
      (T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []] -->
       T"prod" "pair"
        [T"TREG" "HSL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]]))),
   C"," "pair"
    ((T"COND" "preARM" [] -->
      (T"TROC" "HSL" [] -->
       T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]))),
   C"EQ" "preARM" (T"COND" "preARM" []),
   C"CS" "preARM" (T"COND" "preARM" []),
   C"MI" "preARM" (T"COND" "preARM" []),
   C"VS" "preARM" (T"COND" "preARM" []),
   C"HI" "preARM" (T"COND" "preARM" []),
   C"GE" "preARM" (T"COND" "preARM" []),
   C"GT" "preARM" (T"COND" "preARM" []),
   C"AL" "preARM" (T"COND" "preARM" []),
   C"NE" "preARM" (T"COND" "preARM" []),
   C"CC" "preARM" (T"COND" "preARM" []),
   C"PL" "preARM" (T"COND" "preARM" []),
   C"VC" "preARM" (T"COND" "preARM" []),
   C"LS" "preARM" (T"COND" "preARM" []),
   C"LT" "preARM" (T"COND" "preARM" []),
   C"LE" "preARM" (T"COND" "preARM" []),
   C"NV" "preARM" (T"COND" "preARM" []),
   C"!" "bool" (((T"COND" "preARM" [] --> bool) --> bool)),
   V"v1" (T"COND" "preARM" []),
   V"v3"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        -->
        (T"prod" "pair"
          [T"list" "list" [T"TEXP" "HSL" []],
           T"list" "list" [T"TEXP" "HSL" []]] --> bool)) --> bool) -->
      bool)),
   V"P"
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
         T"list" "list" [T"TEXP" "HSL" []]] --> bool))),
   C"NIL" "list" (T"list" "list" [T"TEXP" "HSL" []]),
   V"v10" (T"TEXP" "HSL" []), V"v11" (T"list" "list" [T"TEXP" "HSL" []]),
   V"v"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"v2" (T"list" "list" [T"TEXP" "HSL" []]),
   V"v3" (T"list" "list" [T"TEXP" "HSL" []]),
   C"!" "bool"
    ((((T"HSL_STRUCTURE" "HSL" [] -->
        (T"prod" "pair"
          [T"fmap" "finite_map"
            [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         bool)) --> bool) --> bool)),
   V"P"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))), C"NIL" "list" (T"list" "list" [T"TOPER" "HSL" []]),
   C"!" "bool"
    ((((T"TOPER" "HSL" [] --> (T"num" "num" [] --> bool)) --> bool) -->
      bool)), V"P" ((T"TOPER" "HSL" [] --> (T"num" "num" [] --> bool))),
   V"v38" (T"TREG" "HSL" []), V"v39" (T"TROC" "HSL" []),
   V"v40" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"v35" (T"TREG" "HSL" []), V"v36" (T"TROC" "HSL" []),
   V"v37" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"v32" (T"TREG" "HSL" []), V"v33" (T"TROC" "HSL" []),
   V"v34" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"v29" (T"TREG" "HSL" []), V"v30" (T"TROC" "HSL" []),
   V"v31" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"v26" (T"TREG" "HSL" []), V"v27" (T"TROC" "HSL" []),
   V"v28" (T"TROC" "HSL" []), V"v23" (T"TREG" "HSL" []),
   V"v24" (T"TROC" "HSL" []), V"v25" (T"TROC" "HSL" []),
   V"v20" (T"TREG" "HSL" []), V"v21" (T"TROC" "HSL" []),
   V"v22" (T"TROC" "HSL" []), V"v17" (T"TREG" "HSL" []),
   V"v18" (T"TROC" "HSL" []), V"v19" (T"TROC" "HSL" []),
   V"v14" (T"TREG" "HSL" []), V"v15" (T"TROC" "HSL" []),
   V"v16" (T"TROC" "HSL" []), V"v11" (T"TREG" "HSL" []),
   V"v12" (T"TROC" "HSL" []), V"v13" (T"TROC" "HSL" []),
   V"v8" (T"TREG" "HSL" []), V"v9" (T"TROC" "HSL" []),
   V"v10" (T"TROC" "HSL" []), V"v6" (T"TREG" "HSL" []),
   V"v7" (T"TROC" "HSL" []), V"v1" (T"num" "num" []),
   V"in_f1"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      alpha)), V"f1" ((alpha --> beta)),
   C"!" "bool" ((((beta --> gamma) --> bool) --> bool)),
   V"f2" ((beta --> gamma)),
   V"out_f1"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      beta)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma) --> bool) --> bool)),
   V"out_f2"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      gamma)),
   C"CSPEC" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta),
         T"prod" "pair"
          [(beta --> gamma),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> gamma)]] --> bool))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       beta) -->
      (T"prod" "pair"
        [(beta --> gamma),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> gamma)] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> beta),
         T"prod" "pair"
          [(beta --> gamma),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> gamma)]]))),
   C"," "pair"
    (((beta --> gamma) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma) -->
       T"prod" "pair"
        [(beta --> gamma),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> gamma)]))),
   C"CSPEC" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha),
         T"prod" "pair"
          [(alpha --> gamma),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> gamma)]] --> bool))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       alpha) -->
      (T"prod" "pair"
        [(alpha --> gamma),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> gamma)] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha),
         T"prod" "pair"
          [(alpha --> gamma),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> gamma)]]))),
   C"," "pair"
    (((alpha --> gamma) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        gamma) -->
       T"prod" "pair"
        [(alpha --> gamma),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> gamma)]))),
   C"sc" "ACF"
    (((alpha --> beta) --> ((beta --> gamma) --> (alpha --> gamma)))),
   V"St" (T"HSL_STRUCTURE" "HSL" []), V"Sf" (T"HSL_STRUCTURE" "HSL" []),
   C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"cond_f" ((alpha --> bool)), V"f2" ((alpha --> beta)),
   C"cj" "ACF"
    (((alpha --> bool) -->
      ((alpha --> beta) --> ((alpha --> beta) --> (alpha --> beta))))),
   C"WF" "relation" (((alpha --> (alpha --> bool)) --> bool)),
   V"R" ((alpha --> (alpha --> bool))), V"P" ((alpha --> bool)),
   C"?" "bool" (((alpha --> bool) --> bool)), V"w" (alpha), V"min" (alpha),
   V"b" (alpha),
   V"prj_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      alpha)), C"!" "bool" ((((alpha --> alpha) --> bool) --> bool)),
   V"f" ((alpha --> alpha)), V"t1" (alpha), V"t0" (alpha),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool)) --> bool)),
   C"?" "bool" ((((alpha --> (alpha --> bool)) --> bool) --> bool)),
   C"CSPEC" "HSL"
    ((T"HSL_STRUCTURE" "HSL" [] -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha),
         T"prod" "pair"
          [(alpha --> alpha),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> alpha)]] --> bool))),
   C"," "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       alpha) -->
      (T"prod" "pair"
        [(alpha --> alpha),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha)] -->
       T"prod" "pair"
        [(T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha),
         T"prod" "pair"
          [(alpha --> alpha),
           (T"prod" "pair"
             [T"fmap" "finite_map"
               [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
            --> alpha)]]))),
   C"," "pair"
    (((alpha --> alpha) -->
      ((T"prod" "pair"
         [T"fmap" "finite_map"
           [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        alpha) -->
       T"prod" "pair"
        [(alpha --> alpha),
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> alpha)]))),
   C"tr" "ACF"
    (((alpha --> bool) --> ((alpha --> alpha) --> (alpha --> alpha)))),
   V"v2" (T"num" "num" []), V"v" (T"TEXP" "HSL" []),
   V"h" (T"TEXP" "HSL" []),
   C"=" "min"
    ((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool))), V"x" (T"TEXP" "HSL" []),
   C"MEM" "list"
    ((T"TEXP" "HSL" [] --> (T"list" "list" [T"TEXP" "HSL" []] --> bool))),
   V"f" ((alpha --> beta)),
   V"caller_i_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      alpha)),
   V"caller_o_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      beta)),
   V"callee_i_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      alpha)),
   V"callee_o_f"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      beta)),
   V"g1"
    ((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] --> alpha)),
   C"!" "bool"
    ((((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] --> beta)
       --> bool) --> bool)),
   V"g2"
    ((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] --> beta)),
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
   C"match" "HSL"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       beta) -->
      (T"list" "list" [T"TEXP" "HSL" []] -->
       ((T"list" "list" [T"cart" "fcp" [bool, T"i32" "words" []]] --> beta)
        --> bool))))]
  val DT = Thm.disk_thm share_table
  in
  val PTR_TY_DEF =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (\%3. ((%4 $0) (%5 (%6 (%6 %7)))))) $0)))`)
  val PTR_BIJ =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%10. ((%11 (%12 (%13 $0))) $0)))) (%14 (\%15. ((%16
       ((\%3. ((%4 $0) (%5 (%6 (%6 %7))))) $0)) ((%17 (%13 (%12 $0)))
       $0)))))`)
  val TTP = DT([], [], `((%11 %18) (%12 %19))`)
  val THP = DT([], [], `((%11 %20) (%12 (%5 (%21 %7))))`)
  val TFP = DT([], [], `((%11 %22) (%12 (%5 (%6 %7))))`)
  val TIP = DT([], [], `((%11 %23) (%12 (%5 (%21 (%21 %7)))))`)
  val TSP = DT([], [], `((%11 %24) (%12 (%5 (%6 (%21 %7)))))`)
  val TLR = DT([], [], `((%11 %25) (%12 (%5 (%21 (%6 %7)))))`)
  val PTR_size_def = DT([], [], `(%9 (\%26. ((%17 (%27 $0)) %19)))`)
  val PTR_case =
    DT([], [],
       `(%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33. (%28
       (\%34. (%9 (\%26. ((%35 (((((((%36 $6) $5) $4) $3) $2) $1) $0))
       ((\%37. (((%38 ((%4 $0) (%5 (%6 %7)))) (((%38 ((%17 $0) %19)) $7)
       $6)) (((%38 ((%4 $0) (%5 (%21 (%21 %7))))) $5) (((%38 ((%4 $0) (%5
       (%6 (%21 %7))))) $4) (((%38 ((%17 $0) (%5 (%6 (%21 %7))))) $3)
       $2))))) (%13 $0)))))))))))))))))`)
  val toPTR_def =
    DT(["DISK_THM"], [],
       `((%8 ((%17 (%39 %18)) %40)) ((%8 ((%17 (%39 %20)) %41)) ((%8 ((%17
       (%39 %22)) %42)) ((%8 ((%17 (%39 %23)) %43)) ((%8 ((%17 (%39 %24))
       %44)) ((%17 (%39 %25)) %45))))))`)
  val TREG_TY_DEF =
    DT(["DISK_THM"], [],
       `(%46 (\%47. ((%48 (\%3. ((%4 $0) (%5 (%21 (%6 (%21 %7)))))))
       $0)))`)
  val TREG_BIJ =
    DT(["DISK_THM"], [],
       `((%8 (%49 (\%50. ((%51 (%52 (%53 $0))) $0)))) (%14 (\%15. ((%16
       ((\%3. ((%4 $0) (%5 (%21 (%6 (%21 %7)))))) $0)) ((%17 (%53 (%52
       $0))) $0)))))`)
  val r0 = DT([], [], `((%51 %54) (%52 %19))`)
  val r1 = DT([], [], `((%51 %55) (%52 (%5 (%21 %7))))`)
  val r2 = DT([], [], `((%51 %56) (%52 (%5 (%6 %7))))`)
  val r3 = DT([], [], `((%51 %57) (%52 (%5 (%21 (%21 %7)))))`)
  val r4 = DT([], [], `((%51 %58) (%52 (%5 (%6 (%21 %7)))))`)
  val r5 = DT([], [], `((%51 %59) (%52 (%5 (%21 (%6 %7)))))`)
  val r6 = DT([], [], `((%51 %60) (%52 (%5 (%6 (%6 %7)))))`)
  val r7 = DT([], [], `((%51 %61) (%52 (%5 (%21 (%21 (%21 %7))))))`)
  val r8 = DT([], [], `((%51 %62) (%52 (%5 (%6 (%21 (%21 %7))))))`)
  val TREG_size_def = DT([], [], `(%49 (\%63. ((%17 (%64 $0)) %19)))`)
  val TREG_case =
    DT([], [],
       `(%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33. (%28
       (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. (%49 (\%63. ((%35
       ((((((((((%68 $9) $8) $7) $6) $5) $4) $3) $2) $1) $0)) ((\%37.
       (((%38 ((%4 $0) (%5 (%6 (%21 %7))))) (((%38 ((%4 $0) (%5 (%21 %7))))
       $10) (((%38 ((%4 $0) (%5 (%6 %7)))) $9) (((%38 ((%17 $0) (%5 (%6
       %7)))) $8) $7)))) (((%38 ((%4 $0) (%5 (%6 (%6 %7))))) (((%38 ((%17
       $0) (%5 (%6 (%21 %7))))) $6) $5)) (((%38 ((%4 $0) (%5 (%21 (%21 (%21
       %7)))))) $4) (((%38 ((%17 $0) (%5 (%21 (%21 (%21 %7)))))) $3)
       $2))))) (%53 $0)))))))))))))))))))))))`)
  val data_reg_index_def =
    DT(["DISK_THM"], [],
       `((%8 ((%17 (%69 %54)) %19)) ((%8 ((%17 (%69 %55)) (%5 (%21 %7))))
       ((%8 ((%17 (%69 %56)) (%5 (%6 %7)))) ((%8 ((%17 (%69 %57)) (%5 (%21
       (%21 %7))))) ((%8 ((%17 (%69 %58)) (%5 (%6 (%21 %7))))) ((%8 ((%17
       (%69 %59)) (%5 (%21 (%6 %7))))) ((%8 ((%17 (%69 %60)) (%5 (%6 (%6
       %7))))) ((%8 ((%17 (%69 %61)) (%5 (%21 (%21 (%21 %7)))))) ((%17 (%69
       %62)) (%5 (%6 (%21 (%21 %7)))))))))))))`)
  val data_reg_name_def =
    DT([], [],
       `(%14 (\%70. ((%51 (%71 $0)) (((%72 ((%17 $0) %19)) %54) (((%72
       ((%17 $0) (%5 (%21 %7)))) %55) (((%72 ((%17 $0) (%5 (%6 %7)))) %56)
       (((%72 ((%17 $0) (%5 (%21 (%21 %7))))) %57) (((%72 ((%17 $0) (%5 (%6
       (%21 %7))))) %58) (((%72 ((%17 $0) (%5 (%21 (%6 %7))))) %59) (((%72
       ((%17 $0) (%5 (%6 (%6 %7))))) %60) (((%72 ((%17 $0) (%5 (%21 (%21
       (%21 %7)))))) %61) %62)))))))))))`)
  val conv_reg_def = DT([], [], `((%73 %74) ((%75 %76) %69))`)
  val TEXP_TY_DEF =
    DT(["DISK_THM"], [],
       `(%77 (\%78. ((%79 (\%80. (%81 (\%82. ((%83 (%84 (\%80. ((%83 ((%85
       (%86 (\%50. ((%87 $1) ((\%50. (((%88 %19) ((%89 $0) ((%90 (%91
       (\%92. %93))) (%94 (\%95. %93))))) (\%3. %96))) $0))))) ((%85 (%97
       (\%98. ((%87 $1) ((\%98. (((%88 (%99 %19)) ((%89 (%100 (\%101.
       %93))) ((%90 $0) (%94 (\%95. %93))))) (\%3. %96))) $0))))) (%102
       (\%103. ((%87 $1) ((\%103. (((%88 (%99 (%99 %19))) ((%89 (%100
       (\%101. %93))) ((%90 (%91 (\%92. %93))) $0))) (\%3. %96))) $0)))))))
       ($1 $0))))) ($0 $1)))))) $0)))`)
  val TEXP_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%104 (\%105. ((%106 (%107 (%108 $0))) $0)))) (%84 (\%109.
       ((%16 ((\%80. (%81 (\%82. ((%83 (%84 (\%80. ((%83 ((%85 (%86 (\%50.
       ((%87 $1) ((\%50. (((%88 %19) ((%89 $0) ((%90 (%91 (\%92. %93)))
       (%94 (\%95. %93))))) (\%3. %96))) $0))))) ((%85 (%97 (\%98. ((%87
       $1) ((\%98. (((%88 (%99 %19)) ((%89 (%100 (\%101. %93))) ((%90 $0)
       (%94 (\%95. %93))))) (\%3. %96))) $0))))) (%102 (\%103. ((%87 $1)
       ((\%103. (((%88 (%99 (%99 %19))) ((%89 (%100 (\%101. %93))) ((%90
       (%91 (\%92. %93))) $0))) (\%3. %96))) $0))))))) ($1 $0))))) ($0
       $1))))) $0)) ((%87 (%108 (%107 $0))) $0)))))`)
  val HSL0_def =
    DT([], [],
       `((%110 %111) (\%50. (%107 ((\%50. (((%88 %19) ((%89 $0) ((%90 (%91
       (\%92. %93))) (%94 (\%95. %93))))) (\%3. %96))) $0))))`)
  val HSL1_def =
    DT([], [],
       `((%112 %113) (\%98. (%107 ((\%98. (((%88 (%99 %19)) ((%89 (%100
       (\%101. %93))) ((%90 $0) (%94 (\%95. %93))))) (\%3. %96))) $0))))`)
  val HSL2_def =
    DT([], [],
       `((%114 %115) (\%103. (%107 ((\%103. (((%88 (%99 (%99 %19))) ((%89
       (%100 (\%101. %93))) ((%90 (%91 (\%92. %93))) $0))) (\%3. %96)))
       $0))))`)
  val inR = DT([], [], `((%110 %116) %111)`)
  val inC = DT([], [], `((%112 %117) %113)`)
  val inE = DT([], [], `((%114 %118) %115)`)
  val TEXP_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%119 (\%120. (%121 (\%122. (%123 (\%124. (%49 (\%50. ((%35
       ((((%125 $3) $2) $1) (%116 $0))) ($3 $0))))))))))) ((%8 (%119
       (\%120. (%121 (\%122. (%123 (\%124. (%126 (\%98. ((%35 ((((%125 $3)
       $2) $1) (%117 $0))) ($2 $0))))))))))) (%119 (\%120. (%121 (\%122.
       (%123 (\%124. (%14 (\%103. ((%35 ((((%125 $3) $2) $1) (%118 $0)))
       ($1 $0))))))))))))`)
  val TEXP_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%49 (\%50. ((%17 (%127 (%116 $0))) ((%128 (%5 (%21 %7))) (%64
       $0)))))) ((%8 (%126 (\%98. ((%17 (%127 (%117 $0))) (%5 (%21 %7))))))
       (%14 (\%103. ((%17 (%127 (%118 $0))) ((%128 (%5 (%21 %7)))
       $0))))))`)
  val TROC_TY_DEF =
    DT(["DISK_THM"], [],
       `(%129 (\%130. ((%131 (\%132. (%133 (\%134. ((%83 (%135 (\%132.
       ((%83 ((%85 (%86 (\%50. ((%136 $1) ((\%50. (((%137 %19) ((%138 $0)
       (%91 (\%92. %93)))) (\%3. %139))) $0))))) (%97 (\%98. ((%136 $1)
       ((\%98. (((%137 (%99 %19)) ((%138 (%100 (\%101. %93))) $0)) (\%3.
       %139))) $0)))))) ($1 $0))))) ($0 $1)))))) $0)))`)
  val TROC_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%140 (\%141. ((%142 (%143 (%144 $0))) $0)))) (%135 (\%145.
       ((%16 ((\%132. (%133 (\%134. ((%83 (%135 (\%132. ((%83 ((%85 (%86
       (\%50. ((%136 $1) ((\%50. (((%137 %19) ((%138 $0) (%91 (\%92.
       %93)))) (\%3. %139))) $0))))) (%97 (\%98. ((%136 $1) ((\%98. (((%137
       (%99 %19)) ((%138 (%100 (\%101. %93))) $0)) (\%3. %139))) $0))))))
       ($1 $0))))) ($0 $1))))) $0)) ((%136 (%144 (%143 $0))) $0)))))`)
  val HSL3_def =
    DT([], [],
       `((%146 %147) (\%50. (%143 ((\%50. (((%137 %19) ((%138 $0) (%91
       (\%92. %93)))) (\%3. %139))) $0))))`)
  val HSL4_def =
    DT([], [],
       `((%148 %149) (\%98. (%143 ((\%98. (((%137 (%99 %19)) ((%138 (%100
       (\%101. %93))) $0)) (\%3. %139))) $0))))`)
  val Rg = DT([], [], `((%146 %150) %147)`)
  val Cn = DT([], [], `((%148 %151) %149)`)
  val TROC_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%119 (\%120. (%121 (\%122. (%49 (\%50. ((%35 (((%152 $2) $1)
       (%150 $0))) ($2 $0))))))))) (%119 (\%120. (%121 (\%122. (%126 (\%98.
       ((%35 (((%152 $2) $1) (%151 $0))) ($1 $0)))))))))`)
  val TROC_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%49 (\%50. ((%17 (%153 (%150 $0))) ((%128 (%5 (%21 %7))) (%64
       $0)))))) (%126 (\%98. ((%17 (%153 (%151 $0))) (%5 (%21 %7))))))`)
  val roc_2_exp_def =
    DT(["DISK_THM"], [],
       `((%8 (%49 (\%154. ((%106 (%155 (%150 $0))) (%116 $0))))) (%126
       (\%92. ((%106 (%155 (%151 $0))) (%117 $0)))))`)
  val tread_tupled_primitive_def =
    DT([], [],
       `((%156 %157) ((%158 (%159 (\%160. (%161 $0)))) (\%162. (\%163.
       ((%164 (\%165. (\%166. ((%167 (\%168. (\%169. ((((%170 (\%154. (%171
       ((%172 $2) $0)))) (\%92. (%171 $0))) (\%70. (%171 ((%173 $1) $0))))
       $2)))) $1)))) $0)))))`)
  val tread_curried_def =
    DT([], [],
       `(%174 (\%175. (%104 (\%176. ((%177 ((%178 $1) $0)) (%157 ((%179 $1)
       $0)))))))`)
  val twrite_tupled_primitive_def =
    DT([], [],
       `((%180 %181) ((%182 (%183 (\%184. (%185 $0)))) (\%186. (\%187.
       ((%188 (\%189. (\%190. ((%191 (\%192. (\%193. ((%194 (\%195. (\%196.
       ((((%197 (\%154. (%198 ((%199 ((%200 $4) ((%201 $0) $1))) $3))))
       (\%202. (%198 ((%199 $4) $3)))) (\%70. (%198 ((%199 $4) ((%203 $3)
       ((%204 $0) $1)))))) $1)))) $2)))) $1)))) $0)))))`)
  val twrite_curried_def =
    DT([], [],
       `(%205 (\%206. (%104 (\%176. (%28 (\%207. ((%208 (((%209 $2) $1)
       $0)) (%181 ((%210 $2) ((%211 $1) $0))))))))))`)
  val from_MEXP_def =
    DT(["DISK_THM"], [],
       `((%8 (%212 (\%213. ((%106 (%214 (%215 $0))) (%116 (%71 (%216
       $0))))))) (%126 (\%92. ((%106 (%214 (%217 $0))) (%117 $0)))))`)
  val TOPER_TY_DEF =
    DT(["DISK_THM"], [],
       `(%218 (\%219. ((%220 (\%221. (%222 (\%223. ((%83 (%224 (\%221.
       ((%83 ((%85 (%86 (\%225. (%102 (\%226. ((%227 $2) (((\%225. (\%226.
       (((%228 %19) ((%229 $1) ((%230 $0) ((%231 (%232 (\%233. %93)))
       ((%234 (%232 (\%233. %93))) (%235 (\%236. %93))))))) (\%3. %237))))
       $1) $0))))))) ((%85 (%102 (\%238. (%86 (\%239. ((%227 $2) (((\%238.
       (\%239. (((%228 (%99 %19)) ((%229 $0) ((%230 $1) ((%231 (%232
       (\%233. %93))) ((%234 (%232 (\%233. %93))) (%235 (\%236. %93)))))))
       (\%3. %237)))) $1) $0))))))) ((%85 (%86 (\%225. (%240 (\%241. ((%227
       $2) (((\%225. (\%241. (((%228 (%99 (%99 %19))) ((%229 $1) ((%230
       (%94 (\%95. %93))) ((%231 $0) ((%234 (%232 (\%233. %93))) (%235
       (\%236. %93))))))) (\%3. %237)))) $1) $0))))))) ((%85 (%86 (\%225.
       (%240 (\%241. (%240 (\%242. ((%227 $3) ((((\%225. (\%241. (\%242.
       (((%228 (%99 (%99 (%99 %19)))) ((%229 $2) ((%230 (%94 (\%95. %93)))
       ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3. %237))))) $2)
       $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241. (%240 (\%242.
       ((%227 $3) ((((\%225. (\%241. (\%242. (((%228 (%99 (%99 (%99 (%99
       %19))))) ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 $0)
       (%235 (\%236. %93))))))) (\%3. %237))))) $2) $1) $0))))))))) ((%85
       (%86 (\%225. (%240 (\%241. (%240 (\%242. ((%227 $3) ((((\%225.
       (\%241. (\%242. (((%228 (%99 (%99 (%99 (%99 (%99 %19)))))) ((%229
       $2) ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 $0) (%235 (\%236.
       %93))))))) (\%3. %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225.
       (%240 (\%241. (%240 (\%242. ((%227 $3) ((((\%225. (\%241. (\%242.
       (((%228 (%99 (%99 (%99 (%99 (%99 (%99 %19))))))) ((%229 $2) ((%230
       (%94 (\%95. %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93)))))))
       (\%3. %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241.
       (%240 (\%242. ((%227 $3) ((((\%225. (\%241. (\%242. (((%228 (%99
       (%99 (%99 (%99 (%99 (%99 (%99 %19)))))))) ((%229 $2) ((%230 (%94
       (\%95. %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3.
       %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241. (%240
       (\%242. ((%227 $3) ((((\%225. (\%241. (\%242. (((%228 (%99 (%99 (%99
       (%99 (%99 (%99 (%99 (%99 %19))))))))) ((%229 $2) ((%230 (%94 (\%95.
       %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3.
       %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241. (%240
       (\%242. ((%227 $3) ((((\%225. (\%241. (\%242. (((%228 (%99 (%99 (%99
       (%99 (%99 (%99 (%99 (%99 (%99 %19)))))))))) ((%229 $2) ((%230 (%94
       (\%95. %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3.
       %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241. (%243
       (\%244. ((%227 $3) ((((\%225. (\%241. (\%244. (((%228 (%99 (%99 (%99
       (%99 (%99 (%99 (%99 (%99 (%99 (%99 %19))))))))))) ((%229 $2) ((%230
       (%94 (\%95. %93))) ((%231 $1) ((%234 (%232 (\%233. %93))) $0)))))
       (\%3. %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241.
       (%243 (\%244. ((%227 $3) ((((\%225. (\%241. (\%244. (((%228 (%99
       (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 %19))))))))))))
       ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 (%232 (\%233.
       %93))) $0))))) (\%3. %237))))) $2) $1) $0))))))))) ((%85 (%86
       (\%225. (%240 (\%241. (%243 (\%244. ((%227 $3) ((((\%225. (\%241.
       (\%244. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99
       (%99 (%99 %19))))))))))))) ((%229 $2) ((%230 (%94 (\%95. %93)))
       ((%231 $1) ((%234 (%232 (\%233. %93))) $0))))) (\%3. %237))))) $2)
       $1) $0))))))))) (%86 (\%225. (%240 (\%241. (%243 (\%244. ((%227 $3)
       ((((\%225. (\%241. (\%244. (((%228 (%99 (%99 (%99 (%99 (%99 (%99
       (%99 (%99 (%99 (%99 (%99 (%99 (%99 %19)))))))))))))) ((%229 $2)
       ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 (%232 (\%233. %93)))
       $0))))) (\%3. %237))))) $2) $1) $0)))))))))))))))))))))) ($1 $0)))))
       ($0 $1)))))) $0)))`)
  val TOPER_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%245 (\%246. ((%247 (%248 (%249 $0))) $0)))) (%224 (\%250.
       ((%16 ((\%221. (%222 (\%223. ((%83 (%224 (\%221. ((%83 ((%85 (%86
       (\%225. (%102 (\%226. ((%227 $2) (((\%225. (\%226. (((%228 %19)
       ((%229 $1) ((%230 $0) ((%231 (%232 (\%233. %93))) ((%234 (%232
       (\%233. %93))) (%235 (\%236. %93))))))) (\%3. %237)))) $1) $0)))))))
       ((%85 (%102 (\%238. (%86 (\%239. ((%227 $2) (((\%238. (\%239.
       (((%228 (%99 %19)) ((%229 $0) ((%230 $1) ((%231 (%232 (\%233. %93)))
       ((%234 (%232 (\%233. %93))) (%235 (\%236. %93))))))) (\%3. %237))))
       $1) $0))))))) ((%85 (%86 (\%225. (%240 (\%241. ((%227 $2) (((\%225.
       (\%241. (((%228 (%99 (%99 %19))) ((%229 $1) ((%230 (%94 (\%95.
       %93))) ((%231 $0) ((%234 (%232 (\%233. %93))) (%235 (\%236.
       %93))))))) (\%3. %237)))) $1) $0))))))) ((%85 (%86 (\%225. (%240
       (\%241. (%240 (\%242. ((%227 $3) ((((\%225. (\%241. (\%242. (((%228
       (%99 (%99 (%99 %19)))) ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231
       $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3. %237))))) $2) $1)
       $0))))))))) ((%85 (%86 (\%225. (%240 (\%241. (%240 (\%242. ((%227
       $3) ((((\%225. (\%241. (\%242. (((%228 (%99 (%99 (%99 (%99 %19)))))
       ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 $0) (%235
       (\%236. %93))))))) (\%3. %237))))) $2) $1) $0))))))))) ((%85 (%86
       (\%225. (%240 (\%241. (%240 (\%242. ((%227 $3) ((((\%225. (\%241.
       (\%242. (((%228 (%99 (%99 (%99 (%99 (%99 %19)))))) ((%229 $2) ((%230
       (%94 (\%95. %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93)))))))
       (\%3. %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241.
       (%240 (\%242. ((%227 $3) ((((\%225. (\%241. (\%242. (((%228 (%99
       (%99 (%99 (%99 (%99 (%99 %19))))))) ((%229 $2) ((%230 (%94 (\%95.
       %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3.
       %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241. (%240
       (\%242. ((%227 $3) ((((\%225. (\%241. (\%242. (((%228 (%99 (%99 (%99
       (%99 (%99 (%99 (%99 %19)))))))) ((%229 $2) ((%230 (%94 (\%95. %93)))
       ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3. %237))))) $2)
       $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241. (%240 (\%242.
       ((%227 $3) ((((\%225. (\%241. (\%242. (((%228 (%99 (%99 (%99 (%99
       (%99 (%99 (%99 (%99 %19))))))))) ((%229 $2) ((%230 (%94 (\%95.
       %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3.
       %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241. (%240
       (\%242. ((%227 $3) ((((\%225. (\%241. (\%242. (((%228 (%99 (%99 (%99
       (%99 (%99 (%99 (%99 (%99 (%99 %19)))))))))) ((%229 $2) ((%230 (%94
       (\%95. %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3.
       %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241. (%243
       (\%244. ((%227 $3) ((((\%225. (\%241. (\%244. (((%228 (%99 (%99 (%99
       (%99 (%99 (%99 (%99 (%99 (%99 (%99 %19))))))))))) ((%229 $2) ((%230
       (%94 (\%95. %93))) ((%231 $1) ((%234 (%232 (\%233. %93))) $0)))))
       (\%3. %237))))) $2) $1) $0))))))))) ((%85 (%86 (\%225. (%240 (\%241.
       (%243 (\%244. ((%227 $3) ((((\%225. (\%241. (\%244. (((%228 (%99
       (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 %19))))))))))))
       ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 (%232 (\%233.
       %93))) $0))))) (\%3. %237))))) $2) $1) $0))))))))) ((%85 (%86
       (\%225. (%240 (\%241. (%243 (\%244. ((%227 $3) ((((\%225. (\%241.
       (\%244. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99
       (%99 (%99 %19))))))))))))) ((%229 $2) ((%230 (%94 (\%95. %93)))
       ((%231 $1) ((%234 (%232 (\%233. %93))) $0))))) (\%3. %237))))) $2)
       $1) $0))))))))) (%86 (\%225. (%240 (\%241. (%243 (\%244. ((%227 $3)
       ((((\%225. (\%241. (\%244. (((%228 (%99 (%99 (%99 (%99 (%99 (%99
       (%99 (%99 (%99 (%99 (%99 (%99 (%99 %19)))))))))))))) ((%229 $2)
       ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 (%232 (\%233. %93)))
       $0))))) (\%3. %237))))) $2) $1) $0)))))))))))))))))))))) ($1 $0)))))
       ($0 $1))))) $0)) ((%227 (%249 (%248 $0))) $0)))))`)
  val HSL5_def =
    DT([], [],
       `((%251 %252) (\%225. (\%226. (%248 (((\%225. (\%226. (((%228 %19)
       ((%229 $1) ((%230 $0) ((%231 (%232 (\%233. %93))) ((%234 (%232
       (\%233. %93))) (%235 (\%236. %93))))))) (\%3. %237)))) $1) $0)))))`)
  val HSL6_def =
    DT([], [],
       `((%253 %254) (\%238. (\%239. (%248 (((\%238. (\%239. (((%228 (%99
       %19)) ((%229 $0) ((%230 $1) ((%231 (%232 (\%233. %93))) ((%234 (%232
       (\%233. %93))) (%235 (\%236. %93))))))) (\%3. %237)))) $1) $0)))))`)
  val HSL7_def =
    DT([], [],
       `((%255 %256) (\%225. (\%241. (%248 (((\%225. (\%241. (((%228 (%99
       (%99 %19))) ((%229 $1) ((%230 (%94 (\%95. %93))) ((%231 $0) ((%234
       (%232 (\%233. %93))) (%235 (\%236. %93))))))) (\%3. %237)))) $1)
       $0)))))`)
  val HSL8_def =
    DT([], [],
       `((%257 %258) (\%225. (\%241. (\%242. (%248 ((((\%225. (\%241.
       (\%242. (((%228 (%99 (%99 (%99 %19)))) ((%229 $2) ((%230 (%94 (\%95.
       %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3.
       %237))))) $2) $1) $0))))))`)
  val HSL9_def =
    DT([], [],
       `((%257 %259) (\%225. (\%241. (\%242. (%248 ((((\%225. (\%241.
       (\%242. (((%228 (%99 (%99 (%99 (%99 %19))))) ((%229 $2) ((%230 (%94
       (\%95. %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93))))))) (\%3.
       %237))))) $2) $1) $0))))))`)
  val HSL10_def =
    DT([], [],
       `((%257 %260) (\%225. (\%241. (\%242. (%248 ((((\%225. (\%241.
       (\%242. (((%228 (%99 (%99 (%99 (%99 (%99 %19)))))) ((%229 $2) ((%230
       (%94 (\%95. %93))) ((%231 $1) ((%234 $0) (%235 (\%236. %93)))))))
       (\%3. %237))))) $2) $1) $0))))))`)
  val HSL11_def =
    DT([], [],
       `((%257 %261) (\%225. (\%241. (\%242. (%248 ((((\%225. (\%241.
       (\%242. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 %19))))))) ((%229 $2)
       ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 $0) (%235 (\%236.
       %93))))))) (\%3. %237))))) $2) $1) $0))))))`)
  val HSL12_def =
    DT([], [],
       `((%257 %262) (\%225. (\%241. (\%242. (%248 ((((\%225. (\%241.
       (\%242. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 (%99 %19))))))))
       ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 $0) (%235
       (\%236. %93))))))) (\%3. %237))))) $2) $1) $0))))))`)
  val HSL13_def =
    DT([], [],
       `((%257 %263) (\%225. (\%241. (\%242. (%248 ((((\%225. (\%241.
       (\%242. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 %19)))))))))
       ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234 $0) (%235
       (\%236. %93))))))) (\%3. %237))))) $2) $1) $0))))))`)
  val HSL14_def =
    DT([], [],
       `((%257 %264) (\%225. (\%241. (\%242. (%248 ((((\%225. (\%241.
       (\%242. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99
       %19)))))))))) ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231 $1) ((%234
       $0) (%235 (\%236. %93))))))) (\%3. %237))))) $2) $1) $0))))))`)
  val HSL15_def =
    DT([], [],
       `((%265 %266) (\%225. (\%241. (\%244. (%248 ((((\%225. (\%241.
       (\%244. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99
       %19))))))))))) ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231 $1)
       ((%234 (%232 (\%233. %93))) $0))))) (\%3. %237))))) $2) $1)
       $0))))))`)
  val HSL16_def =
    DT([], [],
       `((%265 %267) (\%225. (\%241. (\%244. (%248 ((((\%225. (\%241.
       (\%244. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99
       (%99 %19)))))))))))) ((%229 $2) ((%230 (%94 (\%95. %93))) ((%231 $1)
       ((%234 (%232 (\%233. %93))) $0))))) (\%3. %237))))) $2) $1)
       $0))))))`)
  val HSL17_def =
    DT([], [],
       `((%265 %268) (\%225. (\%241. (\%244. (%248 ((((\%225. (\%241.
       (\%244. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99
       (%99 (%99 %19))))))))))))) ((%229 $2) ((%230 (%94 (\%95. %93)))
       ((%231 $1) ((%234 (%232 (\%233. %93))) $0))))) (\%3. %237))))) $2)
       $1) $0))))))`)
  val HSL18_def =
    DT([], [],
       `((%265 %269) (\%225. (\%241. (\%244. (%248 ((((\%225. (\%241.
       (\%244. (((%228 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99 (%99
       (%99 (%99 (%99 %19)))))))))))))) ((%229 $2) ((%230 (%94 (\%95.
       %93))) ((%231 $1) ((%234 (%232 (\%233. %93))) $0))))) (\%3.
       %237))))) $2) $1) $0))))))`)
  val TLDR = DT([], [], `((%251 %270) %252)`)
  val TSTR = DT([], [], `((%253 %271) %254)`)
  val TMOV = DT([], [], `((%255 %272) %256)`)
  val TADD = DT([], [], `((%257 %273) %258)`)
  val TSUB = DT([], [], `((%257 %274) %259)`)
  val TRSB = DT([], [], `((%257 %275) %260)`)
  val TMUL = DT([], [], `((%257 %276) %261)`)
  val TAND = DT([], [], `((%257 %277) %262)`)
  val TORR = DT([], [], `((%257 %278) %263)`)
  val TEOR = DT([], [], `((%257 %279) %264)`)
  val TLSL = DT([], [], `((%265 %280) %266)`)
  val TLSR = DT([], [], `((%265 %281) %267)`)
  val TASR = DT([], [], `((%265 %282) %268)`)
  val TROR = DT([], [], `((%265 %283) %269)`)
  val TOPER_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%284 (\%285. (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290
       (\%292. (%290 (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296.
       (%290 (\%297. (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298
       (\%302. (%49 (\%225. (%14 (\%226. ((%35 (((((((((((((((%303 $15)
       $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) ((%270 $1)
       $0))) (($15 $1) $0))))))))))))))))))))))))))))))))))) ((%8 (%284
       (\%285. (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292.
       (%290 (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290
       (\%297. (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%14
       (\%238. (%49 (\%239. ((%35 (((((((((((((((%303 $15) $14) $13) $12)
       $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) ((%271 $1) $0))) (($14 $1)
       $0))))))))))))))))))))))))))))))))))) ((%8 (%284 (\%285. (%286
       (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292. (%290 (\%293.
       (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290 (\%297. (%298
       (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%49 (\%225. (%140
       (\%241. ((%35 (((((((((((((((%303 $15) $14) $13) $12) $11) $10) $9)
       $8) $7) $6) $5) $4) $3) $2) ((%272 $1) $0))) (($13 $1)
       $0))))))))))))))))))))))))))))))))))) ((%8 (%284 (\%285. (%286
       (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292. (%290 (\%293.
       (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290 (\%297. (%298
       (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%49 (\%225. (%140
       (\%241. (%140 (\%242. ((%35 (((((((((((((((%303 $16) $15) $14) $13)
       $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) (((%273 $2) $1) $0)))
       ((($13 $2) $1) $0))))))))))))))))))))))))))))))))))))) ((%8 (%284
       (\%285. (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292.
       (%290 (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290
       (\%297. (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%49
       (\%225. (%140 (\%241. (%140 (\%242. ((%35 (((((((((((((((%303 $16)
       $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) (((%274
       $2) $1) $0))) ((($12 $2) $1) $0)))))))))))))))))))))))))))))))))))))
       ((%8 (%284 (\%285. (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290
       (\%292. (%290 (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296.
       (%290 (\%297. (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298
       (\%302. (%49 (\%225. (%140 (\%241. (%140 (\%242. ((%35
       (((((((((((((((%303 $16) $15) $14) $13) $12) $11) $10) $9) $8) $7)
       $6) $5) $4) $3) (((%275 $2) $1) $0))) ((($11 $2) $1)
       $0))))))))))))))))))))))))))))))))))))) ((%8 (%284 (\%285. (%286
       (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292. (%290 (\%293.
       (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290 (\%297. (%298
       (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%49 (\%225. (%140
       (\%241. (%140 (\%242. ((%35 (((((((((((((((%303 $16) $15) $14) $13)
       $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) (((%276 $2) $1) $0)))
       ((($10 $2) $1) $0))))))))))))))))))))))))))))))))))))) ((%8 (%284
       (\%285. (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292.
       (%290 (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290
       (\%297. (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%49
       (\%225. (%140 (\%241. (%140 (\%242. ((%35 (((((((((((((((%303 $16)
       $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) (((%277
       $2) $1) $0))) ((($9 $2) $1) $0)))))))))))))))))))))))))))))))))))))
       ((%8 (%284 (\%285. (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290
       (\%292. (%290 (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296.
       (%290 (\%297. (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298
       (\%302. (%49 (\%225. (%140 (\%241. (%140 (\%242. ((%35
       (((((((((((((((%303 $16) $15) $14) $13) $12) $11) $10) $9) $8) $7)
       $6) $5) $4) $3) (((%278 $2) $1) $0))) ((($8 $2) $1)
       $0))))))))))))))))))))))))))))))))))))) ((%8 (%284 (\%285. (%286
       (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292. (%290 (\%293.
       (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290 (\%297. (%298
       (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%49 (\%225. (%140
       (\%241. (%140 (\%242. ((%35 (((((((((((((((%303 $16) $15) $14) $13)
       $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) (((%279 $2) $1) $0)))
       ((($7 $2) $1) $0))))))))))))))))))))))))))))))))))))) ((%8 (%284
       (\%285. (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292.
       (%290 (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290
       (\%297. (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%49
       (\%225. (%140 (\%241. (%304 (\%244. ((%35 (((((((((((((((%303 $16)
       $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) (((%280
       $2) $1) $0))) ((($6 $2) $1) $0)))))))))))))))))))))))))))))))))))))
       ((%8 (%284 (\%285. (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290
       (\%292. (%290 (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296.
       (%290 (\%297. (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298
       (\%302. (%49 (\%225. (%140 (\%241. (%304 (\%244. ((%35
       (((((((((((((((%303 $16) $15) $14) $13) $12) $11) $10) $9) $8) $7)
       $6) $5) $4) $3) (((%281 $2) $1) $0))) ((($5 $2) $1)
       $0))))))))))))))))))))))))))))))))))))) ((%8 (%284 (\%285. (%286
       (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292. (%290 (\%293.
       (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290 (\%297. (%298
       (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%49 (\%225. (%140
       (\%241. (%304 (\%244. ((%35 (((((((((((((((%303 $16) $15) $14) $13)
       $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) (((%282 $2) $1) $0)))
       ((($4 $2) $1) $0))))))))))))))))))))))))))))))))))))) (%284 (\%285.
       (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290 (\%292. (%290
       (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296. (%290 (\%297.
       (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298 (\%302. (%49 (\%225.
       (%140 (\%241. (%304 (\%244. ((%35 (((((((((((((((%303 $16) $15) $14)
       $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) (((%283 $2) $1)
       $0))) ((($3 $2) $1)
       $0)))))))))))))))))))))))))))))))))))))))))))))))))`)
  val TOPER_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%49 (\%225. (%14 (\%226. ((%17 (%305 ((%270 $1) $0))) ((%128
       (%5 (%21 %7))) ((%128 (%64 $1)) $0)))))))) ((%8 (%14 (\%238. (%49
       (\%239. ((%17 (%305 ((%271 $1) $0))) ((%128 (%5 (%21 %7))) ((%128
       $1) (%64 $0))))))))) ((%8 (%49 (\%225. (%140 (\%241. ((%17 (%305
       ((%272 $1) $0))) ((%128 (%5 (%21 %7))) ((%128 (%64 $1)) (%153
       $0))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242. ((%17
       (%305 (((%273 $2) $1) $0))) ((%128 (%5 (%21 %7))) ((%128 (%64 $2))
       ((%128 (%153 $1)) (%153 $0)))))))))))) ((%8 (%49 (\%225. (%140
       (\%241. (%140 (\%242. ((%17 (%305 (((%274 $2) $1) $0))) ((%128 (%5
       (%21 %7))) ((%128 (%64 $2)) ((%128 (%153 $1)) (%153 $0))))))))))))
       ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242. ((%17 (%305 (((%275
       $2) $1) $0))) ((%128 (%5 (%21 %7))) ((%128 (%64 $2)) ((%128 (%153
       $1)) (%153 $0)))))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140
       (\%242. ((%17 (%305 (((%276 $2) $1) $0))) ((%128 (%5 (%21 %7)))
       ((%128 (%64 $2)) ((%128 (%153 $1)) (%153 $0)))))))))))) ((%8 (%49
       (\%225. (%140 (\%241. (%140 (\%242. ((%17 (%305 (((%277 $2) $1)
       $0))) ((%128 (%5 (%21 %7))) ((%128 (%64 $2)) ((%128 (%153 $1)) (%153
       $0)))))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242. ((%17
       (%305 (((%278 $2) $1) $0))) ((%128 (%5 (%21 %7))) ((%128 (%64 $2))
       ((%128 (%153 $1)) (%153 $0)))))))))))) ((%8 (%49 (\%225. (%140
       (\%241. (%140 (\%242. ((%17 (%305 (((%279 $2) $1) $0))) ((%128 (%5
       (%21 %7))) ((%128 (%64 $2)) ((%128 (%153 $1)) (%153 $0))))))))))))
       ((%8 (%49 (\%225. (%140 (\%241. (%304 (\%244. ((%17 (%305 (((%280
       $2) $1) $0))) ((%128 (%5 (%21 %7))) ((%128 (%64 $2)) (%153
       $1))))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%304 (\%244. ((%17
       (%305 (((%281 $2) $1) $0))) ((%128 (%5 (%21 %7))) ((%128 (%64 $2))
       (%153 $1))))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%304 (\%244.
       ((%17 (%305 (((%282 $2) $1) $0))) ((%128 (%5 (%21 %7))) ((%128 (%64
       $2)) (%153 $1))))))))))) (%49 (\%225. (%140 (\%241. (%304 (\%244.
       ((%17 (%305 (((%283 $2) $1) $0))) ((%128 (%5 (%21 %7))) ((%128 (%64
       $2)) (%153 $1)))))))))))))))))))))))`)
  val HSL_STRUCTURE_TY_DEF =
    DT(["DISK_THM"], [],
       `(%306 (\%307. ((%308 (\%309. (%310 (\%311. ((%83 (%312 (\%309.
       ((%83 ((%85 (%313 (\%314. ((%315 $1) ((\%314. (((%316 %19) ((%317
       $0) ((%318 (%319 (\%320. %93))) ((%321 (%322 (\%323. %93))) (%322
       (\%323. %93)))))) (\%3. %324))) $0))))) ((%85 (%325 (\%326. (%325
       (\%327. ((%8 ((%315 $2) (((\%326. (\%327. (((%316 (%99 %19)) ((%317
       (%328 (\%329. %93))) ((%318 (%319 (\%320. %93))) ((%321 (%322
       (\%323. %93))) (%322 (\%323. %93)))))) ((%330 $1) ((%330 $0) (\%3.
       %324)))))) $1) $0))) ((%8 ($3 $1)) ($3 $0)))))))) ((%85 (%331
       (\%332. (%325 (\%327. (%325 (\%333. ((%8 ((%315 $3) ((((\%332.
       (\%327. (\%333. (((%316 (%99 (%99 %19))) ((%317 (%328 (\%329. %93)))
       ((%318 $2) ((%321 (%322 (\%323. %93))) (%322 (\%323. %93))))))
       ((%330 $1) ((%330 $0) (\%3. %324))))))) $2) $1) $0))) ((%8 ($4 $1))
       ($4 $0)))))))))) ((%85 (%331 (\%332. (%325 (\%327. ((%8 ((%315 $2)
       (((\%332. (\%327. (((%316 (%99 (%99 (%99 %19)))) ((%317 (%328
       (\%329. %93))) ((%318 $1) ((%321 (%322 (\%323. %93))) (%322 (\%323.
       %93)))))) ((%330 $0) (\%3. %324))))) $1) $0))) ($3 $0))))))) (%334
       (\%335. (%325 (\%327. (%334 (\%336. ((%8 ((%315 $3) ((((\%335.
       (\%327. (\%336. (((%316 (%99 (%99 (%99 (%99 %19))))) ((%317 (%328
       (\%329. %93))) ((%318 (%319 (\%320. %93))) ((%321 $2) $0)))) ((%330
       $1) (\%3. %324)))))) $2) $1) $0))) ($4 $1))))))))))))) ($1 $0)))))
       ($0 $1)))))) $0)))`)
  val HSL_STRUCTURE_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%337 (\%338. ((%339 (%340 (%341 $0))) $0)))) (%312 (\%342.
       ((%16 ((\%309. (%310 (\%311. ((%83 (%312 (\%309. ((%83 ((%85 (%313
       (\%314. ((%315 $1) ((\%314. (((%316 %19) ((%317 $0) ((%318 (%319
       (\%320. %93))) ((%321 (%322 (\%323. %93))) (%322 (\%323. %93))))))
       (\%3. %324))) $0))))) ((%85 (%325 (\%326. (%325 (\%327. ((%8 ((%315
       $2) (((\%326. (\%327. (((%316 (%99 %19)) ((%317 (%328 (\%329. %93)))
       ((%318 (%319 (\%320. %93))) ((%321 (%322 (\%323. %93))) (%322
       (\%323. %93)))))) ((%330 $1) ((%330 $0) (\%3. %324)))))) $1) $0)))
       ((%8 ($3 $1)) ($3 $0)))))))) ((%85 (%331 (\%332. (%325 (\%327. (%325
       (\%333. ((%8 ((%315 $3) ((((\%332. (\%327. (\%333. (((%316 (%99 (%99
       %19))) ((%317 (%328 (\%329. %93))) ((%318 $2) ((%321 (%322 (\%323.
       %93))) (%322 (\%323. %93)))))) ((%330 $1) ((%330 $0) (\%3.
       %324))))))) $2) $1) $0))) ((%8 ($4 $1)) ($4 $0)))))))))) ((%85 (%331
       (\%332. (%325 (\%327. ((%8 ((%315 $2) (((\%332. (\%327. (((%316 (%99
       (%99 (%99 %19)))) ((%317 (%328 (\%329. %93))) ((%318 $1) ((%321
       (%322 (\%323. %93))) (%322 (\%323. %93)))))) ((%330 $0) (\%3.
       %324))))) $1) $0))) ($3 $0))))))) (%334 (\%335. (%325 (\%327. (%334
       (\%336. ((%8 ((%315 $3) ((((\%335. (\%327. (\%336. (((%316 (%99 (%99
       (%99 (%99 %19))))) ((%317 (%328 (\%329. %93))) ((%318 (%319 (\%320.
       %93))) ((%321 $2) $0)))) ((%330 $1) (\%3. %324)))))) $2) $1) $0)))
       ($4 $1))))))))))))) ($1 $0))))) ($0 $1))))) $0)) ((%315 (%341 (%340
       $0))) $0)))))`)
  val HSL19_def =
    DT([], [],
       `((%343 %344) (\%314. (%340 ((\%314. (((%316 %19) ((%317 $0) ((%318
       (%319 (\%320. %93))) ((%321 (%322 (\%323. %93))) (%322 (\%323.
       %93)))))) (\%3. %324))) $0))))`)
  val HSL20_def =
    DT([], [],
       `((%345 %346) (\%347. (\%348. (%340 (((\%326. (\%327. (((%316 (%99
       %19)) ((%317 (%328 (\%329. %93))) ((%318 (%319 (\%320. %93))) ((%321
       (%322 (\%323. %93))) (%322 (\%323. %93)))))) ((%330 $1) ((%330 $0)
       (\%3. %324)))))) (%341 $1)) (%341 $0))))))`)
  val HSL21_def =
    DT([], [],
       `((%349 %350) (\%332. (\%348. (\%351. (%340 ((((\%332. (\%327.
       (\%333. (((%316 (%99 (%99 %19))) ((%317 (%328 (\%329. %93))) ((%318
       $2) ((%321 (%322 (\%323. %93))) (%322 (\%323. %93)))))) ((%330 $1)
       ((%330 $0) (\%3. %324))))))) $2) (%341 $1)) (%341 $0)))))))`)
  val HSL22_def =
    DT([], [],
       `((%352 %353) (\%332. (\%348. (%340 (((\%332. (\%327. (((%316 (%99
       (%99 (%99 %19)))) ((%317 (%328 (\%329. %93))) ((%318 $1) ((%321
       (%322 (\%323. %93))) (%322 (\%323. %93)))))) ((%330 $0) (\%3.
       %324))))) $1) (%341 $0))))))`)
  val HSL23_def =
    DT([], [],
       `((%354 %355) (\%335. (\%348. (\%336. (%340 ((((\%335. (\%327.
       (\%336. (((%316 (%99 (%99 (%99 (%99 %19))))) ((%317 (%328 (\%329.
       %93))) ((%318 (%319 (\%320. %93))) ((%321 $2) $0)))) ((%330 $1)
       (\%3. %324)))))) $2) (%341 $1)) $0))))))`)
  val Blk = DT([], [], `((%343 %356) %344)`)
  val Sc = DT([], [], `((%345 %357) %346)`)
  val Cj = DT([], [], `((%349 %358) %350)`)
  val Tr = DT([], [], `((%352 %359) %353)`)
  val Fc = DT([], [], `((%354 %360) %355)`)
  val HSL_STRUCTURE_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%361 (\%362. (%363 (\%364. (%365 (\%366. (%367 (\%368. (%369
       (\%370. (%371 (\%314. ((%35 ((((((%372 $5) $4) $3) $2) $1) (%356
       $0))) ($5 $0))))))))))))))) ((%8 (%361 (\%362. (%363 (\%364. (%365
       (\%366. (%367 (\%368. (%369 (\%370. (%337 (\%347. (%337 (\%348.
       ((%35 ((((((%372 $6) $5) $4) $3) $2) ((%357 $1) $0))) (($5 $1)
       $0))))))))))))))))) ((%8 (%361 (\%362. (%363 (\%364. (%365 (\%366.
       (%367 (\%368. (%369 (\%370. (%373 (\%332. (%337 (\%348. (%337
       (\%351. ((%35 ((((((%372 $7) $6) $5) $4) $3) (((%358 $2) $1) $0)))
       ((($5 $2) $1) $0))))))))))))))))))) ((%8 (%361 (\%362. (%363 (\%364.
       (%365 (\%366. (%367 (\%368. (%369 (\%370. (%373 (\%332. (%337
       (\%348. ((%35 ((((((%372 $6) $5) $4) $3) $2) ((%359 $1) $0))) (($3
       $1) $0))))))))))))))))) (%361 (\%362. (%363 (\%364. (%365 (\%366.
       (%367 (\%368. (%369 (\%370. (%374 (\%335. (%337 (\%348. (%374
       (\%336. ((%35 ((((((%372 $7) $6) $5) $4) $3) (((%360 $2) $1) $0)))
       ((($3 $2) $1) $0))))))))))))))))))))))`)
  val HSL_STRUCTURE_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%371 (\%314. ((%17 (%375 (%356 $0))) ((%128 (%5 (%21 %7)))
       ((%376 %305) $0)))))) ((%8 (%337 (\%347. (%337 (\%348. ((%17 (%375
       ((%357 $1) $0))) ((%128 (%5 (%21 %7))) ((%128 (%375 $1)) (%375
       $0))))))))) ((%8 (%373 (\%332. (%337 (\%348. (%337 (\%351. ((%17
       (%375 (((%358 $2) $1) $0))) ((%128 (%5 (%21 %7))) ((%128 ((%377
       (\%63. (\%378. ((%128 (%64 $1)) ((%379 (\%380. (\%381. ((%128 (%382
       $1)) (%153 $0))))) $0))))) $2)) ((%128 (%375 $1)) (%375
       $0)))))))))))) ((%8 (%373 (\%332. (%337 (\%348. ((%17 (%375 ((%359
       $1) $0))) ((%128 (%5 (%21 %7))) ((%128 ((%377 (\%63. (\%378. ((%128
       (%64 $1)) ((%379 (\%380. (\%381. ((%128 (%382 $1)) (%153 $0)))))
       $0))))) $1)) (%375 $0))))))))) (%374 (\%335. (%337 (\%348. (%374
       (\%336. ((%17 (%375 (((%360 $2) $1) $0))) ((%128 (%5 (%21 %7)))
       ((%128 ((%383 (\%384. (\%385. ((%128 ((%386 %127) $1)) ((%386 %127)
       $0))))) $2)) ((%128 (%375 $1)) ((%383 (\%384. (\%385. ((%128 ((%386
       %127) $1)) ((%386 %127) $0))))) $0)))))))))))))))`)
  val eval_TCND_tupled_primitive_def =
    DT([], [],
       `((%387 %388) ((%389 (%390 (\%391. (%392 $0)))) (\%393. (\%394.
       ((%395 (\%320. (\%396. ((%397 (\%398. (\%399. ((%400 (\%401. (\%402.
       (((((((((((((((((%403 (%404 ((%177 ((%178 $4) (%116 $3))) ((%178 $4)
       (%155 $0))))) (%404 ((%405 ((%178 $4) (%116 $3))) ((%178 $4) (%155
       $0))))) (%404 ((%406 (%407 (\%408. (%409 (\%410. (%411 (\%412.
       (\%413. $3)))))))) ((%414 ((%178 $4) (%116 $3))) ((%178 $4) (%155
       $0)))))) (%404 ((%406 (%407 (\%408. (%409 (\%410. (%411 (\%412.
       (\%413. $0)))))))) ((%414 ((%178 $4) (%116 $3))) ((%178 $4) (%155
       $0)))))) (%404 ((%415 ((%178 $4) (%116 $3))) ((%178 $4) (%155
       $0))))) (%404 ((%416 ((%178 $4) (%116 $3))) ((%178 $4) (%155 $0)))))
       (%404 ((%417 ((%178 $4) (%116 $3))) ((%178 $4) (%155 $0))))) (%404
       %93)) (%404 (%418 ((%177 ((%178 $4) (%116 $3))) ((%178 $4) (%155
       $0)))))) (%404 ((%419 ((%178 $4) (%116 $3))) ((%178 $4) (%155
       $0))))) (%404 ((%406 (%407 (\%408. (%409 (\%410. (%411 (\%412.
       (\%413. (%418 $3))))))))) ((%414 ((%178 $4) (%116 $3))) ((%178 $4)
       (%155 $0)))))) (%404 ((%406 (%407 (\%408. (%409 (\%410. (%411
       (\%412. (\%413. (%418 $0))))))))) ((%414 ((%178 $4) (%116 $3)))
       ((%178 $4) (%155 $0)))))) (%404 ((%420 ((%178 $4) (%116 $3))) ((%178
       $4) (%155 $0))))) (%404 ((%421 ((%178 $4) (%116 $3))) ((%178 $4)
       (%155 $0))))) (%404 ((%422 ((%178 $4) (%116 $3))) ((%178 $4) (%155
       $0))))) (%404 %423)) $1)))) $0)))) $1)))) $0)))))`)
  val eval_TCND_curried_def =
    DT([], [],
       `(%373 (\%424. (%174 (\%425. ((%16 ((%426 $1) $0)) (%388 ((%427 $1)
       $0)))))))`)
  val transfer_tupled_primitive_def =
    DT([], [],
       `((%428 %429) ((%430 (%431 (\%432. ((%8 (%433 $0)) (%434 (\%435.
       (%434 (\%436. (%104 (\%437. (%174 (\%438. (%104 (\%439. (%174
       (\%440. (($6 ((%441 ((%442 (((%443 $0) $1) ((%178 $2) $3))) $2))
       ((%444 $4) $5))) ((%441 ((%442 $0) $2)) ((%444 ((%445 $1) $4))
       ((%445 $3) $5)))))))))))))))))))) (\%446. (\%447. ((%448 (\%449.
       (\%450. ((%451 (\%440. (\%438. ((%452 (\%453. (\%454. (((%455
       (((%455 (%456 $3)) (\%457. (\%458. %459))) $0)) (\%439. (\%436.
       (((%455 %459) (\%437. (\%435. (%456 ($11 ((%441 ((%442 (((%443 $7)
       $3) ((%178 $6) $1))) $6)) ((%444 $2) $0))))))) $2)))) $1)))) $2))))
       $1)))) $0)))))`)
  val transfer_curried_def =
    DT([], [],
       `(%460 (\%461. (%374 (\%462. ((%463 ((%464 $1) $0)) (%429 ((%441 $1)
       $0)))))))`)
  val tdecode_def =
    DT(["DISK_THM"], [],
       `((%8 (%174 (\%465. (%49 (\%466. (%14 (\%467. ((%463 ((%468 $2)
       ((%270 $1) $0))) (((%443 $2) (%116 $1)) ((%178 $2) (%118
       $0))))))))))) ((%8 (%174 (\%465. (%14 (\%469. (%49 (\%470. ((%463
       ((%468 $2) ((%271 $1) $0))) (((%443 $2) (%118 $1)) ((%178 $2) (%116
       $0))))))))))) ((%8 (%174 (\%465. (%49 (\%466. (%140 (\%471. ((%463
       ((%468 $2) ((%272 $1) $0))) (((%443 $2) (%116 $1)) ((%178 $2) (%155
       $0))))))))))) ((%8 (%174 (\%465. (%49 (\%466. (%140 (\%472. (%140
       (\%473. ((%463 ((%468 $3) (((%273 $2) $1) $0))) (((%443 $3) (%116
       $2)) ((%474 ((%178 $3) (%155 $1))) ((%178 $3) (%155 $0))))))))))))))
       ((%8 (%174 (\%465. (%49 (\%466. (%140 (\%472. (%140 (\%473. ((%463
       ((%468 $3) (((%274 $2) $1) $0))) (((%443 $3) (%116 $2)) ((%475
       ((%178 $3) (%155 $1))) ((%178 $3) (%155 $0)))))))))))))) ((%8 (%174
       (\%465. (%49 (\%466. (%140 (\%472. (%140 (\%473. ((%463 ((%468 $3)
       (((%275 $2) $1) $0))) (((%443 $3) (%116 $2)) ((%475 ((%178 $3) (%155
       $0))) ((%178 $3) (%155 $1)))))))))))))) ((%8 (%174 (\%465. (%49
       (\%466. (%140 (\%472. (%140 (\%476. ((%463 ((%468 $3) (((%276 $2)
       $1) $0))) (((%443 $3) (%116 $2)) ((%477 ((%178 $3) (%155 $1)))
       ((%178 $3) (%155 $0)))))))))))))) ((%8 (%174 (\%465. (%49 (\%466.
       (%140 (\%472. (%140 (\%473. ((%463 ((%468 $3) (((%277 $2) $1) $0)))
       (((%443 $3) (%116 $2)) ((%478 ((%178 $3) (%155 $1))) ((%178 $3)
       (%155 $0)))))))))))))) ((%8 (%174 (\%465. (%49 (\%466. (%140 (\%472.
       (%140 (\%473. ((%463 ((%468 $3) (((%278 $2) $1) $0))) (((%443 $3)
       (%116 $2)) ((%479 ((%178 $3) (%155 $1))) ((%178 $3) (%155
       $0)))))))))))))) ((%8 (%174 (\%465. (%49 (\%466. (%140 (\%472. (%140
       (\%473. ((%463 ((%468 $3) (((%279 $2) $1) $0))) (((%443 $3) (%116
       $2)) ((%480 ((%178 $3) (%155 $1))) ((%178 $3) (%155 $0))))))))))))))
       ((%8 (%174 (\%465. (%49 (\%466. (%140 (\%476. (%304 (\%481. ((%463
       ((%468 $3) (((%280 $2) $1) $0))) (((%443 $3) (%116 $2)) ((%482
       ((%178 $3) (%155 $1))) (%483 $0))))))))))))) ((%8 (%174 (\%465. (%49
       (\%466. (%140 (\%476. (%304 (\%481. ((%463 ((%468 $3) (((%281 $2)
       $1) $0))) (((%443 $3) (%116 $2)) ((%484 ((%178 $3) (%155 $1))) (%483
       $0))))))))))))) ((%8 (%174 (\%465. (%49 (\%466. (%140 (\%476. (%304
       (\%481. ((%463 ((%468 $3) (((%282 $2) $1) $0))) (((%443 $3) (%116
       $2)) ((%485 ((%178 $3) (%155 $1))) (%483 $0))))))))))))) (%174
       (\%465. (%49 (\%466. (%140 (\%476. (%304 (\%481. ((%463 ((%468 $3)
       (((%283 $2) $1) $0))) (((%443 $3) (%116 $2)) ((%486 ((%178 $3) (%155
       $1))) (%483 $0)))))))))))))))))))))))))`)
  val empty_s_def = DT([], [], `((%463 %487) ((%488 %489) %490))`)
  val run_hsl_tupled_AUX_def =
    DT([], [],
       `(%491 (\%492. ((%493 (%494 $0)) ((%495 $0) (\%496. (\%497. ((%498
       (\%499. (\%396. ((((((%500 (\%501. (((%502 (%456 $1)) (\%503.
       (\%504. (%456 ($6 ((%505 (%356 $0)) ((%468 $3) $1))))))) $0)))
       (\%506. (\%507. (%456 ($5 ((%505 $0) ($5 ((%505 $1) $2))))))))
       (\%508. (\%509. (\%510. (%456 (((%511 ((%426 $2) $3)) ($6 ((%505 $1)
       $3))) ($6 ((%505 $0) $3)))))))) (\%512. (\%513. (%456 (((%514
       (\%515. (%418 ((%426 $2) $0)))) (\%516. ($6 ((%505 $1) $0))))
       $2))))) (\%517. (\%518. (\%519. ((%452 (\%520. (\%521. ((%452
       (\%522. (\%523. (%456 ((%524 (\%440. ((%524 (\%525. ((%464 ((%442
       $9) $0)) ((%444 $3) $2)))) ($11 ((%505 $6) $0))))) ((%464 ((%442
       %487) $7)) ((%444 $2) $3))))))) $2)))) $2))))) $1)))) $0)))))))`)
  val run_hsl_tupled_primitive_def =
    DT([], [],
       `((%493 %526) (%494 (%527 (\%492. ((%8 (%528 $0)) ((%8 (%245 (\%503.
       (%174 (\%396. (%371 (\%504. (($3 ((%505 (%356 $0)) ((%468 $1) $2)))
       ((%505 (%356 ((%529 $2) $0))) $1))))))))) ((%8 (%174 (\%396. (%337
       (\%506. (%337 (\%507. (($3 ((%505 $0) ((%494 $3) ((%505 $1) $2))))
       ((%505 ((%357 $1) $0)) $2))))))))) ((%8 (%337 (\%507. (%174 (\%396.
       (%337 (\%506. (($3 ((%505 $0) $1)) ((%505 ((%357 $0) $2))
       $1))))))))) ((%8 (%337 (\%507. (%337 (\%506. (%174 (\%396. (%373
       (\%508. ((%83 ((%426 $0) $1)) (($4 ((%505 $2) $1)) ((%505 (((%358
       $0) $2) $3)) $1)))))))))))) ((%8 (%337 (\%506. (%337 (\%507. (%174
       (\%396. (%373 (\%508. ((%83 (%418 ((%426 $0) $1))) (($4 ((%505 $2)
       $1)) ((%505 (((%358 $0) $3) $2)) $1)))))))))))) ((%8 (%174 (\%396.
       (%373 (\%508. (%337 (\%506. (%174 (\%516. (($4 ((%505 $1) $0))
       ((%505 ((%359 $2) $1)) $3))))))))))) (%434 (\%523. (%434 (\%522.
       (%337 (\%518. (%434 (\%520. (%434 (\%521. (%174 (\%396. (%174
       (\%440. ((%83 ((%463 $0) ((%464 ((%442 %487) $1)) ((%444 $2) $3))))
       (($7 ((%505 $4) $0)) ((%505 (((%360 ((%444 $3) $2)) $4) ((%444 $5)
       $6))) $1))))))))))))))))))))))))))))`)
  val run_hsl_curried_def =
    DT([], [],
       `(%337 (\%530. (%174 (\%425. ((%463 ((%531 $1) $0)) (%526 ((%505 $1)
       $0)))))))`)
  val within_bound_def =
    DT([], [],
       `(%14 (\%70. (%14 (\%532. ((%16 ((%533 $1) $0)) ((%4 $1) $0))))))`)
  val valid_TEXP_def =
    DT(["DISK_THM"], [],
       `((%8 (%14 (\%37. (%14 (\%532. ((%16 ((%534 (%118 $1)) $0)) ((%533
       $1) $0))))))) ((%8 (%49 (\%154. (%14 (\%532. ((%16 ((%534 (%116 $1))
       $0)) %93)))))) (%126 (\%202. (%14 (\%532. ((%16 ((%534 (%117 $1))
       $0)) %93)))))))`)
  val valid_assgn_tupled_primitive_def =
    DT([], [],
       `((%535 %536) ((%537 (%538 (\%539. (%540 $0)))) (\%541. (\%542.
       ((%543 (\%544. (\%532. (((((((((((((((%545 (\%154. (\%37. (%404
       ((%533 $0) $2))))) (\%546. (\%547. (%404 ((%533 $1) $2))))) (\%548.
       (\%549. (%404 %93)))) (\%550. (\%551. (\%552. (%404 %93))))) (\%553.
       (\%554. (\%555. (%404 %93))))) (\%556. (\%557. (\%558. (%404
       %93))))) (\%559. (\%560. (\%561. (%404 %93))))) (\%562. (\%563.
       (\%564. (%404 %93))))) (\%565. (\%566. (\%567. (%404 %93)))))
       (\%568. (\%569. (\%570. (%404 %93))))) (\%571. (\%572. (\%573. (%404
       %93))))) (\%574. (\%575. (\%576. (%404 %93))))) (\%577. (\%578.
       (\%579. (%404 %93))))) (\%580. (\%581. (\%582. (%404 %93))))) $1))))
       $0)))))`)
  val valid_assgn_curried_def =
    DT([], [],
       `(%245 (\%583. (%14 (\%584. ((%16 ((%585 $1) $0)) (%536 ((%586 $1)
       $0)))))))`)
  val valid_struct_def =
    DT(["DISK_THM"], [],
       `((%8 (%371 (\%504. (%14 (\%532. ((%16 ((%587 (%356 $1)) $0)) ((%588
       (\%503. ((%585 $0) $1))) $1))))))) ((%8 (%337 (\%506. (%337 (\%507.
       (%14 (\%532. ((%16 ((%587 ((%357 $2) $1)) $0)) ((%8 ((%587 $2) $0))
       ((%587 $1) $0)))))))))) ((%8 (%373 (\%508. (%337 (\%589. (%337
       (\%590. (%14 (\%532. ((%16 ((%587 (((%358 $3) $2) $1)) $0)) ((%8
       ((%587 $2) $0)) ((%587 $1) $0)))))))))))) (%373 (\%508. (%337
       (\%591. (%14 (\%532. ((%16 ((%587 ((%359 $2) $1)) $0)) ((%587 $1)
       $0)))))))))))`)
  val CSPEC_def =
    DT(["DISK_THM"], [],
       `(%337 (\%518. (%592 (\%593. (%594 (\%595. (%596 (\%597. ((%16
       ((%598 $3) ((%599 $2) ((%600 $1) $0)))) (%28 (\%196. (%174 (\%396.
       ((%83 ((%35 ($4 $0)) $1)) ((%601 ($2 ((%531 $5) $0))) ($3
       $1))))))))))))))))`)
  val unique_list_def =
    DT(["DISK_THM"], [],
       `((%8 (%28 (\%602. (%603 (\%604. ((%16 (%605 ((%606 $1) $0))) ((%8
       ((%607 (\%608. (%418 ((%35 $0) $2)))) $0)) (%605 $0)))))))) ((%16
       (%605 %609)) %93))`)
  val notC_primitive_def =
    DT([], [],
       `((%610 %611) ((%612 (%613 (\%614. (%615 $0)))) (\%616. (\%105.
       ((((%617 (\%618. (%404 %93))) (\%619. (%404 %423))) (\%620. (%404
       %93))) $0)))))`)
  val match_def =
    DT([], [],
       `(%592 (\%621. (%434 (\%622. (%623 (\%624. ((%16 (((%625 $2) $1)
       $0)) (%174 (\%396. ((%35 ($3 $0)) ($1 ((%626 (%178 $0))
       $2))))))))))))`)
  val valid_arg_list_def =
    DT(["DISK_THM"], [],
       `(%603 (\%627. (%434 (\%522. (%434 (\%521. (%628 (\%629. ((%16 (%630
       ((%631 $3) ((%632 $2) ((%633 $1) $0))))) ((%8 (%634 $2)) ((%8 (%634
       $1)) ((%8 ((%17 (%635 $3)) (%636 $1))) ((%8 ((%17 (%636 $2)) (%637
       $0))) ((%8 ((%638 %611) $1)) ((%638 %611) $2)))))))))))))))`)
  val num2PTR_PTR2num =
    DT(["DISK_THM"], [], `(%9 (\%10. ((%11 (%12 (%13 $0))) $0)))`)
  val PTR2num_num2PTR =
    DT(["DISK_THM"], [],
       `(%14 (\%15. ((%16 ((%4 $0) (%5 (%6 (%6 %7))))) ((%17 (%13 (%12
       $0))) $0))))`)
  val num2PTR_11 =
    DT(["DISK_THM"], [],
       `(%14 (\%15. (%14 (\%639. ((%83 ((%4 $1) (%5 (%6 (%6 %7))))) ((%83
       ((%4 $0) (%5 (%6 (%6 %7))))) ((%16 ((%11 (%12 $1)) (%12 $0))) ((%17
       $1) $0))))))))`)
  val PTR2num_11 =
    DT(["DISK_THM"], [],
       `(%9 (\%10. (%9 (\%640. ((%16 ((%17 (%13 $1)) (%13 $0))) ((%11 $1)
       $0))))))`)
  val num2PTR_ONTO =
    DT(["DISK_THM"], [],
       `(%9 (\%10. (%102 (\%15. ((%8 ((%11 $1) (%12 $0))) ((%4 $0) (%5 (%6
       (%6 %7)))))))))`)
  val PTR2num_ONTO =
    DT(["DISK_THM"], [],
       `(%14 (\%15. ((%16 ((%4 $0) (%5 (%6 (%6 %7))))) (%641 (\%10. ((%17
       $1) (%13 $0)))))))`)
  val num2PTR_thm =
    DT([], [],
       `((%8 ((%11 (%12 %19)) %18)) ((%8 ((%11 (%12 (%5 (%21 %7)))) %20))
       ((%8 ((%11 (%12 (%5 (%6 %7)))) %22)) ((%8 ((%11 (%12 (%5 (%21 (%21
       %7))))) %23)) ((%8 ((%11 (%12 (%5 (%6 (%21 %7))))) %24)) ((%11 (%12
       (%5 (%21 (%6 %7))))) %25))))))`)
  val PTR2num_thm =
    DT(["DISK_THM"], [],
       `((%8 ((%17 (%13 %18)) %19)) ((%8 ((%17 (%13 %20)) (%5 (%21 %7))))
       ((%8 ((%17 (%13 %22)) (%5 (%6 %7)))) ((%8 ((%17 (%13 %23)) (%5 (%21
       (%21 %7))))) ((%8 ((%17 (%13 %24)) (%5 (%6 (%21 %7))))) ((%17 (%13
       %25)) (%5 (%21 (%6 %7)))))))))`)
  val PTR_EQ_PTR =
    DT(["DISK_THM"], [],
       `(%9 (\%10. (%9 (\%640. ((%16 ((%11 $1) $0)) ((%17 (%13 $1)) (%13
       $0)))))))`)
  val PTR_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33.
       (%28 (\%34. ((%35 (((((((%36 $5) $4) $3) $2) $1) $0) %18))
       $5)))))))))))))) ((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28
       (\%32. (%28 (\%33. (%28 (\%34. ((%35 (((((((%36 $5) $4) $3) $2) $1)
       $0) %20)) $4)))))))))))))) ((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31.
       (%28 (\%32. (%28 (\%33. (%28 (\%34. ((%35 (((((((%36 $5) $4) $3) $2)
       $1) $0) %22)) $3)))))))))))))) ((%8 (%28 (\%29. (%28 (\%30. (%28
       (\%31. (%28 (\%32. (%28 (\%33. (%28 (\%34. ((%35 (((((((%36 $5) $4)
       $3) $2) $1) $0) %23)) $2)))))))))))))) ((%8 (%28 (\%29. (%28 (\%30.
       (%28 (\%31. (%28 (\%32. (%28 (\%33. (%28 (\%34. ((%35 (((((((%36 $5)
       $4) $3) $2) $1) $0) %24)) $1)))))))))))))) (%28 (\%29. (%28 (\%30.
       (%28 (\%31. (%28 (\%32. (%28 (\%33. (%28 (\%34. ((%35 (((((((%36 $5)
       $4) $3) $2) $1) $0) %25)) $0))))))))))))))))))`)
  val datatype_PTR =
    DT(["DISK_THM"], [], `(%642 ((((((%643 %18) %20) %22) %23) %24) %25))`)
  val PTR_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%418 ((%11 %18) %20))) ((%8 (%418 ((%11 %18) %22))) ((%8
       (%418 ((%11 %18) %23))) ((%8 (%418 ((%11 %18) %24))) ((%8 (%418
       ((%11 %18) %25))) ((%8 (%418 ((%11 %20) %22))) ((%8 (%418 ((%11 %20)
       %23))) ((%8 (%418 ((%11 %20) %24))) ((%8 (%418 ((%11 %20) %25)))
       ((%8 (%418 ((%11 %22) %23))) ((%8 (%418 ((%11 %22) %24))) ((%8 (%418
       ((%11 %22) %25))) ((%8 (%418 ((%11 %23) %24))) ((%8 (%418 ((%11 %23)
       %25))) (%418 ((%11 %24) %25))))))))))))))))`)
  val PTR_case_cong =
    DT(["DISK_THM"], [],
       `(%9 (\%644. (%9 (\%645. (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28
       (\%32. (%28 (\%33. (%28 (\%34. ((%83 ((%8 ((%11 $7) $6)) ((%8 ((%83
       ((%11 $6) %18)) ((%35 $5) %646))) ((%8 ((%83 ((%11 $6) %20)) ((%35
       $4) %647))) ((%8 ((%83 ((%11 $6) %22)) ((%35 $3) %648))) ((%8 ((%83
       ((%11 $6) %23)) ((%35 $2) %649))) ((%8 ((%83 ((%11 $6) %24)) ((%35
       $1) %650))) ((%83 ((%11 $6) %25)) ((%35 $0) %651))))))))) ((%35
       (((((((%36 $5) $4) $3) $2) $1) $0) $7)) (((((((%36 %646) %647) %648)
       %649) %650) %651) $6)))))))))))))))))))`)
  val PTR_nchotomy =
    DT(["DISK_THM"], [],
       `(%9 (\%10. ((%85 ((%11 $0) %18)) ((%85 ((%11 $0) %20)) ((%85 ((%11
       $0) %22)) ((%85 ((%11 $0) %23)) ((%85 ((%11 $0) %24)) ((%11 $0)
       %25))))))))`)
  val PTR_Axiom =
    DT(["DISK_THM"], [],
       `(%28 (\%652. (%28 (\%653. (%28 (\%207. (%28 (\%654. (%28 (\%655.
       (%28 (\%656. (%657 (\%658. ((%8 ((%35 ($0 %18)) $6)) ((%8 ((%35 ($0
       %20)) $5)) ((%8 ((%35 ($0 %22)) $4)) ((%8 ((%35 ($0 %23)) $3)) ((%8
       ((%35 ($0 %24)) $2)) ((%35 ($0 %25)) $1))))))))))))))))))))`)
  val PTR_induction =
    DT(["DISK_THM"], [],
       `(%659 (\%660. ((%83 ((%8 ($0 %22)) ((%8 ($0 %20)) ((%8 ($0 %23))
       ((%8 ($0 %25)) ((%8 ($0 %24)) ($0 %18))))))) (%9 (\%10. ($1
       $0))))))`)
  val toPTR_lem =
    DT(["DISK_THM"], [],
       `(%9 (\%661. ((%8 (%418 ((%17 (%39 $0)) %19))) ((%8 (%418 ((%17 (%39
       $0)) (%5 (%21 %7))))) ((%8 (%418 ((%17 (%39 $0)) (%5 (%6 %7)))))
       ((%8 (%418 ((%17 (%39 $0)) (%5 (%21 (%21 %7)))))) ((%8 (%418 ((%17
       (%39 $0)) (%5 (%6 (%21 %7)))))) ((%8 (%418 ((%17 (%39 $0)) (%5 (%21
       (%6 %7)))))) ((%8 (%418 ((%17 (%39 $0)) (%5 (%6 (%6 %7)))))) ((%8
       (%418 ((%17 (%39 $0)) (%5 (%21 (%21 (%21 %7))))))) (%418 ((%17 (%39
       $0)) (%5 (%6 (%21 (%21 %7))))))))))))))))`)
  val num2TREG_TREG2num =
    DT(["DISK_THM"], [], `(%49 (\%50. ((%51 (%52 (%53 $0))) $0)))`)
  val TREG2num_num2TREG =
    DT(["DISK_THM"], [],
       `(%14 (\%15. ((%16 ((%4 $0) (%5 (%21 (%6 (%21 %7)))))) ((%17 (%53
       (%52 $0))) $0))))`)
  val num2TREG_11 =
    DT(["DISK_THM"], [],
       `(%14 (\%15. (%14 (\%639. ((%83 ((%4 $1) (%5 (%21 (%6 (%21 %7))))))
       ((%83 ((%4 $0) (%5 (%21 (%6 (%21 %7)))))) ((%16 ((%51 (%52 $1)) (%52
       $0))) ((%17 $1) $0))))))))`)
  val TREG2num_11 =
    DT(["DISK_THM"], [],
       `(%49 (\%50. (%49 (\%662. ((%16 ((%17 (%53 $1)) (%53 $0))) ((%51 $1)
       $0))))))`)
  val num2TREG_ONTO =
    DT(["DISK_THM"], [],
       `(%49 (\%50. (%102 (\%15. ((%8 ((%51 $1) (%52 $0))) ((%4 $0) (%5
       (%21 (%6 (%21 %7))))))))))`)
  val TREG2num_ONTO =
    DT(["DISK_THM"], [],
       `(%14 (\%15. ((%16 ((%4 $0) (%5 (%21 (%6 (%21 %7)))))) (%86 (\%50.
       ((%17 $1) (%53 $0)))))))`)
  val num2TREG_thm =
    DT([], [],
       `((%8 ((%51 (%52 %19)) %54)) ((%8 ((%51 (%52 (%5 (%21 %7)))) %55))
       ((%8 ((%51 (%52 (%5 (%6 %7)))) %56)) ((%8 ((%51 (%52 (%5 (%21 (%21
       %7))))) %57)) ((%8 ((%51 (%52 (%5 (%6 (%21 %7))))) %58)) ((%8 ((%51
       (%52 (%5 (%21 (%6 %7))))) %59)) ((%8 ((%51 (%52 (%5 (%6 (%6 %7)))))
       %60)) ((%8 ((%51 (%52 (%5 (%21 (%21 (%21 %7)))))) %61)) ((%51 (%52
       (%5 (%6 (%21 (%21 %7)))))) %62)))))))))`)
  val TREG2num_thm =
    DT(["DISK_THM"], [],
       `((%8 ((%17 (%53 %54)) %19)) ((%8 ((%17 (%53 %55)) (%5 (%21 %7))))
       ((%8 ((%17 (%53 %56)) (%5 (%6 %7)))) ((%8 ((%17 (%53 %57)) (%5 (%21
       (%21 %7))))) ((%8 ((%17 (%53 %58)) (%5 (%6 (%21 %7))))) ((%8 ((%17
       (%53 %59)) (%5 (%21 (%6 %7))))) ((%8 ((%17 (%53 %60)) (%5 (%6 (%6
       %7))))) ((%8 ((%17 (%53 %61)) (%5 (%21 (%21 (%21 %7)))))) ((%17 (%53
       %62)) (%5 (%6 (%21 (%21 %7)))))))))))))`)
  val TREG_EQ_TREG =
    DT(["DISK_THM"], [],
       `(%49 (\%50. (%49 (\%662. ((%16 ((%51 $1) $0)) ((%17 (%53 $1)) (%53
       $0)))))))`)
  val TREG_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33.
       (%28 (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. ((%35 ((((((((((%68
       $8) $7) $6) $5) $4) $3) $2) $1) $0) %54)) $8))))))))))))))))))))
       ((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33.
       (%28 (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. ((%35 ((((((((((%68
       $8) $7) $6) $5) $4) $3) $2) $1) $0) %55)) $7))))))))))))))))))))
       ((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33.
       (%28 (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. ((%35 ((((((((((%68
       $8) $7) $6) $5) $4) $3) $2) $1) $0) %56)) $6))))))))))))))))))))
       ((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33.
       (%28 (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. ((%35 ((((((((((%68
       $8) $7) $6) $5) $4) $3) $2) $1) $0) %57)) $5))))))))))))))))))))
       ((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33.
       (%28 (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. ((%35 ((((((((((%68
       $8) $7) $6) $5) $4) $3) $2) $1) $0) %58)) $4))))))))))))))))))))
       ((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33.
       (%28 (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. ((%35 ((((((((((%68
       $8) $7) $6) $5) $4) $3) $2) $1) $0) %59)) $3))))))))))))))))))))
       ((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33.
       (%28 (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. ((%35 ((((((((((%68
       $8) $7) $6) $5) $4) $3) $2) $1) $0) %60)) $2))))))))))))))))))))
       ((%8 (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33.
       (%28 (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. ((%35 ((((((((((%68
       $8) $7) $6) $5) $4) $3) $2) $1) $0) %61)) $1))))))))))))))))))))
       (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28 (\%32. (%28 (\%33. (%28
       (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67. ((%35 ((((((((((%68 $8)
       $7) $6) $5) $4) $3) $2) $1) $0) %62))
       $0)))))))))))))))))))))))))))`)
  val datatype_TREG =
    DT(["DISK_THM"], [],
       `(%642 (((((((((%663 %54) %55) %56) %57) %58) %59) %60) %61) %62))`)
  val TREG_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%418 ((%51 %54) %55))) ((%8 (%418 ((%51 %54) %56))) ((%8
       (%418 ((%51 %54) %57))) ((%8 (%418 ((%51 %54) %58))) ((%8 (%418
       ((%51 %54) %59))) ((%8 (%418 ((%51 %54) %60))) ((%8 (%418 ((%51 %54)
       %61))) ((%8 (%418 ((%51 %54) %62))) ((%8 (%418 ((%51 %55) %56)))
       ((%8 (%418 ((%51 %55) %57))) ((%8 (%418 ((%51 %55) %58))) ((%8 (%418
       ((%51 %55) %59))) ((%8 (%418 ((%51 %55) %60))) ((%8 (%418 ((%51 %55)
       %61))) ((%8 (%418 ((%51 %55) %62))) ((%8 (%418 ((%51 %56) %57)))
       ((%8 (%418 ((%51 %56) %58))) ((%8 (%418 ((%51 %56) %59))) ((%8 (%418
       ((%51 %56) %60))) ((%8 (%418 ((%51 %56) %61))) ((%8 (%418 ((%51 %56)
       %62))) ((%8 (%418 ((%51 %57) %58))) ((%8 (%418 ((%51 %57) %59)))
       ((%8 (%418 ((%51 %57) %60))) ((%8 (%418 ((%51 %57) %61))) ((%8 (%418
       ((%51 %57) %62))) ((%8 (%418 ((%51 %58) %59))) ((%8 (%418 ((%51 %58)
       %60))) ((%8 (%418 ((%51 %58) %61))) ((%8 (%418 ((%51 %58) %62)))
       ((%8 (%418 ((%51 %59) %60))) ((%8 (%418 ((%51 %59) %61))) ((%8 (%418
       ((%51 %59) %62))) ((%8 (%418 ((%51 %60) %61))) ((%8 (%418 ((%51 %60)
       %62))) (%418 ((%51 %61) %62)))))))))))))))))))))))))))))))))))))`)
  val TREG_case_cong =
    DT(["DISK_THM"], [],
       `(%49 (\%664. (%49 (\%665. (%28 (\%29. (%28 (\%30. (%28 (\%31. (%28
       (\%32. (%28 (\%33. (%28 (\%34. (%28 (\%65. (%28 (\%66. (%28 (\%67.
       ((%83 ((%8 ((%51 $10) $9)) ((%8 ((%83 ((%51 $9) %54)) ((%35 $8)
       %646))) ((%8 ((%83 ((%51 $9) %55)) ((%35 $7) %647))) ((%8 ((%83
       ((%51 $9) %56)) ((%35 $6) %648))) ((%8 ((%83 ((%51 $9) %57)) ((%35
       $5) %649))) ((%8 ((%83 ((%51 $9) %58)) ((%35 $4) %650))) ((%8 ((%83
       ((%51 $9) %59)) ((%35 $3) %651))) ((%8 ((%83 ((%51 $9) %60)) ((%35
       $2) %666))) ((%8 ((%83 ((%51 $9) %61)) ((%35 $1) %667))) ((%83 ((%51
       $9) %62)) ((%35 $0) %668)))))))))))) ((%35 ((((((((((%68 $8) $7) $6)
       $5) $4) $3) $2) $1) $0) $10)) ((((((((((%68 %646) %647) %648) %649)
       %650) %651) %666) %667) %668) $9)))))))))))))))))))))))))`)
  val TREG_nchotomy =
    DT(["DISK_THM"], [],
       `(%49 (\%50. ((%85 ((%51 $0) %54)) ((%85 ((%51 $0) %55)) ((%85 ((%51
       $0) %56)) ((%85 ((%51 $0) %57)) ((%85 ((%51 $0) %58)) ((%85 ((%51
       $0) %59)) ((%85 ((%51 $0) %60)) ((%85 ((%51 $0) %61)) ((%51 $0)
       %62)))))))))))`)
  val TREG_Axiom =
    DT(["DISK_THM"], [],
       `(%28 (\%652. (%28 (\%653. (%28 (\%207. (%28 (\%654. (%28 (\%655.
       (%28 (\%656. (%28 (\%669. (%28 (\%670. (%28 (\%671. (%672 (\%120.
       ((%8 ((%35 ($0 %54)) $9)) ((%8 ((%35 ($0 %55)) $8)) ((%8 ((%35 ($0
       %56)) $7)) ((%8 ((%35 ($0 %57)) $6)) ((%8 ((%35 ($0 %58)) $5)) ((%8
       ((%35 ($0 %59)) $4)) ((%8 ((%35 ($0 %60)) $3)) ((%8 ((%35 ($0 %61))
       $2)) ((%35 ($0 %62)) $1)))))))))))))))))))))))))))))`)
  val TREG_induction =
    DT(["DISK_THM"], [],
       `(%673 (\%674. ((%83 ((%8 ($0 %54)) ((%8 ($0 %55)) ((%8 ($0 %56))
       ((%8 ($0 %57)) ((%8 ($0 %58)) ((%8 ($0 %59)) ((%8 ($0 %60)) ((%8 ($0
       %61)) ($0 %62)))))))))) (%49 (\%50. ($1 $0))))))`)
  val data_reg_name_lem =
    DT(["DISK_THM"], [],
       `(%49 (\%154. ((%8 ((%16 ((%17 (%69 $0)) %19)) ((%51 $0) %54))) ((%8
       ((%16 ((%17 (%69 $0)) (%5 (%21 %7)))) ((%51 $0) %55))) ((%8 ((%16
       ((%17 (%69 $0)) (%5 (%6 %7)))) ((%51 $0) %56))) ((%8 ((%16 ((%17
       (%69 $0)) (%5 (%21 (%21 %7))))) ((%51 $0) %57))) ((%8 ((%16 ((%17
       (%69 $0)) (%5 (%6 (%21 %7))))) ((%51 $0) %58))) ((%8 ((%16 ((%17
       (%69 $0)) (%5 (%21 (%6 %7))))) ((%51 $0) %59))) ((%8 ((%16 ((%17
       (%69 $0)) (%5 (%6 (%6 %7))))) ((%51 $0) %60))) ((%8 ((%16 ((%17 (%69
       $0)) (%5 (%21 (%21 (%21 %7)))))) ((%51 $0) %61))) ((%16 ((%17 (%69
       $0)) (%5 (%6 (%21 (%21 %7)))))) ((%51 $0) %62))))))))))))`)
  val data_reg_name_thm =
    DT(["DISK_THM"], [],
       `((%8 ((%51 (%71 %19)) %54)) ((%8 ((%51 (%71 (%5 (%21 %7)))) %55))
       ((%8 ((%51 (%71 (%5 (%6 %7)))) %56)) ((%8 ((%51 (%71 (%5 (%21 (%21
       %7))))) %57)) ((%8 ((%51 (%71 (%5 (%6 (%21 %7))))) %58)) ((%8 ((%51
       (%71 (%5 (%21 (%6 %7))))) %59)) ((%8 ((%51 (%71 (%5 (%6 (%6 %7)))))
       %60)) ((%8 ((%51 (%71 (%5 (%21 (%21 (%21 %7)))))) %61)) ((%51 (%71
       (%5 (%6 (%21 (%21 %7)))))) %62)))))))))`)
  val toPTR_lem_2 =
    DT(["DISK_THM"], [],
       `(%9 (\%661. (%49 (\%154. (%418 ((%17 (%39 $1)) (%69 $0)))))))`)
  val conv_reg_thm =
    DT(["DISK_THM"], [],
       `((%8 ((%675 (%74 %54)) %676)) ((%8 ((%675 (%74 %55)) %677)) ((%8
       ((%675 (%74 %56)) %678)) ((%8 ((%675 (%74 %57)) %679)) ((%8 ((%675
       (%74 %58)) %680)) ((%8 ((%675 (%74 %59)) %681)) ((%8 ((%675 (%74
       %60)) %682)) ((%8 ((%675 (%74 %61)) %683)) ((%675 (%74 %62))
       %684)))))))))`)
  val CONV_REG_LEM =
    DT(["DISK_THM"], [],
       `(%49 (\%154. (%49 (\%547. ((%8 ((%17 (%69 $1)) (%216 (%74 $1))))
       ((%83 ((%17 (%69 $1)) (%69 $0))) ((%51 $1) $0)))))))`)
  val FORALL_TSTATE =
    DT(["DISK_THM"], [],
       `((%16 (%174 (\%396. (%685 $0)))) (%686 (\%168. (%687 (\%169. (%685
       ((%488 $1) $0)))))))`)
  val datatype_TEXP =
    DT(["DISK_THM"], [], `(%642 (((%688 %116) %117) %118))`)
  val TEXP_11 =
    DT(["DISK_THM"], [],
       `((%8 (%49 (\%50. (%49 (\%662. ((%16 ((%106 (%116 $1)) (%116 $0)))
       ((%51 $1) $0))))))) ((%8 (%126 (\%98. (%126 (\%689. ((%16 ((%106
       (%117 $1)) (%117 $0))) ((%177 $1) $0))))))) (%14 (\%103. (%14
       (\%690. ((%16 ((%106 (%118 $1)) (%118 $0))) ((%17 $1) $0))))))))`)
  val TEXP_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%126 (\%689. (%49 (\%50. (%418 ((%106 (%116 $0)) (%117
       $1)))))))) ((%8 (%14 (\%690. (%49 (\%50. (%418 ((%106 (%116 $0))
       (%118 $1)))))))) (%14 (\%690. (%126 (\%98. (%418 ((%106 (%117 $0))
       (%118 $1)))))))))`)
  val TEXP_case_cong =
    DT(["DISK_THM"], [],
       `(%104 (\%691. (%104 (\%692. (%119 (\%120. (%121 (\%122. (%123
       (\%124. ((%83 ((%8 ((%106 $4) $3)) ((%8 (%49 (\%50. ((%83 ((%106 $4)
       (%116 $0))) ((%35 ($3 $0)) (%693 $0)))))) ((%8 (%126 (\%98. ((%83
       ((%106 $4) (%117 $0))) ((%35 ($2 $0)) (%694 $0)))))) (%14 (\%103.
       ((%83 ((%106 $4) (%118 $0))) ((%35 ($1 $0)) (%695 $0))))))))) ((%35
       ((((%125 $2) $1) $0) $4)) ((((%125 %693) %694) %695)
       $3)))))))))))))`)
  val TEXP_nchotomy =
    DT(["DISK_THM"], [],
       `(%104 (\%696. ((%85 (%86 (\%697. ((%106 $1) (%116 $0))))) ((%85
       (%97 (\%619. ((%106 $1) (%117 $0))))) (%102 (\%3. ((%106 $1) (%118
       $0))))))))`)
  val TEXP_Axiom =
    DT(["DISK_THM"], [],
       `(%119 (\%698. (%121 (\%122. (%123 (\%124. (%699 (\%700. ((%8 (%49
       (\%50. ((%35 ($1 (%116 $0))) ($4 $0))))) ((%8 (%126 (\%98. ((%35 ($1
       (%117 $0))) ($3 $0))))) (%14 (\%103. ((%35 ($1 (%118 $0))) ($2
       $0))))))))))))))`)
  val TEXP_induction =
    DT(["DISK_THM"], [],
       `(%701 (\%702. ((%83 ((%8 (%49 (\%697. ($1 (%116 $0))))) ((%8 (%126
       (\%619. ($1 (%117 $0))))) (%14 (\%3. ($1 (%118 $0))))))) (%104
       (\%696. ($1 $0))))))`)
  val datatype_TROC = DT(["DISK_THM"], [], `(%642 ((%703 %150) %151))`)
  val TROC_11 =
    DT(["DISK_THM"], [],
       `((%8 (%49 (\%50. (%49 (\%662. ((%16 ((%142 (%150 $1)) (%150 $0)))
       ((%51 $1) $0))))))) (%126 (\%98. (%126 (\%689. ((%16 ((%142 (%151
       $1)) (%151 $0))) ((%177 $1) $0)))))))`)
  val TROC_distinct =
    DT(["DISK_THM"], [],
       `(%126 (\%689. (%49 (\%50. (%418 ((%142 (%150 $0)) (%151 $1)))))))`)
  val TROC_case_cong =
    DT(["DISK_THM"], [],
       `(%140 (\%704. (%140 (\%705. (%119 (\%120. (%121 (\%122. ((%83 ((%8
       ((%142 $3) $2)) ((%8 (%49 (\%50. ((%83 ((%142 $3) (%150 $0))) ((%35
       ($2 $0)) (%693 $0)))))) (%126 (\%98. ((%83 ((%142 $3) (%151 $0)))
       ((%35 ($1 $0)) (%694 $0)))))))) ((%35 (((%152 $1) $0) $3)) (((%152
       %693) %694) $2)))))))))))`)
  val TROC_nchotomy =
    DT(["DISK_THM"], [],
       `(%140 (\%706. ((%85 (%86 (\%697. ((%142 $1) (%150 $0))))) (%97
       (\%619. ((%142 $1) (%151 $0)))))))`)
  val TROC_Axiom =
    DT(["DISK_THM"], [],
       `(%119 (\%698. (%121 (\%122. (%707 (\%708. ((%8 (%49 (\%50. ((%35
       ($1 (%150 $0))) ($3 $0))))) (%126 (\%98. ((%35 ($1 (%151 $0))) ($2
       $0)))))))))))`)
  val TROC_induction =
    DT(["DISK_THM"], [],
       `(%709 (\%710. ((%83 ((%8 (%49 (\%697. ($1 (%150 $0))))) (%126
       (\%619. ($1 (%151 $0)))))) (%140 (\%706. ($1 $0))))))`)
  val tread_ind =
    DT(["DISK_THM"], [],
       `(%711 (\%712. ((%83 ((%8 (%686 (\%168. (%687 (\%169. (%14 (\%70.
       (($3 ((%488 $2) $1)) (%118 $0))))))))) ((%8 (%686 (\%168. (%687
       (\%169. (%126 (\%92. (($3 ((%488 $2) $1)) (%117 $0))))))))) (%686
       (\%168. (%687 (\%169. (%49 (\%154. (($3 ((%488 $2) $1)) (%116
       $0))))))))))) (%686 (\%713. (%687 (\%714. (%104 (\%166. (($3 ((%488
       $2) $1)) $0))))))))))`)
  val tread_def =
    DT(["DISK_THM"], [],
       `((%8 ((%177 ((%178 ((%488 %168) %169)) (%118 %70))) ((%173 %169)
       %70))) ((%8 ((%177 ((%178 ((%488 %168) %169)) (%117 %92))) %92))
       ((%177 ((%178 ((%488 %168) %169)) (%116 %154))) ((%172 %168)
       %154))))`)
  val twrite_ind =
    DT(["DISK_THM"], [],
       `(%715 (\%716. ((%83 ((%8 (%717 (\%192. (%718 (\%193. (%14 (\%70.
       (%28 (\%196. ((($4 ((%199 $3) $2)) (%118 $1)) $0)))))))))) ((%8
       (%717 (\%192. (%718 (\%193. (%49 (\%154. (%28 (\%196. ((($4 ((%199
       $3) $2)) (%116 $1)) $0)))))))))) (%717 (\%192. (%718 (\%193. (%126
       (\%202. (%28 (\%196. ((($4 ((%199 $3) $2)) (%117 $1)) $0))))))))))))
       (%717 (\%719. (%718 (\%720. (%104 (\%166. (%28 (\%32. ((($4 ((%199
       $3) $2)) $1) $0))))))))))))`)
  val twrite_def =
    DT(["DISK_THM"], [],
       `((%8 ((%208 (((%209 ((%199 %192) %193)) (%118 %70)) %196)) ((%199
       %192) ((%203 %193) ((%204 %70) %196))))) ((%8 ((%208 (((%209 ((%199
       %192) %193)) (%116 %154)) %196)) ((%199 ((%200 %192) ((%201 %154)
       %196))) %193))) ((%208 (((%209 ((%199 %192) %193)) (%117 %202))
       %196)) ((%199 %192) %193))))`)
  val datatype_TOPER =
    DT(["DISK_THM"], [],
       `(%642 ((((((((((((((%721 %270) %271) %272) %273) %274) %275) %276)
       %277) %278) %279) %280) %281) %282) %283))`)
  val TOPER_11 =
    DT(["DISK_THM"], [],
       `((%8 (%49 (\%225. (%14 (\%226. (%49 (\%722. (%14 (\%723. ((%16
       ((%247 ((%270 $3) $2)) ((%270 $1) $0))) ((%8 ((%51 $3) $1)) ((%17
       $2) $0)))))))))))) ((%8 (%14 (\%238. (%49 (\%239. (%14 (\%724. (%49
       (\%725. ((%16 ((%247 ((%271 $3) $2)) ((%271 $1) $0))) ((%8 ((%17 $3)
       $1)) ((%51 $2) $0)))))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%49
       (\%722. (%140 (\%726. ((%16 ((%247 ((%272 $3) $2)) ((%272 $1) $0)))
       ((%8 ((%51 $3) $1)) ((%142 $2) $0)))))))))))) ((%8 (%49 (\%225.
       (%140 (\%241. (%140 (\%242. (%49 (\%722. (%140 (\%726. (%140 (\%727.
       ((%16 ((%247 (((%273 $5) $4) $3)) (((%273 $2) $1) $0))) ((%8 ((%51
       $5) $2)) ((%8 ((%142 $4) $1)) ((%142 $3) $0))))))))))))))))) ((%8
       (%49 (\%225. (%140 (\%241. (%140 (\%242. (%49 (\%722. (%140 (\%726.
       (%140 (\%727. ((%16 ((%247 (((%274 $5) $4) $3)) (((%274 $2) $1)
       $0))) ((%8 ((%51 $5) $2)) ((%8 ((%142 $4) $1)) ((%142 $3)
       $0))))))))))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242.
       (%49 (\%722. (%140 (\%726. (%140 (\%727. ((%16 ((%247 (((%275 $5)
       $4) $3)) (((%275 $2) $1) $0))) ((%8 ((%51 $5) $2)) ((%8 ((%142 $4)
       $1)) ((%142 $3) $0))))))))))))))))) ((%8 (%49 (\%225. (%140 (\%241.
       (%140 (\%242. (%49 (\%722. (%140 (\%726. (%140 (\%727. ((%16 ((%247
       (((%276 $5) $4) $3)) (((%276 $2) $1) $0))) ((%8 ((%51 $5) $2)) ((%8
       ((%142 $4) $1)) ((%142 $3) $0))))))))))))))))) ((%8 (%49 (\%225.
       (%140 (\%241. (%140 (\%242. (%49 (\%722. (%140 (\%726. (%140 (\%727.
       ((%16 ((%247 (((%277 $5) $4) $3)) (((%277 $2) $1) $0))) ((%8 ((%51
       $5) $2)) ((%8 ((%142 $4) $1)) ((%142 $3) $0))))))))))))))))) ((%8
       (%49 (\%225. (%140 (\%241. (%140 (\%242. (%49 (\%722. (%140 (\%726.
       (%140 (\%727. ((%16 ((%247 (((%278 $5) $4) $3)) (((%278 $2) $1)
       $0))) ((%8 ((%51 $5) $2)) ((%8 ((%142 $4) $1)) ((%142 $3)
       $0))))))))))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242.
       (%49 (\%722. (%140 (\%726. (%140 (\%727. ((%16 ((%247 (((%279 $5)
       $4) $3)) (((%279 $2) $1) $0))) ((%8 ((%51 $5) $2)) ((%8 ((%142 $4)
       $1)) ((%142 $3) $0))))))))))))))))) ((%8 (%49 (\%225. (%140 (\%241.
       (%304 (\%244. (%49 (\%722. (%140 (\%726. (%304 (\%728. ((%16 ((%247
       (((%280 $5) $4) $3)) (((%280 $2) $1) $0))) ((%8 ((%51 $5) $2)) ((%8
       ((%142 $4) $1)) ((%729 $3) $0))))))))))))))))) ((%8 (%49 (\%225.
       (%140 (\%241. (%304 (\%244. (%49 (\%722. (%140 (\%726. (%304 (\%728.
       ((%16 ((%247 (((%281 $5) $4) $3)) (((%281 $2) $1) $0))) ((%8 ((%51
       $5) $2)) ((%8 ((%142 $4) $1)) ((%729 $3) $0))))))))))))))))) ((%8
       (%49 (\%225. (%140 (\%241. (%304 (\%244. (%49 (\%722. (%140 (\%726.
       (%304 (\%728. ((%16 ((%247 (((%282 $5) $4) $3)) (((%282 $2) $1)
       $0))) ((%8 ((%51 $5) $2)) ((%8 ((%142 $4) $1)) ((%729 $3)
       $0))))))))))))))))) (%49 (\%225. (%140 (\%241. (%304 (\%244. (%49
       (\%722. (%140 (\%726. (%304 (\%728. ((%16 ((%247 (((%283 $5) $4)
       $3)) (((%283 $2) $1) $0))) ((%8 ((%51 $5) $2)) ((%8 ((%142 $4) $1))
       ((%729 $3) $0)))))))))))))))))))))))))))))`)
  val TOPER_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%49 (\%725. (%14 (\%226. (%14 (\%724. (%49 (\%225. (%418
       ((%247 ((%270 $0) $2)) ((%271 $1) $3)))))))))))) ((%8 (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       ((%272 $1) $3)))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%14
       (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%273 $1) $3) $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%274 $1) $3) $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%275 $1) $3) $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%276 $1) $3) $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%277 $1) $3) $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%278 $1) $3) $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%279 $1) $3) $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%280 $1) $3) $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%281 $1) $3) $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%282 $1) $3) $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726.
       (%14 (\%226. (%49 (\%722. (%49 (\%225. (%418 ((%247 ((%270 $0) $2))
       (((%283 $1) $3) $4)))))))))))))) ((%8 (%140 (\%726. (%49 (\%239.
       (%49 (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) ((%272 $1)
       $3)))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%273 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%274 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%275 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%276 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%277 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%278 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%279 $1) $3)
       $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%280 $1) $3)
       $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%281 $1) $3)
       $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%282 $1) $3)
       $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726. (%49 (\%239. (%49
       (\%722. (%14 (\%238. (%418 ((%247 ((%271 $0) $2)) (((%283 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%273 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%274 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%275 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%276 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%277 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%278 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%279 $1) $3)
       $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%280 $1) $3)
       $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%281 $1) $3)
       $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%282 $1) $3)
       $4)))))))))))))) ((%8 (%304 (\%244. (%140 (\%726. (%140 (\%241. (%49
       (\%722. (%49 (\%225. (%418 ((%247 ((%272 $0) $2)) (((%283 $1) $3)
       $4)))))))))))))) ((%8 (%140 (\%727. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%273 $0) $2)
       $4)) (((%274 $1) $3) $5)))))))))))))))) ((%8 (%140 (\%727. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%273 $0) $2) $4)) (((%275 $1) $3) $5)))))))))))))))) ((%8
       (%140 (\%727. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%273 $0) $2) $4)) (((%276 $1) $3)
       $5)))))))))))))))) ((%8 (%140 (\%727. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%273 $0) $2)
       $4)) (((%277 $1) $3) $5)))))))))))))))) ((%8 (%140 (\%727. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%273 $0) $2) $4)) (((%278 $1) $3) $5)))))))))))))))) ((%8
       (%140 (\%727. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%273 $0) $2) $4)) (((%279 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%273 $0) $2)
       $4)) (((%280 $1) $3) $5)))))))))))))))) ((%8 (%304 (\%728. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%273 $0) $2) $4)) (((%281 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%273 $0) $2) $4)) (((%282 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%273 $0) $2)
       $4)) (((%283 $1) $3) $5)))))))))))))))) ((%8 (%140 (\%727. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%274 $0) $2) $4)) (((%275 $1) $3) $5)))))))))))))))) ((%8
       (%140 (\%727. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%274 $0) $2) $4)) (((%276 $1) $3)
       $5)))))))))))))))) ((%8 (%140 (\%727. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%274 $0) $2)
       $4)) (((%277 $1) $3) $5)))))))))))))))) ((%8 (%140 (\%727. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%274 $0) $2) $4)) (((%278 $1) $3) $5)))))))))))))))) ((%8
       (%140 (\%727. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%274 $0) $2) $4)) (((%279 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%274 $0) $2)
       $4)) (((%280 $1) $3) $5)))))))))))))))) ((%8 (%304 (\%728. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%274 $0) $2) $4)) (((%281 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%274 $0) $2) $4)) (((%282 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%274 $0) $2)
       $4)) (((%283 $1) $3) $5)))))))))))))))) ((%8 (%140 (\%727. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%275 $0) $2) $4)) (((%276 $1) $3) $5)))))))))))))))) ((%8
       (%140 (\%727. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%275 $0) $2) $4)) (((%277 $1) $3)
       $5)))))))))))))))) ((%8 (%140 (\%727. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%275 $0) $2)
       $4)) (((%278 $1) $3) $5)))))))))))))))) ((%8 (%140 (\%727. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%275 $0) $2) $4)) (((%279 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%275 $0) $2) $4)) (((%280 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%275 $0) $2)
       $4)) (((%281 $1) $3) $5)))))))))))))))) ((%8 (%304 (\%728. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%275 $0) $2) $4)) (((%282 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%275 $0) $2) $4)) (((%283 $1) $3)
       $5)))))))))))))))) ((%8 (%140 (\%727. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%276 $0) $2)
       $4)) (((%277 $1) $3) $5)))))))))))))))) ((%8 (%140 (\%727. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%276 $0) $2) $4)) (((%278 $1) $3) $5)))))))))))))))) ((%8
       (%140 (\%727. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%276 $0) $2) $4)) (((%279 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%276 $0) $2)
       $4)) (((%280 $1) $3) $5)))))))))))))))) ((%8 (%304 (\%728. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%276 $0) $2) $4)) (((%281 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%276 $0) $2) $4)) (((%282 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%276 $0) $2)
       $4)) (((%283 $1) $3) $5)))))))))))))))) ((%8 (%140 (\%727. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%277 $0) $2) $4)) (((%278 $1) $3) $5)))))))))))))))) ((%8
       (%140 (\%727. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%277 $0) $2) $4)) (((%279 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%277 $0) $2)
       $4)) (((%280 $1) $3) $5)))))))))))))))) ((%8 (%304 (\%728. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%277 $0) $2) $4)) (((%281 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%277 $0) $2) $4)) (((%282 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%277 $0) $2)
       $4)) (((%283 $1) $3) $5)))))))))))))))) ((%8 (%140 (\%727. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%278 $0) $2) $4)) (((%279 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%278 $0) $2) $4)) (((%280 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%278 $0) $2)
       $4)) (((%281 $1) $3) $5)))))))))))))))) ((%8 (%304 (\%728. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%278 $0) $2) $4)) (((%282 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%278 $0) $2) $4)) (((%283 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%279 $0) $2)
       $4)) (((%280 $1) $3) $5)))))))))))))))) ((%8 (%304 (\%728. (%140
       (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%279 $0) $2) $4)) (((%281 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%140 (\%242. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%279 $0) $2) $4)) (((%282 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%140 (\%242. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%279 $0) $2)
       $4)) (((%283 $1) $3) $5)))))))))))))))) ((%8 (%304 (\%728. (%304
       (\%244. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%280 $0) $2) $4)) (((%281 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%304 (\%244. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%280 $0) $2) $4)) (((%282 $1) $3)
       $5)))))))))))))))) ((%8 (%304 (\%728. (%304 (\%244. (%140 (\%726.
       (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%280 $0) $2)
       $4)) (((%283 $1) $3) $5)))))))))))))))) ((%8 (%304 (\%728. (%304
       (\%244. (%140 (\%726. (%140 (\%241. (%49 (\%722. (%49 (\%225. (%418
       ((%247 (((%281 $0) $2) $4)) (((%282 $1) $3) $5)))))))))))))))) ((%8
       (%304 (\%728. (%304 (\%244. (%140 (\%726. (%140 (\%241. (%49 (\%722.
       (%49 (\%225. (%418 ((%247 (((%281 $0) $2) $4)) (((%283 $1) $3)
       $5)))))))))))))))) (%304 (\%728. (%304 (\%244. (%140 (\%726. (%140
       (\%241. (%49 (\%722. (%49 (\%225. (%418 ((%247 (((%282 $0) $2) $4))
       (((%283 $1) $3)
       $5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val TOPER_case_cong =
    DT(["DISK_THM"], [],
       `(%245 (\%730. (%245 (\%731. (%284 (\%285. (%286 (\%287. (%288
       (\%289. (%290 (\%291. (%290 (\%292. (%290 (\%293. (%290 (\%294.
       (%290 (\%295. (%290 (\%296. (%290 (\%297. (%298 (\%299. (%298
       (\%300. (%298 (\%301. (%298 (\%302. ((%83 ((%8 ((%247 $15) $14))
       ((%8 (%49 (\%225. (%14 (\%226. ((%83 ((%247 $16) ((%270 $1) $0)))
       ((%35 (($15 $1) $0)) ((%732 $1) $0)))))))) ((%8 (%14 (\%238. (%49
       (\%239. ((%83 ((%247 $16) ((%271 $1) $0))) ((%35 (($14 $1) $0))
       ((%733 $1) $0)))))))) ((%8 (%49 (\%225. (%140 (\%241. ((%83 ((%247
       $16) ((%272 $1) $0))) ((%35 (($13 $1) $0)) ((%734 $1) $0))))))))
       ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242. ((%83 ((%247 $17)
       (((%273 $2) $1) $0))) ((%35 ((($13 $2) $1) $0)) (((%735 $2) $1)
       $0)))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242. ((%83
       ((%247 $17) (((%274 $2) $1) $0))) ((%35 ((($12 $2) $1) $0)) (((%736
       $2) $1) $0)))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242.
       ((%83 ((%247 $17) (((%275 $2) $1) $0))) ((%35 ((($11 $2) $1) $0))
       (((%737 $2) $1) $0)))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140
       (\%242. ((%83 ((%247 $17) (((%276 $2) $1) $0))) ((%35 ((($10 $2) $1)
       $0)) (((%738 $2) $1) $0)))))))))) ((%8 (%49 (\%225. (%140 (\%241.
       (%140 (\%242. ((%83 ((%247 $17) (((%277 $2) $1) $0))) ((%35 ((($9
       $2) $1) $0)) (((%739 $2) $1) $0)))))))))) ((%8 (%49 (\%225. (%140
       (\%241. (%140 (\%242. ((%83 ((%247 $17) (((%278 $2) $1) $0))) ((%35
       ((($8 $2) $1) $0)) (((%740 $2) $1) $0)))))))))) ((%8 (%49 (\%225.
       (%140 (\%241. (%140 (\%242. ((%83 ((%247 $17) (((%279 $2) $1) $0)))
       ((%35 ((($7 $2) $1) $0)) (((%741 $2) $1) $0)))))))))) ((%8 (%49
       (\%225. (%140 (\%241. (%304 (\%244. ((%83 ((%247 $17) (((%280 $2)
       $1) $0))) ((%35 ((($6 $2) $1) $0)) (((%742 $2) $1) $0)))))))))) ((%8
       (%49 (\%225. (%140 (\%241. (%304 (\%244. ((%83 ((%247 $17) (((%281
       $2) $1) $0))) ((%35 ((($5 $2) $1) $0)) (((%743 $2) $1) $0))))))))))
       ((%8 (%49 (\%225. (%140 (\%241. (%304 (\%244. ((%83 ((%247 $17)
       (((%282 $2) $1) $0))) ((%35 ((($4 $2) $1) $0)) (((%744 $2) $1)
       $0)))))))))) (%49 (\%225. (%140 (\%241. (%304 (\%244. ((%83 ((%247
       $17) (((%283 $2) $1) $0))) ((%35 ((($3 $2) $1) $0)) (((%745 $2) $1)
       $0)))))))))))))))))))))))) ((%35 (((((((((((((((%303 $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) $15))
       (((((((((((((((%303 %732) %733) %734) %735) %736) %737) %738) %739)
       %740) %741) %742) %743) %744) %745)
       $14)))))))))))))))))))))))))))))))))))`)
  val TOPER_nchotomy =
    DT(["DISK_THM"], [],
       `(%245 (\%746. ((%85 (%86 (\%697. (%102 (\%3. ((%247 $2) ((%270 $1)
       $0))))))) ((%85 (%102 (\%3. (%86 (\%697. ((%247 $2) ((%271 $1)
       $0))))))) ((%85 (%86 (\%697. (%240 (\%747. ((%247 $2) ((%272 $1)
       $0))))))) ((%85 (%86 (\%697. (%240 (\%747. (%240 (\%748. ((%247 $3)
       (((%273 $2) $1) $0))))))))) ((%85 (%86 (\%697. (%240 (\%747. (%240
       (\%748. ((%247 $3) (((%274 $2) $1) $0))))))))) ((%85 (%86 (\%697.
       (%240 (\%747. (%240 (\%748. ((%247 $3) (((%275 $2) $1) $0)))))))))
       ((%85 (%86 (\%697. (%240 (\%747. (%240 (\%748. ((%247 $3) (((%276
       $2) $1) $0))))))))) ((%85 (%86 (\%697. (%240 (\%747. (%240 (\%748.
       ((%247 $3) (((%277 $2) $1) $0))))))))) ((%85 (%86 (\%697. (%240
       (\%747. (%240 (\%748. ((%247 $3) (((%278 $2) $1) $0))))))))) ((%85
       (%86 (\%697. (%240 (\%747. (%240 (\%748. ((%247 $3) (((%279 $2) $1)
       $0))))))))) ((%85 (%86 (\%697. (%240 (\%747. (%243 (\%749. ((%247
       $3) (((%280 $2) $1) $0))))))))) ((%85 (%86 (\%697. (%240 (\%747.
       (%243 (\%749. ((%247 $3) (((%281 $2) $1) $0))))))))) ((%85 (%86
       (\%697. (%240 (\%747. (%243 (\%749. ((%247 $3) (((%282 $2) $1)
       $0))))))))) (%86 (\%697. (%240 (\%747. (%243 (\%749. ((%247 $3)
       (((%283 $2) $1) $0)))))))))))))))))))))))`)
  val TOPER_Axiom =
    DT(["DISK_THM"], [],
       `(%284 (\%750. (%286 (\%287. (%288 (\%289. (%290 (\%291. (%290
       (\%292. (%290 (\%293. (%290 (\%294. (%290 (\%295. (%290 (\%296.
       (%290 (\%297. (%298 (\%299. (%298 (\%300. (%298 (\%301. (%298
       (\%302. (%751 (\%752. ((%8 (%49 (\%225. (%14 (\%226. ((%35 ($2
       ((%270 $1) $0))) (($16 $1) $0))))))) ((%8 (%14 (\%238. (%49 (\%239.
       ((%35 ($2 ((%271 $1) $0))) (($15 $1) $0))))))) ((%8 (%49 (\%225.
       (%140 (\%241. ((%35 ($2 ((%272 $1) $0))) (($14 $1) $0))))))) ((%8
       (%49 (\%225. (%140 (\%241. (%140 (\%242. ((%35 ($3 (((%273 $2) $1)
       $0))) ((($14 $2) $1) $0))))))))) ((%8 (%49 (\%225. (%140 (\%241.
       (%140 (\%242. ((%35 ($3 (((%274 $2) $1) $0))) ((($13 $2) $1)
       $0))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242. ((%35 ($3
       (((%275 $2) $1) $0))) ((($12 $2) $1) $0))))))))) ((%8 (%49 (\%225.
       (%140 (\%241. (%140 (\%242. ((%35 ($3 (((%276 $2) $1) $0))) ((($11
       $2) $1) $0))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140 (\%242.
       ((%35 ($3 (((%277 $2) $1) $0))) ((($10 $2) $1) $0))))))))) ((%8 (%49
       (\%225. (%140 (\%241. (%140 (\%242. ((%35 ($3 (((%278 $2) $1) $0)))
       ((($9 $2) $1) $0))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%140
       (\%242. ((%35 ($3 (((%279 $2) $1) $0))) ((($8 $2) $1) $0)))))))))
       ((%8 (%49 (\%225. (%140 (\%241. (%304 (\%244. ((%35 ($3 (((%280 $2)
       $1) $0))) ((($7 $2) $1) $0))))))))) ((%8 (%49 (\%225. (%140 (\%241.
       (%304 (\%244. ((%35 ($3 (((%281 $2) $1) $0))) ((($6 $2) $1)
       $0))))))))) ((%8 (%49 (\%225. (%140 (\%241. (%304 (\%244. ((%35 ($3
       (((%282 $2) $1) $0))) ((($5 $2) $1) $0))))))))) (%49 (\%225. (%140
       (\%241. (%304 (\%244. ((%35 ($3 (((%283 $2) $1) $0))) ((($4 $2) $1)
       $0)))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val TOPER_induction =
    DT(["DISK_THM"], [],
       `(%753 (\%754. ((%83 ((%8 (%49 (\%697. (%14 (\%3. ($2 ((%270 $1)
       $0))))))) ((%8 (%14 (\%3. (%49 (\%697. ($2 ((%271 $1) $0))))))) ((%8
       (%49 (\%697. (%140 (\%747. ($2 ((%272 $1) $0))))))) ((%8 (%49
       (\%697. (%140 (\%747. (%140 (\%748. ($3 (((%273 $2) $1) $0)))))))))
       ((%8 (%49 (\%697. (%140 (\%747. (%140 (\%748. ($3 (((%274 $2) $1)
       $0))))))))) ((%8 (%49 (\%697. (%140 (\%747. (%140 (\%748. ($3
       (((%275 $2) $1) $0))))))))) ((%8 (%49 (\%697. (%140 (\%747. (%140
       (\%748. ($3 (((%276 $2) $1) $0))))))))) ((%8 (%49 (\%697. (%140
       (\%747. (%140 (\%748. ($3 (((%277 $2) $1) $0))))))))) ((%8 (%49
       (\%697. (%140 (\%747. (%140 (\%748. ($3 (((%278 $2) $1) $0)))))))))
       ((%8 (%49 (\%697. (%140 (\%747. (%140 (\%748. ($3 (((%279 $2) $1)
       $0))))))))) ((%8 (%49 (\%697. (%140 (\%747. (%304 (\%749. ($3
       (((%280 $2) $1) $0))))))))) ((%8 (%49 (\%697. (%140 (\%747. (%304
       (\%749. ($3 (((%281 $2) $1) $0))))))))) ((%8 (%49 (\%697. (%140
       (\%747. (%304 (\%749. ($3 (((%282 $2) $1) $0))))))))) (%49 (\%697.
       (%140 (\%747. (%304 (\%749. ($3 (((%283 $2) $1)
       $0)))))))))))))))))))))) (%245 (\%746. ($1 $0))))))`)
  val datatype_HSL_STRUCTURE =
    DT(["DISK_THM"], [], `(%642 (((((%755 %356) %357) %358) %359) %360))`)
  val HSL_STRUCTURE_11 =
    DT(["DISK_THM"], [],
       `((%8 (%371 (\%314. (%371 (\%756. ((%16 ((%339 (%356 $1)) (%356
       $0))) ((%757 $1) $0))))))) ((%8 (%337 (\%347. (%337 (\%348. (%337
       (\%758. (%337 (\%759. ((%16 ((%339 ((%357 $3) $2)) ((%357 $1) $0)))
       ((%8 ((%339 $3) $1)) ((%339 $2) $0)))))))))))) ((%8 (%373 (\%332.
       (%337 (\%348. (%337 (\%351. (%373 (\%760. (%337 (\%759. (%337
       (\%761. ((%16 ((%339 (((%358 $5) $4) $3)) (((%358 $2) $1) $0))) ((%8
       ((%762 $5) $2)) ((%8 ((%339 $4) $1)) ((%339 $3) $0)))))))))))))))))
       ((%8 (%373 (\%332. (%337 (\%348. (%373 (\%760. (%337 (\%759. ((%16
       ((%339 ((%359 $3) $2)) ((%359 $1) $0))) ((%8 ((%762 $3) $1)) ((%339
       $2) $0)))))))))))) (%374 (\%335. (%337 (\%348. (%374 (\%336. (%374
       (\%763. (%337 (\%759. (%374 (\%764. ((%16 ((%339 (((%360 $5) $4)
       $3)) (((%360 $2) $1) $0))) ((%8 ((%765 $5) $2)) ((%8 ((%339 $4) $1))
       ((%765 $3) $0))))))))))))))))))))`)
  val HSL_STRUCTURE_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%337 (\%348. (%337 (\%347. (%371 (\%314. (%418 ((%339 (%356
       $0)) ((%357 $1) $2)))))))))) ((%8 (%337 (\%351. (%337 (\%348. (%373
       (\%332. (%371 (\%314. (%418 ((%339 (%356 $0)) (((%358 $1) $2)
       $3)))))))))))) ((%8 (%337 (\%348. (%373 (\%332. (%371 (\%314. (%418
       ((%339 (%356 $0)) ((%359 $1) $2)))))))))) ((%8 (%374 (\%336. (%337
       (\%348. (%374 (\%335. (%371 (\%314. (%418 ((%339 (%356 $0)) (((%360
       $1) $2) $3)))))))))))) ((%8 (%337 (\%351. (%337 (\%759. (%337
       (\%348. (%373 (\%760. (%337 (\%347. (%418 ((%339 ((%357 $0) $2))
       (((%358 $1) $3) $4)))))))))))))) ((%8 (%337 (\%759. (%337 (\%348.
       (%373 (\%760. (%337 (\%347. (%418 ((%339 ((%357 $0) $2)) ((%359 $1)
       $3)))))))))))) ((%8 (%374 (\%336. (%337 (\%759. (%337 (\%348. (%374
       (\%763. (%337 (\%347. (%418 ((%339 ((%357 $0) $2)) (((%360 $1) $3)
       $4)))))))))))))) ((%8 (%337 (\%351. (%337 (\%759. (%337 (\%348.
       (%373 (\%760. (%373 (\%332. (%418 ((%339 (((%358 $0) $2) $4)) ((%359
       $1) $3)))))))))))))) ((%8 (%374 (\%764. (%337 (\%351. (%337 (\%759.
       (%337 (\%348. (%374 (\%763. (%373 (\%332. (%418 ((%339 (((%358 $0)
       $2) $4)) (((%360 $1) $3) $5)))))))))))))))) (%374 (\%336. (%337
       (\%759. (%337 (\%348. (%374 (\%763. (%373 (\%332. (%418 ((%339
       ((%359 $0) $2)) (((%360 $1) $3) $4))))))))))))))))))))))`)
  val HSL_STRUCTURE_case_cong =
    DT(["DISK_THM"], [],
       `(%337 (\%766. (%337 (\%767. (%361 (\%362. (%363 (\%364. (%365
       (\%366. (%367 (\%368. (%369 (\%370. ((%83 ((%8 ((%339 $6) $5)) ((%8
       (%371 (\%314. ((%83 ((%339 $6) (%356 $0))) ((%35 ($5 $0)) (%768
       $0)))))) ((%8 (%337 (\%347. (%337 (\%348. ((%83 ((%339 $7) ((%357
       $1) $0))) ((%35 (($5 $1) $0)) ((%769 $1) $0)))))))) ((%8 (%373
       (\%332. (%337 (\%348. (%337 (\%351. ((%83 ((%339 $8) (((%358 $2) $1)
       $0))) ((%35 ((($5 $2) $1) $0)) (((%770 $2) $1) $0)))))))))) ((%8
       (%373 (\%332. (%337 (\%348. ((%83 ((%339 $7) ((%359 $1) $0))) ((%35
       (($3 $1) $0)) ((%771 $1) $0)))))))) (%374 (\%335. (%337 (\%348.
       (%374 (\%336. ((%83 ((%339 $8) (((%360 $2) $1) $0))) ((%35 ((($3 $2)
       $1) $0)) (((%772 $2) $1) $0))))))))))))))) ((%35 ((((((%372 $4) $3)
       $2) $1) $0) $6)) ((((((%372 %768) %769) %770) %771) %772)
       $5)))))))))))))))))`)
  val HSL_STRUCTURE_nchotomy =
    DT(["DISK_THM"], [],
       `(%337 (\%773. ((%85 (%313 (\%774. ((%339 $1) (%356 $0))))) ((%85
       (%775 (\%773. (%775 (\%776. ((%339 $2) ((%357 $1) $0))))))) ((%85
       (%331 (\%777. (%775 (\%773. (%775 (\%776. ((%339 $3) (((%358 $2) $1)
       $0))))))))) ((%85 (%331 (\%777. (%775 (\%773. ((%339 $2) ((%359 $1)
       $0))))))) (%334 (\%778. (%775 (\%773. (%334 (\%779. ((%339 $3)
       (((%360 $2) $1) $0))))))))))))))`)
  val HSL_STRUCTURE_Axiom =
    DT(["DISK_THM"], [],
       `(%361 (\%780. (%781 (\%782. (%783 (\%784. (%785 (\%786. (%787
       (\%788. (%789 (\%790. ((%8 (%371 (\%314. ((%35 ($1 (%356 $0))) ($6
       $0))))) ((%8 (%337 (\%347. (%337 (\%348. ((%35 ($2 ((%357 $1) $0)))
       (((($6 $1) $0) ($2 $1)) ($2 $0)))))))) ((%8 (%373 (\%332. (%337
       (\%348. (%337 (\%351. ((%35 ($3 (((%358 $2) $1) $0))) ((((($6 $2)
       $1) $0) ($3 $1)) ($3 $0)))))))))) ((%8 (%373 (\%332. (%337 (\%348.
       ((%35 ($2 ((%359 $1) $0))) ((($4 $1) $0) ($2 $0)))))))) (%374
       (\%335. (%337 (\%348. (%374 (\%336. ((%35 ($3 (((%360 $2) $1) $0)))
       (((($4 $2) $0) $1) ($3 $1)))))))))))))))))))))))))`)
  val HSL_STRUCTURE_induction =
    DT(["DISK_THM"], [],
       `(%791 (\%792. ((%83 ((%8 (%371 (\%774. ($1 (%356 $0))))) ((%8 (%337
       (\%773. (%337 (\%776. ((%83 ((%8 ($2 $1)) ($2 $0))) ($2 ((%357 $1)
       $0)))))))) ((%8 (%337 (\%773. (%337 (\%776. ((%83 ((%8 ($2 $1)) ($2
       $0))) (%373 (\%777. ($3 (((%358 $0) $2) $1)))))))))) ((%8 (%337
       (\%773. ((%83 ($1 $0)) (%373 (\%777. ($2 ((%359 $0) $1)))))))) (%337
       (\%773. ((%83 ($1 $0)) (%374 (\%779. (%374 (\%778. ($3 (((%360 $0)
       $2) $1)))))))))))))) (%337 (\%773. ($1 $0))))))`)
  val eval_TCND_ind =
    DT(["DISK_THM"], [],
       `(%793 (\%794. ((%83 ((%8 (%49 (\%398. (%140 (\%402. (%174 (\%396.
       (($3 ((%795 $2) ((%796 %797) $1))) $0)))))))) ((%8 (%49 (\%398.
       (%140 (\%402. (%174 (\%396. (($3 ((%795 $2) ((%796 %798) $1)))
       $0)))))))) ((%8 (%49 (\%398. (%140 (\%402. (%174 (\%396. (($3 ((%795
       $2) ((%796 %799) $1))) $0)))))))) ((%8 (%49 (\%398. (%140 (\%402.
       (%174 (\%396. (($3 ((%795 $2) ((%796 %800) $1))) $0)))))))) ((%8
       (%49 (\%398. (%140 (\%402. (%174 (\%396. (($3 ((%795 $2) ((%796
       %801) $1))) $0)))))))) ((%8 (%49 (\%398. (%140 (\%402. (%174 (\%396.
       (($3 ((%795 $2) ((%796 %802) $1))) $0)))))))) ((%8 (%49 (\%398.
       (%140 (\%402. (%174 (\%396. (($3 ((%795 $2) ((%796 %803) $1)))
       $0)))))))) ((%8 (%49 (\%398. (%140 (\%402. (%174 (\%396. (($3 ((%795
       $2) ((%796 %804) $1))) $0)))))))) ((%8 (%49 (\%398. (%140 (\%402.
       (%174 (\%396. (($3 ((%795 $2) ((%796 %805) $1))) $0)))))))) ((%8
       (%49 (\%398. (%140 (\%402. (%174 (\%396. (($3 ((%795 $2) ((%796
       %806) $1))) $0)))))))) ((%8 (%49 (\%398. (%140 (\%402. (%174 (\%396.
       (($3 ((%795 $2) ((%796 %807) $1))) $0)))))))) ((%8 (%49 (\%398.
       (%140 (\%402. (%174 (\%396. (($3 ((%795 $2) ((%796 %808) $1)))
       $0)))))))) ((%8 (%49 (\%398. (%140 (\%402. (%174 (\%396. (($3 ((%795
       $2) ((%796 %809) $1))) $0)))))))) ((%8 (%49 (\%398. (%140 (\%402.
       (%174 (\%396. (($3 ((%795 $2) ((%796 %810) $1))) $0)))))))) ((%8
       (%49 (\%398. (%140 (\%402. (%174 (\%396. (($3 ((%795 $2) ((%796
       %811) $1))) $0)))))))) (%49 (\%398. (%140 (\%402. (%174 (\%396. (($3
       ((%795 $2) ((%796 %812) $1))) $0))))))))))))))))))))))) (%49 (\%101.
       (%813 (\%814. (%140 (\%402. (%174 (\%815. (($4 ((%795 $3) ((%796 $2)
       $1))) $0))))))))))))`)
  val eval_TCND_def =
    DT(["DISK_THM"], [],
       `((%8 ((%16 ((%426 ((%795 %398) ((%796 %797) %402))) %396)) ((%177
       ((%178 %396) (%116 %398))) ((%178 %396) (%155 %402))))) ((%8 ((%16
       ((%426 ((%795 %398) ((%796 %798) %402))) %396)) ((%405 ((%178 %396)
       (%116 %398))) ((%178 %396) (%155 %402))))) ((%8 ((%16 ((%426 ((%795
       %398) ((%796 %799) %402))) %396)) ((%406 (%407 (\%408. (%409 (\%410.
       (%411 (\%412. (\%413. $3)))))))) ((%414 ((%178 %396) (%116 %398)))
       ((%178 %396) (%155 %402)))))) ((%8 ((%16 ((%426 ((%795 %398) ((%796
       %800) %402))) %396)) ((%406 (%407 (\%408. (%409 (\%410. (%411
       (\%412. (\%413. $0)))))))) ((%414 ((%178 %396) (%116 %398))) ((%178
       %396) (%155 %402)))))) ((%8 ((%16 ((%426 ((%795 %398) ((%796 %801)
       %402))) %396)) ((%415 ((%178 %396) (%116 %398))) ((%178 %396) (%155
       %402))))) ((%8 ((%16 ((%426 ((%795 %398) ((%796 %802) %402))) %396))
       ((%416 ((%178 %396) (%116 %398))) ((%178 %396) (%155 %402))))) ((%8
       ((%16 ((%426 ((%795 %398) ((%796 %803) %402))) %396)) ((%417 ((%178
       %396) (%116 %398))) ((%178 %396) (%155 %402))))) ((%8 ((%16 ((%426
       ((%795 %398) ((%796 %804) %402))) %396)) %93)) ((%8 ((%16 ((%426
       ((%795 %398) ((%796 %805) %402))) %396)) (%418 ((%177 ((%178 %396)
       (%116 %398))) ((%178 %396) (%155 %402)))))) ((%8 ((%16 ((%426 ((%795
       %398) ((%796 %806) %402))) %396)) ((%419 ((%178 %396) (%116 %398)))
       ((%178 %396) (%155 %402))))) ((%8 ((%16 ((%426 ((%795 %398) ((%796
       %807) %402))) %396)) ((%406 (%407 (\%408. (%409 (\%410. (%411
       (\%412. (\%413. (%418 $3))))))))) ((%414 ((%178 %396) (%116 %398)))
       ((%178 %396) (%155 %402)))))) ((%8 ((%16 ((%426 ((%795 %398) ((%796
       %808) %402))) %396)) ((%406 (%407 (\%408. (%409 (\%410. (%411
       (\%412. (\%413. (%418 $0))))))))) ((%414 ((%178 %396) (%116 %398)))
       ((%178 %396) (%155 %402)))))) ((%8 ((%16 ((%426 ((%795 %398) ((%796
       %809) %402))) %396)) ((%420 ((%178 %396) (%116 %398))) ((%178 %396)
       (%155 %402))))) ((%8 ((%16 ((%426 ((%795 %398) ((%796 %810) %402)))
       %396)) ((%421 ((%178 %396) (%116 %398))) ((%178 %396) (%155
       %402))))) ((%8 ((%16 ((%426 ((%795 %398) ((%796 %811) %402))) %396))
       ((%422 ((%178 %396) (%116 %398))) ((%178 %396) (%155 %402))))) ((%16
       ((%426 ((%795 %398) ((%796 %812) %402))) %396))
       %423))))))))))))))))`)
  val transfer_ind =
    DT(["DISK_THM"], [],
       `(%816 (\%817. ((%83 ((%8 (%174 (\%440. (%174 (\%438. (%104 (\%439.
       (%434 (\%436. (($4 ((%442 $3) $2)) ((%444 ((%445 $1) $0))
       %818))))))))))) ((%8 (%174 (\%440. (%174 (\%438. (%104 (\%819. (%434
       (\%820. (($4 ((%442 $3) $2)) ((%444 %818) ((%445 $1) $0))))))))))))
       ((%8 (%174 (\%440. (%174 (\%438. (($2 ((%442 $1) $0)) ((%444 %818)
       %818))))))) (%174 (\%440. (%174 (\%438. (%104 (\%439. (%434 (\%436.
       (%104 (\%437. (%434 (\%435. ((%83 (($6 ((%442 (((%443 $5) $3) ((%178
       $4) $1))) $4)) ((%444 $2) $0))) (($6 ((%442 $5) $4)) ((%444 ((%445
       $3) $2)) ((%445 $1) $0)))))))))))))))))))) (%174 (\%821. (%174
       (\%165. (%434 (\%822. (%434 (\%823. (($4 ((%442 $3) $2)) ((%444 $1)
       $0)))))))))))))`)
  val transfer_def =
    DT(["DISK_THM"], [],
       `((%8 ((%463 ((%464 ((%442 %440) %438)) ((%444 %818) %818))) %440))
       ((%463 ((%464 ((%442 %440) %438)) ((%444 ((%445 %439) %436)) ((%445
       %437) %435)))) ((%464 ((%442 (((%443 %440) %439) ((%178 %438)
       %437))) %438)) ((%444 %436) %435))))`)
  val run_hsl_ind =
    DT(["DISK_THM"], [],
       `(%824 (\%825. ((%83 ((%8 (%245 (\%503. (%371 (\%504. (%174 (\%396.
       ((%83 (($3 (%356 $1)) ((%468 $0) $2))) (($3 (%356 ((%529 $2) $1)))
       $0))))))))) ((%8 (%174 (\%396. (($1 (%356 %826)) $0)))) ((%8 (%337
       (\%506. (%337 (\%507. (%174 (\%396. ((%83 ((%8 (($3 $2) $0)) (($3
       $1) ((%531 $2) $0)))) (($3 ((%357 $2) $1)) $0))))))))) ((%8 (%373
       (\%508. (%337 (\%506. (%337 (\%507. (%174 (\%396. ((%83 ((%8 ((%83
       (%418 ((%426 $3) $0))) (($4 $1) $0))) ((%83 ((%426 $3) $0)) (($4 $2)
       $0)))) (($4 (((%358 $3) $2) $1)) $0))))))))))) ((%8 (%373 (\%508.
       (%337 (\%506. (%174 (\%396. ((%83 (%174 (\%516. (($4 $2) $0)))) (($3
       ((%359 $2) $1)) $0))))))))) (%434 (\%520. (%434 (\%521. (%337
       (\%518. (%434 (\%522. (%434 (\%523. (%174 (\%396. ((%83 (%174
       (\%440. ((%83 ((%463 $0) ((%464 ((%442 %487) $1)) ((%444 $5) $6))))
       (($7 $4) $0))))) (($6 (((%360 ((%444 $5) $4)) $3) ((%444 $2) $1)))
       $0)))))))))))))))))))) (%337 (\%499. (%174 (\%165. (($2 $1)
       $0))))))))`)
  val run_hsl_def =
    DT(["DISK_THM"], [],
       `((%8 ((%463 ((%531 (%356 ((%529 %503) %504))) %396)) ((%531 (%356
       %504)) ((%468 %396) %503)))) ((%8 ((%463 ((%531 (%356 %826)) %396))
       %396)) ((%8 ((%463 ((%531 ((%357 %506) %507)) %396)) ((%531 %507)
       ((%531 %506) %396)))) ((%8 ((%463 ((%531 (((%358 %508) %506) %507))
       %396)) (((%511 ((%426 %508) %396)) ((%531 %506) %396)) ((%531 %507)
       %396)))) ((%8 ((%463 ((%531 ((%359 %508) %506)) %396)) (((%514
       (\%515. (%418 ((%426 %508) $0)))) (\%516. ((%531 %506) $0))) %396)))
       ((%463 ((%531 (((%360 ((%444 %520) %521)) %518) ((%444 %522) %523)))
       %396)) ((%524 (\%440. ((%524 (\%525. ((%464 ((%442 %396) $0)) ((%444
       %522) %523)))) ((%531 %518) $0)))) ((%464 ((%442 %487) %396)) ((%444
       %521) %520)))))))))`)
  val valid_assgn_ind =
    DT(["DISK_THM"], [],
       `(%827 (\%828. ((%83 ((%8 (%49 (\%154. (%14 (\%37. (%14 (\%532. (($3
       ((%270 $2) $1)) $0)))))))) ((%8 (%14 (\%37. (%49 (\%154. (%14
       (\%532. (($3 ((%271 $2) $1)) $0)))))))) ((%8 (%49 (\%829. (%140
       (\%830. (%304 (\%831. (%14 (\%532. (($4 (((%283 $3) $2) $1))
       $0)))))))))) ((%8 (%49 (\%832. (%140 (\%833. (%304 (\%834. (%14
       (\%532. (($4 (((%282 $3) $2) $1)) $0)))))))))) ((%8 (%49 (\%835.
       (%140 (\%836. (%304 (\%837. (%14 (\%532. (($4 (((%281 $3) $2) $1))
       $0)))))))))) ((%8 (%49 (\%838. (%140 (\%839. (%304 (\%840. (%14
       (\%532. (($4 (((%280 $3) $2) $1)) $0)))))))))) ((%8 (%49 (\%841.
       (%140 (\%842. (%140 (\%843. (%14 (\%532. (($4 (((%279 $3) $2) $1))
       $0)))))))))) ((%8 (%49 (\%844. (%140 (\%845. (%140 (\%846. (%14
       (\%532. (($4 (((%278 $3) $2) $1)) $0)))))))))) ((%8 (%49 (\%847.
       (%140 (\%848. (%140 (\%849. (%14 (\%532. (($4 (((%277 $3) $2) $1))
       $0)))))))))) ((%8 (%49 (\%850. (%140 (\%851. (%140 (\%852. (%14
       (\%532. (($4 (((%276 $3) $2) $1)) $0)))))))))) ((%8 (%49 (\%853.
       (%140 (\%854. (%140 (\%855. (%14 (\%532. (($4 (((%275 $3) $2) $1))
       $0)))))))))) ((%8 (%49 (\%856. (%140 (\%857. (%140 (\%858. (%14
       (\%532. (($4 (((%274 $3) $2) $1)) $0)))))))))) ((%8 (%49 (\%859.
       (%140 (\%860. (%140 (\%861. (%14 (\%532. (($4 (((%273 $3) $2) $1))
       $0)))))))))) (%49 (\%862. (%140 (\%863. (%14 (\%532. (($3 ((%272 $2)
       $1)) $0))))))))))))))))))))) (%245 (\%544. (%14 (\%864. (($2 $1)
       $0))))))))`)
  val valid_assgn_def =
    DT(["DISK_THM"], [],
       `((%8 ((%16 ((%585 ((%270 %154) %37)) %532)) ((%533 %37) %532)))
       ((%8 ((%16 ((%585 ((%271 %37) %154)) %532)) ((%533 %37) %532))) ((%8
       ((%16 ((%585 (((%283 %829) %830) %831)) %532)) %93)) ((%8 ((%16
       ((%585 (((%282 %832) %833) %834)) %532)) %93)) ((%8 ((%16 ((%585
       (((%281 %835) %836) %837)) %532)) %93)) ((%8 ((%16 ((%585 (((%280
       %838) %839) %840)) %532)) %93)) ((%8 ((%16 ((%585 (((%279 %841)
       %842) %843)) %532)) %93)) ((%8 ((%16 ((%585 (((%278 %844) %845)
       %846)) %532)) %93)) ((%8 ((%16 ((%585 (((%277 %847) %848) %849))
       %532)) %93)) ((%8 ((%16 ((%585 (((%276 %850) %851) %852)) %532))
       %93)) ((%8 ((%16 ((%585 (((%275 %853) %854) %855)) %532)) %93)) ((%8
       ((%16 ((%585 (((%274 %856) %857) %858)) %532)) %93)) ((%8 ((%16
       ((%585 (((%273 %859) %860) %861)) %532)) %93)) ((%16 ((%585 ((%272
       %862) %863)) %532)) %93))))))))))))))`)
  val Sc_RULE =
    DT(["DISK_THM"], [],
       `(%337 (\%506. (%337 (\%507. (%592 (\%865. (%594 (\%866. (%867
       (\%868. (%596 (\%869. (%870 (\%871. ((%83 ((%8 ((%598 $6) ((%599 $4)
       ((%600 $3) $1)))) ((%872 $5) ((%873 $1) ((%874 $2) $0))))) ((%875
       ((%357 $6) $5)) ((%876 $4) ((%877 ((%878 $3) $2))
       $0))))))))))))))))))`)
  val Cj_RULE =
    DT(["DISK_THM"], [],
       `(%373 (\%508. (%337 (\%879. (%337 (\%880. (%881 (\%882. (%592
       (\%593. (%594 (\%866. (%594 (\%883. (%596 (\%597. ((%83 ((%8 ((%598
       $6) ((%599 $3) ((%600 $2) $0)))) ((%8 ((%598 $5) ((%599 $3) ((%600
       $1) $0)))) (%174 (\%396. ((%16 ($5 ($4 $0))) ((%426 $8) $0)))))))
       ((%598 (((%358 $7) $6) $5)) ((%599 $3) ((%600 (((%884 $4) $2) $1))
       $0))))))))))))))))))))`)
  val WF_DEF_2 =
    DT(["DISK_THM"], [],
       `((%16 (%885 %886)) (%881 (\%887. ((%83 (%888 (\%889. ($1 $0))))
       (%888 (\%890. ((%8 ($1 $0)) (%28 (\%891. ((%83 ((%886 $0) $1)) (%418
       ($2 $0))))))))))))`)
  val WF_HSL_TR_LEM_2 =
    DT(["DISK_THM"], [],
       `(%373 (\%508. (%337 (\%518. (%592 (\%892. (%893 (\%894. (%881
       (\%882. ((%83 ((%8 (%174 (\%396. ((%16 ($1 ($3 $0))) ((%426 $5)
       $0))))) ((%8 (%174 (\%396. ((%35 ($3 ((%531 $4) $0))) ($2 ($3
       $0)))))) (%885 (\%895. (\%896. ((%8 (%418 ($2 $0))) ((%35 $1) ($3
       $0))))))))) (%897 (\%440. (\%438. ((%8 (%418 ((%426 $6) $0))) ((%463
       $1) ((%531 $5) $0)))))))))))))))))`)
  val WF_HSL_TR_LEM_3 =
    DT(["DISK_THM"], [],
       `(%881 (\%882. (%893 (\%894. ((%83 (%898 (\%886. ((%8 (%885 $0))
       (%28 (\%896. ((%83 (%418 ($3 $0))) (($1 ($2 $0)) $0)))))))) (%885
       (\%895. (\%896. ((%8 (%418 ($3 $0))) ((%35 $1) ($2 $0)))))))))))`)
  val WF_HSL_TR_THM =
    DT(["DISK_THM"], [],
       `(%373 (\%508. (%337 (\%518. (%592 (\%892. (%893 (\%894. (%881
       (\%882. ((%83 ((%8 (%174 (\%396. ((%16 ($1 ($3 $0))) ((%426 $5)
       $0))))) ((%8 (%174 (\%396. ((%35 ($3 ((%531 $4) $0))) ($2 ($3
       $0)))))) (%898 (\%886. ((%8 (%885 $0)) (%28 (\%896. ((%83 (%418 ($2
       $0))) (($1 ($3 $0)) $0)))))))))) (%897 (\%440. (\%438. ((%8 (%418
       ((%426 $6) $0))) ((%463 $1) ((%531 $5) $0)))))))))))))))))`)
  val Tr_RULE =
    DT(["DISK_THM"], [],
       `(%373 (\%508. (%337 (\%518. (%881 (\%882. (%592 (\%892. (%893
       (\%894. ((%83 ((%8 (%898 (\%886. ((%8 (%885 $0)) (%28 (\%608. ((%83
       (%418 ($4 $0))) (($1 ($2 $0)) $0)))))))) ((%8 (%174 (\%396. ((%16
       ($3 ($2 $0))) ((%426 $5) $0))))) ((%899 $3) ((%900 $1) ((%901 $0)
       $1)))))) ((%899 ((%359 $4) $3)) ((%900 $1) ((%901 ((%902 $2) $0))
       $1))))))))))))))`)
  val notC_ind =
    DT(["DISK_THM"], [],
       `(%701 (\%702. ((%83 ((%8 (%126 (\%619. ($1 (%117 $0))))) ((%8 (%14
       (\%903. ($1 (%118 $0))))) (%49 (\%101. ($1 (%116 $0))))))) (%104
       (\%904. ($1 $0))))))`)
  val notC_def =
    DT(["DISK_THM"], [],
       `((%8 ((%16 (%611 (%117 %619))) %423)) ((%8 ((%16 (%611 (%118
       %903))) %93)) ((%16 (%611 (%116 %101))) %93)))`)
  val TRANSFER_LEM_1 =
    DT(["DISK_THM"], [],
       `(%104 (\%905. (%434 (\%436. (%434 (\%435. (%174 (\%440. (%174
       (\%438. ((%83 ((%8 (%634 ((%445 $4) $3))) ((%17 (%636 $3)) (%636
       $2)))) ((%177 ((%178 ((%464 ((%442 $1) $0)) ((%444 $3) $2))) $4))
       ((%178 $1) $4)))))))))))))`)
  val TRANSFER_THM =
    DT(["DISK_THM"], [],
       `(%434 (\%436. (%434 (\%435. (%174 (\%440. (%174 (\%438. ((%83 ((%8
       (%634 $3)) ((%8 ((%17 (%636 $3)) (%636 $2))) ((%638 %611) $3))))
       ((%906 ((%626 (%178 ((%464 ((%442 $1) $0)) ((%444 $3) $2)))) $3))
       ((%626 (%178 $0)) $2)))))))))))`)
  val TRANSFER_INTACT =
    DT(["DISK_THM"], [],
       `(%434 (\%436. (%434 (\%435. (%174 (\%440. (%174 (\%438. (%104
       (\%907. ((%83 ((%8 ((%17 (%636 $4)) (%636 $3))) (%418 ((%908 $0)
       $4)))) ((%177 ((%178 ((%464 ((%442 $2) $1)) ((%444 $4) $3))) $0))
       ((%178 $2) $0)))))))))))))`)
  val Fc_RULE =
    DT(["DISK_THM"], [],
       `(%337 (\%518. (%594 (\%909. (%434 (\%520. (%434 (\%522. (%434
       (\%521. (%434 (\%523. (%592 (\%910. (%596 (\%911. (%592 (\%912.
       (%596 (\%913. (%623 (\%914. (%915 (\%916. ((%83 ((%8 (%917 ((%918
       $9) ((%919 $8) ((%444 $7) $6))))) ((%8 ((%8 (((%625 $5) $9) $1))
       (((%625 $3) $7) $1))) ((%8 (((%920 $4) $8) $0)) (((%920 $2) $6)
       $0))))) ((%83 ((%598 $11) ((%599 $3) ((%600 $10) $2)))) ((%598
       (((%360 ((%444 $9) $7)) $11) ((%444 $8) $6))) ((%599 $5) ((%600 $10)
       $4)))))))))))))))))))))))))))))`)
  end
  val _ = DB.bindl "HSL"
  [("PTR_TY_DEF",PTR_TY_DEF,DB.Def), ("PTR_BIJ",PTR_BIJ,DB.Def),
   ("TTP",TTP,DB.Def), ("THP",THP,DB.Def), ("TFP",TFP,DB.Def),
   ("TIP",TIP,DB.Def), ("TSP",TSP,DB.Def), ("TLR",TLR,DB.Def),
   ("PTR_size_def",PTR_size_def,DB.Def), ("PTR_case",PTR_case,DB.Def),
   ("toPTR_def",toPTR_def,DB.Def), ("TREG_TY_DEF",TREG_TY_DEF,DB.Def),
   ("TREG_BIJ",TREG_BIJ,DB.Def), ("r0",r0,DB.Def), ("r1",r1,DB.Def),
   ("r2",r2,DB.Def), ("r3",r3,DB.Def), ("r4",r4,DB.Def), ("r5",r5,DB.Def),
   ("r6",r6,DB.Def), ("r7",r7,DB.Def), ("r8",r8,DB.Def),
   ("TREG_size_def",TREG_size_def,DB.Def), ("TREG_case",TREG_case,DB.Def),
   ("data_reg_index_def",data_reg_index_def,DB.Def),
   ("data_reg_name_def",data_reg_name_def,DB.Def),
   ("conv_reg_def",conv_reg_def,DB.Def),
   ("TEXP_TY_DEF",TEXP_TY_DEF,DB.Def), ("TEXP_repfns",TEXP_repfns,DB.Def),
   ("HSL0_def",HSL0_def,DB.Def), ("HSL1_def",HSL1_def,DB.Def),
   ("HSL2_def",HSL2_def,DB.Def), ("inR",inR,DB.Def), ("inC",inC,DB.Def),
   ("inE",inE,DB.Def), ("TEXP_case_def",TEXP_case_def,DB.Def),
   ("TEXP_size_def",TEXP_size_def,DB.Def),
   ("TROC_TY_DEF",TROC_TY_DEF,DB.Def), ("TROC_repfns",TROC_repfns,DB.Def),
   ("HSL3_def",HSL3_def,DB.Def), ("HSL4_def",HSL4_def,DB.Def),
   ("Rg",Rg,DB.Def), ("Cn",Cn,DB.Def),
   ("TROC_case_def",TROC_case_def,DB.Def),
   ("TROC_size_def",TROC_size_def,DB.Def),
   ("roc_2_exp_def",roc_2_exp_def,DB.Def),
   ("tread_tupled_primitive_def",tread_tupled_primitive_def,DB.Def),
   ("tread_curried_def",tread_curried_def,DB.Def),
   ("twrite_tupled_primitive_def",twrite_tupled_primitive_def,DB.Def),
   ("twrite_curried_def",twrite_curried_def,DB.Def),
   ("from_MEXP_def",from_MEXP_def,DB.Def),
   ("TOPER_TY_DEF",TOPER_TY_DEF,DB.Def),
   ("TOPER_repfns",TOPER_repfns,DB.Def), ("HSL5_def",HSL5_def,DB.Def),
   ("HSL6_def",HSL6_def,DB.Def), ("HSL7_def",HSL7_def,DB.Def),
   ("HSL8_def",HSL8_def,DB.Def), ("HSL9_def",HSL9_def,DB.Def),
   ("HSL10_def",HSL10_def,DB.Def), ("HSL11_def",HSL11_def,DB.Def),
   ("HSL12_def",HSL12_def,DB.Def), ("HSL13_def",HSL13_def,DB.Def),
   ("HSL14_def",HSL14_def,DB.Def), ("HSL15_def",HSL15_def,DB.Def),
   ("HSL16_def",HSL16_def,DB.Def), ("HSL17_def",HSL17_def,DB.Def),
   ("HSL18_def",HSL18_def,DB.Def), ("TLDR",TLDR,DB.Def),
   ("TSTR",TSTR,DB.Def), ("TMOV",TMOV,DB.Def), ("TADD",TADD,DB.Def),
   ("TSUB",TSUB,DB.Def), ("TRSB",TRSB,DB.Def), ("TMUL",TMUL,DB.Def),
   ("TAND",TAND,DB.Def), ("TORR",TORR,DB.Def), ("TEOR",TEOR,DB.Def),
   ("TLSL",TLSL,DB.Def), ("TLSR",TLSR,DB.Def), ("TASR",TASR,DB.Def),
   ("TROR",TROR,DB.Def), ("TOPER_case_def",TOPER_case_def,DB.Def),
   ("TOPER_size_def",TOPER_size_def,DB.Def),
   ("HSL_STRUCTURE_TY_DEF",HSL_STRUCTURE_TY_DEF,DB.Def),
   ("HSL_STRUCTURE_repfns",HSL_STRUCTURE_repfns,DB.Def),
   ("HSL19_def",HSL19_def,DB.Def), ("HSL20_def",HSL20_def,DB.Def),
   ("HSL21_def",HSL21_def,DB.Def), ("HSL22_def",HSL22_def,DB.Def),
   ("HSL23_def",HSL23_def,DB.Def), ("Blk",Blk,DB.Def), ("Sc",Sc,DB.Def),
   ("Cj",Cj,DB.Def), ("Tr",Tr,DB.Def), ("Fc",Fc,DB.Def),
   ("HSL_STRUCTURE_case_def",HSL_STRUCTURE_case_def,DB.Def),
   ("HSL_STRUCTURE_size_def",HSL_STRUCTURE_size_def,DB.Def),
   ("eval_TCND_tupled_primitive_def",
    eval_TCND_tupled_primitive_def,
    DB.Def), ("eval_TCND_curried_def",eval_TCND_curried_def,DB.Def),
   ("transfer_tupled_primitive_def",transfer_tupled_primitive_def,DB.Def),
   ("transfer_curried_def",transfer_curried_def,DB.Def),
   ("tdecode_def",tdecode_def,DB.Def), ("empty_s_def",empty_s_def,DB.Def),
   ("run_hsl_tupled_AUX_def",run_hsl_tupled_AUX_def,DB.Def),
   ("run_hsl_tupled_primitive_def",run_hsl_tupled_primitive_def,DB.Def),
   ("run_hsl_curried_def",run_hsl_curried_def,DB.Def),
   ("within_bound_def",within_bound_def,DB.Def),
   ("valid_TEXP_def",valid_TEXP_def,DB.Def),
   ("valid_assgn_tupled_primitive_def",
    valid_assgn_tupled_primitive_def,
    DB.Def), ("valid_assgn_curried_def",valid_assgn_curried_def,DB.Def),
   ("valid_struct_def",valid_struct_def,DB.Def),
   ("CSPEC_def",CSPEC_def,DB.Def),
   ("unique_list_def",unique_list_def,DB.Def),
   ("notC_primitive_def",notC_primitive_def,DB.Def),
   ("match_def",match_def,DB.Def),
   ("valid_arg_list_def",valid_arg_list_def,DB.Def),
   ("num2PTR_PTR2num",num2PTR_PTR2num,DB.Thm),
   ("PTR2num_num2PTR",PTR2num_num2PTR,DB.Thm),
   ("num2PTR_11",num2PTR_11,DB.Thm), ("PTR2num_11",PTR2num_11,DB.Thm),
   ("num2PTR_ONTO",num2PTR_ONTO,DB.Thm),
   ("PTR2num_ONTO",PTR2num_ONTO,DB.Thm),
   ("num2PTR_thm",num2PTR_thm,DB.Thm), ("PTR2num_thm",PTR2num_thm,DB.Thm),
   ("PTR_EQ_PTR",PTR_EQ_PTR,DB.Thm), ("PTR_case_def",PTR_case_def,DB.Thm),
   ("datatype_PTR",datatype_PTR,DB.Thm),
   ("PTR_distinct",PTR_distinct,DB.Thm),
   ("PTR_case_cong",PTR_case_cong,DB.Thm),
   ("PTR_nchotomy",PTR_nchotomy,DB.Thm), ("PTR_Axiom",PTR_Axiom,DB.Thm),
   ("PTR_induction",PTR_induction,DB.Thm), ("toPTR_lem",toPTR_lem,DB.Thm),
   ("num2TREG_TREG2num",num2TREG_TREG2num,DB.Thm),
   ("TREG2num_num2TREG",TREG2num_num2TREG,DB.Thm),
   ("num2TREG_11",num2TREG_11,DB.Thm), ("TREG2num_11",TREG2num_11,DB.Thm),
   ("num2TREG_ONTO",num2TREG_ONTO,DB.Thm),
   ("TREG2num_ONTO",TREG2num_ONTO,DB.Thm),
   ("num2TREG_thm",num2TREG_thm,DB.Thm),
   ("TREG2num_thm",TREG2num_thm,DB.Thm),
   ("TREG_EQ_TREG",TREG_EQ_TREG,DB.Thm),
   ("TREG_case_def",TREG_case_def,DB.Thm),
   ("datatype_TREG",datatype_TREG,DB.Thm),
   ("TREG_distinct",TREG_distinct,DB.Thm),
   ("TREG_case_cong",TREG_case_cong,DB.Thm),
   ("TREG_nchotomy",TREG_nchotomy,DB.Thm),
   ("TREG_Axiom",TREG_Axiom,DB.Thm),
   ("TREG_induction",TREG_induction,DB.Thm),
   ("data_reg_name_lem",data_reg_name_lem,DB.Thm),
   ("data_reg_name_thm",data_reg_name_thm,DB.Thm),
   ("toPTR_lem_2",toPTR_lem_2,DB.Thm),
   ("conv_reg_thm",conv_reg_thm,DB.Thm),
   ("CONV_REG_LEM",CONV_REG_LEM,DB.Thm),
   ("FORALL_TSTATE",FORALL_TSTATE,DB.Thm),
   ("datatype_TEXP",datatype_TEXP,DB.Thm), ("TEXP_11",TEXP_11,DB.Thm),
   ("TEXP_distinct",TEXP_distinct,DB.Thm),
   ("TEXP_case_cong",TEXP_case_cong,DB.Thm),
   ("TEXP_nchotomy",TEXP_nchotomy,DB.Thm),
   ("TEXP_Axiom",TEXP_Axiom,DB.Thm),
   ("TEXP_induction",TEXP_induction,DB.Thm),
   ("datatype_TROC",datatype_TROC,DB.Thm), ("TROC_11",TROC_11,DB.Thm),
   ("TROC_distinct",TROC_distinct,DB.Thm),
   ("TROC_case_cong",TROC_case_cong,DB.Thm),
   ("TROC_nchotomy",TROC_nchotomy,DB.Thm),
   ("TROC_Axiom",TROC_Axiom,DB.Thm),
   ("TROC_induction",TROC_induction,DB.Thm),
   ("tread_ind",tread_ind,DB.Thm), ("tread_def",tread_def,DB.Thm),
   ("twrite_ind",twrite_ind,DB.Thm), ("twrite_def",twrite_def,DB.Thm),
   ("datatype_TOPER",datatype_TOPER,DB.Thm), ("TOPER_11",TOPER_11,DB.Thm),
   ("TOPER_distinct",TOPER_distinct,DB.Thm),
   ("TOPER_case_cong",TOPER_case_cong,DB.Thm),
   ("TOPER_nchotomy",TOPER_nchotomy,DB.Thm),
   ("TOPER_Axiom",TOPER_Axiom,DB.Thm),
   ("TOPER_induction",TOPER_induction,DB.Thm),
   ("datatype_HSL_STRUCTURE",datatype_HSL_STRUCTURE,DB.Thm),
   ("HSL_STRUCTURE_11",HSL_STRUCTURE_11,DB.Thm),
   ("HSL_STRUCTURE_distinct",HSL_STRUCTURE_distinct,DB.Thm),
   ("HSL_STRUCTURE_case_cong",HSL_STRUCTURE_case_cong,DB.Thm),
   ("HSL_STRUCTURE_nchotomy",HSL_STRUCTURE_nchotomy,DB.Thm),
   ("HSL_STRUCTURE_Axiom",HSL_STRUCTURE_Axiom,DB.Thm),
   ("HSL_STRUCTURE_induction",HSL_STRUCTURE_induction,DB.Thm),
   ("eval_TCND_ind",eval_TCND_ind,DB.Thm),
   ("eval_TCND_def",eval_TCND_def,DB.Thm),
   ("transfer_ind",transfer_ind,DB.Thm),
   ("transfer_def",transfer_def,DB.Thm),
   ("run_hsl_ind",run_hsl_ind,DB.Thm), ("run_hsl_def",run_hsl_def,DB.Thm),
   ("valid_assgn_ind",valid_assgn_ind,DB.Thm),
   ("valid_assgn_def",valid_assgn_def,DB.Thm), ("Sc_RULE",Sc_RULE,DB.Thm),
   ("Cj_RULE",Cj_RULE,DB.Thm), ("WF_DEF_2",WF_DEF_2,DB.Thm),
   ("WF_HSL_TR_LEM_2",WF_HSL_TR_LEM_2,DB.Thm),
   ("WF_HSL_TR_LEM_3",WF_HSL_TR_LEM_3,DB.Thm),
   ("WF_HSL_TR_THM",WF_HSL_TR_THM,DB.Thm), ("Tr_RULE",Tr_RULE,DB.Thm),
   ("notC_ind",notC_ind,DB.Thm), ("notC_def",notC_def,DB.Thm),
   ("TRANSFER_LEM_1",TRANSFER_LEM_1,DB.Thm),
   ("TRANSFER_THM",TRANSFER_THM,DB.Thm),
   ("TRANSFER_INTACT",TRANSFER_INTACT,DB.Thm), ("Fc_RULE",Fc_RULE,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("CFLTheory.CFL_grammars",CFLTheory.CFL_grammars),
                         ("ACFTheory.ACF_grammars",ACFTheory.ACF_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms temp_add_type "PTR"
  val _ = update_grms
       (temp_overload_on_by_nametype "PTR2num")
        {Name = "PTR2num", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "num2PTR")
        {Name = "num2PTR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TTP")
        {Name = "TTP", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "THP")
        {Name = "THP", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TFP")
        {Name = "TFP", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TIP")
        {Name = "TIP", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TSP")
        {Name = "TSP", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TLR")
        {Name = "TLR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "PTR_size")
        {Name = "PTR_size", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "PTR_case")
        {Name = "PTR_case", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "toPTR")
        {Name = "toPTR", Thy = "HSL"}
  val _ = update_grms temp_add_type "TREG"
  val _ = update_grms
       (temp_overload_on_by_nametype "TREG2num")
        {Name = "TREG2num", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "num2TREG")
        {Name = "num2TREG", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "r0")
        {Name = "r0", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "r1")
        {Name = "r1", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "r2")
        {Name = "r2", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "r3")
        {Name = "r3", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "r4")
        {Name = "r4", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "r5")
        {Name = "r5", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "r6")
        {Name = "r6", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "r7")
        {Name = "r7", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "r8")
        {Name = "r8", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TREG_size")
        {Name = "TREG_size", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TREG_case")
        {Name = "TREG_case", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "data_reg_index")
        {Name = "data_reg_index", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "data_reg_name")
        {Name = "data_reg_name", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "conv_reg")
        {Name = "conv_reg", Thy = "HSL"}
  val _ = update_grms
       temp_type_abbrev
       ("TSTATE", T"prod" "pair"
 [T"fmap" "finite_map"
   [T"TREG" "HSL" [], T"cart" "fcp" [bool, T"i32" "words" []]],
  T"fmap" "finite_map"
   [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
  val _ = update_grms
       temp_type_abbrev
       ("TMEM", T"prod" "pair" [T"PTR" "HSL" [], T"OFFSET" "preARM" []])
  val _ = update_grms temp_add_type "TEXP"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_TEXP")
        {Name = "dest_TEXP", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_TEXP")
        {Name = "mk_TEXP", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL0")
        {Name = "HSL0", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL1")
        {Name = "HSL1", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL2")
        {Name = "HSL2", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "inR")
        {Name = "inR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "inC")
        {Name = "inC", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "inE")
        {Name = "inE", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TEXP_case")
        {Name = "TEXP_case", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TEXP_size")
        {Name = "TEXP_size", Thy = "HSL"}
  val _ = update_grms temp_add_type "TROC"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_TROC")
        {Name = "dest_TROC", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_TROC")
        {Name = "mk_TROC", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL3")
        {Name = "HSL3", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL4")
        {Name = "HSL4", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Rg")
        {Name = "Rg", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Cn")
        {Name = "Cn", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TROC_case")
        {Name = "TROC_case", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TROC_size")
        {Name = "TROC_size", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "roc_2_exp")
        {Name = "roc_2_exp", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "tread_tupled")
        {Name = "tread_tupled", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "tread")
        {Name = "tread", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "twrite_tupled")
        {Name = "twrite_tupled", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "twrite")
        {Name = "twrite", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "from_MEXP")
        {Name = "from_MEXP", Thy = "HSL"}
  val _ = update_grms
       temp_type_abbrev
       ("TCND", T"prod" "pair"
 [T"TREG" "HSL" [],
  T"prod" "pair" [T"COND" "preARM" [], T"TROC" "HSL" []]])
  val _ = update_grms temp_add_type "TOPER"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_TOPER")
        {Name = "dest_TOPER", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_TOPER")
        {Name = "mk_TOPER", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL5")
        {Name = "HSL5", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL6")
        {Name = "HSL6", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL7")
        {Name = "HSL7", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL8")
        {Name = "HSL8", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL9")
        {Name = "HSL9", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL10")
        {Name = "HSL10", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL11")
        {Name = "HSL11", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL12")
        {Name = "HSL12", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL13")
        {Name = "HSL13", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL14")
        {Name = "HSL14", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL15")
        {Name = "HSL15", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL16")
        {Name = "HSL16", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL17")
        {Name = "HSL17", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL18")
        {Name = "HSL18", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TLDR")
        {Name = "TLDR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TSTR")
        {Name = "TSTR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TMOV")
        {Name = "TMOV", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TADD")
        {Name = "TADD", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TSUB")
        {Name = "TSUB", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TRSB")
        {Name = "TRSB", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TMUL")
        {Name = "TMUL", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TAND")
        {Name = "TAND", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TORR")
        {Name = "TORR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TEOR")
        {Name = "TEOR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TLSL")
        {Name = "TLSL", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TLSR")
        {Name = "TLSR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TASR")
        {Name = "TASR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TROR")
        {Name = "TROR", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TOPER_case")
        {Name = "TOPER_case", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TOPER_size")
        {Name = "TOPER_size", Thy = "HSL"}
  val _ = update_grms temp_add_type "HSL_STRUCTURE"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_HSL_STRUCTURE")
        {Name = "dest_HSL_STRUCTURE", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_HSL_STRUCTURE")
        {Name = "mk_HSL_STRUCTURE", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL19")
        {Name = "HSL19", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL20")
        {Name = "HSL20", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL21")
        {Name = "HSL21", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL22")
        {Name = "HSL22", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL23")
        {Name = "HSL23", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Blk")
        {Name = "Blk", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Sc")
        {Name = "Sc", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Cj")
        {Name = "Cj", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Tr")
        {Name = "Tr", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Fc")
        {Name = "Fc", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL_STRUCTURE_case")
        {Name = "HSL_STRUCTURE_case", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HSL_STRUCTURE_size")
        {Name = "HSL_STRUCTURE_size", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eval_TCND_tupled")
        {Name = "eval_TCND_tupled", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eval_TCND")
        {Name = "eval_TCND", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "transfer_tupled")
        {Name = "transfer_tupled", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "transfer")
        {Name = "transfer", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "tdecode")
        {Name = "tdecode", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "empty_s")
        {Name = "empty_s", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "run_hsl_tupled_aux")
        {Name = "run_hsl_tupled_aux", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "run_hsl_tupled")
        {Name = "run_hsl_tupled", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "run_hsl")
        {Name = "run_hsl", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "within_bound")
        {Name = "within_bound", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_TEXP")
        {Name = "valid_TEXP", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_assgn_tupled")
        {Name = "valid_assgn_tupled", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_assgn")
        {Name = "valid_assgn", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_struct")
        {Name = "valid_struct", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CSPEC")
        {Name = "CSPEC", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "unique_list")
        {Name = "unique_list", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "notC")
        {Name = "notC", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "match")
        {Name = "match", Thy = "HSL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "valid_arg_list")
        {Name = "valid_arg_list", Thy = "HSL"}
  val HSL_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG PTR_Axiom,
           case_def=PTR_case_def,
           case_cong=PTR_case_cong,
           induction=ORIG PTR_induction,
           nchotomy=PTR_nchotomy,
           size=SOME(Parse.Term`(HSL$PTR_size) :(HSL$PTR) -> (num$num)`,
                     ORIG PTR_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME PTR_distinct,
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
  
  
  val _ = computeLib.add_funs [toPTR_def];  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG TREG_Axiom,
           case_def=TREG_case_def,
           case_cong=TREG_case_cong,
           induction=ORIG TREG_induction,
           nchotomy=TREG_nchotomy,
           size=SOME(Parse.Term`(HSL$TREG_size) :(HSL$TREG) -> (num$num)`,
                     ORIG TREG_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME TREG_distinct,
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
  
  
  val _ = computeLib.add_funs [data_reg_index_def];  
  
  val _ = computeLib.add_funs [data_reg_name_def];  
  
  val _ = computeLib.add_funs [conv_reg_def];  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG TEXP_Axiom,
           case_def=TEXP_case_def,
           case_cong=TEXP_case_cong,
           induction=ORIG TEXP_induction,
           nchotomy=TEXP_nchotomy,
           size=SOME(Parse.Term`(HSL$TEXP_size) :(HSL$TEXP) -> (num$num)`,
                     ORIG TEXP_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME TEXP_11,
           distinct=SOME TEXP_distinct,
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
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG TROC_Axiom,
           case_def=TROC_case_def,
           case_cong=TROC_case_cong,
           induction=ORIG TROC_induction,
           nchotomy=TROC_nchotomy,
           size=SOME(Parse.Term`(HSL$TROC_size) :(HSL$TROC) -> (num$num)`,
                     ORIG TROC_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME TROC_11,
           distinct=SOME TROC_distinct,
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
  
  
  val _ = computeLib.add_funs [roc_2_exp_def];  
  
  val _ = computeLib.add_funs [tread_def];  
  
  val _ = computeLib.add_funs [twrite_def];  
  
  val _ = computeLib.add_funs [from_MEXP_def];  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG TOPER_Axiom,
           case_def=TOPER_case_def,
           case_cong=TOPER_case_cong,
           induction=ORIG TOPER_induction,
           nchotomy=TOPER_nchotomy,
           size=SOME(Parse.Term`(HSL$TOPER_size) :(HSL$TOPER) -> (num$num)`,
                     ORIG TOPER_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME TOPER_11,
           distinct=SOME TOPER_distinct,
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
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG HSL_STRUCTURE_Axiom,
           case_def=HSL_STRUCTURE_case_def,
           case_cong=HSL_STRUCTURE_case_cong,
           induction=ORIG HSL_STRUCTURE_induction,
           nchotomy=HSL_STRUCTURE_nchotomy,
           size=SOME(Parse.Term`(HSL$HSL_STRUCTURE_size) :(HSL$HSL_STRUCTURE) -> (num$num)`,
                     ORIG HSL_STRUCTURE_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME HSL_STRUCTURE_11,
           distinct=SOME HSL_STRUCTURE_distinct,
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
  
  
  val _ = computeLib.add_funs [eval_TCND_def];  
  
  val _ = computeLib.add_funs [transfer_def];  
  
  val _ = computeLib.add_funs [tdecode_def];  
  
  val _ = computeLib.add_funs [empty_s_def];  
  
  val _ = computeLib.add_funs [run_hsl_def];  
  
  val _ = computeLib.add_funs [within_bound_def];  
  
  val _ = computeLib.add_funs [valid_TEXP_def];  
  
  val _ = computeLib.add_funs [valid_assgn_def];  
  
  val _ = computeLib.add_funs [valid_struct_def];  
  
  val _ = computeLib.add_funs [CSPEC_def];  
  
  val _ = computeLib.add_funs [unique_list_def];  
  
  val _ = computeLib.add_funs [notC_def];  
  
  val _ = computeLib.add_funs [match_def];  
  
  val _ = computeLib.add_funs [valid_arg_list_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
