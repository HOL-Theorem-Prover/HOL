structure ILTheory :> ILTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading ILTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype

  (*  Parents *)
  local open ARMCompositionTheory
  in end;
  val _ = Theory.link_parents
          ("IL",Arbnum.fromString "1157171238",Arbnum.fromString "41829")
          [("ARMComposition",
           Arbnum.fromString "1157170992",
           Arbnum.fromString "779283")];
  val _ = Theory.incorporate_types "IL"
       [("MEXP",0), ("DOPER",0), ("MREG",0), ("CTL_STRUCTURE",0)];
  val _ = Theory.incorporate_consts "IL"
     [("translate_condition",
       ((T"prod" "pair"
          [T"MREG" "IL" [], T"prod" "pair" [alpha, T"MEXP" "IL" []]] -->
         T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [alpha, T"EXP" "preARM" []]]))),
      ("index_of_reg",((T"MREG" "IL" [] --> T"num" "num" []))),
      ("dest_DOPER",
       ((T"DOPER" "IL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"prod" "pair"
                [T"MEXP" "IL" [],
                 T"prod" "pair"
                  [T"MREG" "IL" [],
                   T"prod" "pair"
                    [T"MREG" "IL" [],
                     T"prod" "pair"
                      [T"cart" "fcp" [bool, T"i5" "words" []],
                       T"prod" "pair"
                        [T"num" "num" [],
                         T"list" "list" [T"num" "num" []]]]]]]]]]))),
      ("run_ir",
       ((T"CTL_STRUCTURE" "IL" [] -->
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          -->
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]])))),
      ("WELL_FORMED",((T"CTL_STRUCTURE" "IL" [] --> bool))),
      ("eval_il_cond",
       ((T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)))),
      ("WELL_FORMED_SUB",((T"CTL_STRUCTURE" "IL" [] --> bool))),
      ("num2MREG",((T"num" "num" [] --> T"MREG" "IL" []))),
      ("mdecode",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"DOPER" "IL" [] -->
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]])))),
      ("DOPER_case",
       (((T"MREG" "IL" [] -->
          (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
           alpha)) -->
         ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
           (T"MREG" "IL" [] --> alpha)) -->
          ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)) -->
           ((T"MREG" "IL" [] -->
             (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
            ((T"MREG" "IL" [] -->
              (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
             ((T"MREG" "IL" [] -->
               (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
              ((T"MREG" "IL" [] -->
                (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> alpha))) -->
               ((T"MREG" "IL" [] -->
                 (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
                ((T"MREG" "IL" [] -->
                  (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
                 ((T"MREG" "IL" [] -->
                   (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
                  ((T"MREG" "IL" [] -->
                    (T"MREG" "IL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                   -->
                   ((T"MREG" "IL" [] -->
                     (T"MREG" "IL" [] -->
                      (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                    -->
                    ((T"MREG" "IL" [] -->
                      (T"MREG" "IL" [] -->
                       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                     -->
                     ((T"MREG" "IL" [] -->
                       (T"MREG" "IL" [] -->
                        (T"cart" "fcp" [bool, T"i5" "words" []] -->
                         alpha))) -->
                      ((T"num" "num" [] -->
                        (T"list" "list" [T"num" "num" []] --> alpha)) -->
                       ((T"num" "num" [] -->
                         (T"list" "list" [T"num" "num" []] --> alpha)) -->
                        (T"DOPER" "IL" [] --> alpha))))))))))))))))))),
      ("R14",(T"MREG" "IL" [])), ("R13",(T"MREG" "IL" [])),
      ("R12",(T"MREG" "IL" [])), ("R11",(T"MREG" "IL" [])),
      ("R10",(T"MREG" "IL" [])),
      ("IL9",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("IL8",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> T"DOPER" "IL" []))))),
      ("IL7",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("IL6",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("IL5",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("IL4",
       ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
      ("IL3",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         (T"MREG" "IL" [] --> T"DOPER" "IL" [])))),
      ("IL2",
       ((T"MREG" "IL" [] -->
         (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
          T"DOPER" "IL" [])))),
      ("IL1",
       ((T"cart" "fcp" [bool, T"i4" "words" []] -->
         (T"cart" "fcp" [bool, T"i8" "words" []] --> T"MEXP" "IL" [])))),
      ("IL0",((T"MREG" "IL" [] --> T"MEXP" "IL" []))),
      ("popL",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"num" "num" [] -->
          (T"list" "list" [T"num" "num" []] -->
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]))))),
      ("BLK",
       ((T"list" "list" [T"DOPER" "IL" []] --> T"CTL_STRUCTURE" "IL" []))),
      ("run_arm",
       ((T"list" "list"
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
         (T"prod" "pair"
           [T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]],
            (T"num" "num" [] --> bool)] -->
          T"prod" "pair"
           [T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]],
            (T"num" "num" [] --> bool)])))),
      ("dest_MEXP",
       ((T"MEXP" "IL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i4" "words" []],
               T"cart" "fcp" [bool, T"i8" "words" []]]]]))),
      ("translate",
       ((T"CTL_STRUCTURE" "IL" [] -->
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
                 T"option" "option" [T"OFFSET" "preARM" []]]]]]))),
      ("MREG_case",
       ((alpha -->
         (alpha -->
          (alpha -->
           (alpha -->
            (alpha -->
             (alpha -->
              (alpha -->
               (alpha -->
                (alpha -->
                 (alpha -->
                  (alpha -->
                   (alpha -->
                    (alpha -->
                     (alpha -->
                      (alpha -->
                       (T"MREG" "IL" [] --> alpha)))))))))))))))))),
      ("MEXP_case",
       (((T"MREG" "IL" [] --> alpha) -->
         ((T"cart" "fcp" [bool, T"i4" "words" []] -->
           (T"cart" "fcp" [bool, T"i8" "words" []] --> alpha)) -->
          (T"MEXP" "IL" [] --> alpha))))),
      ("CTL_STRUCTURE_size",
       ((T"CTL_STRUCTURE" "IL" [] --> T"num" "num" []))),
      ("mk_MEXP",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i4" "words" []],
               T"cart" "fcp" [bool, T"i8" "words" []]]]] -->
         T"MEXP" "IL" []))),
      ("dest_CTL_STRUCTURE",
       ((T"CTL_STRUCTURE" "IL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"DOPER" "IL" []],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]))),
      ("DOPER_size",((T"DOPER" "IL" [] --> T"num" "num" []))),
      ("mk_DOPER",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"prod" "pair"
                [T"MEXP" "IL" [],
                 T"prod" "pair"
                  [T"MREG" "IL" [],
                   T"prod" "pair"
                    [T"MREG" "IL" [],
                     T"prod" "pair"
                      [T"cart" "fcp" [bool, T"i5" "words" []],
                       T"prod" "pair"
                        [T"num" "num" [],
                         T"list" "list" [T"num" "num" []]]]]]]]]] -->
         T"DOPER" "IL" []))),
      ("MSTR",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         (T"MREG" "IL" [] --> T"DOPER" "IL" [])))),
      ("MSUB",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("MREG2num",((T"MREG" "IL" [] --> T"num" "num" []))),
      ("MROR",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "IL" []))))),
      ("MRSB",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("MPUSH",
       ((T"num" "num" [] -->
         (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" [])))),
      ("MPOP",
       ((T"num" "num" [] -->
         (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" [])))),
      ("MORR",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("MMUL",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> T"DOPER" "IL" []))))),
      ("mk_CTL_STRUCTURE",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"DOPER" "IL" []],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
         T"CTL_STRUCTURE" "IL" []))),
      ("MMOV",
       ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
      ("MLSR",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "IL" []))))),
      ("MLSL",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "IL" []))))),
      ("translate_assignment",
       ((T"DOPER" "IL" [] -->
         T"prod" "pair"
          [T"prod" "pair"
            [T"OPERATOR" "preARM" [],
             T"prod" "pair"
              [T"option" "option" [T"COND" "preARM" []], bool]],
           T"prod" "pair"
            [T"option" "option" [T"EXP" "preARM" []],
             T"prod" "pair"
              [T"list" "list" [T"EXP" "preARM" []],
               T"option" "option" [T"OFFSET" "preARM" []]]]]))),
      ("pushL",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"num" "num" [] -->
          (T"list" "list" [T"num" "num" []] -->
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]))))),
      ("MLDR",
       ((T"MREG" "IL" [] -->
         (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
          T"DOPER" "IL" [])))),
      ("from_reg_index",((T"num" "num" [] --> T"MREG" "IL" []))),
      ("toREG",((T"MREG" "IL" [] --> T"EXP" "preARM" []))),
      ("MEOR",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("MREG_size",((T"MREG" "IL" [] --> T"num" "num" []))),
      ("TR",
       ((T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
         (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])))),
      ("MEXP_size",((T"MEXP" "IL" [] --> T"num" "num" []))),
      ("toMEM",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         T"EXP" "preARM" []))),
      ("SC",
       ((T"CTL_STRUCTURE" "IL" [] -->
         (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])))),
      ("MR",((T"MREG" "IL" [] --> T"MEXP" "IL" []))),
      ("MASR",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "IL" []))))), ("R9",(T"MREG" "IL" [])),
      ("R8",(T"MREG" "IL" [])), ("R7",(T"MREG" "IL" [])),
      ("R6",(T"MREG" "IL" [])), ("R5",(T"MREG" "IL" [])),
      ("R4",(T"MREG" "IL" [])), ("R3",(T"MREG" "IL" [])),
      ("R2",(T"MREG" "IL" [])), ("R1",(T"MREG" "IL" [])),
      ("R0",(T"MREG" "IL" [])),
      ("MC",
       ((T"cart" "fcp" [bool, T"i4" "words" []] -->
         (T"cart" "fcp" [bool, T"i8" "words" []] --> T"MEXP" "IL" [])))),
      ("toEXP",((T"MEXP" "IL" [] --> T"EXP" "preARM" []))),
      ("MAND",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("CJ",
       ((T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
         (T"CTL_STRUCTURE" "IL" [] -->
          (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" []))))),
      ("MADD",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("IL19",
       ((T"CTL_STRUCTURE" "IL" [] -->
         (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])))),
      ("IL18",
       ((T"list" "list" [T"DOPER" "IL" []] --> T"CTL_STRUCTURE" "IL" []))),
      ("IL17",
       ((T"num" "num" [] -->
         (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" [])))),
      ("IL16",
       ((T"num" "num" [] -->
         (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" [])))),
      ("IL21",
       ((T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
         (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])))),
      ("IL15",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "IL" []))))),
      ("IL20",
       ((T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
         (T"CTL_STRUCTURE" "IL" [] -->
          (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" []))))),
      ("IL14",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "IL" []))))),
      ("IL13",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "IL" []))))),
      ("IL12",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "IL" []))))),
      ("IL11",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("IL10",
       ((T"MREG" "IL" [] -->
         (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))))),
      ("CTL_STRUCTURE_case",
       (((T"list" "list" [T"DOPER" "IL" []] --> alpha) -->
         ((T"CTL_STRUCTURE" "IL" [] -->
           (T"CTL_STRUCTURE" "IL" [] --> alpha)) -->
          ((T"prod" "pair"
             [T"MREG" "IL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
            (T"CTL_STRUCTURE" "IL" [] -->
             (T"CTL_STRUCTURE" "IL" [] --> alpha))) -->
           ((T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
             (T"CTL_STRUCTURE" "IL" [] --> alpha)) -->
            (T"CTL_STRUCTURE" "IL" [] --> alpha)))))))];

  local
  val share_table = Vector.fromList
  [C"?" "bool"
    ((((T"MREG" "IL" [] --> T"num" "num" []) --> bool) --> bool)),
   V"rep" ((T"MREG" "IL" [] --> T"num" "num" [])),
   C"TYPE_DEFINITION" "bool"
    (((T"num" "num" [] --> bool) -->
      ((T"MREG" "IL" [] --> T"num" "num" []) --> bool))),
   V"n" (T"num" "num" []),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"MREG" "IL" [] --> bool) --> bool)),
   V"a" (T"MREG" "IL" []),
   C"=" "min" ((T"MREG" "IL" [] --> (T"MREG" "IL" [] --> bool))),
   C"num2MREG" "IL" ((T"num" "num" [] --> T"MREG" "IL" [])),
   C"MREG2num" "IL" ((T"MREG" "IL" [] --> T"num" "num" [])),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"r" (T"num" "num" []), C"=" "min" ((bool --> (bool --> bool))),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"R0" "IL" (T"MREG" "IL" []), C"0" "num" (T"num" "num" []),
   C"R1" "IL" (T"MREG" "IL" []), C"R2" "IL" (T"MREG" "IL" []),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"R3" "IL" (T"MREG" "IL" []), C"R4" "IL" (T"MREG" "IL" []),
   C"R5" "IL" (T"MREG" "IL" []), C"R6" "IL" (T"MREG" "IL" []),
   C"R7" "IL" (T"MREG" "IL" []), C"R8" "IL" (T"MREG" "IL" []),
   C"R9" "IL" (T"MREG" "IL" []), C"R10" "IL" (T"MREG" "IL" []),
   C"R11" "IL" (T"MREG" "IL" []), C"R12" "IL" (T"MREG" "IL" []),
   C"R13" "IL" (T"MREG" "IL" []), C"R14" "IL" (T"MREG" "IL" []),
   V"x" (T"MREG" "IL" []),
   C"MREG_size" "IL" ((T"MREG" "IL" [] --> T"num" "num" [])),
   C"!" "bool" (((alpha --> bool) --> bool)), V"v0" (alpha), V"v1" (alpha),
   V"v2" (alpha), V"v3" (alpha), V"v4" (alpha), V"v5" (alpha),
   V"v6" (alpha), V"v7" (alpha), V"v8" (alpha), V"v9" (alpha),
   V"v10" (alpha), V"v11" (alpha), V"v12" (alpha), V"v13" (alpha),
   V"v14" (alpha), C"=" "min" ((alpha --> (alpha --> bool))),
   C"MREG_case" "IL"
    ((alpha -->
      (alpha -->
       (alpha -->
        (alpha -->
         (alpha -->
          (alpha -->
           (alpha -->
            (alpha -->
             (alpha -->
              (alpha -->
               (alpha -->
                (alpha -->
                 (alpha -->
                  (alpha -->
                   (alpha --> (T"MREG" "IL" [] --> alpha))))))))))))))))),
   V"m" (T"num" "num" []),
   C"COND" "bool" ((bool --> (alpha --> (alpha --> alpha)))),
   C"?" "bool"
    ((((T"MEXP" "IL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i4" "words" []],
              T"cart" "fcp" [bool, T"i8" "words" []]]]]) --> bool) -->
      bool)),
   V"rep"
    ((T"MEXP" "IL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i4" "words" []],
            T"cart" "fcp" [bool, T"i8" "words" []]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i4" "words" []],
             T"cart" "fcp" [bool, T"i8" "words" []]]]] --> bool) -->
      ((T"MEXP" "IL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i4" "words" []],
              T"cart" "fcp" [bool, T"i8" "words" []]]]]) --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i4" "words" []],
           T"cart" "fcp" [bool, T"i8" "words" []]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i4" "words" []],
              T"cart" "fcp" [bool, T"i8" "words" []]]]] --> bool) --> bool)
      --> bool)),
   V"'MEXP'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i4" "words" []],
            T"cart" "fcp" [bool, T"i8" "words" []]]]] --> bool)),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i4" "words" []],
             T"cart" "fcp" [bool, T"i8" "words" []]]]] --> bool) -->
      bool)), C"\\/" "bool" ((bool --> (bool --> bool))),
   C"?" "bool" (((T"MREG" "IL" [] --> bool) --> bool)),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i4" "words" []],
            T"cart" "fcp" [bool, T"i8" "words" []]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i4" "words" []],
             T"cart" "fcp" [bool, T"i8" "words" []]]]] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i4" "words" []],
           T"cart" "fcp" [bool, T"i8" "words" []]]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i4" "words" []],
               T"cart" "fcp" [bool, T"i8" "words" []]]]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i4" "words" []],
              T"cart" "fcp" [bool, T"i8" "words" []]]]])))),
   C"," "pair"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair"
        [T"cart" "fcp" [bool, T"i4" "words" []],
         T"cart" "fcp" [bool, T"i8" "words" []]] -->
       T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i4" "words" []],
           T"cart" "fcp" [bool, T"i8" "words" []]]]))),
   C"," "pair"
    ((T"cart" "fcp" [bool, T"i4" "words" []] -->
      (T"cart" "fcp" [bool, T"i8" "words" []] -->
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i4" "words" []],
         T"cart" "fcp" [bool, T"i8" "words" []]]))),
   C"@" "min"
    (((T"cart" "fcp" [bool, T"i4" "words" []] --> bool) -->
      T"cart" "fcp" [bool, T"i4" "words" []])),
   V"v" (T"cart" "fcp" [bool, T"i4" "words" []]), C"T" "bool" (bool),
   C"@" "min"
    (((T"cart" "fcp" [bool, T"i8" "words" []] --> bool) -->
      T"cart" "fcp" [bool, T"i8" "words" []])),
   V"v" (T"cart" "fcp" [bool, T"i8" "words" []]),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i4" "words" []],
           T"cart" "fcp" [bool, T"i8" "words" []]]]]),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i4" "words" []] --> bool) --> bool)),
   V"a0" (T"cart" "fcp" [bool, T"i4" "words" []]),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i8" "words" []] --> bool) --> bool)),
   V"a1" (T"cart" "fcp" [bool, T"i8" "words" []]),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"@" "min" (((T"MREG" "IL" [] --> bool) --> T"MREG" "IL" [])),
   V"v" (T"MREG" "IL" []),
   C"!" "bool" (((T"MEXP" "IL" [] --> bool) --> bool)),
   V"a" (T"MEXP" "IL" []),
   C"=" "min" ((T"MEXP" "IL" [] --> (T"MEXP" "IL" [] --> bool))),
   C"mk_MEXP" "IL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i4" "words" []],
            T"cart" "fcp" [bool, T"i8" "words" []]]]] -->
      T"MEXP" "IL" [])),
   C"dest_MEXP" "IL"
    ((T"MEXP" "IL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i4" "words" []],
            T"cart" "fcp" [bool, T"i8" "words" []]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i4" "words" []],
           T"cart" "fcp" [bool, T"i8" "words" []]]]]),
   C"=" "min"
    (((T"MREG" "IL" [] --> T"MEXP" "IL" []) -->
      ((T"MREG" "IL" [] --> T"MEXP" "IL" []) --> bool))),
   C"IL0" "IL" ((T"MREG" "IL" [] --> T"MEXP" "IL" [])),
   C"=" "min"
    (((T"cart" "fcp" [bool, T"i4" "words" []] -->
       (T"cart" "fcp" [bool, T"i8" "words" []] --> T"MEXP" "IL" [])) -->
      ((T"cart" "fcp" [bool, T"i4" "words" []] -->
        (T"cart" "fcp" [bool, T"i8" "words" []] --> T"MEXP" "IL" [])) -->
       bool))),
   C"IL1" "IL"
    ((T"cart" "fcp" [bool, T"i4" "words" []] -->
      (T"cart" "fcp" [bool, T"i8" "words" []] --> T"MEXP" "IL" []))),
   C"MR" "IL" ((T"MREG" "IL" [] --> T"MEXP" "IL" [])),
   C"MC" "IL"
    ((T"cart" "fcp" [bool, T"i4" "words" []] -->
      (T"cart" "fcp" [bool, T"i8" "words" []] --> T"MEXP" "IL" []))),
   C"!" "bool" ((((T"MREG" "IL" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"MREG" "IL" [] --> alpha)),
   C"!" "bool"
    ((((T"cart" "fcp" [bool, T"i4" "words" []] -->
        (T"cart" "fcp" [bool, T"i8" "words" []] --> alpha)) --> bool) -->
      bool)),
   V"f1"
    ((T"cart" "fcp" [bool, T"i4" "words" []] -->
      (T"cart" "fcp" [bool, T"i8" "words" []] --> alpha))),
   C"MEXP_case" "IL"
    (((T"MREG" "IL" [] --> alpha) -->
      ((T"cart" "fcp" [bool, T"i4" "words" []] -->
        (T"cart" "fcp" [bool, T"i8" "words" []] --> alpha)) -->
       (T"MEXP" "IL" [] --> alpha)))),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i4" "words" []] --> bool) --> bool)),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i8" "words" []] --> bool) --> bool)),
   C"MEXP_size" "IL" ((T"MEXP" "IL" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"index_of_reg" "IL" ((T"MREG" "IL" [] --> T"num" "num" [])),
   V"i" (T"num" "num" []),
   C"from_reg_index" "IL" ((T"num" "num" [] --> T"MREG" "IL" [])),
   C"COND" "bool"
    ((bool -->
      (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> T"MREG" "IL" [])))),
   V"r" (T"MREG" "IL" []),
   C"=" "min" ((T"EXP" "preARM" [] --> (T"EXP" "preARM" [] --> bool))),
   C"toREG" "IL" ((T"MREG" "IL" [] --> T"EXP" "preARM" [])),
   C"REG" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   V"base" (T"num" "num" []),
   C"!" "bool" (((T"OFFSET" "preARM" [] --> bool) --> bool)),
   V"offset" (T"OFFSET" "preARM" []),
   C"toMEM" "IL"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"EXP" "preARM" [])),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"OFFSET" "preARM" [] -->
       T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]))),
   C"MEM" "preARM"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"EXP" "preARM" [])),
   C"toEXP" "IL" ((T"MEXP" "IL" [] --> T"EXP" "preARM" [])),
   V"shift" (T"cart" "fcp" [bool, T"i4" "words" []]),
   V"c" (T"cart" "fcp" [bool, T"i8" "words" []]),
   C"WCONST" "preARM"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"EXP" "preARM" [])),
   C"word_ror" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"w2w" "words"
    ((T"cart" "fcp" [bool, T"i8" "words" []] -->
      T"cart" "fcp" [bool, T"i32" "words" []])),
   C"*" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"w2n" "words"
    ((T"cart" "fcp" [bool, T"i4" "words" []] --> T"num" "num" [])),
   C"?" "bool"
    ((((T"DOPER" "IL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"prod" "pair"
               [T"MEXP" "IL" [],
                T"prod" "pair"
                 [T"MREG" "IL" [],
                  T"prod" "pair"
                   [T"MREG" "IL" [],
                    T"prod" "pair"
                     [T"cart" "fcp" [bool, T"i5" "words" []],
                      T"prod" "pair"
                       [T"num" "num" [],
                        T"list" "list" [T"num" "num" []]]]]]]]]]) --> bool)
      --> bool)),
   V"rep"
    ((T"DOPER" "IL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "IL" [],
              T"prod" "pair"
               [T"MREG" "IL" [],
                T"prod" "pair"
                 [T"MREG" "IL" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i5" "words" []],
                    T"prod" "pair"
                     [T"num" "num" [],
                      T"list" "list" [T"num" "num" []]]]]]]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"prod" "pair"
              [T"MEXP" "IL" [],
               T"prod" "pair"
                [T"MREG" "IL" [],
                 T"prod" "pair"
                  [T"MREG" "IL" [],
                   T"prod" "pair"
                    [T"cart" "fcp" [bool, T"i5" "words" []],
                     T"prod" "pair"
                      [T"num" "num" [],
                       T"list" "list" [T"num" "num" []]]]]]]]]] --> bool)
      -->
      ((T"DOPER" "IL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"prod" "pair"
               [T"MEXP" "IL" [],
                T"prod" "pair"
                 [T"MREG" "IL" [],
                  T"prod" "pair"
                   [T"MREG" "IL" [],
                    T"prod" "pair"
                     [T"cart" "fcp" [bool, T"i5" "words" []],
                      T"prod" "pair"
                       [T"num" "num" [],
                        T"list" "list" [T"num" "num" []]]]]]]]]]) -->
       bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "IL" [],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair"
                [T"MREG" "IL" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i5" "words" []],
                   T"prod" "pair"
                    [T"num" "num" [],
                     T"list" "list" [T"num" "num" []]]]]]]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"prod" "pair"
               [T"MEXP" "IL" [],
                T"prod" "pair"
                 [T"MREG" "IL" [],
                  T"prod" "pair"
                   [T"MREG" "IL" [],
                    T"prod" "pair"
                     [T"cart" "fcp" [bool, T"i5" "words" []],
                      T"prod" "pair"
                       [T"num" "num" [],
                        T"list" "list" [T"num" "num" []]]]]]]]]] --> bool)
       --> bool) --> bool)),
   V"'DOPER'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "IL" [],
              T"prod" "pair"
               [T"MREG" "IL" [],
                T"prod" "pair"
                 [T"MREG" "IL" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i5" "words" []],
                    T"prod" "pair"
                     [T"num" "num" [],
                      T"list" "list" [T"num" "num" []]]]]]]]]] --> bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"prod" "pair"
              [T"MEXP" "IL" [],
               T"prod" "pair"
                [T"MREG" "IL" [],
                 T"prod" "pair"
                  [T"MREG" "IL" [],
                   T"prod" "pair"
                    [T"cart" "fcp" [bool, T"i5" "words" []],
                     T"prod" "pair"
                      [T"num" "num" [],
                       T"list" "list" [T"num" "num" []]]]]]]]]] --> bool)
      --> bool)), V"a0" (T"MREG" "IL" []),
   C"?" "bool"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> bool)),
   V"a1" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "IL" [],
              T"prod" "pair"
               [T"MREG" "IL" [],
                T"prod" "pair"
                 [T"MREG" "IL" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i5" "words" []],
                    T"prod" "pair"
                     [T"num" "num" [],
                      T"list" "list" [T"num" "num" []]]]]]]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"prod" "pair"
              [T"MEXP" "IL" [],
               T"prod" "pair"
                [T"MREG" "IL" [],
                 T"prod" "pair"
                  [T"MREG" "IL" [],
                   T"prod" "pair"
                    [T"cart" "fcp" [bool, T"i5" "words" []],
                     T"prod" "pair"
                      [T"num" "num" [],
                       T"list" "list" [T"num" "num" []]]]]]]]]] -->
       bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "IL" [],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair"
                [T"MREG" "IL" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i5" "words" []],
                   T"prod" "pair"
                    [T"num" "num" [],
                     T"list" "list" [T"num" "num" []]]]]]]]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"prod" "pair"
                [T"MEXP" "IL" [],
                 T"prod" "pair"
                  [T"MREG" "IL" [],
                   T"prod" "pair"
                    [T"MREG" "IL" [],
                     T"prod" "pair"
                      [T"cart" "fcp" [bool, T"i5" "words" []],
                       T"prod" "pair"
                        [T"num" "num" [],
                         T"list" "list" [T"num" "num" []]]]]]]]]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"prod" "pair"
               [T"MEXP" "IL" [],
                T"prod" "pair"
                 [T"MREG" "IL" [],
                  T"prod" "pair"
                   [T"MREG" "IL" [],
                    T"prod" "pair"
                     [T"cart" "fcp" [bool, T"i5" "words" []],
                      T"prod" "pair"
                       [T"num" "num" [],
                        T"list" "list" [T"num" "num" []]]]]]]]]])))),
   C"," "pair"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"prod" "pair"
          [T"MEXP" "IL" [],
           T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i5" "words" []],
                 T"prod" "pair"
                  [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]]]]
       -->
       T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "IL" [],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair"
                [T"MREG" "IL" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i5" "words" []],
                   T"prod" "pair"
                    [T"num" "num" [],
                     T"list" "list" [T"num" "num" []]]]]]]]]))),
   C"," "pair"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"prod" "pair"
        [T"MEXP" "IL" [],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i5" "words" []],
               T"prod" "pair"
                [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]]] -->
       T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"prod" "pair"
          [T"MEXP" "IL" [],
           T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i5" "words" []],
                 T"prod" "pair"
                  [T"num" "num" [],
                   T"list" "list" [T"num" "num" []]]]]]]]))),
   C"," "pair"
    ((T"MEXP" "IL" [] -->
      (T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i5" "words" []],
             T"prod" "pair"
              [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]] -->
       T"prod" "pair"
        [T"MEXP" "IL" [],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i5" "words" []],
               T"prod" "pair"
                [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]]]))),
   C"@" "min" (((T"MEXP" "IL" [] --> bool) --> T"MEXP" "IL" [])),
   V"v" (T"MEXP" "IL" []),
   C"," "pair"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i5" "words" []],
           T"prod" "pair"
            [T"num" "num" [], T"list" "list" [T"num" "num" []]]]] -->
       T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i5" "words" []],
             T"prod" "pair"
              [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]]))),
   C"," "pair"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair"
        [T"cart" "fcp" [bool, T"i5" "words" []],
         T"prod" "pair"
          [T"num" "num" [], T"list" "list" [T"num" "num" []]]] -->
       T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i5" "words" []],
           T"prod" "pair"
            [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]))),
   C"," "pair"
    ((T"cart" "fcp" [bool, T"i5" "words" []] -->
      (T"prod" "pair" [T"num" "num" [], T"list" "list" [T"num" "num" []]]
       -->
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i5" "words" []],
         T"prod" "pair"
          [T"num" "num" [], T"list" "list" [T"num" "num" []]]]))),
   C"@" "min"
    (((T"cart" "fcp" [bool, T"i5" "words" []] --> bool) -->
      T"cart" "fcp" [bool, T"i5" "words" []])),
   V"v" (T"cart" "fcp" [bool, T"i5" "words" []]),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"list" "list" [T"num" "num" []] -->
       T"prod" "pair"
        [T"num" "num" [], T"list" "list" [T"num" "num" []]]))),
   C"@" "min" (((T"num" "num" [] --> bool) --> T"num" "num" [])),
   V"v" (T"num" "num" []),
   C"@" "min"
    (((T"list" "list" [T"num" "num" []] --> bool) -->
      T"list" "list" [T"num" "num" []])),
   V"v" (T"list" "list" [T"num" "num" []]),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "IL" [],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair"
                [T"MREG" "IL" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i5" "words" []],
                   T"prod" "pair"
                    [T"num" "num" [],
                     T"list" "list" [T"num" "num" []]]]]]]]]]),
   V"a0" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"a1" (T"MREG" "IL" []),
   C"?" "bool" (((T"MEXP" "IL" [] --> bool) --> bool)),
   V"a1" (T"MEXP" "IL" []),
   C"@" "min"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []])),
   V"v" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"a2" (T"MEXP" "IL" []), V"a2" (T"MREG" "IL" []),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i5" "words" []] --> bool) --> bool)),
   V"a2" (T"cart" "fcp" [bool, T"i5" "words" []]),
   C"?" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"a0" (T"num" "num" []),
   C"?" "bool" (((T"list" "list" [T"num" "num" []] --> bool) --> bool)),
   V"a1" (T"list" "list" [T"num" "num" []]),
   C"!" "bool" (((T"DOPER" "IL" [] --> bool) --> bool)),
   V"a" (T"DOPER" "IL" []),
   C"=" "min" ((T"DOPER" "IL" [] --> (T"DOPER" "IL" [] --> bool))),
   C"mk_DOPER" "IL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "IL" [],
              T"prod" "pair"
               [T"MREG" "IL" [],
                T"prod" "pair"
                 [T"MREG" "IL" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i5" "words" []],
                    T"prod" "pair"
                     [T"num" "num" [],
                      T"list" "list" [T"num" "num" []]]]]]]]]] -->
      T"DOPER" "IL" [])),
   C"dest_DOPER" "IL"
    ((T"DOPER" "IL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "IL" [],
              T"prod" "pair"
               [T"MREG" "IL" [],
                T"prod" "pair"
                 [T"MREG" "IL" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i5" "words" []],
                    T"prod" "pair"
                     [T"num" "num" [],
                      T"list" "list" [T"num" "num" []]]]]]]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "IL" [],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair"
                [T"MREG" "IL" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i5" "words" []],
                   T"prod" "pair"
                    [T"num" "num" [],
                     T"list" "list" [T"num" "num" []]]]]]]]]]),
   C"=" "min"
    (((T"MREG" "IL" [] -->
       (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        T"DOPER" "IL" [])) -->
      ((T"MREG" "IL" [] -->
        (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         T"DOPER" "IL" [])) --> bool))),
   C"IL2" "IL"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"DOPER" "IL" []))),
   C"=" "min"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       (T"MREG" "IL" [] --> T"DOPER" "IL" [])) -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        (T"MREG" "IL" [] --> T"DOPER" "IL" [])) --> bool))),
   C"IL3" "IL"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "IL" [] --> T"DOPER" "IL" []))),
   C"=" "min"
    (((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])) -->
      ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])) -->
       bool))),
   C"IL4" "IL"
    ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))),
   C"=" "min"
    (((T"MREG" "IL" [] -->
       (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))) -->
      ((T"MREG" "IL" [] -->
        (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))) -->
       bool))),
   C"IL5" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"IL6" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"IL7" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"=" "min"
    (((T"MREG" "IL" [] -->
       (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> T"DOPER" "IL" []))) -->
      ((T"MREG" "IL" [] -->
        (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> T"DOPER" "IL" []))) -->
       bool))),
   C"IL8" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> T"DOPER" "IL" [])))),
   C"IL9" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"IL10" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"IL11" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"=" "min"
    (((T"MREG" "IL" [] -->
       (T"MREG" "IL" [] -->
        (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" []))) -->
      ((T"MREG" "IL" [] -->
        (T"MREG" "IL" [] -->
         (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" [])))
       --> bool))),
   C"IL12" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" [])))),
   C"IL13" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" [])))),
   C"IL14" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" [])))),
   C"IL15" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" [])))),
   C"=" "min"
    (((T"num" "num" [] -->
       (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" [])) -->
      ((T"num" "num" [] -->
        (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" [])) -->
       bool))),
   C"IL16" "IL"
    ((T"num" "num" [] -->
      (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" []))),
   C"IL17" "IL"
    ((T"num" "num" [] -->
      (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" []))),
   C"MLDR" "IL"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"DOPER" "IL" []))),
   C"MSTR" "IL"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "IL" [] --> T"DOPER" "IL" []))),
   C"MMOV" "IL"
    ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))),
   C"MADD" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"MSUB" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"MRSB" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"MMUL" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> T"DOPER" "IL" [])))),
   C"MAND" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"MORR" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"MEOR" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))),
   C"MLSL" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" [])))),
   C"MLSR" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" [])))),
   C"MASR" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" [])))),
   C"MROR" "IL"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "IL" [])))),
   C"MPUSH" "IL"
    ((T"num" "num" [] -->
      (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" []))),
   C"MPOP" "IL"
    ((T"num" "num" [] -->
      (T"list" "list" [T"num" "num" []] --> T"DOPER" "IL" []))),
   C"!" "bool"
    ((((T"MREG" "IL" [] -->
        (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         alpha)) --> bool) --> bool)),
   V"f"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       alpha))),
   C"!" "bool"
    ((((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        (T"MREG" "IL" [] --> alpha)) --> bool) --> bool)),
   V"f1"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "IL" [] --> alpha))),
   C"!" "bool"
    ((((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)) --> bool) -->
      bool)), V"f2" ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))),
   C"!" "bool"
    ((((T"MREG" "IL" [] -->
        (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) --> bool) -->
      bool)),
   V"f3"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f4"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f5"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   C"!" "bool"
    ((((T"MREG" "IL" [] -->
        (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> alpha))) --> bool) -->
      bool)),
   V"f6"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> alpha)))),
   V"f7"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f8"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f9"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   C"!" "bool"
    ((((T"MREG" "IL" [] -->
        (T"MREG" "IL" [] -->
         (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha))) --> bool) -->
      bool)),
   V"f10"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f11"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f12"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f13"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   C"!" "bool"
    ((((T"num" "num" [] --> (T"list" "list" [T"num" "num" []] --> alpha))
       --> bool) --> bool)),
   V"f14"
    ((T"num" "num" [] --> (T"list" "list" [T"num" "num" []] --> alpha))),
   V"f15"
    ((T"num" "num" [] --> (T"list" "list" [T"num" "num" []] --> alpha))),
   C"!" "bool"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> bool)),
   C"DOPER_case" "IL"
    (((T"MREG" "IL" [] -->
       (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha))
      -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        (T"MREG" "IL" [] --> alpha)) -->
       ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)) -->
        ((T"MREG" "IL" [] -->
          (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
         ((T"MREG" "IL" [] -->
           (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
          ((T"MREG" "IL" [] -->
            (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
           ((T"MREG" "IL" [] -->
             (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> alpha))) -->
            ((T"MREG" "IL" [] -->
              (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
             ((T"MREG" "IL" [] -->
               (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
              ((T"MREG" "IL" [] -->
                (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))) -->
               ((T"MREG" "IL" [] -->
                 (T"MREG" "IL" [] -->
                  (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha))) -->
                ((T"MREG" "IL" [] -->
                  (T"MREG" "IL" [] -->
                   (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha))) -->
                 ((T"MREG" "IL" [] -->
                   (T"MREG" "IL" [] -->
                    (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                  -->
                  ((T"MREG" "IL" [] -->
                    (T"MREG" "IL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                   -->
                   ((T"num" "num" [] -->
                     (T"list" "list" [T"num" "num" []] --> alpha)) -->
                    ((T"num" "num" [] -->
                      (T"list" "list" [T"num" "num" []] --> alpha)) -->
                     (T"DOPER" "IL" [] --> alpha)))))))))))))))))),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i5" "words" []] --> bool) --> bool)),
   C"!" "bool" (((T"list" "list" [T"num" "num" []] --> bool) --> bool)),
   C"DOPER_size" "IL" ((T"DOPER" "IL" [] --> T"num" "num" [])),
   C"UNCURRY" "pair"
    (((T"num" "num" [] --> (T"OFFSET" "preARM" [] --> T"num" "num" [])) -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"num" "num" []))), V"x" (T"num" "num" []),
   V"y" (T"OFFSET" "preARM" []),
   C"OFFSET_size" "preARM" ((T"OFFSET" "preARM" [] --> T"num" "num" [])),
   C"list_size" "list"
    (((T"num" "num" [] --> T"num" "num" []) -->
      (T"list" "list" [T"num" "num" []] --> T"num" "num" []))),
   C"?" "bool"
    ((((T"CTL_STRUCTURE" "IL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "IL" []],
            T"prod" "pair"
             [T"MREG" "IL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]) -->
       bool) --> bool)),
   V"rep"
    ((T"CTL_STRUCTURE" "IL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "IL" []],
          T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"DOPER" "IL" []],
           T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
       bool) -->
      ((T"CTL_STRUCTURE" "IL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "IL" []],
            T"prod" "pair"
             [T"MREG" "IL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]) -->
       bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "IL" []],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "IL" []],
            T"prod" "pair"
             [T"MREG" "IL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
        bool) --> bool) --> bool)),
   V"'CTL_STRUCTURE'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "IL" []],
          T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
      bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"DOPER" "IL" []],
           T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
       bool) --> bool)),
   C"?" "bool" (((T"list" "list" [T"DOPER" "IL" []] --> bool) --> bool)),
   V"a" (T"list" "list" [T"DOPER" "IL" []]),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "IL" []],
          T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"DOPER" "IL" []],
           T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
       bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"DOPER" "IL" []],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"DOPER" "IL" []],
             T"prod" "pair"
              [T"MREG" "IL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]])
        -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "IL" []],
            T"prod" "pair"
             [T"MREG" "IL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]])))),
   C"," "pair"
    ((T"list" "list" [T"DOPER" "IL" []] -->
      (T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
       T"prod" "pair"
        [T"list" "list" [T"DOPER" "IL" []],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]))),
   C"@" "min"
    (((T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] --> bool)
      -->
      T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]])),
   V"v"
    (T"prod" "pair"
      [T"MREG" "IL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "IL" []],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]),
   C"?" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"DOPER" "IL" []],
           T"prod" "pair"
            [T"MREG" "IL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
       bool) --> bool)),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "IL" []],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]),
   V"a1"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "IL" []],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]),
   C"@" "min"
    (((T"list" "list" [T"DOPER" "IL" []] --> bool) -->
      T"list" "list" [T"DOPER" "IL" []])),
   V"v" (T"list" "list" [T"DOPER" "IL" []]),
   C"FCONS" "ind_type"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "IL" []],
          T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
      ((T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "IL" []],
            T"prod" "pair"
             [T"MREG" "IL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]) -->
       (T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "IL" []],
            T"prod" "pair"
             [T"MREG" "IL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]])))),
   C"?" "bool"
    (((T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] --> bool)
      --> bool)),
   V"a0"
    (T"prod" "pair"
      [T"MREG" "IL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]),
   V"a2"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "IL" []],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]),
   C"!" "bool" (((T"CTL_STRUCTURE" "IL" [] --> bool) --> bool)),
   V"a" (T"CTL_STRUCTURE" "IL" []),
   C"=" "min"
    ((T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> bool))),
   C"mk_CTL_STRUCTURE" "IL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "IL" []],
          T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]] -->
      T"CTL_STRUCTURE" "IL" [])),
   C"dest_CTL_STRUCTURE" "IL"
    ((T"CTL_STRUCTURE" "IL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "IL" []],
          T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "IL" []],
         T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]]]),
   C"=" "min"
    (((T"list" "list" [T"DOPER" "IL" []] --> T"CTL_STRUCTURE" "IL" []) -->
      ((T"list" "list" [T"DOPER" "IL" []] --> T"CTL_STRUCTURE" "IL" []) -->
       bool))),
   C"IL18" "IL"
    ((T"list" "list" [T"DOPER" "IL" []] --> T"CTL_STRUCTURE" "IL" [])),
   C"=" "min"
    (((T"CTL_STRUCTURE" "IL" [] -->
       (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])) -->
      ((T"CTL_STRUCTURE" "IL" [] -->
        (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])) -->
       bool))),
   C"IL19" "IL"
    ((T"CTL_STRUCTURE" "IL" [] -->
      (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" []))),
   V"a0" (T"CTL_STRUCTURE" "IL" []), V"a1" (T"CTL_STRUCTURE" "IL" []),
   C"=" "min"
    (((T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
       (T"CTL_STRUCTURE" "IL" [] -->
        (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" []))) -->
      ((T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
        (T"CTL_STRUCTURE" "IL" [] -->
         (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" []))) -->
       bool))),
   C"IL20" "IL"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] -->
       (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])))),
   V"a2" (T"CTL_STRUCTURE" "IL" []),
   C"=" "min"
    (((T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
       (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])) -->
      ((T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
        (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])) -->
       bool))),
   C"IL21" "IL"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" []))),
   C"BLK" "IL"
    ((T"list" "list" [T"DOPER" "IL" []] --> T"CTL_STRUCTURE" "IL" [])),
   C"SC" "IL"
    ((T"CTL_STRUCTURE" "IL" [] -->
      (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" []))),
   C"CJ" "IL"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] -->
       (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])))),
   C"TR" "IL"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" []))),
   C"!" "bool"
    ((((T"list" "list" [T"DOPER" "IL" []] --> alpha) --> bool) --> bool)),
   V"f" ((T"list" "list" [T"DOPER" "IL" []] --> alpha)),
   C"!" "bool"
    ((((T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> alpha))
       --> bool) --> bool)),
   V"f1"
    ((T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> alpha))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
        (T"CTL_STRUCTURE" "IL" [] -->
         (T"CTL_STRUCTURE" "IL" [] --> alpha))) --> bool) --> bool)),
   V"f2"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] -->
       (T"CTL_STRUCTURE" "IL" [] --> alpha)))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
        (T"CTL_STRUCTURE" "IL" [] --> alpha)) --> bool) --> bool)),
   V"f3"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] --> alpha))),
   C"!" "bool" (((T"list" "list" [T"DOPER" "IL" []] --> bool) --> bool)),
   C"CTL_STRUCTURE_case" "IL"
    (((T"list" "list" [T"DOPER" "IL" []] --> alpha) -->
      ((T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> alpha))
       -->
       ((T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
         (T"CTL_STRUCTURE" "IL" [] -->
          (T"CTL_STRUCTURE" "IL" [] --> alpha))) -->
        ((T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
          (T"CTL_STRUCTURE" "IL" [] --> alpha)) -->
         (T"CTL_STRUCTURE" "IL" [] --> alpha)))))),
   C"!" "bool"
    (((T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] --> bool)
      --> bool)),
   C"CTL_STRUCTURE_size" "IL"
    ((T"CTL_STRUCTURE" "IL" [] --> T"num" "num" [])),
   C"list_size" "list"
    (((T"DOPER" "IL" [] --> T"num" "num" []) -->
      (T"list" "list" [T"DOPER" "IL" []] --> T"num" "num" []))),
   C"UNCURRY" "pair"
    (((T"MREG" "IL" [] -->
       (T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []] -->
        T"num" "num" [])) -->
      (T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
       T"num" "num" []))),
   V"y" (T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]),
   C"UNCURRY" "pair"
    (((T"COND" "preARM" [] --> (T"MEXP" "IL" [] --> T"num" "num" [])) -->
      (T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []] -->
       T"num" "num" []))), V"x" (T"COND" "preARM" []),
   V"y" (T"MEXP" "IL" []),
   C"COND_size" "preARM" ((T"COND" "preARM" [] --> T"num" "num" [])),
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
   V"baseR" (T"num" "num" []), V"regL" (T"list" "list" [T"num" "num" []]),
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
   C"pushL" "IL"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"num" "num" [] -->
       (T"list" "list" [T"num" "num" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
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
   C"FST" "pair"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
        T"num" "num" []] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"FOLDL" "list"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"num" "num" []] -->
       (T"EXP" "preARM" [] -->
        T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"num" "num" []])) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"num" "num" []] -->
       (T"list" "list" [T"EXP" "preARM" []] -->
        T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"num" "num" []])))),
   C"UNCURRY" "pair"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"num" "num" [] -->
        (T"EXP" "preARM" [] -->
         T"prod" "pair"
          [T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
           T"num" "num" []]))) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"num" "num" []] -->
       (T"EXP" "preARM" [] -->
        T"prod" "pair"
         [T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
          T"num" "num" []])))),
   V"st1"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"reg" (T"EXP" "preARM" []),
   C"," "pair"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"num" "num" [] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]],
         T"num" "num" []]))),
   C"NEG" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"read" "preARM"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"EXP" "preARM" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"REVERSE" "list"
    ((T"list" "list" [T"EXP" "preARM" []] -->
      T"list" "list" [T"EXP" "preARM" []])),
   C"MAP" "list"
    (((T"num" "num" [] --> T"EXP" "preARM" []) -->
      (T"list" "list" [T"num" "num" []] -->
       T"list" "list" [T"EXP" "preARM" []]))),
   C"word_sub" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"n2w" "words"
    ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []])),
   C"LENGTH" "list"
    ((T"list" "list" [T"num" "num" []] --> T"num" "num" [])),
   C"popL" "IL"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"num" "num" [] -->
       (T"list" "list" [T"num" "num" []] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"POS" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"word_add" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   V"dst" (T"MREG" "IL" []),
   V"src" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"mdecode" "IL"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"DOPER" "IL" [] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   V"dst" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"src" (T"MREG" "IL" []), V"src" (T"MEXP" "IL" []),
   V"src1" (T"MREG" "IL" []), V"src2" (T"MEXP" "IL" []),
   V"src2_reg" (T"MREG" "IL" []),
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
   V"dst'" (T"num" "num" []), V"srcL" (T"list" "list" [T"num" "num" []]),
   C"=" "min"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"OPERATOR" "preARM" [],
          T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]],
        T"prod" "pair"
         [T"option" "option" [T"EXP" "preARM" []],
          T"prod" "pair"
           [T"list" "list" [T"EXP" "preARM" []],
            T"option" "option" [T"OFFSET" "preARM" []]]]] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"OPERATOR" "preARM" [],
           T"prod" "pair"
            [T"option" "option" [T"COND" "preARM" []], bool]],
         T"prod" "pair"
          [T"option" "option" [T"EXP" "preARM" []],
           T"prod" "pair"
            [T"list" "list" [T"EXP" "preARM" []],
             T"option" "option" [T"OFFSET" "preARM" []]]]] --> bool))),
   C"translate_assignment" "IL"
    ((T"DOPER" "IL" [] -->
      T"prod" "pair"
       [T"prod" "pair"
         [T"OPERATOR" "preARM" [],
          T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]],
        T"prod" "pair"
         [T"option" "option" [T"EXP" "preARM" []],
          T"prod" "pair"
           [T"list" "list" [T"EXP" "preARM" []],
            T"option" "option" [T"OFFSET" "preARM" []]]]])),
   C"," "pair"
    ((T"prod" "pair"
       [T"OPERATOR" "preARM" [],
        T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]]
      -->
      (T"prod" "pair"
        [T"option" "option" [T"EXP" "preARM" []],
         T"prod" "pair"
          [T"list" "list" [T"EXP" "preARM" []],
           T"option" "option" [T"OFFSET" "preARM" []]]] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"OPERATOR" "preARM" [],
           T"prod" "pair"
            [T"option" "option" [T"COND" "preARM" []], bool]],
         T"prod" "pair"
          [T"option" "option" [T"EXP" "preARM" []],
           T"prod" "pair"
            [T"list" "list" [T"EXP" "preARM" []],
             T"option" "option" [T"OFFSET" "preARM" []]]]]))),
   C"," "pair"
    ((T"OPERATOR" "preARM" [] -->
      (T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool] -->
       T"prod" "pair"
        [T"OPERATOR" "preARM" [],
         T"prod" "pair"
          [T"option" "option" [T"COND" "preARM" []], bool]]))),
   C"MOV" "preARM" (T"OPERATOR" "preARM" []),
   C"," "pair"
    ((T"option" "option" [T"COND" "preARM" []] -->
      (bool -->
       T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]))),
   C"NONE" "option" (T"option" "option" [T"COND" "preARM" []]),
   C"F" "bool" (bool),
   C"," "pair"
    ((T"option" "option" [T"EXP" "preARM" []] -->
      (T"prod" "pair"
        [T"list" "list" [T"EXP" "preARM" []],
         T"option" "option" [T"OFFSET" "preARM" []]] -->
       T"prod" "pair"
        [T"option" "option" [T"EXP" "preARM" []],
         T"prod" "pair"
          [T"list" "list" [T"EXP" "preARM" []],
           T"option" "option" [T"OFFSET" "preARM" []]]]))),
   C"SOME" "option"
    ((T"EXP" "preARM" [] --> T"option" "option" [T"EXP" "preARM" []])),
   C"," "pair"
    ((T"list" "list" [T"EXP" "preARM" []] -->
      (T"option" "option" [T"OFFSET" "preARM" []] -->
       T"prod" "pair"
        [T"list" "list" [T"EXP" "preARM" []],
         T"option" "option" [T"OFFSET" "preARM" []]]))),
   C"CONS" "list"
    ((T"EXP" "preARM" [] -->
      (T"list" "list" [T"EXP" "preARM" []] -->
       T"list" "list" [T"EXP" "preARM" []]))),
   C"NIL" "list" (T"list" "list" [T"EXP" "preARM" []]),
   C"NONE" "option" (T"option" "option" [T"OFFSET" "preARM" []]),
   C"ADD" "preARM" (T"OPERATOR" "preARM" []),
   C"SUB" "preARM" (T"OPERATOR" "preARM" []),
   C"RSB" "preARM" (T"OPERATOR" "preARM" []),
   C"MUL" "preARM" (T"OPERATOR" "preARM" []),
   C"AND" "preARM" (T"OPERATOR" "preARM" []),
   C"ORR" "preARM" (T"OPERATOR" "preARM" []),
   C"EOR" "preARM" (T"OPERATOR" "preARM" []),
   C"LSL" "preARM" (T"OPERATOR" "preARM" []),
   C"w2w" "words"
    ((T"cart" "fcp" [bool, T"i5" "words" []] -->
      T"cart" "fcp" [bool, T"i32" "words" []])),
   C"LSR" "preARM" (T"OPERATOR" "preARM" []),
   C"ASR" "preARM" (T"OPERATOR" "preARM" []),
   C"ROR" "preARM" (T"OPERATOR" "preARM" []),
   C"LDR" "preARM" (T"OPERATOR" "preARM" []),
   C"STR" "preARM" (T"OPERATOR" "preARM" []), V"dst" (T"num" "num" []),
   C"STMFD" "preARM" (T"OPERATOR" "preARM" []),
   C"WREG" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   C"LDMFD" "preARM" (T"OPERATOR" "preARM" []), V"c" (alpha),
   V"e" (T"MEXP" "IL" []),
   C"=" "min"
    ((T"prod" "pair"
       [T"EXP" "preARM" [], T"prod" "pair" [alpha, T"EXP" "preARM" []]] -->
      (T"prod" "pair"
        [T"EXP" "preARM" [], T"prod" "pair" [alpha, T"EXP" "preARM" []]]
       --> bool))),
   C"translate_condition" "IL"
    ((T"prod" "pair"
       [T"MREG" "IL" [], T"prod" "pair" [alpha, T"MEXP" "IL" []]] -->
      T"prod" "pair"
       [T"EXP" "preARM" [], T"prod" "pair" [alpha, T"EXP" "preARM" []]])),
   C"," "pair"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair" [alpha, T"MEXP" "IL" []] -->
       T"prod" "pair"
        [T"MREG" "IL" [], T"prod" "pair" [alpha, T"MEXP" "IL" []]]))),
   C"," "pair"
    ((alpha -->
      (T"MEXP" "IL" [] --> T"prod" "pair" [alpha, T"MEXP" "IL" []]))),
   C"," "pair"
    ((T"EXP" "preARM" [] -->
      (T"prod" "pair" [alpha, T"EXP" "preARM" []] -->
       T"prod" "pair"
        [T"EXP" "preARM" [],
         T"prod" "pair" [alpha, T"EXP" "preARM" []]]))),
   C"," "pair"
    ((alpha -->
      (T"EXP" "preARM" [] -->
       T"prod" "pair" [alpha, T"EXP" "preARM" []]))),
   V"cond"
    (T"prod" "pair"
      [T"MREG" "IL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]),
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
   C"eval_il_cond" "IL"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   C"eval_cond" "ARMComposition"
    ((T"prod" "pair"
       [T"EXP" "preARM" [],
        T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   C"translate_condition" "IL"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      T"prod" "pair"
       [T"EXP" "preARM" [],
        T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]])),
   C"=" "min"
    (((T"CTL_STRUCTURE" "IL" [] -->
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
               T"option" "option" [T"OFFSET" "preARM" []]]]]]) -->
      ((T"CTL_STRUCTURE" "IL" [] -->
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
                T"option" "option" [T"OFFSET" "preARM" []]]]]]) -->
       bool))),
   C"translate" "IL"
    ((T"CTL_STRUCTURE" "IL" [] -->
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
   C"WFREC" "relation"
    (((T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> bool))
      -->
      (((T"CTL_STRUCTURE" "IL" [] -->
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
                 T"option" "option" [T"OFFSET" "preARM" []]]]]]) -->
        (T"CTL_STRUCTURE" "IL" [] -->
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
                 T"option" "option" [T"OFFSET" "preARM" []]]]]])) -->
       (T"CTL_STRUCTURE" "IL" [] -->
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
                T"option" "option" [T"OFFSET" "preARM" []]]]]])))),
   C"@" "min"
    ((((T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> bool))
       --> bool) -->
      (T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> bool)))),
   V"R"
    ((T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> bool))),
   C"WF" "relation"
    (((T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> bool))
      --> bool)), V"stm" (T"DOPER" "IL" []),
   V"stmL" (T"list" "list" [T"DOPER" "IL" []]),
   C"CONS" "list"
    ((T"DOPER" "IL" [] -->
      (T"list" "list" [T"DOPER" "IL" []] -->
       T"list" "list" [T"DOPER" "IL" []]))),
   V"S1" (T"CTL_STRUCTURE" "IL" []), V"S2" (T"CTL_STRUCTURE" "IL" []),
   V"Sfalse" (T"CTL_STRUCTURE" "IL" []),
   V"Strue" (T"CTL_STRUCTURE" "IL" []),
   V"Sbody" (T"CTL_STRUCTURE" "IL" []),
   V"translate"
    ((T"CTL_STRUCTURE" "IL" [] -->
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
   C"CTL_STRUCTURE_case" "IL"
    (((T"list" "list" [T"DOPER" "IL" []] -->
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
               T"option" "option" [T"OFFSET" "preARM" []]]]]]) -->
      ((T"CTL_STRUCTURE" "IL" [] -->
        (T"CTL_STRUCTURE" "IL" [] -->
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
                 T"option" "option" [T"OFFSET" "preARM" []]]]]])) -->
       ((T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
         (T"CTL_STRUCTURE" "IL" [] -->
          (T"CTL_STRUCTURE" "IL" [] -->
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
                   T"option" "option" [T"OFFSET" "preARM" []]]]]]))) -->
        ((T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
          (T"CTL_STRUCTURE" "IL" [] -->
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
                   T"option" "option" [T"OFFSET" "preARM" []]]]]])) -->
         (T"CTL_STRUCTURE" "IL" [] -->
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
                  T"option" "option" [T"OFFSET" "preARM" []]]]]])))))),
   C"list_case" "list"
    ((T"list" "list"
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
      ((T"DOPER" "IL" [] -->
        (T"list" "list" [T"DOPER" "IL" []] -->
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
                 T"option" "option" [T"OFFSET" "preARM" []]]]]])) -->
       (T"list" "list" [T"DOPER" "IL" []] -->
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
                T"option" "option" [T"OFFSET" "preARM" []]]]]])))),
   C"I" "combin"
    ((T"list" "list"
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
   C"NIL" "list"
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
             T"option" "option" [T"OFFSET" "preARM" []]]]]]),
   C"CONS" "list"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"OPERATOR" "preARM" [],
          T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]],
        T"prod" "pair"
         [T"option" "option" [T"EXP" "preARM" []],
          T"prod" "pair"
           [T"list" "list" [T"EXP" "preARM" []],
            T"option" "option" [T"OFFSET" "preARM" []]]]] -->
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
               T"option" "option" [T"OFFSET" "preARM" []]]]]]))),
   C"mk_SC" "ARMComposition"
    ((T"list" "list"
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
               T"option" "option" [T"OFFSET" "preARM" []]]]]]))),
   C"mk_CJ" "ARMComposition"
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
                T"option" "option" [T"OFFSET" "preARM" []]]]]])))),
   V"cond'"
    (T"prod" "pair"
      [T"MREG" "IL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]),
   C"mk_TR" "ARMComposition"
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
               T"option" "option" [T"OFFSET" "preARM" []]]]]]))),
   C"!" "bool"
    (((T"list" "list"
        [T"prod" "pair"
          [T"prod" "pair"
            [T"OPERATOR" "preARM" [],
             T"prod" "pair"
              [T"option" "option" [T"COND" "preARM" []], bool]],
           T"prod" "pair"
            [T"option" "option" [T"EXP" "preARM" []],
             T"prod" "pair"
              [T"list" "list" [T"EXP" "preARM" []],
               T"option" "option" [T"OFFSET" "preARM" []]]]]] --> bool) -->
      bool)),
   V"arm"
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
             T"option" "option" [T"OFFSET" "preARM" []]]]]]),
   V"pc" (T"num" "num" []),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"cpsr" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"!" "bool" ((((T"num" "num" [] --> bool) --> bool) --> bool)),
   V"pcS" ((T"num" "num" [] --> bool)),
   C"=" "min"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]],
        (T"num" "num" [] --> bool)] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]],
         (T"num" "num" [] --> bool)] --> bool))),
   C"run_arm" "IL"
    ((T"list" "list"
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
      (T"prod" "pair"
        [T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]],
         (T"num" "num" [] --> bool)] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]],
         (T"num" "num" [] --> bool)]))),
   C"," "pair"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
      -->
      ((T"num" "num" [] --> bool) -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]],
         (T"num" "num" [] --> bool)]))),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]]]))),
   C"," "pair"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
   C"runTo" "preARM"
    (((T"num" "num" [] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"OPERATOR" "preARM" [],
           T"prod" "pair"
            [T"option" "option" [T"COND" "preARM" []], bool]],
         T"prod" "pair"
          [T"option" "option" [T"EXP" "preARM" []],
           T"prod" "pair"
            [T"list" "list" [T"EXP" "preARM" []],
             T"option" "option" [T"OFFSET" "preARM" []]]]]) -->
      (T"num" "num" [] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []],
              T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]]],
          (T"num" "num" [] --> bool)] -->
        T"prod" "pair"
         [T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []],
              T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]]],
          (T"num" "num" [] --> bool)])))),
   C"upload" "preARM"
    ((T"list" "list"
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
      ((T"num" "num" [] -->
        T"prod" "pair"
         [T"prod" "pair"
           [T"OPERATOR" "preARM" [],
            T"prod" "pair"
             [T"option" "option" [T"COND" "preARM" []], bool]],
          T"prod" "pair"
           [T"option" "option" [T"EXP" "preARM" []],
            T"prod" "pair"
             [T"list" "list" [T"EXP" "preARM" []],
              T"option" "option" [T"OFFSET" "preARM" []]]]]) -->
       (T"num" "num" [] -->
        (T"num" "num" [] -->
         T"prod" "pair"
          [T"prod" "pair"
            [T"OPERATOR" "preARM" [],
             T"prod" "pair"
              [T"option" "option" [T"COND" "preARM" []], bool]],
           T"prod" "pair"
            [T"option" "option" [T"EXP" "preARM" []],
             T"prod" "pair"
              [T"list" "list" [T"EXP" "preARM" []],
               T"option" "option" [T"OFFSET" "preARM" []]]]]))))),
   C"ARB" "bool"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"OPERATOR" "preARM" [],
         T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]],
       T"prod" "pair"
        [T"option" "option" [T"EXP" "preARM" []],
         T"prod" "pair"
          [T"list" "list" [T"EXP" "preARM" []],
           T"option" "option" [T"OFFSET" "preARM" []]]]]),
   C"LENGTH" "list"
    ((T"list" "list"
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
      T"num" "num" [])), V"ir" (T"CTL_STRUCTURE" "IL" []),
   C"run_ir" "IL"
    ((T"CTL_STRUCTURE" "IL" [] -->
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
   C"get_st" "ARMComposition"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]],
        (T"num" "num" [] --> bool)] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"EMPTY" "pred_set" ((T"num" "num" [] --> bool)),
   C"WELL_FORMED" "IL" ((T"CTL_STRUCTURE" "IL" [] --> bool)),
   C"well_formed" "ARMComposition"
    ((T"list" "list"
       [T"prod" "pair"
         [T"prod" "pair"
           [T"OPERATOR" "preARM" [],
            T"prod" "pair"
             [T"option" "option" [T"COND" "preARM" []], bool]],
          T"prod" "pair"
           [T"option" "option" [T"EXP" "preARM" []],
            T"prod" "pair"
             [T"list" "list" [T"EXP" "preARM" []],
              T"option" "option" [T"OFFSET" "preARM" []]]]]] --> bool)),
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
   C"WELL_FORMED_SUB" "IL" ((T"CTL_STRUCTURE" "IL" [] --> bool)),
   V"r'" (T"num" "num" []), V"a'" (T"MREG" "IL" []),
   C"DATATYPE" "bool" ((bool --> bool)),
   V"MREG"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"MREG" "IL" [] -->
        (T"MREG" "IL" [] -->
         (T"MREG" "IL" [] -->
          (T"MREG" "IL" [] -->
           (T"MREG" "IL" [] -->
            (T"MREG" "IL" [] -->
             (T"MREG" "IL" [] -->
              (T"MREG" "IL" [] -->
               (T"MREG" "IL" [] -->
                (T"MREG" "IL" [] -->
                 (T"MREG" "IL" [] -->
                  (T"MREG" "IL" [] -->
                   (T"MREG" "IL" [] --> bool)))))))))))))))),
   C"~" "bool" ((bool --> bool)), V"M" (T"MREG" "IL" []),
   V"M'" (T"MREG" "IL" []), V"v0'" (alpha), V"v1'" (alpha), V"v2'" (alpha),
   V"v3'" (alpha), V"v4'" (alpha), V"v5'" (alpha), V"v6'" (alpha),
   V"v7'" (alpha), V"v8'" (alpha), V"v9'" (alpha), V"v10'" (alpha),
   V"v11'" (alpha), V"v12'" (alpha), V"v13'" (alpha), V"v14'" (alpha),
   V"x0" (alpha), V"x1" (alpha), V"x2" (alpha), V"x3" (alpha),
   V"x4" (alpha), V"x5" (alpha), V"x6" (alpha), V"x7" (alpha),
   V"x8" (alpha), V"x9" (alpha), V"x10" (alpha), V"x11" (alpha),
   V"x12" (alpha), V"x13" (alpha), V"x14" (alpha),
   C"?" "bool" ((((T"MREG" "IL" [] --> alpha) --> bool) --> bool)),
   C"!" "bool" ((((T"MREG" "IL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"MREG" "IL" [] --> bool)),
   V"MEXP"
    (((T"MREG" "IL" [] --> T"MEXP" "IL" []) -->
      ((T"cart" "fcp" [bool, T"i4" "words" []] -->
        (T"cart" "fcp" [bool, T"i8" "words" []] --> T"MEXP" "IL" [])) -->
       bool))), V"a0'" (T"cart" "fcp" [bool, T"i4" "words" []]),
   V"a1'" (T"cart" "fcp" [bool, T"i8" "words" []]),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i4" "words" []] -->
      (T"cart" "fcp" [bool, T"i4" "words" []] --> bool))),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i8" "words" []] -->
      (T"cart" "fcp" [bool, T"i8" "words" []] --> bool))),
   V"M" (T"MEXP" "IL" []), V"M'" (T"MEXP" "IL" []),
   V"f'" ((T"MREG" "IL" [] --> alpha)),
   V"f1'"
    ((T"cart" "fcp" [bool, T"i4" "words" []] -->
      (T"cart" "fcp" [bool, T"i8" "words" []] --> alpha))),
   V"c" (T"cart" "fcp" [bool, T"i4" "words" []]),
   V"c0" (T"cart" "fcp" [bool, T"i8" "words" []]),
   V"f0" ((T"MREG" "IL" [] --> alpha)),
   C"?" "bool" ((((T"MEXP" "IL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"MEXP" "IL" [] --> alpha)),
   C"!" "bool" ((((T"MEXP" "IL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"MEXP" "IL" [] --> bool)),
   V"DOPER"
    (((T"MREG" "IL" [] -->
       (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        T"DOPER" "IL" [])) -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        (T"MREG" "IL" [] --> T"DOPER" "IL" [])) -->
       ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])) -->
        ((T"MREG" "IL" [] -->
          (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" []))) -->
         ((T"MREG" "IL" [] -->
           (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))
          -->
          ((T"MREG" "IL" [] -->
            (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))
           -->
           ((T"MREG" "IL" [] -->
             (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> T"DOPER" "IL" [])))
            -->
            ((T"MREG" "IL" [] -->
              (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> T"DOPER" "IL" [])))
             -->
             ((T"MREG" "IL" [] -->
               (T"MREG" "IL" [] -->
                (T"MEXP" "IL" [] --> T"DOPER" "IL" []))) -->
              ((T"MREG" "IL" [] -->
                (T"MREG" "IL" [] -->
                 (T"MEXP" "IL" [] --> T"DOPER" "IL" []))) -->
               ((T"MREG" "IL" [] -->
                 (T"MREG" "IL" [] -->
                  (T"cart" "fcp" [bool, T"i5" "words" []] -->
                   T"DOPER" "IL" []))) -->
                ((T"MREG" "IL" [] -->
                  (T"MREG" "IL" [] -->
                   (T"cart" "fcp" [bool, T"i5" "words" []] -->
                    T"DOPER" "IL" []))) -->
                 ((T"MREG" "IL" [] -->
                   (T"MREG" "IL" [] -->
                    (T"cart" "fcp" [bool, T"i5" "words" []] -->
                     T"DOPER" "IL" []))) -->
                  ((T"MREG" "IL" [] -->
                    (T"MREG" "IL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] -->
                      T"DOPER" "IL" []))) -->
                   ((T"num" "num" [] -->
                     (T"list" "list" [T"num" "num" []] -->
                      T"DOPER" "IL" [])) -->
                    ((T"num" "num" [] -->
                      (T"list" "list" [T"num" "num" []] -->
                       T"DOPER" "IL" [])) --> bool))))))))))))))))),
   V"a0'" (T"MREG" "IL" []),
   V"a1'" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"=" "min"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool))),
   V"a0'" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"a1'" (T"MREG" "IL" []), V"a1'" (T"MEXP" "IL" []),
   V"a2'" (T"MEXP" "IL" []), V"a2'" (T"MREG" "IL" []),
   V"a2'" (T"cart" "fcp" [bool, T"i5" "words" []]),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i5" "words" []] -->
      (T"cart" "fcp" [bool, T"i5" "words" []] --> bool))),
   V"a0'" (T"num" "num" []), V"a1'" (T"list" "list" [T"num" "num" []]),
   C"=" "min"
    ((T"list" "list" [T"num" "num" []] -->
      (T"list" "list" [T"num" "num" []] --> bool))),
   V"M" (T"DOPER" "IL" []), V"M'" (T"DOPER" "IL" []),
   V"f'"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       alpha))),
   V"f1'"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "IL" [] --> alpha))),
   V"f2'" ((T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha))),
   V"f3'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f4'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f5'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f6'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MREG" "IL" [] --> alpha)))),
   V"f7'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f8'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f9'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] --> (T"MEXP" "IL" [] --> alpha)))),
   V"f10'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f11'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f12'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f13'"
    ((T"MREG" "IL" [] -->
      (T"MREG" "IL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f14'"
    ((T"num" "num" [] --> (T"list" "list" [T"num" "num" []] --> alpha))),
   V"f15'"
    ((T"num" "num" [] --> (T"list" "list" [T"num" "num" []] --> alpha))),
   V"D" (T"DOPER" "IL" []),
   V"p" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"M0" (T"MEXP" "IL" []), V"M0" (T"MREG" "IL" []),
   V"M1" (T"MEXP" "IL" []), V"M1" (T"MREG" "IL" []),
   V"c" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"l" (T"list" "list" [T"num" "num" []]),
   V"f0"
    ((T"MREG" "IL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       alpha))),
   C"?" "bool" ((((T"DOPER" "IL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"DOPER" "IL" [] --> alpha)),
   C"!" "bool" ((((T"DOPER" "IL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"DOPER" "IL" [] --> bool)),
   V"CTL_STRUCTURE"
    (((T"list" "list" [T"DOPER" "IL" []] --> T"CTL_STRUCTURE" "IL" []) -->
      ((T"CTL_STRUCTURE" "IL" [] -->
        (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])) -->
       ((T"prod" "pair"
          [T"MREG" "IL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
         (T"CTL_STRUCTURE" "IL" [] -->
          (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" []))) -->
        ((T"prod" "pair"
           [T"MREG" "IL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
          (T"CTL_STRUCTURE" "IL" [] --> T"CTL_STRUCTURE" "IL" [])) -->
         bool))))), V"a'" (T"list" "list" [T"DOPER" "IL" []]),
   C"=" "min"
    ((T"list" "list" [T"DOPER" "IL" []] -->
      (T"list" "list" [T"DOPER" "IL" []] --> bool))),
   V"a0'" (T"CTL_STRUCTURE" "IL" []), V"a1'" (T"CTL_STRUCTURE" "IL" []),
   V"a0'"
    (T"prod" "pair"
      [T"MREG" "IL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]),
   V"a2'" (T"CTL_STRUCTURE" "IL" []),
   C"=" "min"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"prod" "pair"
        [T"MREG" "IL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
       bool))), V"M" (T"CTL_STRUCTURE" "IL" []),
   V"M'" (T"CTL_STRUCTURE" "IL" []),
   V"f'" ((T"list" "list" [T"DOPER" "IL" []] --> alpha)),
   V"f1'"
    ((T"CTL_STRUCTURE" "IL" [] --> (T"CTL_STRUCTURE" "IL" [] --> alpha))),
   V"f2'"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] -->
       (T"CTL_STRUCTURE" "IL" [] --> alpha)))),
   V"f3'"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] --> alpha))),
   V"C" (T"CTL_STRUCTURE" "IL" []),
   V"l" (T"list" "list" [T"DOPER" "IL" []]),
   C"?" "bool" (((T"CTL_STRUCTURE" "IL" [] --> bool) --> bool)),
   V"C0" (T"CTL_STRUCTURE" "IL" []),
   V"p"
    (T"prod" "pair"
      [T"MREG" "IL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]]),
   V"f0" ((T"list" "list" [T"DOPER" "IL" []] --> alpha)),
   C"!" "bool"
    ((((T"CTL_STRUCTURE" "IL" [] -->
        (T"CTL_STRUCTURE" "IL" [] --> (alpha --> (alpha --> alpha)))) -->
       bool) --> bool)),
   V"f1"
    ((T"CTL_STRUCTURE" "IL" [] -->
      (T"CTL_STRUCTURE" "IL" [] --> (alpha --> (alpha --> alpha))))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
        (T"CTL_STRUCTURE" "IL" [] -->
         (T"CTL_STRUCTURE" "IL" [] --> (alpha --> (alpha --> alpha))))) -->
       bool) --> bool)),
   V"f2"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] -->
       (T"CTL_STRUCTURE" "IL" [] --> (alpha --> (alpha --> alpha)))))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"MREG" "IL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
        (T"CTL_STRUCTURE" "IL" [] --> (alpha --> alpha))) --> bool) -->
      bool)),
   V"f3"
    ((T"prod" "pair"
       [T"MREG" "IL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]] -->
      (T"CTL_STRUCTURE" "IL" [] --> (alpha --> alpha)))),
   C"?" "bool"
    ((((T"CTL_STRUCTURE" "IL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"CTL_STRUCTURE" "IL" [] --> alpha)),
   C"!" "bool" ((((T"CTL_STRUCTURE" "IL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"CTL_STRUCTURE" "IL" [] --> bool)),
   C"=" "min"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
      -->
      (T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
       --> bool))),
   C"decode_cond" "preARM"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
      -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"OPERATOR" "preARM" [],
           T"prod" "pair"
            [T"option" "option" [T"COND" "preARM" []], bool]],
         T"prod" "pair"
          [T"option" "option" [T"EXP" "preARM" []],
           T"prod" "pair"
            [T"list" "list" [T"EXP" "preARM" []],
             T"option" "option" [T"OFFSET" "preARM" []]]]] -->
       T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]]]))),
   C"!" "bool"
    (((T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
       --> bool) --> bool)),
   V"s"
    (T"prod" "pair"
      [T"num" "num" [],
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]),
   C"FST" "pair"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
      --> T"num" "num" [])),
   C"FST" "pair"
    ((T"prod" "pair"
       [T"cart" "fcp" [bool, T"i32" "words" []],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      T"cart" "fcp" [bool, T"i32" "words" []])),
   C"SND" "pair"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
      -->
      T"prod" "pair"
       [T"cart" "fcp" [bool, T"i32" "words" []],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])),
   C"SND" "pair"
    ((T"prod" "pair"
       [T"cart" "fcp" [bool, T"i32" "words" []],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"NIL" "list" (T"list" "list" [T"DOPER" "IL" []]),
   V"v" (T"CTL_STRUCTURE" "IL" []),
   C"=" "min"
    ((T"list" "list"
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
               T"option" "option" [T"OFFSET" "preARM" []]]]]] --> bool))),
   V"ir1" (T"CTL_STRUCTURE" "IL" []), V"ir2" (T"CTL_STRUCTURE" "IL" []),
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
   V"Q"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   V"R"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)),
   V"T"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)), V"ir_t" (T"CTL_STRUCTURE" "IL" []),
   V"ir_f" (T"CTL_STRUCTURE" "IL" []),
   C"COND" "bool" ((bool --> (bool --> (bool --> bool)))),
   C"!" "bool"
    (((T"prod" "pair" [T"num" "num" [], alpha] --> bool) --> bool)),
   V"s" (T"prod" "pair" [T"num" "num" [], alpha]),
   C"!" "bool" (((beta --> bool) --> bool)), V"stm" (beta),
   C"!" "bool" ((((T"num" "num" [] --> beta) --> bool) --> bool)),
   V"iB" ((T"num" "num" [] --> beta)),
   C"=" "min" ((beta --> (beta --> bool))),
   C"upload" "preARM"
    ((T"list" "list" [beta] -->
      ((T"num" "num" [] --> beta) -->
       (T"num" "num" [] --> (T"num" "num" [] --> beta))))),
   C"CONS" "list"
    ((beta --> (T"list" "list" [beta] --> T"list" "list" [beta]))),
   C"NIL" "list" (T"list" "list" [beta]),
   C"FST" "pair"
    ((T"prod" "pair" [T"num" "num" [], alpha] --> T"num" "num" [])),
   C"COND" "bool"
    ((bool -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"WHILE" "while"
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
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   V"st'"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])]
  val DT = Thm.disk_thm share_table
  in
  val MREG_TY_DEF =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (\%3. ((%4 $0) (%5 (%6 (%6 (%6 (%6 %7))))))))
       $0)))`)
  val MREG_BIJ =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%10. ((%11 (%12 (%13 $0))) $0)))) (%14 (\%15. ((%16
       ((\%3. ((%4 $0) (%5 (%6 (%6 (%6 (%6 %7))))))) $0)) ((%17 (%13 (%12
       $0))) $0)))))`)
  val R0 = DT([], [], `((%11 %18) (%12 %19))`)
  val R1 = DT([], [], `((%11 %20) (%12 (%5 (%6 %7))))`)
  val R2 = DT([], [], `((%11 %21) (%12 (%5 (%22 %7))))`)
  val R3 = DT([], [], `((%11 %23) (%12 (%5 (%6 (%6 %7)))))`)
  val R4 = DT([], [], `((%11 %24) (%12 (%5 (%22 (%6 %7)))))`)
  val R5 = DT([], [], `((%11 %25) (%12 (%5 (%6 (%22 %7)))))`)
  val R6 = DT([], [], `((%11 %26) (%12 (%5 (%22 (%22 %7)))))`)
  val R7 = DT([], [], `((%11 %27) (%12 (%5 (%6 (%6 (%6 %7))))))`)
  val R8 = DT([], [], `((%11 %28) (%12 (%5 (%22 (%6 (%6 %7))))))`)
  val R9 = DT([], [], `((%11 %29) (%12 (%5 (%6 (%22 (%6 %7))))))`)
  val R10 = DT([], [], `((%11 %30) (%12 (%5 (%22 (%22 (%6 %7))))))`)
  val R11 = DT([], [], `((%11 %31) (%12 (%5 (%6 (%6 (%22 %7))))))`)
  val R12 = DT([], [], `((%11 %32) (%12 (%5 (%22 (%6 (%22 %7))))))`)
  val R13 = DT([], [], `((%11 %33) (%12 (%5 (%6 (%22 (%22 %7))))))`)
  val R14 = DT([], [], `((%11 %34) (%12 (%5 (%22 (%22 (%22 %7))))))`)
  val MREG_size_def = DT([], [], `(%9 (\%35. ((%17 (%36 $0)) %19)))`)
  val MREG_case =
    DT([], [],
       `(%37 (\%38. (%37 (\%39. (%37 (\%40. (%37 (\%41. (%37 (\%42. (%37
       (\%43. (%37 (\%44. (%37 (\%45. (%37 (\%46. (%37 (\%47. (%37 (\%48.
       (%37 (\%49. (%37 (\%50. (%37 (\%51. (%37 (\%52. (%9 (\%35. ((%53
       ((((((((((((((((%54 $15) $14) $13) $12) $11) $10) $9) $8) $7) $6)
       $5) $4) $3) $2) $1) $0)) ((\%55. (((%56 ((%4 $0) (%5 (%6 (%6 (%6
       %7)))))) (((%56 ((%4 $0) (%5 (%6 (%6 %7))))) (((%56 ((%4 $0) (%5 (%6
       %7)))) $16) (((%56 ((%17 $0) (%5 (%6 %7)))) $15) $14))) (((%56 ((%4
       $0) (%5 (%22 (%6 %7))))) $13) (((%56 ((%4 $0) (%5 (%6 (%22 %7)))))
       $12) (((%56 ((%17 $0) (%5 (%6 (%22 %7))))) $11) $10))))) (((%56 ((%4
       $0) (%5 (%22 (%22 (%6 %7)))))) (((%56 ((%4 $0) (%5 (%22 (%6 (%6
       %7)))))) $9) (((%56 ((%17 $0) (%5 (%22 (%6 (%6 %7)))))) $8) $7)))
       (((%56 ((%4 $0) (%5 (%22 (%6 (%22 %7)))))) (((%56 ((%17 $0) (%5 (%22
       (%22 (%6 %7)))))) $6) $5)) (((%56 ((%4 $0) (%5 (%6 (%22 (%22
       %7)))))) $4) (((%56 ((%17 $0) (%5 (%6 (%22 (%22 %7)))))) $3)
       $2)))))) (%13 $0)))))))))))))))))))))))))))))))))))`)
  val MEXP_TY_DEF =
    DT(["DISK_THM"], [],
       `(%57 (\%58. ((%59 (\%60. (%61 (\%62. ((%63 (%64 (\%60. ((%63 ((%65
       (%66 (\%10. ((%67 $1) ((\%10. (((%68 %19) ((%69 $0) ((%70 (%71
       (\%72. %73))) (%74 (\%75. %73))))) (\%3. %76))) $0))))) (%77 (\%78.
       (%79 (\%80. ((%67 $2) (((\%78. (\%80. (((%68 (%81 %19)) ((%69 (%82
       (\%83. %73))) ((%70 $1) $0))) (\%3. %76)))) $1) $0)))))))) ($1
       $0))))) ($0 $1)))))) $0)))`)
  val MEXP_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%84 (\%85. ((%86 (%87 (%88 $0))) $0)))) (%64 (\%89. ((%16
       ((\%60. (%61 (\%62. ((%63 (%64 (\%60. ((%63 ((%65 (%66 (\%10. ((%67
       $1) ((\%10. (((%68 %19) ((%69 $0) ((%70 (%71 (\%72. %73))) (%74
       (\%75. %73))))) (\%3. %76))) $0))))) (%77 (\%78. (%79 (\%80. ((%67
       $2) (((\%78. (\%80. (((%68 (%81 %19)) ((%69 (%82 (\%83. %73))) ((%70
       $1) $0))) (\%3. %76)))) $1) $0)))))))) ($1 $0))))) ($0 $1))))) $0))
       ((%67 (%88 (%87 $0))) $0)))))`)
  val IL0_def =
    DT([], [],
       `((%90 %91) (\%10. (%87 ((\%10. (((%68 %19) ((%69 $0) ((%70 (%71
       (\%72. %73))) (%74 (\%75. %73))))) (\%3. %76))) $0))))`)
  val IL1_def =
    DT([], [],
       `((%92 %93) (\%78. (\%80. (%87 (((\%78. (\%80. (((%68 (%81 %19))
       ((%69 (%82 (\%83. %73))) ((%70 $1) $0))) (\%3. %76)))) $1) $0)))))`)
  val MR = DT([], [], `((%90 %94) %91)`)
  val MC = DT([], [], `((%92 %95) %93)`)
  val MEXP_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%96 (\%97. (%98 (\%99. (%9 (\%10. ((%53 (((%100 $2) $1) (%94
       $0))) ($2 $0))))))))) (%96 (\%97. (%98 (\%99. (%101 (\%78. (%102
       (\%80. ((%53 (((%100 $3) $2) ((%95 $1) $0))) (($2 $1)
       $0)))))))))))`)
  val MEXP_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%10. ((%17 (%103 (%94 $0))) ((%104 (%5 (%6 %7))) (%36
       $0)))))) (%101 (\%78. (%102 (\%80. ((%17 (%103 ((%95 $1) $0))) (%5
       (%6 %7))))))))`)
  val index_of_reg_def =
    DT(["DISK_THM"], [],
       `((%8 ((%17 (%105 %18)) %19)) ((%8 ((%17 (%105 %20)) (%5 (%6 %7))))
       ((%8 ((%17 (%105 %21)) (%5 (%22 %7)))) ((%8 ((%17 (%105 %23)) (%5
       (%6 (%6 %7))))) ((%8 ((%17 (%105 %24)) (%5 (%22 (%6 %7))))) ((%8
       ((%17 (%105 %25)) (%5 (%6 (%22 %7))))) ((%8 ((%17 (%105 %26)) (%5
       (%22 (%22 %7))))) ((%8 ((%17 (%105 %27)) (%5 (%6 (%6 (%6 %7))))))
       ((%8 ((%17 (%105 %28)) (%5 (%22 (%6 (%6 %7)))))) ((%8 ((%17 (%105
       %29)) (%5 (%6 (%22 (%6 %7)))))) ((%8 ((%17 (%105 %30)) (%5 (%22 (%22
       (%6 %7)))))) ((%8 ((%17 (%105 %31)) (%5 (%6 (%6 (%22 %7)))))) ((%8
       ((%17 (%105 %32)) (%5 (%22 (%6 (%22 %7)))))) ((%8 ((%17 (%105 %33))
       (%5 (%6 (%22 (%22 %7)))))) ((%17 (%105 %34)) (%5 (%22 (%22 (%22
       %7)))))))))))))))))))`)
  val from_reg_index_def =
    DT([], [],
       `(%14 (\%106. ((%11 (%107 $0)) (((%108 ((%17 $0) %19)) %18) (((%108
       ((%17 $0) (%5 (%6 %7)))) %20) (((%108 ((%17 $0) (%5 (%22 %7)))) %21)
       (((%108 ((%17 $0) (%5 (%6 (%6 %7))))) %23) (((%108 ((%17 $0) (%5
       (%22 (%6 %7))))) %24) (((%108 ((%17 $0) (%5 (%6 (%22 %7))))) %25)
       (((%108 ((%17 $0) (%5 (%22 (%22 %7))))) %26) (((%108 ((%17 $0) (%5
       (%6 (%6 (%6 %7)))))) %27) (((%108 ((%17 $0) (%5 (%22 (%6 (%6
       %7)))))) %28) (((%108 ((%17 $0) (%5 (%6 (%22 (%6 %7)))))) %29)
       (((%108 ((%17 $0) (%5 (%22 (%22 (%6 %7)))))) %30) (((%108 ((%17 $0)
       (%5 (%6 (%6 (%22 %7)))))) %31) (((%108 ((%17 $0) (%5 (%22 (%6 (%22
       %7)))))) %32) (((%108 ((%17 $0) (%5 (%6 (%22 (%22 %7)))))) %33)
       %34)))))))))))))))))`)
  val toREG_def =
    DT([], [], `(%9 (\%109. ((%110 (%111 $0)) (%112 (%105 $0)))))`)
  val toMEM_def =
    DT(["DISK_THM"], [],
       `(%14 (\%113. (%114 (\%115. ((%110 (%116 ((%117 $1) $0))) (%118
       ((%117 $1) $0)))))))`)
  val toEXP_def =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%109. ((%110 (%119 (%94 $0))) (%111 $0))))) (%101
       (\%120. (%102 (\%121. ((%110 (%119 ((%95 $1) $0))) (%122 ((%123
       (%124 $0)) ((%125 (%5 (%22 %7))) (%126 $1))))))))))`)
  val DOPER_TY_DEF =
    DT(["DISK_THM"], [],
       `(%127 (\%128. ((%129 (\%130. (%131 (\%132. ((%63 (%133 (\%130.
       ((%63 ((%65 (%66 (\%134. (%135 (\%136. ((%137 $2) (((\%134. (\%136.
       (((%138 %19) ((%139 $1) ((%140 $0) ((%141 (%142 (\%143. %73)))
       ((%144 (%82 (\%83. %73))) ((%145 (%82 (\%83. %73))) ((%146 (%147
       (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152 (\%153.
       %73)))))))))) (\%3. %154)))) $1) $0))))))) ((%65 (%135 (\%155. (%66
       (\%156. ((%137 $2) (((\%155. (\%156. (((%138 (%81 %19)) ((%139 $0)
       ((%140 $1) ((%141 (%142 (\%143. %73))) ((%144 (%82 (\%83. %73)))
       ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149 (%150
       (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3. %154)))) $1)
       $0))))))) ((%65 (%66 (\%134. (%157 (\%158. ((%137 $2) (((\%134.
       (\%158. (((%138 (%81 (%81 %19))) ((%139 $1) ((%140 (%159 (\%160.
       %73))) ((%141 $0) ((%144 (%82 (\%83. %73))) ((%145 (%82 (\%83.
       %73))) ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154)))) $1) $0))))))) ((%65 (%66
       (\%134. (%66 (\%156. (%157 (\%161. ((%137 $3) ((((\%134. (\%156.
       (\%161. (((%138 (%81 (%81 (%81 %19)))) ((%139 $2) ((%140 (%159
       (\%160. %73))) ((%141 $0) ((%144 $1) ((%145 (%82 (\%83. %73)))
       ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0))))))))) ((%65 (%66
       (\%134. (%66 (\%156. (%157 (\%161. ((%137 $3) ((((\%134. (\%156.
       (\%161. (((%138 (%81 (%81 (%81 (%81 %19))))) ((%139 $2) ((%140 (%159
       (\%160. %73))) ((%141 $0) ((%144 $1) ((%145 (%82 (\%83. %73)))
       ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0))))))))) ((%65 (%66
       (\%134. (%66 (\%156. (%157 (\%161. ((%137 $3) ((((\%134. (\%156.
       (\%161. (((%138 (%81 (%81 (%81 (%81 (%81 %19)))))) ((%139 $2) ((%140
       (%159 (\%160. %73))) ((%141 $0) ((%144 $1) ((%145 (%82 (\%83. %73)))
       ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0))))))))) ((%65 (%66
       (\%134. (%66 (\%156. (%66 (\%162. ((%137 $3) ((((\%134. (\%156.
       (\%162. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 %19))))))) ((%139 $2)
       ((%140 (%159 (\%160. %73))) ((%141 (%142 (\%143. %73))) ((%144 $1)
       ((%145 $0) ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73)))
       (%152 (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0)))))))))
       ((%65 (%66 (\%134. (%66 (\%156. (%157 (\%161. ((%137 $3) ((((\%134.
       (\%156. (\%161. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       %19)))))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 $0) ((%144
       $1) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149
       (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3. %154))))) $2)
       $1) $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%157 (\%161. ((%137
       $3) ((((\%134. (\%156. (\%161. (((%138 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 (%81 %19))))))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141
       $0) ((%144 $1) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73)))
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154))))) $2) $1) $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%157
       (\%161. ((%137 $3) ((((\%134. (\%156. (\%161. (((%138 (%81 (%81 (%81
       (%81 (%81 (%81 (%81 (%81 (%81 %19)))))))))) ((%139 $2) ((%140 (%159
       (\%160. %73))) ((%141 $0) ((%144 $1) ((%145 (%82 (\%83. %73)))
       ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0))))))))) ((%65 (%66
       (\%134. (%66 (\%156. (%163 (\%164. ((%137 $3) ((((\%134. (\%156.
       (\%164. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       %19))))))))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 (%142
       (\%143. %73))) ((%144 $1) ((%145 (%82 (\%83. %73))) ((%146 $0)
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154))))) $2) $1) $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%163
       (\%164. ((%137 $3) ((((\%134. (\%156. (\%164. (((%138 (%81 (%81 (%81
       (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 %19)))))))))))) ((%139 $2)
       ((%140 (%159 (\%160. %73))) ((%141 (%142 (\%143. %73))) ((%144 $1)
       ((%145 (%82 (\%83. %73))) ((%146 $0) ((%149 (%150 (\%151. %73)))
       (%152 (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0)))))))))
       ((%65 (%66 (\%134. (%66 (\%156. (%163 (\%164. ((%137 $3) ((((\%134.
       (\%156. (\%164. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 (%81 (%81 %19))))))))))))) ((%139 $2) ((%140 (%159 (\%160.
       %73))) ((%141 (%142 (\%143. %73))) ((%144 $1) ((%145 (%82 (\%83.
       %73))) ((%146 $0) ((%149 (%150 (\%151. %73))) (%152 (\%153.
       %73)))))))))) (\%3. %154))))) $2) $1) $0))))))))) ((%65 (%66 (\%134.
       (%66 (\%156. (%163 (\%164. ((%137 $3) ((((\%134. (\%156. (\%164.
       (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 %19)))))))))))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141
       (%142 (\%143. %73))) ((%144 $1) ((%145 (%82 (\%83. %73))) ((%146 $0)
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154))))) $2) $1) $0))))))))) ((%65 (%165 (\%166. (%167 (\%168.
       ((%137 $2) (((\%166. (\%168. (((%138 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 %19))))))))))))))) ((%139
       (%82 (\%83. %73))) ((%140 (%159 (\%160. %73))) ((%141 (%142 (\%143.
       %73))) ((%144 (%82 (\%83. %73))) ((%145 (%82 (\%83. %73))) ((%146
       (%147 (\%148. %73))) ((%149 $1) $0)))))))) (\%3. %154)))) $1)
       $0))))))) (%165 (\%166. (%167 (\%168. ((%137 $2) (((\%166. (\%168.
       (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 (%81 (%81 %19)))))))))))))))) ((%139 (%82 (\%83. %73))) ((%140
       (%159 (\%160. %73))) ((%141 (%142 (\%143. %73))) ((%144 (%82 (\%83.
       %73))) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149
       $1) $0)))))))) (\%3. %154)))) $1) $0)))))))))))))))))))))) ($1
       $0))))) ($0 $1)))))) $0)))`)
  val DOPER_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%169 (\%170. ((%171 (%172 (%173 $0))) $0)))) (%133 (\%174.
       ((%16 ((\%130. (%131 (\%132. ((%63 (%133 (\%130. ((%63 ((%65 (%66
       (\%134. (%135 (\%136. ((%137 $2) (((\%134. (\%136. (((%138 %19)
       ((%139 $1) ((%140 $0) ((%141 (%142 (\%143. %73))) ((%144 (%82 (\%83.
       %73))) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149
       (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3. %154)))) $1)
       $0))))))) ((%65 (%135 (\%155. (%66 (\%156. ((%137 $2) (((\%155.
       (\%156. (((%138 (%81 %19)) ((%139 $0) ((%140 $1) ((%141 (%142
       (\%143. %73))) ((%144 (%82 (\%83. %73))) ((%145 (%82 (\%83. %73)))
       ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154)))) $1) $0))))))) ((%65 (%66
       (\%134. (%157 (\%158. ((%137 $2) (((\%134. (\%158. (((%138 (%81 (%81
       %19))) ((%139 $1) ((%140 (%159 (\%160. %73))) ((%141 $0) ((%144 (%82
       (\%83. %73))) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73)))
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154)))) $1) $0))))))) ((%65 (%66 (\%134. (%66 (\%156. (%157 (\%161.
       ((%137 $3) ((((\%134. (\%156. (\%161. (((%138 (%81 (%81 (%81 %19))))
       ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 $0) ((%144 $1) ((%145
       (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151.
       %73))) (%152 (\%153. %73)))))))))) (\%3. %154))))) $2) $1)
       $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%157 (\%161. ((%137 $3)
       ((((\%134. (\%156. (\%161. (((%138 (%81 (%81 (%81 (%81 %19)))))
       ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 $0) ((%144 $1) ((%145
       (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151.
       %73))) (%152 (\%153. %73)))))))))) (\%3. %154))))) $2) $1)
       $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%157 (\%161. ((%137 $3)
       ((((\%134. (\%156. (\%161. (((%138 (%81 (%81 (%81 (%81 (%81
       %19)))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 $0) ((%144
       $1) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149
       (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3. %154))))) $2)
       $1) $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%66 (\%162. ((%137
       $3) ((((\%134. (\%156. (\%162. (((%138 (%81 (%81 (%81 (%81 (%81 (%81
       %19))))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 (%142
       (\%143. %73))) ((%144 $1) ((%145 $0) ((%146 (%147 (\%148. %73)))
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154))))) $2) $1) $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%157
       (\%161. ((%137 $3) ((((\%134. (\%156. (\%161. (((%138 (%81 (%81 (%81
       (%81 (%81 (%81 (%81 %19)))))))) ((%139 $2) ((%140 (%159 (\%160.
       %73))) ((%141 $0) ((%144 $1) ((%145 (%82 (\%83. %73))) ((%146 (%147
       (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152 (\%153.
       %73)))))))))) (\%3. %154))))) $2) $1) $0))))))))) ((%65 (%66 (\%134.
       (%66 (\%156. (%157 (\%161. ((%137 $3) ((((\%134. (\%156. (\%161.
       (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 %19))))))))) ((%139
       $2) ((%140 (%159 (\%160. %73))) ((%141 $0) ((%144 $1) ((%145 (%82
       (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151.
       %73))) (%152 (\%153. %73)))))))))) (\%3. %154))))) $2) $1)
       $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%157 (\%161. ((%137 $3)
       ((((\%134. (\%156. (\%161. (((%138 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 (%81 (%81 %19)))))))))) ((%139 $2) ((%140 (%159 (\%160. %73)))
       ((%141 $0) ((%144 $1) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148.
       %73))) ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154))))) $2) $1) $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%163
       (\%164. ((%137 $3) ((((\%134. (\%156. (\%164. (((%138 (%81 (%81 (%81
       (%81 (%81 (%81 (%81 (%81 (%81 (%81 %19))))))))))) ((%139 $2) ((%140
       (%159 (\%160. %73))) ((%141 (%142 (\%143. %73))) ((%144 $1) ((%145
       (%82 (\%83. %73))) ((%146 $0) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0))))))))) ((%65 (%66
       (\%134. (%66 (\%156. (%163 (\%164. ((%137 $3) ((((\%134. (\%156.
       (\%164. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 %19)))))))))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141
       (%142 (\%143. %73))) ((%144 $1) ((%145 (%82 (\%83. %73))) ((%146 $0)
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154))))) $2) $1) $0))))))))) ((%65 (%66 (\%134. (%66 (\%156. (%163
       (\%164. ((%137 $3) ((((\%134. (\%156. (\%164. (((%138 (%81 (%81 (%81
       (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 %19))))))))))))) ((%139
       $2) ((%140 (%159 (\%160. %73))) ((%141 (%142 (\%143. %73))) ((%144
       $1) ((%145 (%82 (\%83. %73))) ((%146 $0) ((%149 (%150 (\%151. %73)))
       (%152 (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0)))))))))
       ((%65 (%66 (\%134. (%66 (\%156. (%163 (\%164. ((%137 $3) ((((\%134.
       (\%156. (\%164. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 (%81 (%81 (%81 %19)))))))))))))) ((%139 $2) ((%140 (%159
       (\%160. %73))) ((%141 (%142 (\%143. %73))) ((%144 $1) ((%145 (%82
       (\%83. %73))) ((%146 $0) ((%149 (%150 (\%151. %73))) (%152 (\%153.
       %73)))))))))) (\%3. %154))))) $2) $1) $0))))))))) ((%65 (%165
       (\%166. (%167 (\%168. ((%137 $2) (((\%166. (\%168. (((%138 (%81 (%81
       (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       %19))))))))))))))) ((%139 (%82 (\%83. %73))) ((%140 (%159 (\%160.
       %73))) ((%141 (%142 (\%143. %73))) ((%144 (%82 (\%83. %73))) ((%145
       (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149 $1) $0))))))))
       (\%3. %154)))) $1) $0))))))) (%165 (\%166. (%167 (\%168. ((%137 $2)
       (((\%166. (\%168. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 (%81 (%81 (%81 (%81 (%81 (%81 %19)))))))))))))))) ((%139 (%82
       (\%83. %73))) ((%140 (%159 (\%160. %73))) ((%141 (%142 (\%143.
       %73))) ((%144 (%82 (\%83. %73))) ((%145 (%82 (\%83. %73))) ((%146
       (%147 (\%148. %73))) ((%149 $1) $0)))))))) (\%3. %154)))) $1)
       $0)))))))))))))))))))))) ($1 $0))))) ($0 $1))))) $0)) ((%137 (%173
       (%172 $0))) $0)))))`)
  val IL2_def =
    DT([], [],
       `((%175 %176) (\%134. (\%136. (%172 (((\%134. (\%136. (((%138 %19)
       ((%139 $1) ((%140 $0) ((%141 (%142 (\%143. %73))) ((%144 (%82 (\%83.
       %73))) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149
       (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3. %154)))) $1)
       $0)))))`)
  val IL3_def =
    DT([], [],
       `((%177 %178) (\%155. (\%156. (%172 (((\%155. (\%156. (((%138 (%81
       %19)) ((%139 $0) ((%140 $1) ((%141 (%142 (\%143. %73))) ((%144 (%82
       (\%83. %73))) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73)))
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154)))) $1) $0)))))`)
  val IL4_def =
    DT([], [],
       `((%179 %180) (\%134. (\%158. (%172 (((\%134. (\%158. (((%138 (%81
       (%81 %19))) ((%139 $1) ((%140 (%159 (\%160. %73))) ((%141 $0) ((%144
       (%82 (\%83. %73))) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148.
       %73))) ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154)))) $1) $0)))))`)
  val IL5_def =
    DT([], [],
       `((%181 %182) (\%134. (\%156. (\%161. (%172 ((((\%134. (\%156.
       (\%161. (((%138 (%81 (%81 (%81 %19)))) ((%139 $2) ((%140 (%159
       (\%160. %73))) ((%141 $0) ((%144 $1) ((%145 (%82 (\%83. %73)))
       ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0))))))`)
  val IL6_def =
    DT([], [],
       `((%181 %183) (\%134. (\%156. (\%161. (%172 ((((\%134. (\%156.
       (\%161. (((%138 (%81 (%81 (%81 (%81 %19))))) ((%139 $2) ((%140 (%159
       (\%160. %73))) ((%141 $0) ((%144 $1) ((%145 (%82 (\%83. %73)))
       ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0))))))`)
  val IL7_def =
    DT([], [],
       `((%181 %184) (\%134. (\%156. (\%161. (%172 ((((\%134. (\%156.
       (\%161. (((%138 (%81 (%81 (%81 (%81 (%81 %19)))))) ((%139 $2) ((%140
       (%159 (\%160. %73))) ((%141 $0) ((%144 $1) ((%145 (%82 (\%83. %73)))
       ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73))) (%152
       (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0))))))`)
  val IL8_def =
    DT([], [],
       `((%185 %186) (\%134. (\%156. (\%162. (%172 ((((\%134. (\%156.
       (\%162. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 %19))))))) ((%139 $2)
       ((%140 (%159 (\%160. %73))) ((%141 (%142 (\%143. %73))) ((%144 $1)
       ((%145 $0) ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151. %73)))
       (%152 (\%153. %73)))))))))) (\%3. %154))))) $2) $1) $0))))))`)
  val IL9_def =
    DT([], [],
       `((%181 %187) (\%134. (\%156. (\%161. (%172 ((((\%134. (\%156.
       (\%161. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 %19))))))))
       ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 $0) ((%144 $1) ((%145
       (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151.
       %73))) (%152 (\%153. %73)))))))))) (\%3. %154))))) $2) $1)
       $0))))))`)
  val IL10_def =
    DT([], [],
       `((%181 %188) (\%134. (\%156. (\%161. (%172 ((((\%134. (\%156.
       (\%161. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 %19)))))))))
       ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 $0) ((%144 $1) ((%145
       (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149 (%150 (\%151.
       %73))) (%152 (\%153. %73)))))))))) (\%3. %154))))) $2) $1)
       $0))))))`)
  val IL11_def =
    DT([], [],
       `((%181 %189) (\%134. (\%156. (\%161. (%172 ((((\%134. (\%156.
       (\%161. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       %19)))))))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 $0)
       ((%144 $1) ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73)))
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154))))) $2) $1) $0))))))`)
  val IL12_def =
    DT([], [],
       `((%190 %191) (\%134. (\%156. (\%164. (%172 ((((\%134. (\%156.
       (\%164. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       %19))))))))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141 (%142
       (\%143. %73))) ((%144 $1) ((%145 (%82 (\%83. %73))) ((%146 $0)
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154))))) $2) $1) $0))))))`)
  val IL13_def =
    DT([], [],
       `((%190 %192) (\%134. (\%156. (\%164. (%172 ((((\%134. (\%156.
       (\%164. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 %19)))))))))))) ((%139 $2) ((%140 (%159 (\%160. %73))) ((%141
       (%142 (\%143. %73))) ((%144 $1) ((%145 (%82 (\%83. %73))) ((%146 $0)
       ((%149 (%150 (\%151. %73))) (%152 (\%153. %73)))))))))) (\%3.
       %154))))) $2) $1) $0))))))`)
  val IL14_def =
    DT([], [],
       `((%190 %193) (\%134. (\%156. (\%164. (%172 ((((\%134. (\%156.
       (\%164. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 (%81 %19))))))))))))) ((%139 $2) ((%140 (%159 (\%160. %73)))
       ((%141 (%142 (\%143. %73))) ((%144 $1) ((%145 (%82 (\%83. %73)))
       ((%146 $0) ((%149 (%150 (\%151. %73))) (%152 (\%153. %73))))))))))
       (\%3. %154))))) $2) $1) $0))))))`)
  val IL15_def =
    DT([], [],
       `((%190 %194) (\%134. (\%156. (\%164. (%172 ((((\%134. (\%156.
       (\%164. (((%138 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 (%81 (%81 %19)))))))))))))) ((%139 $2) ((%140 (%159 (\%160.
       %73))) ((%141 (%142 (\%143. %73))) ((%144 $1) ((%145 (%82 (\%83.
       %73))) ((%146 $0) ((%149 (%150 (\%151. %73))) (%152 (\%153.
       %73)))))))))) (\%3. %154))))) $2) $1) $0))))))`)
  val IL16_def =
    DT([], [],
       `((%195 %196) (\%166. (\%168. (%172 (((\%166. (\%168. (((%138 (%81
       (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       %19))))))))))))))) ((%139 (%82 (\%83. %73))) ((%140 (%159 (\%160.
       %73))) ((%141 (%142 (\%143. %73))) ((%144 (%82 (\%83. %73))) ((%145
       (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149 $1) $0))))))))
       (\%3. %154)))) $1) $0)))))`)
  val IL17_def =
    DT([], [],
       `((%195 %197) (\%166. (\%168. (%172 (((\%166. (\%168. (((%138 (%81
       (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81 (%81
       (%81 %19)))))))))))))))) ((%139 (%82 (\%83. %73))) ((%140 (%159
       (\%160. %73))) ((%141 (%142 (\%143. %73))) ((%144 (%82 (\%83. %73)))
       ((%145 (%82 (\%83. %73))) ((%146 (%147 (\%148. %73))) ((%149 $1)
       $0)))))))) (\%3. %154)))) $1) $0)))))`)
  val MLDR = DT([], [], `((%175 %198) %176)`)
  val MSTR = DT([], [], `((%177 %199) %178)`)
  val MMOV = DT([], [], `((%179 %200) %180)`)
  val MADD = DT([], [], `((%181 %201) %182)`)
  val MSUB = DT([], [], `((%181 %202) %183)`)
  val MRSB = DT([], [], `((%181 %203) %184)`)
  val MMUL = DT([], [], `((%185 %204) %186)`)
  val MAND = DT([], [], `((%181 %205) %187)`)
  val MORR = DT([], [], `((%181 %206) %188)`)
  val MEOR = DT([], [], `((%181 %207) %189)`)
  val MLSL = DT([], [], `((%190 %208) %191)`)
  val MLSR = DT([], [], `((%190 %209) %192)`)
  val MASR = DT([], [], `((%190 %210) %193)`)
  val MROR = DT([], [], `((%190 %211) %194)`)
  val MPUSH = DT([], [], `((%195 %212) %196)`)
  val MPOP = DT([], [], `((%195 %213) %197)`)
  val DOPER_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%214 (\%215. (%216 (\%217. (%218 (\%219. (%220 (\%221. (%220
       (\%222. (%220 (\%223. (%224 (\%225. (%220 (\%226. (%220 (\%227.
       (%220 (\%228. (%229 (\%230. (%229 (\%231. (%229 (\%232. (%229
       (\%233. (%234 (\%235. (%234 (\%236. (%9 (\%134. (%237 (\%136. ((%53
       (((((((((((((((((%238 $17) $16) $15) $14) $13) $12) $11) $10) $9)
       $8) $7) $6) $5) $4) $3) $2) ((%198 $1) $0))) (($17 $1)
       $0))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%237 (\%155. (%9 (\%156. ((%53 (((((((((((((((((%238
       $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3)
       $2) ((%199 $1) $0))) (($16 $1)
       $0))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%84 (\%158. ((%53 (((((((((((((((((%238
       $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3)
       $2) ((%200 $1) $0))) (($15 $1)
       $0))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%201 $2) $1) $0))) ((($15 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%202 $2) $1) $0))) ((($14 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%203 $2) $1) $0))) ((($13 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%9 (\%162. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%204 $2) $1) $0))) ((($12 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%205 $2) $1) $0))) ((($11 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%206 $2) $1) $0))) ((($10 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%207 $2) $1) $0))) ((($9 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%239 (\%164. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%208 $2) $1) $0))) ((($8 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%239 (\%164. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%209 $2) $1) $0))) ((($7 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%239 (\%164. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%210 $2) $1) $0))) ((($6 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%9 (\%134. (%9 (\%156. (%239 (\%164. ((%53
       (((((((((((((((((%238 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%211 $2) $1) $0))) ((($5 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%14 (\%166. (%240 (\%168. ((%53 (((((((((((((((((%238
       $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3)
       $2) ((%212 $1) $0))) (($3 $1)
       $0))))))))))))))))))))))))))))))))))))))) (%214 (\%215. (%216
       (\%217. (%218 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223.
       (%224 (\%225. (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229
       (\%230. (%229 (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235.
       (%234 (\%236. (%14 (\%166. (%240 (\%168. ((%53 (((((((((((((((((%238
       $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3)
       $2) ((%213 $1) $0))) (($2 $1)
       $0)))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val DOPER_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%134. (%237 (\%136. ((%17 (%241 ((%198 $1) $0))) ((%104
       (%5 (%6 %7))) ((%104 (%36 $1)) ((%242 (\%243. (\%244. ((%104
       ((\%243. $0) $1)) (%245 $0))))) $0))))))))) ((%8 (%237 (\%155. (%9
       (\%156. ((%17 (%241 ((%199 $1) $0))) ((%104 (%5 (%6 %7))) ((%104
       ((%242 (\%243. (\%244. ((%104 ((\%243. $0) $1)) (%245 $0))))) $1))
       (%36 $0))))))))) ((%8 (%9 (\%134. (%84 (\%158. ((%17 (%241 ((%200
       $1) $0))) ((%104 (%5 (%6 %7))) ((%104 (%36 $1)) (%103 $0)))))))))
       ((%8 (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%17 (%241 (((%201 $2)
       $1) $0))) ((%104 (%5 (%6 %7))) ((%104 (%36 $2)) ((%104 (%36 $1))
       (%103 $0)))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%17
       (%241 (((%202 $2) $1) $0))) ((%104 (%5 (%6 %7))) ((%104 (%36 $2))
       ((%104 (%36 $1)) (%103 $0)))))))))))) ((%8 (%9 (\%134. (%9 (\%156.
       (%84 (\%161. ((%17 (%241 (((%203 $2) $1) $0))) ((%104 (%5 (%6 %7)))
       ((%104 (%36 $2)) ((%104 (%36 $1)) (%103 $0)))))))))))) ((%8 (%9
       (\%134. (%9 (\%156. (%9 (\%162. ((%17 (%241 (((%204 $2) $1) $0)))
       ((%104 (%5 (%6 %7))) ((%104 (%36 $2)) ((%104 (%36 $1)) (%36
       $0)))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%17 (%241
       (((%205 $2) $1) $0))) ((%104 (%5 (%6 %7))) ((%104 (%36 $2)) ((%104
       (%36 $1)) (%103 $0)))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84
       (\%161. ((%17 (%241 (((%206 $2) $1) $0))) ((%104 (%5 (%6 %7)))
       ((%104 (%36 $2)) ((%104 (%36 $1)) (%103 $0)))))))))))) ((%8 (%9
       (\%134. (%9 (\%156. (%84 (\%161. ((%17 (%241 (((%207 $2) $1) $0)))
       ((%104 (%5 (%6 %7))) ((%104 (%36 $2)) ((%104 (%36 $1)) (%103
       $0)))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239 (\%164. ((%17
       (%241 (((%208 $2) $1) $0))) ((%104 (%5 (%6 %7))) ((%104 (%36 $2))
       (%36 $1))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239 (\%164. ((%17
       (%241 (((%209 $2) $1) $0))) ((%104 (%5 (%6 %7))) ((%104 (%36 $2))
       (%36 $1))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239 (\%164. ((%17
       (%241 (((%210 $2) $1) $0))) ((%104 (%5 (%6 %7))) ((%104 (%36 $2))
       (%36 $1))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239 (\%164. ((%17
       (%241 (((%211 $2) $1) $0))) ((%104 (%5 (%6 %7))) ((%104 (%36 $2))
       (%36 $1))))))))))) ((%8 (%14 (\%166. (%240 (\%168. ((%17 (%241
       ((%212 $1) $0))) ((%104 (%5 (%6 %7))) ((%104 $1) ((%246 (\%243. $0))
       $0))))))))) (%14 (\%166. (%240 (\%168. ((%17 (%241 ((%213 $1) $0)))
       ((%104 (%5 (%6 %7))) ((%104 $1) ((%246 (\%243. $0))
       $0)))))))))))))))))))))))`)
  val CTL_STRUCTURE_TY_DEF =
    DT(["DISK_THM"], [],
       `(%247 (\%248. ((%249 (\%250. (%251 (\%252. ((%63 (%253 (\%250.
       ((%63 ((%65 (%254 (\%255. ((%256 $1) ((\%255. (((%257 %19) ((%258
       $0) (%259 (\%260. %73)))) (\%3. %261))) $0))))) ((%65 (%262 (\%263.
       (%262 (\%264. ((%8 ((%256 $2) (((\%263. (\%264. (((%257 (%81 %19))
       ((%258 (%265 (\%266. %73))) (%259 (\%260. %73)))) ((%267 $1) ((%267
       $0) (\%3. %261)))))) $1) $0))) ((%8 ($3 $1)) ($3 $0)))))))) ((%65
       (%268 (\%269. (%262 (\%264. (%262 (\%270. ((%8 ((%256 $3) ((((\%269.
       (\%264. (\%270. (((%257 (%81 (%81 %19))) ((%258 (%265 (\%266. %73)))
       $2)) ((%267 $1) ((%267 $0) (\%3. %261))))))) $2) $1) $0))) ((%8 ($4
       $1)) ($4 $0)))))))))) (%268 (\%269. (%262 (\%264. ((%8 ((%256 $2)
       (((\%269. (\%264. (((%257 (%81 (%81 (%81 %19)))) ((%258 (%265
       (\%266. %73))) $1)) ((%267 $0) (\%3. %261))))) $1) $0))) ($3
       $0)))))))))) ($1 $0))))) ($0 $1)))))) $0)))`)
  val CTL_STRUCTURE_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%271 (\%272. ((%273 (%274 (%275 $0))) $0)))) (%253 (\%276.
       ((%16 ((\%250. (%251 (\%252. ((%63 (%253 (\%250. ((%63 ((%65 (%254
       (\%255. ((%256 $1) ((\%255. (((%257 %19) ((%258 $0) (%259 (\%260.
       %73)))) (\%3. %261))) $0))))) ((%65 (%262 (\%263. (%262 (\%264. ((%8
       ((%256 $2) (((\%263. (\%264. (((%257 (%81 %19)) ((%258 (%265 (\%266.
       %73))) (%259 (\%260. %73)))) ((%267 $1) ((%267 $0) (\%3. %261))))))
       $1) $0))) ((%8 ($3 $1)) ($3 $0)))))))) ((%65 (%268 (\%269. (%262
       (\%264. (%262 (\%270. ((%8 ((%256 $3) ((((\%269. (\%264. (\%270.
       (((%257 (%81 (%81 %19))) ((%258 (%265 (\%266. %73))) $2)) ((%267 $1)
       ((%267 $0) (\%3. %261))))))) $2) $1) $0))) ((%8 ($4 $1)) ($4
       $0)))))))))) (%268 (\%269. (%262 (\%264. ((%8 ((%256 $2) (((\%269.
       (\%264. (((%257 (%81 (%81 (%81 %19)))) ((%258 (%265 (\%266. %73)))
       $1)) ((%267 $0) (\%3. %261))))) $1) $0))) ($3 $0)))))))))) ($1
       $0))))) ($0 $1))))) $0)) ((%256 (%275 (%274 $0))) $0)))))`)
  val IL18_def =
    DT([], [],
       `((%277 %278) (\%255. (%274 ((\%255. (((%257 %19) ((%258 $0) (%259
       (\%260. %73)))) (\%3. %261))) $0))))`)
  val IL19_def =
    DT([], [],
       `((%279 %280) (\%281. (\%282. (%274 (((\%263. (\%264. (((%257 (%81
       %19)) ((%258 (%265 (\%266. %73))) (%259 (\%260. %73)))) ((%267 $1)
       ((%267 $0) (\%3. %261)))))) (%275 $1)) (%275 $0))))))`)
  val IL20_def =
    DT([], [],
       `((%283 %284) (\%269. (\%282. (\%285. (%274 ((((\%269. (\%264.
       (\%270. (((%257 (%81 (%81 %19))) ((%258 (%265 (\%266. %73))) $2))
       ((%267 $1) ((%267 $0) (\%3. %261))))))) $2) (%275 $1)) (%275
       $0)))))))`)
  val IL21_def =
    DT([], [],
       `((%286 %287) (\%269. (\%282. (%274 (((\%269. (\%264. (((%257 (%81
       (%81 (%81 %19)))) ((%258 (%265 (\%266. %73))) $1)) ((%267 $0) (\%3.
       %261))))) $1) (%275 $0))))))`)
  val BLK = DT([], [], `((%277 %288) %278)`)
  val SC = DT([], [], `((%279 %289) %280)`)
  val CJ = DT([], [], `((%283 %290) %284)`)
  val TR = DT([], [], `((%286 %291) %287)`)
  val CTL_STRUCTURE_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%292 (\%293. (%294 (\%295. (%296 (\%297. (%298 (\%299. (%300
       (\%255. ((%53 (((((%301 $4) $3) $2) $1) (%288 $0))) ($4
       $0))))))))))))) ((%8 (%292 (\%293. (%294 (\%295. (%296 (\%297. (%298
       (\%299. (%271 (\%281. (%271 (\%282. ((%53 (((((%301 $5) $4) $3) $2)
       ((%289 $1) $0))) (($4 $1) $0))))))))))))))) ((%8 (%292 (\%293. (%294
       (\%295. (%296 (\%297. (%298 (\%299. (%302 (\%269. (%271 (\%282.
       (%271 (\%285. ((%53 (((((%301 $6) $5) $4) $3) (((%290 $2) $1) $0)))
       ((($4 $2) $1) $0))))))))))))))))) (%292 (\%293. (%294 (\%295. (%296
       (\%297. (%298 (\%299. (%302 (\%269. (%271 (\%282. ((%53 (((((%301
       $5) $4) $3) $2) ((%291 $1) $0))) (($2 $1) $0)))))))))))))))))`)
  val CTL_STRUCTURE_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%300 (\%255. ((%17 (%303 (%288 $0))) ((%104 (%5 (%6 %7)))
       ((%304 %241) $0)))))) ((%8 (%271 (\%281. (%271 (\%282. ((%17 (%303
       ((%289 $1) $0))) ((%104 (%5 (%6 %7))) ((%104 (%303 $1)) (%303
       $0))))))))) ((%8 (%302 (\%269. (%271 (\%282. (%271 (\%285. ((%17
       (%303 (((%290 $2) $1) $0))) ((%104 (%5 (%6 %7))) ((%104 ((%305
       (\%35. (\%306. ((%104 (%36 $1)) ((%307 (\%308. (\%309. ((%104 (%310
       $1)) (%103 $0))))) $0))))) $2)) ((%104 (%303 $1)) (%303
       $0)))))))))))) (%302 (\%269. (%271 (\%282. ((%17 (%303 ((%291 $1)
       $0))) ((%104 (%5 (%6 %7))) ((%104 ((%305 (\%35. (\%306. ((%104 (%36
       $1)) ((%307 (\%308. (\%309. ((%104 (%310 $1)) (%103 $0))))) $0)))))
       $1)) (%303 $0)))))))))))`)
  val pushL_def =
    DT([], [],
       `(%311 (\%312. (%14 (\%313. (%240 (\%314. ((%315 (((%316 $2) $1)
       $0)) (((%317 (%318 (((%319 (%320 (\%321. (\%106. (\%322. ((%323
       (((%317 $2) (%118 ((%117 $4) (%324 $1)))) ((%325 $5) $0))) ((%104
       $1) (%5 (%6 %7))))))))) ((%323 $2) %19)) (%326 ((%327 %112) $0)))))
       (%112 $1)) ((%328 ((%325 $2) (%112 $1))) (%329 (%330 $0)))))))))))`)
  val popL_def =
    DT([], [],
       `(%311 (\%312. (%14 (\%313. (%240 (\%314. ((%315 (((%331 $2) $1)
       $0)) (((%317 (%318 (((%319 (%320 (\%321. (\%106. (\%322. ((%323
       (((%317 $2) $0) ((%325 $5) (%118 ((%117 $4) (%332 ((%104 $1) (%5 (%6
       %7))))))))) ((%104 $1) (%5 (%6 %7))))))))) ((%323 $2) %19)) ((%327
       %112) $0)))) (%112 $1)) ((%333 ((%325 $2) (%112 $1))) (%329 (%330
       $0)))))))))))`)
  val mdecode_def =
    DT(["DISK_THM"], [],
       `((%8 (%311 (\%312. (%9 (\%334. (%237 (\%335. ((%315 ((%336 $2)
       ((%198 $1) $0))) (((%317 $2) (%111 $1)) ((%325 $2) (%116
       $0))))))))))) ((%8 (%311 (\%312. (%237 (\%337. (%9 (\%338. ((%315
       ((%336 $2) ((%199 $1) $0))) (((%317 $2) (%116 $1)) ((%325 $2) (%111
       $0))))))))))) ((%8 (%311 (\%312. (%9 (\%334. (%84 (\%339. ((%315
       ((%336 $2) ((%200 $1) $0))) (((%317 $2) (%111 $1)) ((%325 $2) (%119
       $0))))))))))) ((%8 (%311 (\%312. (%9 (\%334. (%9 (\%340. (%84
       (\%341. ((%315 ((%336 $3) (((%201 $2) $1) $0))) (((%317 $3) (%111
       $2)) ((%333 ((%325 $3) (%111 $1))) ((%325 $3) (%119 $0))))))))))))))
       ((%8 (%311 (\%312. (%9 (\%334. (%9 (\%340. (%84 (\%341. ((%315
       ((%336 $3) (((%202 $2) $1) $0))) (((%317 $3) (%111 $2)) ((%328
       ((%325 $3) (%111 $1))) ((%325 $3) (%119 $0)))))))))))))) ((%8 (%311
       (\%312. (%9 (\%334. (%9 (\%340. (%84 (\%341. ((%315 ((%336 $3)
       (((%203 $2) $1) $0))) (((%317 $3) (%111 $2)) ((%328 ((%325 $3) (%119
       $0))) ((%325 $3) (%111 $1)))))))))))))) ((%8 (%311 (\%312. (%9
       (\%334. (%9 (\%340. (%9 (\%342. ((%315 ((%336 $3) (((%204 $2) $1)
       $0))) (((%317 $3) (%111 $2)) ((%343 ((%325 $3) (%111 $1))) ((%325
       $3) (%111 $0)))))))))))))) ((%8 (%311 (\%312. (%9 (\%334. (%9
       (\%340. (%84 (\%341. ((%315 ((%336 $3) (((%205 $2) $1) $0))) (((%317
       $3) (%111 $2)) ((%344 ((%325 $3) (%111 $1))) ((%325 $3) (%119
       $0)))))))))))))) ((%8 (%311 (\%312. (%9 (\%334. (%9 (\%340. (%84
       (\%341. ((%315 ((%336 $3) (((%206 $2) $1) $0))) (((%317 $3) (%111
       $2)) ((%345 ((%325 $3) (%111 $1))) ((%325 $3) (%119 $0))))))))))))))
       ((%8 (%311 (\%312. (%9 (\%334. (%9 (\%340. (%84 (\%341. ((%315
       ((%336 $3) (((%207 $2) $1) $0))) (((%317 $3) (%111 $2)) ((%346
       ((%325 $3) (%111 $1))) ((%325 $3) (%119 $0)))))))))))))) ((%8 (%311
       (\%312. (%9 (\%334. (%9 (\%342. (%239 (\%347. ((%315 ((%336 $3)
       (((%208 $2) $1) $0))) (((%317 $3) (%111 $2)) ((%348 ((%325 $3) (%111
       $1))) (%349 $0))))))))))))) ((%8 (%311 (\%312. (%9 (\%334. (%9
       (\%342. (%239 (\%347. ((%315 ((%336 $3) (((%209 $2) $1) $0)))
       (((%317 $3) (%111 $2)) ((%350 ((%325 $3) (%111 $1))) (%349
       $0))))))))))))) ((%8 (%311 (\%312. (%9 (\%334. (%9 (\%342. (%239
       (\%347. ((%315 ((%336 $3) (((%210 $2) $1) $0))) (((%317 $3) (%111
       $2)) ((%351 ((%325 $3) (%111 $1))) (%349 $0))))))))))))) ((%8 (%311
       (\%312. (%9 (\%334. (%9 (\%342. (%239 (\%347. ((%315 ((%336 $3)
       (((%211 $2) $1) $0))) (((%317 $3) (%111 $2)) ((%123 ((%325 $3) (%111
       $1))) (%349 $0))))))))))))) ((%8 (%311 (\%312. (%14 (\%352. (%240
       (\%353. ((%315 ((%336 $2) ((%212 $1) $0))) (((%316 $2) $1)
       $0))))))))) (%311 (\%312. (%14 (\%352. (%240 (\%353. ((%315 ((%336
       $2) ((%213 $1) $0))) (((%331 $2) $1) $0)))))))))))))))))))))))`)
  val translate_assignment_def =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%334. (%84 (\%339. ((%354 (%355 ((%200 $1) $0))) ((%356
       ((%357 %358) ((%359 %360) %361))) ((%362 (%363 (%111 $1))) ((%364
       ((%365 (%119 $0)) %366)) %367))))))))) ((%8 (%9 (\%334. (%9 (\%340.
       (%84 (\%341. ((%354 (%355 (((%201 $2) $1) $0))) ((%356 ((%357 %368)
       ((%359 %360) %361))) ((%362 (%363 (%111 $2))) ((%364 ((%365 (%111
       $1)) ((%365 (%119 $0)) %366))) %367))))))))))) ((%8 (%9 (\%334. (%9
       (\%340. (%84 (\%341. ((%354 (%355 (((%202 $2) $1) $0))) ((%356
       ((%357 %369) ((%359 %360) %361))) ((%362 (%363 (%111 $2))) ((%364
       ((%365 (%111 $1)) ((%365 (%119 $0)) %366))) %367))))))))))) ((%8 (%9
       (\%334. (%9 (\%340. (%84 (\%341. ((%354 (%355 (((%203 $2) $1) $0)))
       ((%356 ((%357 %370) ((%359 %360) %361))) ((%362 (%363 (%111 $2)))
       ((%364 ((%365 (%111 $1)) ((%365 (%119 $0)) %366))) %367)))))))))))
       ((%8 (%9 (\%334. (%9 (\%340. (%9 (\%342. ((%354 (%355 (((%204 $2)
       $1) $0))) ((%356 ((%357 %371) ((%359 %360) %361))) ((%362 (%363
       (%111 $2))) ((%364 ((%365 (%111 $1)) ((%365 (%111 $0)) %366)))
       %367))))))))))) ((%8 (%9 (\%334. (%9 (\%340. (%84 (\%341. ((%354
       (%355 (((%205 $2) $1) $0))) ((%356 ((%357 %372) ((%359 %360) %361)))
       ((%362 (%363 (%111 $2))) ((%364 ((%365 (%111 $1)) ((%365 (%119 $0))
       %366))) %367))))))))))) ((%8 (%9 (\%334. (%9 (\%340. (%84 (\%341.
       ((%354 (%355 (((%206 $2) $1) $0))) ((%356 ((%357 %373) ((%359 %360)
       %361))) ((%362 (%363 (%111 $2))) ((%364 ((%365 (%111 $1)) ((%365
       (%119 $0)) %366))) %367))))))))))) ((%8 (%9 (\%334. (%9 (\%340. (%84
       (\%341. ((%354 (%355 (((%207 $2) $1) $0))) ((%356 ((%357 %374)
       ((%359 %360) %361))) ((%362 (%363 (%111 $2))) ((%364 ((%365 (%111
       $1)) ((%365 (%119 $0)) %366))) %367))))))))))) ((%8 (%9 (\%334. (%9
       (\%342. (%239 (\%347. ((%354 (%355 (((%208 $2) $1) $0))) ((%356
       ((%357 %375) ((%359 %360) %361))) ((%362 (%363 (%111 $2))) ((%364
       ((%365 (%111 $1)) ((%365 (%122 (%376 $0))) %366))) %367)))))))))))
       ((%8 (%9 (\%334. (%9 (\%342. (%239 (\%347. ((%354 (%355 (((%209 $2)
       $1) $0))) ((%356 ((%357 %377) ((%359 %360) %361))) ((%362 (%363
       (%111 $2))) ((%364 ((%365 (%111 $1)) ((%365 (%122 (%376 $0)))
       %366))) %367))))))))))) ((%8 (%9 (\%334. (%9 (\%342. (%239 (\%347.
       ((%354 (%355 (((%210 $2) $1) $0))) ((%356 ((%357 %378) ((%359 %360)
       %361))) ((%362 (%363 (%111 $2))) ((%364 ((%365 (%111 $1)) ((%365
       (%122 (%376 $0))) %366))) %367))))))))))) ((%8 (%9 (\%334. (%9
       (\%342. (%239 (\%347. ((%354 (%355 (((%211 $2) $1) $0))) ((%356
       ((%357 %379) ((%359 %360) %361))) ((%362 (%363 (%111 $2))) ((%364
       ((%365 (%111 $1)) ((%365 (%122 (%376 $0))) %366))) %367)))))))))))
       ((%8 (%9 (\%334. (%237 (\%335. ((%354 (%355 ((%198 $1) $0))) ((%356
       ((%357 %380) ((%359 %360) %361))) ((%362 (%363 (%111 $1))) ((%364
       ((%365 (%116 $0)) %366)) %367))))))))) ((%8 (%237 (\%337. (%9
       (\%338. ((%354 (%355 ((%199 $1) $0))) ((%356 ((%357 %381) ((%359
       %360) %361))) ((%362 (%363 (%111 $0))) ((%364 ((%365 (%116 $1))
       %366)) %367))))))))) ((%8 (%14 (\%382. (%240 (\%353. ((%354 (%355
       ((%212 $1) $0))) ((%356 ((%357 %383) ((%359 %360) %361))) ((%362
       (%363 (%384 $1))) ((%364 ((%327 %112) $0)) %367))))))))) (%14
       (\%382. (%240 (\%353. ((%354 (%355 ((%213 $1) $0))) ((%356 ((%357
       %385) ((%359 %360) %361))) ((%362 (%363 (%384 $1))) ((%364 ((%327
       %112) $0)) %367)))))))))))))))))))))))`)
  val translate_condition_def =
    DT(["DISK_THM"], [],
       `(%9 (\%109. (%37 (\%386. (%84 (\%387. ((%388 (%389 ((%390 $2)
       ((%391 $1) $0)))) ((%392 (%111 $2)) ((%393 $1) (%119 $0))))))))))`)
  val eval_il_cond_def =
    DT([], [], `(%302 (\%394. ((%395 (%396 $0)) (%397 (%398 $0)))))`)
  val translate_primitive_def =
    DT([], [],
       `((%399 %400) ((%401 (%402 (\%403. ((%8 (%404 $0)) ((%8 (%169
       (\%405. (%300 (\%406. (($2 (%288 $0)) (%288 ((%407 $1) $0))))))))
       ((%8 (%271 (\%408. (%271 (\%409. (($2 $0) ((%289 $1) $0))))))) ((%8
       (%271 (\%409. (%271 (\%408. (($2 $0) ((%289 $0) $1))))))) ((%8 (%271
       (\%410. (%302 (\%394. (%271 (\%411. (($3 $0) (((%290 $1) $0)
       $2))))))))) ((%8 (%271 (\%411. (%302 (\%394. (%271 (\%410. (($3 $0)
       (((%290 $1) $2) $0))))))))) (%302 (\%394. (%271 (\%412. (($2 $0)
       ((%291 $1) $0))))))))))))))) (\%413. (\%272. (((((%414 (\%266.
       (((%415 (%416 %417)) (\%405. (\%406. (%416 ((%418 (%355 $1)) ($4
       (%288 $0))))))) $0))) (\%408. (\%409. (%416 ((%419 ($3 $1)) ($3
       $0)))))) (\%394. (\%411. (\%410. (%416 (((%420 (%398 $2)) ($4 $1))
       ($4 $0))))))) (\%421. (\%412. (%416 ((%422 (%398 $1)) ($3 $0))))))
       $0)))))`)
  val run_arm_def =
    DT(["DISK_THM"], [],
       `(%423 (\%424. (%14 (\%425. (%426 (\%427. (%311 (\%312. (%428
       (\%429. ((%430 ((%431 $4) ((%432 ((%433 $3) ((%434 $2) $1))) $0)))
       (((%435 (((%436 $4) (\%106. %437)) $3)) ((%104 $3) (%438 $4)))
       ((%432 ((%433 $3) ((%434 $2) $1))) $0)))))))))))))`)
  val run_ir_def =
    DT([], [],
       `(%271 (\%439. (%311 (\%312. ((%315 ((%440 $1) $0)) (%441 ((%431
       (%400 $1)) ((%432 ((%433 %19) ((%434 (%329 %19)) $0)))
       %442))))))))`)
  val WELL_FORMED_def =
    DT(["DISK_THM"], [],
       `((%8 (%300 (\%406. ((%16 (%443 (%288 $0))) (%444 (%400 (%288
       $0))))))) ((%8 (%271 (\%408. (%271 (\%409. ((%16 (%443 ((%289 $1)
       $0))) ((%8 (%444 (%400 ((%289 $1) $0)))) ((%8 (%443 $1)) (%443
       $0))))))))) ((%8 (%302 (\%394. (%271 (\%408. (%271 (\%409. ((%16
       (%443 (((%290 $2) $1) $0))) ((%8 (%444 (%400 (((%290 $2) $1) $0))))
       ((%8 (%443 $1)) (%443 $0))))))))))) (%302 (\%394. (%271 (\%408.
       ((%16 (%443 ((%291 $1) $0))) ((%8 (%444 (%400 ((%291 $1) $0)))) ((%8
       (%443 $0)) (%445 ((%446 (%398 $1)) (%400 $0)))))))))))))`)
  val WELL_FORMED_SUB_def =
    DT(["DISK_THM"], [],
       `((%8 (%300 (\%406. ((%16 (%447 (%288 $0))) %73)))) ((%8 (%271
       (\%408. (%271 (\%409. ((%16 (%447 ((%289 $1) $0))) ((%8 (%443 $1))
       (%443 $0)))))))) ((%8 (%302 (\%394. (%271 (\%408. (%271 (\%409.
       ((%16 (%447 (((%290 $2) $1) $0))) ((%8 (%443 $1)) (%443 $0))))))))))
       (%302 (\%394. (%271 (\%408. ((%16 (%447 ((%291 $1) $0))) ((%8 (%443
       $0)) (%445 ((%446 (%398 $1)) (%400 $0))))))))))))`)
  val num2MREG_MREG2num =
    DT(["DISK_THM"], [], `(%9 (\%10. ((%11 (%12 (%13 $0))) $0)))`)
  val MREG2num_num2MREG =
    DT(["DISK_THM"], [],
       `(%14 (\%15. ((%16 ((%4 $0) (%5 (%6 (%6 (%6 (%6 %7))))))) ((%17 (%13
       (%12 $0))) $0))))`)
  val num2MREG_11 =
    DT(["DISK_THM"], [],
       `(%14 (\%15. (%14 (\%448. ((%63 ((%4 $1) (%5 (%6 (%6 (%6 (%6
       %7))))))) ((%63 ((%4 $0) (%5 (%6 (%6 (%6 (%6 %7))))))) ((%16 ((%11
       (%12 $1)) (%12 $0))) ((%17 $1) $0))))))))`)
  val MREG2num_11 =
    DT(["DISK_THM"], [],
       `(%9 (\%10. (%9 (\%449. ((%16 ((%17 (%13 $1)) (%13 $0))) ((%11 $1)
       $0))))))`)
  val num2MREG_ONTO =
    DT(["DISK_THM"], [],
       `(%9 (\%10. (%165 (\%15. ((%8 ((%11 $1) (%12 $0))) ((%4 $0) (%5 (%6
       (%6 (%6 (%6 %7)))))))))))`)
  val MREG2num_ONTO =
    DT(["DISK_THM"], [],
       `(%14 (\%15. ((%16 ((%4 $0) (%5 (%6 (%6 (%6 (%6 %7))))))) (%66
       (\%10. ((%17 $1) (%13 $0)))))))`)
  val num2MREG_thm =
    DT([], [],
       `((%8 ((%11 (%12 %19)) %18)) ((%8 ((%11 (%12 (%5 (%6 %7)))) %20))
       ((%8 ((%11 (%12 (%5 (%22 %7)))) %21)) ((%8 ((%11 (%12 (%5 (%6 (%6
       %7))))) %23)) ((%8 ((%11 (%12 (%5 (%22 (%6 %7))))) %24)) ((%8 ((%11
       (%12 (%5 (%6 (%22 %7))))) %25)) ((%8 ((%11 (%12 (%5 (%22 (%22
       %7))))) %26)) ((%8 ((%11 (%12 (%5 (%6 (%6 (%6 %7)))))) %27)) ((%8
       ((%11 (%12 (%5 (%22 (%6 (%6 %7)))))) %28)) ((%8 ((%11 (%12 (%5 (%6
       (%22 (%6 %7)))))) %29)) ((%8 ((%11 (%12 (%5 (%22 (%22 (%6 %7))))))
       %30)) ((%8 ((%11 (%12 (%5 (%6 (%6 (%22 %7)))))) %31)) ((%8 ((%11
       (%12 (%5 (%22 (%6 (%22 %7)))))) %32)) ((%8 ((%11 (%12 (%5 (%6 (%22
       (%22 %7)))))) %33)) ((%11 (%12 (%5 (%22 (%22 (%22 %7))))))
       %34)))))))))))))))`)
  val MREG2num_thm =
    DT(["DISK_THM"], [],
       `((%8 ((%17 (%13 %18)) %19)) ((%8 ((%17 (%13 %20)) (%5 (%6 %7))))
       ((%8 ((%17 (%13 %21)) (%5 (%22 %7)))) ((%8 ((%17 (%13 %23)) (%5 (%6
       (%6 %7))))) ((%8 ((%17 (%13 %24)) (%5 (%22 (%6 %7))))) ((%8 ((%17
       (%13 %25)) (%5 (%6 (%22 %7))))) ((%8 ((%17 (%13 %26)) (%5 (%22 (%22
       %7))))) ((%8 ((%17 (%13 %27)) (%5 (%6 (%6 (%6 %7)))))) ((%8 ((%17
       (%13 %28)) (%5 (%22 (%6 (%6 %7)))))) ((%8 ((%17 (%13 %29)) (%5 (%6
       (%22 (%6 %7)))))) ((%8 ((%17 (%13 %30)) (%5 (%22 (%22 (%6 %7))))))
       ((%8 ((%17 (%13 %31)) (%5 (%6 (%6 (%22 %7)))))) ((%8 ((%17 (%13
       %32)) (%5 (%22 (%6 (%22 %7)))))) ((%8 ((%17 (%13 %33)) (%5 (%6 (%22
       (%22 %7)))))) ((%17 (%13 %34)) (%5 (%22 (%22 (%22
       %7)))))))))))))))))))`)
  val MREG_EQ_MREG =
    DT(["DISK_THM"], [],
       `(%9 (\%10. (%9 (\%449. ((%16 ((%11 $1) $0)) ((%17 (%13 $1)) (%13
       $0)))))))`)
  val MREG_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%37 (\%38. (%37 (\%39. (%37 (\%40. (%37 (\%41. (%37 (\%42.
       (%37 (\%43. (%37 (\%44. (%37 (\%45. (%37 (\%46. (%37 (\%47. (%37
       (\%48. (%37 (\%49. (%37 (\%50. (%37 (\%51. (%37 (\%52. ((%53
       ((((((((((((((((%54 $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %18)) $14)))))))))))))))))))))))))))))))) ((%8 (%37
       (\%38. (%37 (\%39. (%37 (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43.
       (%37 (\%44. (%37 (\%45. (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37
       (\%49. (%37 (\%50. (%37 (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54
       $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0)
       %20)) $13)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37
       (\%39. (%37 (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44.
       (%37 (\%45. (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37
       (\%50. (%37 (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13)
       $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %21))
       $12)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39.
       (%37 (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37
       (\%45. (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50.
       (%37 (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12)
       $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %23))
       $11)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39.
       (%37 (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37
       (\%45. (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50.
       (%37 (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12)
       $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %24))
       $10)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39.
       (%37 (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37
       (\%45. (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50.
       (%37 (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12)
       $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %25))
       $9)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39. (%37
       (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45.
       (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37
       (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %26))
       $8)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39. (%37
       (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45.
       (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37
       (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %27))
       $7)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39. (%37
       (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45.
       (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37
       (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %28))
       $6)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39. (%37
       (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45.
       (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37
       (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %29))
       $5)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39. (%37
       (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45.
       (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37
       (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %30))
       $4)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39. (%37
       (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45.
       (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37
       (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %31))
       $3)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39. (%37
       (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45.
       (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37
       (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %32))
       $2)))))))))))))))))))))))))))))))) ((%8 (%37 (\%38. (%37 (\%39. (%37
       (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45.
       (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37
       (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %33))
       $1)))))))))))))))))))))))))))))))) (%37 (\%38. (%37 (\%39. (%37
       (\%40. (%37 (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45.
       (%37 (\%46. (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37
       (\%51. (%37 (\%52. ((%53 ((((((((((((((((%54 $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %34))
       $0)))))))))))))))))))))))))))))))))))))))))))))`)
  val datatype_MREG =
    DT(["DISK_THM"], [],
       `(%450 (((((((((((((((%451 %18) %20) %21) %23) %24) %25) %26) %27)
       %28) %29) %30) %31) %32) %33) %34))`)
  val MREG_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%452 ((%11 %18) %20))) ((%8 (%452 ((%11 %18) %21))) ((%8
       (%452 ((%11 %18) %23))) ((%8 (%452 ((%11 %18) %24))) ((%8 (%452
       ((%11 %18) %25))) ((%8 (%452 ((%11 %18) %26))) ((%8 (%452 ((%11 %18)
       %27))) ((%8 (%452 ((%11 %18) %28))) ((%8 (%452 ((%11 %18) %29)))
       ((%8 (%452 ((%11 %18) %30))) ((%8 (%452 ((%11 %18) %31))) ((%8 (%452
       ((%11 %18) %32))) ((%8 (%452 ((%11 %18) %33))) ((%8 (%452 ((%11 %18)
       %34))) ((%8 (%452 ((%11 %20) %21))) ((%8 (%452 ((%11 %20) %23)))
       ((%8 (%452 ((%11 %20) %24))) ((%8 (%452 ((%11 %20) %25))) ((%8 (%452
       ((%11 %20) %26))) ((%8 (%452 ((%11 %20) %27))) ((%8 (%452 ((%11 %20)
       %28))) ((%8 (%452 ((%11 %20) %29))) ((%8 (%452 ((%11 %20) %30)))
       ((%8 (%452 ((%11 %20) %31))) ((%8 (%452 ((%11 %20) %32))) ((%8 (%452
       ((%11 %20) %33))) ((%8 (%452 ((%11 %20) %34))) ((%8 (%452 ((%11 %21)
       %23))) ((%8 (%452 ((%11 %21) %24))) ((%8 (%452 ((%11 %21) %25)))
       ((%8 (%452 ((%11 %21) %26))) ((%8 (%452 ((%11 %21) %27))) ((%8 (%452
       ((%11 %21) %28))) ((%8 (%452 ((%11 %21) %29))) ((%8 (%452 ((%11 %21)
       %30))) ((%8 (%452 ((%11 %21) %31))) ((%8 (%452 ((%11 %21) %32)))
       ((%8 (%452 ((%11 %21) %33))) ((%8 (%452 ((%11 %21) %34))) ((%8 (%452
       ((%11 %23) %24))) ((%8 (%452 ((%11 %23) %25))) ((%8 (%452 ((%11 %23)
       %26))) ((%8 (%452 ((%11 %23) %27))) ((%8 (%452 ((%11 %23) %28)))
       ((%8 (%452 ((%11 %23) %29))) ((%8 (%452 ((%11 %23) %30))) ((%8 (%452
       ((%11 %23) %31))) ((%8 (%452 ((%11 %23) %32))) ((%8 (%452 ((%11 %23)
       %33))) ((%8 (%452 ((%11 %23) %34))) ((%8 (%452 ((%11 %24) %25)))
       ((%8 (%452 ((%11 %24) %26))) ((%8 (%452 ((%11 %24) %27))) ((%8 (%452
       ((%11 %24) %28))) ((%8 (%452 ((%11 %24) %29))) ((%8 (%452 ((%11 %24)
       %30))) ((%8 (%452 ((%11 %24) %31))) ((%8 (%452 ((%11 %24) %32)))
       ((%8 (%452 ((%11 %24) %33))) ((%8 (%452 ((%11 %24) %34))) ((%8 (%452
       ((%11 %25) %26))) ((%8 (%452 ((%11 %25) %27))) ((%8 (%452 ((%11 %25)
       %28))) ((%8 (%452 ((%11 %25) %29))) ((%8 (%452 ((%11 %25) %30)))
       ((%8 (%452 ((%11 %25) %31))) ((%8 (%452 ((%11 %25) %32))) ((%8 (%452
       ((%11 %25) %33))) ((%8 (%452 ((%11 %25) %34))) ((%8 (%452 ((%11 %26)
       %27))) ((%8 (%452 ((%11 %26) %28))) ((%8 (%452 ((%11 %26) %29)))
       ((%8 (%452 ((%11 %26) %30))) ((%8 (%452 ((%11 %26) %31))) ((%8 (%452
       ((%11 %26) %32))) ((%8 (%452 ((%11 %26) %33))) ((%8 (%452 ((%11 %26)
       %34))) ((%8 (%452 ((%11 %27) %28))) ((%8 (%452 ((%11 %27) %29)))
       ((%8 (%452 ((%11 %27) %30))) ((%8 (%452 ((%11 %27) %31))) ((%8 (%452
       ((%11 %27) %32))) ((%8 (%452 ((%11 %27) %33))) ((%8 (%452 ((%11 %27)
       %34))) ((%8 (%452 ((%11 %28) %29))) ((%8 (%452 ((%11 %28) %30)))
       ((%8 (%452 ((%11 %28) %31))) ((%8 (%452 ((%11 %28) %32))) ((%8 (%452
       ((%11 %28) %33))) ((%8 (%452 ((%11 %28) %34))) ((%8 (%452 ((%11 %29)
       %30))) ((%8 (%452 ((%11 %29) %31))) ((%8 (%452 ((%11 %29) %32)))
       ((%8 (%452 ((%11 %29) %33))) ((%8 (%452 ((%11 %29) %34))) ((%8 (%452
       ((%11 %30) %31))) ((%8 (%452 ((%11 %30) %32))) ((%8 (%452 ((%11 %30)
       %33))) ((%8 (%452 ((%11 %30) %34))) ((%8 (%452 ((%11 %31) %32)))
       ((%8 (%452 ((%11 %31) %33))) ((%8 (%452 ((%11 %31) %34))) ((%8 (%452
       ((%11 %32) %33))) ((%8 (%452 ((%11 %32) %34))) (%452 ((%11 %33)
       %34))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val MREG_case_cong =
    DT(["DISK_THM"], [],
       `(%9 (\%453. (%9 (\%454. (%37 (\%38. (%37 (\%39. (%37 (\%40. (%37
       (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45. (%37 (\%46.
       (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37 (\%51. (%37
       (\%52. ((%63 ((%8 ((%11 $16) $15)) ((%8 ((%63 ((%11 $15) %18)) ((%53
       $14) %455))) ((%8 ((%63 ((%11 $15) %20)) ((%53 $13) %456))) ((%8
       ((%63 ((%11 $15) %21)) ((%53 $12) %457))) ((%8 ((%63 ((%11 $15)
       %23)) ((%53 $11) %458))) ((%8 ((%63 ((%11 $15) %24)) ((%53 $10)
       %459))) ((%8 ((%63 ((%11 $15) %25)) ((%53 $9) %460))) ((%8 ((%63
       ((%11 $15) %26)) ((%53 $8) %461))) ((%8 ((%63 ((%11 $15) %27)) ((%53
       $7) %462))) ((%8 ((%63 ((%11 $15) %28)) ((%53 $6) %463))) ((%8 ((%63
       ((%11 $15) %29)) ((%53 $5) %464))) ((%8 ((%63 ((%11 $15) %30)) ((%53
       $4) %465))) ((%8 ((%63 ((%11 $15) %31)) ((%53 $3) %466))) ((%8 ((%63
       ((%11 $15) %32)) ((%53 $2) %467))) ((%8 ((%63 ((%11 $15) %33)) ((%53
       $1) %468))) ((%63 ((%11 $15) %34)) ((%53 $0) %469))))))))))))))))))
       ((%53 ((((((((((((((((%54 $14) $13) $12) $11) $10) $9) $8) $7) $6)
       $5) $4) $3) $2) $1) $0) $16)) ((((((((((((((((%54 %455) %456) %457)
       %458) %459) %460) %461) %462) %463) %464) %465) %466) %467) %468)
       %469) $15)))))))))))))))))))))))))))))))))))))`)
  val MREG_nchotomy =
    DT(["DISK_THM"], [],
       `(%9 (\%10. ((%65 ((%11 $0) %18)) ((%65 ((%11 $0) %20)) ((%65 ((%11
       $0) %21)) ((%65 ((%11 $0) %23)) ((%65 ((%11 $0) %24)) ((%65 ((%11
       $0) %25)) ((%65 ((%11 $0) %26)) ((%65 ((%11 $0) %27)) ((%65 ((%11
       $0) %28)) ((%65 ((%11 $0) %29)) ((%65 ((%11 $0) %30)) ((%65 ((%11
       $0) %31)) ((%65 ((%11 $0) %32)) ((%65 ((%11 $0) %33)) ((%11 $0)
       %34)))))))))))))))))`)
  val MREG_Axiom =
    DT(["DISK_THM"], [],
       `(%37 (\%470. (%37 (\%471. (%37 (\%472. (%37 (\%473. (%37 (\%474.
       (%37 (\%475. (%37 (\%476. (%37 (\%477. (%37 (\%478. (%37 (\%479.
       (%37 (\%480. (%37 (\%481. (%37 (\%482. (%37 (\%483. (%37 (\%484.
       (%485 (\%97. ((%8 ((%53 ($0 %18)) $15)) ((%8 ((%53 ($0 %20)) $14))
       ((%8 ((%53 ($0 %21)) $13)) ((%8 ((%53 ($0 %23)) $12)) ((%8 ((%53 ($0
       %24)) $11)) ((%8 ((%53 ($0 %25)) $10)) ((%8 ((%53 ($0 %26)) $9))
       ((%8 ((%53 ($0 %27)) $8)) ((%8 ((%53 ($0 %28)) $7)) ((%8 ((%53 ($0
       %29)) $6)) ((%8 ((%53 ($0 %30)) $5)) ((%8 ((%53 ($0 %31)) $4)) ((%8
       ((%53 ($0 %32)) $3)) ((%8 ((%53 ($0 %33)) $2)) ((%53 ($0 %34))
       $1)))))))))))))))))))))))))))))))))))))))))))))))`)
  val MREG_induction =
    DT(["DISK_THM"], [],
       `(%486 (\%487. ((%63 ((%8 ($0 %18)) ((%8 ($0 %20)) ((%8 ($0 %30))
       ((%8 ($0 %31)) ((%8 ($0 %32)) ((%8 ($0 %33)) ((%8 ($0 %34)) ((%8 ($0
       %21)) ((%8 ($0 %23)) ((%8 ($0 %24)) ((%8 ($0 %25)) ((%8 ($0 %26))
       ((%8 ($0 %27)) ((%8 ($0 %28)) ($0 %29)))))))))))))))) (%9 (\%10. ($1
       $0))))))`)
  val datatype_MEXP = DT(["DISK_THM"], [], `(%450 ((%488 %94) %95))`)
  val MEXP_11 =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%10. (%9 (\%449. ((%16 ((%86 (%94 $1)) (%94 $0))) ((%11
       $1) $0))))))) (%101 (\%78. (%102 (\%80. (%101 (\%489. (%102 (\%490.
       ((%16 ((%86 ((%95 $3) $2)) ((%95 $1) $0))) ((%8 ((%491 $3) $1))
       ((%492 $2) $0))))))))))))`)
  val MEXP_distinct =
    DT(["DISK_THM"], [],
       `(%102 (\%80. (%101 (\%78. (%9 (\%10. (%452 ((%86 (%94 $0)) ((%95
       $1) $2)))))))))`)
  val MEXP_case_cong =
    DT(["DISK_THM"], [],
       `(%84 (\%493. (%84 (\%494. (%96 (\%97. (%98 (\%99. ((%63 ((%8 ((%86
       $3) $2)) ((%8 (%9 (\%10. ((%63 ((%86 $3) (%94 $0))) ((%53 ($2 $0))
       (%495 $0)))))) (%101 (\%78. (%102 (\%80. ((%63 ((%86 $4) ((%95 $1)
       $0))) ((%53 (($2 $1) $0)) ((%496 $1) $0)))))))))) ((%53 (((%100 $1)
       $0) $3)) (((%100 %495) %496) $2)))))))))))`)
  val MEXP_nchotomy =
    DT(["DISK_THM"], [],
       `(%84 (\%493. ((%65 (%66 (\%453. ((%86 $1) (%94 $0))))) (%77 (\%497.
       (%79 (\%498. ((%86 $2) ((%95 $1) $0)))))))))`)
  val MEXP_Axiom =
    DT(["DISK_THM"], [],
       `(%96 (\%499. (%98 (\%99. (%500 (\%501. ((%8 (%9 (\%10. ((%53 ($1
       (%94 $0))) ($3 $0))))) (%101 (\%78. (%102 (\%80. ((%53 ($2 ((%95 $1)
       $0))) (($3 $1) $0)))))))))))))`)
  val MEXP_induction =
    DT(["DISK_THM"], [],
       `(%502 (\%503. ((%63 ((%8 (%9 (\%453. ($1 (%94 $0))))) (%101 (\%497.
       (%102 (\%498. ($2 ((%95 $1) $0)))))))) (%84 (\%493. ($1 $0))))))`)
  val from_reg_index_thm =
    DT(["DISK_THM"], [],
       `((%8 ((%11 (%107 %19)) %18)) ((%8 ((%11 (%107 (%5 (%6 %7)))) %20))
       ((%8 ((%11 (%107 (%5 (%22 %7)))) %21)) ((%8 ((%11 (%107 (%5 (%6 (%6
       %7))))) %23)) ((%8 ((%11 (%107 (%5 (%22 (%6 %7))))) %24)) ((%8 ((%11
       (%107 (%5 (%6 (%22 %7))))) %25)) ((%8 ((%11 (%107 (%5 (%22 (%22
       %7))))) %26)) ((%8 ((%11 (%107 (%5 (%6 (%6 (%6 %7)))))) %27)) ((%8
       ((%11 (%107 (%5 (%22 (%6 (%6 %7)))))) %28)) ((%8 ((%11 (%107 (%5 (%6
       (%22 (%6 %7)))))) %29)) ((%8 ((%11 (%107 (%5 (%22 (%22 (%6 %7))))))
       %30)) ((%8 ((%11 (%107 (%5 (%6 (%6 (%22 %7)))))) %31)) ((%8 ((%11
       (%107 (%5 (%22 (%6 (%22 %7)))))) %32)) ((%8 ((%11 (%107 (%5 (%6 (%22
       (%22 %7)))))) %33)) ((%11 (%107 (%5 (%22 (%22 (%22 %7))))))
       %34)))))))))))))))`)
  val datatype_DOPER =
    DT(["DISK_THM"], [],
       `(%450 ((((((((((((((((%504 %198) %199) %200) %201) %202) %203)
       %204) %205) %206) %207) %208) %209) %210) %211) %212) %213))`)
  val DOPER_11 =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%134. (%237 (\%136. (%9 (\%505. (%237 (\%506. ((%16
       ((%171 ((%198 $3) $2)) ((%198 $1) $0))) ((%8 ((%11 $3) $1)) ((%507
       $2) $0)))))))))))) ((%8 (%237 (\%155. (%9 (\%156. (%237 (\%508. (%9
       (\%509. ((%16 ((%171 ((%199 $3) $2)) ((%199 $1) $0))) ((%8 ((%507
       $3) $1)) ((%11 $2) $0)))))))))))) ((%8 (%9 (\%134. (%84 (\%158. (%9
       (\%505. (%84 (\%510. ((%16 ((%171 ((%200 $3) $2)) ((%200 $1) $0)))
       ((%8 ((%11 $3) $1)) ((%86 $2) $0)))))))))))) ((%8 (%9 (\%134. (%9
       (\%156. (%84 (\%161. (%9 (\%505. (%9 (\%509. (%84 (\%511. ((%16
       ((%171 (((%201 $5) $4) $3)) (((%201 $2) $1) $0))) ((%8 ((%11 $5)
       $2)) ((%8 ((%11 $4) $1)) ((%86 $3) $0))))))))))))))))) ((%8 (%9
       (\%134. (%9 (\%156. (%84 (\%161. (%9 (\%505. (%9 (\%509. (%84
       (\%511. ((%16 ((%171 (((%202 $5) $4) $3)) (((%202 $2) $1) $0))) ((%8
       ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%86 $3) $0)))))))))))))))))
       ((%8 (%9 (\%134. (%9 (\%156. (%84 (\%161. (%9 (\%505. (%9 (\%509.
       (%84 (\%511. ((%16 ((%171 (((%203 $5) $4) $3)) (((%203 $2) $1) $0)))
       ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%86 $3)
       $0))))))))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%9 (\%162. (%9
       (\%505. (%9 (\%509. (%9 (\%512. ((%16 ((%171 (((%204 $5) $4) $3))
       (((%204 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%11
       $3) $0))))))))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84 (\%161.
       (%9 (\%505. (%9 (\%509. (%84 (\%511. ((%16 ((%171 (((%205 $5) $4)
       $3)) (((%205 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1))
       ((%86 $3) $0))))))))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84
       (\%161. (%9 (\%505. (%9 (\%509. (%84 (\%511. ((%16 ((%171 (((%206
       $5) $4) $3)) (((%206 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11
       $4) $1)) ((%86 $3) $0))))))))))))))))) ((%8 (%9 (\%134. (%9 (\%156.
       (%84 (\%161. (%9 (\%505. (%9 (\%509. (%84 (\%511. ((%16 ((%171
       (((%207 $5) $4) $3)) (((%207 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8
       ((%11 $4) $1)) ((%86 $3) $0))))))))))))))))) ((%8 (%9 (\%134. (%9
       (\%156. (%239 (\%164. (%9 (\%505. (%9 (\%509. (%239 (\%513. ((%16
       ((%171 (((%208 $5) $4) $3)) (((%208 $2) $1) $0))) ((%8 ((%11 $5)
       $2)) ((%8 ((%11 $4) $1)) ((%514 $3) $0))))))))))))))))) ((%8 (%9
       (\%134. (%9 (\%156. (%239 (\%164. (%9 (\%505. (%9 (\%509. (%239
       (\%513. ((%16 ((%171 (((%209 $5) $4) $3)) (((%209 $2) $1) $0))) ((%8
       ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%514 $3) $0)))))))))))))))))
       ((%8 (%9 (\%134. (%9 (\%156. (%239 (\%164. (%9 (\%505. (%9 (\%509.
       (%239 (\%513. ((%16 ((%171 (((%210 $5) $4) $3)) (((%210 $2) $1)
       $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%514 $3)
       $0))))))))))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239 (\%164. (%9
       (\%505. (%9 (\%509. (%239 (\%513. ((%16 ((%171 (((%211 $5) $4) $3))
       (((%211 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%514
       $3) $0))))))))))))))))) ((%8 (%14 (\%166. (%240 (\%168. (%14 (\%515.
       (%240 (\%516. ((%16 ((%171 ((%212 $3) $2)) ((%212 $1) $0))) ((%8
       ((%17 $3) $1)) ((%517 $2) $0)))))))))))) (%14 (\%166. (%240 (\%168.
       (%14 (\%515. (%240 (\%516. ((%16 ((%171 ((%213 $3) $2)) ((%213 $1)
       $0))) ((%8 ((%17 $3) $1)) ((%517 $2) $0))))))))))))))))))))))))))`)
  val DOPER_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%509. (%237 (\%136. (%237 (\%508. (%9 (\%134. (%452
       ((%171 ((%198 $0) $2)) ((%199 $1) $3)))))))))))) ((%8 (%84 (\%510.
       (%237 (\%136. (%9 (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2))
       ((%200 $1) $3)))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%237
       (\%136. (%9 (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%201
       $1) $3) $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%237 (\%136.
       (%9 (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%202 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%237 (\%136. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%203 $1) $3)
       $4)))))))))))))) ((%8 (%9 (\%162. (%9 (\%509. (%237 (\%136. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%204 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%237 (\%136. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%205 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%237 (\%136. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%206 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%237 (\%136. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%207 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%237 (\%136. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%208 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%237 (\%136. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%209 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%237 (\%136. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%210 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%237 (\%136. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%198 $0) $2)) (((%211 $1) $3)
       $4)))))))))))))) ((%8 (%240 (\%516. (%237 (\%136. (%14 (\%515. (%9
       (\%134. (%452 ((%171 ((%198 $0) $2)) ((%212 $1) $3)))))))))))) ((%8
       (%240 (\%516. (%237 (\%136. (%14 (\%515. (%9 (\%134. (%452 ((%171
       ((%198 $0) $2)) ((%213 $1) $3)))))))))))) ((%8 (%84 (\%510. (%9
       (\%156. (%9 (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2))
       ((%200 $1) $3)))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%9 (\%156.
       (%9 (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%201 $1)
       $3) $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%202 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%203 $1) $3)
       $4)))))))))))))) ((%8 (%9 (\%162. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%204 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%205 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%206 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%207 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%208 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%209 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%210 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%9 (\%156. (%9
       (\%505. (%237 (\%155. (%452 ((%171 ((%199 $0) $2)) (((%211 $1) $3)
       $4)))))))))))))) ((%8 (%240 (\%516. (%9 (\%156. (%14 (\%515. (%237
       (\%155. (%452 ((%171 ((%199 $0) $2)) ((%212 $1) $3)))))))))))) ((%8
       (%240 (\%516. (%9 (\%156. (%14 (\%515. (%237 (\%155. (%452 ((%171
       ((%199 $0) $2)) ((%213 $1) $3)))))))))))) ((%8 (%84 (\%161. (%9
       (\%509. (%84 (\%158. (%9 (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0)
       $2)) (((%201 $1) $3) $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509.
       (%84 (\%158. (%9 (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2))
       (((%202 $1) $3) $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%84
       (\%158. (%9 (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2)) (((%203
       $1) $3) $4)))))))))))))) ((%8 (%9 (\%162. (%9 (\%509. (%84 (\%158.
       (%9 (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2)) (((%204 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%84 (\%158. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2)) (((%205 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%84 (\%158. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2)) (((%206 $1) $3)
       $4)))))))))))))) ((%8 (%84 (\%161. (%9 (\%509. (%84 (\%158. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2)) (((%207 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%84 (\%158. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2)) (((%208 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%84 (\%158. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2)) (((%209 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%84 (\%158. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2)) (((%210 $1) $3)
       $4)))))))))))))) ((%8 (%239 (\%164. (%9 (\%509. (%84 (\%158. (%9
       (\%505. (%9 (\%134. (%452 ((%171 ((%200 $0) $2)) (((%211 $1) $3)
       $4)))))))))))))) ((%8 (%240 (\%516. (%84 (\%158. (%14 (\%515. (%9
       (\%134. (%452 ((%171 ((%200 $0) $2)) ((%212 $1) $3)))))))))))) ((%8
       (%240 (\%516. (%84 (\%158. (%14 (\%515. (%9 (\%134. (%452 ((%171
       ((%200 $0) $2)) ((%213 $1) $3)))))))))))) ((%8 (%84 (\%511. (%84
       (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171
       (((%201 $0) $2) $4)) (((%202 $1) $3) $5)))))))))))))))) ((%8 (%84
       (\%511. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134.
       (%452 ((%171 (((%201 $0) $2) $4)) (((%203 $1) $3) $5))))))))))))))))
       ((%8 (%9 (\%512. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505.
       (%9 (\%134. (%452 ((%171 (((%201 $0) $2) $4)) (((%204 $1) $3)
       $5)))))))))))))))) ((%8 (%84 (\%511. (%84 (\%161. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%201 $0) $2) $4))
       (((%205 $1) $3) $5)))))))))))))))) ((%8 (%84 (\%511. (%84 (\%161.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%201
       $0) $2) $4)) (((%206 $1) $3) $5)))))))))))))))) ((%8 (%84 (\%511.
       (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%201 $0) $2) $4)) (((%207 $1) $3) $5)))))))))))))))) ((%8
       (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%201 $0) $2) $4)) (((%208 $1) $3)
       $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%201 $0) $2) $4))
       (((%209 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%201
       $0) $2) $4)) (((%210 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513.
       (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%201 $0) $2) $4)) (((%211 $1) $3) $5)))))))))))))))) ((%8
       (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134.
       (%452 ((%171 (((%201 $0) $2) $4)) ((%212 $1) $3)))))))))))))) ((%8
       (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134.
       (%452 ((%171 (((%201 $0) $2) $4)) ((%213 $1) $3)))))))))))))) ((%8
       (%84 (\%511. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%202 $0) $2) $4)) (((%203 $1) $3)
       $5)))))))))))))))) ((%8 (%9 (\%512. (%84 (\%161. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%202 $0) $2) $4))
       (((%204 $1) $3) $5)))))))))))))))) ((%8 (%84 (\%511. (%84 (\%161.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%202
       $0) $2) $4)) (((%205 $1) $3) $5)))))))))))))))) ((%8 (%84 (\%511.
       (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%202 $0) $2) $4)) (((%206 $1) $3) $5)))))))))))))))) ((%8
       (%84 (\%511. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%202 $0) $2) $4)) (((%207 $1) $3)
       $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%202 $0) $2) $4))
       (((%208 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%202
       $0) $2) $4)) (((%209 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513.
       (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%202 $0) $2) $4)) (((%210 $1) $3) $5)))))))))))))))) ((%8
       (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%202 $0) $2) $4)) (((%211 $1) $3)
       $5)))))))))))))))) ((%8 (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14
       (\%515. (%9 (\%134. (%452 ((%171 (((%202 $0) $2) $4)) ((%212 $1)
       $3)))))))))))))) ((%8 (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14
       (\%515. (%9 (\%134. (%452 ((%171 (((%202 $0) $2) $4)) ((%213 $1)
       $3)))))))))))))) ((%8 (%9 (\%512. (%84 (\%161. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%203 $0) $2) $4))
       (((%204 $1) $3) $5)))))))))))))))) ((%8 (%84 (\%511. (%84 (\%161.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%203
       $0) $2) $4)) (((%205 $1) $3) $5)))))))))))))))) ((%8 (%84 (\%511.
       (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%203 $0) $2) $4)) (((%206 $1) $3) $5)))))))))))))))) ((%8
       (%84 (\%511. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%203 $0) $2) $4)) (((%207 $1) $3)
       $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%203 $0) $2) $4))
       (((%208 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%203
       $0) $2) $4)) (((%209 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513.
       (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%203 $0) $2) $4)) (((%210 $1) $3) $5)))))))))))))))) ((%8
       (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%203 $0) $2) $4)) (((%211 $1) $3)
       $5)))))))))))))))) ((%8 (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14
       (\%515. (%9 (\%134. (%452 ((%171 (((%203 $0) $2) $4)) ((%212 $1)
       $3)))))))))))))) ((%8 (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14
       (\%515. (%9 (\%134. (%452 ((%171 (((%203 $0) $2) $4)) ((%213 $1)
       $3)))))))))))))) ((%8 (%84 (\%511. (%9 (\%162. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%204 $0) $2) $4))
       (((%205 $1) $3) $5)))))))))))))))) ((%8 (%84 (\%511. (%9 (\%162. (%9
       (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%204 $0)
       $2) $4)) (((%206 $1) $3) $5)))))))))))))))) ((%8 (%84 (\%511. (%9
       (\%162. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171
       (((%204 $0) $2) $4)) (((%207 $1) $3) $5)))))))))))))))) ((%8 (%239
       (\%513. (%9 (\%162. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134.
       (%452 ((%171 (((%204 $0) $2) $4)) (((%208 $1) $3) $5))))))))))))))))
       ((%8 (%239 (\%513. (%9 (\%162. (%9 (\%509. (%9 (\%156. (%9 (\%505.
       (%9 (\%134. (%452 ((%171 (((%204 $0) $2) $4)) (((%209 $1) $3)
       $5)))))))))))))))) ((%8 (%239 (\%513. (%9 (\%162. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%204 $0) $2) $4))
       (((%210 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513. (%9 (\%162.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%204
       $0) $2) $4)) (((%211 $1) $3) $5)))))))))))))))) ((%8 (%9 (\%162.
       (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171
       (((%204 $0) $2) $4)) ((%212 $1) $3)))))))))))))) ((%8 (%9 (\%162.
       (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171
       (((%204 $0) $2) $4)) ((%213 $1) $3)))))))))))))) ((%8 (%84 (\%511.
       (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%205 $0) $2) $4)) (((%206 $1) $3) $5)))))))))))))))) ((%8
       (%84 (\%511. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%205 $0) $2) $4)) (((%207 $1) $3)
       $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%205 $0) $2) $4))
       (((%208 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%205
       $0) $2) $4)) (((%209 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513.
       (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%205 $0) $2) $4)) (((%210 $1) $3) $5)))))))))))))))) ((%8
       (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%205 $0) $2) $4)) (((%211 $1) $3)
       $5)))))))))))))))) ((%8 (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14
       (\%515. (%9 (\%134. (%452 ((%171 (((%205 $0) $2) $4)) ((%212 $1)
       $3)))))))))))))) ((%8 (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14
       (\%515. (%9 (\%134. (%452 ((%171 (((%205 $0) $2) $4)) ((%213 $1)
       $3)))))))))))))) ((%8 (%84 (\%511. (%84 (\%161. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%206 $0) $2) $4))
       (((%207 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%206
       $0) $2) $4)) (((%208 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513.
       (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%206 $0) $2) $4)) (((%209 $1) $3) $5)))))))))))))))) ((%8
       (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%206 $0) $2) $4)) (((%210 $1) $3)
       $5)))))))))))))))) ((%8 (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%206 $0) $2) $4))
       (((%211 $1) $3) $5)))))))))))))))) ((%8 (%84 (\%161. (%240 (\%516.
       (%9 (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171 (((%206 $0) $2)
       $4)) ((%212 $1) $3)))))))))))))) ((%8 (%84 (\%161. (%240 (\%516. (%9
       (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171 (((%206 $0) $2) $4))
       ((%213 $1) $3)))))))))))))) ((%8 (%239 (\%513. (%84 (\%161. (%9
       (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%207 $0)
       $2) $4)) (((%208 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513. (%84
       (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171
       (((%207 $0) $2) $4)) (((%209 $1) $3) $5)))))))))))))))) ((%8 (%239
       (\%513. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134.
       (%452 ((%171 (((%207 $0) $2) $4)) (((%210 $1) $3) $5))))))))))))))))
       ((%8 (%239 (\%513. (%84 (\%161. (%9 (\%509. (%9 (\%156. (%9 (\%505.
       (%9 (\%134. (%452 ((%171 (((%207 $0) $2) $4)) (((%211 $1) $3)
       $5)))))))))))))))) ((%8 (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14
       (\%515. (%9 (\%134. (%452 ((%171 (((%207 $0) $2) $4)) ((%212 $1)
       $3)))))))))))))) ((%8 (%84 (\%161. (%240 (\%516. (%9 (\%156. (%14
       (\%515. (%9 (\%134. (%452 ((%171 (((%207 $0) $2) $4)) ((%213 $1)
       $3)))))))))))))) ((%8 (%239 (\%513. (%239 (\%164. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%208 $0) $2) $4))
       (((%209 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513. (%239 (\%164.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%208
       $0) $2) $4)) (((%210 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%513.
       (%239 (\%164. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452
       ((%171 (((%208 $0) $2) $4)) (((%211 $1) $3) $5)))))))))))))))) ((%8
       (%239 (\%164. (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134.
       (%452 ((%171 (((%208 $0) $2) $4)) ((%212 $1) $3)))))))))))))) ((%8
       (%239 (\%164. (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134.
       (%452 ((%171 (((%208 $0) $2) $4)) ((%213 $1) $3)))))))))))))) ((%8
       (%239 (\%513. (%239 (\%164. (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9
       (\%134. (%452 ((%171 (((%209 $0) $2) $4)) (((%210 $1) $3)
       $5)))))))))))))))) ((%8 (%239 (\%513. (%239 (\%164. (%9 (\%509. (%9
       (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%209 $0) $2) $4))
       (((%211 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%164. (%240 (\%516.
       (%9 (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171 (((%209 $0) $2)
       $4)) ((%212 $1) $3)))))))))))))) ((%8 (%239 (\%164. (%240 (\%516.
       (%9 (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171 (((%209 $0) $2)
       $4)) ((%213 $1) $3)))))))))))))) ((%8 (%239 (\%513. (%239 (\%164.
       (%9 (\%509. (%9 (\%156. (%9 (\%505. (%9 (\%134. (%452 ((%171 (((%210
       $0) $2) $4)) (((%211 $1) $3) $5)))))))))))))))) ((%8 (%239 (\%164.
       (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171
       (((%210 $0) $2) $4)) ((%212 $1) $3)))))))))))))) ((%8 (%239 (\%164.
       (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171
       (((%210 $0) $2) $4)) ((%213 $1) $3)))))))))))))) ((%8 (%239 (\%164.
       (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171
       (((%211 $0) $2) $4)) ((%212 $1) $3)))))))))))))) ((%8 (%239 (\%164.
       (%240 (\%516. (%9 (\%156. (%14 (\%515. (%9 (\%134. (%452 ((%171
       (((%211 $0) $2) $4)) ((%213 $1) $3)))))))))))))) (%240 (\%516. (%240
       (\%168. (%14 (\%515. (%14 (\%166. (%452 ((%171 ((%212 $0) $2))
       ((%213 $1)
       $3))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val DOPER_case_cong =
    DT(["DISK_THM"], [],
       `(%169 (\%518. (%169 (\%519. (%214 (\%215. (%216 (\%217. (%218
       (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223. (%224 (\%225.
       (%220 (\%226. (%220 (\%227. (%220 (\%228. (%229 (\%230. (%229
       (\%231. (%229 (\%232. (%229 (\%233. (%234 (\%235. (%234 (\%236.
       ((%63 ((%8 ((%171 $17) $16)) ((%8 (%9 (\%134. (%237 (\%136. ((%63
       ((%171 $18) ((%198 $1) $0))) ((%53 (($17 $1) $0)) ((%520 $1)
       $0)))))))) ((%8 (%237 (\%155. (%9 (\%156. ((%63 ((%171 $18) ((%199
       $1) $0))) ((%53 (($16 $1) $0)) ((%521 $1) $0)))))))) ((%8 (%9
       (\%134. (%84 (\%158. ((%63 ((%171 $18) ((%200 $1) $0))) ((%53 (($15
       $1) $0)) ((%522 $1) $0)))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84
       (\%161. ((%63 ((%171 $19) (((%201 $2) $1) $0))) ((%53 ((($15 $2) $1)
       $0)) (((%523 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84
       (\%161. ((%63 ((%171 $19) (((%202 $2) $1) $0))) ((%53 ((($14 $2) $1)
       $0)) (((%524 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84
       (\%161. ((%63 ((%171 $19) (((%203 $2) $1) $0))) ((%53 ((($13 $2) $1)
       $0)) (((%525 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%9
       (\%162. ((%63 ((%171 $19) (((%204 $2) $1) $0))) ((%53 ((($12 $2) $1)
       $0)) (((%526 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84
       (\%161. ((%63 ((%171 $19) (((%205 $2) $1) $0))) ((%53 ((($11 $2) $1)
       $0)) (((%527 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84
       (\%161. ((%63 ((%171 $19) (((%206 $2) $1) $0))) ((%53 ((($10 $2) $1)
       $0)) (((%528 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84
       (\%161. ((%63 ((%171 $19) (((%207 $2) $1) $0))) ((%53 ((($9 $2) $1)
       $0)) (((%529 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239
       (\%164. ((%63 ((%171 $19) (((%208 $2) $1) $0))) ((%53 ((($8 $2) $1)
       $0)) (((%530 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239
       (\%164. ((%63 ((%171 $19) (((%209 $2) $1) $0))) ((%53 ((($7 $2) $1)
       $0)) (((%531 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239
       (\%164. ((%63 ((%171 $19) (((%210 $2) $1) $0))) ((%53 ((($6 $2) $1)
       $0)) (((%532 $2) $1) $0)))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239
       (\%164. ((%63 ((%171 $19) (((%211 $2) $1) $0))) ((%53 ((($5 $2) $1)
       $0)) (((%533 $2) $1) $0)))))))))) ((%8 (%14 (\%166. (%240 (\%168.
       ((%63 ((%171 $18) ((%212 $1) $0))) ((%53 (($3 $1) $0)) ((%534 $1)
       $0)))))))) (%14 (\%166. (%240 (\%168. ((%63 ((%171 $18) ((%213 $1)
       $0))) ((%53 (($2 $1) $0)) ((%535 $1) $0))))))))))))))))))))))))
       ((%53 (((((((((((((((((%238 $15) $14) $13) $12) $11) $10) $9) $8)
       $7) $6) $5) $4) $3) $2) $1) $0) $17)) (((((((((((((((((%238 %520)
       %521) %522) %523) %524) %525) %526) %527) %528) %529) %530) %531)
       %532) %533) %534) %535) $16)))))))))))))))))))))))))))))))))))))))`)
  val DOPER_nchotomy =
    DT(["DISK_THM"], [],
       `(%169 (\%536. ((%65 (%66 (\%453. (%135 (\%537. ((%171 $2) ((%198
       $1) $0))))))) ((%65 (%135 (\%537. (%66 (\%453. ((%171 $2) ((%199 $1)
       $0))))))) ((%65 (%66 (\%453. (%157 (\%538. ((%171 $2) ((%200 $1)
       $0))))))) ((%65 (%66 (\%453. (%66 (\%539. (%157 (\%540. ((%171 $3)
       (((%201 $2) $1) $0))))))))) ((%65 (%66 (\%453. (%66 (\%539. (%157
       (\%540. ((%171 $3) (((%202 $2) $1) $0))))))))) ((%65 (%66 (\%453.
       (%66 (\%539. (%157 (\%540. ((%171 $3) (((%203 $2) $1) $0)))))))))
       ((%65 (%66 (\%453. (%66 (\%539. (%66 (\%541. ((%171 $3) (((%204 $2)
       $1) $0))))))))) ((%65 (%66 (\%453. (%66 (\%539. (%157 (\%540. ((%171
       $3) (((%205 $2) $1) $0))))))))) ((%65 (%66 (\%453. (%66 (\%539.
       (%157 (\%540. ((%171 $3) (((%206 $2) $1) $0))))))))) ((%65 (%66
       (\%453. (%66 (\%539. (%157 (\%540. ((%171 $3) (((%207 $2) $1)
       $0))))))))) ((%65 (%66 (\%453. (%66 (\%539. (%163 (\%542. ((%171 $3)
       (((%208 $2) $1) $0))))))))) ((%65 (%66 (\%453. (%66 (\%539. (%163
       (\%542. ((%171 $3) (((%209 $2) $1) $0))))))))) ((%65 (%66 (\%453.
       (%66 (\%539. (%163 (\%542. ((%171 $3) (((%210 $2) $1) $0)))))))))
       ((%65 (%66 (\%453. (%66 (\%539. (%163 (\%542. ((%171 $3) (((%211 $2)
       $1) $0))))))))) ((%65 (%165 (\%3. (%167 (\%543. ((%171 $2) ((%212
       $1) $0))))))) (%165 (\%3. (%167 (\%543. ((%171 $2) ((%213 $1)
       $0)))))))))))))))))))))))`)
  val DOPER_Axiom =
    DT(["DISK_THM"], [],
       `(%214 (\%544. (%216 (\%217. (%218 (\%219. (%220 (\%221. (%220
       (\%222. (%220 (\%223. (%224 (\%225. (%220 (\%226. (%220 (\%227.
       (%220 (\%228. (%229 (\%230. (%229 (\%231. (%229 (\%232. (%229
       (\%233. (%234 (\%235. (%234 (\%236. (%545 (\%546. ((%8 (%9 (\%134.
       (%237 (\%136. ((%53 ($2 ((%198 $1) $0))) (($18 $1) $0))))))) ((%8
       (%237 (\%155. (%9 (\%156. ((%53 ($2 ((%199 $1) $0))) (($17 $1)
       $0))))))) ((%8 (%9 (\%134. (%84 (\%158. ((%53 ($2 ((%200 $1) $0)))
       (($16 $1) $0))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84 (\%161. ((%53
       ($3 (((%201 $2) $1) $0))) ((($16 $2) $1) $0))))))))) ((%8 (%9
       (\%134. (%9 (\%156. (%84 (\%161. ((%53 ($3 (((%202 $2) $1) $0)))
       ((($15 $2) $1) $0))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84 (\%161.
       ((%53 ($3 (((%203 $2) $1) $0))) ((($14 $2) $1) $0))))))))) ((%8 (%9
       (\%134. (%9 (\%156. (%9 (\%162. ((%53 ($3 (((%204 $2) $1) $0)))
       ((($13 $2) $1) $0))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84 (\%161.
       ((%53 ($3 (((%205 $2) $1) $0))) ((($12 $2) $1) $0))))))))) ((%8 (%9
       (\%134. (%9 (\%156. (%84 (\%161. ((%53 ($3 (((%206 $2) $1) $0)))
       ((($11 $2) $1) $0))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%84 (\%161.
       ((%53 ($3 (((%207 $2) $1) $0))) ((($10 $2) $1) $0))))))))) ((%8 (%9
       (\%134. (%9 (\%156. (%239 (\%164. ((%53 ($3 (((%208 $2) $1) $0)))
       ((($9 $2) $1) $0))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239 (\%164.
       ((%53 ($3 (((%209 $2) $1) $0))) ((($8 $2) $1) $0))))))))) ((%8 (%9
       (\%134. (%9 (\%156. (%239 (\%164. ((%53 ($3 (((%210 $2) $1) $0)))
       ((($7 $2) $1) $0))))))))) ((%8 (%9 (\%134. (%9 (\%156. (%239 (\%164.
       ((%53 ($3 (((%211 $2) $1) $0))) ((($6 $2) $1) $0))))))))) ((%8 (%14
       (\%166. (%240 (\%168. ((%53 ($2 ((%212 $1) $0))) (($4 $1) $0)))))))
       (%14 (\%166. (%240 (\%168. ((%53 ($2 ((%213 $1) $0))) (($3 $1)
       $0)))))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val DOPER_induction =
    DT(["DISK_THM"], [],
       `(%547 (\%548. ((%63 ((%8 (%9 (\%453. (%237 (\%537. ($2 ((%198 $1)
       $0))))))) ((%8 (%237 (\%537. (%9 (\%453. ($2 ((%199 $1) $0)))))))
       ((%8 (%9 (\%453. (%84 (\%538. ($2 ((%200 $1) $0))))))) ((%8 (%9
       (\%453. (%9 (\%539. (%84 (\%540. ($3 (((%201 $2) $1) $0)))))))))
       ((%8 (%9 (\%453. (%9 (\%539. (%84 (\%540. ($3 (((%202 $2) $1)
       $0))))))))) ((%8 (%9 (\%453. (%9 (\%539. (%84 (\%540. ($3 (((%203
       $2) $1) $0))))))))) ((%8 (%9 (\%453. (%9 (\%539. (%9 (\%541. ($3
       (((%204 $2) $1) $0))))))))) ((%8 (%9 (\%453. (%9 (\%539. (%84
       (\%540. ($3 (((%205 $2) $1) $0))))))))) ((%8 (%9 (\%453. (%9 (\%539.
       (%84 (\%540. ($3 (((%206 $2) $1) $0))))))))) ((%8 (%9 (\%453. (%9
       (\%539. (%84 (\%540. ($3 (((%207 $2) $1) $0))))))))) ((%8 (%9
       (\%453. (%9 (\%539. (%239 (\%542. ($3 (((%208 $2) $1) $0)))))))))
       ((%8 (%9 (\%453. (%9 (\%539. (%239 (\%542. ($3 (((%209 $2) $1)
       $0))))))))) ((%8 (%9 (\%453. (%9 (\%539. (%239 (\%542. ($3 (((%210
       $2) $1) $0))))))))) ((%8 (%9 (\%453. (%9 (\%539. (%239 (\%542. ($3
       (((%211 $2) $1) $0))))))))) ((%8 (%14 (\%3. (%240 (\%543. ($2 ((%212
       $1) $0))))))) (%14 (\%3. (%240 (\%543. ($2 ((%213 $1)
       $0)))))))))))))))))))))) (%169 (\%536. ($1 $0))))))`)
  val datatype_CTL_STRUCTURE =
    DT(["DISK_THM"], [], `(%450 ((((%549 %288) %289) %290) %291))`)
  val CTL_STRUCTURE_11 =
    DT(["DISK_THM"], [],
       `((%8 (%300 (\%255. (%300 (\%550. ((%16 ((%273 (%288 $1)) (%288
       $0))) ((%551 $1) $0))))))) ((%8 (%271 (\%281. (%271 (\%282. (%271
       (\%552. (%271 (\%553. ((%16 ((%273 ((%289 $3) $2)) ((%289 $1) $0)))
       ((%8 ((%273 $3) $1)) ((%273 $2) $0)))))))))))) ((%8 (%302 (\%269.
       (%271 (\%282. (%271 (\%285. (%302 (\%554. (%271 (\%553. (%271
       (\%555. ((%16 ((%273 (((%290 $5) $4) $3)) (((%290 $2) $1) $0))) ((%8
       ((%556 $5) $2)) ((%8 ((%273 $4) $1)) ((%273 $3) $0)))))))))))))))))
       (%302 (\%269. (%271 (\%282. (%302 (\%554. (%271 (\%553. ((%16 ((%273
       ((%291 $3) $2)) ((%291 $1) $0))) ((%8 ((%556 $3) $1)) ((%273 $2)
       $0))))))))))))))`)
  val CTL_STRUCTURE_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%271 (\%282. (%271 (\%281. (%300 (\%255. (%452 ((%273 (%288
       $0)) ((%289 $1) $2)))))))))) ((%8 (%271 (\%285. (%271 (\%282. (%302
       (\%269. (%300 (\%255. (%452 ((%273 (%288 $0)) (((%290 $1) $2)
       $3)))))))))))) ((%8 (%271 (\%282. (%302 (\%269. (%300 (\%255. (%452
       ((%273 (%288 $0)) ((%291 $1) $2)))))))))) ((%8 (%271 (\%285. (%271
       (\%553. (%271 (\%282. (%302 (\%554. (%271 (\%281. (%452 ((%273
       ((%289 $0) $2)) (((%290 $1) $3) $4)))))))))))))) ((%8 (%271 (\%553.
       (%271 (\%282. (%302 (\%554. (%271 (\%281. (%452 ((%273 ((%289 $0)
       $2)) ((%291 $1) $3)))))))))))) (%271 (\%285. (%271 (\%553. (%271
       (\%282. (%302 (\%554. (%302 (\%269. (%452 ((%273 (((%290 $0) $2)
       $4)) ((%291 $1) $3))))))))))))))))))`)
  val CTL_STRUCTURE_case_cong =
    DT(["DISK_THM"], [],
       `(%271 (\%557. (%271 (\%558. (%292 (\%293. (%294 (\%295. (%296
       (\%297. (%298 (\%299. ((%63 ((%8 ((%273 $5) $4)) ((%8 (%300 (\%255.
       ((%63 ((%273 $5) (%288 $0))) ((%53 ($4 $0)) (%559 $0)))))) ((%8
       (%271 (\%281. (%271 (\%282. ((%63 ((%273 $6) ((%289 $1) $0))) ((%53
       (($4 $1) $0)) ((%560 $1) $0)))))))) ((%8 (%302 (\%269. (%271 (\%282.
       (%271 (\%285. ((%63 ((%273 $7) (((%290 $2) $1) $0))) ((%53 ((($4 $2)
       $1) $0)) (((%561 $2) $1) $0)))))))))) (%302 (\%269. (%271 (\%282.
       ((%63 ((%273 $6) ((%291 $1) $0))) ((%53 (($2 $1) $0)) ((%562 $1)
       $0)))))))))))) ((%53 (((((%301 $3) $2) $1) $0) $5)) (((((%301 %559)
       %560) %561) %562) $4)))))))))))))))`)
  val CTL_STRUCTURE_nchotomy =
    DT(["DISK_THM"], [],
       `(%271 (\%563. ((%65 (%254 (\%564. ((%273 $1) (%288 $0))))) ((%65
       (%565 (\%563. (%565 (\%566. ((%273 $2) ((%289 $1) $0))))))) ((%65
       (%268 (\%567. (%565 (\%563. (%565 (\%566. ((%273 $3) (((%290 $2) $1)
       $0))))))))) (%268 (\%567. (%565 (\%563. ((%273 $2) ((%291 $1)
       $0)))))))))))`)
  val CTL_STRUCTURE_Axiom =
    DT(["DISK_THM"], [],
       `(%292 (\%568. (%569 (\%570. (%571 (\%572. (%573 (\%574. (%575
       (\%576. ((%8 (%300 (\%255. ((%53 ($1 (%288 $0))) ($5 $0))))) ((%8
       (%271 (\%281. (%271 (\%282. ((%53 ($2 ((%289 $1) $0))) (((($5 $1)
       $0) ($2 $1)) ($2 $0)))))))) ((%8 (%302 (\%269. (%271 (\%282. (%271
       (\%285. ((%53 ($3 (((%290 $2) $1) $0))) ((((($5 $2) $1) $0) ($3 $1))
       ($3 $0)))))))))) (%302 (\%269. (%271 (\%282. ((%53 ($2 ((%291 $1)
       $0))) ((($3 $1) $0) ($2 $0))))))))))))))))))))`)
  val CTL_STRUCTURE_induction =
    DT(["DISK_THM"], [],
       `(%577 (\%578. ((%63 ((%8 (%300 (\%564. ($1 (%288 $0))))) ((%8 (%271
       (\%563. (%271 (\%566. ((%63 ((%8 ($2 $1)) ($2 $0))) ($2 ((%289 $1)
       $0)))))))) ((%8 (%271 (\%563. (%271 (\%566. ((%63 ((%8 ($2 $1)) ($2
       $0))) (%302 (\%567. ($3 (((%290 $0) $2) $1)))))))))) (%271 (\%563.
       ((%63 ($1 $0)) (%302 (\%567. ($2 ((%291 $0) $1))))))))))) (%271
       (\%563. ($1 $0))))))`)
  val TRANSLATE_ASSIGMENT_CORRECT =
    DT(["DISK_THM"], [],
       `(%169 (\%405. (%14 (\%425. (%426 (\%427. (%311 (\%312. ((%579
       ((%433 (%81 $2)) ((%434 $1) ((%336 $0) $3)))) ((%580 ((%433 $2)
       ((%434 $1) $0))) (%355 $3)))))))))))`)
  val TRANSLATE_ASSIGMENT_CORRECT_2 =
    DT(["DISK_THM"], [],
       `(%169 (\%405. (%581 (\%582. ((%579 ((%580 $0) (%355 $1))) ((%433
       (%81 (%583 $0))) ((%434 (%584 (%585 $0))) ((%336 (%586 (%585 $0)))
       $1))))))))`)
  val translate_ind =
    DT(["DISK_THM"], [],
       `(%577 (\%578. ((%63 ((%8 (%169 (\%405. (%300 (\%406. ((%63 ($2
       (%288 $0))) ($2 (%288 ((%407 $1) $0))))))))) ((%8 ($0 (%288 %587)))
       ((%8 (%271 (\%408. (%271 (\%409. ((%63 ((%8 ($2 $1)) ($2 $0))) ($2
       ((%289 $1) $0)))))))) ((%8 (%302 (\%394. (%271 (\%411. (%271 (\%410.
       ((%63 ((%8 ($3 $0)) ($3 $1))) ($3 (((%290 $2) $1) $0)))))))))) (%302
       (\%394. (%271 (\%412. ((%63 ($2 $0)) ($2 ((%291 $1) $0))))))))))))
       (%271 (\%588. ($1 $0))))))`)
  val translate_def =
    DT(["DISK_THM"], [],
       `((%8 ((%589 (%400 (%288 ((%407 %405) %406)))) ((%418 (%355 %405))
       (%400 (%288 %406))))) ((%8 ((%589 (%400 (%288 %587))) %417)) ((%8
       ((%589 (%400 ((%289 %408) %409))) ((%419 (%400 %408)) (%400 %409))))
       ((%8 ((%589 (%400 (((%290 %394) %411) %410))) (((%420 (%398 %394))
       (%400 %411)) (%400 %410)))) ((%589 (%400 ((%291 %394) %412))) ((%422
       (%398 %394)) (%400 %412)))))))`)
  val WELL_FORMED_SUB_thm =
    DT(["DISK_THM"], [],
       `(%271 (\%439. ((%16 (%443 $0)) ((%8 (%447 $0)) (%444 (%400
       $0))))))`)
  val HOARE_SC_IR =
    DT(["DISK_THM"], [],
       `(%271 (\%590. (%271 (\%591. (%592 (\%593. (%592 (\%594. (%592
       (\%595. (%592 (\%596. ((%63 ((%8 (%443 $5)) ((%8 (%443 $4)) ((%8
       (%311 (\%312. ((%63 ($4 $0)) ($3 ((%440 $6) $0)))))) ((%8 (%311
       (\%312. ((%63 ($2 $0)) ($1 ((%440 $5) $0)))))) (%311 (\%312. ((%63
       ($3 $0)) ($2 $0))))))))) (%311 (\%312. ((%63 ($4 $0)) ($1 ((%440
       ((%289 $6) $5)) $0))))))))))))))))))`)
  val HOARE_CJ_IR =
    DT(["DISK_THM"], [],
       `(%302 (\%394. (%271 (\%597. (%271 (\%598. (%592 (\%593. (%592
       (\%594. (%592 (\%595. ((%63 ((%8 (%443 $4)) ((%8 (%443 $3)) ((%8
       (%311 (\%312. ((%63 ($3 $0)) ($2 ((%440 $5) $0)))))) (%311 (\%312.
       ((%63 ($3 $0)) ($1 ((%440 $4) $0))))))))) (%311 (\%312. ((%63 ($3
       $0)) (((%599 ((%396 $6) $0)) ($2 ((%440 (((%290 $6) $5) $4)) $0)))
       ($1 ((%440 (((%290 $6) $5) $4)) $0)))))))))))))))))))`)
  val HOARE_TR_IR =
    DT(["DISK_THM"], [],
       `(%302 (\%394. (%271 (\%439. (%592 (\%593. ((%63 ((%8 (%443 $1))
       ((%8 (%445 ((%446 (%398 $2)) (%400 $1)))) (%311 (\%312. ((%63 ($1
       $0)) ($1 ((%440 $2) $0)))))))) (%311 (\%312. ((%63 ($1 $0)) ((%8 ($1
       ((%440 ((%291 $3) $2)) $0))) ((%396 $3) ((%440 ((%291 $3) $2))
       $0)))))))))))))`)
  val UPLOAD_LEM_2 =
    DT(["DISK_THM"], [],
       `(%600 (\%601. (%602 (\%603. (%604 (\%605. ((%606 ((((%607 ((%608
       $1) %609)) $0) (%610 $2)) (%610 $2))) $1)))))))`)
  val STATEMENT_IS_WELL_FORMED =
    DT(["DISK_THM"], [], `(%169 (\%405. (%444 ((%418 (%355 $0)) %417))))`)
  val BLOCK_IS_WELL_FORMED =
    DT(["DISK_THM"], [], `(%300 (\%406. (%443 (%288 $0))))`)
  val IR_SC_IS_WELL_FORMED =
    DT(["DISK_THM"], [],
       `(%271 (\%590. (%271 (\%591. ((%16 ((%8 (%443 $1)) (%443 $0))) (%443
       ((%289 $1) $0)))))))`)
  val IR_CJ_IS_WELL_FORMED =
    DT(["DISK_THM"], [],
       `(%302 (\%394. (%271 (\%597. (%271 (\%598. ((%16 ((%8 (%443 $1))
       (%443 $0))) (%443 (((%290 $2) $1) $0)))))))))`)
  val IR_TR_IS_WELL_FORMED =
    DT(["DISK_THM"], [],
       `(%271 (\%439. (%302 (\%394. ((%16 ((%8 (%443 $1)) (%445 ((%446
       (%398 $0)) (%400 $1))))) (%443 ((%291 $0) $1)))))))`)
  val WELL_FORMED_thm =
    DT(["DISK_THM"], [],
       `((%8 ((%16 (%443 (%288 %406))) %73)) ((%8 ((%16 (%443 ((%289 %408)
       %409))) ((%8 (%443 %408)) (%443 %409)))) ((%8 ((%16 (%443 (((%290
       %394) %408) %409))) ((%8 (%443 %408)) (%443 %409)))) ((%16 (%443
       ((%291 %394) %408))) ((%8 (%443 %408)) (%445 ((%446 (%398 %394))
       (%400 %408))))))))`)
  val IR_SEMANTICS_SC =
    DT(["DISK_THM"], [],
       `((%63 ((%8 (%443 %590)) (%443 %591))) ((%315 ((%440 ((%289 %590)
       %591)) %312)) ((%440 %591) ((%440 %590) %312))))`)
  val IR_SEMANTICS_BLK =
    DT(["DISK_THM"], [],
       `((%8 ((%315 ((%440 (%288 ((%407 %405) %406))) %312)) ((%440 (%288
       %406)) ((%336 %312) %405)))) ((%315 ((%440 (%288 %587)) %312))
       %312))`)
  val IR_SEMANTICS_CJ =
    DT(["DISK_THM"], [],
       `((%63 ((%8 (%443 %597)) (%443 %598))) ((%315 ((%440 (((%290 %394)
       %597) %598)) %312)) (((%611 ((%396 %394) %312)) ((%440 %597) %312))
       ((%440 %598) %312))))`)
  val IR_SEMANTICS_TR =
    DT(["DISK_THM"], [],
       `((%63 ((%8 (%443 %439)) (%445 ((%446 (%398 %394)) (%400 %439)))))
       ((%315 ((%440 ((%291 %394) %439)) %312)) (((%612 (\%613. (%452
       ((%396 %394) $0)))) (%440 %439)) %312)))`)
  val SEMANTICS_OF_IR =
    DT(["DISK_THM"], [],
       `((%63 ((%8 (%443 %590)) (%443 %591))) ((%8 ((%315 ((%440 (%288
       ((%407 %405) %406))) %312)) ((%440 (%288 %406)) ((%336 %312)
       %405)))) ((%8 ((%315 ((%440 (%288 %587)) %312)) %312)) ((%8 ((%315
       ((%440 ((%289 %590) %591)) %312)) ((%440 %591) ((%440 %590) %312))))
       ((%8 ((%315 ((%440 (((%290 %394) %590) %591)) %312)) (((%611 ((%396
       %394) %312)) ((%440 %590) %312)) ((%440 %591) %312)))) ((%63 (%445
       ((%446 (%398 %394)) (%400 %590)))) ((%315 ((%440 ((%291 %394) %590))
       %312)) (((%612 (\%613. (%452 ((%396 %394) $0)))) (%440 %590))
       %312))))))))`)
  end
  val _ = DB.bindl "IL"
  [("MREG_TY_DEF",MREG_TY_DEF,DB.Def), ("MREG_BIJ",MREG_BIJ,DB.Def),
   ("R0",R0,DB.Def), ("R1",R1,DB.Def), ("R2",R2,DB.Def), ("R3",R3,DB.Def),
   ("R4",R4,DB.Def), ("R5",R5,DB.Def), ("R6",R6,DB.Def), ("R7",R7,DB.Def),
   ("R8",R8,DB.Def), ("R9",R9,DB.Def), ("R10",R10,DB.Def),
   ("R11",R11,DB.Def), ("R12",R12,DB.Def), ("R13",R13,DB.Def),
   ("R14",R14,DB.Def), ("MREG_size_def",MREG_size_def,DB.Def),
   ("MREG_case",MREG_case,DB.Def), ("MEXP_TY_DEF",MEXP_TY_DEF,DB.Def),
   ("MEXP_repfns",MEXP_repfns,DB.Def), ("IL0_def",IL0_def,DB.Def),
   ("IL1_def",IL1_def,DB.Def), ("MR",MR,DB.Def), ("MC",MC,DB.Def),
   ("MEXP_case_def",MEXP_case_def,DB.Def),
   ("MEXP_size_def",MEXP_size_def,DB.Def),
   ("index_of_reg_def",index_of_reg_def,DB.Def),
   ("from_reg_index_def",from_reg_index_def,DB.Def),
   ("toREG_def",toREG_def,DB.Def), ("toMEM_def",toMEM_def,DB.Def),
   ("toEXP_def",toEXP_def,DB.Def), ("DOPER_TY_DEF",DOPER_TY_DEF,DB.Def),
   ("DOPER_repfns",DOPER_repfns,DB.Def), ("IL2_def",IL2_def,DB.Def),
   ("IL3_def",IL3_def,DB.Def), ("IL4_def",IL4_def,DB.Def),
   ("IL5_def",IL5_def,DB.Def), ("IL6_def",IL6_def,DB.Def),
   ("IL7_def",IL7_def,DB.Def), ("IL8_def",IL8_def,DB.Def),
   ("IL9_def",IL9_def,DB.Def), ("IL10_def",IL10_def,DB.Def),
   ("IL11_def",IL11_def,DB.Def), ("IL12_def",IL12_def,DB.Def),
   ("IL13_def",IL13_def,DB.Def), ("IL14_def",IL14_def,DB.Def),
   ("IL15_def",IL15_def,DB.Def), ("IL16_def",IL16_def,DB.Def),
   ("IL17_def",IL17_def,DB.Def), ("MLDR",MLDR,DB.Def),
   ("MSTR",MSTR,DB.Def), ("MMOV",MMOV,DB.Def), ("MADD",MADD,DB.Def),
   ("MSUB",MSUB,DB.Def), ("MRSB",MRSB,DB.Def), ("MMUL",MMUL,DB.Def),
   ("MAND",MAND,DB.Def), ("MORR",MORR,DB.Def), ("MEOR",MEOR,DB.Def),
   ("MLSL",MLSL,DB.Def), ("MLSR",MLSR,DB.Def), ("MASR",MASR,DB.Def),
   ("MROR",MROR,DB.Def), ("MPUSH",MPUSH,DB.Def), ("MPOP",MPOP,DB.Def),
   ("DOPER_case_def",DOPER_case_def,DB.Def),
   ("DOPER_size_def",DOPER_size_def,DB.Def),
   ("CTL_STRUCTURE_TY_DEF",CTL_STRUCTURE_TY_DEF,DB.Def),
   ("CTL_STRUCTURE_repfns",CTL_STRUCTURE_repfns,DB.Def),
   ("IL18_def",IL18_def,DB.Def), ("IL19_def",IL19_def,DB.Def),
   ("IL20_def",IL20_def,DB.Def), ("IL21_def",IL21_def,DB.Def),
   ("BLK",BLK,DB.Def), ("SC",SC,DB.Def), ("CJ",CJ,DB.Def),
   ("TR",TR,DB.Def),
   ("CTL_STRUCTURE_case_def",CTL_STRUCTURE_case_def,DB.Def),
   ("CTL_STRUCTURE_size_def",CTL_STRUCTURE_size_def,DB.Def),
   ("pushL_def",pushL_def,DB.Def), ("popL_def",popL_def,DB.Def),
   ("mdecode_def",mdecode_def,DB.Def),
   ("translate_assignment_def",translate_assignment_def,DB.Def),
   ("translate_condition_def",translate_condition_def,DB.Def),
   ("eval_il_cond_def",eval_il_cond_def,DB.Def),
   ("translate_primitive_def",translate_primitive_def,DB.Def),
   ("run_arm_def",run_arm_def,DB.Def), ("run_ir_def",run_ir_def,DB.Def),
   ("WELL_FORMED_def",WELL_FORMED_def,DB.Def),
   ("WELL_FORMED_SUB_def",WELL_FORMED_SUB_def,DB.Def),
   ("num2MREG_MREG2num",num2MREG_MREG2num,DB.Thm),
   ("MREG2num_num2MREG",MREG2num_num2MREG,DB.Thm),
   ("num2MREG_11",num2MREG_11,DB.Thm), ("MREG2num_11",MREG2num_11,DB.Thm),
   ("num2MREG_ONTO",num2MREG_ONTO,DB.Thm),
   ("MREG2num_ONTO",MREG2num_ONTO,DB.Thm),
   ("num2MREG_thm",num2MREG_thm,DB.Thm),
   ("MREG2num_thm",MREG2num_thm,DB.Thm),
   ("MREG_EQ_MREG",MREG_EQ_MREG,DB.Thm),
   ("MREG_case_def",MREG_case_def,DB.Thm),
   ("datatype_MREG",datatype_MREG,DB.Thm),
   ("MREG_distinct",MREG_distinct,DB.Thm),
   ("MREG_case_cong",MREG_case_cong,DB.Thm),
   ("MREG_nchotomy",MREG_nchotomy,DB.Thm),
   ("MREG_Axiom",MREG_Axiom,DB.Thm),
   ("MREG_induction",MREG_induction,DB.Thm),
   ("datatype_MEXP",datatype_MEXP,DB.Thm), ("MEXP_11",MEXP_11,DB.Thm),
   ("MEXP_distinct",MEXP_distinct,DB.Thm),
   ("MEXP_case_cong",MEXP_case_cong,DB.Thm),
   ("MEXP_nchotomy",MEXP_nchotomy,DB.Thm),
   ("MEXP_Axiom",MEXP_Axiom,DB.Thm),
   ("MEXP_induction",MEXP_induction,DB.Thm),
   ("from_reg_index_thm",from_reg_index_thm,DB.Thm),
   ("datatype_DOPER",datatype_DOPER,DB.Thm), ("DOPER_11",DOPER_11,DB.Thm),
   ("DOPER_distinct",DOPER_distinct,DB.Thm),
   ("DOPER_case_cong",DOPER_case_cong,DB.Thm),
   ("DOPER_nchotomy",DOPER_nchotomy,DB.Thm),
   ("DOPER_Axiom",DOPER_Axiom,DB.Thm),
   ("DOPER_induction",DOPER_induction,DB.Thm),
   ("datatype_CTL_STRUCTURE",datatype_CTL_STRUCTURE,DB.Thm),
   ("CTL_STRUCTURE_11",CTL_STRUCTURE_11,DB.Thm),
   ("CTL_STRUCTURE_distinct",CTL_STRUCTURE_distinct,DB.Thm),
   ("CTL_STRUCTURE_case_cong",CTL_STRUCTURE_case_cong,DB.Thm),
   ("CTL_STRUCTURE_nchotomy",CTL_STRUCTURE_nchotomy,DB.Thm),
   ("CTL_STRUCTURE_Axiom",CTL_STRUCTURE_Axiom,DB.Thm),
   ("CTL_STRUCTURE_induction",CTL_STRUCTURE_induction,DB.Thm),
   ("TRANSLATE_ASSIGMENT_CORRECT",TRANSLATE_ASSIGMENT_CORRECT,DB.Thm),
   ("TRANSLATE_ASSIGMENT_CORRECT_2",TRANSLATE_ASSIGMENT_CORRECT_2,DB.Thm),
   ("translate_ind",translate_ind,DB.Thm),
   ("translate_def",translate_def,DB.Thm),
   ("WELL_FORMED_SUB_thm",WELL_FORMED_SUB_thm,DB.Thm),
   ("HOARE_SC_IR",HOARE_SC_IR,DB.Thm), ("HOARE_CJ_IR",HOARE_CJ_IR,DB.Thm),
   ("HOARE_TR_IR",HOARE_TR_IR,DB.Thm),
   ("UPLOAD_LEM_2",UPLOAD_LEM_2,DB.Thm),
   ("STATEMENT_IS_WELL_FORMED",STATEMENT_IS_WELL_FORMED,DB.Thm),
   ("BLOCK_IS_WELL_FORMED",BLOCK_IS_WELL_FORMED,DB.Thm),
   ("IR_SC_IS_WELL_FORMED",IR_SC_IS_WELL_FORMED,DB.Thm),
   ("IR_CJ_IS_WELL_FORMED",IR_CJ_IS_WELL_FORMED,DB.Thm),
   ("IR_TR_IS_WELL_FORMED",IR_TR_IS_WELL_FORMED,DB.Thm),
   ("WELL_FORMED_thm",WELL_FORMED_thm,DB.Thm),
   ("IR_SEMANTICS_SC",IR_SEMANTICS_SC,DB.Thm),
   ("IR_SEMANTICS_BLK",IR_SEMANTICS_BLK,DB.Thm),
   ("IR_SEMANTICS_CJ",IR_SEMANTICS_CJ,DB.Thm),
   ("IR_SEMANTICS_TR",IR_SEMANTICS_TR,DB.Thm),
   ("SEMANTICS_OF_IR",SEMANTICS_OF_IR,DB.Thm)]

  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("ARMCompositionTheory.ARMComposition_grammars",
                          ARMCompositionTheory.ARMComposition_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms temp_add_type "MREG"
  val _ = update_grms
       (temp_overload_on_by_nametype "MREG2num")
        {Name = "MREG2num", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "num2MREG")
        {Name = "num2MREG", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R0")
        {Name = "R0", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R1")
        {Name = "R1", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R2")
        {Name = "R2", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R3")
        {Name = "R3", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R4")
        {Name = "R4", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R5")
        {Name = "R5", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R6")
        {Name = "R6", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R7")
        {Name = "R7", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R8")
        {Name = "R8", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R9")
        {Name = "R9", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R10")
        {Name = "R10", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R11")
        {Name = "R11", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R12")
        {Name = "R12", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R13")
        {Name = "R13", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R14")
        {Name = "R14", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MREG_size")
        {Name = "MREG_size", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MREG_case")
        {Name = "MREG_case", Thy = "IL"}
  val _ = update_grms
       temp_type_abbrev
       ("MMEM", T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []])
  val _ = update_grms temp_add_type "MEXP"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_MEXP")
        {Name = "dest_MEXP", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_MEXP")
        {Name = "mk_MEXP", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL0")
        {Name = "IL0", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL1")
        {Name = "IL1", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MR")
        {Name = "MR", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MC")
        {Name = "MC", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MEXP_case")
        {Name = "MEXP_case", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MEXP_size")
        {Name = "MEXP_size", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "index_of_reg")
        {Name = "index_of_reg", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "from_reg_index")
        {Name = "from_reg_index", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "toREG")
        {Name = "toREG", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "toMEM")
        {Name = "toMEM", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "toEXP")
        {Name = "toEXP", Thy = "IL"}
  val _ = update_grms temp_add_type "DOPER"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_DOPER")
        {Name = "dest_DOPER", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_DOPER")
        {Name = "mk_DOPER", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL2")
        {Name = "IL2", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL3")
        {Name = "IL3", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL4")
        {Name = "IL4", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL5")
        {Name = "IL5", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL6")
        {Name = "IL6", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL7")
        {Name = "IL7", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL8")
        {Name = "IL8", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL9")
        {Name = "IL9", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL10")
        {Name = "IL10", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL11")
        {Name = "IL11", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL12")
        {Name = "IL12", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL13")
        {Name = "IL13", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL14")
        {Name = "IL14", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL15")
        {Name = "IL15", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL16")
        {Name = "IL16", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL17")
        {Name = "IL17", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MLDR")
        {Name = "MLDR", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MSTR")
        {Name = "MSTR", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MMOV")
        {Name = "MMOV", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MADD")
        {Name = "MADD", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MSUB")
        {Name = "MSUB", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MRSB")
        {Name = "MRSB", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MMUL")
        {Name = "MMUL", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MAND")
        {Name = "MAND", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MORR")
        {Name = "MORR", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MEOR")
        {Name = "MEOR", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MLSL")
        {Name = "MLSL", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MLSR")
        {Name = "MLSR", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MASR")
        {Name = "MASR", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MROR")
        {Name = "MROR", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MPUSH")
        {Name = "MPUSH", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MPOP")
        {Name = "MPOP", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "DOPER_case")
        {Name = "DOPER_case", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "DOPER_size")
        {Name = "DOPER_size", Thy = "IL"}
  val _ = update_grms
       temp_type_abbrev
       ("CEXP", T"prod" "pair"
 [T"MREG" "IL" [],
  T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "IL" []]])
  val _ = update_grms temp_add_type "CTL_STRUCTURE"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_CTL_STRUCTURE")
        {Name = "dest_CTL_STRUCTURE", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_CTL_STRUCTURE")
        {Name = "mk_CTL_STRUCTURE", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL18")
        {Name = "IL18", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL19")
        {Name = "IL19", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL20")
        {Name = "IL20", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IL21")
        {Name = "IL21", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "BLK")
        {Name = "BLK", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SC")
        {Name = "SC", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CJ")
        {Name = "CJ", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TR")
        {Name = "TR", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CTL_STRUCTURE_case")
        {Name = "CTL_STRUCTURE_case", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CTL_STRUCTURE_size")
        {Name = "CTL_STRUCTURE_size", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "pushL")
        {Name = "pushL", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "popL")
        {Name = "popL", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mdecode")
        {Name = "mdecode", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "translate_assignment")
        {Name = "translate_assignment", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "translate_condition")
        {Name = "translate_condition", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eval_il_cond")
        {Name = "eval_il_cond", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "translate")
        {Name = "translate", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "run_arm")
        {Name = "run_arm", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "run_ir")
        {Name = "run_ir", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "WELL_FORMED")
        {Name = "WELL_FORMED", Thy = "IL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "WELL_FORMED_SUB")
        {Name = "WELL_FORMED_SUB", Thy = "IL"}
  val IL_grammars = Parse.current_lgrms()
  end




  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG MREG_Axiom,
           case_def=MREG_case_def,
           case_cong=MREG_case_cong,
           induction=ORIG MREG_induction,
           nchotomy=MREG_nchotomy,
           size=SOME(Parse.Term`(IL$MREG_size) :(IL$MREG) -> (num$num)`,
                     ORIG MREG_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME MREG_distinct,
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
          {ax=ORIG MEXP_Axiom,
           case_def=MEXP_case_def,
           case_cong=MEXP_case_cong,
           induction=ORIG MEXP_induction,
           nchotomy=MEXP_nchotomy,
           size=SOME(Parse.Term`(IL$MEXP_size) :(IL$MEXP) -> (num$num)`,
                     ORIG MEXP_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME MEXP_11,
           distinct=SOME MEXP_distinct,
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


  val _ = computeLib.add_funs [index_of_reg_def];

  val _ = computeLib.add_funs [from_reg_index_def];

  val _ = computeLib.add_funs [toREG_def];

  val _ = computeLib.add_funs [toMEM_def];

  val _ = computeLib.add_funs [toEXP_def];

  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG DOPER_Axiom,
           case_def=DOPER_case_def,
           case_cong=DOPER_case_cong,
           induction=ORIG DOPER_induction,
           nchotomy=DOPER_nchotomy,
           size=SOME(Parse.Term`(IL$DOPER_size) :(IL$DOPER) -> (num$num)`,
                     ORIG DOPER_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME DOPER_11,
           distinct=SOME DOPER_distinct,
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
          {ax=ORIG CTL_STRUCTURE_Axiom,
           case_def=CTL_STRUCTURE_case_def,
           case_cong=CTL_STRUCTURE_case_cong,
           induction=ORIG CTL_STRUCTURE_induction,
           nchotomy=CTL_STRUCTURE_nchotomy,
           size=SOME(Parse.Term`(IL$CTL_STRUCTURE_size) :(IL$CTL_STRUCTURE) -> (num$num)`,
                     ORIG CTL_STRUCTURE_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME CTL_STRUCTURE_11,
           distinct=SOME CTL_STRUCTURE_distinct,
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


  val _ = computeLib.add_funs [pushL_def];

  val _ = computeLib.add_funs [popL_def];

  val _ = computeLib.add_funs [mdecode_def];

  val _ = computeLib.add_funs [translate_assignment_def];

  val _ = computeLib.add_funs [translate_condition_def];

  val _ = computeLib.add_funs [eval_il_cond_def];

  val _ = computeLib.add_funs [translate_def];

  val _ = computeLib.add_funs [run_arm_def];

  val _ = computeLib.add_funs [run_ir_def];

  val _ = computeLib.add_funs [WELL_FORMED_def];

  val _ = computeLib.add_funs [WELL_FORMED_SUB_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
