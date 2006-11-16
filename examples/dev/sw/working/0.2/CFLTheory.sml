structure CFLTheory :> CFLTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading CFLTheory ... " else ()
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
          ("CFL",Arbnum.fromString "1163238460",Arbnum.fromString "586624")
          [("ARMComposition",
           Arbnum.fromString "1162366193",
           Arbnum.fromString "485425")];
  val _ = Theory.incorporate_types "CFL"
       [("MEXP",0), ("DOPER",0), ("MREG",0), ("CTL_STRUCTURE",0)];
  val _ = Theory.incorporate_consts "CFL"
     [("translate_condition",
       ((T"prod" "pair"
          [T"MREG" "CFL" [], T"prod" "pair" [alpha, T"MEXP" "CFL" []]] -->
         T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [alpha, T"EXP" "preARM" []]]))),
      ("index_of_reg",((T"MREG" "CFL" [] --> T"num" "num" []))),
      ("dest_DOPER",
       ((T"DOPER" "CFL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"prod" "pair"
                [T"MEXP" "CFL" [],
                 T"prod" "pair"
                  [T"MREG" "CFL" [],
                   T"prod" "pair"
                    [T"cart" "fcp" [bool, T"i5" "words" []],
                     T"prod" "pair"
                      [T"num" "num" [],
                       T"list" "list" [T"num" "num" []]]]]]]]]))),
      ("WELL_FORMED",((T"CTL_STRUCTURE" "CFL" [] --> bool))),
      ("eval_il_cond",
       ((T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)))),
      ("CFL9",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("CFL8",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("CFL7",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("CFL6",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("CFL5",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("CFL4",
       ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
      ("CFL3",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         (T"MREG" "CFL" [] --> T"DOPER" "CFL" [])))),
      ("CFL2",
       ((T"MREG" "CFL" [] -->
         (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
          T"DOPER" "CFL" [])))),
      ("CFL1",
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" []))),
      ("CFL0",((T"MREG" "CFL" [] --> T"MEXP" "CFL" []))),
      ("WELL_FORMED_SUB",((T"CTL_STRUCTURE" "CFL" [] --> bool))),
      ("num2MREG",((T"num" "num" [] --> T"MREG" "CFL" []))),
      ("mdecode",
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
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]])))),
      ("DOPER_case",
       (((T"MREG" "CFL" [] -->
          (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
           alpha)) -->
         ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
           (T"MREG" "CFL" [] --> alpha)) -->
          ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)) -->
           ((T"MREG" "CFL" [] -->
             (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
            ((T"MREG" "CFL" [] -->
              (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
             ((T"MREG" "CFL" [] -->
               (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
              ((T"MREG" "CFL" [] -->
                (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
               ((T"MREG" "CFL" [] -->
                 (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
                ((T"MREG" "CFL" [] -->
                  (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
                 ((T"MREG" "CFL" [] -->
                   (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
                  ((T"MREG" "CFL" [] -->
                    (T"MREG" "CFL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                   -->
                   ((T"MREG" "CFL" [] -->
                     (T"MREG" "CFL" [] -->
                      (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                    -->
                    ((T"MREG" "CFL" [] -->
                      (T"MREG" "CFL" [] -->
                       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                     -->
                     ((T"MREG" "CFL" [] -->
                       (T"MREG" "CFL" [] -->
                        (T"cart" "fcp" [bool, T"i5" "words" []] -->
                         alpha))) -->
                      ((T"num" "num" [] -->
                        (T"list" "list" [T"num" "num" []] --> alpha)) -->
                       ((T"num" "num" [] -->
                         (T"list" "list" [T"num" "num" []] --> alpha)) -->
                        (T"DOPER" "CFL" [] --> alpha))))))))))))))))))),
      ("R14",(T"MREG" "CFL" [])), ("R13",(T"MREG" "CFL" [])),
      ("R12",(T"MREG" "CFL" [])), ("R11",(T"MREG" "CFL" [])),
      ("R10",(T"MREG" "CFL" [])),
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
       ((T"list" "list" [T"DOPER" "CFL" []] -->
         T"CTL_STRUCTURE" "CFL" []))),
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
       ((T"MEXP" "CFL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]]))),
      ("run_cfl",
       ((T"CTL_STRUCTURE" "CFL" [] -->
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
      ("translate",
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
                       (T"MREG" "CFL" [] --> alpha)))))))))))))))))),
      ("MEXP_case",
       (((T"MREG" "CFL" [] --> alpha) -->
         ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
          (T"MEXP" "CFL" [] --> alpha))))),
      ("CTL_STRUCTURE_size",
       ((T"CTL_STRUCTURE" "CFL" [] --> T"num" "num" []))),
      ("CFL19",
       ((T"CTL_STRUCTURE" "CFL" [] -->
         (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])))),
      ("CFL18",
       ((T"list" "list" [T"DOPER" "CFL" []] -->
         T"CTL_STRUCTURE" "CFL" []))),
      ("CFL17",
       ((T"num" "num" [] -->
         (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" [])))),
      ("CFL16",
       ((T"num" "num" [] -->
         (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" [])))),
      ("mk_MEXP",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
         --> T"MEXP" "CFL" []))),
      ("CFL21",
       ((T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
         (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])))),
      ("CFL15",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "CFL" []))))),
      ("CFL20",
       ((T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
         (T"CTL_STRUCTURE" "CFL" [] -->
          (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))))),
      ("CFL14",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "CFL" []))))),
      ("CFL13",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "CFL" []))))),
      ("CFL12",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "CFL" []))))),
      ("CFL11",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("CFL10",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("dest_CTL_STRUCTURE",
       ((T"CTL_STRUCTURE" "CFL" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"DOPER" "CFL" []],
             T"prod" "pair"
              [T"MREG" "CFL" [],
               T"prod" "pair"
                [T"COND" "preARM" [], T"MEXP" "CFL" []]]]]))),
      ("DOPER_size",((T"DOPER" "CFL" [] --> T"num" "num" []))),
      ("mk_DOPER",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"prod" "pair"
                [T"MEXP" "CFL" [],
                 T"prod" "pair"
                  [T"MREG" "CFL" [],
                   T"prod" "pair"
                    [T"cart" "fcp" [bool, T"i5" "words" []],
                     T"prod" "pair"
                      [T"num" "num" [],
                       T"list" "list" [T"num" "num" []]]]]]]]] -->
         T"DOPER" "CFL" []))),
      ("MSTR",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         (T"MREG" "CFL" [] --> T"DOPER" "CFL" [])))),
      ("MSUB",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("MREG2num",((T"MREG" "CFL" [] --> T"num" "num" []))),
      ("MROR",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "CFL" []))))),
      ("MRSB",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("MPUSH",
       ((T"num" "num" [] -->
         (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" [])))),
      ("MPOP",
       ((T"num" "num" [] -->
         (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" [])))),
      ("MORR",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("MMUL",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("tp",(T"num" "num" [])), ("sp",(T"num" "num" [])),
      ("mk_CTL_STRUCTURE",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"DOPER" "CFL" []],
             T"prod" "pair"
              [T"MREG" "CFL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]]
         --> T"CTL_STRUCTURE" "CFL" []))),
      ("MMOV",
       ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
      ("MLSR",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "CFL" []))))),
      ("MLSL",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "CFL" []))))),
      ("translate_assignment",
       ((T"DOPER" "CFL" [] -->
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
      ("lr",(T"num" "num" [])), ("ip",(T"num" "num" [])),
      ("gp",(T"num" "num" [])), ("fp",(T"num" "num" [])),
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
       ((T"MREG" "CFL" [] -->
         (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
          T"DOPER" "CFL" [])))),
      ("from_reg_index",((T"num" "num" [] --> T"MREG" "CFL" []))),
      ("toREG",((T"MREG" "CFL" [] --> T"EXP" "preARM" []))),
      ("MEOR",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("MREG_size",((T"MREG" "CFL" [] --> T"num" "num" []))),
      ("TR",
       ((T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
         (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])))),
      ("MEXP_size",((T"MEXP" "CFL" [] --> T"num" "num" []))),
      ("toMEM",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         T"EXP" "preARM" []))),
      ("SC",
       ((T"CTL_STRUCTURE" "CFL" [] -->
         (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])))),
      ("MR",((T"MREG" "CFL" [] --> T"MEXP" "CFL" []))),
      ("MASR",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"cart" "fcp" [bool, T"i5" "words" []] -->
           T"DOPER" "CFL" []))))), ("R9",(T"MREG" "CFL" [])),
      ("R8",(T"MREG" "CFL" [])), ("R7",(T"MREG" "CFL" [])),
      ("R6",(T"MREG" "CFL" [])), ("R5",(T"MREG" "CFL" [])),
      ("R4",(T"MREG" "CFL" [])), ("R3",(T"MREG" "CFL" [])),
      ("R2",(T"MREG" "CFL" [])), ("R1",(T"MREG" "CFL" [])),
      ("R0",(T"MREG" "CFL" [])),
      ("MC",
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" []))),
      ("toEXP",((T"MEXP" "CFL" [] --> T"EXP" "preARM" []))),
      ("MAND",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("CJ",
       ((T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
         (T"CTL_STRUCTURE" "CFL" [] -->
          (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))))),
      ("MADD",
       ((T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))))),
      ("CTL_STRUCTURE_case",
       (((T"list" "list" [T"DOPER" "CFL" []] --> alpha) -->
         ((T"CTL_STRUCTURE" "CFL" [] -->
           (T"CTL_STRUCTURE" "CFL" [] --> alpha)) -->
          ((T"prod" "pair"
             [T"MREG" "CFL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
            (T"CTL_STRUCTURE" "CFL" [] -->
             (T"CTL_STRUCTURE" "CFL" [] --> alpha))) -->
           ((T"prod" "pair"
              [T"MREG" "CFL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
             (T"CTL_STRUCTURE" "CFL" [] --> alpha)) -->
            (T"CTL_STRUCTURE" "CFL" [] --> alpha)))))))];
  
  local
  val share_table = Vector.fromList
  [C"?" "bool"
    ((((T"MREG" "CFL" [] --> T"num" "num" []) --> bool) --> bool)),
   V"rep" ((T"MREG" "CFL" [] --> T"num" "num" [])),
   C"TYPE_DEFINITION" "bool"
    (((T"num" "num" [] --> bool) -->
      ((T"MREG" "CFL" [] --> T"num" "num" []) --> bool))),
   V"n" (T"num" "num" []),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"MREG" "CFL" [] --> bool) --> bool)),
   V"a" (T"MREG" "CFL" []),
   C"=" "min" ((T"MREG" "CFL" [] --> (T"MREG" "CFL" [] --> bool))),
   C"num2MREG" "CFL" ((T"num" "num" [] --> T"MREG" "CFL" [])),
   C"MREG2num" "CFL" ((T"MREG" "CFL" [] --> T"num" "num" [])),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"r" (T"num" "num" []), C"=" "min" ((bool --> (bool --> bool))),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"R0" "CFL" (T"MREG" "CFL" []), C"0" "num" (T"num" "num" []),
   C"R1" "CFL" (T"MREG" "CFL" []), C"R2" "CFL" (T"MREG" "CFL" []),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"R3" "CFL" (T"MREG" "CFL" []), C"R4" "CFL" (T"MREG" "CFL" []),
   C"R5" "CFL" (T"MREG" "CFL" []), C"R6" "CFL" (T"MREG" "CFL" []),
   C"R7" "CFL" (T"MREG" "CFL" []), C"R8" "CFL" (T"MREG" "CFL" []),
   C"R9" "CFL" (T"MREG" "CFL" []), C"R10" "CFL" (T"MREG" "CFL" []),
   C"R11" "CFL" (T"MREG" "CFL" []), C"R12" "CFL" (T"MREG" "CFL" []),
   C"R13" "CFL" (T"MREG" "CFL" []), C"R14" "CFL" (T"MREG" "CFL" []),
   V"x" (T"MREG" "CFL" []),
   C"MREG_size" "CFL" ((T"MREG" "CFL" [] --> T"num" "num" [])),
   C"!" "bool" (((alpha --> bool) --> bool)), V"v0" (alpha), V"v1" (alpha),
   V"v2" (alpha), V"v3" (alpha), V"v4" (alpha), V"v5" (alpha),
   V"v6" (alpha), V"v7" (alpha), V"v8" (alpha), V"v9" (alpha),
   V"v10" (alpha), V"v11" (alpha), V"v12" (alpha), V"v13" (alpha),
   V"v14" (alpha), C"=" "min" ((alpha --> (alpha --> bool))),
   C"MREG_case" "CFL"
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
                   (alpha --> (T"MREG" "CFL" [] --> alpha))))))))))))))))),
   V"m" (T"num" "num" []),
   C"COND" "bool" ((bool --> (alpha --> (alpha --> alpha)))),
   C"?" "bool"
    ((((T"MEXP" "CFL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
       --> bool) --> bool)),
   V"rep"
    ((T"MEXP" "CFL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) -->
      ((T"MEXP" "CFL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
       --> bool))),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool) --> bool) --> bool)),
   V"'MEXP'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)), C"==>" "min" ((bool --> (bool --> bool))),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) --> bool)), C"\\/" "bool" ((bool --> (bool --> bool))),
   C"?" "bool" (((T"MREG" "CFL" [] --> bool) --> bool)),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
        -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"cart" "fcp" [bool, T"i32" "words" []]]])))),
   C"," "pair"
    ((T"MREG" "CFL" [] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"prod" "pair"
        [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]))),
   C"@" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) -->
      T"cart" "fcp" [bool, T"i32" "words" []])),
   V"v" (T"cart" "fcp" [bool, T"i32" "words" []]), C"T" "bool" (bool),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"a" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"@" "min" (((T"MREG" "CFL" [] --> bool) --> T"MREG" "CFL" [])),
   V"v" (T"MREG" "CFL" []),
   C"!" "bool" (((T"MEXP" "CFL" [] --> bool) --> bool)),
   V"a" (T"MEXP" "CFL" []),
   C"=" "min" ((T"MEXP" "CFL" [] --> (T"MEXP" "CFL" [] --> bool))),
   C"mk_MEXP" "CFL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      T"MEXP" "CFL" [])),
   C"dest_MEXP" "CFL"
    ((T"MEXP" "CFL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"=" "min"
    (((T"MREG" "CFL" [] --> T"MEXP" "CFL" []) -->
      ((T"MREG" "CFL" [] --> T"MEXP" "CFL" []) --> bool))),
   C"CFL0" "CFL" ((T"MREG" "CFL" [] --> T"MEXP" "CFL" [])),
   C"=" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" []) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" []) -->
       bool))),
   C"CFL1" "CFL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" [])),
   C"MR" "CFL" ((T"MREG" "CFL" [] --> T"MEXP" "CFL" [])),
   C"MC" "CFL"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" [])),
   C"!" "bool" ((((T"MREG" "CFL" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"MREG" "CFL" [] --> alpha)),
   C"!" "bool"
    ((((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) --> bool) -->
      bool)), V"f1" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   C"MEXP_case" "CFL"
    (((T"MREG" "CFL" [] --> alpha) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
       (T"MEXP" "CFL" [] --> alpha)))),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   C"MEXP_size" "CFL" ((T"MEXP" "CFL" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"index_of_reg" "CFL" ((T"MREG" "CFL" [] --> T"num" "num" [])),
   V"i" (T"num" "num" []),
   C"from_reg_index" "CFL" ((T"num" "num" [] --> T"MREG" "CFL" [])),
   C"COND" "bool"
    ((bool -->
      (T"MREG" "CFL" [] --> (T"MREG" "CFL" [] --> T"MREG" "CFL" [])))),
   V"r" (T"MREG" "CFL" []),
   C"=" "min" ((T"EXP" "preARM" [] --> (T"EXP" "preARM" [] --> bool))),
   C"toREG" "CFL" ((T"MREG" "CFL" [] --> T"EXP" "preARM" [])),
   C"REG" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   V"base" (T"num" "num" []),
   C"!" "bool" (((T"OFFSET" "preARM" [] --> bool) --> bool)),
   V"offset" (T"OFFSET" "preARM" []),
   C"toMEM" "CFL"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"EXP" "preARM" [])),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"OFFSET" "preARM" [] -->
       T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]))),
   C"MEM" "preARM"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"EXP" "preARM" [])),
   C"toEXP" "CFL" ((T"MEXP" "CFL" [] --> T"EXP" "preARM" [])),
   V"c" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"WCONST" "preARM"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"EXP" "preARM" [])),
   C"tp" "CFL" (T"num" "num" []), C"gp" "CFL" (T"num" "num" []),
   C"fp" "CFL" (T"num" "num" []), C"ip" "CFL" (T"num" "num" []),
   C"sp" "CFL" (T"num" "num" []), C"lr" "CFL" (T"num" "num" []),
   C"?" "bool"
    ((((T"DOPER" "CFL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"prod" "pair"
               [T"MEXP" "CFL" [],
                T"prod" "pair"
                 [T"MREG" "CFL" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i5" "words" []],
                    T"prod" "pair"
                     [T"num" "num" [],
                      T"list" "list" [T"num" "num" []]]]]]]]]) --> bool)
      --> bool)),
   V"rep"
    ((T"DOPER" "CFL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "CFL" [],
              T"prod" "pair"
               [T"MREG" "CFL" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i5" "words" []],
                  T"prod" "pair"
                   [T"num" "num" [],
                    T"list" "list" [T"num" "num" []]]]]]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"prod" "pair"
              [T"MEXP" "CFL" [],
               T"prod" "pair"
                [T"MREG" "CFL" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i5" "words" []],
                   T"prod" "pair"
                    [T"num" "num" [],
                     T"list" "list" [T"num" "num" []]]]]]]]] --> bool) -->
      ((T"DOPER" "CFL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"prod" "pair"
               [T"MEXP" "CFL" [],
                T"prod" "pair"
                 [T"MREG" "CFL" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i5" "words" []],
                    T"prod" "pair"
                     [T"num" "num" [],
                      T"list" "list" [T"num" "num" []]]]]]]]]) --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "CFL" [],
             T"prod" "pair"
              [T"MREG" "CFL" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i5" "words" []],
                 T"prod" "pair"
                  [T"num" "num" [],
                   T"list" "list" [T"num" "num" []]]]]]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"prod" "pair"
               [T"MEXP" "CFL" [],
                T"prod" "pair"
                 [T"MREG" "CFL" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i5" "words" []],
                    T"prod" "pair"
                     [T"num" "num" [],
                      T"list" "list" [T"num" "num" []]]]]]]]] --> bool) -->
       bool) --> bool)),
   V"'DOPER'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "CFL" [],
              T"prod" "pair"
               [T"MREG" "CFL" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i5" "words" []],
                  T"prod" "pair"
                   [T"num" "num" [],
                    T"list" "list" [T"num" "num" []]]]]]]]] --> bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"prod" "pair"
              [T"MEXP" "CFL" [],
               T"prod" "pair"
                [T"MREG" "CFL" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i5" "words" []],
                   T"prod" "pair"
                    [T"num" "num" [],
                     T"list" "list" [T"num" "num" []]]]]]]]] --> bool) -->
      bool)), V"a0" (T"MREG" "CFL" []),
   C"?" "bool"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> bool)),
   V"a1" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "CFL" [],
              T"prod" "pair"
               [T"MREG" "CFL" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i5" "words" []],
                  T"prod" "pair"
                   [T"num" "num" [],
                    T"list" "list" [T"num" "num" []]]]]]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"prod" "pair"
              [T"MEXP" "CFL" [],
               T"prod" "pair"
                [T"MREG" "CFL" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i5" "words" []],
                   T"prod" "pair"
                    [T"num" "num" [],
                     T"list" "list" [T"num" "num" []]]]]]]]] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "CFL" [],
             T"prod" "pair"
              [T"MREG" "CFL" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i5" "words" []],
                 T"prod" "pair"
                  [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]]]]
       -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
               T"prod" "pair"
                [T"MEXP" "CFL" [],
                 T"prod" "pair"
                  [T"MREG" "CFL" [],
                   T"prod" "pair"
                    [T"cart" "fcp" [bool, T"i5" "words" []],
                     T"prod" "pair"
                      [T"num" "num" [],
                       T"list" "list" [T"num" "num" []]]]]]]]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair"
             [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
              T"prod" "pair"
               [T"MEXP" "CFL" [],
                T"prod" "pair"
                 [T"MREG" "CFL" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i5" "words" []],
                    T"prod" "pair"
                     [T"num" "num" [],
                      T"list" "list" [T"num" "num" []]]]]]]]])))),
   C"," "pair"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"prod" "pair"
          [T"MEXP" "CFL" [],
           T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i5" "words" []],
               T"prod" "pair"
                [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]]] -->
       T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "CFL" [],
             T"prod" "pair"
              [T"MREG" "CFL" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i5" "words" []],
                 T"prod" "pair"
                  [T"num" "num" [],
                   T"list" "list" [T"num" "num" []]]]]]]]))),
   C"," "pair"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"prod" "pair"
        [T"MEXP" "CFL" [],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i5" "words" []],
             T"prod" "pair"
              [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]] -->
       T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"prod" "pair"
          [T"MEXP" "CFL" [],
           T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i5" "words" []],
               T"prod" "pair"
                [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]]]))),
   C"," "pair"
    ((T"MEXP" "CFL" [] -->
      (T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i5" "words" []],
           T"prod" "pair"
            [T"num" "num" [], T"list" "list" [T"num" "num" []]]]] -->
       T"prod" "pair"
        [T"MEXP" "CFL" [],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i5" "words" []],
             T"prod" "pair"
              [T"num" "num" [], T"list" "list" [T"num" "num" []]]]]]))),
   C"@" "min" (((T"MEXP" "CFL" [] --> bool) --> T"MEXP" "CFL" [])),
   V"v" (T"MEXP" "CFL" []),
   C"," "pair"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair"
        [T"cart" "fcp" [bool, T"i5" "words" []],
         T"prod" "pair"
          [T"num" "num" [], T"list" "list" [T"num" "num" []]]] -->
       T"prod" "pair"
        [T"MREG" "CFL" [],
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
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "CFL" [],
             T"prod" "pair"
              [T"MREG" "CFL" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i5" "words" []],
                 T"prod" "pair"
                  [T"num" "num" [],
                   T"list" "list" [T"num" "num" []]]]]]]]]),
   V"a0" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"a1" (T"MREG" "CFL" []),
   C"?" "bool" (((T"MEXP" "CFL" [] --> bool) --> bool)),
   V"a1" (T"MEXP" "CFL" []),
   C"@" "min"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []])),
   V"v" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"a2" (T"MEXP" "CFL" []),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i5" "words" []] --> bool) --> bool)),
   V"a2" (T"cart" "fcp" [bool, T"i5" "words" []]),
   C"?" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"a0" (T"num" "num" []),
   C"?" "bool" (((T"list" "list" [T"num" "num" []] --> bool) --> bool)),
   V"a1" (T"list" "list" [T"num" "num" []]),
   C"!" "bool" (((T"DOPER" "CFL" [] --> bool) --> bool)),
   V"a" (T"DOPER" "CFL" []),
   C"=" "min" ((T"DOPER" "CFL" [] --> (T"DOPER" "CFL" [] --> bool))),
   C"mk_DOPER" "CFL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "CFL" [],
              T"prod" "pair"
               [T"MREG" "CFL" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i5" "words" []],
                  T"prod" "pair"
                   [T"num" "num" [],
                    T"list" "list" [T"num" "num" []]]]]]]]] -->
      T"DOPER" "CFL" [])),
   C"dest_DOPER" "CFL"
    ((T"DOPER" "CFL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"MEXP" "CFL" [],
              T"prod" "pair"
               [T"MREG" "CFL" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i5" "words" []],
                  T"prod" "pair"
                   [T"num" "num" [],
                    T"list" "list" [T"num" "num" []]]]]]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"MEXP" "CFL" [],
             T"prod" "pair"
              [T"MREG" "CFL" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i5" "words" []],
                 T"prod" "pair"
                  [T"num" "num" [],
                   T"list" "list" [T"num" "num" []]]]]]]]]),
   C"=" "min"
    (((T"MREG" "CFL" [] -->
       (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        T"DOPER" "CFL" [])) -->
      ((T"MREG" "CFL" [] -->
        (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         T"DOPER" "CFL" [])) --> bool))),
   C"CFL2" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"DOPER" "CFL" []))),
   C"=" "min"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       (T"MREG" "CFL" [] --> T"DOPER" "CFL" [])) -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        (T"MREG" "CFL" [] --> T"DOPER" "CFL" [])) --> bool))),
   C"CFL3" "CFL"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "CFL" [] --> T"DOPER" "CFL" []))),
   C"=" "min"
    (((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])) -->
      ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])) -->
       bool))),
   C"CFL4" "CFL"
    ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))),
   C"=" "min"
    (((T"MREG" "CFL" [] -->
       (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))) -->
      ((T"MREG" "CFL" [] -->
        (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))
       --> bool))),
   C"CFL5" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"CFL6" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"CFL7" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"CFL8" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"CFL9" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"CFL10" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"CFL11" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"=" "min"
    (((T"MREG" "CFL" [] -->
       (T"MREG" "CFL" [] -->
        (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))
      -->
      ((T"MREG" "CFL" [] -->
        (T"MREG" "CFL" [] -->
         (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))
       --> bool))),
   C"CFL12" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   C"CFL13" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   C"CFL14" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   C"CFL15" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   C"=" "min"
    (((T"num" "num" [] -->
       (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" [])) -->
      ((T"num" "num" [] -->
        (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" [])) -->
       bool))),
   C"CFL16" "CFL"
    ((T"num" "num" [] -->
      (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" []))),
   C"CFL17" "CFL"
    ((T"num" "num" [] -->
      (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" []))),
   C"MLDR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"DOPER" "CFL" []))),
   C"MSTR" "CFL"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "CFL" [] --> T"DOPER" "CFL" []))),
   C"MMOV" "CFL"
    ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))),
   C"MADD" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"MSUB" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"MRSB" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"MMUL" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"MAND" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"MORR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"MEOR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))),
   C"MLSL" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   C"MLSR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   C"MASR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   C"MROR" "CFL"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> T"DOPER" "CFL" [])))),
   C"MPUSH" "CFL"
    ((T"num" "num" [] -->
      (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" []))),
   C"MPOP" "CFL"
    ((T"num" "num" [] -->
      (T"list" "list" [T"num" "num" []] --> T"DOPER" "CFL" []))),
   C"!" "bool"
    ((((T"MREG" "CFL" [] -->
        (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         alpha)) --> bool) --> bool)),
   V"f"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       alpha))),
   C"!" "bool"
    ((((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        (T"MREG" "CFL" [] --> alpha)) --> bool) --> bool)),
   V"f1"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "CFL" [] --> alpha))),
   C"!" "bool"
    ((((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)) --> bool) -->
      bool)), V"f2" ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))),
   C"!" "bool"
    ((((T"MREG" "CFL" [] -->
        (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) --> bool) -->
      bool)),
   V"f3"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f4"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f5"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f6"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f7"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f8"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f9"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   C"!" "bool"
    ((((T"MREG" "CFL" [] -->
        (T"MREG" "CFL" [] -->
         (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha))) --> bool) -->
      bool)),
   V"f10"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f11"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f12"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f13"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
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
   C"DOPER_case" "CFL"
    (((T"MREG" "CFL" [] -->
       (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha))
      -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        (T"MREG" "CFL" [] --> alpha)) -->
       ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)) -->
        ((T"MREG" "CFL" [] -->
          (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
         ((T"MREG" "CFL" [] -->
           (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
          ((T"MREG" "CFL" [] -->
            (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
           ((T"MREG" "CFL" [] -->
             (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
            ((T"MREG" "CFL" [] -->
              (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
             ((T"MREG" "CFL" [] -->
               (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
              ((T"MREG" "CFL" [] -->
                (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))) -->
               ((T"MREG" "CFL" [] -->
                 (T"MREG" "CFL" [] -->
                  (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha))) -->
                ((T"MREG" "CFL" [] -->
                  (T"MREG" "CFL" [] -->
                   (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha))) -->
                 ((T"MREG" "CFL" [] -->
                   (T"MREG" "CFL" [] -->
                    (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                  -->
                  ((T"MREG" "CFL" [] -->
                    (T"MREG" "CFL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))
                   -->
                   ((T"num" "num" [] -->
                     (T"list" "list" [T"num" "num" []] --> alpha)) -->
                    ((T"num" "num" [] -->
                      (T"list" "list" [T"num" "num" []] --> alpha)) -->
                     (T"DOPER" "CFL" [] --> alpha)))))))))))))))))),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i5" "words" []] --> bool) --> bool)),
   C"!" "bool" (((T"list" "list" [T"num" "num" []] --> bool) --> bool)),
   C"DOPER_size" "CFL" ((T"DOPER" "CFL" [] --> T"num" "num" [])),
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
    ((((T"CTL_STRUCTURE" "CFL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "CFL" []],
            T"prod" "pair"
             [T"MREG" "CFL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]])
       --> bool) --> bool)),
   V"rep"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "CFL" []],
          T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"DOPER" "CFL" []],
           T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]] -->
       bool) -->
      ((T"CTL_STRUCTURE" "CFL" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "CFL" []],
            T"prod" "pair"
             [T"MREG" "CFL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]])
       --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "CFL" []],
            T"prod" "pair"
             [T"MREG" "CFL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]] -->
        bool) --> bool) --> bool)),
   V"'CTL_STRUCTURE'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "CFL" []],
          T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]] -->
      bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"DOPER" "CFL" []],
           T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]] -->
       bool) --> bool)),
   C"?" "bool" (((T"list" "list" [T"DOPER" "CFL" []] --> bool) --> bool)),
   V"a" (T"list" "list" [T"DOPER" "CFL" []]),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "CFL" []],
          T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"DOPER" "CFL" []],
           T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]] -->
       bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"DOPER" "CFL" []],
             T"prod" "pair"
              [T"MREG" "CFL" [],
               T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]])
        -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "CFL" []],
            T"prod" "pair"
             [T"MREG" "CFL" [],
              T"prod" "pair"
               [T"COND" "preARM" [], T"MEXP" "CFL" []]]]])))),
   C"," "pair"
    ((T"list" "list" [T"DOPER" "CFL" []] -->
      (T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
       T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]))),
   C"@" "min"
    (((T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] --> bool)
      -->
      T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]])),
   V"v"
    (T"prod" "pair"
      [T"MREG" "CFL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]]),
   C"?" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"DOPER" "CFL" []],
           T"prod" "pair"
            [T"MREG" "CFL" [],
             T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]] -->
       bool) --> bool)),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]]),
   V"a1"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]]),
   C"@" "min"
    (((T"list" "list" [T"DOPER" "CFL" []] --> bool) -->
      T"list" "list" [T"DOPER" "CFL" []])),
   V"v" (T"list" "list" [T"DOPER" "CFL" []]),
   C"FCONS" "ind_type"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "CFL" []],
          T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]] -->
      ((T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "CFL" []],
            T"prod" "pair"
             [T"MREG" "CFL" [],
              T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]])
       -->
       (T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"DOPER" "CFL" []],
            T"prod" "pair"
             [T"MREG" "CFL" [],
              T"prod" "pair"
               [T"COND" "preARM" [], T"MEXP" "CFL" []]]]])))),
   C"?" "bool"
    (((T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] --> bool)
      --> bool)),
   V"a0"
    (T"prod" "pair"
      [T"MREG" "CFL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]),
   V"a2"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]]),
   C"!" "bool" (((T"CTL_STRUCTURE" "CFL" [] --> bool) --> bool)),
   V"a" (T"CTL_STRUCTURE" "CFL" []),
   C"=" "min"
    ((T"CTL_STRUCTURE" "CFL" [] --> (T"CTL_STRUCTURE" "CFL" [] --> bool))),
   C"mk_CTL_STRUCTURE" "CFL"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "CFL" []],
          T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]] -->
      T"CTL_STRUCTURE" "CFL" [])),
   C"dest_CTL_STRUCTURE" "CFL"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"DOPER" "CFL" []],
          T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"DOPER" "CFL" []],
         T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]]]),
   C"=" "min"
    (((T"list" "list" [T"DOPER" "CFL" []] --> T"CTL_STRUCTURE" "CFL" [])
      -->
      ((T"list" "list" [T"DOPER" "CFL" []] --> T"CTL_STRUCTURE" "CFL" [])
       --> bool))),
   C"CFL18" "CFL"
    ((T"list" "list" [T"DOPER" "CFL" []] --> T"CTL_STRUCTURE" "CFL" [])),
   C"=" "min"
    (((T"CTL_STRUCTURE" "CFL" [] -->
       (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])) -->
      ((T"CTL_STRUCTURE" "CFL" [] -->
        (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])) -->
       bool))),
   C"CFL19" "CFL"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))),
   V"a0" (T"CTL_STRUCTURE" "CFL" []), V"a1" (T"CTL_STRUCTURE" "CFL" []),
   C"=" "min"
    (((T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
       (T"CTL_STRUCTURE" "CFL" [] -->
        (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))) -->
      ((T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
        (T"CTL_STRUCTURE" "CFL" [] -->
         (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))) -->
       bool))),
   C"CFL20" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] -->
       (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])))),
   V"a2" (T"CTL_STRUCTURE" "CFL" []),
   C"=" "min"
    (((T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
       (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])) -->
      ((T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
        (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])) -->
       bool))),
   C"CFL21" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))),
   C"BLK" "CFL"
    ((T"list" "list" [T"DOPER" "CFL" []] --> T"CTL_STRUCTURE" "CFL" [])),
   C"SC" "CFL"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))),
   C"CJ" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] -->
       (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])))),
   C"TR" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))),
   C"!" "bool"
    ((((T"list" "list" [T"DOPER" "CFL" []] --> alpha) --> bool) --> bool)),
   V"f" ((T"list" "list" [T"DOPER" "CFL" []] --> alpha)),
   C"!" "bool"
    ((((T"CTL_STRUCTURE" "CFL" [] -->
        (T"CTL_STRUCTURE" "CFL" [] --> alpha)) --> bool) --> bool)),
   V"f1"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"CTL_STRUCTURE" "CFL" [] --> alpha))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
        (T"CTL_STRUCTURE" "CFL" [] -->
         (T"CTL_STRUCTURE" "CFL" [] --> alpha))) --> bool) --> bool)),
   V"f2"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] -->
       (T"CTL_STRUCTURE" "CFL" [] --> alpha)))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
        (T"CTL_STRUCTURE" "CFL" [] --> alpha)) --> bool) --> bool)),
   V"f3"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] --> alpha))),
   C"!" "bool" (((T"list" "list" [T"DOPER" "CFL" []] --> bool) --> bool)),
   C"CTL_STRUCTURE_case" "CFL"
    (((T"list" "list" [T"DOPER" "CFL" []] --> alpha) -->
      ((T"CTL_STRUCTURE" "CFL" [] -->
        (T"CTL_STRUCTURE" "CFL" [] --> alpha)) -->
       ((T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
         (T"CTL_STRUCTURE" "CFL" [] -->
          (T"CTL_STRUCTURE" "CFL" [] --> alpha))) -->
        ((T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
          (T"CTL_STRUCTURE" "CFL" [] --> alpha)) -->
         (T"CTL_STRUCTURE" "CFL" [] --> alpha)))))),
   C"!" "bool"
    (((T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] --> bool)
      --> bool)),
   C"CTL_STRUCTURE_size" "CFL"
    ((T"CTL_STRUCTURE" "CFL" [] --> T"num" "num" [])),
   C"list_size" "list"
    (((T"DOPER" "CFL" [] --> T"num" "num" []) -->
      (T"list" "list" [T"DOPER" "CFL" []] --> T"num" "num" []))),
   C"UNCURRY" "pair"
    (((T"MREG" "CFL" [] -->
       (T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []] -->
        T"num" "num" [])) -->
      (T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
       T"num" "num" []))),
   V"y" (T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]),
   C"UNCURRY" "pair"
    (((T"COND" "preARM" [] --> (T"MEXP" "CFL" [] --> T"num" "num" [])) -->
      (T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []] -->
       T"num" "num" []))), V"x" (T"COND" "preARM" []),
   V"y" (T"MEXP" "CFL" []),
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
   C"pushL" "CFL"
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
   C"popL" "CFL"
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
   V"dst" (T"MREG" "CFL" []),
   V"src" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
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
   V"dst" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"src" (T"MREG" "CFL" []), V"src" (T"MEXP" "CFL" []),
   V"src1" (T"MREG" "CFL" []), V"src2" (T"MEXP" "CFL" []),
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
   V"src2_reg" (T"MREG" "CFL" []),
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
   C"translate_assignment" "CFL"
    ((T"DOPER" "CFL" [] -->
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
   V"e" (T"MEXP" "CFL" []),
   C"=" "min"
    ((T"prod" "pair"
       [T"EXP" "preARM" [], T"prod" "pair" [alpha, T"EXP" "preARM" []]] -->
      (T"prod" "pair"
        [T"EXP" "preARM" [], T"prod" "pair" [alpha, T"EXP" "preARM" []]]
       --> bool))),
   C"translate_condition" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [], T"prod" "pair" [alpha, T"MEXP" "CFL" []]] -->
      T"prod" "pair"
       [T"EXP" "preARM" [], T"prod" "pair" [alpha, T"EXP" "preARM" []]])),
   C"," "pair"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair" [alpha, T"MEXP" "CFL" []] -->
       T"prod" "pair"
        [T"MREG" "CFL" [], T"prod" "pair" [alpha, T"MEXP" "CFL" []]]))),
   C"," "pair"
    ((alpha -->
      (T"MEXP" "CFL" [] --> T"prod" "pair" [alpha, T"MEXP" "CFL" []]))),
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
      [T"MREG" "CFL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]),
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
   C"translate_condition" "CFL"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      T"prod" "pair"
       [T"EXP" "preARM" [],
        T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]])),
   C"=" "min"
    (((T"CTL_STRUCTURE" "CFL" [] -->
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
                T"option" "option" [T"OFFSET" "preARM" []]]]]]) -->
       bool))),
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
   C"WFREC" "relation"
    (((T"CTL_STRUCTURE" "CFL" [] --> (T"CTL_STRUCTURE" "CFL" [] --> bool))
      -->
      (((T"CTL_STRUCTURE" "CFL" [] -->
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
        (T"CTL_STRUCTURE" "CFL" [] -->
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
       (T"CTL_STRUCTURE" "CFL" [] -->
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
    ((((T"CTL_STRUCTURE" "CFL" [] --> (T"CTL_STRUCTURE" "CFL" [] --> bool))
       --> bool) -->
      (T"CTL_STRUCTURE" "CFL" [] -->
       (T"CTL_STRUCTURE" "CFL" [] --> bool)))),
   V"R"
    ((T"CTL_STRUCTURE" "CFL" [] --> (T"CTL_STRUCTURE" "CFL" [] --> bool))),
   C"WF" "relation"
    (((T"CTL_STRUCTURE" "CFL" [] --> (T"CTL_STRUCTURE" "CFL" [] --> bool))
      --> bool)), V"stm" (T"DOPER" "CFL" []),
   V"stmL" (T"list" "list" [T"DOPER" "CFL" []]),
   C"CONS" "list"
    ((T"DOPER" "CFL" [] -->
      (T"list" "list" [T"DOPER" "CFL" []] -->
       T"list" "list" [T"DOPER" "CFL" []]))),
   V"S1" (T"CTL_STRUCTURE" "CFL" []), V"S2" (T"CTL_STRUCTURE" "CFL" []),
   V"Sfalse" (T"CTL_STRUCTURE" "CFL" []),
   V"Strue" (T"CTL_STRUCTURE" "CFL" []),
   V"Sbody" (T"CTL_STRUCTURE" "CFL" []),
   V"translate"
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
   C"CTL_STRUCTURE_case" "CFL"
    (((T"list" "list" [T"DOPER" "CFL" []] -->
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
      ((T"CTL_STRUCTURE" "CFL" [] -->
        (T"CTL_STRUCTURE" "CFL" [] -->
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
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
         (T"CTL_STRUCTURE" "CFL" [] -->
          (T"CTL_STRUCTURE" "CFL" [] -->
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
           [T"MREG" "CFL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
          (T"CTL_STRUCTURE" "CFL" [] -->
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
         (T"CTL_STRUCTURE" "CFL" [] -->
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
      ((T"DOPER" "CFL" [] -->
        (T"list" "list" [T"DOPER" "CFL" []] -->
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
       (T"list" "list" [T"DOPER" "CFL" []] -->
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
      [T"MREG" "CFL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]),
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
   C"run_arm" "CFL"
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
      T"num" "num" [])), V"cfl" (T"CTL_STRUCTURE" "CFL" []),
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
   C"WELL_FORMED" "CFL" ((T"CTL_STRUCTURE" "CFL" [] --> bool)),
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
   C"WELL_FORMED_SUB" "CFL" ((T"CTL_STRUCTURE" "CFL" [] --> bool)),
   V"r'" (T"num" "num" []), V"a'" (T"MREG" "CFL" []),
   C"DATATYPE" "bool" ((bool --> bool)),
   V"MREG"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"MREG" "CFL" [] -->
        (T"MREG" "CFL" [] -->
         (T"MREG" "CFL" [] -->
          (T"MREG" "CFL" [] -->
           (T"MREG" "CFL" [] -->
            (T"MREG" "CFL" [] -->
             (T"MREG" "CFL" [] -->
              (T"MREG" "CFL" [] -->
               (T"MREG" "CFL" [] -->
                (T"MREG" "CFL" [] -->
                 (T"MREG" "CFL" [] -->
                  (T"MREG" "CFL" [] -->
                   (T"MREG" "CFL" [] --> bool)))))))))))))))),
   C"~" "bool" ((bool --> bool)), V"M" (T"MREG" "CFL" []),
   V"M'" (T"MREG" "CFL" []), V"v0'" (alpha), V"v1'" (alpha),
   V"v2'" (alpha), V"v3'" (alpha), V"v4'" (alpha), V"v5'" (alpha),
   V"v6'" (alpha), V"v7'" (alpha), V"v8'" (alpha), V"v9'" (alpha),
   V"v10'" (alpha), V"v11'" (alpha), V"v12'" (alpha), V"v13'" (alpha),
   V"v14'" (alpha), V"x0" (alpha), V"x1" (alpha), V"x2" (alpha),
   V"x3" (alpha), V"x4" (alpha), V"x5" (alpha), V"x6" (alpha),
   V"x7" (alpha), V"x8" (alpha), V"x9" (alpha), V"x10" (alpha),
   V"x11" (alpha), V"x12" (alpha), V"x13" (alpha), V"x14" (alpha),
   C"?" "bool" ((((T"MREG" "CFL" [] --> alpha) --> bool) --> bool)),
   C"!" "bool" ((((T"MREG" "CFL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"MREG" "CFL" [] --> bool)),
   V"MEXP"
    (((T"MREG" "CFL" [] --> T"MEXP" "CFL" []) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"MEXP" "CFL" []) -->
       bool))), V"a'" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   V"M" (T"MEXP" "CFL" []), V"M'" (T"MEXP" "CFL" []),
   V"f'" ((T"MREG" "CFL" [] --> alpha)),
   V"f1'" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   V"f0" ((T"MREG" "CFL" [] --> alpha)),
   C"?" "bool" ((((T"MEXP" "CFL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"MEXP" "CFL" [] --> alpha)),
   C"!" "bool" ((((T"MEXP" "CFL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"MEXP" "CFL" [] --> bool)),
   V"DOPER"
    (((T"MREG" "CFL" [] -->
       (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        T"DOPER" "CFL" [])) -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        (T"MREG" "CFL" [] --> T"DOPER" "CFL" [])) -->
       ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])) -->
        ((T"MREG" "CFL" [] -->
          (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))
         -->
         ((T"MREG" "CFL" [] -->
           (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> T"DOPER" "CFL" [])))
          -->
          ((T"MREG" "CFL" [] -->
            (T"MREG" "CFL" [] -->
             (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))) -->
           ((T"MREG" "CFL" [] -->
             (T"MREG" "CFL" [] -->
              (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))) -->
            ((T"MREG" "CFL" [] -->
              (T"MREG" "CFL" [] -->
               (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))) -->
             ((T"MREG" "CFL" [] -->
               (T"MREG" "CFL" [] -->
                (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))) -->
              ((T"MREG" "CFL" [] -->
                (T"MREG" "CFL" [] -->
                 (T"MEXP" "CFL" [] --> T"DOPER" "CFL" []))) -->
               ((T"MREG" "CFL" [] -->
                 (T"MREG" "CFL" [] -->
                  (T"cart" "fcp" [bool, T"i5" "words" []] -->
                   T"DOPER" "CFL" []))) -->
                ((T"MREG" "CFL" [] -->
                  (T"MREG" "CFL" [] -->
                   (T"cart" "fcp" [bool, T"i5" "words" []] -->
                    T"DOPER" "CFL" []))) -->
                 ((T"MREG" "CFL" [] -->
                   (T"MREG" "CFL" [] -->
                    (T"cart" "fcp" [bool, T"i5" "words" []] -->
                     T"DOPER" "CFL" []))) -->
                  ((T"MREG" "CFL" [] -->
                    (T"MREG" "CFL" [] -->
                     (T"cart" "fcp" [bool, T"i5" "words" []] -->
                      T"DOPER" "CFL" []))) -->
                   ((T"num" "num" [] -->
                     (T"list" "list" [T"num" "num" []] -->
                      T"DOPER" "CFL" [])) -->
                    ((T"num" "num" [] -->
                      (T"list" "list" [T"num" "num" []] -->
                       T"DOPER" "CFL" [])) --> bool))))))))))))))))),
   V"a0'" (T"MREG" "CFL" []),
   V"a1'" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"=" "min"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool))),
   V"a0'" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"a1'" (T"MREG" "CFL" []), V"a1'" (T"MEXP" "CFL" []),
   V"a2'" (T"MEXP" "CFL" []),
   V"a2'" (T"cart" "fcp" [bool, T"i5" "words" []]),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i5" "words" []] -->
      (T"cart" "fcp" [bool, T"i5" "words" []] --> bool))),
   V"a0'" (T"num" "num" []), V"a1'" (T"list" "list" [T"num" "num" []]),
   C"=" "min"
    ((T"list" "list" [T"num" "num" []] -->
      (T"list" "list" [T"num" "num" []] --> bool))),
   V"M" (T"DOPER" "CFL" []), V"M'" (T"DOPER" "CFL" []),
   V"f'"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       alpha))),
   V"f1'"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"MREG" "CFL" [] --> alpha))),
   V"f2'" ((T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha))),
   V"f3'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f4'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f5'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f6'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f7'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f8'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f9'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] --> (T"MEXP" "CFL" [] --> alpha)))),
   V"f10'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f11'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f12'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f13'"
    ((T"MREG" "CFL" [] -->
      (T"MREG" "CFL" [] -->
       (T"cart" "fcp" [bool, T"i5" "words" []] --> alpha)))),
   V"f14'"
    ((T"num" "num" [] --> (T"list" "list" [T"num" "num" []] --> alpha))),
   V"f15'"
    ((T"num" "num" [] --> (T"list" "list" [T"num" "num" []] --> alpha))),
   V"D" (T"DOPER" "CFL" []),
   V"p" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"M0" (T"MEXP" "CFL" []), V"M0" (T"MREG" "CFL" []),
   V"M1" (T"MEXP" "CFL" []), V"c" (T"cart" "fcp" [bool, T"i5" "words" []]),
   V"l" (T"list" "list" [T"num" "num" []]),
   V"f0"
    ((T"MREG" "CFL" [] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       alpha))),
   C"?" "bool" ((((T"DOPER" "CFL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"DOPER" "CFL" [] --> alpha)),
   C"!" "bool" ((((T"DOPER" "CFL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"DOPER" "CFL" [] --> bool)),
   V"CTL_STRUCTURE"
    (((T"list" "list" [T"DOPER" "CFL" []] --> T"CTL_STRUCTURE" "CFL" [])
      -->
      ((T"CTL_STRUCTURE" "CFL" [] -->
        (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])) -->
       ((T"prod" "pair"
          [T"MREG" "CFL" [],
           T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
         (T"CTL_STRUCTURE" "CFL" [] -->
          (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" []))) -->
        ((T"prod" "pair"
           [T"MREG" "CFL" [],
            T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
          (T"CTL_STRUCTURE" "CFL" [] --> T"CTL_STRUCTURE" "CFL" [])) -->
         bool))))), V"a'" (T"list" "list" [T"DOPER" "CFL" []]),
   C"=" "min"
    ((T"list" "list" [T"DOPER" "CFL" []] -->
      (T"list" "list" [T"DOPER" "CFL" []] --> bool))),
   V"a0'" (T"CTL_STRUCTURE" "CFL" []), V"a1'" (T"CTL_STRUCTURE" "CFL" []),
   V"a0'"
    (T"prod" "pair"
      [T"MREG" "CFL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]),
   V"a2'" (T"CTL_STRUCTURE" "CFL" []),
   C"=" "min"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"prod" "pair"
        [T"MREG" "CFL" [],
         T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
       bool))), V"M" (T"CTL_STRUCTURE" "CFL" []),
   V"M'" (T"CTL_STRUCTURE" "CFL" []),
   V"f'" ((T"list" "list" [T"DOPER" "CFL" []] --> alpha)),
   V"f1'"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"CTL_STRUCTURE" "CFL" [] --> alpha))),
   V"f2'"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] -->
       (T"CTL_STRUCTURE" "CFL" [] --> alpha)))),
   V"f3'"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] --> alpha))),
   V"C" (T"CTL_STRUCTURE" "CFL" []),
   V"l" (T"list" "list" [T"DOPER" "CFL" []]),
   C"?" "bool" (((T"CTL_STRUCTURE" "CFL" [] --> bool) --> bool)),
   V"C0" (T"CTL_STRUCTURE" "CFL" []),
   V"p"
    (T"prod" "pair"
      [T"MREG" "CFL" [],
       T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]]),
   V"f0" ((T"list" "list" [T"DOPER" "CFL" []] --> alpha)),
   C"!" "bool"
    ((((T"CTL_STRUCTURE" "CFL" [] -->
        (T"CTL_STRUCTURE" "CFL" [] --> (alpha --> (alpha --> alpha)))) -->
       bool) --> bool)),
   V"f1"
    ((T"CTL_STRUCTURE" "CFL" [] -->
      (T"CTL_STRUCTURE" "CFL" [] --> (alpha --> (alpha --> alpha))))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
        (T"CTL_STRUCTURE" "CFL" [] -->
         (T"CTL_STRUCTURE" "CFL" [] --> (alpha --> (alpha --> alpha)))))
       --> bool) --> bool)),
   V"f2"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] -->
       (T"CTL_STRUCTURE" "CFL" [] --> (alpha --> (alpha --> alpha)))))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"MREG" "CFL" [],
          T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
        (T"CTL_STRUCTURE" "CFL" [] --> (alpha --> alpha))) --> bool) -->
      bool)),
   V"f3"
    ((T"prod" "pair"
       [T"MREG" "CFL" [],
        T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]] -->
      (T"CTL_STRUCTURE" "CFL" [] --> (alpha --> alpha)))),
   C"?" "bool"
    ((((T"CTL_STRUCTURE" "CFL" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"CTL_STRUCTURE" "CFL" [] --> alpha)),
   C"!" "bool"
    ((((T"CTL_STRUCTURE" "CFL" [] --> bool) --> bool) --> bool)),
   V"P" ((T"CTL_STRUCTURE" "CFL" [] --> bool)),
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
   C"NIL" "list" (T"list" "list" [T"DOPER" "CFL" []]),
   V"v" (T"CTL_STRUCTURE" "CFL" []),
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
   V"S_cfl" (T"CTL_STRUCTURE" "CFL" []),
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
      bool)), V"S_t" (T"CTL_STRUCTURE" "CFL" []),
   V"S_f" (T"CTL_STRUCTURE" "CFL" []),
   C"COND" "bool" ((bool --> (bool --> (bool --> bool)))), V"S" (alpha),
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
   V"S_body" (T"CTL_STRUCTURE" "CFL" []),
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
       (%66 (\%10. ((%67 $1) ((\%10. (((%68 %19) ((%69 $0) (%70 (\%71.
       %72)))) (\%3. %73))) $0))))) (%74 (\%75. ((%67 $1) ((\%75. (((%68
       (%76 %19)) ((%69 (%77 (\%78. %72))) $0)) (\%3. %73))) $0)))))) ($1
       $0))))) ($0 $1)))))) $0)))`)
  val MEXP_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%79 (\%80. ((%81 (%82 (%83 $0))) $0)))) (%64 (\%84. ((%16
       ((\%60. (%61 (\%62. ((%63 (%64 (\%60. ((%63 ((%65 (%66 (\%10. ((%67
       $1) ((\%10. (((%68 %19) ((%69 $0) (%70 (\%71. %72)))) (\%3. %73)))
       $0))))) (%74 (\%75. ((%67 $1) ((\%75. (((%68 (%76 %19)) ((%69 (%77
       (\%78. %72))) $0)) (\%3. %73))) $0)))))) ($1 $0))))) ($0 $1)))))
       $0)) ((%67 (%83 (%82 $0))) $0)))))`)
  val CFL0_def =
    DT([], [],
       `((%85 %86) (\%10. (%82 ((\%10. (((%68 %19) ((%69 $0) (%70 (\%71.
       %72)))) (\%3. %73))) $0))))`)
  val CFL1_def =
    DT([], [],
       `((%87 %88) (\%75. (%82 ((\%75. (((%68 (%76 %19)) ((%69 (%77 (\%78.
       %72))) $0)) (\%3. %73))) $0))))`)
  val MR = DT([], [], `((%85 %89) %86)`)
  val MC = DT([], [], `((%87 %90) %88)`)
  val MEXP_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%91 (\%92. (%93 (\%94. (%9 (\%10. ((%53 (((%95 $2) $1) (%89
       $0))) ($2 $0))))))))) (%91 (\%92. (%93 (\%94. (%96 (\%75. ((%53
       (((%95 $2) $1) (%90 $0))) ($1 $0)))))))))`)
  val MEXP_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%10. ((%17 (%97 (%89 $0))) ((%98 (%5 (%6 %7))) (%36
       $0)))))) (%96 (\%75. ((%17 (%97 (%90 $0))) (%5 (%6 %7))))))`)
  val index_of_reg_def =
    DT(["DISK_THM"], [],
       `((%8 ((%17 (%99 %18)) %19)) ((%8 ((%17 (%99 %20)) (%5 (%6 %7))))
       ((%8 ((%17 (%99 %21)) (%5 (%22 %7)))) ((%8 ((%17 (%99 %23)) (%5 (%6
       (%6 %7))))) ((%8 ((%17 (%99 %24)) (%5 (%22 (%6 %7))))) ((%8 ((%17
       (%99 %25)) (%5 (%6 (%22 %7))))) ((%8 ((%17 (%99 %26)) (%5 (%22 (%22
       %7))))) ((%8 ((%17 (%99 %27)) (%5 (%6 (%6 (%6 %7)))))) ((%8 ((%17
       (%99 %28)) (%5 (%22 (%6 (%6 %7)))))) ((%8 ((%17 (%99 %29)) (%5 (%6
       (%22 (%6 %7)))))) ((%8 ((%17 (%99 %30)) (%5 (%22 (%22 (%6 %7))))))
       ((%8 ((%17 (%99 %31)) (%5 (%6 (%6 (%22 %7)))))) ((%8 ((%17 (%99
       %32)) (%5 (%22 (%6 (%22 %7)))))) ((%8 ((%17 (%99 %33)) (%5 (%6 (%22
       (%22 %7)))))) ((%17 (%99 %34)) (%5 (%22 (%22 (%22
       %7)))))))))))))))))))`)
  val from_reg_index_def =
    DT([], [],
       `(%14 (\%100. ((%11 (%101 $0)) (((%102 ((%17 $0) %19)) %18) (((%102
       ((%17 $0) (%5 (%6 %7)))) %20) (((%102 ((%17 $0) (%5 (%22 %7)))) %21)
       (((%102 ((%17 $0) (%5 (%6 (%6 %7))))) %23) (((%102 ((%17 $0) (%5
       (%22 (%6 %7))))) %24) (((%102 ((%17 $0) (%5 (%6 (%22 %7))))) %25)
       (((%102 ((%17 $0) (%5 (%22 (%22 %7))))) %26) (((%102 ((%17 $0) (%5
       (%6 (%6 (%6 %7)))))) %27) (((%102 ((%17 $0) (%5 (%22 (%6 (%6
       %7)))))) %28) (((%102 ((%17 $0) (%5 (%6 (%22 (%6 %7)))))) %29)
       (((%102 ((%17 $0) (%5 (%22 (%22 (%6 %7)))))) %30) (((%102 ((%17 $0)
       (%5 (%6 (%6 (%22 %7)))))) %31) (((%102 ((%17 $0) (%5 (%22 (%6 (%22
       %7)))))) %32) (((%102 ((%17 $0) (%5 (%6 (%22 (%22 %7)))))) %33)
       %34)))))))))))))))))`)
  val toREG_def =
    DT([], [], `(%9 (\%103. ((%104 (%105 $0)) (%106 (%99 $0)))))`)
  val toMEM_def =
    DT(["DISK_THM"], [],
       `(%14 (\%107. (%108 (\%109. ((%104 (%110 ((%111 $1) $0))) (%112
       ((%111 $1) $0)))))))`)
  val toEXP_def =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%103. ((%104 (%113 (%89 $0))) (%105 $0))))) (%96 (\%114.
       ((%104 (%113 (%90 $0))) (%115 $0)))))`)
  val tp_def = DT([], [], `((%17 %116) (%5 (%6 (%22 (%6 %7)))))`)
  val gp_def = DT([], [], `((%17 %117) (%5 (%22 (%22 (%6 %7)))))`)
  val fp_def = DT([], [], `((%17 %118) (%5 (%6 (%6 (%22 %7)))))`)
  val ip_def = DT([], [], `((%17 %119) (%5 (%22 (%6 (%22 %7)))))`)
  val sp_def = DT([], [], `((%17 %120) (%5 (%6 (%22 (%22 %7)))))`)
  val lr_def = DT([], [], `((%17 %121) (%5 (%22 (%22 (%22 %7)))))`)
  val DOPER_TY_DEF =
    DT(["DISK_THM"], [],
       `(%122 (\%123. ((%124 (\%125. (%126 (\%127. ((%63 (%128 (\%125.
       ((%63 ((%65 (%66 (\%129. (%130 (\%131. ((%132 $2) (((\%129. (\%131.
       (((%133 %19) ((%134 $1) ((%135 $0) ((%136 (%137 (\%138. %72)))
       ((%139 (%77 (\%78. %72))) ((%140 (%141 (\%142. %72))) ((%143 (%144
       (\%145. %72))) (%146 (\%147. %72))))))))) (\%3. %148)))) $1)
       $0))))))) ((%65 (%130 (\%149. (%66 (\%150. ((%132 $2) (((\%149.
       (\%150. (((%133 (%76 %19)) ((%134 $0) ((%135 $1) ((%136 (%137
       (\%138. %72))) ((%139 (%77 (\%78. %72))) ((%140 (%141 (\%142. %72)))
       ((%143 (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3.
       %148)))) $1) $0))))))) ((%65 (%66 (\%129. (%151 (\%152. ((%132 $2)
       (((\%129. (\%152. (((%133 (%76 (%76 %19))) ((%134 $1) ((%135 (%153
       (\%154. %72))) ((%136 $0) ((%139 (%77 (\%78. %72))) ((%140 (%141
       (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146 (\%147.
       %72))))))))) (\%3. %148)))) $1) $0))))))) ((%65 (%66 (\%129. (%66
       (\%150. (%151 (\%155. ((%132 $3) ((((\%129. (\%150. (\%155. (((%133
       (%76 (%76 (%76 %19)))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136
       $0) ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145.
       %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1)
       $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%151 (\%155. ((%132 $3)
       ((((\%129. (\%150. (\%155. (((%133 (%76 (%76 (%76 (%76 %19)))))
       ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0) ((%139 $1) ((%140
       (%141 (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146 (\%147.
       %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65 (%66 (\%129.
       (%66 (\%150. (%151 (\%155. ((%132 $3) ((((\%129. (\%150. (\%155.
       (((%133 (%76 (%76 (%76 (%76 (%76 %19)))))) ((%134 $2) ((%135 (%153
       (\%154. %72))) ((%136 $0) ((%139 $1) ((%140 (%141 (\%142. %72)))
       ((%143 (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3.
       %148))))) $2) $1) $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%151
       (\%155. ((%132 $3) ((((\%129. (\%150. (\%155. (((%133 (%76 (%76 (%76
       (%76 (%76 (%76 %19))))))) ((%134 $2) ((%135 (%153 (\%154. %72)))
       ((%136 $0) ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144
       (\%145. %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1)
       $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%151 (\%155. ((%132 $3)
       ((((\%129. (\%150. (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 %19)))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0)
       ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72)))
       (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65
       (%66 (\%129. (%66 (\%150. (%151 (\%155. ((%132 $3) ((((\%129.
       (\%150. (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       %19))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0)
       ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72)))
       (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65
       (%66 (\%129. (%66 (\%150. (%151 (\%155. ((%132 $3) ((((\%129.
       (\%150. (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       %19)))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0)
       ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72)))
       (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65
       (%66 (\%129. (%66 (\%150. (%156 (\%157. ((%132 $3) ((((\%129.
       (\%150. (\%157. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 %19))))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136
       (%137 (\%138. %72))) ((%139 $1) ((%140 $0) ((%143 (%144 (\%145.
       %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1)
       $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%156 (\%157. ((%132 $3)
       ((((\%129. (\%150. (\%157. (((%133 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 (%76 (%76 (%76 (%76 %19)))))))))))) ((%134 $2) ((%135 (%153
       (\%154. %72))) ((%136 (%137 (\%138. %72))) ((%139 $1) ((%140 $0)
       ((%143 (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3.
       %148))))) $2) $1) $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%156
       (\%157. ((%132 $3) ((((\%129. (\%150. (\%157. (((%133 (%76 (%76 (%76
       (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 %19))))))))))))) ((%134
       $2) ((%135 (%153 (\%154. %72))) ((%136 (%137 (\%138. %72))) ((%139
       $1) ((%140 $0) ((%143 (%144 (\%145. %72))) (%146 (\%147.
       %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65 (%66 (\%129.
       (%66 (\%150. (%156 (\%157. ((%132 $3) ((((\%129. (\%150. (\%157.
       (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 %19)))))))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136
       (%137 (\%138. %72))) ((%139 $1) ((%140 $0) ((%143 (%144 (\%145.
       %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1)
       $0))))))))) ((%65 (%158 (\%159. (%160 (\%161. ((%132 $2) (((\%159.
       (\%161. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 (%76 (%76 (%76 %19))))))))))))))) ((%134 (%77 (\%78. %72)))
       ((%135 (%153 (\%154. %72))) ((%136 (%137 (\%138. %72))) ((%139 (%77
       (\%78. %72))) ((%140 (%141 (\%142. %72))) ((%143 $1) $0))))))) (\%3.
       %148)))) $1) $0))))))) (%158 (\%159. (%160 (\%161. ((%132 $2)
       (((\%159. (\%161. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 (%76 (%76 (%76 (%76 (%76 (%76 %19)))))))))))))))) ((%134 (%77
       (\%78. %72))) ((%135 (%153 (\%154. %72))) ((%136 (%137 (\%138.
       %72))) ((%139 (%77 (\%78. %72))) ((%140 (%141 (\%142. %72))) ((%143
       $1) $0))))))) (\%3. %148)))) $1) $0)))))))))))))))))))))) ($1
       $0))))) ($0 $1)))))) $0)))`)
  val DOPER_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%162 (\%163. ((%164 (%165 (%166 $0))) $0)))) (%128 (\%167.
       ((%16 ((\%125. (%126 (\%127. ((%63 (%128 (\%125. ((%63 ((%65 (%66
       (\%129. (%130 (\%131. ((%132 $2) (((\%129. (\%131. (((%133 %19)
       ((%134 $1) ((%135 $0) ((%136 (%137 (\%138. %72))) ((%139 (%77 (\%78.
       %72))) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146
       (\%147. %72))))))))) (\%3. %148)))) $1) $0))))))) ((%65 (%130
       (\%149. (%66 (\%150. ((%132 $2) (((\%149. (\%150. (((%133 (%76 %19))
       ((%134 $0) ((%135 $1) ((%136 (%137 (\%138. %72))) ((%139 (%77 (\%78.
       %72))) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146
       (\%147. %72))))))))) (\%3. %148)))) $1) $0))))))) ((%65 (%66 (\%129.
       (%151 (\%152. ((%132 $2) (((\%129. (\%152. (((%133 (%76 (%76 %19)))
       ((%134 $1) ((%135 (%153 (\%154. %72))) ((%136 $0) ((%139 (%77 (\%78.
       %72))) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146
       (\%147. %72))))))))) (\%3. %148)))) $1) $0))))))) ((%65 (%66 (\%129.
       (%66 (\%150. (%151 (\%155. ((%132 $3) ((((\%129. (\%150. (\%155.
       (((%133 (%76 (%76 (%76 %19)))) ((%134 $2) ((%135 (%153 (\%154.
       %72))) ((%136 $0) ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143
       (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2)
       $1) $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%151 (\%155. ((%132
       $3) ((((\%129. (\%150. (\%155. (((%133 (%76 (%76 (%76 (%76 %19)))))
       ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0) ((%139 $1) ((%140
       (%141 (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146 (\%147.
       %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65 (%66 (\%129.
       (%66 (\%150. (%151 (\%155. ((%132 $3) ((((\%129. (\%150. (\%155.
       (((%133 (%76 (%76 (%76 (%76 (%76 %19)))))) ((%134 $2) ((%135 (%153
       (\%154. %72))) ((%136 $0) ((%139 $1) ((%140 (%141 (\%142. %72)))
       ((%143 (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3.
       %148))))) $2) $1) $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%151
       (\%155. ((%132 $3) ((((\%129. (\%150. (\%155. (((%133 (%76 (%76 (%76
       (%76 (%76 (%76 %19))))))) ((%134 $2) ((%135 (%153 (\%154. %72)))
       ((%136 $0) ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144
       (\%145. %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1)
       $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%151 (\%155. ((%132 $3)
       ((((\%129. (\%150. (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 %19)))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0)
       ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72)))
       (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65
       (%66 (\%129. (%66 (\%150. (%151 (\%155. ((%132 $3) ((((\%129.
       (\%150. (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       %19))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0)
       ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72)))
       (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65
       (%66 (\%129. (%66 (\%150. (%151 (\%155. ((%132 $3) ((((\%129.
       (\%150. (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       %19)))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0)
       ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72)))
       (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65
       (%66 (\%129. (%66 (\%150. (%156 (\%157. ((%132 $3) ((((\%129.
       (\%150. (\%157. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 %19))))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136
       (%137 (\%138. %72))) ((%139 $1) ((%140 $0) ((%143 (%144 (\%145.
       %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1)
       $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%156 (\%157. ((%132 $3)
       ((((\%129. (\%150. (\%157. (((%133 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 (%76 (%76 (%76 (%76 %19)))))))))))) ((%134 $2) ((%135 (%153
       (\%154. %72))) ((%136 (%137 (\%138. %72))) ((%139 $1) ((%140 $0)
       ((%143 (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3.
       %148))))) $2) $1) $0))))))))) ((%65 (%66 (\%129. (%66 (\%150. (%156
       (\%157. ((%132 $3) ((((\%129. (\%150. (\%157. (((%133 (%76 (%76 (%76
       (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 %19))))))))))))) ((%134
       $2) ((%135 (%153 (\%154. %72))) ((%136 (%137 (\%138. %72))) ((%139
       $1) ((%140 $0) ((%143 (%144 (\%145. %72))) (%146 (\%147.
       %72))))))))) (\%3. %148))))) $2) $1) $0))))))))) ((%65 (%66 (\%129.
       (%66 (\%150. (%156 (\%157. ((%132 $3) ((((\%129. (\%150. (\%157.
       (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 %19)))))))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136
       (%137 (\%138. %72))) ((%139 $1) ((%140 $0) ((%143 (%144 (\%145.
       %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1)
       $0))))))))) ((%65 (%158 (\%159. (%160 (\%161. ((%132 $2) (((\%159.
       (\%161. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 (%76 (%76 (%76 %19))))))))))))))) ((%134 (%77 (\%78. %72)))
       ((%135 (%153 (\%154. %72))) ((%136 (%137 (\%138. %72))) ((%139 (%77
       (\%78. %72))) ((%140 (%141 (\%142. %72))) ((%143 $1) $0))))))) (\%3.
       %148)))) $1) $0))))))) (%158 (\%159. (%160 (\%161. ((%132 $2)
       (((\%159. (\%161. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 (%76 (%76 (%76 (%76 (%76 (%76 %19)))))))))))))))) ((%134 (%77
       (\%78. %72))) ((%135 (%153 (\%154. %72))) ((%136 (%137 (\%138.
       %72))) ((%139 (%77 (\%78. %72))) ((%140 (%141 (\%142. %72))) ((%143
       $1) $0))))))) (\%3. %148)))) $1) $0)))))))))))))))))))))) ($1
       $0))))) ($0 $1))))) $0)) ((%132 (%166 (%165 $0))) $0)))))`)
  val CFL2_def =
    DT([], [],
       `((%168 %169) (\%129. (\%131. (%165 (((\%129. (\%131. (((%133 %19)
       ((%134 $1) ((%135 $0) ((%136 (%137 (\%138. %72))) ((%139 (%77 (\%78.
       %72))) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146
       (\%147. %72))))))))) (\%3. %148)))) $1) $0)))))`)
  val CFL3_def =
    DT([], [],
       `((%170 %171) (\%149. (\%150. (%165 (((\%149. (\%150. (((%133 (%76
       %19)) ((%134 $0) ((%135 $1) ((%136 (%137 (\%138. %72))) ((%139 (%77
       (\%78. %72))) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145.
       %72))) (%146 (\%147. %72))))))))) (\%3. %148)))) $1) $0)))))`)
  val CFL4_def =
    DT([], [],
       `((%172 %173) (\%129. (\%152. (%165 (((\%129. (\%152. (((%133 (%76
       (%76 %19))) ((%134 $1) ((%135 (%153 (\%154. %72))) ((%136 $0) ((%139
       (%77 (\%78. %72))) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145.
       %72))) (%146 (\%147. %72))))))))) (\%3. %148)))) $1) $0)))))`)
  val CFL5_def =
    DT([], [],
       `((%174 %175) (\%129. (\%150. (\%155. (%165 ((((\%129. (\%150.
       (\%155. (((%133 (%76 (%76 (%76 %19)))) ((%134 $2) ((%135 (%153
       (\%154. %72))) ((%136 $0) ((%139 $1) ((%140 (%141 (\%142. %72)))
       ((%143 (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3.
       %148))))) $2) $1) $0))))))`)
  val CFL6_def =
    DT([], [],
       `((%174 %176) (\%129. (\%150. (\%155. (%165 ((((\%129. (\%150.
       (\%155. (((%133 (%76 (%76 (%76 (%76 %19))))) ((%134 $2) ((%135 (%153
       (\%154. %72))) ((%136 $0) ((%139 $1) ((%140 (%141 (\%142. %72)))
       ((%143 (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3.
       %148))))) $2) $1) $0))))))`)
  val CFL7_def =
    DT([], [],
       `((%174 %177) (\%129. (\%150. (\%155. (%165 ((((\%129. (\%150.
       (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 %19)))))) ((%134 $2) ((%135
       (%153 (\%154. %72))) ((%136 $0) ((%139 $1) ((%140 (%141 (\%142.
       %72))) ((%143 (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3.
       %148))))) $2) $1) $0))))))`)
  val CFL8_def =
    DT([], [],
       `((%174 %178) (\%129. (\%150. (\%155. (%165 ((((\%129. (\%150.
       (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 %19))))))) ((%134 $2)
       ((%135 (%153 (\%154. %72))) ((%136 $0) ((%139 $1) ((%140 (%141
       (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146 (\%147.
       %72))))))))) (\%3. %148))))) $2) $1) $0))))))`)
  val CFL9_def =
    DT([], [],
       `((%174 %179) (\%129. (\%150. (\%155. (%165 ((((\%129. (\%150.
       (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 %19))))))))
       ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0) ((%139 $1) ((%140
       (%141 (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146 (\%147.
       %72))))))))) (\%3. %148))))) $2) $1) $0))))))`)
  val CFL10_def =
    DT([], [],
       `((%174 %180) (\%129. (\%150. (\%155. (%165 ((((\%129. (\%150.
       (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 %19)))))))))
       ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0) ((%139 $1) ((%140
       (%141 (\%142. %72))) ((%143 (%144 (\%145. %72))) (%146 (\%147.
       %72))))))))) (\%3. %148))))) $2) $1) $0))))))`)
  val CFL11_def =
    DT([], [],
       `((%174 %181) (\%129. (\%150. (\%155. (%165 ((((\%129. (\%150.
       (\%155. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       %19)))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 $0)
       ((%139 $1) ((%140 (%141 (\%142. %72))) ((%143 (%144 (\%145. %72)))
       (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1) $0))))))`)
  val CFL12_def =
    DT([], [],
       `((%182 %183) (\%129. (\%150. (\%157. (%165 ((((\%129. (\%150.
       (\%157. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       %19))))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136 (%137
       (\%138. %72))) ((%139 $1) ((%140 $0) ((%143 (%144 (\%145. %72)))
       (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1) $0))))))`)
  val CFL13_def =
    DT([], [],
       `((%182 %184) (\%129. (\%150. (\%157. (%165 ((((\%129. (\%150.
       (\%157. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 %19)))))))))))) ((%134 $2) ((%135 (%153 (\%154. %72))) ((%136
       (%137 (\%138. %72))) ((%139 $1) ((%140 $0) ((%143 (%144 (\%145.
       %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1) $0))))))`)
  val CFL14_def =
    DT([], [],
       `((%182 %185) (\%129. (\%150. (\%157. (%165 ((((\%129. (\%150.
       (\%157. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 (%76 %19))))))))))))) ((%134 $2) ((%135 (%153 (\%154. %72)))
       ((%136 (%137 (\%138. %72))) ((%139 $1) ((%140 $0) ((%143 (%144
       (\%145. %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2) $1)
       $0))))))`)
  val CFL15_def =
    DT([], [],
       `((%182 %186) (\%129. (\%150. (\%157. (%165 ((((\%129. (\%150.
       (\%157. (((%133 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 (%76 (%76 %19)))))))))))))) ((%134 $2) ((%135 (%153 (\%154.
       %72))) ((%136 (%137 (\%138. %72))) ((%139 $1) ((%140 $0) ((%143
       (%144 (\%145. %72))) (%146 (\%147. %72))))))))) (\%3. %148))))) $2)
       $1) $0))))))`)
  val CFL16_def =
    DT([], [],
       `((%187 %188) (\%159. (\%161. (%165 (((\%159. (\%161. (((%133 (%76
       (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       %19))))))))))))))) ((%134 (%77 (\%78. %72))) ((%135 (%153 (\%154.
       %72))) ((%136 (%137 (\%138. %72))) ((%139 (%77 (\%78. %72))) ((%140
       (%141 (\%142. %72))) ((%143 $1) $0))))))) (\%3. %148)))) $1)
       $0)))))`)
  val CFL17_def =
    DT([], [],
       `((%187 %189) (\%159. (\%161. (%165 (((\%159. (\%161. (((%133 (%76
       (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76 (%76
       (%76 %19)))))))))))))))) ((%134 (%77 (\%78. %72))) ((%135 (%153
       (\%154. %72))) ((%136 (%137 (\%138. %72))) ((%139 (%77 (\%78. %72)))
       ((%140 (%141 (\%142. %72))) ((%143 $1) $0))))))) (\%3. %148)))) $1)
       $0)))))`)
  val MLDR = DT([], [], `((%168 %190) %169)`)
  val MSTR = DT([], [], `((%170 %191) %171)`)
  val MMOV = DT([], [], `((%172 %192) %173)`)
  val MADD = DT([], [], `((%174 %193) %175)`)
  val MSUB = DT([], [], `((%174 %194) %176)`)
  val MRSB = DT([], [], `((%174 %195) %177)`)
  val MMUL = DT([], [], `((%174 %196) %178)`)
  val MAND = DT([], [], `((%174 %197) %179)`)
  val MORR = DT([], [], `((%174 %198) %180)`)
  val MEOR = DT([], [], `((%174 %199) %181)`)
  val MLSL = DT([], [], `((%182 %200) %183)`)
  val MLSR = DT([], [], `((%182 %201) %184)`)
  val MASR = DT([], [], `((%182 %202) %185)`)
  val MROR = DT([], [], `((%182 %203) %186)`)
  val MPUSH = DT([], [], `((%187 %204) %188)`)
  val MPOP = DT([], [], `((%187 %205) %189)`)
  val DOPER_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%206 (\%207. (%208 (\%209. (%210 (\%211. (%212 (\%213. (%212
       (\%214. (%212 (\%215. (%212 (\%216. (%212 (\%217. (%212 (\%218.
       (%212 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223. (%220
       (\%224. (%225 (\%226. (%225 (\%227. (%9 (\%129. (%228 (\%131. ((%53
       (((((((((((((((((%229 $17) $16) $15) $14) $13) $12) $11) $10) $9)
       $8) $7) $6) $5) $4) $3) $2) ((%190 $1) $0))) (($17 $1)
       $0))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%228 (\%149. (%9 (\%150. ((%53 (((((((((((((((((%229
       $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3)
       $2) ((%191 $1) $0))) (($16 $1)
       $0))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%79 (\%152. ((%53 (((((((((((((((((%229
       $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3)
       $2) ((%192 $1) $0))) (($15 $1)
       $0))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%193 $2) $1) $0))) ((($15 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%194 $2) $1) $0))) ((($14 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%195 $2) $1) $0))) ((($13 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%196 $2) $1) $0))) ((($12 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%197 $2) $1) $0))) ((($11 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%198 $2) $1) $0))) ((($10 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%199 $2) $1) $0))) ((($9 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%230 (\%157. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%200 $2) $1) $0))) ((($8 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%230 (\%157. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%201 $2) $1) $0))) ((($7 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%230 (\%157. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%202 $2) $1) $0))) ((($6 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%9 (\%129. (%9 (\%150. (%230 (\%157. ((%53
       (((((((((((((((((%229 $18) $17) $16) $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) (((%203 $2) $1) $0))) ((($5 $2) $1)
       $0))))))))))))))))))))))))))))))))))))))))) ((%8 (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%14 (\%159. (%231 (\%161. ((%53 (((((((((((((((((%229
       $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3)
       $2) ((%204 $1) $0))) (($3 $1)
       $0))))))))))))))))))))))))))))))))))))))) (%206 (\%207. (%208
       (\%209. (%210 (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215.
       (%212 (\%216. (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220
       (\%221. (%220 (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226.
       (%225 (\%227. (%14 (\%159. (%231 (\%161. ((%53 (((((((((((((((((%229
       $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3)
       $2) ((%205 $1) $0))) (($2 $1)
       $0)))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val DOPER_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%129. (%228 (\%131. ((%17 (%232 ((%190 $1) $0))) ((%98
       (%5 (%6 %7))) ((%98 (%36 $1)) ((%233 (\%234. (\%235. ((%98 ((\%234.
       $0) $1)) (%236 $0))))) $0))))))))) ((%8 (%228 (\%149. (%9 (\%150.
       ((%17 (%232 ((%191 $1) $0))) ((%98 (%5 (%6 %7))) ((%98 ((%233
       (\%234. (\%235. ((%98 ((\%234. $0) $1)) (%236 $0))))) $1)) (%36
       $0))))))))) ((%8 (%9 (\%129. (%79 (\%152. ((%17 (%232 ((%192 $1)
       $0))) ((%98 (%5 (%6 %7))) ((%98 (%36 $1)) (%97 $0))))))))) ((%8 (%9
       (\%129. (%9 (\%150. (%79 (\%155. ((%17 (%232 (((%193 $2) $1) $0)))
       ((%98 (%5 (%6 %7))) ((%98 (%36 $2)) ((%98 (%36 $1)) (%97
       $0)))))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%17 (%232
       (((%194 $2) $1) $0))) ((%98 (%5 (%6 %7))) ((%98 (%36 $2)) ((%98 (%36
       $1)) (%97 $0)))))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155.
       ((%17 (%232 (((%195 $2) $1) $0))) ((%98 (%5 (%6 %7))) ((%98 (%36
       $2)) ((%98 (%36 $1)) (%97 $0)))))))))))) ((%8 (%9 (\%129. (%9
       (\%150. (%79 (\%155. ((%17 (%232 (((%196 $2) $1) $0))) ((%98 (%5 (%6
       %7))) ((%98 (%36 $2)) ((%98 (%36 $1)) (%97 $0)))))))))))) ((%8 (%9
       (\%129. (%9 (\%150. (%79 (\%155. ((%17 (%232 (((%197 $2) $1) $0)))
       ((%98 (%5 (%6 %7))) ((%98 (%36 $2)) ((%98 (%36 $1)) (%97
       $0)))))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%17 (%232
       (((%198 $2) $1) $0))) ((%98 (%5 (%6 %7))) ((%98 (%36 $2)) ((%98 (%36
       $1)) (%97 $0)))))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155.
       ((%17 (%232 (((%199 $2) $1) $0))) ((%98 (%5 (%6 %7))) ((%98 (%36
       $2)) ((%98 (%36 $1)) (%97 $0)))))))))))) ((%8 (%9 (\%129. (%9
       (\%150. (%230 (\%157. ((%17 (%232 (((%200 $2) $1) $0))) ((%98 (%5
       (%6 %7))) ((%98 (%36 $2)) (%36 $1))))))))))) ((%8 (%9 (\%129. (%9
       (\%150. (%230 (\%157. ((%17 (%232 (((%201 $2) $1) $0))) ((%98 (%5
       (%6 %7))) ((%98 (%36 $2)) (%36 $1))))))))))) ((%8 (%9 (\%129. (%9
       (\%150. (%230 (\%157. ((%17 (%232 (((%202 $2) $1) $0))) ((%98 (%5
       (%6 %7))) ((%98 (%36 $2)) (%36 $1))))))))))) ((%8 (%9 (\%129. (%9
       (\%150. (%230 (\%157. ((%17 (%232 (((%203 $2) $1) $0))) ((%98 (%5
       (%6 %7))) ((%98 (%36 $2)) (%36 $1))))))))))) ((%8 (%14 (\%159. (%231
       (\%161. ((%17 (%232 ((%204 $1) $0))) ((%98 (%5 (%6 %7))) ((%98 $1)
       ((%237 (\%234. $0)) $0))))))))) (%14 (\%159. (%231 (\%161. ((%17
       (%232 ((%205 $1) $0))) ((%98 (%5 (%6 %7))) ((%98 $1) ((%237 (\%234.
       $0)) $0)))))))))))))))))))))))`)
  val CTL_STRUCTURE_TY_DEF =
    DT(["DISK_THM"], [],
       `(%238 (\%239. ((%240 (\%241. (%242 (\%243. ((%63 (%244 (\%241.
       ((%63 ((%65 (%245 (\%246. ((%247 $1) ((\%246. (((%248 %19) ((%249
       $0) (%250 (\%251. %72)))) (\%3. %252))) $0))))) ((%65 (%253 (\%254.
       (%253 (\%255. ((%8 ((%247 $2) (((\%254. (\%255. (((%248 (%76 %19))
       ((%249 (%256 (\%257. %72))) (%250 (\%251. %72)))) ((%258 $1) ((%258
       $0) (\%3. %252)))))) $1) $0))) ((%8 ($3 $1)) ($3 $0)))))))) ((%65
       (%259 (\%260. (%253 (\%255. (%253 (\%261. ((%8 ((%247 $3) ((((\%260.
       (\%255. (\%261. (((%248 (%76 (%76 %19))) ((%249 (%256 (\%257. %72)))
       $2)) ((%258 $1) ((%258 $0) (\%3. %252))))))) $2) $1) $0))) ((%8 ($4
       $1)) ($4 $0)))))))))) (%259 (\%260. (%253 (\%255. ((%8 ((%247 $2)
       (((\%260. (\%255. (((%248 (%76 (%76 (%76 %19)))) ((%249 (%256
       (\%257. %72))) $1)) ((%258 $0) (\%3. %252))))) $1) $0))) ($3
       $0)))))))))) ($1 $0))))) ($0 $1)))))) $0)))`)
  val CTL_STRUCTURE_repfns =
    DT(["DISK_THM"], [],
       `((%8 (%262 (\%263. ((%264 (%265 (%266 $0))) $0)))) (%244 (\%267.
       ((%16 ((\%241. (%242 (\%243. ((%63 (%244 (\%241. ((%63 ((%65 (%245
       (\%246. ((%247 $1) ((\%246. (((%248 %19) ((%249 $0) (%250 (\%251.
       %72)))) (\%3. %252))) $0))))) ((%65 (%253 (\%254. (%253 (\%255. ((%8
       ((%247 $2) (((\%254. (\%255. (((%248 (%76 %19)) ((%249 (%256 (\%257.
       %72))) (%250 (\%251. %72)))) ((%258 $1) ((%258 $0) (\%3. %252))))))
       $1) $0))) ((%8 ($3 $1)) ($3 $0)))))))) ((%65 (%259 (\%260. (%253
       (\%255. (%253 (\%261. ((%8 ((%247 $3) ((((\%260. (\%255. (\%261.
       (((%248 (%76 (%76 %19))) ((%249 (%256 (\%257. %72))) $2)) ((%258 $1)
       ((%258 $0) (\%3. %252))))))) $2) $1) $0))) ((%8 ($4 $1)) ($4
       $0)))))))))) (%259 (\%260. (%253 (\%255. ((%8 ((%247 $2) (((\%260.
       (\%255. (((%248 (%76 (%76 (%76 %19)))) ((%249 (%256 (\%257. %72)))
       $1)) ((%258 $0) (\%3. %252))))) $1) $0))) ($3 $0)))))))))) ($1
       $0))))) ($0 $1))))) $0)) ((%247 (%266 (%265 $0))) $0)))))`)
  val CFL18_def =
    DT([], [],
       `((%268 %269) (\%246. (%265 ((\%246. (((%248 %19) ((%249 $0) (%250
       (\%251. %72)))) (\%3. %252))) $0))))`)
  val CFL19_def =
    DT([], [],
       `((%270 %271) (\%272. (\%273. (%265 (((\%254. (\%255. (((%248 (%76
       %19)) ((%249 (%256 (\%257. %72))) (%250 (\%251. %72)))) ((%258 $1)
       ((%258 $0) (\%3. %252)))))) (%266 $1)) (%266 $0))))))`)
  val CFL20_def =
    DT([], [],
       `((%274 %275) (\%260. (\%273. (\%276. (%265 ((((\%260. (\%255.
       (\%261. (((%248 (%76 (%76 %19))) ((%249 (%256 (\%257. %72))) $2))
       ((%258 $1) ((%258 $0) (\%3. %252))))))) $2) (%266 $1)) (%266
       $0)))))))`)
  val CFL21_def =
    DT([], [],
       `((%277 %278) (\%260. (\%273. (%265 (((\%260. (\%255. (((%248 (%76
       (%76 (%76 %19)))) ((%249 (%256 (\%257. %72))) $1)) ((%258 $0) (\%3.
       %252))))) $1) (%266 $0))))))`)
  val BLK = DT([], [], `((%268 %279) %269)`)
  val SC = DT([], [], `((%270 %280) %271)`)
  val CJ = DT([], [], `((%274 %281) %275)`)
  val TR = DT([], [], `((%277 %282) %278)`)
  val CTL_STRUCTURE_case_def =
    DT(["DISK_THM"], [],
       `((%8 (%283 (\%284. (%285 (\%286. (%287 (\%288. (%289 (\%290. (%291
       (\%246. ((%53 (((((%292 $4) $3) $2) $1) (%279 $0))) ($4
       $0))))))))))))) ((%8 (%283 (\%284. (%285 (\%286. (%287 (\%288. (%289
       (\%290. (%262 (\%272. (%262 (\%273. ((%53 (((((%292 $5) $4) $3) $2)
       ((%280 $1) $0))) (($4 $1) $0))))))))))))))) ((%8 (%283 (\%284. (%285
       (\%286. (%287 (\%288. (%289 (\%290. (%293 (\%260. (%262 (\%273.
       (%262 (\%276. ((%53 (((((%292 $6) $5) $4) $3) (((%281 $2) $1) $0)))
       ((($4 $2) $1) $0))))))))))))))))) (%283 (\%284. (%285 (\%286. (%287
       (\%288. (%289 (\%290. (%293 (\%260. (%262 (\%273. ((%53 (((((%292
       $5) $4) $3) $2) ((%282 $1) $0))) (($2 $1) $0)))))))))))))))))`)
  val CTL_STRUCTURE_size_def =
    DT(["DISK_THM"], [],
       `((%8 (%291 (\%246. ((%17 (%294 (%279 $0))) ((%98 (%5 (%6 %7)))
       ((%295 %232) $0)))))) ((%8 (%262 (\%272. (%262 (\%273. ((%17 (%294
       ((%280 $1) $0))) ((%98 (%5 (%6 %7))) ((%98 (%294 $1)) (%294
       $0))))))))) ((%8 (%293 (\%260. (%262 (\%273. (%262 (\%276. ((%17
       (%294 (((%281 $2) $1) $0))) ((%98 (%5 (%6 %7))) ((%98 ((%296 (\%35.
       (\%297. ((%98 (%36 $1)) ((%298 (\%299. (\%300. ((%98 (%301 $1)) (%97
       $0))))) $0))))) $2)) ((%98 (%294 $1)) (%294 $0)))))))))))) (%293
       (\%260. (%262 (\%273. ((%17 (%294 ((%282 $1) $0))) ((%98 (%5 (%6
       %7))) ((%98 ((%296 (\%35. (\%297. ((%98 (%36 $1)) ((%298 (\%299.
       (\%300. ((%98 (%301 $1)) (%97 $0))))) $0))))) $1)) (%294
       $0)))))))))))`)
  val pushL_def =
    DT([], [],
       `(%302 (\%303. (%14 (\%304. (%231 (\%305. ((%306 (((%307 $2) $1)
       $0)) (((%308 (%309 (((%310 (%311 (\%312. (\%100. (\%313. ((%314
       (((%308 $2) (%112 ((%111 $4) (%315 $1)))) ((%316 $5) $0))) ((%98 $1)
       (%5 (%6 %7))))))))) ((%314 $2) %19)) (%317 ((%318 %106) $0)))))
       (%106 $1)) ((%319 ((%316 $2) (%106 $1))) (%320 (%321 $0)))))))))))`)
  val popL_def =
    DT([], [],
       `(%302 (\%303. (%14 (\%304. (%231 (\%305. ((%306 (((%322 $2) $1)
       $0)) (((%308 (%309 (((%310 (%311 (\%312. (\%100. (\%313. ((%314
       (((%308 $2) $0) ((%316 $5) (%112 ((%111 $4) (%323 ((%98 $1) (%5 (%6
       %7))))))))) ((%98 $1) (%5 (%6 %7))))))))) ((%314 $2) %19)) ((%318
       %106) $0)))) (%106 $1)) ((%324 ((%316 $2) (%106 $1))) (%320 (%321
       $0)))))))))))`)
  val mdecode_def =
    DT(["DISK_THM"], [],
       `((%8 (%302 (\%303. (%9 (\%325. (%228 (\%326. ((%306 ((%327 $2)
       ((%190 $1) $0))) (((%308 $2) (%105 $1)) ((%316 $2) (%110
       $0))))))))))) ((%8 (%302 (\%303. (%228 (\%328. (%9 (\%329. ((%306
       ((%327 $2) ((%191 $1) $0))) (((%308 $2) (%110 $1)) ((%316 $2) (%105
       $0))))))))))) ((%8 (%302 (\%303. (%9 (\%325. (%79 (\%330. ((%306
       ((%327 $2) ((%192 $1) $0))) (((%308 $2) (%105 $1)) ((%316 $2) (%113
       $0))))))))))) ((%8 (%302 (\%303. (%9 (\%325. (%9 (\%331. (%79
       (\%332. ((%306 ((%327 $3) (((%193 $2) $1) $0))) (((%308 $3) (%105
       $2)) ((%324 ((%316 $3) (%105 $1))) ((%316 $3) (%113 $0))))))))))))))
       ((%8 (%302 (\%303. (%9 (\%325. (%9 (\%331. (%79 (\%332. ((%306
       ((%327 $3) (((%194 $2) $1) $0))) (((%308 $3) (%105 $2)) ((%319
       ((%316 $3) (%105 $1))) ((%316 $3) (%113 $0)))))))))))))) ((%8 (%302
       (\%303. (%9 (\%325. (%9 (\%331. (%79 (\%332. ((%306 ((%327 $3)
       (((%195 $2) $1) $0))) (((%308 $3) (%105 $2)) ((%319 ((%316 $3) (%113
       $0))) ((%316 $3) (%105 $1)))))))))))))) ((%8 (%302 (\%303. (%9
       (\%325. (%9 (\%331. (%79 (\%332. ((%306 ((%327 $3) (((%196 $2) $1)
       $0))) (((%308 $3) (%105 $2)) ((%333 ((%316 $3) (%105 $1))) ((%316
       $3) (%113 $0)))))))))))))) ((%8 (%302 (\%303. (%9 (\%325. (%9
       (\%331. (%79 (\%332. ((%306 ((%327 $3) (((%197 $2) $1) $0))) (((%308
       $3) (%105 $2)) ((%334 ((%316 $3) (%105 $1))) ((%316 $3) (%113
       $0)))))))))))))) ((%8 (%302 (\%303. (%9 (\%325. (%9 (\%331. (%79
       (\%332. ((%306 ((%327 $3) (((%198 $2) $1) $0))) (((%308 $3) (%105
       $2)) ((%335 ((%316 $3) (%105 $1))) ((%316 $3) (%113 $0))))))))))))))
       ((%8 (%302 (\%303. (%9 (\%325. (%9 (\%331. (%79 (\%332. ((%306
       ((%327 $3) (((%199 $2) $1) $0))) (((%308 $3) (%105 $2)) ((%336
       ((%316 $3) (%105 $1))) ((%316 $3) (%113 $0)))))))))))))) ((%8 (%302
       (\%303. (%9 (\%325. (%9 (\%337. (%230 (\%338. ((%306 ((%327 $3)
       (((%200 $2) $1) $0))) (((%308 $3) (%105 $2)) ((%339 ((%316 $3) (%105
       $1))) (%340 $0))))))))))))) ((%8 (%302 (\%303. (%9 (\%325. (%9
       (\%337. (%230 (\%338. ((%306 ((%327 $3) (((%201 $2) $1) $0)))
       (((%308 $3) (%105 $2)) ((%341 ((%316 $3) (%105 $1))) (%340
       $0))))))))))))) ((%8 (%302 (\%303. (%9 (\%325. (%9 (\%337. (%230
       (\%338. ((%306 ((%327 $3) (((%202 $2) $1) $0))) (((%308 $3) (%105
       $2)) ((%342 ((%316 $3) (%105 $1))) (%340 $0))))))))))))) ((%8 (%302
       (\%303. (%9 (\%325. (%9 (\%337. (%230 (\%338. ((%306 ((%327 $3)
       (((%203 $2) $1) $0))) (((%308 $3) (%105 $2)) ((%343 ((%316 $3) (%105
       $1))) (%340 $0))))))))))))) ((%8 (%302 (\%303. (%14 (\%344. (%231
       (\%345. ((%306 ((%327 $2) ((%204 $1) $0))) (((%307 $2) $1)
       $0))))))))) (%302 (\%303. (%14 (\%344. (%231 (\%345. ((%306 ((%327
       $2) ((%205 $1) $0))) (((%322 $2) $1) $0)))))))))))))))))))))))`)
  val translate_assignment_def =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%325. (%79 (\%330. ((%346 (%347 ((%192 $1) $0))) ((%348
       ((%349 %350) ((%351 %352) %353))) ((%354 (%355 (%105 $1))) ((%356
       ((%357 (%113 $0)) %358)) %359))))))))) ((%8 (%9 (\%325. (%9 (\%331.
       (%79 (\%332. ((%346 (%347 (((%193 $2) $1) $0))) ((%348 ((%349 %360)
       ((%351 %352) %353))) ((%354 (%355 (%105 $2))) ((%356 ((%357 (%105
       $1)) ((%357 (%113 $0)) %358))) %359))))))))))) ((%8 (%9 (\%325. (%9
       (\%331. (%79 (\%332. ((%346 (%347 (((%194 $2) $1) $0))) ((%348
       ((%349 %361) ((%351 %352) %353))) ((%354 (%355 (%105 $2))) ((%356
       ((%357 (%105 $1)) ((%357 (%113 $0)) %358))) %359))))))))))) ((%8 (%9
       (\%325. (%9 (\%331. (%79 (\%332. ((%346 (%347 (((%195 $2) $1) $0)))
       ((%348 ((%349 %362) ((%351 %352) %353))) ((%354 (%355 (%105 $2)))
       ((%356 ((%357 (%105 $1)) ((%357 (%113 $0)) %358))) %359)))))))))))
       ((%8 (%9 (\%325. (%9 (\%331. (%79 (\%332. ((%346 (%347 (((%196 $2)
       $1) $0))) ((%348 ((%349 %363) ((%351 %352) %353))) ((%354 (%355
       (%105 $2))) ((%356 ((%357 (%105 $1)) ((%357 (%113 $0)) %358)))
       %359))))))))))) ((%8 (%9 (\%325. (%9 (\%331. (%79 (\%332. ((%346
       (%347 (((%197 $2) $1) $0))) ((%348 ((%349 %364) ((%351 %352) %353)))
       ((%354 (%355 (%105 $2))) ((%356 ((%357 (%105 $1)) ((%357 (%113 $0))
       %358))) %359))))))))))) ((%8 (%9 (\%325. (%9 (\%331. (%79 (\%332.
       ((%346 (%347 (((%198 $2) $1) $0))) ((%348 ((%349 %365) ((%351 %352)
       %353))) ((%354 (%355 (%105 $2))) ((%356 ((%357 (%105 $1)) ((%357
       (%113 $0)) %358))) %359))))))))))) ((%8 (%9 (\%325. (%9 (\%331. (%79
       (\%332. ((%346 (%347 (((%199 $2) $1) $0))) ((%348 ((%349 %366)
       ((%351 %352) %353))) ((%354 (%355 (%105 $2))) ((%356 ((%357 (%105
       $1)) ((%357 (%113 $0)) %358))) %359))))))))))) ((%8 (%9 (\%325. (%9
       (\%337. (%230 (\%338. ((%346 (%347 (((%200 $2) $1) $0))) ((%348
       ((%349 %367) ((%351 %352) %353))) ((%354 (%355 (%105 $2))) ((%356
       ((%357 (%105 $1)) ((%357 (%115 (%368 $0))) %358))) %359)))))))))))
       ((%8 (%9 (\%325. (%9 (\%337. (%230 (\%338. ((%346 (%347 (((%201 $2)
       $1) $0))) ((%348 ((%349 %369) ((%351 %352) %353))) ((%354 (%355
       (%105 $2))) ((%356 ((%357 (%105 $1)) ((%357 (%115 (%368 $0)))
       %358))) %359))))))))))) ((%8 (%9 (\%325. (%9 (\%337. (%230 (\%338.
       ((%346 (%347 (((%202 $2) $1) $0))) ((%348 ((%349 %370) ((%351 %352)
       %353))) ((%354 (%355 (%105 $2))) ((%356 ((%357 (%105 $1)) ((%357
       (%115 (%368 $0))) %358))) %359))))))))))) ((%8 (%9 (\%325. (%9
       (\%337. (%230 (\%338. ((%346 (%347 (((%203 $2) $1) $0))) ((%348
       ((%349 %371) ((%351 %352) %353))) ((%354 (%355 (%105 $2))) ((%356
       ((%357 (%105 $1)) ((%357 (%115 (%368 $0))) %358))) %359)))))))))))
       ((%8 (%9 (\%325. (%228 (\%326. ((%346 (%347 ((%190 $1) $0))) ((%348
       ((%349 %372) ((%351 %352) %353))) ((%354 (%355 (%105 $1))) ((%356
       ((%357 (%110 $0)) %358)) %359))))))))) ((%8 (%228 (\%328. (%9
       (\%329. ((%346 (%347 ((%191 $1) $0))) ((%348 ((%349 %373) ((%351
       %352) %353))) ((%354 (%355 (%105 $0))) ((%356 ((%357 (%110 $1))
       %358)) %359))))))))) ((%8 (%14 (\%374. (%231 (\%345. ((%346 (%347
       ((%204 $1) $0))) ((%348 ((%349 %375) ((%351 %352) %353))) ((%354
       (%355 (%376 $1))) ((%356 ((%318 %106) $0)) %359))))))))) (%14
       (\%374. (%231 (\%345. ((%346 (%347 ((%205 $1) $0))) ((%348 ((%349
       %377) ((%351 %352) %353))) ((%354 (%355 (%376 $1))) ((%356 ((%318
       %106) $0)) %359)))))))))))))))))))))))`)
  val translate_condition_def =
    DT(["DISK_THM"], [],
       `(%9 (\%103. (%37 (\%378. (%79 (\%379. ((%380 (%381 ((%382 $2)
       ((%383 $1) $0)))) ((%384 (%105 $2)) ((%385 $1) (%113 $0))))))))))`)
  val eval_il_cond_def =
    DT([], [], `(%293 (\%386. ((%387 (%388 $0)) (%389 (%390 $0)))))`)
  val translate_primitive_def =
    DT([], [],
       `((%391 %392) ((%393 (%394 (\%395. ((%8 (%396 $0)) ((%8 (%162
       (\%397. (%291 (\%398. (($2 (%279 $0)) (%279 ((%399 $1) $0))))))))
       ((%8 (%262 (\%400. (%262 (\%401. (($2 $0) ((%280 $1) $0))))))) ((%8
       (%262 (\%401. (%262 (\%400. (($2 $0) ((%280 $0) $1))))))) ((%8 (%262
       (\%402. (%293 (\%386. (%262 (\%403. (($3 $0) (((%281 $1) $0)
       $2))))))))) ((%8 (%262 (\%403. (%293 (\%386. (%262 (\%402. (($3 $0)
       (((%281 $1) $2) $0))))))))) (%293 (\%386. (%262 (\%404. (($2 $0)
       ((%282 $1) $0))))))))))))))) (\%405. (\%263. (((((%406 (\%257.
       (((%407 (%408 %409)) (\%397. (\%398. (%408 ((%410 (%347 $1)) ($4
       (%279 $0))))))) $0))) (\%400. (\%401. (%408 ((%411 ($3 $1)) ($3
       $0)))))) (\%386. (\%403. (\%402. (%408 (((%412 (%390 $2)) ($4 $1))
       ($4 $0))))))) (\%413. (\%404. (%408 ((%414 (%390 $1)) ($3 $0))))))
       $0)))))`)
  val run_arm_def =
    DT(["DISK_THM"], [],
       `(%415 (\%416. (%14 (\%417. (%96 (\%418. (%302 (\%303. (%419 (\%420.
       ((%421 ((%422 $4) ((%423 ((%424 $3) ((%425 $2) $1))) $0))) (((%426
       (((%427 $4) (\%100. %428)) $3)) ((%98 $3) (%429 $4))) ((%423 ((%424
       $3) ((%425 $2) $1))) $0)))))))))))))`)
  val run_cfl_def =
    DT([], [],
       `(%262 (\%430. (%302 (\%303. ((%306 ((%431 $1) $0)) (%432 ((%422
       (%392 $1)) ((%423 ((%424 %19) ((%425 (%320 %19)) $0)))
       %433))))))))`)
  val WELL_FORMED_def =
    DT(["DISK_THM"], [],
       `((%8 (%291 (\%398. ((%16 (%434 (%279 $0))) (%435 (%392 (%279
       $0))))))) ((%8 (%262 (\%400. (%262 (\%401. ((%16 (%434 ((%280 $1)
       $0))) ((%8 (%435 (%392 ((%280 $1) $0)))) ((%8 (%434 $1)) (%434
       $0))))))))) ((%8 (%293 (\%386. (%262 (\%400. (%262 (\%401. ((%16
       (%434 (((%281 $2) $1) $0))) ((%8 (%435 (%392 (((%281 $2) $1) $0))))
       ((%8 (%434 $1)) (%434 $0))))))))))) (%293 (\%386. (%262 (\%400.
       ((%16 (%434 ((%282 $1) $0))) ((%8 (%435 (%392 ((%282 $1) $0)))) ((%8
       (%434 $0)) (%436 ((%437 (%390 $1)) (%392 $0)))))))))))))`)
  val WELL_FORMED_SUB_def =
    DT(["DISK_THM"], [],
       `((%8 (%291 (\%398. ((%16 (%438 (%279 $0))) %72)))) ((%8 (%262
       (\%400. (%262 (\%401. ((%16 (%438 ((%280 $1) $0))) ((%8 (%434 $1))
       (%434 $0)))))))) ((%8 (%293 (\%386. (%262 (\%400. (%262 (\%401.
       ((%16 (%438 (((%281 $2) $1) $0))) ((%8 (%434 $1)) (%434 $0))))))))))
       (%293 (\%386. (%262 (\%400. ((%16 (%438 ((%282 $1) $0))) ((%8 (%434
       $0)) (%436 ((%437 (%390 $1)) (%392 $0))))))))))))`)
  val num2MREG_MREG2num =
    DT(["DISK_THM"], [], `(%9 (\%10. ((%11 (%12 (%13 $0))) $0)))`)
  val MREG2num_num2MREG =
    DT(["DISK_THM"], [],
       `(%14 (\%15. ((%16 ((%4 $0) (%5 (%6 (%6 (%6 (%6 %7))))))) ((%17 (%13
       (%12 $0))) $0))))`)
  val num2MREG_11 =
    DT(["DISK_THM"], [],
       `(%14 (\%15. (%14 (\%439. ((%63 ((%4 $1) (%5 (%6 (%6 (%6 (%6
       %7))))))) ((%63 ((%4 $0) (%5 (%6 (%6 (%6 (%6 %7))))))) ((%16 ((%11
       (%12 $1)) (%12 $0))) ((%17 $1) $0))))))))`)
  val MREG2num_11 =
    DT(["DISK_THM"], [],
       `(%9 (\%10. (%9 (\%440. ((%16 ((%17 (%13 $1)) (%13 $0))) ((%11 $1)
       $0))))))`)
  val num2MREG_ONTO =
    DT(["DISK_THM"], [],
       `(%9 (\%10. (%158 (\%15. ((%8 ((%11 $1) (%12 $0))) ((%4 $0) (%5 (%6
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
       `(%9 (\%10. (%9 (\%440. ((%16 ((%11 $1) $0)) ((%17 (%13 $1)) (%13
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
       `(%441 (((((((((((((((%442 %18) %20) %21) %23) %24) %25) %26) %27)
       %28) %29) %30) %31) %32) %33) %34))`)
  val MREG_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%443 ((%11 %18) %20))) ((%8 (%443 ((%11 %18) %21))) ((%8
       (%443 ((%11 %18) %23))) ((%8 (%443 ((%11 %18) %24))) ((%8 (%443
       ((%11 %18) %25))) ((%8 (%443 ((%11 %18) %26))) ((%8 (%443 ((%11 %18)
       %27))) ((%8 (%443 ((%11 %18) %28))) ((%8 (%443 ((%11 %18) %29)))
       ((%8 (%443 ((%11 %18) %30))) ((%8 (%443 ((%11 %18) %31))) ((%8 (%443
       ((%11 %18) %32))) ((%8 (%443 ((%11 %18) %33))) ((%8 (%443 ((%11 %18)
       %34))) ((%8 (%443 ((%11 %20) %21))) ((%8 (%443 ((%11 %20) %23)))
       ((%8 (%443 ((%11 %20) %24))) ((%8 (%443 ((%11 %20) %25))) ((%8 (%443
       ((%11 %20) %26))) ((%8 (%443 ((%11 %20) %27))) ((%8 (%443 ((%11 %20)
       %28))) ((%8 (%443 ((%11 %20) %29))) ((%8 (%443 ((%11 %20) %30)))
       ((%8 (%443 ((%11 %20) %31))) ((%8 (%443 ((%11 %20) %32))) ((%8 (%443
       ((%11 %20) %33))) ((%8 (%443 ((%11 %20) %34))) ((%8 (%443 ((%11 %21)
       %23))) ((%8 (%443 ((%11 %21) %24))) ((%8 (%443 ((%11 %21) %25)))
       ((%8 (%443 ((%11 %21) %26))) ((%8 (%443 ((%11 %21) %27))) ((%8 (%443
       ((%11 %21) %28))) ((%8 (%443 ((%11 %21) %29))) ((%8 (%443 ((%11 %21)
       %30))) ((%8 (%443 ((%11 %21) %31))) ((%8 (%443 ((%11 %21) %32)))
       ((%8 (%443 ((%11 %21) %33))) ((%8 (%443 ((%11 %21) %34))) ((%8 (%443
       ((%11 %23) %24))) ((%8 (%443 ((%11 %23) %25))) ((%8 (%443 ((%11 %23)
       %26))) ((%8 (%443 ((%11 %23) %27))) ((%8 (%443 ((%11 %23) %28)))
       ((%8 (%443 ((%11 %23) %29))) ((%8 (%443 ((%11 %23) %30))) ((%8 (%443
       ((%11 %23) %31))) ((%8 (%443 ((%11 %23) %32))) ((%8 (%443 ((%11 %23)
       %33))) ((%8 (%443 ((%11 %23) %34))) ((%8 (%443 ((%11 %24) %25)))
       ((%8 (%443 ((%11 %24) %26))) ((%8 (%443 ((%11 %24) %27))) ((%8 (%443
       ((%11 %24) %28))) ((%8 (%443 ((%11 %24) %29))) ((%8 (%443 ((%11 %24)
       %30))) ((%8 (%443 ((%11 %24) %31))) ((%8 (%443 ((%11 %24) %32)))
       ((%8 (%443 ((%11 %24) %33))) ((%8 (%443 ((%11 %24) %34))) ((%8 (%443
       ((%11 %25) %26))) ((%8 (%443 ((%11 %25) %27))) ((%8 (%443 ((%11 %25)
       %28))) ((%8 (%443 ((%11 %25) %29))) ((%8 (%443 ((%11 %25) %30)))
       ((%8 (%443 ((%11 %25) %31))) ((%8 (%443 ((%11 %25) %32))) ((%8 (%443
       ((%11 %25) %33))) ((%8 (%443 ((%11 %25) %34))) ((%8 (%443 ((%11 %26)
       %27))) ((%8 (%443 ((%11 %26) %28))) ((%8 (%443 ((%11 %26) %29)))
       ((%8 (%443 ((%11 %26) %30))) ((%8 (%443 ((%11 %26) %31))) ((%8 (%443
       ((%11 %26) %32))) ((%8 (%443 ((%11 %26) %33))) ((%8 (%443 ((%11 %26)
       %34))) ((%8 (%443 ((%11 %27) %28))) ((%8 (%443 ((%11 %27) %29)))
       ((%8 (%443 ((%11 %27) %30))) ((%8 (%443 ((%11 %27) %31))) ((%8 (%443
       ((%11 %27) %32))) ((%8 (%443 ((%11 %27) %33))) ((%8 (%443 ((%11 %27)
       %34))) ((%8 (%443 ((%11 %28) %29))) ((%8 (%443 ((%11 %28) %30)))
       ((%8 (%443 ((%11 %28) %31))) ((%8 (%443 ((%11 %28) %32))) ((%8 (%443
       ((%11 %28) %33))) ((%8 (%443 ((%11 %28) %34))) ((%8 (%443 ((%11 %29)
       %30))) ((%8 (%443 ((%11 %29) %31))) ((%8 (%443 ((%11 %29) %32)))
       ((%8 (%443 ((%11 %29) %33))) ((%8 (%443 ((%11 %29) %34))) ((%8 (%443
       ((%11 %30) %31))) ((%8 (%443 ((%11 %30) %32))) ((%8 (%443 ((%11 %30)
       %33))) ((%8 (%443 ((%11 %30) %34))) ((%8 (%443 ((%11 %31) %32)))
       ((%8 (%443 ((%11 %31) %33))) ((%8 (%443 ((%11 %31) %34))) ((%8 (%443
       ((%11 %32) %33))) ((%8 (%443 ((%11 %32) %34))) (%443 ((%11 %33)
       %34))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val MREG_case_cong =
    DT(["DISK_THM"], [],
       `(%9 (\%444. (%9 (\%445. (%37 (\%38. (%37 (\%39. (%37 (\%40. (%37
       (\%41. (%37 (\%42. (%37 (\%43. (%37 (\%44. (%37 (\%45. (%37 (\%46.
       (%37 (\%47. (%37 (\%48. (%37 (\%49. (%37 (\%50. (%37 (\%51. (%37
       (\%52. ((%63 ((%8 ((%11 $16) $15)) ((%8 ((%63 ((%11 $15) %18)) ((%53
       $14) %446))) ((%8 ((%63 ((%11 $15) %20)) ((%53 $13) %447))) ((%8
       ((%63 ((%11 $15) %21)) ((%53 $12) %448))) ((%8 ((%63 ((%11 $15)
       %23)) ((%53 $11) %449))) ((%8 ((%63 ((%11 $15) %24)) ((%53 $10)
       %450))) ((%8 ((%63 ((%11 $15) %25)) ((%53 $9) %451))) ((%8 ((%63
       ((%11 $15) %26)) ((%53 $8) %452))) ((%8 ((%63 ((%11 $15) %27)) ((%53
       $7) %453))) ((%8 ((%63 ((%11 $15) %28)) ((%53 $6) %454))) ((%8 ((%63
       ((%11 $15) %29)) ((%53 $5) %455))) ((%8 ((%63 ((%11 $15) %30)) ((%53
       $4) %456))) ((%8 ((%63 ((%11 $15) %31)) ((%53 $3) %457))) ((%8 ((%63
       ((%11 $15) %32)) ((%53 $2) %458))) ((%8 ((%63 ((%11 $15) %33)) ((%53
       $1) %459))) ((%63 ((%11 $15) %34)) ((%53 $0) %460))))))))))))))))))
       ((%53 ((((((((((((((((%54 $14) $13) $12) $11) $10) $9) $8) $7) $6)
       $5) $4) $3) $2) $1) $0) $16)) ((((((((((((((((%54 %446) %447) %448)
       %449) %450) %451) %452) %453) %454) %455) %456) %457) %458) %459)
       %460) $15)))))))))))))))))))))))))))))))))))))`)
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
       `(%37 (\%461. (%37 (\%462. (%37 (\%463. (%37 (\%464. (%37 (\%465.
       (%37 (\%466. (%37 (\%467. (%37 (\%468. (%37 (\%469. (%37 (\%470.
       (%37 (\%471. (%37 (\%472. (%37 (\%473. (%37 (\%474. (%37 (\%475.
       (%476 (\%92. ((%8 ((%53 ($0 %18)) $15)) ((%8 ((%53 ($0 %20)) $14))
       ((%8 ((%53 ($0 %21)) $13)) ((%8 ((%53 ($0 %23)) $12)) ((%8 ((%53 ($0
       %24)) $11)) ((%8 ((%53 ($0 %25)) $10)) ((%8 ((%53 ($0 %26)) $9))
       ((%8 ((%53 ($0 %27)) $8)) ((%8 ((%53 ($0 %28)) $7)) ((%8 ((%53 ($0
       %29)) $6)) ((%8 ((%53 ($0 %30)) $5)) ((%8 ((%53 ($0 %31)) $4)) ((%8
       ((%53 ($0 %32)) $3)) ((%8 ((%53 ($0 %33)) $2)) ((%53 ($0 %34))
       $1)))))))))))))))))))))))))))))))))))))))))))))))`)
  val MREG_induction =
    DT(["DISK_THM"], [],
       `(%477 (\%478. ((%63 ((%8 ($0 %18)) ((%8 ($0 %20)) ((%8 ($0 %30))
       ((%8 ($0 %31)) ((%8 ($0 %32)) ((%8 ($0 %33)) ((%8 ($0 %34)) ((%8 ($0
       %21)) ((%8 ($0 %23)) ((%8 ($0 %24)) ((%8 ($0 %25)) ((%8 ($0 %26))
       ((%8 ($0 %27)) ((%8 ($0 %28)) ($0 %29)))))))))))))))) (%9 (\%10. ($1
       $0))))))`)
  val datatype_MEXP = DT(["DISK_THM"], [], `(%441 ((%479 %89) %90))`)
  val MEXP_11 =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%10. (%9 (\%440. ((%16 ((%81 (%89 $1)) (%89 $0))) ((%11
       $1) $0))))))) (%96 (\%75. (%96 (\%480. ((%16 ((%81 (%90 $1)) (%90
       $0))) ((%481 $1) $0)))))))`)
  val MEXP_distinct =
    DT(["DISK_THM"], [],
       `(%96 (\%480. (%9 (\%10. (%443 ((%81 (%89 $0)) (%90 $1)))))))`)
  val MEXP_case_cong =
    DT(["DISK_THM"], [],
       `(%79 (\%482. (%79 (\%483. (%91 (\%92. (%93 (\%94. ((%63 ((%8 ((%81
       $3) $2)) ((%8 (%9 (\%10. ((%63 ((%81 $3) (%89 $0))) ((%53 ($2 $0))
       (%484 $0)))))) (%96 (\%75. ((%63 ((%81 $3) (%90 $0))) ((%53 ($1 $0))
       (%485 $0)))))))) ((%53 (((%95 $1) $0) $3)) (((%95 %484) %485)
       $2)))))))))))`)
  val MEXP_nchotomy =
    DT(["DISK_THM"], [],
       `(%79 (\%482. ((%65 (%66 (\%444. ((%81 $1) (%89 $0))))) (%74 (\%114.
       ((%81 $1) (%90 $0)))))))`)
  val MEXP_Axiom =
    DT(["DISK_THM"], [],
       `(%91 (\%486. (%93 (\%94. (%487 (\%488. ((%8 (%9 (\%10. ((%53 ($1
       (%89 $0))) ($3 $0))))) (%96 (\%75. ((%53 ($1 (%90 $0))) ($2
       $0)))))))))))`)
  val MEXP_induction =
    DT(["DISK_THM"], [],
       `(%489 (\%490. ((%63 ((%8 (%9 (\%444. ($1 (%89 $0))))) (%96 (\%114.
       ($1 (%90 $0)))))) (%79 (\%482. ($1 $0))))))`)
  val from_reg_index_thm =
    DT(["DISK_THM"], [],
       `((%8 ((%11 (%101 %19)) %18)) ((%8 ((%11 (%101 (%5 (%6 %7)))) %20))
       ((%8 ((%11 (%101 (%5 (%22 %7)))) %21)) ((%8 ((%11 (%101 (%5 (%6 (%6
       %7))))) %23)) ((%8 ((%11 (%101 (%5 (%22 (%6 %7))))) %24)) ((%8 ((%11
       (%101 (%5 (%6 (%22 %7))))) %25)) ((%8 ((%11 (%101 (%5 (%22 (%22
       %7))))) %26)) ((%8 ((%11 (%101 (%5 (%6 (%6 (%6 %7)))))) %27)) ((%8
       ((%11 (%101 (%5 (%22 (%6 (%6 %7)))))) %28)) ((%8 ((%11 (%101 (%5 (%6
       (%22 (%6 %7)))))) %29)) ((%8 ((%11 (%101 (%5 (%22 (%22 (%6 %7))))))
       %30)) ((%8 ((%11 (%101 (%5 (%6 (%6 (%22 %7)))))) %31)) ((%8 ((%11
       (%101 (%5 (%22 (%6 (%22 %7)))))) %32)) ((%8 ((%11 (%101 (%5 (%6 (%22
       (%22 %7)))))) %33)) ((%11 (%101 (%5 (%22 (%22 (%22 %7))))))
       %34)))))))))))))))`)
  val datatype_DOPER =
    DT(["DISK_THM"], [],
       `(%441 ((((((((((((((((%491 %190) %191) %192) %193) %194) %195)
       %196) %197) %198) %199) %200) %201) %202) %203) %204) %205))`)
  val DOPER_11 =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%129. (%228 (\%131. (%9 (\%492. (%228 (\%493. ((%16
       ((%164 ((%190 $3) $2)) ((%190 $1) $0))) ((%8 ((%11 $3) $1)) ((%494
       $2) $0)))))))))))) ((%8 (%228 (\%149. (%9 (\%150. (%228 (\%495. (%9
       (\%496. ((%16 ((%164 ((%191 $3) $2)) ((%191 $1) $0))) ((%8 ((%494
       $3) $1)) ((%11 $2) $0)))))))))))) ((%8 (%9 (\%129. (%79 (\%152. (%9
       (\%492. (%79 (\%497. ((%16 ((%164 ((%192 $3) $2)) ((%192 $1) $0)))
       ((%8 ((%11 $3) $1)) ((%81 $2) $0)))))))))))) ((%8 (%9 (\%129. (%9
       (\%150. (%79 (\%155. (%9 (\%492. (%9 (\%496. (%79 (\%498. ((%16
       ((%164 (((%193 $5) $4) $3)) (((%193 $2) $1) $0))) ((%8 ((%11 $5)
       $2)) ((%8 ((%11 $4) $1)) ((%81 $3) $0))))))))))))))))) ((%8 (%9
       (\%129. (%9 (\%150. (%79 (\%155. (%9 (\%492. (%9 (\%496. (%79
       (\%498. ((%16 ((%164 (((%194 $5) $4) $3)) (((%194 $2) $1) $0))) ((%8
       ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%81 $3) $0)))))))))))))))))
       ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155. (%9 (\%492. (%9 (\%496.
       (%79 (\%498. ((%16 ((%164 (((%195 $5) $4) $3)) (((%195 $2) $1) $0)))
       ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%81 $3)
       $0))))))))))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155. (%9
       (\%492. (%9 (\%496. (%79 (\%498. ((%16 ((%164 (((%196 $5) $4) $3))
       (((%196 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%81
       $3) $0))))))))))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155.
       (%9 (\%492. (%9 (\%496. (%79 (\%498. ((%16 ((%164 (((%197 $5) $4)
       $3)) (((%197 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1))
       ((%81 $3) $0))))))))))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79
       (\%155. (%9 (\%492. (%9 (\%496. (%79 (\%498. ((%16 ((%164 (((%198
       $5) $4) $3)) (((%198 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11
       $4) $1)) ((%81 $3) $0))))))))))))))))) ((%8 (%9 (\%129. (%9 (\%150.
       (%79 (\%155. (%9 (\%492. (%9 (\%496. (%79 (\%498. ((%16 ((%164
       (((%199 $5) $4) $3)) (((%199 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8
       ((%11 $4) $1)) ((%81 $3) $0))))))))))))))))) ((%8 (%9 (\%129. (%9
       (\%150. (%230 (\%157. (%9 (\%492. (%9 (\%496. (%230 (\%499. ((%16
       ((%164 (((%200 $5) $4) $3)) (((%200 $2) $1) $0))) ((%8 ((%11 $5)
       $2)) ((%8 ((%11 $4) $1)) ((%500 $3) $0))))))))))))))))) ((%8 (%9
       (\%129. (%9 (\%150. (%230 (\%157. (%9 (\%492. (%9 (\%496. (%230
       (\%499. ((%16 ((%164 (((%201 $5) $4) $3)) (((%201 $2) $1) $0))) ((%8
       ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%500 $3) $0)))))))))))))))))
       ((%8 (%9 (\%129. (%9 (\%150. (%230 (\%157. (%9 (\%492. (%9 (\%496.
       (%230 (\%499. ((%16 ((%164 (((%202 $5) $4) $3)) (((%202 $2) $1)
       $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%500 $3)
       $0))))))))))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%230 (\%157. (%9
       (\%492. (%9 (\%496. (%230 (\%499. ((%16 ((%164 (((%203 $5) $4) $3))
       (((%203 $2) $1) $0))) ((%8 ((%11 $5) $2)) ((%8 ((%11 $4) $1)) ((%500
       $3) $0))))))))))))))))) ((%8 (%14 (\%159. (%231 (\%161. (%14 (\%501.
       (%231 (\%502. ((%16 ((%164 ((%204 $3) $2)) ((%204 $1) $0))) ((%8
       ((%17 $3) $1)) ((%503 $2) $0)))))))))))) (%14 (\%159. (%231 (\%161.
       (%14 (\%501. (%231 (\%502. ((%16 ((%164 ((%205 $3) $2)) ((%205 $1)
       $0))) ((%8 ((%17 $3) $1)) ((%503 $2) $0))))))))))))))))))))))))))`)
  val DOPER_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%9 (\%496. (%228 (\%131. (%228 (\%495. (%9 (\%129. (%443
       ((%164 ((%190 $0) $2)) ((%191 $1) $3)))))))))))) ((%8 (%79 (\%497.
       (%228 (\%131. (%9 (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2))
       ((%192 $1) $3)))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%228
       (\%131. (%9 (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%193
       $1) $3) $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%228 (\%131.
       (%9 (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%194 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%228 (\%131. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%195 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%228 (\%131. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%196 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%228 (\%131. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%197 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%228 (\%131. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%198 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%228 (\%131. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%199 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%228 (\%131. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%200 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%228 (\%131. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%201 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%228 (\%131. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%202 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%228 (\%131. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%190 $0) $2)) (((%203 $1) $3)
       $4)))))))))))))) ((%8 (%231 (\%502. (%228 (\%131. (%14 (\%501. (%9
       (\%129. (%443 ((%164 ((%190 $0) $2)) ((%204 $1) $3)))))))))))) ((%8
       (%231 (\%502. (%228 (\%131. (%14 (\%501. (%9 (\%129. (%443 ((%164
       ((%190 $0) $2)) ((%205 $1) $3)))))))))))) ((%8 (%79 (\%497. (%9
       (\%150. (%9 (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2))
       ((%192 $1) $3)))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%9 (\%150.
       (%9 (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%193 $1)
       $3) $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%194 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%195 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%196 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%197 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%198 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%199 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%200 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%201 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%202 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%9 (\%150. (%9
       (\%492. (%228 (\%149. (%443 ((%164 ((%191 $0) $2)) (((%203 $1) $3)
       $4)))))))))))))) ((%8 (%231 (\%502. (%9 (\%150. (%14 (\%501. (%228
       (\%149. (%443 ((%164 ((%191 $0) $2)) ((%204 $1) $3)))))))))))) ((%8
       (%231 (\%502. (%9 (\%150. (%14 (\%501. (%228 (\%149. (%443 ((%164
       ((%191 $0) $2)) ((%205 $1) $3)))))))))))) ((%8 (%79 (\%155. (%9
       (\%496. (%79 (\%152. (%9 (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0)
       $2)) (((%193 $1) $3) $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496.
       (%79 (\%152. (%9 (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2))
       (((%194 $1) $3) $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%79
       (\%152. (%9 (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2)) (((%195
       $1) $3) $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%79 (\%152.
       (%9 (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2)) (((%196 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%79 (\%152. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2)) (((%197 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%79 (\%152. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2)) (((%198 $1) $3)
       $4)))))))))))))) ((%8 (%79 (\%155. (%9 (\%496. (%79 (\%152. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2)) (((%199 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%79 (\%152. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2)) (((%200 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%79 (\%152. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2)) (((%201 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%79 (\%152. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2)) (((%202 $1) $3)
       $4)))))))))))))) ((%8 (%230 (\%157. (%9 (\%496. (%79 (\%152. (%9
       (\%492. (%9 (\%129. (%443 ((%164 ((%192 $0) $2)) (((%203 $1) $3)
       $4)))))))))))))) ((%8 (%231 (\%502. (%79 (\%152. (%14 (\%501. (%9
       (\%129. (%443 ((%164 ((%192 $0) $2)) ((%204 $1) $3)))))))))))) ((%8
       (%231 (\%502. (%79 (\%152. (%14 (\%501. (%9 (\%129. (%443 ((%164
       ((%192 $0) $2)) ((%205 $1) $3)))))))))))) ((%8 (%79 (\%498. (%79
       (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164
       (((%193 $0) $2) $4)) (((%194 $1) $3) $5)))))))))))))))) ((%8 (%79
       (\%498. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129.
       (%443 ((%164 (((%193 $0) $2) $4)) (((%195 $1) $3) $5))))))))))))))))
       ((%8 (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492.
       (%9 (\%129. (%443 ((%164 (((%193 $0) $2) $4)) (((%196 $1) $3)
       $5)))))))))))))))) ((%8 (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%193 $0) $2) $4))
       (((%197 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%498. (%79 (\%155.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%193
       $0) $2) $4)) (((%198 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%498.
       (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%193 $0) $2) $4)) (((%199 $1) $3) $5)))))))))))))))) ((%8
       (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%193 $0) $2) $4)) (((%200 $1) $3)
       $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%193 $0) $2) $4))
       (((%201 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%193
       $0) $2) $4)) (((%202 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499.
       (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%193 $0) $2) $4)) (((%203 $1) $3) $5)))))))))))))))) ((%8
       (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129.
       (%443 ((%164 (((%193 $0) $2) $4)) ((%204 $1) $3)))))))))))))) ((%8
       (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129.
       (%443 ((%164 (((%193 $0) $2) $4)) ((%205 $1) $3)))))))))))))) ((%8
       (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%194 $0) $2) $4)) (((%195 $1) $3)
       $5)))))))))))))))) ((%8 (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%194 $0) $2) $4))
       (((%196 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%498. (%79 (\%155.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%194
       $0) $2) $4)) (((%197 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%498.
       (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%194 $0) $2) $4)) (((%198 $1) $3) $5)))))))))))))))) ((%8
       (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%194 $0) $2) $4)) (((%199 $1) $3)
       $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%194 $0) $2) $4))
       (((%200 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%194
       $0) $2) $4)) (((%201 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499.
       (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%194 $0) $2) $4)) (((%202 $1) $3) $5)))))))))))))))) ((%8
       (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%194 $0) $2) $4)) (((%203 $1) $3)
       $5)))))))))))))))) ((%8 (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14
       (\%501. (%9 (\%129. (%443 ((%164 (((%194 $0) $2) $4)) ((%204 $1)
       $3)))))))))))))) ((%8 (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14
       (\%501. (%9 (\%129. (%443 ((%164 (((%194 $0) $2) $4)) ((%205 $1)
       $3)))))))))))))) ((%8 (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%195 $0) $2) $4))
       (((%196 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%498. (%79 (\%155.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%195
       $0) $2) $4)) (((%197 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%498.
       (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%195 $0) $2) $4)) (((%198 $1) $3) $5)))))))))))))))) ((%8
       (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%195 $0) $2) $4)) (((%199 $1) $3)
       $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%195 $0) $2) $4))
       (((%200 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%195
       $0) $2) $4)) (((%201 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499.
       (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%195 $0) $2) $4)) (((%202 $1) $3) $5)))))))))))))))) ((%8
       (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%195 $0) $2) $4)) (((%203 $1) $3)
       $5)))))))))))))))) ((%8 (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14
       (\%501. (%9 (\%129. (%443 ((%164 (((%195 $0) $2) $4)) ((%204 $1)
       $3)))))))))))))) ((%8 (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14
       (\%501. (%9 (\%129. (%443 ((%164 (((%195 $0) $2) $4)) ((%205 $1)
       $3)))))))))))))) ((%8 (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%196 $0) $2) $4))
       (((%197 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%498. (%79 (\%155.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%196
       $0) $2) $4)) (((%198 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%498.
       (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%196 $0) $2) $4)) (((%199 $1) $3) $5)))))))))))))))) ((%8
       (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%196 $0) $2) $4)) (((%200 $1) $3)
       $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%196 $0) $2) $4))
       (((%201 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%196
       $0) $2) $4)) (((%202 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499.
       (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%196 $0) $2) $4)) (((%203 $1) $3) $5)))))))))))))))) ((%8
       (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129.
       (%443 ((%164 (((%196 $0) $2) $4)) ((%204 $1) $3)))))))))))))) ((%8
       (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129.
       (%443 ((%164 (((%196 $0) $2) $4)) ((%205 $1) $3)))))))))))))) ((%8
       (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%197 $0) $2) $4)) (((%198 $1) $3)
       $5)))))))))))))))) ((%8 (%79 (\%498. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%197 $0) $2) $4))
       (((%199 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%197
       $0) $2) $4)) (((%200 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499.
       (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%197 $0) $2) $4)) (((%201 $1) $3) $5)))))))))))))))) ((%8
       (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%197 $0) $2) $4)) (((%202 $1) $3)
       $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%197 $0) $2) $4))
       (((%203 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%155. (%231 (\%502.
       (%9 (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164 (((%197 $0) $2)
       $4)) ((%204 $1) $3)))))))))))))) ((%8 (%79 (\%155. (%231 (\%502. (%9
       (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164 (((%197 $0) $2) $4))
       ((%205 $1) $3)))))))))))))) ((%8 (%79 (\%498. (%79 (\%155. (%9
       (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%198 $0)
       $2) $4)) (((%199 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499. (%79
       (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164
       (((%198 $0) $2) $4)) (((%200 $1) $3) $5)))))))))))))))) ((%8 (%230
       (\%499. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129.
       (%443 ((%164 (((%198 $0) $2) $4)) (((%201 $1) $3) $5))))))))))))))))
       ((%8 (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492.
       (%9 (\%129. (%443 ((%164 (((%198 $0) $2) $4)) (((%202 $1) $3)
       $5)))))))))))))))) ((%8 (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%198 $0) $2) $4))
       (((%203 $1) $3) $5)))))))))))))))) ((%8 (%79 (\%155. (%231 (\%502.
       (%9 (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164 (((%198 $0) $2)
       $4)) ((%204 $1) $3)))))))))))))) ((%8 (%79 (\%155. (%231 (\%502. (%9
       (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164 (((%198 $0) $2) $4))
       ((%205 $1) $3)))))))))))))) ((%8 (%230 (\%499. (%79 (\%155. (%9
       (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%199 $0)
       $2) $4)) (((%200 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499. (%79
       (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164
       (((%199 $0) $2) $4)) (((%201 $1) $3) $5)))))))))))))))) ((%8 (%230
       (\%499. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129.
       (%443 ((%164 (((%199 $0) $2) $4)) (((%202 $1) $3) $5))))))))))))))))
       ((%8 (%230 (\%499. (%79 (\%155. (%9 (\%496. (%9 (\%150. (%9 (\%492.
       (%9 (\%129. (%443 ((%164 (((%199 $0) $2) $4)) (((%203 $1) $3)
       $5)))))))))))))))) ((%8 (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14
       (\%501. (%9 (\%129. (%443 ((%164 (((%199 $0) $2) $4)) ((%204 $1)
       $3)))))))))))))) ((%8 (%79 (\%155. (%231 (\%502. (%9 (\%150. (%14
       (\%501. (%9 (\%129. (%443 ((%164 (((%199 $0) $2) $4)) ((%205 $1)
       $3)))))))))))))) ((%8 (%230 (\%499. (%230 (\%157. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%200 $0) $2) $4))
       (((%201 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499. (%230 (\%157.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%200
       $0) $2) $4)) (((%202 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%499.
       (%230 (\%157. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443
       ((%164 (((%200 $0) $2) $4)) (((%203 $1) $3) $5)))))))))))))))) ((%8
       (%230 (\%157. (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129.
       (%443 ((%164 (((%200 $0) $2) $4)) ((%204 $1) $3)))))))))))))) ((%8
       (%230 (\%157. (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129.
       (%443 ((%164 (((%200 $0) $2) $4)) ((%205 $1) $3)))))))))))))) ((%8
       (%230 (\%499. (%230 (\%157. (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9
       (\%129. (%443 ((%164 (((%201 $0) $2) $4)) (((%202 $1) $3)
       $5)))))))))))))))) ((%8 (%230 (\%499. (%230 (\%157. (%9 (\%496. (%9
       (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%201 $0) $2) $4))
       (((%203 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%157. (%231 (\%502.
       (%9 (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164 (((%201 $0) $2)
       $4)) ((%204 $1) $3)))))))))))))) ((%8 (%230 (\%157. (%231 (\%502.
       (%9 (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164 (((%201 $0) $2)
       $4)) ((%205 $1) $3)))))))))))))) ((%8 (%230 (\%499. (%230 (\%157.
       (%9 (\%496. (%9 (\%150. (%9 (\%492. (%9 (\%129. (%443 ((%164 (((%202
       $0) $2) $4)) (((%203 $1) $3) $5)))))))))))))))) ((%8 (%230 (\%157.
       (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164
       (((%202 $0) $2) $4)) ((%204 $1) $3)))))))))))))) ((%8 (%230 (\%157.
       (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164
       (((%202 $0) $2) $4)) ((%205 $1) $3)))))))))))))) ((%8 (%230 (\%157.
       (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164
       (((%203 $0) $2) $4)) ((%204 $1) $3)))))))))))))) ((%8 (%230 (\%157.
       (%231 (\%502. (%9 (\%150. (%14 (\%501. (%9 (\%129. (%443 ((%164
       (((%203 $0) $2) $4)) ((%205 $1) $3)))))))))))))) (%231 (\%502. (%231
       (\%161. (%14 (\%501. (%14 (\%159. (%443 ((%164 ((%204 $0) $2))
       ((%205 $1)
       $3))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val DOPER_case_cong =
    DT(["DISK_THM"], [],
       `(%162 (\%504. (%162 (\%505. (%206 (\%207. (%208 (\%209. (%210
       (\%211. (%212 (\%213. (%212 (\%214. (%212 (\%215. (%212 (\%216.
       (%212 (\%217. (%212 (\%218. (%212 (\%219. (%220 (\%221. (%220
       (\%222. (%220 (\%223. (%220 (\%224. (%225 (\%226. (%225 (\%227.
       ((%63 ((%8 ((%164 $17) $16)) ((%8 (%9 (\%129. (%228 (\%131. ((%63
       ((%164 $18) ((%190 $1) $0))) ((%53 (($17 $1) $0)) ((%506 $1)
       $0)))))))) ((%8 (%228 (\%149. (%9 (\%150. ((%63 ((%164 $18) ((%191
       $1) $0))) ((%53 (($16 $1) $0)) ((%507 $1) $0)))))))) ((%8 (%9
       (\%129. (%79 (\%152. ((%63 ((%164 $18) ((%192 $1) $0))) ((%53 (($15
       $1) $0)) ((%508 $1) $0)))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79
       (\%155. ((%63 ((%164 $19) (((%193 $2) $1) $0))) ((%53 ((($15 $2) $1)
       $0)) (((%509 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79
       (\%155. ((%63 ((%164 $19) (((%194 $2) $1) $0))) ((%53 ((($14 $2) $1)
       $0)) (((%510 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79
       (\%155. ((%63 ((%164 $19) (((%195 $2) $1) $0))) ((%53 ((($13 $2) $1)
       $0)) (((%511 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79
       (\%155. ((%63 ((%164 $19) (((%196 $2) $1) $0))) ((%53 ((($12 $2) $1)
       $0)) (((%512 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79
       (\%155. ((%63 ((%164 $19) (((%197 $2) $1) $0))) ((%53 ((($11 $2) $1)
       $0)) (((%513 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79
       (\%155. ((%63 ((%164 $19) (((%198 $2) $1) $0))) ((%53 ((($10 $2) $1)
       $0)) (((%514 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79
       (\%155. ((%63 ((%164 $19) (((%199 $2) $1) $0))) ((%53 ((($9 $2) $1)
       $0)) (((%515 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%230
       (\%157. ((%63 ((%164 $19) (((%200 $2) $1) $0))) ((%53 ((($8 $2) $1)
       $0)) (((%516 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%230
       (\%157. ((%63 ((%164 $19) (((%201 $2) $1) $0))) ((%53 ((($7 $2) $1)
       $0)) (((%517 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%230
       (\%157. ((%63 ((%164 $19) (((%202 $2) $1) $0))) ((%53 ((($6 $2) $1)
       $0)) (((%518 $2) $1) $0)))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%230
       (\%157. ((%63 ((%164 $19) (((%203 $2) $1) $0))) ((%53 ((($5 $2) $1)
       $0)) (((%519 $2) $1) $0)))))))))) ((%8 (%14 (\%159. (%231 (\%161.
       ((%63 ((%164 $18) ((%204 $1) $0))) ((%53 (($3 $1) $0)) ((%520 $1)
       $0)))))))) (%14 (\%159. (%231 (\%161. ((%63 ((%164 $18) ((%205 $1)
       $0))) ((%53 (($2 $1) $0)) ((%521 $1) $0))))))))))))))))))))))))
       ((%53 (((((((((((((((((%229 $15) $14) $13) $12) $11) $10) $9) $8)
       $7) $6) $5) $4) $3) $2) $1) $0) $17)) (((((((((((((((((%229 %506)
       %507) %508) %509) %510) %511) %512) %513) %514) %515) %516) %517)
       %518) %519) %520) %521) $16)))))))))))))))))))))))))))))))))))))))`)
  val DOPER_nchotomy =
    DT(["DISK_THM"], [],
       `(%162 (\%522. ((%65 (%66 (\%444. (%130 (\%523. ((%164 $2) ((%190
       $1) $0))))))) ((%65 (%130 (\%523. (%66 (\%444. ((%164 $2) ((%191 $1)
       $0))))))) ((%65 (%66 (\%444. (%151 (\%524. ((%164 $2) ((%192 $1)
       $0))))))) ((%65 (%66 (\%444. (%66 (\%525. (%151 (\%526. ((%164 $3)
       (((%193 $2) $1) $0))))))))) ((%65 (%66 (\%444. (%66 (\%525. (%151
       (\%526. ((%164 $3) (((%194 $2) $1) $0))))))))) ((%65 (%66 (\%444.
       (%66 (\%525. (%151 (\%526. ((%164 $3) (((%195 $2) $1) $0)))))))))
       ((%65 (%66 (\%444. (%66 (\%525. (%151 (\%526. ((%164 $3) (((%196 $2)
       $1) $0))))))))) ((%65 (%66 (\%444. (%66 (\%525. (%151 (\%526. ((%164
       $3) (((%197 $2) $1) $0))))))))) ((%65 (%66 (\%444. (%66 (\%525.
       (%151 (\%526. ((%164 $3) (((%198 $2) $1) $0))))))))) ((%65 (%66
       (\%444. (%66 (\%525. (%151 (\%526. ((%164 $3) (((%199 $2) $1)
       $0))))))))) ((%65 (%66 (\%444. (%66 (\%525. (%156 (\%527. ((%164 $3)
       (((%200 $2) $1) $0))))))))) ((%65 (%66 (\%444. (%66 (\%525. (%156
       (\%527. ((%164 $3) (((%201 $2) $1) $0))))))))) ((%65 (%66 (\%444.
       (%66 (\%525. (%156 (\%527. ((%164 $3) (((%202 $2) $1) $0)))))))))
       ((%65 (%66 (\%444. (%66 (\%525. (%156 (\%527. ((%164 $3) (((%203 $2)
       $1) $0))))))))) ((%65 (%158 (\%3. (%160 (\%528. ((%164 $2) ((%204
       $1) $0))))))) (%158 (\%3. (%160 (\%528. ((%164 $2) ((%205 $1)
       $0)))))))))))))))))))))))`)
  val DOPER_Axiom =
    DT(["DISK_THM"], [],
       `(%206 (\%529. (%208 (\%209. (%210 (\%211. (%212 (\%213. (%212
       (\%214. (%212 (\%215. (%212 (\%216. (%212 (\%217. (%212 (\%218.
       (%212 (\%219. (%220 (\%221. (%220 (\%222. (%220 (\%223. (%220
       (\%224. (%225 (\%226. (%225 (\%227. (%530 (\%531. ((%8 (%9 (\%129.
       (%228 (\%131. ((%53 ($2 ((%190 $1) $0))) (($18 $1) $0))))))) ((%8
       (%228 (\%149. (%9 (\%150. ((%53 ($2 ((%191 $1) $0))) (($17 $1)
       $0))))))) ((%8 (%9 (\%129. (%79 (\%152. ((%53 ($2 ((%192 $1) $0)))
       (($16 $1) $0))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155. ((%53
       ($3 (((%193 $2) $1) $0))) ((($16 $2) $1) $0))))))))) ((%8 (%9
       (\%129. (%9 (\%150. (%79 (\%155. ((%53 ($3 (((%194 $2) $1) $0)))
       ((($15 $2) $1) $0))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155.
       ((%53 ($3 (((%195 $2) $1) $0))) ((($14 $2) $1) $0))))))))) ((%8 (%9
       (\%129. (%9 (\%150. (%79 (\%155. ((%53 ($3 (((%196 $2) $1) $0)))
       ((($13 $2) $1) $0))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155.
       ((%53 ($3 (((%197 $2) $1) $0))) ((($12 $2) $1) $0))))))))) ((%8 (%9
       (\%129. (%9 (\%150. (%79 (\%155. ((%53 ($3 (((%198 $2) $1) $0)))
       ((($11 $2) $1) $0))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%79 (\%155.
       ((%53 ($3 (((%199 $2) $1) $0))) ((($10 $2) $1) $0))))))))) ((%8 (%9
       (\%129. (%9 (\%150. (%230 (\%157. ((%53 ($3 (((%200 $2) $1) $0)))
       ((($9 $2) $1) $0))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%230 (\%157.
       ((%53 ($3 (((%201 $2) $1) $0))) ((($8 $2) $1) $0))))))))) ((%8 (%9
       (\%129. (%9 (\%150. (%230 (\%157. ((%53 ($3 (((%202 $2) $1) $0)))
       ((($7 $2) $1) $0))))))))) ((%8 (%9 (\%129. (%9 (\%150. (%230 (\%157.
       ((%53 ($3 (((%203 $2) $1) $0))) ((($6 $2) $1) $0))))))))) ((%8 (%14
       (\%159. (%231 (\%161. ((%53 ($2 ((%204 $1) $0))) (($4 $1) $0)))))))
       (%14 (\%159. (%231 (\%161. ((%53 ($2 ((%205 $1) $0))) (($3 $1)
       $0)))))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val DOPER_induction =
    DT(["DISK_THM"], [],
       `(%532 (\%533. ((%63 ((%8 (%9 (\%444. (%228 (\%523. ($2 ((%190 $1)
       $0))))))) ((%8 (%228 (\%523. (%9 (\%444. ($2 ((%191 $1) $0)))))))
       ((%8 (%9 (\%444. (%79 (\%524. ($2 ((%192 $1) $0))))))) ((%8 (%9
       (\%444. (%9 (\%525. (%79 (\%526. ($3 (((%193 $2) $1) $0)))))))))
       ((%8 (%9 (\%444. (%9 (\%525. (%79 (\%526. ($3 (((%194 $2) $1)
       $0))))))))) ((%8 (%9 (\%444. (%9 (\%525. (%79 (\%526. ($3 (((%195
       $2) $1) $0))))))))) ((%8 (%9 (\%444. (%9 (\%525. (%79 (\%526. ($3
       (((%196 $2) $1) $0))))))))) ((%8 (%9 (\%444. (%9 (\%525. (%79
       (\%526. ($3 (((%197 $2) $1) $0))))))))) ((%8 (%9 (\%444. (%9 (\%525.
       (%79 (\%526. ($3 (((%198 $2) $1) $0))))))))) ((%8 (%9 (\%444. (%9
       (\%525. (%79 (\%526. ($3 (((%199 $2) $1) $0))))))))) ((%8 (%9
       (\%444. (%9 (\%525. (%230 (\%527. ($3 (((%200 $2) $1) $0)))))))))
       ((%8 (%9 (\%444. (%9 (\%525. (%230 (\%527. ($3 (((%201 $2) $1)
       $0))))))))) ((%8 (%9 (\%444. (%9 (\%525. (%230 (\%527. ($3 (((%202
       $2) $1) $0))))))))) ((%8 (%9 (\%444. (%9 (\%525. (%230 (\%527. ($3
       (((%203 $2) $1) $0))))))))) ((%8 (%14 (\%3. (%231 (\%528. ($2 ((%204
       $1) $0))))))) (%14 (\%3. (%231 (\%528. ($2 ((%205 $1)
       $0)))))))))))))))))))))) (%162 (\%522. ($1 $0))))))`)
  val datatype_CTL_STRUCTURE =
    DT(["DISK_THM"], [], `(%441 ((((%534 %279) %280) %281) %282))`)
  val CTL_STRUCTURE_11 =
    DT(["DISK_THM"], [],
       `((%8 (%291 (\%246. (%291 (\%535. ((%16 ((%264 (%279 $1)) (%279
       $0))) ((%536 $1) $0))))))) ((%8 (%262 (\%272. (%262 (\%273. (%262
       (\%537. (%262 (\%538. ((%16 ((%264 ((%280 $3) $2)) ((%280 $1) $0)))
       ((%8 ((%264 $3) $1)) ((%264 $2) $0)))))))))))) ((%8 (%293 (\%260.
       (%262 (\%273. (%262 (\%276. (%293 (\%539. (%262 (\%538. (%262
       (\%540. ((%16 ((%264 (((%281 $5) $4) $3)) (((%281 $2) $1) $0))) ((%8
       ((%541 $5) $2)) ((%8 ((%264 $4) $1)) ((%264 $3) $0)))))))))))))))))
       (%293 (\%260. (%262 (\%273. (%293 (\%539. (%262 (\%538. ((%16 ((%264
       ((%282 $3) $2)) ((%282 $1) $0))) ((%8 ((%541 $3) $1)) ((%264 $2)
       $0))))))))))))))`)
  val CTL_STRUCTURE_distinct =
    DT(["DISK_THM"], [],
       `((%8 (%262 (\%273. (%262 (\%272. (%291 (\%246. (%443 ((%264 (%279
       $0)) ((%280 $1) $2)))))))))) ((%8 (%262 (\%276. (%262 (\%273. (%293
       (\%260. (%291 (\%246. (%443 ((%264 (%279 $0)) (((%281 $1) $2)
       $3)))))))))))) ((%8 (%262 (\%273. (%293 (\%260. (%291 (\%246. (%443
       ((%264 (%279 $0)) ((%282 $1) $2)))))))))) ((%8 (%262 (\%276. (%262
       (\%538. (%262 (\%273. (%293 (\%539. (%262 (\%272. (%443 ((%264
       ((%280 $0) $2)) (((%281 $1) $3) $4)))))))))))))) ((%8 (%262 (\%538.
       (%262 (\%273. (%293 (\%539. (%262 (\%272. (%443 ((%264 ((%280 $0)
       $2)) ((%282 $1) $3)))))))))))) (%262 (\%276. (%262 (\%538. (%262
       (\%273. (%293 (\%539. (%293 (\%260. (%443 ((%264 (((%281 $0) $2)
       $4)) ((%282 $1) $3))))))))))))))))))`)
  val CTL_STRUCTURE_case_cong =
    DT(["DISK_THM"], [],
       `(%262 (\%542. (%262 (\%543. (%283 (\%284. (%285 (\%286. (%287
       (\%288. (%289 (\%290. ((%63 ((%8 ((%264 $5) $4)) ((%8 (%291 (\%246.
       ((%63 ((%264 $5) (%279 $0))) ((%53 ($4 $0)) (%544 $0)))))) ((%8
       (%262 (\%272. (%262 (\%273. ((%63 ((%264 $6) ((%280 $1) $0))) ((%53
       (($4 $1) $0)) ((%545 $1) $0)))))))) ((%8 (%293 (\%260. (%262 (\%273.
       (%262 (\%276. ((%63 ((%264 $7) (((%281 $2) $1) $0))) ((%53 ((($4 $2)
       $1) $0)) (((%546 $2) $1) $0)))))))))) (%293 (\%260. (%262 (\%273.
       ((%63 ((%264 $6) ((%282 $1) $0))) ((%53 (($2 $1) $0)) ((%547 $1)
       $0)))))))))))) ((%53 (((((%292 $3) $2) $1) $0) $5)) (((((%292 %544)
       %545) %546) %547) $4)))))))))))))))`)
  val CTL_STRUCTURE_nchotomy =
    DT(["DISK_THM"], [],
       `(%262 (\%548. ((%65 (%245 (\%549. ((%264 $1) (%279 $0))))) ((%65
       (%550 (\%548. (%550 (\%551. ((%264 $2) ((%280 $1) $0))))))) ((%65
       (%259 (\%552. (%550 (\%548. (%550 (\%551. ((%264 $3) (((%281 $2) $1)
       $0))))))))) (%259 (\%552. (%550 (\%548. ((%264 $2) ((%282 $1)
       $0)))))))))))`)
  val CTL_STRUCTURE_Axiom =
    DT(["DISK_THM"], [],
       `(%283 (\%553. (%554 (\%555. (%556 (\%557. (%558 (\%559. (%560
       (\%561. ((%8 (%291 (\%246. ((%53 ($1 (%279 $0))) ($5 $0))))) ((%8
       (%262 (\%272. (%262 (\%273. ((%53 ($2 ((%280 $1) $0))) (((($5 $1)
       $0) ($2 $1)) ($2 $0)))))))) ((%8 (%293 (\%260. (%262 (\%273. (%262
       (\%276. ((%53 ($3 (((%281 $2) $1) $0))) ((((($5 $2) $1) $0) ($3 $1))
       ($3 $0)))))))))) (%293 (\%260. (%262 (\%273. ((%53 ($2 ((%282 $1)
       $0))) ((($3 $1) $0) ($2 $0))))))))))))))))))))`)
  val CTL_STRUCTURE_induction =
    DT(["DISK_THM"], [],
       `(%562 (\%563. ((%63 ((%8 (%291 (\%549. ($1 (%279 $0))))) ((%8 (%262
       (\%548. (%262 (\%551. ((%63 ((%8 ($2 $1)) ($2 $0))) ($2 ((%280 $1)
       $0)))))))) ((%8 (%262 (\%548. (%262 (\%551. ((%63 ((%8 ($2 $1)) ($2
       $0))) (%293 (\%552. ($3 (((%281 $0) $2) $1)))))))))) (%262 (\%548.
       ((%63 ($1 $0)) (%293 (\%552. ($2 ((%282 $0) $1))))))))))) (%262
       (\%548. ($1 $0))))))`)
  val TRANSLATE_ASSIGMENT_CORRECT =
    DT(["DISK_THM"], [],
       `(%162 (\%397. (%14 (\%417. (%96 (\%418. (%302 (\%303. ((%564 ((%424
       (%76 $2)) ((%425 $1) ((%327 $0) $3)))) ((%565 ((%424 $2) ((%425 $1)
       $0))) (%347 $3)))))))))))`)
  val TRANSLATE_ASSIGMENT_CORRECT_2 =
    DT(["DISK_THM"], [],
       `(%162 (\%397. (%566 (\%567. ((%564 ((%565 $0) (%347 $1))) ((%424
       (%76 (%568 $0))) ((%425 (%569 (%570 $0))) ((%327 (%571 (%570 $0)))
       $1))))))))`)
  val translate_ind =
    DT(["DISK_THM"], [],
       `(%562 (\%563. ((%63 ((%8 (%162 (\%397. (%291 (\%398. ((%63 ($2
       (%279 $0))) ($2 (%279 ((%399 $1) $0))))))))) ((%8 ($0 (%279 %572)))
       ((%8 (%262 (\%400. (%262 (\%401. ((%63 ((%8 ($2 $1)) ($2 $0))) ($2
       ((%280 $1) $0)))))))) ((%8 (%293 (\%386. (%262 (\%403. (%262 (\%402.
       ((%63 ((%8 ($3 $0)) ($3 $1))) ($3 (((%281 $2) $1) $0)))))))))) (%293
       (\%386. (%262 (\%404. ((%63 ($2 $0)) ($2 ((%282 $1) $0))))))))))))
       (%262 (\%573. ($1 $0))))))`)
  val translate_def =
    DT(["DISK_THM"], [],
       `((%8 ((%574 (%392 (%279 ((%399 %397) %398)))) ((%410 (%347 %397))
       (%392 (%279 %398))))) ((%8 ((%574 (%392 (%279 %572))) %409)) ((%8
       ((%574 (%392 ((%280 %400) %401))) ((%411 (%392 %400)) (%392 %401))))
       ((%8 ((%574 (%392 (((%281 %386) %403) %402))) (((%412 (%390 %386))
       (%392 %403)) (%392 %402)))) ((%574 (%392 ((%282 %386) %404))) ((%414
       (%390 %386)) (%392 %404)))))))`)
  val WELL_FORMED_SUB_thm =
    DT(["DISK_THM"], [],
       `(%262 (\%575. ((%16 (%434 $0)) ((%8 (%438 $0)) (%435 (%392
       $0))))))`)
  val HOARE_SC_CFL =
    DT(["DISK_THM"], [],
       `(%262 (\%400. (%262 (\%401. (%576 (\%577. (%576 (\%578. (%576
       (\%579. (%576 (\%580. ((%63 ((%8 (%434 $5)) ((%8 (%434 $4)) ((%8
       (%302 (\%303. ((%63 ($4 $0)) ($3 ((%431 $6) $0)))))) ((%8 (%302
       (\%303. ((%63 ($2 $0)) ($1 ((%431 $5) $0)))))) (%302 (\%303. ((%63
       ($3 $0)) ($2 $0))))))))) (%302 (\%303. ((%63 ($4 $0)) ($1 ((%431
       ((%280 $6) $5)) $0))))))))))))))))))`)
  val HOARE_CJ_CFL =
    DT(["DISK_THM"], [],
       `(%293 (\%386. (%262 (\%581. (%262 (\%582. (%576 (\%577. (%576
       (\%578. (%576 (\%579. ((%63 ((%8 (%434 $4)) ((%8 (%434 $3)) ((%8
       (%302 (\%303. ((%63 ($3 $0)) ($2 ((%431 $5) $0)))))) (%302 (\%303.
       ((%63 ($3 $0)) ($1 ((%431 $4) $0))))))))) (%302 (\%303. ((%63 ($3
       $0)) (((%583 ((%388 $6) $0)) ($2 ((%431 (((%281 $6) $5) $4)) $0)))
       ($1 ((%431 (((%281 $6) $5) $4)) $0)))))))))))))))))))`)
  val HOARE_TR_CFL =
    DT(["DISK_THM"], [],
       `(%293 (\%386. (%37 (\%584. (%576 (\%577. ((%63 ((%8 (%434 %575))
       ((%8 (%436 ((%437 (%390 $2)) (%392 %575)))) (%302 (\%303. ((%63 ($1
       $0)) ($1 ((%431 %575) $0)))))))) (%302 (\%303. ((%63 ($1 $0)) ((%8
       ($1 ((%431 ((%282 $3) %575)) $0))) ((%388 $3) ((%431 ((%282 $3)
       %575)) $0)))))))))))))`)
  val UPLOAD_LEM_2 =
    DT(["DISK_THM"], [],
       `(%585 (\%586. (%587 (\%588. (%589 (\%590. ((%591 ((((%592 ((%593
       $1) %594)) $0) (%595 $2)) (%595 $2))) $1)))))))`)
  val STATEMENT_IS_WELL_FORMED =
    DT(["DISK_THM"], [], `(%162 (\%397. (%435 ((%410 (%347 $0)) %409))))`)
  val BLOCK_IS_WELL_FORMED =
    DT(["DISK_THM"], [], `(%291 (\%398. (%434 (%279 $0))))`)
  val CFL_SC_IS_WELL_FORMED =
    DT(["DISK_THM"], [],
       `(%262 (\%400. (%262 (\%401. ((%16 ((%8 (%434 $1)) (%434 $0))) (%434
       ((%280 $1) $0)))))))`)
  val CFL_CJ_IS_WELL_FORMED =
    DT(["DISK_THM"], [],
       `(%293 (\%386. (%262 (\%581. (%262 (\%582. ((%16 ((%8 (%434 $1))
       (%434 $0))) (%434 (((%281 $2) $1) $0)))))))))`)
  val CFL_TR_IS_WELL_FORMED =
    DT(["DISK_THM"], [],
       `(%262 (\%575. (%293 (\%386. ((%16 ((%8 (%434 $1)) (%436 ((%437
       (%390 $0)) (%392 $1))))) (%434 ((%282 $0) $1)))))))`)
  val WELL_FORMED_thm =
    DT(["DISK_THM"], [],
       `((%8 ((%16 (%434 (%279 %398))) %72)) ((%8 ((%16 (%434 ((%280 %400)
       %401))) ((%8 (%434 %400)) (%434 %401)))) ((%8 ((%16 (%434 (((%281
       %386) %400) %401))) ((%8 (%434 %400)) (%434 %401)))) ((%16 (%434
       ((%282 %386) %596))) ((%8 (%434 %596)) (%436 ((%437 (%390 %386))
       (%392 %596))))))))`)
  val CFL_SEMANTICS_SC =
    DT(["DISK_THM"], [],
       `((%63 ((%8 (%434 %400)) (%434 %401))) ((%306 ((%431 ((%280 %400)
       %401)) %303)) ((%431 %401) ((%431 %400) %303))))`)
  val CFL_SEMANTICS_BLK =
    DT(["DISK_THM"], [],
       `((%8 ((%306 ((%431 (%279 ((%399 %397) %398))) %303)) ((%431 (%279
       %398)) ((%327 %303) %397)))) ((%306 ((%431 (%279 %572)) %303))
       %303))`)
  val CFL_SEMANTICS_CJ =
    DT(["DISK_THM"], [],
       `((%63 ((%8 (%434 %581)) (%434 %582))) ((%306 ((%431 (((%281 %386)
       %581) %582)) %303)) (((%597 ((%388 %386) %303)) ((%431 %581) %303))
       ((%431 %582) %303))))`)
  val CFL_SEMANTICS_TR =
    DT(["DISK_THM"], [],
       `((%63 ((%8 (%434 %596)) (%436 ((%437 (%390 %386)) (%392 %596)))))
       ((%306 ((%431 ((%282 %386) %596)) %303)) (((%598 (\%599. (%443
       ((%388 %386) $0)))) (%431 %596)) %303)))`)
  val SEMANTICS_OF_CFL =
    DT(["DISK_THM"], [],
       `((%63 ((%8 (%434 %400)) (%434 %401))) ((%8 ((%306 ((%431 (%279
       ((%399 %397) %398))) %303)) ((%431 (%279 %398)) ((%327 %303)
       %397)))) ((%8 ((%306 ((%431 (%279 %572)) %303)) %303)) ((%8 ((%306
       ((%431 ((%280 %400) %401)) %303)) ((%431 %401) ((%431 %400) %303))))
       ((%8 ((%306 ((%431 (((%281 %386) %400) %401)) %303)) (((%597 ((%388
       %386) %303)) ((%431 %400) %303)) ((%431 %401) %303)))) ((%63 (%436
       ((%437 (%390 %386)) (%392 %400)))) ((%306 ((%431 ((%282 %386) %400))
       %303)) (((%598 (\%599. (%443 ((%388 %386) $0)))) (%431 %400))
       %303))))))))`)
  end
  val _ = DB.bindl "CFL"
  [("MREG_TY_DEF",MREG_TY_DEF,DB.Def), ("MREG_BIJ",MREG_BIJ,DB.Def),
   ("R0",R0,DB.Def), ("R1",R1,DB.Def), ("R2",R2,DB.Def), ("R3",R3,DB.Def),
   ("R4",R4,DB.Def), ("R5",R5,DB.Def), ("R6",R6,DB.Def), ("R7",R7,DB.Def),
   ("R8",R8,DB.Def), ("R9",R9,DB.Def), ("R10",R10,DB.Def),
   ("R11",R11,DB.Def), ("R12",R12,DB.Def), ("R13",R13,DB.Def),
   ("R14",R14,DB.Def), ("MREG_size_def",MREG_size_def,DB.Def),
   ("MREG_case",MREG_case,DB.Def), ("MEXP_TY_DEF",MEXP_TY_DEF,DB.Def),
   ("MEXP_repfns",MEXP_repfns,DB.Def), ("CFL0_def",CFL0_def,DB.Def),
   ("CFL1_def",CFL1_def,DB.Def), ("MR",MR,DB.Def), ("MC",MC,DB.Def),
   ("MEXP_case_def",MEXP_case_def,DB.Def),
   ("MEXP_size_def",MEXP_size_def,DB.Def),
   ("index_of_reg_def",index_of_reg_def,DB.Def),
   ("from_reg_index_def",from_reg_index_def,DB.Def),
   ("toREG_def",toREG_def,DB.Def), ("toMEM_def",toMEM_def,DB.Def),
   ("toEXP_def",toEXP_def,DB.Def), ("tp_def",tp_def,DB.Def),
   ("gp_def",gp_def,DB.Def), ("fp_def",fp_def,DB.Def),
   ("ip_def",ip_def,DB.Def), ("sp_def",sp_def,DB.Def),
   ("lr_def",lr_def,DB.Def), ("DOPER_TY_DEF",DOPER_TY_DEF,DB.Def),
   ("DOPER_repfns",DOPER_repfns,DB.Def), ("CFL2_def",CFL2_def,DB.Def),
   ("CFL3_def",CFL3_def,DB.Def), ("CFL4_def",CFL4_def,DB.Def),
   ("CFL5_def",CFL5_def,DB.Def), ("CFL6_def",CFL6_def,DB.Def),
   ("CFL7_def",CFL7_def,DB.Def), ("CFL8_def",CFL8_def,DB.Def),
   ("CFL9_def",CFL9_def,DB.Def), ("CFL10_def",CFL10_def,DB.Def),
   ("CFL11_def",CFL11_def,DB.Def), ("CFL12_def",CFL12_def,DB.Def),
   ("CFL13_def",CFL13_def,DB.Def), ("CFL14_def",CFL14_def,DB.Def),
   ("CFL15_def",CFL15_def,DB.Def), ("CFL16_def",CFL16_def,DB.Def),
   ("CFL17_def",CFL17_def,DB.Def), ("MLDR",MLDR,DB.Def),
   ("MSTR",MSTR,DB.Def), ("MMOV",MMOV,DB.Def), ("MADD",MADD,DB.Def),
   ("MSUB",MSUB,DB.Def), ("MRSB",MRSB,DB.Def), ("MMUL",MMUL,DB.Def),
   ("MAND",MAND,DB.Def), ("MORR",MORR,DB.Def), ("MEOR",MEOR,DB.Def),
   ("MLSL",MLSL,DB.Def), ("MLSR",MLSR,DB.Def), ("MASR",MASR,DB.Def),
   ("MROR",MROR,DB.Def), ("MPUSH",MPUSH,DB.Def), ("MPOP",MPOP,DB.Def),
   ("DOPER_case_def",DOPER_case_def,DB.Def),
   ("DOPER_size_def",DOPER_size_def,DB.Def),
   ("CTL_STRUCTURE_TY_DEF",CTL_STRUCTURE_TY_DEF,DB.Def),
   ("CTL_STRUCTURE_repfns",CTL_STRUCTURE_repfns,DB.Def),
   ("CFL18_def",CFL18_def,DB.Def), ("CFL19_def",CFL19_def,DB.Def),
   ("CFL20_def",CFL20_def,DB.Def), ("CFL21_def",CFL21_def,DB.Def),
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
   ("run_arm_def",run_arm_def,DB.Def), ("run_cfl_def",run_cfl_def,DB.Def),
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
   ("HOARE_SC_CFL",HOARE_SC_CFL,DB.Thm),
   ("HOARE_CJ_CFL",HOARE_CJ_CFL,DB.Thm),
   ("HOARE_TR_CFL",HOARE_TR_CFL,DB.Thm),
   ("UPLOAD_LEM_2",UPLOAD_LEM_2,DB.Thm),
   ("STATEMENT_IS_WELL_FORMED",STATEMENT_IS_WELL_FORMED,DB.Thm),
   ("BLOCK_IS_WELL_FORMED",BLOCK_IS_WELL_FORMED,DB.Thm),
   ("CFL_SC_IS_WELL_FORMED",CFL_SC_IS_WELL_FORMED,DB.Thm),
   ("CFL_CJ_IS_WELL_FORMED",CFL_CJ_IS_WELL_FORMED,DB.Thm),
   ("CFL_TR_IS_WELL_FORMED",CFL_TR_IS_WELL_FORMED,DB.Thm),
   ("WELL_FORMED_thm",WELL_FORMED_thm,DB.Thm),
   ("CFL_SEMANTICS_SC",CFL_SEMANTICS_SC,DB.Thm),
   ("CFL_SEMANTICS_BLK",CFL_SEMANTICS_BLK,DB.Thm),
   ("CFL_SEMANTICS_CJ",CFL_SEMANTICS_CJ,DB.Thm),
   ("CFL_SEMANTICS_TR",CFL_SEMANTICS_TR,DB.Thm),
   ("SEMANTICS_OF_CFL",SEMANTICS_OF_CFL,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("ARMCompositionTheory.ARMComposition_grammars",
                          ARMCompositionTheory.ARMComposition_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms temp_add_type "MREG"
  val _ = update_grms
       (temp_overload_on_by_nametype "MREG2num")
        {Name = "MREG2num", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "num2MREG")
        {Name = "num2MREG", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R0")
        {Name = "R0", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R1")
        {Name = "R1", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R2")
        {Name = "R2", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R3")
        {Name = "R3", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R4")
        {Name = "R4", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R5")
        {Name = "R5", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R6")
        {Name = "R6", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R7")
        {Name = "R7", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R8")
        {Name = "R8", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R9")
        {Name = "R9", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R10")
        {Name = "R10", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R11")
        {Name = "R11", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R12")
        {Name = "R12", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R13")
        {Name = "R13", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "R14")
        {Name = "R14", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MREG_size")
        {Name = "MREG_size", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MREG_case")
        {Name = "MREG_case", Thy = "CFL"}
  val _ = update_grms
       temp_type_abbrev
       ("MMEM", T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []])
  val _ = update_grms temp_add_type "MEXP"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_MEXP")
        {Name = "dest_MEXP", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_MEXP")
        {Name = "mk_MEXP", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL0")
        {Name = "CFL0", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL1")
        {Name = "CFL1", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MR")
        {Name = "MR", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MC")
        {Name = "MC", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MEXP_case")
        {Name = "MEXP_case", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MEXP_size")
        {Name = "MEXP_size", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "index_of_reg")
        {Name = "index_of_reg", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "from_reg_index")
        {Name = "from_reg_index", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "toREG")
        {Name = "toREG", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "toMEM")
        {Name = "toMEM", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "toEXP")
        {Name = "toEXP", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "tp")
        {Name = "tp", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "gp")
        {Name = "gp", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "fp")
        {Name = "fp", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ip")
        {Name = "ip", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "sp")
        {Name = "sp", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "lr")
        {Name = "lr", Thy = "CFL"}
  val _ = update_grms temp_add_type "DOPER"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_DOPER")
        {Name = "dest_DOPER", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_DOPER")
        {Name = "mk_DOPER", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL2")
        {Name = "CFL2", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL3")
        {Name = "CFL3", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL4")
        {Name = "CFL4", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL5")
        {Name = "CFL5", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL6")
        {Name = "CFL6", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL7")
        {Name = "CFL7", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL8")
        {Name = "CFL8", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL9")
        {Name = "CFL9", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL10")
        {Name = "CFL10", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL11")
        {Name = "CFL11", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL12")
        {Name = "CFL12", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL13")
        {Name = "CFL13", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL14")
        {Name = "CFL14", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL15")
        {Name = "CFL15", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL16")
        {Name = "CFL16", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL17")
        {Name = "CFL17", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MLDR")
        {Name = "MLDR", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MSTR")
        {Name = "MSTR", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MMOV")
        {Name = "MMOV", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MADD")
        {Name = "MADD", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MSUB")
        {Name = "MSUB", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MRSB")
        {Name = "MRSB", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MMUL")
        {Name = "MMUL", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MAND")
        {Name = "MAND", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MORR")
        {Name = "MORR", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MEOR")
        {Name = "MEOR", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MLSL")
        {Name = "MLSL", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MLSR")
        {Name = "MLSR", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MASR")
        {Name = "MASR", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MROR")
        {Name = "MROR", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MPUSH")
        {Name = "MPUSH", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MPOP")
        {Name = "MPOP", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "DOPER_case")
        {Name = "DOPER_case", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "DOPER_size")
        {Name = "DOPER_size", Thy = "CFL"}
  val _ = update_grms
       temp_type_abbrev
       ("CEXP", T"prod" "pair"
 [T"MREG" "CFL" [],
  T"prod" "pair" [T"COND" "preARM" [], T"MEXP" "CFL" []]])
  val _ = update_grms temp_add_type "CTL_STRUCTURE"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_CTL_STRUCTURE")
        {Name = "dest_CTL_STRUCTURE", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_CTL_STRUCTURE")
        {Name = "mk_CTL_STRUCTURE", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL18")
        {Name = "CFL18", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL19")
        {Name = "CFL19", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL20")
        {Name = "CFL20", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CFL21")
        {Name = "CFL21", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "BLK")
        {Name = "BLK", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SC")
        {Name = "SC", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CJ")
        {Name = "CJ", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TR")
        {Name = "TR", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CTL_STRUCTURE_case")
        {Name = "CTL_STRUCTURE_case", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CTL_STRUCTURE_size")
        {Name = "CTL_STRUCTURE_size", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "pushL")
        {Name = "pushL", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "popL")
        {Name = "popL", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mdecode")
        {Name = "mdecode", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "translate_assignment")
        {Name = "translate_assignment", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "translate_condition")
        {Name = "translate_condition", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eval_il_cond")
        {Name = "eval_il_cond", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "translate")
        {Name = "translate", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "run_arm")
        {Name = "run_arm", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "run_cfl")
        {Name = "run_cfl", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "WELL_FORMED")
        {Name = "WELL_FORMED", Thy = "CFL"}
  val _ = update_grms
       (temp_overload_on_by_nametype "WELL_FORMED_SUB")
        {Name = "WELL_FORMED_SUB", Thy = "CFL"}
  val CFL_grammars = Parse.current_lgrms()
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
           size=SOME(Parse.Term`(CFL$MREG_size) :(CFL$MREG) -> (num$num)`,
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
           size=SOME(Parse.Term`(CFL$MEXP_size) :(CFL$MEXP) -> (num$num)`,
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
  
  val _ = computeLib.add_funs [tp_def];  
  
  val _ = computeLib.add_funs [gp_def];  
  
  val _ = computeLib.add_funs [fp_def];  
  
  val _ = computeLib.add_funs [ip_def];  
  
  val _ = computeLib.add_funs [sp_def];  
  
  val _ = computeLib.add_funs [lr_def];  
  
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
           size=SOME(Parse.Term`(CFL$DOPER_size) :(CFL$DOPER) -> (num$num)`,
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
           size=SOME(Parse.Term`(CFL$CTL_STRUCTURE_size) :(CFL$CTL_STRUCTURE) -> (num$num)`,
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
  
  val _ = computeLib.add_funs [run_cfl_def];  
  
  val _ = computeLib.add_funs [WELL_FORMED_def];  
  
  val _ = computeLib.add_funs [WELL_FORMED_SUB_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
