structure preARMTheory :> preARMTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading preARMTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open finite_mapTheory wordsTheory
  in end;
  val _ = Theory.link_parents
          ("preARM",
          Arbnum.fromString "1162366112",
          Arbnum.fromString "110449")
          [("finite_map",
           Arbnum.fromString "1157051022",
           Arbnum.fromString "797566"),
           ("words",
           Arbnum.fromString "1157051160",
           Arbnum.fromString "554114")];
  val _ = Theory.incorporate_types "preARM"
       [("EXP",0), ("SRS",0), ("OFFSET",0), ("OPERATOR",0), ("COND",0)];
  val _ = Theory.incorporate_consts "preARM"
     [("num2OPERATOR",((T"num" "num" [] --> T"OPERATOR" "preARM" []))),
      ("shortest",
       (((alpha --> bool) -->
         ((alpha --> alpha) --> (alpha --> T"num" "num" []))))),
      ("NCONST",((T"num" "num" [] --> T"EXP" "preARM" []))),
      ("TST",(T"OPERATOR" "preARM" [])), ("STR",(T"OPERATOR" "preARM" [])),
      ("step",
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
      ("upload",
       ((T"list" "list" [alpha] -->
         ((T"num" "num" [] --> alpha) -->
          (T"num" "num" [] --> (T"num" "num" [] --> alpha)))))),
      ("SUB",(T"OPERATOR" "preARM" [])), ("ROR",(T"OPERATOR" "preARM" [])),
      ("RSB",(T"OPERATOR" "preARM" [])),
      ("POS",((T"num" "num" [] --> T"OFFSET" "preARM" []))),
      ("ORR",(T"OPERATOR" "preARM" [])),
      ("REG",((T"num" "num" [] --> T"EXP" "preARM" []))),
      ("MUL",(T"OPERATOR" "preARM" [])), ("MSR",(T"OPERATOR" "preARM" [])),
      ("MRS",(T"OPERATOR" "preARM" [])), ("MOV",(T"OPERATOR" "preARM" [])),
      ("LSR",(T"OPERATOR" "preARM" [])), ("LSL",(T"OPERATOR" "preARM" [])),
      ("EXP_size",((T"EXP" "preARM" [] --> T"num" "num" []))),
      ("MLA",(T"OPERATOR" "preARM" [])),
      ("terd",
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
             (T"num" "num" [] --> bool)] --> bool))))),
      ("NEG",((T"num" "num" [] --> T"OFFSET" "preARM" []))),
      ("SRS_size",((T"SRS" "preARM" [] --> T"num" "num" []))),
      ("MEM",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         T"EXP" "preARM" []))),
      ("run_tupled",
       ((T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [(T"num" "num" [] -->
              T"prod" "pair"
               [T"prod" "pair"
                 [T"OPERATOR" "preARM" [],
                  T"prod" "pair"
                   [T"option" "option" [T"COND" "preARM" []], bool]],
                T"prod" "pair"
                 [T"option" "option" [T"EXP" "preARM" []],
                  T"prod" "pair"
                   [T"list" "list" [T"EXP" "preARM" []],
                    T"option" "option" [T"OFFSET" "preARM" []]]]]),
             T"prod" "pair"
              [(T"prod" "pair"
                 [T"num" "num" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i32" "words" []],
                    T"prod" "pair"
                     [T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]],
                      T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
                bool),
               T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
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
      ("LDR",(T"OPERATOR" "preARM" [])),
      ("setS",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         (T"SRS" "preARM" [] -->
          T"cart" "fcp" [bool, T"i32" "words" []])))),
      ("num2SRS",((T"num" "num" [] --> T"SRS" "preARM" []))),
      ("EOR",(T"OPERATOR" "preARM" [])),
      ("preARM6",((T"num" "num" [] --> T"EXP" "preARM" []))),
      ("preARM5",((T"num" "num" [] --> T"EXP" "preARM" []))),
      ("preARM4",
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"EXP" "preARM" []))),
      ("preARM3",((T"num" "num" [] --> T"EXP" "preARM" []))),
      ("preARM2",
       ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
         T"EXP" "preARM" []))),
      ("preARM1",((T"num" "num" [] --> T"OFFSET" "preARM" []))),
      ("preARM0",((T"num" "num" [] --> T"OFFSET" "preARM" []))),
      ("CMP",(T"OPERATOR" "preARM" [])), ("ASR",(T"OPERATOR" "preARM" [])),
      ("AND",(T"OPERATOR" "preARM" [])),
      ("read",
       ((T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         (T"EXP" "preARM" [] -->
          T"cart" "fcp" [bool, T"i32" "words" []])))),
      ("LDMFD",(T"OPERATOR" "preARM" [])),
      ("ADD",(T"OPERATOR" "preARM" [])),
      ("COND_size",((T"COND" "preARM" [] --> T"num" "num" []))),
      ("OFFSET_size",((T"OFFSET" "preARM" [] --> T"num" "num" []))),
      ("mk_OFFSET",
       ((T"recspace" "ind_type" [T"num" "num" []] -->
         T"OFFSET" "preARM" []))),
      ("setNZCV",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         (T"prod" "pair"
           [bool, T"prod" "pair" [bool, T"prod" "pair" [bool, bool]]] -->
          T"cart" "fcp" [bool, T"i32" "words" []])))),
      ("WREG",((T"num" "num" [] --> T"EXP" "preARM" []))),
      ("OPERATOR_case",
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
                       (alpha -->
                        (alpha -->
                         (alpha -->
                          (alpha -->
                           (alpha -->
                            (alpha -->
                             (alpha -->
                              (alpha -->
                               (T"OPERATOR" "preARM" [] -->
                                alpha)))))))))))))))))))))))))),
      ("in_mem_dom",
       ((T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool))),
      ("num2COND",((T"num" "num" [] --> T"COND" "preARM" []))),
      ("WCONST",
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"EXP" "preARM" []))),
      ("decode_cond",
       ((T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
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
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]]])))),
      ("goto",
       ((T"prod" "pair"
          [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
         T"num" "num" []))),
      ("SRS2num",((T"SRS" "preARM" [] --> T"num" "num" []))),
      ("runTo",
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
             (T"num" "num" [] --> bool)]))))),
      ("COND2num",((T"COND" "preARM" [] --> T"num" "num" []))),
      ("uploadSeg",
       ((T"num" "num" [] -->
         (T"list" "list" [T"list" "list" [alpha]] -->
          ((T"num" "num" [] --> alpha) -->
           (T"num" "num" [] --> alpha)))))),
      ("stopAt",
       (((alpha --> bool) --> ((alpha --> alpha) --> (alpha --> bool))))),
      ("getS",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         (T"SRS" "preARM" [] --> bool)))),
      ("mk_EXP",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"prod" "pair"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> T"EXP" "preARM" []))),
      ("uploadCode",
       ((T"list" "list" [alpha] -->
         ((T"num" "num" [] --> alpha) --> (T"num" "num" [] --> alpha))))),
      ("in_regs_dom",
       ((T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool))),
      ("OPERATOR2num",((T"OPERATOR" "preARM" [] --> T"num" "num" []))),
      ("decode_cond_cpsr",
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         (T"COND" "preARM" [] --> bool)))),
      ("EXP_case",
       (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
          alpha) -->
         ((T"num" "num" [] --> alpha) -->
          ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
           ((T"num" "num" [] --> alpha) -->
            ((T"num" "num" [] --> alpha) -->
             (T"EXP" "preARM" [] --> alpha)))))))),
      ("VS",(T"COND" "preARM" [])), ("SZ",(T"SRS" "preARM" [])),
      ("SV",(T"SRS" "preARM" [])), ("SP",(T"EXP" "preARM" [])),
      ("SRS_case",
       ((alpha -->
         (alpha -->
          (alpha --> (alpha --> (T"SRS" "preARM" [] --> alpha))))))),
      ("VC",(T"COND" "preARM" [])), ("SN",(T"SRS" "preARM" [])),
      ("OPERATOR_size",((T"OPERATOR" "preARM" [] --> T"num" "num" []))),
      ("run",
       ((T"num" "num" [] -->
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
          ((T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool)
           -->
           (T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
            T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]])))))),
      ("SC",(T"SRS" "preARM" [])), ("NV",(T"COND" "preARM" [])),
      ("PL",(T"COND" "preARM" [])), ("LT",(T"COND" "preARM" [])),
      ("PC",(T"EXP" "preARM" [])), ("LS",(T"COND" "preARM" [])),
      ("LR",(T"EXP" "preARM" [])), ("NE",(T"COND" "preARM" [])),
      ("MI",(T"COND" "preARM" [])), ("LE",(T"COND" "preARM" [])),
      ("IP",(T"EXP" "preARM" [])), ("GT",(T"COND" "preARM" [])),
      ("HI",(T"COND" "preARM" [])), ("FP",(T"EXP" "preARM" [])),
      ("EQ",(T"COND" "preARM" [])), ("GE",(T"COND" "preARM" [])),
      ("CS",(T"COND" "preARM" [])), ("BL",(T"OPERATOR" "preARM" [])),
      ("AL",(T"COND" "preARM" [])), ("CC",(T"COND" "preARM" [])),
      ("dest_EXP",
       ((T"EXP" "preARM" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"prod" "pair"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
      ("STMFD",(T"OPERATOR" "preARM" [])),
      ("COND_case",
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
                       (alpha -->
                        (T"COND" "preARM" [] --> alpha))))))))))))))))))),
      ("OFFSET_case",
       (((T"num" "num" [] --> alpha) -->
         ((T"num" "num" [] --> alpha) -->
          (T"OFFSET" "preARM" [] --> alpha))))),
      ("dest_OFFSET",
       ((T"OFFSET" "preARM" [] -->
         T"recspace" "ind_type" [T"num" "num" []]))),
      ("decode_op",
       ((T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
         (T"prod" "pair"
           [T"OPERATOR" "preARM" [],
            T"prod" "pair"
             [T"option" "option" [T"EXP" "preARM" []],
              T"prod" "pair" [T"list" "list" [T"EXP" "preARM" []], alpha]]]
          -->
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]])))),
      ("B",(T"OPERATOR" "preARM" [])),
      ("write",
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
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]])))))];
  
  local
  val share_table = Vector.fromList
  [C"?" "bool"
    ((((T"SRS" "preARM" [] --> T"num" "num" []) --> bool) --> bool)),
   V"rep" ((T"SRS" "preARM" [] --> T"num" "num" [])),
   C"TYPE_DEFINITION" "bool"
    (((T"num" "num" [] --> bool) -->
      ((T"SRS" "preARM" [] --> T"num" "num" []) --> bool))),
   V"n" (T"num" "num" []),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"SRS" "preARM" [] --> bool) --> bool)),
   V"a" (T"SRS" "preARM" []),
   C"=" "min" ((T"SRS" "preARM" [] --> (T"SRS" "preARM" [] --> bool))),
   C"num2SRS" "preARM" ((T"num" "num" [] --> T"SRS" "preARM" [])),
   C"SRS2num" "preARM" ((T"SRS" "preARM" [] --> T"num" "num" [])),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"r" (T"num" "num" []), C"=" "min" ((bool --> (bool --> bool))),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"SN" "preARM" (T"SRS" "preARM" []), C"0" "num" (T"num" "num" []),
   C"SZ" "preARM" (T"SRS" "preARM" []),
   C"SC" "preARM" (T"SRS" "preARM" []),
   C"SV" "preARM" (T"SRS" "preARM" []), V"x" (T"SRS" "preARM" []),
   C"SRS_size" "preARM" ((T"SRS" "preARM" [] --> T"num" "num" [])),
   C"!" "bool" (((alpha --> bool) --> bool)), V"v0" (alpha), V"v1" (alpha),
   V"v2" (alpha), V"v3" (alpha), C"=" "min" ((alpha --> (alpha --> bool))),
   C"SRS_case" "preARM"
    ((alpha -->
      (alpha --> (alpha --> (alpha --> (T"SRS" "preARM" [] --> alpha)))))),
   V"m" (T"num" "num" []),
   C"COND" "bool" ((bool --> (alpha --> (alpha --> alpha)))),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"cpsr" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"flag" (T"SRS" "preARM" []),
   C"getS" "preARM"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"SRS" "preARM" [] --> bool))),
   C"SRS_case" "preARM"
    ((bool -->
      (bool --> (bool --> (bool --> (T"SRS" "preARM" [] --> bool)))))),
   C"index" "fcp"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> bool))),
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"setS" "preARM"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"SRS" "preARM" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"SRS_case" "preARM"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       (T"cart" "fcp" [bool, T"i32" "words" []] -->
        (T"cart" "fcp" [bool, T"i32" "words" []] -->
         (T"SRS" "preARM" [] -->
          T"cart" "fcp" [bool, T"i32" "words" []])))))),
   C"word_or" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"n2w" "words"
    ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []])),
   C"!" "bool" (((bool --> bool) --> bool)), V"N" (bool), V"Z" (bool),
   V"C" (bool), V"V" (bool),
   C"setNZCV" "preARM"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"prod" "pair"
        [bool, T"prod" "pair" [bool, T"prod" "pair" [bool, bool]]] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"," "pair"
    ((bool -->
      (T"prod" "pair" [bool, T"prod" "pair" [bool, bool]] -->
       T"prod" "pair"
        [bool, T"prod" "pair" [bool, T"prod" "pair" [bool, bool]]]))),
   C"," "pair"
    ((bool -->
      (T"prod" "pair" [bool, bool] -->
       T"prod" "pair" [bool, T"prod" "pair" [bool, bool]]))),
   C"," "pair" ((bool --> (bool --> T"prod" "pair" [bool, bool]))),
   C"word_modify" "words"
    (((T"num" "num" [] --> (bool --> bool)) -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))), V"i" (T"num" "num" []),
   V"b" (bool), C"\\/" "bool" ((bool --> (bool --> bool))),
   C"?" "bool"
    ((((T"OPERATOR" "preARM" [] --> T"num" "num" []) --> bool) --> bool)),
   V"rep" ((T"OPERATOR" "preARM" [] --> T"num" "num" [])),
   C"TYPE_DEFINITION" "bool"
    (((T"num" "num" [] --> bool) -->
      ((T"OPERATOR" "preARM" [] --> T"num" "num" []) --> bool))),
   C"!" "bool" (((T"OPERATOR" "preARM" [] --> bool) --> bool)),
   V"a" (T"OPERATOR" "preARM" []),
   C"=" "min"
    ((T"OPERATOR" "preARM" [] --> (T"OPERATOR" "preARM" [] --> bool))),
   C"num2OPERATOR" "preARM"
    ((T"num" "num" [] --> T"OPERATOR" "preARM" [])),
   C"OPERATOR2num" "preARM"
    ((T"OPERATOR" "preARM" [] --> T"num" "num" [])),
   C"MOV" "preARM" (T"OPERATOR" "preARM" []),
   C"ADD" "preARM" (T"OPERATOR" "preARM" []),
   C"SUB" "preARM" (T"OPERATOR" "preARM" []),
   C"RSB" "preARM" (T"OPERATOR" "preARM" []),
   C"MUL" "preARM" (T"OPERATOR" "preARM" []),
   C"MLA" "preARM" (T"OPERATOR" "preARM" []),
   C"AND" "preARM" (T"OPERATOR" "preARM" []),
   C"ORR" "preARM" (T"OPERATOR" "preARM" []),
   C"EOR" "preARM" (T"OPERATOR" "preARM" []),
   C"CMP" "preARM" (T"OPERATOR" "preARM" []),
   C"TST" "preARM" (T"OPERATOR" "preARM" []),
   C"LSL" "preARM" (T"OPERATOR" "preARM" []),
   C"LSR" "preARM" (T"OPERATOR" "preARM" []),
   C"ASR" "preARM" (T"OPERATOR" "preARM" []),
   C"ROR" "preARM" (T"OPERATOR" "preARM" []),
   C"LDR" "preARM" (T"OPERATOR" "preARM" []),
   C"STR" "preARM" (T"OPERATOR" "preARM" []),
   C"LDMFD" "preARM" (T"OPERATOR" "preARM" []),
   C"STMFD" "preARM" (T"OPERATOR" "preARM" []),
   C"MRS" "preARM" (T"OPERATOR" "preARM" []),
   C"MSR" "preARM" (T"OPERATOR" "preARM" []),
   C"B" "preARM" (T"OPERATOR" "preARM" []),
   C"BL" "preARM" (T"OPERATOR" "preARM" []),
   V"x" (T"OPERATOR" "preARM" []),
   C"OPERATOR_size" "preARM"
    ((T"OPERATOR" "preARM" [] --> T"num" "num" [])), V"v4" (alpha),
   V"v5" (alpha), V"v6" (alpha), V"v7" (alpha), V"v8" (alpha),
   V"v9" (alpha), V"v10" (alpha), V"v11" (alpha), V"v12" (alpha),
   V"v13" (alpha), V"v14" (alpha), V"v15" (alpha), V"v16" (alpha),
   V"v17" (alpha), V"v18" (alpha), V"v19" (alpha), V"v20" (alpha),
   V"v21" (alpha), V"v22" (alpha),
   C"OPERATOR_case" "preARM"
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
                    (alpha -->
                     (alpha -->
                      (alpha -->
                       (alpha -->
                        (alpha -->
                         (alpha -->
                          (alpha -->
                           (alpha -->
                            (T"OPERATOR" "preARM" [] -->
                             alpha))))))))))))))))))))))))),
   C"?" "bool"
    ((((T"COND" "preARM" [] --> T"num" "num" []) --> bool) --> bool)),
   V"rep" ((T"COND" "preARM" [] --> T"num" "num" [])),
   C"TYPE_DEFINITION" "bool"
    (((T"num" "num" [] --> bool) -->
      ((T"COND" "preARM" [] --> T"num" "num" []) --> bool))),
   C"!" "bool" (((T"COND" "preARM" [] --> bool) --> bool)),
   V"a" (T"COND" "preARM" []),
   C"=" "min" ((T"COND" "preARM" [] --> (T"COND" "preARM" [] --> bool))),
   C"num2COND" "preARM" ((T"num" "num" [] --> T"COND" "preARM" [])),
   C"COND2num" "preARM" ((T"COND" "preARM" [] --> T"num" "num" [])),
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
   C"NV" "preARM" (T"COND" "preARM" []), V"x" (T"COND" "preARM" []),
   C"COND_size" "preARM" ((T"COND" "preARM" [] --> T"num" "num" [])),
   C"COND_case" "preARM"
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
                    (alpha -->
                     (T"COND" "preARM" [] --> alpha)))))))))))))))))),
   C"?" "bool"
    ((((T"OFFSET" "preARM" [] --> T"recspace" "ind_type" [T"num" "num" []])
       --> bool) --> bool)),
   V"rep"
    ((T"OFFSET" "preARM" [] --> T"recspace" "ind_type" [T"num" "num" []])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type" [T"num" "num" []] --> bool) -->
      ((T"OFFSET" "preARM" [] --> T"recspace" "ind_type" [T"num" "num" []])
       --> bool))), V"a0" (T"recspace" "ind_type" [T"num" "num" []]),
   C"!" "bool"
    ((((T"recspace" "ind_type" [T"num" "num" []] --> bool) --> bool) -->
      bool)),
   V"'OFFSET'" ((T"recspace" "ind_type" [T"num" "num" []] --> bool)),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"!" "bool"
    (((T"recspace" "ind_type" [T"num" "num" []] --> bool) --> bool)),
   C"?" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"a" (T"num" "num" []),
   C"=" "min"
    ((T"recspace" "ind_type" [T"num" "num" []] -->
      (T"recspace" "ind_type" [T"num" "num" []] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"num" "num" [] -->
       ((T"num" "num" [] --> T"recspace" "ind_type" [T"num" "num" []]) -->
        T"recspace" "ind_type" [T"num" "num" []])))),
   C"BOTTOM" "ind_type" (T"recspace" "ind_type" [T"num" "num" []]),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"!" "bool" (((T"OFFSET" "preARM" [] --> bool) --> bool)),
   V"a" (T"OFFSET" "preARM" []),
   C"=" "min"
    ((T"OFFSET" "preARM" [] --> (T"OFFSET" "preARM" [] --> bool))),
   C"mk_OFFSET" "preARM"
    ((T"recspace" "ind_type" [T"num" "num" []] --> T"OFFSET" "preARM" [])),
   C"dest_OFFSET" "preARM"
    ((T"OFFSET" "preARM" [] --> T"recspace" "ind_type" [T"num" "num" []])),
   V"r" (T"recspace" "ind_type" [T"num" "num" []]),
   C"=" "min"
    (((T"num" "num" [] --> T"OFFSET" "preARM" []) -->
      ((T"num" "num" [] --> T"OFFSET" "preARM" []) --> bool))),
   C"preARM0" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"preARM1" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"POS" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"NEG" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"!" "bool" ((((T"num" "num" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"num" "num" [] --> alpha)), V"f1" ((T"num" "num" [] --> alpha)),
   C"OFFSET_case" "preARM"
    (((T"num" "num" [] --> alpha) -->
      ((T"num" "num" [] --> alpha) -->
       (T"OFFSET" "preARM" [] --> alpha)))),
   C"OFFSET_size" "preARM" ((T"OFFSET" "preARM" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"?" "bool"
    ((((T"EXP" "preARM" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])
       --> bool) --> bool)),
   V"rep"
    ((T"EXP" "preARM" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
          T"prod" "pair"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool) -->
      ((T"EXP" "preARM" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])
       --> bool))),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"prod" "pair"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool) --> bool) --> bool)),
   V"'EXP'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
          T"prod" "pair"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool) --> bool)),
   C"?" "bool"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> bool)),
   V"a" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
          T"prod" "pair"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
           T"prod" "pair"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"prod" "pair"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
             T"prod" "pair"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])
        -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
            T"prod" "pair"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]]])))),
   C"," "pair"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"prod" "pair"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"prod" "pair"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"prod" "pair"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]))),
   C"@" "min" (((T"num" "num" [] --> bool) --> T"num" "num" [])),
   V"v" (T"num" "num" []), C"T" "bool" (bool),
   C"@" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) -->
      T"cart" "fcp" [bool, T"i32" "words" []])),
   V"v" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"prod" "pair"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"@" "min"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []])),
   V"v" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"a" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"!" "bool" (((T"EXP" "preARM" [] --> bool) --> bool)),
   V"a" (T"EXP" "preARM" []),
   C"=" "min" ((T"EXP" "preARM" [] --> (T"EXP" "preARM" [] --> bool))),
   C"mk_EXP" "preARM"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
          T"prod" "pair"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      T"EXP" "preARM" [])),
   C"dest_EXP" "preARM"
    ((T"EXP" "preARM" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
          T"prod" "pair"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []],
         T"prod" "pair"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"=" "min"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"EXP" "preARM" []) -->
      ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
        T"EXP" "preARM" []) --> bool))),
   C"preARM2" "preARM"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"EXP" "preARM" [])),
   C"=" "min"
    (((T"num" "num" [] --> T"EXP" "preARM" []) -->
      ((T"num" "num" [] --> T"EXP" "preARM" []) --> bool))),
   C"preARM3" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   C"=" "min"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> T"EXP" "preARM" []) -->
      ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"EXP" "preARM" []) -->
       bool))),
   C"preARM4" "preARM"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"EXP" "preARM" [])),
   C"preARM5" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   C"preARM6" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   C"MEM" "preARM"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      T"EXP" "preARM" [])),
   C"NCONST" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   C"WCONST" "preARM"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"EXP" "preARM" [])),
   C"REG" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   C"WREG" "preARM" ((T"num" "num" [] --> T"EXP" "preARM" [])),
   C"!" "bool"
    ((((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha)
       --> bool) --> bool)),
   V"f"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha)),
   C"!" "bool"
    ((((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) --> bool) -->
      bool)), V"f2" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   V"f3" ((T"num" "num" [] --> alpha)),
   V"f4" ((T"num" "num" [] --> alpha)),
   C"!" "bool"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool)
      --> bool)),
   C"EXP_case" "preARM"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha)
      -->
      ((T"num" "num" [] --> alpha) -->
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha) -->
        ((T"num" "num" [] --> alpha) -->
         ((T"num" "num" [] --> alpha) -->
          (T"EXP" "preARM" [] --> alpha))))))),
   C"EXP_size" "preARM" ((T"EXP" "preARM" [] --> T"num" "num" [])),
   C"UNCURRY" "pair"
    (((T"num" "num" [] --> (T"OFFSET" "preARM" [] --> T"num" "num" [])) -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"num" "num" []))), V"x" (T"num" "num" []),
   V"y" (T"OFFSET" "preARM" []), C"FP" "preARM" (T"EXP" "preARM" []),
   C"IP" "preARM" (T"EXP" "preARM" []),
   C"SP" "preARM" (T"EXP" "preARM" []),
   C"LR" "preARM" (T"EXP" "preARM" []),
   C"PC" "preARM" (T"EXP" "preARM" []),
   C"!" "bool"
    (((T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool) --> bool)),
   V"regs"
    (T"fmap" "finite_map"
      [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   V"mem"
    (T"fmap" "finite_map"
      [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   V"exp" (T"EXP" "preARM" []),
   C"read" "preARM"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"EXP" "preARM" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
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
   C"EXP_case" "preARM"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]) -->
      ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"cart" "fcp" [bool, T"i32" "words" []]) -->
        ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
         ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
          (T"EXP" "preARM" [] -->
           T"cart" "fcp" [bool, T"i32" "words" []]))))))),
   C"pair_case" "pair"
    (((T"num" "num" [] -->
       (T"OFFSET" "preARM" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))
      -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))), V"v6" (T"num" "num" []),
   V"v7" (T"OFFSET" "preARM" []),
   C"OFFSET_case" "preARM"
    (((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
      ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]) -->
       (T"OFFSET" "preARM" [] -->
        T"cart" "fcp" [bool, T"i32" "words" []])))),
   V"k" (T"num" "num" []),
   C"FAPPLY" "finite_map"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"w2n" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"num" "num" [])),
   V"k'" (T"num" "num" []),
   C"-" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   V"w" (T"cart" "fcp" [bool, T"i32" "words" []]), V"v4" (T"num" "num" []),
   C"ARB" "bool" (T"cart" "fcp" [bool, T"i32" "words" []]),
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
   C"EXP_case" "preARM"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
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
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
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
         ((T"num" "num" [] -->
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
          -->
          (T"EXP" "preARM" [] -->
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]))))))),
   V"v6" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"pair_case" "pair"
    (((T"num" "num" [] -->
       (T"OFFSET" "preARM" [] -->
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))
      -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   V"offset" (T"OFFSET" "preARM" []),
   C"OFFSET_case" "preARM"
    (((T"num" "num" [] -->
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]) -->
      ((T"num" "num" [] -->
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]) -->
       (T"OFFSET" "preARM" [] -->
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]])))),
   C"FUPDATE" "finite_map"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"prod" "pair"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]))),
   V"v7" (T"num" "num" []),
   V"v8" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"r'" (T"num" "num" []), V"v10" (T"num" "num" []),
   C"=" "min"
    (((T"prod" "pair"
        [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
       T"num" "num" []) -->
      ((T"prod" "pair"
         [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
        T"num" "num" []) --> bool))),
   C"goto" "preARM"
    ((T"prod" "pair"
       [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
      T"num" "num" [])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
       (T"prod" "pair"
         [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
        bool)) -->
      (((T"prod" "pair"
          [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
         T"num" "num" []) -->
        (T"prod" "pair"
          [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
         T"num" "num" [])) -->
       (T"prod" "pair"
         [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
        T"num" "num" [])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
        (T"prod" "pair"
          [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
         bool)) --> bool) -->
      (T"prod" "pair"
        [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
       (T"prod" "pair"
         [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
        bool)))),
   V"R"
    ((T"prod" "pair"
       [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
      (T"prod" "pair"
        [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
       bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
       (T"prod" "pair"
         [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
        bool)) --> bool)),
   V"goto"
    ((T"prod" "pair"
       [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
      T"num" "num" [])),
   V"a"
    (T"prod" "pair"
      [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]]),
   C"pair_case" "pair"
    (((T"num" "num" [] -->
       (T"option" "option" [T"OFFSET" "preARM" []] --> T"num" "num" []))
      -->
      (T"prod" "pair"
        [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
       T"num" "num" []))), V"pc" (T"num" "num" []),
   V"v1" (T"option" "option" [T"OFFSET" "preARM" []]),
   C"option_case" "option"
    ((T"num" "num" [] -->
      ((T"OFFSET" "preARM" [] --> T"num" "num" []) -->
       (T"option" "option" [T"OFFSET" "preARM" []] --> T"num" "num" [])))),
   C"ARB" "bool" (T"num" "num" []), V"jump" (T"OFFSET" "preARM" []),
   C"I" "combin" ((T"num" "num" [] --> T"num" "num" [])),
   C"OFFSET_case" "preARM"
    (((T"num" "num" [] --> T"num" "num" []) -->
      ((T"num" "num" [] --> T"num" "num" []) -->
       (T"OFFSET" "preARM" [] --> T"num" "num" [])))),
   V"n'" (T"num" "num" []),
   C"!" "bool"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool) --> bool)),
   V"s"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"op" (T"OPERATOR" "preARM" []),
   C"!" "bool"
    (((T"option" "option" [T"EXP" "preARM" []] --> bool) --> bool)),
   V"dst" (T"option" "option" [T"EXP" "preARM" []]),
   C"!" "bool" (((T"list" "list" [T"EXP" "preARM" []] --> bool) --> bool)),
   V"src" (T"list" "list" [T"EXP" "preARM" []]), V"jump" (alpha),
   C"=" "min"
    ((T"prod" "pair"
       [T"cart" "fcp" [bool, T"i32" "words" []],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      (T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool))),
   C"decode_op" "preARM"
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
        [T"OPERATOR" "preARM" [],
         T"prod" "pair"
          [T"option" "option" [T"EXP" "preARM" []],
           T"prod" "pair" [T"list" "list" [T"EXP" "preARM" []], alpha]]]
       -->
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
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
   C"," "pair"
    ((T"OPERATOR" "preARM" [] -->
      (T"prod" "pair"
        [T"option" "option" [T"EXP" "preARM" []],
         T"prod" "pair" [T"list" "list" [T"EXP" "preARM" []], alpha]] -->
       T"prod" "pair"
        [T"OPERATOR" "preARM" [],
         T"prod" "pair"
          [T"option" "option" [T"EXP" "preARM" []],
           T"prod" "pair"
            [T"list" "list" [T"EXP" "preARM" []], alpha]]]))),
   C"," "pair"
    ((T"option" "option" [T"EXP" "preARM" []] -->
      (T"prod" "pair" [T"list" "list" [T"EXP" "preARM" []], alpha] -->
       T"prod" "pair"
        [T"option" "option" [T"EXP" "preARM" []],
         T"prod" "pair" [T"list" "list" [T"EXP" "preARM" []], alpha]]))),
   C"," "pair"
    ((T"list" "list" [T"EXP" "preARM" []] -->
      (alpha -->
       T"prod" "pair" [T"list" "list" [T"EXP" "preARM" []], alpha]))),
   C"OPERATOR_case" "preARM"
    ((T"prod" "pair"
       [T"cart" "fcp" [bool, T"i32" "words" []],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      (T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        -->
        (T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         -->
         (T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
          -->
          (T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
           (T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []],
              T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
            (T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []],
               T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
             (T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
              (T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
               (T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
                (T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
                 (T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i32" "words" []],
                    T"prod" "pair"
                     [T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]],
                      T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
                  (T"prod" "pair"
                    [T"cart" "fcp" [bool, T"i32" "words" []],
                     T"prod" "pair"
                      [T"fmap" "finite_map"
                        [T"num" "num" [],
                         T"cart" "fcp" [bool, T"i32" "words" []]],
                       T"fmap" "finite_map"
                        [T"num" "num" [],
                         T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
                   (T"prod" "pair"
                     [T"cart" "fcp" [bool, T"i32" "words" []],
                      T"prod" "pair"
                       [T"fmap" "finite_map"
                         [T"num" "num" [],
                          T"cart" "fcp" [bool, T"i32" "words" []]],
                        T"fmap" "finite_map"
                         [T"num" "num" [],
                          T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
                    (T"prod" "pair"
                      [T"cart" "fcp" [bool, T"i32" "words" []],
                       T"prod" "pair"
                        [T"fmap" "finite_map"
                          [T"num" "num" [],
                           T"cart" "fcp" [bool, T"i32" "words" []]],
                         T"fmap" "finite_map"
                          [T"num" "num" [],
                           T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
                     (T"prod" "pair"
                       [T"cart" "fcp" [bool, T"i32" "words" []],
                        T"prod" "pair"
                         [T"fmap" "finite_map"
                           [T"num" "num" [],
                            T"cart" "fcp" [bool, T"i32" "words" []]],
                          T"fmap" "finite_map"
                           [T"num" "num" [],
                            T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
                      (T"prod" "pair"
                        [T"cart" "fcp" [bool, T"i32" "words" []],
                         T"prod" "pair"
                          [T"fmap" "finite_map"
                            [T"num" "num" [],
                             T"cart" "fcp" [bool, T"i32" "words" []]],
                           T"fmap" "finite_map"
                            [T"num" "num" [],
                             T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
                       (T"prod" "pair"
                         [T"cart" "fcp" [bool, T"i32" "words" []],
                          T"prod" "pair"
                           [T"fmap" "finite_map"
                             [T"num" "num" [],
                              T"cart" "fcp" [bool, T"i32" "words" []]],
                            T"fmap" "finite_map"
                             [T"num" "num" [],
                              T"cart" "fcp" [bool, T"i32" "words" []]]]]
                        -->
                        (T"prod" "pair"
                          [T"cart" "fcp" [bool, T"i32" "words" []],
                           T"prod" "pair"
                            [T"fmap" "finite_map"
                              [T"num" "num" [],
                               T"cart" "fcp" [bool, T"i32" "words" []]],
                             T"fmap" "finite_map"
                              [T"num" "num" [],
                               T"cart" "fcp" [bool, T"i32" "words" []]]]]
                         -->
                         (T"prod" "pair"
                           [T"cart" "fcp" [bool, T"i32" "words" []],
                            T"prod" "pair"
                             [T"fmap" "finite_map"
                               [T"num" "num" [],
                                T"cart" "fcp" [bool, T"i32" "words" []]],
                              T"fmap" "finite_map"
                               [T"num" "num" [],
                                T"cart" "fcp" [bool, T"i32" "words" []]]]]
                          -->
                          (T"prod" "pair"
                            [T"cart" "fcp" [bool, T"i32" "words" []],
                             T"prod" "pair"
                              [T"fmap" "finite_map"
                                [T"num" "num" [],
                                 T"cart" "fcp" [bool, T"i32" "words" []]],
                               T"fmap" "finite_map"
                                [T"num" "num" [],
                                 T"cart" "fcp" [bool, T"i32" "words" []]]]]
                           -->
                           (T"prod" "pair"
                             [T"cart" "fcp" [bool, T"i32" "words" []],
                              T"prod" "pair"
                               [T"fmap" "finite_map"
                                 [T"num" "num" [],
                                  T"cart" "fcp" [bool, T"i32" "words" []]],
                                T"fmap" "finite_map"
                                 [T"num" "num" [],
                                  T"cart" "fcp"
                                   [bool, T"i32" "words" []]]]] -->
                            (T"OPERATOR" "preARM" [] -->
                             T"prod" "pair"
                              [T"cart" "fcp" [bool, T"i32" "words" []],
                               T"prod" "pair"
                                [T"fmap" "finite_map"
                                  [T"num" "num" [],
                                   T"cart" "fcp"
                                    [bool, T"i32" "words" []]],
                                 T"fmap" "finite_map"
                                  [T"num" "num" [],
                                   T"cart" "fcp"
                                    [bool,
                                     T"i32" "words"
                                      []]]]]))))))))))))))))))))))))),
   C"THE" "option"
    ((T"option" "option" [T"EXP" "preARM" []] --> T"EXP" "preARM" [])),
   C"HD" "list"
    ((T"list" "list" [T"EXP" "preARM" []] --> T"EXP" "preARM" [])),
   C"word_add" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"TL" "list"
    ((T"list" "list" [T"EXP" "preARM" []] -->
      T"list" "list" [T"EXP" "preARM" []])),
   C"word_sub" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_mul" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_and" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_xor" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"LET" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])
      -->
      (T"cart" "fcp" [bool, T"i32" "words" []] -->
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
   V"b" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"word_msb" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] --> bool)),
   C"word_ls" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"~" "bool" ((bool --> bool)), C"F" "bool" (bool),
   C"word_lsl" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_lsr" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_asr" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"word_ror" "words"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
   C"EXP_case" "preARM"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])
      -->
      ((T"num" "num" [] -->
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])
       -->
       ((T"cart" "fcp" [bool, T"i32" "words" []] -->
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]])
        -->
        ((T"num" "num" [] -->
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]) -->
         ((T"num" "num" [] -->
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]) -->
          (T"EXP" "preARM" [] -->
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]))))))),
   C"ARB" "bool"
    (T"prod" "pair"
      [T"cart" "fcp" [bool, T"i32" "words" []],
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   V"v2" (T"num" "num" []),
   V"v4" (T"cart" "fcp" [bool, T"i32" "words" []]),
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
   V"s1"
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
   C"," "pair"
    ((T"num" "num" [] -->
      (T"OFFSET" "preARM" [] -->
       T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]))),
   C"LENGTH" "list"
    ((T"list" "list" [T"EXP" "preARM" []] --> T"num" "num" [])),
   C"REVERSE" "list"
    ((T"list" "list" [T"EXP" "preARM" []] -->
      T"list" "list" [T"EXP" "preARM" []])),
   C"decode_cond_cpsr" "preARM"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"COND" "preARM" [] --> bool))),
   C"!" "bool"
    (((T"option" "option" [T"COND" "preARM" []] --> bool) --> bool)),
   V"cond" (T"option" "option" [T"COND" "preARM" []]), V"sflag" (bool),
   C"!" "bool"
    (((T"option" "option" [T"OFFSET" "preARM" []] --> bool) --> bool)),
   V"jump" (T"option" "option" [T"OFFSET" "preARM" []]),
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
   C"," "pair"
    ((T"option" "option" [T"COND" "preARM" []] -->
      (bool -->
       T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]))),
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
   C"," "pair"
    ((T"list" "list" [T"EXP" "preARM" []] -->
      (T"option" "option" [T"OFFSET" "preARM" []] -->
       T"prod" "pair"
        [T"list" "list" [T"EXP" "preARM" []],
         T"option" "option" [T"OFFSET" "preARM" []]]))),
   C"option_case" "option"
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
      ((T"COND" "preARM" [] -->
        T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]]) -->
       (T"option" "option" [T"COND" "preARM" []] -->
        T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]])))),
   C"decode_op" "preARM"
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
        [T"OPERATOR" "preARM" [],
         T"prod" "pair"
          [T"option" "option" [T"EXP" "preARM" []],
           T"prod" "pair"
            [T"list" "list" [T"EXP" "preARM" []],
             T"option" "option" [T"OFFSET" "preARM" []]]]] -->
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
   C"," "pair"
    ((T"OPERATOR" "preARM" [] -->
      (T"prod" "pair"
        [T"option" "option" [T"EXP" "preARM" []],
         T"prod" "pair"
          [T"list" "list" [T"EXP" "preARM" []],
           T"option" "option" [T"OFFSET" "preARM" []]]] -->
       T"prod" "pair"
        [T"OPERATOR" "preARM" [],
         T"prod" "pair"
          [T"option" "option" [T"EXP" "preARM" []],
           T"prod" "pair"
            [T"list" "list" [T"EXP" "preARM" []],
             T"option" "option" [T"OFFSET" "preARM" []]]]]))),
   V"c" (T"COND" "preARM" []),
   C"COND" "bool"
    ((bool -->
      (T"prod" "pair"
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
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
        T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]])))),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"option" "option" [T"OFFSET" "preARM" []] -->
       T"prod" "pair"
        [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]]))),
   V"stm" (alpha),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"stmL" (T"list" "list" [alpha]), V"iB" ((T"num" "num" [] --> alpha)),
   V"start" (T"num" "num" []),
   C"=" "min"
    (((T"num" "num" [] --> alpha) -->
      ((T"num" "num" [] --> alpha) --> bool))),
   C"upload" "preARM"
    ((T"list" "list" [alpha] -->
      ((T"num" "num" [] --> alpha) -->
       (T"num" "num" [] --> (T"num" "num" [] --> alpha))))),
   C"CONS" "list"
    ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   V"addr" (T"num" "num" []), C"NIL" "list" (T"list" "list" [alpha]),
   V"instL" (T"list" "list" [alpha]),
   C"uploadCode" "preARM"
    ((T"list" "list" [alpha] -->
      ((T"num" "num" [] --> alpha) --> (T"num" "num" [] --> alpha)))),
   C"!" "bool"
    (((T"list" "list" [T"list" "list" [alpha]] --> bool) --> bool)),
   V"segs" (T"list" "list" [T"list" "list" [alpha]]),
   C"uploadSeg" "preARM"
    ((T"num" "num" [] -->
      (T"list" "list" [T"list" "list" [alpha]] -->
       ((T"num" "num" [] --> alpha) --> (T"num" "num" [] --> alpha))))),
   C"EL" "list"
    ((T"num" "num" [] -->
      (T"list" "list" [T"list" "list" [alpha]] -->
       T"list" "list" [alpha]))),
   C"*" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"=" "min"
    (((T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [(T"num" "num" [] -->
            T"prod" "pair"
             [T"prod" "pair"
               [T"OPERATOR" "preARM" [],
                T"prod" "pair"
                 [T"option" "option" [T"COND" "preARM" []], bool]],
              T"prod" "pair"
               [T"option" "option" [T"EXP" "preARM" []],
                T"prod" "pair"
                 [T"list" "list" [T"EXP" "preARM" []],
                  T"option" "option" [T"OFFSET" "preARM" []]]]]),
           T"prod" "pair"
            [(T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
              bool),
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
       T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]]]) -->
      ((T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [(T"num" "num" [] -->
             T"prod" "pair"
              [T"prod" "pair"
                [T"OPERATOR" "preARM" [],
                 T"prod" "pair"
                  [T"option" "option" [T"COND" "preARM" []], bool]],
               T"prod" "pair"
                [T"option" "option" [T"EXP" "preARM" []],
                 T"prod" "pair"
                  [T"list" "list" [T"EXP" "preARM" []],
                   T"option" "option" [T"OFFSET" "preARM" []]]]]),
            T"prod" "pair"
             [(T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
               bool),
              T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
        T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]]) --> bool))),
   C"run_tupled" "preARM"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [(T"num" "num" [] -->
           T"prod" "pair"
            [T"prod" "pair"
              [T"OPERATOR" "preARM" [],
               T"prod" "pair"
                [T"option" "option" [T"COND" "preARM" []], bool]],
             T"prod" "pair"
              [T"option" "option" [T"EXP" "preARM" []],
               T"prod" "pair"
                [T"list" "list" [T"EXP" "preARM" []],
                 T"option" "option" [T"OFFSET" "preARM" []]]]]),
          T"prod" "pair"
           [(T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
            T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
      T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]]]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [(T"num" "num" [] -->
            T"prod" "pair"
             [T"prod" "pair"
               [T"OPERATOR" "preARM" [],
                T"prod" "pair"
                 [T"option" "option" [T"COND" "preARM" []], bool]],
              T"prod" "pair"
               [T"option" "option" [T"EXP" "preARM" []],
                T"prod" "pair"
                 [T"list" "list" [T"EXP" "preARM" []],
                  T"option" "option" [T"OFFSET" "preARM" []]]]]),
           T"prod" "pair"
            [(T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
              bool),
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
       (T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [(T"num" "num" [] -->
             T"prod" "pair"
              [T"prod" "pair"
                [T"OPERATOR" "preARM" [],
                 T"prod" "pair"
                  [T"option" "option" [T"COND" "preARM" []], bool]],
               T"prod" "pair"
                [T"option" "option" [T"EXP" "preARM" []],
                 T"prod" "pair"
                  [T"list" "list" [T"EXP" "preARM" []],
                   T"option" "option" [T"OFFSET" "preARM" []]]]]),
            T"prod" "pair"
             [(T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
               bool),
              T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
        bool)) -->
      (((T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [(T"num" "num" [] -->
              T"prod" "pair"
               [T"prod" "pair"
                 [T"OPERATOR" "preARM" [],
                  T"prod" "pair"
                   [T"option" "option" [T"COND" "preARM" []], bool]],
                T"prod" "pair"
                 [T"option" "option" [T"EXP" "preARM" []],
                  T"prod" "pair"
                   [T"list" "list" [T"EXP" "preARM" []],
                    T"option" "option" [T"OFFSET" "preARM" []]]]]),
             T"prod" "pair"
              [(T"prod" "pair"
                 [T"num" "num" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i32" "words" []],
                    T"prod" "pair"
                     [T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]],
                      T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
                bool),
               T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]]) -->
        (T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [(T"num" "num" [] -->
              T"prod" "pair"
               [T"prod" "pair"
                 [T"OPERATOR" "preARM" [],
                  T"prod" "pair"
                   [T"option" "option" [T"COND" "preARM" []], bool]],
                T"prod" "pair"
                 [T"option" "option" [T"EXP" "preARM" []],
                  T"prod" "pair"
                   [T"list" "list" [T"EXP" "preARM" []],
                    T"option" "option" [T"OFFSET" "preARM" []]]]]),
             T"prod" "pair"
              [(T"prod" "pair"
                 [T"num" "num" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i32" "words" []],
                    T"prod" "pair"
                     [T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]],
                      T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
                bool),
               T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]])) -->
       (T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [(T"num" "num" [] -->
             T"prod" "pair"
              [T"prod" "pair"
                [T"OPERATOR" "preARM" [],
                 T"prod" "pair"
                  [T"option" "option" [T"COND" "preARM" []], bool]],
               T"prod" "pair"
                [T"option" "option" [T"EXP" "preARM" []],
                 T"prod" "pair"
                  [T"list" "list" [T"EXP" "preARM" []],
                   T"option" "option" [T"OFFSET" "preARM" []]]]]),
            T"prod" "pair"
             [(T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
               bool),
              T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
        T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [(T"num" "num" [] -->
             T"prod" "pair"
              [T"prod" "pair"
                [T"OPERATOR" "preARM" [],
                 T"prod" "pair"
                  [T"option" "option" [T"COND" "preARM" []], bool]],
               T"prod" "pair"
                [T"option" "option" [T"EXP" "preARM" []],
                 T"prod" "pair"
                  [T"list" "list" [T"EXP" "preARM" []],
                   T"option" "option" [T"OFFSET" "preARM" []]]]]),
            T"prod" "pair"
             [(T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
               bool),
              T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
        (T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [(T"num" "num" [] -->
              T"prod" "pair"
               [T"prod" "pair"
                 [T"OPERATOR" "preARM" [],
                  T"prod" "pair"
                   [T"option" "option" [T"COND" "preARM" []], bool]],
                T"prod" "pair"
                 [T"option" "option" [T"EXP" "preARM" []],
                  T"prod" "pair"
                   [T"list" "list" [T"EXP" "preARM" []],
                    T"option" "option" [T"OFFSET" "preARM" []]]]]),
             T"prod" "pair"
              [(T"prod" "pair"
                 [T"num" "num" [],
                  T"prod" "pair"
                   [T"cart" "fcp" [bool, T"i32" "words" []],
                    T"prod" "pair"
                     [T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]],
                      T"fmap" "finite_map"
                       [T"num" "num" [],
                        T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
                bool),
               T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
         bool)) --> bool) -->
      (T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [(T"num" "num" [] -->
            T"prod" "pair"
             [T"prod" "pair"
               [T"OPERATOR" "preARM" [],
                T"prod" "pair"
                 [T"option" "option" [T"COND" "preARM" []], bool]],
              T"prod" "pair"
               [T"option" "option" [T"EXP" "preARM" []],
                T"prod" "pair"
                 [T"list" "list" [T"EXP" "preARM" []],
                  T"option" "option" [T"OFFSET" "preARM" []]]]]),
           T"prod" "pair"
            [(T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
              bool),
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
       (T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [(T"num" "num" [] -->
             T"prod" "pair"
              [T"prod" "pair"
                [T"OPERATOR" "preARM" [],
                 T"prod" "pair"
                  [T"option" "option" [T"COND" "preARM" []], bool]],
               T"prod" "pair"
                [T"option" "option" [T"EXP" "preARM" []],
                 T"prod" "pair"
                  [T"list" "list" [T"EXP" "preARM" []],
                   T"option" "option" [T"OFFSET" "preARM" []]]]]),
            T"prod" "pair"
             [(T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
               bool),
              T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
        bool)))),
   V"R"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [(T"num" "num" [] -->
           T"prod" "pair"
            [T"prod" "pair"
              [T"OPERATOR" "preARM" [],
               T"prod" "pair"
                [T"option" "option" [T"COND" "preARM" []], bool]],
             T"prod" "pair"
              [T"option" "option" [T"EXP" "preARM" []],
               T"prod" "pair"
                [T"list" "list" [T"EXP" "preARM" []],
                 T"option" "option" [T"OFFSET" "preARM" []]]]]),
          T"prod" "pair"
           [(T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
            T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
      (T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [(T"num" "num" [] -->
            T"prod" "pair"
             [T"prod" "pair"
               [T"OPERATOR" "preARM" [],
                T"prod" "pair"
                 [T"option" "option" [T"COND" "preARM" []], bool]],
              T"prod" "pair"
               [T"option" "option" [T"EXP" "preARM" []],
                T"prod" "pair"
                 [T"list" "list" [T"EXP" "preARM" []],
                  T"option" "option" [T"OFFSET" "preARM" []]]]]),
           T"prod" "pair"
            [(T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
              bool),
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
       bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [(T"num" "num" [] -->
            T"prod" "pair"
             [T"prod" "pair"
               [T"OPERATOR" "preARM" [],
                T"prod" "pair"
                 [T"option" "option" [T"COND" "preARM" []], bool]],
              T"prod" "pair"
               [T"option" "option" [T"EXP" "preARM" []],
                T"prod" "pair"
                 [T"list" "list" [T"EXP" "preARM" []],
                  T"option" "option" [T"OFFSET" "preARM" []]]]]),
           T"prod" "pair"
            [(T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
              bool),
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
       (T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [(T"num" "num" [] -->
             T"prod" "pair"
              [T"prod" "pair"
                [T"OPERATOR" "preARM" [],
                 T"prod" "pair"
                  [T"option" "option" [T"COND" "preARM" []], bool]],
               T"prod" "pair"
                [T"option" "option" [T"EXP" "preARM" []],
                 T"prod" "pair"
                  [T"list" "list" [T"EXP" "preARM" []],
                   T"option" "option" [T"OFFSET" "preARM" []]]]]),
            T"prod" "pair"
             [(T"prod" "pair"
                [T"num" "num" [],
                 T"prod" "pair"
                  [T"cart" "fcp" [bool, T"i32" "words" []],
                   T"prod" "pair"
                    [T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]],
                     T"fmap" "finite_map"
                      [T"num" "num" [],
                       T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
               bool),
              T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
        bool)) --> bool)),
   C"!" "bool"
    ((((T"num" "num" [] -->
        T"prod" "pair"
         [T"prod" "pair"
           [T"OPERATOR" "preARM" [],
            T"prod" "pair"
             [T"option" "option" [T"COND" "preARM" []], bool]],
          T"prod" "pair"
           [T"option" "option" [T"EXP" "preARM" []],
            T"prod" "pair"
             [T"list" "list" [T"EXP" "preARM" []],
              T"option" "option" [T"OFFSET" "preARM" []]]]]) --> bool) -->
      bool)),
   V"instB"
    ((T"num" "num" [] -->
      T"prod" "pair"
       [T"prod" "pair"
         [T"OPERATOR" "preARM" [],
          T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]],
        T"prod" "pair"
         [T"option" "option" [T"EXP" "preARM" []],
          T"prod" "pair"
           [T"list" "list" [T"EXP" "preARM" []],
            T"option" "option" [T"OFFSET" "preARM" []]]]])),
   V"st"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool) -->
       bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
      --> bool)),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [(T"num" "num" [] -->
          T"prod" "pair"
           [T"prod" "pair"
             [T"OPERATOR" "preARM" [],
              T"prod" "pair"
               [T"option" "option" [T"COND" "preARM" []], bool]],
            T"prod" "pair"
             [T"option" "option" [T"EXP" "preARM" []],
              T"prod" "pair"
               [T"list" "list" [T"EXP" "preARM" []],
                T"option" "option" [T"OFFSET" "preARM" []]]]]),
         T"prod" "pair"
          [(T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
           T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []],
               T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]]]]]] -->
       T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [(T"num" "num" [] -->
            T"prod" "pair"
             [T"prod" "pair"
               [T"OPERATOR" "preARM" [],
                T"prod" "pair"
                 [T"option" "option" [T"COND" "preARM" []], bool]],
              T"prod" "pair"
               [T"option" "option" [T"EXP" "preARM" []],
                T"prod" "pair"
                 [T"list" "list" [T"EXP" "preARM" []],
                  T"option" "option" [T"OFFSET" "preARM" []]]]]),
           T"prod" "pair"
            [(T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
              bool),
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]]))),
   C"," "pair"
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
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []],
              T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]]] -->
       T"prod" "pair"
        [(T"num" "num" [] -->
          T"prod" "pair"
           [T"prod" "pair"
             [T"OPERATOR" "preARM" [],
              T"prod" "pair"
               [T"option" "option" [T"COND" "preARM" []], bool]],
            T"prod" "pair"
             [T"option" "option" [T"EXP" "preARM" []],
              T"prod" "pair"
               [T"list" "list" [T"EXP" "preARM" []],
                T"option" "option" [T"OFFSET" "preARM" []]]]]),
         T"prod" "pair"
          [(T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
           T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []],
               T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]))),
   C"," "pair"
    (((T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
       --> bool) -->
      (T"prod" "pair"
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
        [(T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []],
              T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]]]))),
   V"run_tupled"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [(T"num" "num" [] -->
           T"prod" "pair"
            [T"prod" "pair"
              [T"OPERATOR" "preARM" [],
               T"prod" "pair"
                [T"option" "option" [T"COND" "preARM" []], bool]],
             T"prod" "pair"
              [T"option" "option" [T"EXP" "preARM" []],
               T"prod" "pair"
                [T"list" "list" [T"EXP" "preARM" []],
                 T"option" "option" [T"OFFSET" "preARM" []]]]]),
          T"prod" "pair"
           [(T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
            T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
      T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]]]])),
   V"a"
    (T"prod" "pair"
      [T"num" "num" [],
       T"prod" "pair"
        [(T"num" "num" [] -->
          T"prod" "pair"
           [T"prod" "pair"
             [T"OPERATOR" "preARM" [],
              T"prod" "pair"
               [T"option" "option" [T"COND" "preARM" []], bool]],
            T"prod" "pair"
             [T"option" "option" [T"EXP" "preARM" []],
              T"prod" "pair"
               [T"list" "list" [T"EXP" "preARM" []],
                T"option" "option" [T"OFFSET" "preARM" []]]]]),
         T"prod" "pair"
          [(T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
           T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []],
               T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]]),
   C"pair_case" "pair"
    (((T"num" "num" [] -->
       (T"prod" "pair"
         [(T"num" "num" [] -->
           T"prod" "pair"
            [T"prod" "pair"
              [T"OPERATOR" "preARM" [],
               T"prod" "pair"
                [T"option" "option" [T"COND" "preARM" []], bool]],
             T"prod" "pair"
              [T"option" "option" [T"EXP" "preARM" []],
               T"prod" "pair"
                [T"list" "list" [T"EXP" "preARM" []],
                 T"option" "option" [T"OFFSET" "preARM" []]]]]),
          T"prod" "pair"
           [(T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
            T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]]]] -->
        T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]])) -->
      (T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [(T"num" "num" [] -->
            T"prod" "pair"
             [T"prod" "pair"
               [T"OPERATOR" "preARM" [],
                T"prod" "pair"
                 [T"option" "option" [T"COND" "preARM" []], bool]],
              T"prod" "pair"
               [T"option" "option" [T"EXP" "preARM" []],
                T"prod" "pair"
                 [T"list" "list" [T"EXP" "preARM" []],
                  T"option" "option" [T"OFFSET" "preARM" []]]]]),
           T"prod" "pair"
            [(T"prod" "pair"
               [T"num" "num" [],
                T"prod" "pair"
                 [T"cart" "fcp" [bool, T"i32" "words" []],
                  T"prod" "pair"
                   [T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]],
                    T"fmap" "finite_map"
                     [T"num" "num" [],
                      T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
              bool),
             T"prod" "pair"
              [T"num" "num" [],
               T"prod" "pair"
                [T"cart" "fcp" [bool, T"i32" "words" []],
                 T"prod" "pair"
                  [T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]],
                   T"fmap" "finite_map"
                    [T"num" "num" [],
                     T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]] -->
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
   V"v1"
    (T"prod" "pair"
      [(T"num" "num" [] -->
        T"prod" "pair"
         [T"prod" "pair"
           [T"OPERATOR" "preARM" [],
            T"prod" "pair"
             [T"option" "option" [T"COND" "preARM" []], bool]],
          T"prod" "pair"
           [T"option" "option" [T"EXP" "preARM" []],
            T"prod" "pair"
             [T"list" "list" [T"EXP" "preARM" []],
              T"option" "option" [T"OFFSET" "preARM" []]]]]),
       T"prod" "pair"
        [(T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []],
              T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]]]]),
   C"pair_case" "pair"
    ((((T"num" "num" [] -->
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
       (T"prod" "pair"
         [(T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []],
               T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
          T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []],
              T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]]]] -->
        T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]])) -->
      (T"prod" "pair"
        [(T"num" "num" [] -->
          T"prod" "pair"
           [T"prod" "pair"
             [T"OPERATOR" "preARM" [],
              T"prod" "pair"
               [T"option" "option" [T"COND" "preARM" []], bool]],
            T"prod" "pair"
             [T"option" "option" [T"EXP" "preARM" []],
              T"prod" "pair"
               [T"list" "list" [T"EXP" "preARM" []],
                T"option" "option" [T"OFFSET" "preARM" []]]]]),
         T"prod" "pair"
          [(T"prod" "pair"
             [T"num" "num" [],
              T"prod" "pair"
               [T"cart" "fcp" [bool, T"i32" "words" []],
                T"prod" "pair"
                 [T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]],
                  T"fmap" "finite_map"
                   [T"num" "num" [],
                    T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
           T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []],
               T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]]]]]] -->
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
   V"v3"
    (T"prod" "pair"
      [(T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
       T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]]]]),
   C"pair_case" "pair"
    ((((T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool) -->
       (T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
        T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]])) -->
      (T"prod" "pair"
        [(T"prod" "pair"
           [T"num" "num" [],
            T"prod" "pair"
             [T"cart" "fcp" [bool, T"i32" "words" []],
              T"prod" "pair"
               [T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool),
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]]] -->
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
   V"v5"
    (T"prod" "pair"
      [T"num" "num" [],
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]),
   C"pair_case" "pair"
    (((T"num" "num" [] -->
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
                T"cart" "fcp" [bool, T"i32" "words" []]]]]])) -->
      (T"prod" "pair"
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
        [T"num" "num" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [],
               T"cart" "fcp" [bool, T"i32" "words" []]]]]]))),
   V"v7"
    (T"prod" "pair"
      [T"cart" "fcp" [bool, T"i32" "words" []],
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"pair_case" "pair"
    (((T"cart" "fcp" [bool, T"i32" "words" []] -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        T"prod" "pair"
         [T"num" "num" [],
          T"prod" "pair"
           [T"cart" "fcp" [bool, T"i32" "words" []],
            T"prod" "pair"
             [T"fmap" "finite_map"
               [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
              T"fmap" "finite_map"
               [T"num" "num" [],
                T"cart" "fcp" [bool, T"i32" "words" []]]]]])) -->
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
   C"I" "combin"
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
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]]]])),
   V"x1"
    ((T"num" "num" [] -->
      T"prod" "pair"
       [T"prod" "pair"
         [T"OPERATOR" "preARM" [],
          T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]],
        T"prod" "pair"
         [T"option" "option" [T"EXP" "preARM" []],
          T"prod" "pair"
           [T"list" "list" [T"EXP" "preARM" []],
            T"option" "option" [T"OFFSET" "preARM" []]]]])),
   V"x2"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
      --> bool)),
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
   V"x3"
    (T"prod" "pair"
      [T"num" "num" [],
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]),
   C"run" "preARM"
    ((T"num" "num" [] -->
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
       ((T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool) -->
        (T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]] -->
         T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]]))))),
   C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"P" ((alpha --> bool)),
   C"!" "bool" ((((alpha --> alpha) --> bool) --> bool)),
   V"g" ((alpha --> alpha)), V"x" (alpha),
   C"stopAt" "preARM"
    (((alpha --> bool) --> ((alpha --> alpha) --> (alpha --> bool)))),
   C"FUNPOW" "arithmetic"
    (((alpha --> alpha) --> (T"num" "num" [] --> (alpha --> alpha)))),
   C"shortest" "preARM"
    (((alpha --> bool) -->
      ((alpha --> alpha) --> (alpha --> T"num" "num" [])))),
   C"LEAST" "while" (((T"num" "num" [] --> bool) --> T"num" "num" [])),
   C"=" "min"
    (((T"prod" "pair"
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
         (T"num" "num" [] --> bool)]) -->
      ((T"prod" "pair"
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
          (T"num" "num" [] --> bool)]) --> bool))),
   C"step" "preARM"
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
   C"UNCURRY" "pair"
    (((T"prod" "pair"
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
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]],
                T"fmap" "finite_map"
                 [T"num" "num" [],
                  T"cart" "fcp" [bool, T"i32" "words" []]]]]],
          (T"num" "num" [] --> bool)])) -->
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
   V"pcS" ((T"num" "num" [] --> bool)),
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
   C"INSERT" "pred_set"
    ((T"num" "num" [] -->
      ((T"num" "num" [] --> bool) --> (T"num" "num" [] --> bool)))),
   V"j" (T"num" "num" []),
   C"!" "bool" ((((T"num" "num" [] --> bool) --> bool) --> bool)),
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
   C"WHILE" "while"
    (((T"prod" "pair"
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
         (T"num" "num" [] --> bool)] --> bool) -->
      ((T"prod" "pair"
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
          (T"num" "num" [] --> bool)]) -->
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
   C"UNCURRY" "pair"
    (((T"prod" "pair"
        [T"num" "num" [],
         T"prod" "pair"
          [T"cart" "fcp" [bool, T"i32" "words" []],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
       --> ((T"num" "num" [] --> bool) --> bool)) -->
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
   C"!" "bool"
    (((T"prod" "pair"
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
         (T"num" "num" [] --> bool)] --> bool) --> bool)),
   V"s"
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
       (T"num" "num" [] --> bool)]),
   C"terd" "preARM"
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
          (T"num" "num" [] --> bool)] --> bool)))),
   C"stopAt" "preARM"
    (((T"prod" "pair"
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
         (T"num" "num" [] --> bool)] --> bool) -->
      ((T"prod" "pair"
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
          (T"num" "num" [] --> bool)]) -->
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
          (T"num" "num" [] --> bool)] --> bool)))),
   C"FST" "pair"
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
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [],
              T"cart" "fcp" [bool, T"i32" "words" []]]]]])),
   C"!" "bool"
    (((T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool) --> bool)),
   V"regs" (T"fmap" "finite_map" [T"num" "num" [], alpha]),
   C"in_regs_dom" "preARM"
    ((T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool)),
   C"IN" "bool"
    ((T"num" "num" [] --> ((T"num" "num" [] --> bool) --> bool))),
   C"FDOM" "finite_map"
    ((T"fmap" "finite_map" [T"num" "num" [], alpha] -->
      (T"num" "num" [] --> bool))),
   V"mem" (T"fmap" "finite_map" [T"num" "num" [], alpha]),
   C"in_mem_dom" "preARM"
    ((T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool)),
   V"a'" (T"SRS" "preARM" []),
   C"?" "bool" (((T"SRS" "preARM" [] --> bool) --> bool)),
   C"DATATYPE" "bool" ((bool --> bool)),
   V"SRS"
    ((T"SRS" "preARM" [] -->
      (T"SRS" "preARM" [] -->
       (T"SRS" "preARM" [] --> (T"SRS" "preARM" [] --> bool))))),
   V"M" (T"SRS" "preARM" []), V"M'" (T"SRS" "preARM" []), V"v0'" (alpha),
   V"v1'" (alpha), V"v2'" (alpha), V"v3'" (alpha), V"x0" (alpha),
   V"x1" (alpha), V"x2" (alpha), V"x3" (alpha),
   C"?" "bool" ((((T"SRS" "preARM" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"SRS" "preARM" [] --> alpha)),
   C"!" "bool" ((((T"SRS" "preARM" [] --> bool) --> bool) --> bool)),
   V"P" ((T"SRS" "preARM" [] --> bool)), V"a'" (T"OPERATOR" "preARM" []),
   C"?" "bool" (((T"OPERATOR" "preARM" [] --> bool) --> bool)),
   V"OPERATOR"
    ((T"OPERATOR" "preARM" [] -->
      (T"OPERATOR" "preARM" [] -->
       (T"OPERATOR" "preARM" [] -->
        (T"OPERATOR" "preARM" [] -->
         (T"OPERATOR" "preARM" [] -->
          (T"OPERATOR" "preARM" [] -->
           (T"OPERATOR" "preARM" [] -->
            (T"OPERATOR" "preARM" [] -->
             (T"OPERATOR" "preARM" [] -->
              (T"OPERATOR" "preARM" [] -->
               (T"OPERATOR" "preARM" [] -->
                (T"OPERATOR" "preARM" [] -->
                 (T"OPERATOR" "preARM" [] -->
                  (T"OPERATOR" "preARM" [] -->
                   (T"OPERATOR" "preARM" [] -->
                    (T"OPERATOR" "preARM" [] -->
                     (T"OPERATOR" "preARM" [] -->
                      (T"OPERATOR" "preARM" [] -->
                       (T"OPERATOR" "preARM" [] -->
                        (T"OPERATOR" "preARM" [] -->
                         (T"OPERATOR" "preARM" [] -->
                          (T"OPERATOR" "preARM" [] -->
                           (T"OPERATOR" "preARM" [] -->
                            bool)))))))))))))))))))))))),
   V"M" (T"OPERATOR" "preARM" []), V"M'" (T"OPERATOR" "preARM" []),
   V"v4'" (alpha), V"v5'" (alpha), V"v6'" (alpha), V"v7'" (alpha),
   V"v8'" (alpha), V"v9'" (alpha), V"v10'" (alpha), V"v11'" (alpha),
   V"v12'" (alpha), V"v13'" (alpha), V"v14'" (alpha), V"v15'" (alpha),
   V"v16'" (alpha), V"v17'" (alpha), V"v18'" (alpha), V"v19'" (alpha),
   V"v20'" (alpha), V"v21'" (alpha), V"v22'" (alpha), V"x4" (alpha),
   V"x5" (alpha), V"x6" (alpha), V"x7" (alpha), V"x8" (alpha),
   V"x9" (alpha), V"x10" (alpha), V"x11" (alpha), V"x12" (alpha),
   V"x13" (alpha), V"x14" (alpha), V"x15" (alpha), V"x16" (alpha),
   V"x17" (alpha), V"x18" (alpha), V"x19" (alpha), V"x20" (alpha),
   V"x21" (alpha), V"x22" (alpha),
   C"?" "bool" ((((T"OPERATOR" "preARM" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"OPERATOR" "preARM" [] --> alpha)),
   C"!" "bool" ((((T"OPERATOR" "preARM" [] --> bool) --> bool) --> bool)),
   V"P" ((T"OPERATOR" "preARM" [] --> bool)), V"a'" (T"COND" "preARM" []),
   C"?" "bool" (((T"COND" "preARM" [] --> bool) --> bool)),
   V"COND"
    ((T"COND" "preARM" [] -->
      (T"COND" "preARM" [] -->
       (T"COND" "preARM" [] -->
        (T"COND" "preARM" [] -->
         (T"COND" "preARM" [] -->
          (T"COND" "preARM" [] -->
           (T"COND" "preARM" [] -->
            (T"COND" "preARM" [] -->
             (T"COND" "preARM" [] -->
              (T"COND" "preARM" [] -->
               (T"COND" "preARM" [] -->
                (T"COND" "preARM" [] -->
                 (T"COND" "preARM" [] -->
                  (T"COND" "preARM" [] -->
                   (T"COND" "preARM" [] -->
                    (T"COND" "preARM" [] --> bool))))))))))))))))),
   V"M" (T"COND" "preARM" []), V"M'" (T"COND" "preARM" []),
   C"?" "bool" ((((T"COND" "preARM" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"COND" "preARM" [] --> alpha)),
   C"!" "bool" ((((T"COND" "preARM" [] --> bool) --> bool) --> bool)),
   V"P" ((T"COND" "preARM" [] --> bool)),
   V"OFFSET"
    (((T"num" "num" [] --> T"OFFSET" "preARM" []) -->
      ((T"num" "num" [] --> T"OFFSET" "preARM" []) --> bool))),
   V"a'" (T"num" "num" []), V"M" (T"OFFSET" "preARM" []),
   V"M'" (T"OFFSET" "preARM" []), V"f'" ((T"num" "num" [] --> alpha)),
   V"f1'" ((T"num" "num" [] --> alpha)), V"O" (T"OFFSET" "preARM" []),
   V"f0" ((T"num" "num" [] --> alpha)),
   C"?" "bool" ((((T"OFFSET" "preARM" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"OFFSET" "preARM" [] --> alpha)),
   C"!" "bool" ((((T"OFFSET" "preARM" [] --> bool) --> bool) --> bool)),
   V"P" ((T"OFFSET" "preARM" [] --> bool)),
   V"EXP"
    (((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
       T"EXP" "preARM" []) -->
      ((T"num" "num" [] --> T"EXP" "preARM" []) -->
       ((T"cart" "fcp" [bool, T"i32" "words" []] --> T"EXP" "preARM" [])
        -->
        ((T"num" "num" [] --> T"EXP" "preARM" []) -->
         ((T"num" "num" [] --> T"EXP" "preARM" []) --> bool)))))),
   V"a'" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   C"=" "min"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] -->
      (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> bool))),
   V"a'" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"M" (T"EXP" "preARM" []), V"M'" (T"EXP" "preARM" []),
   V"f'"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha)),
   V"f2'" ((T"cart" "fcp" [bool, T"i32" "words" []] --> alpha)),
   V"f3'" ((T"num" "num" [] --> alpha)),
   V"f4'" ((T"num" "num" [] --> alpha)), V"E" (T"EXP" "preARM" []),
   V"p" (T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []]),
   V"c" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"f0"
    ((T"prod" "pair" [T"num" "num" [], T"OFFSET" "preARM" []] --> alpha)),
   C"?" "bool" ((((T"EXP" "preARM" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"EXP" "preARM" [] --> alpha)),
   C"!" "bool" ((((T"EXP" "preARM" [] --> bool) --> bool) --> bool)),
   V"P" ((T"EXP" "preARM" [] --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      bool)), V"pcsr" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
        bool) --> bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
      bool)),
   C"NONE" "option" (T"option" "option" [T"OFFSET" "preARM" []]),
   C"SOME" "option"
    ((T"OFFSET" "preARM" [] -->
      T"option" "option" [T"OFFSET" "preARM" []])),
   V"dst" (T"EXP" "preARM" []),
   C"SOME" "option"
    ((T"EXP" "preARM" [] --> T"option" "option" [T"EXP" "preARM" []])),
   C"NONE" "option" (T"option" "option" [T"EXP" "preARM" []]),
   C"NONE" "option" (T"option" "option" [T"COND" "preARM" []]),
   C"SOME" "option"
    ((T"COND" "preARM" [] --> T"option" "option" [T"COND" "preARM" []])),
   C"LENGTH" "list" ((T"list" "list" [alpha] --> T"num" "num" [])),
   C"EL" "list" ((T"num" "num" [] --> (T"list" "list" [alpha] --> alpha))),
   V"start1" (T"num" "num" []), V"start2" (T"num" "num" []),
   V"instB" ((T"num" "num" [] --> alpha)),
   C"COND" "bool"
    ((bool -->
      ((T"num" "num" [] --> alpha) -->
       ((T"num" "num" [] --> alpha) --> (T"num" "num" [] --> alpha))))),
   C">" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"PRE" "prim_rec" ((T"num" "num" [] --> T"num" "num" [])),
   C"!" "bool"
    ((((T"num" "num" [] -->
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
         ((T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []],
               T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool)
          -->
          (T"prod" "pair"
            [T"num" "num" [],
             T"prod" "pair"
              [T"cart" "fcp" [bool, T"i32" "words" []],
               T"prod" "pair"
                [T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]],
                 T"fmap" "finite_map"
                  [T"num" "num" [],
                   T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool))))
       --> bool) --> bool)),
   V"P'"
    ((T"num" "num" [] -->
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
       ((T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool) -->
        (T"prod" "pair"
          [T"num" "num" [],
           T"prod" "pair"
            [T"cart" "fcp" [bool, T"i32" "words" []],
             T"prod" "pair"
              [T"fmap" "finite_map"
                [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
               T"fmap" "finite_map"
                [T"num" "num" [],
                 T"cart" "fcp" [bool, T"i32" "words" []]]]]] --> bool))))),
   V"v1"
    ((T"num" "num" [] -->
      T"prod" "pair"
       [T"prod" "pair"
         [T"OPERATOR" "preARM" [],
          T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]],
        T"prod" "pair"
         [T"option" "option" [T"EXP" "preARM" []],
          T"prod" "pair"
           [T"list" "list" [T"EXP" "preARM" []],
            T"option" "option" [T"OFFSET" "preARM" []]]]])),
   V"v2"
    ((T"prod" "pair"
       [T"num" "num" [],
        T"prod" "pair"
         [T"cart" "fcp" [bool, T"i32" "words" []],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]
      --> bool)), V"v3" (T"num" "num" []),
   V"v5"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"P" ((T"num" "num" [] --> bool)),
   C"<=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"f" ((alpha --> alpha)),
   C"=" "min" (((alpha --> alpha) --> ((alpha --> alpha) --> bool))),
   C"!" "bool" ((((beta --> beta) --> bool) --> bool)),
   V"f" ((beta --> beta)),
   C"=" "min" (((beta --> beta) --> ((beta --> beta) --> bool))),
   C"FUNPOW" "arithmetic"
    (((beta --> beta) --> (T"num" "num" [] --> (beta --> beta)))),
   C"o" "combin"
    (((beta --> beta) --> ((beta --> beta) --> (beta --> beta)))),
   C"o" "combin"
    (((alpha --> alpha) --> ((alpha --> alpha) --> (alpha --> alpha)))),
   C"WHILE" "while"
    (((alpha --> bool) --> ((alpha --> alpha) --> (alpha --> alpha)))),
   C"o" "combin"
    (((bool --> bool) --> ((alpha --> bool) --> (alpha --> bool)))),
   C"SND" "pair"
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
        (T"num" "num" [] --> bool)] --> (T"num" "num" [] --> bool))),
   V"pcS0" ((T"num" "num" [] --> bool)),
   V"pcS1" ((T"num" "num" [] --> bool)),
   C"FUNPOW" "arithmetic"
    (((T"prod" "pair"
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
         (T"num" "num" [] --> bool)]) -->
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
   V"j"
    (T"prod" "pair"
      [T"num" "num" [],
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]),
   V"s0"
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
       (T"num" "num" [] --> bool)]),
   V"s1"
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
       (T"num" "num" [] --> bool)]),
   C"shortest" "preARM"
    (((T"prod" "pair"
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
         (T"num" "num" [] --> bool)] --> bool) -->
      ((T"prod" "pair"
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
          (T"num" "num" [] --> bool)]) -->
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
          (T"num" "num" [] --> bool)] --> T"num" "num" [])))),
   C"COND" "bool"
    ((bool -->
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
          (T"num" "num" [] --> bool)])))), V"k" (alpha), V"j" (alpha),
   C"SUBSET" "pred_set"
    (((T"num" "num" [] --> bool) -->
      ((T"num" "num" [] --> bool) --> bool))),
   C"EMPTY" "pred_set" ((T"num" "num" [] --> bool)),
   V"pcS'" ((T"num" "num" [] --> bool)),
   C"=" "min"
    (((T"num" "num" [] --> bool) -->
      ((T"num" "num" [] --> bool) --> bool))),
   C"UNION" "pred_set"
    (((T"num" "num" [] --> bool) -->
      ((T"num" "num" [] --> bool) --> (T"num" "num" [] --> bool)))),
   V"n" (alpha),
   V"s0"
    (T"prod" "pair"
      [T"num" "num" [],
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]),
   C"LET" "bool"
    (((T"prod" "pair"
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
         (T"num" "num" [] --> bool)] --> bool) -->
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
   V"s1"
    (T"prod" "pair"
      [T"num" "num" [],
       T"prod" "pair"
        [T"cart" "fcp" [bool, T"i32" "words" []],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]]),
   V"i" (alpha),
   C"!" "bool" (((T"fmap" "finite_map" [alpha, beta] --> bool) --> bool)),
   V"f" (T"fmap" "finite_map" [alpha, beta]),
   C"IN" "bool" ((alpha --> ((alpha --> bool) --> bool))),
   C"FDOM" "finite_map"
    ((T"fmap" "finite_map" [alpha, beta] --> (alpha --> bool))),
   C"=" "min"
    ((T"fmap" "finite_map" [alpha, beta] -->
      (T"fmap" "finite_map" [alpha, beta] --> bool))),
   C"FUPDATE" "finite_map"
    ((T"fmap" "finite_map" [alpha, beta] -->
      (T"prod" "pair" [alpha, beta] -->
       T"fmap" "finite_map" [alpha, beta]))),
   C"," "pair" ((alpha --> (beta --> T"prod" "pair" [alpha, beta]))),
   C"FAPPLY" "finite_map"
    ((T"fmap" "finite_map" [alpha, beta] --> (alpha --> beta))),
   V"f"
    (T"fmap" "finite_map"
      [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]),
   V"c" (T"num" "num" []), V"d" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"=" "min"
    ((T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
      (T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]] -->
       bool))),
   C"!" "bool"
    (((T"fmap" "finite_map" [T"num" "num" [], beta] --> bool) --> bool)),
   V"f" (T"fmap" "finite_map" [T"num" "num" [], beta]),
   C"!" "bool" (((beta --> bool) --> bool)), V"b" (beta), V"d" (beta),
   C"=" "min"
    ((T"fmap" "finite_map" [T"num" "num" [], beta] -->
      (T"fmap" "finite_map" [T"num" "num" [], beta] --> bool))),
   C"FUPDATE" "finite_map"
    ((T"fmap" "finite_map" [T"num" "num" [], beta] -->
      (T"prod" "pair" [T"num" "num" [], beta] -->
       T"fmap" "finite_map" [T"num" "num" [], beta]))),
   C"," "pair"
    ((T"num" "num" [] -->
      (beta --> T"prod" "pair" [T"num" "num" [], beta])))]
  val DT = Thm.disk_thm share_table
  in
  val SRS_TY_DEF =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (\%3. ((%4 $0) (%5 (%6 (%7 %8)))))) $0)))`)
  val SRS_BIJ =
    DT(["DISK_THM"], [],
       `((%9 (%10 (\%11. ((%12 (%13 (%14 $0))) $0)))) (%15 (\%16. ((%17
       ((\%3. ((%4 $0) (%5 (%6 (%7 %8))))) $0)) ((%18 (%14 (%13 $0)))
       $0)))))`)
  val SN = DT([], [], `((%12 %19) (%13 %20))`)
  val SZ = DT([], [], `((%12 %21) (%13 (%5 (%7 %8))))`)
  val SC = DT([], [], `((%12 %22) (%13 (%5 (%6 %8))))`)
  val SV = DT([], [], `((%12 %23) (%13 (%5 (%7 (%7 %8)))))`)
  val SRS_size_def = DT([], [], `(%10 (\%24. ((%18 (%25 $0)) %20)))`)
  val SRS_case =
    DT([], [],
       `(%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%10 (\%24. ((%31
       (((((%32 $4) $3) $2) $1) $0)) ((\%33. (((%34 ((%4 $0) (%5 (%7 %8))))
       $5) (((%34 ((%4 $0) (%5 (%6 %8)))) $4) (((%34 ((%18 $0) (%5 (%6
       %8)))) $3) $2)))) (%14 $0)))))))))))))`)
  val getS_def =
    DT([], [],
       `(%35 (\%36. (%10 (\%37. ((%17 ((%38 $1) $0)) (((((%39 ((%40 $1) (%5
       (%7 (%7 (%7 (%7 (%7 %8)))))))) ((%40 $1) (%5 (%6 (%6 (%6 (%6
       %8))))))) ((%40 $1) (%5 (%7 (%6 (%6 (%6 %8))))))) ((%40 $1) (%5 (%6
       (%7 (%6 (%6 %8))))))) $0))))))`)
  val setS_def =
    DT([], [],
       `(%35 (\%36. (%10 (\%37. ((%41 ((%42 $1) $0)) (((((%43 ((%44 $1)
       (%45 (%5 (%6 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       %8))))))))))))))))))))))))))))))))))) ((%44 $1) (%45 (%5 (%6 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       %8)))))))))))))))))))))))))))))))))) ((%44 $1) (%45 (%5 (%6 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       %8))))))))))))))))))))))))))))))))) ((%44 $1) (%45 (%5 (%6 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 %8))))))))))))))))))))))))))))))))
       $0))))))`)
  val setNZCV_def =
    DT(["DISK_THM"], [],
       `(%35 (\%36. (%46 (\%47. (%46 (\%48. (%46 (\%49. (%46 (\%50. ((%41
       ((%51 $4) ((%52 $3) ((%53 $2) ((%54 $1) $0))))) ((%55 (\%56. (\%57.
       ((%58 ((%9 ((%18 $1) (%5 (%7 (%7 (%7 (%7 (%7 %8)))))))) $5)) ((%58
       ((%9 ((%18 $1) (%5 (%6 (%6 (%6 (%6 %8))))))) $4)) ((%58 ((%9 ((%18
       $1) (%5 (%7 (%6 (%6 (%6 %8))))))) $3)) ((%58 ((%9 ((%18 $1) (%5 (%6
       (%7 (%6 (%6 %8))))))) $2)) ((%9 ((%4 $1) (%5 (%6 (%7 (%6 (%6
       %8))))))) $0)))))))) $4))))))))))))`)
  val OPERATOR_TY_DEF =
    DT(["DISK_THM"], [],
       `(%59 (\%60. ((%61 (\%3. ((%4 $0) (%5 (%7 (%7 (%7 (%6 %8))))))))
       $0)))`)
  val OPERATOR_BIJ =
    DT(["DISK_THM"], [],
       `((%9 (%62 (\%63. ((%64 (%65 (%66 $0))) $0)))) (%15 (\%16. ((%17
       ((\%3. ((%4 $0) (%5 (%7 (%7 (%7 (%6 %8))))))) $0)) ((%18 (%66 (%65
       $0))) $0)))))`)
  val MOV = DT([], [], `((%64 %67) (%65 %20))`)
  val ADD = DT([], [], `((%64 %68) (%65 (%5 (%7 %8))))`)
  val SUB = DT([], [], `((%64 %69) (%65 (%5 (%6 %8))))`)
  val RSB = DT([], [], `((%64 %70) (%65 (%5 (%7 (%7 %8)))))`)
  val MUL = DT([], [], `((%64 %71) (%65 (%5 (%6 (%7 %8)))))`)
  val MLA = DT([], [], `((%64 %72) (%65 (%5 (%7 (%6 %8)))))`)
  val AND = DT([], [], `((%64 %73) (%65 (%5 (%6 (%6 %8)))))`)
  val ORR = DT([], [], `((%64 %74) (%65 (%5 (%7 (%7 (%7 %8))))))`)
  val EOR = DT([], [], `((%64 %75) (%65 (%5 (%6 (%7 (%7 %8))))))`)
  val CMP = DT([], [], `((%64 %76) (%65 (%5 (%7 (%6 (%7 %8))))))`)
  val TST = DT([], [], `((%64 %77) (%65 (%5 (%6 (%6 (%7 %8))))))`)
  val LSL = DT([], [], `((%64 %78) (%65 (%5 (%7 (%7 (%6 %8))))))`)
  val LSR = DT([], [], `((%64 %79) (%65 (%5 (%6 (%7 (%6 %8))))))`)
  val ASR = DT([], [], `((%64 %80) (%65 (%5 (%7 (%6 (%6 %8))))))`)
  val ROR = DT([], [], `((%64 %81) (%65 (%5 (%6 (%6 (%6 %8))))))`)
  val LDR = DT([], [], `((%64 %82) (%65 (%5 (%7 (%7 (%7 (%7 %8)))))))`)
  val STR = DT([], [], `((%64 %83) (%65 (%5 (%6 (%7 (%7 (%7 %8)))))))`)
  val LDMFD = DT([], [], `((%64 %84) (%65 (%5 (%7 (%6 (%7 (%7 %8)))))))`)
  val STMFD = DT([], [], `((%64 %85) (%65 (%5 (%6 (%6 (%7 (%7 %8)))))))`)
  val MRS = DT([], [], `((%64 %86) (%65 (%5 (%7 (%7 (%6 (%7 %8)))))))`)
  val MSR = DT([], [], `((%64 %87) (%65 (%5 (%6 (%7 (%6 (%7 %8)))))))`)
  val B = DT([], [], `((%64 %88) (%65 (%5 (%7 (%6 (%6 (%7 %8)))))))`)
  val BL = DT([], [], `((%64 %89) (%65 (%5 (%6 (%6 (%6 (%7 %8)))))))`)
  val OPERATOR_size_def = DT([], [], `(%62 (\%90. ((%18 (%91 $0)) %20)))`)
  val OPERATOR_case =
    DT([], [],
       `(%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26
       (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98.
       (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26
       (\%104. (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26
       (\%109. (%26 (\%110. (%62 (\%90. ((%31 ((((((((((((((((((((((((%111
       $23) $22) $21) $20) $19) $18) $17) $16) $15) $14) $13) $12) $11)
       $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0)) ((\%33. (((%34 ((%4
       $0) (%5 (%7 (%7 (%6 %8)))))) (((%34 ((%4 $0) (%5 (%7 (%6 %8)))))
       (((%34 ((%4 $0) (%5 (%6 %8)))) (((%34 ((%18 $0) %20)) $24) $23))
       (((%34 ((%4 $0) (%5 (%7 (%7 %8))))) $22) (((%34 ((%18 $0) (%5 (%7
       (%7 %8))))) $21) $20)))) (((%34 ((%4 $0) (%5 (%7 (%7 (%7 %8))))))
       (((%34 ((%18 $0) (%5 (%7 (%6 %8))))) $19) $18)) (((%34 ((%4 $0) (%5
       (%6 (%7 (%7 %8)))))) $17) (((%34 ((%4 $0) (%5 (%7 (%6 (%7 %8))))))
       $16) (((%34 ((%18 $0) (%5 (%7 (%6 (%7 %8)))))) $15) $14)))))) (((%34
       ((%4 $0) (%5 (%6 (%7 (%7 (%7 %8))))))) (((%34 ((%4 $0) (%5 (%7 (%6
       (%6 %8)))))) (((%34 ((%18 $0) (%5 (%7 (%7 (%6 %8)))))) $13) $12))
       (((%34 ((%4 $0) (%5 (%6 (%6 (%6 %8)))))) $11) (((%34 ((%18 $0) (%5
       (%6 (%6 (%6 %8)))))) $10) $9)))) (((%34 ((%4 $0) (%5 (%7 (%7 (%6 (%7
       %8))))))) (((%34 ((%4 $0) (%5 (%7 (%6 (%7 (%7 %8))))))) $8) (((%34
       ((%18 $0) (%5 (%7 (%6 (%7 (%7 %8))))))) $7) $6))) (((%34 ((%4 $0)
       (%5 (%6 (%7 (%6 (%7 %8))))))) $5) (((%34 ((%4 $0) (%5 (%7 (%6 (%6
       (%7 %8))))))) $4) (((%34 ((%18 $0) (%5 (%7 (%6 (%6 (%7 %8))))))) $3)
       $2))))))) (%66
       $0)))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val COND_TY_DEF =
    DT(["DISK_THM"], [],
       `(%112 (\%113. ((%114 (\%3. ((%4 $0) (%5 (%6 (%7 (%7 (%7 %8))))))))
       $0)))`)
  val COND_BIJ =
    DT(["DISK_THM"], [],
       `((%9 (%115 (\%116. ((%117 (%118 (%119 $0))) $0)))) (%15 (\%16.
       ((%17 ((\%3. ((%4 $0) (%5 (%6 (%7 (%7 (%7 %8))))))) $0)) ((%18 (%119
       (%118 $0))) $0)))))`)
  val EQ = DT([], [], `((%117 %120) (%118 %20))`)
  val CS = DT([], [], `((%117 %121) (%118 (%5 (%7 %8))))`)
  val MI = DT([], [], `((%117 %122) (%118 (%5 (%6 %8))))`)
  val VS = DT([], [], `((%117 %123) (%118 (%5 (%7 (%7 %8)))))`)
  val HI = DT([], [], `((%117 %124) (%118 (%5 (%6 (%7 %8)))))`)
  val GE = DT([], [], `((%117 %125) (%118 (%5 (%7 (%6 %8)))))`)
  val GT = DT([], [], `((%117 %126) (%118 (%5 (%6 (%6 %8)))))`)
  val AL = DT([], [], `((%117 %127) (%118 (%5 (%7 (%7 (%7 %8))))))`)
  val NE = DT([], [], `((%117 %128) (%118 (%5 (%6 (%7 (%7 %8))))))`)
  val CC = DT([], [], `((%117 %129) (%118 (%5 (%7 (%6 (%7 %8))))))`)
  val PL = DT([], [], `((%117 %130) (%118 (%5 (%6 (%6 (%7 %8))))))`)
  val VC = DT([], [], `((%117 %131) (%118 (%5 (%7 (%7 (%6 %8))))))`)
  val LS = DT([], [], `((%117 %132) (%118 (%5 (%6 (%7 (%6 %8))))))`)
  val LT = DT([], [], `((%117 %133) (%118 (%5 (%7 (%6 (%6 %8))))))`)
  val LE = DT([], [], `((%117 %134) (%118 (%5 (%6 (%6 (%6 %8))))))`)
  val NV = DT([], [], `((%117 %135) (%118 (%5 (%7 (%7 (%7 (%7 %8)))))))`)
  val COND_size_def = DT([], [], `(%115 (\%136. ((%18 (%137 $0)) %20)))`)
  val COND_case =
    DT([], [],
       `(%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26
       (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98.
       (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103.
       (%115 (\%136. ((%31 (((((((((((((((((%138 $16) $15) $14) $13) $12)
       $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1) $0)) ((\%33. (((%34
       ((%4 $0) (%5 (%7 (%7 (%7 %8)))))) (((%34 ((%4 $0) (%5 (%7 (%7
       %8))))) (((%34 ((%4 $0) (%5 (%7 %8)))) $17) (((%34 ((%18 $0) (%5 (%7
       %8)))) $16) $15))) (((%34 ((%4 $0) (%5 (%6 (%7 %8))))) $14) (((%34
       ((%4 $0) (%5 (%7 (%6 %8))))) $13) (((%34 ((%18 $0) (%5 (%7 (%6
       %8))))) $12) $11))))) (((%34 ((%4 $0) (%5 (%7 (%7 (%6 %8))))))
       (((%34 ((%4 $0) (%5 (%6 (%7 (%7 %8)))))) $10) (((%34 ((%4 $0) (%5
       (%7 (%6 (%7 %8)))))) $9) (((%34 ((%18 $0) (%5 (%7 (%6 (%7 %8))))))
       $8) $7)))) (((%34 ((%4 $0) (%5 (%7 (%6 (%6 %8)))))) (((%34 ((%18 $0)
       (%5 (%7 (%7 (%6 %8)))))) $6) $5)) (((%34 ((%4 $0) (%5 (%6 (%6 (%6
       %8)))))) $4) (((%34 ((%18 $0) (%5 (%6 (%6 (%6 %8)))))) $3) $2))))))
       (%119 $0)))))))))))))))))))))))))))))))))))))`)
  val OFFSET_TY_DEF =
    DT(["DISK_THM"], [],
       `(%139 (\%140. ((%141 (\%142. (%143 (\%144. ((%145 (%146 (\%142.
       ((%145 ((%58 (%147 (\%148. ((%149 $1) ((\%148. (((%150 %20) $0)
       (\%3. %151))) $0))))) (%147 (\%148. ((%149 $1) ((\%148. (((%150
       (%152 %20)) $0) (\%3. %151))) $0)))))) ($1 $0))))) ($0 $1))))))
       $0)))`)
  val OFFSET_repfns =
    DT(["DISK_THM"], [],
       `((%9 (%153 (\%154. ((%155 (%156 (%157 $0))) $0)))) (%146 (\%158.
       ((%17 ((\%142. (%143 (\%144. ((%145 (%146 (\%142. ((%145 ((%58 (%147
       (\%148. ((%149 $1) ((\%148. (((%150 %20) $0) (\%3. %151))) $0)))))
       (%147 (\%148. ((%149 $1) ((\%148. (((%150 (%152 %20)) $0) (\%3.
       %151))) $0)))))) ($1 $0))))) ($0 $1))))) $0)) ((%149 (%157 (%156
       $0))) $0)))))`)
  val preARM0_def =
    DT([], [],
       `((%159 %160) (\%148. (%156 ((\%148. (((%150 %20) $0) (\%3. %151)))
       $0))))`)
  val preARM1_def =
    DT([], [],
       `((%159 %161) (\%148. (%156 ((\%148. (((%150 (%152 %20)) $0) (\%3.
       %151))) $0))))`)
  val POS = DT([], [], `((%159 %162) %160)`)
  val NEG = DT([], [], `((%159 %163) %161)`)
  val OFFSET_case_def =
    DT(["DISK_THM"], [],
       `((%9 (%164 (\%165. (%164 (\%166. (%15 (\%148. ((%31 (((%167 $2) $1)
       (%162 $0))) ($2 $0))))))))) (%164 (\%165. (%164 (\%166. (%15 (\%148.
       ((%31 (((%167 $2) $1) (%163 $0))) ($1 $0)))))))))`)
  val OFFSET_size_def =
    DT(["DISK_THM"], [],
       `((%9 (%15 (\%148. ((%18 (%168 (%162 $0))) ((%169 (%5 (%7 %8)))
       $0))))) (%15 (\%148. ((%18 (%168 (%163 $0))) ((%169 (%5 (%7 %8)))
       $0)))))`)
  val EXP_TY_DEF =
    DT(["DISK_THM"], [],
       `(%170 (\%171. ((%172 (\%173. (%174 (\%175. ((%145 (%176 (\%173.
       ((%145 ((%58 (%177 (\%178. ((%179 $1) ((\%178. (((%180 %20) ((%181
       $0) ((%182 (%183 (\%184. %185))) (%186 (\%187. %185))))) (\%3.
       %188))) $0))))) ((%58 (%147 (\%148. ((%179 $1) ((\%148. (((%180
       (%152 %20)) ((%181 (%189 (\%190. %185))) ((%182 $0) (%186 (\%187.
       %185))))) (\%3. %188))) $0))))) ((%58 (%191 (\%192. ((%179 $1)
       ((\%192. (((%180 (%152 (%152 %20))) ((%181 (%189 (\%190. %185)))
       ((%182 (%183 (\%184. %185))) $0))) (\%3. %188))) $0))))) ((%58 (%147
       (\%148. ((%179 $1) ((\%148. (((%180 (%152 (%152 (%152 %20)))) ((%181
       (%189 (\%190. %185))) ((%182 $0) (%186 (\%187. %185))))) (\%3.
       %188))) $0))))) (%147 (\%148. ((%179 $1) ((\%148. (((%180 (%152
       (%152 (%152 (%152 %20))))) ((%181 (%189 (\%190. %185))) ((%182 $0)
       (%186 (\%187. %185))))) (\%3. %188))) $0))))))))) ($1 $0))))) ($0
       $1)))))) $0)))`)
  val EXP_repfns =
    DT(["DISK_THM"], [],
       `((%9 (%193 (\%194. ((%195 (%196 (%197 $0))) $0)))) (%176 (\%198.
       ((%17 ((\%173. (%174 (\%175. ((%145 (%176 (\%173. ((%145 ((%58 (%177
       (\%178. ((%179 $1) ((\%178. (((%180 %20) ((%181 $0) ((%182 (%183
       (\%184. %185))) (%186 (\%187. %185))))) (\%3. %188))) $0))))) ((%58
       (%147 (\%148. ((%179 $1) ((\%148. (((%180 (%152 %20)) ((%181 (%189
       (\%190. %185))) ((%182 $0) (%186 (\%187. %185))))) (\%3. %188)))
       $0))))) ((%58 (%191 (\%192. ((%179 $1) ((\%192. (((%180 (%152 (%152
       %20))) ((%181 (%189 (\%190. %185))) ((%182 (%183 (\%184. %185)))
       $0))) (\%3. %188))) $0))))) ((%58 (%147 (\%148. ((%179 $1) ((\%148.
       (((%180 (%152 (%152 (%152 %20)))) ((%181 (%189 (\%190. %185)))
       ((%182 $0) (%186 (\%187. %185))))) (\%3. %188))) $0))))) (%147
       (\%148. ((%179 $1) ((\%148. (((%180 (%152 (%152 (%152 (%152 %20)))))
       ((%181 (%189 (\%190. %185))) ((%182 $0) (%186 (\%187. %185)))))
       (\%3. %188))) $0))))))))) ($1 $0))))) ($0 $1))))) $0)) ((%179 (%197
       (%196 $0))) $0)))))`)
  val preARM2_def =
    DT([], [],
       `((%199 %200) (\%178. (%196 ((\%178. (((%180 %20) ((%181 $0) ((%182
       (%183 (\%184. %185))) (%186 (\%187. %185))))) (\%3. %188))) $0))))`)
  val preARM3_def =
    DT([], [],
       `((%201 %202) (\%148. (%196 ((\%148. (((%180 (%152 %20)) ((%181
       (%189 (\%190. %185))) ((%182 $0) (%186 (\%187. %185))))) (\%3.
       %188))) $0))))`)
  val preARM4_def =
    DT([], [],
       `((%203 %204) (\%192. (%196 ((\%192. (((%180 (%152 (%152 %20)))
       ((%181 (%189 (\%190. %185))) ((%182 (%183 (\%184. %185))) $0)))
       (\%3. %188))) $0))))`)
  val preARM5_def =
    DT([], [],
       `((%201 %205) (\%148. (%196 ((\%148. (((%180 (%152 (%152 (%152
       %20)))) ((%181 (%189 (\%190. %185))) ((%182 $0) (%186 (\%187.
       %185))))) (\%3. %188))) $0))))`)
  val preARM6_def =
    DT([], [],
       `((%201 %206) (\%148. (%196 ((\%148. (((%180 (%152 (%152 (%152 (%152
       %20))))) ((%181 (%189 (\%190. %185))) ((%182 $0) (%186 (\%187.
       %185))))) (\%3. %188))) $0))))`)
  val MEM = DT([], [], `((%199 %207) %200)`)
  val NCONST = DT([], [], `((%201 %208) %202)`)
  val WCONST = DT([], [], `((%203 %209) %204)`)
  val REG = DT([], [], `((%201 %210) %205)`)
  val WREG = DT([], [], `((%201 %211) %206)`)
  val EXP_case_def =
    DT(["DISK_THM"], [],
       `((%9 (%212 (\%213. (%164 (\%166. (%214 (\%215. (%164 (\%216. (%164
       (\%217. (%218 (\%178. ((%31 ((((((%219 $5) $4) $3) $2) $1) (%207
       $0))) ($5 $0))))))))))))))) ((%9 (%212 (\%213. (%164 (\%166. (%214
       (\%215. (%164 (\%216. (%164 (\%217. (%15 (\%148. ((%31 ((((((%219
       $5) $4) $3) $2) $1) (%208 $0))) ($4 $0))))))))))))))) ((%9 (%212
       (\%213. (%164 (\%166. (%214 (\%215. (%164 (\%216. (%164 (\%217. (%35
       (\%192. ((%31 ((((((%219 $5) $4) $3) $2) $1) (%209 $0))) ($3
       $0))))))))))))))) ((%9 (%212 (\%213. (%164 (\%166. (%214 (\%215.
       (%164 (\%216. (%164 (\%217. (%15 (\%148. ((%31 ((((((%219 $5) $4)
       $3) $2) $1) (%210 $0))) ($2 $0))))))))))))))) (%212 (\%213. (%164
       (\%166. (%214 (\%215. (%164 (\%216. (%164 (\%217. (%15 (\%148. ((%31
       ((((((%219 $5) $4) $3) $2) $1) (%211 $0))) ($1
       $0))))))))))))))))))`)
  val EXP_size_def =
    DT(["DISK_THM"], [],
       `((%9 (%218 (\%178. ((%18 (%220 (%207 $0))) ((%169 (%5 (%7 %8)))
       ((%221 (\%222. (\%223. ((%169 ((\%222. $0) $1)) (%168 $0)))))
       $0)))))) ((%9 (%15 (\%148. ((%18 (%220 (%208 $0))) ((%169 (%5 (%7
       %8))) $0))))) ((%9 (%35 (\%192. ((%18 (%220 (%209 $0))) (%5 (%7
       %8)))))) ((%9 (%15 (\%148. ((%18 (%220 (%210 $0))) ((%169 (%5 (%7
       %8))) $0))))) (%15 (\%148. ((%18 (%220 (%211 $0))) ((%169 (%5 (%7
       %8))) $0))))))))`)
  val FP_def = DT([], [], `((%195 %224) (%210 (%5 (%7 (%7 (%6 %8))))))`)
  val IP_def = DT([], [], `((%195 %225) (%210 (%5 (%6 (%7 (%6 %8))))))`)
  val SP_def = DT([], [], `((%195 %226) (%210 (%5 (%7 (%6 (%6 %8))))))`)
  val LR_def = DT([], [], `((%195 %227) (%210 (%5 (%6 (%6 (%6 %8))))))`)
  val PC_def =
    DT([], [], `((%195 %228) (%210 (%5 (%7 (%7 (%7 (%7 %8)))))))`)
  val read_def =
    DT(["DISK_THM"], [],
       `(%229 (\%230. (%229 (\%231. (%193 (\%232. ((%41 ((%233 ((%234 $2)
       $1)) $0)) ((((((%235 (\%190. ((%236 (\%237. (\%238. (((%239 (\%240.
       ((%241 $5) ((%169 (%242 ((%241 $6) $2))) $0)))) (\%243. ((%241 $5)
       ((%244 (%242 ((%241 $6) $2))) $0)))) $0)))) $0))) (\%56. (%45 $0)))
       (\%245. $0)) (\%16. ((%241 $3) $0))) (\%246. %247)) $0))))))))`)
  val write_def =
    DT(["DISK_THM"], [],
       `(%229 (\%230. (%229 (\%231. (%193 (\%232. (%35 (\%187. ((%248
       (((%249 ((%234 $3) $2)) $1) $0)) ((((((%250 (\%251. ((%252 (\%16.
       (\%253. ((%234 $6) (((%254 (\%240. ((%255 $6) ((%182 ((%169 (%242
       ((%241 $7) $2))) $0)) $4)))) (\%243. ((%255 $6) ((%182 ((%244 (%242
       ((%241 $7) $2))) $0)) $4)))) $0))))) $0))) (\%256. ((%234 $4) $3)))
       (\%257. ((%234 $4) $3))) (\%258. ((%234 ((%255 $4) ((%182 $0) $1)))
       $3))) (\%259. ((%234 $4) $3))) $1))))))))))`)
  val goto_primitive_def =
    DT([], [],
       `((%260 %261) ((%262 (%263 (\%264. (%265 $0)))) (\%266. (\%267.
       ((%268 (\%269. (\%270. (((%271 %272) (\%273. (%274 (((%275 (\%3.
       ((%169 $3) $0))) (\%276. ((%244 $3) $0))) $0)))) $0)))) $0)))))`)
  val decode_op_def =
    DT(["DISK_THM"], [],
       `(%15 (\%269. (%35 (\%36. (%277 (\%278. (%62 (\%279. (%280 (\%281.
       (%282 (\%283. (%26 (\%284. ((%285 ((%286 ((%287 $6) ((%288 $5) $4)))
       ((%289 $3) ((%290 $2) ((%291 $1) $0)))))
       ((((((((((((((((((((((((%292 ((%288 $5) (((%249 $4) (%293 $2))
       ((%233 $4) (%294 $1))))) ((%288 $5) (((%249 $4) (%293 $2)) ((%295
       ((%233 $4) (%294 $1))) ((%233 $4) (%294 (%296 $1))))))) ((%288 $5)
       (((%249 $4) (%293 $2)) ((%297 ((%233 $4) (%294 $1))) ((%233 $4)
       (%294 (%296 $1))))))) ((%288 $5) (((%249 $4) (%293 $2)) ((%297
       ((%233 $4) (%294 (%296 $1)))) ((%233 $4) (%294 $1)))))) ((%288 $5)
       (((%249 $4) (%293 $2)) ((%298 ((%233 $4) (%294 $1))) ((%233 $4)
       (%294 (%296 $1))))))) ((%288 $5) (((%249 $4) (%293 $2)) ((%295
       ((%298 ((%233 $4) (%294 $1))) ((%233 $4) (%294 (%296 $1))))) ((%233
       $4) (%294 (%296 (%296 $1)))))))) ((%288 $5) (((%249 $4) (%293 $2))
       ((%299 ((%233 $4) (%294 $1))) ((%233 $4) (%294 (%296 $1)))))))
       ((%288 $5) (((%249 $4) (%293 $2)) ((%44 ((%233 $4) (%294 $1)))
       ((%233 $4) (%294 (%296 $1))))))) ((%288 $5) (((%249 $4) (%293 $2))
       ((%300 ((%233 $4) (%294 $1))) ((%233 $4) (%294 (%296 $1)))))))
       ((%301 (\%192. ((%301 (\%302. ((%288 ((%51 $7) ((%52 (%303 ((%297
       $1) $0))) ((%53 ((%41 $1) $0)) ((%54 ((%304 $0) $1)) ((%9 (%305
       ((%17 (%303 $1)) (%303 $0)))) (%305 ((%17 (%303 $1)) (%303 ((%297
       $1) $0)))))))))) $6))) ((%233 $5) (%294 (%296 $2)))))) ((%233 $4)
       (%294 $1)))) ((%301 (\%192. ((%301 (\%302. ((%288 ((%51 $7) ((%52
       (%303 ((%299 $1) $0))) ((%53 ((%41 ((%299 $1) $0)) (%45 %20))) ((%54
       %306) ((%40 $7) (%5 (%6 (%7 (%6 (%6 %8))))))))))) $6))) ((%233 $5)
       (%294 (%296 $2)))))) ((%233 $4) (%294 $1)))) ((%288 $5) (((%249 $4)
       (%293 $2)) ((%307 ((%233 $4) (%294 $1))) (%242 ((%233 $4) (%294
       (%296 $1)))))))) ((%288 $5) (((%249 $4) (%293 $2)) ((%308 ((%233 $4)
       (%294 $1))) (%242 ((%233 $4) (%294 (%296 $1)))))))) ((%288 $5)
       (((%249 $4) (%293 $2)) ((%309 ((%233 $4) (%294 $1))) (%242 ((%233
       $4) (%294 (%296 $1)))))))) ((%288 $5) (((%249 $4) (%293 $2)) ((%310
       ((%233 $4) (%294 $1))) (%242 ((%233 $4) (%294 (%296 $1))))))))
       ((%288 $5) (((%249 $4) (%293 $2)) ((%233 $4) (%294 $1))))) ((%288
       $5) (((%249 $4) (%294 $1)) ((%233 $4) (%293 $2))))) ((((((%311
       (\%190. %312)) (\%313. %312)) (\%314. %312)) (\%16. ((%288 $6) (%315
       (((%316 (%317 (\%318. (\%56. (\%319. ((%320 (((%249 $2) $0) ((%233
       $8) (%207 ((%321 $3) (%162 ((%169 $1) (%5 (%7 %8))))))))) ((%169 $1)
       (%5 (%7 %8))))))))) ((%320 $5) %20)) $2))))) (\%258. ((%288 $6)
       (((%249 (%315 (((%316 (%317 (\%318. (\%56. (\%319. ((%320 (((%249
       $2) $0) ((%233 $8) (%207 ((%321 $3) (%162 ((%169 $1) (%5 (%7
       %8))))))))) ((%169 $1) (%5 (%7 %8))))))))) ((%320 $5) %20)) $2)))
       (%210 $0)) ((%295 ((%233 $5) (%210 $0))) (%45 (%322 $2))))))) (%293
       $2))) ((((((%311 (\%190. %312)) (\%313. %312)) (\%314. %312)) (\%16.
       ((%288 $6) (%315 (((%316 (%317 (\%318. (\%56. (\%319. ((%320 (((%249
       $2) (%207 ((%321 $3) (%163 $1)))) ((%233 $8) $0))) ((%169 $1) (%5
       (%7 %8))))))))) ((%320 $5) %20)) (%323 $2)))))) (\%258. ((%288 $6)
       (((%249 (%315 (((%316 (%317 (\%318. (\%56. (\%319. ((%320 (((%249
       $2) (%207 ((%321 $3) (%163 $1)))) ((%233 $8) $0))) ((%169 $1) (%5
       (%7 %8))))))))) ((%320 $5) %20)) (%323 $2)))) (%210 $0)) ((%297
       ((%233 $5) (%210 $0))) (%45 (%322 $2))))))) (%293 $2))) ((%288 $5)
       (((%249 $4) (%293 $2)) $5))) ((%288 ((%233 $4) (%294 $1))) $4))
       ((%288 $5) $4)) ((%288 $5) (((%249 $4) (%210 (%5 (%6 (%6 (%6
       %8)))))) (%45 (%152 $6))))) $3))))))))))))))))`)
  val decode_cond_cpsr_def =
    DT(["DISK_THM"], [],
       `((%9 (%35 (\%36. ((%17 ((%324 $0) %120)) ((%38 $0) %21))))) ((%9
       (%35 (\%36. ((%17 ((%324 $0) %121)) ((%38 $0) %22))))) ((%9 (%35
       (\%36. ((%17 ((%324 $0) %122)) ((%38 $0) %19))))) ((%9 (%35 (\%36.
       ((%17 ((%324 $0) %123)) ((%38 $0) %23))))) ((%9 (%35 (\%36. ((%17
       ((%324 $0) %124)) ((%9 ((%38 $0) %22)) (%305 ((%38 $0) %21)))))))
       ((%9 (%35 (\%36. ((%17 ((%324 $0) %125)) ((%17 ((%38 $0) %19)) ((%38
       $0) %23)))))) ((%9 (%35 (\%36. ((%17 ((%324 $0) %126)) ((%9 (%305
       ((%38 $0) %21))) ((%17 ((%38 $0) %19)) ((%38 $0) %23))))))) ((%9
       (%35 (\%36. ((%17 ((%324 $0) %127)) %185)))) ((%9 (%35 (\%36. ((%17
       ((%324 $0) %128)) (%305 ((%38 $0) %21)))))) ((%9 (%35 (\%36. ((%17
       ((%324 $0) %129)) (%305 ((%38 $0) %22)))))) ((%9 (%35 (\%36. ((%17
       ((%324 $0) %130)) (%305 ((%38 $0) %19)))))) ((%9 (%35 (\%36. ((%17
       ((%324 $0) %131)) (%305 ((%38 $0) %23)))))) ((%9 (%35 (\%36. ((%17
       ((%324 $0) %132)) ((%58 (%305 ((%38 $0) %22))) ((%38 $0) %21))))))
       ((%9 (%35 (\%36. ((%17 ((%324 $0) %133)) (%305 ((%17 ((%38 $0) %19))
       ((%38 $0) %23))))))) ((%9 (%35 (\%36. ((%17 ((%324 $0) %134)) ((%58
       ((%38 $0) %21)) (%305 ((%17 ((%38 $0) %19)) ((%38 $0) %23))))))))
       (%35 (\%36. ((%17 ((%324 $0) %135)) %306))))))))))))))))))`)
  val decode_cond_def =
    DT(["DISK_THM"], [],
       `(%15 (\%269. (%35 (\%36. (%277 (\%278. (%62 (\%279. (%325 (\%326.
       (%46 (\%327. (%280 (\%281. (%282 (\%283. (%328 (\%329. ((%330 ((%331
       ((%287 $8) ((%288 $7) $6))) ((%332 ((%333 $5) ((%334 $4) $3)))
       ((%335 $2) ((%336 $1) $0))))) (((%337 ((%287 ((%169 $8) (%5 (%7
       %8)))) ((%338 ((%287 $8) ((%288 $7) $6))) ((%339 $5) ((%335 $2)
       ((%336 $1) $0)))))) (\%340. (((%341 ((%324 $8) $0)) ((%287 (%261
       ((%342 $9) $1))) ((%338 ((%287 $9) ((%288 $8) $7))) ((%339 $6)
       ((%335 $3) ((%336 $2) $1)))))) ((%287 ((%169 $9) (%5 (%7 %8))))
       ((%288 $8) $7))))) $4))))))))))))))))))))`)
  val upload_def =
    DT(["DISK_THM"], [],
       `((%9 (%26 (\%343. (%344 (\%345. (%164 (\%346. (%15 (\%347. ((%348
       (((%349 ((%350 $3) $2)) $1) $0)) (((%349 $2) (\%351. (((%34 ((%18
       $0) $1)) $4) ($2 $0)))) (%152 $0)))))))))))) (%164 (\%346. (%15
       (\%347. ((%348 (((%349 %352) $1) $0)) $1))))))`)
  val uploadCode_def =
    DT([], [],
       `(%344 (\%353. (%164 (\%346. ((%348 ((%354 $1) $0)) (((%349 $1) $0)
       %20))))))`)
  val uploadSeg_def =
    DT(["DISK_THM"], [],
       `((%9 (%355 (\%356. (%164 (\%346. ((%348 (((%357 %20) $1) $0))
       $0)))))) (%15 (\%3. (%355 (\%356. (%164 (\%346. ((%348 (((%357 (%152
       $2)) $1) $0)) (((%349 ((%358 $2) $1)) (((%357 $2) $1) $0)) ((%359
       (%5 (%6 (%6 (%7 %8))))) $2))))))))))`)
  val run_tupled_primitive_def =
    DT([], [],
       `((%360 %361) ((%362 (%363 (\%364. ((%9 (%365 $0)) (%366 (\%367.
       (%277 (\%368. (%35 (\%36. (%15 (\%269. (%369 (\%370. (%15 (\%3.
       ((%145 ((%9 (%305 ((%18 $0) %20))) (%305 ($1 ((%287 $2) ((%288 $3)
       $4)))))) (($6 ((%371 ((%244 $0) (%5 (%7 %8)))) ((%372 $5) ((%373 $1)
       ((%331 ((%287 $2) ((%288 $3) $4))) ($5 $2)))))) ((%371 $0) ((%372
       $5) ((%373 $1) ((%287 $2) ((%288 $3) $4)))))))))))))))))))))))
       (\%374. (\%375. ((%376 (\%3. (\%377. ((%378 (\%367. (\%379. ((%380
       (\%370. (\%381. ((%382 (\%269. (\%383. ((%384 (\%36. (\%368. (%385
       (((%341 ((%18 $9) %20)) ((%287 $3) ((%288 $1) $0))) (((%341 ($5
       ((%287 $3) ((%288 $1) $0)))) ((%287 $3) ((%288 $1) $0))) ($11 ((%371
       ((%244 $9) (%5 (%7 %8)))) ((%372 $7) ((%373 $5) ((%331 ((%287 $3)
       ((%288 $1) $0))) ($7 $3)))))))))))) $0)))) $0)))) $0)))) $0))))
       $0)))))`)
  val run_curried_def =
    DT([], [],
       `(%15 (\%222. (%366 (\%386. (%369 (\%387. (%388 (\%389. ((%330
       ((((%390 $3) $2) $1) $0)) (%361 ((%371 $3) ((%372 $2) ((%373 $1)
       $0)))))))))))))`)
  val stopAt_def =
    DT([], [],
       `(%391 (\%392. (%393 (\%394. (%26 (\%395. ((%17 (((%396 $2) $1) $0))
       (%147 (\%3. ($3 (((%397 $2) $0) $1)))))))))))`)
  val shortest_def =
    DT([], [],
       `(%391 (\%392. (%393 (\%394. (%26 (\%395. ((%18 (((%398 $2) $1) $0))
       (%399 (\%3. ($3 (((%397 $2) $0) $1)))))))))))`)
  val step_def =
    DT([], [],
       `(%366 (\%367. ((%400 (%401 $0)) (%402 (\%403. (\%404. ((%405 ((%331
       $1) ($2 (%406 $1)))) ((%407 (%406 $1)) $0))))))))`)
  val runTo_def =
    DT(["DISK_THM"], [],
       `(%366 (\%367. (%15 (\%408. (%388 (\%403. (%409 (\%404. ((%410
       (((%411 $3) $2) ((%405 $1) $0))) (((%412 (%413 (\%403. (\%404. (%305
       ((%18 (%406 $1)) $4)))))) (%401 $3)) ((%405 $1) $0)))))))))))`)
  val terd_def =
    DT([], [],
       `(%366 (\%367. (%15 (\%408. (%414 (\%415. ((%17 (((%416 $2) $1) $0))
       (((%417 (\%415. ((%18 (%406 (%418 $0))) $2))) (%401 $2))
       $0))))))))`)
  val in_regs_dom_def =
    DT([], [],
       `(%419 (\%420. ((%17 (%421 $0)) ((%9 ((%422 %20) (%423 $0))) ((%9
       ((%422 (%5 (%7 %8))) (%423 $0))) ((%9 ((%422 (%5 (%6 %8))) (%423
       $0))) ((%9 ((%422 (%5 (%7 (%7 %8)))) (%423 $0))) ((%9 ((%422 (%5 (%6
       (%7 %8)))) (%423 $0))) ((%9 ((%422 (%5 (%7 (%6 %8)))) (%423 $0)))
       ((%9 ((%422 (%5 (%6 (%6 %8)))) (%423 $0))) ((%9 ((%422 (%5 (%7 (%7
       (%7 %8))))) (%423 $0))) ((%9 ((%422 (%5 (%6 (%7 (%7 %8))))) (%423
       $0))) ((%9 ((%422 (%5 (%7 (%6 (%7 %8))))) (%423 $0))) ((%9 ((%422
       (%5 (%6 (%6 (%7 %8))))) (%423 $0))) ((%9 ((%422 (%5 (%7 (%7 (%6
       %8))))) (%423 $0))) ((%9 ((%422 (%5 (%6 (%7 (%6 %8))))) (%423 $0)))
       ((%9 ((%422 (%5 (%7 (%6 (%6 %8))))) (%423 $0))) ((%422 (%5 (%6 (%6
       (%6 %8))))) (%423 $0)))))))))))))))))))`)
  val in_mem_dom_def =
    DT([], [],
       `(%419 (\%424. ((%17 (%425 $0)) (%15 (\%56. ((%422 $0) (%423
       $1)))))))`)
  val num2SRS_SRS2num =
    DT(["DISK_THM"], [], `(%10 (\%11. ((%12 (%13 (%14 $0))) $0)))`)
  val SRS2num_num2SRS =
    DT(["DISK_THM"], [],
       `(%15 (\%16. ((%17 ((%4 $0) (%5 (%6 (%7 %8))))) ((%18 (%14 (%13
       $0))) $0))))`)
  val num2SRS_11 =
    DT(["DISK_THM"], [],
       `(%15 (\%16. (%15 (\%258. ((%145 ((%4 $1) (%5 (%6 (%7 %8))))) ((%145
       ((%4 $0) (%5 (%6 (%7 %8))))) ((%17 ((%12 (%13 $1)) (%13 $0))) ((%18
       $1) $0))))))))`)
  val SRS2num_11 =
    DT(["DISK_THM"], [],
       `(%10 (\%11. (%10 (\%426. ((%17 ((%18 (%14 $1)) (%14 $0))) ((%12 $1)
       $0))))))`)
  val num2SRS_ONTO =
    DT(["DISK_THM"], [],
       `(%10 (\%11. (%147 (\%16. ((%9 ((%12 $1) (%13 $0))) ((%4 $0) (%5 (%6
       (%7 %8)))))))))`)
  val SRS2num_ONTO =
    DT(["DISK_THM"], [],
       `(%15 (\%16. ((%17 ((%4 $0) (%5 (%6 (%7 %8))))) (%427 (\%11. ((%18
       $1) (%14 $0)))))))`)
  val num2SRS_thm =
    DT([], [],
       `((%9 ((%12 (%13 %20)) %19)) ((%9 ((%12 (%13 (%5 (%7 %8)))) %21))
       ((%9 ((%12 (%13 (%5 (%6 %8)))) %22)) ((%12 (%13 (%5 (%7 (%7 %8)))))
       %23))))`)
  val SRS2num_thm =
    DT(["DISK_THM"], [],
       `((%9 ((%18 (%14 %19)) %20)) ((%9 ((%18 (%14 %21)) (%5 (%7 %8))))
       ((%9 ((%18 (%14 %22)) (%5 (%6 %8)))) ((%18 (%14 %23)) (%5 (%7 (%7
       %8)))))))`)
  val SRS_EQ_SRS =
    DT(["DISK_THM"], [],
       `(%10 (\%11. (%10 (\%426. ((%17 ((%12 $1) $0)) ((%18 (%14 $1)) (%14
       $0)))))))`)
  val SRS_case_def =
    DT(["DISK_THM"], [],
       `((%9 (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. ((%31 (((((%32
       $3) $2) $1) $0) %19)) $3)))))))))) ((%9 (%26 (\%27. (%26 (\%28. (%26
       (\%29. (%26 (\%30. ((%31 (((((%32 $3) $2) $1) $0) %21)) $2))))))))))
       ((%9 (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. ((%31 (((((%32
       $3) $2) $1) $0) %22)) $1)))))))))) (%26 (\%27. (%26 (\%28. (%26
       (\%29. (%26 (\%30. ((%31 (((((%32 $3) $2) $1) $0) %23))
       $0))))))))))))`)
  val datatype_SRS =
    DT(["DISK_THM"], [], `(%428 ((((%429 %19) %21) %22) %23))`)
  val SRS_distinct =
    DT(["DISK_THM"], [],
       `((%9 (%305 ((%12 %19) %21))) ((%9 (%305 ((%12 %19) %22))) ((%9
       (%305 ((%12 %19) %23))) ((%9 (%305 ((%12 %21) %22))) ((%9 (%305
       ((%12 %21) %23))) (%305 ((%12 %22) %23)))))))`)
  val SRS_case_cong =
    DT(["DISK_THM"], [],
       `(%10 (\%430. (%10 (\%431. (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26
       (\%30. ((%145 ((%9 ((%12 $5) $4)) ((%9 ((%145 ((%12 $4) %19)) ((%31
       $3) %432))) ((%9 ((%145 ((%12 $4) %21)) ((%31 $2) %433))) ((%9
       ((%145 ((%12 $4) %22)) ((%31 $1) %434))) ((%145 ((%12 $4) %23))
       ((%31 $0) %435))))))) ((%31 (((((%32 $3) $2) $1) $0) $5)) (((((%32
       %432) %433) %434) %435) $4)))))))))))))))`)
  val SRS_nchotomy =
    DT(["DISK_THM"], [],
       `(%10 (\%11. ((%58 ((%12 $0) %19)) ((%58 ((%12 $0) %21)) ((%58 ((%12
       $0) %22)) ((%12 $0) %23))))))`)
  val SRS_Axiom =
    DT(["DISK_THM"], [],
       `(%26 (\%436. (%26 (\%437. (%26 (\%438. (%26 (\%439. (%440 (\%441.
       ((%9 ((%31 ($0 %19)) $4)) ((%9 ((%31 ($0 %21)) $3)) ((%9 ((%31 ($0
       %22)) $2)) ((%31 ($0 %23)) $1))))))))))))))`)
  val SRS_induction =
    DT(["DISK_THM"], [],
       `(%442 (\%443. ((%145 ((%9 ($0 %22)) ((%9 ($0 %19)) ((%9 ($0 %23))
       ($0 %21))))) (%10 (\%11. ($1 $0))))))`)
  val getS_thm =
    DT(["DISK_THM"], [],
       `((%9 ((%17 ((%38 %36) %19)) ((%40 %36) (%5 (%7 (%7 (%7 (%7 (%7
       %8))))))))) ((%9 ((%17 ((%38 %36) %21)) ((%40 %36) (%5 (%6 (%6 (%6
       (%6 %8)))))))) ((%9 ((%17 ((%38 %36) %22)) ((%40 %36) (%5 (%7 (%6
       (%6 (%6 %8)))))))) ((%17 ((%38 %36) %23)) ((%40 %36) (%5 (%6 (%7 (%6
       (%6 %8))))))))))`)
  val setS_thm =
    DT(["DISK_THM"], [],
       `((%9 ((%41 ((%42 %36) %19)) ((%44 %36) (%45 (%5 (%6 (%7 (%7 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       %8)))))))))))))))))))))))))))))))))))) ((%9 ((%41 ((%42 %36) %21))
       ((%44 %36) (%45 (%5 (%6 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 %8))))))))))))))))))))))))))))))))))) ((%9 ((%41 ((%42 %36)
       %22)) ((%44 %36) (%45 (%5 (%6 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 (%7 %8)))))))))))))))))))))))))))))))))) ((%41 ((%42 %36) %23))
       ((%44 %36) (%45 (%5 (%6 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7 (%7
       %8)))))))))))))))))))))))))))))))))))`)
  val setNZCV_thm =
    DT(["DISK_THM"], [],
       `((%9 ((%17 ((%38 ((%51 %36) ((%52 %47) ((%53 %48) ((%54 %49)
       %50))))) %19)) %47)) ((%9 ((%17 ((%38 ((%51 %36) ((%52 %47) ((%53
       %48) ((%54 %49) %50))))) %21)) %48)) ((%9 ((%17 ((%38 ((%51 %36)
       ((%52 %47) ((%53 %48) ((%54 %49) %50))))) %22)) %49)) ((%17 ((%38
       ((%51 %36) ((%52 %47) ((%53 %48) ((%54 %49) %50))))) %23)) %50))))`)
  val num2OPERATOR_OPERATOR2num =
    DT(["DISK_THM"], [], `(%62 (\%63. ((%64 (%65 (%66 $0))) $0)))`)
  val OPERATOR2num_num2OPERATOR =
    DT(["DISK_THM"], [],
       `(%15 (\%16. ((%17 ((%4 $0) (%5 (%7 (%7 (%7 (%6 %8))))))) ((%18 (%66
       (%65 $0))) $0))))`)
  val num2OPERATOR_11 =
    DT(["DISK_THM"], [],
       `(%15 (\%16. (%15 (\%258. ((%145 ((%4 $1) (%5 (%7 (%7 (%7 (%6
       %8))))))) ((%145 ((%4 $0) (%5 (%7 (%7 (%7 (%6 %8))))))) ((%17 ((%64
       (%65 $1)) (%65 $0))) ((%18 $1) $0))))))))`)
  val OPERATOR2num_11 =
    DT(["DISK_THM"], [],
       `(%62 (\%63. (%62 (\%444. ((%17 ((%18 (%66 $1)) (%66 $0))) ((%64 $1)
       $0))))))`)
  val num2OPERATOR_ONTO =
    DT(["DISK_THM"], [],
       `(%62 (\%63. (%147 (\%16. ((%9 ((%64 $1) (%65 $0))) ((%4 $0) (%5 (%7
       (%7 (%7 (%6 %8)))))))))))`)
  val OPERATOR2num_ONTO =
    DT(["DISK_THM"], [],
       `(%15 (\%16. ((%17 ((%4 $0) (%5 (%7 (%7 (%7 (%6 %8))))))) (%445
       (\%63. ((%18 $1) (%66 $0)))))))`)
  val num2OPERATOR_thm =
    DT([], [],
       `((%9 ((%64 (%65 %20)) %67)) ((%9 ((%64 (%65 (%5 (%7 %8)))) %68))
       ((%9 ((%64 (%65 (%5 (%6 %8)))) %69)) ((%9 ((%64 (%65 (%5 (%7 (%7
       %8))))) %70)) ((%9 ((%64 (%65 (%5 (%6 (%7 %8))))) %71)) ((%9 ((%64
       (%65 (%5 (%7 (%6 %8))))) %72)) ((%9 ((%64 (%65 (%5 (%6 (%6 %8)))))
       %73)) ((%9 ((%64 (%65 (%5 (%7 (%7 (%7 %8)))))) %74)) ((%9 ((%64 (%65
       (%5 (%6 (%7 (%7 %8)))))) %75)) ((%9 ((%64 (%65 (%5 (%7 (%6 (%7
       %8)))))) %76)) ((%9 ((%64 (%65 (%5 (%6 (%6 (%7 %8)))))) %77)) ((%9
       ((%64 (%65 (%5 (%7 (%7 (%6 %8)))))) %78)) ((%9 ((%64 (%65 (%5 (%6
       (%7 (%6 %8)))))) %79)) ((%9 ((%64 (%65 (%5 (%7 (%6 (%6 %8))))))
       %80)) ((%9 ((%64 (%65 (%5 (%6 (%6 (%6 %8)))))) %81)) ((%9 ((%64 (%65
       (%5 (%7 (%7 (%7 (%7 %8))))))) %82)) ((%9 ((%64 (%65 (%5 (%6 (%7 (%7
       (%7 %8))))))) %83)) ((%9 ((%64 (%65 (%5 (%7 (%6 (%7 (%7 %8)))))))
       %84)) ((%9 ((%64 (%65 (%5 (%6 (%6 (%7 (%7 %8))))))) %85)) ((%9 ((%64
       (%65 (%5 (%7 (%7 (%6 (%7 %8))))))) %86)) ((%9 ((%64 (%65 (%5 (%6 (%7
       (%6 (%7 %8))))))) %87)) ((%9 ((%64 (%65 (%5 (%7 (%6 (%6 (%7
       %8))))))) %88)) ((%64 (%65 (%5 (%6 (%6 (%6 (%7 %8)))))))
       %89)))))))))))))))))))))))`)
  val OPERATOR2num_thm =
    DT(["DISK_THM"], [],
       `((%9 ((%18 (%66 %67)) %20)) ((%9 ((%18 (%66 %68)) (%5 (%7 %8))))
       ((%9 ((%18 (%66 %69)) (%5 (%6 %8)))) ((%9 ((%18 (%66 %70)) (%5 (%7
       (%7 %8))))) ((%9 ((%18 (%66 %71)) (%5 (%6 (%7 %8))))) ((%9 ((%18
       (%66 %72)) (%5 (%7 (%6 %8))))) ((%9 ((%18 (%66 %73)) (%5 (%6 (%6
       %8))))) ((%9 ((%18 (%66 %74)) (%5 (%7 (%7 (%7 %8)))))) ((%9 ((%18
       (%66 %75)) (%5 (%6 (%7 (%7 %8)))))) ((%9 ((%18 (%66 %76)) (%5 (%7
       (%6 (%7 %8)))))) ((%9 ((%18 (%66 %77)) (%5 (%6 (%6 (%7 %8)))))) ((%9
       ((%18 (%66 %78)) (%5 (%7 (%7 (%6 %8)))))) ((%9 ((%18 (%66 %79)) (%5
       (%6 (%7 (%6 %8)))))) ((%9 ((%18 (%66 %80)) (%5 (%7 (%6 (%6 %8))))))
       ((%9 ((%18 (%66 %81)) (%5 (%6 (%6 (%6 %8)))))) ((%9 ((%18 (%66 %82))
       (%5 (%7 (%7 (%7 (%7 %8))))))) ((%9 ((%18 (%66 %83)) (%5 (%6 (%7 (%7
       (%7 %8))))))) ((%9 ((%18 (%66 %84)) (%5 (%7 (%6 (%7 (%7 %8)))))))
       ((%9 ((%18 (%66 %85)) (%5 (%6 (%6 (%7 (%7 %8))))))) ((%9 ((%18 (%66
       %86)) (%5 (%7 (%7 (%6 (%7 %8))))))) ((%9 ((%18 (%66 %87)) (%5 (%6
       (%7 (%6 (%7 %8))))))) ((%9 ((%18 (%66 %88)) (%5 (%7 (%6 (%6 (%7
       %8))))))) ((%18 (%66 %89)) (%5 (%6 (%6 (%6 (%7
       %8))))))))))))))))))))))))))))`)
  val OPERATOR_EQ_OPERATOR =
    DT(["DISK_THM"], [],
       `(%62 (\%63. (%62 (\%444. ((%17 ((%64 $1) $0)) ((%18 (%66 $1)) (%66
       $0)))))))`)
  val OPERATOR_case_def =
    DT(["DISK_THM"], [],
       `((%9 (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92.
       (%26 (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26
       (\%98. (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26
       (\%103. (%26 (\%104. (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26
       (\%108. (%26 (\%109. (%26 (\%110. ((%31 ((((((((((((((((((((((((%111
       $22) $21) $20) $19) $18) $17) $16) $15) $14) $13) $12) $11) $10) $9)
       $8) $7) $6) $5) $4) $3) $2) $1) $0) %67))
       $22)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %68))
       $21)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %69))
       $20)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %70))
       $19)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %71))
       $18)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %72))
       $17)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %73))
       $16)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %74))
       $15)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %75))
       $14)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %76))
       $13)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %77))
       $12)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %78))
       $11)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %79))
       $10)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %80))
       $9)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %81))
       $8)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %82))
       $7)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %83))
       $6)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %84))
       $5)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %85))
       $4)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %86))
       $3)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %87))
       $2)))))))))))))))))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104.
       (%26 (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109.
       (%26 (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19)
       $18) $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4)
       $3) $2) $1) $0) %88))
       $1)))))))))))))))))))))))))))))))))))))))))))))))) (%26 (\%27. (%26
       (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26 (\%94.
       (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99. (%26
       (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. (%26 (\%104. (%26
       (\%105. (%26 (\%106. (%26 (\%107. (%26 (\%108. (%26 (\%109. (%26
       (\%110. ((%31 ((((((((((((((((((((((((%111 $22) $21) $20) $19) $18)
       $17) $16) $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3)
       $2) $1) $0) %89))
       $0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val datatype_OPERATOR =
    DT(["DISK_THM"], [],
       `(%428 (((((((((((((((((((((((%446 %67) %68) %69) %70) %71) %72)
       %73) %74) %75) %76) %77) %78) %79) %80) %81) %82) %83) %84) %85)
       %86) %87) %88) %89))`)
  val OPERATOR_case_cong =
    DT(["DISK_THM"], [],
       `(%62 (\%447. (%62 (\%448. (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26
       (\%30. (%26 (\%92. (%26 (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96.
       (%26 (\%97. (%26 (\%98. (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26
       (\%102. (%26 (\%103. (%26 (\%104. (%26 (\%105. (%26 (\%106. (%26
       (\%107. (%26 (\%108. (%26 (\%109. (%26 (\%110. ((%145 ((%9 ((%64
       $24) $23)) ((%9 ((%145 ((%64 $23) %67)) ((%31 $22) %432))) ((%9
       ((%145 ((%64 $23) %68)) ((%31 $21) %433))) ((%9 ((%145 ((%64 $23)
       %69)) ((%31 $20) %434))) ((%9 ((%145 ((%64 $23) %70)) ((%31 $19)
       %435))) ((%9 ((%145 ((%64 $23) %71)) ((%31 $18) %449))) ((%9 ((%145
       ((%64 $23) %72)) ((%31 $17) %450))) ((%9 ((%145 ((%64 $23) %73))
       ((%31 $16) %451))) ((%9 ((%145 ((%64 $23) %74)) ((%31 $15) %452)))
       ((%9 ((%145 ((%64 $23) %75)) ((%31 $14) %453))) ((%9 ((%145 ((%64
       $23) %76)) ((%31 $13) %454))) ((%9 ((%145 ((%64 $23) %77)) ((%31
       $12) %455))) ((%9 ((%145 ((%64 $23) %78)) ((%31 $11) %456))) ((%9
       ((%145 ((%64 $23) %79)) ((%31 $10) %457))) ((%9 ((%145 ((%64 $23)
       %80)) ((%31 $9) %458))) ((%9 ((%145 ((%64 $23) %81)) ((%31 $8)
       %459))) ((%9 ((%145 ((%64 $23) %82)) ((%31 $7) %460))) ((%9 ((%145
       ((%64 $23) %83)) ((%31 $6) %461))) ((%9 ((%145 ((%64 $23) %84))
       ((%31 $5) %462))) ((%9 ((%145 ((%64 $23) %85)) ((%31 $4) %463)))
       ((%9 ((%145 ((%64 $23) %86)) ((%31 $3) %464))) ((%9 ((%145 ((%64
       $23) %87)) ((%31 $2) %465))) ((%9 ((%145 ((%64 $23) %88)) ((%31 $1)
       %466))) ((%145 ((%64 $23) %89)) ((%31 $0)
       %467)))))))))))))))))))))))))) ((%31 ((((((((((((((((((((((((%111
       $22) $21) $20) $19) $18) $17) $16) $15) $14) $13) $12) $11) $10) $9)
       $8) $7) $6) $5) $4) $3) $2) $1) $0) $24))
       ((((((((((((((((((((((((%111 %432) %433) %434) %435) %449) %450)
       %451) %452) %453) %454) %455) %456) %457) %458) %459) %460) %461)
       %462) %463) %464) %465) %466) %467)
       $23)))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val OPERATOR_nchotomy =
    DT(["DISK_THM"], [],
       `(%62 (\%63. ((%58 ((%64 $0) %67)) ((%58 ((%64 $0) %68)) ((%58 ((%64
       $0) %69)) ((%58 ((%64 $0) %70)) ((%58 ((%64 $0) %71)) ((%58 ((%64
       $0) %72)) ((%58 ((%64 $0) %73)) ((%58 ((%64 $0) %74)) ((%58 ((%64
       $0) %75)) ((%58 ((%64 $0) %76)) ((%58 ((%64 $0) %77)) ((%58 ((%64
       $0) %78)) ((%58 ((%64 $0) %79)) ((%58 ((%64 $0) %80)) ((%58 ((%64
       $0) %81)) ((%58 ((%64 $0) %82)) ((%58 ((%64 $0) %83)) ((%58 ((%64
       $0) %84)) ((%58 ((%64 $0) %85)) ((%58 ((%64 $0) %86)) ((%58 ((%64
       $0) %87)) ((%58 ((%64 $0) %88)) ((%64 $0)
       %89)))))))))))))))))))))))))`)
  val OPERATOR_Axiom =
    DT(["DISK_THM"], [],
       `(%26 (\%436. (%26 (\%437. (%26 (\%438. (%26 (\%439. (%26 (\%468.
       (%26 (\%469. (%26 (\%470. (%26 (\%471. (%26 (\%472. (%26 (\%473.
       (%26 (\%474. (%26 (\%475. (%26 (\%476. (%26 (\%477. (%26 (\%478.
       (%26 (\%479. (%26 (\%480. (%26 (\%481. (%26 (\%482. (%26 (\%483.
       (%26 (\%484. (%26 (\%485. (%26 (\%486. (%487 (\%488. ((%9 ((%31 ($0
       %67)) $23)) ((%9 ((%31 ($0 %68)) $22)) ((%9 ((%31 ($0 %69)) $21))
       ((%9 ((%31 ($0 %70)) $20)) ((%9 ((%31 ($0 %71)) $19)) ((%9 ((%31 ($0
       %72)) $18)) ((%9 ((%31 ($0 %73)) $17)) ((%9 ((%31 ($0 %74)) $16))
       ((%9 ((%31 ($0 %75)) $15)) ((%9 ((%31 ($0 %76)) $14)) ((%9 ((%31 ($0
       %77)) $13)) ((%9 ((%31 ($0 %78)) $12)) ((%9 ((%31 ($0 %79)) $11))
       ((%9 ((%31 ($0 %80)) $10)) ((%9 ((%31 ($0 %81)) $9)) ((%9 ((%31 ($0
       %82)) $8)) ((%9 ((%31 ($0 %83)) $7)) ((%9 ((%31 ($0 %84)) $6)) ((%9
       ((%31 ($0 %85)) $5)) ((%9 ((%31 ($0 %86)) $4)) ((%9 ((%31 ($0 %87))
       $3)) ((%9 ((%31 ($0 %88)) $2)) ((%31 ($0 %89))
       $1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val OPERATOR_induction =
    DT(["DISK_THM"], [],
       `(%489 (\%490. ((%145 ((%9 ($0 %68)) ((%9 ($0 %73)) ((%9 ($0 %80))
       ((%9 ($0 %88)) ((%9 ($0 %89)) ((%9 ($0 %76)) ((%9 ($0 %75)) ((%9 ($0
       %84)) ((%9 ($0 %82)) ((%9 ($0 %78)) ((%9 ($0 %79)) ((%9 ($0 %72))
       ((%9 ($0 %67)) ((%9 ($0 %86)) ((%9 ($0 %87)) ((%9 ($0 %71)) ((%9 ($0
       %74)) ((%9 ($0 %81)) ((%9 ($0 %70)) ((%9 ($0 %85)) ((%9 ($0 %83))
       ((%9 ($0 %69)) ($0 %77)))))))))))))))))))))))) (%62 (\%63. ($1
       $0))))))`)
  val num2COND_COND2num =
    DT(["DISK_THM"], [], `(%115 (\%116. ((%117 (%118 (%119 $0))) $0)))`)
  val COND2num_num2COND =
    DT(["DISK_THM"], [],
       `(%15 (\%16. ((%17 ((%4 $0) (%5 (%6 (%7 (%7 (%7 %8))))))) ((%18
       (%119 (%118 $0))) $0))))`)
  val num2COND_11 =
    DT(["DISK_THM"], [],
       `(%15 (\%16. (%15 (\%258. ((%145 ((%4 $1) (%5 (%6 (%7 (%7 (%7
       %8))))))) ((%145 ((%4 $0) (%5 (%6 (%7 (%7 (%7 %8))))))) ((%17 ((%117
       (%118 $1)) (%118 $0))) ((%18 $1) $0))))))))`)
  val COND2num_11 =
    DT(["DISK_THM"], [],
       `(%115 (\%116. (%115 (\%491. ((%17 ((%18 (%119 $1)) (%119 $0)))
       ((%117 $1) $0))))))`)
  val num2COND_ONTO =
    DT(["DISK_THM"], [],
       `(%115 (\%116. (%147 (\%16. ((%9 ((%117 $1) (%118 $0))) ((%4 $0) (%5
       (%6 (%7 (%7 (%7 %8)))))))))))`)
  val COND2num_ONTO =
    DT(["DISK_THM"], [],
       `(%15 (\%16. ((%17 ((%4 $0) (%5 (%6 (%7 (%7 (%7 %8))))))) (%492
       (\%116. ((%18 $1) (%119 $0)))))))`)
  val num2COND_thm =
    DT([], [],
       `((%9 ((%117 (%118 %20)) %120)) ((%9 ((%117 (%118 (%5 (%7 %8))))
       %121)) ((%9 ((%117 (%118 (%5 (%6 %8)))) %122)) ((%9 ((%117 (%118 (%5
       (%7 (%7 %8))))) %123)) ((%9 ((%117 (%118 (%5 (%6 (%7 %8))))) %124))
       ((%9 ((%117 (%118 (%5 (%7 (%6 %8))))) %125)) ((%9 ((%117 (%118 (%5
       (%6 (%6 %8))))) %126)) ((%9 ((%117 (%118 (%5 (%7 (%7 (%7 %8))))))
       %127)) ((%9 ((%117 (%118 (%5 (%6 (%7 (%7 %8)))))) %128)) ((%9 ((%117
       (%118 (%5 (%7 (%6 (%7 %8)))))) %129)) ((%9 ((%117 (%118 (%5 (%6 (%6
       (%7 %8)))))) %130)) ((%9 ((%117 (%118 (%5 (%7 (%7 (%6 %8))))))
       %131)) ((%9 ((%117 (%118 (%5 (%6 (%7 (%6 %8)))))) %132)) ((%9 ((%117
       (%118 (%5 (%7 (%6 (%6 %8)))))) %133)) ((%9 ((%117 (%118 (%5 (%6 (%6
       (%6 %8)))))) %134)) ((%117 (%118 (%5 (%7 (%7 (%7 (%7 %8)))))))
       %135))))))))))))))))`)
  val COND2num_thm =
    DT(["DISK_THM"], [],
       `((%9 ((%18 (%119 %120)) %20)) ((%9 ((%18 (%119 %121)) (%5 (%7
       %8)))) ((%9 ((%18 (%119 %122)) (%5 (%6 %8)))) ((%9 ((%18 (%119
       %123)) (%5 (%7 (%7 %8))))) ((%9 ((%18 (%119 %124)) (%5 (%6 (%7
       %8))))) ((%9 ((%18 (%119 %125)) (%5 (%7 (%6 %8))))) ((%9 ((%18 (%119
       %126)) (%5 (%6 (%6 %8))))) ((%9 ((%18 (%119 %127)) (%5 (%7 (%7 (%7
       %8)))))) ((%9 ((%18 (%119 %128)) (%5 (%6 (%7 (%7 %8)))))) ((%9 ((%18
       (%119 %129)) (%5 (%7 (%6 (%7 %8)))))) ((%9 ((%18 (%119 %130)) (%5
       (%6 (%6 (%7 %8)))))) ((%9 ((%18 (%119 %131)) (%5 (%7 (%7 (%6
       %8)))))) ((%9 ((%18 (%119 %132)) (%5 (%6 (%7 (%6 %8)))))) ((%9 ((%18
       (%119 %133)) (%5 (%7 (%6 (%6 %8)))))) ((%9 ((%18 (%119 %134)) (%5
       (%6 (%6 (%6 %8)))))) ((%18 (%119 %135)) (%5 (%7 (%7 (%7 (%7
       %8)))))))))))))))))))))`)
  val COND_EQ_COND =
    DT(["DISK_THM"], [],
       `(%115 (\%116. (%115 (\%491. ((%17 ((%117 $1) $0)) ((%18 (%119 $1))
       (%119 $0)))))))`)
  val COND_case_def =
    DT(["DISK_THM"], [],
       `((%9 (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92.
       (%26 (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26
       (\%98. (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26
       (\%103. ((%31 (((((((((((((((((%138 $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %120))
       $15)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27. (%26 (\%28.
       (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26 (\%94. (%26
       (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99. (%26 (\%100.
       (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31 (((((((((((((((((%138
       $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1)
       $0) %121)) $14)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31
       (((((((((((((((((%138 $15) $14) $13) $12) $11) $10) $9) $8) $7) $6)
       $5) $4) $3) $2) $1) $0) %122)) $13))))))))))))))))))))))))))))))))))
       ((%9 (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92.
       (%26 (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26
       (\%98. (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26
       (\%103. ((%31 (((((((((((((((((%138 $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %123))
       $12)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27. (%26 (\%28.
       (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26 (\%94. (%26
       (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99. (%26 (\%100.
       (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31 (((((((((((((((((%138
       $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1)
       $0) %124)) $11)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31
       (((((((((((((((((%138 $15) $14) $13) $12) $11) $10) $9) $8) $7) $6)
       $5) $4) $3) $2) $1) $0) %125)) $10))))))))))))))))))))))))))))))))))
       ((%9 (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92.
       (%26 (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26
       (\%98. (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26
       (\%103. ((%31 (((((((((((((((((%138 $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %126))
       $9)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27. (%26 (\%28.
       (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26 (\%94. (%26
       (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99. (%26 (\%100.
       (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31 (((((((((((((((((%138
       $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1)
       $0) %127)) $8)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31
       (((((((((((((((((%138 $15) $14) $13) $12) $11) $10) $9) $8) $7) $6)
       $5) $4) $3) $2) $1) $0) %128)) $7))))))))))))))))))))))))))))))))))
       ((%9 (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92.
       (%26 (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26
       (\%98. (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26
       (\%103. ((%31 (((((((((((((((((%138 $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %129))
       $6)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27. (%26 (\%28.
       (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26 (\%94. (%26
       (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99. (%26 (\%100.
       (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31 (((((((((((((((((%138
       $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1)
       $0) %130)) $5)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31
       (((((((((((((((((%138 $15) $14) $13) $12) $11) $10) $9) $8) $7) $6)
       $5) $4) $3) $2) $1) $0) %131)) $4))))))))))))))))))))))))))))))))))
       ((%9 (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92.
       (%26 (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26
       (\%98. (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26
       (\%103. ((%31 (((((((((((((((((%138 $15) $14) $13) $12) $11) $10)
       $9) $8) $7) $6) $5) $4) $3) $2) $1) $0) %132))
       $3)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27. (%26 (\%28.
       (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26 (\%94. (%26
       (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99. (%26 (\%100.
       (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31 (((((((((((((((((%138
       $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1)
       $0) %133)) $2)))))))))))))))))))))))))))))))))) ((%9 (%26 (\%27.
       (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26
       (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99.
       (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103. ((%31
       (((((((((((((((((%138 $15) $14) $13) $12) $11) $10) $9) $8) $7) $6)
       $5) $4) $3) $2) $1) $0) %134)) $1))))))))))))))))))))))))))))))))))
       (%26 (\%27. (%26 (\%28. (%26 (\%29. (%26 (\%30. (%26 (\%92. (%26
       (\%93. (%26 (\%94. (%26 (\%95. (%26 (\%96. (%26 (\%97. (%26 (\%98.
       (%26 (\%99. (%26 (\%100. (%26 (\%101. (%26 (\%102. (%26 (\%103.
       ((%31 (((((((((((((((((%138 $15) $14) $13) $12) $11) $10) $9) $8)
       $7) $6) $5) $4) $3) $2) $1) $0) %135))
       $0))))))))))))))))))))))))))))))))))))))))))))))))`)
  val datatype_COND =
    DT(["DISK_THM"], [],
       `(%428 ((((((((((((((((%493 %120) %121) %122) %123) %124) %125)
       %126) %127) %128) %129) %130) %131) %132) %133) %134) %135))`)
  val COND_case_cong =
    DT(["DISK_THM"], [],
       `(%115 (\%494. (%115 (\%495. (%26 (\%27. (%26 (\%28. (%26 (\%29.
       (%26 (\%30. (%26 (\%92. (%26 (\%93. (%26 (\%94. (%26 (\%95. (%26
       (\%96. (%26 (\%97. (%26 (\%98. (%26 (\%99. (%26 (\%100. (%26 (\%101.
       (%26 (\%102. (%26 (\%103. ((%145 ((%9 ((%117 $17) $16)) ((%9 ((%145
       ((%117 $16) %120)) ((%31 $15) %432))) ((%9 ((%145 ((%117 $16) %121))
       ((%31 $14) %433))) ((%9 ((%145 ((%117 $16) %122)) ((%31 $13) %434)))
       ((%9 ((%145 ((%117 $16) %123)) ((%31 $12) %435))) ((%9 ((%145 ((%117
       $16) %124)) ((%31 $11) %449))) ((%9 ((%145 ((%117 $16) %125)) ((%31
       $10) %450))) ((%9 ((%145 ((%117 $16) %126)) ((%31 $9) %451))) ((%9
       ((%145 ((%117 $16) %127)) ((%31 $8) %452))) ((%9 ((%145 ((%117 $16)
       %128)) ((%31 $7) %453))) ((%9 ((%145 ((%117 $16) %129)) ((%31 $6)
       %454))) ((%9 ((%145 ((%117 $16) %130)) ((%31 $5) %455))) ((%9 ((%145
       ((%117 $16) %131)) ((%31 $4) %456))) ((%9 ((%145 ((%117 $16) %132))
       ((%31 $3) %457))) ((%9 ((%145 ((%117 $16) %133)) ((%31 $2) %458)))
       ((%9 ((%145 ((%117 $16) %134)) ((%31 $1) %459))) ((%145 ((%117 $16)
       %135)) ((%31 $0) %460))))))))))))))))))) ((%31 (((((((((((((((((%138
       $15) $14) $13) $12) $11) $10) $9) $8) $7) $6) $5) $4) $3) $2) $1)
       $0) $17)) (((((((((((((((((%138 %432) %433) %434) %435) %449) %450)
       %451) %452) %453) %454) %455) %456) %457) %458) %459) %460)
       $16)))))))))))))))))))))))))))))))))))))))`)
  val COND_nchotomy =
    DT(["DISK_THM"], [],
       `(%115 (\%116. ((%58 ((%117 $0) %120)) ((%58 ((%117 $0) %121)) ((%58
       ((%117 $0) %122)) ((%58 ((%117 $0) %123)) ((%58 ((%117 $0) %124))
       ((%58 ((%117 $0) %125)) ((%58 ((%117 $0) %126)) ((%58 ((%117 $0)
       %127)) ((%58 ((%117 $0) %128)) ((%58 ((%117 $0) %129)) ((%58 ((%117
       $0) %130)) ((%58 ((%117 $0) %131)) ((%58 ((%117 $0) %132)) ((%58
       ((%117 $0) %133)) ((%58 ((%117 $0) %134)) ((%117 $0)
       %135))))))))))))))))))`)
  val COND_Axiom =
    DT(["DISK_THM"], [],
       `(%26 (\%436. (%26 (\%437. (%26 (\%438. (%26 (\%439. (%26 (\%468.
       (%26 (\%469. (%26 (\%470. (%26 (\%471. (%26 (\%472. (%26 (\%473.
       (%26 (\%474. (%26 (\%475. (%26 (\%476. (%26 (\%477. (%26 (\%478.
       (%26 (\%479. (%496 (\%497. ((%9 ((%31 ($0 %120)) $16)) ((%9 ((%31
       ($0 %121)) $15)) ((%9 ((%31 ($0 %122)) $14)) ((%9 ((%31 ($0 %123))
       $13)) ((%9 ((%31 ($0 %124)) $12)) ((%9 ((%31 ($0 %125)) $11)) ((%9
       ((%31 ($0 %126)) $10)) ((%9 ((%31 ($0 %127)) $9)) ((%9 ((%31 ($0
       %128)) $8)) ((%9 ((%31 ($0 %129)) $7)) ((%9 ((%31 ($0 %130)) $6))
       ((%9 ((%31 ($0 %131)) $5)) ((%9 ((%31 ($0 %132)) $4)) ((%9 ((%31 ($0
       %133)) $3)) ((%9 ((%31 ($0 %134)) $2)) ((%31 ($0 %135))
       $1))))))))))))))))))))))))))))))))))))))))))))))))))`)
  val COND_induction =
    DT(["DISK_THM"], [],
       `(%498 (\%499. ((%145 ((%9 ($0 %127)) ((%9 ($0 %129)) ((%9 ($0
       %121)) ((%9 ($0 %120)) ((%9 ($0 %125)) ((%9 ($0 %126)) ((%9 ($0
       %124)) ((%9 ($0 %134)) ((%9 ($0 %132)) ((%9 ($0 %133)) ((%9 ($0
       %122)) ((%9 ($0 %128)) ((%9 ($0 %135)) ((%9 ($0 %130)) ((%9 ($0
       %131)) ($0 %123))))))))))))))))) (%115 (\%116. ($1 $0))))))`)
  val datatype_OFFSET = DT(["DISK_THM"], [], `(%428 ((%500 %162) %163))`)
  val OFFSET_11 =
    DT(["DISK_THM"], [],
       `((%9 (%15 (\%148. (%15 (\%501. ((%17 ((%155 (%162 $1)) (%162 $0)))
       ((%18 $1) $0))))))) (%15 (\%148. (%15 (\%501. ((%17 ((%155 (%163
       $1)) (%163 $0))) ((%18 $1) $0)))))))`)
  val OFFSET_distinct =
    DT(["DISK_THM"], [],
       `(%15 (\%501. (%15 (\%148. (%305 ((%155 (%162 $0)) (%163 $1)))))))`)
  val OFFSET_case_cong =
    DT(["DISK_THM"], [],
       `(%153 (\%502. (%153 (\%503. (%164 (\%165. (%164 (\%166. ((%145 ((%9
       ((%155 $3) $2)) ((%9 (%15 (\%148. ((%145 ((%155 $3) (%162 $0)))
       ((%31 ($2 $0)) (%504 $0)))))) (%15 (\%148. ((%145 ((%155 $3) (%163
       $0))) ((%31 ($1 $0)) (%505 $0)))))))) ((%31 (((%167 $1) $0) $3))
       (((%167 %504) %505) $2)))))))))))`)
  val OFFSET_nchotomy =
    DT(["DISK_THM"], [],
       `(%153 (\%506. ((%58 (%147 (\%3. ((%155 $1) (%162 $0))))) (%147
       (\%3. ((%155 $1) (%163 $0)))))))`)
  val OFFSET_Axiom =
    DT(["DISK_THM"], [],
       `(%164 (\%507. (%164 (\%166. (%508 (\%509. ((%9 (%15 (\%148. ((%31
       ($1 (%162 $0))) ($3 $0))))) (%15 (\%148. ((%31 ($1 (%163 $0))) ($2
       $0)))))))))))`)
  val OFFSET_induction =
    DT(["DISK_THM"], [],
       `(%510 (\%511. ((%145 ((%9 (%15 (\%3. ($1 (%162 $0))))) (%15 (\%3.
       ($1 (%163 $0)))))) (%153 (\%506. ($1 $0))))))`)
  val datatype_EXP =
    DT(["DISK_THM"], [], `(%428 (((((%512 %207) %208) %209) %210) %211))`)
  val EXP_11 =
    DT(["DISK_THM"], [],
       `((%9 (%218 (\%178. (%218 (\%513. ((%17 ((%195 (%207 $1)) (%207
       $0))) ((%514 $1) $0))))))) ((%9 (%15 (\%148. (%15 (\%501. ((%17
       ((%195 (%208 $1)) (%208 $0))) ((%18 $1) $0))))))) ((%9 (%35 (\%192.
       (%35 (\%515. ((%17 ((%195 (%209 $1)) (%209 $0))) ((%41 $1) $0)))))))
       ((%9 (%15 (\%148. (%15 (\%501. ((%17 ((%195 (%210 $1)) (%210 $0)))
       ((%18 $1) $0))))))) (%15 (\%148. (%15 (\%501. ((%17 ((%195 (%211
       $1)) (%211 $0))) ((%18 $1) $0))))))))))`)
  val EXP_distinct =
    DT(["DISK_THM"], [],
       `((%9 (%15 (\%501. (%218 (\%178. (%305 ((%195 (%207 $0)) (%208
       $1)))))))) ((%9 (%35 (\%515. (%218 (\%178. (%305 ((%195 (%207 $0))
       (%209 $1)))))))) ((%9 (%15 (\%501. (%218 (\%178. (%305 ((%195 (%207
       $0)) (%210 $1)))))))) ((%9 (%15 (\%501. (%218 (\%178. (%305 ((%195
       (%207 $0)) (%211 $1)))))))) ((%9 (%35 (\%515. (%15 (\%148. (%305
       ((%195 (%208 $0)) (%209 $1)))))))) ((%9 (%15 (\%501. (%15 (\%148.
       (%305 ((%195 (%208 $0)) (%210 $1)))))))) ((%9 (%15 (\%501. (%15
       (\%148. (%305 ((%195 (%208 $0)) (%211 $1)))))))) ((%9 (%15 (\%501.
       (%35 (\%192. (%305 ((%195 (%209 $0)) (%210 $1)))))))) ((%9 (%15
       (\%501. (%35 (\%192. (%305 ((%195 (%209 $0)) (%211 $1)))))))) (%15
       (\%501. (%15 (\%148. (%305 ((%195 (%210 $0)) (%211
       $1))))))))))))))))`)
  val EXP_case_cong =
    DT(["DISK_THM"], [],
       `(%193 (\%516. (%193 (\%517. (%212 (\%213. (%164 (\%166. (%214
       (\%215. (%164 (\%216. (%164 (\%217. ((%145 ((%9 ((%195 $6) $5)) ((%9
       (%218 (\%178. ((%145 ((%195 $6) (%207 $0))) ((%31 ($5 $0)) (%518
       $0)))))) ((%9 (%15 (\%148. ((%145 ((%195 $6) (%208 $0))) ((%31 ($4
       $0)) (%505 $0)))))) ((%9 (%35 (\%192. ((%145 ((%195 $6) (%209 $0)))
       ((%31 ($3 $0)) (%519 $0)))))) ((%9 (%15 (\%148. ((%145 ((%195 $6)
       (%210 $0))) ((%31 ($2 $0)) (%520 $0)))))) (%15 (\%148. ((%145 ((%195
       $6) (%211 $0))) ((%31 ($1 $0)) (%521 $0))))))))))) ((%31 ((((((%219
       $4) $3) $2) $1) $0) $6)) ((((((%219 %518) %505) %519) %520) %521)
       $5)))))))))))))))))`)
  val EXP_nchotomy =
    DT(["DISK_THM"], [],
       `(%193 (\%522. ((%58 (%177 (\%523. ((%195 $1) (%207 $0))))) ((%58
       (%147 (\%3. ((%195 $1) (%208 $0))))) ((%58 (%191 (\%524. ((%195 $1)
       (%209 $0))))) ((%58 (%147 (\%3. ((%195 $1) (%210 $0))))) (%147 (\%3.
       ((%195 $1) (%211 $0))))))))))`)
  val EXP_Axiom =
    DT(["DISK_THM"], [],
       `(%212 (\%525. (%164 (\%166. (%214 (\%215. (%164 (\%216. (%164
       (\%217. (%526 (\%527. ((%9 (%218 (\%178. ((%31 ($1 (%207 $0))) ($6
       $0))))) ((%9 (%15 (\%148. ((%31 ($1 (%208 $0))) ($5 $0))))) ((%9
       (%35 (\%192. ((%31 ($1 (%209 $0))) ($4 $0))))) ((%9 (%15 (\%148.
       ((%31 ($1 (%210 $0))) ($3 $0))))) (%15 (\%148. ((%31 ($1 (%211 $0)))
       ($2 $0))))))))))))))))))))`)
  val EXP_induction =
    DT(["DISK_THM"], [],
       `(%528 (\%529. ((%145 ((%9 (%218 (\%523. ($1 (%207 $0))))) ((%9 (%15
       (\%3. ($1 (%208 $0))))) ((%9 (%35 (\%524. ($1 (%209 $0))))) ((%9
       (%15 (\%3. ($1 (%210 $0))))) (%15 (\%3. ($1 (%211 $0))))))))) (%193
       (\%522. ($1 $0))))))`)
  val FORALL_DSTATE =
    DT(["DISK_THM"], [],
       `((%17 (%277 (\%278. (%530 $0)))) (%229 (\%230. (%229 (\%231. (%530
       ((%234 $1) $0)))))))`)
  val FORALL_STATE =
    DT(["DISK_THM"], [],
       `((%17 (%388 (\%403. (%370 $0)))) (%15 (\%269. (%35 (\%531. (%229
       (\%230. (%229 (\%231. (%370 ((%287 $3) ((%288 $2) ((%234 $1)
       $0)))))))))))))`)
  val read_thm =
    DT(["DISK_THM"], [],
       `((%9 ((%41 ((%233 ((%234 %230) %231)) (%207 ((%321 %16) (%162
       %240))))) ((%241 %231) ((%169 (%242 ((%241 %230) %16))) %240))))
       ((%9 ((%41 ((%233 ((%234 %230) %231)) (%207 ((%321 %16) (%163
       %240))))) ((%241 %231) ((%244 (%242 ((%241 %230) %16))) %240))))
       ((%9 ((%41 ((%233 ((%234 %230) %231)) (%208 %56))) (%45 %56))) ((%9
       ((%41 ((%233 ((%234 %230) %231)) (%209 %245))) %245)) ((%41 ((%233
       ((%234 %230) %231)) (%210 %16))) ((%241 %230) %16))))))`)
  val write_thm =
    DT(["DISK_THM"], [],
       `((%9 ((%248 (((%249 ((%234 %230) %231)) (%207 ((%321 %16) (%162
       %240)))) %187)) ((%234 %230) ((%255 %231) ((%182 ((%169 (%242 ((%241
       %230) %16))) %240)) %187))))) ((%9 ((%248 (((%249 ((%234 %230)
       %231)) (%207 ((%321 %16) (%163 %240)))) %187)) ((%234 %230) ((%255
       %231) ((%182 ((%244 (%242 ((%241 %230) %16))) %240)) %187)))))
       ((%248 (((%249 ((%234 %230) %231)) (%210 %16)) %187)) ((%234 ((%255
       %230) ((%182 %16) %187))) %231))))`)
  val goto_ind =
    DT(["DISK_THM"], [],
       `(%532 (\%533. ((%145 ((%9 (%15 (\%269. ($1 ((%342 $0) %534)))))
       (%15 (\%269. (%153 (\%273. ($2 ((%342 $1) (%535 $0))))))))) (%15
       (\%184. (%328 (\%270. ($2 ((%342 $1) $0)))))))))`)
  val goto_def =
    DT(["DISK_THM"], [],
       `((%18 (%261 ((%342 %269) (%535 %273)))) (((%275 (\%3. ((%169 %269)
       $0))) (\%276. ((%244 %269) $0))) %273))`)
  val goto_thm =
    DT(["DISK_THM"], [],
       `((%9 ((%18 (%261 ((%342 %269) (%535 (%162 %3))))) ((%169 %269)
       %3))) ((%18 (%261 ((%342 %269) (%535 (%163 %3))))) ((%244 %269)
       %3)))`)
  val decode_op_thm =
    DT(["DISK_THM"], [],
       `(%15 (\%269. (%35 (\%36. (%277 (\%278. (%193 (\%536. (%282 (\%283.
       (%26 (\%284. ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289
       %67) ((%290 (%537 $2)) ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2)
       ((%233 $3) (%294 $1)))))) ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4)
       $3))) ((%289 %68) ((%290 (%537 $2)) ((%291 $1) $0))))) ((%288 $4)
       (((%249 $3) $2) ((%295 ((%233 $3) (%294 $1))) ((%233 $3) (%294 (%296
       $1)))))))) ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289
       %69) ((%290 (%537 $2)) ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2)
       ((%297 ((%233 $3) (%294 $1))) ((%233 $3) (%294 (%296 $1)))))))) ((%9
       ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %70) ((%290 (%537
       $2)) ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2) ((%297 ((%233 $3)
       (%294 (%296 $1)))) ((%233 $3) (%294 $1))))))) ((%9 ((%285 ((%286
       ((%287 $5) ((%288 $4) $3))) ((%289 %71) ((%290 (%537 $2)) ((%291 $1)
       $0))))) ((%288 $4) (((%249 $3) $2) ((%298 ((%233 $3) (%294 $1)))
       ((%233 $3) (%294 (%296 $1)))))))) ((%9 ((%285 ((%286 ((%287 $5)
       ((%288 $4) $3))) ((%289 %72) ((%290 (%537 $2)) ((%291 $1) $0)))))
       ((%288 $4) (((%249 $3) $2) ((%295 ((%298 ((%233 $3) (%294 $1)))
       ((%233 $3) (%294 (%296 $1))))) ((%233 $3) (%294 (%296 (%296
       $1))))))))) ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289
       %73) ((%290 (%537 $2)) ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2)
       ((%299 ((%233 $3) (%294 $1))) ((%233 $3) (%294 (%296 $1)))))))) ((%9
       ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %74) ((%290 (%537
       $2)) ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2) ((%44 ((%233 $3)
       (%294 $1))) ((%233 $3) (%294 (%296 $1)))))))) ((%9 ((%285 ((%286
       ((%287 $5) ((%288 $4) $3))) ((%289 %75) ((%290 (%537 $2)) ((%291 $1)
       $0))))) ((%288 $4) (((%249 $3) $2) ((%300 ((%233 $3) (%294 $1)))
       ((%233 $3) (%294 (%296 $1)))))))) ((%9 ((%285 ((%286 ((%287 $5)
       ((%288 $4) $3))) ((%289 %76) ((%290 %538) ((%291 $1) $0))))) ((%301
       (\%192. ((%301 (\%302. ((%288 ((%51 $6) ((%52 (%303 ((%297 $1) $0)))
       ((%53 ((%41 $1) $0)) ((%54 ((%304 $0) $1)) ((%9 (%305 ((%17 (%303
       $1)) (%303 $0)))) (%305 ((%17 (%303 $1)) (%303 ((%297 $1)
       $0)))))))))) $5))) ((%233 $4) (%294 (%296 $2)))))) ((%233 $3) (%294
       $1))))) ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %77)
       ((%290 %538) ((%291 $1) $0))))) ((%301 (\%192. ((%301 (\%302. ((%288
       ((%51 $6) ((%52 (%303 ((%299 $1) $0))) ((%53 ((%41 ((%299 $1) $0))
       (%45 %20))) ((%54 %306) ((%40 $6) (%5 (%6 (%7 (%6 (%6 %8)))))))))))
       $5))) ((%233 $4) (%294 (%296 $2)))))) ((%233 $3) (%294 $1))))) ((%9
       ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %78) ((%290 (%537
       $2)) ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2) ((%307 ((%233 $3)
       (%294 $1))) (%242 ((%233 $3) (%294 (%296 $1))))))))) ((%9 ((%285
       ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %79) ((%290 (%537 $2))
       ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2) ((%308 ((%233 $3)
       (%294 $1))) (%242 ((%233 $3) (%294 (%296 $1))))))))) ((%9 ((%285
       ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %80) ((%290 (%537 $2))
       ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2) ((%309 ((%233 $3)
       (%294 $1))) (%242 ((%233 $3) (%294 (%296 $1))))))))) ((%9 ((%285
       ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %81) ((%290 (%537 $2))
       ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2) ((%310 ((%233 $3)
       (%294 $1))) (%242 ((%233 $3) (%294 (%296 $1))))))))) ((%9 ((%285
       ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %82) ((%290 (%537 $2))
       ((%291 $1) $0))))) ((%288 $4) (((%249 $3) $2) ((%233 $3) (%294
       $1)))))) ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %83)
       ((%290 (%537 $2)) ((%291 $1) $0))))) ((%288 $4) (((%249 $3) (%294
       $1)) ((%233 $3) $2))))) ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4)
       $3))) ((%289 %84) ((%290 (%537 (%210 %16))) ((%291 $1) $0)))))
       ((%288 $4) (%315 (((%316 (%317 (\%318. (\%56. (\%319. ((%320 (((%249
       $2) $0) ((%233 $6) (%207 ((%321 %16) (%162 ((%169 $1) (%5 (%7
       %8))))))))) ((%169 $1) (%5 (%7 %8))))))))) ((%320 $3) %20)) $1)))))
       ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %84) ((%290
       (%537 (%211 %16))) ((%291 $1) $0))))) ((%288 $4) (((%249 (%315
       (((%316 (%317 (\%318. (\%56. (\%319. ((%320 (((%249 $2) $0) ((%233
       $6) (%207 ((%321 %16) (%162 ((%169 $1) (%5 (%7 %8))))))))) ((%169
       $1) (%5 (%7 %8))))))))) ((%320 $3) %20)) $1))) (%210 %16)) ((%295
       ((%233 $3) (%210 %16))) (%45 (%322 $1))))))) ((%9 ((%285 ((%286
       ((%287 $5) ((%288 $4) $3))) ((%289 %85) ((%290 (%537 (%210 %16)))
       ((%291 $1) $0))))) ((%288 $4) (%315 (((%316 (%317 (\%318. (\%56.
       (\%319. ((%320 (((%249 $2) (%207 ((%321 %16) (%163 $1)))) ((%233 $6)
       $0))) ((%169 $1) (%5 (%7 %8))))))))) ((%320 $3) %20)) (%323 $1))))))
       ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %85) ((%290
       (%537 (%211 %16))) ((%291 $1) $0))))) ((%288 $4) (((%249 (%315
       (((%316 (%317 (\%318. (\%56. (\%319. ((%320 (((%249 $2) (%207 ((%321
       %16) (%163 $1)))) ((%233 $6) $0))) ((%169 $1) (%5 (%7 %8)))))))))
       ((%320 $3) %20)) (%323 $1)))) (%210 %16)) ((%297 ((%233 $3) (%210
       %16))) (%45 (%322 $1))))))) ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4)
       $3))) ((%289 %86) ((%290 (%537 $2)) ((%291 $1) $0))))) ((%288 $4)
       (((%249 $3) $2) $4)))) ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4)
       $3))) ((%289 %87) ((%290 %538) ((%291 $1) $0))))) ((%288 ((%233 $3)
       (%294 $1))) $3))) ((%9 ((%285 ((%286 ((%287 $5) ((%288 $4) $3)))
       ((%289 %88) ((%290 %538) ((%291 $1) $0))))) ((%288 $4) $3))) ((%285
       ((%286 ((%287 $5) ((%288 $4) $3))) ((%289 %89) ((%290 %538) ((%291
       $1) $0))))) ((%288 $4) (((%249 $3) (%210 (%5 (%6 (%6 (%6 %8))))))
       (%45 (%152 $5)))))))))))))))))))))))))))))))))))))))))`)
  val decode_cond_thm =
    DT(["DISK_THM"], [],
       `(%15 (\%269. (%35 (\%36. (%277 (\%278. (%62 (\%279. (%46 (\%327.
       (%280 (\%281. (%282 (\%283. (%328 (\%329. ((%9 ((%330 ((%331 ((%287
       $7) ((%288 $6) $5))) ((%332 ((%333 $4) ((%334 %539) $3))) ((%335 $2)
       ((%336 $1) $0))))) ((%287 ((%169 $7) (%5 (%7 %8)))) ((%338 ((%287
       $7) ((%288 $6) $5))) ((%339 $4) ((%335 $2) ((%336 $1) $0))))))) ((%9
       ((%330 ((%331 ((%287 $7) ((%288 $6) $5))) ((%332 ((%333 $4) ((%334
       (%540 %127)) $3))) ((%335 $2) ((%336 $1) $0))))) ((%287 (%261 ((%342
       $7) $0))) ((%338 ((%287 $7) ((%288 $6) $5))) ((%339 $4) ((%335 $2)
       ((%336 $1) $0))))))) ((%330 ((%331 ((%287 $7) ((%288 $6) $5)))
       ((%332 ((%333 $4) ((%334 (%540 %135)) $3))) ((%335 $2) ((%336 $1)
       $0))))) ((%287 ((%169 $7) (%5 (%7 %8)))) ((%288 $6)
       $5)))))))))))))))))))))`)
  val UPLOAD_NOT_AFFECT_LOWER =
    DT(["DISK_THM"], [],
       `(%344 (\%353. (%164 (\%346. (%15 (\%347. (%15 (\%3. ((%145 ((%4 $0)
       $1)) ((%31 ((((%349 $3) $2) $1) $0)) ($2 $0)))))))))))`)
  val UPLOAD_LEM =
    DT(["DISK_THM"], [],
       `(%344 (\%353. (%164 (\%346. (%15 (\%347. (%15 (\%3. ((%145 ((%4 $0)
       (%541 $3))) ((%31 ((((%349 $3) $2) $1) ((%169 $1) $0))) ((%542 $0)
       $3)))))))))))`)
  val UPLOAD_START_POINT_INDEPENDENT =
    DT(["DISK_THM"], [],
       `(%344 (\%353. (%15 (\%543. (%15 (\%544. (%164 (\%346. (%15 (\%351.
       ((%145 ((%4 $0) (%541 $4))) ((%31 ((((%349 $4) $1) $3) ((%169 $3)
       $0))) ((((%349 $4) $1) $2) ((%169 $2) $0))))))))))))))`)
  val UPLOADCODE_LEM =
    DT(["DISK_THM"], [],
       `(%344 (\%353. (%164 (\%346. (%15 (\%3. ((%145 ((%4 $0) (%541 $2)))
       ((%31 (((%354 $2) $1) $0)) ((%542 $0) $2)))))))))`)
  val UPLOADSEG_LEM =
    DT(["DISK_THM"], [],
       `(%15 (\%3. (%355 (\%356. (%164 (\%545. ((%348 (((%357 $2) $1) $0))
       (((%546 ((%547 $2) %20)) (((%349 ((%358 (%548 $2)) $1)) (((%357
       (%548 $2)) $1) $0)) ((%359 (%5 (%6 (%6 (%7 %8))))) (%548 $2))))
       $0))))))))`)
  val run_def =
    DT(["DISK_THM"], [],
       `((%330 ((((%390 %3) %367) %370) ((%287 %269) ((%288 %36) %368))))
       (((%341 ((%18 %3) %20)) ((%287 %269) ((%288 %36) %368))) (((%341
       (%370 ((%287 %269) ((%288 %36) %368)))) ((%287 %269) ((%288 %36)
       %368))) ((((%390 ((%244 %3) (%5 (%7 %8)))) %367) %370) ((%331 ((%287
       %269) ((%288 %36) %368))) (%367 %269))))))`)
  val run_ind =
    DT(["DISK_THM"], [],
       `(%549 (\%550. ((%145 (%15 (\%3. (%366 (\%367. (%369 (\%370. (%15
       (\%269. (%35 (\%36. (%277 (\%368. ((%145 ((%145 ((%9 (%305 ((%18 $5)
       %20))) (%305 ($3 ((%287 $2) ((%288 $1) $0)))))) (((($6 ((%244 $5)
       (%5 (%7 %8)))) $4) $3) ((%331 ((%287 $2) ((%288 $1) $0))) ($4
       $2))))) (((($6 $5) $4) $3) ((%287 $2) ((%288 $1) $0)))))))))))))))))
       (%15 (\%184. (%366 (\%551. (%369 (\%552. (%15 (\%553. (%35 (\%314.
       (%277 (\%554. (((($6 $5) $4) $3) ((%287 $2) ((%288 $1)
       $0))))))))))))))))))`)
  val RUN_LEM_1 =
    DT(["DISK_THM"], [],
       `(%15 (\%3. (%366 (\%367. (%388 (\%403. ((%9 ((%330 ((((%390 (%152
       $2)) $1) %370) $0)) (((%341 (%370 $0)) $0) ((((%390 $2) $1) %370)
       ((%331 $0) ($1 (%406 $0))))))) ((%330 ((((%390 %20) $1) %370) $0))
       $0))))))))`)
  val RUN_LEM_2 =
    DT(["DISK_THM"], [],
       `(%15 (\%3. (%366 (\%367. (%369 (\%370. (%388 (\%403. ((%145 ($1
       $0)) ((%330 ((((%390 $3) $2) $1) $0)) $0))))))))))`)
  val RUN_THM_1 =
    DT(["DISK_THM"], [],
       `(%15 (\%33. (%15 (\%3. (%388 (\%403. (%366 (\%367. ((%330 ((((%390
       ((%169 $3) $2)) $0) %370) $1)) ((((%390 $2) $0) %370) ((((%390 $3)
       $0) %370) $1)))))))))))`)
  val LEAST_ADD_LEM =
    DT(["DISK_THM"], [],
       `(%409 (\%555. (%15 (\%33. ((%145 ((%9 (%147 (\%3. ($2 $0)))) ((%556
       $0) (%399 (\%3. ($2 $0)))))) ((%18 (%399 (\%3. ($2 $0)))) ((%169
       (%399 (\%3. ($2 ((%169 $1) $0))))) $0)))))))`)
  val FUNPOW_THM_1 =
    DT(["DISK_THM"], [],
       `((%9 (%393 (\%557. ((%558 ((%397 $0) %20)) (\%395. $0))))) (%559
       (\%560. (%15 (\%3. ((%561 ((%562 $1) (%152 $0))) ((%563 $1) ((%562
       $1) $0))))))))`)
  val FUNPOW_THM_2 =
    DT(["DISK_THM"], [],
       `((%9 (%393 (\%557. ((%558 ((%397 $0) %20)) (\%395. $0))))) (%559
       (\%560. (%15 (\%3. ((%561 ((%562 $1) (%152 $0))) ((%563 ((%562 $1)
       $0)) $1)))))))`)
  val FUNPOW_FUNPOW =
    DT(["DISK_THM"], [],
       `(%393 (\%557. (%15 (\%33. (%15 (\%3. ((%558 ((%564 ((%397 $2) $1))
       ((%397 $2) $0))) ((%397 $2) ((%169 $1) $0)))))))))`)
  val STOPAT_THM =
    DT(["DISK_THM"], [],
       `(%15 (\%33. (%391 (\%392. (%393 (\%394. (%26 (\%395. ((%145 ((%9
       (((%396 $2) $1) $0)) ((%556 $3) (((%398 $2) $1) $0)))) (((%396 $2)
       $1) (((%397 $1) $3) $0)))))))))))`)
  val SHORTEST_STOP =
    DT(["DISK_THM"], [],
       `(%26 (\%395. (%391 (\%392. (%393 (\%394. ((%145 (((%396 $1) $0)
       $2)) ($1 (((%397 $0) (((%398 $1) $0) $2)) $2)))))))))`)
  val SHORTEST_LEM =
    DT(["DISK_THM"], [],
       `(%26 (\%395. (%391 (\%392. (%393 (\%394. ((%9 ((%145 ($1 $2)) ((%18
       (((%398 $1) $0) $2)) %20))) ((%145 (((%396 $1) $0) $2)) ((%9 ((%145
       ((%18 %20) (((%398 $1) $0) $2))) ($1 $2))) ((%17 (%305 ($1 $2)))
       ((%556 (%5 (%7 %8))) (((%398 $1) $0) $2))))))))))))`)
  val SHORTEST_THM =
    DT(["DISK_THM"], [],
       `(%26 (\%395. (%391 (\%392. (%393 (\%394. (%15 (\%33. ((%145 ((%9
       (((%396 $2) $1) $3)) ((%556 $0) (((%398 $2) $1) $3)))) ((%18 (((%398
       $2) $1) $3)) ((%169 (((%398 $2) $1) (((%397 $1) $0) $3)))
       $0)))))))))))`)
  val SHORTEST_CASES =
    DT(["DISK_THM"], [],
       `(%26 (\%395. (%391 (\%392. (%393 (\%394. ((%145 (((%396 $1) $0)
       $2)) ((%9 ((%145 ($1 $2)) ((%18 (((%398 $1) $0) $2)) %20))) ((%145
       (%305 ($1 $2))) ((%18 (((%398 $1) $0) $2)) (%152 (((%398 $1) $0) ($0
       $2)))))))))))))`)
  val SHORTEST_INDUCTIVE =
    DT(["DISK_THM"], [],
       `(%391 (\%392. (%393 (\%394. (%26 (\%395. (%15 (\%3. ((%145 ((%9
       (((%396 $3) $2) $1)) ((%18 (((%398 $3) $2) $1)) (%152 $0)))) ((%9
       (((%396 $3) $2) ($2 $1))) ((%9 (%305 ($3 $1))) ((%18 $0) (((%398 $3)
       $2) ($2 $1))))))))))))))`)
  val TERD_WHILE_EQ_UNROLL =
    DT(["DISK_THM"], [],
       `(%26 (\%395. (%391 (\%392. (%393 (\%394. ((%145 (((%396 $1) $0)
       $2)) ((%31 (((%565 ((%566 %305) $1)) $0) $2)) (((%397 $0) (((%398
       $1) $0) $2)) $2)))))))))`)
  val UNROLL_ADVANCE =
    DT(["DISK_THM"], [],
       `(%391 (\%392. (%393 (\%394. (%26 (\%395. ((%145 (((%396 $2) $1)
       $0)) ((%31 (((%397 $1) (((%398 $2) $1) $0)) $0)) (((%34 ($2 $0)) $0)
       (((%397 $1) (((%398 $2) $1) ($1 $0))) ($1 $0)))))))))))`)
  val WHILE_STILL =
    DT(["DISK_THM"], [],
       `(%391 (\%392. (%393 (\%394. (%26 (\%395. ((%145 (((%396 $2) $1)
       $0)) ((%31 (((%565 ((%566 %305) $2)) $1) (((%565 ((%566 %305) $2))
       $1) $0))) (((%565 ((%566 %305) $2)) $1) $0)))))))))`)
  val step_FORM1 =
    DT(["DISK_THM"], [],
       `(%366 (\%367. ((%400 (%401 $0)) (\%415. ((%405 ((%331 (%418 $0))
       ($1 (%406 (%418 $0))))) ((%407 (%406 (%418 $0))) (%567 $0)))))))`)
  val STATE_PCS_SEPERATE =
    DT(["DISK_THM"], [],
       `(%15 (\%33. (%409 (\%568. (%409 (\%569. (%366 (\%367. (%388 (\%403.
       ((%330 (%418 (((%570 (%401 $1)) $4) ((%405 $0) $3)))) (%418 (((%570
       (%401 $1)) $4) ((%405 $0) $2))))))))))))))`)
  val STOPAT_ANY_PCS =
    DT(["DISK_THM"], [],
       `(%409 (\%568. (%409 (\%569. (%366 (\%367. (%388 (\%571. (%388
       (\%403. ((%145 (((%417 (\%415. ((%330 (%418 $0)) $2))) (%401 $2))
       ((%405 $0) $4))) (((%417 (\%415. ((%330 (%418 $0)) $2))) (%401 $2))
       ((%405 $0) $3)))))))))))))`)
  val STOPAT_ANY_PCS_2 =
    DT(["DISK_THM"], [],
       `(%409 (\%568. (%409 (\%569. (%366 (\%367. (%15 (\%408. (%388
       (\%403. ((%145 (((%417 (\%415. ((%18 (%406 (%418 $0))) $2))) (%401
       $2)) ((%405 $0) $4))) (((%417 (\%415. ((%18 (%406 (%418 $0))) $2)))
       (%401 $2)) ((%405 $0) $3)))))))))))))`)
  val SHORTEST_INDEPENDENT_OF_PCS =
    DT(["DISK_THM"], [],
       `(%414 (\%572. (%414 (\%573. (%366 (\%367. (%15 (\%408. ((%145 ((%9
       (((%417 (\%415. ((%18 (%406 (%418 $0))) $1))) (%401 $1)) $3)) ((%330
       (%418 $3)) (%418 $2)))) ((%18 (((%574 (\%415. ((%18 (%406 (%418
       $0))) $1))) (%401 $1)) $3)) (((%574 (\%415. ((%18 (%406 (%418 $0)))
       $1))) (%401 $1)) $2)))))))))))`)
  val runTo_FORM1 =
    DT(["DISK_THM"], [],
       `(%366 (\%367. (%15 (\%408. (%414 (\%415. ((%410 (((%411 $2) $1)
       $0)) (((%412 (\%415. (%305 ((%18 (%406 (%418 $0))) $2)))) (%401 $2))
       $0))))))))`)
  val RUNTO_ADVANCE =
    DT(["DISK_THM"], [],
       `(%366 (\%367. (%15 (\%408. (%388 (\%403. (%409 (\%404. ((%410
       (((%411 $3) $2) ((%405 $1) $0))) (((%575 ((%18 (%406 $1)) $2))
       ((%405 $1) $0)) (((%411 $3) $2) ((%405 ((%331 $1) ($3 (%406 $1))))
       ((%407 (%406 $1)) $0)))))))))))))`)
  val RUNTO_EXPAND_ONCE =
    DT(["DISK_THM"], [],
       `(%366 (\%367. (%15 (\%408. (%414 (\%415. ((%410 (((%411 $2) $1)
       $0)) (((%575 ((%18 (%406 (%418 $0))) $1)) $0) (((%411 $2) $1) ((%401
       $2) $0))))))))))`)
  val UNROLL_RUNTO =
    DT(["DISK_THM"], [],
       `(%366 (\%367. (%15 (\%408. (%414 (\%415. ((%145 (((%417 (\%415.
       ((%18 (%406 (%418 $0))) $2))) (%401 $2)) $0)) ((%410 (((%411 $2) $1)
       $0)) (((%570 (%401 $2)) (((%574 (\%415. ((%18 (%406 (%418 $0)))
       $2))) (%401 $2)) $0)) $0)))))))))`)
  val RUNTO_STATE_PCS_SEPERATE =
    DT(["DISK_THM"], [],
       `(%15 (\%408. (%409 (\%568. (%409 (\%569. (%366 (\%367. (%388
       (\%403. ((%145 (((%417 (\%415. ((%18 (%406 (%418 $0))) $5))) (%401
       $1)) ((%405 $0) $3))) ((%330 (%418 (((%411 $1) $4) ((%405 $0) $3))))
       (%418 (((%411 $1) $4) ((%405 $0) $2)))))))))))))))`)
  val RUNTO_STILL =
    DT(["DISK_THM"], [],
       `(%15 (\%408. (%26 (\%576. (%366 (\%367. (%414 (\%415. ((%145
       (((%416 $1) $3) $0)) ((%410 (((%411 $1) $3) (((%411 $1) $3) $0)))
       (((%411 $1) $3) $0)))))))))))`)
  val RUNTO_PCS_GROW =
    DT(["DISK_THM"], [],
       `(%15 (\%3. (%26 (\%577. (%366 (\%367. (%414 (\%415. ((%578 (%567
       $0)) (%567 (((%570 (%401 $1)) $3) $0)))))))))))`)
  val RUNTO_PCS_MEMBERS =
    DT(["DISK_THM"], [],
       `(%15 (\%3. (%15 (\%33. (%366 (\%367. (%414 (\%415. ((%145 ((%4 $2)
       $3)) ((%422 (%406 (%418 (((%570 (%401 $1)) $2) $0)))) (%567 (((%570
       (%401 $1)) $3) $0))))))))))))`)
  val RUNTO_PCS_MEMBERS_2 =
    DT(["DISK_THM"], [],
       `(%15 (\%3. (%15 (\%33. (%366 (\%367. (%388 (\%403. (%409 (\%404.
       ((%145 ((%4 $3) $4)) ((%422 (%406 (%418 (((%570 (%401 $2)) $3)
       ((%405 $1) $0))))) (%567 (((%570 (%401 $2)) $4) ((%405 $1)
       %579)))))))))))))))`)
  val RUNTO_PCS_UNION_LEM =
    DT(["DISK_THM"], [],
       `(%15 (\%3. (%366 (\%367. (%388 (\%403. (%409 (\%404. (%409 (\%580.
       ((%145 ((%578 $0) (%567 (((%570 (%401 $3)) $4) ((%405 $2) $1)))))
       ((%581 ((%582 (%567 (((%570 (%401 $3)) $4) ((%405 $2) $1)))) $0))
       ((%582 (%567 (((%570 (%401 $3)) $4) ((%405 $2) $0))))
       $1)))))))))))))`)
  val RUNTO_PCS_UNION =
    DT(["DISK_THM"], [],
       `(%26 (\%583. (%366 (\%367. (%388 (\%403. (%409 (\%404. ((%145
       (((%417 (\%415. ((%18 (%406 (%418 $0))) %408))) (%401 $2)) ((%405
       $1) $0))) ((%581 (%567 (((%411 $2) %408) ((%405 $1) $0)))) ((%582
       (%567 (((%411 $2) %408) ((%405 $1) %579)))) $0)))))))))))`)
  val RUNTO_COMPOSITION_LEM =
    DT(["DISK_THM"], [],
       `(%15 (\%408. (%15 (\%240. (%366 (\%367. (%388 (\%584. (%409 (\%568.
       ((%145 (((%416 $2) $4) ((%405 $1) $0))) ((%585 (%413 (\%586. (\%569.
       ((%145 (%305 ((%422 $5) ((%407 (%406 $3)) $0)))) ((%410 (((%411 $4)
       $5) ((%405 $3) $2))) (((%411 $4) $5) ((%405 $1) $0)))))))) (((%411
       $2) $4) ((%405 $1) $0))))))))))))))`)
  val RUNTO_COMPOSITION =
    DT(["DISK_THM"], [],
       `(%15 (\%408. (%15 (\%240. (%366 (\%367. (%388 (\%584. (%409 (\%568.
       (%388 (\%586. (%409 (\%569. ((%145 ((%9 (((%416 $4) $6) ((%405 $3)
       $2))) ((%9 ((%410 ((%405 $1) $0)) (((%411 $4) $6) ((%405 $3) $2))))
       (%305 ((%422 $5) ((%407 (%406 $3)) $0)))))) ((%410 (((%411 $4) $5)
       ((%405 $3) $2))) (((%411 $4) $5) ((%405 $1) $0))))))))))))))))))`)
  val FUPDATE_REFL =
    DT(["DISK_THM"], [],
       `(%26 (\%587. (%588 (\%589. ((%145 ((%590 $1) (%591 $0))) ((%592
       ((%593 $0) ((%594 $1) ((%595 $0) $1)))) $0))))))`)
  val FUPDATE_LT_COMMUTES =
    DT(["DISK_THM"], [],
       `(%229 (\%596. (%15 (\%148. (%35 (\%302. (%15 (\%597. (%35 (\%598.
       ((%145 ((%4 $1) $3)) ((%599 ((%255 ((%255 $4) ((%182 $3) $2)))
       ((%182 $1) $0))) ((%255 ((%255 $4) ((%182 $1) $0))) ((%182 $3)
       $2))))))))))))))`)
  val FUPDATE_GT_COMMUTES =
    DT(["DISK_THM"], [],
       `(%600 (\%601. (%15 (\%148. (%602 (\%603. (%15 (\%597. (%602 (\%604.
       ((%145 ((%547 $1) $3)) ((%605 ((%606 ((%606 $4) ((%607 $3) $2)))
       ((%607 $1) $0))) ((%606 ((%606 $4) ((%607 $1) $0))) ((%607 $3)
       $2))))))))))))))`)
  end
  val _ = DB.bindl "preARM"
  [("SRS_TY_DEF",SRS_TY_DEF,DB.Def), ("SRS_BIJ",SRS_BIJ,DB.Def),
   ("SN",SN,DB.Def), ("SZ",SZ,DB.Def), ("SC",SC,DB.Def), ("SV",SV,DB.Def),
   ("SRS_size_def",SRS_size_def,DB.Def), ("SRS_case",SRS_case,DB.Def),
   ("getS_def",getS_def,DB.Def), ("setS_def",setS_def,DB.Def),
   ("setNZCV_def",setNZCV_def,DB.Def),
   ("OPERATOR_TY_DEF",OPERATOR_TY_DEF,DB.Def),
   ("OPERATOR_BIJ",OPERATOR_BIJ,DB.Def), ("MOV",MOV,DB.Def),
   ("ADD",ADD,DB.Def), ("SUB",SUB,DB.Def), ("RSB",RSB,DB.Def),
   ("MUL",MUL,DB.Def), ("MLA",MLA,DB.Def), ("AND",AND,DB.Def),
   ("ORR",ORR,DB.Def), ("EOR",EOR,DB.Def), ("CMP",CMP,DB.Def),
   ("TST",TST,DB.Def), ("LSL",LSL,DB.Def), ("LSR",LSR,DB.Def),
   ("ASR",ASR,DB.Def), ("ROR",ROR,DB.Def), ("LDR",LDR,DB.Def),
   ("STR",STR,DB.Def), ("LDMFD",LDMFD,DB.Def), ("STMFD",STMFD,DB.Def),
   ("MRS",MRS,DB.Def), ("MSR",MSR,DB.Def), ("B",B,DB.Def),
   ("BL",BL,DB.Def), ("OPERATOR_size_def",OPERATOR_size_def,DB.Def),
   ("OPERATOR_case",OPERATOR_case,DB.Def),
   ("COND_TY_DEF",COND_TY_DEF,DB.Def), ("COND_BIJ",COND_BIJ,DB.Def),
   ("EQ",EQ,DB.Def), ("CS",CS,DB.Def), ("MI",MI,DB.Def), ("VS",VS,DB.Def),
   ("HI",HI,DB.Def), ("GE",GE,DB.Def), ("GT",GT,DB.Def), ("AL",AL,DB.Def),
   ("NE",NE,DB.Def), ("CC",CC,DB.Def), ("PL",PL,DB.Def), ("VC",VC,DB.Def),
   ("LS",LS,DB.Def), ("LT",LT,DB.Def), ("LE",LE,DB.Def), ("NV",NV,DB.Def),
   ("COND_size_def",COND_size_def,DB.Def), ("COND_case",COND_case,DB.Def),
   ("OFFSET_TY_DEF",OFFSET_TY_DEF,DB.Def),
   ("OFFSET_repfns",OFFSET_repfns,DB.Def),
   ("preARM0_def",preARM0_def,DB.Def), ("preARM1_def",preARM1_def,DB.Def),
   ("POS",POS,DB.Def), ("NEG",NEG,DB.Def),
   ("OFFSET_case_def",OFFSET_case_def,DB.Def),
   ("OFFSET_size_def",OFFSET_size_def,DB.Def),
   ("EXP_TY_DEF",EXP_TY_DEF,DB.Def), ("EXP_repfns",EXP_repfns,DB.Def),
   ("preARM2_def",preARM2_def,DB.Def), ("preARM3_def",preARM3_def,DB.Def),
   ("preARM4_def",preARM4_def,DB.Def), ("preARM5_def",preARM5_def,DB.Def),
   ("preARM6_def",preARM6_def,DB.Def), ("MEM",MEM,DB.Def),
   ("NCONST",NCONST,DB.Def), ("WCONST",WCONST,DB.Def), ("REG",REG,DB.Def),
   ("WREG",WREG,DB.Def), ("EXP_case_def",EXP_case_def,DB.Def),
   ("EXP_size_def",EXP_size_def,DB.Def), ("FP_def",FP_def,DB.Def),
   ("IP_def",IP_def,DB.Def), ("SP_def",SP_def,DB.Def),
   ("LR_def",LR_def,DB.Def), ("PC_def",PC_def,DB.Def),
   ("read_def",read_def,DB.Def), ("write_def",write_def,DB.Def),
   ("goto_primitive_def",goto_primitive_def,DB.Def),
   ("decode_op_def",decode_op_def,DB.Def),
   ("decode_cond_cpsr_def",decode_cond_cpsr_def,DB.Def),
   ("decode_cond_def",decode_cond_def,DB.Def),
   ("upload_def",upload_def,DB.Def),
   ("uploadCode_def",uploadCode_def,DB.Def),
   ("uploadSeg_def",uploadSeg_def,DB.Def),
   ("run_tupled_primitive_def",run_tupled_primitive_def,DB.Def),
   ("run_curried_def",run_curried_def,DB.Def),
   ("stopAt_def",stopAt_def,DB.Def), ("shortest_def",shortest_def,DB.Def),
   ("step_def",step_def,DB.Def), ("runTo_def",runTo_def,DB.Def),
   ("terd_def",terd_def,DB.Def),
   ("in_regs_dom_def",in_regs_dom_def,DB.Def),
   ("in_mem_dom_def",in_mem_dom_def,DB.Def),
   ("num2SRS_SRS2num",num2SRS_SRS2num,DB.Thm),
   ("SRS2num_num2SRS",SRS2num_num2SRS,DB.Thm),
   ("num2SRS_11",num2SRS_11,DB.Thm), ("SRS2num_11",SRS2num_11,DB.Thm),
   ("num2SRS_ONTO",num2SRS_ONTO,DB.Thm),
   ("SRS2num_ONTO",SRS2num_ONTO,DB.Thm),
   ("num2SRS_thm",num2SRS_thm,DB.Thm), ("SRS2num_thm",SRS2num_thm,DB.Thm),
   ("SRS_EQ_SRS",SRS_EQ_SRS,DB.Thm), ("SRS_case_def",SRS_case_def,DB.Thm),
   ("datatype_SRS",datatype_SRS,DB.Thm),
   ("SRS_distinct",SRS_distinct,DB.Thm),
   ("SRS_case_cong",SRS_case_cong,DB.Thm),
   ("SRS_nchotomy",SRS_nchotomy,DB.Thm), ("SRS_Axiom",SRS_Axiom,DB.Thm),
   ("SRS_induction",SRS_induction,DB.Thm), ("getS_thm",getS_thm,DB.Thm),
   ("setS_thm",setS_thm,DB.Thm), ("setNZCV_thm",setNZCV_thm,DB.Thm),
   ("num2OPERATOR_OPERATOR2num",num2OPERATOR_OPERATOR2num,DB.Thm),
   ("OPERATOR2num_num2OPERATOR",OPERATOR2num_num2OPERATOR,DB.Thm),
   ("num2OPERATOR_11",num2OPERATOR_11,DB.Thm),
   ("OPERATOR2num_11",OPERATOR2num_11,DB.Thm),
   ("num2OPERATOR_ONTO",num2OPERATOR_ONTO,DB.Thm),
   ("OPERATOR2num_ONTO",OPERATOR2num_ONTO,DB.Thm),
   ("num2OPERATOR_thm",num2OPERATOR_thm,DB.Thm),
   ("OPERATOR2num_thm",OPERATOR2num_thm,DB.Thm),
   ("OPERATOR_EQ_OPERATOR",OPERATOR_EQ_OPERATOR,DB.Thm),
   ("OPERATOR_case_def",OPERATOR_case_def,DB.Thm),
   ("datatype_OPERATOR",datatype_OPERATOR,DB.Thm),
   ("OPERATOR_case_cong",OPERATOR_case_cong,DB.Thm),
   ("OPERATOR_nchotomy",OPERATOR_nchotomy,DB.Thm),
   ("OPERATOR_Axiom",OPERATOR_Axiom,DB.Thm),
   ("OPERATOR_induction",OPERATOR_induction,DB.Thm),
   ("num2COND_COND2num",num2COND_COND2num,DB.Thm),
   ("COND2num_num2COND",COND2num_num2COND,DB.Thm),
   ("num2COND_11",num2COND_11,DB.Thm), ("COND2num_11",COND2num_11,DB.Thm),
   ("num2COND_ONTO",num2COND_ONTO,DB.Thm),
   ("COND2num_ONTO",COND2num_ONTO,DB.Thm),
   ("num2COND_thm",num2COND_thm,DB.Thm),
   ("COND2num_thm",COND2num_thm,DB.Thm),
   ("COND_EQ_COND",COND_EQ_COND,DB.Thm),
   ("COND_case_def",COND_case_def,DB.Thm),
   ("datatype_COND",datatype_COND,DB.Thm),
   ("COND_case_cong",COND_case_cong,DB.Thm),
   ("COND_nchotomy",COND_nchotomy,DB.Thm),
   ("COND_Axiom",COND_Axiom,DB.Thm),
   ("COND_induction",COND_induction,DB.Thm),
   ("datatype_OFFSET",datatype_OFFSET,DB.Thm),
   ("OFFSET_11",OFFSET_11,DB.Thm),
   ("OFFSET_distinct",OFFSET_distinct,DB.Thm),
   ("OFFSET_case_cong",OFFSET_case_cong,DB.Thm),
   ("OFFSET_nchotomy",OFFSET_nchotomy,DB.Thm),
   ("OFFSET_Axiom",OFFSET_Axiom,DB.Thm),
   ("OFFSET_induction",OFFSET_induction,DB.Thm),
   ("datatype_EXP",datatype_EXP,DB.Thm), ("EXP_11",EXP_11,DB.Thm),
   ("EXP_distinct",EXP_distinct,DB.Thm),
   ("EXP_case_cong",EXP_case_cong,DB.Thm),
   ("EXP_nchotomy",EXP_nchotomy,DB.Thm), ("EXP_Axiom",EXP_Axiom,DB.Thm),
   ("EXP_induction",EXP_induction,DB.Thm),
   ("FORALL_DSTATE",FORALL_DSTATE,DB.Thm),
   ("FORALL_STATE",FORALL_STATE,DB.Thm), ("read_thm",read_thm,DB.Thm),
   ("write_thm",write_thm,DB.Thm), ("goto_ind",goto_ind,DB.Thm),
   ("goto_def",goto_def,DB.Thm), ("goto_thm",goto_thm,DB.Thm),
   ("decode_op_thm",decode_op_thm,DB.Thm),
   ("decode_cond_thm",decode_cond_thm,DB.Thm),
   ("UPLOAD_NOT_AFFECT_LOWER",UPLOAD_NOT_AFFECT_LOWER,DB.Thm),
   ("UPLOAD_LEM",UPLOAD_LEM,DB.Thm),
   ("UPLOAD_START_POINT_INDEPENDENT",
    UPLOAD_START_POINT_INDEPENDENT,
    DB.Thm), ("UPLOADCODE_LEM",UPLOADCODE_LEM,DB.Thm),
   ("UPLOADSEG_LEM",UPLOADSEG_LEM,DB.Thm), ("run_def",run_def,DB.Thm),
   ("run_ind",run_ind,DB.Thm), ("RUN_LEM_1",RUN_LEM_1,DB.Thm),
   ("RUN_LEM_2",RUN_LEM_2,DB.Thm), ("RUN_THM_1",RUN_THM_1,DB.Thm),
   ("LEAST_ADD_LEM",LEAST_ADD_LEM,DB.Thm),
   ("FUNPOW_THM_1",FUNPOW_THM_1,DB.Thm),
   ("FUNPOW_THM_2",FUNPOW_THM_2,DB.Thm),
   ("FUNPOW_FUNPOW",FUNPOW_FUNPOW,DB.Thm),
   ("STOPAT_THM",STOPAT_THM,DB.Thm),
   ("SHORTEST_STOP",SHORTEST_STOP,DB.Thm),
   ("SHORTEST_LEM",SHORTEST_LEM,DB.Thm),
   ("SHORTEST_THM",SHORTEST_THM,DB.Thm),
   ("SHORTEST_CASES",SHORTEST_CASES,DB.Thm),
   ("SHORTEST_INDUCTIVE",SHORTEST_INDUCTIVE,DB.Thm),
   ("TERD_WHILE_EQ_UNROLL",TERD_WHILE_EQ_UNROLL,DB.Thm),
   ("UNROLL_ADVANCE",UNROLL_ADVANCE,DB.Thm),
   ("WHILE_STILL",WHILE_STILL,DB.Thm), ("step_FORM1",step_FORM1,DB.Thm),
   ("STATE_PCS_SEPERATE",STATE_PCS_SEPERATE,DB.Thm),
   ("STOPAT_ANY_PCS",STOPAT_ANY_PCS,DB.Thm),
   ("STOPAT_ANY_PCS_2",STOPAT_ANY_PCS_2,DB.Thm),
   ("SHORTEST_INDEPENDENT_OF_PCS",SHORTEST_INDEPENDENT_OF_PCS,DB.Thm),
   ("runTo_FORM1",runTo_FORM1,DB.Thm),
   ("RUNTO_ADVANCE",RUNTO_ADVANCE,DB.Thm),
   ("RUNTO_EXPAND_ONCE",RUNTO_EXPAND_ONCE,DB.Thm),
   ("UNROLL_RUNTO",UNROLL_RUNTO,DB.Thm),
   ("RUNTO_STATE_PCS_SEPERATE",RUNTO_STATE_PCS_SEPERATE,DB.Thm),
   ("RUNTO_STILL",RUNTO_STILL,DB.Thm),
   ("RUNTO_PCS_GROW",RUNTO_PCS_GROW,DB.Thm),
   ("RUNTO_PCS_MEMBERS",RUNTO_PCS_MEMBERS,DB.Thm),
   ("RUNTO_PCS_MEMBERS_2",RUNTO_PCS_MEMBERS_2,DB.Thm),
   ("RUNTO_PCS_UNION_LEM",RUNTO_PCS_UNION_LEM,DB.Thm),
   ("RUNTO_PCS_UNION",RUNTO_PCS_UNION,DB.Thm),
   ("RUNTO_COMPOSITION_LEM",RUNTO_COMPOSITION_LEM,DB.Thm),
   ("RUNTO_COMPOSITION",RUNTO_COMPOSITION,DB.Thm),
   ("FUPDATE_REFL",FUPDATE_REFL,DB.Thm),
   ("FUPDATE_LT_COMMUTES",FUPDATE_LT_COMMUTES,DB.Thm),
   ("FUPDATE_GT_COMMUTES",FUPDATE_GT_COMMUTES,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("finite_mapTheory.finite_map_grammars",
                          finite_mapTheory.finite_map_grammars),
                         ("wordsTheory.words_grammars",
                          wordsTheory.words_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms temp_type_abbrev ("REGISTER", T"num" "num" [])
  val _ = update_grms
       temp_type_abbrev
       ("CPSR", T"cart" "fcp" [bool, T"i32" "words" []])
  val _ = update_grms temp_add_type "SRS"
  val _ = update_grms
       (temp_overload_on_by_nametype "SRS2num")
        {Name = "SRS2num", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "num2SRS")
        {Name = "num2SRS", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SN")
        {Name = "SN", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SZ")
        {Name = "SZ", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SC")
        {Name = "SC", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SV")
        {Name = "SV", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SRS_size")
        {Name = "SRS_size", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SRS_case")
        {Name = "SRS_case", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "getS")
        {Name = "getS", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "setS")
        {Name = "setS", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "setNZCV")
        {Name = "setNZCV", Thy = "preARM"}
  val _ = update_grms temp_add_type "OPERATOR"
  val _ = update_grms
       (temp_overload_on_by_nametype "OPERATOR2num")
        {Name = "OPERATOR2num", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "num2OPERATOR")
        {Name = "num2OPERATOR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MOV")
        {Name = "MOV", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ADD")
        {Name = "ADD", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SUB")
        {Name = "SUB", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "RSB")
        {Name = "RSB", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MUL")
        {Name = "MUL", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MLA")
        {Name = "MLA", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "AND")
        {Name = "AND", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ORR")
        {Name = "ORR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "EOR")
        {Name = "EOR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CMP")
        {Name = "CMP", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TST")
        {Name = "TST", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "LSL")
        {Name = "LSL", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "LSR")
        {Name = "LSR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ASR")
        {Name = "ASR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ROR")
        {Name = "ROR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "LDR")
        {Name = "LDR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "STR")
        {Name = "STR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "LDMFD")
        {Name = "LDMFD", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "STMFD")
        {Name = "STMFD", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MRS")
        {Name = "MRS", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MSR")
        {Name = "MSR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "B")
        {Name = "B", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "BL")
        {Name = "BL", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "OPERATOR_size")
        {Name = "OPERATOR_size", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "OPERATOR_case")
        {Name = "OPERATOR_case", Thy = "preARM"}
  val _ = update_grms temp_add_type "COND"
  val _ = update_grms
       (temp_overload_on_by_nametype "COND2num")
        {Name = "COND2num", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "num2COND")
        {Name = "num2COND", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "EQ")
        {Name = "EQ", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CS")
        {Name = "CS", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MI")
        {Name = "MI", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "VS")
        {Name = "VS", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "HI")
        {Name = "HI", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "GE")
        {Name = "GE", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "GT")
        {Name = "GT", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "AL")
        {Name = "AL", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "NE")
        {Name = "NE", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "CC")
        {Name = "CC", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "PL")
        {Name = "PL", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "VC")
        {Name = "VC", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "LS")
        {Name = "LS", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "LT")
        {Name = "LT", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "LE")
        {Name = "LE", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "NV")
        {Name = "NV", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "COND_size")
        {Name = "COND_size", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "COND_case")
        {Name = "COND_case", Thy = "preARM"}
  val _ = update_grms temp_type_abbrev ("ADDR", T"num" "num" [])
  val _ = update_grms
       temp_type_abbrev
       ("DATA", T"cart" "fcp" [bool, T"i32" "words" []])
  val _ = update_grms temp_type_abbrev ("DISTANCE", T"num" "num" [])
  val _ = update_grms temp_add_type "OFFSET"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_OFFSET")
        {Name = "dest_OFFSET", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_OFFSET")
        {Name = "mk_OFFSET", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "preARM0")
        {Name = "preARM0", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "preARM1")
        {Name = "preARM1", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "POS")
        {Name = "POS", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "NEG")
        {Name = "NEG", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "OFFSET_case")
        {Name = "OFFSET_case", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "OFFSET_size")
        {Name = "OFFSET_size", Thy = "preARM"}
  val _ = update_grms temp_add_type "EXP"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_EXP")
        {Name = "dest_EXP", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_EXP")
        {Name = "mk_EXP", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "preARM2")
        {Name = "preARM2", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "preARM3")
        {Name = "preARM3", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "preARM4")
        {Name = "preARM4", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "preARM5")
        {Name = "preARM5", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "preARM6")
        {Name = "preARM6", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "MEM")
        {Name = "MEM", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "NCONST")
        {Name = "NCONST", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "WCONST")
        {Name = "WCONST", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "REG")
        {Name = "REG", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "WREG")
        {Name = "WREG", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "EXP_case")
        {Name = "EXP_case", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "EXP_size")
        {Name = "EXP_size", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "FP")
        {Name = "FP", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "IP")
        {Name = "IP", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "SP")
        {Name = "SP", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "LR")
        {Name = "LR", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "PC")
        {Name = "PC", Thy = "preARM"}
  val _ = update_grms
       temp_type_abbrev
       ("OPERATION", T"prod" "pair"
 [T"OPERATOR" "preARM" [],
  T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]])
  val _ = update_grms
       temp_type_abbrev
       ("INST", T"prod" "pair"
 [T"prod" "pair"
   [T"OPERATOR" "preARM" [],
    T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]],
  T"prod" "pair"
   [T"option" "option" [T"EXP" "preARM" []],
    T"prod" "pair"
     [T"list" "list" [T"EXP" "preARM" []],
      T"option" "option" [T"OFFSET" "preARM" []]]]])
  val _ = update_grms
       temp_type_abbrev
       ("STATE", T"prod" "pair"
 [T"num" "num" [],
  T"prod" "pair"
   [T"cart" "fcp" [bool, T"i32" "words" []],
    T"prod" "pair"
     [T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
      T"fmap" "finite_map"
       [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]])
  val _ = update_grms
       (temp_overload_on_by_nametype "read")
        {Name = "read", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "write")
        {Name = "write", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "goto")
        {Name = "goto", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "decode_op")
        {Name = "decode_op", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "decode_cond_cpsr")
        {Name = "decode_cond_cpsr", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "decode_cond")
        {Name = "decode_cond", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "upload")
        {Name = "upload", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "uploadCode")
        {Name = "uploadCode", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "uploadSeg")
        {Name = "uploadSeg", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "run_tupled")
        {Name = "run_tupled", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "run")
        {Name = "run", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "stopAt")
        {Name = "stopAt", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "shortest")
        {Name = "shortest", Thy = "preARM"}
  val _ = update_grms
       temp_type_abbrev
       ("STATEPCS", T"prod" "pair"
 [T"prod" "pair"
   [T"num" "num" [],
    T"prod" "pair"
     [T"cart" "fcp" [bool, T"i32" "words" []],
      T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]],
  (T"num" "num" [] --> bool)])
  val _ = update_grms
       (temp_overload_on_by_nametype "step")
        {Name = "step", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "runTo")
        {Name = "runTo", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "terd")
        {Name = "terd", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "in_regs_dom")
        {Name = "in_regs_dom", Thy = "preARM"}
  val _ = update_grms
       (temp_overload_on_by_nametype "in_mem_dom")
        {Name = "in_mem_dom", Thy = "preARM"}
  val preARM_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG SRS_Axiom,
           case_def=SRS_case_def,
           case_cong=SRS_case_cong,
           induction=ORIG SRS_induction,
           nchotomy=SRS_nchotomy,
           size=SOME(Parse.Term`(preARM$SRS_size) :(preARM$SRS) -> (num$num)`,
                     ORIG SRS_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME SRS_distinct,
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
  
  
  val _ = computeLib.add_funs [getS_def];  
  
  val _ = computeLib.add_funs [setS_def];  
  
  val _ = computeLib.add_funs [setNZCV_def];  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG OPERATOR_Axiom,
           case_def=OPERATOR_case_def,
           case_cong=OPERATOR_case_cong,
           induction=ORIG OPERATOR_induction,
           nchotomy=OPERATOR_nchotomy,
           size=SOME(Parse.Term`(preARM$OPERATOR_size) :(preARM$OPERATOR) -> (num$num)`,
                     ORIG OPERATOR_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=NONE,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[]}
        val tyinfo0 = EnumType.update_tyinfo "OPERATOR" OPERATOR_EQ_OPERATOR OPERATOR2num_thm tyinfo0
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
          {ax=ORIG COND_Axiom,
           case_def=COND_case_def,
           case_cong=COND_case_cong,
           induction=ORIG COND_induction,
           nchotomy=COND_nchotomy,
           size=SOME(Parse.Term`(preARM$COND_size) :(preARM$COND) -> (num$num)`,
                     ORIG COND_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=NONE,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[]}
        val tyinfo0 = EnumType.update_tyinfo "COND" COND_EQ_COND COND2num_thm tyinfo0
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
          {ax=ORIG OFFSET_Axiom,
           case_def=OFFSET_case_def,
           case_cong=OFFSET_case_cong,
           induction=ORIG OFFSET_induction,
           nchotomy=OFFSET_nchotomy,
           size=SOME(Parse.Term`(preARM$OFFSET_size) :(preARM$OFFSET) -> (num$num)`,
                     ORIG OFFSET_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME OFFSET_11,
           distinct=SOME OFFSET_distinct,
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
          {ax=ORIG EXP_Axiom,
           case_def=EXP_case_def,
           case_cong=EXP_case_cong,
           induction=ORIG EXP_induction,
           nchotomy=EXP_nchotomy,
           size=SOME(Parse.Term`(preARM$EXP_size) :(preARM$EXP) -> (num$num)`,
                     ORIG EXP_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME EXP_11,
           distinct=SOME EXP_distinct,
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
  
  
  val _ = computeLib.add_funs [FP_def];  
  
  val _ = computeLib.add_funs [IP_def];  
  
  val _ = computeLib.add_funs [SP_def];  
  
  val _ = computeLib.add_funs [LR_def];  
  
  val _ = computeLib.add_funs [PC_def];  
  
  val _ = computeLib.add_funs [read_def];  
  
  val _ = computeLib.add_funs [write_def];  
  
  val _ = computeLib.add_funs [goto_def];  
  
  val _ = computeLib.add_funs [decode_op_def];  
  
  val _ = computeLib.add_funs [decode_cond_cpsr_def];  
  
  val _ = computeLib.add_funs [decode_cond_def];  
  
  val _ = computeLib.add_funs [upload_def];  
  
  val _ = computeLib.add_funs [uploadCode_def];  
  
  val _ = computeLib.add_funs [uploadSeg_def,
                               (Conv.CONV_RULE TotalDefn.SUC_TO_NUMERAL_DEFN_CONV uploadSeg_def)];
  
  
  val _ = computeLib.add_funs [stopAt_def];  
  
  val _ = computeLib.add_funs [shortest_def];  
  
  val _ = computeLib.add_funs [step_def];  
  
  val _ = computeLib.add_funs [runTo_def];  
  
  val _ = computeLib.add_funs [terd_def];  
  
  val _ = computeLib.add_funs [in_regs_dom_def];  
  
  val _ = computeLib.add_funs [in_mem_dom_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
