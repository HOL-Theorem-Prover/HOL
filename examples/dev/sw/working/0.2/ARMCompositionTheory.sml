structure ARMCompositionTheory :> ARMCompositionTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading ARMCompositionTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open preARMTheory rich_listTheory
  in end;
  val _ = Theory.link_parents
          ("ARMComposition",
          Arbnum.fromString "1162366193",
          Arbnum.fromString "485425")
          [("rich_list",
           Arbnum.fromString "1157050838",
           Arbnum.fromString "226018"),
           ("preARM",
           Arbnum.fromString "1162366112",
           Arbnum.fromString "110449")];
  val _ = Theory.incorporate_types "ARMComposition" [];
  val _ = Theory.incorporate_consts "ARMComposition"
     [("eval_cond",
       ((T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
         (T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]
          --> bool)))),
      ("WF_Loop",
       ((T"prod" "pair" [(alpha --> bool), (alpha --> alpha)] --> bool))),
      ("loopNum",
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
              (T"num" "num" [] --> bool)] --> T"num" "num" [])))))),
      ("eval_cond_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [T"EXP" "preARM" [],
             T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool))),
      ("status_independent",
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
         bool))),
      ("get_st",
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
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
      ("mk_TR",
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
                  T"option" "option" [T"OFFSET" "preARM" []]]]]])))),
      ("WF_TR",
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
                   T"option" "option" [T"OFFSET" "preARM" []]]]]]] -->
         bool))),
      ("mk_SC",
       ((T"list" "list" [alpha] -->
         (T"list" "list" [alpha] --> T"list" "list" [alpha])))),
      ("mk_CJ",
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
                   T"option" "option" [T"OFFSET" "preARM" []]]]]]))))),
      ("eval_fl",
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
      ("closed",
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
         bool))),
      ("well_formed",
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
         bool))),
      ("terminated",
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
         bool)))];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool"
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
   C"=" "min" ((bool --> (bool --> bool))),
   C"terminated" "ARMComposition"
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
   V"iB"
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
   V"s'"
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
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
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
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
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
      T"num" "num" [])),
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
   C"closed" "ARMComposition"
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
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"x" (T"num" "num" []), C"==>" "min" ((bool --> (bool --> bool))),
   C"IN" "bool"
    ((T"num" "num" [] --> ((T"num" "num" [] --> bool) --> bool))),
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
   C"EMPTY" "pred_set" ((T"num" "num" [] --> bool)),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"<=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
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
   C"status_independent" "ARMComposition"
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
   V"pos0" (T"num" "num" []), V"pos1" (T"num" "num" []),
   C"!" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"cpsr0" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"cpsr1" (T"cart" "fcp" [bool, T"i32" "words" []]),
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
   C"eval_fl" "ARMComposition"
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
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]))),
   C"uploadCode" "preARM"
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
        T"prod" "pair"
         [T"prod" "pair"
           [T"OPERATOR" "preARM" [],
            T"prod" "pair"
             [T"option" "option" [T"COND" "preARM" []], bool]],
          T"prod" "pair"
           [T"option" "option" [T"EXP" "preARM" []],
            T"prod" "pair"
             [T"list" "list" [T"EXP" "preARM" []],
              T"option" "option" [T"OFFSET" "preARM" []]]]])))),
   V"i" (T"num" "num" []),
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
   C"0" "num" (T"num" "num" []),
   C"n2w" "words"
    ((T"num" "num" [] --> T"cart" "fcp" [bool, T"i32" "words" []])),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"arm1" (T"list" "list" [alpha]), V"arm2" (T"list" "list" [alpha]),
   C"=" "min"
    ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool))),
   C"mk_SC" "ARMComposition"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"APPEND" "list"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"!" "bool" (((T"EXP" "preARM" [] --> bool) --> bool)),
   V"v1" (T"EXP" "preARM" []),
   C"!" "bool" (((T"COND" "preARM" [] --> bool) --> bool)),
   V"rop" (T"COND" "preARM" []), V"v2" (T"EXP" "preARM" []),
   V"arm_t"
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
   V"arm_f"
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
   C"," "pair"
    ((T"EXP" "preARM" [] -->
      (T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []] -->
       T"prod" "pair"
        [T"EXP" "preARM" [],
         T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]]))),
   C"," "pair"
    ((T"COND" "preARM" [] -->
      (T"EXP" "preARM" [] -->
       T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]))),
   C"APPEND" "list"
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
   C"CMP" "preARM" (T"OPERATOR" "preARM" []),
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
   C"NONE" "option" (T"option" "option" [T"EXP" "preARM" []]),
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
   C"B" "preARM" (T"OPERATOR" "preARM" []),
   C"SOME" "option"
    ((T"COND" "preARM" [] --> T"option" "option" [T"COND" "preARM" []])),
   C"SOME" "option"
    ((T"OFFSET" "preARM" [] -->
      T"option" "option" [T"OFFSET" "preARM" []])),
   C"POS" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"AL" "preARM" (T"COND" "preARM" []),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
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
   C"NEG" "preARM" ((T"num" "num" [] --> T"OFFSET" "preARM" [])),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool) -->
      ((T"prod" "pair"
         [T"prod" "pair"
           [T"EXP" "preARM" [],
            T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool) --> bool))),
   C"eval_cond_tupled" "ARMComposition"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"EXP" "preARM" [],
          T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      bool)),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"EXP" "preARM" [],
            T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [T"EXP" "preARM" [],
             T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool) -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"EXP" "preARM" [],
             T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool)) -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"EXP" "preARM" [],
            T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [T"EXP" "preARM" [],
            T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        -->
        (T"prod" "pair"
          [T"prod" "pair"
            [T"EXP" "preARM" [],
             T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
           T"prod" "pair"
            [T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
             T"fmap" "finite_map"
              [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
         --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"EXP" "preARM" [],
            T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"EXP" "preARM" [],
          T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"EXP" "preARM" [],
            T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
          T"prod" "pair"
           [T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
            T"fmap" "finite_map"
             [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
        --> bool)) --> bool)),
   V"eval_cond_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [T"EXP" "preARM" [],
          T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
        T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]] -->
      bool)),
   V"a"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"EXP" "preARM" [],
         T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"EXP" "preARM" [],
         T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
       (T"prod" "pair"
         [T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
          T"fmap" "finite_map"
           [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
        bool)) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]]
       --> bool))),
   V"v"
    (T"prod" "pair"
      [T"EXP" "preARM" [],
       T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]]),
   V"s"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   C"pair_case" "pair"
    (((T"EXP" "preARM" [] -->
       (T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []] --> bool))
      -->
      (T"prod" "pair"
        [T"EXP" "preARM" [],
         T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
       bool))),
   V"v5" (T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]),
   C"pair_case" "pair"
    (((T"COND" "preARM" [] --> (T"EXP" "preARM" [] --> bool)) -->
      (T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []] -->
       bool))), V"v6" (T"COND" "preARM" []),
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
   C"=" "min"
    ((T"cart" "fcp" [bool, T"i32" "words" []] -->
      (T"cart" "fcp" [bool, T"i32" "words" []] --> bool))),
   C"read" "preARM"
    ((T"prod" "pair"
       [T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
        T"fmap" "finite_map"
         [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
      (T"EXP" "preARM" [] --> T"cart" "fcp" [bool, T"i32" "words" []]))),
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
   C"T" "bool" (bool), C"~" "bool" ((bool --> bool)),
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
   C"!" "bool"
    (((T"prod" "pair"
        [T"EXP" "preARM" [],
         T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
       bool) --> bool)),
   V"x"
    (T"prod" "pair"
      [T"EXP" "preARM" [],
       T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]]),
   V"x1"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
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
   C"," "pair"
    ((T"prod" "pair"
       [T"EXP" "preARM" [],
        T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"EXP" "preARM" [],
           T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]],
         T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [],
             T"cart" "fcp" [bool, T"i32" "words" []]]]]))),
   C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"cond_f" ((alpha --> bool)),
   C"!" "bool" ((((alpha --> alpha) --> bool) --> bool)),
   V"g" ((alpha --> alpha)),
   C"WF_Loop" "ARMComposition"
    ((T"prod" "pair" [(alpha --> bool), (alpha --> alpha)] --> bool)),
   C"," "pair"
    (((alpha --> bool) -->
      ((alpha --> alpha) -->
       T"prod" "pair" [(alpha --> bool), (alpha --> alpha)]))),
   C"?" "bool" ((((alpha --> (alpha --> bool)) --> bool) --> bool)),
   V"R" ((alpha --> (alpha --> bool))),
   C"WF" "relation" (((alpha --> (alpha --> bool)) --> bool)),
   C"!" "bool" (((alpha --> bool) --> bool)), V"s" (alpha),
   V"cond"
    (T"prod" "pair"
      [T"EXP" "preARM" [],
       T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]]),
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
   C"WF_Loop" "ARMComposition"
    ((T"prod" "pair"
       [(T"prod" "pair"
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
           (T"num" "num" [] --> bool)] --> bool),
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
           (T"num" "num" [] --> bool)])] --> bool)),
   C"," "pair"
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
       T"prod" "pair"
        [(T"prod" "pair"
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
            (T"num" "num" [] --> bool)] --> bool),
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
            (T"num" "num" [] --> bool)])]))),
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
         (T"num" "num" [] --> bool)] --> T"num" "num" []) -->
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
          (T"num" "num" [] --> bool)] --> T"num" "num" []) --> bool))),
   C"loopNum" "ARMComposition"
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
           (T"num" "num" [] --> bool)] --> T"num" "num" []))))),
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
   C"!" "bool"
    (((T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool) --> bool)),
   V"f" (T"fmap" "finite_map" [T"num" "num" [], alpha]),
   V"a" (T"num" "num" []), V"b" (alpha), V"c" (T"num" "num" []),
   V"d" (alpha),
   C"=" "min"
    ((T"fmap" "finite_map" [T"num" "num" [], alpha] -->
      (T"fmap" "finite_map" [T"num" "num" [], alpha] --> bool))),
   C"FUPDATE" "finite_map"
    ((T"fmap" "finite_map" [T"num" "num" [], alpha] -->
      (T"prod" "pair" [T"num" "num" [], alpha] -->
       T"fmap" "finite_map" [T"num" "num" [], alpha]))),
   C"," "pair"
    ((T"num" "num" [] -->
      (alpha --> T"prod" "pair" [T"num" "num" [], alpha]))),
   C">" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"m" (T"num" "num" []), V"pos" (alpha),
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
   V"arm'"
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
   V"arm''"
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
   V"pos" (T"num" "num" []),
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
   C"=" "min"
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
              T"option" "option" [T"OFFSET" "preARM" []]]]]) --> bool))),
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
   C"?" "bool" (((T"num" "num" [] --> bool) --> bool)),
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
       (T"num" "num" [] --> bool)]), V"instB" (alpha),
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
   V"arm1"
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
   V"arm2"
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
   C"!" "bool" ((((T"num" "num" [] --> bool) --> bool) --> bool)),
   V"pcS0" ((T"num" "num" [] --> bool)),
   V"pcS1" ((T"num" "num" [] --> bool)), V"pos2" (T"num" "num" []),
   V"cpsr2" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"=" "min"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
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
       bool))),
   C"o" "combin"
    (((T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]) -->
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
   V"cpsr" (T"cart" "fcp" [bool, T"i32" "words" []]),
   V"pcS" ((T"num" "num" [] --> bool)),
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
      bool)),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"EXP" "preARM" [],
          T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
        (T"prod" "pair"
          [T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
           T"fmap" "finite_map"
            [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
         bool)) --> bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [T"EXP" "preARM" [],
        T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
      (T"prod" "pair"
        [T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
         T"fmap" "finite_map"
          [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
       bool))), C"EQ" "preARM" (T"COND" "preARM" []),
   C"CS" "preARM" (T"COND" "preARM" []),
   C"MI" "preARM" (T"COND" "preARM" []),
   C"VS" "preARM" (T"COND" "preARM" []),
   C"HI" "preARM" (T"COND" "preARM" []),
   C"GE" "preARM" (T"COND" "preARM" []),
   C"GT" "preARM" (T"COND" "preARM" []),
   C"NE" "preARM" (T"COND" "preARM" []),
   C"CC" "preARM" (T"COND" "preARM" []),
   C"PL" "preARM" (T"COND" "preARM" []),
   C"VC" "preARM" (T"COND" "preARM" []),
   C"LS" "preARM" (T"COND" "preARM" []),
   C"LT" "preARM" (T"COND" "preARM" []),
   C"LE" "preARM" (T"COND" "preARM" []),
   C"NV" "preARM" (T"COND" "preARM" []), V"v" (T"EXP" "preARM" []),
   V"v1" (T"COND" "preARM" []),
   V"v3"
    (T"prod" "pair"
      [T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
       T"fmap" "finite_map"
        [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]]),
   V"pc" (T"num" "num" []),
   C"!" "bool" (((T"OFFSET" "preARM" [] --> bool) --> bool)),
   V"offset" (T"OFFSET" "preARM" []),
   C"?" "bool"
    (((T"cart" "fcp" [bool, T"i32" "words" []] --> bool) --> bool)),
   V"cpsr'" (T"cart" "fcp" [bool, T"i32" "words" []]),
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
   C"FST" "pair"
    ((T"prod" "pair"
       [T"EXP" "preARM" [],
        T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
      T"EXP" "preARM" [])),
   C"SND" "pair"
    ((T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []] -->
      T"EXP" "preARM" [])),
   C"SND" "pair"
    ((T"prod" "pair"
       [T"EXP" "preARM" [],
        T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []]] -->
      T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []])),
   C"FST" "pair"
    ((T"prod" "pair" [T"COND" "preARM" [], T"EXP" "preARM" []] -->
      T"COND" "preARM" [])),
   C"goto" "preARM"
    ((T"prod" "pair"
       [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]] -->
      T"num" "num" [])),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"option" "option" [T"OFFSET" "preARM" []] -->
       T"prod" "pair"
        [T"num" "num" [], T"option" "option" [T"OFFSET" "preARM" []]]))),
   V"cpsr''" (T"cart" "fcp" [bool, T"i32" "words" []]),
   C"INSERT" "pred_set"
    ((T"num" "num" [] -->
      ((T"num" "num" [] --> bool) --> (T"num" "num" [] --> bool)))),
   C"COND" "bool" ((bool --> (bool --> (bool --> bool)))),
   V"k" (T"num" "num" []),
   C"FUNPOW" "arithmetic"
    (((alpha --> alpha) --> (T"num" "num" [] --> (alpha --> alpha)))),
   C"!" "bool" (((beta --> bool) --> bool)), V"s" (beta),
   C"stopAt" "preARM"
    (((alpha --> bool) --> ((alpha --> alpha) --> (alpha --> bool)))),
   V"x" (alpha),
   C"shortest" "preARM"
    (((alpha --> bool) -->
      ((alpha --> alpha) --> (alpha --> T"num" "num" [])))),
   V"P" ((alpha --> bool)), C"=" "min" ((alpha --> (alpha --> bool))),
   C"WHILE" "while"
    (((alpha --> bool) --> ((alpha --> alpha) --> (alpha --> alpha)))),
   C"o" "combin"
    (((bool --> bool) --> ((alpha --> bool) --> (alpha --> bool)))),
   V"n" (alpha), V"n" (T"num" "num" []),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   V"pc0" (T"num" "num" []), V"pc1" (T"num" "num" []),
   C"?" "bool" ((((T"num" "num" [] --> bool) --> bool) --> bool)),
   V"pcS'" ((T"num" "num" [] --> bool)),
   C"?" "bool" (((alpha --> bool) --> bool)), V"cpsr''" (alpha),
   C"DIFF" "pred_set"
    (((T"num" "num" [] --> bool) -->
      ((T"num" "num" [] --> bool) --> (T"num" "num" [] --> bool)))),
   V"arm_t" (alpha),
   V"iB0"
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
   V"iB1"
    ((T"num" "num" [] -->
      T"prod" "pair"
       [T"prod" "pair"
         [T"OPERATOR" "preARM" [],
          T"prod" "pair" [T"option" "option" [T"COND" "preARM" []], bool]],
        T"prod" "pair"
         [T"option" "option" [T"EXP" "preARM" []],
          T"prod" "pair"
           [T"list" "list" [T"EXP" "preARM" []],
            T"option" "option" [T"OFFSET" "preARM" []]]]]))]
  val DT = Thm.disk_thm share_table
  in
  val terminated_def =
    DT([], [],
       `(%0 (\%1. ((%2 (%3 $0)) (%4 (\%5. (%6 (\%7. (((%8 (\%9. ((%10 (%11
       (%12 $0))) ((%13 (%11 (%12 $2))) (%14 $3))))) (%15 (((%16 $2) $0)
       (%11 (%12 $1))))) $1))))))))`)
  val closed_def =
    DT([], [],
       `(%0 (\%1. ((%2 (%17 $0)) (%18 (\%19. (%6 (\%7. (%20 (\%21. ((%22
       ((%23 $0) (%24 (((%25 (((%16 $3) $1) (%11 $2))) ((%13 (%11 $2)) (%14
       $3))) ((%26 $2) %27))))) ((%28 ((%29 (%11 $2)) $0)) ((%30 $0) ((%13
       (%11 $2)) (%14 $3))))))))))))))`)
  val get_st_def =
    DT([], [], `(%4 (\%5. ((%31 (%32 $0)) (%33 (%34 (%12 $0))))))`)
  val status_independent_def =
    DT([], [],
       `(%0 (\%1. ((%2 (%35 $0)) (%36 (\%37. (%20 (\%38. (%20 (\%39. (%40
       (\%41. (%40 (\%42. (%6 (\%7. ((%31 (%32 (((%25 (((%16 $6) $0) $4))
       ((%13 $4) (%14 $6))) ((%26 ((%43 $4) ((%44 $2) $5))) %27)))) (%32
       (((%25 (((%16 $6) $0) $3)) ((%13 $3) (%14 $6))) ((%26 ((%43 $3)
       ((%44 $1) $5))) %27)))))))))))))))))))`)
  val well_formed_def =
    DT([], [],
       `(%0 (\%1. ((%2 (%45 $0)) ((%28 (%17 $0)) ((%28 (%3 $0)) (%35
       $0))))))`)
  val eval_fl_def =
    DT([], [],
       `(%0 (\%1. (%36 (\%37. ((%31 ((%46 $1) $0)) (%32 (((%25 ((%47 $1)
       (\%48. %49))) (%14 $1)) ((%26 ((%43 %50) ((%44 (%51 %50)) $0)))
       %27))))))))`)
  val mk_SC_def =
    DT([], [],
       `(%52 (\%53. (%52 (\%54. ((%55 ((%56 $1) $0)) ((%57 $1) $0))))))`)
  val mk_CJ_def =
    DT(["DISK_THM"], [],
       `(%58 (\%59. (%60 (\%61. (%58 (\%62. (%0 (\%63. (%0 (\%64. ((%65
       (((%66 ((%67 $4) ((%68 $3) $2))) $1) $0)) ((%69 ((%69 ((%69 ((%69
       ((%70 ((%71 ((%72 %73) ((%74 %75) %76))) ((%77 %78) ((%79 ((%80 $4)
       ((%80 $2) %81))) %82)))) %83)) ((%70 ((%71 ((%72 %84) ((%74 (%85
       $3)) %76))) ((%77 %78) ((%79 %81) (%86 (%87 ((%13 (%14 $0)) (%88
       (%89 %90))))))))) %83))) $0)) ((%70 ((%71 ((%72 %84) ((%74 (%85
       %91)) %76))) ((%77 %78) ((%79 %81) (%86 (%87 ((%13 (%14 $1)) (%88
       (%92 %90))))))))) %83))) $1))))))))))))`)
  val mk_TR_def =
    DT(["DISK_THM"], [],
       `(%58 (\%59. (%60 (\%61. (%58 (\%62. (%0 (\%1. ((%65 ((%93 ((%67 $3)
       ((%68 $2) $1))) $0)) ((%69 ((%70 ((%71 ((%72 %73) ((%74 %75) %76)))
       ((%77 %78) ((%79 ((%80 $3) ((%80 $1) %81))) %82)))) ((%70 ((%71
       ((%72 %84) ((%74 (%85 $2)) %76))) ((%77 %78) ((%79 %81) (%86 (%87
       ((%13 (%14 $0)) (%88 (%89 %90))))))))) $0))) ((%70 ((%71 ((%72 %84)
       ((%74 (%85 %91)) %76))) ((%77 %78) ((%79 %81) (%86 (%94 ((%13 (%14
       $0)) (%88 (%89 %90))))))))) %83)))))))))))`)
  val eval_cond_tupled_primitive_def =
    DT([], [],
       `((%95 %96) ((%97 (%98 (\%99. (%100 $0)))) (\%101. (\%102. ((%103
       (\%104. (\%105. ((%106 (\%59. (\%107. ((%108 (\%109. (\%62.
       (((((((((((((((((%110 (%111 ((%112 ((%113 $4) $3)) ((%113 $4) $0))))
       (%111 ((%114 ((%113 $4) $3)) ((%113 $4) $0)))) (%111 ((%115 (%116
       (\%117. (%118 (\%119. (%120 (\%121. (\%122. $3)))))))) ((%123 ((%113
       $4) $3)) ((%113 $4) $0))))) (%111 ((%115 (%116 (\%117. (%118 (\%119.
       (%120 (\%121. (\%122. $0)))))))) ((%123 ((%113 $4) $3)) ((%113 $4)
       $0))))) (%111 ((%124 ((%113 $4) $3)) ((%113 $4) $0)))) (%111 ((%125
       ((%113 $4) $3)) ((%113 $4) $0)))) (%111 ((%126 ((%113 $4) $3))
       ((%113 $4) $0)))) (%111 %127)) (%111 (%128 ((%112 ((%113 $4) $3))
       ((%113 $4) $0))))) (%111 ((%129 ((%113 $4) $3)) ((%113 $4) $0))))
       (%111 ((%115 (%116 (\%117. (%118 (\%119. (%120 (\%121. (\%122. (%128
       $3))))))))) ((%123 ((%113 $4) $3)) ((%113 $4) $0))))) (%111 ((%115
       (%116 (\%117. (%118 (\%119. (%120 (\%121. (\%122. (%128 $0)))))))))
       ((%123 ((%113 $4) $3)) ((%113 $4) $0))))) (%111 ((%130 ((%113 $4)
       $3)) ((%113 $4) $0)))) (%111 ((%131 ((%113 $4) $3)) ((%113 $4)
       $0)))) (%111 ((%132 ((%113 $4) $3)) ((%113 $4) $0)))) (%111 %76))
       $1)))) $0)))) $1)))) $0)))))`)
  val eval_cond_curried_def =
    DT([], [],
       `(%133 (\%134. (%36 (\%135. ((%2 ((%136 $1) $0)) (%96 ((%137 $1)
       $0)))))))`)
  val WF_Loop_def =
    DT(["DISK_THM"], [],
       `(%138 (\%139. (%140 (\%141. ((%2 (%142 ((%143 $1) $0))) (%144
       (\%145. ((%28 (%146 $0)) (%147 (\%148. ((%22 (%128 ($3 $0))) (($1
       ($2 $0)) $0))))))))))))`)
  val WF_TR_def =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%1. ((%2 (%150 ((%151 $1) $0))) (%6 (\%7. (%152
       ((%153 (\%5. ((%136 $3) (%33 (%34 (%12 $0)))))) (\%5. (((%25 (((%16
       $2) $1) (%11 (%12 $0)))) ((%13 (%11 (%12 $0))) (%14 $2)))
       $0)))))))))))`)
  val loopNum_def =
    DT([], [],
       `(%133 (\%149. (%0 (\%1. (%6 (\%7. ((%154 (((%155 $2) $1) $0))
       ((%156 (\%9. ((%136 $3) (%32 $0)))) (\%9. (((%25 (((%16 $2) $1) (%11
       (%12 $0)))) ((%13 (%11 (%12 $0))) (%14 $2))) $0))))))))))`)
  val FUPDATE_LT_COMMUTES =
    DT(["DISK_THM"], [],
       `(%157 (\%158. (%20 (\%159. (%147 (\%160. (%20 (\%161. (%147 (\%162.
       ((%22 ((%30 $1) $3)) ((%163 ((%164 ((%164 $4) ((%165 $3) $2)))
       ((%165 $1) $0))) ((%164 ((%164 $4) ((%165 $1) $0))) ((%165 $3)
       $2))))))))))))))`)
  val FUPDATE_GT_COMMUTES =
    DT(["DISK_THM"], [],
       `(%157 (\%158. (%20 (\%159. (%147 (\%160. (%20 (\%161. (%147 (\%162.
       ((%22 ((%166 $1) $3)) ((%163 ((%164 ((%164 $4) ((%165 $3) $2)))
       ((%165 $1) $0))) ((%164 ((%164 $4) ((%165 $1) $0))) ((%165 $3)
       $2))))))))))))))`)
  val TERMINATED_THM =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%22 (%3 $0)) (%4 (\%5. (%6 (\%7. ((%10 (%11 (%12 (((%25
       (((%16 $2) $0) (%11 (%12 $1)))) ((%13 (%11 (%12 $1))) (%14 $2)))
       $1)))) ((%13 (%11 (%12 $1))) (%14 $2))))))))))`)
  val CLOSED_THM =
    DT(["DISK_THM"], [],
       `(%20 (\%167. (%0 (\%1. (%4 (\%5. (%6 (\%7. (%147 (\%168. ((%22 (%17
       $3)) ((%22 ((%28 (((%8 (\%9. ((%10 (%11 (%12 $0))) ((%13 (%11 (%12
       $3))) (%14 $4))))) (%15 (((%16 $3) $1) (%11 (%12 $2))))) $2)) ((%30
       $4) (((%156 (\%9. ((%10 (%11 (%12 $0))) ((%13 (%11 (%12 $3))) (%14
       $4))))) (%15 (((%16 $3) $1) (%11 (%12 $2))))) $2)))) ((%28 ((%29
       (%11 (%12 $2))) (%11 (%12 (((%169 (%15 (((%16 $3) $1) (%11 (%12
       $2))))) $4) $2))))) ((%30 (%11 (%12 (((%169 (%15 (((%16 $3) $1) (%11
       (%12 $2))))) $4) $2)))) ((%13 (%11 (%12 $2))) (%14
       $3))))))))))))))))`)
  val CLOSED_MIDDLE_STEP_LEM =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%0 (\%170. (%0 (\%171. (%147 (\%168. (%6 (\%7. (%20
       (\%172. (%4 (\%5. ((%22 ((%28 ((%29 ((%13 $1) (%14 $5))) (%11 (%12
       $0)))) ((%30 (%11 (%12 $0))) ((%13 ((%13 $1) (%14 $5))) (%14 $6)))))
       ((%173 ((%15 (((%16 ((%69 ((%69 $5) $6)) $4)) $2) $1)) $0)) ((%15
       (((%16 $6) $2) ((%13 $1) (%14 $5)))) $0)))))))))))))))))`)
  val CLOSED_MIDDLE_LEM =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%0 (\%170. (%0 (\%171. (%20 (\%172. (%6 (\%7. (%4 (\%5.
       (%4 (\%9. ((%22 ((%28 (%17 $6)) ((%28 (%3 $6)) ((%28 ((%10 ((%13 $3)
       (%14 $5))) (%11 (%12 $1)))) ((%28 ((%174 %175) (((%16 $6) $2) (%11
       (%12 $1))))) (%176 (\%167. ((%28 ((%173 $1) (((%169 (%15 %175)) $0)
       $2))) ((%29 $0) (((%156 (\%177. ((%10 (%11 (%12 $0))) ((%13 (%11
       (%12 $3))) (%14 $8))))) (%15 %175)) $2)))))))))) ((%173 (((%25
       (((%16 ((%69 ((%69 $5) $6)) $4)) $2) $3)) ((%13 (%11 (%12 $1))) (%14
       $6))) $0)) (((%25 (((%16 $6) $2) (%11 (%12 $1)))) ((%13 (%11 (%12
       $1))) (%14 $6))) $0)))))))))))))))))`)
  val CLOSED_MIDDLE =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%0 (\%170. (%0 (\%171. (%20 (\%172. (%6 (\%7. (%4 (\%5.
       ((%22 ((%28 (%17 $5)) ((%28 (%3 $5)) ((%10 ((%13 $2) (%14 $4))) (%11
       (%12 $0)))))) ((%173 (((%25 (((%16 ((%69 ((%69 $4) $5)) $3)) $1)
       $2)) ((%13 (%11 (%12 $0))) (%14 $5))) $0)) (((%25 (((%16 $5) $1)
       (%11 (%12 $0)))) ((%13 (%11 (%12 $0))) (%14 $5)))
       $0)))))))))))))))`)
  val CLOSED_PREFIX =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%0 (\%170. (%20 (\%172. (%6 (\%7. (%4 (\%5. ((%22 ((%28
       (%17 $4)) ((%28 (%3 $4)) ((%10 ((%13 $2) (%14 $3))) (%11 (%12
       $0)))))) ((%173 (((%25 (((%16 ((%69 $3) $4)) $1) $2)) ((%13 (%11
       (%12 $0))) (%14 $4))) $0)) (((%25 (((%16 $4) $1) (%11 (%12 $0))))
       ((%13 (%11 (%12 $0))) (%14 $4))) $0)))))))))))))`)
  val CLOSED_SUFFIX =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%0 (\%170. (%6 (\%7. (%147 (\%178. (%4 (\%5. ((%22 ((%28
       (%17 $4)) (%3 $4))) ((%173 (((%25 (((%16 ((%69 $4) $3)) $2) (%11
       (%12 $0)))) ((%13 (%11 (%12 $0))) (%14 $4))) $0)) (((%25 (((%16 $4)
       $2) (%11 (%12 $0)))) ((%13 (%11 (%12 $0))) (%14 $4)))
       $0)))))))))))))`)
  val TERMINATED_MIDDLE_LEM =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%0 (\%170. (%0 (\%171. (%20 (\%172. (%6 (\%7. (%4 (\%5.
       (%4 (\%9. ((%22 ((%28 (%17 $6)) ((%28 (%3 $6)) ((%28 ((%10 ((%13 $3)
       (%14 $5))) (%11 (%12 $1)))) ((%28 ((%174 %175) (((%16 $6) $2) (%11
       (%12 $1))))) (%176 (\%167. ((%28 ((%173 $1) (((%169 (%15 %175)) $0)
       $2))) ((%29 $0) (((%156 (\%177. ((%10 (%11 (%12 $0))) ((%13 (%11
       (%12 $3))) (%14 $8))))) (%15 %175)) $2)))))))))) (((%179 (((%16
       ((%69 ((%69 $5) $6)) $4)) $2) $3)) ((%13 (%11 (%12 $1))) (%14 $6)))
       $0))))))))))))))))`)
  val TERMINATED_MIDDLE =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%0 (\%170. (%0 (\%171. (%20 (\%172. (%6 (\%7. (%147
       (\%178. (%4 (\%5. ((%22 ((%28 (%17 $6)) ((%28 (%3 $6)) ((%10 ((%13
       $3) (%14 $5))) (%11 (%12 $0)))))) (((%179 (((%16 ((%69 ((%69 $5)
       $6)) $4)) $2) $3)) ((%13 (%11 (%12 $0))) (%14 $6)))
       $0))))))))))))))))`)
  val CLOSED_SEQUENTIAL_COMPOSITION =
    DT(["DISK_THM"], [],
       `(%0 (\%180. (%0 (\%181. (%0 (\%170. (%0 (\%171. (%20 (\%172. (%6
       (\%7. (%4 (\%5. ((%22 ((%28 (%17 $6)) ((%28 (%3 $6)) ((%28 (%17 $5))
       ((%28 (%3 $5)) ((%28 ((%10 ((%13 $2) (%14 $4))) (%11 (%12 $0))))
       (%128 ((%23 ((%13 ((%13 (%11 (%12 $0))) (%14 $6))) (%14 $5))) (%24
       $0))))))))) ((%28 (((%8 (\%9. ((%10 (%11 (%12 $0))) ((%13 ((%13 (%11
       (%12 $1))) (%14 $7))) (%14 $6))))) (%15 (((%16 ((%69 ((%69 ((%69 $4)
       $6)) $5)) $3)) $1) $2))) $0)) ((%173 (((%25 (((%16 ((%69 ((%69 ((%69
       $4) $6)) $5)) $3)) $1) $2)) ((%13 ((%13 (%11 (%12 $0))) (%14 $6)))
       (%14 $5))) $0)) (((%25 (((%16 $5) $1) ((%13 (%11 (%12 $0))) (%14
       $6)))) ((%13 ((%13 (%11 (%12 $0))) (%14 $6))) (%14 $5))) (((%25
       (((%16 $6) $1) (%11 (%12 $0)))) ((%13 (%11 (%12 $0))) (%14 $6)))
       $0)))))))))))))))))))`)
  val DSTATE_IRRELEVANT_PCS =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%182 (\%183. (%182 (\%184. (%6 (\%7. (%18 (\%19. ((%22
       (%3 $4)) ((%31 (%32 (((%25 (((%16 $4) $1) (%11 $0))) ((%13 (%11 $0))
       (%14 $4))) ((%26 $0) $3)))) (%32 (((%25 (((%16 $4) $1) (%11 $0)))
       ((%13 (%11 $0)) (%14 $4))) ((%26 $0) $2)))))))))))))))`)
  val DSTATE_COMPOSITION =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%0 (\%170. (%20 (\%38. (%20 (\%39. (%20 (\%185. (%40
       (\%41. (%40 (\%42. (%40 (\%186. (%6 (\%7. (%36 (\%37. ((%22 ((%28
       (%17 $9)) ((%28 (%3 $9)) ((%28 (%35 $9)) ((%28 (%17 $8)) ((%28 (%3
       $8)) (%35 $8))))))) ((%31 (%32 (((%25 (((%16 ((%69 $9) $8)) $1) $7))
       ((%13 ((%13 $7) (%14 $9))) (%14 $8))) ((%26 ((%43 $7) ((%44 $4)
       $0))) %27)))) (%32 (((%25 (((%16 $8) $1) $5)) ((%13 $5) (%14 $8)))
       ((%26 ((%43 $5) ((%44 $2) (%32 (((%25 (((%16 $9) $1) $6)) ((%13 $6)
       (%14 $9))) ((%26 ((%43 $6) ((%44 $3) $0))) %27))))))
       %27)))))))))))))))))))))))))`)
  val SEQ_COMPOSITION_FLAT =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%0 (\%170. ((%22 ((%28 (%45 $1)) (%45 $0))) ((%187 (%46
       ((%69 $1) $0))) ((%188 (%46 $0)) (%46 $1))))))))`)
  val SC_IS_WELL_FORMED =
    DT(["DISK_THM"], [],
       `(%0 (\%180. (%0 (\%181. ((%22 ((%28 (%45 $1)) (%45 $0))) (%45
       ((%189 $1) $0)))))))`)
  val UNCOND_JUMP_OVER_THM =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%28 (%45 ((%69 ((%70 ((%71 ((%72 %84) ((%74 (%85 %91))
       %76))) ((%77 %78) ((%79 %81) (%86 (%87 ((%13 (%14 $0)) (%88 (%92
       %90))))))))) %83)) $0))) (%6 (\%7. (%20 (\%172. (%40 (\%190. (%36
       (\%37. (%182 (\%191. ((%31 (%32 (((%25 (((%16 ((%69 ((%70 ((%71
       ((%72 %84) ((%74 (%85 %91)) %76))) ((%77 %78) ((%79 %81) (%86 (%87
       ((%13 (%14 $5)) (%88 (%92 %90))))))))) %83)) $5)) $4) $3)) ((%13
       ((%13 $3) (%14 $5))) (%88 (%92 %90)))) ((%26 ((%43 $3) ((%44 $2)
       $1))) $0)))) $1))))))))))))))`)
  val HOARE_SC_FLAT =
    DT(["DISK_THM"], [],
       `(%0 (\%180. (%0 (\%181. (%192 (\%193. (%192 (\%194. (%192 (\%195.
       (%192 (\%196. ((%22 ((%28 (%45 $5)) ((%28 (%45 $4)) ((%28 (%36
       (\%37. ((%22 ($4 $0)) ($3 ((%46 $6) $0)))))) ((%28 (%36 (\%37. ((%22
       ($2 $0)) ($1 ((%46 $5) $0)))))) (%36 (\%37. ((%22 ($3 $0)) ($2
       $0))))))))) (%36 (\%37. ((%22 ($4 $0)) ($1 ((%46 ((%189 $6) $5))
       $0))))))))))))))))))`)
  val eval_cond_ind =
    DT(["DISK_THM"], [],
       `(%197 (\%198. ((%22 ((%28 (%58 (\%59. (%58 (\%62. (%36 (\%105. (($3
       ((%67 $2) ((%68 %199) $1))) $0)))))))) ((%28 (%58 (\%59. (%58 (\%62.
       (%36 (\%105. (($3 ((%67 $2) ((%68 %200) $1))) $0)))))))) ((%28 (%58
       (\%59. (%58 (\%62. (%36 (\%105. (($3 ((%67 $2) ((%68 %201) $1)))
       $0)))))))) ((%28 (%58 (\%59. (%58 (\%62. (%36 (\%105. (($3 ((%67 $2)
       ((%68 %202) $1))) $0)))))))) ((%28 (%58 (\%59. (%58 (\%62. (%36
       (\%105. (($3 ((%67 $2) ((%68 %203) $1))) $0)))))))) ((%28 (%58
       (\%59. (%58 (\%62. (%36 (\%105. (($3 ((%67 $2) ((%68 %204) $1)))
       $0)))))))) ((%28 (%58 (\%59. (%58 (\%62. (%36 (\%105. (($3 ((%67 $2)
       ((%68 %205) $1))) $0)))))))) ((%28 (%58 (\%59. (%58 (\%62. (%36
       (\%105. (($3 ((%67 $2) ((%68 %91) $1))) $0)))))))) ((%28 (%58 (\%59.
       (%58 (\%62. (%36 (\%105. (($3 ((%67 $2) ((%68 %206) $1))) $0))))))))
       ((%28 (%58 (\%59. (%58 (\%62. (%36 (\%105. (($3 ((%67 $2) ((%68
       %207) $1))) $0)))))))) ((%28 (%58 (\%59. (%58 (\%62. (%36 (\%105.
       (($3 ((%67 $2) ((%68 %208) $1))) $0)))))))) ((%28 (%58 (\%59. (%58
       (\%62. (%36 (\%105. (($3 ((%67 $2) ((%68 %209) $1))) $0))))))))
       ((%28 (%58 (\%59. (%58 (\%62. (%36 (\%105. (($3 ((%67 $2) ((%68
       %210) $1))) $0)))))))) ((%28 (%58 (\%59. (%58 (\%62. (%36 (\%105.
       (($3 ((%67 $2) ((%68 %211) $1))) $0)))))))) ((%28 (%58 (\%59. (%58
       (\%62. (%36 (\%105. (($3 ((%67 $2) ((%68 %212) $1))) $0)))))))) (%58
       (\%59. (%58 (\%62. (%36 (\%105. (($3 ((%67 $2) ((%68 %213) $1)))
       $0))))))))))))))))))))))) (%58 (\%214. (%60 (\%215. (%58 (\%62. (%36
       (\%216. (($4 ((%67 $3) ((%68 $2) $1))) $0))))))))))))`)
  val eval_cond_def =
    DT(["DISK_THM"], [],
       `((%28 ((%2 ((%136 ((%67 %59) ((%68 %199) %62))) %105)) ((%112
       ((%113 %105) %59)) ((%113 %105) %62)))) ((%28 ((%2 ((%136 ((%67 %59)
       ((%68 %200) %62))) %105)) ((%114 ((%113 %105) %59)) ((%113 %105)
       %62)))) ((%28 ((%2 ((%136 ((%67 %59) ((%68 %201) %62))) %105))
       ((%115 (%116 (\%117. (%118 (\%119. (%120 (\%121. (\%122. $3))))))))
       ((%123 ((%113 %105) %59)) ((%113 %105) %62))))) ((%28 ((%2 ((%136
       ((%67 %59) ((%68 %202) %62))) %105)) ((%115 (%116 (\%117. (%118
       (\%119. (%120 (\%121. (\%122. $0)))))))) ((%123 ((%113 %105) %59))
       ((%113 %105) %62))))) ((%28 ((%2 ((%136 ((%67 %59) ((%68 %203)
       %62))) %105)) ((%124 ((%113 %105) %59)) ((%113 %105) %62)))) ((%28
       ((%2 ((%136 ((%67 %59) ((%68 %204) %62))) %105)) ((%125 ((%113 %105)
       %59)) ((%113 %105) %62)))) ((%28 ((%2 ((%136 ((%67 %59) ((%68 %205)
       %62))) %105)) ((%126 ((%113 %105) %59)) ((%113 %105) %62)))) ((%28
       ((%2 ((%136 ((%67 %59) ((%68 %91) %62))) %105)) %127)) ((%28 ((%2
       ((%136 ((%67 %59) ((%68 %206) %62))) %105)) (%128 ((%112 ((%113
       %105) %59)) ((%113 %105) %62))))) ((%28 ((%2 ((%136 ((%67 %59) ((%68
       %207) %62))) %105)) ((%129 ((%113 %105) %59)) ((%113 %105) %62))))
       ((%28 ((%2 ((%136 ((%67 %59) ((%68 %208) %62))) %105)) ((%115 (%116
       (\%117. (%118 (\%119. (%120 (\%121. (\%122. (%128 $3))))))))) ((%123
       ((%113 %105) %59)) ((%113 %105) %62))))) ((%28 ((%2 ((%136 ((%67
       %59) ((%68 %209) %62))) %105)) ((%115 (%116 (\%117. (%118 (\%119.
       (%120 (\%121. (\%122. (%128 $0))))))))) ((%123 ((%113 %105) %59))
       ((%113 %105) %62))))) ((%28 ((%2 ((%136 ((%67 %59) ((%68 %210)
       %62))) %105)) ((%130 ((%113 %105) %59)) ((%113 %105) %62)))) ((%28
       ((%2 ((%136 ((%67 %59) ((%68 %211) %62))) %105)) ((%131 ((%113 %105)
       %59)) ((%113 %105) %62)))) ((%28 ((%2 ((%136 ((%67 %59) ((%68 %212)
       %62))) %105)) ((%132 ((%113 %105) %59)) ((%113 %105) %62)))) ((%2
       ((%136 ((%67 %59) ((%68 %213) %62))) %105)) %76))))))))))))))))`)
  val ENUMERATE_CJ =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%20 (\%217. (%40 (\%190. (%36 (\%37. (%218 (\%219.
       ((%28 ((%22 ((%136 $4) $1)) (%220 (\%221. ((%222 ((%223 ((%43 ((%13
       $4) (%88 (%92 %90)))) ((%224 ((%43 $4) ((%44 $3) $2))) ((%225 %73)
       ((%77 %78) ((%79 ((%80 (%226 $5)) ((%80 (%227 (%228 $5))) %81)))
       %82)))))) ((%71 ((%72 %84) ((%74 (%85 (%229 (%228 $5)))) %76)))
       ((%77 %78) ((%79 %81) (%86 $1)))))) ((%43 (%230 ((%231 ((%13 $4)
       (%88 (%92 %90)))) (%86 $1)))) ((%44 $0) $2))))))) ((%22 (%128 ((%136
       $4) $1))) (%220 (\%221. ((%222 ((%223 ((%43 ((%13 $4) (%88 (%92
       %90)))) ((%224 ((%43 $4) ((%44 $3) $2))) ((%225 %73) ((%77 %78)
       ((%79 ((%80 (%226 $5)) ((%80 (%227 (%228 $5))) %81))) %82))))))
       ((%71 ((%72 %84) ((%74 (%85 (%229 (%228 $5)))) %76))) ((%77 %78)
       ((%79 %81) (%86 $1)))))) ((%43 ((%13 $4) (%88 (%89 %90)))) ((%44 $0)
       $2)))))))))))))))))`)
  val CJ_COMPOSITION_LEM_1 =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. (%0 (\%170. (%18 (\%19. (%6
       (\%7. ((%22 ((%28 (%45 $4)) ((%28 (%45 $3)) ((%28 ((%136 $5) (%33
       (%34 $1)))) ((%65 $2) (((%66 $5) $4) $3)))))) (%220 (\%221. (%220
       (\%232. ((%173 (((%25 (((%16 $4) $2) (%11 $3))) ((%13 (%11 $3)) (%14
       $4))) ((%26 $3) %27))) ((%26 ((%43 ((%13 (%11 $3)) (%14 $4))) ((%44
       $1) (%32 (((%25 ((%47 $6) $2)) (%14 $6)) ((%26 ((%43 %50) (%34 $3)))
       %27)))))) (%24 (((%25 (((%16 $6) $2) ((%13 ((%13 (%11 $3)) (%14
       $5))) (%88 (%92 (%92 %90)))))) ((%13 ((%13 ((%13 (%11 $3)) (%14
       $5))) (%88 (%92 (%92 %90))))) (%14 $6))) ((%26 ((%43 ((%13 ((%13
       (%11 $3)) (%14 $5))) (%88 (%92 (%92 %90))))) ((%44 $0) (%33 (%34
       $3))))) ((%233 ((%13 (%11 $3)) (%88 (%92 %90)))) ((%233 (%11 $3))
       %27))))))))))))))))))))))))`)
  val CJ_TERMINATED_LEM_1 =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. (%0 (\%170. (%18 (\%19. (%182
       (\%191. (%6 (\%7. ((%22 ((%28 (%45 $5)) ((%28 (%45 $4)) ((%28 ((%136
       $6) (%33 (%34 $2)))) ((%65 $3) (((%66 $6) $5) $4)))))) (((%179
       (((%16 $3) $0) (%11 $2))) ((%13 (%11 $2)) (%14 $3))) ((%26 $2)
       $1)))))))))))))))))`)
  val CJ_COMPOSITION_LEM_2 =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. (%0 (\%170. (%18 (\%19. (%6
       (\%7. ((%22 ((%28 (%45 $4)) ((%28 (%45 $3)) ((%28 (%128 ((%136 $5)
       (%33 (%34 $1))))) ((%65 $2) (((%66 $5) $4) $3)))))) (%220 (\%221.
       (%220 (\%232. ((%173 (((%25 (((%16 $4) $2) (%11 $3))) ((%13 (%11
       $3)) (%14 $4))) ((%26 $3) %27))) ((%26 ((%43 ((%13 (%11 $3)) (%14
       $4))) ((%44 $1) (%32 (((%25 ((%47 $5) $2)) (%14 $5)) ((%26 ((%43
       %50) (%34 $3))) %27)))))) ((%233 ((%13 ((%13 (%11 $3)) (%88 (%89
       %90)))) (%14 $5))) (%24 (((%25 (((%16 $5) $2) ((%13 (%11 $3)) (%88
       (%89 %90))))) ((%13 ((%13 (%11 $3)) (%88 (%89 %90)))) (%14 $5)))
       ((%26 ((%43 ((%13 (%11 $3)) (%88 (%89 %90)))) ((%44 $0) (%33 (%34
       $3))))) ((%233 ((%13 (%11 $3)) (%88 (%92 %90)))) ((%233 (%11 $3))
       %27)))))))))))))))))))))))))`)
  val CJ_TERMINATED_LEM_2 =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. (%0 (\%170. (%18 (\%19. (%182
       (\%191. (%6 (\%7. ((%22 ((%28 (%45 $5)) ((%28 (%45 $4)) ((%28 (%128
       ((%136 $6) (%33 (%34 $2))))) ((%65 $3) (((%66 $6) $5) $4))))))
       (((%179 (((%16 $3) $0) (%11 $2))) ((%13 (%11 $2)) (%14 $3))) ((%26
       $2) $1)))))))))))))))))`)
  val LENGTH_CJ =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. ((%10 (%14 (((%66 $2) $1) $0)))
       ((%13 ((%13 (%14 $0)) (%88 (%92 (%92 %90))))) (%14 $1)))))))))`)
  val CJ_IS_WELL_FORMED =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. ((%22 ((%28 (%45 $1)) (%45
       $0))) (%45 (((%66 $2) $1) $0)))))))))`)
  val HAORE_CJ_FLAT_LEM_1 =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. (%192 (\%193. (%192 (\%194.
       (%192 (\%195. ((%22 ((%28 (%45 $4)) ((%28 (%45 $3)) ((%28 (%36
       (\%37. ((%22 ($3 $0)) ($2 ((%46 $5) $0)))))) (%36 (\%37. ((%22 ($3
       $0)) ($1 ((%46 $4) $0))))))))) (%36 (\%37. ((%22 ((%28 ($3 $0))
       ((%136 $6) $0))) ($2 ((%46 (((%66 $6) $5) $4))
       $0))))))))))))))))))`)
  val HAORE_CJ_FLAT_LEM_2 =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. (%192 (\%193. (%192 (\%194.
       (%192 (\%195. ((%22 ((%28 (%45 $4)) ((%28 (%45 $3)) ((%28 (%36
       (\%37. ((%22 ($3 $0)) ($2 ((%46 $5) $0)))))) (%36 (\%37. ((%22 ($3
       $0)) ($1 ((%46 $4) $0))))))))) (%36 (\%37. ((%22 ((%28 ($3 $0))
       (%128 ((%136 $6) $0)))) ($1 ((%46 (((%66 $6) $5) $4))
       $0))))))))))))))))))`)
  val HOARE_CJ_FLAT_1 =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. (%192 (\%193. (%192 (\%194.
       (%192 (\%195. ((%22 ((%28 (%45 $4)) ((%28 (%45 $3)) ((%28 (%36
       (\%37. ((%22 ($3 $0)) ($2 ((%46 $5) $0)))))) (%36 (\%37. ((%22 ($3
       $0)) ($1 ((%46 $4) $0))))))))) (%36 (\%37. ((%28 ((%22 ((%28 ($3
       $0)) ((%136 $6) $0))) ($2 ((%46 (((%66 $6) $5) $4)) $0)))) ((%22
       ((%28 ($3 $0)) (%128 ((%136 $6) $0)))) ($1 ((%46 (((%66 $6) $5) $4))
       $0)))))))))))))))))))`)
  val HOARE_CJ_FLAT =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%63. (%0 (\%64. (%192 (\%193. (%192 (\%194.
       (%192 (\%195. ((%22 ((%28 (%45 $4)) ((%28 (%45 $3)) ((%28 (%36
       (\%37. ((%22 ($3 $0)) ($2 ((%46 $5) $0)))))) (%36 (\%37. ((%22 ($3
       $0)) ($1 ((%46 $4) $0))))))))) (%36 (\%37. ((%22 ($3 $0)) (((%234
       ((%136 $6) $0)) ($2 ((%46 (((%66 $6) $5) $4)) $0))) ($1 ((%46 (((%66
       $6) $5) $4)) $0)))))))))))))))))))`)
  val WF_LOOP_IMP_TER =
    DT(["DISK_THM"], [],
       `(%140 (\%141. (%138 (\%139. ((%22 (%142 ((%143 $0) $1))) (%147
       (\%148. (%176 (\%235. ($2 (((%236 $3) $0) $1)))))))))))`)
  val WF_LOOP_IMP_STOPAT =
    DT(["DISK_THM"], [],
       `(%140 (\%141. (%138 (\%139. (%237 (\%238. ((%22 (%142 ((%143 $1)
       $2))) (((%239 $1) $2) %240))))))))`)
  val LOOP_SHORTEST_LESS_LEAST =
    DT(["DISK_THM"], [],
       `(%20 (\%48. (%147 (\%148. (%140 (\%141. (%138 (\%139. ((%22 ((%30
       $3) (((%241 $0) $1) $2))) (%128 ($0 (((%236 $1) $3) $2))))))))))))`)
  val LOOP_SHORTEST_THM =
    DT(["DISK_THM"], [],
       `(%20 (\%48. (%147 (\%148. (%140 (\%141. (%138 (\%139. ((%22 (%142
       ((%143 $0) $1))) ((%22 ((%29 $3) (((%241 $0) $1) $2))) ((%10 (((%241
       $0) $1) $2)) ((%13 (((%241 $0) $1) (((%236 $1) $3) $2)))
       $3))))))))))))`)
  val WF_LOOP_IMP_LEAST =
    DT(["DISK_THM"], [],
       `(%138 (\%139. (%140 (\%141. ((%22 (%142 ((%143 $1) $0))) (%147
       (\%148. ($2 (((%236 $1) (((%241 $2) $1) $0)) $0)))))))))`)
  val UNROLL_LOOP =
    DT(["DISK_THM"], [],
       `(%138 (\%242. (%140 (\%141. (%147 (\%240. ((%22 (%142 ((%143 $2)
       $1))) ((%243 (((%244 ((%245 %128) $2)) $1) $0)) (((%236 $1) (((%241
       $2) $1) $0)) $0)))))))))`)
  val LENGTH_TR =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%1. ((%10 (%14 ((%93 $1) $0))) ((%13 (%14 $0))
       (%88 (%92 (%92 %90)))))))))`)
  val LOOPNUM_BASIC =
    DT(["DISK_THM"], [],
       `(%147 (\%246. (%133 (\%149. (%0 (\%1. ((%22 ((%28 (%150 ((%151 $1)
       $0))) ((%10 ((((%155 $1) $0) %7) %5)) %50))) ((%136 $1) (%32
       %5)))))))))`)
  val LOOPNUM_INDUCTIVE =
    DT(["DISK_THM"], [],
       `(%20 (\%247. (%133 (\%149. (%0 (\%1. ((%22 ((%28 (%150 ((%151 $1)
       $0))) ((%10 ((((%155 $1) $0) %7) %5)) (%248 $2)))) ((%28 (%128
       ((%136 $1) (%32 %5)))) ((%10 $2) ((((%155 $1) $0) %7) (((%25 (((%16
       $0) %7) (%11 (%12 %5)))) ((%13 (%11 (%12 %5))) (%14 $0)))
       %5)))))))))))`)
  val LOOPNUM_INDEPENDENT_OF_CPSR_PCS =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%1. (%6 (\%7. (%20 (\%249. (%20 (\%250. (%40
       (\%41. (%40 (\%42. (%36 (\%37. (%182 (\%183. (%182 (\%184. ((%22
       ((%28 (%45 $8)) (%150 ((%151 $9) $8)))) ((%10 ((((%155 $9) $8) $7)
       ((%26 ((%43 $6) ((%44 $4) $2))) $1))) ((((%155 $9) $8) $7) ((%26
       ((%43 $5) ((%44 $3) $2))) $0))))))))))))))))))))))))`)
  val TR_TERMINATED_LEM =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%1. (%4 (\%5. (%6 (\%7. ((%22 ((%28 (%45 $2))
       (%150 ((%151 $3) $2)))) (((%179 (((%16 ((%93 $3) $2)) $0) (%11 (%12
       $1)))) ((%13 (%11 (%12 $1))) (%14 ((%93 $3) $2)))) $1))))))))))`)
  val FUNPOW_DSTATE =
    DT(["DISK_THM"], [],
       `(%20 (\%247. (%0 (\%1. (%6 (\%7. (%20 (\%249. (%20 (\%250. (%40
       (\%41. (%40 (\%42. (%36 (\%37. (%182 (\%183. (%182 (\%184. ((%22
       (%45 $8)) ((%31 (%32 (((%169 (\%9. (((%25 (((%16 $9) $8) (%11 (%12
       $0)))) ((%13 (%11 (%12 $0))) (%14 $9))) $0))) $9) ((%26 ((%43 $6)
       ((%44 $4) $2))) $1)))) (%32 (((%169 (\%9. (((%25 (((%16 $9) $8) (%11
       (%12 $0)))) ((%13 (%11 (%12 $0))) (%14 $9))) $0))) $9) ((%26 ((%43
       $5) ((%44 $3) $2))) $0)))))))))))))))))))))))))`)
  val UNROLL_TR_LEM =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%1. (%6 (\%7. (%18 (\%19. (%182 (\%191. ((%22
       ((%28 (%45 $3)) ((%28 (%150 ((%151 $4) $3))) (%128 ((%23 ((%13 (%11
       $1)) (%14 ((%93 $4) $3)))) $0))))) (%220 (\%221. (%251 (\%252. (%253
       (\%254. ((%28 ((%173 (((%25 (((%16 ((%93 $7) $6)) $5) (%11 $4)))
       ((%13 (%11 $4)) (%14 ((%93 $7) $6)))) ((%26 $4) $3))) ((%26 ((%43
       ((%13 (%11 $4)) (%14 ((%93 $7) $6)))) ((%44 $2) (%32 (((%169 (\%9.
       (((%25 (((%16 $7) $6) (%11 (%12 $0)))) ((%13 (%11 (%12 $0))) (%14
       $7))) $0))) ((((%155 $7) $6) $5) ((%26 $4) $3))) ((%26 $4) $3))))))
       $1))) (%20 (\%21. ((%22 ((%23 $0) ((%255 $2) $4))) ((%28 ((%29 (%11
       $5)) $0)) ((%30 $0) ((%13 (%11 $5)) (%14 ((%93 $8)
       $7))))))))))))))))))))))))))`)
  val TR_IS_WELL_FORMED =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%0 (\%1. ((%22 ((%28 (%45 $0)) (%150 ((%151 $1)
       $0)))) (%45 ((%93 $1) $0)))))))`)
  val HOARE_TR_FLAT =
    DT(["DISK_THM"], [],
       `(%133 (\%149. (%147 (\%256. (%192 (\%193. ((%22 ((%28 (%45 %1))
       ((%28 (%150 ((%151 $2) %1))) (%36 (\%37. ((%22 ($1 $0)) ($1 ((%46
       %1) $0)))))))) (%36 (\%37. ((%22 ($1 $0)) ((%28 ($1 ((%46 ((%93 $3)
       %1)) $0))) ((%136 $3) ((%46 ((%93 $3) %1)) $0)))))))))))))`)
  val WELL_FORMED_INSTB_LEM =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%6 (\%257. (%6 (\%258. (%4 (\%5. (%4 (\%9. ((%22 ((%28
       (%17 $4)) ((%28 (%3 $4)) ((%28 ((%174 %175) (((%16 $4) $3) (%11 (%12
       $1))))) (%176 (\%167. ((%28 ((%173 $1) (((%169 (%15 %175)) $0) $2)))
       ((%29 $0) (((%156 (\%177. ((%10 (%11 (%12 $0))) ((%13 (%11 (%12
       $3))) (%14 $6))))) (%15 %175)) $2))))))))) ((%173 (((%25 (((%16 $4)
       $3) (%11 (%12 $1)))) ((%13 (%11 (%12 $1))) (%14 $4))) $0)) (((%25
       (((%16 $4) $2) (%11 (%12 $1)))) ((%13 (%11 (%12 $1))) (%14 $4)))
       $0)))))))))))))`)
  val WELL_FORMED_INSTB =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%6 (\%257. (%6 (\%258. (%4 (\%5. ((%22 (%45 $3)) ((%173
       (((%25 (((%16 $3) $2) (%11 (%12 $0)))) ((%13 (%11 (%12 $0))) (%14
       $3))) $0)) (((%25 (((%16 $3) $1) (%11 (%12 $0)))) ((%13 (%11 (%12
       $0))) (%14 $3))) $0)))))))))))`)
  end
  val _ = DB.bindl "ARMComposition"
  [("terminated_def",terminated_def,DB.Def),
   ("closed_def",closed_def,DB.Def), ("get_st_def",get_st_def,DB.Def),
   ("status_independent_def",status_independent_def,DB.Def),
   ("well_formed_def",well_formed_def,DB.Def),
   ("eval_fl_def",eval_fl_def,DB.Def), ("mk_SC_def",mk_SC_def,DB.Def),
   ("mk_CJ_def",mk_CJ_def,DB.Def), ("mk_TR_def",mk_TR_def,DB.Def),
   ("eval_cond_tupled_primitive_def",
    eval_cond_tupled_primitive_def,
    DB.Def), ("eval_cond_curried_def",eval_cond_curried_def,DB.Def),
   ("WF_Loop_def",WF_Loop_def,DB.Def), ("WF_TR_def",WF_TR_def,DB.Def),
   ("loopNum_def",loopNum_def,DB.Def),
   ("FUPDATE_LT_COMMUTES",FUPDATE_LT_COMMUTES,DB.Thm),
   ("FUPDATE_GT_COMMUTES",FUPDATE_GT_COMMUTES,DB.Thm),
   ("TERMINATED_THM",TERMINATED_THM,DB.Thm),
   ("CLOSED_THM",CLOSED_THM,DB.Thm),
   ("CLOSED_MIDDLE_STEP_LEM",CLOSED_MIDDLE_STEP_LEM,DB.Thm),
   ("CLOSED_MIDDLE_LEM",CLOSED_MIDDLE_LEM,DB.Thm),
   ("CLOSED_MIDDLE",CLOSED_MIDDLE,DB.Thm),
   ("CLOSED_PREFIX",CLOSED_PREFIX,DB.Thm),
   ("CLOSED_SUFFIX",CLOSED_SUFFIX,DB.Thm),
   ("TERMINATED_MIDDLE_LEM",TERMINATED_MIDDLE_LEM,DB.Thm),
   ("TERMINATED_MIDDLE",TERMINATED_MIDDLE,DB.Thm),
   ("CLOSED_SEQUENTIAL_COMPOSITION",CLOSED_SEQUENTIAL_COMPOSITION,DB.Thm),
   ("DSTATE_IRRELEVANT_PCS",DSTATE_IRRELEVANT_PCS,DB.Thm),
   ("DSTATE_COMPOSITION",DSTATE_COMPOSITION,DB.Thm),
   ("SEQ_COMPOSITION_FLAT",SEQ_COMPOSITION_FLAT,DB.Thm),
   ("SC_IS_WELL_FORMED",SC_IS_WELL_FORMED,DB.Thm),
   ("UNCOND_JUMP_OVER_THM",UNCOND_JUMP_OVER_THM,DB.Thm),
   ("HOARE_SC_FLAT",HOARE_SC_FLAT,DB.Thm),
   ("eval_cond_ind",eval_cond_ind,DB.Thm),
   ("eval_cond_def",eval_cond_def,DB.Thm),
   ("ENUMERATE_CJ",ENUMERATE_CJ,DB.Thm),
   ("CJ_COMPOSITION_LEM_1",CJ_COMPOSITION_LEM_1,DB.Thm),
   ("CJ_TERMINATED_LEM_1",CJ_TERMINATED_LEM_1,DB.Thm),
   ("CJ_COMPOSITION_LEM_2",CJ_COMPOSITION_LEM_2,DB.Thm),
   ("CJ_TERMINATED_LEM_2",CJ_TERMINATED_LEM_2,DB.Thm),
   ("LENGTH_CJ",LENGTH_CJ,DB.Thm),
   ("CJ_IS_WELL_FORMED",CJ_IS_WELL_FORMED,DB.Thm),
   ("HAORE_CJ_FLAT_LEM_1",HAORE_CJ_FLAT_LEM_1,DB.Thm),
   ("HAORE_CJ_FLAT_LEM_2",HAORE_CJ_FLAT_LEM_2,DB.Thm),
   ("HOARE_CJ_FLAT_1",HOARE_CJ_FLAT_1,DB.Thm),
   ("HOARE_CJ_FLAT",HOARE_CJ_FLAT,DB.Thm),
   ("WF_LOOP_IMP_TER",WF_LOOP_IMP_TER,DB.Thm),
   ("WF_LOOP_IMP_STOPAT",WF_LOOP_IMP_STOPAT,DB.Thm),
   ("LOOP_SHORTEST_LESS_LEAST",LOOP_SHORTEST_LESS_LEAST,DB.Thm),
   ("LOOP_SHORTEST_THM",LOOP_SHORTEST_THM,DB.Thm),
   ("WF_LOOP_IMP_LEAST",WF_LOOP_IMP_LEAST,DB.Thm),
   ("UNROLL_LOOP",UNROLL_LOOP,DB.Thm), ("LENGTH_TR",LENGTH_TR,DB.Thm),
   ("LOOPNUM_BASIC",LOOPNUM_BASIC,DB.Thm),
   ("LOOPNUM_INDUCTIVE",LOOPNUM_INDUCTIVE,DB.Thm),
   ("LOOPNUM_INDEPENDENT_OF_CPSR_PCS",
    LOOPNUM_INDEPENDENT_OF_CPSR_PCS,
    DB.Thm), ("TR_TERMINATED_LEM",TR_TERMINATED_LEM,DB.Thm),
   ("FUNPOW_DSTATE",FUNPOW_DSTATE,DB.Thm),
   ("UNROLL_TR_LEM",UNROLL_TR_LEM,DB.Thm),
   ("TR_IS_WELL_FORMED",TR_IS_WELL_FORMED,DB.Thm),
   ("HOARE_TR_FLAT",HOARE_TR_FLAT,DB.Thm),
   ("WELL_FORMED_INSTB_LEM",WELL_FORMED_INSTB_LEM,DB.Thm),
   ("WELL_FORMED_INSTB",WELL_FORMED_INSTB,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("rich_listTheory.rich_list_grammars",
                          rich_listTheory.rich_list_grammars),
                         ("preARMTheory.preARM_grammars",
                          preARMTheory.preARM_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "terminated")
        {Name = "terminated", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "closed")
        {Name = "closed", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "get_st")
        {Name = "get_st", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "status_independent")
        {Name = "status_independent", Thy = "ARMComposition"}
  val _ = update_grms
       temp_type_abbrev
       ("DSTATE", T"prod" "pair"
 [T"fmap" "finite_map"
   [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
  T"fmap" "finite_map"
   [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]])
  val _ = update_grms
       (temp_overload_on_by_nametype "well_formed")
        {Name = "well_formed", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eval_fl")
        {Name = "eval_fl", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_SC")
        {Name = "mk_SC", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_CJ")
        {Name = "mk_CJ", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_TR")
        {Name = "mk_TR", Thy = "ARMComposition"}
  val _ = update_grms
       temp_type_abbrev
       ("P_DSTATE", (T"prod" "pair"
  [T"fmap" "finite_map"
    [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]],
   T"fmap" "finite_map"
    [T"num" "num" [], T"cart" "fcp" [bool, T"i32" "words" []]]] -->
 bool))
  val _ = update_grms
       (temp_overload_on_by_nametype "eval_cond_tupled")
        {Name = "eval_cond_tupled", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "eval_cond")
        {Name = "eval_cond", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "WF_Loop")
        {Name = "WF_Loop", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "WF_TR")
        {Name = "WF_TR", Thy = "ARMComposition"}
  val _ = update_grms
       (temp_overload_on_by_nametype "loopNum")
        {Name = "loopNum", Thy = "ARMComposition"}
  val ARMComposition_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [terminated_def];  
  
  val _ = computeLib.add_funs [closed_def];  
  
  val _ = computeLib.add_funs [get_st_def];  
  
  val _ = computeLib.add_funs [status_independent_def];  
  
  val _ = computeLib.add_funs [well_formed_def];  
  
  val _ = computeLib.add_funs [eval_fl_def];  
  
  val _ = computeLib.add_funs [mk_SC_def];  
  
  val _ = computeLib.add_funs [mk_CJ_def];  
  
  val _ = computeLib.add_funs [mk_TR_def];  
  
  val _ = computeLib.add_funs [eval_cond_def];  
  
  val _ = computeLib.add_funs [WF_Loop_def];  
  
  val _ = computeLib.add_funs [WF_TR_def];  
  
  val _ = computeLib.add_funs [loopNum_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
