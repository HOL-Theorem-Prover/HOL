Theory ex1
Ancestors
  combin pair option prim_rec arithmetic list hol_to_acl2
Libs
  HOL_to_ACL2

Definition Even_Odd_def:
  Even 0 = T ∧
  Even (SUC n) = Odd n ∧
  Odd 0 = F ∧
  Odd (SUC n) = Even n
End

Theorem DIVISION_FOR_ACL2[local] =
    DIVISION
     |> SIMP_RULE bool_ss [PULL_FORALL]
     |> SPEC_ALL
     |> EQT_INTRO
     |> GEN_ALL;

val defs =  (* following ex1.lisp plus a few others *)
   [def_bundle suc_thm,
    def_bundle PRE,
    def_bundle I_THM,
    def_bundle C_THM,
    def_bundle K_THM,
    def_bundle o_THM,
    def_bundle COMMA_def,
    def_bundle FST,
    def_bundle SND,
    def_bundle UNCURRY_DEF,
    def_bundle OPTION_BIND_def,
    def_bundle OPTION_MAP_DEF,
    def_bundle list_case_def,
    def_bundle list_size_def,
    def_bundle MAP,
    def_bundle FOLDR,
    def_bundle FOLDL,
    spec_bundle [``(DIV)``, ``(MOD)``] DIVISION_FOR_ACL2,
    def_bundle Even_Odd_def,
    def_bundle EXP]

val thms =
  [thm_bundle "MAP_ID_I" MAP_ID_I,
   thm_bundle "MAP_o" MAP_o
  ];

val goals =
  [goal_bundle "FST-COMMA" (concl FST),
   goal_bundle "BOOL_CASES_AX" (concl BOOL_CASES_AX),
   goal_bundle "pair_fst_snd_eq" (concl (GSYM PAIR_FST_SND_EQ))];

val _ = print_bundles_to_file "ex1.defhol" (defs @ thms @ goals);
