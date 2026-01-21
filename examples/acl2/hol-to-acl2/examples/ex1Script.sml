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
  [suc_thm,
   PRE,
   I_THM,
   C_THM,
   K_THM,
   o_THM,
   COMMA_def,
   FST,
   SND,
   UNCURRY_DEF,
   OPTION_BIND_def,
   OPTION_MAP_DEF,
   list_case_def,
   list_size_def,
   MAP,
   FOLDR,
   FOLDL,
   mk_spec [``(DIV)``, ``(MOD)``] DIVISION_FOR_ACL2,
   Even_Odd_def,
   EXP]

val thms =
  [mk_named_thm "MAP_ID_I" MAP_ID_I,
   mk_named_thm "MAP_o" MAP_o
  ];

val goals =
  [mk_named_goal "FST-COMMA" (concl FST),
   mk_named_goal "BOOL_CASES_AX" (concl BOOL_CASES_AX),
   mk_named_goal "pair_fst_snd_eq" (concl (GSYM PAIR_FST_SND_EQ))];

val _ = print_defhols_to_file "ex1.defhol" (defs @ thms @ goals);
