open HolKernel boolLib lcsymtacs BasicProvers;

val _ = new_theory "bool_defs";

val LET_def = new_definition
  ("LET_def", mk_eq(mk_var("LET",type_of(lhs(concl LET_DEF))),rhs(concl LET_DEF)));

val literal_case_def = new_definition
  ("literal_case_def",
    mk_eq(mk_var("literal_case",type_of(lhs(concl literal_case_DEF))),
          rhs(concl literal_case_DEF)));

val IN_def = new_definition
  ("IN_def", mk_eq(mk_var("IN",type_of(lhs(concl IN_DEF))),rhs(concl IN_DEF)));

val TYPE_DEFINITION_def = new_definition
  ("TYPE_DEFINITION_def",
    mk_eq(mk_var("TYPE_DEFINITION",type_of(lhs(concl TYPE_DEFINITION))),
          rhs(concl TYPE_DEFINITION)));

val LET_thm = PURE_REWRITE_RULE[FUN_EQ_THM]LET_def
 |> BETA_RULE |> curry save_thm "LET_thm";

val literal_case_thm = PURE_REWRITE_RULE[FUN_EQ_THM]literal_case_def
 |> BETA_RULE |> curry save_thm "literal_case_thm";

val IN_thm = PURE_REWRITE_RULE[FUN_EQ_THM]IN_def
 |> BETA_RULE |> curry save_thm "IN_thm";

val T_iff = mk_thm([],``!t. (T <=> t) <=> t``);
val F_iff = mk_thm([],``!t. (F <=> t) <=> ~t``);

val TYPE_DEFINITION_thm = store_thm
  ("TYPE_DEFINITION_thm",
  ``!P. (?(rep:'b->'a). TYPE_DEFINITION P rep) ==>
         ?(rep:'b->'a) abs. (!a. abs (rep a) = a) /\ !r. P r <=> (rep (abs r) = r)``,
  PURE_REWRITE_TAC[TYPE_DEFINITION_def]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt strip_tac
  \\ qexists_tac`rep`
  \\ qexists_tac`\a. @x. a = rep x`
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ conj_tac
  \\ rpt strip_tac
  >- (
    `(\x. rep a = rep x)(@x. rep a = rep x)`
    by (
      match_mp_tac SELECT_AX
      \\ qexists_tac`a`
      \\ CONV_TAC BETA_CONV
      \\ REFL_TAC )
    \\ first_x_assum match_mp_tac
    \\ pop_assum(ACCEPT_TAC o SYM o BETA_RULE) )
  \\ qspec_then`P r`strip_assume_tac BOOL_CASES_AX
  \\ PURE_ASM_REWRITE_TAC[F_iff,T_iff]
  >- (
    `(\x. r = rep x) (@x. r = rep x)`
    by (
      match_mp_tac SELECT_AX
      \\ first_x_assum(qspec_then`r`mp_tac)
      \\ PURE_ASM_REWRITE_TAC[T_iff]
      \\ CONV_TAC(DEPTH_CONV BETA_CONV)
      \\ disch_then ACCEPT_TAC )
    \\ pop_assum(ACCEPT_TAC o SYM o BETA_RULE) )
  \\ first_x_assum(qspec_then`r`mp_tac)
  \\ PURE_ASM_REWRITE_TAC[F_iff]
  \\ Ho_Rewrite.PURE_REWRITE_TAC[NOT_EXISTS_THM]
  \\ disch_then(qspec_then`@x. r = rep x`(ACCEPT_TAC o GSYM)));

val _ = Parse.hide "ARB";
val ARB_def = gen_new_specification("ARB_def",ADD_ASSUM``ARB = @x. F`` TRUTH);
val ARB_thm = save_thm("ARB_thm",REFL``bool_defs$ARB``);

val _ = export_theory();
