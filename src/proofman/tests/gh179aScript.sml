open HolKernel Parse boolLib

val _ = new_theory "gh179a";

val tyexists = store_thm("tyexists", “?x:bool. (\x. T) x”,
  BETA_TAC >> REWRITE_TAC[]
);

val foo_TYDEF = new_type_definition("foo", tyexists);

val foo_bijs = define_new_type_bijections {
  ABS = "b2f", REP = "f2b", name = "foo_bijs", tyax = foo_TYDEF
} |> BETA_RULE |> REWRITE_RULE []

val A_def = new_definition ("A_def", ``A = b2f T``)
val B_def = new_definition ("B_def", ``B = b2f F``)

val A_neq_B = store_thm("A_neq_B", “A <> B”,
  REWRITE_TAC[A_def,B_def] >>
  DISCH_THEN (mp_tac o AP_TERM ``f2b``) >>
  REWRITE_TAC [foo_bijs]
);

val _ = delete_type "foo"


val _ = export_theory();
