Theory gh179a[bare]
Libs
  HolKernel Parse boolLib

val tyexists = store_thm("tyexists", “?x:bool. (\x. T) x”,
  BETA_TAC >> REWRITE_TAC[]
);

val foo_TYDEF = new_type_definition("foo", tyexists);

val foo_bijs = define_new_type_bijections {
  ABS = "b2f", REP = "f2b", name = "foo_bijs", tyax = foo_TYDEF
} |> BETA_RULE |> REWRITE_RULE []

Definition A_def[nocompute]: A = b2f T
End
Definition B_def[nocompute]: B = b2f F
End

val A_neq_B = store_thm("A_neq_B", “A <> B”,
  REWRITE_TAC[A_def,B_def] >>
  DISCH_THEN (mp_tac o AP_TERM ``f2b``) >>
  REWRITE_TAC [foo_bijs]
);

val _ = delete_type "foo"
