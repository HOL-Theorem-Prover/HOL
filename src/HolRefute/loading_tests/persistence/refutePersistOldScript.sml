Theory refutePersistOld
Ancestors
  arithmetic

val _ = new_type ("persist_old", 0);
val _ = new_constant ("persist_old_a", ``:persist_old -> persist_old``);
val _ = new_constant ("persist_old_b", ``:persist_old -> persist_old``);
val _ = new_constant ("persist_old_case_a",
  ``:persist_old -> (persist_old -> 'a) -> 'a``);
val _ = new_constant ("persist_old_case_b",
  ``:persist_old -> (persist_old -> 'a) -> 'a``);

Theorem persist_cross_exists[local]:
  ?b : bool. (\b. T) b
Proof
  qexists_tac `T` >> simp []
QED
val persist_cross_tydef =
  new_type_definition ("persist_cross", persist_cross_exists);
val persist_cross_bij = define_new_type_bijections
  {name = "persist_cross_bij", ABS = "persist_cross_abs",
   REP = "persist_cross_rep", tyax = persist_cross_tydef};
val _ = new_constant
  ("persist_cross_cons", ``:persist_cross -> persist_cross``);
val _ = new_constant ("persist_cross_case",
  ``:persist_cross -> (persist_cross -> 'a) -> 'a``);
