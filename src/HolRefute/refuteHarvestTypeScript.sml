Theory refuteHarvestType
Ancestors
  refute

Theorem refute_harvest_split_exists[local]:
  ?n : num. (\n. n < 2) n
Proof
  qexists_tac `0` >> simp []
QED

val refute_harvest_split_tydef =
  new_type_definition
    ("refute_harvest_split", refute_harvest_split_exists);

val refute_harvest_split_home_absrep = define_new_type_bijections
  {name = "refute_harvest_split_home_absrep",
   ABS = "refute_harvest_split_home_abs",
   REP = "refute_harvest_split_home_rep",
   tyax = refute_harvest_split_tydef};

Theorem refute_harvest_split_home_absrep_1:
  !x. refute_harvest_split_home_abs
        (refute_harvest_split_home_rep x) = x
Proof
  metis_tac [refute_harvest_split_home_absrep]
QED

Theorem refute_harvest_split_home_absrep_2:
  !n. (\n. n < 2) n =
      (refute_harvest_split_home_rep
         (refute_harvest_split_home_abs n) = n)
Proof
  metis_tac [refute_harvest_split_home_absrep]
QED

(* Keep the constants and the two non-candidate halves, but remove the only
   conjunction that the lazy harvester could accept in the home theory. *)
val _ = Theory.delete_binding "refute_harvest_split_home_absrep";
