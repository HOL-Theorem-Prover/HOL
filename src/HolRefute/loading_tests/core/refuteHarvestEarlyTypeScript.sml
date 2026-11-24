Theory refuteHarvestEarlyType

(* A typedef whose home theory carries nothing about its bijection; the
   abs/rep constants and the bijection live in [refuteHarvestEarlyAbs]. *)
Theorem refute_harvest_early_exists[local]:
  ?n : num. (\n. n < 2) n
Proof
  qexists_tac `0` >> simp []
QED

val refute_harvest_early_tydef =
  new_type_definition
    ("refute_harvest_early", refute_harvest_early_exists);
