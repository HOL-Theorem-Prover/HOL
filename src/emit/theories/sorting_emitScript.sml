open HolKernel boolLib bossLib Parse;
open EmitML sortingTheory;
open list_emitTheory;

val _ = new_theory "sorting_emit";

val defs =
  OPEN ["list"] :: map DEFN [PART_DEF, PARTITION_DEF, QSORT_DEF, SORTED_DEF];

val _ = eSML "sorting" defs;
val _ = eCAML "sorting" defs;

val _ = export_theory ();
