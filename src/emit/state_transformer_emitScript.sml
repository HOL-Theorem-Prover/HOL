open HolKernel boolLib bossLib Parse;
open EmitML combin_emitTheory pair_emitTheory;
open state_transformerTheory

val _ = new_theory "state_transformer_emit";

val defs = map DEFN [UNIT_DEF, BIND_DEF, MMAP_DEF, JOIN_DEF]

val _ = eSML "state_transformer" defs
val _ = eCAML "state_transformer" defs;

val _ = export_theory ();
