open HolKernel boolLib bossLib BytecodeTheory
val _ = new_theory"bytecodeTermination"

val (bc_fetch_aux_def, bc_fetch_aux_ind) =
  Defn.tprove_no_defn ((bc_fetch_aux_def, bc_fetch_aux_ind),
  WF_REL_TAC `measure (LENGTH o FST)` THEN SRW_TAC [] []);
val _ = save_thm ("bc_fetch_aux_def", bc_fetch_aux_def);
val _ = save_thm ("bc_fetch_aux_ind", bc_fetch_aux_ind);
val _ = export_rewrites["bc_fetch_aux_def"];

val _ = save_thm("bc_fetch_def",bc_fetch_def);
val _ = save_thm("bump_pc_def",bump_pc_def);
val _ = save_thm("bc_find_loc_def",bc_find_loc_def);
val _ = save_thm("bc_next_rules",bc_next_rules);
val _ = save_thm("bc_next_ind",bc_next_ind);
val _ = save_thm("bc_next_cases",bc_next_cases);
val _ = save_thm("bc_stack_op_cases",bc_stack_op_cases);
val _ = save_thm("bool_to_int_def",bool_to_int_def);
val _ = save_thm("calc_len_def",calc_len_def);

val _ = export_theory()
