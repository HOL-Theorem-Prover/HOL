signature cond_cleanLib =
sig

  val dest_IMPL_INST_IF_ASM_ASM :
     Thm.thm -> Term.term * (Term.term * Term.term * Term.term) *
                (Term.term * Term.term * Term.term)
  val find_inst_for : Term.term -> Thm.thm list -> Thm.thm
  val negate : Term.term -> Term.term
  val inst_only_updates_pc : Thm.thm -> bool
  val negate_guard : Term.term -> Term.term
  val pc_string : Term.term
  val reduce_inst_under_assum : Term.term -> Thm.thm -> Thm.thm
  val optimisations_count : int ref
  val append_nop_to_if : Thm.thm -> Thm.thm list -> Thm.thm
  val clean_conds : Thm.thm list -> Thm.thm list
  val list_append_nop_to_if : Thm.thm list -> Thm.thm list
  val report_optimisation : string -> int -> int -> int -> unit
  val solve_conv : Conv.conv

end
