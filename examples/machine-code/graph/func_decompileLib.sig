signature func_decompileLib =
sig

  val add_export_fail : string -> unit
  val clear_export_fails : unit -> unit
  val get_export_fails : unit -> string list
  val func_export : string -> Thm.thm -> Thm.thm -> Thm.thm * string
  val remove_bif_field_insert_conv : Term.term -> Thm.thm
  val func_decompile : (string -> 'a) -> string -> Thm.thm * (Thm.thm * string)
  val get_loction_as_word : string -> Term.term
  val list_mk_union : Term.term list -> Term.term
  val print_title : string -> unit
  val prove_funcs_ok : string list -> Thm.thm

end
