signature DiskFilesHeader =
sig

  type dftables
  val initial_tables : unit -> dftables

  val type_init : dftables -> int -> unit
  val lookup_type : dftables -> int -> Type.hol_type
  val newtype : Type.hol_type -> dftables -> unit

  val term_init : dftables -> int -> unit
  val lookup_term : dftables -> int -> Term.term
  val newterm : dftables -> Term.term -> unit

  val id_init : dftables -> int -> unit
  val lookup_id : dftables -> int -> {Thy:string,Other:string}
  val newid : dftables -> {Thy:string,Other:string} -> unit

end
