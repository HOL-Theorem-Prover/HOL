signature Systeml =
sig

  val systeml : string list -> Process.status
  val xable_string : string -> string
  val mk_xable : string -> string

  val emit_hol_script : string -> string -> string -> string -> string
  val emit_hol_unquote_script : string -> string -> string -> string ->
                                string -> string -> string

  (* configuration time constants *)
  val HOLDIR : string
  val MOSMLDIR : string
  val OS : string
  val DEPDIR : string
  val GNUMAKE : string



end;
