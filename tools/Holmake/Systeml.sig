signature Systeml =
sig

  val systeml : string list -> Process.status
  val protect : string -> string
  val xable_string : string -> string
  val mk_xable : string -> string

(* first argument to these are the name of the desired executable, the
   second is the name of the post-initialisation script to run. *)
  val emit_hol_script : string -> string -> string
  val emit_hol_unquote_script : string -> string -> string

  (* configuration time constants *)
  val HOLDIR : string
  val MOSMLDIR : string
  val OS : string
  val DEPDIR : string
  val GNUMAKE : string

end;
