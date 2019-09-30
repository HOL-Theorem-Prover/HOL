signature hhTptp =
sig

include Abbrev

  val write_type : TextIO.outstream -> hol_type -> unit
  val write_term : TextIO.outstream -> term -> unit
  val write_pred : TextIO.outstream -> term -> unit
  val write_formula : TextIO.outstream -> term -> unit
  val write_tptp_file : string -> (string * term) list -> term -> unit
  val write_tptp : string -> (string * term) list -> term -> unit

end
