signature DiskThms =
sig

  val ppwrite : ppstream -> (string * Thm.thm) list -> unit
  val write_stream : TextIO.outstream -> (string * Thm.thm) list -> unit
  val write_file : string -> (string * Thm.thm) list -> unit
  val read_stream : TextIO.instream -> (string * Thm.thm) list
  val read_file : string -> (string * Thm.thm) list

end
