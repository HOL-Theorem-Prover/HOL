signature AssembleDiskFiles =
sig
  val read_stream : TextIO.instream -> (string * Thm.thm) list
  val read_file : string -> (string * Thm.thm) list
end
