signature AssembleHolfootParser =
sig
  val raw_read_stream : TextIO.instream -> Parsetree.p_program
  val raw_read_file : string -> Parsetree.p_program
  val print_parse_error : string -> unit;
end
