signature AssembleHolfootParser =
sig
  val raw_read_stream : TextIO.instream -> Parsetree.p_top
  val raw_read_file : string -> Parsetree.p_top
  val print_parse_error : string -> unit;
end
