signature HOLsexp_parser =
sig

  type t = HOLsexp_dtype.t
  val raw_read_stream : TextIO.instream -> t
  val raw_read_file : string -> t
  val scan : (char, 'a) StringCvt.reader -> (t, 'a) StringCvt.reader

end (* sig *)
