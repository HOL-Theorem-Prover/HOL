signature TheoryDat_Reader =
sig

  datatype token = datatype TheoryDatTokens_dtype.t
  val toString : token -> string


  type buffer
  val current : buffer -> token
  val advance : buffer -> unit
  val eof : buffer -> bool

  val datBuffer : {filename:string} -> buffer

end
