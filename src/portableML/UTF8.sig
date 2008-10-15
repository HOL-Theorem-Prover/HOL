signature UTF8 =
sig

  exception BadUTF8 of string
  val getChar : string -> ((string * int) * string) option
  val lastChar : string -> (string * int) option
  val size : string -> int
  val chr : int -> string (* May raise Chr *)

end
