signature Coding =
sig

  type 'a reader = string -> string * 'a option
  val getc : char reader
  val literal : string -> string reader
  val takeP : (char -> bool) -> string reader
  val || : 'a reader * 'a reader -> 'a reader
  val >- : 'a reader * ('a -> 'b reader) -> 'b reader
  val >> : 'a reader * 'b reader -> 'b reader
  val >* : 'a reader * 'b reader -> ('a * 'b) reader
  val >-> : 'a reader * 'b reader -> 'a reader
  val fail : 'a reader
  val return : 'a -> 'a reader
  val eof : unit reader
  val chop : int -> string reader
  val length_encoded : (string -> 'a option) -> 'a reader
  val lift : 'a reader -> string -> 'a option
  val map : ('a -> 'b) -> 'a reader -> 'b reader
  val many : 'a reader -> 'a list reader

  structure StringData : sig
    val encode : string -> string
    val decode : string -> string option
    val reader : string -> (string * string option)

    val encodel : string list -> string
    val decodel : string -> string list option
  end

  structure IntData : sig
    val encode : int -> string
    val decode : string -> int option
    val reader : string -> (string * int option)
  end

  structure BoolData : sig
    val encode : bool -> string
    val decode : string -> bool option
    val reader : bool reader
  end

end
