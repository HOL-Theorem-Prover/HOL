signature stringML = 
sig
  type string = String.string
  type char   = Char.char

  val explode : string -> char list
  val concat  : string list -> string
  val implode : char list -> string
  val map     : (char -> char) -> string -> string
  val extract : string * int * int option -> string
  val collate : (char * char -> order) -> string * string -> order
  val str     : char -> string
  val <= : string * string -> bool
  val >= : string * string -> bool
  val < : string * string -> bool
  val > : string * string -> bool
  val sub : string * int -> char
  val compare : string * string -> order
  val fields : (char -> bool) -> string -> string list
  val isPrefix : string -> string -> bool
  val ^ : string * string -> string
  val fromString : string -> string option
  val toString : string -> string
  val size : string -> int
  val substring : string * int * int -> string
  val translate : (char -> string) -> string -> string
  val tokens : (char -> bool) -> string -> string list

end
