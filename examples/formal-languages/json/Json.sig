signature Json =
sig
  type substring = Substring.substring

 datatype number
    = Int of int
    | Float of real

 datatype json
    = Null
    | LBRACK  (* stack symbol only *)
    | LBRACE  (* stack symbol only *)
    | Boolean of bool
    | Number of number
    | String of string
    | List of json list
    | AList of (string * json) list;

  val fromSubstring  : substring -> json list * substring
  val fromString     : string -> json list * substring
  val fromFile       : string -> json list * substring

  val foldArray      : json -> (json -> 'a option) -> 'a list option
  val foldArray'     : json -> (json -> 'a       ) -> 'a list

  val getObject      : json -> string -> json option
  val getObject'     : json -> string -> json

  val getKeys        : json -> (string list) option
  val getKeys'       : json -> string list

  val getBool        : json -> bool option
  val getBool'       : json -> bool

  val getString      : json -> string option
  val getString'     : json -> string

  val getInt         : json -> int option
  val getInt'        : json -> int

  val getFloat       : json -> real option
  val getFloat'      : json -> real

  val pp_json : json PP.pprinter

end
