(* -------------------------------------------------------------------------
   L3
   ------------------------------------------------------------------------- *)

signature L3 =
sig
   val K : 'a -> 'b -> 'a
   val equal : ''a -> ''a -> bool
   val for : int * int * (int -> 'a) -> unit
   val fst : 'a * 'b -> 'a
   val listCompare : ('a * 'a -> order) -> 'a list * 'a list -> order
   val lowercase : string -> string
   val mem : ''a * ''a list -> bool
   val mkSet : ''a list -> ''a list
   val padLeft : 'a * (int * 'a list) -> 'a list
   val padLeftString : char * (int * string) -> string
   val padRight : 'a * (int * 'a list) -> 'a list
   val padRightString : char * (int * string) -> string
   val pairCompare :
    ('a * 'a -> order) * ('b * 'b -> order) -> ('a * 'b) * ('a * 'b) -> order
   val prefix : char * string -> string
   val revString : string -> string
   val snd : 'a * 'b -> 'b
   val splitl : (char -> bool) * string -> string * string
   val splitr : (char -> bool) * string -> string * string
   val strHd : string -> char
   val strTl : string -> string
   val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
   val update : (''a -> 'b) -> ''a -> 'b -> ''a -> 'b
   val uppercase : string -> string
end
