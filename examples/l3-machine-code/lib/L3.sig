(* -------------------------------------------------------------------------
   L3
   ------------------------------------------------------------------------- *)

signature L3 =
sig
   val K : 'a -> 'b -> 'a
   val chr : IntInf.int -> char
   val drop : IntInf.int * 'a list -> 'a list
   val dropString : IntInf.int * string -> string
   val element : IntInf.int * 'a list -> 'a
   val equal : ''a -> ''a -> bool
   val for : IntInf.int * IntInf.int * (IntInf.int -> unit) -> unit
   val foreach : 'a list * ('a -> unit) -> unit
   val indexOf : ''a * ''a list -> IntInf.int option
   val indexOfString : char * string -> IntInf.int option
   val fst : 'a * 'b -> 'a
   val length : 'a list -> IntInf.int
   val listCompare : ('a * 'a -> order) -> 'a list * 'a list -> order
   val listUpdate : 'a * (IntInf.int * 'a list) -> 'a list
   val lowercase : string -> string
   val memString : char * string -> bool
   val ord : char -> IntInf.int
   val padLeft : 'a * (IntInf.int * 'a list) -> 'a list
   val padLeftString : char * (IntInf.int * string) -> string
   val padRight : 'a * (IntInf.int * 'a list) -> 'a list
   val padRightString : char * (IntInf.int * string) -> string
   val pairCompare :
    ('a * 'a -> order) * ('b * 'b -> order) -> ('a * 'b) * ('a * 'b) -> order
   val prefix : char * string -> string
   val remove : ''a list * ''a list -> ''a list
   val removeExceptString : string * string -> string
   val removeString : string * string -> string
   val removeDuplicatesString : string -> string
   val revLookup : ('a -> 'a -> bool) -> 'a * 'a list -> IntInf.int option
   val revString : string -> string
   val size : string -> IntInf.int
   val snd : 'a * 'b -> 'b
   val splitl : (char -> bool) * string -> string * string
   val splitr : (char -> bool) * string -> string * string
   val strHd : string -> char
   val strTl : string -> string
   val stringToChar : string -> char
   val stringUpdate : char * (IntInf.int * string) -> string
   val swap : 'a * 'b -> 'b * 'a
   val take : IntInf.int * 'a list -> 'a list
   val takeString : IntInf.int * string -> string
   val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
   val update : (''a -> 'b) -> ''a -> 'b -> ''a -> 'b
   val uppercase : string -> string
end
