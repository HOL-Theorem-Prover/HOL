(* -------------------------------------------------------------------------
   L3
   ------------------------------------------------------------------------- *)

signature L3 =
sig
   val K : 'a -> 'b -> 'a
   val drop : int * 'a list -> 'a list
   val dropString : int * string -> string
   val element : int * 'a list -> 'a
   val equal : ''a -> ''a -> bool
   val for : int * int * (int -> unit) -> unit
   val foreach : 'a list * ('a -> unit) -> unit
   val indexOf : ''a * ''a list -> int option
   val indexOfString : char * string -> int option
   val fst : 'a * 'b -> 'a
   val listCompare : ('a * 'a -> order) -> 'a list * 'a list -> order
   val listUpdate : 'a * (int * 'a list) -> 'a list
   val lowercase : string -> string
   val memString : char * string -> bool
   val padLeft : 'a * (int * 'a list) -> 'a list
   val padLeftString : char * (int * string) -> string
   val padRight : 'a * (int * 'a list) -> 'a list
   val padRightString : char * (int * string) -> string
   val pairCompare :
    ('a * 'a -> order) * ('b * 'b -> order) -> ('a * 'b) * ('a * 'b) -> order
   val prefix : char * string -> string
   val remove : ''a list * ''a list -> ''a list
   val removeExceptString : string * string -> string
   val removeString : string * string -> string
   val removeDuplicatesString : string -> string
   val revLookup : ('a -> 'a -> bool) -> 'a * 'a list -> int option
   val revString : string -> string
   val snd : 'a * 'b -> 'b
   val splitl : (char -> bool) * string -> string * string
   val splitr : (char -> bool) * string -> string * string
   val strHd : string -> char
   val strTl : string -> string
   val stringToChar : string -> char
   val stringUpdate : char * (int * string) -> string
   val swap : 'a * 'b -> 'b * 'a
   val take : int * 'a list -> 'a list
   val takeString : int * string -> string
   val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
   val update : (''a -> 'b) -> ''a -> 'b -> ''a -> 'b
   val uppercase : string -> string
end
