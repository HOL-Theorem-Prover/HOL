(* ========================================================================= *)
(* A POSSIBLY-INFINITE STREAM DATATYPE FOR ML                                *)
(* Created by Joe Hurd, April 2001                                           *)
(* ========================================================================= *)

signature mlibStream =
sig

datatype 'a stream = NIL | CONS of 'a * (unit -> 'a stream)

(* If you're wondering how to create an infinite stream: *)
(* val stream4 = let fun s4 () = CONS 4 s4 in s4 () end; *)

val cons          : 'a -> (unit -> 'a stream) -> 'a stream
val null          : 'a stream -> bool
val hd            : 'a stream -> 'a                    (* raises Empty *)
val tl            : 'a stream -> 'a stream             (* raises Empty *)
val dest          : 'a stream -> 'a * 'a stream        (* raises Empty *)
val repeat        : 'a -> 'a stream
val count         : int -> int stream
val fold          : ('a -> (unit -> 'b) -> 'b) -> 'b -> 'a stream -> 'b
val map           : ('a -> 'b) -> 'a stream -> 'b stream
val partial_map   : ('a -> 'b option) -> 'a stream -> 'b stream
val maps          : ('a -> 'c -> 'b * 'c) -> 'c -> 'a stream -> 'b stream
val partial_maps  : ('a -> 'c -> 'b option * 'c) -> 'c -> 'a stream -> 'b stream
val filter        : ('a -> bool) -> 'a stream -> 'a stream
val flatten       : 'a stream stream -> 'a stream
val zipwith       : ('a -> 'b -> 'c) -> 'a stream -> 'b stream -> 'c stream
val zip           : 'a stream -> 'b stream -> ('a * 'b) stream
val take          : int -> 'a stream -> 'a stream      (* raises Subscript *)
val drop          : int -> 'a stream -> 'a stream      (* raises Subscript *)
val to_list       : 'a stream -> 'a list
val from_list     : 'a list -> 'a stream
val from_textfile : string -> string stream            (* lines of the file *)

end