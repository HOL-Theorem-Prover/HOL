(* ========================================================================= *)
(* A POSSIBLY-INFINITE STREAM DATATYPE FOR ML                                *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibStream =
sig

datatype 'a stream = NIL | CONS of 'a * (unit -> 'a stream)

(* If you're wondering how to create an infinite stream: *)
(* val stream4 = let fun s4 () = CONS 4 s4 in s4 () end; *)

(* mlibStream constructors *)
val repeat : 'a -> 'a stream
val count  : int -> int stream
val powers : ('a -> 'a) -> 'a -> 'a stream

(* mlibStream versions of standard list operations: these should all terminate *)
val cons        : 'a -> (unit -> 'a stream) -> 'a stream
val null        : 'a stream -> bool
val hd          : 'a stream -> 'a                      (* raises Empty *)
val tl          : 'a stream -> 'a stream               (* raises Empty *)
val hd_tl       : 'a stream -> 'a * 'a stream          (* raises Empty *)
val sing        : 'a -> 'a stream
val append      : 'a stream -> (unit -> 'a stream) -> 'a stream
val map         : ('a -> 'b) -> 'a stream -> 'b stream
val maps        : ('a -> 's -> 'b * 's) -> 's -> 'a stream -> 'b stream
val zipwith     : ('a -> 'b -> 'c) -> 'a stream -> 'b stream -> 'c stream
val zip         : 'a stream -> 'b stream -> ('a * 'b) stream
val take        : int -> 'a stream -> 'a stream        (* raises Subscript *)
val drop        : int -> 'a stream -> 'a stream        (* raises Subscript *)

(* mlibStream versions of standard list operations: these might not terminate *)
val length       : 'a stream -> int
val exists       : ('a -> bool) -> 'a stream -> bool
val all          : ('a -> bool) -> 'a stream -> bool
val filter       : ('a -> bool) -> 'a stream -> 'a stream
val foldl        : ('a * 's -> 's) -> 's -> 'a stream -> 's
val flatten      : 'a stream stream -> 'a stream
val partial_map  : ('a -> 'b option) -> 'a stream -> 'b stream
val partial_maps : ('a -> 's -> 'b option * 's) -> 's -> 'a stream -> 'b stream

(* mlibStream operations *)
val memoize       : 'a stream -> 'a stream
val to_list       : 'a stream -> 'a list
val from_list     : 'a list -> 'a stream
val to_textfile   : {filename : string} -> string stream -> unit
val from_textfile : {filename : string} -> string stream  (* line by line *)

end
