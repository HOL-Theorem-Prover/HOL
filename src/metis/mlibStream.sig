(* ========================================================================= *)
(* A POSSIBLY-INFINITE STREAM DATATYPE FOR ML                                *)
(* Created by Joe Hurd, April 2001                                           *)
(* ========================================================================= *)

signature mlibStream =
sig

type ('a,'b) sum = ('a,'b) mlibUseful.sum

datatype 'a stream = NIL | CONS of 'a * (unit -> 'a stream)

(* If you're wondering how to create an infinite stream: *)
(* val stream4 = let fun s4 () = CONS 4 s4 in s4 () end; *)

(* Basic operations *)
val cons        : 'a -> (unit -> 'a stream) -> 'a stream
val null        : 'a stream -> bool
val hd          : 'a stream -> 'a                      (* raises Empty *)
val tl          : 'a stream -> 'a stream               (* raises Empty *)
val dest        : 'a stream -> 'a * 'a stream          (* raises Empty *)
val repeat      : 'a -> 'a stream
val count       : int -> int stream
val append      : 'a stream -> (unit -> 'a stream) -> 'a stream
val map         : ('a -> 'b) -> 'a stream -> 'b stream
val partial_map : ('a -> 'b option) -> 'a stream -> 'b stream
val zipwith     : ('a -> 'b -> 'c) -> 'a stream -> 'b stream -> 'c stream
val zip         : 'a stream -> 'b stream -> ('a * 'b) stream
val take        : int -> 'a stream -> 'a stream        (* raises Subscript *)
val drop        : int -> 'a stream -> 'a stream        (* raises Subscript *)

(* mlibStream versions of standard list operations that might not terminate *)
val length  : 'a stream -> int
val exists  : ('a -> bool) -> 'a stream -> bool
val all     : ('a -> bool) -> 'a stream -> bool
val filter  : ('a -> bool) -> 'a stream -> 'a stream
val flatten : 'a stream stream -> 'a stream

(* More complicated stream operations *)
type 'a Sthk = unit -> 'a stream
val foldl        : ('a * 's -> ('s,'b) sum) -> 's -> 'a stream -> ('s,'b) sum
val foldr        : ('a * (unit -> 's) -> 's) -> 's -> 'a stream -> 's
val map_thk      : ('a Sthk -> 'a Sthk) -> 'a Sthk -> 'a Sthk
val maps         : ('a -> 's -> 'b * 's) -> 's -> 'a stream -> 'b stream
val partial_maps : ('a -> 's -> 'b option * 's) -> 's -> 'a stream -> 'b stream

(* Maps to other data structures *)
val to_list       : 'a stream -> 'a list
val from_list     : 'a list -> 'a stream
val from_textfile : string -> string stream  (* lines of the file, raises Io *)

end
