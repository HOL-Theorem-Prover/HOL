val profile : string -> ('a -> 'b) -> 'a -> 'b

val reset1 : string -> unit
val reset_all : unit -> unit

val results : unit -> (string * {usr : Time.time, sys : Time.time,
                                 gc : Time.time}) list

