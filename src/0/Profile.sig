val profile : string -> ('a -> 'b) -> 'a -> 'b

val reset1 : string -> unit
val reset_all : unit -> unit

val results : unit -> (string * {usr : Time.time, sys : Time.time,
                                 gc : Time.time}) list

val print_profile_result  : (string * {usr : Time.time, sys : Time.time,
                                       gc : Time.time}) -> unit
val print_profile_results : (string * {usr : Time.time, sys : Time.time,
                                       gc : Time.time}) list -> unit
