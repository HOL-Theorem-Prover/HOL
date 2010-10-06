signature Profile =
sig

type call_info = {usr : Time.time, sys : Time.time, gc : Time.time, real : Time.time, n : int}

val profile : string -> ('a -> 'b) -> 'a -> 'b
val profile_with_exn : string -> ('a -> 'b) -> 'a -> 'b
val profile_with_exn_name : string -> ('a -> 'b) -> 'a -> 'b
val profile_no_exn : string -> ('a -> 'b) -> 'a -> 'b

val reset1 : string -> unit
val reset_all : unit -> unit

val results : unit -> (string * call_info) list

val print_profile_result  : (string * call_info) -> unit
val print_profile_results : (string * call_info) list -> unit

val output_profile_result : TextIO.outstream -> string * call_info -> unit
val output_profile_results : TextIO.outstream -> (string * call_info) list ->
                             unit

end
