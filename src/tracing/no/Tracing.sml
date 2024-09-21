signature Tracing =
sig

open TheoryPP
val trace_theory : string -> struct_info_record -> unit

end

structure Tracing :> Tracing =
struct

fun trace_theory _ _ = ()

end
