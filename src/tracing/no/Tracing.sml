signature Tracing =
sig

val trace_theory : string -> TheoryPP.struct_info_record -> unit

end

structure Tracing :> Tracing =
struct

fun trace_theory _ _ = ()

end
