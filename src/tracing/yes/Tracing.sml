signature Tracing =
sig

val trace_theory : string -> TheoryPP.struct_info_record -> unit

end

structure Tracing :> Tracing =
struct

open TheoryPP

fun trace_theory name
    ({theory,parents,types,constants,axioms,definitions,theorems,mldeps,...}: struct_info_record) = let
  val file = concat[".holobjs/",name,".tr"]
  val () = Portable.export(file, (theory,parents,types,constants,axioms,definitions,theorems,mldeps))
  val _ = Unix.execute ("/usr/bin/gzip", ["-f", file])
in () end

end
