structure Tracing :> Tracing =
struct

open TheoryPP

fun export (file, x: 'a) = let
  val _ = PolyML.shareCommonData x
  val body = PolyML.exportSmall x
  val ostream = BinIO.openOut file
  val () = BinIO.output (ostream, body)
  val () = BinIO.closeOut ostream
in () end

fun trace_theory name
    ({theory,parents,types,constants,all_thms,mldeps,...}: struct_info_record) = let
  val file = concat[".hol/objs/",name,".tr"]
  val () = export(file, (theory,parents,types,constants,all_thms,mldeps))
  val _ = Unix.execute ("/usr/bin/gzip", ["-f", file])
in () end

end
