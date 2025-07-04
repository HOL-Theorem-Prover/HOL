structure LTSprimitives =
struct

infix ++
val op++ = OS.Path.concat

fun primLink {from,to} = Systeml.systeml ["ln" "-sf", from, to]
fun appendToSRCFILES paths =
    let val istrm = TextIO.openAppend (Systeml.HOLDIR ++ "sigobj" ++ "SRCFILES")
    in
      List.app (fn p => TextIO.output(istrm, p ^ "\n")) paths;
      TextIO.closeOut istrm
    end


end
