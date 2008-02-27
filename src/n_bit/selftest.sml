open HolKernel Parse boolLib

val _ = print "Calling mkword 16 to build a theory of 16-bit words\n";
val result = Systeml.systeml ["./mkword.exe", "16"]

(* cleanup *)
val successp = (result = OS.Process.success)

val _ = print "Cleaning up\n";
fun remove s = FileSys.remove s handle Interrupt => raise Interrupt
                                     | e => ()
val _ = app remove (map (fn s => "word16"^s)
                    ["Lib.sml", "Lib.ui", "Lib.uo", "Theory.sig",
                     "Theory.sml", "Theory.ui", "Theory.uo"])

(* can't just return result as this frobs a Mosml bug of some sort *)
val _ = OS.Process.exit
          (if successp then OS.Process.success else OS.Process.failure)

