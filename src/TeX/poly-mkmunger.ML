val cn = PolyML.Compiler.compilerVersionNumber
val main = munger (551 <= cn andalso cn <= 552);

val output_fname =
    case !buildheap_extra_data of
        NONE => "munge.exe"
      | SOME s => Systeml.protect s
val objfname = output_fname ^ ".o"
val _ = PolyML.export(objfname, main)
val _ = Systeml.systeml (["cc", objfname, "-o", output_fname] @
                         Systeml.POLY_LDFLAGS)
val _ = OS.FileSys.remove objfname
