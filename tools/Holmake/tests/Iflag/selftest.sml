open testutils

val _ = tprint "Testing a -I cleanAll"
val res = OS.Process.system (Systeml.HOLDIR ^
                             "/bin/Holmake -q -I includethis -r cleanAll")

val _ =
    if OS.Process.isSuccess res andalso
       not (OS.FileSys.access ("includethis/ATheory.sml", [OS.FileSys.A_READ]))
    then
      OK()
    else die ""

val _ = tprint "Testing Holmake -I includethis"

val res = OS.Process.system
            (Systeml.HOLDIR ^
             "/bin/Holmake -q  -I includethis BTheory.uo > /dev/null");

val _ = if OS.Process.isSuccess res then OK()
        else die ""
