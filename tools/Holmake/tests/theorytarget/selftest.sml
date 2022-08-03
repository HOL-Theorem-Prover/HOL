open testutils

val _ = tprint "Checking 'Holmake fooTheory' in subdir"

val _ = HOLFileSys.chDir "subdir"

val op++ = OS.Path.concat
val result =
    Systeml.systeml ([Globals.HOLDIR ++ "bin" ++ "Holmake"] @
                     (if Systeml.ML_SYSNAME = "poly" then
                        ["--holstate", Globals.HOLDIR ++ "bin" ++ "hol.state0"]
                      else []) @
                     ["fooTheory"])

val _ = if OS.Process.isSuccess result then
          if HOLFileSys.access ("fooTheory.dat", [OS.FileSys.A_READ]) then
            OK()
          else die "fooTheory.dat doesn't exist"
        else die "Holmake failed"
