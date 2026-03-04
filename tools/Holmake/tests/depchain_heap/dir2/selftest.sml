open testutils Systeml

infix ++
val op++ = OS.Path.concat

val _ = tprint "Test that hol buildheap fails"

val stat = systeml [HOLDIR ++ "bin" ++ "hol", "buildheap", "-q", "-o", "heap", "-b",
                    HOLDIR ++ "bin" ++ "hol.state0", "../thy1Theory"]

val _ = if OS.Process.isSuccess stat then die "FAILED!" else OK()
