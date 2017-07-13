open testutils

val hmstr = OS.Path.concat (Globals.HOLDIR, OS.Path.concat("bin", "Holmake"))
val _ = OS.FileSys.chDir "testdir";

fun hm testname tgts test =
  (tprint testname ;
   Systeml.systeml (hmstr::"-q"::tgts);
   if test() then OK() else die "FAILED!")

fun present n = OS.FileSys.access(n, [OS.FileSys.A_READ])

fun delete n = OS.FileSys.remove n handle SysErr _ => ()

val _ = hm "Cleaning" ["cleanAll"]
           (fn () => List.all (not o present)
                              ["foo", "simpleTheory.sig", "simpleTheory.sml"])

val _ = hm "Default make builds foo" [] (fn () => present "foo")

val _ = delete "simpleTheory.sml"

val _ = hm "rm thy.sml; build; no change" []
           (fn () => not (present "simpleTheory.sml"))

val _ = hm "rm thy.sml; build foo; no change" ["foo"]
           (fn () => not (present "simpleTheory.sml"))

val _ = hm "rm thy.sml; build thy.sig; no change" ["simpleTheory.sig"]
           (fn () => not (present "simpleTheory.sml"))

val _ = hm "rm thy.sml; build thy.sml; builds it" ["simpleTheory.sml"]
           (fn () => present "simpleTheory.sml")

val _ = delete "simpleTheory.sml"
val _ = hm "rm thy.sml; build thy.sig thy.sml; builds it"
           ["simpleTheory.sig", "simpleTheory.sml"]
           (fn () => present "simpleTheory.sml")

val _ = delete "simpleTheory.sml"
val _ = hm "rm thy.sml; build thy.sml thy.sig; builds it"
           ["simpleTheory.sml", "simpleTheory.sig"]
           (fn () => present "simpleTheory.sml")
