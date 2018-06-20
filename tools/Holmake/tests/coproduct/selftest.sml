open testutils

val hmstr = OS.Path.concat (Globals.HOLDIR, OS.Path.concat("bin", "Holmake"))
val _ = OS.FileSys.chDir "testdir";

fun hm testname tgts test =
  (tprint testname ;
   Systeml.systeml (hmstr::"-q"::tgts);
   if test() then OK() else die "FAILED!")

fun present n = OS.FileSys.access(n, [OS.FileSys.A_READ])

fun delete n = OS.FileSys.remove n handle SysErr _ => ()

fun testscenario hm =
  let
  in
    hm "Cleaning" ["-r", "cleanAll"]
       (fn () => List.all (not o present)
                          ["foo", "bar", "master",
                           "simpleTheory.sig", "simpleTheory.sml"]);
    hm "Default make builds foo/bar/master" []
       (fn () => List.all present ["foo", "bar", "master"]);
    hm "Cleaning" ["cleanAll"]
       (fn () => List.all (not o present)
                          ["foo", "simpleTheory.sig", "simpleTheory.sml"]);
    hm "Explicit make foo builds all" ["foo"]
       (fn () => List.all present ["foo", "simpleTheory.sig",
                                   "simpleTheory.sml"]);

    delete "simpleTheory.sml";

    hm "rm thy.sml; build; no change" []
       (fn () => not (present "simpleTheory.sml"));

    hm "rm thy.sml; build foo; no change" ["foo"]
       (fn () => not (present "simpleTheory.sml"));

    hm "rm thy.sml; build thy.sig; no change" ["simpleTheory.sig"]
       (fn () => not (present "simpleTheory.sml"));

    hm "rm thy.sml; build thy.sml; builds it" ["simpleTheory.sml"]
       (fn () => present "simpleTheory.sml");

    delete "simpleTheory.sml";
    hm "rm thy.sml; build thy.sig thy.sml; builds it"
       ["simpleTheory.sig", "simpleTheory.sml"]
       (fn () => present "simpleTheory.sml");

    delete "simpleTheory.sml";
    hm "rm thy.sml; build thy.sml thy.sig; builds it"
       ["simpleTheory.sml", "simpleTheory.sig"]
       (fn () => present "simpleTheory.sml")
end

val _ = testscenario hm
val _ = testscenario
          (fn s => fn tgts => fn f => hm (s^" (-j1)") ("-j1"::tgts) f)
