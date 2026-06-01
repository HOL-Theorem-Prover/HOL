infix ++
val op++ = OS.Path.concat

fun die s = (TextIO.output (TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

fun tprint s =
    TextIO.output (TextIO.stdOut, StringCvt.padRight #" " 60 (s ^ " ... "))
fun ok () = TextIO.output (TextIO.stdOut, "OK\n")

val holmake = Systeml.HOLDIR ++ "bin" ++ "Holmake"

(* Runs before Overlay.ui exists in the build sequence. *)
val baseopts =
    if Systeml.ML_SYSNAME = "poly" then ["--no_overlay", "--poly_not_hol"]
    else ["--no_overlay"]
fun hm xs = Systeml.systeml ([holmake, "-q"] @ baseopts @ xs)

val _ = OS.FileSys.chDir "testdir"

val _ = tprint "Holmake --dirs sub1 sub2 builds both"
val res =
    hm ["--dirs", "sub1", "sub2"]
val _ =
    if OS.Process.isSuccess res andalso
       HOLFileSys.access ("sub1" ++ "A.uo", [OS.FileSys.A_READ]) andalso
       HOLFileSys.access ("sub2" ++ "B.uo", [OS.FileSys.A_READ])
    then ok ()
    else die "Holmake --dirs did not build both targets"

val _ = tprint "Re-running --dirs is a no-op"
val res2 =
    hm ["--dirs", "sub1", "sub2"]
val _ =
    if OS.Process.isSuccess res2 then ok ()
    else die "Second --dirs invocation failed"

val _ = tprint "--dirs with a clean token errors"
val res3 =
    hm ["--dirs", "sub1", "clean"]
val _ =
    if OS.Process.isSuccess res3 then
      die "Holmake should have rejected --dirs ... clean"
    else ok ()

val _ = tprint "--dirs with no positional dirs errors"
val res4 = hm ["--dirs"]
val _ =
    if OS.Process.isSuccess res4 then
      die "Holmake should have rejected bare --dirs"
    else ok ()

val _ = tprint "--dirs rejects non-directory arguments"
val res5 = hm ["--dirs", "sub1/A.sml"]
val _ =
    if OS.Process.isSuccess res5 then
      die "Holmake should have rejected a non-directory under --dirs"
    else ok ()

val _ = tprint "--dirs rejects non-existent arguments"
val res6 = hm ["--dirs", "no-such-dir"]
val _ =
    if OS.Process.isSuccess res6 then
      die "Holmake should have rejected a missing dir under --dirs"
    else ok ()
