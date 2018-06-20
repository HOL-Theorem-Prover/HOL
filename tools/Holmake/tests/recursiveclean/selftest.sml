infix ++
val op++ = OS.Path.concat

fun touch p = TextIO.closeOut (TextIO.openOut p)
fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

fun safedel p = OS.FileSys.remove p handle OS.SysErr _ => ()
fun contents p =
  let
    val strm = TextIO.openIn p
  in
    TextIO.inputAll strm before
    TextIO.closeIn strm
  end
fun exists p = OS.FileSys.access(p, [])

val testfiles = ["../depchain1/dir3/foo.uo", "../depchain1/dir2/dir1/bar.uo",
                 "../depchain1/dir2/foo"]

val _ = app touch testfiles
val _ = case List.find (not o exists) testfiles of
            NONE => ()
          | SOME f => die ("Didn't manage to touch "^f)


val dir = OS.FileSys.getDir()
val _ = OS.Process.atExit
          (fn () => (OS.FileSys.chDir dir;
                     app safedel ("../depchain1/dir3/log" :: testfiles)))


val _ = OS.FileSys.chDir "../depchain1/dir3"

val res =
    Systeml.systeml [Systeml.HOLDIR ++ "bin" ++ "Holmake", "-r", "cleanAll"]

val _ = OS.Process.isSuccess res orelse die "Holmake didn't exit successfully"

val _ = OS.FileSys.chDir dir

val _ = case List.find exists testfiles of
            NONE => ()
          | SOME f => die ("Holmake left "^f^" still present")
