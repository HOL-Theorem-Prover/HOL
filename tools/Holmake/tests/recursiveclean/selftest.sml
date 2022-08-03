infix ++
val op++ = OS.Path.concat

fun touch p = HOLFileSys.closeOut (HOLFileSys.openOut p)
fun die s = (HOLFileSys.output(HOLFileSys.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

fun safedel p = HOLFileSys.remove p handle OS.SysErr _ => ()
fun contents p =
  let
    val strm = HOLFileSys.openIn p
  in
    HOLFileSys.inputAll strm before
    HOLFileSys.closeIn strm
  end
fun exists p = HOLFileSys.access(p, [])

val testfiles = ["../depchain1/dir3/foo.uo",
                 "../depchain1/dir2/dir1/bar.uo",
                 "../depchain1/dir2/foo"]

val _ = app touch testfiles
val _ = case List.find (not o exists) testfiles of
            NONE => ()
          | SOME f => die ("Didn't manage to touch "^f)


val dir = HOLFileSys.getDir()
val _ = OS.Process.atExit
          (fn () => (FileSys.chDir dir;
                     app safedel ("../depchain1/dir3/log" :: testfiles)))


val _ = HOLFileSys.chDir "../depchain1/dir3"

val res =
    Systeml.systeml [Systeml.HOLDIR ++ "bin" ++ "Holmake", "-r", "cleanAll"]

val _ = OS.Process.isSuccess res orelse die "Holmake didn't exit successfully"

val _ = HOLFileSys.chDir dir

val _ = case List.find exists testfiles of
            NONE => ()
          | SOME f => die ("Holmake left "^f^" still present")
