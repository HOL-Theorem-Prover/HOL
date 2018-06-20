val _ = OS.FileSys.chDir "loopingdir";

infix ++
val op++ = OS.Path.concat

val _ = print "Calling Holmake in loopingdir"

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

val _ =
    if Systeml.isUnix then
      let
        val now = Time.now()
        val res =
            OS.Process.system ("/bin/sh -c 'ulimit -t 2 ; " ^
                               Systeml.HOLDIR ++ "bin" ++ "Holmake'")
      in
        if OS.Process.isSuccess res then die "FAILED!?"
        else let
          val elapsed = Time.-(Time.now(), now)
        in
          if Time.>(elapsed, Time.fromMilliseconds 1500) then
            die "FAILED!"
          else print "OK\n"
        end
      end
    else
      let
        val res = Systeml.systeml [Systeml.HOLDIR ++ "bin" ++ "Holmake'"]
      in
        if OS.Process.isSuccess res then die "FAILED!?"
        else print "OK\n"
      end
