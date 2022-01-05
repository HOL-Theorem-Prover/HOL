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
            OS.Process.system ("/bin/sh -c 'ulimit -t 4 ; " ^
                               Systeml.HOLDIR ++ "bin" ++ "Holmake" ^
                               (if Systeml.ML_SYSNAME = "poly" then
                                  " --poly_not_hol'"
                                else "'"))
      in
        if OS.Process.isSuccess res then die "sub-Holmake completed"
        else let
          val elapsed = Time.-(Time.now(), now)
        in
          if Time.>(elapsed, Time.fromMilliseconds 4000) then
            die "sub-Holmake took too long"
          else print "OK\n"
        end
      end
    else
      let
        val res = Systeml.systeml [Systeml.HOLDIR ++ "bin" ++ "Holmake"]
      in
        if OS.Process.isSuccess res then die "sub-Holmake completed"
        else print "OK\n"
      end
