val progs = ["test_omega.exe", "test_coopers.exe"]

val _ = FileSys.chDir "testing"

val () =
    if Systeml.systeml (Globals.HOLDIR^"/bin/Holmake" :: progs) = Process.success then
      ()
    else (print "Couldn't compile test programs!\n" ; Process.exit Process.failure)


fun can_run s = FileSys.access (s, [FileSys.A_EXEC])

val _ =
    case List.find (not o can_run) progs of
      SOME s => (print ("No sign of test program: "^s^"; failing\n");
                 Process.exit Process.failure)
    | NONE => ()

fun run s = let
  val fname = FileSys.getDir() ^ "/" ^ s
  val _ = print ("Running test "^s^"\n")
in
  Systeml.systeml [fname] = Process.success
end

val _ = Process.exit (if List.all run progs then Process.success
                      else Process.failure)
