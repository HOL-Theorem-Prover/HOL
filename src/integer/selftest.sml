fun die s = (print (s^"\n"); Process.exit Process.failure)

val progs = ["test_omega.exe", "test_coopers.exe"]

val _ = FileSys.chDir "testing"
        handle OS.SysErr _ => die "No testing directory"
open Systeml


fun cleanup () = systeml [HOLDIR ^ "/bin/Holmake", "cleanAll"]

val () =
    if cleanup() = Process.success then ()
    else die "Couldn't cleanup in testing directory";

val () =
    if systeml (HOLDIR^"/bin/Holmake" :: progs) = Process.success then ()
    else die "Couldn't compile test programs!" ;


fun can_run s = FileSys.access (s, [FileSys.A_EXEC])

val _ =
    case List.find (not o can_run) progs of
      SOME s => die ("No sign of test program: "^s^"; failing")
    | NONE => ()

fun run s = let
  val fname = FileSys.getDir() ^ "/" ^ s
  val _ = print ("Running test "^s^"\n")
in
  Systeml.systeml [fname] = Process.success
end

val _ = Process.atExit (ignore o cleanup)

val _ = Process.exit (if List.all run progs then Process.success
                      else Process.failure)
