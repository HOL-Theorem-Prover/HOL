structure selftest =
struct

open HolKernel boolLib Parse

structure Parse =
struct
open Parse
val (Type,Term) = parse_from_grammars integerTheory.integer_grammars
end
open Parse

structure Process = OS.Process;

fun die s = (print (s^"\n"); Process.exit Process.failure)

val _ = print "Testing normalisers\n"
fun test (s, f, orig, answer) = let
  val result = QCONV f orig
in
  print (StringCvt.padRight #" " 60 (s ^ "  ``" ^ term_to_string orig ^ "``"));
  if aconv (rhs (concl result)) answer then print "OK\n"
  else die "FAILED!\n"
end
val _ = let
  open intSimps
  val AL = ADDL_CANON_CONV
  val AR = ADDR_CANON_CONV
in
  app test
  [("ADDL_CANON_CONV", AL, ``~3 + ~y + x + x + 4``, ``2 * x + ~y + 1``),
   ("ADDL_CANON_CONV", AL, ``~3 + ~y + x + x + 4 + y``, ``2 * x + 1``),
   ("ADDR_CANON_CONV", AR, ``~3 + ~y + x + x + 4``, ``2 * x + (~y + 1)``),
   ("ADDR_CANON_CONV", AR, ``~3 + ~y + x + x + 4 + y``, ``2 * x + 1``)]
end


val test_level = case CommandLine.arguments() of
                   [] => 1
                 | h::_ => valOf (Int.fromString h)
val progs = if test_level > 1 then ["test_omega.exe", "test_coopers.exe"]
            else ["test_omega.exe"]

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
end; (* struct *)
