(* Regression tests for INCLUDES-walk propagation of
   .hol/make-deps/lastmaker.

   Holmake used to write the lastmaker file only in the directory it
   was started in.  After the fix, every directory reached via
   INCLUDES (or PRE_INCLUDES) also gets one with the same content, so
   downstream tools (the emacs mode, recursive Holmake invocations on
   subtrees) can identify the right binary from any of them.

   To avoid silently destroying useful state when two HOL
   installations share a tree, propagation refuses to overwrite an
   existing lastmaker that points at a *different* usable Holmake
   binary, and emits a prominent warning instead.  A garbage
   pointer (an executable that no longer exists) is treated as stale
   and overwritten. *)

open testutils

infix ++
val op++ = OS.Path.concat

fun read_file f =
    let val s = TextIO.openIn f
    in TextIO.inputAll s before TextIO.closeIn s end

fun safedel p = OS.FileSys.remove p handle _ => ()
fun safermdir p = OS.FileSys.rmDir p handle _ => ()

fun clean_lastmaker_in dir = let
  val depdir = dir ++ ".hol" ++ "make-deps"
in
  safedel (depdir ++ "lastmaker");
  safermdir depdir;
  safermdir (dir ++ ".hol")
end

fun rstrip s =
    Substring.string (Substring.dropr Char.isSpace (Substring.full s))

fun read_lastmaker dir =
    let val lm = dir ++ ".hol" ++ "make-deps" ++ "lastmaker"
    in if OS.FileSys.access (lm, [OS.FileSys.A_READ]) then
         SOME (rstrip (read_file lm))
       else NONE
    end

fun write_lastmaker_with_content dir content =
    let val depdir = dir ++ ".hol" ++ "make-deps"
        val _ = OS.FileSys.mkDir (dir ++ ".hol")
                handle OS.SysErr _ => ()
        val _ = OS.FileSys.mkDir depdir handle OS.SysErr _ => ()
        val strm = TextIO.openOut (depdir ++ "lastmaker")
    in TextIO.output (strm, content ^ "\n"); TextIO.closeOut strm end

val real_holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val fixture = "fixture"
val sub     = fixture ++ "sub"

fun cleanup () = (app clean_lastmaker_in [fixture, sub])
val _ = cleanup()
val _ = OS.Process.atExit cleanup

val outputlog = "lastmaker_propagation-output"
val _ = safedel outputlog
val _ = OS.Process.atExit (fn () => safedel outputlog)

fun run_holmake_in dir =
    let val cmd = String.concatWith " "
                    [real_holmake, "-C", dir, "--no-cache", "-n",
                     ">", outputlog, "2>&1"]
        val res = OS.Process.system cmd
        val out = read_file outputlog handle _ => ""
    in (res, out) end

fun dump out =
    (print "\n--- captured Holmake output ---\n"; print out;
     print "--- end captured output ---\n")

(* ----------------------------------------------------------------------
   Test 1: clean propagation
   ---------------------------------------------------------------------- *)
val _ = tprint "lastmaker propagates into INCLUDES-visited subdirectories"
val _ = cleanup()
val (res1, out1) = run_holmake_in fixture
val _ = if OS.Process.isSuccess res1 then ()
        else (dump out1; die "Holmake exited non-zero")
val _ = case read_lastmaker fixture of
            NONE => (dump out1; die "fixture/.hol/make-deps/lastmaker absent")
          | SOME got =>
            if got = real_holmake then ()
            else (dump out1;
                  die ("fixture lastmaker content: " ^ Lib.quote got))
val _ = case read_lastmaker sub of
            NONE => (dump out1; die "fixture/sub/.hol/make-deps/lastmaker absent")
          | SOME got =>
            if got = real_holmake then ()
            else (dump out1;
                  die ("sub lastmaker content: " ^ Lib.quote got))
val _ = OK ()

(* ----------------------------------------------------------------------
   Test 2: conflicting existing lastmaker is preserved and warned
   /bin/cat stands in as a "different but real executable" -- any
   readable+executable file path will do.
   ---------------------------------------------------------------------- *)
val other_executable = "/bin/cat"
val _ = if OS.FileSys.access (other_executable, [OS.FileSys.A_EXEC]) then ()
        else die ("test prerequisite missing: " ^ other_executable)

val _ = tprint "conflicting lastmaker is preserved, with a warning"
val _ = cleanup()
val _ = write_lastmaker_with_content sub other_executable
val (res2, out2) = run_holmake_in fixture
val _ = if OS.Process.isSuccess res2 then ()
        else (dump out2; die "Holmake exited non-zero")
val _ = case read_lastmaker sub of
            NONE => (dump out2; die "sub lastmaker disappeared")
          | SOME got =>
            if got = other_executable then ()
            else (dump out2;
                  die ("sub lastmaker was clobbered to: " ^ Lib.quote got))
val _ = if String.isSubstring "WARNING" out2 andalso
           String.isSubstring "lastmaker" out2
        then ()
        else (dump out2; die "expected conflict warning not emitted")
val _ = OK ()

(* ----------------------------------------------------------------------
   Test 3: stale lastmaker (nonexistent path) is replaced silently
   ---------------------------------------------------------------------- *)
val _ = tprint "stale lastmaker pointing nowhere is replaced"
val _ = cleanup()
val _ = write_lastmaker_with_content sub
          "/this/path/does/not/exist/Holmake"
val (res3, out3) = run_holmake_in fixture
val _ = if OS.Process.isSuccess res3 then ()
        else (dump out3; die "Holmake exited non-zero")
val _ = case read_lastmaker sub of
            NONE => (dump out3; die "sub lastmaker disappeared")
          | SOME got =>
            if got = real_holmake then ()
            else (dump out3;
                  die ("sub lastmaker still stale: " ^ Lib.quote got))
val _ = OK ()
