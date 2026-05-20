(* Regression tests for INCLUDES-walk propagation of
   .hol/make-deps/lastmaker.

   Holmake used to write the lastmaker file only in the directory it
   was started in.  After the fix, every directory reached via
   INCLUDES (or PRE_INCLUDES) also gets one with the same content, so
   downstream tools (the emacs mode, recursive Holmake invocations on
   subtrees) can identify the right binary from any of them.

   Propagation is intentionally skipped when Holmake is launched
   from under any HOLDIR -- HOLDIR-relative resolution disambiguates
   on its own, and INCLUDES walks starting inside a HOLDIR don't
   leave it -- so the tests must drive Holmake from a directory that
   isn't itself under a HOL distribution.  We build the fixture in a
   fresh OS.FileSys.tmpName() directory for each run.

   To avoid silently destroying useful state when two HOL
   installations share a tree, propagation refuses to overwrite an
   existing lastmaker that points at a *different* usable Holmake
   binary.  Interactively the user gets a y/N prompt to choose
   between overwriting (and proceeding) or aborting; in any
   non-interactive context (no TTY -- the selftest harness, CI,
   child Holmakes, editor probes) the run aborts with a non-zero
   exit code and the existing lastmaker is left alone.  The
   --force-lastmaker command-line flag suppresses the prompt and
   forces overwrite-and-continue.  A garbage pointer (an executable
   that no longer exists) is treated as stale and overwritten
   without prompting. *)

open testutils

infix ++
val op++ = OS.Path.concat

fun read_file f =
    let val s = TextIO.openIn f
    in TextIO.inputAll s before TextIO.closeIn s end

fun safedel p = OS.FileSys.remove p handle _ => ()
fun safermdir p = OS.FileSys.rmDir p handle _ => ()

fun mkdir_p p =
    if OS.FileSys.access (p, []) then ()
    else (mkdir_p (OS.Path.dir p);
          OS.FileSys.mkDir p handle OS.SysErr _ => ())

fun write_file path content =
    let val s = TextIO.openOut path
    in TextIO.output (s, content); TextIO.closeOut s end

fun rm_rf path =
    if OS.FileSys.isDir path handle _ => false then
      let val ds = OS.FileSys.openDir path
          fun loop () =
              case OS.FileSys.readDir ds of
                  NONE => (OS.FileSys.closeDir ds; safermdir path)
                | SOME f => (rm_rf (path ++ f); loop ())
      in loop () end
    else safedel path

(* Create a fresh tmpdir for fixtures, outside any HOLDIR so the
   started_under_holdir short-circuit doesn't bypass propagation. *)
fun mktmpdir () =
    let val n = OS.FileSys.tmpName ()
        val _ = safedel n
        val _ = OS.FileSys.mkDir n
    in n end

val tmp_root = mktmpdir ()
val fixture = tmp_root ++ "fixture"
val sub     = fixture ++ "sub"
val _ = mkdir_p sub
val _ = write_file (fixture ++ "Holmakefile")
          "INCLUDES = sub\nall: $(DEFAULT_TARGETS)\n.PHONY: all\n"
val _ = write_file (sub ++ "Holmakefile")
          "all: $(DEFAULT_TARGETS)\n.PHONY: all\n"
val _ = OS.Process.atExit (fn () => rm_rf tmp_root)

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
        val _ = mkdir_p depdir
    in write_file (depdir ++ "lastmaker") (content ^ "\n") end

val real_holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val outputlog = tmp_root ++ "output"
val _ = safedel outputlog
val _ = OS.Process.atExit (fn () => safedel outputlog)

fun cleanup () = app clean_lastmaker_in [fixture, sub]

(* Redirect stdin from /dev/null so the prompt branch in
   Holmake_tools sees "not a TTY" and aborts deterministically
   instead of asking. *)
fun run_holmake_in_with extra_args dir =
    let val cmd = String.concatWith " "
                    ([real_holmake, "-C", dir, "--no-cache", "-n"] @
                     extra_args @
                     ["<", "/dev/null", ">", outputlog, "2>&1"])
        val res = OS.Process.system cmd
        val out = read_file outputlog handle _ => ""
    in (res, out) end
fun run_holmake_in dir = run_holmake_in_with [] dir

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
   Test 2: conflicting existing lastmaker non-interactively aborts the
   build and leaves the existing file alone.  /bin/cat stands in as a
   "different but real executable" -- any readable+executable file
   path will do.
   ---------------------------------------------------------------------- *)
val other_executable = "/bin/cat"
val _ = if OS.FileSys.access (other_executable, [OS.FileSys.A_EXEC]) then ()
        else die ("test prerequisite missing: " ^ other_executable)

val _ = tprint "conflicting lastmaker aborts non-interactively, file preserved"
val _ = cleanup()
val _ = write_lastmaker_with_content sub other_executable
val (res2, out2) = run_holmake_in fixture
val _ = if OS.Process.isSuccess res2 then
          (dump out2; die "Holmake should have aborted but exited 0")
        else ()
val _ = case read_lastmaker sub of
            NONE => (dump out2; die "sub lastmaker disappeared")
          | SOME got =>
            if got = other_executable then ()
            else (dump out2;
                  die ("sub lastmaker was clobbered to: " ^ Lib.quote got))
val _ = if String.isSubstring "WARNING" out2 andalso
           String.isSubstring "lastmaker" out2 andalso
           String.isSubstring "no tty" out2
        then ()
        else (dump out2; die "expected conflict warning / abort msg not emitted")
val _ = OK ()

(* ----------------------------------------------------------------------
   Test 3: --force-lastmaker overwrites a conflicting lastmaker even
   without a TTY, still printing the warning so the user knows.
   ---------------------------------------------------------------------- *)
val _ = tprint "--force-lastmaker overwrites conflict non-interactively"
val _ = cleanup()
val _ = write_lastmaker_with_content sub other_executable
val (resF, outF) = run_holmake_in_with ["--force-lastmaker"] fixture
val _ = if OS.Process.isSuccess resF then ()
        else (dump outF; die "Holmake aborted despite --force-lastmaker")
val _ = case read_lastmaker sub of
            NONE => (dump outF; die "sub lastmaker disappeared")
          | SOME got =>
            if got = real_holmake then ()
            else (dump outF;
                  die ("sub lastmaker not overwritten: " ^ Lib.quote got))
val _ = if String.isSubstring "WARNING" outF
        then ()
        else (dump outF; die "expected conflict warning was suppressed")
val _ = OK ()

(* ----------------------------------------------------------------------
   Test 4: stale lastmaker (nonexistent path) is replaced silently
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
