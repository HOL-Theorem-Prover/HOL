(* Regression test for project-file cross-directory rule resolution.

   With a holproject.toml at the project root and *no* INCLUDES line
   anywhere, a rule in dirA that depends on a file produced by dirB's
   Holmakefile must still build successfully: Holmake's startup-time
   seeding of known_dirs from HMProject.discover_dirs should let
   find_rule consult dirB's Holmakefile on demand.

   The test build all happens under an isolated temp directory so the
   test never observes ambient state in the surrounding tree. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

fun run_holmake_in dir args =
    let val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir dir
        val r = Systeml.systeml (Holmake :: args)
    in
      OS.FileSys.chDir saved; r
    end

fun write_file p contents =
    let val s = TextIO.openOut p
    in TextIO.output (s, contents); TextIO.closeOut s end

fun rm_rf p =
    if OS.FileSys.isDir p handle OS.SysErr _ => false then
      let val ds = OS.FileSys.openDir p
          fun loop () =
              case OS.FileSys.readDir ds of
                  NONE => OS.FileSys.closeDir ds
                | SOME nm => (rm_rf (p ++ nm); loop ())
      in loop (); OS.FileSys.rmDir p handle OS.SysErr _ => () end
    else (OS.FileSys.remove p handle OS.SysErr _ => ())

(* Build the test project under a fresh tmp directory. *)
val tmpname = OS.FileSys.tmpName ()
val _ = OS.FileSys.remove tmpname handle OS.SysErr _ => ()
val root = tmpname
val _ = OS.FileSys.mkDir root

val dirA = root ++ "dirA"
val dirB = root ++ "dirB"
val _ = OS.FileSys.mkDir dirA
val _ = OS.FileSys.mkDir dirB

val _ = write_file (root ++ "holproject.toml")
                   "name = \"projfile_basic_test\"\n"

(* dirA's Holmakefile depends on dirB/dirB_output.txt.  No INCLUDES. *)
val _ = write_file (dirA ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \all: dirA_target.txt\n\
  \.PHONY: all\n\
  \\n\
  \dirA_target.txt: ../dirB/dirB_output.txt\n\
  \\tcp ../dirB/dirB_output.txt dirA_target.txt\n\
  \\n\
  \EXTRA_CLEANS = dirA_target.txt\n"

(* dirB's Holmakefile produces dirB_output.txt.  No INCLUDES. *)
val _ = write_file (dirB ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \dirB_output.txt:\n\
  \\techo produced > dirB_output.txt\n\
  \\n\
  \EXTRA_CLEANS = dirB_output.txt\n"

(* Run Holmake from dirA. *)
val _ = tprint "Cross-dir rule resolves via holproject.toml (no INCLUDES)"
val result = run_holmake_in dirA ["--nolmbc"]

val dirA_built = OS.FileSys.access (dirA ++ "dirA_target.txt", [])
                 handle OS.SysErr _ => false
val dirB_built = OS.FileSys.access (dirB ++ "dirB_output.txt", [])
                 handle OS.SysErr _ => false

val _ = if OS.Process.isSuccess result andalso dirA_built andalso dirB_built
        then OK ()
        else die ("FAILED: holmake exit=" ^
                  Bool.toString (OS.Process.isSuccess result) ^
                  " dirA_target.txt=" ^ Bool.toString dirA_built ^
                  " dirB_output.txt=" ^ Bool.toString dirB_built)

(* Sanity check: with --no-project, the same setup must fail (otherwise
   the test isn't proving that the projfile is what's doing the work). *)
val _ = ignore (run_holmake_in dirA ["--nolmbc", "cleanAll"])
val _ = ignore (run_holmake_in dirB ["--nolmbc", "cleanAll"])

val _ = tprint "Same setup with --no-project fails (control)"
val ctrl = run_holmake_in dirA ["--nolmbc", "--no-project"]
val _ = if OS.Process.isSuccess ctrl
        then die "FAILED: build should have failed without project mode"
        else OK ()

val _ = rm_rf root
