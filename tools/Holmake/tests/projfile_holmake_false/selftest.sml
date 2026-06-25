(* End-to-end test for `holmake = false` in holproject.toml. *)

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

fun fresh_dir () =
    let val nm = OS.FileSys.tmpName ()
        val _ = OS.FileSys.remove nm handle OS.SysErr _ => ()
        val _ = OS.FileSys.mkDir nm
    in nm end

(* ---------- 1. holmake = false: explicit INCLUDES still works ---------- *)

val root1 = fresh_dir ()
val dirA1 = root1 ++ "dirA"
val dirB1 = root1 ++ "dirB"
val _ = OS.FileSys.mkDir dirA1
val _ = OS.FileSys.mkDir dirB1

val _ = write_file (root1 ++ "holproject.toml") "holmake = false\n"

val _ = write_file (dirA1 ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \INCLUDES = ../dirB\n\
  \\n\
  \all: dirA_target.txt\n\
  \.PHONY: all\n\
  \\n\
  \dirA_target.txt: ../dirB/dirB_output.txt\n\
  \\tcp ../dirB/dirB_output.txt dirA_target.txt\n\
  \\n\
  \EXTRA_CLEANS = dirA_target.txt\n"

val _ = write_file (dirB1 ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \dirB_output.txt:\n\
  \\techo produced > dirB_output.txt\n\
  \\n\
  \EXTRA_CLEANS = dirB_output.txt\n"

val _ = tprint "holmake = false: classical INCLUDES build succeeds"
val r1 = run_holmake_in dirA1 ["--nolmbc"]
val r1a = OS.FileSys.access (dirA1 ++ "dirA_target.txt", [])
          handle OS.SysErr _ => false
val r1b = OS.FileSys.access (dirB1 ++ "dirB_output.txt", [])
          handle OS.SysErr _ => false
val _ = if OS.Process.isSuccess r1 andalso r1a andalso r1b
        then OK ()
        else die ("FAILED: exit=" ^ Bool.toString (OS.Process.isSuccess r1) ^
                  " dirA_target.txt=" ^ Bool.toString r1a ^
                  " dirB_output.txt=" ^ Bool.toString r1b)

val _ = ignore (run_holmake_in dirA1 ["--nolmbc", "cleanAll"])
val _ = ignore (run_holmake_in dirB1 ["--nolmbc", "cleanAll"])

(* ---------- 2. Negative control: no INCLUDES => build must fail ---------- *)

val root2 = fresh_dir ()
val dirA2 = root2 ++ "dirA"
val dirB2 = root2 ++ "dirB"
val _ = OS.FileSys.mkDir dirA2
val _ = OS.FileSys.mkDir dirB2

val _ = write_file (root2 ++ "holproject.toml") "holmake = false\n"

(* Same as test 1 but with the `INCLUDES = ../dirB` line stripped.  Under
   holmake = true this would succeed via discover_dirs auto-resolution. *)
val _ = write_file (dirA2 ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \all: dirA_target.txt\n\
  \.PHONY: all\n\
  \\n\
  \dirA_target.txt: ../dirB/dirB_output.txt\n\
  \\tcp ../dirB/dirB_output.txt dirA_target.txt\n\
  \\n\
  \EXTRA_CLEANS = dirA_target.txt\n"

val _ = write_file (dirB2 ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \dirB_output.txt:\n\
  \\techo produced > dirB_output.txt\n\
  \\n\
  \EXTRA_CLEANS = dirB_output.txt\n"

val _ = tprint "holmake = false: no INCLUDES => cross-dir build fails"
val r2 = run_holmake_in dirA2 ["--nolmbc"]
val _ = if OS.Process.isSuccess r2
        then die "FAILED: build succeeded; project mode appears to still be on"
        else OK ()

(* ---------- 3. external_includes inheritance ---------- *)

val root3 = fresh_dir ()
val dirA3 = root3 ++ "dirA"
val dirC3 = root3 ++ "dirC"
val _ = OS.FileSys.mkDir dirA3
val _ = OS.FileSys.mkDir dirC3

(* external_includes points at dirC; dirA has no INCLUDES of its own. *)
val _ = write_file (root3 ++ "holproject.toml")
  ("holmake = false\n\
   \external_includes = [\"" ^ String.toString dirC3 ^ "\"]\n")

(* dirA depends on a product produced by dirC's Holmakefile, referenced
   by path.  With no INCLUDES line, the only way Holmake can locate
   dirC's rule is through external_includes putting dirC on the
   known-dirs set at startup (mark_known project_active_dirs). *)
val _ = write_file (dirA3 ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \all: dirA_target.txt\n\
  \.PHONY: all\n\
  \\n\
  \dirA_target.txt: ../dirC/dirC_output.txt\n\
  \\tcp ../dirC/dirC_output.txt dirA_target.txt\n\
  \\n\
  \EXTRA_CLEANS = dirA_target.txt\n"

val _ = write_file (dirC3 ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \dirC_output.txt:\n\
  \\techo produced > dirC_output.txt\n\
  \\n\
  \EXTRA_CLEANS = dirC_output.txt\n"

val _ = tprint "holmake = false: external_includes inherited as classic includes"
val r3 = run_holmake_in dirA3 ["--nolmbc"]
val r3a = OS.FileSys.access (dirA3 ++ "dirA_target.txt", [])
          handle OS.SysErr _ => false
val _ = if OS.Process.isSuccess r3 andalso r3a
        then OK ()
        else die ("FAILED: exit=" ^ Bool.toString (OS.Process.isSuccess r3) ^
                  " dirA_target.txt=" ^ Bool.toString r3a)

val _ = ignore (run_holmake_in dirA3 ["--nolmbc", "cleanAll"])
val _ = ignore (run_holmake_in dirC3 ["--nolmbc", "cleanAll"])

val _ = rm_rf root1
val _ = rm_rf root2
val _ = rm_rf root3
