(* End-to-end test: a synthetic multi-dir project where one subdir's
   theory has `Ancestors` reaching across to a sibling subdir's theory,
   with NO INCLUDES line anywhere.  Holmake is invoked at the project
   root with `-r`; project mode picks up holproject.toml, adds every
   project dir to cline_incs, and the build runs each subdir's
   Holmake in the right order with Holdep finding cross-dir source
   references via the project's include set.

   Models the "stripped-down lambda" scenario without depending on
   lambda's actual sources or HOL examples build sequence: a fresh
   Holmake at the synthetic project's root has to find and build
   everything from holproject.toml alone. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val hol_state0 = Globals.HOLDIR ++ "bin" ++ "hol.state0"

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

val tmpname = OS.FileSys.tmpName ()
val _ = OS.FileSys.remove tmpname handle OS.SysErr _ => ()
val root = tmpname
val _ = OS.FileSys.mkDir root
val dirA = root ++ "dirA"
val dirB = root ++ "dirB"
val _ = OS.FileSys.mkDir dirA
val _ = OS.FileSys.mkDir dirB

(* Synthetic two-dir project: dirB's theory has Ancestors A, with no
   INCLUDES = ../dirA in dirB's Holmakefile.  Project mode must lift
   dirA into dirB's Holdep search path and ensure dirA is built before
   dirB.  Theories use [bare] so the bare HOL heap (hol.state0)
   suffices -- no need for the full system. *)
val _ = write_file (root ++ "holproject.toml")
                   "name = \"projfile_synthetic_test\"\n"

fun holheap_decl () =
    "ifdef POLY\nHOLHEAP = " ^ hol_state0 ^ "\nendif\n"

(* Root Holmakefile: HOLHEAP + recursive-build so Holmake at the root
   triggers building every project dir's default targets. *)
val _ = write_file (root ++ "Holmakefile")
                   (holheap_decl () ^ "\nCLINE_OPTIONS = -r\n")

val _ = write_file (dirA ++ "Holmakefile") (holheap_decl ())
val _ = write_file (dirA ++ "AScript.sml")
  "Theory A[bare]\n\
  \Ancestors bool\n\
  \Theorem a_truth = TRUTH\n"

val _ = write_file (dirB ++ "Holmakefile") (holheap_decl ())
val _ = write_file (dirB ++ "BScript.sml")
  "Theory B[bare]\n\
  \Ancestors A\n\
  \Theorem b_truth = a_truth\n"

val _ = tprint "Synthetic project: Holmake -r at root builds all subdirs"
val result = run_holmake_in root ["--nolmbc"]

fun product_at d nm =
    OS.FileSys.access (d ++ ".hol" ++ "objs" ++ nm, [])
    handle OS.SysErr _ => false

val a_built = product_at dirA "ATheory.uo"
            andalso product_at dirA "ATheory.dat"
val b_built = product_at dirB "BTheory.uo"
            andalso product_at dirB "BTheory.dat"

val _ = if OS.Process.isSuccess result andalso a_built andalso b_built
        then OK ()
        else die ("FAILED: exit=" ^
                  Bool.toString (OS.Process.isSuccess result) ^
                  " ATheory.{uo,dat}=" ^ Bool.toString a_built ^
                  " BTheory.{uo,dat}=" ^ Bool.toString b_built)

(* Sanity check: the cross-dir resolution was via project mode, not
   accidental classical INCLUDES that snuck in somewhere.  Re-run
   with --no-project after cleaning -- Holdep must now fail to find
   ATheory and BTheory's compile should fail. *)
val _ = ignore (run_holmake_in dirA ["--nolmbc", "cleanAll"])
val _ = ignore (run_holmake_in dirB ["--nolmbc", "cleanAll"])
val _ = ignore (run_holmake_in root ["--nolmbc", "cleanAll"])

val _ = tprint "Same project with --no-project leaves BTheory unbuilt"
val ctrl = run_holmake_in root ["--nolmbc", "--no-project"]
val b_still_unbuilt = not (product_at dirB "BTheory.uo")
val _ = if b_still_unbuilt then OK ()
        else die ("FAILED: BTheory.uo was built without project mode " ^
                  "(exit=" ^ Bool.toString (OS.Process.isSuccess ctrl) ^ ")")

val _ = rm_rf root
