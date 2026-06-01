(* Regression test for project-file source-resolution via Holdep.

   With a holproject.toml at the root and no INCLUDES anywhere, a
   reference like `Bar.greet ()` in dirA/foo.sml must resolve to
   dirB's Bar.{sig,sml}: Holmake must (a) widen Holdep's include
   list with the project_dirs and (b) populate graph nodes for
   dirB so Bar.{ui,uo} can actually be built. *)

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

val tmpname = OS.FileSys.tmpName ()
val _ = OS.FileSys.remove tmpname handle OS.SysErr _ => ()
val root = tmpname
val _ = OS.FileSys.mkDir root
val dirA = root ++ "dirA"
val dirB = root ++ "dirB"
val _ = OS.FileSys.mkDir dirA
val _ = OS.FileSys.mkDir dirB

val _ = write_file (root ++ "holproject.toml")
                   "name = \"projfile_open_resolution_test\"\n"

(* dirB exposes a module Bar. *)
val _ = write_file (dirB ++ "Bar.sig")
  "signature Bar = sig\n  val greet : unit -> unit\nend\n"
val _ = write_file (dirB ++ "Bar.sml")
  "structure Bar :> Bar = struct\n\
  \  fun greet () = print \"hello\\n\"\n\
  \end\n"
val _ = write_file (dirB ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol --no_overlay\nendif\n"

(* dirA's foo.sml references Bar without any INCLUDES. *)
val _ = write_file (dirA ++ "foo.sml")
  "val _ = Bar.greet ()\n"
val _ = write_file (dirA ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol --no_overlay\nendif\n\
  \\n\
  \all: foo.uo\n\
  \.PHONY: all\n"

val _ = tprint "Open-resolution via holproject.toml (no INCLUDES)"
val result = run_holmake_in dirA ["--nolmbc"]

(* Theory products land under .hol/objs/ — check there. *)
fun product_at d nm =
    OS.FileSys.access (d ++ ".hol" ++ "objs" ++ nm, [])
    handle OS.SysErr _ => false

val foo_built = product_at dirA "foo.uo"
val bar_built = product_at dirB "Bar.uo"

val _ = if OS.Process.isSuccess result andalso foo_built andalso bar_built
        then OK ()
        else die ("FAILED: exit=" ^
                  Bool.toString (OS.Process.isSuccess result) ^
                  " foo.uo=" ^ Bool.toString foo_built ^
                  " Bar.uo=" ^ Bool.toString bar_built)

(* Control: --no-project must leave Bar undiscovered, so either Holmake
   produces foo.uo with an empty deps list (compile may even succeed
   under poly, since it tolerates missing references at this stage) or
   Bar.uo is never built.  The robust assertion is "Bar.uo is absent". *)
val _ = ignore (run_holmake_in dirA ["--nolmbc", "cleanAll"])
val _ = ignore (run_holmake_in dirB ["--nolmbc", "cleanAll"])

val _ = tprint "Same setup with --no-project leaves Bar.uo unbuilt"
val _ = ignore (run_holmake_in dirA ["--nolmbc", "--no-project"])
val bar_still_unbuilt = not (product_at dirB "Bar.uo")

val _ = if bar_still_unbuilt then OK ()
        else die "FAILED: Bar.uo was built without project mode"

val _ = rm_rf root
