(* Duplicate source names across project_dirs must be a startup-time
   fatal error: Holmake exits non-zero and the message names every
   offending path so the user can disambiguate via [exclude] or by
   renaming. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

fun write_file p contents =
    let val s = TextIO.openOut p
    in TextIO.output (s, contents); TextIO.closeOut s end

fun read_file p =
    let val s = TextIO.openIn p
        val r = TextIO.inputAll s before TextIO.closeIn s
    in r end

fun run_capture dir args captured =
    let val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir dir
        val cmd =
            String.concatWith " "
              (Systeml.protect Holmake ::
               args @ [">", captured, "2>&1"])
        val r = OS.Process.system cmd
    in OS.FileSys.chDir saved; r end

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

val _ = write_file (root ++ "holproject.toml") "name = \"clashtest\"\n"
val _ = write_file (dirA ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol --no_overlay\nendif\n"
val _ = write_file (dirB ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol --no_overlay\nendif\n"
val _ = write_file (dirA ++ "Foo.sml") "val _ = ()\n"
val _ = write_file (dirB ++ "Foo.sml") "val _ = ()\n"

val out = root ++ "out"

val _ = tprint "Duplicate source name aborts Holmake startup"
val rc = run_capture dirA ["--nolmbc"] out
val msg = read_file out handle _ => ""
val saw_name = String.isSubstring "ambiguous source name 'Foo.sml'" msg
val saw_pathA = String.isSubstring "dirA/Foo.sml" msg
val saw_pathB = String.isSubstring "dirB/Foo.sml" msg
val _ = if not (OS.Process.isSuccess rc) andalso saw_name
           andalso saw_pathA andalso saw_pathB
        then OK ()
        else die ("FAILED: rc=" ^
                  Bool.toString (OS.Process.isSuccess rc) ^
                  " saw_name=" ^ Bool.toString saw_name ^
                  " saw_pathA=" ^ Bool.toString saw_pathA ^
                  " saw_pathB=" ^ Bool.toString saw_pathB ^
                  "\nCaptured output:\n" ^ msg)

(* Adding dirB to [exclude] resolves the clash *)
val _ = write_file (root ++ "holproject.toml")
                   "name = \"clashtest\"\nexclude = [\"dirB\"]\n"

val _ = tprint "Listing offending dir in [exclude] resolves the clash"
val rc2 = run_capture dirA ["--nolmbc"] out
val _ = if OS.Process.isSuccess rc2 then OK ()
        else die ("FAILED to recover after exclude: rc=" ^
                  Bool.toString (OS.Process.isSuccess rc2) ^
                  "\n" ^ read_file out handle _ => "")

val _ = rm_rf root
