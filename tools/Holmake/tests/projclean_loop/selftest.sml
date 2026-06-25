(* In project mode, a sub-directory whose Holmakefile says
   `INCLUDES = ..` is referring back to a sibling Holmake has already
   visited via project discovery, not creating a cycle.  `Holmake -r
   cleanAll` must not warn `INCLUDES chain loops:` for that. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

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
val _ = OS.FileSys.mkDir dirA

val _ = write_file (root ++ "holproject.toml")
                   "name = \"projclean_loop_test\"\n"

val _ = write_file (root ++ "Holmakefile")
                   "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n"

val _ = write_file (dirA ++ "Holmakefile")
                   "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
                   \INCLUDES = ..\n"

fun run_in_dir d args =
    let val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir d
        val res = Mosml.run Holmake args ""
    in OS.FileSys.chDir saved; res end

val _ = tprint
          "Holmake -r cleanAll in project root: no spurious INCLUDES chain"

val result = run_in_dir root ["--nolmbc", "-r", "cleanAll"]
val (succeeded, out) = case result of
                          Mosml.Success s => (true, s)
                        | Mosml.Failure s => (false, s)

val _ =
    if String.isSubstring "INCLUDES chain" out then
      die ("FAILED: spurious loop warning:\n" ^ out)
    else if not succeeded then
      die ("FAILED: Holmake exited non-zero:\n" ^ out)
    else OK ()

val _ = rm_rf root
