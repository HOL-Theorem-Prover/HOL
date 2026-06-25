(* Regression tests for the `holpath` override key in holproject.toml.

   When `holpath` is set, it (rather than `name`) becomes the HOL-path
   variable name registered in holpathdb for that project's root.  This
   lets a project keep a human-facing `name` while exposing a distinct
   variable name to dependants (e.g. name = "cakeml", holpath =
   "CAKEMLDIR"). *)

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

fun run_holmake_capture dir args =
    let
      val saved = OS.FileSys.getDir()
      val _ = OS.FileSys.chDir dir
      val outfile = OS.FileSys.tmpName()
      val cmd = String.concatWith " "
                  (Holmake :: args @ [">", outfile, "2>&1"])
      val r = OS.Process.system cmd
      val istrm = TextIO.openIn outfile
      val output = TextIO.inputAll istrm before TextIO.closeIn istrm
      val _ = OS.FileSys.remove outfile handle OS.SysErr _ => ()
    in
      OS.FileSys.chDir saved; (r, output)
    end

fun write_file p contents =
    let val s = TextIO.openOut p
    in TextIO.output (s, contents); TextIO.closeOut s end

fun read_file p =
    let val s = TextIO.openIn p
    in TextIO.inputAll s before TextIO.closeIn s end

fun rm_rf p =
    if OS.FileSys.isDir p handle OS.SysErr _ => false then
      let val ds = OS.FileSys.openDir p
          fun loop () =
              case OS.FileSys.readDir ds of
                  NONE => OS.FileSys.closeDir ds
                | SOME nm => (rm_rf (p ++ nm); loop ())
      in loop (); OS.FileSys.rmDir p handle OS.SysErr _ => () end
    else (OS.FileSys.remove p handle OS.SysErr _ => ())

fun strip s =
    let val t = Substring.dropr Char.isSpace (Substring.full s)
        val t = Substring.dropl Char.isSpace t
    in Substring.string t end

(* getDir resolves symlinks (e.g. /var/tmp -> /private/var/tmp on
   macOS), matching how Holmake's upward walk records project roots.
   Without the roundtrip, comparisons against the tmpName-derived
   string spuriously fail on platforms with symlinked tmp dirs. *)
fun mk_root () =
    let val tmpname = OS.FileSys.tmpName ()
        val _ = OS.FileSys.remove tmpname handle OS.SysErr _ => ()
        val _ = OS.FileSys.mkDir tmpname
        val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir tmpname
        val resolved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir saved
    in resolved end

(* ----------------------------------------------------------------------
   Sub-test 1: holpath overrides name.
   ---------------------------------------------------------------------- *)
val _ = tprint "holpath key overrides name for holpathdb registration"
val root1 = mk_root()
val dir1 = root1 ++ "dirA"
val _ = OS.FileSys.mkDir dir1
val _ = write_file (root1 ++ "holproject.toml")
                   "name = \"human_label\"\n\
                   \holpath = \"CHECK_VNAME\"\n"
val _ = write_file (dir1 ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \all: out.txt\n\
  \.PHONY: all\n\
  \\n\
  \out.txt:\n\
  \\techo $(CHECK_VNAME) > out.txt\n\
  \\n\
  \EXTRA_CLEANS = out.txt\n"
val r1 = run_holmake_in dir1 ["--nolmbc"]
val content1 = (strip (read_file (dir1 ++ "out.txt"))) handle _ => ""
val expected1 = OS.Path.mkCanonical root1
val _ = if OS.Process.isSuccess r1 andalso content1 = expected1 then OK ()
        else die ("FAILED: exit=" ^
                  Bool.toString (OS.Process.isSuccess r1) ^
                  " expected '" ^ expected1 ^ "' got '" ^ content1 ^ "'")
val _ = rm_rf root1

(* ----------------------------------------------------------------------
   Sub-test 2: holpath alone (no name) still registers.
   ---------------------------------------------------------------------- *)
val _ = tprint "holpath alone (no name) registers vname"
val root2 = mk_root()
val dir2 = root2 ++ "dirA"
val _ = OS.FileSys.mkDir dir2
val _ = write_file (root2 ++ "holproject.toml")
                   "holpath = \"ONLY_HOLPATH\"\n"
val _ = write_file (dir2 ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \\n\
  \all: out.txt\n\
  \.PHONY: all\n\
  \\n\
  \out.txt:\n\
  \\techo $(ONLY_HOLPATH) > out.txt\n\
  \\n\
  \EXTRA_CLEANS = out.txt\n"
val r2 = run_holmake_in dir2 ["--nolmbc"]
val content2 = (strip (read_file (dir2 ++ "out.txt"))) handle _ => ""
val expected2 = OS.Path.mkCanonical root2
val _ = if OS.Process.isSuccess r2 andalso content2 = expected2 then OK ()
        else die ("FAILED: exit=" ^
                  Bool.toString (OS.Process.isSuccess r2) ^
                  " expected '" ^ expected2 ^ "' got '" ^ content2 ^ "'")
val _ = rm_rf root2

(* ----------------------------------------------------------------------
   Sub-test 3: non-string holpath value is a fatal startup error.
   ---------------------------------------------------------------------- *)
val _ = tprint "non-string holpath value rejected at startup"
val root3 = mk_root()
val dir3 = root3 ++ "dirA"
val _ = OS.FileSys.mkDir dir3
val _ = write_file (root3 ++ "holproject.toml")
                   "holpath = 42\n"
val _ = write_file (dir3 ++ "Holmakefile")
  "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol\nendif\n\
  \all: ; @echo unreached\n.PHONY: all\n"
val (r3, out3) = run_holmake_capture dir3 ["--nolmbc"]
val _ = if not (OS.Process.isSuccess r3) andalso
           String.isSubstring "holpath" out3
        then OK ()
        else die ("FAILED: expected non-zero exit and message mentioning \
                  \`holpath`; exit=" ^ Bool.toString (OS.Process.isSuccess r3) ^
                  " output:\n" ^ out3)
val _ = rm_rf root3
