(* End-to-end test for h4pedant reading [h4pedant] from holproject.toml. *)

open testutils

val op++ = OS.Path.concat
val h4pedant = Globals.HOLDIR ++ "tools" ++ "h4pedant" ++ "h4pedant"

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

fun run_h4pedant_in dir args =
    let val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir dir
        val r = Systeml.systeml (h4pedant :: args)
    in
      OS.FileSys.chDir saved; r
    end

(* Three checks:
     1. A long line in a dir with default settings -> flagged.
     2. A long line in a dir with linelen = 0 override -> *not* flagged.
     3. A long line in an excluded dir -> *not* flagged.
   In every case we then run with --nolinelen and confirm the flag wins. *)

val root = fresh_dir ()
val defaultsub = root ++ "defaultsub"
val loosesub = root ++ "loosesub"
val excludedsub = root ++ "excludedsub"
val _ = List.app OS.FileSys.mkDir [defaultsub, loosesub, excludedsub]

val long_line = String.implode (List.tabulate (95, fn _ => #"x"))
val long_sml = "val _ = (\"" ^ long_line ^ "\", 0)\n"

val _ = write_file (defaultsub ++ "a.sml") long_sml
val _ = write_file (loosesub ++ "b.sml") long_sml
val _ = write_file (excludedsub ++ "c.sml") long_sml

val _ = write_file (root ++ "holproject.toml")
  ("holmake = false\n\
   \\n\
   \[h4pedant]\n\
   \linelen = 80\n\
   \unicode_ok = false\n\
   \exclude = [\"excludedsub\"]\n\
   \\n\
   \[[h4pedant.dir]]\n\
   \path = \"loosesub\"\n\
   \linelen = 0\n")

val _ = tprint "default dir: long line is flagged"
val r1 = run_h4pedant_in root []
val _ = if OS.Process.isSuccess r1 then die "FAILED: expected failure" else OK ()

val _ = tprint "override dir (linelen = 0): long line is silent"
val r2 = run_h4pedant_in loosesub [loosesub]
val _ = if OS.Process.isSuccess r2 then OK ()
        else die "FAILED: loosesub should have been silent"

val _ = tprint "excluded dir: not visited even from project root"
(* Remove the long line in defaultsub so the only remaining violation
   would be in the excluded dir.  Pass: scan succeeds. *)
val _ = write_file (defaultsub ++ "a.sml") "val _ = 0\n"
val r3 = run_h4pedant_in root []
val _ = if OS.Process.isSuccess r3 then OK ()
        else die "FAILED: excluded dir leaked into scan"

(* Put the long line back so the default dir is dirty again. *)
val _ = write_file (defaultsub ++ "a.sml") long_sml

val _ = tprint "--nolinelen: CLI wins, default dir is silent too"
val r4 = run_h4pedant_in root ["--nolinelen"]
val _ = if OS.Process.isSuccess r4 then OK ()
        else die "FAILED: --nolinelen should have silenced all dirs"

val _ = tprint "Unicode override: unicode_ok=true silences only that dir"
val _ = rm_rf root
val root2 = fresh_dir ()
val ucsub = root2 ++ "uc"
val plainsub = root2 ++ "plain"
val _ = List.app OS.FileSys.mkDir [ucsub, plainsub]
(* α (U+03B1) is non-ASCII and not in h4pedant's allowed set (which
   permits λ at U+03BB plus a few smart quotes).  Built byte-by-byte
   so we write the UTF-8 encoding regardless of how the SML compiler
   handles `\uXXXX` literals. *)
val alpha_utf8 =
    String.implode [Char.chr 0xCE, Char.chr 0xB1]
val unicode_sml = "val _ = \"" ^ alpha_utf8 ^ "\"\n"
val _ = write_file (ucsub ++ "u.sml") unicode_sml
val _ = write_file (plainsub ++ "p.sml") unicode_sml
val _ = write_file (root2 ++ "holproject.toml")
  ("holmake = false\n\
   \\n\
   \[h4pedant]\n\
   \linelen = 0\n\
   \\n\
   \[[h4pedant.dir]]\n\
   \path = \"uc\"\n\
   \unicode_ok = true\n")
val r5 = run_h4pedant_in root2 []
val _ = if OS.Process.isSuccess r5 then die "FAILED: plain dir's unicode should have been flagged"
        else OK ()

val _ = tprint "Unicode in override dir alone is silent"
(* Clean the plain dir's violation; only `uc` (which is unicode_ok) has unicode. *)
val _ = write_file (plainsub ++ "p.sml") "val _ = 0\n"
val r6 = run_h4pedant_in root2 []
val _ = if OS.Process.isSuccess r6 then OK ()
        else die "FAILED: unicode_ok override should have silenced uc/"

val _ = rm_rf root2

(* --- include ----------------------------------------------------- *)

(* With `include = [in1]` and no CLI positional args, only `in1` is
   scanned: violations under `out1` (a sibling of `in1`) go unseen. *)
val _ = tprint "include restricts scan set to listed dirs"
val root3 = fresh_dir ()
val in1 = root3 ++ "in1"
val out1 = root3 ++ "out1"
val _ = List.app OS.FileSys.mkDir [in1, out1]
val _ = write_file (in1 ++ "a.sml") "val _ = 0\n"
val _ = write_file (out1 ++ "b.sml") long_sml
val _ = write_file (root3 ++ "holproject.toml")
  ("holmake = false\n\
   \\n\
   \[h4pedant]\n\
   \linelen = 80\n\
   \include = [\"in1\"]\n")
val ri1 = run_h4pedant_in root3 []
val _ = if OS.Process.isSuccess ri1 then OK ()
        else die "FAILED: include should have kept us out of out1"

(* Include and exclude compose: include the parent, exclude a child. *)
val _ = tprint "include + exclude compose (exclude prunes inside include)"
val _ = rm_rf root3
val root4 = fresh_dir ()
val incdir = root4 ++ "inc"
val excsub = incdir ++ "skip"
val _ = List.app OS.FileSys.mkDir [incdir, excsub]
val _ = write_file (incdir ++ "ok.sml") "val _ = 0\n"
val _ = write_file (excsub ++ "bad.sml") long_sml
val _ = write_file (root4 ++ "holproject.toml")
  ("holmake = false\n\
   \\n\
   \[h4pedant]\n\
   \linelen = 80\n\
   \include = [\"inc\"]\n\
   \exclude = [\"inc/skip\"]\n")
val ri2 = run_h4pedant_in root4 []
val _ = if OS.Process.isSuccess ri2 then OK ()
        else die "FAILED: excluded child of included dir leaked into scan"

(* A CLI positional arg overrides the include list (excludes still apply). *)
val _ = tprint "CLI positional dir overrides include list"
val ri3 = run_h4pedant_in root4 [incdir]
val _ = if OS.Process.isSuccess ri3 then OK ()
        else die "FAILED: exclude did not apply under explicit CLI dir"

(* Direct conflict: same path in both include and exclude is fatal. *)
val _ = tprint "same path in include and exclude aborts with error"
val _ = rm_rf root4
val root5 = fresh_dir ()
val bothdir = root5 ++ "both"
val _ = OS.FileSys.mkDir bothdir
val _ = write_file (bothdir ++ "x.sml") "val _ = 0\n"
val _ = write_file (root5 ++ "holproject.toml")
  ("holmake = false\n\
   \\n\
   \[h4pedant]\n\
   \include = [\"both\"]\n\
   \exclude = [\"both\"]\n")
val ri4 = run_h4pedant_in root5 []
val _ = if OS.Process.isSuccess ri4 then die "FAILED: conflict must be fatal"
        else OK ()
val _ = rm_rf root5

(* --- [[h4pedant.dir]] deeper-wins -------------------------------- *)

(* The child directory holds a Unicode file; the deeper of the two
   overrides is whatever governs whether it's flagged. *)
fun deeper_wins_case { parent_ok, child_ok, expect_success } =
    let
      val bstr = fn true => "true" | false => "false"
      val root = fresh_dir ()
      val parent = root ++ "parent"
      val child = parent ++ "child"
      val _ = List.app OS.FileSys.mkDir [parent, child]
      val _ = write_file (child ++ "c.sml") unicode_sml
      val _ = write_file (root ++ "holproject.toml")
        ("holmake = false\n\
         \\n\
         \[h4pedant]\n\
         \linelen = 0\n\
         \\n\
         \[[h4pedant.dir]]\n\
         \path = \"parent\"\n\
         \unicode_ok = " ^ bstr parent_ok ^ "\n\
         \\n\
         \[[h4pedant.dir]]\n\
         \path = \"parent/child\"\n\
         \unicode_ok = " ^ bstr child_ok ^ "\n")
      val r = run_h4pedant_in root []
    in
      (if OS.Process.isSuccess r = expect_success then OK ()
       else die ("FAILED: parent unicode_ok=" ^ bstr parent_ok ^
                 ", child unicode_ok=" ^ bstr child_ok));
      rm_rf root
    end

val _ = tprint "[[h4pedant.dir]] deeper override wins over shallower"
val _ = deeper_wins_case
          { parent_ok = true, child_ok = false, expect_success = false }

val _ = tprint "[[h4pedant.dir]] deeper override wins (mirror direction)"
val _ = deeper_wins_case
          { parent_ok = false, child_ok = true, expect_success = true }
