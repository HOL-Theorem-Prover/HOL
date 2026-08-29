(* Nested projects: a sub-directory of a project that carries its own
   holproject.toml heads a separate project, which HMProject.discover
   prunes out of the enclosing project's directory set.

   What that has to mean:
     - the nested project's own directories see each other, because its
       project file governs them and not the parent's;
     - the parent may name a file inside the nested project and have it
       built, without declaring anything (adoption by reference);
     - `-r' in the parent covers the nested project too, when building
       and when cleaning;
     - `--dirs' governs each named root by the project file at or above
       *it*, whether the invocation is from the enclosing project or
       from a directory in no project at all.

   The fixture is built under a fresh temp directory: the HOL repository
   root carries its own holproject.toml, so an in-tree fixture would sit
   inside HOL's project and the test would measure ambient state. *)

infix ++
val op++ = OS.Path.concat

fun die s = (TextIO.output (TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

fun tprint s =
    TextIO.output (TextIO.stdOut, StringCvt.padRight #" " 60 (s ^ " ... "))
fun ok () = TextIO.output (TextIO.stdOut, "OK\n")

val holmake = Systeml.HOLDIR ++ "bin" ++ "Holmake"

(* Runs before Overlay.ui exists in the build sequence. *)
val baseopts =
    if Systeml.ML_SYSNAME = "poly" then ["--no_overlay", "--poly_not_hol"]
    else ["--no_overlay"]

fun hm_in dir xs =
    let
      val saved = OS.FileSys.getDir()
      val () = OS.FileSys.chDir dir
      val r = Systeml.systeml ([holmake, "-q", "--nolmbc"] @ baseopts @ xs)
    in
      OS.FileSys.chDir saved; r
    end

fun write_file p contents =
    let val s = TextIO.openOut p
    in TextIO.output (s, contents); TextIO.closeOut s end

(* Object files live under .hol/objs/ (HFS_NameMunge); HOLFileSys does
   that translation for us, and is the identity under mosml. *)
fun exists p = HOLFileSys.access (p, []) handle OS.SysErr _ => false

fun rm_rf p =
    if OS.FileSys.isDir p handle OS.SysErr _ => false then
      let
        val ds = OS.FileSys.openDir p
        fun loop () =
            case OS.FileSys.readDir ds of
                NONE => OS.FileSys.closeDir ds
              | SOME nm => (rm_rf (p ++ nm); loop ())
      in
        loop (); OS.FileSys.rmDir p handle OS.SysErr _ => ()
      end
    else (OS.FileSys.remove p handle OS.SysErr _ => ())

(* ----------------------------------------------------------------------
    The fixture; `outside' carries no project file of its own.

      outside/
        P/                    project "pn_parent"
          Holmakefile         all: PNParent.uo nested/dep/PNDep.uo
          PNParent.sml        opens PNLib
          lib/PNLib.sml       source-only project dir
          sub/Holmakefile     all: PNSub.uo   (PNSub.sml opens PNLib)
          nested/             project "pn_nested", [projects.pn_parent]=..
            Holmakefile       all: PNTop.uo   (no INCLUDES anywhere)
            PNTop.sml         opens PNDep and PNLib
            dep/PNDep.sml     source-only dir of the *nested* project
            extra/PNExtra.sml nothing refers to it; only -r reaches it
   ---------------------------------------------------------------------- *)

val outside = OS.FileSys.tmpName ()
val () = OS.FileSys.remove outside handle OS.SysErr _ => ()
val () = OS.FileSys.mkDir outside

val root = outside ++ "P"
val lib = root ++ "lib"
val sub = root ++ "sub"
val nested = root ++ "nested"
val nested_dep = nested ++ "dep"
val nested_extra = nested ++ "extra"

(* `declare_parent' is what makes the parent's sources visible from
   inside the nested project.  The --no-project control below turns it
   off, so that nothing about the fixture other than project mode
   explains the difference. *)
fun build_fixture {declare_parent} =
    (rm_rf root;
     List.app OS.FileSys.mkDir
              [root, lib, sub, nested, nested_dep, nested_extra];
     write_file (root ++ "holproject.toml") "name = \"pn_parent\"\n";
     write_file (nested ++ "holproject.toml")
                ("name = \"pn_nested\"\n" ^
                 (if declare_parent then
                    "\n[projects.pn_parent]\npath = \"..\"\n"
                  else ""));
     write_file (root ++ "Holmakefile")
                "all: PNParent.uo nested/dep/PNDep.uo\n.PHONY: all\n";
     write_file (sub ++ "Holmakefile") "all: PNSub.uo\n.PHONY: all\n";
     write_file (nested ++ "Holmakefile") "all: PNTop.uo\n.PHONY: all\n";
     write_file (lib ++ "PNLib.sml")
                "structure PNLib = struct val lib = 1 end\n";
     write_file (root ++ "PNParent.sml")
                "structure PNParent = struct\n\
                \  open PNLib val p = lib + 1\n\
                \end\n";
     write_file (sub ++ "PNSub.sml")
                "structure PNSub = struct open PNLib val s = lib + 2 end\n";
     write_file (nested_dep ++ "PNDep.sml")
                "structure PNDep = struct val dep = 3 end\n";
     write_file (nested_extra ++ "PNExtra.sml")
                "structure PNExtra = struct val extra = 4 end\n";
     write_file (nested ++ "PNTop.sml")
                "structure PNTop = struct\n\
                \  open PNDep PNLib\n\
                \  val t = dep + lib\n\
                \end\n")

val parent_uo = root ++ "PNParent.uo"
val lib_uo = lib ++ "PNLib.uo"
val sub_uo = sub ++ "PNSub.uo"
val dep_uo = nested_dep ++ "PNDep.uo"
val top_uo = nested ++ "PNTop.uo"
val extra_uo = nested_extra ++ "PNExtra.uo"

(* Poly tolerates an unresolved `open' at this stage, so the presence of
   the *dependent's* .uo proves nothing about the include path.  What
   proves it is that the dependency's product got built: PNLib.uo for
   the parent's source-only dir, PNDep.uo for the nested project's. *)
fun report res =
    "exit=" ^ Bool.toString (OS.Process.isSuccess res) ^
    " PNParent.uo=" ^ Bool.toString (exists parent_uo) ^
    " lib/PNLib.uo=" ^ Bool.toString (exists lib_uo) ^
    " sub/PNSub.uo=" ^ Bool.toString (exists sub_uo) ^
    " nested/PNTop.uo=" ^ Bool.toString (exists top_uo) ^
    " nested/dep/PNDep.uo=" ^ Bool.toString (exists dep_uo) ^
    " nested/extra/PNExtra.uo=" ^ Bool.toString (exists extra_uo)

fun check what res built =
    if OS.Process.isSuccess res andalso List.all exists built then ok ()
    else die ("FAILED (" ^ what ^ "): " ^ report res)

(* ---------------------------------------------------------------------- *)

val () = build_fixture {declare_parent = true}

val () = tprint "Parent's prereq inside a nested project builds"
val () = check "plain invocation at the parent" (hm_in root [])
               [parent_uo, lib_uo, dep_uo]

val () = tprint "...without unreferenced nested targets"
val () = if exists top_uo orelse exists extra_uo then
           die ("FAILED: built without -r: " ^ report OS.Process.success)
         else ok ()

val () = tprint "-r in the parent builds the nested project as well"
val () = check "-r at the parent" (hm_in root ["-r"]) [top_uo, extra_uo]

val () = tprint "-r cleanAll reaches into the nested project too"
val res = hm_in root ["-r", "cleanAll"]
val () =
    if OS.Process.isSuccess res andalso
       not (List.exists exists [parent_uo, lib_uo, top_uo, dep_uo, extra_uo])
    then ok ()
    else die ("FAILED: left behind: " ^ report res)

(* PNTop.sml opens both PNDep (a dir of the nested project) and PNLib (a
   dir of the parent, reachable only because the nested project declares
   [projects.pn_parent]).  Neither is named in any INCLUDES. *)
val () = tprint "Nested project's own dirs resolve without INCLUDES"
val () = check "invocation inside the nested project" (hm_in nested [])
               [top_uo, dep_uo, lib_uo]

(* ---------------------------------------------------------------------- *)

val () = build_fixture {declare_parent = true}

val () = tprint "--dirs sub nested from the enclosing project root"
val () = check "--dirs from the parent"
               (hm_in root ["--dirs", "sub", "nested"])
               [sub_uo, lib_uo, top_uo, dep_uo]

val () = tprint "...leaving the sub-project's other dirs alone"
val () = if exists extra_uo then
           die "FAILED: nested/extra/PNExtra.uo built without -r"
         else ok ()

val () = tprint "-r --dirs nested covers the whole sub-project"
val () = check "-r --dirs" (hm_in root ["-r", "--dirs", "nested"]) [extra_uo]

(* Same sub-project, but invoked from a directory in no project at all:
   the nested root's own holproject.toml is what has to be found. *)
val () = build_fixture {declare_parent = true}

val () = tprint "--dirs P/nested from outside every project"
val () = check "--dirs from outside"
               (hm_in outside ["--dirs", "P" ++ "nested"])
               [top_uo, dep_uo, lib_uo]

(* Control: none of the above can be an accident of the include path
   already containing everything. *)
val () = build_fixture {declare_parent = false}

val () = tprint "--no-project makes the same fixture fail"
val res = hm_in root ["--no-project"]
val () = if OS.Process.isSuccess res then
           die "FAILED: --no-project build unexpectedly succeeded"
         else ok ()

val () = rm_rf outside
