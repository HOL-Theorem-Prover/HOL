(* A project nested inside another sees nothing of the enclosing tree
   unless it declares it with [projects.<id>]: project registration is
   never inherited upwards, and a directory no registered project owns
   gets no implicit INCLUDES at all.  The enclosing tree is still
   *scanned* when something names it explicitly -- a holpathdb variable
   resolves regardless of project registration -- so the symptom is not
   "directory not found" but a compile error against an include path
   that turned out to be empty, or a "Don't know how to build" for the
   directories reachable only through the missing implicit includes.

   Two ways the declaration goes missing, and a diagnostic for each:

     - it is simply absent, warned about here as "refers into the
       project rooted at ...";

     - it is present under a misspelled key ([project.parent] for
       [projects.parent]), which reads as correct and behaves as
       absent.  TOML lookups cannot tell a typo from an absent key, so
       this needs the unrecognised-key warning to be intelligible --
       without it the advice would be "declare [projects.parent]" to
       someone whose file appears to do exactly that.

   The fixture is built under a fresh temp directory: the HOL
   repository root carries its own holproject.toml, so an in-tree
   fixture would sit inside it and measure ambient state.  Each round
   rebuilds the fixture from scratch, because a cached dep file
   computed under one include path survives a change to that path. *)

open testutils

val op++ = OS.Path.concat

val holmake = Systeml.HOLDIR ++ "bin" ++ "Holmake"

(* The fixture holds no HOL code, so the inner builds want neither
   overlay nor heap.  `--no-cache` so a cache-enabled regression run
   cannot supply a product the fixture is asserting about. *)
val baseopts =
    "--no-cache" ::
    (if Systeml.ML_SYSNAME = "poly" then ["--no_overlay", "--poly_not_hol"]
     else ["--no_overlay"])

fun write_file p contents =
    let val s = TextIO.openOut p
    in TextIO.output (s, contents); TextIO.closeOut s end

fun read_file p =
    let val s = TextIO.openIn p
    in TextIO.inputAll s before TextIO.closeIn s end
    handle IO.Io _ => ""

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

(* Object files live under .hol/objs/ (HFS_NameMunge); HOLFileSys does
   that translation for us, and is the identity under mosml. *)
fun exists p = HOLFileSys.access (p, []) handle OS.SysErr _ => false

val tmproot = HMTestPaths.mk_root ()

val outside = tmproot ++ "outside"
val parent = tmproot ++ "parent"
val core = parent ++ "core"
val lib = parent ++ "lib"
val nested = parent ++ "nested"

val captured = tmproot ++ "output"

(* Holmake in `nested`, with everything it says captured.  Not `-q`:
   the warnings under test are what we are here to read. *)
fun hm_nested () =
    let
      val saved = OS.FileSys.getDir()
      val () = OS.FileSys.chDir nested
      val cmd = String.concatWith " "
                  (Systeml.protect holmake :: "--nolmbc" :: baseopts @
                   [">", Systeml.protect captured, "2>&1"])
      val res = OS.Process.system cmd
    in
      OS.FileSys.chDir saved;
      (res, read_file captured)
    end

(* ----------------------------------------------------------------------
    The fixture.  `tmproot` itself carries no project file, so
    `parent` is the only enclosing project there is.

      tmproot/
        outside/PUPOutside.sml    in no project at all
        parent/                   project "parent", holpath PARENTDIR
          core/PUPCore.sml        reachable only via parent's implicit
                                  INCLUDES -- nothing names it
          lib/Holmakefile         no INCLUDES: relies on the implicit
          lib/PUPLib.sml          opens PUPCore
          nested/                 project "nested"
            Holmakefile           INCLUDES = the `points_at` directory
            PUPTop.sml            opens what that directory holds

    `core` is what makes the difference observable: `lib` is named
    explicitly and so gets scanned either way, but `core` is reached
    only through the implicit INCLUDES `lib` gets from its project.
   ---------------------------------------------------------------------- *)

(* What nested's Holmakefile reaches out to: a directory of the
   enclosing project, or one in no project at all. *)
datatype pointing = Lib | Outside

fun build_fixture {toml : string, points_at : pointing} =
    (rm_rf parent; rm_rf outside;
     List.app OS.FileSys.mkDir [outside, parent, core, lib, nested];
     write_file (parent ++ "holproject.toml")
                "name = \"parent\"\nholpath = \"PARENTDIR\"\n";
     write_file (core ++ "PUPCore.sml")
                "structure PUPCore = struct val core = 1 end\n";
     write_file (lib ++ "Holmakefile")
                "# no INCLUDES: lib relies on what its project gives it\n";
     write_file (lib ++ "PUPLib.sml")
                "structure PUPLib = struct open PUPCore\n\
                \  val lib = core + 1\n\
                \end\n";
     write_file (outside ++ "PUPOutside.sml")
                "structure PUPOutside = struct val out = 9 end\n";
     write_file (nested ++ "holproject.toml") toml;
     case points_at of
         Lib =>
           (write_file (nested ++ "Holmakefile")
                       "INCLUDES = $(PARENTDIR)/lib\n";
            write_file (nested ++ "PUPTop.sml")
                       "structure PUPTop = struct open PUPLib\n\
                       \  val top = lib + 1\n\
                       \end\n")
       | Outside =>
           (write_file (nested ++ "Holmakefile") "INCLUDES = ../../outside\n";
            write_file (nested ++ "PUPTop.sml")
                       "structure PUPTop = struct open PUPOutside\n\
                       \  val top = out + 1\n\
                       \end\n"))

val core_uo = core ++ "PUPCore.uo"

val refers_warning = "refers into the project rooted at " ^ parent
val unknown_warning = "unrecognised key `project`"

fun has s out = String.isSubstring s out

(* The `tprint` line printed just before says which case this is, and
   `die` dumps everything Holmake said, so a failure needs no further
   labelling here. *)
fun expect out (wanted, unwanted) =
    if List.all (fn s => has s out) wanted andalso
       List.all (fn s => not (has s out)) unwanted
    then OK ()
    else die ("FAILED:\n" ^ out)

(* ---------------------------------------------------------------------- *)

val () = build_fixture {toml = "name = \"nested\"\n", points_at = Lib}

val () = tprint "Undeclared enclosing project is named, with the stanza"
val (_, out) = hm_nested ()
val () = expect out ([refers_warning, lib, "[projects.parent]",
                      "path = \"..\""],
                     ["unrecognised key"])

val () = tprint "...and its directories got no implicit INCLUDES"
val () = if exists core_uo then
           die ("FAILED: " ^ core_uo ^ " was built after all")
         else OK ()

(* Case B: the declaration is there, under a singular key.  Both
   warnings have to fire -- part 1's advice alone would tell the author
   to declare what their file appears to declare already. *)
val () = build_fixture
           {toml = "name = \"nested\"\n\n[project.parent]\npath = \"..\"\n",
            points_at = Lib}

val () = tprint "A misspelled [project.<id>] key is reported as unknown"
val (_, out) = hm_nested ()
val () = expect out ([unknown_warning, "(recognised: ", ", projects,"], [])

val () = tprint "...and the enclosing project is still reported missing"
val () = expect out ([refers_warning, "[projects.parent]"], [])

(* The declared form, from a nested root: silent, and `core` -- named
   nowhere, reachable only through the implicit INCLUDES `lib` gets
   from the project that now owns it -- is built. *)
val () = build_fixture
           {toml = "name = \"nested\"\n\n[projects.parent]\npath = \"..\"\n",
            points_at = Lib}

val () = tprint "Declaring [projects.parent] silences both warnings"
val (res, out) = hm_nested ()
val () = expect out ([], [refers_warning, "unrecognised key"])

val () = tprint "...and the enclosing project's dirs are now reachable"
val () = if OS.Process.isSuccess res andalso exists core_uo then OK ()
         else die ("FAILED: rc=" ^ Bool.toString (OS.Process.isSuccess res) ^
                   " " ^ core_uo ^ "=" ^ Bool.toString (exists core_uo) ^
                   "\n" ^ out)

(* Negative case for the unknown-key warning: every key any reader of
   holproject.toml understands, including [h4pedant], whose sub-keys
   are h4pedant's own business and are not descended into.  This is the
   round above with the extra keys added, so only the project file
   changes -- the include path, and hence what has to be built, is the
   same. *)
val () = write_file (nested ++ "holproject.toml")
                    "name = \"nested\"\n\
                    \holpath = \"NESTEDDIR\"\n\
                    \holmake = true\n\
                    \exclude = []\n\
                    \external_includes = []\n\
                    \\n\
                    \[projects.parent]\n\
                    \path = \"..\"\n\
                    \exclude = []\n\
                    \\n\
                    \[h4pedant]\n\
                    \linelen = 80\n\
                    \unicode_ok = false\n\
                    \include = [\".\"]\n\
                    \\n\
                    \[[h4pedant.dir]]\n\
                    \path = \".\"\n\
                    \linelen = 0\n"

val () = tprint "A file using every recognised key is silent"
val (res, out) = hm_nested ()
val () = if OS.Process.isSuccess res then
           expect out ([], ["unrecognised key", refers_warning])
         else die ("FAILED: build died:\n" ^ out)

(* Negative case for the reaches-out warning.  `parent` is still an
   undeclared enclosing project, but nothing points into it: an
   ownerless directory elsewhere on disk, whose own Holmakefile carries
   whatever INCLUDES it needs, is the classical arrangement. *)
val () = build_fixture {toml = "name = \"nested\"\n", points_at = Outside}

val () = tprint "An ownerless dir outside every ancestor project is fine"
val (_, out) = hm_nested ()
val () = expect out ([], [refers_warning])

val () = rm_rf tmproot
