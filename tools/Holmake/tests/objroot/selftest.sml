(* Test artifact-root configuration, building, loading and cleaning.
   Fixtures use temporary directories and [bare] theories, so they need
   only hol.state0. *)

open testutils

infix 7 ++
val op++ = OS.Path.concat
val HOLDIR = Globals.HOLDIR
val Holmake = HOLDIR ++ "bin" ++ "Holmake"
val hol = HOLDIR ++ "bin" ++ "hol"
val hol_state0 = HOLDIR ++ "bin" ++ "hol.state0"

val common_args = ["--nolmbc", "--no-cache"]

fun capture dir cmd =
    let
      val outfile = OS.FileSys.tmpName()
      val r = OS.Process.system
                ("cd " ^ Systeml.protect dir ^ " && " ^ cmd ^ " > " ^
                 outfile ^ " 2>&1")
      val istrm = TextIO.openIn outfile
      val output = TextIO.inputAll istrm before TextIO.closeIn istrm
      val _ = OS.FileSys.remove outfile handle OS.SysErr _ => ()
    in
      (r, output)
    end

(* env contains shell-quoted NAME=value assignments. *)
fun holmake_env env dir args =
    capture dir (String.concatWith " "
                   (env @ map Systeml.protect
                              (Holmake :: common_args @ args)))
val holmake = holmake_env []

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

fun exists p = OS.FileSys.access (p, [])
fun isdir p = OS.FileSys.isDir p handle OS.SysErr _ => false

(* List files recursively under p. *)
fun files_under p =
    if isdir p then
      let val ds = OS.FileSys.openDir p
          fun loop A =
              case OS.FileSys.readDir ds of
                  NONE => (OS.FileSys.closeDir ds; A)
                | SOME nm => loop (files_under (p ++ nm) @ A)
      in loop [] end
    else if exists p then [p] else []

fun contains sub s = String.isSubstring sub s

fun check msg b = if b then () else die ("FAILED: " ^ msg)

fun check_build msg (r, out) =
    if OS.Process.isSuccess r then ()
    else die ("FAILED: " ^ msg ^ "; output:\n" ^ out)

val T = HMTestPaths.mk_root ()
val _ = OS.Process.atExit
          (fn () => (ignore (OS.Process.system
                               ("chmod -R u+w " ^ Systeml.protect T));
                     rm_rf T))

fun holheap_decl () =
    "ifdef POLY\nHOLHEAP = " ^ hol_state0 ^ "\nendif\n"

(* C in dirA/sub depends on A in dirA; B in dirB depends on both.
   A custom rule in dirA writes a marker to $(HOLOBJDIR). *)
fun mk_fixture {name, toml} =
    let
      val root = T ++ name
      val dirA = root ++ "dirA"
      val sub = dirA ++ "sub"
      val dirB = root ++ "dirB"
    in
      app OS.FileSys.mkDir [root, dirA, sub, dirB];
      case toml of
          NONE => ()
        | SOME extra =>
          write_file (root ++ "holproject.toml")
                     ("name = \"objroot_test\"\n" ^ extra);
      write_file (root ++ "Holmakefile")
        (holheap_decl () ^
         "CLINE_OPTIONS = -r\n\n\
         \all: dirB/BTheory.uo dirA/ATheory.uo dirA/sub/CTheory.uo\n\
         \.PHONY: all\n");
      write_file (dirA ++ "Holmakefile")
        (holheap_decl () ^
         "all: $(DEFAULT_TARGETS) marker\n\
         \.PHONY: all\n\n\
         \marker:\n\
         \\tmkdir -p $(HOLOBJDIR) && touch $(HOLOBJDIR)/marker\n");
      write_file (dirA ++ "AScript.sml")
        "Theory A[bare]\nAncestors bool\nTheorem a_truth = TRUTH\n";
      write_file (sub ++ "Holmakefile") (holheap_decl () ^ "INCLUDES = ..\n");
      write_file (sub ++ "CScript.sml")
        "Theory C[bare]\nAncestors A\nTheorem c_truth = a_truth\n";
      write_file (dirB ++ "Holmakefile")
        (holheap_decl () ^ "INCLUDES = ../dirA ../dirA/sub\n");
      write_file (dirB ++ "BScript.sml")
        "Theory B[bare]\nAncestors A C\nTheorem b_truth = c_truth\n";
      root
    end

fun thy_dats out =
    [out ++ "objs/dirA/ATheory.dat", out ++ "objs/dirA/sub/CTheory.dat",
     out ++ "objs/dirB/BTheory.dat"]

fun modtimes ps = map OS.FileSys.modTime ps

(* Path mapping and directory listings. *)
val _ = tprint "Pure mapping: HOLtoFS, FStoHOL, objdir_for, owned_by_layout"
val R = T ++ "r12"
val O = T ++ "o12"
val E = T ++ "elsewhere"
val _ = app OS.FileSys.mkDir [R, R ++ "a", E]
val _ = HFS_NameMunge.configure (SOME {srcroot = R, objroot = O})
fun fullfile p = Option.map #fullfile (HFS_NameMunge.HOLtoFS p)
val _ =
    let
      open HFS_NameMunge
      val saved = OS.FileSys.getDir()
      val relative =
          (OS.FileSys.chDir (R ++ "a");
           fullfile "x.uo" before OS.FileSys.chDir saved)
    in
      check "theory .dat"
            (fullfile (R ++ "a/fooTheory.dat") =
             SOME (O ++ "objs/a/fooTheory.dat"));
      check ".uo" (fullfile (R ++ "a/x.uo") = SOME (O ++ "objs/a/x.uo"));
      check "source file" (fullfile (R ++ "a/x.sml") = NONE);
      check "sigobj" (fullfile (HOLDIR ++ "sigobj/x.uo") = NONE);
      check "already in objroot" (fullfile (O ++ "objs/a/x.uo") = NONE);
      check "outside srcroot"
            (fullfile (E ++ "x.uo") = SOME (E ++ ".hol/objs/x.uo"));
      check "relative name" (relative = SOME (O ++ "objs/a/x.uo"));
      check "FStoHOL objroot"
            (FStoHOL (O ++ "objs/a/x.uo") = SOME (R ++ "a/x.uo"));
      check "FStoHOL legacy"
            (FStoHOL (E ++ ".hol/objs/x.uo") = SOME (E ++ "x.uo"));
      check "FStoHOL source" (FStoHOL (R ++ "a/x.uo") = NONE);
      check "objdir_for" (objdir_for (R ++ "a") = O ++ "objs/a");
      check "objdir_for root" (objdir_for R = O ++ "objs");
      check "depdir_for" (depdir_for (R ++ "a") = O ++ "make-deps/a");
      check "objdir_for objroot dir"
            (objdir_for (O ++ "objs/a") = O ++ "objs/a");
      check "owned" (owned_by_layout (R ++ "a"));
      check "not owned (objroot)" (not (owned_by_layout (O ++ "objs/a")));
      check "not owned (elsewhere)" (not (owned_by_layout E))
    end
fun insert (x : string) [] = [x]
  | insert x (y :: ys) = if x <= y then x :: y :: ys else y :: insert x ys
fun sort xs = List.foldl (fn (x, A) => insert x A) [] xs
fun listing d =
    let
      val ds = HOLFileSys.openDir d
      fun loop A = case HOLFileSys.readDir ds of
                       NONE => (HOLFileSys.closeDir ds; A)
                     | SOME f => loop (f :: A)
    in
      sort (loop [])
    end
val _ =
    let
      val od = O ++ "objs/a"
    in
      HOLFileSys.createDirIfNecessary od;
      write_file (od ++ "p.uo") ""; write_file (od ++ "q.uo") "";
      write_file (R ++ "a/s.sml") "";
      OS.FileSys.mkDir (R ++ "a/.hol");
      check "objroot dir listed once" (listing od = ["p.uo", "q.uo"]);
      check "source dir chains its products, hides .hol"
            (listing (R ++ "a") = ["p.uo", "q.uo", "s.sml"])
    end
val _ = HFS_NameMunge.configure NONE
val _ = check "legacy restored"
              (fullfile (R ++ "a/x.uo") = SOME (R ++ "a/.hol/objs/x.uo") andalso
               HFS_NameMunge.objdir_for (R ++ "a") = R ++ "a/.hol/objs")
val _ = OK ()

(* Build from the project root with an external objroot from the manifest.
   Exercise both parallel and -j1 builds. *)
val out = T ++ "out"
val root = mk_fixture {name = "p1", toml = SOME ("objroot = \"" ^ out ^ "\"\n")}
val dirA = root ++ "dirA"
val dirB = root ++ "dirB"

fun check_products jflags =
    let
      val r = holmake root jflags
      val expected =
          map (fn s => out ++ s)
              ["objs/dirA/ATheory.dat", "objs/dirA/ATheory.sml",
               "objs/dirA/ATheory.sig", "objs/dirA/ATheory.uo",
               "objs/dirA/ATheory.ui", "objs/dirA/sub/CTheory.dat",
               "objs/dirB/BTheory.dat", "objs/dirA/marker",
               "make-deps/dirA/AScript.sml.d", "make-deps/dirA/lastmaker"] @
          (if null jflags then [out ++ "logs/dirB/BTheory"] else [])
      fun is_product f =
          let val {base, ext} = OS.Path.splitBaseExt (OS.Path.file f)
          in
            ext = SOME "uo" orelse ext = SOME "ui" orelse
            String.isSuffix "Theory" base
          end
    in
      check_build "build into objroot" r;
      List.app (fn p => check ("missing " ^ p) (exists p)) expected;
      List.app (fn d => check (d ^ " exists") (not (exists (d ++ ".hol"))))
               [root, dirA, dirA ++ "sub", dirB];
      check "products in the source tree"
            (not (List.exists is_product (files_under root)))
    end

val _ = tprint "External objroot from holproject.toml (default -j)"
val _ = check_products []
val _ = HFS_NameMunge.configure (SOME {srcroot = root, objroot = out})
val _ = check "logical view of BTheory.dat"
              (HOLFileSys.access (dirB ++ "BTheory.dat", []))
val _ = HFS_NameMunge.configure NONE
val _ = OK ()

(* An unchanged project does not rebuild. *)
val _ = tprint "Rerun leaves the products alone"
val before_times = modtimes (thy_dats out)
val (r2, o2) = holmake root []
val _ = check_build "rerun" (r2, o2)
val _ = check "theories rebuilt" (modtimes (thy_dats out) = before_times)
val _ = check "rerun built theories" (not (contains "Building" o2))
val _ = OK ()

(* Load products with layout settings from options or the project file. *)
fun write_check dir =
    write_file (dir ++ "check.ML")
               "val _ = load \"BTheory\";\n\
               \val _ = DB.fetch \"B\" \"b_truth\";\n"
val _ = write_check dirB
fun hol_run dir env opts =
    capture dir
      (String.concatWith " "
         (env @ map Systeml.protect
                    ([hol, "run", "--holstate=" ^ hol_state0] @ opts @
                     ["check.ML"])))
val _ = tprint "hol run loads BTheory with --objroot/--srcroot"
val _ = check_build "hol run with options"
          (hol_run dirB [] ["--objroot=" ^ out, "--srcroot=" ^ root])
val _ = OK ()
val _ = tprint "hol run loads BTheory with holproject.toml alone"
val _ = check_build "hol run with the toml" (hol_run dirB [] [])
val _ = OK ()
val _ = OS.FileSys.remove (dirB ++ "check.ML")

val _ = tprint "The -j1 builder uses the objroot too"
val _ = check_build "cleanAll" (holmake root ["-r", "cleanAll"])
val _ = check_products ["-j", "1"]
val _ = OK ()

(* A subdirectory build uses objroot for its included dependencies. *)
val _ = tprint "Holmake in dirB builds A and C into the objroot"
val _ = check_build "cleanAll" (holmake root ["-r", "cleanAll"])
val _ = check_build "build in dirB" (holmake dirB [])
val _ = check "A, C, B built" (List.all exists (thy_dats out))
val _ = OK ()

(* Cleaning preserves artifacts belonging to other source directories. *)
val _ = tprint "clean and cleanAll in dirA leave other directories alone"
val _ = check_build "build" (holmake root [])
val _ = check_build "clean in dirA" (holmake dirA ["clean"])
val _ = check "A's products removed"
              (not (exists (out ++ "objs/dirA/ATheory.dat")) andalso
               not (exists (out ++ "objs/dirA/ATheory.uo")))
val _ = check "C and B kept"
              (exists (out ++ "objs/dirA/sub/CTheory.dat") andalso
               exists (out ++ "objs/dirB/BTheory.dat"))
val _ = check_build "cleanAll in dirA" (holmake dirA ["cleanAll"])
val _ = check "A's depfiles removed"
              (not (exists (out ++ "make-deps/dirA/AScript.sml.d")))
val _ = check "B's depfiles and C's products kept"
              (exists (out ++ "make-deps/dirB/BScript.sml.d") andalso
               exists (out ++ "objs/dirA/sub/CTheory.dat"))
val _ = check_build "-r cleanAll" (holmake root ["-r", "cleanAll"])
val _ = check "files left in objroot" (null (files_under out))
val _ = OK ()

(* Configuration precedence: command line, project file, environment. *)
val out2 = T ++ "out2"
val out3 = T ++ "out3"
fun has_products d = exists (d ++ "objs/dirA/ATheory.dat")
val _ = tprint "--objroot beats holproject.toml"
val _ = check_build "build" (holmake root ["--objroot=" ^ out2])
val _ = check "products in out2, not out"
              (has_products out2 andalso not (has_products out))
val _ = rm_rf out2
val _ = OK ()
val _ = tprint "holproject.toml beats HOLOBJROOT"
val _ = check_build "build"
          (holmake_env ["HOLOBJROOT=" ^ Systeml.protect out3] root [])
val _ = check "products in out, not out3"
              (has_products out andalso not (has_products out3))
val _ = check_build "cleanAll" (holmake root ["-r", "cleanAll"])
val _ = OK ()
val rootE = mk_fixture {name = "p6", toml = SOME ""}
val _ = tprint "HOLOBJROOT applies when holproject.toml has no objroot"
val _ = check_build "build"
          (holmake_env ["HOLOBJROOT=" ^ Systeml.protect out3] rootE [])
val _ = check "products in out3" (has_products out3)
val _ = check "source tree clean" (not (exists (rootE ++ "dirA/.hol")))
val _ = OK ()
val _ = tprint "hol run loads BTheory with HOLOBJROOT/HOLSRCROOT"
val _ = write_check (rootE ++ "dirB")
val _ = check_build "hol run with environment"
          (hol_run (rootE ++ "dirB")
                   ["HOLOBJROOT=" ^ Systeml.protect out3,
                    "HOLSRCROOT=" ^ Systeml.protect rootE] [])
val _ = check "hol run without the environment loaded BTheory"
              (not (OS.Process.isSuccess
                      (#1 (hol_run (rootE ++ "dirB") [] []))))
val _ = rm_rf out3
val _ = OK ()
val _ = tprint "--objroot beats HOLOBJROOT"
val _ = check_build "build"
          (holmake_env ["HOLOBJROOT=" ^ Systeml.protect out3] rootE
                       ["--objroot=" ^ out2])
val _ = check "products in out2, not out3"
              (has_products out2 andalso not (has_products out3))
val _ = rm_rf out2
val _ = OK ()
val _ = tprint "-C root --objroot=rel resolves rel against root"
val _ = check_build "build" (holmake T ["-C", rootE, "--objroot=relout"])
val _ = check "products in root/relout"
              (has_products (rootE ++ "relout") andalso
               not (exists (T ++ "relout")))
val _ = OK ()

(* Require an explicit source root outside a project.  Preserve separate
   products for modules with the same basename in different directories. *)
val rootN = T ++ "p7"
val _ = app OS.FileSys.mkDir [rootN, rootN ++ "dirA", rootN ++ "dirB"]
val _ = write_file (rootN ++ "Holmakefile")
                   (holheap_decl () ^ "INCLUDES = dirA dirB\n")
val _ = app (fn (d, x) =>
                (write_file (rootN ++ d ++ "Holmakefile") (holheap_decl ());
                 write_file (rootN ++ d ++ "util.sml")
                            ("structure util = struct val x = " ^ x ^
                             " end\n")))
            [("dirA", "1"), ("dirB", "2")]
val out7 = T ++ "out7"
val _ = tprint "--objroot without a project or --srcroot is an error"
val (r7, o7) = holmake rootN ["--objroot=" ^ out7]
val _ = check "accepted" (not (OS.Process.isSuccess r7))
val _ = check ("message does not name --srcroot:\n" ^ o7)
              (contains "--srcroot" o7)
val _ = OK ()
val _ = tprint "...and with --srcroot=. duplicate basenames build apart"
val _ = check_build "build" (holmake rootN ["-r", "--objroot=" ^ out7,
                                            "--srcroot=."])
val _ = check "both util.uo"
              (exists (out7 ++ "objs/dirA/util.uo") andalso
               exists (out7 ++ "objs/dirB/util.uo"))
val _ = OK ()
val _ = tprint "Inside HOLDIR the srcroot is not defaulted"
val (r7h, o7h) =
    holmake T ["-C", HOLDIR ++ "tools/Holmake/tests/objroot",
               "--objroot=" ^ (T ++ "out4"), "-n"]
val _ = check "accepted" (not (OS.Process.isSuccess r7h))
val _ = check ("message does not name --srcroot:\n" ^ o7h)
              (contains "--srcroot" o7h)
val _ = OK ()

(* Project discovery skips an artifact root inside the source tree. *)
val _ = tprint "In-tree objroot is pruned from project discovery"
val root8 = mk_fixture {name = "p8",
                        toml = SOME "objroot = \"build\"\nholmake = true\n"}
val (r8, o8) = holmake root8 []
val _ = check_build "build" (r8, o8)
val _ = check "products in build/"
              (List.all exists (thy_dats (root8 ++ "build")))
val _ = check ("build/ scanned or clashing:\n" ^ o8)
              (not (contains "/build" o8) andalso
               not (contains "ambiguous" o8))
val times8 = modtimes (thy_dats (root8 ++ "build"))
val _ = check_build "rerun" (holmake root8 [])
val _ = check "rerun rebuilt" (modtimes (thy_dats (root8 ++ "build")) = times8)
val _ = OK ()

(* Build read-only sources into a writable artifact root. *)
val _ = tprint "Read-only sources build into an external objroot"
val _ = check_build "cleanAll" (holmake root ["-r", "cleanAll"])
val _ = OS.Process.system ("chmod -R a-w " ^ Systeml.protect root)
val r9 = holmake root []
val _ = OS.Process.system ("chmod -R u+w " ^ Systeml.protect root)
val _ = if Posix.ProcEnv.uidToWord (Posix.ProcEnv.getuid ()) = 0w0 then
          (* Root bypasses the source permissions restriction. *)
          ()
        else (check_build "read-only build" r9;
              check "products" (List.all exists (thy_dats out)))
val _ = OK ()

(* Cachekey builds store stamps in objroot and reuse unchanged products. *)
val _ = tprint "--rebuild=cachekey uses objroot stamps"
val _ = check_build "cleanAll" (holmake root ["-r", "cleanAll"])
val _ = check_build "first" (holmake root ["--rebuild=cachekey"])
val _ = check "cachekey stamp" (exists (out ++ "objs/dirA/ATheory.cachekey"))
val times10 = modtimes (thy_dats out)
val _ = check_build "second" (holmake root ["--rebuild=cachekey"])
val _ = check "second run rebuilt" (modtimes (thy_dats out) = times10)
val _ = OK ()

(* Without an artifact root, retain the legacy layout. *)
val _ = tprint "Without objroot products stay in .hol/objs"
val root11 = mk_fixture {name = "p11", toml = NONE}
val out11 = T ++ "out11"
val _ = check_build "build" (holmake (root11 ++ "dirA") [])
val _ = check "legacy products"
              (exists (root11 ++ "dirA/.hol/objs/ATheory.dat") andalso
               exists (root11 ++ "dirA/.hol/objs/marker") andalso
               not (exists out11))
val _ = OK ()
