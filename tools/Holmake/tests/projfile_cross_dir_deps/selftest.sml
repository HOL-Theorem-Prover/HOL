(* A target's dependencies must not depend on which directory's scan
   reaches it first.

   B/Holmakefile gives B/Bb.uo an extra dependency with a rule that has
   no commands (`Bb.uo: stamp.txt'), and Bb.sml refers to B's structure
   Bc, so holdep adds B/Bc.uo as well.  A/Aa.sml refers to Bb.  In
   project mode every directory is scanned, so when A is scanned first
   Bb.uo is reached from A.  Its node must still carry both
   dependencies, and changing either must recompile it -- as it does
   when B is scanned first, and with INCLUDES, where the recursion
   reaches B before A.

   The project is built under a temp directory: a fixture inside the
   HOL tree would be a nested project of the tree's own
   holproject.toml. *)

open testutils

infix ++
val op++ = OS.Path.concat

val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

val failures = ref 0
val _ = diemode := Remember failures
fun fatal s : 'a = (die s; OS.Process.exit OS.Process.failure)

(* --- plumbing ------------------------------------------------------- *)

fun write_file p contents =
    let val s = TextIO.openOut p
    in TextIO.output (s, contents); TextIO.closeOut s end

fun read_file p =
    let val s = TextIO.openIn p
    in TextIO.inputAll s before TextIO.closeIn s end
    handle IO.Io _ => ""

fun rm_rf p =
    if OS.FileSys.isDir p handle OS.SysErr _ => false then
      let val ds = OS.FileSys.openDir p
          fun loop () =
              case OS.FileSys.readDir ds of
                  NONE => OS.FileSys.closeDir ds
                | SOME nm => (rm_rf (p ++ nm); loop ())
      in loop (); OS.FileSys.rmDir p handle OS.SysErr _ => () end
    else (OS.FileSys.remove p handle OS.SysErr _ => ())

fun rm_f p = OS.FileSys.remove p handle OS.SysErr _ => ()

fun mkdir_p p = OS.FileSys.mkDir p handle OS.SysErr _ => ()

fun fresh_dir () =
    let val nm = OS.FileSys.tmpName ()
    in rm_f nm; OS.FileSys.mkDir nm; nm end

fun in_dir d f =
    let
      val saved = OS.FileSys.getDir ()
      val _ = OS.FileSys.chDir d
      val result = f () handle e => (OS.FileSys.chDir saved; raise e)
    in
      OS.FileSys.chDir saved; result
    end

fun hm_ok dir args =
    let
      val out = OS.FileSys.tmpName ()
      val st = in_dir dir (fn () =>
                  Systeml.systeml_out {outfile = out} (Holmake :: args))
    in
      rm_f out; OS.Process.isSuccess st
    end

(* --json goes to stdout, so it needs its own redirect rather than
   systeml_out's merged one. *)
fun hm_json dir args =
    let
      val jsonf = OS.FileSys.tmpName ()
      val errf = OS.FileSys.tmpName ()
      val cmd = String.concatWith " " (Holmake :: args @ ["--json"]) ^
                " > " ^ jsonf ^ " 2> " ^ errf
      val st = in_dir dir (fn () => OS.Process.system cmd)
    in
      rm_f errf;
      if OS.Process.isSuccess st then jsonf
      else (rm_f jsonf; fatal ("Holmake --json failed in " ^ dir))
    end

(* .uo/.ui live under .hol/objs, so mtimes go through HOLFileSys. *)
fun mtime_of f =
    if HOLFileSys.access (f, [HOLFileSys.A_READ]) then
      SOME (HOLFileSys.modTime f)
    else NONE

fun mtime_str NONE = "<missing>"
  | mtime_str (SOME t) = Time.toString t

(* Coarse filesystems can give two events the same mtime; sleep so a
   following write is strictly newer. *)
fun sleep_for_mtime () = OS.Process.sleep (Time.fromMilliseconds 1100)

(* target |-> the targets it depends on, as Holmake --json reports them *)
fun read_deps jsonf : (string * string list) list =
    let
      open JSON
      fun fld nm flds =
          case List.find (fn (k, _) => k = nm) flds of
              SOME (_, v) => v
            | NONE => fatal ("--json node has no " ^ nm ^ " field")
      fun str (STRING s) = s
        | str _ = fatal "expected a JSON string"
      fun int (INT i) = IntInf.toInt i
        | int _ = fatal "expected a JSON int"
      fun node (OBJECT flds) =
          (int (fld "node_id" flds),
           str (fld "target" flds),
           case fld "dependencies" flds of
               ARRAY ds => map int ds
             | _ => fatal "expected a JSON array of dependencies")
        | node _ = fatal "expected a JSON object per node"
      val nodes =
          case JSONParser.parseFile jsonf of
              ARRAY objs => map node objs
            | _ => fatal "expected a JSON array of nodes"
      fun target_of i =
          case List.find (fn (j, _, _) => i = j) nodes of
              SOME (_, t, _) => t
            | NONE => fatal ("--json refers to absent node " ^ Int.toString i)
    in
      map (fn (_, t, ds) => (t, map target_of ds)) nodes
    end

(* --- the project ---------------------------------------------------- *)

val plainopts = ["-r", "--nolmbc", "--no_overlay", "--poly_not_hol"]

val root = fresh_dir ()
val _ = List.app (fn d => mkdir_p (root ++ d)) ["A", "B"]
val _ = write_file (root ++ "holproject.toml")
                   "name = \"projfile_cross_dir_deps\"\n"
val hmf_prefix = "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol --no_overlay\n\
                 \endif\n\n"
val _ = write_file (root ++ "A" ++ "Holmakefile")
                   (hmf_prefix ^ "all: Aa.uo\n.PHONY: all\n")
val _ = write_file (root ++ "B" ++ "Holmakefile")
                   (hmf_prefix ^ "Bb.uo: stamp.txt\n")
val _ = write_file (root ++ "A" ++ "Aa.sml")
                   "structure Aa = struct val x = Bb.y end\n"
val _ = write_file (root ++ "B" ++ "Bb.sml")
                   "structure Bb = struct val y = Bc.z end\n"
val _ = write_file (root ++ "B" ++ "Bc.sml")
                   "structure Bc = struct val z = 1 end\n"
val _ = write_file (root ++ "B" ++ "stamp.txt") "1\n"

val Bb_uo = root ++ "B" ++ "Bb.uo"
val stamp = root ++ "B" ++ "stamp.txt"
val Bc_uo = root ++ "B" ++ "Bc.uo"

val _ = tprint "Clean build of the project, A scanned first"
val _ =
    if hm_ok root (plainopts @ ["--dirs", "B", "A"]) andalso
       isSome (mtime_of (root ++ "A" ++ "Aa.uo")) andalso
       isSome (mtime_of Bb_uo)
    then OK() else fatal "clean build of A and B failed"

(* Post-order: the first root named is scanned last. *)
fun check_deps order =
    let
      val _ = tprint ("B/Bb.uo depends on stamp.txt and Bc.uo (--dirs " ^
                      String.concatWith " " order ^ ")")
      val jsonf = hm_json root (plainopts @ ("--dirs" :: order))
      val deps =
          case List.find (fn (t, _) => t = Bb_uo) (read_deps jsonf) of
              SOME (_, ds) => ds
            | NONE => fatal "no node for B/Bb.uo in the graph"
      val missing =
          List.filter (fn d => not (List.exists (fn d' => d' = d) deps))
                      [stamp, Bc_uo]
    in
      rm_f jsonf;
      if null missing then OK()
      else die ("missing: " ^ String.concatWith ", " missing ^
                "; recorded: " ^ String.concatWith ", " deps)
    end

val _ = check_deps ["B", "A"]
val _ = check_deps ["A", "B"]

fun check_rebuilt what change =
    let
      val _ = tprint ("B/Bb.uo is recompiled when " ^ what ^
                      " changes (A scanned first)")
      val old_mtime = mtime_of Bb_uo
      val _ = sleep_for_mtime ()
      val _ = change ()
      val _ = if hm_ok root (plainopts @ ["--dirs", "B", "A"]) then ()
              else fatal "rebuild failed"
    in
      case (old_mtime, mtime_of Bb_uo) of
          (SOME b, SOME a) =>
          if Time.compare (a, b) = GREATER then OK()
          else die ("B/Bb.uo was not recompiled (mtime still " ^
                    Time.toString b ^ ")")
        | (b, a) => die ("B/Bb.uo missing: before=" ^ mtime_str b ^
                         " after=" ^ mtime_str a)
    end

val _ = check_rebuilt "stamp.txt" (fn () => write_file stamp "2\n")
val _ = check_rebuilt "Bc.sml"
          (fn () => write_file (root ++ "B" ++ "Bc.sml")
                               "structure Bc = struct val z = 2 end\n")

val _ = rm_rf root

val _ = exit_count0 failures
