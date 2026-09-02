(* A foreign target enters the graph as a NoCmd placeholder, and acquires
   its real command only when the directory that owns it is scanned.  For
   a theory product that real command is BIC_BuildScript, which is the
   key `command_map' indexes the node under -- and the key everything
   that treats one script's products as a group looks it up by.

   `updnode_fully' used to replace the node record without moving it in
   that index, so the upgraded node stayed filed under NoCmd.  Its own
   group lookup then returned its siblings and not itself; those siblings
   are decided first, `assign_statuses' filters them out as settled, and
   the node was decided against an empty group -- `hd []', reported as
   `Holmake failed with exception: Empty'.

   The placeholder only appears when the referring directory is scanned
   before the owning one, which under `--dirs' is a matter of the order
   the roots are named.  Building CakeML's compiler/backend/proofs with
   `Holmake --dirs .' hit it after scanning 296 directories. *)

open testutils

infix ++
val op++ = OS.Path.concat

val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

val failures = ref 0
val _ = diemode := Remember failures
fun fatal s : 'a = (die s; OS.Process.exit OS.Process.failure)

fun write_file p contents =
    let val s = TextIO.openOut p
    in TextIO.output (s, contents); TextIO.closeOut s end

fun read_file p =
    let val s = TextIO.openIn p
    in TextIO.inputAll s before TextIO.closeIn s end
    handle IO.Io _ => ""

fun rm_f p = OS.FileSys.remove p handle OS.SysErr _ => ()

fun rm_rf p =
    if OS.FileSys.isDir p handle OS.SysErr _ => false then
      let val ds = OS.FileSys.openDir p
          fun loop () =
              case OS.FileSys.readDir ds of
                  NONE => OS.FileSys.closeDir ds
                | SOME nm => (rm_rf (p ++ nm); loop ())
      in loop (); OS.FileSys.rmDir p handle OS.SysErr _ => () end
    else rm_f p

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

(* Output is captured: while the defect stands these runs die, and the
   failure text is noise until it is quoted into a message. *)
fun hm dir args =
    let
      val out = OS.FileSys.tmpName ()
      val st = in_dir dir (fn () =>
                  Systeml.systeml_out {outfile = out} (Holmake :: args))
      val txt = read_file out
    in
      rm_f out; (st, txt)
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
      if OS.Process.isSuccess st then SOME jsonf
      else (rm_f jsonf; NONE)
    end

(* --- the fixture ---------------------------------------------------- *)

(* A names a product of B's theory script and has no rule for it, so
   whichever of A and B is scanned first enters the other's targets as
   placeholders.  The project's own directories are every directory's
   implicit INCLUDES, so the post-order walk from the first root named
   reaches the other root first: `--dirs B A' is what scans A first. *)
fun mk_project heap_line =
    let
      val root = fresh_dir ()
      val hmf = "ifdef POLY\n" ^ heap_line ^ "endif\n\n"
    in
      List.app (fn d => mkdir_p (root ++ d)) ["A", "B"];
      write_file (root ++ "holproject.toml")
                 "name = \"placeholder_regroup\"\n";
      write_file (root ++ "A" ++ "Holmakefile")
                 (hmf ^ "all: ../B/fooTheory.dat\n.PHONY: all\n");
      write_file (root ++ "B" ++ "Holmakefile")
                 (hmf ^ "all: fooTheory.uo\n.PHONY: all\n");
      write_file (root ++ "B" ++ "fooScript.sml")
                 "Theory foo[bare]\n\
                 \Ancestors bool\n\
                 \Theorem foo_thm = TRUTH\n";
      root
    end

(* ================================================================== *)
(* Part 1: the graph alone.  No heap is needed to build one, so this   *)
(* runs without HOL and is where the crash shows up.                   *)
(* ================================================================== *)

val root1 = mk_project "CLINE_OPTIONS = --poly_not_hol --no_overlay\n"
val graphopts = ["-r", "--nolmbc", "--no_overlay", "--poly_not_hol"]

fun graph_for order =
    (tprint ("Graph builds with --dirs " ^ String.concatWith " " order);
     case hm_json root1 (graphopts @ ["--dirs"] @ order) of
         SOME f => (OK(); SOME f)
       | NONE => (die "Holmake failed to report the graph"; NONE))

val json_AB = graph_for ["A", "B"]
val json_BA = graph_for ["B", "A"]

(* Not dying is the crash regression; agreeing is the point of the
   index.  A node filed under the wrong command is decided outside its
   group, and what a group decides is whether its products are to be
   rebuilt. *)
type gnode = {target : string, needs_rebuild : bool, command : string}

fun read_graph jsonf : gnode list =
    let
      open JSON
      fun fld nm flds =
          case List.find (fn (k, _) => k = nm) flds of
              SOME (_, v) => v
            | NONE => fatal ("--json node has no " ^ nm ^ " field")
      fun str (STRING s) = s
        | str _ = fatal "expected a JSON string"
      fun bool (BOOL b) = b
        | bool _ = fatal "expected a JSON bool"
      fun node (OBJECT flds) =
            {target = str (fld "target" flds),
             needs_rebuild = bool (fld "needs_rebuild" flds),
             command = str (fld "command" flds)}
        | node _ = fatal "expected a JSON object per node"
    in
      case JSONParser.parseFile jsonf of
          ARRAY objs => map node objs
        | _ => fatal "expected a JSON array of nodes"
    end

fun shorten t =
    if String.isPrefix (root1 ^ "/") t then
      String.extract (t, size root1 + 1, NONE)
    else t

fun verdicts jsonf =
    map (fn n : gnode => (shorten (#target n), #needs_rebuild n))
        (read_graph jsonf)

fun diffs s1 s2 =
    let
      fun peek s t = Option.map #2 (List.find (fn (t', _) => t' = t) s)
      fun cmp (t, b) =
          case peek s2 t of
              NONE => SOME (t ^ ": under --dirs A B only")
            | SOME b' =>
              if b = b' then NONE
              else SOME (t ^ ": A B=" ^ Bool.toString b ^
                         ", B A=" ^ Bool.toString b')
      fun missing (t, _) =
          if isSome (peek s1 t) then NONE
          else SOME (t ^ ": under --dirs B A only")
    in
      List.mapPartial cmp s1 @ List.mapPartial missing s2
    end

val _ = tprint "Rebuild decisions agree under both root orders"
val _ =
    case (json_AB, json_BA) of
        (SOME a, SOME b) =>
        (case diffs (verdicts a) (verdicts b) of
             [] => OK()
           | ds => die ("scan order changed the verdict:\n" ^
                        String.concat
                          (map (fn s => "    " ^ s ^ "\n") ds)))
      | _ => die "no graph to compare"

val _ = List.app (fn SOME f => rm_f f | NONE => ()) [json_AB, json_BA]
val _ = rm_rf root1

(* ================================================================== *)
(* Part 2: and the products really are grouped.  Running foo's script  *)
(* writes .sig, .sml and .dat together, and the group is how the build *)
(* marks all three done; the upgraded node was the .dat one.           *)
(* ================================================================== *)

val root2 = mk_project "HOLHEAP = $(HOLDIR)/bin/hol.state0\n"
val buildopts = ["-r", "--nolmbc",
                 "--holstate", Globals.HOLDIR ++ "bin" ++ "hol.state0"]

val _ = tprint "Theory builds with the placeholder order (--dirs B A)"
val (st, txt) = hm root2 (buildopts @ ["--dirs", "B", "A"])
val _ = if OS.Process.isSuccess st then OK()
        else die ("build failed:\n" ^ txt)

val _ = tprint "All of foo's script products are present"
val _ =
    case List.filter
           (fn e => not (HOLFileSys.access (root2 ++ "B" ++
                                            ("fooTheory." ^ e),
                                            [HOLFileSys.A_READ])))
           ["sig", "sml", "dat"] of
        [] => OK()
      | missing => die ("fooTheory." ^ String.concatWith "/" missing ^
                        " not produced")

(* Nothing changed on disk, so a second run has nothing to do.  A .dat
   node left out of its group is not marked done with its siblings,
   which shows up here as a theory that rebuilds every time. *)
val _ = tprint "Nothing is left needing a rebuild"
val _ =
    case hm_json root2 (buildopts @ ["--dirs", "B", "A"]) of
        NONE => die "Holmake failed to report the graph"
      | SOME f =>
        let
          val stale =
              List.filter (fn n : gnode => #needs_rebuild n andalso
                                           #command n <> "")
                          (read_graph f)
        in
          rm_f f;
          if null stale then OK()
          else die ("up to date, yet " ^ Int.toString (length stale) ^
                    " node(s) still need rebuilding:\n" ^
                    String.concat
                      (map (fn n => "    " ^ #target n ^ "\n") stale))
        end

val _ = rm_rf root2

val _ = exit_count0 failures
