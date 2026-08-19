(* Holmake's staleness decision must not depend on the order in which
   directories happen to be scanned.

   `build_depgraph' fixes each node's status while walking directories,
   from the dependency statuses as they stand at that moment.  A
   cross-directory target that no rule claims is entered as a
   placeholder judged on bare file existence; when the directory that
   owns it is scanned later the placeholder is upgraded to Pending, but
   nodes already decided against it are never revisited.  A consumer
   scanned before its producer therefore freezes as Succeeded while a
   dependency of it is still Pending.

   In project mode that scan order is ordinary rather than unlucky:
   every directory's implicit INCLUDES are the whole project, so the
   order is alphabetical over the project's directories and has nothing
   to do with dependency order.  (With explicit INCLUDES the recursion
   reaches the producer first, which is why this stays hidden there.)

   Part 1 uses two directories of plain SML, and reads the graph for one
   on-disk state under both root orders.  Part 2 reproduces the
   theory-level failure from the state a killed script job leaves behind
   -- .uo/.ui present, .sig/.sml/.dat gone.

   Each project is built under its own temp directory: these are
   project-mode builds, and a fixture inside the HOL tree would be a
   nested project of the tree's own holproject.toml. *)

open testutils

infix ++
val op++ = OS.Path.concat

val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

(* Every property below is checked independently: a frozen node in one
   scan order says nothing about the others, and seeing all of them at
   once is the point.  So `die' records and continues, and the exit
   status comes from the tally at the end.  `fatal' is for the setup
   steps, where continuing would only produce noise. *)
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

(* Output is captured rather than shown: these runs are expected to fail
   while the defect stands, and the failure text is noisy. *)
fun hm dir args =
    let
      val out = OS.FileSys.tmpName ()
      val st = in_dir dir (fn () =>
                  Systeml.systeml_out {outfile = out} (Holmake :: args))
      val txt = read_file out
    in
      rm_f out; (st, txt)
    end

fun hm_ok dir args = OS.Process.isSuccess (#1 (hm dir args))

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

(* Theory products and .uo/.ui live under .hol/objs, so mtimes go
   through HOLFileSys rather than OS.FileSys. *)
fun mtime_of f =
    if HOLFileSys.access (f, [HOLFileSys.A_READ]) then
      SOME (HOLFileSys.modTime f)
    else NONE

fun mtime_str NONE = "<missing>"
  | mtime_str (SOME t) = Time.toString t

(* Coarse filesystems can give two events the same mtime; sleep so a
   following write is strictly newer. *)
fun sleep_for_mtime () = OS.Process.sleep (Time.fromMilliseconds 1100)

(* --- the dependency graph, as Holmake reports it -------------------- *)

type gnode = {target : string, phony : bool, needs_rebuild : bool,
              command : string, dependencies : int list}

fun read_graph jsonf : (int * gnode) list =
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
      fun int (INT i) = IntInf.toInt i
        | int _ = fatal "expected a JSON int"
      fun node (OBJECT flds) =
          (int (fld "node_id" flds),
           {target = str (fld "target" flds),
            phony = bool (fld "phony" flds),
            needs_rebuild = bool (fld "needs_rebuild" flds),
            command = str (fld "command" flds),
            dependencies =
              case fld "dependencies" flds of
                  ARRAY ds => map int ds
                | _ => fatal "expected a JSON array of dependencies"})
        | node _ = fatal "expected a JSON object per node"
    in
      case JSONParser.parseFile jsonf of
          ARRAY objs => map node objs
        | _ => fatal "expected a JSON array of nodes"
    end

fun lookup g i =
    case List.find (fn (j, _) => i = j) g of
        SOME (_, n) => n
      | NONE => fatal ("--json refers to absent node " ^ Int.toString i)

(* Report targets relative to the project root, so messages stay
   readable. *)
fun shorten root t =
    if String.isPrefix (root ^ "/") t then
      String.extract (t, size root + 1, NONE)
    else t

(* The invariant the graph walk breaks: a node that will not be rebuilt
   must not depend on one that will.  Phony and command-less nodes are
   exempt -- nothing runs for them, so nothing can read a half-written
   file through them. *)
fun invariant_violations root g =
    let
      fun frozen (_, n : gnode) =
          not (#phony n) andalso #command n <> "" andalso
          not (#needs_rebuild n)
      fun pending_edges (n : gnode) =
          List.mapPartial
            (fn i => let val d = lookup g i
                     in
                       if #needs_rebuild d then
                         SOME (shorten root (#target n),
                               shorten root (#target d))
                       else NONE
                     end)
            (#dependencies n)
    in
      List.concat (map (pending_edges o #2) (List.filter frozen g))
    end

fun check_invariant root what jsonf =
    case invariant_violations root (read_graph jsonf) of
        [] => OK()
      | vs => die (what ^ ": " ^ Int.toString (length vs) ^
                   " node(s) will not be rebuilt but depend on one that \
                   \will:\n" ^
                   String.concat
                     (map (fn (a, b) => "    " ^ a ^ " <- " ^ b ^ "\n") vs))

(* target |-> needs_rebuild, for comparing two scan orders *)
fun rebuild_set root g =
    map (fn (_, n : gnode) => (shorten root (#target n), #needs_rebuild n)) g

(* Differences between two such maps, each labelled by the scan order it
   came from. *)
fun verdict_diffs (l1, s1) (l2, s2) =
    let
      fun peek s t = Option.map #2 (List.find (fn (t', _) => t' = t) s)
      fun cmp (t, b) =
          case peek s2 t of
              NONE => SOME (t ^ ": present under " ^ l1 ^ " only")
            | SOME b' =>
              if b = b' then NONE
              else SOME (t ^ ": " ^ l1 ^ "=" ^ Bool.toString b ^ ", " ^
                         l2 ^ "=" ^ Bool.toString b')
      fun missing (t, _) =
          if isSome (peek s1 t) then NONE
          else SOME (t ^ ": present under " ^ l2 ^ " only")
    in
      List.mapPartial cmp s1 @ List.mapPartial missing s2
    end

(* ================================================================== *)
(* Part 1: plain SML compile products.                                *)
(*                                                                    *)
(* A/Aa.sml refers to B's structure, so A/Aa.uo depends on ../B/Bb.uo, *)
(* a target no rule claims.  Whichever of A and B is scanned first     *)
(* sees the other's products as bare files on disk.                    *)
(* ================================================================== *)

val plainopts = ["-r", "--nolmbc", "--no_overlay", "--poly_not_hol"]

val root1 = fresh_dir ()
val _ = List.app (fn d => mkdir_p (root1 ++ d)) ["A", "B"]
val _ = write_file (root1 ++ "holproject.toml")
                   "name = \"scan_order_staleness_plain\"\n"
val hmf_prefix = "ifdef POLY\nCLINE_OPTIONS = --poly_not_hol --no_overlay\n\
                 \endif\n\n"
val _ = write_file (root1 ++ "A" ++ "Holmakefile")
                   (hmf_prefix ^ "all: Aa.uo\n.PHONY: all\n")
val _ = write_file (root1 ++ "B" ++ "Holmakefile")
                   (hmf_prefix ^ "all: Bb.uo\n.PHONY: all\n")
val _ = write_file (root1 ++ "A" ++ "Aa.sml")
                   "structure Aa = struct val x = Bb.y end\n"
val _ = write_file (root1 ++ "B" ++ "Bb.sml")
                   "structure Bb = struct val y = 1 end\n"

val Aa_uo = root1 ++ "A" ++ "Aa.uo"

val _ = tprint "Plain: clean build of both directories"
val _ =
    if hm_ok (root1 ++ "A") plainopts andalso
       isSome (mtime_of Aa_uo) andalso
       isSome (mtime_of (root1 ++ "B" ++ "Bb.uo"))
    then OK() else fatal "clean build of A and B failed"

(* One edit to B, then read the graph under both root orders without
   building in between: --json only reports, so both dumps describe the
   very same on-disk state.  Post-order means the first root named is
   scanned last, so --dirs B A is what scans A first. *)
val _ = sleep_for_mtime ()
val _ = write_file (root1 ++ "B" ++ "Bb.sml")
                   "structure Bb = struct val y = 2 end\n"

val json_AB = hm_json root1 (plainopts @ ["--dirs", "A", "B"])
val json_BA = hm_json root1 (plainopts @ ["--dirs", "B", "A"])

val _ = tprint "Plain: rebuild decision is the same under both root orders"
fun verdicts jsonf = rebuild_set root1 (read_graph jsonf)
val _ =
    case verdict_diffs ("--dirs A B", verdicts json_AB)
                       ("--dirs B A", verdicts json_BA) of
        [] => OK()
      | ds => die ("scan order changed the verdict:\n" ^
                   String.concat (map (fn s => "    " ^ s ^ "\n") ds))

val _ = tprint "Plain: no frozen node over a pending dependency (--dirs A B)"
val _ = check_invariant root1 "--dirs A B" json_AB

val _ = tprint "Plain: no frozen node over a pending dependency (--dirs B A)"
val _ = check_invariant root1 "--dirs B A" json_BA

val _ = List.app rm_f [json_AB, json_BA]

(* And the consequence: under the order that freezes A, the consumer is
   never recompiled, and Holmake reports success. *)
val _ = tprint "Plain: consumer is recompiled when its producer changes"
val aa_before = mtime_of Aa_uo
val _ = if hm_ok root1 (plainopts @ ["--dirs", "B", "A"]) then ()
        else fatal "build under --dirs B A failed"
val _ =
    case (aa_before, mtime_of Aa_uo) of
        (SOME b, SOME a) =>
        if Time.compare (a, b) = GREATER then OK()
        else die ("A/Aa.uo was not recompiled (mtime still " ^
                  Time.toString b ^ ")")
      | (b, a) => die ("A/Aa.uo missing: before=" ^ mtime_str b ^
                       " after=" ^ mtime_str a)

val _ = rm_rf root1

(* ================================================================== *)
(* Part 2: theory products.                                           *)
(*                                                                    *)
(* base (in B) <- mid (in A) <- top (in C).  A sorts before B, so A is *)
(* scanned first and freezes against B's products; top is then         *)
(* runnable at once and loads through the frozen mid into a base that  *)
(* B's script is concurrently rebuilding.                             *)
(* ================================================================== *)

val root2 = fresh_dir ()
val _ = List.app (fn d => mkdir_p (root2 ++ d)) ["A", "B", "C"]
val _ = write_file (root2 ++ "holproject.toml")
                   "name = \"scan_order_staleness_theories\"\n"
val _ = List.app
          (fn d => write_file (root2 ++ d ++ "Holmakefile")
              "ifdef POLY\nHOLHEAP = $(HOLDIR)/bin/hol.state0\nendif\n")
          ["A", "B", "C"]
val _ = write_file (root2 ++ "A" ++ "midScript.sml")
                   "Theory mid[bare]\n\
                   \Ancestors base\n\
                   \Theorem mid_thm = base_thm\n"
(* The delay makes the window deterministic: without it, whether top
   reads base's products before or after the rebuild has replaced them
   is a coin toss. *)
val _ = write_file (root2 ++ "B" ++ "baseScript.sml")
                   "Theory base[bare]\n\
                   \Ancestors bool\n\
                   \val _ = OS.Process.sleep (Time.fromSeconds 3)\n\
                   \Theorem base_thm = TRUTH\n"
val _ = write_file (root2 ++ "C" ++ "topScript.sml")
                   "Theory top[bare]\n\
                   \Ancestors mid\n\
                   \Theorem top_thm = mid_thm\n"

val thyopts = ["-r", "--nolmbc",
               "--holstate", Globals.HOLDIR ++ "bin" ++ "hol.state0"]

fun dat d thy = root2 ++ d ++ (thy ^ "Theory.dat")

(* Reproduce the state a script job killed mid-rebuild leaves behind:
   base's compile products survive, its own files are gone, and top has
   an independent reason to rebuild.

   Bringing the project up to date first is not ceremony.  A scenario
   that has already run leaves mid older than base's products, and a mid
   that stale would be rebuilt for ordinary mtime reasons -- never
   freezing, and quietly costing the next scenario its precondition. *)
fun to_aborted_job_state () =
    (if hm_ok (root2 ++ "C") thyopts then ()
     else fatal "could not bring the project up to date";
     sleep_for_mtime ();
     List.app (fn e => HOLFileSys.remove (root2 ++ "B" ++
                                          ("baseTheory." ^ e))
                       handle _ => ())
              ["sig", "sml", "dat"];
     OS.FileSys.setTime (root2 ++ "C" ++ "topScript.sml", NONE))

val _ = tprint "Theories: clean build of base, mid and top"
val _ = if hm_ok (root2 ++ "C") thyopts andalso
           isSome (mtime_of (dat "B" "base")) andalso
           isSome (mtime_of (dat "A" "mid")) andalso
           isSome (mtime_of (dat "C" "top"))
        then OK() else fatal "clean build of base, mid and top failed"

val _ = to_aborted_job_state ()

val _ = tprint "Theories: no frozen node over a pending dependency"
val json2 = hm_json (root2 ++ "C") thyopts
val _ = check_invariant root2 "aborted-job state" json2
val _ = rm_f json2

(* Sequentially the defect is quiet: every job reads complete files, so
   the build succeeds having simply not rebuilt mid, leaving it older
   than the ancestor it was built against. *)
val _ = tprint "Theories: -j1 rebuilds mid after its ancestor base"
val _ = if hm_ok (root2 ++ "C") (thyopts @ ["-j1"]) then ()
        else die "sequential build failed"
val _ =
    case (mtime_of (dat "B" "base"), mtime_of (dat "A" "mid")) of
        (SOME b, SOME m) =>
        if Time.compare (m, b) = GREATER then OK()
        else die ("midTheory.dat (" ^ Time.toString m ^
                  ") is older than baseTheory.dat (" ^ Time.toString b ^
                  "): mid was not rebuilt")
      | (b, m) => die ("missing .dat: base=" ^ mtime_str b ^
                       " mid=" ^ mtime_str m)

(* In parallel it is loud: top is dispatched alongside base's rebuild
   and loads a theory whose files have just been removed. *)
val _ = to_aborted_job_state ()

val _ = tprint "Theories: -j4 does not read a theory being rebuilt"
val (st2, txt2) = hm (root2 ++ "C") (thyopts @ ["-j4"])
val _ = if OS.Process.isSuccess st2 then OK()
        else die ("parallel build aborted:\n" ^ txt2)

val _ = rm_rf root2

val _ = exit_count0 failures
