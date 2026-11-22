open testutils
infix ++
val op++ = OS.Path.concat

val cwd = OS.FileSys.getDir()
val fresh = cwd ++ "tmp-root"
val seedpath = cwd ++ "tmp-seed"
val cachepath = fresh ++ ".hol" ++ "build-logs" ++ "target-times"

fun write_file path lines =
  let val outs = TextIO.openOut path
  in List.app (fn s => TextIO.output(outs, s ^ "\n")) lines;
     TextIO.closeOut outs
  end

fun slurp path =
  let val ins = TextIO.openIn path
  in TextIO.inputAll ins before TextIO.closeIn ins end

fun has_key path k =
  List.exists (fn l => String.isPrefix (k ^ " ") l)
              (String.tokens (fn c => c = #"\n") (slurp path))

(* ------------------------------------------------------------------
   load: empty when there is nothing to read
   ------------------------------------------------------------------ *)
val _ = tprint "load with no seeds and no root returns empty map"
val _ = require (check_result (fn m => Binarymap.numItems m = 0))
                target_times.load_seeds {seeds = [], root = NONE}

val _ = tprint "load on a root with no cache returns empty map"
val _ = OS.Process.system ("rm -rf " ^ fresh)   (* clean any leftover *)
val _ = OS.FileSys.mkDir fresh
val _ = require (check_result (fn m => Binarymap.numItems m = 0))
                target_times.load_seeds {seeds = [], root = SOME fresh}

val _ = tprint "load tolerates a seed path that does not exist"
val _ = require (check_result (fn m => Binarymap.numItems m = 0))
                target_times.load_seeds {seeds = [cwd ++ "no-such-seed"],
                                   root = SOME fresh}

(* ------------------------------------------------------------------
   merge_entries: round-trip, upsert, preserve
   ------------------------------------------------------------------ *)
val _ = tprint "merge_entries creates and populates the cache"
val _ = target_times.merge_entries
          {root = fresh, entries = [("src/foo/bar", 1.5),
                                    ("src/foo/baz", 2.75)]}
val m = target_times.load_seeds {seeds = [], root = SOME fresh}
val _ = if Binarymap.numItems m = 2 andalso
           Real.== (target_times.cost m "src/foo/bar", 1.5) andalso
           Real.== (target_times.cost m "src/foo/baz", 2.75)
        then OK() else die "unexpected contents"

val _ = tprint "merge_entries upserts and preserves"
val _ = target_times.merge_entries
          {root = fresh, entries = [("src/foo/bar", 9.0),   (* update *)
                                    ("src/foo/new", 0.5)]}  (* new *)
val m2 = target_times.load_seeds {seeds = [], root = SOME fresh}
val _ = if Binarymap.numItems m2 = 3 andalso
           Real.== (target_times.cost m2 "src/foo/bar", 9.0) andalso
           Real.== (target_times.cost m2 "src/foo/baz", 2.75) andalso
           Real.== (target_times.cost m2 "src/foo/new", 0.5)
        then OK() else die "upsert or preservation failed"

val _ = tprint "cost of an unknown key is 0.0"
val _ = if Real.== (target_times.cost m2 "src/foo/absent", 0.0) then OK()
        else die "unknown key did not score 0.0"

(* ------------------------------------------------------------------
   seeds: consulted, but always beaten by the cache
   ------------------------------------------------------------------ *)
val _ = write_file seedpath
          ["# a comment line, skipped",
           "#  3",                        (* would parse as key "#" *)
           "src/foo/bar 100.0",           (* also in the cache *)
           "src/seeded/only 42.0",        (* seed-only *)
           "malformed line without a number",
           ""]

val _ = tprint "a seed supplies keys the cache does not have"
val ms = target_times.load_seeds {seeds = [seedpath], root = SOME fresh}
val _ = if Real.== (target_times.cost ms "src/seeded/only", 42.0) then OK()
        else die "seed-only key not found"

val _ = tprint "the cache beats the seed for a shared key"
val _ = if Real.== (target_times.cost ms "src/foo/bar", 9.0) then OK()
        else die "seed overrode a locally measured value"

val _ = tprint "comment and malformed lines are skipped"
val _ = if Binarymap.numItems ms = 4 andalso
           Real.== (target_times.cost ms "#", 0.0)
        then OK() else die "a comment or malformed line was parsed"

(* ------------------------------------------------------------------
   The seed is never written back into the cache.  See `merge_with' in
   poly/target_times.sml for why that matters.
   ------------------------------------------------------------------ *)
val _ = tprint "merge_entries does not write seed entries to the cache"
val _ = target_times.merge_entries
          {root = fresh, entries = [("src/foo/later", 1.0)]}
val _ = if has_key cachepath "src/foo/later" andalso
           not (has_key cachepath "src/seeded/only")
        then OK() else die "a seed entry reached the cache"

val _ = tprint "a later load still sees the seed"
val ms2 = target_times.load_seeds {seeds = [seedpath], root = SOME fresh}
val _ = if Real.== (target_times.cost ms2 "src/seeded/only", 42.0) andalso
           Real.== (target_times.cost ms2 "src/foo/later", 1.0)
        then OK() else die "seed or cache lost after merge"

(* `load' itself finds a project's seed at the default path, which is
   what wires HMProject's lookup to the scheduler.  Asserted by key
   rather than by count: HOL may ship a seed of its own, and this test
   runs inside HOLDIR. *)
val _ = tprint "load finds <root>/build-times without being told"
val _ = write_file (fresh ++ "build-times") ["src/defaulted/seed 7.5"]
val md = target_times.load {root = SOME fresh}
val _ = if Real.== (target_times.cost md "src/defaulted/seed", 7.5) andalso
           Real.== (target_times.cost md "src/foo/bar", 9.0)
        then OK() else die "default seed path not consulted"

(* ------------------------------------------------------------------
   rel_to_root: the key space itself
   ------------------------------------------------------------------ *)
val H = Systeml.HOLDIR
fun rel r p = Holmake_tools.rel_to_root {root = r} p

val _ = tprint "rel_to_root: under the project root"
val _ = if rel (SOME "/p/cake") "/p/cake/basis/basis" = "basis/basis"
        then OK() else die "not made relative to the root"

val _ = tprint "rel_to_root: root = HOLDIR leaves HOL keys bare"
val _ = if rel (SOME H) (H ++ "src/list/src/list") = "src/list/src/list"
        then OK() else die "HOL key did not stay bare"

val _ = tprint "rel_to_root: no root falls back to HOLDIR"
val _ = if rel NONE (H ++ "src/list/src/list") = "src/list/src/list"
        then OK() else die "NONE root did not fall back to HOLDIR"

val _ = tprint "rel_to_root: HOL paths under a foreign root get $(HOLDIR)/"
val _ = if rel (SOME "/p/cake") (H ++ "examples/foo/bar") =
           "$(HOLDIR)/examples/foo/bar"
        then OK() else die "missing $(HOLDIR)/ prefix"

val _ = tprint "rel_to_root: a foreign key cannot collide with a HOL one"
val _ = if rel (SOME "/p/cake") "/p/cake/examples/foo/bar" <>
           rel (SOME "/p/cake") (H ++ "examples/foo/bar")
        then OK() else die "collision between project and HOL keys"

val _ = tprint "rel_to_root: outside both stays absolute"
val _ = if rel (SOME "/p/cake") "/elsewhere/x/y" = "/elsewhere/x/y"
        then OK() else die "unrelated path was rewritten"

(* ------------------------------------------------------------------
   merge_entries is last-wins within one call, so a caller that times a
   key twice must combine the two itself.
   ------------------------------------------------------------------ *)
val _ = tprint "a repeated key in one call keeps the later pair"
val _ = OS.Process.system ("rm -rf " ^ fresh)
val _ = OS.FileSys.mkDir fresh
val _ = target_times.merge_entries
          {root = fresh, entries = [("src/dup/tgt", 1.0),
                                    ("src/dup/tgt", 4.0)]}
val mdup = target_times.load_seeds {seeds = [], root = SOME fresh}
val _ = if Real.== (target_times.cost mdup "src/dup/tgt", 4.0) then OK()
        else die "a repeated key did not resolve to the later pair"

(* ------------------------------------------------------------------
   End to end: a recipe of several command lines is one job per line,
   and all of those jobs share the node's cost key, so the node's
   recorded cost has to be their sum.  Recording a single one of them
   instead silently understates every multi-command recipe in the tree
   -- `src/HolRefute/theory-tests', whose first line is a cheap
   `Holmake -C theory_tests clean', was logged at a few hundredths of a
   second while the build it drives ran for a minute.

   multiline/ builds `twoline' (cheap line then dear line) and
   `oneline' (the same total work in one line) and the two recorded
   costs are compared to each other, never to a wall-clock figure, so
   the test says the same thing on any machine.  Keeping only
   `twoline's first line puts the ratio at about 1/10.
   ------------------------------------------------------------------ *)
val Holmake = Systeml.HOLDIR ++ "bin" ++ "Holmake"
val mldir = cwd ++ "multiline"
val mlhol = mldir ++ ".hol"
val mlcache = mlhol ++ "build-logs" ++ "target-times"

fun value_of path k =
  let
    fun get [] = NONE
      | get (l :: rest) =
          (case String.tokens Char.isSpace l of
               [k', v] => if k' = k then Real.fromString v else get rest
             | _ => get rest)
  in
    get (String.tokens (fn c => c = #"\n") (slurp path))
  end

val _ = tprint "every command line of a recipe is counted"
val _ = OS.Process.system ("rm -rf " ^ mlhol)
val mlres =
    Systeml.systeml [Holmake, "-C", mldir, "-j", "2", "all"]
val _ =
    if not (OS.Process.isSuccess mlres) then die "multiline build failed"
    else
      case (value_of mlcache "twoline", value_of mlcache "oneline") of
          (NONE, _) => die "no cost recorded for twoline"
        | (_, NONE) => die "no cost recorded for oneline"
        | (SOME two, SOME one) =>
          (* A machine fast enough to put `oneline' under the clock's
             resolution would make the ratio meaningless rather than
             false; say so rather than passing by luck. *)
          if one < 0.05 then
            die ("oneline too cheap to compare: " ^ Real.toString one)
          else if two >= 0.5 * one then OK()
          else die ("twoline " ^ Real.toString two ^ " vs oneline " ^
                    Real.toString one ^ ": a command line went unrecorded")

(* ------------------------------------------------------------------
   A job's cost is its user time *and* its system time.  `times'
   reports the two separately and only `cutime' used to be read, which
   hid everything a child spends in the kernel -- heap mapping, page
   faults, I/O -- and made a target that mostly does I/O look free.

   systime/ runs one syscall-bound recipe that measures itself with the
   shell's own `times' builtin, so Holmake's figure is compared against
   another measurement of the same work rather than against a
   wall-clock number.  The recipe's sed and awk run after it takes that
   reading, so self-measured sits a little *under* what Holmake sees;
   the lower bound allows for it.  Counting user time alone put the
   ratio at about 0.3.
   ------------------------------------------------------------------ *)
val stdir = cwd ++ "systime"
val sthol = stdir ++ ".hol"
val stcache = sthol ++ "build-logs" ++ "target-times"

val _ = tprint "a job's system time is counted"
val _ = OS.Process.system ("rm -rf " ^ sthol)
val stres = Systeml.systeml [Holmake, "-C", stdir, "all"]
val _ =
    if not (OS.Process.isSuccess stres) then die "systime build failed"
    else
      let
        val self = Real.fromString (slurp (stdir ++ "self-measured"))
      in
        case (value_of stcache "syswork", self) of
            (NONE, _) => die "no cost recorded for syswork"
          | (_, NONE) => die "recipe did not report its own cost"
          | (SOME recorded, SOME measured) =>
            (* Too fast to see is a meaningless ratio, not a false one. *)
            if measured < 0.1 then
              die ("syswork too cheap to compare: " ^ Real.toString measured)
            else if recorded >= 0.8 * measured andalso
                    recorded <= 2.0 * measured
            then OK()
            else die ("recorded " ^ Real.toString recorded ^
                      " against a self-measured " ^ Real.toString measured ^
                      ": system time is being dropped")
      end

(* ------------------------------------------------------------------
   Concurrent jobs are billed separately.  `times' counts waited-for
   children only, so a child still running contributes nothing to it,
   and reaping exactly one child and differencing across that `waitpid'
   bills that child alone.  Nothing in the types keeps reaping and
   billing in step: batch the reaps, or reap without re-stamping the
   watermark, and whichever job exits next silently picks up its
   neighbours' work.

   concurrent/ runs 1:2:4:8 rounds of the same work under `-j 4'.  The
   assertion is on the spread between the recorded costs, never on a
   wall-clock figure, and the bands are wide because a loaded machine
   inflates a long job more than a short one.  Billing the neighbours'
   work too would pull the cheap jobs up towards the dear ones and
   collapse that spread.
   ------------------------------------------------------------------ *)
val cdir = cwd ++ "concurrent"
val chol = cdir ++ ".hol"
val ccache = chol ++ "build-logs" ++ "target-times"

val _ = tprint "concurrent jobs are costed separately"
val _ = OS.Process.system ("rm -rf " ^ chol)
val cres = Systeml.systeml [Holmake, "-C", cdir, "-j", "4", "all"]
val _ =
    if not (OS.Process.isSuccess cres) then die "concurrent build failed"
    else
      case (value_of ccache "one", value_of ccache "two",
            value_of ccache "four", value_of ccache "eight") of
          (SOME one, SOME two, SOME four, SOME eight) =>
          if one < 0.05 then
            die ("one too cheap to compare: " ^ Real.toString one)
          else
            let
              fun within (lo, hi) r = lo <= r andalso r <= hi
              val rs = [(two / one, (1.2, 4.0), "two"),
                        (four / one, (2.0, 8.0), "four"),
                        (eight / one, (4.0, 16.0), "eight")]
            in
              case List.find (fn (r, band, _) => not (within band r)) rs of
                  NONE => OK()
                | SOME (r, _, nm) =>
                  die (nm ^ "/one = " ^ Real.toString r ^
                       ": jobs are not being costed separately")
            end
        | _ => die "a target went uncosted"

(* ------------------------------------------------------------------
   Cleanup
   ------------------------------------------------------------------ *)
val _ = OS.Process.system ("rm -rf " ^ fresh)
val _ = OS.Process.system ("rm -rf " ^ mlhol)
val _ = OS.Process.system ("rm -rf " ^ sthol)
val _ = OS.Process.system ("rm -rf " ^ chol)
val _ = OS.FileSys.remove seedpath
