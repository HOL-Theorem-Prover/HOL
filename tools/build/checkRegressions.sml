(* ======================================================================
   Compare a freshly-completed build log against the median per-theory
   time across the most recent prior runs and print a summary if any
   individual theory or the total wall time has grown past conservative
   thresholds.  Intended to be invoked from buildutils.finish_logging on
   a successful build.
   ====================================================================== *)
structure checkRegressions :> checkRegressions =
struct

(* Number of prior log files used to form the baseline. *)
val baseline_window = 3

(* A per-key regression must clear BOTH thresholds. *)
val abs_threshold = 1.0     (* seconds                    *)
val rel_threshold = 1.20    (* new time as ratio over old *)

(* The total-time check uses its own (looser) thresholds. *)
val total_abs_threshold = 30.0
val total_rel_threshold = 1.05

(* If the median age of the baseline files exceeds this, prepend a
   note to the report so the reader can discount accordingly. *)
val staleness_days = 7

(* ---------------------------------------------------------------------- *)
(* Reading logs                                                            *)
(* ---------------------------------------------------------------------- *)

(* Read one log file as a Binarymap.  Duplicate keys are dropped, matching
   the convention used by comparelogs - an entry that appears more than
   once in a single log is ambiguous about which time to trust. *)
fun read_log fname =
  let
    val instr = TextIO.openIn fname
    fun add (k, v, (acc, dups)) =
      if Binaryset.member (dups, k) then (acc, dups)
      else
        case Binarymap.peek (acc, k) of
            NONE => (Binarymap.insert (acc, k, v), dups)
          | SOME _ =>
              (#1 (Binarymap.remove (acc, k)), Binaryset.add (dups, k))
    fun loop acc =
      case TextIO.inputLine instr of
          NONE => acc
        | SOME line =>
            (case String.tokens Char.isSpace line of
                 [k, ts] => (case Real.fromString ts of
                                 SOME v => loop (add (k, v, acc))
                               | NONE => loop acc)
               | _ => loop acc)
    val empty = (Binarymap.mkDict String.compare,
                 Binaryset.empty String.compare)
  in
    #1 (loop empty) before TextIO.closeIn instr
  end handle _ => Binarymap.mkDict String.compare

(* ---------------------------------------------------------------------- *)
(* Picking prior logs                                                      *)
(* ---------------------------------------------------------------------- *)

fun same_path (p, q) =
  let val canon = OS.Path.mkCanonical
  in canon p = canon q end

(* Up to N most-recently-modified ordinary files in `logdir`, excluding
   `latest`.  Returned newest-first as (path, mtime) pairs. *)
fun prior_logs {logdir, latest, n} =
  let
    open OS.FileSys
    val dstrm = openDir logdir
    fun harvest acc =
      case readDir dstrm of
          NONE => acc
        | SOME f =>
            let
              val full = OS.Path.concat (logdir, f)
            in
              if same_path (full, latest) then harvest acc
              else if not (access (full, [A_READ])) orelse isDir full
                then harvest acc
                else harvest ((full, modTime full) :: acc)
            end
    val all = harvest [] before closeDir dstrm
    val sorted = Listsort.sort
                   (fn ((_,a), (_,b)) => Time.compare (b, a)) all
  in
    List.take (sorted, Int.min (length sorted, n))
  end handle _ => []

(* ---------------------------------------------------------------------- *)
(* Median + per-key baseline                                               *)
(* ---------------------------------------------------------------------- *)

fun median xs =
  case xs of
      [] => NONE
    | _ =>
        let
          val sorted = Listsort.sort Real.compare xs
          val n = length sorted
          val mid = n div 2
        in
          SOME (if n mod 2 = 1 then List.nth (sorted, mid)
                else (List.nth (sorted, mid - 1) +
                      List.nth (sorted, mid)) / 2.0)
        end

(* Per-key median across a list of single-log maps. *)
fun per_key_medians maps =
  let
    val gathered =
        List.foldl
          (fn (m, acc) =>
             Binarymap.foldl
               (fn (k, v, a) =>
                  let val cur = case Binarymap.peek (a, k) of
                                    NONE => []
                                  | SOME xs => xs
                  in Binarymap.insert (a, k, v :: cur) end)
               acc m)
          (Binarymap.mkDict String.compare) maps
  in
    Binarymap.foldl
      (fn (k, vs, a) =>
         case median vs of
             SOME m => Binarymap.insert (a, k, m)
           | NONE => a)
      (Binarymap.mkDict String.compare) gathered
  end

(* ---------------------------------------------------------------------- *)
(* Threshold checks                                                        *)
(* ---------------------------------------------------------------------- *)

(* (key, baseline, new, delta, ratio), descending by delta. *)
fun per_key_regressions {baseline, current} =
  let
    val regs =
        Binarymap.foldl
          (fn (k, new, acc) =>
             case Binarymap.peek (baseline, k) of
                 NONE => acc
               | SOME old =>
                   let
                     val delta = new - old
                     val ratio = if old > 0.0 then new / old else 1.0
                   in
                     if delta > abs_threshold andalso
                        ratio > rel_threshold
                     then (k, old, new, delta, ratio) :: acc
                     else acc
                   end)
          [] current
  in
    Listsort.sort
      (fn ((_,_,_,d1,_), (_,_,_,d2,_)) => Real.compare (d2, d1)) regs
  end

(* Sum across keys present in BOTH baseline and current; report iff
   the total-time thresholds are also exceeded. *)
fun total_regression {baseline, current} =
  let
    val (sum_old, sum_new) =
        Binarymap.foldl
          (fn (k, new, (so, sn)) =>
             case Binarymap.peek (baseline, k) of
                 SOME old => (so + old, sn + new)
               | NONE => (so, sn))
          (0.0, 0.0) current
    val delta = sum_new - sum_old
    val ratio = if sum_old > 0.0 then sum_new / sum_old else 1.0
  in
    if delta > total_abs_threshold andalso
       ratio > total_rel_threshold
    then SOME (sum_old, sum_new, delta, ratio)
    else NONE
  end

(* ---------------------------------------------------------------------- *)
(* Output                                                                  *)
(* ---------------------------------------------------------------------- *)

fun median_age_days mtimes =
  let
    val now = Time.now ()
    val ages = List.map
                 (fn t => Time.toReal (Time.- (now, t)) / 86400.0) mtimes
  in
    median ages
  end

fun fmt2 r = Real.fmt (StringCvt.FIX (SOME 2)) r
fun fmt_pct r = fmt2 ((r - 1.0) * 100.0) ^ "%"

fun report_regressions regs =
  List.app
    (fn (k, old, new, delta, ratio) =>
        print ("  " ^ k ^ ": " ^ fmt2 old ^ "s -> " ^ fmt2 new ^
               "s (+" ^ fmt2 delta ^ "s, +" ^ fmt_pct ratio ^ ")\n"))
    regs

fun report_total NONE = ()
  | report_total (SOME (sum_old, sum_new, delta, ratio)) =
      print ("  Total wall time: " ^ fmt2 sum_old ^ "s -> " ^
             fmt2 sum_new ^ "s (+" ^ fmt2 delta ^ "s, +" ^
             fmt_pct ratio ^ ")\n")

fun run {logdir, latest} =
  let
    val priors = prior_logs {logdir = logdir, latest = latest,
                             n = baseline_window}
  in
    if null priors then ()
    else
      let
        val current = read_log latest
        val baseline_maps = List.map (read_log o #1) priors
        val baseline = per_key_medians baseline_maps
        val regs = per_key_regressions
                     {baseline = baseline, current = current}
        val total = total_regression
                      {baseline = baseline, current = current}
      in
        if null regs andalso not (Option.isSome total) then ()
        else
          let
            val mtimes = List.map #2 priors
            val age = median_age_days mtimes
            val stale_note =
                case age of
                    SOME d => if d > Real.fromInt staleness_days then
                                "; baseline median age " ^ fmt2 d ^
                                " days"
                              else ""
                  | NONE => ""
          in
            print ("\nPossible time regressions vs. median of last " ^
                   Int.toString (length priors) ^ " run(s)" ^
                   stale_note ^ ":\n");
            report_regressions regs;
            report_total total
          end
      end
  end handle _ => ()

end (* structure checkRegressions *)
