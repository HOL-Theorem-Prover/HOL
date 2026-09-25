structure target_times :> target_times =
struct

infix ++
fun p1 ++ p2 = OS.Path.concat (p1, p2)

type map = (string, real) Binarymap.dict

val empty : map = Binarymap.mkDict String.compare

val subdir_a  = ".hol"
val subdir_b  = "build-logs"
val filename  = "target-times"

fun file_for root = root ++ subdir_a ++ subdir_b ++ filename
fun dir_for  root = root ++ subdir_a ++ subdir_b

(* Keys are paths, so a leading `#' marks a comment.  Prose comments
   already fail the two-token match; the test is what stops "# 3"
   parsing as the key "#".  Seeds carry a provenance header. *)
fun parse_line line =
  case String.tokens Char.isSpace line of
      [k, ts] => if String.isPrefix "#" k then NONE
                 else Option.map (fn v => (k, v)) (Real.fromString ts)
    | _ => NONE

fun fold_file path add acc0 =
  let
    val ins = TextIO.openIn path
    fun loop acc =
      case TextIO.inputLine ins of
          NONE => acc
        | SOME line => loop (add (parse_line line, acc))
  in
    loop acc0 before TextIO.closeIn ins
  end

fun cost m k =
    case Binarymap.peek (m, k) of
        NONE => 0.0
      | SOME v => v

fun insert_all (src, m) =
    Binarymap.foldl (fn (k, v, m) => Binarymap.insert (m, k, v)) m src

fun load_from path =
    fold_file path
      (fn (SOME (k, v), m) => Binarymap.insert (m, k, v)
        | (NONE, m) => m)
      empty

fun read path =
    (if HOLFileSys.exists_readable path then load_from path else empty)
    handle IO.Io _ => empty | OS.SysErr _ => empty

(* Seeds first, the project's own cache last, so a locally measured
   value wins: later in the list overwrites earlier. *)
fun load_seeds {seeds, root} =
    let
      val cache = case root of NONE => [] | SOME r => [file_for r]
    in
      List.foldl (fn (p, m) => insert_all (read p, m)) empty (seeds @ cache)
    end

fun load {root} =
    load_seeds {seeds = HMProject.build_times_files root, root = root}

fun warn s =
  (TextIO.output (TextIO.stdErr, "target_times: " ^ s ^ "\n");
   TextIO.flushOut TextIO.stdErr)

fun merge_with root add =
  let
    val outpath = file_for root
    val tmp = outpath ^ ".tmp"
    val () = HOLFileSys.createDirIfNecessary (dir_for root)
    (* The cache alone, never `load': `merge_with' writes back
       everything it reads, so pulling seeds in here would copy them
       into the cache -- laundering seeded values as if this machine
       had measured them, and putting stale keys beyond the reach of a
       regenerated seed. *)
    val m1 = add (read outpath)
    val outs = TextIO.openOut tmp
    (* Fixed-point matches the per-run log format (0.760, not 1E~3);
       both parse via Real.fromString, but FIX keeps the file
       readable at a glance. *)
    fun emit (k, v) =
      TextIO.output (outs, k ^ " " ^
                           Real.fmt (StringCvt.FIX (SOME 3)) v ^ "\n")
    val () = Binarymap.app emit m1
    val () = TextIO.closeOut outs
  in
    OS.FileSys.rename {old = tmp, new = outpath}
  end
  handle IO.Io _ => warn ("could not update " ^ file_for root)
       | OS.SysErr (msg, _) =>
           warn ("could not update " ^ file_for root ^ ": " ^ msg)

fun merge_entries {root, entries} =
    if null entries then ()
    else merge_with root
           (fn m0 => List.foldl
                       (fn ((k, v), m) => Binarymap.insert (m, k, v))
                       m0 entries)

end
