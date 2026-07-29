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

fun parse_line line =
  case String.tokens Char.isSpace line of
      [k, ts] => Option.map (fn v => (k, v)) (Real.fromString ts)
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

fun theory_cost m fp =
    case Binarymap.peek (m, Holmake_tools.rel_to_holdir fp) of
        NONE => 0.0
      | SOME v => v

fun load_from path =
    fold_file path
      (fn (SOME (k, v), m) => Binarymap.insert (m, k, v)
        | (NONE, m) => m)
      empty

fun load {root = NONE} = empty
  | load {root = SOME r} =
    let val path = file_for r
    in if HOLFileSys.exists_readable path then load_from path else empty
    end handle IO.Io _ => empty | OS.SysErr _ => empty

fun warn s =
  (TextIO.output (TextIO.stdErr, "target_times: " ^ s ^ "\n");
   TextIO.flushOut TextIO.stdErr)

fun merge_from_log {root, log_path} =
  let
    val outpath = file_for root
    val tmp = outpath ^ ".tmp"
    val () = HOLFileSys.createDirIfNecessary (dir_for root)
    val m0 = load {root = SOME root}
    val m1 =
      if HOLFileSys.exists_readable log_path then
        fold_file log_path
          (fn (SOME (k, v), m) => Binarymap.insert (m, k, v)
            | (NONE, m) => m)
          m0
      else m0
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

end
