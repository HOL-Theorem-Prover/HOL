structure corpus_diff =
struct

fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
fun die s = (warn s; OS.Process.exit OS.Process.failure)
fun pr s  = TextIO.output(TextIO.stdOut, s)

(* SHA1 via /usr/bin/shasum, matching src/portableML/poly/SHA1-byexec.ML so
   the emitted hashes match HOL's export_theory_return_hash byte-for-byte.
   Route through sh so shasum's stderr can be silenced without contaminating
   the parent's stderr (shasum emits harmless perl locale warnings on some
   systems). *)
fun sh_quote s =
    "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"

fun sha1_file filename =
    let val cmd = "/usr/bin/shasum " ^ sh_quote filename ^ " 2>/dev/null"
        val proc = Unix.execute("/bin/sh", ["-c", cmd])
        val line = TextIO.inputLine (Unix.textInstreamOf proc)
        val _ = Unix.reap proc
    in
      case line of
          NONE => die ("shasum on " ^ filename ^ " produced no output")
        | SOME s =>
          case String.tokens Char.isSpace s of
              h :: _ => h
            | [] => die ("shasum on " ^ filename ^ " produced empty line")
    end

(* Walk from root, collect .hol/objs/*Theory.dat paths.  A .hol directory is
   visited only for its objs/ subdirectory; other dotted names are skipped. *)
fun walk root =
    let
      fun list_dats objsdir acc =
          let val ds = OS.FileSys.openDir objsdir
              fun loop acc =
                  case OS.FileSys.readDir ds of
                      NONE => (OS.FileSys.closeDir ds; acc)
                    | SOME name =>
                      if String.isSuffix "Theory.dat" name then
                        loop (OS.Path.concat(objsdir, name) :: acc)
                      else loop acc
          in loop acc end
          handle OS.SysErr _ => acc

      fun descend d acc =
          let val ds = OS.FileSys.openDir d
              fun loop acc =
                  case OS.FileSys.readDir ds of
                      NONE => (OS.FileSys.closeDir ds; acc)
                    | SOME name =>
                      let val p = OS.Path.concat(d, name) in
                        if name = "." orelse name = ".." then loop acc
                        else if (OS.FileSys.isLink p handle _ => false) then
                          loop acc
                        else if not (OS.FileSys.isDir p handle _ => false) then
                          loop acc
                        else if name = ".hol" then
                          loop (list_dats (OS.Path.concat(p, "objs")) acc)
                        else if String.sub(name, 0) = #"." then loop acc
                        else loop (descend p acc)
                      end
          in loop acc end
          handle OS.SysErr _ => acc
    in
      descend root []
    end

fun merge cmp l1 l2 =
    case (l1, l2) of
        ([], _) => l2
      | (_, []) => l1
      | (x :: xs, y :: ys) =>
        case cmp(x, y) of
            GREATER => y :: merge cmp l1 ys
          | _ => x :: merge cmp xs l2

fun sort cmp xs =
    let fun splitAt n acc xs =
            if n <= 0 then (acc, xs)
            else case xs of
                     [] => (acc, [])
                   | x::rest => splitAt (n - 1) (x :: acc) rest
    in
      case xs of
          [] => []
        | [x] => [x]
        | _ =>
          let val (l, r) = splitAt (length xs div 2) [] xs
          in merge cmp (sort cmp l) (sort cmp r) end
    end

(* Keys are the .dat file paths relative to the capture root.  Paths are
   unique (a directory can't hold two files with the same name), so sort
   and diff logic collapses to the straightforward set case: - / + / ~. *)
fun cmp_entry ((a,_),(b,_)) = String.compare(a,b)

fun rel_to root path =
    OS.Path.mkRelative {path = path, relativeTo = root}
    handle OS.Path.Path => path

fun capture root =
    let val abs_root = OS.FileSys.fullPath root
                       handle OS.SysErr _ => root
        val paths = walk abs_root
        val hashed = map (fn p => (rel_to abs_root p, sha1_file p)) paths
        val sorted = sort cmp_entry hashed
    in
      List.app (fn (p, h) => pr (p ^ " " ^ h ^ "\n")) sorted;
      OS.Process.exit OS.Process.success
    end

fun read_capture filename =
    let val is = TextIO.openIn filename
        fun loop acc =
            case TextIO.inputLine is of
                NONE => (TextIO.closeIn is; acc)
              | SOME line =>
                case String.tokens Char.isSpace line of
                    [] => loop acc
                  | [path, hash] => loop ((path, hash) :: acc)
                  | _ => die ("malformed line in " ^ filename ^ ": " ^ line)
        val entries = loop []
    in
      sort cmp_entry entries
    end

(* Path-keyed set difference.  Each entry appears at most once per file,
   so the three buckets are unambiguous:
     + <path>   present in AFTER but not BEFORE
     - <path>   present in BEFORE but not AFTER
     ~ <path>   present in both with different hashes  *)
fun diff before_file after_file =
    let val bef = read_capture before_file
        val aft = read_capture after_file
        fun walk (bs, as_, added, removed, changed) =
            case (bs, as_) of
                ([], rest) => (added @ map #1 rest, removed, changed)
              | (rest, []) => (added, removed @ map #1 rest, changed)
              | ((bp,bh)::brest, (ap,ah)::arest) =>
                case String.compare(bp, ap) of
                    EQUAL =>
                      walk (brest, arest, added, removed,
                            if bh = ah then changed else bp :: changed)
                  | LESS =>
                      walk (brest, as_, added, bp :: removed, changed)
                  | GREATER =>
                      walk (bs, arest, ap :: added, removed, changed)
        val (added, removed, changed) = walk (bef, aft, [], [], [])
        val added = List.rev added
        val removed = List.rev removed
        val changed = List.rev changed
    in
      List.app (fn p => pr ("+ " ^ p ^ "\n")) added;
      List.app (fn p => pr ("- " ^ p ^ "\n")) removed;
      List.app (fn p => pr ("~ " ^ p ^ "\n")) changed;
      if null added andalso null removed andalso null changed then
        OS.Process.exit OS.Process.success
      else
        OS.Process.exit OS.Process.failure
    end

datatype cline = C of {help : bool}
val init = C {help = false}
fun help_upd b (C _) = C {help = b}

val cline_options = [
  {short = "h", long = ["help"],
   desc = GetOpt.NoArg (fn () => help_upd true),
   help = "Show this message"}
]

fun usage_string () =
    CommandLine.name() ^ " {capture ROOT | diff BEFORE AFTER}\n\n\
    \  capture ROOT           walk ROOT for .hol/objs/*Theory.dat files;\n\
    \                         emit sorted \"<rel-path> <sha1>\" lines\n\
    \                         where <rel-path> is the .dat file's path\n\
    \                         relative to ROOT\n\
    \  diff BEFORE AFTER      compare two capture files;\n\
    \                         prefix + added, - removed, ~ changed;\n\
    \                         exit 1 if any difference, else 0\n"

fun main () =
    let val header = usage_string()
        val uinfo = GetOpt.usageInfo {header = header, options = cline_options}
        val (upds, rest) =
            GetOpt.getOpt {argOrder = GetOpt.Permute,
                           options = cline_options,
                           errFn = warn}
                          (CommandLine.arguments())
        val C {help} = List.foldl (fn (f, a) => f a) init upds
        val _ = not help orelse (pr uinfo; OS.Process.exit OS.Process.success)
    in
      case rest of
          ["capture", root] => capture root
        | ["diff", b, a] => diff b a
        | _ => die uinfo
    end

end (* structure corpus_diff *)
