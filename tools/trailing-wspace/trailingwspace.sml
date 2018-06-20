structure trailingwspace =
struct

val WSOK = ".holwsok"
infix ++
val op++  = OS.Path.concat

fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")

datatype extra_avoid = ALL_FILES | SOME_FILES of string list

fun iLine is =
  Option.map (fn s => String.extract(s, 0, SOME (size s - 1)))
             (TextIO.inputLine is)

fun read_wsok_file dname =
  let
    val fname = dname ++ WSOK
    fun read instrm =
      let
        fun recurse (emptyp, acc) =
          case iLine instrm of
              NONE => (emptyp, acc)
            | SOME s =>
                if size s > 0 andalso String.sub(s, 0) = #"#" orelse
                   size s = 0
                then
                  recurse (false, acc)
                else
                  recurse (false, s::acc)
        val (was_empty, files) = recurse (true, [])
      in
        if was_empty then ALL_FILES else SOME_FILES files
      end
  in
    if OS.FileSys.access(fname, [OS.FileSys.A_READ]) then
      SOME (read (TextIO.openIn fname))
    else NONE
  end

fun lastchar s = String.sub(s, size s - 1)

datatype action = ShowLines | ShowFile | Fix

fun numNONWS s =
  let
    val i = size s - 1
    fun recurse i =
      if i < 0 then 0
      else if Char.isSpace (String.sub(s, i)) then recurse (i - 1)
      else i + 1
  in
    recurse i
  end
fun pr s = TextIO.output(TextIO.stdOut, s ^ "\n")

fun scanOneFile quietp action full_fname =
  let
    fun stdcont (s:string) a k = k a
    fun fixfinish a =
      let
        val _ = if quietp then () else pr full_fname
        val os = TextIO.openOut full_fname
      in
        app (fn s => TextIO.output(os, s)) (List.rev a);
        TextIO.closeOut os
      end
    val (readAction, rdflt, finish) =
        case action of
            ShowLines => ((fn s => fn ln => fn a => fn k =>
                             (pr (full_fname ^ ":" ^ Int.toString ln ^ ":" ^ s);
                              k a)),
                          stdcont,
                          fn a => ())
          | ShowFile =>
              ((fn _ => fn _ => fn a => fn _ => (pr full_fname; (true, a))),
               stdcont, fn a => ())
          | Fix => ((fn s => fn ln => fn a => fn k =>
                        k((String.extract(s, 0, SOME (numNONWS s))^"\n")::a)),
                    (fn s => fn a => fn k => k ((s ^ "\n")::a)),
                    fixfinish)
    val is = TextIO.openIn full_fname
    fun recurse seenws lnum acc act dfltact =
      case iLine is of
          NONE => (seenws, acc)
        | SOME s =>
          if size s > 0 andalso Char.isSpace (lastchar s) then
            act s lnum acc (fn acc => recurse true (lnum + 1) acc act dfltact)
          else
            dfltact s acc (fn acc => recurse seenws (lnum + 1) acc act dfltact)
    val (seenws, acc) =
      recurse false 1 [] readAction rdflt before TextIO.closeIn is
  in
    if seenws then (finish acc; true) else false
  end

fun mem x [] = false
  | mem x (y::ys) = x = y orelse mem x ys

fun ignorable fname =
  let
    val {base, ext} = OS.Path.splitBaseExt fname
  in
    case ext of
        SOME s => if s = "sml" then
                    String.isSuffix "Theory" base orelse
                    String.isSuffix "ML" base
                  else if s = "sig" then String.isSuffix "Theory" base
                  else s <> "tex" andalso s <> "ML" andalso s <> "lem" andalso
                       s <> "doc" andalso s <> "bib"
      | NONE => true
  end

fun handleDir quietp action seenws dname =
  let
    open OS.FileSys
    val ds = openDir dname
    fun recurse P seenws acc =
      case readDir ds of
          NONE => (closeDir ds; (seenws, acc))
        | SOME f0 =>
          let
            val f = dname ++ f0
          in
            if isDir f then recurse P seenws (f::acc)
            else if isLink f orelse P f orelse ignorable f then
              recurse P seenws acc
            else
              let
                val b = scanOneFile quietp action f
              in
                recurse P (b orelse seenws) acc
              end
          end
  in
    case read_wsok_file dname of
        SOME ALL_FILES =>
          (if quietp then ()
           else warn ("Not checking files in "^dname^" because of "^
                      WSOK^" file");
           recurse (fn _ => true) seenws [])
      | SOME (SOME_FILES fs) => recurse (fn n => mem n fs) seenws []
      | NONE => recurse (fn _ => false) seenws []
  end

fun doall quietp action seenws ds =
  case ds of
      [] => seenws
    | d::ds =>
      let
        val (seenws', newds) = handleDir quietp action seenws d
      in
        doall quietp action seenws' (newds @ ds)
      end

datatype cline_record = CR of { quiet : bool, action : action, help : bool}
val init = CR {quiet = false, action = Fix, help = false}
fun quiet_upd b (CR {action, help, ...}) =
  CR {action = action, quiet = b, help = help}
fun act_upd a (CR {quiet, help, ...}) =
  CR {action = a, quiet = quiet, help = help}
fun help_upd b (CR{quiet, action, ...}) =
  CR {action = action, quiet = quiet, help = b}
val NoArg = GetOpt.NoArg

val cline_options = [
  {short = "h", long = ["help"], desc = NoArg (fn () => help_upd true),
   help = "Show this message"},
  {short = "q", long = ["quiet"], desc = NoArg (fn () => quiet_upd true),
   help = "be quieter"},
  {short = "n", long = [], desc = NoArg (fn () => act_upd ShowFile),
   help = "No action; just list files (overrides -q)"},
  {short = "l", long = ["showlines"], desc = NoArg (fn () => act_upd ShowLines),
   help = "No action; list files and lines"}]


fun main () =
  let
    val uheader = CommandLine.name() ^ " [options] dir1 dir2 ..."
    val uinfo = GetOpt.usageInfo {header = uheader, options = cline_options}
    val (cline_upds, dirs) =
        GetOpt.getOpt {argOrder = GetOpt.Permute,
                       options = cline_options,
                       errFn = warn}
                      (CommandLine.arguments())
    val CR {quiet, action, help} =
        List.foldl (fn (f, acc) => f acc) init cline_upds
    val _ = not help orelse
            (TextIO.output(TextIO.stdOut, uinfo);
             OS.Process.exit OS.Process.success)
    val _ = not (null dirs) orelse
            (warn uinfo; OS.Process.exit OS.Process.failure)
    val seenws = doall quiet action false dirs
    val output_actionp = case action of Fix => false | _ => true
    val resultcode = if seenws andalso output_actionp then OS.Process.failure
                     else OS.Process.success
  in
    OS.Process.exit resultcode
  end

end
