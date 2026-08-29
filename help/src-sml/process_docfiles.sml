(* process_docfiles.sml

   Build-time driver: turns *.smd from one or more source directories
   (help/Docfiles, plus any --extra-src directory such as
   help/generated-alias-docs) into

     (1)  Manual/build/Docfiles-processed/<base>.md
          (polyscripter-evaluated; consumed by mdbook, Md2TeX, and the
          .txt step below), and

     (2)  <src-dir-of-that-entry>/<base>.txt
          (consumed by makebase.exe -> the in-HOL `help` command;
          makebase scans the directories named in
          tools/documentation-directories).

   Optionally also produces help/Docfiles/HTML/<base>.html in a third
   step, for builds where mdbook isn't available to provide per-entry
   HTML pages.

   Polyscripter (Manual/Tools/polyscripter.sml) is invoked as a library:
   one setup, one obuf, threaded through every entry so Poly/ML
   compiler state and loaded theories persist between calls.

   Pandoc is invoked at most twice per build: once on the concatenated
   processed markdown (with a per-entry sentinel between documents) to
   produce all .txt, and optionally a second time for HTML.  The
   resulting stream is split on the sentinel and each chunk is written
   to its own per-entry file. *)

(* No top-level `infix ++` here: `>>` directives in .smd files are
   compiled in the same Poly/ML session as this file, and an infix
   override would shadow whatever else `++` is in the HOL heap
   (e.g. `simpLib.++ : simpset * ssfrag -> simpset`).  Use a plain
   function instead. *)
fun pjoin (a, b) = OS.Path.concat (a, b)

fun warnLn s = (TextIO.output(TextIO.stdErr, s ^ "\n");
                TextIO.flushOut TextIO.stdErr)
fun dieLn s = (warnLn s; OS.Process.exit OS.Process.failure)

fun which arg =
  let
    open OS.FileSys Systeml
    val sepc = if isUnix then #":" else #";"
    fun check p =
      let val fname = OS.Path.concat(p, arg)
      in if access (fname, [A_READ, A_EXEC]) then SOME fname else NONE end
    fun first [] = NONE
      | first (p::ps) = (case check p of NONE => first ps | sm => sm)
  in
    case OS.Process.getEnv "PATH" of
        NONE => if isUnix then NONE else check "."
      | SOME path =>
        let val paths = (if isUnix then [] else ["."]) @
                        String.fields (fn c => c = sepc) path
        in first paths end
  end

fun mkdir_p dir =
  if dir = "" orelse dir = "." orelse OS.FileSys.access(dir, []) then ()
  else (mkdir_p (OS.Path.dir dir);
        OS.FileSys.mkDir dir handle OS.SysErr _ => ())

fun find_smd_bases dir =
  let
    val dirstrm = OS.FileSys.openDir dir
    fun loop A =
      case OS.FileSys.readDir dirstrm of
          NONE => (OS.FileSys.closeDir dirstrm;
                   Listsort.sort String.compare A)
        | SOME s =>
          (case OS.Path.splitBaseExt s of
              {base, ext = SOME "smd"} => loop (base :: A)
            | _ => loop A)
  in
    loop [] handle e => (OS.FileSys.closeDir dirstrm handle _ => (); raise e)
  end

(* A sentinel survives pandoc markdown->plain and markdown->html
   unchanged because it's just text in its own paragraph.  The hex
   tag makes accidental collisions with source content effectively
   impossible. *)
val sentinel_prefix = "==HOL_DOC_BREAK_a8f3c2_"
val sentinel_suffix = "=="
fun sentinel base = sentinel_prefix ^ base ^ sentinel_suffix

(* Per-entry progress reporting.  Two modes:

   - default: one "<entry>.smd" line per file to stdout.  Intended
     for invocation under Holmake, which weaves a child job's latest
     output into its own TTY status; a silent tool there triggers
     Holmake's "time since last output" counter, which reads as
     "hung".

   - show_progress=true: a spinner + decreasing-count on a single
     \r-overwritten line via Flash.initialise_spinner.  Intended for
     direct invocation (e.g. from bin/build), where one self-
     overwriting line is tidier than scrolling 1500+ filenames. *)
fun polyscript_all {entries, processed_dir, obuf, show_progress} =
  let
    val concatBuf = SimpleBuffer.mkBuffer()
    val pushConcat = #push concatBuf
    val umap = Binarymap.mkDict String.compare
    val (announce, finish_progress) =
        if show_progress then
          let val (tick, finish) =
                  Flash.initialise_spinner ("", length entries)
          in (fn _ => tick (), finish) end
        else
          (fn entry =>
              (TextIO.output (TextIO.stdOut, "  " ^ entry ^ ".smd\n");
               TextIO.flushOut TextIO.stdOut),
           fn () => ())
    fun do_one (src_dir, entry) =
      let
        val () = announce entry
        val srcfile = OS.Path.joinBaseExt {base = pjoin (src_dir, entry),
                                           ext = SOME "smd"}
        (* Keep the .smd extension on the processed side so that the
           SUMMARY.md generator (Manual/Tools/gen_reference_summary)
           and Md2TeX (help/src-sml/Md2TeX.sml) -- both of which
           reference filenames literally -- can target the processed
           directory without any other changes.  The
           processed-vs-source distinction is conveyed by the
           directory name, not the extension. *)
        val dstfile = OS.Path.joinBaseExt {base = pjoin (processed_dir, entry),
                                           ext = SOME "smd"}
        val instrm = TextIO.openIn srcfile
        val outstrm = TextIO.openOut dstfile
        fun out s = (TextIO.output(outstrm, s); pushConcat s)
        val () = resetParseError ()
        (* Name the entry on polyscripter's die-style diagnostics
           so they identify which .smd is at fault. *)
        val () = currentSource := entry ^ ".smd"
      in
        processStream {input = instrm, output = out,
                       debug = false, umap = umap, obuf = obuf};
        TextIO.closeIn instrm;
        TextIO.closeOut outstrm;
        (* HOLSource's parse errors land on stderr, but `>>+`
           swallows the resulting Fail "Static Errors" so the
           build proceeds with a broken example.  Treat any parse
           error as fatal here -- the .smd is wrong at source and
           the maintainer needs to know. *)
        if hadParseError () then
          dieLn ("process_docfiles: parse error in " ^ entry ^
                 ".smd (see preceding stderr output)")
        else ();
        pushConcat ("\n\n" ^ sentinel entry ^ "\n\n")
      end
  in
    List.app do_one entries;
    finish_progress ();
    #read concatBuf ()
  end

fun writeTmpFile content =
  let
    val tmp = OS.FileSys.tmpName()
    val ostrm = TextIO.openOut tmp
  in
    TextIO.output(ostrm, content);
    TextIO.closeOut ostrm;
    tmp
  end

fun readWholeFile fname =
  let
    val istrm = TextIO.openIn fname
    val s = TextIO.inputAll istrm
  in
    TextIO.closeIn istrm; s
  end

fun pandoc_once pdexe input extraArgs =
  let
    val intmp = writeTmpFile input
    val outtmp = OS.FileSys.tmpName()
    val args = [pdexe, "-f", "markdown", intmp, "-o", outtmp] @ extraArgs
    val res = Systeml.systeml args
    fun cleanup () = (OS.FileSys.remove intmp handle _ => ();
                      OS.FileSys.remove outtmp handle _ => ())
  in
    if OS.Process.isSuccess res then
      let val s = readWholeFile outtmp in cleanup (); s end
    else (cleanup ();
          dieLn ("pandoc invocation failed: " ^
                 String.concatWith " " (List.tl args)))
  end

(* Peel chunks off `output` in the order given by `bases`.  Each
   chunk is the slice before that base's sentinel; the sentinel and
   the rest of its line are discarded along with one trailing newline. *)
fun split_chunks bases output =
  let
    fun split_one entry s =
      let
        val target = sentinel entry
        open Substring
        val (pfx, sfx) = position target (full s)
      in
        if size sfx = 0 then
          dieLn ("Sentinel for " ^ entry ^ " not found in pandoc output")
        else
          let
            val after = triml (String.size target) sfx
            val (_, after_line) = splitl (fn c => c <> #"\n") after
            val after_line = if size after_line > 0 then triml 1 after_line
                             else after_line
          in
            (string pfx, string after_line)
          end
      end
    fun loop acc s [] = List.rev acc
      | loop acc s (b::bs) =
        let val (chunk, rest) = split_one b s
        in loop ((b, chunk) :: acc) rest bs end
  in
    loop [] output bases
  end

fun strip_outer_blanks s =
  let
    open Substring
    val ss = dropr Char.isSpace (full s)
    val ss = dropl (fn c => c = #"\n") ss
  in
    string ss ^ "\n"
  end

(* out_dir_of maps an entry base to the directory its output belongs
   in: for .txt that's the entry's own source directory (so makebase
   finds it next to the .smd), for .html it's the single fallback
   HTML directory.  out_dirs is the (small) set of directories it can
   return, created once up front rather than per entry. *)
fun write_chunks {out_dir_of, out_dirs, ext, chunks, wrap} =
  let
    val () = List.app mkdir_p out_dirs
    fun do_one (base, chunk) =
      let
        val out_dir = out_dir_of base
        val outfile = OS.Path.joinBaseExt {base = pjoin (out_dir, base),
                                           ext = SOME ext}
        val ostrm = TextIO.openOut outfile
      in
        TextIO.output(ostrm, wrap base chunk);
        TextIO.closeOut ostrm
      end
  in
    List.app do_one chunks
  end

(* For the HTML fallback path: pandoc emits body fragments (no -s);
   wrap each in a minimal standalone document with the same CSS link
   the old per-file `-s -c doc.css` invocation produced. *)
fun html_wrap base body =
  String.concat [
    "<!DOCTYPE html>\n<html>\n<head>\n  <meta charset=\"utf-8\">\n",
    "  <title>", base, "</title>\n",
    "  <link rel=\"stylesheet\" href=\"doc.css\">\n",
    "</head>\n<body>\n",
    strip_outer_blanks body,
    "</body>\n</html>\n"
  ]

fun txt_wrap _ body = strip_outer_blanks body

(* Positional args:
     <src-dir>        primary directory of .smd source files
                      (help/Docfiles); see also --extra-src
     <processed-dir>  where to write polyscripter-processed .md
                      (e.g. Manual/build/Docfiles-processed)
     <html-dir>       optional; when given, also produces per-entry
                      HTML pages there via a second pandoc pass *)
datatype cline = CR of { show_progress : bool, help : bool,
                         extra_src : string list }
val cline_init = CR { show_progress = false, help = false, extra_src = [] }
fun progress_upd b (CR {help, extra_src, ...}) =
  CR { show_progress = b, help = help, extra_src = extra_src }
fun help_upd b (CR {show_progress, extra_src, ...}) =
  CR { show_progress = show_progress, help = b, extra_src = extra_src }
fun extra_src_upd d (CR {show_progress, help, extra_src}) =
  CR { show_progress = show_progress, help = help,
       extra_src = extra_src @ [d] }

val cline_options : (cline -> cline) GetOpt.opt_descr list = [
  {short = "h", long = ["help"],
   desc = GetOpt.NoArg (fn () => help_upd true),
   help = "Show this message"},
  {short = "", long = ["extra-src"],
   desc = GetOpt.ReqArg (extra_src_upd, "DIR"),
   help = "Additional directory of .smd sources to process alongside \
          \<src-dir>; may be repeated.  Each entry's .txt is written \
          \back beside its own source."},
  {short = "", long = ["show-progress"],
   desc = GetOpt.NoArg (fn () => progress_upd true),
   help = "Animate a spinner + decreasing entry count on a single \
          \line (suppresses the default per-entry filename output)."}
]

fun process_docfiles_main () =
  let
    val uheader =
        CommandLine.name() ^
        " [options] <src-dir> <processed-dir> [<html-dir>]"
    val uinfo =
        GetOpt.usageInfo {header = uheader, options = cline_options}
    val (upds, positional) =
        GetOpt.getOpt {argOrder = GetOpt.Permute,
                       options = cline_options,
                       errFn = warnLn}
                      (CommandLine.arguments ())
    val CR {show_progress, help, extra_src} =
        List.foldl (fn (f, a) => f a) cline_init upds
    val () = if help then
               (print (uinfo ^ "\n"); OS.Process.exit OS.Process.success)
             else ()
    val (src_dir, processed_dir, html_opt) =
        case positional of
            [a, b] => (a, b, NONE)
          | [a, b, c] => (a, b, SOME c)
          | _ => dieLn uinfo

    (* Pandoc is needed only for the .txt (and optional .html) passes
       below; the .md mirror is produced by the polyscripter and needs
       no pandoc.  So a missing pandoc downgrades to "no .txt/.html"
       rather than aborting -- otherwise we'd leave processed_dir
       uncreated and the caller's follow-up steps (e.g. the build's
       Docfiles-processed/.stamp write) would fail with ENOENT. *)
    val pandoc_opt = which "pandoc"

    val () = mkdir_p processed_dir

    val src_dirs = src_dir :: extra_src
    fun entries_of d =
        map (fn b => (d, b))
            (find_smd_bases d
             handle e => dieLn ("Couldn't enumerate " ^ d ^ ": " ^
                                General.exnMessage e))
    (* An entry base must be unique across the source directories:
       it names the processed file, the pandoc sentinel and the
       mdbook page.  AliasGen enforces the same thing from its side;
       check here too so a stray file can't silently shadow one. *)
    val (entries, srcdir) =
        let
          fun add ((d, b), (acc, seen)) =
              case Binarymap.peek (seen, b) of
                  SOME d' => dieLn ("Entry " ^ b ^ ".smd appears in both " ^
                                    d' ^ " and " ^ d)
                | NONE => ((d, b) :: acc,
                           Binarymap.insert (seen, b, d))
          val (acc, seen) =
              List.foldl add ([], Binarymap.mkDict String.compare)
                         (List.concat (map entries_of src_dirs))
        in (List.rev acc, seen) end
    val bases = map #2 entries
    (* The dedup map doubles as the base -> source-directory lookup. *)
    fun srcdir_of b = Binarymap.find (srcdir, b)
    val () = if null entries then
               (warnLn ("No .smd files in " ^
                        String.concatWith ", " src_dirs);
                OS.Process.exit OS.Process.success)
             else ()
    val () = print ("Processing " ^ Int.toString (length entries) ^
                    " entries from " ^ String.concatWith ", " src_dirs ^
                    "\n")

    val () = elision_string1 := elision_string1_plain
    val obuf = setupPolyscripter ()

    val concat = polyscript_all
                   {entries = entries, processed_dir = processed_dir,
                    obuf = obuf, show_progress = show_progress}
    val () = print ("...polyscripter pass done\n")

    val () =
      case pandoc_opt of
          NONE =>
            warnLn ("Can't find pandoc in PATH; wrote the mdbook .md \
                    \mirror to " ^ processed_dir ^ " but skipped the \
                    \.txt help text" ^
                    (case html_opt of SOME _ => " and .html pages." | NONE => "."))
        | SOME pdexe =>
          let
            val txt_out = pandoc_once pdexe concat ["-t", "plain"]
            val txt_chunks = split_chunks bases txt_out
            val () = write_chunks {out_dir_of = srcdir_of,
                                   out_dirs = src_dirs, ext = "txt",
                                   chunks = txt_chunks, wrap = txt_wrap}
            val () = print ("...wrote " ^ Int.toString (length txt_chunks) ^
                            " .txt files to " ^
                            String.concatWith ", " src_dirs ^ "\n")
          in
            case html_opt of
                NONE => ()
              | SOME html_dir =>
                let
                  (* List.foldl passes the list element first; the
                     accumulator must stay in the absolute-prefix slot
                     of pjoin, because OS.Path.concat raises Path if
                     its second argument is absolute. *)
                  val luaFilter =
                      List.foldl (fn (p, acc) => pjoin (acc, p))
                                 Systeml.HOLDIR
                                 ["help", "src-sml",
                                  "internal-to-external.lua"]
                  val html_out =
                      pandoc_once pdexe concat
                                  ["-t", "html",
                                   "--lua-filter=" ^ luaFilter]
                  val html_chunks = split_chunks bases html_out
                in
                  write_chunks {out_dir_of = (fn _ => html_dir),
                                out_dirs = [html_dir], ext = "html",
                                chunks = html_chunks, wrap = html_wrap};
                  print ("...wrote " ^ Int.toString (length html_chunks) ^
                         " .html files to " ^ html_dir ^ "\n")
                end
          end
  in
    ()
  end
  (* Poly/ML --exe-main binaries exit silently on uncaught exceptions
     (no stack trace, no error message), which left CI failures here
     unattributable until the dieLn surfaced a name to look up. *)
  handle e =>
    dieLn ("process_docfiles: uncaught " ^ General.exnMessage e)

(* buildheap --exe main runs `main` at startup. *)
val main = process_docfiles_main
