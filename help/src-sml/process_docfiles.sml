(* process_docfiles.sml

   Build-time driver: turns help/Docfiles/*.smd into

     (1)  Manual/build/Docfiles-processed/<base>.md
          (polyscripter-evaluated; consumed by mdbook, Md2TeX, and the
          .txt step below), and

     (2)  help/Docfiles/<base>.txt
          (consumed by makebase.exe -> the in-HOL `help` command).

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

(* Optional trace: print each entry name as it's processed.  Enabled
   by setting PROCESS_DOCFILES_DEBUG=1 in the environment.
   Wrapped in a function so the env lookup happens at run time, not
   when the buildheap is saved. *)
fun debug_progress () =
    Option.isSome (OS.Process.getEnv "PROCESS_DOCFILES_DEBUG")

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

fun polyscript_all {src_dir, processed_dir, bases, obuf} =
  let
    val concatBuf = SimpleBuffer.mkBuffer()
    val pushConcat = #push concatBuf
    val umap = Binarymap.mkDict String.compare
    fun do_one entry =
      let
        val () = if debug_progress () then
                   (TextIO.output(TextIO.stdErr, "  [" ^ entry ^ "]\n");
                    TextIO.flushOut TextIO.stdErr)
                 else ()
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
    List.app do_one bases;
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

fun write_chunks {out_dir, ext, chunks, wrap} =
  let
    val () = mkdir_p out_dir
    fun do_one (base, chunk) =
      let
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

fun usage () =
  "Usage:\n  " ^ CommandLine.name() ^
  " <src-dir> <processed-dir> [<html-fallback-dir>]\n\
  \  src-dir          directory of .smd source files (help/Docfiles)\n\
  \  processed-dir    where to write polyscripter-processed .md\n\
  \                   (e.g. Manual/build/Docfiles-processed)\n\
  \  html-fallback-dir  optional; when given, also produces per-entry\n\
  \                   HTML pages there via a second pandoc pass\n"

fun process_docfiles_main () =
  let
    val (src_dir, processed_dir, html_opt) =
        case CommandLine.arguments () of
            [a, b] => (a, b, NONE)
          | [a, b, c] => (a, b, SOME c)
          | _ => dieLn (usage())

    val pdexe =
        case which "pandoc" of
            SOME s => s
          | NONE => (warnLn "Can't find pandoc in PATH; doing nothing.";
                     OS.Process.exit OS.Process.success)

    val () = mkdir_p processed_dir

    val bases = find_smd_bases src_dir
                handle e => dieLn ("Couldn't enumerate " ^ src_dir ^
                                   ": " ^ General.exnMessage e)
    val () = if null bases then
               (warnLn ("No .smd files in " ^ src_dir); OS.Process.exit OS.Process.success)
             else ()
    val () = print ("Processing " ^ Int.toString (length bases) ^
                    " entries from " ^ src_dir ^ "\n")

    val () = elision_string1 := elision_string1_plain
    val obuf = setupPolyscripter ()

    val concat = polyscript_all
                   {src_dir = src_dir, processed_dir = processed_dir,
                    bases = bases, obuf = obuf}
    val () = print ("...polyscripter pass done\n")

    val txt_out = pandoc_once pdexe concat ["-t", "plain"]
    val txt_chunks = split_chunks bases txt_out
    val () = write_chunks {out_dir = src_dir, ext = "txt",
                           chunks = txt_chunks, wrap = txt_wrap}
    val () = print ("...wrote " ^ Int.toString (length txt_chunks) ^
                    " .txt files to " ^ src_dir ^ "\n")

    val () = case html_opt of
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
                  write_chunks {out_dir = html_dir, ext = "html",
                                chunks = html_chunks, wrap = html_wrap};
                  print ("...wrote " ^ Int.toString (length html_chunks) ^
                         " .html files to " ^ html_dir ^ "\n")
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
