(* smdpp.sml — mdbook preprocessor for scripted markdown (.smd) files.

   Reads the [Context, Book] JSON pair from stdin (mdbook's preprocessor
   protocol), runs polyscripter on each chapter's content, strips
   pandoc-only artefacts (YAML frontmatter, \index{...} entries, raw
   LaTeX fenced blocks), and writes the rewritten Book JSON to stdout.

   The single Poly/ML session is shared across all chapters, so theory
   loads and compiler state amortise.

   Built by `buildheap` after polyscripter.sml; relies on the JSON
   library (already loaded into bin/hol). *)

(* ===== JSON printer ===== *)

structure JSONPrinter : sig
  val toString : JSON.value -> string
  val output : (string -> unit) -> JSON.value -> unit
end = struct

  fun escString s =
    let
      fun pad4 n =
        StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX n)
      fun esc #"\"" = "\\\""
        | esc #"\\" = "\\\\"
        | esc #"\n" = "\\n"
        | esc #"\r" = "\\r"
        | esc #"\t" = "\\t"
        | esc #"\b" = "\\b"
        | esc #"\f" = "\\f"
        | esc c =
            if Char.ord c < 32 then "\\u" ^ pad4 (Char.ord c)
            else String.str c
    in
      "\"" ^ String.translate esc s ^ "\""
    end

  fun outputItems put sep f xs =
    let
      fun loop _ [] = ()
        | loop true (x::xs) = (f x; loop false xs)
        | loop false (x::xs) = (put sep; f x; loop false xs)
    in
      loop true xs
    end

  fun output put v =
    case v of
        JSON.NULL => put "null"
      | JSON.BOOL true => put "true"
      | JSON.BOOL false => put "false"
      | JSON.INT i => put (IntInf.toString i)
      | JSON.FLOAT r =>
          (* Real.toString uses ~ for negatives; rewrite to ASCII '-' *)
          put (String.translate
                 (fn #"~" => "-" | c => String.str c)
                 (Real.toString r))
      | JSON.STRING s => put (escString s)
      | JSON.ARRAY vs =>
          (put "["; outputItems put "," (output put) vs; put "]")
      | JSON.OBJECT pairs =>
          let
            fun pair (k, v) =
              (put (escString k); put ":"; output put v)
          in
            put "{"; outputItems put "," pair pairs; put "}"
          end

  fun toString v =
    let val sb = SimpleBuffer.mkBuffer()
    in output (#push sb) v; #read sb () end
end

(* ===== text transforms ===== *)

(* Drop a YAML frontmatter block at the very start of the content
   (between two `---` lines on their own).  Such frontmatter is
   pandoc-targeted and serves no purpose for mdbook. *)
fun dropFrontmatter s =
  if String.isPrefix "---\n" s then
    let
      val lines = String.fields (fn c => c = #"\n") s
      fun findEnd [] = NONE
        | findEnd ("---" :: rest) = SOME rest
        | findEnd (_ :: rest) = findEnd rest
    in
      case findEnd (tl lines) of
          NONE => s
        | SOME rest => String.concatWith "\n" rest
    end
  else s

(* Strip occurrences of `\<cmd>{...}` from the input, with brace
   counting on the argument.  Two-stage: first remove the
   substrings, then walk the result line-by-line and drop any
   line that became blank because it consisted only of stripped
   commands plus whitespace -- inside a definition-list
   continuation those leftover blank lines break the paragraph
   and cause the next 4-space-indented line to reparse as a code
   block. *)
fun stripCmd cmdName s =
  let
    val sub = String.sub
    val sz = String.size s
    val cmd = "\\" ^ cmdName ^ "{"
    val cmdsz = String.size cmd
    fun matchAt i =
      i + cmdsz <= sz andalso
      String.substring (s, i, cmdsz) = cmd
    fun skipBraces (i, depth) =
      if i >= sz then i
      else case sub (s, i) of
              #"{" => skipBraces (i+1, depth+1)
            | #"}" => if depth = 1 then i+1
                      else skipBraces (i+1, depth-1)
            | _ => skipBraces (i+1, depth)
    fun loop (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else if matchAt i then
        loop (skipBraces (i + cmdsz, 1), acc)
      else loop (i+1, sub (s, i) :: acc)
    val stripped = loop (0, [])
    val origLines = String.fields (fn c => c = #"\n") s
    val newLines = String.fields (fn c => c = #"\n") stripped
    fun isBlank ln = CharVector.all Char.isSpace ln
    fun zip (origs, news, acc) =
      case (origs, news) of
          ([], []) => List.rev acc
        | (o1::orest, n1::nrest) =>
            if isBlank n1 andalso not (isBlank o1) then
              zip (orest, nrest, acc)
            else
              zip (orest, nrest, n1 :: acc)
        | _ => List.rev acc @ news (* shouldn't happen *)
    val kept = zip (origLines, newLines, [])
  in
    String.concatWith "\n" kept
  end

val stripIndex = stripCmd "index"

(* Strip \label{...} for the mdbook output: pandoc passes labels
   through to the LaTeX pipeline as raw_tex, but in mdbook's HTML
   they would just be inert noise.  The label *registry* built in
   the scan pass below (see scanLabels) records what each label
   pointed at, so resolveRefs can turn `\ref{X}` calls into real
   mdbook hyperlinks before stripLabel runs. *)
fun stripLabel s = stripCmd "label" s

(* Handle pandoc-style raw fenced blocks `` ```{=<fmt>} ... ``` ``.
   The PDF pipeline runs through pandoc, which honours these
   blocks natively (passing the body to the matching writer and
   discarding the rest); mdbook's pulldown-cmark doesn't, so we
   have to dispose of them ourselves:

     {=mdbook}   strip the fence, keep the body so the markdown
                 inside gets parsed normally.  Use this for
                 mdbook-only content (typically table captions
                 that LaTeX emits via \caption{...}).
     anything    drop fence *and* body -- e.g. {=latex} chapter-
       else      local macro definitions, or {=html} fragments
                 we don't want in mdbook.                          *)
fun handleRawBlocks s =
  let
    val lines = String.fields (fn c => c = #"\n") s
    fun firstTok ln =
      case String.tokens Char.isSpace ln of
          [] => NONE
        | t :: _ => SOME t
    (* Returns SOME format if `ln` opens a raw fenced block,
       e.g. "```{=latex}" -> SOME "latex"; NONE otherwise. *)
    fun fenceOpenFormat ln =
      case firstTok ln of
          SOME t =>
            if String.isPrefix "```{=" t andalso
               String.isSuffix "}" t
            then SOME (String.substring (t, 5, String.size t - 6))
            else NONE
        | NONE => NONE
    fun isFenceClose ln =
      case firstTok ln of
          SOME "```" => true
        | _ => false
    datatype state = Outside | Stripping | Inlining
    fun loop ([], acc, _) = List.rev acc
      | loop (l :: rest, acc, Stripping) =
          if isFenceClose l then loop (rest, acc, Outside)
          else loop (rest, acc, Stripping)
      | loop (l :: rest, acc, Inlining) =
          if isFenceClose l then loop (rest, acc, Outside)
          else loop (rest, l :: acc, Inlining)
      | loop (l :: rest, acc, Outside) =
          case fenceOpenFormat l of
              SOME "mdbook" => loop (rest, acc, Inlining)
            | SOME _ => loop (rest, acc, Stripping)
            | NONE => loop (rest, l :: acc, Outside)
  in
    String.concatWith "\n" (loop (lines, [], Outside))
  end

(* Convert pandoc superscript syntax `^...^` to `<sup>...</sup>`.
   Pandoc's default reader treats `^x^` as superscript when the body
   has no whitespace; pulldown-cmark (mdbook) doesn't.  We avoid `^`
   inside math: $...$ and $$...$$ blocks pass through untouched. *)
fun convertSuperscripts s =
  let
    val sub = String.sub
    val sz = String.size s
    fun isBodyChar c = not (Char.isSpace c) andalso c <> #"^"
    (* Try to find matching `^` for opening at i; bound by line end. *)
    fun findClose j =
      if j >= sz then NONE
      else case sub (s, j) of
              #"^" => SOME j
            | #"\n" => NONE
            | c => if isBodyChar c then findClose (j + 1) else NONE
    fun outside (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else case sub (s, i) of
              #"$" =>
                if i + 1 < sz andalso sub (s, i+1) = #"$"
                then mathSpan true (i+2, #"$" :: #"$" :: acc)
                else mathSpan false (i+1, #"$" :: acc)
            | #"`" => codeSpan (i+1, #"`" :: acc)
            | #"^" =>
                if i + 1 < sz andalso isBodyChar (sub (s, i+1)) then
                  case findClose (i+1) of
                      SOME j =>
                        outside (j+1,
                          List.revAppend
                            (String.explode ("<sup>"
                              ^ String.substring (s, i+1, j-i-1)
                              ^ "</sup>"), acc))
                    | NONE => outside (i+1, #"^" :: acc)
                else outside (i+1, #"^" :: acc)
            | c => outside (i+1, c :: acc)
    and mathSpan isDisplay (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else if sub (s, i) = #"$" then
        if isDisplay then
          if i + 1 < sz andalso sub (s, i+1) = #"$"
          then outside (i+2, #"$" :: #"$" :: acc)
          else mathSpan isDisplay (i+1, #"$" :: acc)
        else outside (i+1, #"$" :: acc)
      else mathSpan isDisplay (i+1, sub (s, i) :: acc)
    and codeSpan (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else case sub (s, i) of
              #"`" => outside (i+1, #"`" :: acc)
            | c => codeSpan (i+1, c :: acc)
  in
    outside (0, [])
  end

(* Inside $...$ inline math and $$...$$ display math, escape characters
   that CommonMark would otherwise consume:
     `\` doubled to `\\` so the original backslash survives the
        backslash-escape pass for MathJax (`\_`, `\{`, `\}`, etc.).
     `_` and `*` prefixed with `\` so pulldown-cmark's emphasis pass
        doesn't pair them up across math content (e.g.
        `\mathsf{Terms}_{\Sigma_{\Omega}}` would otherwise turn the
        embedded `_` into <em> tags).
   Code spans (`...`) and fenced code blocks (```...```) are passed
   through verbatim: a stray `$` inside a code span or block must
   not flip protectMath into math mode (otherwise everything between
   that `$` and the next stray `$` -- possibly many lines later --
   gets `_` and `\` over-escaped). *)
fun protectMath s =
  let
    val sub = String.sub
    val sz = String.size s
    fun emit c acc = c :: acc
    fun emitStr str acc = List.revAppend (String.explode str, acc)
    fun protect c acc =
      case c of
          #"\\" => emitStr "\\\\" acc
        | #"_"  => emitStr "\\_" acc
        | #"*"  => emitStr "\\*" acc
        | _ => c :: acc
    (* Test whether position i starts a fenced-code-block delimiter:
       three backticks following nothing but blockquote markers (`>`)
       and whitespace back to the start of the line.  Allowing the
       blockquote prefix is what lets a ```...``` fence nested inside
       a `> ` blockquote register as a code block here -- otherwise a
       stray `$` inside such a fenced block flips protectMath into
       math mode and over-escapes underscores throughout the rest of
       the file. *)
    fun atFenceLineStart i =
      if i = 0 then true
      else case sub (s, i-1) of
              #"\n" => true
            | #" " => atFenceLineStart (i-1)
            | #"\t" => atFenceLineStart (i-1)
            | #">" => atFenceLineStart (i-1)
            | _ => false
    fun fenceAt i =
      if i + 2 < sz andalso sub (s, i) = #"`"
         andalso sub (s, i+1) = #"`" andalso sub (s, i+2) = #"`"
         andalso atFenceLineStart i
      then SOME 3
      else NONE
    (* In "outside" state: looking for $...$ math, code spans, or
       fenced code blocks. *)
    fun outside (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else case fenceAt i of
              SOME 3 => fenced (i+3, emitStr "```" acc)
            | _ =>
        case sub (s, i) of
            #"`" => codespan (i+1, emit #"`" acc)
          | #"$" =>
              if i + 1 < sz andalso sub (s, i+1) = #"$" then
                display (i+2, emitStr "$$" acc)
              else
                inline (i+1, emit #"$" acc)
          | c => outside (i+1, emit c acc)
    (* In a single-backtick code span, copy verbatim until the
       closing backtick or end-of-line (CommonMark: code spans don't
       cross newlines without backticks). *)
    and codespan (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else case sub (s, i) of
              #"`" => outside (i+1, emit #"`" acc)
            | #"\n" => outside (i+1, emit #"\n" acc)
            | c => codespan (i+1, emit c acc)
    (* Inside a fenced code block, copy verbatim until the closing
       triple-backtick (also at the start of a line). *)
    and fenced (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else case fenceAt i of
              SOME 3 => outside (i+3, emitStr "```" acc)
            | _ => fenced (i+1, emit (sub (s, i)) acc)
    and inline (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else case sub (s, i) of
              #"$" => outside (i+1, emit #"$" acc)
            | c => inline (i+1, protect c acc)
    and display (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else if sub (s, i) = #"$" andalso
              i + 1 < sz andalso sub (s, i+1) = #"$" then
        outside (i+2, emitStr "$$" acc)
      else display (i+1, protect (sub (s, i)) acc)
  in
    outside (0, [])
  end

(* Use the plain-text elision marker for the .smd path: the
   default `\quad\textit{\small\dots{}output elided\dots{}}` is
   LaTeX-flavoured and would render literally inside an mdbook
   <pre><code> block.  This mirrors what polyscripter's `-md` CLI
   flag does for the .smd -> .md path. *)
val () = elision_string1 := elision_string1_plain

(* When the input has already been polyscripted upstream (e.g. by
   help/src-sml/process_docfiles, which materialises a directory of
   evaluated .md before mdbook is invoked), we want this preprocessor
   to leave `>>` directives -- which by then no longer exist anyway --
   alone and to skip the cost of loading the HOL heap a second time.
   The Reference book.toml sets this via
     command = "../Tools/smdpp --no-polyscripter"
   while Description / Tutorial use the default. *)
val noPolyscripter = ref false

fun runScripted obuf s =
  if !noPolyscripter then s
  else processString {input = s, debug = false,
                      umap = Binarymap.mkDict String.compare,
                      obuf = obuf}

(* If the content has no heading at all, prepend `# <name>` so the
   rendered chapter has a title.  Some .smd files defer chapter-
   titling to the LaTeX driver (e.g., modern-syntax.smd is wrapped
   by modern-syntax-chapter.tex); Reference manual entries start at
   H2 (the entry's H2 is its title); a few .smd files might lack any
   heading.  Only the last group needs synthesis; for those that do
   have an H2/H3 already we let mdbook use that as the page heading
   directly. *)
fun hasHeading s =
  let
    val lines = String.fields (fn c => c = #"\n") s
    fun isHeading ln =
      String.isPrefix "# " ln orelse ln = "#" orelse
      String.isPrefix "## " ln orelse ln = "##" orelse
      String.isPrefix "### " ln orelse ln = "###" orelse
      String.isPrefix "#### " ln orelse ln = "####"
  in
    List.exists isHeading lines
  end

fun ensureH1 name s =
  if hasHeading s then s else "# " ^ name ^ "\n\n" ^ s

(* Strip the chapter file's extension and append `.html`; used when
   we resolve a cross-chapter `\ref` or `[text](#anchor)` and need
   the URL of the target chapter's rendered page. *)
fun toHtml f =
  let val {base, ...} = OS.Path.splitBaseExt f
  in OS.Path.joinBaseExt {base = base, ext = SOME "html"} end

(* Find the index of the `}` that closes the group opening just
   *before* position `start` (i.e. depth is already 1 at `start`).
   Brace-counted so `\foo{\bar{baz}}` matches the outer `}`. *)
fun findCloseBrace (s, start) =
  let
    val sub = String.sub
    val sz = String.size s
    fun loop (j, depth) =
      if j >= sz then NONE
      else case sub (s, j) of
              #"{" => loop (j+1, depth+1)
            | #"}" => if depth = 1 then SOME j
                      else loop (j+1, depth-1)
            | _ => loop (j+1, depth)
  in loop (start, 1) end

(* Cross-book label registry: at preprocessor startup, smdpp scans
   `../*/labels.tsv` (one per sibling book) and loads each book's
   labels into this map.  Each row is `(book, label, file, anchor,
   num)`.  `book` is the sibling directory name (`Description`,
   `Tutorial`, `Reference`).  `resolveRefs` looks up entries here
   when it sees a `\ref{Book:label}` form. *)
val crossBookLabels :
    (string * string * string * string * string) list ref = ref []

(* Hard-coded list of sibling book directory names.  In practice
   the manuals live as siblings under `Manual/`, and there are
   exactly three (Description, Tutorial, Reference) for now; if
   another joins later, it needs adding here.  We accept that
   over a fully-dynamic discovery to keep cross-book label
   resolution explicit and predictable. *)
val knownSiblingBooks = ["Description", "Tutorial", "Reference"]

fun loadCrossBookLabels () =
  let
    fun loadOne book =
      let val path = "../" ^ book ^ "/labels.tsv"
      in
        if not (OS.FileSys.access (path, [OS.FileSys.A_READ])) then ()
        else
          let
            val content =
                let val ins = TextIO.openIn path
                    val s = TextIO.inputAll ins
                    val () = TextIO.closeIn ins
                in s end
            val rows = String.fields (fn c => c = #"\n") content
            fun parseRow row =
              case String.fields (fn c => c = #"\t") row of
                  [lbl, file, anchor, num] =>
                    SOME (book, lbl, file, anchor, num)
                | _ => NONE
            val parsed = List.mapPartial parseRow rows
            val () = crossBookLabels := parsed @ !crossBookLabels
          in () end
      end
  in
    crossBookLabels := [];
    List.app loadOne knownSiblingBooks
  end

(* Distinguishes parenthetical `\cite` (pandoc `[@k]`, "(Author Year)")
   from textual `\citet` (pandoc `@k`, "Author (Year)").  The PDF side
   resolves both via natbib; for HTML we run the same key through
   pandoc twice when both forms appear, since the rendered span
   differs. *)
datatype citeForm = Paren | Text

fun formToString Paren = "p"
  | formToString Text  = "t"

fun formFromString "p" = SOME Paren
  | formFromString "t" = SOME Text
  | formFromString _   = NONE

(* Detect a `\cite` or `\citet` command starting at position i.  Both
   require a non-letter character (or end of string) immediately after
   the command name so prefixes like `\citeX` don't false-positive.
   Returns SOME (form, position-just-past-command-name). *)
fun detectCite (s, i, sz) =
  let
    val sub = String.sub
    fun isCmdEnd c = not (Char.isAlpha c)
    val marker = "\\cite"
    val msz = String.size marker
  in
    (* Cheap byte check first: detectCite is called for every position
       in the input, so dodging the 5-char substring allocation at
       non-`\` positions saves ~99% of intermediate strings on a
       typical .smd file. *)
    if i + msz > sz then NONE
    else if sub (s, i) <> #"\\" then NONE
    else if String.substring (s, i, msz) <> marker then NONE
    else
      let val k = i + msz in
        if k < sz andalso sub (s, k) = #"t"
           andalso (k + 1 = sz orelse isCmdEnd (sub (s, k + 1)))
        then SOME (Text, k + 1)
        else if k = sz orelse isCmdEnd (sub (s, k))
        then SOME (Paren, k)
        else NONE
      end
  end

(* Loaded once from `cite-labels.tsv` at preprocessor startup (see
   loadCiteLabels below).  Each row is (keys, locator, form,
   rendered-html) matching the TSV emitted by `smdpp render-bib`.
   Empty when the labels file is missing — citations then pass through
   unrewritten and the post-build `smdpp check-html` leak check
   surfaces them. *)
val citeLabels : (string * string * citeForm * string) list ref = ref []

(* Read cite-labels.tsv from cwd; warn (don't die) if missing. *)
fun loadCiteLabels () =
  let
    val path = "cite-labels.tsv"
  in
    if not (OS.FileSys.access (path, [OS.FileSys.A_READ])) then
      (TextIO.output (TextIO.stdErr,
         "smdpp: cite-labels.tsv not found in " ^
         OS.FileSys.getDir () ^
         "; \\cite{...} calls will pass through unrewritten\n");
       citeLabels := [])
    else
      let
        val content =
            let val ins = TextIO.openIn path
                val s = TextIO.inputAll ins
                val () = TextIO.closeIn ins
            in s end
        val lines = String.fields (fn c => c = #"\n") content
        fun parse line =
          case String.fields (fn c => c = #"\t") line of
              [k, l, f, h] =>
                (case formFromString f of
                     SOME form => SOME (k, l, form, h)
                   | NONE => NONE)
            | _ => NONE
      in
        citeLabels := List.mapPartial parse lines
      end
  end

(* Loaded once from `../Reference/entries.list` at preprocessor
   startup (see loadRefEntries below).  Each line names one entry
   that exists in help/Docfiles/ (e.g. `BasicProvers.CASE_TAC`).
   Used to resolve `\refentry{Foo.bar}` cross-manual references and
   to error out at preprocess-time on typos / removed entries. *)
val refEntries : string list ref = ref []

(* Read ../Reference/entries.list relative to cwd; warn (don't die)
   if missing -- e.g., on a Reference-only checkout where Description
   hasn't been wired yet.  When the file is missing, `\refentry{}`
   calls pass through unrewritten and `smdpp check-html`'s leak check
   surfaces them. *)
fun loadRefEntries () =
  let
    val path = "../Reference/entries.list"
  in
    if not (OS.FileSys.access (path, [OS.FileSys.A_READ])) then
      (TextIO.output (TextIO.stdErr,
         "smdpp: " ^ path ^ " not found; \\refentry{...} calls " ^
         "will pass through unrewritten\n");
       refEntries := [])
    else
      let
        val content =
            let val ins = TextIO.openIn path
                val s = TextIO.inputAll ins
                val () = TextIO.closeIn ins
            in s end
        val lines = String.fields (fn c => c = #"\n") content
        val entries = List.filter (fn s => s <> "") lines
      in
        refEntries := entries
      end
  end

(* Replace each `\refentry{Foo.bar}` with a markdown link to the
   matching entry page in the Reference manual.  Brace-counted on
   the argument.  Unknown entry names abort the build with a clear
   error -- catches typos and stale references at preprocess time
   rather than letting them silently break links in the rendered
   HTML.  Skipped when `refEntries` is empty (loadRefEntries
   couldn't find entries.list); leaks then get surfaced by
   `smdpp check-html`. *)
fun rewriteRefEntry currentFile s =
  let
    val sub = String.sub
    val sz = String.size s
    val marker = "\\refentry{"
    val msz = String.size marker
    val knownEntries = !refEntries
    fun knownEntry key = List.exists (fn e => e = key) knownEntries
    fun loop (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else if i + msz <= sz andalso
              String.substring (s, i, msz) = marker
      then
        case findCloseBrace (s, i + msz) of
            NONE => loop (i + 1, sub (s, i) :: acc)
          | SOME j =>
            let
              val key = String.substring (s, i + msz, j - i - msz)
              val () =
                if null knownEntries orelse knownEntry key then ()
                else
                  die ("smdpp: \\refentry{" ^ key ^ "} in " ^
                       currentFile ^ " has no matching " ^
                       "help/Docfiles/" ^ key ^ ".smd")
              (* Path is relative to the current book's output dir.
                 From book/<Book>/<chapter>.html, ../Reference/X.html
                 resolves to book/Reference/X.html -- works uniformly
                 across all books, including Reference itself
                 (../Reference/X.html from book/Reference/Y.html is
                 still book/Reference/X.html). *)
              val replacement =
                  "[`" ^ key ^ "`](../Reference/" ^ key ^ ".html)"
            in
              loop (j + 1, List.revAppend
                             (String.explode replacement, acc))
            end
      else loop (i + 1, sub (s, i) :: acc)
  in loop (0, []) end

(* Replace each `\cite[loc]{keys}` / `\citet[loc]{keys}` with the
   rendered-HTML span captured in the citation label registry, keyed
   by form so the textual and parenthetical renderings of the same
   key stay distinct.  Unknown call-sites are left untouched: the
   rendered HTML keeps the literal `\cite{...}` text, which
   `smdpp check-html` then reports as a leak.  Brace-counted on the
   key argument; loose `]`-terminator on the locator (LaTeX locators
   never contain literal `]`). *)
fun rewriteCites s =
  let
    val sub = String.sub
    val sz = String.size s
    fun lookup keys locator form =
      List.find (fn (k, l, f, _) =>
                   k = keys andalso l = locator andalso f = form)
                (!citeLabels)
    fun loop (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else
        case detectCite (s, i, sz) of
            SOME (form, k) =>
              let
                val (locator, afterLoc) =
                  if k < sz andalso sub (s, k) = #"[" then
                    let
                      fun findRBrack j =
                        if j >= sz then NONE
                        else if sub (s, j) = #"]" then SOME j
                        else findRBrack (j + 1)
                    in
                      case findRBrack (k + 1) of
                          SOME e =>
                            (String.substring (s, k + 1, e - k - 1), e + 1)
                        | NONE => ("", k)
                    end
                  else ("", k)
              in
                if afterLoc < sz andalso sub (s, afterLoc) = #"{" then
                  case findCloseBrace (s, afterLoc + 1) of
                      NONE => loop (i + 1, sub (s, i) :: acc)
                    | SOME e =>
                      let
                        val keys =
                          String.substring
                            (s, afterLoc + 1, e - afterLoc - 1)
                      in
                        case lookup keys locator form of
                            SOME (_, _, _, html) =>
                              loop (e + 1,
                                    List.revAppend
                                      (String.explode html, acc))
                          | NONE => loop (i + 1, sub (s, i) :: acc)
                      end
                else loop (i + 1, sub (s, i) :: acc)
              end
          | NONE => loop (i + 1, sub (s, i) :: acc)
  in loop (0, []) end

(* Replace each `\ref{X}` with a markdown link `[N.M.O](url)` where
   N.M.O is the formatted section number recorded for X in the
   label registry and `url` points to the heading-anchor in the
   chapter where X was defined (omitting the file prefix when the
   ref is to the current chapter).  Unknown labels are stripped
   silently. *)
fun resolveRefs {currentFile, labelRegistry} s =
  let
    val sub = String.sub
    val sz = String.size s
    val prefix = "\\ref{"
    val psz = String.size prefix
    fun localLookup lbl =
      List.find (fn (l, _, _, _) => l = lbl) labelRegistry
    (* Split "Book:label" if the prefix matches a known sibling
       book name.  Returns SOME (book, label) only for known book
       names so labels with legitimate `:` content (rare but
       legal) aren't false-positively split. *)
    fun splitBookPrefix lbl =
      case String.fields (fn c => c = #":") lbl of
          [book, rest] =>
            if List.exists (fn b => b = book) knownSiblingBooks
            then SOME (book, rest)
            else NONE
        | _ => NONE
    fun crossLookup book lbl =
      List.find
        (fn (b, l, _, _, _) => b = book andalso l = lbl)
        (!crossBookLabels)
    fun lookup lbl =
      case splitBookPrefix lbl of
          SOME (book, sublbl) =>
            (case crossLookup book sublbl of
                 SOME (_, _, file, anchor, num) =>
                   SOME ("../" ^ book ^ "/" ^ toHtml file, anchor, num)
               | NONE => NONE)
        | NONE =>
            (case localLookup lbl of
                 SOME (_, file, anchor, num) =>
                   SOME (if file = currentFile then ""
                         else toHtml file,
                         anchor, num)
               | NONE => NONE)
    fun loop (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else if i + psz <= sz andalso
              String.substring (s, i, psz) = prefix
      then
        case findCloseBrace (s, i + psz) of
            NONE => loop (i+1, sub (s, i) :: acc)
          | SOME j =>
            let
              val lbl = String.substring (s, i + psz, j - i - psz)
              val replacement =
                  case lookup lbl of
                      SOME (pageUrl, anchor, num) =>
                        "[" ^ num ^ "](" ^ pageUrl ^ "#" ^ anchor ^ ")"
                    | NONE => ""
            in
              loop (j+1, List.revAppend
                           (String.explode replacement, acc))
            end
      else loop (i+1, sub (s, i) :: acc)
  in loop (0, []) end

(* Stage 1: run polyscripter and the LaTeX-source strippers that
   don't touch \label/\ref.  The scan pass walks this output to
   build the label registry.  handleRawBlocks is deferred to stage 2
   so scanLabels can still see `\input{X}` lines living inside
   `{=latex}` raw blocks — those mark the source positions where
   mdbook slots in sub-file sub-sections, and scanLabels needs them
   to keep sub-section numbers aligned with SUMMARY.md. *)
fun preprocessStage1 obuf s =
  s |> dropFrontmatter
    |> runScripted obuf
    |> stripIndex

(* Stage 2: with the registry in hand, resolve \ref{X} to a
   markdown link, then drop the (now-redundant) \label{X} marks
   and finish the markdown-side rewrites. *)
fun preprocessStage2 {labelRegistry, currentFile, name} s =
  s |> handleRawBlocks
    |> resolveRefs {currentFile = currentFile,
                    labelRegistry = labelRegistry}
    |> stripLabel
    |> rewriteRefEntry currentFile
    |> rewriteCites
    |> convertSuperscripts
    |> protectMath
    |> ensureH1 name

(* GitHub-style heading slugger: lowercase, drop punctuation other
   than space/`-`/`_`, replace spaces with `-`, collapse multiple
   `-`s, trim.  Approximates pulldown-cmark's heading-id rule. *)
(* UTF-8 codepoint at byte offset i in s.  Returns (codepoint, nBytes).
   Malformed bytes are passed through as Latin-1 codepoints. *)
fun utf8Decode s i =
  let
    val slen = String.size s
    val b0 = Char.ord (String.sub (s, i))
    fun cont k =
      if i + k < slen
      then Char.ord (String.sub (s, i + k)) - 0x80
      else 0
  in
    if b0 < 0x80 then (b0, 1)
    else if b0 < 0xC0 then (b0, 1)
    else if b0 < 0xE0 then ((b0 - 0xC0) * 64 + cont 1, 2)
    else if b0 < 0xF0 then
      ((b0 - 0xE0) * 4096 + cont 1 * 64 + cont 2, 3)
    else
      ((b0 - 0xF0) * 262144 + cont 1 * 4096 +
       cont 2 * 64 + cont 3, 4)
  end

(* Approximation of Unicode general category L* (letters), covering
   the ranges the HOL manuals actually use in heading text.  Letters
   outside these ranges (CJK, Arabic, ...) would be dropped, but
   none appear in the manual so a fuller table isn't justified. *)
fun isUnicodeLetter cp =
  (cp >= 0xC0 andalso cp <= 0xFF
       andalso cp <> 0xD7 andalso cp <> 0xF7) orelse  (* Latin-1 *)
  (cp >= 0x0100 andalso cp <= 0x024F) orelse          (* Latin Ext-A/B *)
  (cp >= 0x0370 andalso cp <= 0x03FF                  (* Greek *)
       andalso cp <> 0x0374 andalso cp <> 0x0375
       andalso cp <> 0x037E andalso cp <> 0x0387) orelse
  (cp >= 0x0400 andalso cp <= 0x04FF)                 (* Cyrillic *)

(* Mirrors pulldown-cmark / mdbook's normalize_id: keep Unicode
   letters and digits, `_`, `-`; convert ASCII whitespace to `-`;
   lowercase ASCII letters; leave non-ASCII letters as-is (good
   enough -- the manual's only non-ASCII letter is `ý`, already
   lowercase in source).  Strip leading/trailing dashes; don't
   collapse consecutive ones (pulldown-cmark keeps them, e.g.
   "Foo — Bar" → "foo--bar", and any mismatch breaks anchor
   resolution). *)
fun slugify text =
  let
    val tlen = String.size text
    val buf = ref ([] : char list)
    fun emitByte b = buf := b :: !buf
    fun emitRange i n =
      let fun loop k =
            if k >= n then ()
            else (emitByte (String.sub (text, i + k)); loop (k + 1))
      in loop 0 end
    fun walk i =
      if i >= tlen then ()
      else
        let val (cp, n) = utf8Decode text i
        in
          if cp < 128 then
            let val c = Char.chr cp
                val () =
                  if Char.isAlphaNum c orelse c = #"-" orelse c = #"_"
                  then emitByte (Char.toLower c)
                  else if c = #" " orelse c = #"\t" then emitByte #"-"
                  else ()
            in walk (i + 1) end
          else
            (if isUnicodeLetter cp then emitRange i n else ();
             walk (i + n))
        end
    val () = walk 0
    val ss = Substring.full (String.implode (List.rev (!buf)))
    val ss = Substring.dropl (fn c => c = #"-") ss
    val ss = Substring.dropr (fn c => c = #"-") ss
  in
    Substring.string ss
  end

(* Strip inline markdown formatting from heading text before slugging.
   We drop *, _, ` (emphasis/code), and skip $...$ inline math.  This
   is best-effort and matches what most heading text looks like. *)
fun cleanHeading s =
  let
    val sub = String.sub
    val sz = String.size s
    fun loop (i, acc, inMath) =
      if i >= sz then String.implode (List.rev acc)
      else
        let val c = sub (s, i)
        in
          if inMath then
            if c = #"$" then loop (i+1, acc, false)
            else loop (i+1, acc, inMath)
          else
            case c of
                #"$" => loop (i+1, acc, true)
              | #"*" => loop (i+1, acc, inMath)
              | #"`" => loop (i+1, acc, inMath)
              | #"\\" =>
                  (* skip a LaTeX command name following the backslash *)
                  let
                    fun skipLetters j =
                      if j >= sz orelse not (Char.isAlpha (sub (s, j)))
                      then j
                      else skipLetters (j + 1)
                    val j = skipLetters (i + 1)
                  in
                    loop (if j = i + 1 then i + 2 else j, acc, inMath)
                  end
              | _ => loop (i+1, c :: acc, inMath)
        end
  in
    loop (0, [], false)
  end

(* Canonical heading-text → mdbook-anchor: strip emphasis/math
   noise, then slugify to match what pulldown-cmark assigns. *)
val headingAnchor = slugify o cleanHeading

(* Return the markdown heading level of a line ("# " → 1, ... up
   to "#### " → 4) or NONE if it isn't a heading. *)
fun headingLevel ln =
  if String.isPrefix "#### " ln then SOME 4
  else if String.isPrefix "### " ln then SOME 3
  else if String.isPrefix "## " ln then SOME 2
  else if String.isPrefix "# " ln then SOME 1
  else NONE

(* Drop the leading #s and following whitespace of a heading line. *)
fun headingBody ln =
  let
    val ss = Substring.full ln
    val ss = Substring.dropl (fn c => c = #"#") ss
  in
    Substring.string (Substring.dropl Char.isSpace ss)
  end

(* Extract heading slugs from markdown content. *)
fun extractAnchors content =
  let
    val lines = String.fields (fn c => c = #"\n") content
    fun loop ([], acc) = List.rev acc
      | loop (l :: rest, acc) =
          case headingLevel l of
              NONE => loop (rest, acc)
            | SOME _ => loop (rest, headingAnchor (headingBody l) :: acc)
  in
    loop (lines, [])
  end

(* Walk a chapter's content tracking heading levels, and return
   one entry per `\label{X}` found.  Each entry is

       (label, chapter_file, heading_anchor, formatted_number)

   where `formatted_number` is "N", "N.M", "N.M.O", or "N.M.O.P"
   depending on how deeply nested the surrounding heading was.
   We also auto-register each heading's own slug as a label, so
   `\ref{slug}` resolves the way pandoc would (pandoc emits an
   implicit `\label{slug}` for every section).

   The chapter name seeds the anchor for labels that appear
   *before* any heading (e.g. on the H1 line of a chapter that
   ensureH1 will synthesise). *)
(* `chapterPrefix` is the canonical mdbook section number for the
   chapter (e.g. [8] for a top-level chapter, [8, 5] for a sub-file
   slotted at SUMMARY.md position 8.5).  Internal sub-section
   numbering (s2, s3, s4 below) appends to this prefix.

   `titleLvl = length chapterPrefix` tells scanLabels which heading
   level corresponds to the chapter's own title — H1 for top-level
   chapters, H2 for sub-files.  Headings one level deeper bump s2,
   then s3, then s4.

   On top-level chapters whose source `\input{X}`s an existing
   `X.smd` sub-file, the `\input{}` occupies one slot in the parent
   chapter's sub-section numbering even though it carries no H2 of
   its own.  scanLabels bumps s2 at such lines so that later H2s
   line up with the SUMMARY.md positions mdbook will assign them. *)
fun scanLabels chapterPrefix chapterFile chapterName content =
  let
    val lines = String.fields (fn c => c = #"\n") content
    val titleLvl = List.length chapterPrefix
    (* Mirror pulldown-cmark's per-page heading-id rule: when the
       same base slug appears more than once in a chapter's content,
       the Nth (1-indexed N>1) occurrence gets `-N-1` appended.

       For sub-files (titleLvl > 1) whose content has no heading at
       all, smdpp's ensureH1 will prepend `# <chapterName>` (an H1
       whose slug matches chapterName).  In that case seed seenSlugs
       so any subsequent body heading with the same slug picks up
       the `-1` suffix that pulldown-cmark will assign.

       For sub-files whose content already starts at H2 (the common
       case, e.g. HolSat.smd's `## The HolSat Library`), ensureH1
       doesn't prepend anything -- the H2 is the page's first
       heading and gets the un-disambiguated slug.  No seeding. *)
    val seenSlugs = ref ([] : (string * int) list)
    val () =
        if titleLvl > 1 andalso not (hasHeading content) then
          seenSlugs := [(headingAnchor chapterName, 1)]
        else ()
    fun nextSlug raw =
      let
        val cnt =
            case List.find (fn (s, _) => s = raw) (!seenSlugs) of
                SOME (_, n) => n
              | NONE => 0
        val s = if cnt = 0 then raw
                else raw ^ "-" ^ Int.toString cnt
        val () = seenSlugs :=
                   (raw, cnt + 1) ::
                   List.filter (fn (s, _) => s <> raw) (!seenSlugs)
      in s end
    (* The slug for a heading is computed *after* stripping any
       inline \label{}/\ref{} from the heading text. *)
    fun headingSlug ln =
      let
        val body = headingBody ln
        val body = stripCmd "label" body
        val body = stripCmd "ref" body
      in nextSlug (headingAnchor body) end
    (* Find every `\label{X}` on a line; brace-counted body. *)
    val labelPrefix = "\\label{"
    val psz = String.size labelPrefix
    fun findLabels ln =
      let
        val sz = String.size ln
        fun loop (i, acc) =
          if i >= sz then List.rev acc
          else if i + psz <= sz andalso
                  String.substring (ln, i, psz) = labelPrefix
          then
            case findCloseBrace (ln, i + psz) of
                NONE => List.rev acc
              | SOME j =>
                  let val lbl = String.substring (ln, i + psz, j - i - psz)
                  in loop (j+1, lbl :: acc) end
          else loop (i+1, acc)
      in loop (0, []) end
    (* Detect `\input{X}` lines; return the brace body, otherwise
       NONE.  Used to spot sub-file insertion points. *)
    val inputMarker = "\\input{"
    val ipsz = String.size inputMarker
    fun findInputStem ln =
      let
        val sz = String.size ln
        fun loop i =
          if i + ipsz > sz then NONE
          else if String.substring (ln, i, ipsz) = inputMarker
          then case findCloseBrace (ln, i + ipsz) of
                   NONE => NONE
                 | SOME j =>
                     SOME (String.substring
                             (ln, i + ipsz, j - i - ipsz))
          else loop (i + 1)
      in loop 0 end
    fun stripDotTex s =
      if String.isSuffix ".tex" s
      then String.substring (s, 0, String.size s - 4)
      else s
    fun isSubfileInput ln =
      case findInputStem ln of
          SOME raw =>
            let val stem = stripDotTex raw
            in OS.FileSys.access (stem ^ ".smd", [OS.FileSys.A_READ]) end
        | NONE => false
    (* Format `chapterPrefix @ tail` joined by `.`, where `tail`
       drops trailing zeros from (s2, s3, s4). *)
    fun fmtNumber (s2, s3, s4) =
      let
        val tail = if s2 = 0 then []
                   else if s3 = 0 then [s2]
                   else if s4 = 0 then [s2, s3]
                   else [s2, s3, s4]
      in
        String.concatWith "."
          (List.map Int.toString (chapterPrefix @ tail))
      end
    val initAnchor = headingAnchor chapterName
    (* state = (anchor-for-labels-on-this-line, s2, s3, s4).
       Heading-level effects depend on the heading's offset from
       `titleLvl`: offset 0 is the chapter title (reset internal
       counters), offset 1..3 bump s2/s3/s4.  An `\input{X.smd}`
       line acts like an offset-1 heading without an anchor. *)
    fun loop ([], _, acc) = List.rev acc
      | loop (ln :: rest, state as (_, s2, s3, s4), acc) =
          let
            val lvl = headingLevel ln
            val state' =
                case lvl of
                    SOME h_lvl =>
                      let val offset = h_lvl - titleLvl
                      in
                        if offset = 0 then (headingSlug ln, 0, 0, 0)
                        else if offset = 1 then (headingSlug ln, s2 + 1, 0, 0)
                        else if offset = 2 then (headingSlug ln, s2, s3 + 1, 0)
                        else if offset = 3 then (headingSlug ln, s2, s3, s4 + 1)
                        else state
                      end
                  | NONE =>
                      if titleLvl = 1 andalso isSubfileInput ln
                      then let val (anchor, _, _, _) = state
                           in (anchor, s2 + 1, 0, 0) end
                      else state
            val (anchor', s2', s3', s4') = state'
            val numStr = fmtNumber (s2', s3', s4')
            val acc =
                case lvl of
                    SOME _ => (anchor', chapterFile, anchor', numStr) :: acc
                  | NONE => acc
            val acc =
                foldl (fn (lbl, a) =>
                          (lbl, chapterFile, anchor', numStr) :: a)
                      acc (findLabels ln)
          in
            loop (rest, state', acc)
          end
  in
    loop (lines, (initAnchor, 0, 0, 0), [])
  end

(* Rewrite `[text](#anchor)` in content so that anchors not present in
   `localAnchors` get prefixed with the chapter file they live in.
   Anchors not found anywhere are left as-is. *)
fun rewriteLinks {localAnchors, registry} content =
  let
    val sub = String.sub
    val sz = String.size content
    fun lookup anchor =
      List.find (fn (a, _) => a = anchor) registry
    fun emit acc s = String.implode (List.rev acc) ^ s
    (* Find the matching `)` for `(` at position i; bracket counting. *)
    fun findClose (i, depth) =
      if i >= sz then NONE
      else case sub (content, i) of
              #")" => if depth = 1 then SOME i
                      else findClose (i+1, depth-1)
            | #"(" => findClose (i+1, depth+1)
            | _ => findClose (i+1, depth)
    fun loop (i, acc) =
      if i >= sz then String.implode (List.rev acc)
      else
        let val c = sub (content, i)
        in
          if c = #"]" andalso i + 1 < sz andalso
             sub (content, i+1) = #"(" andalso
             i + 2 < sz andalso sub (content, i+2) = #"#"
          then
            (* `](#...)` — a relative anchor link.  Find closing `)`. *)
            case findClose (i+2, 1) of
                NONE => loop (i+1, c :: acc)
              | SOME j =>
                let
                  val anchor = String.substring (content, i+3, j - i - 3)
                  (* When `anchor` matches the base of the resolved
                     file (one of the chapter-base registry entries
                     added in finalizeChapter), drop the fragment:
                     the link is just "go to that entry's page", and
                     the entry's H2 doesn't carry the literal anchor
                     (pulldown-cmark slugifies it differently).  This
                     keeps `smdpp check-html` quiet and is functionally
                     identical for the reader -- the browser scrolls
                     to the top of the page either way. *)
                  fun stemOf f =
                    #base (OS.Path.splitBaseExt f)
                  val replacement =
                      if List.exists (fn a => a = anchor) localAnchors
                      then "](#" ^ anchor ^ ")"
                      else case lookup anchor of
                              SOME (_, file) =>
                                if stemOf file = anchor
                                then "](" ^ toHtml file ^ ")"
                                else "](" ^ toHtml file ^ "#" ^ anchor ^ ")"
                            | NONE => "](#" ^ anchor ^ ")"
                  val acc' = List.revAppend
                               (String.explode replacement, acc)
                in
                  loop (j+1, acc')
                end
          else loop (i+1, c :: acc)
        end
  in
    loop (0, [])
  end

(* ===== book walker =====
   mdbook Book JSON shape:
     { "items": [ <Item>, ... ], "__non_exhaustive": null }
   where <Item> is one of:
     {"Chapter": {"name":..., "content":..., "sub_items":[...], ...}}
     {"Separator": null}
     {"PartTitle": "..."}

   We walk the book in three passes:

     scan      Run polyscripter + initial stripping on every
               chapter, assign a chapter number to each top-level
               Chapter with content, and harvest `\label{X}` calls
               into a label registry.
     finalize  Use the registry to resolve `\ref{X}` to markdown
               links, finish the rest of the markdown rewrites,
               and harvest the resulting heading anchors.
     rewrite   Rewrite cross-chapter `[text](#anchor)` links so
               they pick up the chapter-file prefix.              *)

fun stringField k fields =
  case List.find (fn (k', _) => k = k') fields of
      SOME (_, JSON.STRING s) => SOME s
    | _ => NONE

fun chapterName fields = Option.getOpt (stringField "name" fields, "")
fun chapterPath fields = stringField "path" fields
(* The `number` field is mdbook's canonical section path for the
   chapter — `[8]` for a top-level chapter, `[8, 5]` for a sub-file
   at SUMMARY.md position 8.5, and so on.  Returns NONE only for
   unnumbered chapters (prefix-/suffix-chapters, separators); for
   our manual every Chapter we care about is numbered. *)
fun chapterNumber fields =
  case List.find (fn (k, _) => k = "number") fields of
      SOME (_, JSON.ARRAY xs) =>
        let
          fun toInt (JSON.INT i) = SOME (IntInf.toInt i)
            | toInt _ = NONE
          val ints = List.mapPartial toInt xs
        in
          if List.length ints = List.length xs
          then SOME ints else NONE
        end
    | _ => NONE

(* --- Pass 1: scan ---
   Run polyscripter + the LaTeX-source strippers on every chapter,
   read each chapter's `number` straight from mdbook's JSON, and
   harvest its `\label{X}` calls into the registry. *)

fun scanChapter obuf chap labelReg =
  case chap of
      JSON.OBJECT fields =>
        let
          val name = chapterName fields
          val pathOpt = chapterPath fields
          val prefix = Option.getOpt (chapterNumber fields, [])
          val (newContent, labelReg) =
              case (stringField "content" fields, pathOpt) of
                  (SOME s, SOME p) =>
                    let
                      val s' = preprocessStage1 obuf s
                      val labels = scanLabels prefix p name s'
                    in (SOME s', labelReg @ labels) end
                | (SOME s, NONE) =>
                    (SOME (preprocessStage1 obuf s), labelReg)
                | _ => (NONE, labelReg)
          val (newSubItems, labelReg) =
              case List.find (fn (k, _) => k = "sub_items") fields of
                  SOME (_, JSON.ARRAY xs) =>
                    let
                      fun loop ([], acc, reg) = (List.rev acc, reg)
                        | loop (item :: rest, acc, reg) =
                            let val (item', reg') =
                                    scanItem obuf item reg
                            in loop (rest, item' :: acc, reg') end
                      val (xs', reg') = loop (xs, [], labelReg)
                    in (SOME (JSON.ARRAY xs'), reg') end
                | _ => (NONE, labelReg)
          fun trField ("content", _) =
                (case newContent of
                     SOME s => ("content", JSON.STRING s)
                   | NONE => ("content", JSON.NULL))
            | trField ("sub_items", _) =
                (case newSubItems of
                     SOME v => ("sub_items", v)
                   | NONE => ("sub_items", JSON.ARRAY []))
            | trField kv = kv
        in
          (JSON.OBJECT (map trField fields), labelReg)
        end
    | _ => (chap, labelReg)
and scanItem obuf item labelReg =
  case item of
      JSON.OBJECT [("Chapter", chap)] =>
        let val (chap', reg') = scanChapter obuf chap labelReg
        in (JSON.OBJECT [("Chapter", chap')], reg') end
    | _ => (item, labelReg)

(* --- Pass 2: finalize ---
   With the label registry in hand, resolve `\ref{X}` to markdown
   links, finish the markdown rewrites, and harvest heading anchors
   so pass 3 can rewrite cross-chapter `[text](#anchor)` links. *)

fun finalizeChapter labelRegistry chap anchorReg =
  case chap of
      JSON.OBJECT fields =>
        let
          val name = chapterName fields
          val pathOpt = chapterPath fields
          val (newContent, anchorReg) =
              case (stringField "content" fields, pathOpt) of
                  (SOME s, SOME p) =>
                    let
                      val s' = preprocessStage2
                                 {labelRegistry = labelRegistry,
                                  currentFile = p, name = name} s
                      val anchors = extractAnchors s'
                      (* Reference entries (e.g. `Foo.bar.smd`) carry
                         their entry name in the filename; their bodies
                         link to other entries via `#Foo.bar`-style
                         same-page anchors -- a CommonMark fiction that
                         "works" only when the whole reference manual
                         is one big concatenated page (the legacy PDF
                         path).  Under mdbook, where each entry is its
                         own page, we register the chapter's filename
                         base as an extra anchor pointing at the
                         chapter itself, so rewriteLinks redirects
                         `](#Foo.bar)` to `](Foo.bar.html#Foo.bar)`.
                         Browsers resolve the missing fragment by
                         scrolling to the top of the page -- which is
                         the entry. *)
                      val {base, ...} = OS.Path.splitBaseExt p
                    in
                      (SOME s',
                       anchorReg @ map (fn a => (a, p)) anchors
                                 @ [(base, p)])
                    end
                | (SOME s, NONE) =>
                    (SOME (preprocessStage2
                             {labelRegistry = labelRegistry,
                              currentFile = "", name = name} s),
                     anchorReg)
                | _ => (NONE, anchorReg)
          val (newSubItems, anchorReg) =
              case List.find (fn (k, _) => k = "sub_items") fields of
                  SOME (_, JSON.ARRAY xs) =>
                    let
                      fun loop ([], acc, reg) = (List.rev acc, reg)
                        | loop (item :: rest, acc, reg) =
                            let val (item', reg') =
                                  finalizeItem labelRegistry item reg
                            in loop (rest, item' :: acc, reg') end
                      val (xs', reg') = loop (xs, [], anchorReg)
                    in (SOME (JSON.ARRAY xs'), reg') end
                | _ => (NONE, anchorReg)
          fun trField ("content", _) =
                (case newContent of
                     SOME s => ("content", JSON.STRING s)
                   | NONE => ("content", JSON.NULL))
            | trField ("sub_items", _) =
                (case newSubItems of
                     SOME v => ("sub_items", v)
                   | NONE => ("sub_items", JSON.ARRAY []))
            | trField kv = kv
        in
          (JSON.OBJECT (map trField fields), anchorReg)
        end
    | _ => (chap, anchorReg)
and finalizeItem labelRegistry item anchorReg =
  case item of
      JSON.OBJECT [("Chapter", chap)] =>
        let val (chap', reg') =
                finalizeChapter labelRegistry chap anchorReg
        in (JSON.OBJECT [("Chapter", chap')], reg') end
    | _ => (item, anchorReg)

(* --- Pass 3: rewrite cross-chapter [text](#anchor) links --- *)

fun rewriteChapter registry chap =
  case chap of
      JSON.OBJECT fields =>
        let
          (* Anchors local to this chapter = those in the registry
             pointing at this chapter's path.  Avoids a second
             `extractAnchors` pass on the content.

             Exclude the chapter's own filename-base entry (added by
             finalizeChapter for cross-chapter resolution): without
             this exclusion a Reference entry's "See also" link to
             itself by name (`#Foo.bar` inside `Foo.bar.smd`) would
             match localAnchors and stay as a broken `#Foo.bar`
             same-page link instead of falling through to the
             registry lookup that drops the fragment. *)
          val localAnchors =
              case chapterPath fields of
                  SOME p =>
                    let val baseOfP = #base (OS.Path.splitBaseExt p)
                    in
                      List.mapPartial
                        (fn (a, f) =>
                            if f = p andalso a <> baseOfP
                            then SOME a else NONE)
                        registry
                    end
                | NONE => []
          fun trField ("content", JSON.STRING s) =
                ("content",
                 JSON.STRING (rewriteLinks
                                {localAnchors = localAnchors,
                                 registry = registry}
                                s))
            | trField ("sub_items", JSON.ARRAY xs) =
                ("sub_items",
                 JSON.ARRAY (map (rewriteItem registry) xs))
            | trField kv = kv
        in
          JSON.OBJECT (map trField fields)
        end
    | _ => chap
and rewriteItem registry item =
  case item of
      JSON.OBJECT [("Chapter", chap)] =>
        JSON.OBJECT [("Chapter", rewriteChapter registry chap)]
    | _ => item

fun transformBook obuf book =
  case book of
      JSON.OBJECT fields =>
        let
          fun scanItems xs =
              let
                fun loop ([], acc, reg) = (List.rev acc, reg)
                  | loop (item :: rest, acc, reg) =
                      let val (item', reg') =
                              scanItem obuf item reg
                      in loop (rest, item' :: acc, reg') end
              in loop (xs, [], []) end
          fun finalizeItems labelReg xs =
              let
                fun loop ([], acc, reg) = (List.rev acc, reg)
                  | loop (item :: rest, acc, reg) =
                      let val (item', reg') =
                              finalizeItem labelReg item reg
                      in loop (rest, item' :: acc, reg') end
              in loop (xs, [], []) end
          fun trField ("items", JSON.ARRAY xs) =
                let
                  val (xs1, labelReg)  = scanItems xs
                  val (xs2, anchorReg) = finalizeItems labelReg xs1
                  val xs3 = map (rewriteItem anchorReg) xs2
                in
                  ("items", JSON.ARRAY xs3)
                end
            | trField kv = kv
        in
          JSON.OBJECT (map trField fields)
        end
    | _ => book

(* ===== check-refs sub-command =====

   Cross-check a rendered mdbook output directory: for every
   `<a href="page.html#anchor">N.M.O</a>` link, verify the displayed
   N.M.O matches the section number the target heading actually
   carries.  Catches the class of regression where smdpp's section
   numbering drifts from mdbook's interleaved sidebar numbering
   (the hyperlink lands at the right anchor but the displayed
   number is stale).

   Build a {(page, anchor) -> number} map by reading toc.html for
   chapter prefixes and sidebar entries, then walking each page's
   <hN id="X"> headings in DOM order to derive numbers for deeper
   levels the sidebar doesn't enumerate. *)

fun strFindFrom needle haystack start =
  let
    val nlen = String.size needle
    val hlen = String.size haystack
    fun loop i =
      if i + nlen > hlen then NONE
      else if String.substring (haystack, i, nlen) = needle
      then SOME i
      else loop (i + 1)
  in loop start end

fun readUntilChar stop haystack start =
  let
    val hlen = String.size haystack
    fun loop i =
      if i >= hlen orelse String.sub (haystack, i) = stop
      then (String.substring (haystack, start, i - start), i)
      else loop (i + 1)
  in loop start end

fun parseSecNum s =
  List.mapPartial Int.fromString
    (String.tokens (fn c => c = #".") s)

fun fmtSecNum xs = String.concatWith "." (map Int.toString xs)

fun trimSpace s =
  let val ss = Substring.full s
      val ss = Substring.dropl Char.isSpace ss
      val ss = Substring.dropr Char.isSpace ss
  in Substring.string ss end

fun readFileAll path =
  let val ins = TextIO.openIn path
      val s = TextIO.inputAll ins
      val () = TextIO.closeIn ins
  in s end

(* Walk toc.html.  For each chapter-item LI, find the strong-tagged
   section number, the title text, and any preceding <a href> that
   marks the entry as a real page.  Track descendantPage[depth] so
   draft chapters resolve to their parent's page rather than
   accidentally inheriting a sibling sub-file's page. *)
fun parseSidebarTOC tocHtml =
  let
    val liMarker = "<li class=\"chapter-item"
    val strongMarker = "<strong aria-hidden=\"true\">"
    val hrefMarker = " href=\""
    val pagePrefix = ref ([] : (string * int list) list)
    val sidebarAnchor = ref ([] : ((string * string) * string) list)
    val descendantPage = ref ([] : (int * string option) list)
    fun setDescendant d p =
      descendantPage := (d, p) ::
        List.filter (fn (d', _) => d' <> d) (!descendantPage)
    fun dropDeeper d =
      descendantPage :=
        List.filter (fn (d', _) => d' <= d) (!descendantPage)
    fun lookupDescendant d =
      case List.find (fn (d', _) => d' = d) (!descendantPage) of
          SOME (_, p) => p
        | NONE => NONE
    fun walk pos =
      case strFindFrom liMarker tocHtml pos of
          NONE => ()
        | SOME liPos =>
          let
            val liEnd = Option.getOpt
                          (strFindFrom "</li>" tocHtml liPos,
                           String.size tocHtml)
            val strongPos =
              case strFindFrom strongMarker tocHtml liPos of
                  NONE => NONE
                | SOME sp =>
                    if sp < liEnd then SOME sp else NONE
          in
            case strongPos of
                NONE => walk (liPos + String.size liMarker)
              | SOME sp =>
                let
                  val numStart = sp + String.size strongMarker
                  val (numText, numTextEnd) =
                    readUntilChar #"<" tocHtml numStart
                  val numTrimmed =
                    if String.size numText > 0 andalso
                       String.sub (numText, String.size numText - 1) = #"."
                    then String.substring (numText, 0, String.size numText - 1)
                    else numText
                  val nums = parseSecNum numTrimmed
                  val depth = List.length nums
                  val afterStrong =
                    Option.getOpt
                      (strFindFrom "</strong>" tocHtml numTextEnd,
                       numTextEnd)
                  val titleStart = afterStrong + String.size "</strong>"
                  val (titleRaw, titleEnd) =
                    readUntilChar #"<" tocHtml titleStart
                  val title = trimSpace titleRaw
                  val ownPage =
                    case strFindFrom hrefMarker tocHtml liPos of
                        NONE => NONE
                      | SOME hp =>
                          if hp >= sp then NONE
                          else
                            let val hs = hp + String.size hrefMarker
                                val (hv, _) = readUntilChar #"\"" tocHtml hs
                            in SOME hv end
                  val () =
                    case ownPage of
                        SOME p =>
                          (pagePrefix := (p, nums) :: !pagePrefix;
                           setDescendant depth (SOME p))
                      | NONE =>
                          setDescendant depth
                            (if depth > 1 then lookupDescendant (depth - 1)
                             else NONE)
                  val () = dropDeeper depth
                  val resolvedPage =
                    case ownPage of
                        SOME p => SOME p
                      | NONE =>
                          if depth > 1 then lookupDescendant (depth - 1)
                          else NONE
                  val () =
                    case resolvedPage of
                        SOME p =>
                          sidebarAnchor :=
                            ((p, slugify title), numTrimmed) ::
                            !sidebarAnchor
                      | NONE => ()
                in walk titleEnd end
          end
    val () = walk 0
  in (!pagePrefix, !sidebarAnchor) end

(* Walk an HTML file's <hN id="X"> tags in DOM order; for each,
   assign the section number smdpp would record.  Sidebar entries
   are trusted at the right level (so interleaved sub-files line
   up); deeper levels fall back to a per-page counter.  When a
   sidebar slug collides with a heading at a different DOM level
   (pulldown-cmark's `-N` suffix mechanic), the level mismatch is
   detected and the counter takes over. *)
fun parsePageHeadingsImpl prefix sidebarForPage pageHtml =
  let
    val titleLvl = List.length prefix
    val maxLevel = titleLvl + 3
    val prefixStr = fmtSecNum prefix
    val seen = ref ([] : (string * string) list)
    val pathRef = ref ([] : int list)
    fun currentNum () = fmtSecNum (prefix @ !pathRef)
    val hlen = String.size pageHtml
    fun findHeading start =
      let
        fun loop i =
          if i + 5 > hlen then NONE
          else if String.sub (pageHtml, i) = #"<"
                  andalso String.sub (pageHtml, i + 1) = #"h"
                  andalso Char.isDigit (String.sub (pageHtml, i + 2))
                  andalso let val c = String.sub (pageHtml, i + 3)
                          in c = #" " orelse c = #"\t" end
          then
            let
              val hLvl = Char.ord (String.sub (pageHtml, i + 2)) -
                         Char.ord #"0"
              val tagEnd = Option.getOpt
                             (strFindFrom ">" pageHtml i, hlen)
              val idPos = strFindFrom " id=\"" pageHtml i
            in
              case idPos of
                  SOME ip =>
                    if ip < tagEnd andalso hLvl >= 1 andalso hLvl <= 6 then
                      let val ans = ip + String.size " id=\""
                          val (anchor, ane) = readUntilChar #"\"" pageHtml ans
                      in SOME (hLvl, anchor, ane + 1) end
                    else loop (i + 1)
                | NONE => loop (i + 1)
            end
          else loop (i + 1)
      in loop start end
    fun lookupSidebar a =
      case List.find (fn (k, _) => k = a) sidebarForPage of
          SOME (_, v) => SOME v | NONE => NONE
    fun remember (a, n) = seen := (a, n) :: !seen
    fun stepCounter hLvl =
      let
        val targetLen = hLvl - titleLvl
        val truncated =
          if List.length (!pathRef) > targetLen
          then List.take (!pathRef, targetLen)
          else !pathRef
        fun padTo n xs =
          if List.length xs >= n then xs
          else padTo n (xs @ [0])
        val padded = padTo targetLen truncated
        val (rest, last) =
          case List.rev padded of
              x :: r => (List.rev r, x)
            | [] => ([], 0)
        val next = rest @ [last + 1]
      in pathRef := next; fmtSecNum (prefix @ next) end
    fun handleHeading hLvl anchor =
      if hLvl <= titleLvl then
        remember (anchor, prefixStr)
      else
        let
          fun viaCounter () =
            if hLvl > maxLevel
            then remember (anchor, currentNum ())
            else remember (anchor, stepCounter hLvl)
        in
          case lookupSidebar anchor of
              SOME sb =>
                let
                  val sbNums = parseSecNum sb
                  val sbRel = List.length sbNums - List.length prefix
                  val domRel = hLvl - titleLvl
                in
                  if sbRel = domRel then
                    (pathRef := List.drop (sbNums, List.length prefix);
                     remember (anchor, sb))
                  else viaCounter ()
                end
            | NONE => viaCounter ()
        end
    fun loop pos =
      case findHeading pos of
          NONE => ()
        | SOME (hLvl, anchor, nextPos) =>
            (handleHeading hLvl anchor; loop nextPos)
    val () = loop 0
  in !seen end

(* Scan `pageHtml` for <a ...href="X#A"...>TEXT</a> links whose
   TEXT is a section-number pattern, and verify each against
   pageHeadings. *)
fun checkPageRefs selfPage pageHtml pageHeadings =
  let
    val hlen = String.size pageHtml
    val errs = ref ([] : (string * string * string * string) list)
    fun isSecNum s =
      let val cs = String.explode s
      in cs <> [] andalso
         List.all (fn c => Char.isDigit c orelse c = #".") cs andalso
         Char.isDigit (hd cs) andalso Char.isDigit (List.last cs)
      end
    fun lookup page anchor =
      case List.find (fn (p, _) => p = page) pageHeadings of
          NONE => NONE
        | SOME (_, hs) =>
            (case List.find (fn (a, _) => a = anchor) hs of
                 NONE => NONE
               | SOME (_, n) => SOME n)
    fun walk start =
      case strFindFrom "<a " pageHtml start of
          NONE => ()
        | SOME ap =>
          let
            val attrStart = ap + 3
            val tagEnd = Option.getOpt
                           (strFindFrom ">" pageHtml attrStart, hlen)
            val hrefP = strFindFrom " href=\"" pageHtml attrStart
          in
            case hrefP of
                SOME hp =>
                  if hp < tagEnd then
                    let
                      val hs = hp + String.size " href=\""
                      val (hvalue, _) = readUntilChar #"\"" pageHtml hs
                      val (host, anchor) =
                        if hvalue = "" then ("", "")
                        else if String.sub (hvalue, 0) = #"#"
                        then ("", String.extract (hvalue, 1, NONE))
                        else
                          (case String.fields (fn c => c = #"#") hvalue of
                               [h, a] => (h, a)
                             | _ => ("", ""))
                      val aClose = strFindFrom "</a>" pageHtml (tagEnd + 1)
                    in
                      case aClose of
                          NONE => walk (tagEnd + 1)
                        | SOME ac =>
                          let
                            val text =
                              String.substring (pageHtml, tagEnd + 1,
                                                ac - tagEnd - 1)
                            val text' = trimSpace text
                            val page = if host = "" then selfPage else host
                          in
                            if anchor <> "" andalso isSecNum text'
                            then case lookup page anchor of
                                     NONE => ()
                                   | SOME expected =>
                                       if text' <> expected
                                       then errs := (page, anchor, text', expected) :: !errs
                                       else ()
                            else ();
                            walk (ac + 4)
                          end
                    end
                  else walk (tagEnd + 1)
              | NONE => walk (tagEnd + 1)
          end
    val () = walk 0
  in !errs end

(* ===== check-links ===== *)

(* Collect every id="..." (and the JS-rewrite-equivalent name="...")
   attribute value from an HTML string.  Over-collects (scripts, etc.)
   but that only causes false negatives, never false positives. *)
fun collectIdAttrs html =
  let
    val ids = ref ([] : string list)
    fun scan marker pos =
      case strFindFrom marker html pos of
          NONE => ()
        | SOME p =>
            let val start = p + String.size marker
                val (v, eend) = readUntilChar #"\"" html start
            in ids := v :: !ids; scan marker eend end
    val () = scan " id=\"" 0
    val () = scan " name=\"" 0
  in !ids end

(* Collect every <a ... href="X"> from HTML.  We skip <link href="">
   in <head> by requiring the opening "<a " marker. *)
fun collectAnchorHrefs html =
  let
    val hrefs = ref ([] : string list)
    val hlen = String.size html
    fun walk pos =
      case strFindFrom "<a " html pos of
          NONE => ()
        | SOME p =>
            let
              val tagEnd = Option.getOpt
                             (strFindFrom ">" html p, hlen)
              val hpos = strFindFrom " href=\"" html p
            in
              case hpos of
                  SOME hp =>
                    if hp < tagEnd then
                      let val start = hp + 7
                          val (v, eend) = readUntilChar #"\"" html start
                      in hrefs := v :: !hrefs; walk eend end
                    else walk (p + 3)
                | NONE => walk (p + 3)
            end
    val () = walk 0
  in !hrefs end

(* Split "page.html#anchor", "page.html", "#anchor", or "" into
   (pageOpt, anchorOpt). *)
fun splitHref href =
  case String.fields (fn c => c = #"#") href of
      [p] => (if p = "" then NONE else SOME p, NONE)
    | p :: a :: _ =>
        (if p = "" then NONE else SOME p,
         if a = "" then NONE else SOME a)
    | [] => (NONE, NONE)

(* Heuristic: skip hrefs we don't validate -- external schemes,
   pure-asset references (CSS/JS/image/font), the mdbook generated
   print page, and synthetic placeholder hrefs. *)
fun skipHref href =
  let
    fun startsWith pre =
      String.size href >= String.size pre andalso
      String.substring (href, 0, String.size pre) = pre
    fun endsWith suf =
      String.size href >= String.size suf andalso
      String.substring (href, String.size href - String.size suf,
                        String.size suf) = suf
  in
    href = "" orelse href = "#" orelse
    startsWith "http://" orelse startsWith "https://" orelse
    startsWith "mailto:" orelse startsWith "javascript:" orelse
    startsWith "data:" orelse startsWith "//" orelse
    (* Cross-book links from the persistent manual switcher (see
       Manual/theme/index.hbs) leave the current book's directory,
       so they're out of scope for this single-book check; the
       cross-book validator (check-refs-all, future) covers them. *)
    startsWith "../" orelse
    endsWith ".css" orelse endsWith ".js" orelse
    endsWith ".png" orelse endsWith ".svg" orelse
    endsWith ".jpg" orelse endsWith ".jpeg" orelse
    endsWith ".gif" orelse endsWith ".ico" orelse
    endsWith ".woff" orelse endsWith ".woff2" orelse
    endsWith ".ttf" orelse endsWith ".eot" orelse
    endsWith ".json" orelse endsWith ".pdf" orelse
    href = "print.html"
  end

(* Decode the common HTML entities pulldown-cmark emits in heading
   text: &amp; &lt; &gt; &quot; &#NN; (decimal numeric).  Used to
   recover the JS .textContent before slugifying a draft sidebar
   title -- without it, the literal entity characters (`&#92;` etc.)
   feed `9`/`2` into the slug. *)
fun decodeEntities s =
  let
    val slen = String.size s
    val buf = ref ([] : char list)
    fun emit c = buf := c :: !buf
    fun namedEntity name =
      case name of
          "amp" => SOME #"&"
        | "lt" => SOME #"<"
        | "gt" => SOME #">"
        | "quot" => SOME #"\""
        | "apos" => SOME #"'"
        | "nbsp" => SOME #" "
        | _ => NONE
    fun walk i =
      if i >= slen then ()
      else if String.sub (s, i) = #"&" then
        let val semi = strFindFrom ";" s i
        in case semi of
               NONE => (emit #"&"; walk (i + 1))
             | SOME sp =>
                 if sp > i + 1 andalso sp - i <= 12 andalso
                    String.sub (s, i + 1) = #"#"
                 then
                   let val numStart = i + 2
                       val (numStr, base) =
                         if numStart < sp andalso
                            (String.sub (s, numStart) = #"x" orelse
                             String.sub (s, numStart) = #"X")
                         then (String.substring (s, numStart + 1,
                                                 sp - numStart - 1),
                               StringCvt.HEX)
                         else (String.substring (s, numStart,
                                                 sp - numStart),
                               StringCvt.DEC)
                   in case Int.scan base Substring.getc
                          (Substring.full numStr) of
                          SOME (n, _) =>
                            if n > 0 andalso n < 128 then
                              (emit (Char.chr n); walk (sp + 1))
                            else (emit #"&"; walk (i + 1))
                        | NONE => (emit #"&"; walk (i + 1))
                   end
                 else
                   let val name = String.substring (s, i + 1, sp - i - 1)
                   in case namedEntity name of
                          SOME c => (emit c; walk (sp + 1))
                        | NONE => (emit #"&"; walk (i + 1))
                   end
        end
      else (emit (String.sub (s, i)); walk (i + 1))
    val () = walk 0
  in String.implode (List.rev (!buf)) end

(* Walk toc.html, predicting the JS sidebar-rewrite URL for every
   draft <li> (a chapter-item li whose <span class="chapter-link-wrapper">
   first child is <span>, not <a>).
   We mirror what `closest('li')`/wrapper-anchor walking does in the
   browser: track an `<ol>`-nesting level (toc.html uses only
   `<ol class="chapter">` at level 1 and nested `<ol class="section">`
   for deeper levels), and at each level remember the chapter URL of
   the most recently opened chapter-item li at that level (or NONE
   if the most recent was a draft).  For a draft at level L, walk
   down to find the nearest enclosing level with a real chapter URL
   -- that's what the JS DOM-ancestor walk computes.
   Returns a list of (predictedUrl, sourceTitle). *)
fun predictDraftRewrites tocHtml =
  let
    val wrapMarker = "<span class=\"chapter-link-wrapper\">"
    val strongMarker = "<strong aria-hidden=\"true\">"
    val hrefMarker = " href=\""
    val rewrites = ref ([] : (string * string) list)
    val urls = ref ([] : (int * string option) list)
    val level = ref 0
    fun setUrl L v =
      urls := (L, v) ::
        List.filter (fn (L', _) => L' <> L) (!urls)
    fun lookupUrl L =
      case List.find (fn (L', _) => L' = L) (!urls) of
          SOME (_, v) => v
        | NONE => NONE
    fun ancestorUrl L =
      if L <= 0 then NONE
      else case lookupUrl L of
               SOME u => SOME u
             | NONE => ancestorUrl (L - 1)
    val hlen = String.size tocHtml
    fun skipWS i =
      if i < hlen andalso Char.isSpace (String.sub (tocHtml, i))
      then skipWS (i + 1) else i
    fun startsAt p s =
      p + String.size s <= hlen andalso
      String.substring (tocHtml, p, String.size s) = s
    fun handleChapterItemAt p =
      (* p is just past `<li class="chapter-item ...">`.  Look at the
         next element after whitespace: if it's the wrapper-span, this
         is a real chapter-item entry; otherwise (e.g. the outer li
         that wraps a <li class="part-title"> sibling) skip. *)
      let
        val q = skipWS p
      in
        if not (startsAt q "<span class=\"chapter-link-wrapper\"")
        then ()
        else
          let
            val afterWrap = q + String.size wrapMarker
            val firstChild = skipWS afterWrap
            val isAnchor = startsAt firstChild "<a "
          in
            if isAnchor then
              case strFindFrom hrefMarker tocHtml firstChild of
                  SOME hp =>
                    let
                      val hs = hp + String.size hrefMarker
                      val (hv, _) = readUntilChar #"\"" tocHtml hs
                    in
                      if not (CharVector.exists (fn c => c = #"#") hv)
                      then setUrl (!level) (SOME hv)
                      else setUrl (!level) NONE
                    end
                | NONE => setUrl (!level) NONE
            else
              (* Draft: extract title and predict URL. *)
              let
                val sp = strFindFrom strongMarker tocHtml q
                val title =
                  case sp of
                      NONE => ""
                    | SOME spos =>
                        let
                          val numStart = spos + String.size strongMarker
                          val (_, numEnd) =
                            readUntilChar #"<" tocHtml numStart
                          val afterStrong =
                            Option.getOpt
                              (strFindFrom "</strong>" tocHtml numEnd,
                               numEnd) + String.size "</strong>"
                          val (raw, _) =
                            readUntilChar #"<" tocHtml afterStrong
                        in trimSpace raw end
                val () = setUrl (!level) NONE
              in
                if title = "" then ()
                else
                  case ancestorUrl (!level - 1) of
                      SOME chHref =>
                        let val decoded = decodeEntities title
                            val slug = slugify decoded
                            val url = chHref ^ "#" ^ slug
                        in rewrites := (url, decoded) :: !rewrites end
                    | NONE => ()
              end
          end
      end
    fun walk p =
      if p >= hlen then ()
      else if startsAt p "<ol class=\"chapter\""
              orelse startsAt p "<ol class=\"section\"" then
        let val tagEnd = Option.getOpt
                           (strFindFrom ">" tocHtml p, hlen) + 1
        in level := !level + 1; setUrl (!level) NONE; walk tagEnd end
      else if startsAt p "</ol>" then
        (setUrl (!level) NONE;
         level := !level - 1;
         walk (p + 5))
      else if startsAt p "<li class=\"chapter-item" then
        let val tagEnd = Option.getOpt
                           (strFindFrom ">" tocHtml p, hlen) + 1
        in handleChapterItemAt tagEnd; walk tagEnd end
      else walk (p + 1)
    val () = walk 0
  in List.rev (!rewrites) end

fun checkLinksMain bookDir =
  let
    val tocPath = OS.Path.concat (bookDir, "toc.html")
    val () =
      if OS.FileSys.access (tocPath, [OS.FileSys.A_READ]) then ()
      else die ("check-links: " ^ tocPath ^ " missing")
    val tocHtml = readFileAll tocPath
    val (pagePrefix, _) = parseSidebarTOC tocHtml
    (* Per-page (page, html, idSet) for fast lookup. *)
    val pageInfo =
      List.mapPartial
        (fn (page, _) =>
           let val path = OS.Path.concat (bookDir, page)
           in if OS.FileSys.access (path, [OS.FileSys.A_READ])
              then let val h = readFileAll path
                       val ids = collectIdAttrs h
                   in SOME (page, h, ids) end
              else NONE
           end)
        pagePrefix
    fun pageExists p =
      List.exists (fn (q, _, _) => q = p) pageInfo
    fun anchorIn p a =
      case List.find (fn (q, _, _) => q = p) pageInfo of
          SOME (_, _, ids) => List.exists (fn x => x = a) ids
        | NONE => false
    val total = ref 0
    fun reportErr msg = (print (msg ^ "\n"); total := !total + 1)
    fun checkOne sourcePage href =
      if skipHref href then ()
      else
        case splitHref href of
            (NONE, NONE) => ()
          | (NONE, SOME a) =>
              if anchorIn sourcePage a then ()
              else reportErr (OS.Path.concat (bookDir, sourcePage) ^
                              ": href=\"#" ^ a ^ "\" -> anchor missing")
          | (SOME p, NONE) =>
              if pageExists p then ()
              else reportErr (OS.Path.concat (bookDir, sourcePage) ^
                              ": href=\"" ^ p ^ "\" -> page missing")
          | (SOME p, SOME a) =>
              if not (pageExists p) then
                reportErr (OS.Path.concat (bookDir, sourcePage) ^
                           ": href=\"" ^ href ^ "\" -> page missing")
              else if not (anchorIn p a) then
                reportErr (OS.Path.concat (bookDir, sourcePage) ^
                           ": href=\"" ^ href ^ "\" -> anchor missing in " ^ p)
              else ()
    (* Static body / sidebar / nav <a href> validation, per chapter. *)
    val () =
      List.app
        (fn (page, html, _) =>
           List.app (checkOne page) (collectAnchorHrefs html))
        pageInfo
    (* JS-rewritten draft-sidebar URLs (predicted statically). *)
    val () =
      List.app
        (fn (url, title) =>
           if skipHref url then ()
           else
             case splitHref url of
                 (SOME p, SOME a) =>
                   if not (pageExists p) then
                     reportErr (tocPath ^ ": sidebar draft \"" ^ title ^
                                "\" rewrites to " ^ url ^ " -> page missing")
                   else if not (anchorIn p a) then
                     reportErr (tocPath ^ ": sidebar draft \"" ^ title ^
                                "\" rewrites to " ^ url ^
                                " -> anchor missing in " ^ p)
                   else ()
               | _ =>
                   reportErr (tocPath ^ ": sidebar draft \"" ^ title ^
                              "\" rewrites to malformed URL " ^ url))
        (predictDraftRewrites tocHtml)
  in
    if !total > 0 then
      (TextIO.output (TextIO.stdErr,
        "check-links: " ^ Int.toString (!total) ^
        " broken link(s).\n");
       OS.Process.exit OS.Process.failure)
    else
      OS.Process.exit OS.Process.success
  end

fun checkRefsMain bookDir =
  let
    val tocPath = OS.Path.concat (bookDir, "toc.html")
    val () =
      if OS.FileSys.access (tocPath, [OS.FileSys.A_READ]) then ()
      else die ("check-refs: " ^ tocPath ^ " missing")
    val (pagePrefix, sidebarAnchor) =
      parseSidebarTOC (readFileAll tocPath)
    fun sidebarForPage page =
      List.mapPartial
        (fn ((p, a), n) => if p = page then SOME (a, n) else NONE)
        sidebarAnchor
    (* Read each chapter HTML once into (page, html) and reuse for
       both the heading walk and the ref-link walk. *)
    val pageHtml =
      List.mapPartial
        (fn (page, _) =>
           let val path = OS.Path.concat (bookDir, page)
           in if OS.FileSys.access (path, [OS.FileSys.A_READ])
              then SOME (page, readFileAll path)
              else NONE
           end)
        pagePrefix
    fun lookupHtml page =
      case List.find (fn (p, _) => p = page) pageHtml of
          SOME (_, h) => SOME h
        | NONE => NONE
    val pageHeadings =
      List.map
        (fn (page, prefix) =>
           case lookupHtml page of
               SOME html =>
                 (page, parsePageHeadingsImpl prefix
                          (sidebarForPage page) html)
             | NONE => (page, []))
        pagePrefix
    val total = ref 0
    val () =
      List.app
        (fn (name, html) =>
           let
             val path = OS.Path.concat (bookDir, name)
             val errs = checkPageRefs name html pageHeadings
           in
             List.app
               (fn (page, anchor, shown, expected) =>
                  (print (path ^ ": link to " ^ page ^ "#" ^ anchor ^
                          " displays " ^ shown ^
                          " but heading number is " ^ expected ^ "\n");
                   total := !total + 1))
               (List.rev errs)
           end)
        pageHtml
  in
    if !total > 0 then
      (TextIO.output (TextIO.stdErr,
        "check-refs: " ^ Int.toString (!total) ^
        " cross-reference mismatch(es).\n");
       OS.Process.exit OS.Process.failure)
    else
      OS.Process.exit OS.Process.success
  end

(* ===== check-html sub-command =====

   Lint the rendered mdbook output for raw-LaTeX and other "leak"
   patterns that should never reach published HTML.  Each *.html
   is read once and all 17 patterns are applied in a single pass
   -- one grep subprocess per (pattern x file) would dominate wall
   time at the Reference manual's hundreds of entries.

   Lines containing any of `$`, `MathJax`, `worda:`, `wordb:`,
   `wordc:`, `term:`, `type:`, `holtxt:`, `textsl:`, `<!--`,
   ` !--`, `-->`, `<code>` are dropped by the default checks (the
   `$` filter alone covers MathJax math contexts where many of the
   forbidden tokens are legitimate).  Two checks opt out of the
   filter: the display-math `<word>` check (filter would mask
   every `$$`-anchored line) and the empty-code-block check
   (filter would mask the `<code>` we're looking for). *)

fun checkHtmlMain bookDir =
  let
    val () =
      if OS.FileSys.access (bookDir, []) andalso
         OS.FileSys.isDir bookDir
      then ()
      else (TextIO.output (TextIO.stdErr,
              "mdbook-check: " ^ bookDir ^ " is not a directory\n");
            OS.Process.exit OS.Process.failure)

    fun lineFilteredOut ln =
      String.isSubstring "$" ln orelse
      String.isSubstring "MathJax" ln orelse
      String.isSubstring "worda:" ln orelse
      String.isSubstring "wordb:" ln orelse
      String.isSubstring "wordc:" ln orelse
      String.isSubstring "term:" ln orelse
      String.isSubstring "type:" ln orelse
      String.isSubstring "holtxt:" ln orelse
      String.isSubstring "textsl:" ln orelse
      String.isSubstring "ty: [" ln orelse
      String.isSubstring "<!--" ln orelse
      String.isSubstring " !--" ln orelse
      String.isSubstring "-->" ln orelse
      String.isSubstring "<code>" ln

    fun isWordChar c =
      Char.isAlphaNum c orelse c = #"_"

    fun containsLit lit ln = String.isSubstring lit ln
    fun containsAny lits ln =
      List.exists (fn lit => containsLit lit ln) lits

    (* `\textbar` not immediately followed by [a-z]. *)
    fun hasTextbarLeak ln =
      let
        val sz = String.size ln
        val needle = "\\textbar"
        val nsz = String.size needle
        fun look p =
          if p + nsz > sz then false
          else if String.substring (ln, p, nsz) = needle then
            let
              val q = p + nsz
              val ok = q >= sz orelse
                       let val c = String.sub (ln, q)
                       in not (c >= #"a" andalso c <= #"z") end
            in if ok then true else look (p + 1) end
          else look (p + 1)
      in look 0 end

    (* `\cite` or `\citet`, optionally followed by `[..]`, then `{`. *)
    fun hasCiteLeak ln =
      let
        val sz = String.size ln
        fun afterOptBracket p =
          if p < sz andalso String.sub (ln, p) = #"[" then
            let
              fun scan q =
                if q >= sz then NONE
                else if String.sub (ln, q) = #"]" then SOME (q + 1)
                else scan (q + 1)
            in scan (p + 1) end
          else SOME p
        fun look p =
          if p >= sz then false
          else
            case detectCite (ln, p, sz) of
                NONE => look (p + 1)
              | SOME (_, k) =>
                let
                  val hit =
                    case afterOptBracket k of
                        SOME q => q < sz andalso String.sub (ln, q) = #"{"
                      | NONE => false
                in if hit then true else look (p + 1) end
      in look 0 end

    (* `\\X{` where X is mathit/mathtt/texttt/textbf/textit -- the
       double-backslash signature of escaped MathJax content that
       got trapped inside a <pre><code> block. *)
    val mathTrapPrefixes =
      ["\\\\mathit{", "\\\\mathtt{", "\\\\texttt{",
       "\\\\textbf{", "\\\\textit{"]
    fun hasMathTrap ln = containsAny mathTrapPrefixes ln

    (* Line starting with `$$`, with a `<word>` pseudo-HTML tag
       inside the math span (before the closing `$`). *)
    fun hasDisplayMathTag ln =
      let
        val sz = String.size ln
      in
        sz >= 2 andalso
        String.sub (ln, 0) = #"$" andalso String.sub (ln, 1) = #"$" andalso
        let
          fun findClose p =
            if p >= sz orelse String.sub (ln, p) = #"$" then p
            else findClose (p + 1)
          val endPos = findClose 2
          fun look p =
            if p >= endPos then false
            else if String.sub (ln, p) = #"<" then
              let
                fun scanWord q =
                  if q < endPos andalso
                     let val c = String.sub (ln, q)
                     in c >= #"a" andalso c <= #"z" end
                  then scanWord (q + 1)
                  else q
                val q' = scanWord (p + 1)
                val matched =
                  q' > p + 1 andalso q' < endPos andalso
                  String.sub (ln, q') = #">"
              in if matched then true else look (p + 1) end
            else look (p + 1)
        in look 2 end
      end

    (* `\providecommand` / `\newcommand` / `\renewcommand`, with a
       non-word-character boundary after, matching ERE `\b`. *)
    val macroDefLits =
      ["\\providecommand", "\\newcommand", "\\renewcommand"]
    fun hasMacroDefLeak ln =
      let
        val sz = String.size ln
        fun matchAt lit p =
          let val n = String.size lit
          in p + n <= sz andalso
             String.substring (ln, p, n) = lit andalso
             (p + n = sz orelse
              not (isWordChar (String.sub (ln, p + n))))
          end
        fun look p =
          if p >= sz then false
          else if List.exists (fn lit => matchAt lit p) macroDefLits then true
          else look (p + 1)
      in look 0 end

    val envLeakLits =
      ["\\begin{tikzpicture}", "\\begin{figure}",
       "\\begin{center}", "\\begin{tabular}"]
    fun hasEnvLeak ln = containsAny envLeakLits ln

    (* `href="..."` whose URL portion contains two `#` characters.
       Don't require a closing `"` -- the shell ERE
       `href="[^"]*#[^"]*#` doesn't either. *)
    fun hasDoubleHash ln =
      let
        val sz = String.size ln
        val needle = "href=\""
        val nsz = String.size needle
        fun countHash q acc =
          if q >= sz orelse String.sub (ln, q) = #"\"" then acc
          else if String.sub (ln, q) = #"#" then countHash (q + 1) (acc + 1)
          else countHash (q + 1) acc
        fun look p =
          if p + nsz > sz then false
          else if String.substring (ln, p, nsz) = needle then
            (countHash (p + nsz) 0 >= 2 orelse look (p + 1))
          else look (p + 1)
      in look 0 end

    fun checkHtmlFile path failRef =
      let
        val content = readFileAll path
        val lines = String.fields (fn c => c = #"\n") content
        (* (lineNo, line, alreadyFiltered) triples, 1-indexed. *)
        val numbered =
          let
            fun pair _ [] acc = List.rev acc
              | pair n (ln :: rest) acc =
                  pair (n + 1) rest ((n, ln, lineFilteredOut ln) :: acc)
          in pair 1 lines [] end

        fun report description hits =
          case hits of
              [] => ()
            | _ =>
                (print (path ^ ": " ^ description ^ "\n");
                 List.app
                   (fn (n, ln) =>
                      print ("  " ^ Int.toString n ^ ":" ^ ln ^ "\n"))
                   hits;
                 failRef := true)

        (* Collect up to 3 matching (lineNo, line) pairs. *)
        fun collect useFilter test =
          let
            fun walk [] _ acc = List.rev acc
              | walk _ 3 acc = List.rev acc
              | walk ((n, ln, fo) :: rest) c acc =
                  if useFilter andalso fo then walk rest c acc
                  else if test ln then walk rest (c + 1) ((n, ln) :: acc)
                  else walk rest c acc
          in walk numbered 0 [] end

        fun checkFiltered test description =
          report description (collect true test)
        fun checkUnfiltered test description =
          report description (collect false test)
      in
        checkFiltered (containsLit "\\texttt{")        "raw \\texttt{} leak";
        checkFiltered hasTextbarLeak                   "raw \\textbar leak";
        checkFiltered (containsLit "\\textasciitilde")
          "raw \\textasciitilde leak";
        checkFiltered (containsLit "\\begin{table}")
          "raw \\begin{table} leak";
        checkFiltered (containsLit "\\end{table}")     "raw \\end{table} leak";
        checkFiltered (containsLit "\\ref{")           "unresolved \\ref{}";
        checkFiltered (containsLit "\\label{")         "unstripped \\label{}";
        checkFiltered hasCiteLeak
          "unresolved \\cite{} (smdpp citation pass)";
        checkFiltered (containsLit "\\refentry{")
          "unresolved \\refentry{} (smdpp \\refentry pass)";
        checkFiltered hasMathTrap
          "math content trapped in code block (escaped \\X{...})";
        checkUnfiltered hasDisplayMathTag
          "<word> pseudo-HTML tag inside $$math$$ (use \\langle...\\rangle)";
        checkUnfiltered (containsLit "<pre><code></code></pre>")
          ("empty rendered code block " ^
           "(likely a fence around silent polyscripter setup)");
        checkFiltered (containsLit "class=\"language-{=")
          "{=fmt} raw block reached mdbook (smdpp didn't strip it)";
        checkFiltered hasMacroDefLeak
          "LaTeX macro-definition command leaked into mdbook";
        checkFiltered hasEnvLeak
          "LaTeX environment leaked into mdbook";
        checkFiltered hasDoubleHash
          "double-hash URL (sidebar rewrite picked up an anchored ancestor)";
        checkFiltered (containsLit "<i class=\"fa fa-")
          "FA4 webfont icon syntax leaked from theme template"
      end

    (* Enumerate `<bookDir>/*.html`, excluding print.html, in
       lexicographic order (matching the shell glob). *)
    fun listHtml dir =
      let
        val d = OS.FileSys.openDir dir
        fun loop acc =
          case OS.FileSys.readDir d of
              NONE => acc
            | SOME name =>
                if String.isSuffix ".html" name andalso name <> "print.html"
                then loop (name :: acc)
                else loop acc
        val raw = loop []
        val () = OS.FileSys.closeDir d
      in Listsort.sort String.compare raw end

    val failRef = ref false
    val () =
      List.app
        (fn name => checkHtmlFile (OS.Path.concat (bookDir, name)) failRef)
        (listHtml bookDir)
  in
    if !failRef then
      (TextIO.output (TextIO.stdErr,
        "mdbook-check: rendered-HTML leaks detected (see hits above).\n");
       OS.Process.exit OS.Process.failure)
    else
      (print "mdbook-check: OK\n";
       OS.Process.exit OS.Process.success)
  end

(* ===== render-bib sub-command =====
   Scans the supplied .smd files for `\cite[loc]{keys}` call-sites,
   runs pandoc citeproc once over a synthetic markdown doc with one
   paragraph per unique call-site, and parses the resulting HTML to
   extract:
     - per-call-site rendered `<span class="citation">` markup, with
       intra-bibliography href rewrites applied so links resolve from
       any chapter to references.html;
     - the bibliography `<div id="refs">` block.
   Writes two files into the current directory:
     references.md    — mdbook chapter wrapping the bibliography.
     cite-labels.tsv  — smdpp's preprocessor reads this at mdbook
                         build time to substitute `\cite{...}` calls.
   Each TSV row is `keys<TAB>locator<TAB>rendered-html`, single-line. *)

(* A single `\cite[loc]{keys}` or `\citet[loc]{keys}` occurrence in
   source.  `locator` is the raw locator text without brackets (or ""
   if no `[..]` block); `keys` is the raw comma-joined key list;
   `form` is Paren for `\cite`, Text for `\citet`. *)
type cite = { keys : string, locator : string, form : citeForm }

(* Find every `\cite[loc]{keys}` / `\citet[loc]{keys}` in `s`.
   Brace-counted on the key argument; loose `]`-terminator on the
   locator (locators never contain literal `]` in practice).  Returns
   occurrences in source order, possibly with duplicates. *)
fun findCites s =
  let
    val sub = String.sub
    val sz = String.size s
    fun scan i acc =
      if i >= sz then List.rev acc
      else
        case detectCite (s, i, sz) of
            SOME (form, k) =>
              let
                val (locator, k') =
                  if k < sz andalso sub (s, k) = #"[" then
                    let
                      fun findRBrack j =
                        if j >= sz then NONE
                        else if sub (s, j) = #"]" then SOME j
                        else findRBrack (j + 1)
                    in
                      case findRBrack (k + 1) of
                          SOME e =>
                            (String.substring (s, k + 1, e - k - 1), e + 1)
                        | NONE => ("", k)
                    end
                  else ("", k)
              in
                if k' < sz andalso sub (s, k') = #"{" then
                  case findCloseBrace (s, k' + 1) of
                      NONE => scan (i + 1) acc
                    | SOME e =>
                      let val keys =
                        String.substring (s, k' + 1, e - k' - 1)
                      in scan (e + 1)
                              ({keys = keys, locator = locator,
                                form = form} :: acc)
                      end
                else scan (i + 1) acc
              end
          | NONE => scan (i + 1) acc
  in scan 0 [] end

(* Translate a LaTeX-flavoured locator into the form citeproc parses
   after the comma in `[@key, loc]`.  Currently just `~` → ` `;
   trim leading/trailing whitespace. *)
fun normalizeLocator s =
  let
    val mapped = String.translate
                   (fn #"~" => " " | c => String.str c) s
  in trimSpace mapped end

(* Build the pandoc-citeproc syntax from a cite record.  `Paren` form
   (from `\cite`) emits `[@k1; @k2, loc]`, which pandoc renders as
   "(Author Year)".  `Text` form (from `\citet`) emits `@k [loc]`,
   which pandoc renders as "Author (Year)" textually.  pandoc has no
   well-defined multi-key textual syntax, so multi-key `\citet` is
   rejected at render-bib time. *)
fun citeprocOf {keys, locator, form} =
  let
    val keyList =
        List.map trimSpace (String.tokens (fn c => c = #",") keys)
    val locForm = normalizeLocator locator
  in
    case form of
        Paren =>
          let
            val keyForm =
                String.concatWith "; "
                  (List.map (fn k => "@" ^ k) keyList)
          in
            if locForm = "" then "[" ^ keyForm ^ "]"
            else "[" ^ keyForm ^ ", " ^ locForm ^ "]"
          end
      | Text =>
          (case keyList of
              [k] => if locForm = "" then "@" ^ k
                     else "@" ^ k ^ " [" ^ locForm ^ "]"
            | _ => die ("smdpp: \\citet{" ^ keys ^ "}: textual form " ^
                        "requires a single key (pandoc has no clean " ^
                        "multi-key textual syntax); use \\cite for " ^
                        "parenthetical multi-key"))
  end

(* Write `content` to `path`, overwriting. *)
fun writeFile path content =
  let val out = TextIO.openOut path
  in TextIO.output (out, content); TextIO.closeOut out end

(* Resolve `path` to an absolute filesystem path; passes through if
   already absolute.  pandoc resolves bibliography/csl YAML paths
   relative to its own cwd, which during render-bib is the book dir;
   feeding absolute paths is robust regardless of where pandoc runs. *)
fun absPath path =
  if OS.Path.isAbsolute path then path
  else OS.Path.mkAbsolute
         {path = path, relativeTo = OS.FileSys.getDir ()}

(* Run pandoc --citeproc --from markdown --to html5 < inputPath >
   outputPath; die on failure. *)
fun runPandoc inputPath outputPath =
  let
    val cmd =
        "pandoc --citeproc --from markdown --to html5 " ^
        inputPath ^ " > " ^ outputPath
    val rc = OS.Process.system cmd
  in
    if OS.Process.isSuccess rc then ()
    else die ("render-bib: pandoc invocation failed: " ^ cmd)
  end

(* Find every occurrence of `needle` in `haystack` and replace with
   `replacement`.  Non-overlapping, left-to-right. *)
fun replaceAll needle replacement haystack =
  let
    val nsz = String.size needle
    val hsz = String.size haystack
    fun loop i acc =
      if i + nsz > hsz then
        String.concat (List.rev (String.substring (haystack, i, hsz - i) :: acc))
      else if String.substring (haystack, i, nsz) = needle then
        loop (i + nsz) (replacement :: acc)
      else
        loop (i + 1) (String.str (String.sub (haystack, i)) :: acc)
  in loop 0 [] end

(* Collapse runs of ASCII whitespace (incl. tabs, newlines) to a
   single space.  Trims leading/trailing whitespace. *)
fun normalizeWhitespace s =
  let
    val sub = String.sub
    val sz = String.size s
    fun loop (i, prevSpace, acc) =
      if i >= sz then String.implode (List.rev acc)
      else
        let val c = sub (s, i)
        in
          if Char.isSpace c then
            if prevSpace orelse acc = [] then loop (i + 1, true, acc)
            else loop (i + 1, true, #" " :: acc)
          else loop (i + 1, false, c :: acc)
        end
    val collapsed = loop (0, true, [])
    val ss = Substring.full collapsed
    val ss = Substring.dropr (fn c => c = #" ") ss
  in Substring.string ss end

(* Locate the next `<span class="citation"` opening at or after
   `start` in `html`, and return (span-content, position-after-span).
   The span body is brace-balanced over nested `<span>` tags; the
   actual citeproc output never nests <span> inside <span> for an
   individual citation, but we depth-track anyway. *)
fun extractCitationSpan html start =
  let
    val openMarker = "<span class=\"citation\""
    val openTag = "<span"
    val closeTag = "</span>"
  in
    case strFindFrom openMarker html start of
        NONE => NONE
      | SOME openPos =>
        let
          val hsz = String.size html
          fun loop (i, depth) =
            if i >= hsz then NONE
            else if i + String.size closeTag <= hsz andalso
                    String.substring (html, i, String.size closeTag)
                    = closeTag
            then
              if depth = 1
              then SOME (i + String.size closeTag)
              else loop (i + String.size closeTag, depth - 1)
            else if i + String.size openTag <= hsz andalso
                    String.substring (html, i, String.size openTag)
                    = openTag
            then loop (i + String.size openTag, depth + 1)
            else loop (i + 1, depth)
        in
          case loop (openPos + String.size openTag, 1) of
              NONE => NONE
            | SOME endPos =>
                SOME (String.substring (html, openPos, endPos - openPos),
                      endPos)
        end
  end

(* Locate the `<div id="refs"` block and return its full markup
   (opening tag through matching `</div>`), or "" if not found.
   Depth-tracks nested <div> children (each csl-entry is one). *)
fun extractRefsDiv html =
  let
    val marker = "<div id=\"refs\""
    val openTag = "<div"
    val closeTag = "</div>"
  in
    case strFindFrom marker html 0 of
        NONE => ""
      | SOME openPos =>
        let
          val hsz = String.size html
          fun loop (i, depth) =
            if i >= hsz then NONE
            else if i + String.size closeTag <= hsz andalso
                    String.substring (html, i, String.size closeTag)
                    = closeTag
            then
              if depth = 1
              then SOME (i + String.size closeTag)
              else loop (i + String.size closeTag, depth - 1)
            else if i + String.size openTag <= hsz andalso
                    String.substring (html, i, String.size openTag)
                    = openTag
            then loop (i + String.size openTag, depth + 1)
            else loop (i + 1, depth)
        in
          case loop (openPos + String.size openTag, 1) of
              NONE => ""
            | SOME endPos =>
                String.substring (html, openPos, endPos - openPos)
        end
  end

(* Build the synthetic markdown doc that drives the single pandoc
   invocation.  One paragraph per unique cite, each prefixed with a
   `%CITE-N%` sentinel so the resulting HTML's citation spans line
   up with the input cite list. *)
fun buildSynthetic absBib absCsl cites =
  let
    val header =
        "---\nbibliography: " ^ absBib ^
        "\ncsl: " ^ absCsl ^
        "\nlink-citations: true\nsuppress-bibliography: false\n---\n\n"
    fun row (i, cite) =
        "%CITE-" ^ Int.toString i ^ "% " ^ citeprocOf cite ^ "\n\n"
    fun loop _ [] acc = String.concat (List.rev acc)
      | loop i (c :: rest) acc = loop (i + 1) rest (row (i, c) :: acc)
    val body = loop 0 cites []
    val tail = "::: {#refs}\n:::\n"
  in header ^ body ^ tail end

(* De-duplicate cites by (keys, locator, form).  Preserves first-seen
   order so the resulting list is stable across runs.  Form is part
   of the key because the same source key can appear as both `\cite`
   and `\citet` and the two renderings differ. *)
fun uniqueCites cites =
  let
    fun seen [] _ = false
      | seen ({keys, locator, form} :: rest) c =
          (keys = #keys c andalso locator = #locator c
                          andalso form = #form c)
          orelse seen rest c
    fun loop [] acc = List.rev acc
      | loop (c :: rest) acc =
          if seen acc c then loop rest acc
          else loop rest (c :: acc)
  in loop cites [] end

(* TSV row escaping is trivial here: the locator and keys are never
   allowed to contain tabs (they come from LaTeX source where literal
   tabs are banned).  The rendered HTML can hold whitespace, but
   normalizeWhitespace already collapsed everything to single spaces
   so no tabs survive. *)
fun renderBibMain bibPath cslPath smdPaths =
  let
    val absBib = absPath bibPath
    val absCsl = absPath cslPath
    val () =
      if OS.FileSys.access (absBib, [OS.FileSys.A_READ]) then ()
      else die ("render-bib: bibliography not readable: " ^ absBib)
    val () =
      if OS.FileSys.access (absCsl, [OS.FileSys.A_READ]) then ()
      else die ("render-bib: CSL not readable: " ^ absCsl)
    val allCites =
        List.concat
          (List.map (fn p => findCites (readFileAll p)) smdPaths)
    val cites = uniqueCites allCites
    val () =
      if List.null cites then
        die "render-bib: no \\cite{...} calls found in the supplied .smd files"
      else ()
    val inputPath = OS.FileSys.tmpName ()
    val outputPath = OS.FileSys.tmpName ()
    val () = writeFile inputPath (buildSynthetic absBib absCsl cites)
    val () = runPandoc inputPath outputPath
    val html = readFileAll outputPath
    val () = (OS.FileSys.remove inputPath; OS.FileSys.remove outputPath)
              handle _ => ()
    (* Capture per-cite spans.  We walk the HTML in source order,
       advancing past each marker and grabbing the next citation
       span — this matches up with our cite list because pandoc
       preserves paragraph order. *)
    fun grab cites0 pos rows =
        case cites0 of
            [] => List.rev rows
          | c :: rest =>
            let
              val idx = List.length rows
              val marker = "%CITE-" ^ Int.toString idx ^ "%"
            in
              case strFindFrom marker html pos of
                  NONE => die ("render-bib: marker " ^ marker ^
                               " not found in pandoc output")
                | SOME mp =>
                  let val afterMarker = mp + String.size marker
                  in
                    case extractCitationSpan html afterMarker of
                        NONE => die ("render-bib: no citation span after " ^
                                     marker)
                      | SOME (raw, endPos) =>
                        let
                          val rewritten =
                              replaceAll "href=\"#ref-"
                                         "href=\"references.html#ref-" raw
                          val flat = normalizeWhitespace rewritten
                        in
                          grab rest endPos ((c, flat) :: rows)
                        end
                  end
            end
    val labelled = grab cites 0 []
    val refsDiv = extractRefsDiv html
    val () =
      if refsDiv = "" then die "render-bib: <div id=\"refs\"> not found"
      else ()
    val tsv =
        String.concat
          (List.map
             (fn ({keys, locator, form}, html) =>
                keys ^ "\t" ^ locator ^ "\t" ^
                formToString form ^ "\t" ^ html ^ "\n")
             labelled)
    val refsMd =
        "# References\n\n" ^ refsDiv ^ "\n"
  in
    writeFile "cite-labels.tsv" tsv;
    writeFile "references.md" refsMd;
    print ("render-bib: wrote " ^ Int.toString (List.length labelled) ^
           " citation labels and " ^
           Int.toString
             (List.length
                (String.tokens (fn c => c = #"\n") tsv)) ^
           " TSV row(s); references.md " ^
           Int.toString (String.size refsMd) ^ " bytes\n")
  end

(* ===== dump-labels sub-command =====
   Scan a book's chapters in scan-only mode (no polyscripter,
   no mdbook): walk SUMMARY.md to get chapter ordering, run the
   existing `scanLabels` pass on each chapter's content, write
   the resulting `(label, file, anchor, num)` tuples to
   `<book-dir>/labels.tsv` (one row per tab-separated tuple).

   This is the fast prereq for cross-book `\ref{Book:label}`:
   each book emits its labels.tsv before any mdbook build, then
   smdpp's preprocessor pass reads sibling labels.tsv files at
   startup so `\ref{Book:label}` resolves to cross-book URLs. *)

(* Parse SUMMARY.md.  Returns chapter entries in source order as
   `(prefix-as-int-list, name, path)` tuples.  `prefix` follows
   mdbook numbering (top-level [1], [2]; sub-chapters [2,1], [2,2]
   inferred from two-space indentation).  Skips:
     - the `# Summary` title and any other `#`-prefix part titles
     - empty-link draft chapters (`- [Foo]()`); they have no path
     - prefix/suffix chapters listed outside any `- [Foo](...)`
       structure (we just don't emit them — they're rare).
   Tolerates blank lines and arbitrary other markup between
   chapter rows. *)
fun parseSummary content =
  let
    val lines = String.fields (fn c => c = #"\n") content
    fun countLeadingSpaces ln =
      let val sz = String.size ln
          fun loop i =
            if i >= sz orelse String.sub (ln, i) <> #" " then i
            else loop (i + 1)
      in loop 0 end
    fun isChapterRow ln =
      let val ind = countLeadingSpaces ln
          val rest = String.extract (ln, ind, NONE)
      in
        (String.isPrefix "- [" rest orelse String.isPrefix "* [" rest)
      end
    fun parseRow ln =
      let
        val ind = countLeadingSpaces ln
        val depth = ind div 2
        val rest = String.extract (ln, ind + 2, NONE)
        (* `rest` now begins with `[Title](path)` -- find the
           closing bracket of the title, then the open paren, then
           the closing paren. *)
        val sz = String.size rest
        fun findChar c i =
          if i >= sz then NONE
          else if String.sub (rest, i) = c then SOME i
          else findChar c (i + 1)
      in
        case findChar #"]" 0 of
            NONE => NONE
          | SOME closeBracket =>
            if closeBracket + 1 >= sz orelse
               String.sub (rest, closeBracket + 1) <> #"("
            then NONE
            else
              case findChar #")" (closeBracket + 2) of
                  NONE => NONE
                | SOME closeParen =>
                  let
                    val title =
                        String.substring (rest, 1, closeBracket - 1)
                    val path =
                        String.substring (rest, closeBracket + 2,
                                          closeParen - closeBracket - 2)
                  in
                    if path = "" then NONE
                    else SOME (depth, title, path)
                  end
      end
    (* Walk rows tracking per-depth counters; emit prefix-paths. *)
    val counters = Array.array (16, 0)  (* up to 16 levels *)
    fun bumpDepth d =
      let val () = Array.update (counters, d, Array.sub (counters, d) + 1)
          (* reset deeper counters *)
          fun resetDeeper i =
            if i >= Array.length counters then ()
            else (Array.update (counters, i, 0); resetDeeper (i + 1))
          val () = resetDeeper (d + 1)
          fun gatherPrefix i acc =
            if i > d then List.rev acc
            else gatherPrefix (i + 1) (Array.sub (counters, i) :: acc)
      in gatherPrefix 0 [] end
    fun loop [] acc = List.rev acc
      | loop (ln :: rest) acc =
          if not (isChapterRow ln) then loop rest acc
          else case parseRow ln of
              NONE => loop rest acc
            | SOME (depth, title, path) =>
                let val prefix = bumpDepth depth
                in loop rest ((prefix, title, path) :: acc) end
  in
    loop lines []
  end

(* Lightweight per-chapter scan: read the .smd, drop frontmatter
   and \index{} (mirrors stage 1 minus polyscripter and
   stripIndex's secondary line-collapse), then scanLabels.

   We deliberately don't run polyscripter: it's slow and produces
   labels only as side-effects of HOL evaluation, which authors
   don't typically reference from \ref.  Static \label{} calls in
   the source survive; that's enough for cross-book \ref.

   `readPath` is the on-disk path to the chapter source (src-dir-
   relative); `regPath` is the bare filename `scanLabels` records
   in the registry — this is what `toHtml` keys off, so the
   resulting URL is `../Book/<basename>.html`, no `src` prefix. *)
fun scanChapterFile (prefix, name, readPath, regPath) =
  let
    val content =
        let val ins = TextIO.openIn readPath
            val s = TextIO.inputAll ins
            val () = TextIO.closeIn ins
        in s end handle IO.Io _ =>
          ( TextIO.output (TextIO.stdErr,
              "dump-labels: warning: cannot read " ^ readPath ^
              "; skipping\n");
            "" )
    val s = content |> dropFrontmatter |> stripIndex
  in
    scanLabels prefix regPath name s
  end

(* Find the book's `src` setting in book.toml; defaults to ".". *)
fun readBookSrc tomlPath =
  let
    val content =
        let val ins = TextIO.openIn tomlPath
            val s = TextIO.inputAll ins
            val () = TextIO.closeIn ins
        in s end
    val lines = String.fields (fn c => c = #"\n") content
    fun parseQuoted s =
      let val n = String.size s
      in if n >= 2 andalso String.sub (s, 0) = #"\""
            andalso String.sub (s, n - 1) = #"\""
         then SOME (String.substring (s, 1, n - 2))
         else NONE
      end
    fun findSrc [] = "."
      | findSrc (ln :: rest) =
          let val t = trimSpace ln
          in
            if String.isPrefix "src" t orelse
               String.isPrefix "src " t
            then
              (* "src = \"…\"" *)
              case List.find (fn c => c = #"=") (String.explode t) of
                  NONE => findSrc rest
                | SOME _ =>
                  let val parts = String.tokens (fn c => c = #"=") t
                  in case parts of
                         [_, rhs] =>
                           (case parseQuoted (trimSpace rhs) of
                                SOME v => v
                              | NONE => findSrc rest)
                       | _ => findSrc rest
                  end
            else findSrc rest
          end
  in findSrc lines end

fun dumpLabelsMain bookDir =
  let
    val origDir = OS.FileSys.getDir ()
    val () = OS.FileSys.chDir bookDir
    val src = readBookSrc "book.toml"
              handle IO.Io _ => "."
    val summaryPath = OS.Path.concat (src, "SUMMARY.md")
    val () =
      if OS.FileSys.access (summaryPath, [OS.FileSys.A_READ]) then ()
      else die ("dump-labels: " ^ summaryPath ^ " missing")
    val summary =
        let val ins = TextIO.openIn summaryPath
            val s = TextIO.inputAll ins
            val () = TextIO.closeIn ins
        in s end
    val chapters = parseSummary summary
    (* Two paths: one for reading off disk (src-prefixed), one for
       the registry (just the chapter filename — this is what
       toHtml keys off when building cross-book URLs). *)
    fun pathsOf (prefix, name, path) =
        (prefix, name, OS.Path.concat (src, path), path)
    val labels =
        List.concat (List.map (scanChapterFile o pathsOf) chapters)
    (* Format labels.tsv: label TAB file TAB anchor TAB num *)
    fun rowOf (lbl, file, anchor, num) =
        lbl ^ "\t" ^ file ^ "\t" ^ anchor ^ "\t" ^ num ^ "\n"
    val out = TextIO.openOut "labels.tsv"
    val () = List.app (fn row => TextIO.output (out, rowOf row)) labels
    val () = TextIO.closeOut out
    val () = OS.FileSys.chDir origDir
    val () = TextIO.output (TextIO.stdErr,
              "dump-labels: " ^ bookDir ^
              ": wrote " ^ Int.toString (List.length labels) ^
              " label(s) to " ^ OS.Path.concat (bookDir, "labels.tsv") ^
              "\n")
  in
    OS.Process.exit OS.Process.success
  end

(* ===== main ===== *)

fun smdppMain () =
  let
    (* Peel off --no-polyscripter wherever it appears at the front of argv;
       remaining args dispatch the usual subcommands. *)
    fun stripFlag (acc as (flagSeen, rest)) =
      case rest of
          "--no-polyscripter" :: r => stripFlag (true, r)
        | _ => acc
    val (sawFlag, args) = stripFlag (false, CommandLine.arguments ())
    val () = noPolyscripter := sawFlag
  in
    case args of
        ["supports", "html"] => OS.Process.exit OS.Process.success
      | "supports" :: _ => OS.Process.exit OS.Process.failure
      | ["check-refs", bookDir] => checkRefsMain bookDir
      | ["check-links", bookDir] => checkLinksMain bookDir
      | ["check-html", bookDir] => checkHtmlMain bookDir
      | "render-bib" :: bib :: csl :: smds =>
          if List.null smds then
            die "Usage: smdpp render-bib BIB CSL SMD..."
          else renderBibMain bib csl smds
      | ["dump-labels", bookDir] => dumpLabelsMain bookDir
      | [] =>
          let
            val () = loadCiteLabels ()
            val () = loadRefEntries ()
            val () = loadCrossBookLabels ()
            (* When --no-polyscripter is in effect we skip the heap load:
               runScripted will ignore obuf, so any dummy SimpleBuffer
               of the right type will do. *)
            val obuf = if !noPolyscripter then SimpleBuffer.mkBuffer ()
                       else setupPolyscripter ()
            val raw = TextIO.inputAll TextIO.stdIn
            val src = JSONParser.openString raw
            val pair = JSONParser.parse src
            val () = JSONParser.close src
            val book = case pair of
                           JSON.ARRAY [_, b] => b
                         | _ => die "Expected [ctx, book] JSON on stdin"
            val book' = transformBook obuf book
          in
            print (JSONPrinter.toString book');
            TextIO.flushOut TextIO.stdOut
          end
      | _ => die ("Usage:\n  " ^ CommandLine.name() ^
                  " [--no-polyscripter]\
                  \ [supports <renderer> |\
                  \ check-refs <book-dir> |\
                  \ check-links <book-dir> |\
                  \ check-html <book-dir> |\
                  \ render-bib <bib> <csl> <smd>... |\
                  \ dump-labels <book-dir>]")
  end

fun main () = smdppMain ()
