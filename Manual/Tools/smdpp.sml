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
       three backticks at the start of a line (any leading
       whitespace).  Return SOME (delim length) if so. *)
    fun fenceAt i =
      if i + 2 < sz andalso sub (s, i) = #"`"
         andalso sub (s, i+1) = #"`" andalso sub (s, i+2) = #"`"
         andalso (i = 0 orelse sub (s, i-1) = #"\n")
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

fun runScripted obuf s =
  processString {input = s, debug = false,
                 umap = Binarymap.mkDict String.compare,
                 obuf = obuf}

(* If the content has no top-level H1 heading anywhere, prepend
   `# <name>` so the rendered chapter has a title.  Some .smd files
   defer chapter-titling to the LaTeX driver (e.g., modern-syntax.smd
   is wrapped by modern-syntax-chapter.tex); for mdbook we synthesise
   the heading from the SUMMARY.md entry. *)
fun hasH1 s =
  let
    val lines = String.fields (fn c => c = #"\n") s
    fun isH1 ln =
      String.isPrefix "# " ln orelse ln = "#"
  in
    List.exists isH1 lines
  end

fun ensureH1 name s =
  if hasH1 s then s else "# " ^ name ^ "\n\n" ^ s

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
    fun lookup lbl =
      List.find (fn (l, _, _, _) => l = lbl) labelRegistry
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
                      SOME (_, file, anchor, num) =>
                        let
                          val url = if file = currentFile then
                                      "#" ^ anchor
                                    else
                                      toHtml file ^ "#" ^ anchor
                        in "[" ^ num ^ "](" ^ url ^ ")" end
                    | NONE => ""
            in
              loop (j+1, List.revAppend
                           (String.explode replacement, acc))
            end
      else loop (i+1, sub (s, i) :: acc)
  in loop (0, []) end

(* Stage 1: run polyscripter and the LaTeX-source strippers that
   don't touch \label/\ref.  The scan pass walks this output to
   build the label registry. *)
fun preprocessStage1 obuf s =
  s |> dropFrontmatter
    |> runScripted obuf
    |> stripIndex
    |> handleRawBlocks

(* Stage 2: with the registry in hand, resolve \ref{X} to a
   markdown link, then drop the (now-redundant) \label{X} marks
   and finish the markdown-side rewrites. *)
fun preprocessStage2 {labelRegistry, currentFile, name} s =
  s |> resolveRefs {currentFile = currentFile,
                    labelRegistry = labelRegistry}
    |> stripLabel
    |> convertSuperscripts
    |> protectMath
    |> ensureH1 name

(* GitHub-style heading slugger: lowercase, drop punctuation other
   than space/`-`/`_`, replace spaces with `-`, collapse multiple
   `-`s, trim.  Approximates pulldown-cmark's heading-id rule. *)
fun slugify text =
  let
    fun strip c =
      Char.isAlphaNum c orelse c = #" " orelse c = #"-" orelse c = #"_"
    val lower = String.map Char.toLower text
    val kept = String.translate
                 (fn c => if strip c then String.str c
                          else if c = #"\t" then " "
                          else "")
                 lower
    val dashed = String.map (fn #" " => #"-" | c => c) kept
    fun collapse [] = []
      | collapse (#"-" :: (rest as #"-" :: _)) = collapse rest
      | collapse (c :: rest) = c :: collapse rest
    val r = String.implode (collapse (String.explode dashed))
    val ss = Substring.full r
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
              | #"_" => loop (i+1, acc, inMath)
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
fun scanLabels chapterNum chapterFile chapterName content =
  let
    val lines = String.fields (fn c => c = #"\n") content
    (* The slug for a heading is computed *after* stripping any
       inline \label{}/\ref{} from the heading text. *)
    fun headingSlug ln =
      let
        val body = headingBody ln
        val body = stripCmd "label" body
        val body = stripCmd "ref" body
      in headingAnchor body end
    (* Find every `\label{X}` on a line; brace-counted body. *)
    val prefix = "\\label{"
    val psz = String.size prefix
    fun findLabels ln =
      let
        val sz = String.size ln
        fun loop (i, acc) =
          if i >= sz then List.rev acc
          else if i + psz <= sz andalso
                  String.substring (ln, i, psz) = prefix
          then
            case findCloseBrace (ln, i + psz) of
                NONE => List.rev acc
              | SOME j =>
                  let val lbl = String.substring (ln, i + psz, j - i - psz)
                  in loop (j+1, lbl :: acc) end
          else loop (i+1, acc)
      in loop (0, []) end
    fun fmtNumber (c, 0, _, _) = Int.toString c
      | fmtNumber (c, s2, 0, _) =
          Int.toString c ^ "." ^ Int.toString s2
      | fmtNumber (c, s2, s3, 0) =
          Int.toString c ^ "." ^ Int.toString s2 ^ "." ^ Int.toString s3
      | fmtNumber (c, s2, s3, s4) =
          Int.toString c ^ "." ^ Int.toString s2 ^ "." ^
          Int.toString s3 ^ "." ^ Int.toString s4
    val initAnchor = headingAnchor chapterName
    (* Build the entry list with cons-then-reverse to avoid the
       O(|acc|) cost of `acc @ ...` on every line. *)
    fun loop ([], _, acc) = List.rev acc
      | loop (ln :: rest, state as (_, s2, s3, s4), acc) =
          let
            val lvl = headingLevel ln
            val state' =
                case lvl of
                    SOME 1 => (headingSlug ln, 0, 0, 0)
                  | SOME 2 => (headingSlug ln, s2 + 1, 0, 0)
                  | SOME 3 => (headingSlug ln, s2, s3 + 1, 0)
                  | SOME 4 => (headingSlug ln, s2, s3, s4 + 1)
                  | _ => state
            val (anchor', s2', s3', s4') = state'
            val numStr = fmtNumber (chapterNum, s2', s3', s4')
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
                  val replacement =
                      if List.exists (fn a => a = anchor) localAnchors
                      then "](#" ^ anchor ^ ")"
                      else case lookup anchor of
                              SOME (_, file) =>
                                "](" ^ toHtml file ^ "#" ^ anchor ^ ")"
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
     { "sections": [ <Item>, ... ], "__non_exhaustive": null }
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

(* --- Pass 1: scan ---
   Run polyscripter + the LaTeX-source strippers on every chapter,
   assigning a chapter number to each top-level Chapter with content,
   and harvest its `\label{X}` calls into the registry. *)

fun scanChapter obuf chap (chapterNumRef, labelReg) =
  case chap of
      JSON.OBJECT fields =>
        let
          val name = chapterName fields
          val pathOpt = chapterPath fields
          val (newContent, labelReg) =
              case (stringField "content" fields, pathOpt) of
                  (SOME s, SOME p) =>
                    let
                      val () = chapterNumRef := !chapterNumRef + 1
                      val s' = preprocessStage1 obuf s
                      val labels =
                          scanLabels (!chapterNumRef) p name s'
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
                                    scanItem obuf item
                                              (chapterNumRef, reg)
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
and scanItem obuf item (chapterNumRef, labelReg) =
  case item of
      JSON.OBJECT [("Chapter", chap)] =>
        let val (chap', reg') =
                scanChapter obuf chap (chapterNumRef, labelReg)
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
                    in
                      (SOME s',
                       anchorReg @ map (fn a => (a, p)) anchors)
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
             `extractAnchors` pass on the content. *)
          val localAnchors =
              case chapterPath fields of
                  SOME p =>
                    List.mapPartial
                      (fn (a, f) => if f = p then SOME a else NONE)
                      registry
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
          val chapterNumRef = ref 0
          fun scanSections xs =
              let
                fun loop ([], acc, reg) = (List.rev acc, reg)
                  | loop (item :: rest, acc, reg) =
                      let val (item', reg') =
                              scanItem obuf item (chapterNumRef, reg)
                      in loop (rest, item' :: acc, reg') end
              in loop (xs, [], []) end
          fun finalizeSections labelReg xs =
              let
                fun loop ([], acc, reg) = (List.rev acc, reg)
                  | loop (item :: rest, acc, reg) =
                      let val (item', reg') =
                              finalizeItem labelReg item reg
                      in loop (rest, item' :: acc, reg') end
              in loop (xs, [], []) end
          fun trField ("sections", JSON.ARRAY xs) =
                let
                  val (xs1, labelReg)  = scanSections xs
                  val (xs2, anchorReg) = finalizeSections labelReg xs1
                  val xs3 = map (rewriteItem anchorReg) xs2
                in
                  ("sections", JSON.ARRAY xs3)
                end
            | trField kv = kv
        in
          JSON.OBJECT (map trField fields)
        end
    | _ => book

(* ===== main ===== *)

fun smdppMain () =
  case CommandLine.arguments () of
      ["supports", "html"] => OS.Process.exit OS.Process.success
    | "supports" :: _ => OS.Process.exit OS.Process.failure
    | [] =>
        let
          val obuf = setupPolyscripter ()
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
                " [supports <renderer>]")

fun main () = smdppMain ()
