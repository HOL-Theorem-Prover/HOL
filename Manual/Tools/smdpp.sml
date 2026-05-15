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
    (* Don't collapse consecutive dashes — pulldown-cmark keeps them
       (e.g. `simp_tac : foo` slugs to `simp_tac--foo`), and a mismatch
       here means `\ref{X}` URLs point at non-existent anchors. *)
    val ss = Substring.full dashed
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
       For sub-files (titleLvl > 1) mdbook also auto-emits an H1 at
       the top of the page whose slug matches chapterName; the
       content's leading H2 then collides with that auto-H1 and
       gets `-1` appended.  Seed seenSlugs so we account for it. *)
    val seenSlugs = ref ([] : (string * int) list)
    val () =
        if titleLvl > 1 then
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
          fun scanSections xs =
              let
                fun loop ([], acc, reg) = (List.rev acc, reg)
                  | loop (item :: rest, acc, reg) =
                      let val (item', reg') =
                              scanItem obuf item reg
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

(* ===== main ===== *)

fun smdppMain () =
  case CommandLine.arguments () of
      ["supports", "html"] => OS.Process.exit OS.Process.success
    | "supports" :: _ => OS.Process.exit OS.Process.failure
    | ["check-refs", bookDir] => checkRefsMain bookDir
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
                " [supports <renderer> | check-refs <book-dir>]")

fun main () = smdppMain ()
