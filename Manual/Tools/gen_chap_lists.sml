(* Generate one of two chapter-listing files from
   Manual/Description/chapters.txt:

     gen_chap_lists summary       > SUMMARY.md
     gen_chap_lists latex-include > chapters-include.tex

   chapters.txt is a human-maintained list of chapter stems.
   Top-level (un-indented) lines are chapters; lines with any
   leading whitespace are nested sub-files of the most recent
   top-level stem.  Blank lines and `#`-comment lines are
   ignored.

   .smd convention:
     - A top-level chapter .smd begins with `# Chapter Title`
       (H1).  Pandoc with --top-level-division=chapter maps the
       H1 to \chapter{} in the PDF; mdbook uses it as the page
       title.
     - A nested sub-file .smd begins with `## Section Title`
       (H2, no H1).  The same pandoc invocation maps the H2 to
       \section{} so the sub-file's .tex slots cleanly into the
       parent's \input{<stem>}; mdbook uses the H2 as the
       sidebar link's title.

   Outputs:
     - SUMMARY.md emits a top-level entry only when <stem>.smd
       exists (those are the chapters with a mdbook
       presentation).  The entry's title is the H1 of the .smd;
       sub-entries are draft-chapter links built from the H2/H3
       headings.  For a chapter with nested sub-files, the
       parent .smd is scanned line-by-line: H2/H3 headings emit
       anchor entries (as before) and `\input{<stem>}` lines
       referring to a declared sub-file whose <stem>.smd exists
       emit a nested-file link at that source position (the
       link's title is the H2 of the sub-file), preserving the
       sidebar order against the PDF.
     - chapters-include.tex emits `\include{<stem>}` for every
       top-level stem unconditionally (the LaTeX bundle uses
       .tex from .smd, .stex, or hand-maintained sources
       interchangeably).  Nested stems are NOT \include'd at
       the top level; they're pulled in by their parent's
       `\input{<stem>}`.

   The script must be run from Manual/Description/ (paths are
   relative). *)

(* --- file-system helpers --------------------------------------- *)

fun readFile path =
    let val s = TextIO.openIn path
        val all = TextIO.inputAll s
        val () = TextIO.closeIn s
    in all end

fun fileExists path =
    OS.FileSys.access (path, [OS.FileSys.A_READ])

fun emit s = TextIO.output (TextIO.stdOut, s)

fun die msg =
    ( TextIO.output (TextIO.stdErr, msg ^ "\n")
    ; OS.Process.exit OS.Process.failure )

(* --- chapters.txt parser --------------------------------------- *)

fun trim s =
    let val ss = Substring.full s
        val ss = Substring.dropl Char.isSpace ss
        val ss = Substring.dropr Char.isSpace ss
    in Substring.string ss end

(* A chapter is (stem, list-of-child-stems-in-order). *)
type chap = string * string list

fun isBlankOrComment ln =
    let val t = trim ln
    in t = "" orelse String.isPrefix "#" t end

fun startsWithSpace s = size s > 0 andalso Char.isSpace (String.sub (s, 0))

(* Walk lines.  Maintain (current-parent-stem, accumulated-children)
   while collecting a list of completed (parent, children) pairs. *)
fun parseChaptersFile path : chap list =
    let
      val all = readFile path
      val lines = String.fields (fn c => c = #"\n") all
      fun close (NONE, _, acc) = acc
        | close (SOME p, kids, acc) = (p, List.rev kids) :: acc
      fun go [] cur kids acc = List.rev (close (cur, kids, acc))
        | go (ln :: rest) cur kids acc =
            if isBlankOrComment ln then go rest cur kids acc
            else if startsWithSpace ln then
              (case cur of
                   NONE => die ("chapters.txt: indented line `" ^
                                trim ln ^
                                "' has no preceding top-level stem")
                 | SOME _ => go rest cur (trim ln :: kids) acc)
            else
              let val acc' = close (cur, kids, acc)
              in go rest (SOME (trim ln)) [] acc' end
    in go lines NONE [] [] end

(* --- .smd H1/H2/H3 extraction ---------------------------------- *)

fun smdLines stem =
    let val all = readFile (stem ^ ".smd")
        val ls = String.fields (fn c => c = #"\n") all
    in case List.rev ls of
           "" :: rest => List.rev rest
         | _ => ls
    end

fun isHeading pre s =
    String.isPrefix pre s andalso
    (size s = size pre orelse String.sub (s, size pre) <> #"#")

fun stripPrefix pre s = trim (String.extract (s, size pre, NONE))

(* Backticks in headings (e.g. `## The Theory `min``) are dropped
   so the slug-rewriting JS in theme/index.hbs sees a plain title. *)
fun cleanTitle s =
    String.translate (fn #"`" => "" | c => str c) s

fun extractH1 ls =
    let fun go [] = NONE
          | go (l :: rest) =
            if isHeading "# " l
            then SOME (cleanTitle (stripPrefix "# " l))
            else go rest
    in go ls end

(* For nested sub-files: they start at H2, no H1.  Take the
   first H2 as the sub-file's section title. *)
fun extractFirstH2 ls =
    let fun go [] = NONE
          | go (l :: rest) =
            if isHeading "## " l
            then SOME (cleanTitle (stripPrefix "## " l))
            else go rest
    in go ls end

(* Find an \input{X} on a line.  Look for the substring
   "\input{" and read up to the matching "}".  Returns the stem
   X, or NONE if the line doesn't look like an \input. *)
fun findInput line =
    let val marker = "\\input{"
        val mlen = size marker
        fun find i =
            if i + mlen > size line then NONE
            else if String.substring (line, i, mlen) = marker then SOME i
            else find (i + 1)
    in
      case find 0 of
          NONE => NONE
        | SOME i =>
            let val start = i + mlen
                fun close j =
                    if j >= size line then NONE
                    else if String.sub (line, j) = #"}" then SOME j
                    else close (j + 1)
            in
              case close start of
                  NONE => NONE
                | SOME j =>
                    SOME (String.substring (line, start, j - start))
            end
    end

(* Sub-file stems are written without trailing extension.  But
   `\input{HolSat.tex}` appears in libraries.stex; strip a
   trailing ".tex" if present so the lookup against declared
   children works. *)
fun stripDotTex s =
    if String.isSuffix ".tex" s
    then String.substring (s, 0, size s - 4)
    else s

(* --- SUMMARY.md output ----------------------------------------- *)

(* Walk parent .smd line-by-line; emit sub-entries (one per H2,
   nested H3s, and nested-file links interleaved by source
   position).  `children` is the set of declared sub-file stems
   for this chapter, used to filter \input occurrences. *)
fun emitSubEntries (children : string list) (ls : string list) =
    let
      val childSet = children
      fun isChild s = List.exists (fn c => c = s) childSet
      fun emitH2 t = emit ("  - [" ^ t ^ "]()\n")
      fun emitH3 t = emit ("    - [" ^ t ^ "]()\n")
      (* Emit a nested sub-file's leading H2 (as a real link to the
         file) and walk its subsequent H3 lines as draft sub-entries
         at the same indent depth parent H3s use, so the sidebar
         and mdbook's section-numbering both pick them up. *)
      fun emitNested stem =
          let
            val lines = smdLines stem
            fun emitH3s [] _ = ()
              | emitH3s (l :: rest) afterH2 =
                  if isHeading "## " l then
                    emitH3s rest true
                  else if isHeading "### " l andalso afterH2 then
                    ( emitH3 (cleanTitle (stripPrefix "### " l))
                    ; emitH3s rest afterH2 )
                  else emitH3s rest afterH2
          in
            case extractFirstH2 lines of
                NONE => die ("No leading H2 in " ^ stem ^
                             ".smd (nested sub-files start at H2)")
              | SOME title =>
                  ( emit ("  - [" ^ title ^ "](" ^ stem ^ ".smd)\n")
                  ; emitH3s lines false )
          end
      (* Track whether we've seen an H2 yet (H3s before any H2 are
         dropped, as in the original). *)
      fun go [] _ = ()
        | go (l :: rest) sawH2 =
            if isHeading "## " l then
              ( emitH2 (cleanTitle (stripPrefix "## " l))
              ; go rest true )
            else if isHeading "### " l andalso sawH2 then
              ( emitH3 (cleanTitle (stripPrefix "### " l))
              ; go rest sawH2 )
            else
              (case findInput l of
                   SOME raw =>
                     let val stem = stripDotTex raw
                     in
                       if isChild stem andalso
                          fileExists (stem ^ ".smd")
                       then ( emitNested stem ; go rest sawH2 )
                       else go rest sawH2
                     end
                 | NONE => go rest sawH2)
    in go ls false end

fun emitSummary (bookTitle : string) (chaps : chap list) =
    let
      fun emitChap (stem, children) =
          if not (fileExists (stem ^ ".smd")) then ()
          else let
            val ls = smdLines stem
            val title = case extractH1 ls of
                            SOME t => t
                          | NONE => die ("No H1 in " ^ stem ^ ".smd")
          in
            emit ("- [" ^ title ^ "](" ^ stem ^ ".smd)\n");
            emitSubEntries children ls
          end
    in
      emit ("# Summary\n\n# " ^ bookTitle ^ "\n\n");
      List.app emitChap chaps
    end

(* --- chapters-include.tex output ------------------------------- *)

fun emitLatexInclude (chaps : chap list) =
    ( emit "% Generated by Manual/Tools/gen_chap_lists from\n"
    ; emit "% Manual/Description/chapters.txt; do not edit by hand.\n"
    ; List.app (fn (s, _) => emit ("\\include{" ^ s ^ "}\n")) chaps )

(* --- entry point ----------------------------------------------- *)

fun main () =
    let val chaps = parseChaptersFile "chapters.txt"
    in case CommandLine.arguments () of
           ["summary"]              => emitSummary "The HOL System" chaps
         | ["summary", title]       => emitSummary title chaps
         | ["latex-include"]        => emitLatexInclude chaps
         | _ => die ("usage: gen_chap_lists summary [book-title] " ^
                     "| latex-include")
    end
