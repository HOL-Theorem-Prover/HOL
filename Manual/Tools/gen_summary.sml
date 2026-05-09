(* Generate Manual/Description/SUMMARY.md from the chapter .smd
   sources.  The chapter ORDERING is hard-coded below (mdbook
   needs an explicit order; book.toml has none); chapter TITLES
   are extracted from each .smd's `# ` H1, and per-chapter
   sub-entries from each `## ` H2.

   Usage (from Manual/Description/):
     ../Tools/gen_summary > SUMMARY.md

   The sub-entries are emitted as draft-chapter links (`[Title]()`)
   because mdbook's SUMMARY.md doesn't natively support
   `chapter.md#anchor` style entries.  theme/index.hbs has a small
   JS that post-processes those drafts into clickable anchor
   links on page load. *)

(* Hard-coded chapter ordering: edit this list when chapters are
   added, removed, or reordered.  Filenames are relative to
   Manual/Description/.  Titles come from each file's H1. *)
val chapterFiles =
    [ "system.smd"
    , "drules.smd"
    , "conv.smd"
    , "tactics.smd"
    , "theories.smd"
    , "modern-syntax.smd" ]

(* Read whole file as a string. *)
fun readFile path =
    let val s = TextIO.openIn path
        val all = TextIO.inputAll s
        val () = TextIO.closeIn s
    in all end

(* Lines of a string, dropping a trailing empty after a final \n. *)
fun lines s =
    let val ls = String.fields (fn c => c = #"\n") s
    in case List.rev ls of
           "" :: rest => List.rev rest
         | _ => ls
    end

(* True iff [pre] is a prefix of [s] AND the next char (if any)
   isn't `#` -- so `# X` matches but `## X` doesn't. *)
fun isHeading pre s =
    String.isPrefix pre s andalso
    (size s = size pre orelse
     not (String.sub (s, size pre) = #"#"))

(* Strip a `^# ` prefix; trim trailing whitespace. *)
fun stripHeadingPrefix pre s =
    let val r = String.extract (s, size pre, NONE)
        (* Trim leading and trailing whitespace. *)
        val trimmed = Substring.string (Substring.dropr Char.isSpace
                                       (Substring.dropl Char.isSpace
                                                        (Substring.full r)))
    in trimmed end

(* Backticks in headings (e.g. `## The Theory `min``) are dropped
   so the slug-rewriting JS in theme/index.hbs sees a plain title.
   Not strictly needed but keeps the SUMMARY.md tidy. *)
fun cleanTitle s =
    String.translate (fn #"`" => "" | c => str c) s

fun extractH1 ls =
    let fun go [] = NONE
          | go (l :: rest) =
            if isHeading "# " l
            then SOME (cleanTitle (stripHeadingPrefix "# " l))
            else go rest
    in go ls end

fun extractH2s ls =
    let fun go [] acc = List.rev acc
          | go (l :: rest) acc =
            if isHeading "## " l
            then go rest (cleanTitle (stripHeadingPrefix "## " l) :: acc)
            else go rest acc
    in go ls [] end

fun emit s = TextIO.output (TextIO.stdOut, s)

fun processChapter file =
    let val ls = lines (readFile file)
        val title = case extractH1 ls of
                        SOME t => t
                      | NONE => raise Fail ("No H1 heading in " ^ file)
        val sections = extractH2s ls
    in
        emit ("- [" ^ title ^ "](" ^ file ^ ")\n");
        List.app (fn s => emit ("  - [" ^ s ^ "]()\n")) sections
    end

fun main () =
    ( emit "# Summary\n\n# The HOL System\n\n"
    ; List.app processChapter chapterFiles )
