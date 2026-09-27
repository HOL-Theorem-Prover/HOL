(* ----------------------------------------------------------------------
   Installs `LSPExtension.helpLookup': the name under the cursor to the
   text of its Reference entry, for the hover to show below the type.

   Two build products, neither in the repository, and both written by
   `bin/build's help step:

     help/HOL.Help                            the index, from makebase
     Manual/build/Docfiles-processed/*.smd    the entries themselves

   A tree built with `--no-helpdocs' has neither, and the hover then
   shows what it always did.  The entries are the polyscripter-evaluated
   mirror of `help/Docfiles/*.smd' -- markdown a client can render,
   unlike the `.txt' beside each source (a pandoc plain-text rendering)
   or the source itself (still carrying its frontmatter and `>>'
   directives).

   Here rather than in `tools-poly/poly/Help.sml', which reads the same
   index for the REPL's `help': none of what follows -- frontmatter,
   the manual's anchor scheme, `file://' URIs -- is reachable from a
   REPL, and `Help' is a terminal pager that should not have to know
   about any of it.  `hol.ML' loads `help/src-sml/Database' just before
   this file; nothing else here needs a load.
   ---------------------------------------------------------------------- *)

local

val HOLDIR = Systeml.HOLDIR
fun under l = OS.Path.toString (OS.Path.fromString
                (List.foldl (fn (s, a) => OS.Path.concat (a, s)) HOLDIR l))

val indexfile = under ["help", "HOL.Help"]
val entrydir = under ["Manual", "build", "Docfiles-processed"]

val toLower = String.implode o map Char.toLower o String.explode

fun splitOn c s = String.fields (fn c' => c' = c) s

fun readToString file = let
  val istr = TextIO.openIn file
  in TextIO.inputAll istr before TextIO.closeIn istr end

(* The processed entry for `base', if one has been built.  An entry's
   filename is its name with non-alphanumerics `UC_ASCII_Encode'd, and
   so is the anchor the manual writes for it, so this needs no
   encoding of its own. *)
fun findProcessed base = let
  val p = OS.Path.concat (entrydir, base ^ ".smd")
  in if HOLFileSys.exists_readable p then SOME p else NONE end

(* An entry opens with the YAML frontmatter its source carried
   (`aliases:', and `canonical:'/`generated:' on an alias stub).  In a
   rendered hover the opening `---' is a horizontal rule and the keys
   below it are body text, so drop the block. *)
fun stripFrontmatter s =
  if not (String.isPrefix "---\n" s) then s
  else let
    fun drop [] = s  (* unterminated: leave it alone *)
      | drop ("---" :: rest) = String.concatWith "\n" rest
      | drop (_ :: rest) = drop rest
  in drop (List.tl (splitOn #"\n" s)) end

(* Drop every `\\cmd{...}' call, brace-matched, and any line the
   removal leaves blank that was not blank before -- an `\\index{}'
   alone on its line would otherwise leave one, and a blank line makes
   the next 4-space-indented line reparse as a code block.  Mirrors
   `stripCmd' in Manual/Tools/smdpp.sml. *)
fun stripCmd cmdName s = let
  val sz = String.size s
  val cmd = "\\" ^ cmdName ^ "{"
  val cmdsz = String.size cmd
  fun matchAt i =
    i + cmdsz <= sz andalso String.substring (s, i, cmdsz) = cmd
  fun skipBraces (i, depth) =
    if i >= sz then i
    else case String.sub (s, i) of
           #"{" => skipBraces (i + 1, depth + 1)
         | #"}" => if depth = 1 then i + 1 else skipBraces (i + 1, depth - 1)
         | _ => skipBraces (i + 1, depth)
  fun loop (i, acc) =
    if i >= sz then String.concat (List.rev acc)
    else if matchAt i then loop (skipBraces (i + cmdsz, 1), acc)
    else loop (i + 1, String.str (String.sub (s, i)) :: acc)
  fun isBlank ln = CharVector.all Char.isSpace ln
  fun zip ([], [], acc) = List.rev acc
    | zip (o1 :: orest, n1 :: nrest, acc) =
      if isBlank n1 andalso not (isBlank o1) then zip (orest, nrest, acc)
      else zip (orest, nrest, n1 :: acc)
    | zip (_, news, acc) = List.rev acc @ news
  in
    if not (String.isSubstring cmd s) then s
    else String.concatWith "\n"
           (zip (splitOn #"\n" s, splitOn #"\n" (loop (0, [])), []))
  end

(* Pandoc raw fenced blocks, ```{=<fmt>} ... ```.  The PDF pipeline
   hands the body to the matching writer and discards the rest, and
   mdbook's markdown parser does not, so smdpp disposes of them: a
   `{=mdbook}' block keeps its body, any other drops body and all.
   Mirrors `handleRawBlocks' in Manual/Tools/smdpp.sml.  Neither
   renderer ever shows a `{=latex}' body, so nor does a hover. *)
fun handleRawBlocks s = let
  fun firstTok ln = case String.tokens Char.isSpace ln of
                      [] => NONE
                    | t :: _ => SOME t
  fun fenceOpenFormat ln =
    case firstTok ln of
      SOME t =>
      if String.isPrefix "```{=" t andalso String.isSuffix "}" t
      then SOME (String.substring (t, 5, String.size t - 6))
      else NONE
    | NONE => NONE
  fun isFenceClose ln = firstTok ln = SOME "```"
  datatype state = Outside | Stripping | Inlining
  fun loop ([], acc, _) = List.rev acc
    | loop (l :: rest, acc, Stripping) =
      loop (rest, acc, if isFenceClose l then Outside else Stripping)
    | loop (l :: rest, acc, Inlining) =
      if isFenceClose l then loop (rest, acc, Outside)
      else loop (rest, l :: acc, Inlining)
    | loop (l :: rest, acc, Outside) =
      case fenceOpenFormat l of
        SOME "mdbook" => loop (rest, acc, Inlining)
      | SOME _ => loop (rest, acc, Stripping)
      | NONE => loop (rest, l :: acc, Outside)
  in String.concatWith "\n" (loop (splitOn #"\n" s, [], Outside)) end

(* What smdpp deletes on the way to HTML, deleted here too.  These are
   the constructs whose correct rendering is *absence*: an author has
   no reason to expect an `\\index{}' or a `{=latex}' block to surface
   anywhere, so nothing would stop them writing one, and a hover that
   passed it through would be the only place it showed up.

   The constructs smdpp *resolves* -- `\\ref{}', `\\refentry{}',
   `\\cite{}' -- are left as written.  A hover cannot follow them, but
   deleting a cross-reference is worse than showing one the reader has
   to look up; and `](#Foo.bar)', the one that is resolvable from here,
   is resolved below. *)
fun dropPandocOnly s = stripCmd "label" (handleRawBlocks (stripCmd "index" s))

(* `file://' URI for an absolute path.  Percent-encoded, so a path
   holding a space or a bracket still travels as one markdown link
   destination. *)
fun fileUri path = let
  fun enc c =
    if Char.isAlphaNum c orelse Char.contains "-._~/" c
    then String.str c
    else "%" ^ StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (Char.ord c))
  in "file://" ^ String.translate enc path end

(* An entry's cross-references -- its "See also" list, and the "Also
   exported as" banner -- are written against the single-page anchor
   scheme the Reference manual used to have: `](#Foo.bar)'.  The mdbook
   build rewrites those to its own pages and the PDF resolves them as
   real anchors; a hover can do neither, so point each at the entry's
   own file.  A reference to an entry that no longer exists is left as
   written -- the manual build reports those separately. *)
fun linkAnchors s = let
  fun isNameChar c = Char.isAlphaNum c orelse Char.contains "._'" c
  fun go ss acc = let
    val (pre, rest) = Substring.position "](#" ss
    val acc = Substring.string pre :: acc
  in
    if Substring.isEmpty rest then String.concat (List.rev acc)
    else let
      val body = Substring.triml 3 rest
      val (name, tail) = Substring.splitl isNameChar body
    in
      case (Substring.first tail, findProcessed (Substring.string name)) of
        (SOME #")", SOME p) =>
          go (Substring.triml 1 tail) (")" :: fileUri p :: "](" :: acc)
      | _ => go body ("](#" :: acc)
    end
  end
  in go (Substring.full s) [] end

(* The entry's text, and the file to send a reader to for the whole of
   it.  `file' is what the index recorded -- `help/Docfiles/<base>.txt',
   relative to HOLDIR -- which names the entry and, where the processed
   mirror has been cleaned away, is still readable as plain text. *)
fun getDoc file = let
  fun read f = SOME (readToString f) handle _ => NONE
  fun plain () =
    case read (OS.Path.concat (HOLDIR, file)) of
      NONE => NONE
    | SOME s => SOME {markdown = "```plaintext\n" ^ s ^ "\n```\n",
                      link = NONE}
  in
    case findProcessed (OS.Path.base (OS.Path.file file)) of
      NONE => plain ()
    | SOME p =>
      case read p of
        NONE => plain ()
      | SOME s => SOME {markdown =
                          linkAnchors (dropPandocOnly (stripFrontmatter s)),
                        link = SOME p}
  end

(* The index, read once and kept.  `NONE' is a tree whose help
   documentation has not been built, and is remembered as such: without
   that the next hover tries again, and a hover is not a place to
   discover the same missing file over and over. *)
val theDb = Sref.new (NONE : Database.database option option)

fun database () =
  Sref.gen_update theDb
    (fn SOME tried => (SOME tried, tried)
      | NONE => let
          val tried = SOME (Database.readbase indexfile) handle _ => NONE
        in (SOME tried, tried) end)

(* "\240\159\147\150" is U+1F4D6 OPEN BOOK: the link is the one piece of
   a hover that is not the entry's own text, and a marker glyph is what
   tells them apart at a glance. *)
fun render (fullName, {markdown, link}) =
  case link of
    NONE => markdown
  | SOME p =>
    markdown ^ "\n\n[\240\159\147\150 " ^ fullName ^ "](" ^ fileUri p ^ ")\n"

(* One name can name several entries -- `Cases_on' is `bossLib's and
   `BasicProvers's -- and `validate' is how the caller says which
   structure the identifier it is hovering actually came from. *)
fun helpLookup (id, validate) =
  case database () of
    NONE => []
  | SOME db => let
    fun build ({comp = Database.Term (fullName, SOME "HOL"), file, ...}, out) =
        (case splitOn #"." fullName of
           [] => out
         | hd :: tl =>
           if (case tl of
                 [] => hd = id
               | _ => List.last tl = id andalso validate hd)
           then case getDoc file of
                  NONE => out
                | SOME d => render (fullName, d) :: out
           else out)
      | build (_ : Database.entry, out) = out
    in List.foldr build [] (Database.lookup (db, toLower id)) end

(* Load-time selftest -- raises Fail on regression.

   No Reference entry carries any of these constructs today, so a test
   driven from the built tree would pass over zero cases and read
   exactly like a clean result.  They are what an author gains the
   moment an entry starts using what smdpp offers, which is the point
   of stripping them before anyone does. *)
local
  fun check (name, input, expected) =
    case dropPandocOnly input of
      out => if out = expected then ()
             else raise Fail ("help_init selftest [" ^ name ^
                              "]: expected " ^ String.toString expected ^
                              ", got " ^ String.toString out)
in
val () = List.app check [
  ("index-inline",
   "A \\index{simp}tactic.", "A tactic."),
  (* the line goes, rather than being left blank: a blank line here
     would make an indented line after it reparse as a code block *)
  ("index-own-line",
   "one\n\\index{a}\n    two", "one\n    two"),
  ("index-nested-braces",
   "x \\index{a{b}c} y", "x  y"),
  ("label-dropped",
   "See \\label{sec:x}here.", "See here."),
  ("latex-block-goes",
   "a\n```{=latex}\n\\input{HOLlist}\n```\nb", "a\nb"),
  ("html-block-goes",
   "a\n```{=html}\n<b>x</b>\n```\nb", "a\nb"),
  ("mdbook-block-keeps-its-body",
   "a\n```{=mdbook}\n*cap*\n```\nb", "a\n*cap*\nb"),
  (* a plain fenced block is content, not a raw block *)
  ("ordinary-fence-survives",
   "a\n``` hol4\n\\input{x}\n```\nb", "a\n``` hol4\n\\input{x}\n```\nb"),
  ("nothing-to-do",
   "plain text", "plain text")]
end

in

val _ = LSPExtension.registerInit true "Help"
          (fn () => LSPExtension.helpLookup := helpLookup)

end;
