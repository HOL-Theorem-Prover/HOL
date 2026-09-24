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
      | SOME s => SOME {markdown = linkAnchors (stripFrontmatter s),
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

in

val _ = LSPExtension.registerInit true "Help"
          (fn () => LSPExtension.helpLookup := helpLookup)

end;
