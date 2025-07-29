structure Doc2markdown2 =
struct

open ParseDoc

val toLower = String.implode o map Char.toLower o String.explode

fun endsWith suff haystack = let
  val m = String.size suff
  val n = String.size haystack
  in m <= n andalso String.extract (haystack, n - m, NONE) = suff end

fun splitOn c s = let
  fun loop i j out =
    if i = 0 then String.substring (s, i, j - i) :: out
    else case i - 1 of i' =>
      if c = String.sub (s, i')
      then loop i' i' (String.substring (s, i, j - i) :: out)
      else loop i' j out
  in case String.size s of sz => loop sz sz [] end

datatype doc
  = DocText of string
  | DocDoc of ParseDoc.section list

fun docToMarkdown (DocText s) = "```plaintext\n"^s^"\n```\n"
  | docToMarkdown (DocDoc secs) = let
    fun getSec x = let
      fun go [] = NONE
        | go (FIELD (s, md) :: ss) =
          if x = s then case md of [TEXT s] => SOME s | _ => NONE else go ss
        | go (_::ss) = go ss
      in go secs end
    val mds = DArray.new (8, Substring.full "")
    fun push x = DArray.push (mds, x)
    val pushS = push o Substring.full
    val trim = Substring.dropl Char.isSpace o Substring.dropr Char.isSpace
    fun escapeText ss = let
      val (s, lo, len) = Substring.base ss
      val stop = lo + len
      fun push1 start p = if start = p then () else
        push (Substring.extract (s, start, SOME (p - start)))
      fun go start p = if p = stop then push1 start p else
        (* if Char.contains "\\`*_{}[]()#+-!~>" (String.sub (s, p)) then
          (push1 start p; pushS "\\"; go p (p+1))
        else  *)
        go start (p+1)
      in go lo lo end
    fun field PARA = pushS "\n\n"
      | field (TEXT s) = escapeText s
      | field (BRKT s) = (pushS "```"; push s; pushS "```")
      | field (XMPL s) = (pushS "```hol4\n"; push s; pushS "```\n")
      | field (EMPH s) = (pushS "*"; escapeText s; pushS "*")
    fun sec (TYPE s) = (
        pushS "```hol4\n";
        case case getSec "STRUCTURE" of NONE => getSec "LIBRARY" | s => s of
          NONE => push s
        | SOME ss => (push (trim ss); pushS "."; push s);
        pushS "\n```\n\n---\n\n")
      | sec (FIELD ("DOC", _)) = ()
      | sec (FIELD ("STRUCTURE", _)) = ()
      | sec (FIELD ("LIBRARY", _)) = ()
      | sec (FIELD ("KEYWORDS", _)) = ()
      | sec (FIELD ("COMMENTS", m)) = (pushS "### Comments\n\n"; app field m; pushS "\n\n")
      | sec (FIELD ("USES", m)) = (pushS "### Uses\n\n"; app field m; pushS "\n\n")
      | sec (FIELD ("FAILURE", m)) = (pushS "### Failure\n\n"; app field m; pushS "\n\n")
      | sec (FIELD ("EXAMPLE", m)) = (pushS "### Example\n\n"; app field m; pushS "\n\n")
      | sec (FIELD (_, m)) = (app field m; pushS "\n\n")
      | sec (SEEALSO []) = ()
      | sec (SEEALSO (m::ms)) = (
        pushS "### See Also\n`"; push (trim m);
        app (fn s => (pushS "`, `"; push s)) ms;
        pushS "`\n\n")
    in app sec secs; Substring.concat (DArray.toList mds) end

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

fun capitalise s = CharVector.tabulate (
  size s,
  (fn i => if i = 0 then Char.toUpper (String.sub (s,0))
           else Char.toLower (String.sub(s,i)))
);

fun trans_secnm "DESCRIBE" = "Description"
  | trans_secnm s = capitalise s


fun max_bticks s =
    let fun doit prevbtcount mx i =
            if i < 0 then Int.max(mx,prevbtcount)
            else if String.sub(s, i) = #"`" then
              doit (prevbtcount + 1) mx (i - 1)
            else doit 0 (Int.max(prevbtcount, mx)) (i - 1)
    in
      doit 0 0 (size s - 1)
    end

fun brkt_text s =
    let val btcount = max_bticks s
        val btstring = CharVector.tabulate (btcount, fn _ => #"`")
    in
      if btcount = 0 then s
      else
        btstring ^ " " ^ s ^ " " ^ btstring
    end

val emph_text = String.translate (fn #"*" => "\\*" | c => str c)
fun xmpl_text s = "    " ^ String.translate (fn #"\n" => "\n    " | c => str c) s

fun html_linkify s = "[" ^ s ^ "](" ^ s ^ ".html)"

fun text_encode ss = let
  (* passes over a substring, replacing single apostrophes with &rsquo;
     backquotes with &lsquo; and the "latex" encodings of nice double-quotes:
     `` with &ldquo; and '' with &rdquo;
     Also encodes the < > and & characters into HTML appropriate forms. *)
  open Substring
  datatype state = backquote | apostrophe | normal of int * substring
  val lsquo = "\226\128\152"
  val rsquo = "\226\128\153"
  val ldquo = "\226\128\156"
  val rdquo = "\226\128\157"
  fun recurse acc s ss =
      case (s, getc ss) of
        (backquote, NONE) => (lsquo :: acc)
      | (apostrophe, NONE) => (rsquo :: acc)
      | (normal(n,ss0), NONE) => (string ss0 :: acc)
      | (normal (n,ss0), SOME(#"'", ss')) =>
          recurse (string (slice(ss0,0,SOME n)) :: acc) apostrophe ss'
      | (normal(n,ss0), SOME(#"`", ss')) =>
          recurse (string (slice(ss0,0,SOME n))::acc) backquote ss'
      | (normal(n,ss0), SOME(c, ss')) => recurse acc (normal(n + 1, ss0)) ss'
      | (apostrophe, SOME(#"'", ss')) =>
          recurse (rdquo :: acc) (normal(0,ss')) ss'
      | (apostrophe, SOME(#"`", ss')) =>
          recurse (rsquo :: acc) backquote ss'
      | (apostrophe, SOME _) =>
          recurse (rsquo :: acc) (normal(0,ss)) ss
      | (backquote, SOME(#"`", ss')) =>
          recurse (ldquo :: acc) (normal(0,ss')) ss'
      | (backquote, SOME(#"'", ss')) =>
          recurse (lsquo :: acc) apostrophe ss'
      | (backquote, SOME _) =>
          recurse (lsquo :: acc) (normal(0,ss)) ss
in
  String.concat (List.rev (recurse [] (normal(0,ss)) ss))
end

fun markdown (name,sectionl) ostrm =
    let fun out s = TextIO.output(ostrm, s)
        fun outss ss = out (Substring.string ss)
        fun mdtext elem =
            case elem of
                BRKT ss => out ("`" ^ brkt_text (Substring.string ss) ^ "`")
              | EMPH ss => out ("*" ^ emph_text (Substring.string ss) ^ "*")
              | PARA => out "\n\n"
              | TEXT ss => out (text_encode ss)
              | XMPL ss => out (xmpl_text (Substring.string ss))

        fun mdsection sec =
            case sec of
                SEEALSO sslist =>
                (out "\n## See Also\n\n";
                 out (String.concatWith
                        ", "
                        (map (html_linkify o Substring.string) sslist));
                 out "\n\n")
              | TYPE ss =>
                (out ("\n## Type\n\n```\n" ^ Substring.string ss ^ "\n```\n\n"))
              | FIELD ("DOC", [TEXT ss]) => out ("# `" ^ brkt_text (Substring.string ss) ^ "`\n\n")
              | FIELD (secnm, textelems) =>
                (out ("\n## " ^ trans_secnm secnm ^ "\n\n");
                 List.app mdtext textelems;
                 out "\n")

    in
      List.app mdsection sectionl
    end


fun trans mddir docdir ((str,nm), docfile) = let
  val docbase = OS.Path.base docfile
  val docpath = OS.Path.concat (docdir, docfile)
  val outfile = OS.Path.joinBaseExt{base = OS.Path.concat(mddir, docbase),
                                    ext = SOME "md"}
  val ostrm = TextIO.openOut outfile
in
    TextIO.output(ostrm, docToMarkdown (DocDoc (parse_file docpath)))
  ; TextIO.closeOut ostrm
end handle e => die ("Exception raised: " ^ General.exnMessage e)


fun docdir_to_mddir docdir mddir =
    let  open OS.FileSys
         val docfiles = ParseDoc.find_docfiles docdir
         val _ = isDir mddir orelse die ("Directory "^ mddir^" doesn't exist")
         val (tick,finish) =
             Flash.initialise ("Directory "^docdir^": ", Binarymap.numItems docfiles)
    in
      Binarymap.app (fn d => (trans mddir docdir d; tick())) docfiles;
      finish();
      OS.Process.exit OS.Process.success
    end



fun main() =
    case CommandLine.arguments() of
        [docdir,mddir] => docdir_to_mddir docdir mddir
      | otherwise => (print "Usage: Doc2markdown2 <docdir> <markdown-dir>\n";
                      OS.Process.exit OS.Process.failure)
end (* struct *)
