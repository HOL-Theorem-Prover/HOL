(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*  Invoked with, e.g.,                                                      *)
(*                                                                           *)
(*     Doc2Html "/home/kxs/kanan/help/Docfiles"                              *)
(*              "/home/kxs/kanan/help/Docfiles/html";                        *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)


(* app load ["Substring", "TextIO", "Char", "FileSys"]; *)

open Substring;

fun curry f x y = f (x,y)
fun equal x y = (x=y)
infix ##;
fun (f##g) (x,y) = (f x, g y);

infixr 4 \/
infixr 5 /\
fun (f \/ g) x = f x orelse g x
fun (f /\ g) x = f x andalso g x;

open ParseDoc

fun txt_helper #"<" = SOME "&lt;"
  | txt_helper #">" = SOME "&gt;"
  | txt_helper #"&" = SOME "&amp;"
  | txt_helper c = NONE

fun encode c = Option.getOpt(txt_helper c, String.str c)
fun brkt_encode #" " = "&nbsp;"
  | brkt_encode c = encode c

fun text_encode ss = let
  (* passes over a substring, replacing single apostrophes with &rsquo;
     backquotes with &lsquo; and the "latex" encodings of nice double-quotes:
     `` with &ldquo; and '' with &rdquo;
     Also encodes the < > and & characters into HTML appropriate forms. *)
  open Substring
  datatype state = backquote | apostrophe | normal of int * substring
  fun recurse acc s ss =
      case (s, getc ss) of
        (backquote, NONE) => ("&lsquo;" :: acc)
      | (apostrophe, NONE) => ("&rsquo;" :: acc)
      | (normal(n,ss0), NONE) => (string ss0 :: acc)
      | (normal (n,ss0), SOME(#"'", ss')) =>
          recurse (string (slice(ss0,0,SOME n)) :: acc) apostrophe ss'
      | (normal(n,ss0), SOME(#"`", ss')) =>
          recurse (string (slice(ss0,0,SOME n))::acc) backquote ss'
      | (normal(n,ss0), SOME(c, ss')) => let
        in
          case txt_helper c of
            SOME s => recurse (s :: string (slice(ss0,0,SOME n)) :: acc)
                              (normal(0,ss'))
                              ss'
          | NONE => recurse acc (normal(n + 1, ss0)) ss'
        end
      | (apostrophe, SOME(#"'", ss')) =>
          recurse ("&rdquo;" :: acc) (normal(0,ss')) ss'
      | (apostrophe, SOME(#"`", ss')) =>
          recurse ("&rsquo;" :: acc) backquote ss'
      | (apostrophe, SOME _) =>
          recurse ("&rsquo;" :: acc) (normal(0,ss)) ss
      | (backquote, SOME(#"`", ss')) =>
          recurse ("&ldquo;" :: acc) (normal(0,ss')) ss'
      | (backquote, SOME(#"'", ss')) =>
          recurse ("&lsquo;" :: acc) apostrophe ss'
      | (backquote, SOME _) =>
          recurse ("&lsquo;" :: acc) (normal(0,ss)) ss
in
  String.concat (List.rev (recurse [] (normal(0,ss)) ss))
end


fun del_bslash #"\\" = ""
  | del_bslash c     = String.str c;

(* Location of style sheet *)
val cssURL = "doc.css";

fun html (name,sectionl) ostrm =
 let fun outss ss = TextIO.output(ostrm, Substring.translate encode ss)
     fun out s = TextIO.output(ostrm,s)
     val bracket_trans = Substring.translate brkt_encode
     fun markout PARA = out "\n<P>\n"
       | markout (TEXT ss) =
            (out "<SPAN class = \"TEXT\">";
             out  (text_encode ss);
             out "</SPAN>")
       | markout (BRKT ss) =
           (out "<SPAN class = \"BRKT\">";
            out (bracket_trans ss);
            out "</SPAN>")
       | markout (XMPL ss) =
           (out "<DIV class = \"XMPL\"><pre>";
            outss ss;
            out "</pre></DIV>\n")

     fun markout_section (FIELD ("KEYWORDS", _)) = ()
       | markout_section (FIELD ("DOC", _)) = ()
       | markout_section (FIELD (tag, ss))
           = (out "<DT><SPAN class = \"FIELD-NAME\">";
              out tag;
              out "</SPAN></DT>\n";
              out "<DD><DIV class = \"FIELD-BODY\">";
              List.app markout ss;
              out "</DIV></DD>\n")
       | markout_section (SEEALSO sslist)
           = let fun drop_qual ss =
                 case tokens (equal #".") ss
                  of [strName,fnName] => translate del_bslash fnName
                   | [Name] => string Name
                   | other => raise Fail (string ss)
                 fun link s =
                    (out "<A HREF = \"";
                     out (Symbolic.unsymb(string s)); out ".html\">";
                     out (drop_qual s); out "</A>")
                 fun outlinks [] = ()
                   | outlinks [s] = link s
                   | outlinks (h::t) = (link h; out",\n"; outlinks t)
             in
               (out "<dt><span class = \"FIELD-NAME\">SEEALSO</span></dt>\n";
                out "<dd><div class = \"FIELD-BODY\">";
                outlinks sslist;
                out "</div></dd>\n")
             end
       | markout_section (TYPE _) = raise Fail "markout_section: TYPE"

     fun front_matter name (TYPE ss) =
           (out "<!DOCTYPE HTML PUBLIC \"-//W32//DTD HTML 4.01//EN\"\
                 \ \"http://www.w3.org/TR/html4/strict.dtd\">\n";
            out "<HTML>\n";
            out "<HEAD>\n";
            out "<meta http-equiv=\"content-type\" content=\"text/html ; \
                \charset=US-ASCII\">\n";
            out "<TITLE>"; out name; out "</TITLE>\n";
            out "<LINK REL = \"STYLESHEET\" HREF = \"../";
            out cssURL;
            out "\" TYPE = \"text/css\">";
            out "</HEAD>\n";
            out "<BODY>\n\n";
            out "<DIV class = \"TYPE\"><PRE>";
            outss ss;
            out "</PRE></DIV>\n\n")
       | front_matter _ _ = raise Fail "front_matter: expected TYPE"

     fun back_matter (www,release) =
      (out "<div class = \"HOL\"><A HREF=\""; out www;
       out"\">HOL</A>&nbsp;&nbsp;";
       out release;
       out "</div></BODY></HTML>\n")

     val sectionl = tl sectionl

  in
     front_matter name (hd sectionl);
     out "<DL>\n";
     List.app markout_section (tl sectionl);
     out "</DL>\n\n";
     back_matter ("http://hol.sourceforge.net", "Kananaskis-5")
  end;

fun trans htmldir docdir docname = let
  val docfile = Path.joinBaseExt{base = Path.concat(docdir, docname),
                                 ext = SOME "doc"}
  val outfile = Path.joinBaseExt{base = Path.concat(htmldir, docname),
                                 ext = SOME "html"}
  val ostrm = TextIO.openOut outfile
in
    html (docname, parse_file docfile) ostrm
  ; TextIO.closeOut ostrm
end

fun docdir_to_htmldir docdir htmldir =
 let open FileSys
     val docfiles = ParseDoc.find_docfiles docdir
     val (tick, finish) = Flash.initialise ("Directory "^docdir^": ",
                                            Binaryset.numItems docfiles)
 in
   Binaryset.app (fn d => (trans htmldir docdir d; tick())) docfiles;
   finish();
   Process.exit Process.success
 end

val _ =
    case CommandLine.arguments ()
     of [docdir,htmldir] => docdir_to_htmldir docdir htmldir
      | otherwise => print "Usage: Doc2Html <docdir> <htmldir>\n"

