(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*  Invoked with, e.g.,                                                      *)
(*                                                                           *)
(*     Doc2Html "/home/kxs/kanan/help/Docfiles"                              *)
(*              "/home/kxs/kanan/help/Docfiles/html";                        *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)
structure Doc2Html = struct

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

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

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
       | markout (EMPH ss) =
            out ("<em>" ^ text_encode ss ^ "</em>")
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
       | markout_section (FIELD ("STRUCTURE", [TEXT s]))
           = (out "<DT><SPAN class = \"FIELD-NAME\">STRUCTURE</SPAN></DT>\n";
              out "<DD><DIV class = \"FIELD-BODY\">";
              out "<A HREF = \"../../src-sml/htmlsigs/";
              out (string s); out ".html\">";
              out (string s);
              out "</A></DIV></DD>\n")
       | markout_section (FIELD (tag, ss))
           = (out "<DT><SPAN class = \"FIELD-NAME\">";
              out (if tag = "DESCRIBE" then "DESCRIPTION" else tag);
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
                     out (encode_stem(string s)); out ".html\">";
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
           (out "<!DOCTYPE html>\n";
            out "<HTML>\n";
            out "<HEAD>\n";
            out "<META CHARSET=\"utf-8\">\n";
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
     back_matter ("http://hol.sourceforge.net",
                  Systeml.release ^ "-" ^ Int.toString Systeml.version)
  end;

fun trans htmldir docdir ((str,nm), docfile) = let
  val docbase = OS.Path.base docfile
  val docpath = OS.Path.concat (docdir, docfile)
  val outfile = OS.Path.joinBaseExt{base = OS.Path.concat(htmldir, docbase),
                                    ext = SOME "html"}
  val ostrm = TextIO.openOut outfile
in
    html ((if str <> "" then str ^ "." else "")^nm, parse_file docpath) ostrm
  ; TextIO.closeOut ostrm
end handle e => die ("Exception raised: " ^ General.exnMessage e)

fun docdir_to_htmldir docdir htmldir =
 let open OS.FileSys
     val docfiles = ParseDoc.find_docfiles docdir
     val (tick, finish) = Flash.initialise ("Directory "^docdir^": ",
                                            Binarymap.numItems docfiles)
 in
   Binarymap.app (fn d => (trans htmldir docdir d; tick())) docfiles;
   finish();
   OS.Process.exit OS.Process.success
 end

fun main () =
  case CommandLine.arguments ()
     of [docdir,htmldir] => docdir_to_htmldir docdir htmldir
      | otherwise => print "Usage: Doc2Html <docdir> <htmldir>\n"

end;
