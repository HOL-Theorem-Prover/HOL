
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

(* Snarfed from Htmlsigs.sml *)
fun encode #"<" = "&lt;"
  | encode #">" = "&gt;"
  | encode #"&" = "&amp;"
  | encode c    = String.str c;

fun del_bslash #"\\" = ""
  | del_bslash c     = String.str c;

(* Location of style sheet *)
val cssURL = "doc.css";

fun html (name,sectionl) ostrm =
 let fun outss ss = TextIO.output(ostrm, Substring.translate encode ss)
     fun out s = TextIO.output(ostrm,s)
     fun markout PARA = out "\n<P>\n"
       | markout (TEXT ss) =
            (out "<SPAN class = \"TEXT\">";
             outss ss;
             out "</SPAN>")
       | markout (BRKT ss) =
           (out "<SPAN class = \"BRKT\">";
            outss ss;
            out "</SPAN>")
       | markout (XMPL ss) =
           (out "<PRE><DIV class = \"XMPL\">";
            outss ss;
            out "</DIV></PRE>\n")

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
                   | outlinks (h::t) = (link h;
                                        out","; out "&nbsp;&nbsp;\n";
                                        outlinks t)
             in
               (out "<DT><SPAN class = \"FIELD-NAME\"><DT>SEEALSO</DT></SPAN>\n";
                out "<SPAN class = \"FIELD-BODY\"><DD>";
                outlinks sslist;
                out "</DD></SPAN>\n")
             end
       | markout_section (TYPE _) = raise Fail "markout_section: TYPE"

     fun front_matter name (TYPE ss) =
           (out "<HTML>\n";
            out "<HEAD>\n";
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
      (out "<BR>\n";
       out "<SPAN class = \"HOL\"><A HREF=\""; out www;
       out"\">HOL</A>&nbsp;&nbsp;";
       out release; out "</BODY></HTML>\n")

     val sectionl = tl sectionl

  in
     front_matter name (hd sectionl);
     out "<DL>\n";
     List.app markout_section (tl sectionl);
     out "</DL>\n\n";
     back_matter ("http://www.cl.cam.ac.uk/Research/HVG/FTP/", "Kananaskis 1")
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

