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

fun I x = x;

fun curry f x y = f (x,y)
fun equal x y = (x=y)
infix ##;
fun (f##g) (x,y) = (f x, g y);

val equal = curry (op=);

fun butlast [] = raise Fail "butlast"
  | butlast [x] = []
  | butlast (h::t) = h::butlast t;

fun flat [] = []
  | flat ([]::rst) = flat rst
  | flat ((h::t)::rst) = h::flat(t::rst);

infixr 4 \/ 
infixr 5 /\
fun (f \/ g) x = f x orelse g x
fun (f /\ g) x = f x andalso g x;

fun occurs s ss = not (isEmpty (#2 (position s ss)));

fun fetch_contents docfile =
  let val istrm = TextIO.openIn docfile
      val contents = Substring.all (TextIO.inputAll istrm)
      val _ = TextIO.closeIn istrm
  in contents
  end;

fun fetch str = Substring.string (fetch_contents str);

(*---------------------------------------------------------------------------
       A HOL ".doc" file has the format 

         \DOC <ident>
         
         ( \<keyword> <paragraph>* )*

         \ENDDOC
 ---------------------------------------------------------------------------*)

datatype markup 
   = PARA
   | TEXT of substring
   | BRKT of substring
   | XMPL of substring;

datatype section 
   = TYPE of substring
   | FIELD of string * markup list
   | SEEALSO of substring list;
   

fun divide ss = 
  if isEmpty ss 
    then []
    else let val (ss1,ss2) = position "\n\\" ss
         in ss1::divide (triml 2 ss2)
         end;

local val noindent = Substring.all "noindent"
      val noindent_size = Substring.size noindent
in
fun noindent_elim (ss1::ss2::rst) =
     let val (ssa,ssb) = position "noindent" ss2
     in if isEmpty ssa 
          then noindent_elim (all (concat[ss1, triml noindent_size ssb])::rst)
          else ss1::noindent_elim (ss2::rst)
     end
  | noindent_elim l = l
end;

local val BLTYPE = Substring.all "BLTYPE"
      val ELTYPE = Substring.all "ELTYPE"
      val TYPEss = Substring.all "TYPE"
      val BLTYPEsize = Substring.size ELTYPE
in
fun longtype_elim (l as (ss1::ss2::rst)) =
     let val (ssa,ssb) = position "BLTYPE" ss1
         val (ssc,ssd) = position "ELTYPE" ss2
     in if isEmpty ssa andalso isEmpty ssc
          then all(concat[TYPEss, triml BLTYPEsize ssb]) :: rst
          else l
     end
  | longtype_elim l = l
end;

fun to_sections ss =
  let open Substring
      val sslist = List.tl (divide ss)
      val sslist1 = noindent_elim (longtype_elim (butlast sslist))
  in 
   map ((string##I) o splitl (not o Char.isSpace)) sslist1
  end;

(*---------------------------------------------------------------------------
        Divide into maximal chunks of text enclosed by braces.  
 ---------------------------------------------------------------------------*)

fun braces ss n = 
  case getc ss
   of SOME(#"{", ss1) => braces ss1 (n+1)
    | SOME(#"}", ss1) => if n=1 then ss1 else braces ss1 (n-1)
    | SOME(_,    ss1) => braces ss1 n
    | NONE            => raise Fail "braces: expecting closing brace(s)"


fun markup ss =
 let val (ssa,ssb) = position "{" ss
 in if isEmpty ssb then [TEXT ss]
    else let val ssc = braces ssb 0
             val (s,i,n) = base ssa
             val (_,j,_) = base ssc
             val chunk = substring (s,i+n+1,j-(i+n+2))
         in TEXT ssa 
             :: (if occurs "\n" chunk then XMPL chunk else BRKT chunk)
             :: markup ssc
         end
 end;

val paragraphs = 
  let fun para (TEXT ss) = 
           let fun insP ss =
                let val (ssa,ssb) = position "\n\n" ss
                in if isEmpty ssb then [TEXT ss]
                   else TEXT ssa::PARA::insP (dropl Char.isSpace ssb)
                end
           in insP ss
           end
        | para other = [other]
  in flat o map para
  end;

(*---------------------------------------------------------------------------
       I should check that the closing parens are consecutive.
 ---------------------------------------------------------------------------*)

fun elim_double_braces ss =
 let val (ssa,ssb) = position "{{" ss
 in if isEmpty ssb then ss
    else let val ssc = braces ssb 0
             val (s,i,n) = base ssa
             val (_,j,_) = base ssc
             val chunk = substring (s,i+n+1,j-(i+n+2))
         in 
           all (concat [ssa,elim_double_braces chunk,elim_double_braces ssc])
         end
 end;

fun parse_type ss =
 let val ss' = 
      case getc (dropl Char.isSpace ss)
       of SOME(#"{", ss1) => 
           let val ss2 = dropr Char.isSpace ss1
           in if sub(ss2,size ss2 - 1) = #"}" then trimr 1 ss2 
              else raise Fail "parse_type: closing brace not found"
           end
        | other => ss
  in elim_double_braces ss'
  end

fun parse docfile = 
 let fun db_out (BRKT ss) = BRKT (elim_double_braces ss) 
       | db_out (XMPL ss) = XMPL (elim_double_braces ss)
       | db_out otherwise = otherwise

     fun section (tag, ss) = 
       case tag 
        of "TYPE" => TYPE (parse_type ss)
         | "SEEALSO" => SEEALSO
                          (tokens (Char.isSpace \/ equal #",")
                             (dropr (Char.isSpace \/ equal #".") ss))
         | otherwise => FIELD (tag, List.map db_out (paragraphs (markup ss)))
  in
     List.map section (to_sections (fetch_contents docfile))
  end;

(* Snarfed from Htmlsigs.sml *)
fun encode #"<" = "&lt;"
  | encode #">" = "&gt;"
  | encode #"&" = "&amp;"
  | encode c    = String.str c;

fun del_bslash #"\\" = ""
  | del_bslash c     = String.str c;

fun html (name,sectionl) ostrm =
 let fun outss ss = TextIO.output(ostrm, Substring.translate encode ss)
     fun out s = TextIO.output(ostrm,s)
     fun markout PARA = out "\n<P>\n"
       | markout (TEXT ss) = outss ss
       | markout (BRKT ss) = 
           (out "<FONT size = \"-1\" color = \"crimson\"><KBD>";
            outss (elim_double_braces ss); 
            out "</KBD></FONT>")
       | markout (XMPL ss) = 
           (out "<FONT size = \"-1\"><PRE>";
            outss (elim_double_braces ss); 
            out "</PRE></FONT>")

     fun markout_section (FIELD ("KEYWORDS", _)) = ()
       | markout_section (FIELD (tag, ss))
           = (out "<DT><STRONG>"; out tag; out "</STRONG>\n";
              out "<DD>"; List.app markout ss;
              out "<P>\n")
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
                out "<DT><STRONG>SEEALSO</STRONG>&nbsp;&nbsp;";
                outlinks sslist
             end
       | markout_section (TYPE _) = raise Fail "markout_section: TYPE"

     fun front_matter (TYPE ss) =
           (out "<HTML><HEAD></HEAD>\n";
            out "<BODY BGCOLOR=\"#fbf2e7\">\n\n";
            out "<H1>";
            out "<FONT size = \"+1\" color = \"crimson\"><STRONG><PRE>";
            outss ss; 
            out "</PRE></STRONG></FONT></H1>\n\n")
       | front_matter _ = raise Fail "front_matter: expected TYPE"

     fun back_matter (www,release) =
      (out "<BR>\n";
       out "<EM><A HREF=\""; out www; 
       out"\">HOL</A>&nbsp;&nbsp;";
       out release; out "</EM>\n</BODY></HTML>\n")

  in
     front_matter (hd sectionl);
     out "<DL>\n";
     List.app markout_section (tl sectionl);
     out "</DL>\n\n";
     back_matter ("http://www.cl.cam.ac.uk/Research/HVG/FTP/", "Kananaskis 0")
  end;
 

fun trans htmldir docfile =
 case Path.splitBaseExt docfile
  of {base,ext=SOME "doc"} =>
      (let val file = Path.file base
         val outfile = Path.joinBaseExt
                         {base=Path.concat(htmldir,file),ext=SOME"html"}
         val ostrm = TextIO.openOut outfile
       in 
          html (Path.file base,parse docfile) ostrm
        ; TextIO.closeOut ostrm
       end
       handle e => print ("Failed to translate file: "
                    ^docfile^"---"^exnMessage e^"\n"))
   | otherwise => print ("Failed to parse file name: "^docfile^"\n");



fun docdir_to_htmldir docdir htmldir =
 let open FileSys
     val dstrm = openDir docdir
     val trans_html = trans htmldir
     fun loop () = 
        case readDir dstrm 
         of NONE => ()
          | SOME docfile => 
             let val fulldocfile = Path.concat (docdir,docfile)
             in 
                 print ("Translating "^fulldocfile^"\n");
                 trans_html fulldocfile;
                 loop()
             end
 in loop()
  ; closeDir dstrm
  ; print "\nFinished translating docfiles to html.\n\n"
 end;

val _ = 
    case CommandLine.arguments () 
     of [docdir,htmldir] => docdir_to_htmldir docdir htmldir
      | otherwise => print "Usage: Doc2Html <docdir> <htmldir>\n"

