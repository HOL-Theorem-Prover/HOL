structure HOLPage = struct
open Database;

fun equal x y = (x=y);
fun curry f x y = f (x,y);

fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);

val normPath = (* string list -> string *)
  OS.Path.toString o OS.Path.fromString o itstrings (curry OS.Path.concat);

fun destProperSuffix s1 s2 =
  let val sz1 = String.size s1
      val sz2 = String.size s2
      open Substring
 in
   if sz1 >= sz2 then NONE
   else let val (prefix, suffix) = splitAt(full s2, sz2 - sz1)
        in if string suffix = s1 then SOME (string prefix) else NONE
       end
 end;

val dropTheory = destProperSuffix "Theory";
val dropLib    = destProperSuffix "Lib";
val dropSyntax = destProperSuffix "Syntax";
val dropSimps  = destProperSuffix "Simps";

fun find_most_appealing HOLpath docfile =
  let open OS.Path OS.FileSys
      val {dir,file} = splitDirFile docfile
      val {base,ext} = splitBaseExt file
      val docfile_dir = concat(HOLpath,dir)
      val htmldir  = concat(docfile_dir,"HTML")
      val htmlfile = joinBaseExt{base=base,ext=SOME "html"}
      val adocfile = joinBaseExt{base=base,ext=SOME "adoc"}
      val htmlpath = normPath[htmldir,htmlfile]
      val adocpath = normPath[docfile_dir,adocfile]
      val docpath  = normPath[docfile_dir,file]
  in
     if OS.FileSys.access(htmlpath,[A_READ]) then SOME htmlpath else
     if OS.FileSys.access(adocpath,[A_READ]) then SOME adocpath else
     if OS.FileSys.access(file,[A_READ]) then SOME docpath
     else NONE
  end;

fun printHOLPage version bgcolor HOLpath idIndex TheoryIndex (dbfile, outfile)
  = let val db = readbase dbfile
	val os = TextIO.openOut outfile
	fun out s = TextIO.output(os, s)
	fun href anchor target =
	    app out ["<A HREF=\"file://", target, "\">", anchor, "</A>"]
	fun idhref file line anchor =
	    href anchor (concat [file, ".html#line", Int.toString line])
	fun strhref file anchor = href anchor (file ^ ".html")
	fun mkref line file = idhref file line file
        val sigspath = normPath[HOLpath,"help","src-sml","htmlsigs"]
        fun path front file = normPath[front, file^".html"]

        fun class_of drop {comp=Str, file, line} =
             (case drop file
               of SOME name => SOME(name, path sigspath file)
                | NONE => NONE)
          | class_of _ otherwise = NONE

        val theory_of  = class_of dropTheory
        val library_of = class_of dropLib
        val syntax_of  = class_of dropSyntax
        val simps_of   = class_of dropSimps

        fun misc_struct_of {comp=Str, file, line} =
              if isSome (dropTheory file) orelse
                 isSome (dropLib file) orelse
                 isSome (dropSyntax file) orelse
                 isSome (dropSimps file)
              then NONE
              else SOME(file, path sigspath file)
          | misc_struct_of otherwise = NONE

	fun prentries [] = ()
	  | prentries ((anchor,path)::rst) =
              let
              in href anchor path
               ; out "&nbsp;&nbsp;&nbsp;&nbsp;\n"
               ; prentries rst
              end
	fun prtree f Empty = ()
	  | prtree f (Node(key, entries, t1, t2)) =
	    (prtree f t1;
	     prentries (List.mapPartial f entries);
	     prtree f t2)
    in
	out "<HTML>\
	 \<HEAD><TITLE>HOL Reference Page</TITLE></HEAD>\n";
	out "<BODY BGCOLOR=\""; out bgcolor; out "\">\n";
	out "<H1>HOL Reference Page</H1>\n";

	out "<DL>";

        out"<DT><STRONG>LIBRARIES</STRONG>";
        out"<DD>"; prtree library_of db;
        out "<P>";

        out"<DT><STRONG>THEORIES</STRONG>\n";
        out "&nbsp;&nbsp;&nbsp;\n";
        href "(Theory Graph)"
             (normPath [HOLpath,"help/theorygraph/theories.html"]);
        out "\n";
        out"<DD>"; prtree theory_of db;
        out "<P>";

        out "<DT><STRONG>STRUCTURES</STRONG>";
        out "<DD>"; prtree misc_struct_of db;
        out "<P>";

        out"<DT><STRONG>SYNTAX</STRONG>";
        out"<DD>"; prtree syntax_of db;
        out "<P>";

        out"<DT><STRONG>SIMPLIFICATION SETS</STRONG>";
        out"<DD>"; prtree simps_of db;
        out "<P>";

        out"<DT><STRONG>";
        href "IDENTIFIERS" idIndex;
        out "&nbsp;&nbsp;&nbsp;&nbsp;";
        href "THEORY BINDINGS" TheoryIndex;
        out "</STRONG>";
        out "<P>";
	out "</DL>\n";

	out "<BR><EM>"; out version; out "</EM>";
	out "</BODY></HTML>\n";
	TextIO.closeOut os
    end
end
