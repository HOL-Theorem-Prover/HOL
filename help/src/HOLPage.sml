open Database;

fun equal x y = (x=y);

fun destProperSuffix s1 s2 = 
  let val sz1 = String.size s1
      val sz2 = String.size s2
      open Substring
 in
   if sz1 >= sz2 then NONE
   else let val (prefix, suffix) = splitAt(all s2, sz2 - sz1)
        in if string suffix = s1 then SOME (string prefix) else NONE
       end
 end;

val dropTheory = destProperSuffix "Theory";
val dropLib    = destProperSuffix "Lib";
val dropSyntax = destProperSuffix "Syntax";
val dropSimps  = destProperSuffix "Simps";

fun find_most_appealing HOLpath docfile =
  let open Path FileSys
      val {dir,file} = splitDirFile docfile
      val {base,ext} = splitBaseExt file
      val docfile_dir = concat(HOLpath,dir)
      val htmldir  = concat(docfile_dir,"html")
      val htmlfile = joinBaseExt{base=base,ext=SOME "html"}
      val adocfile = joinBaseExt{base=base,ext=SOME "adoc"}
      val htmlpath = concat(htmldir,htmlfile)
      val adocpath = concat(docfile_dir,adocfile)
      val docpath  = concat(docfile_dir,file)
  in
     if FileSys.access(htmlpath,[A_READ]) then SOME htmlpath else
     if FileSys.access(adocpath,[A_READ]) then SOME adocpath else 
     if FileSys.access(file,[A_READ]) then SOME docpath
     else NONE
  end;

fun printHOLPage version bgcolor HOLpath (dbfile, outfile) =
    let val db = readbase dbfile
	val os = TextIO.openOut outfile
	fun out s = TextIO.output(os, s)
	fun href anchor target = 
	    app out ["<A HREF=\"", target, "\">", anchor, "</A>"]
	fun idhref file line anchor = 
	    href anchor (concat [file, ".html#line", Int.toString line])
	fun strhref file anchor = href anchor (file ^ ".html")
	fun mkref line file = idhref file line file 
        val sigspath = Path.concat(HOLpath,"help/src/htmlsigs")
        fun path front file = Path.concat(front, file^".html")

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

        (*------------------------------------------------------*
         * Generate index for Docfiles                          *
         *------------------------------------------------------*)

        val _ = let val docfileIndex = Path.concat(HOLpath, 
                            "help/Docfiles/HTML/docfileIndex.html")
                  val ostrm = TextIO.openOut docfileIndex
                  fun out s = TextIO.output(ostrm, s)
                  fun href anchor target = 
                      app out ["<A HREF=\"", target, "\">", anchor, "</A>"]
                  fun subheader txt = app out ["\n<H2>", txt, "</H2>\n"]
                  val lastc1 = ref #" "
                  fun separator k1 = 
                   let val c1 = Char.toUpper k1
                   in if Char.isAlpha c1 andalso c1 <> !lastc1 then 
		         (lastc1 := c1;
                          app out ["\n</UL>\n\n<A NAME=\"", str c1, "\">"];
                          subheader (str c1);
                          out "</A>\n<UL>")
                      else ()
                   end
                 fun mkalphaindex () =
	           let fun letterlink c = 
                        if c > #"Z" then ()
                         else (href (str c) ("#" ^ str c); 
                               out "&nbsp;&nbsp;"; 
                               letterlink (Char.succ c))
                   in 
                      out "<HR>\n<CENTER><B>"; letterlink #"A"; 
                      out "</B></CENTER><HR>\n" 
                   end

                  fun dest_id s = 
                   case String.tokens (equal #".") s
                    of [strName,vName] => vName
                     | other => s

                  fun docfile_of {comp=Term(id,SOME "HOL"),file,line} =
                       (case find_most_appealing HOLpath file
                         of SOME path => SOME (dest_id id, path)
                          | NONE => NONE)
                    | docfile_of otherwise = NONE

                  fun prentries [] = ()
	            | prentries ((anchor,path)::rst) = 
                        (separator (String.sub(anchor, 0));
                         out "<LI>"; href anchor path; out "\n";
                         prentries rst)
                  fun prtree Empty = ()
	            | prtree (Node(key, entries, t1, t2)) = 
	               (prtree t1;
	                prentries (List.mapPartial docfile_of entries);
	                prtree t2)
                in
                  out "<HTML><HEAD><TITLE>\
                      \Documented Functions and Values</TITLE></HEAD>\n";
	          out "<BODY BGCOLOR=\""; out bgcolor; out "\">\n";
	          out "<H1>Documented Functions and Values</H1>\n";
                  mkalphaindex();
                  subheader "Symbolic identifiers";
                  out "<UL>"; prtree db; out "</UL>";
                  mkalphaindex();
                  out "<BR><EM>"; out version; out "</EM>";
	          out "</BODY></HTML>\n";
	          TextIO.closeOut ostrm
                end
    in 
	out "<HTML>\
	 \<HEAD><TITLE>HOL Reference Page</TITLE></HEAD>\n";
	out "<BODY BGCOLOR=\""; out bgcolor; out "\">\n";
	out "<H1>HOL Reference Page</H1>\n";

	out "<DL>";

        out"<DT><STRONG>LIBRARIES</STRONG>";
        out"<DD>"; prtree library_of db;
        out "<P>";

        out"<DT><STRONG>THEORIES</STRONG>";
        out"<DD>"; prtree theory_of db;
        out "<P>";

        out "<DT><STRONG>STRUCTURES</STRONG>";
        out "<DD>"; prtree misc_struct_of db;
        out "<P>";

        out"<DT><STRONG>";
        href "DOCUMENTED FUNCTIONS AND VALUES" 
            (Path.concat(HOLpath,"help/Docfiles/HTML/docfileIndex.html"));
        out "</STRONG>";
        out "<P>";

        out"<DT><STRONG>SYNTAX</STRONG>";
        out"<DD>"; prtree syntax_of db;
        out "<P>";

        out"<DT><STRONG>SIMPLIFICATION SETS</STRONG>";
        out"<DD>"; prtree simps_of db;
        out "<P>";

        out"<DT><STRONG>";
        href "INDEX" 
            (Path.concat(HOLpath,"help/src/htmlsigs/idIndex.html"));
        out "</STRONG>";
        out "<P>";
	out "</DL>\n";

	out "<BR><EM>"; out version; out "</EM>";
	out "</BODY></HTML>\n";
	TextIO.closeOut os 
    end
