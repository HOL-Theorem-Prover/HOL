(* Htmlsigs: some hacks to turn Moscow ML annotated signature files into 
   HTML-files.  Peter Sestoft 1997-05-08, 1997-07-31, 2000-01-10, 2000-06-01 
*)

fun indexbar out =
    out "<HR><TABLE WIDTH=100%>\
     \<TR ALIGN = CENTER>\n\
     \<TH><A HREF=\"idIndex.html\">Identifier index</A>\n\
     \<TH><A HREF=\"index.html\">Structure index</A>\n\
     \</TABLE><HR>\n";

val smlIdCharSym = Char.contains "'_!%&$#+-/:<=>?@\\~`^|*"
fun smlIdChar c = Char.isAlphaNum c orelse smlIdCharSym c

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

val destTheorysig = destProperSuffix "Theory.sig";

(*---------------------------------------------------------------------------
   This won't work on a file system without symbolic links. So we will
   have to think of a better way, in order to get this to work on 
   Windows.
 ---------------------------------------------------------------------------*)

fun srcfile sigfile = 
  if FileSys.isLink sigfile
  then let val linkpath = FileSys.readLink sigfile
       in case destTheorysig linkpath
           of SOME path => SOME (path^"Script.sml")
            | NONE => let val {dir,file} = Path.splitDirFile linkpath
                          val {base,ext} = Path.splitBaseExt file
                      in SOME (Path.concat(dir, 
                               Path.joinBaseExt{base=base,ext=SOME"sml"}))
                      end
       end
  else NONE;


fun processSig db version bgcolor sigfile htmlfile =
    let val strName = Path.base (Path.file sigfile)
	val is = TextIO.openIn sigfile
	val lines = Substring.fields (fn c => c = #"\n") 
	                             (Substring.all (TextIO.inputAll is))
	val _ = TextIO.closeIn is

	fun comp2str comp =
	    let open Database
	    in
		case comp of
		    Exc _  => "exc" 
		  | Typ _  => "typ" 
		  | Con _  => "con"
		  | Val _  => "val"
		  | Str    => "str" 
		  | Term _ => "ter"
	    end

	(* Skip 'tyvar and ('tyvar, ..., 'tyvar), return the id that
	   follows *)

	fun scanident getc src =
	    let open StringCvt
		fun isn't c1 c2 = c1 <> c2
		fun is    c1 c2 = c1 = c2
		val sus1 = skipWS getc src
		fun readident sus =
		    splitl smlIdChar getc (skipWS getc sus)
	    in
		case getc sus1 of
		    SOME(#"'", sus2) => 
			let val sus3 = dropl (not o Char.isSpace) getc sus2
			in readident sus3 end
		  | SOME(#"(", sus2) => 
			let val sus3 = dropl (isn't #")") getc sus2
			    val sus4 = dropl (is #")") getc sus3
			in readident sus4 end
		  | SOME _ => readident sus1
		  | NONE   => readident sus1
	    end

	val scanident = scanident Substring.getc 

	fun definition susline isntdef isdef =
	    let open Database Substring 
		val (id, after) = scanident (triml 4 susline)
		fun relevant {file, ...} = file=strName
		val comps = 
		    List.map #comp (List.filter relevant (lookup (db, id)))
		fun linehas s = not (isEmpty (#2 (position s after)))
		fun indexcomp comp =
		    case comp of 
			Exc i  => if i=id then SOME comp else NONE
		      | Typ i  => if i=id andalso linehas "type" then SOME comp
				  else NONE
		      | Con i  => if i=id then SOME comp else NONE
		      | Val i  => if i=id then SOME comp else NONE
		      | Str    => if linehas "structure" then SOME comp 
				  else NONE
		      | Term _ => SOME comp
		fun kindof Str      = 3
		  | kindof (Val _)  = 4
		  | kindof (Typ _)  = 1
		  | kindof (Exc _)  = 2
		  | kindof (Con _)  = 5
		  | kindof (Term _) = 6
		fun kindCompare (c1, c2) = Int.compare(kindof c1, kindof c2)
		val comps = Listsort.sort kindCompare
		                          (List.mapPartial indexcomp comps)
	    in
		case comps of
		    []        => isntdef susline		(* No def *)
		  | comp :: _ => isdef susline id after comp    (* Def    *)
	    end

	(* First pass over the file: record anchors of identifier defs *)

	val anchors = Polyhash.mkPolyTable (71, Fail "Htmlsigs.processSig")

	fun pass1 susline lineno = 
	    let open Substring
		fun nameanchor _ id _ comp = 
		    Polyhash.insert anchors (id ^ "-" ^ comp2str comp, ()) 
	    in
		if isPrefix "   [" susline then
		    definition susline ignore nameanchor
		else ()
	    end

	(* Second pass over the file *)

	val os = TextIO.openOut htmlfile
	fun out s = TextIO.output(os, s)
	fun encode #"<" = "&lt;"
	  | encode #">" = "&gt;"
	  | encode #"&" = "&amp;"
	  | encode c    = str c
	fun outSubstr s = TextIO.output(os, Substring.translate encode s)
    
	val seenDefinition = ref false

	fun name anchor target = 
	    (out "<A NAME=\""; out target; out "\">"; out anchor; out "</A>")

	fun idhref link id = 
	    (out "<A HREF=\"#"; out link; out "\">"; out id; out"</A>")
	fun idhref_full link id = 
	    (out "<A HREF=\""; out link; out "\">"; out id; out"</A>")

(*
        fun locate_docfile id =
           let open FileSys Path Database
           in case lookup(db,id) 
               of {comp=Database.Term(content,SOME "HOL"),file,line} :: _ => 
                   let val {dir,file=docfile} = splitDirFile file
                       val {base, ...} = splitBaseExt docfile
                       val htmldir = Path.concat(dir,"html")
                       val html = joinBaseExt{base=base,ext=SOME"html"}
                       val adoc = joinBaseExt{base=base,ext=SOME"adoc"}
                       val html_docfile = joinDirFile{dir=htmldir,file=html}
                       val adocfile = joinDirFile{dir=dir,file=adoc}
                   in
                     if FileSys.access(html_docfile,[A_READ])
                        then SOME html_docfile else
                     if FileSys.access(adocfile,[A_READ])
                        then SOME adocfile else 
                     if FileSys.access(file,[A_READ])
                        then SOME file 
                        else NONE
                   end
              | otherwise => NONE
           end
*)
        fun locate_docfile id =
           let open FileSys Path Database
           in case lookup(db,id) 
               of {comp=Database.Term(dir,SOME "HOL"),file,line} :: _ => 
                   let val {base, ...} = splitBaseExt file
                       val htmldir = Path.concat(dir,"html")
                       val html = joinBaseExt{base=base,ext=SOME"html"}
                       val adoc = joinBaseExt{base=base,ext=SOME"adoc"}
                       val html_docfile = joinDirFile{dir=htmldir,file=html}
                       val adocfile = joinDirFile{dir=dir,file=adoc}
                   in
print ("Looking for "^html_docfile^"\n");
                     if FileSys.access(html_docfile,[A_READ])
                        then SOME html_docfile else
                     if FileSys.access(adocfile,[A_READ])
                        then SOME adocfile else 
                     if FileSys.access(file,[A_READ])
                        then SOME file 
                        else NONE
                   end
              | otherwise => NONE
           end

          
	fun declaration isThryFile lineno space1 decl kindtag =
	    let open Substring 
		fun isKind c = Char.isAlpha c orelse c = #"_"
		val (kind, rest) = splitl isKind decl
		val (id, after)  = scanident rest
		val preflen = size decl - size after - String.size id
		val preid = slice(decl, 0, SOME preflen)
		val link = id ^ "-" ^ kindtag
	    in 
		outSubstr space1;
		outSubstr preid
               ;
		if id = "" then () 
                 else if Polyhash.peek anchors link = NONE 
                      then if isThryFile then out id (* shouldn't happen *)
                           else case locate_docfile id
                                 of NONE => out id
                                  | SOME file => idhref_full file id
                      else idhref link id
               ;
		outSubstr after
	    end

	(* Format susline which defines identifier id of kind comp: *)

	fun outisdef susline id after comp = 
	    let open Substring 
		fun namebold id s =
		    (out "<A NAME=\""; out id; out "-"; out s; 
		     out "\"><B>"; out id; out "</B></A>")
		val preflen = size susline - size after - String.size id
		val pref = slice(susline, 0, SOME preflen)
	    in 
		outSubstr pref; namebold id (comp2str comp);
		outSubstr after
	    end
	    
	fun pass2 isThryFile susline lineno = 
	    let open Substring
	    in 
		(if isPrefix "   [" susline 
                 then (definition susline outSubstr outisdef; 
		       seenDefinition := true)
		 else if not (!seenDefinition) then
		     (name "" ("line" ^ Int.toString lineno);
		      let val (space, suff) = splitl Char.isSpace susline
			  val dec = declaration isThryFile lineno space suff
		      in
			  if isPrefix "val " suff 
			      orelse isPrefix "prim_val " suff then
			      dec "val"
			  else if isPrefix "prim_type " suff
			      orelse isPrefix "prim_EQtype " suff
			      orelse isPrefix "type " suff
			      orelse isPrefix "eqtype " suff
			      orelse isPrefix "datatype " suff then
			      dec "typ"
			  else if isPrefix "structure " suff then
			      dec "str"
			  else if isPrefix "exception " suff then 
			      dec "exc"
			  else 
			      outSubstr susline
		      end)
		 else
		     outSubstr susline);
		 out "\n"		   
	    end

	fun traverse process = 
	    let fun loop []        lineno = ()
		  | loop (ln::lnr) lineno = 
		    (process ln lineno; loop lnr (lineno+1))
	    in loop lines 1 end
    in
	print "Creating "; print htmlfile; print " from "; 
	print sigfile; print "\n"
       ; 
        traverse pass1;
        out "<HTML><HEAD><TITLE>Structure ";
        out strName; out "</TITLE></HEAD>\n";
        out "<BODY BGCOLOR=\""; out bgcolor; out "\">\n";
        out "<H1>Structure "; out strName; out "</H1>\n";
        indexbar out;
        out "<PRE>\n";
        traverse (pass2 (Option.isSome (destTheorysig sigfile)));
        out "</PRE>"
       ;
        case srcfile sigfile
          of SOME file => out (String.concat
                 ["\n<A HREF=\"", file,"\">Source File</A>\n"])
           | NONE => ();
        indexbar out;
        out "<BR><EM>"; out version; out "</EM>";
        out "</BODY></HTML>\n";
        TextIO.closeOut os
    end

fun processSigfile db version bgcolor stoplist sigdir htmldir sigfile =
    let val {base, ext} = Path.splitBaseExt sigfile
	val htmlfile = Path.joinBaseExt{base=base, ext=SOME "html"}
    in 
	case ext of
	    SOME "sig" => 
		if List.exists (fn name => base = name) stoplist then ()
		else processSig db version bgcolor
		                (Path.concat(sigdir, sigfile))
		                (Path.concat(htmldir, htmlfile))
	  | _          => ()
    end

fun sigsToHtml version bgcolor stoplist helpfile (sigdir, htmldir) =
    let open FileSys Database
	val db = readbase helpfile
	fun mkdir htmldir =
	    if access(htmldir, [A_WRITE, A_EXEC]) andalso isDir htmldir then
		(print "Directory "; print htmldir; print " exists\n")
	    else
		(FileSys.mkDir htmldir; 
		 print "Created directory "; print htmldir; print "\n");
    in 
	mkdir htmldir;
	app (processSigfile db version bgcolor stoplist sigdir htmldir) 
	    (Mosml.listDir sigdir)
    end
    handle exn as OS.SysErr (str, _) => (print(str ^ "\n\n"); raise exn)

fun printHTMLBase version bgcolor (sigfile, outfile) =
    let open Database
	val db = readbase sigfile
	val os = TextIO.openOut outfile
	fun out s = TextIO.output(os, s)
	fun href anchor target = 
	    app out ["<A HREF=\"", target, "\">", anchor, "</A>"]
	fun idhref file line anchor = 
	    href anchor (concat [file, ".html#line", Int.toString line])
	fun strhref file anchor = 
	    href anchor (file ^ ".html")
	fun mkalphaindex () =
	    let fun letterlink c = 
		if c > #"Z" then ()
		else (href (str c) ("#" ^ str c); out "&nbsp;&nbsp;"; 
		      letterlink (Char.succ c))
	    in 
		out "<HR>\n<CENTER><B>"; letterlink #"A"; 
		out "</B></CENTER><HR>\n" 
	    end
	fun subheader txt = app out ["\n<H2>", txt, "</H2>\n"]
	    
	(* Insert a subheader when meeting a new initial letter *)
	val lastc1 = ref #" "
	fun separator k1 = 
	    let val c1 = Char.toUpper k1
	    in 
		if Char.isAlpha c1 andalso c1 <> !lastc1 then 
		    (lastc1 := c1;
		     app out ["\n</UL>\n\n<A NAME=\"", str c1, "\">"];
		     subheader (str c1);
		     out "</A>\n<UL>")
		else ()
	    end
	fun mkref line file = idhref file line file 
	fun mkHOLref docfile = 
            let val frontpath = Path.base docfile
                val {dir,file} = Path.splitDirFile frontpath
                val dir' = Path.concat(dir,"html")
                val file' = Path.concat (dir',file)
            in strhref file' "Docfile"
            end
	fun nextfile last [] = out ")\n"
	  | nextfile last ((e1 as {comp, file, line}) :: erest) =
	    if comp = last then
		(out ", "; mkref line file; nextfile last erest)
	    else 
		(out ")\n"; newitem e1 erest)
	and newitem (e1 as {comp, file, line}) erest =
	    let val key = Database.getname e1
	    in 
		separator (String.sub(key, 0));
		out "<LI><B>"; out key; out "</B> (";
		(case comp of
		     Str    => strhref key "structure"
		   | Val id => (out "value; ";       
				mkref line file)
		   | Typ id => (out "type; ";        
				mkref line file)
		   | Exc id => (out "exception; ";   
				mkref line file)
		   | Con id => (out "constructor; "; 
				mkref line file)
		   | Term (id, NONE) => mkref line file
		   | Term (id, SOME "HOL") => (out "HOL"; out "; ";
					      mkHOLref file)
		   | Term (id, SOME kind) => (out kind; out "; ";
					      mkref line file);
		nextfile comp erest)
	    end
	fun prentries []            = ()
	  | prentries (e1 :: erest) = newitem e1 erest
	fun prtree Empty = ()
	  | prtree (Node(key, entries, t1, t2)) = 
	    (prtree t1;
	     prentries entries;
	     prtree t2)
    in 
	out "<HTML>\
	 \<HEAD><TITLE>HOL identifiers</TITLE></HEAD>\n";
	out "<BODY BGCOLOR=\""; out bgcolor; out "\">\n";
	out "<H1>HOL identifiers</H1>\n";
	indexbar out;
	mkalphaindex();
	subheader "Symbolic identifiers";
	out "<UL>";
	prtree db; 
	out "</UL>\n";
	mkalphaindex();
	out "<BR><EM>"; out version; out "</EM>";
	out "</BODY></HTML>\n";
	TextIO.closeOut os 
    end
