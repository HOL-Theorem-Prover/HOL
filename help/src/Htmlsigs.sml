(* Htmlsigs: some hacks to turn Moscow ML annotated signature files into
   HTML-files.  Peter Sestoft 1997-05-08, 1997-07-31, 2000-01-10, 2000-06-01
*)

fun indexbar out srcpath = out (String.concat
   ["<HR><TABLE WIDTH=100%>",
    "<TR ALIGN = CENTER>\n",
    "<TH><A HREF=\"file://", srcpath, "\">Source File</A>\n",
    "<TH><A HREF=\"idIndex.html\">Identifier index</A>\n",
    "<TH><A HREF=\"TheoryIndex.html\">Theory binding index</A>\n",
    "</TABLE><HR>\n"]);

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

fun isTheorysig path =
  let open Path
      val {dir,file} = splitDirFile path
      val {base,ext} = splitBaseExt file
  in ext=SOME "sig" andalso Option.isSome (destProperSuffix "Theory" base)
  end
  handle _ => false;

fun assoc item =
  let fun assc ((key,ob)::rst) = if item=key then ob else assc rst
        | assc [] = raise Fail ("assoc: "^item^" not found")
  in assc
  end

fun find_most_appealing HOLpath docfile =
  let open Path FileSys
      val {dir,file} = splitDirFile docfile
      val {base,ext} = splitBaseExt file
      val docfile_dir = concat(HOLpath,dir)
      val htmldir  = concat(docfile_dir,"HTML")
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

fun processSig db version bgcolor HOLpath SRCFILES sigfile htmlfile =
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
(*	  | encode #"&" = "&amp;" *)
	  | encode c    = str c

	fun outSubstr s = TextIO.output(os, Substring.translate encode s)

	val seenDefinition = ref false

	fun name anchor target =
	    (out "<A NAME=\""; out target; out "\">"; out anchor; out "</A>")

	fun idhref link id =
	    (out "<A HREF=\"#"; out link; out "\">"; out id; out"</A>")
	fun idhref_full link id =
	    (out "<A HREF=\"file://"; out link; out "\">"; out id; out"</A>")

        fun locate_docfile id =
           let open FileSys Path Database
               val qualid = strName^"."^id
               fun trav [] = NONE
                 | trav({comp=Database.Term(x,SOME "HOL"),file,line}::rst)
                   = if x=qualid
                        then find_most_appealing HOLpath file
                        else trav rst
                 | trav (_::rst) = trav rst
           in
             trav (lookup(db,id))
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

        val srcfile = assoc (Path.base(Path.file sigfile)) SRCFILES
    in
	(*print "Creating "; print htmlfile; print " from ";
	print sigfile; print "\n"
       ; *)
        traverse pass1;
        out "<HTML><HEAD><TITLE>Structure ";
        out strName; out "</TITLE></HEAD>\n";
        out "<BODY BGCOLOR=\""; out bgcolor; out "\">\n";
        out "<H1>Structure "; out strName; out "</H1>\n";
        indexbar out srcfile;
        out "<PRE>\n";
        traverse (pass2 (isTheorysig sigfile));
        out "</PRE>";
        indexbar out srcfile;
        out "<BR><EM>"; out version; out "</EM>";
        out "</BODY></HTML>\n";
        TextIO.closeOut os
    end

fun processSigfile db version bgcolor stoplist
                   sigdir htmldir HOLpath SRCFILES sigfile =
 let val {base, ext} = Path.splitBaseExt sigfile
     val htmlfile = Path.joinBaseExt{base=base, ext=SOME "html"}
 in
   case ext
    of SOME "sig" =>
	if List.exists (fn name => base = name) stoplist then ()
	else processSig db version bgcolor HOLpath SRCFILES
	                (Path.concat(sigdir, sigfile))
	                (Path.concat(htmldir, htmlfile))
     | otherwise => ()
 end

fun sigsToHtml version bgcolor stoplist
               helpfile HOLpath SRCFILES (sigdir, htmldir) =
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
     app (processSigfile db version bgcolor
                         stoplist sigdir htmldir HOLpath SRCFILES)
	 (Mosml.listDir sigdir)
    end
    handle exn as OS.SysErr (str, _) => (print(str ^ "\n\n"); raise exn)

fun printHTMLBase version bgcolor HOLpath pred header (sigfile, outfile) =
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
	val firstsymb = ref true
	fun separator k1 =
	    let val c1 = Char.toUpper k1
	    in
		if Char.isAlpha c1 andalso c1 <> !lastc1 then
		    (lastc1 := c1;
		     app out ["\n</UL>\n\n<A NAME=\"", str c1, "\">"];
		     subheader (str c1);
		     out "</A>\n<UL>")
		else if !firstsymb andalso not (Char.isAlpha c1)
                      then (subheader "Symbolic Identifiers";
                            out "<UL>";
                            firstsymb := false)
                      else ()
	    end
	fun mkref line file = idhref file line file
	fun mkHOLref docfile =
            case find_most_appealing HOLpath docfile
             of SOME file => href "Docfile" file
              | NONE => out "not linked"
	fun nextfile last [] = out ")\n"
	  | nextfile last ((e1 as {comp, file, line}) :: erest) =
	    if comp=last then (out ", "; mkref line file; nextfile last erest)
	                 else (out ")\n"; newitem e1 erest)
	and newitem (e1 as {comp, file, line}) erest =
	    let val key = Database.getname e1
	    in separator (String.sub(key, 0))
             ; out "<LI><B>"; out key; out "</B> ("
             ; (case comp
                 of Str    => strhref key "structure"
                  | Val id => (out "value; "; mkref line file)
                  | Typ id => (out "type; ";  mkref line file)
                  | Exc id => (out "exception; "; mkref line file)
                  | Con id => (out "constructor; "; mkref line file)
                  | Term (id, NONE) => mkref line file
(*                | Term (id, SOME "HOL") => (out "HOL; "; mkHOLref file) *)
                  | Term (id, SOME kind) => (out kind;out"; ";mkref line file)
             ; nextfile comp erest)
	    end
	fun prentries []            = ()
	  | prentries (e1 :: erest) = newitem e1 erest
	fun prtree Empty = ()
	  | prtree (Node(key, entries, t1, t2)) =
	    (prtree t1;
	     prentries (List.filter pred entries);
	     prtree t2)
    in
	out "<HTML><HEAD><TITLE>"; out header; out "</TITLE></HEAD>\n";
	out "<BODY BGCOLOR=\""; out bgcolor; out "\">\n";
	out "<H1>"; out header; out "</H1>\n";
	mkalphaindex();
	prtree db;
	out "</UL>\n";
	mkalphaindex();
	out "<BR><EM>"; out version; out "</EM>";
	out "</BODY></HTML>\n";
	TextIO.closeOut os
    end
