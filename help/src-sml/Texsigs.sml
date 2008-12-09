(* Texsigs: turn Moscow ML annotated signature files into Latex source code.  
   Peter Sestoft 1997, 2000-04-22
*)

val smlIdCharSym = Char.contains "'_!%&$#+-/:<=>?@\\~`^|*"
fun smlIdChar c = Char.isAlphaNum c orelse smlIdCharSym c

fun processSig db out sigfile =
    let open Database
	val strName = Path.base (Path.file sigfile)
	val is    = TextIO.openIn sigfile
	val lines = Substring.fields (fn c => c = #"\n") 
	                             (Substring.all (TextIO.inputAll is))
	val _ = TextIO.closeIn is

	fun encode #"{"  = "\\verb\"{\""
	  | encode #"}"  = "\\verb\"}\""
	  | encode #"\\" = "\\verb\"\\\""
	  | encode #"%"  = "\\verb\"%\""
	  | encode #"$"  = "\\$"
	  | encode #"&"  = "\\&"
	  | encode #"-"  = "\\verb\"-\""
	  | encode #"<"  = "\\verb\"<\""
	  | encode #">"  = "\\verb\">\""
	  | encode c     = str c

	(* Replace SML comment brackets; assume only one comment per line *)
	(* Assume that if a opening or closing bracket appears unbalanced
	   in a line, then there's nothing else on that line.
	   TODO: check this *)

	fun outSubstr sus1 = 
	    let open Substring
		val comment1 = "{\\itshape{}"
		val comment2 = "}"
		val sepline = "\\separatingline"
		val (sus11, afterclose)   = position "*)" sus1
		val (beforeopen, incomment) = position "(*" sus11
		fun outsus sus = out (translate encode sus)
	    in 
		outsus beforeopen;
		if isEmpty incomment then	(* No opening comment *)
		    if isEmpty afterclose then	(* No closing comment *)
			()
		    else 
			()
		else
		    if isEmpty afterclose then  (* No closing comment *)
			out sepline
		    else 
			(out comment1; outsus (triml 3 incomment); 
			 out comment2; outsus (triml 2 afterclose))
	    end
    
	fun index' id comp extra = 
	    let fun encode #"!" = "\"!"
		  | encode #"@" = "\"@"
		  | encode c    = str c
		fun tt id = (out "\\verb,"; 
			     out (String.translate encode id); 
			     out ",")
		val encid = String.translate encode id
	    in
		out "\\index{"; out encid; out "@"; tt id;
		(case comp of
		     Str   => out " (structure"
		   | Val _ => (out "!value ("; tt strName)
		   | Typ _ => (out "!type ("; tt strName)
		   | Exc _ => (out "!exception ("; tt strName)
		   | Con _ => (out "!constructor ("; tt strName)
		   | Term (_, NONE) => (out "("; tt strName)
		   | Term (_, SOME kind) => (out kind; out " ("; tt strName)
		 )
		 ; out ")"; out extra; out "}"
	    end

	fun index id comp = index' id comp ""

	fun beginsection title =
	    let val header = "\\MakeUppercase{" ^ title ^ "}"
	    in
		out "\\newpage\n\n\\section*{Module "; out title; out "}\n";
		index' title Str "|("; out "\n";
		out "\\markboth{"; out header; out "}{"; out header; out "}\n";
		out "\\addcontentsline{toc}{section}{"; out title; out "}\n"
	    end

	fun endsection title = index' title Str "|)"

	fun chkdecl id mkcomp =
	    let open Database
		val entries = lookup (db, id)
		fun found {comp, file, ...} =
		    comp = mkcomp id andalso file = strName
	    in List.exists found entries end

	(* Skip 'tyvar and ('tyvar, ..., 'tyvar), return the id that
	   follows *)

	fun scanident getc src =
	    let open StringCvt
		fun isn't c1 c2 = c1 <> c2
		fun is    c1 c2 = c1 = c2
		val sus1 = skipWS getc src
		fun readident sus =
		    takel smlIdChar getc (skipWS getc sus)
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

	fun definition susline =
	    let open Database Substring 
		val id = scanident (triml 4 susline)
		fun relevant {file, ...} = file=strName
		val comps = 
		    List.map #comp (List.filter relevant (lookup (db, id)))
		fun indexif s comp = 
		    if isEmpty (#2 (position s susline)) then ()
		    else index id comp
		fun indexcomp comp =
		    case comp of 
			Exc _  => indexif "exception" comp
		      | Typ _  => indexif "type" comp
		      | Con _  => index id comp
		      | Val _  => 
			    if isEmpty (#2 (position "type" susline)) then 
				index id comp
			    else ()
		      | Str    => indexif "structure" comp
		      | Term _ => index id comp
	    in
		out "\n";
		outSubstr susline;
		List.app indexcomp comps
	    end

	fun declaration space1 decl mkcomp =
	    let open Substring
		fun isKind c = Char.isAlpha c orelse c = #"_"
		val (kind, rest) = splitl isKind decl
		val id           = scanident rest
	    in 
		out "\n";
		outSubstr space1;
		outSubstr kind;
		outSubstr rest;
		if chkdecl id mkcomp then 
		    index id (mkcomp id)
		else
		    ()
	    end
	    
	fun pass2 susline = 
	    let open Substring
	    in 
		if isPrefix "   [" susline then 		    
		    definition susline
		else 
		    let val (space, suff) = splitl Char.isSpace susline
		    in
			if isPrefix "val " suff then 
			    declaration space suff Val 
			else if isPrefix "type " suff then
			    declaration space suff Typ 
			else if isPrefix "eqtype " suff then 
			    declaration space suff Typ 
			else if isPrefix "prim_EQtype " suff then 
			    declaration space suff Typ 
  		        else if isPrefix "datatype " suff then 
		            declaration space suff Typ 
			else if isPrefix "structure " suff then
			    declaration space suff (fn _ => Str)
			else if isPrefix "exception " suff then 
			    declaration space suff Exc 
			else if isPrefix "*)" suff then 
			    ()
			else
			    (out "\n"; outSubstr susline)
		    end
	    end
    in
	print "Generating LaTeX code for "; print sigfile; print "\n"; 
	beginsection strName;
	out "\\begin{longprogram}";
	app pass2 lines;
	out "\\end{longprogram}\n";
	endsection strName 
    end

fun processSigfile db out stoplist sigdir sigfile =
    let val {base, ext} = Path.splitBaseExt sigfile
    in 
	case ext of
	    SOME "sig" => 
		if List.exists (fn name => base = name) stoplist then ()
		else processSig db out (Path.concat(sigdir, sigfile))
	  | _          => ()
    end

fun sigsToLatex stoplist sigdir sigfile texfile =
    let open Database
	val db    = readbase sigfile
	val os    = TextIO.openOut texfile
	fun out s = TextIO.output(os, s)
    in 
	app (processSigfile db out stoplist sigdir) 
	    (Listsort.sort String.compare (Mosml.listDir sigdir));
	TextIO.closeOut os
    end
    handle exn as OS.SysErr (str, _) => (print(str ^ "\n\n"); raise exn)

