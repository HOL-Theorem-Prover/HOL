(* Outputting the help signature database in ASCII, LaTeX and HTML format *)

fun printASCIIBase(sigfile, outfile) =
    let fun prtseq (pr, sep) []      = ""
	  | prtseq (pr, sep) [x]     = pr x
	  | prtseq (pr, sep) (x::xs) = pr x ^ sep ^ prtseq(pr, sep) xs
	
	open Database
	val db = readbase sigfile
	val os = TextIO.openOut outfile
	fun out s = TextIO.output(os, s)
	fun prentry {comp, file, line} =
	    let fun mkitem0 id = 
		    concat[id, " (", file, " ", Int.toString line, ")"]
		fun mkitem1 kind id = 
		concat[kind, " ", id, " (", file, " ", Int.toString line, ")"]
	    in
		case comp of
		    Str    => "structure " ^ file
		  | Exc id => mkitem1 "exception" id
		  | Typ id => mkitem1 "type" id
		  | Val id => mkitem1 "value" id
		  | Con id => mkitem1 "constructor" id
		  | Term (id, NONE)      => mkitem0 id
		  | Term (id, SOME kind) => mkitem1 kind id
	    end
	fun prtree Empty = ()
	  | prtree (Node(key, entries, t1, t2)) = 
	    (prtree t1;
	     out (prtseq (prentry, ", ") entries);
	     out "\n";
	     prtree t2)
    in prtree db; TextIO.closeOut os end

fun printLatexBase(sigfile, outfile) =
    let open Database
	val db = readbase sigfile
	val os = TextIO.openOut outfile
	fun out s = TextIO.output(os, s)
	fun tt s = "\\verb\"" ^ s ^ "\""

	(* Insert extra vertical space when meeting a new initial letter *)
	val lastc1 = ref #" "
	fun separator k1 = 
	    let val c1 = Char.toLower k1
	    in 
		if Char.isAlpha c1 andalso c1 <> !lastc1 then 
		    (lastc1 := c1;
		     out "\\\\[2ex]\n\n")
	       else ()
	    end
	fun nextstr last []                                  = out ")\n"
	  | nextstr last ((e1 as {comp, file, ...}) :: erest) =
	    if comp = last then
		(out ", "; out (tt file); nextstr last erest)
	    else 
		(out ")\n"; newitem e1 erest)
	and newitem (e1 as {comp, file, ...}) erest =
	    let val key = Database.getname e1
	    in 
		(separator (String.sub(key, 0));
		 out "\\item[] "; out (tt key); out " (";
		 out (case comp of
			  Str => "structure"
			| Val id => "value; " ^ tt file
			| Typ id => "type; " ^ tt file
			| Exc id => "exception; " ^ tt file
			| Con id => "constructor; " ^ tt file
			| Term (id, NONE) => ""
			| Term (id, SOME kind) => kind ^ "; ");
		 nextstr comp erest)
	    end
	fun prentries []            = ()
	  | prentries (e1 :: erest) = newitem e1 erest
	fun prtree Empty = ()
	  | prtree (Node(key, entries, t1, t2)) = 
	    (prtree t1;
	     prentries entries;
	     prtree t2)
    in 
	out "\\begin{description}\\small\n";
	prtree db; 
	out "\\end{description}\n";
	TextIO.closeOut os 
    end
