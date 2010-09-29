(* makebase -- create the signature database from the Moscow ML
 * library signatures.  PS 1995-11-19, 2000-06-29
 *
 * Hacked for HOL help system, Konrad Slind, Nov. 2001.
 *)

structure makebase = struct

fun curry f x y = f (x,y);
fun single x = [x];

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

fun isTheory {comp,file=path,line} =
  let open OS.Path
      val {dir,file} = splitDirFile path
      val {base,ext} = splitBaseExt file
  in Option.isSome (destProperSuffix "Theory" base)
  end
  handle _ => false;

fun isSigId {comp=Database.Term(_,SOME"HOL"),file,line} = false
  | isSigId entry = not (isTheory entry)


(*---------------------------------------------------------------------------
    Set values
 ---------------------------------------------------------------------------*)
(* The version number inserted in generated files: *)
val version =
    String.concat ["<a href=\"http://hol.sourceforge.net\">HOL&nbsp;4,&nbsp;",
                   Systeml.release, "-", Int.toString Systeml.version,
                  "</a>"]

(* HOL distribution directory: *)
val HOLpath = normPath [Systeml.HOLDIR];

(* Default directory containing the signature files: *)
val libdirDef = normPath[HOLpath,"sigobj"]

(* Default filename for the resulting help database: *)
val helpfileDef = normPath[HOLpath, "help","HOL.Help"]

(* Default filename for the HOL reference page: *)
val HOLpageDef = normPath[HOLpath, "help","HOLindex.html"]

(* Default filename for the ASCII format database: *)
val txtIndexDef = "index.txt"

(* Default filename for the LaTeX format database: *)
val texIndexDef = "index.tex"

(* Default directory for signatures in HTML format: *)
val htmlDirDef = "htmlsigs"

(* Default filename for the HTML format database for identifiers: *)
val htmlIndexDef = normPath[HOLpath,"help","src-sml",htmlDirDef,"idIndex.html"]

(* Default filename for the HTML format database for theories: *)
val htmlTheoryIndexDef =
   normPath[HOLpath,"help","src-sml",htmlDirDef,"TheoryIndex.html"]

(* Default filename for the LaTeX signatures: *)
val texSigs = "texsigsigs.tex"

(* Signatures not to be included in the help database: *)
val stoplist = [];

(* The background colour in generated HTML files (HTML colour code): *)
val bgcolor = "#fbf2e7";

(* To make the database, sort entries on normalized (lower case) name,
 * lump together equal normalized names in entry lists, and sort these by
 * structure name (except that a Str entry always precedes the others):
 *)

fun mkbase (entries : Database.entry list) =
    let open Database
	fun compname (e1, e2) = keycompare (getname e1, getname e2)
	val entries = Listsort.sort compname entries
	infix THEN
	fun (comp1 THEN comp2) arg =
	    case comp1 arg of
		EQUAL => comp2 arg
	      | res   => res
	fun kindof Str     = "structure"
	  | kindof (Val _) = "val"
	  | kindof (Typ _) = "type"
	  | kindof (Exc _) = "exn"
	  | kindof (Con _) = "con"
	  | kindof (Term (_, NONE)) = ""
	  | kindof (Term (_, SOME kind)) = kind
	fun kindCompare (e1 as {comp=c1, ...}, e2 as {comp=c2, ...}) =
	    String.compare(kindof c1, kindof c2)
	fun nameCompare (e1, e2) =
	    String.compare(getname e1, getname e2)
	fun fileCompare (e1, e2) = String.compare(#file e1, #file e2)
	val entryCompare = kindCompare THEN nameCompare THEN fileCompare
	(* Share strings if result=argument: *)
	fun toLower s =
	    let val s' = String.map Char.toLower s
	    in if s=s' then s else s' end
	(* Lump together names that differ only in capitalization;
           then sort each lump using entryCompare                   *)
	fun lump [] = []
	  | lump (x1 :: xr) =
	    let fun mkLump lumpname lump = (toLower (getname lumpname),
					    Listsort.sort entryCompare lump)
		fun h lump1name lump1 []       = [mkLump lump1name lump1]
		  | h lump1name lump1 (x1::xr) =
		    if compname(x1, lump1name) = EQUAL then
			h lump1name (x1 :: lump1) xr
		    else
			mkLump lump1name lump1 :: h x1 [x1] xr
	    in h x1 [x1] xr end
	val lumps = lump entries : (string * entry list) list
	fun mkOrderedTree xs =
	    let fun h 0 xs = (Empty, xs)
		  | h n xs =
		    let val m = n div 2
			val (t1, l) = h m xs
                        val (key, value) = hd l
                        val yr = tl l
			val (t2, zs)                 = h (n-m-1) yr
		    in (Node(key, value, t1, t2), zs) end
	    in #1 (h (length xs) xs) end
    in
	mkOrderedTree lumps
    end

(*---------------------------------------------------------------------------*)
(* Additional stuff specific to HOL.                                         *)
(*---------------------------------------------------------------------------*)

fun mk_HOLdocfile_entry (dir,s) =
 let val content =String.substring(s,0,size s - 5)
 in
    {comp=Database.Term(Symbolic.tosymb content, SOME"HOL"),
     file=normPath[dir,s], line=0}
 end

local fun is_adocfile s =
         String.size s>5 andalso
         String.extract(s, String.size s - 5, NONE) = ".adoc"
      fun is_docfile s =
         String.size s>4 andalso
         String.extract(s, String.size s - 4, NONE) = ".doc"
in
fun docdir_to_entries path (endpath, entries) =
  let val L1 = List.filter is_adocfile
                  (Htmlsigs.listDir (normPath [path, endpath]))
  in List.foldl (fn (s,l) => mk_HOLdocfile_entry (endpath,s)::l) entries L1
  end
end;

fun dirToBase (sigdir, docdirs, filename) =
    let val doc_entryl = List.foldl (docdir_to_entries HOLpath) [] docdirs
        val res = List.foldl (Parsspec.processfile stoplist sigdir)
	                     doc_entryl Keepers.keepers
	val _ = print ("\nProcessed " ^ Int.toString (length res)
		       ^ " entries in total.\n");
	val _ = print ("Building database...\n");
	val db = mkbase res
	val _ = print ("Writing database to file " ^ filename ^ "\n");
    in
	Database.writebase(filename, db)
    end
    handle exn as OS.SysErr (str, _) => (print(str ^ "\n\n"); raise exn)

fun main () = let

val docdirs =
 let val instr = TextIO.openIn
                   (OS.Path.concat(HOLpath,"tools/documentation-directories"))
        handle _ => (print "Couldn't open documentation directories file";
                    raise Fail "File not found")
     val wholefile = TextIO.inputAll instr
     val _ = TextIO.closeIn instr
 in
   map (normPath o single) (String.tokens Char.isSpace wholefile)
 end

val SRCFILES =
 let open TextIO
     val istrm = openIn (OS.Path.concat(HOLpath,"sigobj/SRCFILES"))
        handle _ => (print "Couldn't open HOLDIR/sigobj/SRCFILES";
                     raise Fail "File not found")
     fun readlines acc =
         case inputLine istrm of
           NONE => List.rev acc
         | SOME s => readlines (String.substring(s, 0, size s - 1) :: acc)
                (* drop final newline *)
     val wholefile = readlines [] before closeIn istrm
     fun munge path =
       let val {dir,file} = OS.Path.splitDirFile path
       in case destProperSuffix "Theory" file
           of SOME thy => (file, OS.Path.concat(dir,thy^"Script.sml"))
            | NONE     => (file,path^".sml")
       end
 in
   map (munge o normPath o single) wholefile
 end

fun process (libdir, helpfile, txtIndex,
             texIndex, htmldir, htmlIndex, htmlTheoryIndex, HOLpage)
 =
 (print ("Reading signatures in directory " ^ libdir ^
        "\nand writing help database in file " ^ helpfile ^ "\n")
 ; dirToBase (libdir, docdirs, helpfile)

 ; print ("\nWriting ASCII signature index in file " ^ txtIndex ^ "\n")
 ; Printbase.printASCIIBase(helpfile, txtIndex)

 ; print ("\nWriting Latex signature index in file " ^ texIndex ^ "\n")
 ; Printbase.printLatexBase(helpfile, texIndex)

 ; print ("\nCreating HTML versions of signature files\n")
 ; Htmlsigs.sigsToHtml
     version bgcolor stoplist helpfile HOLpath SRCFILES (libdir, htmldir)

 ; print ("\nWriting HTML signature index in file " ^ htmlIndex ^ "\n")
 ; Htmlsigs.printHTMLBase version bgcolor HOLpath
         isSigId "HOL IDENTIFIER INDEX" (helpfile, htmlIndex)

 ; print ("\nWriting HTML theory signature index in file "
          ^ htmlTheoryIndex ^ "\n")
 ; Htmlsigs.printHTMLBase version bgcolor HOLpath
         isTheory "HOL THEORY BINDINGS" (helpfile, htmlTheoryIndex)

 ; print ("\nWriting HOLPage\n")
 ; HOLPage.printHOLPage version bgcolor HOLpath
                        htmlIndex htmlTheoryIndex (helpfile, HOLpage)
 )

in
    case CommandLine.arguments () of
	[]       =>
	    process (libdirDef, helpfileDef,
		     txtIndexDef, texIndexDef,
                     htmlDirDef, htmlIndexDef,
                     htmlTheoryIndexDef, HOLpageDef)
      | [libdir] =>
	    process (libdir, helpfileDef,
		     txtIndexDef, texIndexDef,
                     htmlDirDef, htmlIndexDef,
                     htmlTheoryIndexDef, HOLpageDef)
      | _ => print "Usage: makebase\n"
end  (* main *)

end;
