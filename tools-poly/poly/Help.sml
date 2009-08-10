structure Help :> Help = struct

(* Help -- a simple Moscow ML library browser, PS 1995-04-30, 2000-04-22

Invoking `help s' has the following effect:

 (a) s is normalized to lower case
 (b) if s is the empty string, then the help browser is invoked with the
     message !welcome;
 (c) otherwise, if the term s appears in !specialfiles, then the browser
     is invoked with the file associated with s;
 (d) otherwise, if the term appears in one of the index files in
     !indexfiles, then the help system asks the user to choose which
     help file to load, in case there are several, and invokes the
     browser with that file;
 (e) otherwise, a standard error message is shown.

The help system looks for help files in the -stdlib and in the
directories in !helpdirs.

The browser can open a file on a specified line, attempting to center
that lines in the display (assuming the display can hold !displayLines
lines at a time).

The browser accepts several commands for moving forth and back in the
current file.

The browser's search facility cyclically searches (case-insensitive)
for occurrences of a given string and displays the line in which the
string was found, as close to the center of the display (or portion
displayed) as possible.

Several hacks are being used to avoid loading too many other libraries
along with Help.
*)

(* The number of lines to show interactively: *)

val displayLines = ref 24

(* Additional directories to search for help files *)

val helpdirs = ref [] : string list ref




val slash = #"/"


fun joinDirFile dir file =
    let open String
    in
	if dir <> "" andalso sub(dir, size dir - 1) = slash then
	    dir ^ file
	else
	    dir ^ str slash ^ file
    end

(* Find the standard library directory: *)
(*
fun getstdlib () =
    let open Vector
	prim_val argv_ : string vector = 0 "command_line";
	val stop = length argv_ - 1;
	fun h i =
	    if i < stop then
		if sub(argv_, i) = "-stdlib" then sub(argv_, i+1)
		else h (i+1)
	    else
		raise Fail "Cannot find the standard libraries!"
    in h 0 end;
    *)

(* Full path of the signature index database: *)

val indexfiles = ref [(*joinDirFile (getstdlib ()) "helpsigs.val"*)]

(* Mapping particular search terms to non-.sig files: *)

val specialfiles = ref [{term="lib", file="README", title="Overview"}];

(* The help system's response to help "" : *)
val welcome =
    ref (Vector.fromList ["HOL ML library browser: \n",
	  "\n",
	  "   help \"lib\";   gives an overview of the library units\n",
	  "   help \"id\";    provides help on identifier id\n",
	  "\n"])

local
fun print s = TextIO.print s

(* Auxiliaries: *)

fun min (x, y) = if x < y then x else y : int;
fun max (x, y) = if x < y then y else x : int;

fun normalize []           = []
  | normalize (#"\n" :: _) = []
  | normalize (c :: cr)    = Char.toLower c :: normalize cr

fun toLower s = String.implode (normalize (String.explode s))

(* The signature browser: *)

fun show name centerline initiallySought (strs : string Vector.vector) =
    let
	val lines = Vector.length strs
	val sought = ref initiallySought
	fun instr s str =
	    let val len = String.size s
		fun eq j k =
		    j >= len orelse
		    String.sub (s, j) = Char.toLower (String.sub (str, k)) andalso eq (j+1) (k+1)
		val stop = String.size str - len
		fun cmp k = k<=stop andalso (eq 0 k orelse cmp(k+1))
	    in cmp 0 end;
	fun occurshere str =
	    case !sought of
		NONE   => false
	      | SOME s => instr s str
	fun findline s curr =
	    let fun h i =
		if i >= lines then NONE
		else if instr s (Vector.sub(strs, (i+curr) mod lines)) then
		    SOME ((i + curr) mod lines)
		else h(i+1)
	    in h 0 end
	val portion = max(!displayLines, 5) - 1
	fun wait next =
	    let val prompt =
		"---- " ^ name ^ "[" ^
		Int.toString((100 * next) div lines)
		^ "%]: down, up, bottom, top, /(find), next, quit: "
		fun toend () = (print "\n....\n";
				nextpart (lines - portion) portion)
		fun tobeg () = (print "\n....\n"; nextpart 0 portion)
		fun up   ()  = (print "\n....\n";
				nextpart (next-3*portion div 2) portion)
		fun down ()  = if next=lines then toend()
			       else nextpart next (portion div 2)
		fun find s =
		    case findline s next of
			NONE      =>
			    (print ("**** String \"" ^ s ^ "\" not found\n");
			     wait next)
		      | SOME line =>
			    (print "\n....\n";
			     nextpart (line - portion div 2) portion)
		fun search chars =
		    let val s = String.implode (normalize chars)
		    in sought := SOME s; find s end
		fun findnext () =
		    (case !sought of
			 NONE   => (print "**** No previous search string\n";
				    wait next)
		       | SOME s => find s)
	    in
		print prompt;
		case Option.map String.explode (TextIO.inputLine TextIO.stdIn) of
                    NONE => ()
		  | SOME (#"q" :: _) => ()
		  | SOME (#"u" :: _) => up ()
		  | SOME (#"d" :: _) => down ()
		  | SOME (#"t" :: _) => tobeg ()
		  | SOME (#"g" :: _) => tobeg ()
		  | SOME (#"b" :: _) => toend ()
		  | SOME (#"G" :: _) => toend ()
                  | SOME (#"/" :: s) => search s
                  | SOME (#"n" :: s) => findnext ()
		  | _         => if next=lines then toend ()
				 else nextpart next portion
	    end
	and nextpart first amount =
	    let val start = max(0, min(lines - amount + 1, first))
		val stop  = min(start + amount, lines)
	    in prt wait start stop end
	and prt wait i stop =
	    if i >= stop then wait i
	    else
		let val line = Vector.sub(strs, i)
		in
		    if occurshere line then print "@>" else print "+ ";
		    print line;
		    prt wait (i+1) stop
		end
    in
	print "\n";
	if lines <= portion then prt ignore 0 lines
	else nextpart (centerline - portion div 2) portion
    end

(* Read a signature file from the standard library: *)

fun readfile file =
    let fun openFile [] =
	    raise Fail ("Help.readFile: help file `" ^ file ^ "' not found")
	  | openFile (dir1 :: dirr) =
		(TextIO.openIn (joinDirFile dir1 file))
		handle IO.Io _ => openFile dirr
	val is = openFile ((*getstdlib () :: *)!helpdirs)
	fun h () = case TextIO.inputLine is of
                       NONE => []
                     | SOME s => s :: h ()
    in Vector.fromList (h ()) end;

(* Invoke the browser on a particular line of a signature: *)
local
open Database
in
fun showFile sought entry =
    (case entry of
	 {comp = Str, file, ...} =>
	     show file 0 NONE (readfile (file ^ ".sig"))
       | {comp = Term _, file, line} =>
	     show file line NONE (readfile file)
       | {comp, file, line} =>
	     show file line (SOME sought) (readfile (file ^ ".sig")))
    handle OS.SysErr _ => raise Fail "Help.showFile: inconsistent help database"
end

(* Let the user select from the menu: *)

fun choose sought entries =
    let val _ = print "\nChoose number to browse, or quit: "
	val response =
          case TextIO.inputLine TextIO.stdIn of
               NONE => ""
             | SOME s => s
    in
	case Int.fromString response of
	    NONE => (case String.explode response of
			  []        => ()
	                | [#"\n"]   => ()
			| #"Q" :: _ => ()
			| #"q" :: _ => ()
			| _         => choose sought entries)
	  | SOME choice =>
		if choice = 0 then ()
		else showFile sought (List.nth(entries, choice - 1))
    end
    handle Subscript => choose sought entries
	 | Overflow  => choose sought entries;

(* Display the menu of identifiers matching the given one, or
 * invoke the browser directly if these is only one match:
 *)

fun display sought []                  = raise Fail "Help.display"
  | display sought [entry]             = showFile sought entry
  | display sought (entries as e0::er) =
    let open Database
        fun render (entry as {comp, file, ...}) =
	    case comp of
		Str    => "structure " ^ file
	      | Exc id => "exn  " ^ file ^ "." ^ id
	      | Typ id => "type " ^ file ^ "." ^ id
	      | Val id => "val  " ^ file ^ "." ^ id
	      | Con id => "con  " ^ file ^ "." ^ id
	      | Term (id, NONE)      => id ^ " (" ^ file ^ ")"
	      | Term (id, SOME kind) => kind ^ " " ^ id ^ " (" ^ file ^ ")"
	fun maxlen []         max = max
	  | maxlen (e1 :: er) max =
	    let val len = size (render e1)
	    in maxlen er (if len > max then len else max) end
	val maxwidth = maxlen er (size (render e0))
	val boxwidth = 6 + 3 + 3 + maxwidth + 2
	val horizontal = StringCvt.padRight #"-" boxwidth "    " ^ "\n"

	fun prline lin [] = ()
	  | prline lin (e1 :: rest) =
	    (print "    | ";
	     print (StringCvt.padLeft #" " 3 (Int.toString lin));
	     print " | ";
	     print (StringCvt.padRight #" " maxwidth (render e1));
	     print " |\n";
	     prline (lin+1) rest)
    in
	print "\n";
	print horizontal;
	prline 1 entries;
	print horizontal;
	choose sought entries
    end

in

(* Main help function: search for a string in the signature index database: *)

fun defaultBrowser ""    = show "help"     0 NONE (!welcome)
  | defaultBrowser "lib" = show "Overview" 0 NONE (readfile "README")
  | defaultBrowser id    =
    let fun getdb filename =
	    (Database.readbase filename)
	    handle OS.SysErr _ => raise Fail "Cannot read help database!"
	val sought = toLower id
	fun lookone(dbn, res) = Database.lookup(getdb dbn, sought) :: res
	fun tryspecial [] =
	    (case List.concat(List.foldl lookone [] (!indexfiles)) of
		 [] =>
		     print ("\nSorry, no help on identifier `" ^ id ^ "'\n\n")
	       | entries  => display sought entries)
	  | tryspecial ({term, file, title} :: rest) =
	    if term = sought then show title 0 NONE (readfile file)
	    else tryspecial rest
    in
	tryspecial (!specialfiles)
    end
val browser = ref defaultBrowser
(* It appears necessary to eat the newline that entered the call to "help" *)
fun help s = (TextIO.inputLine TextIO.stdIn; !browser s)

end
end
