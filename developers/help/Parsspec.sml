(* Parsspec -- parse Moscow ML signature files.
 
*)

open BasicIO List

(* Lexer of stream *)

fun createLexerStream (is : instream) =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n)
;

fun parsePhraseAndClear parsingFun lexingFun lexbuf =
  let val phr =
    parsingFun lexingFun lexbuf
    handle x => (Parsing.clearParser(); raise x)
  in
    Parsing.clearParser();
    phr
  end;

val parseSpec =
  parsePhraseAndClear Parser.SigFile Lexer.Token;

fun processSpec is str ((Location.Loc(pos1, pos2), spec), res) =
    let fun getline line pos =
	    if pos < pos1 then 
		case Nonstdio.input_char is of
		    #"\^Z" => raise Fail "Parsspec.processSpec: internal error"
		  | #"\n"  => getline (line+1) (pos+1)
		  | _      => getline line (pos+1)
	    else line
	val lineno = (Nonstdio.seek_in is 0; getline 0 0)
	open Asynt Database
	fun getId ({qualid = {id, ...}, ...} : IdInfo) = id
	fun valdesc ((idInfo, ty), res) = 
	    {comp = Val (getId idInfo), file = str, line = lineno} :: res
	fun pvaldesc ((idInfo, ty, arity, cfun), res) = 
	    {comp = Val (getId idInfo), file = str, line = lineno} :: res
	fun typdesc ((tyvars, idInfo), res) = 
	    {comp = Typ (getId idInfo), file = str, line = lineno} :: res
	fun typbind ((tyvars, idInfo, ty), res) = 
	    {comp = Typ (getId idInfo), file = str, line = lineno} :: res
	fun conbind ((ConBind(idInfo, tyOpt)), res) = 
	    {comp = Con (getId idInfo), file = str, line = lineno} :: res
	fun datbind ((tyvars, idInfo, cbs), res) =
	    {comp = Typ (getId idInfo), file = str, line = lineno} 
	    :: foldl conbind res cbs
	fun exdesc ((idInfo, tyOpt), res) = 
	    {comp = Exc (getId idInfo), file = str, line = lineno} :: res
    in
	case spec of
	    VALspec vs                  => foldl valdesc res vs
	  | PRIM_VALspec pvs            => foldl pvaldesc res pvs
	  | TYPEDESCspec (tnEqu, tyds)  => foldl typdesc res tyds
	  | TYPEspec tybs               => foldl typbind res tybs
	  | DATATYPEspec (dbs, tybsOpt) => 
		foldl datbind (foldl typbind res (getOpt(tybsOpt, []))) dbs
	  | EXCEPTIONspec eds           => foldl exdesc res eds
	  | LOCALspec (spec1, spec2)    => processSpec is str (spec2, res)
	  | OPENspec strs               => res
	  | EMPTYspec                   => res
	  | SEQspec (spec1, spec2)      => 
		processSpec is str (spec2, processSpec is str (spec1, res))
    end

fun parseAndProcess dir str res =
    let val filename = Path.joinDirFile
	    {dir=dir, file = Path.joinBaseExt{base = str, ext = SOME "sig"}}
	val _ = print("Parsing " ^ filename ^ " ... "); 
	val resLength = length res
	val is           = open_in filename
	val lexbuf       = createLexerStream is
	val specs        = case parseSpec lexbuf of
	                        Asynt.NamedSig {specs, ...} => specs
			      | Asynt.AnonSig specs         => specs;
	val initialbase = {comp = Database.Str, file = str, line = 0} :: res
	val res = foldl (processSpec is str) initialbase specs
	val _ = print ("processed " ^ Int.toString (length res - resLength)
		       ^ " entries.\n")
    in
	close_in is; res
    end
    handle exn as Parsing.ParseError _ => 
	(print ("Parseerror in signature " ^ str ^ ".\n"); raise exn)

(* To parse the signature of unit `filename' and prepend the 
 * entries to the list res:
 *)

fun processfile stoplist dir (filename, res) =
    let val {base, ext} = Path.splitBaseExt filename
    in 
	case ext of
	    SOME "sig" => 
		if List.exists (fn name => base = name) stoplist then 
		    res
		else 
		    parseAndProcess dir base res
	  | _          => res
    end
