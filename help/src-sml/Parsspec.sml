(* Parsspec -- parse Moscow ML signature files.

*)

structure Parsspec = struct

open List 

structure SMLLrVals =
  SMLLrValsFun(structure Token = LrParser.Token);
structure SMLLex = 
  SMLLexFun(structure Tokens = SMLLrVals.Tokens);
structure SMLParser =
  JoinWithArg(structure ParserData = SMLLrVals.ParserData
              structure Lex=SMLLex
              structure LrParser=LrParser);
  
fun parseSpec is =
  let val lexer = SMLParser.makeLexer (fn n => TextIO.inputN (is, n)) 0
      fun print_error (s,(bc:int,bl:int),(ec:int,el:int)) =
        if bc = ~1 andalso bl = ~1 then () else
            TextIO.output(TextIO.stdOut,
               "\nError, " ^ "between line " ^ (Int.toString (bl + 1)) ^
                                " and line " ^ (Int.toString (el + 1)) ^ ":\n   "
                           ^ s)
  in
    #1 (SMLParser.parse(15, lexer, print_error, ()))
    (* #1 (SMLParser.parse(15, lexer, (fn _ => ()), ())) *)
  end;

fun processSpec is str (((pos1, pos2), spec), res) =
    let open Asynt Database
	fun getId ({qualid = {id, ...}, ...} : IdInfo) = id
	fun valdesc ((idInfo, ty), res) =
	    {comp = Val (getId idInfo), file = str, line = #2 pos1} :: res
	fun pvaldesc ((idInfo, ty, arity, cfun), res) =
	    {comp = Val (getId idInfo), file = str, line = #2 pos1} :: res
	fun typdesc ((tyvars, idInfo), res) =
	    {comp = Typ (getId idInfo), file = str, line = #2 pos1} :: res
	fun typbind ((tyvars, idInfo, ty), res) =
	    {comp = Typ (getId idInfo), file = str, line = #2 pos1} :: res
	fun conbind ((ConBind(idInfo, tyOpt)), res) =
	    {comp = Con (getId idInfo), file = str, line = #2 pos1} :: res
	fun datbind ((tyvars, idInfo, cbs), res) =
	    {comp = Typ (getId idInfo), file = str, line = #2 pos1}
	    :: foldl conbind res cbs
	fun datrep (idInfo, res) =
	    {comp = Typ (getId idInfo), file = str, line = #2 pos1} :: res
	fun exdesc ((idInfo, tyOpt), res) =
	    {comp = Exc (getId idInfo), file = str, line = #2 pos1} :: res
    in
	case spec of
	    VALspec vs                  => foldl valdesc res vs
	  | PRIM_VALspec pvs            => foldl pvaldesc res pvs
	  | TYPEDESCspec (tnEqu, tyds)  => foldl typdesc res tyds
	  | TYPEspec tybs               => foldl typbind res tybs
	  | DATATYPEspec (dbs, tybsOpt) =>
		foldl datbind (foldl typbind res (getOpt(tybsOpt, []))) dbs
	  | DATATYPErepspec (ty, _)     => datrep (ty, res)
	  | EXCEPTIONspec eds           => foldl exdesc res eds
	  | LOCALspec (spec1, spec2)    => processSpec is str (spec2, res)
	  | OPENspec strs               => res
	  | INCLUDEspec strs            => res
	  | EMPTYspec                   => res
	  | SEQspec (spec1, spec2)      =>
		processSpec is str (spec2, processSpec is str (spec1, res))
	  | STRUCTUREspec moddescs      => res (* TODO: add link *)
    end

fun parseAndProcess dir str res =
    let val basefile = OS.Path.joinBaseExt {base = str, ext = SOME "sig"}
        val filename = OS.Path.joinDirFile {dir=dir, file = basefile}
	(* val _ = print("Parsing " ^ basefile ^ " ... "); *)
	val resLength = length res
	val is        = TextIO.openIn filename
	(**) val _ = print("Parsing " ^ basefile ^ " ... "); (**)
	val specs     = case parseSpec is
                         of Asynt.NamedSig {specs, ...} => specs
			  | Asynt.AnonSig specs         => specs;
	(**) val _ = print("completed parse ... "); (**)
	val initialbase = {comp = Database.Str, file = str, line = 0} :: res
	val res = foldl (processSpec is str) initialbase specs
	(**) val _ = print ("processed " ^ Int.toString (length res - resLength)
		       ^ " entries.\n") (**)
    in
	TextIO.closeIn is; res
    end
    handle SML90.Interrupt => raise SML90.Interrupt
         | _ => (print ("Failed to parse (or find?) "^str^
                        ".sig (continuing anyway).\n");
                 res)

(* To parse the signature of unit `filename' and prepend the
 * entries to the list res:
 *)

fun processfile stoplist dir (filename, res) =
    let val {base, ext} = OS.Path.splitBaseExt filename
    in
	case ext of
	    SOME "sig" =>
		if List.exists (fn name => base = name) stoplist then
		    res
		else
		    parseAndProcess dir base res
	  | _          => res
    end
end
