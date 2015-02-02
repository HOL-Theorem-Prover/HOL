(* Holdep -- computing dependencies for a (list of) Moscow ML
   source files. Also has knowledge of HOL script and theory files.
   Handles strings and nested comments correctly;

   DOES NOT normalize file names under DOS. (yet)

  This has been adapted from the mosmldep in the MoscowML compiler
  sources, first by Ken Larsen and later by Konrad Slind and
  Michael Norrish.
*)
structure Holdep :> Holdep =
struct

structure Process = OS.Process

fun normPath s = Path.toString(Path.fromString s)
fun manglefilename s = normPath s
fun errMsg str = BasicIO.output(BasicIO.std_err, str ^ "\n\n")
fun fail()     = Process.exit Process.failure

fun addExt s ""  = normPath s
  | addExt s ext = normPath s^"."^ext;
fun addDir dir s = Path.joinDirFile{dir=normPath dir,file=s}
val srev = String.implode o List.rev o String.explode

val space = " ";
fun spacify [] = []
  | spacify [x] = [x]
  | spacify (h::t) = h::space::spacify t;

fun createLexerStream (is : BasicIO.instream) =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n)

fun parsePhraseAndClear (file, stream) parsingFun lexingFun lexbuf = let
  val phr = parsingFun lexingFun lexbuf handle
    Parsing.ParseError f => let
      val pos1 = Lexing.getLexemeStart lexbuf
      val pos2 = Lexing.getLexemeEnd lexbuf
    in
      Location.errMsg (file, stream, lexbuf) (Location.Loc(pos1, pos2))
      "Syntax error."
    end
  | Lexer.LexicalError(msg, pos1, pos2) =>
    if pos1 >= 0 andalso pos2 >= 0 then
      Location.errMsg (file, stream, lexbuf)
      (Location.Loc(pos1, pos2))
      ("Lexical error: " ^ msg)
    else
      (Location.errPrompt ("Lexical error: " ^ msg ^ "\n\n");
       raise Fail "Lexical error")
  | x => (Parsing.clearParser(); raise x)
in
  Parsing.clearParser();
  phr
end;

fun parseFile (f, strm) =
  parsePhraseAndClear (f, strm) Parser.MLtext Lexer.Token;

fun access {assumes, includes} cdir s ext = let
  val sext = addExt s ext
  fun inDir dir = FileSys.access (addDir dir sext, [])
in
  if inDir cdir orelse List.exists (fn nm => nm = sext) assumes then SOME s
  else
    case List.find inDir includes of
      SOME dir => SOME(addDir dir s)
    | NONE     => NONE
end

fun isTheory s =
  case List.rev(String.explode s) of
    #"y" :: #"r" :: #"o" :: #"e" :: #"h" :: #"T" :: n::ame =>
      SOME(String.implode(List.rev (n::ame)))
  | _ => NONE

fun addThExt s s' ext = addExt (addDir (Path.dir s') s) ext
fun outname (rcd as {assumes,includes}) cdir (s, res) =
  case isTheory s of
    SOME n => let
    in
      (* allow a dependency on a theory if we can see a script.sml file *)
      case access rcd cdir (n^"Script") "sml" of
        SOME s' => addThExt s s' "ui" :: res
      | NONE => let
        in
          (* or, if we can see the theory.ui file already; which might
             happen if the theory file is in sigobj *)
          case access rcd cdir (n^"Theory") "ui" of
            SOME s' => addThExt s s' "ui" :: res
          | NONE => res
        end
    end
  | _ => let
    in
      case access rcd cdir s "sig" of
        SOME s' => addExt s' "ui" :: res
      | _       => let
        in
          case access rcd cdir s "sml" of
            (* this case handles the situation where there is no .sig file
               locally, but a .sml file instead; compiling this will generate
               the .ui file too.  We have to say that we're dependent
               on the .uo file because the automatic logic will then
               correctly hunt back to the .sml file *)
            SOME s' => addExt s' "uo" :: res
          | _       => let
            in
              (* this case added to cover the situations where we think we
                 are dependent on module foo, but we can't find foo.sml or
                 foo.sig.  This can happen when foo.sml exists in some
                 HOL directory but no foo.sig.  In this situation, the HOL
                 build process only copies foo.ui and foo.uo across to
                 sigobj (and not the .sig file that we usually find there),
                 so making the dependency analysis ignore foo.  We cover
                 this possibility by looking to see if we can see a .ui
                 file; if so, we can retain the dependency *)
              case access rcd cdir s "ui" of
                SOME s' => addExt s' "ui" :: res
              | NONE => res
            end
        end
    end

fun beginentry objext target = let
  val targetname = addExt target objext
in
  (targetname,
   if objext = "uo" andalso FileSys.access(addExt target "sig", []) then
     [addExt target "ui"]
   else [])
end;

val escape_spaces = let
  fun translation c = if c = #" " then "\\ "
                      else if c = #"\\" then "\\\\"
                      else str c
  val escape_space = String.translate translation
in
  map escape_space
end

fun endentry tgtname s =
    if null s then ""
    else
      hd (escape_spaces [tgtname]) ^ ": " ^
      String.concat (spacify (rev ("\n" :: escape_spaces s)))

fun read {assumes, includes, srcext, objext, filename} = let
  open OS.FileSys Systeml
  val op ^ = Path.concat
  val unquote = xable_string(Systeml.HOLDIR ^ "bin" ^ "unquote")
  val file0 = addExt filename srcext
  val actualfile =
      if access (unquote, [A_EXEC]) then let
          val newname = tmpName()
        in
          if Process.isSuccess (Systeml.systeml [unquote, file0, newname]) then
            newname
          else file0
        end
      else file0
  val is       = BasicIO.open_in actualfile
  val lexbuf   = createLexerStream is
  val names    = parseFile (filename, is) lexbuf
  val mentions = Binaryset.addList (Binaryset.empty String.compare, names)
  val _        = BasicIO.close_in is
  val _        = if actualfile <> file0 then
                   FileSys.remove actualfile handle _ => ()
                 else ()
  val curr_dir = Path.dir filename
  val outrcd = {assumes = assumes, includes = includes}
  val (targetname, res0) = beginentry objext (manglefilename filename);
  val res = Binaryset.foldl
              (fn (s, acc) => outname outrcd curr_dir (manglefilename s, acc))
              res0
              mentions
in
  endentry targetname res
end
  handle (e as Parsing.ParseError _) => (print "Parse error!\n"; raise e)


fun processfile {assumes, includes, fname = filename, debug} =
    let (* val _ = output(std_err, "Processing " ^ filename ^ "\n"); *)
	val {base, ext} = Path.splitBaseExt filename
    in
	case ext of
	    SOME "sig" => read {assumes = assumes, srcext = "sig", objext = "ui",
                                filename = base, includes = includes}
	  | SOME "sml" => read {assumes = assumes, srcext = "sml", objext = "uo",
                                filename = base, includes = includes}
	  | _          => ""
    end

(* assumes parameter is a list of files that we assume can be built in this
   directory *)
fun main (r as {assumes, debug, includes, fname}) =
  let
    val results = processfile r
  in
    if debug then print ("Holdep: "^results^"\n") else ();
    results
  end
   handle e as OS.SysErr (str, _) => (errMsg str; raise e)

end (* struct *)
