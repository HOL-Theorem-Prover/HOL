(* Holdep -- computing dependencies for a (list of) Moscow ML
   source files. Also has knowledge of HOL script and theory files.
   Handles strings and nested comments correctly;

   DOES NOT normalize file names under DOS. (yet)

  This has been adapted from the mosmldep in the MoscowML compiler
  sources, first by Ken Larsen and later by Konrad Slind and
  Michael Norrish.
*)


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

local val path    = ref [""]
      fun lpcl []                = (errMsg "No filenames"; fail())
        | lpcl ("-I"::dir::tail) = (path := dir :: !path ; lpcl tail)
        | lpcl l                 = l
in
fun parseComLine l =
  let val s = lpcl l
  in
    path := List.rev (!path);
    s
  end

fun access cdir s ext =
  let val sext = addExt s ext
      fun inDir dir = FileSys.access (addDir dir sext, [])
  in if inDir cdir then SOME s
     else case List.find inDir (!path)
           of SOME dir => SOME(addDir dir s)
            | NONE     => NONE
  end

end;

local val res = ref [];
in
fun isTheory s =
  case List.rev(String.explode s) of
    #"y" :: #"r" :: #"o" :: #"e" :: #"h" :: #"T" :: n::ame =>
      SOME(String.implode(List.rev (n::ame)))
  | _ => NONE

fun addThExt s s' ext = addExt (addDir (Path.dir s') s) ext
fun outname cdir s =
  case isTheory s of
    SOME n => let
    in
      case access cdir (n^"Script") "sig" of
        SOME s' => res := addThExt s s' "ui" :: !res
      | _  => let
        in
          case access cdir (n^"Script") "sml" of
            SOME s' => res := addThExt s s' "uo" :: !res
          | NONE => let
            in
              case access cdir (n^"Theory") "uo" of
                SOME s' => res := addThExt s s' "uo" :: !res
              | NONE => ()
            end
        end
    end
  | _ => let
    in
      case access cdir s "sig" of
        SOME s' => res := addExt s' "ui" :: !res
      | _       => let
        in
          case access cdir s "sml" of
            SOME s' => res := addExt s' "uo" :: !res
          | _       => let
            in
              (* this case added to cover the situations where we think we
                 are dependent on module foo, but we can't find foo.sml or
                 foo.sig.  This can happen when foo.sml exists in some
                 HOL directory but no foo.sig.  In this situation, the HOL
                 build process only copies foo.ui and foo.uo across to sigobj,
                 so making the dependency analysis ignore foo.  We cover
                 this possibility by looking to see if we can see a .uo
                 file; if so, we can retain the dependency *)
              case access cdir s "uo" of
                SOME s' => res := addExt s' "uo" :: !res
              | NONE => ()
            end
        end
    end

fun beginentry objext target = let
  val targetname = addExt target objext
in
  res := [targetname ^ ":"];
  if objext = "uo" andalso FileSys.access(addExt target "sig", []) then
    res := addExt target "ui" :: !res
  else ()
end;

fun endentry() = (* for non-file-based Holdep *)
  if length (!res) > 1
  then String.concat (spacify (rev ("\n" :: !res)))
   else ""
end;

fun read srcext objext filename =
 let val is       = BasicIO.open_in (addExt filename srcext)
     val lexbuf   = createLexerStream is
     val mentions = Polyhash.mkPolyTable (37, Subscript)
     fun insert s = Polyhash.insert mentions (s,())
     val names    = parseFile (filename, is) lexbuf
     val _        = BasicIO.close_in is
     val curr_dir = Path.dir filename
 in
   beginentry objext (manglefilename filename);
   app insert names;
   Polyhash.apply (outname curr_dir o manglefilename o #1) mentions;
   endentry ()
 end
  handle (e as Parsing.ParseError _) => (print "Parse error!\n"; raise e)


fun processfile filename =
    let (* val _ = output(std_err, "Processing " ^ filename ^ "\n"); *)
	val {base, ext} = Path.splitBaseExt filename
    in
	case ext of
	    SOME "sig" => read "sig" "ui" base
	  | SOME "sml" => read "sml" "uo" base
	  | _          => ""
    end

fun main debug sl =
  let val cl_args = parseComLine sl
      val results = List.map processfile cl_args
      val final = String.concat results
  in
    if debug then print ("Holdep: "^final^"\n") else ();
    final
  end
   handle e as OS.SysErr (str, _) => (errMsg str; raise e)

(* val _ = main (parseComLine(CommandLine.arguments())) *)
