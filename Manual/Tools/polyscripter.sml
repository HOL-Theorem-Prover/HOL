val _ = PolyML.SaveState.loadState "../../bin/hol.state";

val _ = use "../../tools-poly/prelude.ML";
val _ = use "../../tools-poly/prelude2.ML";
val _ = PolyML.print_depth 0;

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun lnumdie linenum extra exn =
  die ("Exception raised on line " ^ Int.toString linenum ^ ": "^
       extra ^ General.exnMessage exn)

fun mkBuffer () = let
  val buf = ref ([] : string list)
  fun push s = buf := s :: !buf
  fun read () = let
    val contents = String.concat (List.rev (!buf))
  in
    buf := [contents];
    contents
  end
  fun reset() = buf := []
in
  (push, read, reset)
end;

use "../../tools/quote-filter/filter.sml";

val (QBpush, QBread, QBreset) = mkBuffer()
val qstate = filter.UserDeclarations.newstate(QBpush, fn () => ())

fun readFromString s =
  let
    val sz = size s
    val i = ref 0
    fun read _ =
      if !i < sz then str (String.sub(s, !i)) before i := !i + 1
      else ""
  in
    read
  end

fun quote s =
  (QBreset() ; filter.makeLexer (readFromString s) qstate ();
   QBread())

fun quoteFile lnum fname =
  let
    val instrm = TextIO.openIn fname handle e => lnumdie lnum "" e
  in
    QBreset() ;
    filter.makeLexer (fn n => TextIO.input instrm) qstate ();
    TextIO.closeIn instrm;
    QBread()
  end


datatype lbuf =
         LB of {
           currentOpt : string option ref,
           strm : TextIO.instream ,
           line : int ref
         }

fun current (LB {currentOpt, ...}) = !currentOpt
fun linenum (LB {line, ...}) = !line
fun advance (LB {strm, currentOpt, line}) =
  (currentOpt := TextIO.inputLine strm ;
   line := !line + 1)

fun mklbuf strm =
  let
    val lb = LB {currentOpt = ref NONE, strm = strm, line = ref 0}
    val _ = advance lb
  in
    lb
  end

fun mkLex s = let
  val i = ref 0
  val sz = size s
  fun doit () =
    if !i < sz then SOME (String.sub(s,!i)) before i := !i + 1
    else NONE
in
  doit
end

fun compiler (obufPush, obufRD, obufRST) linenum infn = let
  fun record_error {message,...} = PolyML.prettyPrint(obufPush,70) message
  fun rpt acc =
    (obufRST();
     PolyML.compiler(infn,
                     [PolyML.Compiler.CPErrorMessageProc record_error,
                      PolyML.Compiler.CPOutStream obufPush]) ()
     handle e => lnumdie linenum (obufRD()) e;
     if obufRD() = "" then String.concat (List.rev acc)
     else rpt (obufRD() :: acc))
in
  rpt []
end

fun silentUse lnum s =
  let
    val filecontents = quoteFile lnum s
    val buf = mkBuffer()
  in
    compiler buf 1 (mkLex filecontents)
  end


fun umunge umap s =
  let
    fun recurse acc s =
      case UTF8.getChar s of
          NONE => String.concat (List.rev acc)
        | SOME ((c, _), rest) =>
          case Binarymap.peek(umap, c) of
              NONE => recurse (c :: acc) rest
            | SOME s => recurse (s :: acc) rest
  in
    recurse [] s
  end

fun process_line umap (obuf as (_, _, obRST)) line lbuf = let
  fun getRest acc =
    let
      val _ = advance lbuf
    in
      case current lbuf of
          NONE => String.concat (List.rev acc)
        | SOME s => if String.size s > 1 andalso
                       Char.isSpace (String.sub(s,0))
                    then
                      getRest (String.extract(s,1,NONE)::acc)
                    else
                      String.concat (List.rev acc)
    end
in
  if String.isPrefix "##use " line then
    let
      val fname = String.substring(line, 6, size line - 7) (* for \n at end *)
      val _ = silentUse (linenum lbuf) fname
      val _ = advance lbuf
    in
      ("\n", NONE)
    end
  else if String.isPrefix ">>__" line then
    let
      val firstline = String.extract(line, 4, NONE)
      val input = getRest [firstline]
      val _ = compiler obuf (linenum lbuf) (mkLex (quote input))
    in
      ("\n", NONE)
    end
  else if String.isPrefix ">>_" line then
    let
      val firstline = String.extract(line, 3, NONE)
      val input = getRest [firstline]
      val _ = compiler obuf (linenum lbuf) (mkLex (quote input))
    in
      (umunge umap input, SOME "  ... output elided ...\n")
    end
  else if String.isPrefix ">>" line then
    let
      val _ = obRST()
      val firstline = String.extract(line, 2, NONE)
      val input = getRest [firstline]
    in
      (umunge umap input,
       SOME (umunge umap (compiler obuf (linenum lbuf) (mkLex (quote input)))))
    end
  else
    (advance lbuf; (line, NONE))
end

fun read_umap fname =
  let
    val instrm = TextIO.openIn fname
    fun recurse (i, acc) =
      case TextIO.inputLine instrm of
          SOME line =>
          (if size line <= 1 then recurse (i + 1, acc)
           else
             case UTF8.getChar line of
                NONE => die ("read_umap: should never happen")
              | SOME ((cstr, _), rest) =>
                let
                  val restss = Substring.full rest
                  val range =
                      restss |> Substring.dropl Char.isSpace
                             |> Substring.dropr Char.isSpace
                             |> Substring.string
                in
                  recurse(i + 1, Binarymap.insert(acc, cstr, range))
                end)
        | NONE => acc
  in
    recurse(1, Binarymap.mkDict String.compare)
  end


fun usage() =
  "Usage:\n  "^ CommandLine.name() ^ " [umapfile]"

fun main () =
  let
    val _ = PolyML.print_depth 100;
    val _ = Parse.current_backend := PPBackEnd.raw_terminal
    val umap =
        case CommandLine.arguments() of
            [] => Binarymap.mkDict String.compare
          | [name] => read_umap name
          | _ => die (usage())
    val (obuf as (obPush, _, _)) = mkBuffer()
    val _ = Feedback.ERR_outstream := obPush
    val _ = Feedback.WARNING_outstream := obPush
    val _ = Feedback.MESG_outstream := obPush
    val cvn = PolyML.Compiler.compilerVersionNumber
    val _ = if cvn = 551 orelse cvn = 552 then
              ignore (TextIO.inputLine TextIO.stdIn)
            else ()
    val lb = mklbuf TextIO.stdIn
    fun recurse lb : unit=
      case current lb of
          NONE => ()
        | SOME line =>
          let
            val (i, coutopt) = process_line umap obuf line lb
          in
            (case coutopt of
                NONE => print i
              | SOME out => print (">" ^ i ^ out));
            recurse lb
          end
  in
    recurse lb
  end
