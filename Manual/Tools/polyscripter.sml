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

val elision_string1 =
    ref "\\quad\\textit{\\small\\dots{}output elided\\dots{}}\n"

fun deleteTrailingWhiteSpace s =
  let
    open Substring
    val (pfx, sfx) = splitr Char.isSpace (full s)
    val noNLsfx = dropl (not o equal #"\n") sfx
    val term = if size noNLsfx = 0 then "" else "\n"
  in
    string pfx ^ term
  end

fun cruftSuffix sfxs s =
  case List.find (fn (sfx,_) => String.isSuffix sfx s) sfxs of
      NONE => NONE
    | SOME (sfx,rep) => SOME (String.substring(s, 0, size s - size sfx) ^ rep)

val cruftySuffixes = ref [
      (":\n   proofs\n", ""),
      ("\n: proof\n", "\n"),
      (":\n   proof\n", "\n")
    ]

fun removeCruft s =
  case cruftSuffix (!cruftySuffixes) s of
      NONE => s
    | SOME s' => removeCruft s'

fun addIndent ws = String.translate(fn #"\n" => "\n"^ws | c => str c)

fun transformOutput umap ws s =
  s |> umunge umap
    |> removeCruft
    |> addIndent ws
    |> deleteTrailingWhiteSpace

val getIndent =
  (Substring.string ## Substring.string)
    o Substring.splitl Char.isSpace o Substring.full

fun process_line umap (obuf as (_, _, obRST)) line lbuf = let
  val (ws,line) = getIndent line
  val indent = String.size ws
  fun getRest acc =
    let
      val _ = advance lbuf
    in
      case current lbuf of
          NONE => String.concat (List.rev acc)
        | SOME s =>
          let
            val (ws',s) = getIndent s
          in
            if indent < String.size ws'
            then getRest (s::acc)
            else String.concat (List.rev acc)
          end
    end
  val assertcmd = "##assert "
  val assertcmdsz = size assertcmd
in
  if String.isPrefix assertcmd line then
    let
      val e = String.substring(line, assertcmdsz, size line - assertcmdsz - 1)
                              (* for \n at end *)
      val _ = compiler obuf (linenum lbuf)
                       (mkLex ("val _ = if (" ^ quote e ^ ") then () " ^
                               "else die \"Assertion failed: line " ^
                               Int.toString (linenum lbuf) ^ "\";"))
      val _ = advance lbuf
    in
      ("\n", NONE)
    end
  else if String.isPrefix "##use " line then
    let
      val fname = String.substring(line, 6, size line - 7) (* for \n at end *)
      val _ = silentUse (linenum lbuf) fname
      val _ = advance lbuf
    in
      ("", NONE)
    end
  else if String.isPrefix ">>__" line then
    let
      val firstline = String.extract(line, 4, NONE)
      val input = getRest [firstline]
      val _ = compiler obuf (linenum lbuf) (mkLex (quote input))
    in
      ("", NONE)
    end
  else if String.isPrefix ">>_" line then
    let
      val firstline = String.extract(line, 3, NONE)
      val input = getRest [firstline]
      val _ = compiler obuf (linenum lbuf) (mkLex (quote input))
      fun removeNL s = String.substring(s, 0, size s - 1)
    in
      (ws^">"^addIndent ws (removeNL (umunge umap input)), SOME (!elision_string1))
    end
  else if String.isPrefix ">>" line then
    let
      val _ = obRST()
      val firstline = String.extract(line, 2, NONE)
      val input = getRest [firstline]
      val raw_output = compiler obuf (linenum lbuf) (mkLex (quote input))
    in
      (ws^">"^addIndent ws (umunge umap input), SOME (transformOutput umap ws raw_output))
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
              | SOME out => print (i ^ out));
            recurse lb
          end
  in
    recurse lb
  end
