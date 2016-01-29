val _ = PolyML.SaveState.loadState "../../bin/hol.state";

val _ = use "../../tools-poly/prelude.ML";
val _ = use "../../tools-poly/prelude2.ML";
val _ = PolyML.print_depth 0;

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun lnumdie linenum extra exn =
  die ("Exception raised on line " ^ Int.toString linenum ^ ": "^
       extra ^ General.exnMessage exn)

val outputPrompt = ref ">"

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

fun compiler (obufPush, obufRD, obufRST) handler infn = let
  fun record_error {message,...} = PolyML.prettyPrint(obufPush,70) message
  fun rpt acc =
    (obufRST();
     PolyML.compiler(infn,
                     [PolyML.Compiler.CPErrorMessageProc record_error,
                      PolyML.Compiler.CPOutStream obufPush]) ()
     handle e => handler (obufRD()) e;
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
    compiler buf (lnumdie 1) (mkLex filecontents)
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

fun remove_multi_goalproved s =
  let
    val ss = Substring.full s
    val (l,r) = Substring.position "\n\nGoal proved." ss
    fun recurse ss =
      let
        val ss' = Substring.slice(ss, 1, NONE)
        val (l,r) = Substring.position "\n\nGoal proved." ss'
      in
        if Substring.size r <> 0 then
          case recurse r of NONE => SOME r | x => x
        else NONE
      end
  in
    if Substring.size r <> 0 then
      case recurse r of
          NONE => NONE
        | SOME r' =>
          SOME (Substring.string l ^ !elision_string1 ^
                Substring.string (Substring.triml 1 r'))
    else
      NONE
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

fun try _ [] s = s
  | try restart (f::fs) s = case f s of
                                SOME s' => restart s'
                              | NONE => try restart fs s

fun remove_nsubgoals s =
  let
    open Substring
    val ss0 = full s
    val (ss,_) = splitr Char.isSpace ss0
  in
    if isSuffix "subgoals" ss then
      let
        val (p,s) = splitr (fn c => c <> #"\n") ss
        val (sn, rest) = splitl Char.isDigit s
      in
        if size sn <> 0 andalso string rest = " subgoals" then SOME (string p)
        else NONE
      end
    else NONE
  end

fun removeCruft s =
  try removeCruft [cruftSuffix (!cruftySuffixes),
                   remove_multi_goalproved,
                   remove_nsubgoals]
      s

fun addIndent ws = String.translate(fn #"\n" => "\n"^ws | c => str c)

fun transformOutput umap ws s =
  s |> umunge umap
    |> removeCruft
    |> addIndent ws
    |> deleteTrailingWhiteSpace
    |> (fn s => ws ^ s)

fun spaceNotNL c = Char.isSpace c andalso c <> #"\n"

val getIndent =
  (Substring.string ## Substring.string)
    o Substring.splitl spaceNotNL o Substring.full

fun process_line umap (obuf as (_, _, obRST)) origline lbuf = let
  val (ws,line) = getIndent origline
  val indent = String.size ws
  val oPsize = size (!outputPrompt)
  fun getRest userPromptSize acc =
    let
      val _ = advance lbuf
      val handlePromptSize =
        if userPromptSize > oPsize then
          fn i => fn s =>
             if i < userPromptSize then
               s |> Substring.full |> Substring.dropl Char.isSpace
                 |> Substring.string
             else
               String.extract(s, userPromptSize - oPsize, NONE)
        else
          let
            val ws_n =
                CharVector.tabulate(oPsize - userPromptSize, fn _ => #" ")
          in
            fn i => fn s => ws_n ^ s
          end
    in
      case current lbuf of
          NONE => String.concat (List.rev acc)
        | SOME s =>
          let
            val (ws',_) = getIndent s
            val wssz = String.size ws'
          in
            if indent < wssz
            then getRest userPromptSize (handlePromptSize wssz s::acc)
            else String.concat (List.rev acc)
          end
    end
  val assertcmd = "##assert "
  val assertcmdsz = size assertcmd
in
  if String.isPrefix ">>>" line then
    (advance lbuf; (ws ^ String.extract(line, 1, NONE), NONE))
  else if String.isPrefix "###" line then
    (advance lbuf; (ws ^ String.extract(line, 1, NONE), NONE))
  else if String.isPrefix assertcmd line then
    let
      val e = String.substring(line, assertcmdsz, size line - assertcmdsz - 1)
                              (* for \n at end *)
      val _ = compiler obuf (lnumdie (linenum lbuf))
                       (mkLex ("val _ = if (" ^ quote e ^ ") then () " ^
                               "else die \"Assertion failed: line " ^
                               Int.toString (linenum lbuf) ^ "\";"))
      val _ = advance lbuf
    in
      ("\n", NONE)
    end
  else if String.isPrefix "##eval" line then
    let
      val line = String.extract(line, 6, NONE)
      val e = Fail ""
      val (inputpfx, firstline, indent) =
          if String.isPrefix "[" line then
            let
              val ss = Substring.full line
              val (p,s) = Substring.position "] " ss
              val _ = Substring.size s <> 0 orelse
                      lnumdie (linenum lbuf) "Mal-formed ##eval directive" e
              val vname = String.extract(Substring.string p, 1, NONE)
              val firstline = String.extract(Substring.string s, 2, NONE)
            in
              ("val "^vname^" = ", firstline, 9 + size vname)
            end
          else
            ("", String.extract(line, 1, NONE), 7)
              handle Subcript =>
                     lnumdie (linenum lbuf) "Mal-formed ##eval directive" e
      val input = getRest (indent + 1) [firstline]
      val _ = compiler obuf
                       (lnumdie (linenum lbuf))
                       (mkLex (quote (inputpfx ^ input)))
    in
      (ws ^ umunge umap input, NONE)
    end
  else if String.isPrefix "##use " line then
    let
      val fname = String.substring(line, 6, size line - 7) (* for \n at end *)
      val _ = silentUse (linenum lbuf) fname
      val _ = advance lbuf
    in
      ("", NONE)
    end
  else if String.isPrefix ">>-" line then
    let
      val firstline = String.extract(line, 3, NONE)
      val input = getRest 3 [firstline]
      val raw_output = compiler obuf (lnumdie (linenum lbuf)) (mkLex (quote input))
    in
      ("", SOME (transformOutput umap ws raw_output))
    end
  else if String.isPrefix ">>__" line then
    let
      val firstline = String.extract(line, 4, NONE)
      val input = getRest 4 [firstline]
      val _ = compiler obuf (lnumdie (linenum lbuf)) (mkLex (quote input))
    in
      ("", NONE)
    end
  else if String.isPrefix ">>_" line then
    let
      val firstline = String.extract(line, 3, NONE)
      val input = getRest 3 [firstline]
      val _ = compiler obuf (lnumdie (linenum lbuf)) (mkLex (quote input))
      fun removeNL s = String.substring(s, 0, size s - 1)
    in
      (ws ^ ">" ^ removeNL (umunge umap input), SOME (!elision_string1))
    end
  else if String.isPrefix ">>+" line then
    let
      val firstline = String.extract(line, 3, NONE)
      val input = getRest 3 [firstline]
      fun handle_exn extra exn = raise Fail (extra ^ General.exnMessage exn)
      val raw_output = compiler obuf handle_exn (mkLex (quote input))
                       handle Fail s => "Exception- " ^ s ^ " raised\n"
    in
      (ws ^ ">" ^ umunge umap input, SOME (transformOutput umap ws raw_output))
    end
  else if String.isPrefix ">>" line then
    let
      val _ = obRST()
      val firstline = String.extract(line, 2, NONE)
      val input = getRest 2 [firstline]
      val raw_output = compiler obuf (lnumdie (linenum lbuf)) (mkLex (quote input))
    in
      (ws ^ ">" ^ umunge umap input, SOME (transformOutput umap ws raw_output))
    end
  else
    (advance lbuf; (origline, NONE))
end

fun read_umap fname =
  let
    val instrm = TextIO.openIn fname handle _ => die ("Couldn't open "^fname)
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
