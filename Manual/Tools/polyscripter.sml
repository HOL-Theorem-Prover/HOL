val _ = use "../../tools-poly/prelude.ML";
val _ = use "../../tools-poly/prelude2.ML";
val _ = PolyML.print_depth 0;

fun exnMessage (e:exn) =
  let
    fun p (e:exn) = PolyML.prettyRepresentation (e, 10000)
  in
    PP.pp_to_string 75 p e
  end

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun lnumdie linenum extra exn =
  die ("Exception raised on line " ^ Int.toString linenum ^ ": "^
       extra ^ exnMessage exn)

val outputPrompt = ref "> "

val quote = HolParser.fromString
val default_linewidth = 77

fun quoteFile lnum fname =
  HolParser.inputFile fname handle e => lnumdie lnum "" e

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

fun compiler {push = obufPush, read = obufRD, reset = obufRST} handler infn =
  let
    fun pushback c infn =
        let val used = ref false
        in
          fn () => if !used then infn() else (used := true; SOME c)
        end
    fun record_error {message,...} = PolyML.prettyPrint(obufPush,70) message
    fun rpt infn acc =
      (obufRST();
       PolyML.compiler(infn,
                       [PolyML.Compiler.CPErrorMessageProc record_error,
                        PolyML.Compiler.CPOutStream obufPush]) ()
       handle e => handler (obufRD()) e;
       case infn() of
           NONE => String.concat (List.rev (obufRD() :: acc))
         | SOME c => rpt (pushback c infn) (obufRD() :: acc)
      )
  in
    rpt infn []
  end

fun silentUse lnum s =
  let
    val filecontents = quoteFile lnum s
    val buf = HM_SimpleBuffer.mkBuffer()
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
      ("\n   : proofs\n", "\n"),
      ("\n   : proof\n", "\n"),
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

fun delete_suffixNL sfx s =
  if String.isSuffix (sfx ^ "\n") s then
    String.extract(s, 0, SOME (size s - (size sfx + 1))) ^ "\n"
        |> deleteTrailingWhiteSpace
  else s

fun remove_colonthm s =
  s |> delete_suffixNL "thm" |> delete_suffixNL ":"

fun shorten_longmetis s =
  let
    open Substring
    val ss = full s
    val (pfx, sfx) = position "\nmetis: " ss
    fun ismetis_guff c =
      case c of
          #"r" => true | #"+" => true | #"[" => true | #"]" => true
        | _ => Char.isDigit c
    fun recurse csfx =
      if size csfx <> 0 then
        let
          val (guff, rest) = splitl ismetis_guff (triml 8 csfx)
        in
          if size guff > 55 then
            SOME (string (span (pfx, slice(guff, 0, SOME 50))) ^ " .... " ^
                  string rest)
          else
            let
              val (_, sfx') = position "\nmetis: " (triml 1 csfx)
            in
              recurse sfx'
            end
        end
      else NONE
  in
    recurse sfx
  end

fun removeCruft s =
  try removeCruft [cruftSuffix (!cruftySuffixes),
                   remove_multi_goalproved,
                   shorten_longmetis,
                   remove_nsubgoals]
      s

fun addIndent ws = String.translate(fn #"\n" => "\n"^ws | c => str c)

val linelen_limit = ref (NONE : int option)

fun trunc lim s =
    if UTF8.size s <= lim then s
    else if lim > 3 then UTF8.substring(s,0, lim - 3) ^ "..."
    else UTF8.substring(s,0,lim)

fun impose_linelen_limit s =
    case !linelen_limit of
        NONE => s
      | SOME lim =>
        let
          val lines = String.fields (fn c => c = #"\n") s
        in
          String.concatWith "\n" (map (trunc lim) lines)
        end

fun transformOutput umap ws s =
  s |> umunge umap
    |> removeCruft
    |> addIndent ws
    |> deleteTrailingWhiteSpace
    |> (fn s => ws ^ s)
    |> impose_linelen_limit

fun spaceNotNL c = Char.isSpace c andalso c <> #"\n"

val getIndent =
  (Substring.string ## Substring.string)
    o Substring.splitl spaceNotNL o Substring.full

fun dropLWS s =
  s |> Substring.full |> Substring.dropl Char.isSpace |> Substring.string

fun strip_for_thm s =
  let
    val s0 = if String.isPrefix "val it =" s then
               String.extract(s, 9, NONE) |> dropLWS
             else s
  in
    remove_colonthm s0
  end

fun tailmap f [] = []
  | tailmap f (h::t) = h :: map f t

fun poss_space_extract n s =
    let val s = String.extract(s,n,NONE)
    in
      if s <> "" andalso String.sub(s,0) = #" " then
        (String.extract(s, 1, NONE), n + 1)
      else (s, n)
    end

fun strcat s1 s2 = s1 ^ s2

fun dropWhile0 P a [] = (List.rev a,[])
  | dropWhile0 P a (l as h::t) = if P h then dropWhile0 P (h::a) t
                                 else (List.rev a, l)
fun dropWhile P l = dropWhile0 P [] l

fun process_line debugp umap obuf origline lbuf = let
  val {reset = obRST, ...} = obuf
  val (ws,line) = getIndent origline
  val indent = String.size ws
  val oPsize = size (!outputPrompt)
  val oPws = CharVector.tabulate(oPsize, fn _ => #" ")
  fun getRest userPromptSize acc =
    let
      val _ = advance lbuf
      (* know that we're being called on something with > indent many space
         characters at the start of the line; that number is wssz *)
      fun handlePromptSize wssz line =
          (* strip indent many characters from line first *)
          let
            val line = String.extract(line, indent, NONE)
            val remws = wssz - indent
            val tostrip = Int.min(remws, userPromptSize)
          in
            String.extract(line, tostrip, NONE)
          end
      fun extract_trailing_blanklines l =
          let
            val (blanks, rest) = dropWhile (CharVector.all Char.isSpace) l
          in
            (List.rev rest, blanks |> List.rev |> String.concat)
          end
    in
      case current lbuf of
          NONE => extract_trailing_blanklines acc
        | SOME s =>
          let
            val (ws',_) = getIndent s
            val wssz = String.size ws'
          in
            if indent < wssz then
              getRest userPromptSize (handlePromptSize wssz s::acc)
            else if CharVector.all Char.isSpace s then
              getRest userPromptSize ("\n" :: acc)
            else extract_trailing_blanklines acc
          end
    end
  val assertcmd = "##assert "
  val assertcmdsz = size assertcmd
  val stringCReader = #read o HolParser.stringToReader true
  fun compile exnhandle input =
      (if debugp then
         TextIO.output(TextIO.stdErr, input)
       else ();
       compiler obuf exnhandle (stringCReader input))
in
  if String.isPrefix ">>>" line then
    (advance lbuf; (ws ^ String.extract(line, 1, NONE), ""))
  else if String.isPrefix "###" line then
    (advance lbuf; (ws ^ String.extract(line, 1, NONE), ""))
  else if String.isPrefix assertcmd line then
    let
      val e = String.substring(line, assertcmdsz, size line - assertcmdsz - 1)
                              (* for \n at end *)
      val _ = compile (lnumdie (linenum lbuf))
                      ("val _ = if (" ^ e ^ ") then () " ^
                       "else die \"Assertion failed: line " ^
                       Int.toString (linenum lbuf) ^ "\";\n")
      val _ = advance lbuf
    in
      ("", "")
    end
  else if String.isPrefix "##thm" line then
    let
      val suffix = String.extract(line, 5, NONE)
      val ((guffp,guffs), thm_name) =
          if Char.isDigit (String.sub(suffix,0)) then
            let
              val (w,nm) =
                  case String.tokens Char.isSpace suffix of
                      [ds,nm] => ((valOf (Int.fromString ds), nm)
                                  handle Option =>
                                         lnumdie (linenum lbuf)
                                                 "Bad integer for linewidth"
                                                 Option)
                    | _ => lnumdie (linenum lbuf)
                                   "Malformed ##thm line"
                                   (Fail "")
            in
              (("val _ = linewidth := " ^ Int.toString w ^"; ",
                "val _ = linewidth := " ^ Int.toString default_linewidth ^ ";"),
               nm ^ "\n")
            end
          else (("",""), dropLWS suffix)
      val raw_output =
          compile (lnumdie (linenum lbuf))
                  (guffp ^ thm_name ^ " :Thm.thm;" ^ guffs)
      val output = transformOutput umap ws (strip_for_thm raw_output)
                        |> deleteTrailingWhiteSpace
                        |> (fn s => "  " ^ s)
      val _ = advance lbuf
    in
      (ws ^ umunge umap thm_name, output)
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
              handle Subscript =>
                     lnumdie (linenum lbuf) "Mal-formed ##eval directive" e
      val (input, blankstr) = getRest indent [firstline]
      val input = input |> map (fn s => ws ^ s) |> String.concat
      val _ = compile (lnumdie (linenum lbuf)) (inputpfx ^ input)
    in
      (umunge umap input, blankstr)
    end
  else if String.isPrefix "##parse" line then
    let
      val line = String.extract(line, 7, NONE)
      val pfx =
          if String.isPrefix "tm " line then ""
          else if String.isPrefix "ty " line then ":"
          else lnumdie (linenum lbuf) "Mal-formed ##parse directive" (Fail "")
      val (firstline, indent) = (String.extract(line, 3, NONE), 10)
      val (input, blankstr) = getRest indent [firstline]
      val input = input |> map (fn s => ws ^ s) |> String.concat
      val _ = compile (lnumdie (linenum lbuf)) ("``" ^ pfx ^ input ^ "``")
    in
      (umunge umap input, blankstr)
    end
  else if String.isPrefix "##use " line then
    let
      val fname = String.substring(line, 6, size line - 7) (* for \n at end *)
      val _ = silentUse (linenum lbuf) fname
      val _ = advance lbuf
    in
      ("", "")
    end
  else if String.isPrefix "##linelen_limit " line then
    case Int.fromString (String.extract(line, 16, NONE)) of
        NONE => lnumdie (linenum lbuf) "Mal-formed ##linelen_limit directive"
                        (Fail "")
      | SOME i => if i >= 10 then
                    (advance lbuf; linelen_limit := SOME i; ("", ""))
                  else
                    lnumdie (linenum lbuf)
                            "Unreasonable (<10) ##linelen_limit directive"
                            (Fail "")
  else if String.isPrefix "##nolinelen_limit" line then
    (advance lbuf; linelen_limit := NONE; ("", ""))
  else if String.isPrefix ">>-" line then
    let
      val (firstline,d) = poss_space_extract 3 line
      val (input, blankstr) = getRest d [firstline]
      val raw_output = compile (lnumdie (linenum lbuf)) (String.concat input)
    in
      ("", transformOutput umap ws raw_output ^ blankstr)
    end
  else if String.isPrefix ">>__" line then
    let
      val (firstline,d) = poss_space_extract 4 line
      val (input, blankstr) = getRest d [firstline]
      val _ = compile (lnumdie (linenum lbuf)) (String.concat input)
    in
      ("", blankstr)
    end
  else if String.isPrefix ">>_" line then
    let
      val (firstline,d) = poss_space_extract 3 line
      val (input, blankstr) = getRest d [firstline]
      val inp_to_print = input |> tailmap (strcat (oPws ^ ws)) |> String.concat
      val _ = compile (lnumdie (linenum lbuf)) (String.concat input)
      fun removeNL s = String.substring(s, 0, size s - 1)
    in
      (ws ^ !outputPrompt ^ removeNL (umunge umap inp_to_print),
       !elision_string1 ^ blankstr)
    end
  else if String.isPrefix ">>+" line then
    let
      val (firstline,d) = poss_space_extract 3 line
      val (input,blankstr) = getRest d [firstline]
      val inp_to_print = input |> tailmap (strcat (oPws ^ ws)) |> String.concat
      fun handle_exn extra exn = raise Fail (extra ^ exnMessage exn)
      val raw_output = compile handle_exn (String.concat input)
                       handle Fail s => "Exception- " ^ s ^ " raised\n"
    in
      (ws ^ !outputPrompt ^ umunge umap inp_to_print,
       transformOutput umap ws raw_output ^ blankstr)
    end
  else if String.isPrefix ">>" line then
    let
      val _ = obRST()
      val (firstline, d) = poss_space_extract 2 line
      val (input,blankstr) = getRest d [firstline]
      val inp_to_print = input |> tailmap (strcat (oPws ^ ws)) |> String.concat
      val raw_output = compile (lnumdie (linenum lbuf)) (String.concat input)
    in
      (ws ^ !outputPrompt ^ umunge umap inp_to_print,
       transformOutput umap ws raw_output ^ blankstr)
    end
  else
    (advance lbuf; (origline, ""))
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
  "Usage:\n  "^ CommandLine.name() ^ " [-d] [umapfile]"

fun main () =
  let
    val _ = PolyML.print_depth 100;
    val _ = Parse.current_backend := PPBackEnd.raw_terminal
    val (debugp,umap) =
        case CommandLine.arguments() of
            [] => (false, Binarymap.mkDict String.compare)
          | ["-d"] => (true, Binarymap.mkDict String.compare)
          | [name] => (false, read_umap name)
          | ["-d", name] => (true, read_umap name)
          | _ => die (usage())
    val (obuf as {push = obPush, ...}) = HM_SimpleBuffer.mkBuffer()
    val _ = ReadHMF.extend_path_with_includes {verbosity = 0, lpref = loadPath}
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
            val (i, output) = process_line debugp umap obuf line lb
               handle e => die ("Untrapped exception: line "^
                                Int.toString (linenum lb) ^ ": " ^
                                exnMessage e)
          in
            print (i ^ output);
            recurse lb
          end
  in
    recurse lb
  end
