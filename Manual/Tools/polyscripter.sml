val _ = use "../../tools-poly/prelude.ML";
val _ = use "../../tools-poly/prelude2.ML";
val _ = PolyML.print_depth 0;

fun exnMessage (e:exn) =
  let
    fun p (e:exn) = PolyML.prettyRepresentation (e, 10000)
  in
    PP.pp_to_string 75 p e
  end

(* External drivers (e.g. help/src-sml/process_docfiles) that loop
   over many .smd inputs can set this to the current entry's name
   so that die-style diagnostics name the source.  Default empty
   keeps stand-alone CLI output unchanged. *)
val currentSource : string ref = ref ""

fun die s =
  let val pfx = case !currentSource of "" => "" | s => "[" ^ s ^ "] "
  in
    TextIO.output(TextIO.stdErr, pfx ^ s ^ "\n");
    OS.Process.exit OS.Process.failure
  end
fun lnumdie linenum extra exn =
  die ("Exception raised on line " ^ Int.toString linenum ^ ": "^
       extra ^ "\n" ^ exnMessage exn)

val outputPrompt = ref "> "

(* Global outstream for user scripts.  In CLI mode this points at
   `print` (so user output goes to stdout, joining polyscripter's own
   emission); when polyscripter is driven as a library (e.g., from the
   smdpp mdbook preprocessor), processStream rebinds it to the
   caller-supplied `output` callback so that user-script writes land
   in the same captured stream as polyscripter's emission. *)
val scriptPrint : (string -> unit) ref = ref print

(* HOLSource (the unquote pre-processor) reports parse errors --
   unclosed quotations, stray punctuation, etc. -- by calling
   `args.print`.  Track whether any such report happened during the
   current chunk so external drivers (e.g. help/src-sml/process_docfiles)
   that loop over many .smd inputs can detect a malformed `>>` block
   even when the exception-tolerant `>>+` would otherwise swallow
   the resulting Fail "Static Errors".  CLI behaviour is unchanged
   -- the stderr output still happens; we just also raise a flag. *)
val parseErrorFlag = ref false
fun resetParseError () = parseErrorFlag := false
fun hadParseError () = !parseErrorFlag

val args =
    {quietOpen = true,
     print = fn s => (parseErrorFlag := true;
                      TextIO.output(TextIO.stdErr, s))}
val quote = HOLSource.fromString args
val default_linewidth = 77

fun quoteFile lnum fname =
  HOLSource.inputFile args fname handle e => lnumdie lnum "" e

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
    val buf = SimpleBuffer.mkBuffer()
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

(* Plain-text alternative used when -md is passed.  The LaTeX form
   above relied on the surrounding alltt environment to interpret
   \textit etc.; .smd output ends up inside a fenced code block, which
   pandoc lowers to verbatim, so the LaTeX would leak through as
   literal characters. *)
val elision_string1_plain =
    "   ... output elided ...\n"

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
        val (_,r) = Substring.position "\n\nGoal proved." ss'
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

type 'a refstack = 'a list ref
fun rsPushValue a (r as ref v) = r := a::v
fun rsValue (ref v) = hd v
fun rsPop (ref [_]) = ()
  | rsPop (r as ref (_::xs)) = r := xs
  | rsPop (ref []) = raise Fail "rsPop: can't happen"
fun newRS v = ref [v]

val linelen_limit = newRS (NONE : int option)
val linecount_limit = newRS (0, NONE) : (int*int option) refstack

fun trunc lim s =
    if UTF8.size s <= lim then s
    else if lim > 3 then UTF8.substring(s,0, lim - 3) ^ "..."
    else UTF8.substring(s,0,lim)

fun impose_linelen_limit s =
    case rsValue linelen_limit of
        NONE => s
      | SOME lim =>
        let
          val lines = String.fields (fn c => c = #"\n") s
        in
          String.concatWith "\n" (map (trunc lim) lines)
        end

fun impose_linecount_limit s =
    case rsValue linecount_limit of
        (0,NONE) => s
      | (dropc, NONE) =>
        let
          val lines = String.fields (fn c => c = #"\n") s
          val c = length lines
        in
          if dropc >= c then "[...No output after prefix elided...]\n"
          else
            "[...Lines elided...]\n" ^
            String.concatWith "\n" (List.drop (lines, dropc)) ^ "\n"
        end
      | (0, SOME lim) =>
        let
          val lines = String.fields (fn c => c = #"\n") s
          val c = length lines
          val (lines', closeWith) =
              case Int.compare(lim,c) of
                  LESS => (List.take(lines, lim), "\n[...Output elided...]\n")
                | _ => (lines, "\n")
        in
          String.concatWith "\n" lines' ^ closeWith
        end
      | (dropc, SOME takec) =>
        let
          val lines = String.fields (fn c => c = #"\n") s
          val dr = List.drop and tk = List.take
          val c = length lines
        in
          if c <= dropc then
            "[...No output after prefix elided...]\n"
          else if dropc + takec >= c then
            "[...Lines elided...]\n" ^
            String.concatWith "\n" (dr (lines, dropc)) ^ "\n"
          else
            "[...Lines elided...]\n" ^
            String.concatWith "\n" (tk (dr (lines,dropc), takec)) ^
            "\n[...Output elided...]\n"
        end

fun transformOutput umap ws s =
  s |> umunge umap
    |> removeCruft
    |> addIndent ws
    |> deleteTrailingWhiteSpace
    |> (fn s => ws ^ s)
    |> impose_linelen_limit
    |> impose_linecount_limit

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

fun tailmap _ [] = []
  | tailmap f (h::t) = h :: map f t

fun poss_space_extract n s =
    let val s = String.extract(s,n,NONE)
    in
      if s <> "" andalso String.sub(s,0) = #" " then
        (String.extract(s, 1, NONE), n + 1)
      else (s, n)
    end

fun strcat s1 s2 = s1 ^ s2

fun dropWhile0 _ a [] = (List.rev a,[])
  | dropWhile0 P a (l as h::t) = if P h then dropWhile0 P (h::a) t
                                 else (List.rev a, l)
fun dropWhile P l = dropWhile0 P [] l

datatype cstate = Consuming | Skipping

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
  val stringCReader = #read o HOLSource.stringToReader args
  fun compile exnhandle input =
      (if debugp then
         TextIO.output(TextIO.stdErr, input)
       else ();
       compiler obuf exnhandle (stringCReader input))
in
  if String.isPrefix ">>>" line then
    (advance lbuf; (ws ^ String.extract(line, 1, NONE), ""))
  else if String.isPrefix "###" line then
    let val toks = String.tokens Char.isSpace line
    in
      advance lbuf;
      case (ws, toks) of
          ("", tok1 :: _) =>
          if CharVector.all (fn c => c = #"#") tok1 then
            (line, "")
          else (ws ^ String.extract(line, 1, NONE), "")
        | _ => (ws ^ String.extract(line, 1, NONE), "")
    end
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
                    (advance lbuf; rsPushValue (SOME i) linelen_limit; ("", ""))
                  else
                    lnumdie (linenum lbuf)
                            "Unreasonable (<10) ##linelen_limit directive"
                            (Fail "")
  else if String.isPrefix "##nolinelen_limit" line then
    (advance lbuf; rsPushValue NONE linelen_limit; ("", ""))
  else if String.isPrefix "##poplinelen_limit" line then
    (advance lbuf; rsPop linelen_limit; ("", ""))
  else if String.isPrefix "##linecount_limit " line then
    case tl (String.tokens Char.isSpace line) of
        [dr] => (case Int.fromString dr of
                     NONE => lnumdie
                               (linenum lbuf)
                               ("Mal-formed ##linecount_limit directive: \""^
                                dr ^ "\" not a valid integer")
                               (Fail "")
                   | SOME dri => (rsPushValue (dri,NONE) linecount_limit;
                                  advance lbuf;
                                  ("", "")))
      | [dr,tk] =>
        let
          val dri =
              case Int.fromString dr of
                  NONE => lnumdie (linenum lbuf)
                                  ("Mal-formed ##linecount_limit directive: \""^
                                   dr ^ "\" not a valid integer")
                                  (Fail "")
                      | SOME i => i
          val tkopt =
              if tk = "_" then NONE
              else
                case Int.fromString tk of
                    NONE => lnumdie
                              (linenum lbuf)
                              ("Mal-formed ##linecount_limit directive: \"" ^
                               tk ^ "\" not a valid integer or \"_\"")
                              (Fail "")
                  | SOME i => SOME i
        in
          (advance lbuf; rsPushValue (dri,tkopt) linecount_limit; ("", ""))
        end
      | _ => lnumdie (linenum lbuf) "Mal-formed ##linecount_limit directive"
                     (Fail "")
  else if String.isPrefix "##poplinecount_limit" line then
    (advance lbuf; rsPop linecount_limit; ("", ""))
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
  "Usage:\n  "^ CommandLine.name() ^ " [-d] [-md] [umapfile]"

(* One-time setup shared between the CLI driver and external callers
   (e.g., the smdpp mdbook preprocessor).  Returns the compiler output
   buffer used by process_line. *)
fun setupPolyscripter () =
  let
    val _ = PolyML.print_depth 100
    val _ = Parse.current_backend := PPBackEnd.raw_terminal
    val (obuf as {push = obPush, ...}) = SimpleBuffer.mkBuffer()
    val _ = ReadHMF.extend_path_with_includes {verbosity = 0, lpref = loadPath}
    val _ = Feedback.ERR_outstream := obPush
    val _ = Feedback.WARNING_outstream := obPush
    val _ = Feedback.MESG_outstream := obPush
    val _ = Feedback.INFO_outstream := obPush
  in
    obuf
  end

(* Drive a single .smd document.  `obuf` should be a buffer obtained from
   setupPolyscripter (and may be reused across documents to share Poly/ML
   compiler state and theory loads).  `scriptPrint` is rebound to
   `output` for the duration of the call so user-script writes land in
   the same stream as polyscripter's emission. *)
fun processStream {input, output, debug, umap, obuf} =
  let
    val savedScriptPrint = !scriptPrint
    val () = scriptPrint := output
    val lb = mklbuf input
    fun recurse cstate =
      case current lb of
          NONE => ()
        | SOME line =>
          if String.isPrefix "##skip" line then
            (advance lb; recurse (Skipping :: cstate))
          else if String.isPrefix "##endskip" line then
            (case cstate of
                Skipping :: rest => (advance lb; recurse rest)
              | _ => die ("Unbalanced ##endskip on line " ^
                          Int.toString (linenum lb)))
          else
            case cstate of
                Skipping :: _ => (advance lb; recurse cstate)
              | _ =>
                let
                  val (i, out) =
                      process_line debug umap obuf line lb
                      handle e => die ("Untrapped exception: line "^
                                       Int.toString (linenum lb) ^ ": " ^
                                       exnMessage e)
                in
                  output (i ^ out);
                  recurse cstate
                end
  in
    (recurse [] handle e => (scriptPrint := savedScriptPrint; raise e));
    scriptPrint := savedScriptPrint
  end

fun processString {input, debug, umap, obuf} =
  let
    val sb = SimpleBuffer.mkBuffer ()
  in
    processStream {input = TextIO.openString input,
                   output = #push sb,
                   debug = debug,
                   umap = umap,
                   obuf = obuf};
    #read sb ()
  end

fun main () =
  let
    fun parseArgs (mdp, debugp, umap) args =
        case args of
            [] => (mdp, debugp, umap)
          | "-md" :: rest => parseArgs (true, debugp, umap) rest
          | "-d"  :: rest => parseArgs (mdp, true, umap) rest
          | [name] => (mdp, debugp, read_umap name)
          | _ => die (usage())
    val (mdp, debugp, umap) =
        parseArgs (false, false, Binarymap.mkDict String.compare)
                  (CommandLine.arguments())
    val () = if mdp then elision_string1 := elision_string1_plain else ()
    val obuf = setupPolyscripter ()
    val cvn = PolyML.Compiler.compilerVersionNumber
    val _ = if cvn = 551 orelse cvn = 552 then
              ignore (TextIO.inputLine TextIO.stdIn)
            else ()
  in
    processStream {input = TextIO.stdIn,
                   output = print,
                   debug = debugp,
                   umap = umap,
                   obuf = obuf}
  end
