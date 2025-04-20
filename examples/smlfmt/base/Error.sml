(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Error:
sig

  datatype element =
    Paragraph of string
  | ItemList of string list
  | SourceReference of Source.t

  type t = {header: string, content: element list}

  type err = t

  exception Error of err

  val lineError:
    {header: string, pos: Source.t, what: string, explain: string option}
    -> err

  (** Note: very important that the syntax highlighter given as argument
    * always succeeds. For example, see SyntaxHighlighter.fuzzyHighlight
    *)
  val show: {highlighter: (Source.t -> TerminalColorString.t) option}
            -> err
            -> TerminalColorString.t
end =
struct

  structure TCS = TerminalColorString
  (* structure TC = TerminalColors *)
  open Palette

  datatype element =
    Paragraph of string
  | ItemList of string list
  | SourceReference of Source.t

  type t = {header: string, content: element list}

  type err = t
  exception Error of err

  fun spaces n = TextFormat.repeatChar n #" "

  fun lcToStr {line, col} = (* "[line " ^ Int.toString line ^ ", col " ^ Int.toString col ^ "]" *)
    Int.toString line ^ "." ^ Int.toString col


  infix 6 ^^
  fun x ^^ y = TCS.append (x, y)
  fun $ x = TCS.fromString x

  fun showElement highlighter desiredWidth e =
    let
      val bullet = "-"
      val desiredWidth = Int.max (5, desiredWidth)
    in
      case e of
        Paragraph s => $(TextFormat.textWrap desiredWidth s)

      | ItemList lns =>
          let
            fun showLine ln =
              "  " ^ TextFormat.textWrap (desiredWidth - 4) (bullet ^ " " ^ ln)
          in
            TCS.concatWith ($ "\n") (List.map ($ o showLine) lns)
          end

      | SourceReference pos =>
          let
            val {line = lineNum, col = colStart} = Source.absoluteStart pos
            val {line = lineNum', col = colEnd} = Source.absoluteEnd pos
            val _ =
              if lineNum = lineNum' orelse colEnd = 1 then
                ()
              else
                raise Fail "ErrorReport.show: end of position past end of line"

            val startOffset = Source.absoluteStartOffset pos
            val stopOffset = Source.absoluteEndOffset pos
            val pointyLen = stopOffset - startOffset

            val line = Source.wholeLine pos lineNum

            val lineNumStr = Int.toString lineNum
            val marginSize = 1 + String.size lineNumStr

            val colOffset = colStart - 1

            val pathName = FilePath.toHostPath (Source.fileName pos)

            val numTabsBefore =
              List.length
                (List.filter (fn c => c = #"\t")
                   (String.explode (Source.toString
                      (Source.take line colOffset))))

            val line =
              case highlighter of
                NONE => $(Source.toString line)
              | SOME h => h line
            val line = TCS.translate (fn #"\t" => "  " | c => String.str c) line

            val filestyle =
              TCS.foreground lightblue (*o TCS.background lightgray*)
          in
            TCS.concatWith ($ "\n")
              [ TCS.bold (TCS.underline (filestyle ($pathName)))
              , filestyle ($(spaces marginSize ^ "| "))
              , filestyle ($(lineNumStr ^ " | ")) ^^ line
              , TCS.concat
                  [ filestyle ($(spaces marginSize ^ "| "))
                  , $(spaces (colOffset + numTabsBefore))
                  , TCS.bold (TCS.foreground brightred ($
                      (TextFormat.repeatChar pointyLen #"^")))
                  ]
              (* , spaces marginSize ^ "|" *)
              ]
          end
    end


  fun show {highlighter} {header, content} =
    let
      val desiredWidth = Int.min (Terminal.currentCols (), 80)

      val headerStr = TextFormat.rightPadWith #"-" desiredWidth
        ("-- " ^ header ^ " ")
    in
      TCS.bold (TCS.foreground brightred ($headerStr)) ^^ $ "\n\n"
      ^^
      TCS.concatWith ($ "\n\n")
        (List.map (showElement highlighter desiredWidth) content) ^^ $ "\n"
    end


  fun lineError {header, pos, what, explain} =
    let
      val elems = [Paragraph what, SourceReference pos]

      val more =
        case explain of
          NONE => []
        | SOME s => [Paragraph s]
    in
      {header = header, content = elems @ more}
    end

end
