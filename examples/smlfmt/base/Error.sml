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

  val toString: t -> string
end =
struct

  datatype element =
    Paragraph of string
  | ItemList of string list
  | SourceReference of Source.t

  type t = {header: string, content: element list}

  type err = t
  exception Error of err

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

  fun elementToString (el: element) =
    case el of
      Paragraph s => s
    | ItemList ss =>
      let val items = String.concatWith ", " ss
      in String.concat ["[", items, "]"] end
    | SourceReference src =>
      let
        val {line, col} = Source.absoluteStart src
        val startStr =
          String.concat ["(", Int.toString line, ", ", Int.toString col, ")"]

        val {line, col} = Source.absoluteEnd src
        val endStr =
          String.concat ["(", Int.toString line, ", ", Int.toString col, ")"]

        val srcStr = String.concat ["> ", Source.toString src, " <"]
      in
        String.concat [startStr, " - ", endStr, ": ", srcStr]
      end

  fun toString ({header, content} : t) =
    let val elements = String.concatWith "\n" (List.map elementToString content)
    in String.concat [header, "\n", elements] end
end
