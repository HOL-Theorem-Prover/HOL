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
end =
struct

  datatype element =
    Paragraph of string
  | ItemList of string list
  | SourceReference of Source.t

  type t = {header: string, content: element list}

  type err = t
  exception Error of err

  infix 6 ^^

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
