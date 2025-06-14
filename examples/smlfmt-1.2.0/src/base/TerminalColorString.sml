(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure TerminalColorString :>
sig
  type t
  type color = TerminalColors.color

  val fromChar: char -> t
  val fromString: string -> t
  val toString: {colors: bool} -> t -> string

  val size: t -> int
  val empty: t
  val append: t * t -> t
  val concat: t list -> t
  val concatWith: t -> t list -> t
  val substring: t * int * int -> t
  val translate: (char -> string) -> t -> t

  (** Returns how much effective whitespace was removed. Effective whitespace
    * for a tab is typically larger than 1, as indicated in the argument. All
    * other characters are effective space 1.
    *)
  val stripEffectiveWhitespace: {tabWidth: int, removeAtMost: int}
                                -> t
                                -> int * t

  val foreground: color -> t -> t
  val background: color -> t -> t
  val backgroundIfNone: color -> t -> t
  val bold: t -> t
  val italic: t -> t
  val underline: t -> t
  val clear: t -> t

  (** prints with colors if stdout is a terminal,
    * and without colors otherwise *)
  val print: t -> unit
  val printErr: t -> unit

  val debugShow: t -> string
end =
struct

  structure TC = TerminalColors

  type color = TC.color

  type attributes =
    { foreground: color option
    , background: color option
    , bold: bool
    , italic: bool
    , underline: bool
    }

  datatype t =
    Append of {size: int, left: t, right: t}
  | Attributes of {size: int, attr: attributes, child: t}
  | String of string
  | Empty

  fun size t =
    case t of
      Append {size = n, ...} => n
    | Attributes {size = n, ...} => n
    | String s => String.size s
    | Empty => 0

  val empty = Empty

  fun fromChar c =
    String (String.str c)
  fun fromString s = String s

  fun append (t1, t2) =
    case (t1, t2) of
      (Empty, _) => t2
    | (_, Empty) => t1
    | _ => Append {size = size t1 + size t2, left = t1, right = t2}

  fun concat ts =
    List.foldl (fn (next, prev) => append (prev, next)) Empty ts

  fun concatWith t ts =
    case ts of
      [] => empty
    | first :: rest =>
        List.foldl (fn (next, prev) => concat [prev, t, next]) first rest

  fun stripEffectiveWhitespace {tabWidth, removeAtMost = n} t =
    if n <= 0 then
      (0, t)
    else
      case t of
        Empty => (0, Empty)

      | Attributes {attr, child, ...} =>
          let
            val (count, child') =
              stripEffectiveWhitespace {tabWidth = tabWidth, removeAtMost = n}
                child
          in
            ( count
            , Attributes {size = size child', attr = attr, child = child'}
            )
          end

      | Append {left, right, ...} =>
          let
            val (count, left') =
              stripEffectiveWhitespace {tabWidth = tabWidth, removeAtMost = n}
                left
          in
            if size left' > 0 then
              (count, append (left', right))
            else
              let
                val remaining = n - count
                val (count', right') =
                  stripEffectiveWhitespace
                    {tabWidth = tabWidth, removeAtMost = remaining} right
              in
                (count + count', right')
              end
          end

      | String s =>
          let
            val {result, removed} =
              StripEffectiveWhitespace.strip
                {tabWidth = tabWidth, removeAtMost = n} s
          in
            (removed, String result)
          end

  fun substring (t, i, n) =
    if i < 0 orelse n < 0 orelse size t < i + n then
      raise Subscript
    else
      let
        fun cut (t, i, n) =
          case t of
            Empty => Empty
          | String s => String (String.substring (s, i, n))
          | Attributes {size = _, attr, child} =>
              Attributes {size = n, attr = attr, child = cut (child, i, n)}
          | Append {left, right, ...} =>
              if i < size left andalso i + n <= size left then
                cut (left, i, n)
              else if i >= size left then
                cut (right, i - size left, n)
              else
                append (cut (left, i, size left - i), cut
                  (right, 0, i + n - size left))
      in
        cut (t, i, n)
      end

  val default =
    { foreground = NONE
    , background = NONE
    , bold = false
    , italic = false
    , underline = false
    }

  fun setForeground (a: attributes) color =
    { foreground = SOME color
    , background = #background a
    , bold = #bold a
    , italic = #italic a
    , underline = #underline a
    }

  fun setBackground (a: attributes) color =
    { foreground = #foreground a
    , background = SOME color
    , bold = #bold a
    , italic = #italic a
    , underline = #underline a
    }

  fun setBold (a: attributes) =
    { foreground = #foreground a
    , background = #background a
    , bold = true
    , italic = #italic a
    , underline = #underline a
    }

  fun setItalic (a: attributes) =
    { foreground = #foreground a
    , background = #background a
    , bold = #bold a
    , italic = true
    , underline = #underline a
    }

  fun setUnderline (a: attributes) =
    { foreground = #foreground a
    , background = #background a
    , bold = #bold a
    , italic = #italic a
    , underline = true
    }

  fun mergeOpt xo yo =
    case yo of
      SOME _ => yo
    | NONE => xo

  fun mergeAttributes (a1: attributes) (a2: attributes) =
    { foreground = mergeOpt (#foreground a1) (#foreground a2)
    , background = mergeOpt (#background a1) (#background a2)
    , bold = #bold a1 orelse #bold a2
    , italic = #italic a1 orelse #italic a2
    , underline = #underline a1 orelse #underline a2
    }

  fun splitAttributes t =
    case t of
      Attributes {attr = a, child, ...} => (a, child)
    | _ => (default, t)

  fun hasNoBackground t =
    case t of
      Append {left, right, ...} =>
        hasNoBackground left andalso hasNoBackground right
    | Attributes {attr, child, ...} =>
        not (Option.isSome (#background attr)) andalso hasNoBackground child
    | _ => true

  fun foreground color t =
    let val (a, t) = splitAttributes t
    in Attributes {size = size t, attr = setForeground a color, child = t}
    end

  fun background color t =
    let val (a, t) = splitAttributes t
    in Attributes {size = size t, attr = setBackground a color, child = t}
    end

  fun backgroundIfNone color t =
    if hasNoBackground t then background color t else t

  fun bold t =
    let val (a, t) = splitAttributes t
    in Attributes {size = size t, attr = setBold a, child = t}
    end

  fun italic t =
    let val (a, t) = splitAttributes t
    in Attributes {size = size t, attr = setItalic a, child = t}
    end

  fun underline t =
    let val (a, t) = splitAttributes t
    in Attributes {size = size t, attr = setUnderline a, child = t}
    end

  fun clear t =
    case t of
      Append {size, left, right} =>
        Append {size = size, left = clear left, right = clear right}
    | Attributes {child, ...} => child
    | _ => t

  fun translate f t =
    case t of
      Empty => Empty
    | String s => String (String.translate f s)
    | Append {left, right, ...} => append (translate f left, translate f right)
    | Attributes {attr, child, ...} =>
        let val c = translate f child
        in Attributes {attr = attr, child = c, size = size c}
        end

  fun toString {colors} t =
    let
      fun traverse attr acc t =
        case t of
          Append {left, right, ...} =>
            traverse attr (traverse attr acc left) right
        | Attributes {attr = attr', child, ...} =>
            traverse (mergeAttributes attr attr') acc child
        | Empty => acc
        | String s =>
            if not colors then
              s :: acc
            else
              let
                val acc =
                  case #foreground attr of
                    NONE => acc
                  | SOME c => TC.foreground c :: acc
                val acc =
                  case #background attr of
                    NONE => acc
                  | SOME c => TC.background c :: acc
                val acc = if #bold attr then TC.bold :: acc else acc
                val acc = if #underline attr then TC.underline :: acc else acc
                val acc = if #italic attr then TC.italic :: acc else acc
              in
                TC.reset :: s :: acc
              end

    in
      String.concat (List.rev (traverse default [] t))
    end

  fun debugShow t =
    case t of
      Append {left, right, ...} =>
        "Append(" ^ debugShow left ^ "," ^ debugShow right ^ ")"
    | Attributes {child, ...} => "(" ^ debugShow child ^ ")"
    | Empty => ""
    | String s => s


  datatype out = stdout | stderr

  fun print_ out t =
    let
      val (printer, filedesc) =
        case out of
          stdout => (print, Posix.FileSys.stdout)
        | _ => (fn x => TextIO.output (TextIO.stdErr, x), Posix.FileSys.stderr)

      val kind = OS.IO.kind (Posix.FileSys.fdToIOD filedesc)
    in
      if kind = OS.IO.Kind.tty then printer (toString {colors = true} t)
      else printer (toString {colors = false} t)
    end

  val print = print_ stdout
  val printErr = print_ stderr

end
