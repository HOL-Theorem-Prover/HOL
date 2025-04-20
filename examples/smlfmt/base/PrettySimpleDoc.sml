(** Copyright (c) 2020 Sam Westrick
  *
  * See the file LICENSE for details.
  *)


(** Functor argument CustomString could either be a standard string, or could
  * be a TerminalColorString, etc.
  *)
functor PrettySimpleDoc
  (CustomString:
   sig
     type t
     val fromString: string -> t
     val size: t -> int
     val concat: t list -> t
   end) :>
sig
  type doc
  type t = doc

  val empty: doc
  val text: CustomString.t -> doc

  val beside: doc * doc -> doc

  (** Align a doc so that it wraps back to the same indentation as the
    * first doc:
    *
    *      d1       d2           besideAndAbove (d1, d2)
    *    .......   ****             .......
    *    .......   ***    ====>     .......
    *    .....                      .....****
    *                               ***
    *
    * The first version gets replaced by a space when undone by group. The
    * second is put exactly beside.
    *)
  val besideAndAboveOrSpace: doc * doc -> doc
  val besideAndAbove: doc * doc -> doc

  (** When an "above" is flattened by a group, it can either be replaced by a
    * a space, or it can be put exactly beside (with no extra space).
    *)
  val aboveOrSpace: doc * doc -> doc
  val aboveOrBeside: doc * doc -> doc

  val indent: doc -> doc

  val space: doc
  val softspace: doc
  val group: doc -> doc
  val rigid: doc -> doc

  val pretty: {ribbonFrac: real, maxWidth: int, indentWidth: int}
              -> doc
              -> CustomString.t

  val toString: doc -> CustomString.t
end =
struct

  (** for Space, Above, and BesideAndAbove, the boolean indicates whether or
    * not to keep space when undone by group.
    *)
  datatype doc =
    Empty
  | Space of bool
  | Indent of doc
  | Text of CustomString.t
  | Beside of doc * doc
  | BesideAndAbove of bool * doc * doc
  | Above of bool * doc * doc
  | Choice of {flattened: flattened, normal: doc}
  | Rigid of doc
  withtype flattened = bool * doc * int * bool


  type t = doc


  val empty = Empty
  val space = Space true
  val softspace = Space false
  val text = Text


  fun beside (doc1, doc2) =
    case (doc1, doc2) of
      (Empty, _) => doc2
    | (_, Empty) => doc1
    | _ => Beside (doc1, doc2)


  fun above' withSpace (doc1, doc2) =
    case (doc1, doc2) of
      (Empty, _) => doc2
    | (_, Empty) => doc1
    | _ => Above (withSpace, doc1, doc2)

  fun besideAndAbove' withSpace (doc1, doc2) =
    case (doc1, doc2) of
      (Empty, _) => doc2
    | (_, Empty) => doc1
    | _ => BesideAndAbove (withSpace, doc1, doc2)

  val besideAndAboveOrSpace = besideAndAbove' true
  val besideAndAbove = besideAndAbove' false

  val aboveOrSpace = above' true
  val aboveOrBeside = above' false

  val indent = Indent

  fun flatten (doc: doc) : flattened option =
    let
      (** Returns (space-before?, flattened, flattened size, space-after?) *)
      fun loop (doc: doc) : flattened option =
        case doc of
          Empty => SOME (false, Empty, 0, false)
        | Space keepSpace => SOME (keepSpace, Empty, 0, keepSpace)
        | Indent d => loop d
        | Text str => SOME (false, Text str, CustomString.size str, false)
        | Beside (d1, d2) => loopBeside (d1, d2)
        | BesideAndAbove (withSpace, d1, d2) =>
            if withSpace then loopBeside (d1, Beside (Space true, d2))
            else loopBeside (d1, d2)
        | Above (withSpace, d1, d2) =>
            if withSpace then loopBeside (d1, Beside (Space true, d2))
            else loopBeside (d1, d2)
        | Choice {flattened, ...} => SOME flattened
        | Rigid _ => NONE

      and loopBeside (d1, d2) =
        case (loop d1, loop d2) of
          (NONE, _) => NONE
        | (_, NONE) => NONE
        | (SOME (l1, flat1, sz1, r1), SOME (l2, flat2, sz2, r2)) =>
            let
              (** Beside(flat1, flat2), but put a space between if
                * necessary, and compute the size too. This might result in
                * spaces l or r on either side, if flat1 or flat2 is Empty
                *)
              val (l, m, sz, r) =
                case (flat1, r1 orelse l2, flat2) of
                  (Empty, b, _) => (b, flat2, sz2, false)
                | (_, b, Empty) => (false, flat1, sz1, b)
                | (_, false, _) =>
                    (false, Beside (flat1, flat2), sz1 + sz2, false)
                | _ =>
                    ( false
                    , Beside (flat1, Beside (Space true, flat2))
                    , sz1 + sz2 + 1
                    , false
                    )
            in
              SOME (l1 orelse l, m, sz, r2 orelse r)
            end

    in
      loop doc
    end


  fun group doc =
    case flatten doc of
      NONE => doc
    | SOME flattened => Choice {flattened = flattened, normal = doc}

  val rigid = Rigid


  fun spaces count =
    CustomString.fromString (CharVector.tabulate (count, fn _ => #" "))


  datatype item = Spaces of int | Newline | Stuff of CustomString.t


  fun revAndStripTrailingWhitespace (items: item list) =
    let
      fun loopStrip acc items =
        case items of
          [] => acc
        | Spaces _ :: items' => loopStrip acc items'
        | x :: items' => loopKeep (x :: acc) items'

      and loopKeep acc items =
        case items of
          [] => acc
        | Newline :: items' => loopStrip (Newline :: acc) items'
        | x :: items' => loopKeep (x :: acc) items'
    in
      loopStrip [] items
    end


  fun pretty {ribbonFrac, maxWidth, indentWidth} inputDoc =
    let
      val ribbonWidth = Int.max (0, Int.min (maxWidth, Real.round
        (ribbonFrac * Real.fromInt maxWidth)))

      datatype above_mode = UseCurrentCol | ResetTo of int

      type layout_state = above_mode * int * int * (item list)

      val newline = CustomString.fromString "\n"

      fun layout ((am, lnStart, col, acc): layout_state) doc : layout_state =
        case doc of
          Empty => (am, lnStart, col, acc)
        | Space _ => (am, lnStart, col + 1, Spaces 1 :: acc)
        | Indent d =>
            let
              val (col, acc) =
                if col = lnStart then
                  (col + indentWidth, Spaces indentWidth :: acc)
                else
                  (col, acc)
            in
              layout (am, lnStart + indentWidth, col, acc) d
            end
        | Text str =>
            (am, lnStart, col + CustomString.size str, Stuff str :: acc)
        | Beside (doc1, doc2) =>
            layout (layout (am, lnStart, col, acc) doc1) doc2
        | BesideAndAbove (withSpace, doc1, doc2) =>
            let
              val newAm =
                case am of
                  UseCurrentCol => ResetTo lnStart
                | ResetTo r => ResetTo r
              val (_, lnStart, col, acc) = layout (am, lnStart, col, acc) doc1
              val (col, acc) =
                if withSpace then (col + 1, Spaces 1 :: acc) else (col, acc)
            in
              layout (newAm, lnStart, col, acc) doc2
            end
        | Above (_, doc1, doc2) =>
            let
              val (_, _, _, acc) = layout (am, lnStart, col, acc) doc1
              val newLnStart =
                case am of
                  UseCurrentCol => col
                | ResetTo r => r
              val acc = Spaces newLnStart :: Newline :: acc
            in
              layout (UseCurrentCol, newLnStart, newLnStart, acc) doc2
            end
        | Choice {flattened = (_, flat, sz, _), normal} =>
            let
              val widthOkay = col + sz <= maxWidth
              val ribbonOkay = (col - lnStart) + sz <= ribbonWidth
            in
              if widthOkay andalso ribbonOkay then
                layout (am, lnStart, col, acc) flat
              else
                layout (am, lnStart, col, acc) normal
            end
        | Rigid d => layout (am, lnStart, col, acc) d

      val (_, _, _, items) = layout (UseCurrentCol, 0, 0, []) inputDoc

      val items = revAndStripTrailingWhitespace items

      fun itemToString x =
        case x of
          Newline => newline
        | Spaces n => spaces n
        | Stuff s => s
    in
      CustomString.concat (List.map itemToString items)
    end


  val toString = pretty {ribbonFrac = 0.5, maxWidth = 80, indentWidth = 2}

end
