structure PrettyImpl =
struct

  type context = unit
  datatype pretty =
           PrettyBlock of int * bool * context list * pretty list
           | PrettyBreak of int * int
           | PrettyLineBreak
           | PrettyString of string
           | PrettyStringWithWidth of string * int

  fun prettyPrint (stream, lineWidth) pretty =
    let
      fun printBlanks n =
        if n > 0 then (stream " "; printBlanks(n-1)) else ()

      (* Find out whether the block fits and return the space left if it does.
         Terminates with NONE as soon as it finds the line doesn't fit. *)
      fun getSize(PrettyBlock (_, _, _, entries), spaceLeft) =
            List.foldl(fn (p, SOME s) => getSize(p, s) | (_, NONE) => NONE)
                      (SOME spaceLeft)
                      entries

      |   getSize(PrettyBreak (blanks, _), spaceLeft) =
            if blanks <= spaceLeft then SOME(spaceLeft-blanks) else NONE

      |   getSize(PrettyString st, spaceLeft) =
            let
              val size = String.size st
            in
              if size <= spaceLeft then SOME(spaceLeft-size) else NONE
            end

      |   getSize(PrettyStringWithWidth(_, w), spaceLeft) =
            if w <= spaceLeft then SOME(spaceLeft-w) else NONE

      |   getSize(PrettyLineBreak, _) = NONE

        (* Lay out the block and return the space that is left after the line
           has been printed. *)
      fun layOut(p as PrettyBlock (blockOffset, consistent, context, entries),
                 indent, spaceLeft) =
        let
          val blockIndent = indent+blockOffset
        in
          case getSize(p, spaceLeft) of
              SOME s => (* Fits *)
                (* Lay out the contents. This will not need to break. *)
                (List.foldl(fn(p, space) => layOut(p, blockIndent, space))
                           spaceLeft entries;
                 s)
           |   NONE => (* Doesn't fit - break line somewhere. *)
               let
                 (* Lay out this block, breaking where necessary. *)
                 fun doPrint([], _, left) = (* Finished: return what's left. *)
                       left

                 |   doPrint([PrettyBreak _], _, left) =
                       left (* Ignore trailing breaks. *)

                 |   doPrint(PrettyBreak (blanks, breakIndent)::rest, _, left) =
                     let
                       val currentIndent = blockIndent+breakIndent
                       (* Compute the space of the next item(s) up to the end
                          or the next space.  Since we only break at spaces if
                          there are Blocks or Strings without spaces between we
                          need to know the total size. *)
                       fun getsp([], left) = SOME left
                       |   getsp(PrettyBreak _ :: _, left) = SOME left
                       |   getsp(next::rest, left) =
                           case getSize(next, left) of
                               NONE => NONE
                            |   SOME sp => getsp(rest, sp)

                     in
                       if consistent orelse left <= blanks orelse
                          not(isSome(getsp(rest, left-blanks)))
                       then
                         (* Either a consistent break or the next item won't
                            fit. *)
                         (
                           stream "\n";
                           printBlanks currentIndent;
                           (* Carry the indent associated with this item
                              forward so that it is included in the block
                              indentation if the next item is a block.  If
                              it is a string we have already included it. *)
                           doPrint(rest, breakIndent, lineWidth-currentIndent)
                         )
                       else (* We don't need to break here. *)
                         (
                           printBlanks blanks;
                           doPrint(rest, 0, left-blanks)
                         )
                     end

                 |   doPrint(PrettyString s :: rest, _, left) =
                       (
                         stream s;
                         doPrint(rest, 0, left - size s)
                       )

                 |   doPrint(PrettyStringWithWidth(s, w) :: rest, _, left) =
                       (
                         stream s;
                         doPrint(rest, 0, left-w)
                       )

                 |   doPrint((b as PrettyBlock _) :: rest, breakIndent, left) =
                       doPrint(rest,0, layOut(b, blockIndent+breakIndent, left))
                 |   doPrint(PrettyLineBreak :: rest, _, _) =
                       (
                         stream "\n";
                         printBlanks blockIndent;
                         doPrint(rest, 0, lineWidth-blockIndent)
                       )

                 val onLine = doPrint(entries, 0, spaceLeft);
               in
                 onLine
               end
        end

      |   layOut (PrettyBreak (blanks, _), _, spaceLeft) =
                ( printBlanks blanks; Int.max(spaceLeft-blanks, 0) )

      |   layOut (PrettyString st, _, spaceLeft) =
            ( stream st;
              Int.max(spaceLeft - String.size st, 0) )

      |   layOut (PrettyStringWithWidth(st, w), _, spaceLeft) =
            ( stream st; Int.max(spaceLeft-w, 0) )

      |   layOut (PrettyLineBreak, _, spaceLeft) = spaceLeft

    in
      if layOut(pretty, 0, lineWidth) <> lineWidth
      then stream "\n" (* End the line unless we haven't written anything. *)
      else ()
    end

end
