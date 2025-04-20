(** Copyright (c) 2020 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

(** A source is a contiguous subsequence of a code file. We can look up its
  * position (e.g. line-and-column, or character index), take subsequences,
  * etc.
  *)
structure Source :>
sig
  type source
  type t = source

  val loadFromFile: FilePath.t -> source
  val loadFromStdin: unit -> source

  val make: {fileName: FilePath.t, contents: char Seq.t} -> source

  val fileName: source -> FilePath.t
  val absoluteStart: source -> {line: int, col: int}
  val absoluteEnd: source -> {line: int, col: int}

  val absoluteStartOffset: source -> int
  val absoluteEndOffset: source -> int

  val length: source -> int
  val nth: source -> int -> char
  val slice: source -> int * int -> source
  val take: source -> int -> source
  val drop: source -> int -> source

  val lineRanges: source -> (int * int) Seq.t

  (** if src1 adjacent to scr2, attach them and return new. *)
  val abut: source * source -> source option

  val toString: source -> string

  val wholeFile: source -> source

  (** `wholeLine src lineNum`
    * Doesn't matter if the src is positioned elsewhere. Uses absolute lineNum.
    * Remember, 1-indexing for line nums, ugh.
    *)
  val wholeLine: source -> int -> source
end =
struct

  type source =
    { data: char Seq.t
    (** underlying file *)
    , fileName: FilePath.t
    (** the byte offsets of newlines in the underlying file *)
    , newlineIdxs: int Seq.t
    }

  type t = source

  fun loadFromCharSeq path contents =
    let
      val n = Seq.length contents

      (** Check that we can use the slice base as the actual base. *)
      val (_, absoluteOffset, _) = ArraySlice.base contents
      val _ =
        if absoluteOffset = 0 then
          ()
        else
          raise Fail
            "bug in Source.loadFromFile: expected \
            \ReadFile.contentsSeq to return slice at offset 0"

      val newlineIdxs =
        ArraySlice.full (SeqBasis.filter (0, n) (fn i => i) (fn i =>
          Seq.nth contents i = #"\n"))
    in
      {data = contents, fileName = path, newlineIdxs = newlineIdxs}
    end

  fun loadFromFile path =
    let val contents = ReadFile.contentsSeq (FilePath.toHostPath path)
    in loadFromCharSeq path contents
    end

  fun loadFromStdin () =
    let
      (* kind of faking it *)
      val path = FilePath.fromFields ["<stdin>"]
      val s = TextIO.inputAll TextIO.stdIn
      val contents = Seq.tabulate (fn i => String.sub (s, i)) (String.size s)
    in
      loadFromCharSeq path contents
    end

  fun make {fileName, contents} = loadFromCharSeq fileName contents

  fun fileName (s: source) = #fileName s

  fun absoluteStartOffset ({data, ...}: source) =
    let val (_, off, _) = ArraySlice.base data
    in off
    end

  fun absoluteEndOffset ({data, ...}: source) =
    let val (_, off, n) = ArraySlice.base data
    in off + n
    end

  fun absoluteStart (s as {newlineIdxs, ...}: source) =
    if absoluteStartOffset s = 0 then
      {line = 1, col = 1}
    else
      let
        val lineNum =
          BinarySearch.search Int.compare newlineIdxs (absoluteStartOffset s)
        val lineOffset =
          if lineNum = 0 then 0 else 1 + Seq.nth newlineIdxs (lineNum - 1)
        val charNum = absoluteStartOffset s - lineOffset
      in
        (** Convert to 1-indexing *)
        {line = lineNum + 1, col = charNum + 1}
      end

  fun length ({data, ...}: source) = Seq.length data
  fun nth ({data, ...}: source) k = Seq.nth data k

  fun slice {data, fileName, newlineIdxs} (i, len) =
    { data = Seq.subseq data (i, Int.min (len, Seq.length data - i))
    , fileName = fileName
    , newlineIdxs = newlineIdxs
    }

  fun take s k = slice s (0, k)
  fun drop s k =
    slice s (k, length s - k)

  fun absoluteEnd s =
    absoluteStart (drop s (length s))

  fun toString s =
    CharVector.tabulate (length s, nth s)

  fun wholeFile ({data, fileName, newlineIdxs}: source) =
    let
      val (a, _, _) = ArraySlice.base data
    in
      {data = ArraySlice.full a, fileName = fileName, newlineIdxs = newlineIdxs}
    end

  fun wholeLine (s as {newlineIdxs, ...}: source) lineNum1 =
    let
      val base = wholeFile s

      (** Back to 0-indexing *)
      val lineNum0 = lineNum1 - 1

      val lineStartOffset =
        if lineNum0 = 0 then 0 else 1 + Seq.nth newlineIdxs (lineNum0 - 1)

      val lineEndOffset =
        if lineNum0 >= Seq.length newlineIdxs then length base
        else Seq.nth newlineIdxs lineNum0

    in
      slice base (lineStartOffset, lineEndOffset - lineStartOffset)
    end


  fun abut (src1, src2) =
    if
      FilePath.sameFile (fileName src1, fileName src2)
      andalso absoluteEndOffset src1 = absoluteStartOffset src2
    then
      let
        val src = wholeFile src1
        val i = absoluteStartOffset src1
        val j = absoluteEndOffset src2
      in
        SOME (slice src (i, j - i))
      end
    else
      NONE


  fun lineRanges (s as {newlineIdxs, ...}: source) =
    let
      (** convert back to 0-indexing (-_-) *)
      val {line = lnStart, ...} = absoluteStart s
      val lnStart = lnStart - 1
      val {line = lnEnd, ...} = absoluteEnd s
      val lnEnd = lnEnd - 1

      val numLines = lnEnd - lnStart + 1

      fun start i =
        if i = 0 then absoluteStartOffset s
        else 1 + Seq.nth newlineIdxs (lnStart + i - 1)

      fun endd i =
        if i = numLines - 1 then absoluteEndOffset s
        else Seq.nth newlineIdxs (lnStart + i)

      val off = absoluteStartOffset s
    in
      Seq.tabulate (fn i => (start i - off, endd i - off)) numLines
    end

end
