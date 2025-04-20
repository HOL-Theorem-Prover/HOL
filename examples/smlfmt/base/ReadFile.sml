(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ReadFile:
sig
  type 'a seq = 'a ArraySlice.slice

  val contentsSeq: string -> char seq
  val contentsBinSeq: string -> Word8.word seq
  val contents: string -> string
end =
struct

  type 'a seq = 'a ArraySlice.slice

  fun contentsSeq' (default, readByte: Word8.word -> 'a) path =
    let
      val (file, length) =
        let
          open Posix.FileSys
          val file = openf (path, O_RDONLY, O.fromWord 0w0)
        in
          (file, Position.toInt (ST.size (fstat file)))
        end

      open Posix.IO

      val bufferSize = 10000
      val buffer = Word8Array.array (bufferSize, 0w0)
      val result = Array.array (length, default)

      fun copyToResult i n =
        Word8ArraySlice.appi
          (fn (j, b) => Array.update (result, i + j, readByte b))
          (Word8ArraySlice.slice (buffer, 0, SOME n))

      fun dumpFrom i =
        if i >= length then
          ()
        else
          let val bytesRead = readArr (file, Word8ArraySlice.full buffer)
          in copyToResult i bytesRead; dumpFrom (i + bytesRead)
          end
    in
      dumpFrom 0;
      close file;
      ArraySlice.full result
    end

  fun contentsSeq path =
    contentsSeq' (Char.chr 0, Char.chr o Word8.toInt) path

  fun contentsBinSeq path =
    contentsSeq' (0w0, fn w => w) path

  fun contents filename =
    let
      val chars = contentsSeq filename
    in
      CharVector.tabulate (ArraySlice.length chars, fn i =>
        ArraySlice.sub (chars, i))
    end
end
