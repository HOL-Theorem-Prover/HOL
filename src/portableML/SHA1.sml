structure SHA1 :> SHA1 =
struct

  (* taken from
       git@github.com:srdqty/sml-sha1.git
  *)

(* Copyright (c) 2014 Sophia Donataccio, The MIT License (MIT) *)

(* A good explanation of the sha1 algorithm is available at
   https://en.wikipedia.org/wiki/SHA-1 *)

  type 'a byte_reader = 'a * int -> Word8Vector.vector * 'a

  local
    fun toBitSize x = Word64.*(x, 0w8)

    fun explodeSize size (* in bits *) =
      let
        val s7 = Word64.>>(Word64.<<(size, 0w56), 0w56)
        val s6 = Word64.>>(Word64.<<(size, 0w48), 0w56)
        val s5 = Word64.>>(Word64.<<(size, 0w40), 0w56)
        val s4 = Word64.>>(Word64.<<(size, 0w32), 0w56)
        val s3 = Word64.>>(Word64.<<(size, 0w24), 0w56)
        val s2 = Word64.>>(Word64.<<(size, 0w16), 0w56)
        val s1 = Word64.>>(Word64.<<(size, 0w08), 0w56)
        val s0 = Word64.>>(size                 , 0w56)
      in
        ( Word8.fromLarge (Word64.toLarge s0)
        , Word8.fromLarge (Word64.toLarge s1)
        , Word8.fromLarge (Word64.toLarge s2)
        , Word8.fromLarge (Word64.toLarge s3)
        , Word8.fromLarge (Word64.toLarge s4)
        , Word8.fromLarge (Word64.toLarge s5)
        , Word8.fromLarge (Word64.toLarge s6)
        , Word8.fromLarge (Word64.toLarge s7))
      end

    fun createLastChunk (chunk, messageByteSize) =
      let
        val chunkSize = Word8Vector.length chunk
        val (s0, s1, s2, s3, s4, s5, s6, s7) =
          (* Size in bits is stored in the chunk *)
          explodeSize (toBitSize messageByteSize)
        fun buildChunk i =
          if i < chunkSize then Word8Vector.sub (chunk, i)
          else if i = chunkSize then 0wx80
          else if i = 56 then s0
          else if i = 57 then s1
          else if i = 58 then s2
          else if i = 59 then s3
          else if i = 60 then s4
          else if i = 61 then s5
          else if i = 62 then s6
          else if i = 63 then s7
          else 0w0
      in
        Word8Vector.tabulate (64, buildChunk)
      end

    fun addPadding chunk =
      let
        val chunkSize = Word8Vector.length chunk
        fun buildChunk i =
          if i < chunkSize then Word8Vector.sub (chunk, i)
          else if i = chunkSize then 0wx80
          else 0w0
      in
        Word8Vector.tabulate (64, buildChunk)
      end

    fun createPadChunk messageByteSize =
      let
        val (s0, s1, s2, s3, s4, s5, s6, s7) =
          (* Size in bits is stored in the chunk *)
          explodeSize (toBitSize messageByteSize)
        fun buildChunk i =
          if i < 56 then 0w0
          else if i = 56 then s0
          else if i = 57 then s1
          else if i = 58 then s2
          else if i = 59 then s3
          else if i = 60 then s4
          else if i = 61 then s5
          else if i = 62 then s6
          else if i = 63 then s7
          else raise (Fail "createPadChunk: invalid chunk size")
      in
        Word8Vector.tabulate (64, buildChunk)
      end

    datatype 'a ChunkReaderState =
      Reading of 'a byte_reader * 'a * Word64.word
    | PadChunk of Word8Vector.vector
    | Empty

  in (* local *)

    fun makeInitChunkStreamState (byteReader, byteStreamState) =
      Reading (byteReader, byteStreamState, 0w0)

    fun readChunk Empty = NONE
      | readChunk (PadChunk chunk) = SOME (chunk, Empty)
      | readChunk (Reading(byteReader, byteStreamState, totalBytesRead)) =
        let
          val (chunk, nextByteStreamState) = byteReader (byteStreamState, 64)
          val chunkSize = Word8Vector.length chunk
          val nextTotalBytesRead =
              Word64.+(Word64.fromInt chunkSize, totalBytesRead)
        in
          if chunkSize = 64 then SOME (chunk, Reading(byteReader,
              nextByteStreamState, nextTotalBytesRead))
          else if chunkSize < 56 then SOME(createLastChunk (chunk,
              nextTotalBytesRead), Empty)
          else (* 56 < chunkSize <= 64 *)
            SOME(addPadding chunk, PadChunk (createPadChunk nextTotalBytesRead))
        end
  end

  structure Word32Array = Array

  local
    fun initializeWorkingArrayWithDataFromChunk (chunk, wArray) =
      let
        fun sub (c, i) =
          Word32.fromLarge(PackWord32Big.subVec (c, i))
        fun calcW i =
          let
            val w1 = Word32Array.sub(wArray, i - 3)
            val w2 = Word32Array.sub(wArray, i - 8)
            val w3 = Word32Array.sub(wArray, i - 14)
            val w4 = Word32Array.sub(wArray, i - 16)
            fun lrot1 w = Word32.orb(Word32.<<(w, 0w1), Word32.>>(w, 0w31))
          in
            lrot1 (Word32.xorb(Word32.xorb(Word32.xorb(w1, w2), w3), w4))
          end
        fun loop1 i =
          if 0 <= i andalso i <= 15 then
            (Word32Array.update (wArray, i, sub (chunk, i))
            ; loop1 (i + 1))
          else ()
        fun loop2 i =
          if 16 <= i andalso i <= 79 then
            (Word32Array.update (wArray, i, calcW i)
            ; loop2 (i + 1))
          else ()
      in
        ( loop1 0
        ; loop2 16)
      end

    fun packHashResultIntoByteVector (h0, h1, h2, h3, h4) =
      let
        val result = Word8Array.array (20, 0wx0)
      in
        (PackWord32Big.update(result, 0, Word32.toLarge h0)
        ; PackWord32Big.update(result, 1, Word32.toLarge h1)
        ; PackWord32Big.update(result, 2, Word32.toLarge h2)
        ; PackWord32Big.update(result, 3, Word32.toLarge h3)
        ; PackWord32Big.update(result, 4, Word32.toLarge h4)
        ; Word8Array.vector result)
      end

    (* Given the current hash state values and the current
       chunk (preprocessed into a working array by fillWorkingArray),
       this function updates the hash state values according to the
       sha1 algorithm *)
    fun processChunkData (wArray, h0, h1, h2, h3, h4) =
      let
        fun loop (i, a, b, c, d, e) =
          let
            fun lrot5 w =
              let
                val lsb5 = Word32.>>(w, 0w27)
                val msb27 = Word32.<<(w, 0w5)
              in
                Word32.orb(msb27, lsb5)
              end
            fun lrot30 w =
              let
                val lsb30 = Word32.>>(w, 0w2)
                val msb2 = Word32.<<(w, 0w30)
              in
                Word32.orb(msb2, lsb30)
              end
            fun calcF (i, b, c, d) =
              if 0 <= i andalso i <= 19 then
                Word32.orb(Word32.andb(b, c),
                           Word32.andb(Word32.notb b, d))
              else if 20 <= i andalso i <= 39 then
                Word32.xorb(Word32.xorb(b, c), d)
              else if 40 <= i andalso i <= 59 then
                Word32.orb(Word32.orb(Word32.andb(b, c),
                                      Word32.andb(b, d)),
                           Word32.andb(c, d))
              else (* 60 <= i <= 79 *)
                Word32.xorb(Word32.xorb(b, c), d)
            fun calcK i =
              if 0 <= i andalso i <= 19 then       0wx5a827999
              else if 20 <= i andalso i <= 39 then 0wx6ed9eba1
              else if 40 <= i andalso i <= 59 then 0wx8f1bbcdc
              else (* 60 <= i <= 79 *)             0wxca62c1d6
            fun calcA (a, f, e, k, w) =
              Word32.+(Word32.+(Word32.+(Word32.+(lrot5 a, f), e), k), w)
          in
            if 0 <= i andalso i <= 79 then
              let
                val f = calcF (i, b, c, d)
                val k = calcK i
                val a' = calcA (a, f, e, k, Word32Array.sub(wArray, i))
                val b' = a
                val c' = lrot30 b
                val d' = c
                val e' = d
              in
                loop (i + 1, a', b', c', d', e')
              end
            else
              (h0 + a, h1 + b, h2 + c, h3 + d, h4 + e)
          end
      in
        loop (0, h0, h1, h2, h3, h4)
      end

  in (* local *)

    fun sha1 byteReader byteStreamState =
      let
        (* The initial values of the hash result state. These are defined
           by the sha1 algorithm. *)
        val initH0 : Word32.word = 0wx67452301
        val initH1 : Word32.word = 0wxefcdab89
        val initH2 : Word32.word = 0wx98badcfe
        val initH3 : Word32.word = 0wx10325476
        val initH4 : Word32.word = 0wxc3d2e1f0

        (* An array that will be used for temporary space repeatedly
           to process each chunk *)
        val workingArray = Word32Array.array (80, 0wx0)

        fun loopOverChunks (chunkStreamState, h0, h1, h2, h3, h4) =
          case readChunk chunkStreamState of
            NONE => packHashResultIntoByteVector (h0, h1, h2, h3, h4)
          | SOME (chunk, nextChunkStreamState) =>
            let
              val _ =
                initializeWorkingArrayWithDataFromChunk (chunk, workingArray)

              (* Process the data in the working array (filled
                 with the current chunk's data) using the sha1
                 hash algorithm *)
              val (h0', h1', h2', h3', h4') =
                processChunkData (workingArray, h0, h1, h2, h3, h4)
            in
              loopOverChunks (nextChunkStreamState, h0', h1', h2', h3', h4')
            end
      in
        loopOverChunks (makeInitChunkStreamState (byteReader, byteStreamState),
                        initH0, initH1, initH2, initH3, initH4)
      end
  end

  fun sha1String byteReader byteStreamState = let
    val hashVector = sha1 byteReader byteStreamState

    fun ithNibbleToHexDigitChar i = let
      fun getNibble i = let
        fun isEven n = n mod 2 = 0
        fun getMostSignificantNibble byte = Word8.>>(byte, 0w4)
        fun getLeastSignificantNibble byte = Word8.andb(byte, 0wx0f)
        val byteI = Word8Vector.sub (hashVector, i div 2)
      in
        if isEven i
          then getMostSignificantNibble byteI
          else getLeastSignificantNibble byteI
      end

      fun nibbleToHexDigitChar nibble =
        case Char.fromString (Word8.toString nibble) of
            NONE => raise (Fail "sha1String: invalid hex digit")
          | SOME ch => Char.toLower ch

    in
      nibbleToHexDigitChar (getNibble i)
    end

  in
    CharVector.tabulate (40, ithNibbleToHexDigitChar)
  end

  fun sha1_file0 {filename} =
      let
        val fstream = BinIO.openIn filename
        val fstream' = BinIO.getInstream fstream
      in
        sha1String BinIO.StreamIO.inputN fstream' before
        BinIO.closeIn fstream
      end

  fun sha1_file {filename} =
      if OS.FileSys.access("/usr/bin/shasum", [OS.FileSys.A_EXEC]) then
          case Mosml.run "/usr/bin/shasum" [Systeml.protect filename] "" of
              Mosml.Success s => hd (String.tokens Char.isSpace s)
            | Mosml.Failure _ => sha1_file0 {filename=filename}
      else
        sha1_file0 {filename=filename}

end
