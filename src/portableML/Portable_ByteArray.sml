(* Should check range of integers *)
structure Portable_ByteArray =
    struct
        type bytearray = Word8Array.array  (* ### POTENTIAL ### *)
        exception Range
        open Word8Array
        (* The next definition isn't quite right *)
        fun extract (a,i,nopt) =
            let val l = Portable_Array.length a
                val n = case nopt of SOME n => n | NONE => l - i
                fun bytes j =
                    if (j >= i + n) then []
                    else Portable_Array.sub (a,j) :: bytes (j + 1)
            in String.implode (map Char.chr (bytes i))
            end
    end
