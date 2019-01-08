structure RL_Socket :> RL_Socket = struct

fun sendStr(sock, str) =
  let
    val vec = Word8Vector.tabulate(
      String.size str + 1,
      (fn i => Word8.fromInt(Char.ord(String.sub(str, i)))
               handle Subscript => Word8.fromInt 0))
    val slice = Word8VectorSlice.slice(vec,0,NONE)
  in
    Socket.sendVec(sock, slice)
  end

fun recvStr(sock, n) =
  let val datar =
    Socket.recvVec(sock, n)
  in
    CharVector.tabulate(Word8Vector.length datar,
      (fn i => Char.chr(Word8.toInt(Word8Vector.sub(datar,i)))))
  end

fun receive(sock) =
  let
    fun rec_k(sock, acc) =
      let val datar = recvStr(sock, 4096) in
        if String.isSuffix (String.str(Char.chr 0)) datar
        then String.concat(List.rev(
          String.extract(datar, 0, SOME (String.size datar - 1))
          ::acc))
        else if Char.contains datar (Char.chr 0)
             then raise HolKernel.ERR "receive" "found deliminator within response"
             else if size datar = 0
                  then raise HolKernel.ERR "receive" "found empty string, maybe a broken socket"
                  else rec_k(sock, datar::acc)
      end
  in
    rec_k(sock, [])
  end

end
