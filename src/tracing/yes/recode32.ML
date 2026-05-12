(* recode32.ML — Standalone streaming 64-bit → 32-bit PolyML heap recoder.
   Reads a 64-bit heap dump from stdin, writes a 32-bit narrow format to
   stdout, with constant memory usage (two small buffers).

   Built by Holmake (see Holmakefile in this directory) into
   $HOLDIR/bin/recode32. Invoked by Tracing.export as a pipe stage:
     poly-export | recode32 | gzip > file.tr.gz
*)

val BUF_SIZE = 65536

(* ----- Buffered stdin reader ----- *)

val rBuf = Word8Array.array (BUF_SIZE, 0w0)
val rSize = ref 0
val rPos = ref 0
val rEof = ref false

fun rFill () =
  if !rEof then () else
  let
    val keep = !rSize - !rPos
    val () = if !rPos > 0 andalso keep > 0 then
               Word8ArraySlice.copy
                 {src = Word8ArraySlice.slice (rBuf, !rPos, SOME keep),
                  dst = rBuf, di = 0}
             else ()
    val () = rPos := 0
    val () = rSize := keep
    fun loop () =
      if !rSize >= BUF_SIZE then () else
      let val got = Posix.IO.readArr (Posix.FileSys.stdin,
                      Word8ArraySlice.slice (rBuf, !rSize, SOME (BUF_SIZE - !rSize)))
      in if got = 0 then rEof := true
         else (rSize := !rSize + got; loop ()) end
  in loop () end

fun rEnsure n =
  if !rSize - !rPos >= n then true
  else (rFill (); !rSize - !rPos >= n)

fun rReadW64 () =
  if not (rEnsure 8) then NONE
  else let
    val p = !rPos
    fun b i = Word64.fromInt (Word8.toInt (Word8Array.sub (rBuf, p + i)))
    val w = let open Word64 infix orb <<
            in b 0 orb (b 1 << 0w8) orb (b 2 << 0w16) orb (b 3 << 0w24) orb
               (b 4 << 0w32) orb (b 5 << 0w40) orb (b 6 << 0w48) orb (b 7 << 0w56)
            end
    val () = rPos := p + 8
  in SOME w end

fun rReadW64' () = case rReadW64 () of SOME w => w
  | NONE => raise Fail "recode32: unexpected EOF"

(* Pump n raw bytes from stdin to the writer function `sink`. *)
fun rPump n sink = let
  fun loop rem =
    if rem = 0 then () else
    let val avail = !rSize - !rPos
        val chunk = Int.min (avail, rem)
    in
      if chunk > 0 then (
        sink (rBuf, !rPos, chunk);
        rPos := !rPos + chunk;
        loop (rem - chunk))
      else if rEnsure 1 then loop rem
      else raise Fail "recode32: EOF in byte pump"
    end
in loop n end

(* ----- Buffered stdout writer ----- *)

val wBuf = Word8Array.array (BUF_SIZE, 0w0)
val wPos = ref 0

fun wFlush () =
  if !wPos = 0 then ()
  else let
    val n = !wPos
    fun loop p =
      if p >= n then ()
      else let val s = Word8ArraySlice.slice (wBuf, p, SOME (n - p))
               val k = Posix.IO.writeArr (Posix.FileSys.stdout, s)
           in loop (p + k) end
  in loop 0; wPos := 0 end

fun wReserve n = if !wPos + n > BUF_SIZE then wFlush () else ()

fun wU32 v = let
  val () = wReserve 4
  val p = !wPos
  fun bite i = Word8.fromLargeWord
    (Word64.toLargeWord (Word64.andb (Word64.>> (v, Word.fromInt (i*8)), 0wxFF)))
in
  Word8Array.update (wBuf, p,   bite 0);
  Word8Array.update (wBuf, p+1, bite 1);
  Word8Array.update (wBuf, p+2, bite 2);
  Word8Array.update (wBuf, p+3, bite 3);
  wPos := p + 4
end

fun wHeader32 (len, flags) =
  if len >= 0x1000000 then
    raise Fail ("recode32: object length " ^ Int.toString len ^ " >= 2^24")
  else wU32 (Word64.orb (Word64.fromInt len,
                         Word64.<< (Word64.fromInt flags, 0w24)))

(* Write a tagged pointer, verifying it sign-extends from 32 to 64 bits
   (i.e. parses back identically via get32). One shift-shift-compare per
   write; the not-overflow branch is taken on every valid input. *)
fun wTagptr32 v =
  if Word64.~>> (Word64.<< (v, 0w32), 0w32) = v then wU32 v
  else raise Fail ("recode32: tagptr 0x" ^ Word64.toString v ^
                   " does not fit in 32 bits")

fun wBytes4 (b0, b1, b2, b3) = (
  wReserve 4;
  let val p = !wPos in
    Word8Array.update (wBuf, p,   b0);
    Word8Array.update (wBuf, p+1, b1);
    Word8Array.update (wBuf, p+2, b2);
    Word8Array.update (wBuf, p+3, b3);
    wPos := p + 4
  end)

fun wSlice (src, off, n) = let
  fun loop i =
    if i >= n then () else (
      wReserve 1;
      Word8Array.update (wBuf, !wPos, Word8Array.sub (src, off + i));
      wPos := !wPos + 1;
      loop (i + 1))
in loop 0 end

(* ----- Main recoder loop ----- *)

val LEN_MASK = Word64.- (Word64.<< (0w1, 0w56), 0w1)

fun processHeader buf peek = let
  val flags = Word64.toInt (Word64.>> (buf, 0w56))
  val len = Word64.toInt (Word64.andb (buf, LEN_MASK))
  val kind = flags mod 4
in case kind of
     0 => ( (* Regular *)
       wHeader32 (len, flags);
       if len = 0 then loop peek
       else (
         wTagptr32 peek;
         let fun copy i =
           if i >= len then () else (wTagptr32 (rReadW64' ()); copy (i+1))
         in copy 1 end;
         loop (rReadW64' ())))
   | 1 => ( (* Bytes-kind: opaque raw bytes *)
       if len = 0 then raise Fail "recode32: Bytes with len=0" else ();
       let val new_len32 = len * 2
           val () = wHeader32 (new_len32, flags)
           val () = wU32 peek
           val () = wU32 (Word64.>> (peek, 0w32))
           val () = rPump ((len - 1) * 8) wSlice
       in loop (rReadW64' ()) end)
   | _ => ( (* Code/Closure *)
       wHeader32 (len, flags);
       if len = 0 then loop peek
       else raise Fail "recode32: Code/Closure with len > 0")
end

and loop buf =
  case rReadW64 () of
    NONE => wTagptr32 buf  (* EOF: buf was the root tagptr *)
  | SOME peek => processHeader buf peek

fun main () = (
  wBytes4 (0wx54, 0wx52, 0wx33, 0wx32);  (* 32-bit magic: "TR32" *)
  wBytes4 (0w0, 0w0, 0w0, 0wxFF);         (* + \0\0\0\xFF       *)
  case rReadW64 () of
    NONE => raise Fail "recode32: empty input"
  | SOME first => loop first;
  wFlush ())
