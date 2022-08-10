structure UTF8 :> UTF8 =
struct

exception BadUTF8 of string

val two11 = 2048  (* 2 ^ 11 *)
val two16 = 65536 (* 2 ^ 16 *)
val Umax = 0x10FFFF (* maximum Unicode code point *)

fun chr i =
    if i < 0 then raise Chr
    else if i < 128 then str (Char.chr i)
    else if i < two11 then let
        val w = Word.fromInt i
        val byte2 = 128 + Word.toInt (Word.andb(w, 0wx3F))
        val byte1 = 0xC0 + Word.toInt (Word.>>(w,0w6))
      in
        String.implode [Char.chr byte1, Char.chr byte2]
      end
    else if i < two16 then let
        val w = Word.fromInt i
        val byte3 = 128 + Word.toInt (Word.andb(w, 0wx3F))  (* 3F = 6 bits *)
        val w = Word.>>(w,0w6)
        val byte2 = 128 + Word.toInt (Word.andb(w, 0wx3F))  (* 3F = 6 bits *)
        val w = Word.>>(w,0w6)
        val byte1 = 0xE0 + Word.toInt (Word.andb(w, 0wxF))
           (* inital E says there are 3 bytes, and with F to extract 4 bits *)
      in
        String.implode (map Char.chr [byte1, byte2, byte3])
      end
    else if i <= Umax then let
        val w = Word.fromInt i
        val byte4 = 128 + Word.toInt (Word.andb(w, 0wx3F))  (* 3F = 6 bits *)
        val w = Word.>>(w,0w6)
        val byte3 = 128 + Word.toInt (Word.andb(w, 0wx3F))  (* 3F = 6 bits *)
        val w = Word.>>(w,0w6)
        val byte2 = 128 + Word.toInt (Word.andb(w, 0wx3F))  (* 3F = 6 bits *)
        val w = Word.>>(w,0w6)
        val byte1 = 0xF0 + Word.toInt (Word.andb(w, 0wx7))
           (* inital F says there are 4 bytes, and with 7 to extract 3 bits *)
      in
        String.implode (map Char.chr [byte1, byte2, byte3, byte4])
      end
    else raise Chr

fun byte1_count c = let
  fun recurse acc b = if b > 0w127 then recurse (acc + 1) (Word8.<<(b,0w1))
                      else acc
in
  recurse 0 (Word8.fromInt (Char.ord c))
end

fun isCont_char c = let val i = Char.ord c in 128 <= i andalso i < 192 end

fun pow2 i = Word.toInt (Word.<<(0w1, Word.fromInt i))

fun getChar s = let
  fun rangeCheck cnt (res as ((_, i), _)) =
    if case cnt of 2 => 0x80 <= i
                 | 3 => 0x800 <= i
                 | 4 => 0x10000 <= i andalso i <= Umax
                 | _ => false
    then res
    else raise BadUTF8 s
  open Substring
  fun ucontinue acc pos limit ss =
      if pos = limit then let
          val (p,s) = splitAt (ss, limit)
        in
          SOME((string p, acc), string s)
        end
      else let
          val pos_c = sub(ss, pos)
              handle Subscript => raise BadUTF8 (string (slice(ss,0,SOME pos)))
        in
          if isCont_char pos_c then
            ucontinue (acc * 64 + Char.ord pos_c - 128) (pos + 1) limit ss
          else raise BadUTF8 (string (slice(ss,0,SOME (pos + 1))))
        end
  fun recurse ss =
      case getc ss of
        NONE => NONE
      | SOME (c, ss') => let
          val i = Char.ord c
        in
          if i < 128 then SOME((str c, i), string ss')
          else let
              val cnt = byte1_count c
            in
              if cnt = 1 then raise BadUTF8 (str c)
              else
                Option.map
                    (rangeCheck cnt)
                    (ucontinue (i + pow2 (8 - cnt) - 256) 1 cnt ss)
            end
        end
in
  recurse (full s)
end

fun size s = let
  open Substring
  val ss = full s
  val sz = size ss
  fun recurse acc pos =
      if pos = sz then acc
      else let
          val c = sub(ss,pos)
        in
          if Char.ord c < 128 then recurse (acc + 1) (pos + 1)
          else let
              val bc = byte1_count c
            in
              check acc (pos + 1) pos (bc - 1)
            end
        end
  and check acc pos start cnt =
      if cnt = 0 then recurse (acc + 1) pos
      else if pos = sz then
        raise BadUTF8 (string (slice(ss,start,SOME(pos-start))))
      else let
          val c = sub(ss,pos)
        in
          if isCont_char c then check acc (pos + 1) start (cnt - 1)
          else raise BadUTF8 (string (slice(ss,start,SOME(pos-start))))
        end
in
  recurse 0 0
end

val firstChar = Option.map #1 o getChar

fun lastChar s = let
  open Substring
  val ss = full s
  val lastpos = size ss - 1
  fun goback pos =
      if pos < 0 then raise BadUTF8 (str (sub(ss,0)))
      else let
          val c = sub(ss,pos)
        in
          if Char.ord c >= 192 then let
              val bc = byte1_count c
            in
              if lastpos - pos + 1 = bc then string (slice(ss,pos,NONE))
              else raise BadUTF8 (string (slice(ss,pos+bc,NONE)))
            end
          else if isCont_char c then goback (pos - 1)
          else raise BadUTF8 (string (slice(ss,pos+1,NONE)))
        end
in
  if lastpos < 0 then NONE
  else let
      val c = sub(ss, lastpos)
    in
      if Char.ord c < 128 then SOME(str c, Char.ord c)
      else Option.map #1 (getChar (goback (lastpos - 1)))
    end
end

fun translate f s = let
  fun recurse i changed acc ustr =
      case getChar ustr of
        NONE => if changed then String.concat (List.rev acc)
                else s
      | SOME ((c,code), rest) => let
          val c' = f c
        in
          if c' = c andalso not changed then
            recurse (i + 1) changed acc rest
          else if not changed then
            recurse i true (c' :: String.extract(s,0,SOME i)::acc) rest
          else
            recurse i true (c' :: acc) rest
        end
in
  recurse 0 false [] s
end

fun padRight c len s =
  let
    val slen = size s
  in
    if slen > len then s
    else s ^ CharVector.tabulate(len - slen, fn _ => c)
  end

fun substring (s,start,numchars) =
  let
    fun recurse acc i c s =
        if c >= numchars then String.concat (List.rev acc)
        else if i < start then
          case getChar s of
              NONE => raise Subscript
            | SOME (_, rest) => recurse acc (i + 1) c rest
        else
          case getChar s of
              NONE => raise Subscript
            | SOME ((char, _), rest) =>
                recurse (char::acc) (i + 1) (c + 1) rest
  in
    recurse [] 0 0 s
  end

fun all P s =
    case getChar s of
        NONE => true
      | SOME ((s,_), rest) => P s andalso all P rest

fun explode s =
    let
      fun recurse A s =
          case getChar s of
              NONE => List.rev A
            | SOME((s,_), rest) => recurse (s::A) rest
    in
      recurse [] s
    end

fun explodei s =
    let
      fun recurse A s =
          case getChar s of
              NONE => List.rev A
            | SOME((_,i), rest) => recurse (i::A) rest
    in
      recurse [] s
    end

fun apfst f (x,y) = (f x, y)

datatype safecp = CP of int (* UTF8-encoded code-point *)
                | RB of int (* raw byte *)
fun safecp_to_char (CP i) = chr i
  | safecp_to_char (RB b) = str (Char.chr b)
fun safe_explode s =
    let
      fun recurse A s =
          if s = "" then List.rev A
          else
            let
              val (i, rest) =
                  apfst (CP o #2) (valOf (getChar s))
                  handle BadUTF8 _ =>
                         (RB (Char.ord (String.sub(s,0))),
                          String.extract(s,1,NONE))
            in
              recurse (i::A) rest
            end
    in
      recurse [] s
    end


end (* struct *)
