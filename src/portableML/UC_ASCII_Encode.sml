structure UC_ASCII_Encode :> UC_ASCII_Encode =
struct

val encoding_table =
    Vector.tabulate (32, fn i => if i < 26 then Char.chr (i + 65)
                                 else Char.chr (i + 22))

fun d2c d = Vector.sub(encoding_table, d)
fun c2d c = let val i = Char.ord c
            in
              if i > 53 then i - 65
              else i - 22
            end


(*
val eight_W = Word.fromInt 8
val three_W = Word.fromInt 3
val one_W = Word8.fromInt 1
val masks = let
  fun gen i =
      let val wwi = Word.fromInt i
          val shift_right = Word.-(eight_W, wwi)
      in
        (shift_right, Word8.-(Word8.<<(one_W, shift_right), one_W))
      end
in
  Vector.tabulate (8, gen)
end

fun gethibits A n cw =
    let
      val (shiftr,mask) = Vector.sub(masks, n)
    in
      (Word8.toInt (Word8.>>(cw,shiftr)) + A, Word8.andb(cw,mask))
    end

fun encode0 s =
    let
      (* bc is index into 8 bits of character word cw representing our
         "current position".  If bc = 0, then bA may be non-zero, representing
         the value of the previous character's trailing bits, and which must
         be added to what is about to be extracted from cw.

         totake is some integer in [1,5] specifying number of bits to be
         consumed.  It will always be 5 if bc <> 0; it may be 5 even if bc > 3;
         in this latter situation, the behaviour is to consume the available
         bits and call recursively on the next character with bc = 0 and
         totake < 5.

         ix is the index into the underlying string
      *)
      val sz = String.size s
      fun i2w i = Word8.fromInt (Char.ord (String.sub(s,i)))
      fun recurse bA A totake bc ix (cw:Word8.word) =
          if bc = 0 then
            let
              val (nextvalue, rest) = gethibits bA totake cw
            in
              recurse 0 (nextvalue::A) 5 totake ix rest
            end
          else if bc > 3 then (* taking 5, falling off end of byte *)
            let val bA = Word8.toInt
                           (Word8.<<(cw, Word.-(Word.fromInt bc, three_W)))
            in
              if ix + 1 < sz then
                recurse bA A (bc - 3) 0 (ix + 1) (i2w (ix + 1))
              else List.rev (bA :: A)
            end
          else (* bc in [1,3] *)
            let val nextvalue =
                    Word8.toInt (Word8.>>(cw, Word.fromInt (3 - bc)))
            in
              if bc = 3 then
                if ix + 1 < sz then
                  recurse 0 (nextvalue::A) 5 0 (ix + 1) (i2w (ix + 1))
                else
                  List.rev(nextvalue::A)
              else (* bc is 1 or 2 *)
                let
                  val cw' = Word8.andb (cw, #2 (Vector.sub(masks, bc + 5)))
                in
                  recurse 0 (nextvalue :: A) 5 (bc + 5) ix cw'
                end
            end
    in
      if sz = 0 then []
      else recurse 0 [] 5 0 0 (i2w 0)
    end

fun encode s =
    String.implode (map (fn i => Vector.sub(encoding_table, i)) (encode0 s))

fun decode s =
    let
      val sz = String.size s
      val i2ww = Word.fromInt
      fun ix2w i =
          let val i0 = Char.ord (String.sub(s,i))
          in
            if i0 > 53 then Word8.fromInt (i0 - 65)
            else Word8.fromInt (i0 - 22)
          end
      fun recurse A ix cw numbitsread tgt =
          if numbitsread < 3 then
            recurse A (ix + 1) (ix2w (ix + 1)) (numbitsread+5)
                    (tgt + Word8.toInt(Word8.<<(c, i2ww (3 - numbitsread))))
          else if numbitsread = 3 then
            recurse ((tgt + Word8.toInt c) :: A) (ix + 1) (ix2w (ix + 1)) 0 0
          else
            let (chunk1, chunk2) = gethibits tgt (11 - numbitsread) c
            in
              recurse (chunk1 :: A) (ix + 1) (ix2w (ix + 1)) (numbitsread - 3)
                      Word8.<<(chunk2

*)

fun toInt df b s =
    let
      val sz = String.size s
      fun recurse A ix =
          if ix < sz then
            let
              val ix' = ix + 1
              open Arbint
            in
              recurse (A * b + fromInt (df (String.sub(s,ix))) + one) ix'
            end
          else A
    in
      recurse Arbint.zero 0
    end

fun fromInt df b i =
    let
      fun recurse A j =
          if j = Arbint.zero then A
          else
            let val d0 = Arbint.mod(j,b)
                val d = if d0 = Arbint.zero then b else d0
            in
              recurse ((Arbint.toInt d - 1)::A) (Arbint.div(Arbint.-(j,d),b))
          end
    in
      String.implode (map df (recurse [] i))
    end

val ai = Arbint.fromInt
val encode = fromInt d2c (ai 32) o toInt Char.ord (ai 256)
val decode = fromInt Char.chr (ai 256) o toInt c2d (ai 32) o
             CharVector.map Char.toUpper


end (* struct *)
