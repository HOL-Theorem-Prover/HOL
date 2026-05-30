structure BloomApprox :> BloomApprox =
struct

open HolKernel

type t = Word64.word

val empty : t = 0w0

local
  val P : Word64.word = 0wx9E3779B185EBCA87  (* splitmix-style mixer *)
  fun mix (a : Word64.word, b : Word64.word) : Word64.word =
      let val a' = Word64.* (Word64.xorb (a, Word64.>> (a, 0w30)), P)
      in Word64.+ (a', b) end
  fun strhash s =
      CharVector.foldl
        (fn (c, h) => mix (h, Word64.fromInt (Char.ord c)))
        (0w0 : Word64.word) s
  fun term_hash t =
      if is_var t then
        let val (n, _) = dest_var t in strhash n end
      else if is_const t then
        let val {Name, Thy, ...} = dest_thy_const t
        in mix (strhash Thy, strhash Name) end
      else if is_comb t then
        mix (term_hash (rator t), term_hash (rand t))
      else if is_abs t then
        mix (Word64.<< (term_hash (bvar t), 0w3), term_hash (body t))
      else 0w0 : Word64.word
in
  (* Three 6-bit positions in the 64-bit filter per term. *)
  fun from_term t =
      let
        val h    = term_hash t
        val one  = 0w1  : Word64.word
        val mask = 0wx3F : Word64.word
        fun bit shift =
            let val pos = Word64.toInt
                            (Word64.andb (Word64.>> (h, shift), mask))
            in Word64.<< (one, Word.fromInt pos) end
      in
        Word64.orb (Word64.orb (bit 0w0, bit 0w6), bit 0w16)
      end
end

fun union (a : t, b : t) : t = Word64.orb (a, b)

fun maybeSubset (a : t, b : t) : bool =
    Word64.andb (a, Word64.notb b) = (0w0 : Word64.word)

end
