(* -------------------------------------------------------------------------
   BitsN
   ------------------------------------------------------------------------- *)

structure BitsN :> BitsN =
struct
   infix 8 >> >>+ << #>> #<< >>^ >>+^ <<^ #>>^ #<<^
   infix 7 &&
   infix 6 || ??
   infix 5 @@

   datatype nbit = B of (int * Nat.nat)

   fun checkSize s = if s = Nat.zero then raise Fail "Size must be >= 1." else s
   fun size (B (_, s)) = s

   fun dim s = IntInf.<< (1, Word.fromInt s)
   fun modDim s n = IntInf.andb (n, dim s - 1)

   fun UINT_MAX s = B (dim s - 1, checkSize s)
   fun INT_MIN s = B (dim (s - 1), checkSize s)
   fun INT_MAX s = B (dim (s - 1) - 1, checkSize s)
   fun zero s = B (0, checkSize s)
   fun one s = B (1, checkSize s)

   fun fromInt (n, s) = B (modDim s n, checkSize s)
   fun fromNat (n, s) = fromInt (Nat.toInt n, s)
   fun toNat (B (i, _)) = Nat.fromInt i
   val toUInt = Nat.toInt o toNat
   fun fromBitstring (b, s) = fromNat (Bitstring.toNat b, s)
   fun toBitstring (B (n, s)) =
      Bitstring.setSize (Nat.toInt s) (Bitstring.fromInt n)
   fun toString (B (i, _)) = Int.toString i
   fun toBinString (B (i, _)) = IntExtra.toBinString i
   fun toHexString (B (i, _)) = IntExtra.toHexString i

   fun rep_error n s =
      raise Fail ("Literal " ^ n ^ " cannot be represented with " ^
                  Nat.toString s ^ " bit" ^ (if s = Nat.one then "" else "s"))

   fun fromBool s = fn true => one s | false => zero s
   val fromBit = fromBool 1

   fun fromNatCheck (x as (n, s)) =
      let
         val w = fromNat x
      in
         toNat w = n orelse rep_error (Nat.toString n) s
         ; w
      end

   fun resize i w = fromNat (toNat w, Nat.fromInt i)

   fun fromLit (s, i) =
      Option.map
         (fn n =>
            let
               val j = Nat.fromInt i
               val w = fromNat (n, j)
            in
               toNat w = n orelse rep_error ("0" ^ s) j
               ; w
            end) (Nat.fromLit s)

   fun bits (B (i, s), h, l) =
      let
         val w = h + 1 - l
      in
         0 < w andalso 0 <= l andalso h < s orelse
         raise Fail ("bits invalid: (" ^ Nat.toString s ^ "-bit)<" ^
                     Nat.toString h ^ ":" ^ Nat.toString l ^ ">")
         ; B (modDim w (IntInf.~>> (i, Word.fromInt l)), w)
      end

   fun bit (a, n) = bits (a, n, n) = B (1, 1)
   fun lsb (B (a, _)) = IntInf.andb (a, 1) = 1
   fun msb a = bit (a, Nat.- (size a, Nat.one))

   fun neg (B (a, s)) = B (modDim s (Int.- (dim s, a)), s)

   fun toInt a = if msb a then Int.~ (toUInt (neg a)) else toUInt a

   fun compare (B (a, b), B (c, d)) =
      L3.pairCompare (Nat.compare, Int.compare) ((b, a), (d, c))

   fun signedCompare (x as B (_, a), y as B (_, b)) =
      L3.pairCompare (Nat.compare, Int.compare) ((a, toInt x), (b, toInt y))

   fun fromBaseString (from, nfrom) (v: string, s) =
      case from v of
         SOME i =>
            let
               val w = fromInt (i, s)
               val _ = if i < 0
                          then toInt w = i orelse rep_error (Int.toString i) s
                       else let
                               val n = Option.valOf (nfrom v)
                            in
                               toNat w = n orelse rep_error (Nat.toString n) s
                            end
            in
               SOME w
            end
       | NONE => NONE

   val fromString = fromBaseString (IntExtra.fromString, Nat.fromString)
   val fromBinString =
      fromBaseString (IntExtra.fromBinString, Nat.fromBinString)
   val fromHexString =
      fromBaseString (IntExtra.fromHexString, Nat.fromHexString)

   fun toList (B (a, s)) =
      let
         fun iter (l, n, b) =
            if b <= 0 orelse n = 0
               then List.tabulate (b, fn _ => false) @ l
            else let
                    val (r, v) = IntInf.divMod (n, 2)
                 in
                    iter ((v = 1) :: l, r, b - 1)
                 end
      in
         iter ([], a, Nat.toInt s)
      end

   fun fromList l =
      let
         val s = List.length l
         val _ = 0 < s orelse raise Fail ("List must be non-empty")
         fun iter a =
            fn [] => a
             | (h::t) => iter (2 * a + (if h then 1 else 0)) t
      in
         B (iter 0 l, Nat.fromInt s)
      end

   fun modify (f: Nat.nat * bool -> bool, a) =
      let
         val s = Nat.toInt (size a)
         val l = toList a
         val n = List.tabulate (s, fn i => Nat.fromInt (s - 1 - i))
         val z = ListPair.zip (n, l)
      in
         fromList (List.map f z)
      end

   fun tabulate (s, f: Nat.nat -> bool) =
      let
         val s = Nat.toInt s
      in
         fromList (List.tabulate (s, fn i => f (Nat.fromInt (s - 1 - i))))
      end
      handle Fail _ => raise Fail "tabulate"

   val reverse = fromList o List.rev o toList

   fun log2 (B (a, s)) = B (IntInf.log2 a, s)

   fun zeroExtend s2 (B (n, s1)) =
      if Nat.<= (s1, s2)
         then B (n, s2)
      else raise Fail ("Bad zeroExtend: `" ^ Nat.toString s1 ^ " -> `" ^
                       Nat.toString s2)

   fun signExtend s2 (a as B (n, s1)) =
      if Nat.<= (s1, s2)
         then B (Int.+ (if msb a then (Int.- (dim s2, dim s1)) else 0, n), s2)
      else raise Fail ("Bad signExtend: `" ^ Nat.toString s1 ^ " -> `" ^
                       Nat.toString s2)

   fun op @@ (a as B (v1, s1), b as B (v2, s2)) =
      B (IntInf.orb (IntInf.<< (v1, Word.fromInt s2), v2), Int.+ (s1, s2))

   fun concat [] = raise Fail "concat: empty"
     | concat l = let val r = List.rev l in List.foldl (op @@) (hd r) (tl r) end

   fun replicate (a as B (_, s1), n) =
      let
         open Nat
         val _ = zero < n orelse raise Fail "replicate must be > 0-bit"
         val l = toList a
         val m = pred s1
      in
         tabulate (s1 * n, fn i => List.nth (l, toInt (m - i mod s1)))
      end

   fun resize_replicate i = resize i o replicate

   fun bitFieldInsert (x, y, h, l) =
      modify (fn (i, b) =>
                 if Nat.<= (l, i) andalso Nat.<= (i, h)
                    then bit (y, Nat.- (i, l))
                 else b, x)

   fun checkSameSize opn =
      let
         val err = opn ^ " : Bit widths do not match: "
      in
         fn (s1, s2) =>
           s1 = s2 orelse
           raise Fail (err ^ Nat.toString s1 ^ " <> " ^ Nat.toString s2)
      end

   fun op <+ (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "<+" (s1, s2); Int.< (v1, v2) )

   fun op <=+ (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "<=+" (s1, s2); Int.<= (v1, v2) )

   fun op >+ (B (v1, s1), B (v2, s2)) =
      ( checkSameSize ">+" (s1, s2); Int.> (v1, v2) )

   fun op >=+ (B (v1, s1), B (v2, s2)) =
      ( checkSameSize ">=+" (s1, s2); Int.>= (v1, v2) )

   fun op < (w1 as B (_, s1), w2 as B (_, s2)) =
      ( checkSameSize "<" (s1, s2); Int.< (toInt w1, toInt w2) )

   fun op <= (w1 as B (_, s1), w2 as B (_, s2)) =
      ( checkSameSize "<=" (s1, s2); Int.<= (toInt w1, toInt w2) )

   fun op > (w1 as B (_, s1), w2 as B (_, s2)) =
      ( checkSameSize ">" (s1, s2); Int.> (toInt w1, toInt w2) )

   fun op >= (w1 as B (_, s1), w2 as B (_, s2)) =
      ( checkSameSize ">=" (s1, s2); Int.>= (toInt w1, toInt w2) )

   fun op && (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "&&" (s1, s2); B (IntInf.andb (v1, v2), s1) )

   fun op || (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "||" (s1, s2); B (IntInf.orb (v1, v2), s1) )

   fun op ?? (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "??" (s1, s2); B (IntInf.xorb (v1, v2), s1) )

   fun op div (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "div" (s1, s2); B (Int.div (v1, v2), s1) )

   fun op mod (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "mod" (s1, s2); B (Int.mod (v1, v2), s1) )

   fun op quot (a as B (_, s1), b as B (_, s2)) =
      ( checkSameSize "quot" (s1, s2)
      ; fromInt (Int.quot (toInt a, toInt b), s1)
      )

   fun op rem (a as B (_, s1), b as B (_, s2)) =
      ( checkSameSize "quot" (s1, s2)
      ; fromInt (Int.rem (toInt a, toInt b), s1)
      )

   fun min (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "min" (s1, s2); B (Int.min (v1, v2), s1) )

   fun max (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "max" (s1, s2); B (Int.max (v1, v2), s1) )

   fun smin (w1 as B (_, s1), w2 as B (_, s2)) =
      ( checkSameSize "smin" (s1, s2)
      ; fromInt (Int.min (toInt w1, toInt w2), s1)
      )

   fun smax (w1 as B (_, s1), w2 as B (_, s2)) =
      ( checkSameSize "smax" (s1, s2)
      ; fromInt (Int.max (toInt w1, toInt w2), s1)
      )

   fun op << (B (v, s), n) =
      B (modDim s (IntInf.<< (v, Word.fromInt (Int.min (n, s)))), s)

   fun op >>+ (B (v, s), n) = B (IntInf.~>> (v, Word.fromInt n), s)

   fun op >> (a as B (_, s), n) =
      if msb a
         then fromInt (dim s - dim (s - Int.min (n, s)), s) || a >>+ n
      else a >>+ n

   fun op #>> (a as B (_, s), n) =
      let
         open Nat
         val x = n mod s
      in
         if x = 0 then a else bits (a, pred x, zero) @@ bits (a, pred s, x)
      end

   fun op #<< (a as B (_, s), n) = let open Nat in a #>> (s - n mod s) end

   fun op <<^ (w as B (_, s1), v as B (_, s2)) =
      ( checkSameSize "<<^" (s1, s2); w << toNat v )

   fun op >>^ (w as B (_, s1), v as B (_, s2)) =
      ( checkSameSize ">>^" (s1, s2); w >> toNat v )

   fun op >>+^ (w as B (_, s1), v as B (_, s2)) =
      ( checkSameSize ">>+^" (s1, s2); w >>+ toNat v )

   fun op #>>^ (w as B (_, s1), v as B (_, s2)) =
      ( checkSameSize "#>>^" (s1, s2); w #>> toNat v )

   fun op #<<^ (w as B (_, s1), v as B (_, s2)) =
      ( checkSameSize "#<<^" (s1, s2); w #<< toNat v )

   fun op * (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "*" (s1, s2); B (modDim s1 (Int.* (v1, v2)), s1) )

   fun op + (B (v1, s1), B (v2, s2)) =
      ( checkSameSize "+" (s1, s2); B (modDim s1 (Int.+ (v1, v2)), s1) )

   fun op ~ (B (a, s)) = B (modDim s (IntInf.notb a), s)

   fun abs a = if a < B (0, size a) then neg a else a

   fun op - (a, b) = a + neg b

end (* structure BitsN *)
