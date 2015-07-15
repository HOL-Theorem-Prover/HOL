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

   fun size (B (_, s)) = s

   fun dim s = IntInf.<< (1, Word.fromInt s)
   fun pdim s = dim s - 1
   fun modDim s n = IntInf.andb (n, pdim s)

   fun UINT_MAX s = B (pdim s, s)
   fun INT_MIN s = B (dim (s - 1), s)
   fun INT_MAX s = B (pdim (s - 1), s)
   fun zero s = B (0, s)
   fun one s = B (1, s)

   fun fromInt (n, s) = B (modDim s n, s)
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

   fun bits (h,l) =
      let
         val w = h + 1 - l
         val l =  Word.fromInt l
         val mask = pdim w
      in
         fn B (i, _) => B (IntInf.andb (mask,IntInf.~>> (i, l)), w)
      end

   fun bit (B (a, _), n) = Int.rem (IntInf.~>> (a, Word.fromInt n), 2) = 1
   fun lsb (B (a, _)) = Int.rem (a, 2) = 1
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

   local
      fun iter (l, n, b) =
         if n = 0 orelse b <= 0
            then Bitstring.zero b @ l
         else let
                 val (r, v) = IntInf.quotRem (n, 2)
              in
                 iter ((v = 1) :: l, r, b - 1)
              end
   in
      fun toList (B (a, s)) = iter ([], a, Nat.toInt s)
   end

   local
      fun iter a =
         fn [] => a
          | (false::t) => iter (IntInf.<< (a, 0w1)) t
          | (true::t) => iter (IntInf.orb (IntInf.<< (a, 0w1), 1)) t
   in
      fun fromList l = B (iter 0 l, Nat.fromInt (List.length l))
   end

   fun modify (f: Nat.nat * bool -> bool, a) =
      fromList
         (#1 (List.foldr (fn (b, (l, i)) => (f (i, b) :: l, i + 1)) ([], 0)
                (toList a)))

   fun tabulate (s, f: Nat.nat -> bool) =
      let
         val s = Nat.toInt s
      in
         fromList (List.tabulate (s, fn i => f (Nat.fromInt (s - 1 - i))))
      end
      handle Fail _ => raise Fail "tabulate"

   val reverse = fromList o List.rev o toList

   fun log2 (B (a, s)) = B (IntInf.log2 a, s)

   fun zeroExtend s (B (n, _)) = B (n, s)

   fun signExtend s2 (a as B (n, s1)) =
      B (Int.+ (if msb a then (Int.- (dim s2, dim s1)) else 0, n), s2)

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

   fun bitFieldInsert (h,l) =
      let
         val dl = dim l
         val dh = dim (h + 1)
         val wl = Word.fromInt l
      in
         fn (B (v, s), B (w, _)) =>
            let
               val mask = Int.max (Int.min (dim s, dh) - dl, 0)
               val w' = IntInf.<< (w, wl)
            in
               B (IntInf.orb (IntInf.andb (IntInf.notb mask, v),
                              IntInf.andb (mask, w')), s)
            end
      end

   fun op <+  (B (v1, _), B (v2, _)) = Int.< (v1, v2)
   fun op <=+ (B (v1, _), B (v2, _)) = Int.<= (v1, v2)
   fun op >+  (B (v1, _), B (v2, _)) = Int.> (v1, v2)
   fun op >=+ (B (v1, _), B (v2, _)) = Int.>= (v1, v2)

   fun op <  (w1, w2) = Int.< (toInt w1, toInt w2)
   fun op <= (w1, w2) = Int.<= (toInt w1, toInt w2)
   fun op >  (w1, w2) = Int.> (toInt w1, toInt w2)
   fun op >= (w1, w2) = Int.>= (toInt w1, toInt w2)

   fun op && (B (v1, _), B (v2, s)) = B (IntInf.andb (v1, v2), s)
   fun op || (B (v1, _), B (v2, s)) = B (IntInf.orb (v1, v2), s)
   fun op ?? (B (v1, _), B (v2, s)) = B (IntInf.xorb (v1, v2), s)
   fun op div (B (v1, _), B (v2, s)) = B (Int.div (v1, v2), s)
   fun op mod (B (v1, _), B (v2, s)) = B (Int.mod (v1, v2), s)

   fun op quot (a, b as B (_, s)) = fromInt (Int.quot (toInt a, toInt b), s)
   fun op rem (a, b as B (_, s)) = fromInt (Int.rem (toInt a, toInt b), s)

   fun min (B (v1, _), B (v2, s)) = B (Int.min (v1, v2), s)
   fun max (B (v1, _), B (v2, s)) = B (Int.max (v1, v2), s)

   fun smin (w1, w2 as B (_, s)) = fromInt (Int.min (toInt w1, toInt w2), s)
   fun smax (w1, w2 as B (_, s)) = fromInt (Int.max (toInt w1, toInt w2), s)

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
         if x = 0 then a else bits (pred x, zero) a @@ bits (pred s, x) a
      end

   fun op #<< (a as B (_, s), n) = let open Nat in a #>> (s - n mod s) end

   fun op <<^ (w, v) = w << toNat v
   fun op >>^ (w, v) = w >> toNat v
   fun op >>+^ (w, v) = w >>+ toNat v
   fun op #>>^ (w, v) = w #>> toNat v
   fun op #<<^ (w, v) = w #<< toNat v

   fun op * (B (v1, _), B (v2, s)) = B (modDim s (Int.* (v1, v2)), s)
   fun op + (B (v1, _), B (v2, s)) = B (modDim s (Int.+ (v1, v2)), s)

   fun op ~ (B (a, s)) = B (modDim s (IntInf.notb a), s)

   fun abs a = if a < B (0, size a) then neg a else a

   fun op - (a, b) = a + neg b

end (* structure BitsN *)
