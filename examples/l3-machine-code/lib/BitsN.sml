(* -------------------------------------------------------------------------
   BitsN
   ------------------------------------------------------------------------- *)

structure BitsN :> BitsN =
struct
   infix 8 >> >>+ << #>> #<< >>^ >>+^ <<^ #>>^ #<<^
   infix 7 &&
   infix 6 || ??
   infix 5 @@

   datatype nbit = B of (IntInf.int * Nat.nat)

   fun size (B (_, s)) = s
   val nativeSize = Nat.toNativeInt o size

   fun dim s = IntInf.<< (1, Word.fromLargeInt s)
   fun mask s = dim s - 1
   fun BV (n, s) = B (IntInf.andb (n, mask s), s)

   fun zero s = B (0, s)
   fun one s = B (1, s)

   val fromInt = BV
   fun fromNativeInt (i, j) = BV (IntInf.fromInt i, Nat.fromNativeInt j)
   fun fromNat (n, s) = fromInt (Nat.toInt n, s)
   fun toNat (B (i, _)) = Nat.fromInt i
   val toUInt = Nat.toInt o toNat
   fun fromBitstring (b, s) = fromNat (Bitstring.toNat b, s)
   fun toBitstring (B (n, s)) =
      Bitstring.setSize (Nat.toNativeInt s) (Bitstring.fromInt n)
   fun toString (B (i, _)) = IntInf.toString i
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

   val allow_resize = ref true

   fun resize i (w as B (_, j)) =
     let
       val i' = Nat.fromNativeInt i
     in
       if i' = j
         then w
       else if !allow_resize
         then fromNat (toNat w, i')
       else raise Fail ("Tried to resize bits(" ^ Nat.toString j ^
                        ") to bits(" ^ Int.toString i ^ ")")
     end

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

   fun bits (h, l) =
      let
         val w = Nat.- (Nat.suc h, l)
         val l =  Word.fromLargeInt l
         val m = mask w
      in
         fn B (i, _) => B (IntInf.andb (m, IntInf.~>> (i, l)), w)
      end

   fun bit (B (a, _), n) =
      IntInf.rem (IntInf.~>> (a, Word.fromLargeInt n), 2) = 1
   fun lsb (B (a, _)) = IntInf.rem (a, 2) = 1
   fun msb (a as B (_, s)) = bit (a, Nat.- (s, Nat.one))

   fun neg (B (a, s)) = BV (IntInf.~ a, s)

   fun toInt a = if msb a then IntInf.~ (toUInt (neg a)) else toUInt a

   fun compare (B (a, b), B (c, d)) =
      L3.pairCompare (Nat.compare, IntInf.compare) ((b, a), (d, c))

   fun signedCompare (x as B (_, a), y as B (_, b)) =
      L3.pairCompare (Nat.compare, IntInf.compare) ((a, toInt x), (b, toInt y))

   fun fromBaseString (from, nfrom) (v: string, s) =
      case from v of
         SOME i =>
            let
               val w = fromInt (i, s)
               val _ = if i < 0
                         then toInt w = i orelse rep_error (IntInf.toString i) s
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
      fun fromList l = B (iter 0 l, Nat.fromNativeInt (List.length l))
   end

   fun tabulate (s, f: Nat.nat -> bool) =
      let
         val s = Nat.toNativeInt s
      in
         fromList (List.tabulate (s, fn i => f (Nat.fromNativeInt (s - 1 - i))))
      end
      handle Fail _ => raise Fail "tabulate"

   val reverse = fromList o List.rev o toList

   fun log2 (B (a, s)) = B (IntInf.fromInt (IntInf.log2 a), s)

   fun zeroExtend s (B (n, _)) = B (n, s)

   fun signExtend s2 (a as B (n, s1)) =
      B (IntInf.+ (if msb a then (IntInf.- (dim s2, dim s1)) else 0, n), s2)

   fun op @@ (a as B (v1, s1), b as B (v2, s2)) =
      B (IntInf.orb (IntInf.<< (v1, Word.fromLargeInt s2), v2),
         IntInf.+ (s1, s2))

   fun concat [] = raise Fail "concat: empty"
     | concat l = let val r = List.rev l in List.foldl (op @@) (hd r) (tl r) end

   fun replicate (a, n) =
     List.foldl (op @@) a (List.tabulate (Nat.toNativeInt n - 1, fn _ => a))
     handle General.Size => raise Fail "replicate must be > 0-bit"

   fun resize_replicate i = resize i o replicate

   fun bitFieldInsert (h, l) =
      let
         val dl = dim l
         val dh = dim (h + 1)
         val wl = Word.fromLargeInt l
      in
         fn (B (v, s), B (w, _)) =>
            let
               val mask = IntInf.max (IntInf.min (dim s, dh) - dl, 0)
               val w' = IntInf.<< (w, wl)
            in
               B (IntInf.orb (IntInf.andb (IntInf.notb mask, v),
                              IntInf.andb (mask, w')), s)
            end
      end

   fun op <+  (B (v1, _), B (v2, _)) = IntInf.< (v1, v2)
   fun op <=+ (B (v1, _), B (v2, _)) = IntInf.<= (v1, v2)
   fun op >+  (B (v1, _), B (v2, _)) = IntInf.> (v1, v2)
   fun op >=+ (B (v1, _), B (v2, _)) = IntInf.>= (v1, v2)

   fun op <  (w1, w2) = IntInf.< (toInt w1, toInt w2)
   fun op <= (w1, w2) = IntInf.<= (toInt w1, toInt w2)
   fun op >  (w1, w2) = IntInf.> (toInt w1, toInt w2)
   fun op >= (w1, w2) = IntInf.>= (toInt w1, toInt w2)

   fun op && (B (v1, _), B (v2, s)) = B (IntInf.andb (v1, v2), s)
   fun op || (B (v1, _), B (v2, s)) = B (IntInf.orb (v1, v2), s)
   fun op ?? (B (v1, _), B (v2, s)) = B (IntInf.xorb (v1, v2), s)
   fun op div (B (v1, _), B (v2, s)) = B (IntInf.div (v1, v2), s)
   fun op mod (B (v1, _), B (v2, s)) = B (IntInf.mod (v1, v2), s)

   fun op quot (a, b as B (_, s)) = fromInt (IntInf.quot (toInt a, toInt b), s)
   fun op rem (a, b as B (_, s)) = fromInt (IntInf.rem (toInt a, toInt b), s)

   fun min (B (v1, _), B (v2, s)) = B (IntInf.min (v1, v2), s)
   fun max (B (v1, _), B (v2, s)) = B (IntInf.max (v1, v2), s)

   fun smin (w1, w2 as B (_, s)) = fromInt (IntInf.min (toInt w1, toInt w2), s)
   fun smax (w1, w2 as B (_, s)) = fromInt (IntInf.max (toInt w1, toInt w2), s)

   fun op << (B (v, s), n) =
      BV (IntInf.<< (v, Word.fromLargeInt (IntInf.min (n, s))), s)

   fun op >>+ (B (v, s), n) = B (IntInf.~>> (v, Word.fromLargeInt n), s)

   fun op >> (a as B (_, s), n) =
      if msb a
         then B (dim s - dim (s - IntInf.min (n, s)), s) || a >>+ n
      else a >>+ n

   fun op #>> (a as B (_, s), n) =
      let
         open Nat
         val x = n mod s
      in
         if x = 0 then a else a << (s - x) || a >>+ x
      end

   fun op #<< (a as B (_, s), n) = let open Nat in a #>> (s - n mod s) end

   fun op <<^ (w, v) = w << toNat v
   fun op >>^ (w, v) = w >> toNat v
   fun op >>+^ (w, v) = w >>+ toNat v
   fun op #>>^ (w, v) = w #>> toNat v
   fun op #<<^ (w, v) = w #<< toNat v

   fun op * (B (v1, _), B (v2, s)) = BV (IntInf.* (v1, v2), s)
   fun op + (B (v1, _), B (v2, s)) = BV (IntInf.+ (v1, v2), s)
   fun op - (B (v1, _), B (v2, s)) = BV (IntInf.- (v1, v2), s)

   fun op ~ (B (a, s)) = BV (IntInf.notb a, s)

   fun abs a = if msb a then neg a else a

end (* structure BitsN *)
