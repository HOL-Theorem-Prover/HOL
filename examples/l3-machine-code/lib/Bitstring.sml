(* -------------------------------------------------------------------------
   Bitstring
   ------------------------------------------------------------------------- *)

structure Bitstring :> Bitstring =
struct

   infix 8 >>+

   type bitstring = bool list

   val boolCompare =
      fn (false, true) => General.LESS
       | (true, false) => General.GREATER
       | _ => General.EQUAL

   val compare = L3.listCompare boolCompare

   fun zero n = List.tabulate (Nat.toNativeInt n, fn _ => false)
   fun one n = if n < 1 then [] else zero (n - 1) @ [true]

   val size: bitstring -> Nat.nat = Nat.fromNativeInt o List.length

   local
      fun iter a i =
         if i <= 0 then a
         else let
                  val (q, r) = IntInf.quotRem (i, 2)
              in
                  iter ((r = 1) :: a) q
              end
   in
      fun fromInt i =
         if i < 0
            then raise Domain
         else if i = 0
            then [false]
         else iter [] i
   end

   val fromNativeInt = fromInt o IntInf.fromInt

   val fromNat = fromInt o Nat.toInt

   val toInt = List.foldl (fn (true, v) => 2 * v + 1 | (false, v) => 2 * v) 0

   val toNat = Nat.fromInt o toInt
   val toNativeInt = IntInf.toInt o toInt

   val fromBool = fn x => [x]

   fun fromBinString s =
      (SOME o List.map (fn #"0" => false | #"1" => true | _ => raise Domain) o
       String.explode) s
      handle Domain => NONE

   fun fromDecString s =
      Option.map fromNat (Nat.fromString s) handle Domain => NONE

   val hexBits =
      fn #"0" => [false, false, false, false]
       | #"1" => [false, false, false, true]
       | #"2" => [false, false, true, false]
       | #"3" => [false, false, true, true]
       | #"4" => [false, true, false, false]
       | #"5" => [false, true, false, true]
       | #"6" => [false, true, true, false]
       | #"7" => [false, true, true, true]
       | #"8" => [true, false, false, false]
       | #"9" => [true, false, false, true]
       | #"a" => [true, false, true, false]
       | #"b" => [true, false, true, true]
       | #"c" => [true, true, false, false]
       | #"d" => [true, true, false, true]
       | #"e" => [true, true, true, false]
       | #"f" => [true, true, true, true]
       | _ => raise Domain

   fun fromHexString s =
      (SOME o List.concat o List.map (hexBits o Char.toLower) o
       String.explode) s
      handle Domain => NONE

   fun fromLit s =
      let
         val v = String.extract (s, 1, NONE)
      in
         case String.sub (s, 0) of
            #"d" => fromDecString v
          | #"b" => fromBinString v
          | #"x" => fromHexString v
          | _ => NONE
      end

   val toBinString = String.implode o List.map (fn false => #"0" | true => #"1")

   val toDecString = Nat.toString o toNat

   val hexBits =
      fn [false, false, false, false] => #"0"
       | [false, false, false, true]  => #"1"
       | [false, false, true, false]  => #"2"
       | [false, false, true, true]   => #"3"
       | [false, true, false, false]  => #"4"
       | [false, true, false, true]   => #"5"
       | [false, true, true, false]   => #"6"
       | [false, true, true, true]    => #"7"
       | [true, false, false, false]  => #"8"
       | [true, false, false, true]   => #"9"
       | [true, false, true, false]   => #"a"
       | [true, false, true, true]    => #"b"
       | [true, true, false, false]   => #"c"
       | [true, true, false, true]    => #"d"
       | [true, true, true, false]    => #"e"
       | [true, true, true, true]     => #"f"
       | _ => raise Domain

   val toHexString =
      let
         fun iter a =
            fn [] => String.implode (List.rev a)
             | l => iter (hexBits (List.take (l, 4)) :: a) (List.drop (l, 4))
      in
         fn l =>
           let
              val n = 4 - List.length l mod 4
              val p = if n = 4 then [] else List.tabulate (n, fn _ => false)
           in
              iter [] (p @ l)
           end
      end

   fun toList l = l
   fun fromList l = l

   fun op << (l, s) = l @ zero s

   fun op >>+ (l, s) = List.take (l, List.length l - Nat.toNativeInt s)
                       handle General.Subscript => []

   fun op #>> (l, s) =
      let
         val n = List.length l
         val x = n - (IntInf.toInt s) mod n
      in
         List.drop (l, x) @ List.take (l, x)
      end

   fun setSize s l =
      let
         val n = List.length l
      in
         if n < s
           then zero (Nat.fromNativeInt (s - n)) @ l
         else List.drop (l, n - s)
      end

   fun bits (h, l) =
      let
         val s = Nat.- (Nat.suc h, l)
      in
         fn b =>
           if s = Nat.zero then [false]
           else setSize (Nat.toNativeInt s) (b >>+ l)
      end

   fun bit (a, n) = bits (n, n) a = [true]

   fun modify (f: Nat.nat * bool -> bool) a =
      #1 (List.foldr (fn (b, (l, i)) => (f (i, b) :: l, i + 1)) ([], 0) a)

   fun bitFieldInsert (h,l) (x, y) =
      modify (fn (i, b) => if Nat.<= (l, i) andalso Nat.<= (i, h)
                              then bit (y, Nat.- (i, l))
                           else b) x

   fun maxLength (l1, l2) = Int.max (List.length l1, List.length l2)

   fun log2plus1 i = if i = 0 then 1 else IntInf.log2 i + 1

   fun op + (l1, l2) =
      let
         val r = IntInf.+ (toInt l1, toInt l2)
      in
         setSize (Int.max (log2plus1 r, maxLength (l1, l2))) (fromInt r)
      end

   fun bitwise f =
      let
         val mapf = List.map f
      in
         fn (l1, l2) =>
            let
               val m = maxLength (l1, l2)
            in
               mapf (ListPair.zip (setSize m l1, setSize m l2))
            end
      end

   val op || = bitwise (fn (a, b) => a orelse b)
   val op && = bitwise (fn (a, b) => a andalso b)
   val op ?? = bitwise (fn (a, b) => a = b)

   val op @@ = op @

   fun replicate (a, n) =
      if n = Nat.zero
         then zero n
      else List.foldl (op @@) a
             (List.tabulate (Nat.toNativeInt n - 1, fn _ => a))

end (* structure Bitstring *)
