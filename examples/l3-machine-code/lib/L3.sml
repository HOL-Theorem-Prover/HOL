(* -------------------------------------------------------------------------
   L3
   ------------------------------------------------------------------------- *)

structure L3 :> L3 =
struct

   fun fst (x, _) = x
   fun snd (_, x) = x
   fun K x _ = x
   fun uncurry f (x,y) = f x y
   fun equal x y = (x = y)

   val lowercase = String.map Char.toLower
   val uppercase = String.map Char.toUpper

   fun prefix (c, s) = String.str c ^ s
   fun strHd s = String.sub (s, 0)
   fun strTl s = String.extract (s, 1, NONE)

   fun update m i e = fn x => if x = i then e else m x

   fun for (i, j, a) =
      ( a i
      ; if i = j
           then ()
        else for (if Nat.< (i, j) then Nat.suc i else Nat.pred i, j, a)
      )

   fun pairCompare (cmp1, cmp2) ((a: 'a, b: 'b), (c: 'a, d :'b)) =
      case cmp1 (a, c) of
         General.EQUAL => cmp2 (b, d)
       | x => x

   fun listCompare cmp =
      let
         fun compare ([], _) = General.EQUAL
           | compare (_, []) = raise Fail "list_compare"
           | compare (h1 :: t1, h2 :: t2) =
                case cmp (h1, h2) of
                   General.EQUAL => compare (t1, t2)
                 | x => x
      in
         fn (l1, l2) =>
            pairCompare (Int.compare, compare)
               ((List.length l1, l1), (List.length l2, l2))
      end

   fun mem (i, l) = List.exists (fn x => x = i) l

   local
      fun insert i l = if mem (i, l) then l else i :: l
   in
      fun mkSet [] = []
        | mkSet (h :: t) = insert h (mkSet t)
   end

   local
      fun liftSubstring (f, s) =
         let
            val (a, b) = f (Substring.full s)
         in
            (Substring.string a, Substring.string b)
         end
   in
      fun splitl (p, s) = liftSubstring (Substring.splitl p, s)
      fun splitr (p, s) = liftSubstring (Substring.splitr p, s)
   end

   fun padLeft (e, (n, l)) =
      List.tabulate (Nat.- (n, List.length l), fn _ => e) @ l
   fun padRight (e, (n, l)) =
      l @ List.tabulate (Nat.- (n, List.length l), fn _ => e)
   fun padLeftString (e, (n, l)) = StringCvt.padLeft e n l
   fun padRightString (e, (n, l)) = StringCvt.padRight e n l
   val revString = String.implode o List.rev o String.explode

end (* structure L3 *)
