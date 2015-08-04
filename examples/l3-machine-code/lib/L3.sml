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

   fun foreach ([], _) = ()
     | foreach (h :: t, a) = (a h; foreach (t, a))

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

   fun listUpdate (e, (i, [])) = []
     | listUpdate (e, (0, _::l)) = e::l
     | listUpdate (e, (n, h::l)) = h :: listUpdate (e, (n - 1, l))

   fun padLeft (e, (n, l)) =
      List.tabulate (Nat.- (n, List.length l), fn _ => e) @ l
   fun padRight (e, (n, l)) =
      l @ List.tabulate (Nat.- (n, List.length l), fn _ => e)
   fun padLeftString (e, (n, l)) = StringCvt.padLeft e n l
   fun padRightString (e, (n, l)) = StringCvt.padRight e n l
   fun takeString (n, s) = String.extract (s, 0, SOME n)
   fun dropString (n, s) = String.extract (s, n, NONE)
   val removeDuplicatesString = String.implode o Set.mk o String.explode
   val revString = String.implode o List.rev o String.explode
   fun stringToChar s =
      if String.size s = 1 then String.sub (s, 0) else raise Domain
   fun memString (c, s) = String.isSubstring (String.str c) s
   fun stringUpdate (e, (i, s)) =
      String.implode (listUpdate (e, (i, String.explode s)))

   local
      fun trans P (s, r) =
         String.translate
            (fn d => let val x = String.str d in if P x r then "" else x end) s
   in
      val removeExceptString =
         trans (fn x => fn r => not (String.isSubstring x r))
      val removeString = trans String.isSubstring
   end

   fun revLookup eq (e, l) =
      let
         fun loop i =
            fn [] => NONE
             | h :: t => if eq e h then SOME i else loop (i + 1) t
      in
         loop 0 l
      end

   fun remove (l1, l2) = List.filter (fn x => not (Set.mem (x, l2))) l1
   fun swap (n, l) = (l, n)
   fun take (n, l) = List.take (l, n)
   fun drop (n, l) = List.drop (l, n)
   fun element (n, l) = List.nth (l, n)
   fun indexOf x = revLookup equal x
   fun indexOfString (c, s) = revLookup equal (c, String.explode s)

end (* structure L3 *)
