(* -------------------------------------------------------------------------
   Patricia trees
   ------------------------------------------------------------------------- *)

structure Ptree :> Ptree =
struct

datatype 'a ptree =
     Empty
   | Leaf of int * 'a
   | Branch of int * int * 'a ptree * 'a ptree

fun bit (b, n) = IntInf.~>> (n, Word.fromInt b) mod 2 = 1
fun mod_2exp (x, n) = IntInf.andb (n, IntInf.<< (1, Word.fromInt x) - 1)
fun mod_2exp_eq (x, a, b) = mod_2exp (x, IntInf.xorb (a, b)) = 0

fun peek (Empty, _) = NONE
  | peek (Leaf (j, d), k) = if k = j then SOME d else NONE
  | peek (Branch (_, m, l, r), k) = peek (if bit (m, k) then l else r, k)

local
   fun leastSetBit a = IntInf.log2 (IntInf.andb (a, ~a))
   fun branching_bit (p0, p1) =
      if p0 = p1 then 0 else leastSetBit (IntInf.xorb (p0, p1))
   fun join (p0, t0, p1, t1) =
      let
         val m = branching_bit (p0, p1)
         val p = mod_2exp (m, p0)
      in
         if bit (m, p0) then Branch (p, m, t0, t1) else Branch (p, m, t1, t0)
      end
in
   fun add (Empty, x) = Leaf x
     | add (Leaf (j, d), x as (k, _)) =
         if j = k then Leaf x else join (k, Leaf x, j, Leaf (j, d))
     | add (Branch (p, m, l, r), x as (k, _)) =
         if mod_2exp_eq (m, k, p)
            then if bit (m, k)
                    then Branch (p, m, add (l, x), r)
                 else Branch (p, m, l, add (r, x))
         else join (k, Leaf x, p, Branch (p, m, l, r))
end

fun transform f Empty = Empty
  | transform f (Leaf (j, d)) = Leaf (j, f d)
  | transform f (Branch (p, m, l, r)) =
      Branch (p, m, transform f l, transform f r)

(*
fun add_list t = List.foldl (fn (x, t) => add (t, x)) t
fun ptree_of_list l = add_list Empty l

local
   fun branch (_, _, Empty, t) = t
     | branch (_, _, t, Empty) = t
     | branch (p, m, t0, t1) = Branch (p, m, t0, t1)
in
   fun remove (Empty, _) = Empty
     | remove (t as Leaf (j, _), k) = if j = k then Empty else t
     | remove (t as Branch (p, m, l, r), k) =
         if mod_2exp_eq (m, k, p)
            then if bit (m, k)
                    then branch (p, m, remove (l, k), r)
                 else branch (p, m, l, remove (r, k))
         else t
end

local
   fun traverse (Empty, a) = a
     | traverse (Leaf x, a) = x :: a
     | traverse (Branch (p, m, l, r), a) = traverse (l, traverse (r, a))
in
   fun list_of_ptree t = traverse (t, [])
   fun keys t = List.map fst (list_of_ptree t)
end

fun size Empty = 0
  | size (Leaf _) = 1
  | size (Branch (_, _, l, r)) = size l + size r
*)

end (* structure Ptree *)
