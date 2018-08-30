structure Library =
struct
local open Portable in
  fun member eq list x =
    let
      fun memb [] = false
        | memb (y :: ys) = eq (x, y) orelse memb ys;
    in memb list end;
  fun remove eq x xs = if member eq xs x then
                         List.filter (fn y => not (eq (x, y))) xs
                       else xs;
  fun update eq x xs = cons x (remove eq x xs);
  fun insert eq x xs = if member eq xs x then xs else x :: xs;
  fun merge eq (xs, ys) =
    if null xs then ys else foldr' (insert eq) ys xs;
  fun fold2 _ [] [] z = z
    | fold2 f (x :: xs) (y :: ys) z = fold2 f xs ys (f x y z)
    | fold2 _ _ _ _ = raise ListPair.UnequalLengths;

  fun single x = [x]
  fun the_single [x] = x
    | the_single _ = raise List.Empty;
  fun singleton f x = the_single (f [x])

end (* local *)
end;
