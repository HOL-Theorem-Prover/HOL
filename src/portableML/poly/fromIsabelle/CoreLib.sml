infix 2 ?

fun the_list NONE = [] | the_list (SOME x) = [x]
fun the_default d NONE = d | the_default d (SOME x) = x

fun fold _ [] y = y
  | fold f (x :: xs) y = fold f xs (f x y);
fun fold_rev _ [] y = y
  | fold_rev f (x :: xs) y = f x (fold_rev f xs y);
fun fold_map _ [] y = ([], y)
  | fold_map f (x :: xs) y =
      let
        val (x', y') = f x y;
        val (xs', y'') = fold_map f xs y';
      in (x' :: xs', y'') end;


fun these (SOME x) = x
  | these NONE = [];
fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;
fun cons h t = h::t
fun pair x y = (x,y)
fun snd(x,y) = y
