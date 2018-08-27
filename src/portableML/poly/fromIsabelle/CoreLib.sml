infix 2 ?

fun the_list NONE = [] | the_list (SOME x) = [x]
fun the_default d NONE = d | the_default d (SOME x) = x

fun fold_map _ [] y = ([], y)
  | fold_map f (x :: xs) y =
      let
        val (x', y') = f x y;
        val (xs', y'') = fold_map f xs y';
      in (x' :: xs', y'') end;


fun these (SOME x) = x
  | these NONE = [];
