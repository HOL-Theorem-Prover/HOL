infix 2 ?

fun the_list NONE = [] | the_list (SOME x) = [x]
fun the_default d NONE = d | the_default d (SOME x) = x

fun these (SOME x) = x
  | these NONE = [];
