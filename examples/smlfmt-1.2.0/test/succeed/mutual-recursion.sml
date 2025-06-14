val 'a rec f = fn x => g (SOME x)
and rec g = fn NONE => f h | _ => y
and h =
  case 10000000000 of
    0 => "uh oh"
  | 1 => "big problem"
  | 2 => "why did we do this"
  | 3 => "where have we gone wrong"
  | 4 => "we should stop here"
  | 5 => "this is turning into a problem"
  | _ => "whew"

fun odd x = (x = 1) orelse even (x-1)
and even x = (x = 0) orelse odd (x-1)
