structure pairML :> pairML =
struct

fun fst(x,y) = x
fun snd(x,y) = y
fun curry f x y = f(x,y)
fun uncurry f (x,y) = f x y
fun pairmap (f,g) (x,y) = (f x, g y)

end
