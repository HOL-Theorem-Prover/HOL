structure pairML :> pairML =
struct

fun fst(x,y) = x
fun snd(x,y) = y
fun curry f x y = f(x,y)
fun uncurry f (x,y) = f x y
fun pair_map (f,g) (x,y) = (f x, g y)

val _ = app ConstMapML.insert
           [(pairSyntax.comma_tm, ("",",")),
            (pairSyntax.fst_tm, ("pairML","fst")),
            (pairSyntax.snd_tm, ("pairML","snd")),
            (pairSyntax.curry_tm, ("pairML","curry")),
            (pairSyntax.uncurry_tm, ("pairML","uncurry")),
            (pairSyntax.pair_map_tm, ("pairML","pair_map"))];
end
