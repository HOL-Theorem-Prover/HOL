structure combinML :> combinML =
struct

fun S f g x = f x (g x)

fun K x y = x

fun I x = x

fun C f x y = f y x

fun W f x = f x x

nonfix o;

fun o f g x = f (g x);

val _ = app ConstMapML.insert
           [(combinSyntax.S_tm, ("combinML","S")),
            (combinSyntax.K_tm, ("combinML","K")),
            (combinSyntax.I_tm, ("combinML","I")),
            (combinSyntax.C_tm, ("combinML","C")),
            (combinSyntax.W_tm, ("combinML","W")),
            (combinSyntax.o_tm, ("combinML","o"))];

end
