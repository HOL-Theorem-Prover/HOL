structure badLib :> badLib =
struct

open HolKernel boolLib
val something = 3;
val p = mk_var("p", bool) val q = mk_var("q", bool)
val _ = Rewrite.add_implicit_rewrites [EQT_INTRO (ASSUME (mk_conj(p,q)))]

end
