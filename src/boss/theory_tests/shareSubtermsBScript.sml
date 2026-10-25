Theory shareSubtermsB
Ancestors
  shareSubtermsA
Libs
  testutils

val f = mk_var("f", “:num -> num -> num”)
val g = mk_var("g", “:num -> num”)
val num = “:num”
val h10 = mk_var("h", list_mk_fun (List.tabulate (10, fn _ => num), num))

(* a chain of distinct leaves, repeated ten times, repeated ten times again *)
fun chain 0 = mk_var("x", num)
  | chain n = list_mk_comb(f, [chain (n - 1), mk_var("a" ^ Int.toString n, num)])
fun rep t = list_mk_comb(h10, List.tabulate (10, fn _ => t))
val u = chain 20
val w = rep u
val z = rep w

(* the same shapes underneath binders *)
val m = “(λy. ^f y ^w) (^g ^u)”
val mm = “(λv. ^f (^g v) ^m) ^z”

(* repeated subterms that mention the bound variable *)
val yv = mk_var("y", num)
val fy = list_mk_comb(f, [yv, yv])
val lb = mk_abs(yv, rep (list_mk_comb(f, [fy, rep fy])))

fun check (nm, th, t) =
    (tprint ("round trip of shared subterms: " ^ nm);
     if aconv (concl th) (mk_eq(t, t)) then OK() else die "terms differ")

val _ = check ("z_refl", shareSubtermsATheory.z_refl, z)
val _ = check ("mm_refl", shareSubtermsATheory.mm_refl, mm)
val _ = check ("lb_refl", shareSubtermsATheory.lb_refl, lb)
