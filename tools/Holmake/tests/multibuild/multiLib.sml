structure multiLib =
struct

open HolKernel boolLib
fun genthms delay n =
  let
    val v = mk_var("v" ^ Int.toString n, bool)
    val g = mk_imp(v,v)
  in
    store_thm(current_theory() ^ Int.toString n, g,
              REWRITE_TAC[]) before
    ignore (Posix.Process.sleep (Time.fromMilliseconds delay))
  end

end
