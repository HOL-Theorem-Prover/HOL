structure intermediateLib =
struct

local
open HolKernel Parse boolLib baseTheory
in

fun is_base t = aconv (rator t) (prim_mk_const{Thy = "base", Name = "base"})
end

end (* struct *)
