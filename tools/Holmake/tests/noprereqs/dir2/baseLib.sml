structure baseLib =
struct

local
  open HolKernel baseTheory
in

fun basefn x = mk_comb(prim_mk_const{Thy = "base", Name = "foo"}, x)

end (* local *)

end (* struct *)
