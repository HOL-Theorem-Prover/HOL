structure oneSyntax :> oneSyntax =
struct

local open oneTheory in end;

open HolKernel Abbrev;

val one_ty = mk_thy_type{Tyop="one", Thy="one", Args=[]}

val one_tm      = prim_mk_const{Thy="one",Name="one"}
val one_case_tm = prim_mk_const{Thy="one",Name="one_case"}

fun mk_one_case x =
   list_mk_comb(inst[alpha |-> type_of x]one_case_tm,[x,one_tm])

fun lift_one ty () = one_tm

val is_one = Lib.equal one_tm

end
