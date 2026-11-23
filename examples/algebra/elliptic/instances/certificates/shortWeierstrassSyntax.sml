structure shortWeierstrassSyntax :> shortWeierstrassSyntax =
struct

open HolKernel
open shortWeierstrassTheory shortWeierstrassGroupTheory

val ERR = mk_HOL_ERR "shortWeierstrassSyntax"
val ECInfinity_tm =
  prim_mk_const {Thy = "shortWeierstrass", Name = "ECInfinity"}
val (ECAffine_tm,mk_ECAffine,_,_) =
  syntax_fns2 "shortWeierstrass" "ECAffine"
val (_,mk_ShortWeierstrassCurve,_,_) =
  syntax_fns3 "shortWeierstrass" "ShortWeierstrassCurve"
val (_,mk_sw_points,_,_) = syntax_fns3 "shortWeierstrass" "sw_points"
val sw_add_tm =
  prim_mk_const {Thy = "shortWeierstrassGroup", Name = "sw_add"}
val (sw_group_tm,mk_sw_group,_,_) =
  syntax_fns3 "shortWeierstrassGroup" "sw_group"

fun mk_sw_point_type ty =
  mk_thy_type {Thy = "shortWeierstrass", Tyop = "sw_point", Args = [ty]}
fun mk_ECInfinity ty = inst [alpha |-> ty] ECInfinity_tm
fun mk_sw_add (r,a,b,P,Q) = list_mk_icomb sw_add_tm [r,a,b,P,Q]
fun mk_sw_scalar (r,a,b,P,n) =
  list_mk_comb
    (polynomialSyntax.mk_monoid_exp (mk_sw_group (r,a,b)),[P,n])

fun dest_sw_scalar tm =
  let
    fun bad () = raise ERR "dest_sw_scalar" "Expected a curve scalar expression"
  in
    case strip_comb tm of
      (head,[group,P,n]) =>
        if is_const head andalso
           same_const head polynomialSyntax.monoid_exp_tm then
          (case strip_comb group of
             (head,[r,a,b]) =>
               if is_const head andalso same_const head sw_group_tm
               then (r,a,b,P,n) else bad ()
           | _ => bad ())
        else bad ()
    | _ => bad ()
  end

end
