structure polynomialSyntax :> polynomialSyntax =
struct

open HolKernel
open fieldInstancesTheory polynomialTheory polyMonicTheory
     polyDivisionTheory polyModuloRingTheory

val (GF_tm,mk_GF,_,_) = syntax_fns1 "fieldInstances" "GF"
val (_,mk_Field,_,_) = syntax_fns1 "field" "Field"
val (_,mk_Poly,_,_) = syntax_fns2 "polynomial" "Poly"
val (_,mk_poly_monic,_,_) = syntax_fns2 "polyMonic" "poly_monic"
val (_,mk_poly_deg,_,_) = syntax_fns2 "polynomial" "poly_deg"
val (poly_mod_tm,mk_poly_mod,_,_) = syntax_fns3 "polyDivision" "poly_mod"
val (_,mk_poly_ring,_,_) = syntax_fns1 "polynomial" "poly_ring"
val (_,mk_poly_mod_ring,_,_) =
  syntax_fns2 "polyModuloRing" "poly_mod_ring"
val (monoid_exp_tm,mk_monoid_exp,_,_) = syntax_fns1 "monoid" "monoid_exp"
val (monoid_inv_tm,mk_monoid_inv,_,_) = syntax_fns1 "monoid" "monoid_inv"

fun selector thy tyname fieldname =
  syntax_fns1 thy (TypeBasePure.mk_recordtype_fieldsel
    {tyname = tyname, fieldname = fieldname})

val (_,mk_ring_carrier,_,_) = selector "ring" "ring" "carrier"
val (_,mk_ring_sum,_,_) = selector "ring" "ring" "sum"
val (_,mk_ring_prod,_,_) = selector "ring" "ring" "prod"
val (_,mk_monoid_op,_,_) = selector "monoid" "monoid" "op"
val (_,mk_monoid_id,_,_) = selector "monoid" "monoid" "id"

fun mk_ring_type ty = mk_thy_type {Thy = "ring", Tyop = "ring", Args = [ty]}

end
