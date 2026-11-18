structure polynomialSyntax :> polynomialSyntax =
struct

open HolKernel boolSyntax
open fieldInstancesTheory polynomialTheory polyMonicTheory
     polyDivisionTheory polyModuloRingTheory

val GF_tm = prim_mk_const {Thy = "fieldInstances", Name = "GF"}
val Field_tm = prim_mk_const {Thy = "field", Name = "Field"}
val Poly_tm = prim_mk_const {Thy = "polynomial", Name = "Poly"}
val poly_monic_tm = prim_mk_const {Thy = "polyMonic", Name = "poly_monic"}
val poly_deg_tm = prim_mk_const {Thy = "polynomial", Name = "poly_deg"}
val poly_mod_tm = prim_mk_const {Thy = "polyDivision", Name = "poly_mod"}
val poly_ring_tm = prim_mk_const {Thy = "polynomial", Name = "poly_ring"}
val poly_mod_ring_tm =
  prim_mk_const {Thy = "polyModuloRing", Name = "poly_mod_ring"}
val monoid_exp_tm = prim_mk_const {Thy = "monoid", Name = "monoid_exp"}
val monoid_inv_tm = prim_mk_const {Thy = "monoid", Name = "monoid_inv"}

fun selector thy tyname fieldname =
  prim_mk_const
    {Thy = thy, Name = TypeBasePure.mk_recordtype_fieldsel
      {tyname = tyname, fieldname = fieldname}}

val ring_carrier_tm = selector "ring" "ring" "carrier"
val ring_sum_tm = selector "ring" "ring" "sum"
val ring_prod_tm = selector "ring" "ring" "prod"
val monoid_op_tm = selector "monoid" "monoid" "op"
val monoid_id_tm = selector "monoid" "monoid" "id"

fun mk_ring_type ty = mk_thy_type {Thy = "ring", Tyop = "ring", Args = [ty]}
fun mk_GF p = mk_comb (GF_tm,p)
fun mk_Field r = mk_icomb (Field_tm,r)
fun mk_Poly (r,p) = list_mk_icomb (Poly_tm,[r,p])
fun mk_poly_monic (r,p) = list_mk_icomb (poly_monic_tm,[r,p])
fun mk_poly_deg (r,p) = list_mk_icomb (poly_deg_tm,[r,p])
fun mk_poly_mod (r,p,q) = list_mk_icomb (poly_mod_tm,[r,p,q])
fun mk_poly_ring r = mk_icomb (poly_ring_tm,r)
fun mk_poly_mod_ring (r,p) = list_mk_icomb (poly_mod_ring_tm,[r,p])
fun mk_ring_carrier r = mk_icomb (ring_carrier_tm,r)
fun mk_ring_sum r = mk_icomb (ring_sum_tm,r)
fun mk_ring_prod r = mk_icomb (ring_prod_tm,r)
fun mk_monoid_op g = mk_icomb (monoid_op_tm,g)
fun mk_monoid_id g = mk_icomb (monoid_id_tm,g)
fun mk_monoid_exp g = mk_icomb (monoid_exp_tm,g)
fun mk_monoid_inv g = mk_icomb (monoid_inv_tm,g)

end
