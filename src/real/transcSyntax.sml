structure transcSyntax :> transcSyntax =
struct

open Abbrev HolKernel
open realSyntax transcTheory

(* ------------------------------------------------------------------------- *)

val monop =
   HolKernel.syntax_fns "transc" 1 HolKernel.dest_monop
      (Lib.curry boolSyntax.mk_icomb)

val binop =
   HolKernel.syntax_fns "transc" 2 HolKernel.dest_binop HolKernel.mk_binop

val triop =
   HolKernel.syntax_fns "transc" 3 HolKernel.dest_triop HolKernel.mk_triop

(* ------------------------------------------------------------------------- *)

val pi_tm =
   Term.mk_thy_const {Ty = realSyntax.real_ty, Thy = "transc", Name = "pi"}

val (Dint_tm, mk_Dint, dest_Dint, is_Dint) = triop "Dint"
val (acs_tm, mk_acs, dest_acs, is_acs) = monop "acs"
val (asn_tm, mk_asn, dest_asn, is_asn) = monop "asn"
val (atn_tm, mk_atn, dest_atn, is_atn) = monop "atn"
val (cos_tm, mk_cos, dest_cos, is_cos) = monop "cos"
val (division_tm, mk_division, dest_division, is_division) = binop "division"
val (dsize_tm, mk_dsize, dest_dsize, is_dsize) = monop "dsize"
val (exp_tm, mk_exp, dest_exp, is_exp) = monop "exp"
val (fine_tm, mk_fine, dest_fine, is_fine) = binop "fine"
val (gauge_tm, mk_gauge, dest_gauge, is_gauge) = binop "gauge"
val (ln_tm, mk_ln, dest_ln, is_ln) = monop "ln"
val (root_tm, mk_root, dest_root, is_root) = binop "root"
val (rpow_tm, mk_rpow, dest_rpow, is_rpow) = binop "rpow"
val (rsum_tm, mk_rsum, dest_rsum, is_rsum) = binop "rsum"
val (sin_tm, mk_sin, dest_sin, is_sin) = monop "sin"
val (sqrt_tm, mk_sqrt, dest_sqrt, is_sqrt) = monop "sqrt"
val (tan_tm, mk_tan, dest_tan, is_tan) = monop "tan"
val (tdiv_tm, mk_tdiv, dest_tdiv, is_tdiv) = binop "tdiv"

(* ------------------------------------------------------------------------- *)

end
