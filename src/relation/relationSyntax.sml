structure relationSyntax :> relationSyntax =
struct

open HolKernel Parse boolLib
open relationTheory

val ERR = mk_HOL_ERR "relationSyntax"

(* ------------------------------------------------------------------------- *)

val empty_rel_tm    = Term.prim_mk_const {Name = "EMPTY_REL", Thy = "relation"}
fun mk_empty_rel ty = Term.inst [Type.alpha |-> ty] empty_rel_tm
val is_empty_rel    = Term.same_const empty_rel_tm

val runiv_tm = Term.prim_mk_const {Name = "RUNIV", Thy = "relation"}
fun mk_runiv (ty1, ty2) =
  Term.inst [Type.alpha |-> ty1, Type.beta |-> ty2] runiv_tm
val is_runiv = Term.same_const runiv_tm

(* - unary ----------------------------------------------------------------- *)

fun s1 n =
  HolKernel.syntax_fns
    { n = n,
      dest = HolKernel.dest_monop,
      make = fn tm => Lib.curry boolSyntax.list_mk_icomb tm o
                      Lib.list_of_singleton }
    "relation"

val (cr_tm, mk_cr, dest_cr, is_cr)                         = s1 1 "CR"
val (diag_tm, mk_diag, dest_diag, is_diag)                 = s1 3 "diag"
val (diamond_tm, mk_diamond, dest_diamond, is_diamond)     = s1 1 "diamond"
val (eqc_tm, mk_eqc, dest_eqc, is_eqc)                     = s1 3 "EQC"
val (idem_tm, mk_idem, dest_idem, is_idem)                 = s1 1 "IDEM"
val (inv_tm, mk_inv, dest_inv, is_inv)                     = s1 3 "inv"
val (invol_tm, mk_invol, dest_invol, is_invol)             = s1 1 "INVOL"
val (order_tm, mk_order, dest_order, is_order)             = s1 1 "Order"
val (preorder_tm, mk_preorder, dest_preorder, is_preorder) = s1 1 "PreOrder"
val (rc_tm, mk_rc, dest_rc, is_rc)                         = s1 3 "RC"
val (rcompl_tm, mk_rcompl, dest_rcompl, is_rcompl)         = s1 3 "RCOMPL"
val (rdom_tm, mk_rdom, dest_rdom, is_rdom)                 = s1 2 "RDOM"
val (rrange_tm, mk_rrange, dest_rrange, is_rrange)         = s1 2 "RRANGE"
val (rtc_tm, mk_rtc, dest_rtc, is_rtc)                     = s1 3 "RTC"
val (sc_tm, mk_sc, dest_sc, is_sc)                         = s1 3 "SC"
val (sn_tm, mk_sn, dest_sn, is_sn)                         = s1 1 "SN"
val (strord_tm, mk_strord, dest_strord, is_strord)         = s1 3 "STRORD"
val (tc_tm, mk_tc, dest_tc, is_tc)                         = s1 3 "TC"
val (wcr_tm, mk_wcr, dest_wcr, is_wcr)                     = s1 1 "WCR"
val (wfp_tm, mk_wfp, dest_wfp, is_wfp)                     = s1 2 "WFP"
val (wf_tm, mk_wf, dest_wf, is_wf)                         = s1 1 "WF"

val (antisymmetric_tm, mk_antisymmetric, dest_antisymmetric, is_antisymmetric) =
  s1 1 "antisymmetric"

val (equivalence_tm, mk_equivalence, dest_equivalence, is_equivalence) =
  s1 1 "equivalence"

val (irreflexive_tm, mk_irreflexive, dest_irreflexive, is_irreflexive) =
  s1 1 "irreflexive"

val (linearorder_tm, mk_linearorder, dest_linearorder, is_linearorder) =
  s1 1 "LinearOrder"

val (rcdiamond_tm, mk_rcdiamond, dest_rcdiamond, is_rcdiamond) =
  s1 1 "rcdiamond"

val (reflexive_tm, mk_reflexive, dest_reflexive, is_reflexive) =
  s1 1 "reflexive"

val (stronglinearorder_tm, mk_stronglinearorder, dest_stronglinearorder,
     is_stronglinearorder) = s1 1 "StrongLinearOrder"

val (strongorder_tm, mk_strongorder, dest_strongorder, is_strongorder) =
  s1 1 "StrongOrder"

val (symmetric_tm, mk_symmetric, dest_symmetric, is_symmetric) =
  s1 1 "symmetric"

val (total_tm, mk_total, dest_total, is_total) =
  s1 1 "total"

val (transitive_tm, mk_transitive, dest_transitive, is_transitive) =
  s1 1 "transitive"

val (weaklinearorder_tm, mk_weaklinearorder, dest_weaklinearorder,
     is_weaklinearorder) = s1 1 "WeakLinearOrder"

val (weakorder_tm, mk_weakorder, dest_weakorder, is_weakorder) =
  s1 1 "WeakOrder"

(* - binary ---------------------------------------------------------------- *)

fun s2 n =
  HolKernel.syntax_fns
    { n = n,
      dest = HolKernel.dest_binop,
      make = fn tm => Lib.curry boolSyntax.list_mk_icomb tm o
                      Lib.list_of_pair }
    "relation"

val (inv_image_tm, mk_inv_image, dest_inv_image, is_inv_image)= s2 4 "inv_image"
val (o_tm, mk_o, dest_o, is_o)                                = s2 4 "O"
val (restrict_tm, mk_restrict, dest_restrict, is_restrict)    = s2 4 "RESTRICT"
val (rinter_tm, mk_rinter, dest_rinter, is_rinter)            = s2 4 "RINTER"
val (rrestrict_tm, mk_rrestrict, dest_rrestrict, is_rrestrict)= s2 4 "RRESTRICT"
val (rsubset_tm, mk_rsubset, dest_rsubset, is_rsubset)        = s2 2 "RSUBSET"
val (runion_tm, mk_runion, dest_runion, is_runion)            = s2 4 "RUNION"

(* ------------------------------------------------------------------------- *)

end
