(* Numeric polynomial quotient conversions; see pairingFieldCertificateLib.sig.
   QUOTIENT_CONV prime modulus evaluates identities, sums, products and natural
   powers in PolyModRing (GF p) modulus, using checked polynomial remainders.
   Supply prime p with literal p and a canonical ascending monic modulus of
   positive degree; [] is zero. Power evaluation also checks base membership.
   Irreducibility is not required for these quotient-ring computations, and
   abstract quotient inverses are deliberately left unevaluated. *)

structure pairingFieldCertificateLib :> pairingFieldCertificateLib =
struct

open HolKernel boolLib bossLib Conv

fun QUOTIENT_CONV prime modulus =
  let
    val p = rand (concl prime)
    val base = ``GF ^p``
    val r = ``PolyModRing ^base ^modulus``
    val ring = MATCH_MP fieldTheory.field_is_ring
      (MATCH_MP fieldInstancesTheory.GF_field prime)
    val bounded = polynomialCertificateLib.BOUNDED_CONV ()
    val monic = EQT_ELIM (bounded ``poly_monic ^base ^modulus``)
    val ulead = MATCH_MP (MATCH_MP polyMonicTheory.poly_monic_ulead ring) monic
    val power = MATCH_MP
      (ISPECL [base,modulus] polyModuloRingTheory.poly_mod_ring_exp)
      (CONJ ring ulead)
    val remainder = polynomialCertificateLib.REMAINDER_CONV prime modulus
    val modpow = polynomialCertificateLib.MODPOW_CONV prime modulus
    val remainder_head = fst (strip_comb ``poly_mod ^base [] ^modulus``)
    val sumop = ``^r.sum.op``
    val prodop = ``^r.prod.op``
    val powop = ``^r.prod.exp``
    val zero = ``^r.sum.id``
    val one = ``^r.prod.id``
    val add_rule = SIMP_CONV (srw_ss()) [polyModuloRingTheory.poly_mod_ring_def]
      ``^r.sum.op (x:num list) y``
    val mult_rule = SIMP_CONV (srw_ss()) [polyModuloRingTheory.poly_mod_ring_def]
      ``^r.prod.op (x:num list) y``
    fun member x = EQT_ELIM
      ((REWRITE_CONV [polyModuloRingTheory.poly_mod_ring_element] THENC bounded)
       ``^x IN ^r.carrier``)
    fun literal_polynomial tm =
      case total listSyntax.dest_list tm of
        SOME (xs,ty) => ty = numSyntax.num andalso List.all numSyntax.is_numeral xs
      | NONE => false
    (* Normalize polynomial arguments before certifying their remainder;
       unfolding the record projection alone can leave weak arithmetic. *)
    val operation =
      FIRST_CONV [REWR_CONV add_rule, REWR_CONV mult_rule] THENC
      bounded THENC remainder THENC bounded
    fun primitive tm =
      case strip_comb tm of
        (head,[_,_,_]) =>
          if is_const head andalso same_const head remainder_head then remainder tm
          else identity tm
      | _ => identity tm
    and identity tm =
      if aconv tm zero orelse aconv tm one then
        (REWRITE_CONV [polyModuloRingTheory.poly_mod_ring_ids] THENC bounded) tm
      else raise UNCHANGED
    fun normalize tm =
      if numSyntax.is_numeral tm orelse literal_polynomial tm orelse aconv tm r
      then REFL tm
      else
        let
          val children = if is_comb tm then COMB_CONV normalize tm
            else if is_abs tm then ABS_CONV normalize tm else REFL tm
        in TRANS children (QCONV step (rhs (concl children))) end
    and step tm =
      if is_comb tm andalso is_comb (rator tm) then
        let val operator = rator (rator tm)
        in
          if aconv operator sumop orelse aconv operator prodop then operation tm
          else if aconv operator powop then
            let val x = rand (rator tm)
                val n = rand tm
                val law = SPEC n (MP (SPEC x power) (member x))
            in TRANS law (modpow (rhs (concl law))) end
          else primitive tm
        end
      else primitive tm
  in
    DEPTH_CONV BETA_CONV THENC certificateComputeLib.NAT_CONV THENC
    normalize THENC bounded
  end

end
