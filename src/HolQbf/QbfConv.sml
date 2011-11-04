structure QbfConv :> QbfConv = struct

  open Canon Conv Feedback boolSyntax

  local open Tactical bossLib Term
    val forall_or1 = prove(``(∀x. (x ∨ P)) = P``,METIS_TAC[])
    val forall_or2 = prove(``(∀x. (¬x ∨ P)) = P``,METIS_TAC[])
  in val remove_forall =
    Ho_Rewrite.PURE_REWRITE_CONV [boolTheory.FORALL_AND_THM] THENC
    EVERY_CONJ_CONV (fn t =>
      let val (x,_) = dest_forall t in
        Rewrite.PURE_REWRITE_CONV [boolTheory.FORALL_SIMP] t
        handle UNCHANGED => (
          QUANT_CONV (
            markerLib.move_disj_left
             (fn t => t = x orelse dest_neg t = x handle HOL_ERR _ => false)
          ) THENC
          Rewrite.PURE_REWRITE_CONV [forall_or1,forall_or2] ) t
      end)
  end

  fun last_quant_conv (fc,ec) = let
    exception Innermost
    fun f t =
      QUANT_CONV f t handle
        HOL_ERR {origin_function="RAND_CONV",...} => raise Innermost
      | Innermost => if is_forall t then fc t else
                     if is_exists t then ec t else
                       raise mk_HOL_ERR "QbfConv" "last_quant_conv"
                       "term doesn't have quantifier prefix of forall and exists"
  in f end

  val qbf_prenex_conv =
    (* remove equalities THENC *)
    PRENEX_CONV THENC
    let val c = QUANT_CONV (
      NNF_CONV NO_CONV true THENC
      PROP_CNF_CONV THENC
      let open simpLib boolSimps boolTheory in
        SIMP_CONV bool_ss [AC DISJ_COMM DISJ_ASSOC, AC CONJ_COMM CONJ_ASSOC]
      end)
    in
      last_quant_conv (c THENC remove_forall, c)
    end

end
