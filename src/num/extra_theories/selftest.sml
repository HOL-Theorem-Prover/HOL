open HolKernel Parse testutils logrootTheory simpLib numSimps BasicProvers

val LOG_t = prim_mk_const{Thy = "logroot", Name = "LOG"}
fun test (b, n, answer) =
    let
      val mk = numSyntax.mk_numeral o Arbnum.fromInt
      val b_t = mk b and n_t = mk n and out_t = mk answer
      val in_t = list_mk_comb(LOG_t, [b_t, n_t])
      val in_s = term_to_string in_t
      val prob_s = in_s ^ " (= " ^ Int.toString answer ^ ")"
    in
      convtest ("simp: " ^ prob_s, SIMP_CONV (srw_ss()) [], in_t, out_t);
      convtest ("EVAL: " ^ prob_s, computeLib.EVAL_CONV, in_t, out_t)
    end

val _ = List.app test [(2,10,3), (5,10653,5), (2,2048,11), (3,1,0), (11,121,2)]
