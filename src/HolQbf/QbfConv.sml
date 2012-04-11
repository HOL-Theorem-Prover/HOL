structure QbfConv :> QbfConv = struct

  open Canon Conv Feedback boolSyntax

  local open Tactical bossLib simpLib boolSimps boolTheory Thm
    val QMETIS_TAC = Feedback.trace ("metis", 0) (METIS_TAC [])
    val th1 = Tactical.prove(``(!x. (x \/ P)) = P``, QMETIS_TAC)
    val th2 = prove(``(!x. (~x \/ P)) = P``,SIMP_TAC bool_ss [])
    val th3 = SYM F_DEF
    val th4 = prove(``(!x. ~x) = F``,SIMP_TAC bool_ss [])
    val th5 = AC DISJ_COMM DISJ_ASSOC
    val th6 = AC CONJ_COMM CONJ_ASSOC
  in
    val simp_clauses = SIMP_CONV bool_ss [th1,th2,th3,th4,th5,th6]
  end

  local
    open boolSyntax boolTheory markerLib
    fun literal x t = t = x orelse dest_neg t = x handle HOL_ERR _ => false
  in
    val remove_forall =
      Ho_Rewrite.PURE_REWRITE_CONV [FORALL_AND_THM] THENC
      EVERY_CONJ_CONV (fn t =>
        let val (x,_) = dest_forall t in
          CHANGED_CONV (Rewrite.PURE_REWRITE_CONV [FORALL_SIMP])
            ORELSEC
          QUANT_CONV (move_disj_left (literal x))
        end t) THENC
      simp_clauses
  end

  fun last_quant_conv c = let
    exception Innermost
    fun f t =
      QUANT_CONV f t handle
        HOL_ERR {origin_function="RAND_CONV",...} => raise Innermost
      | Innermost => c t
  in f end

  fun strip_prefix_conv c = let
    fun f tm =
      (if is_forall tm orelse is_exists tm
       then STRIP_QUANT_CONV f
       else c) tm
  in f end

  fun last_quant_seq_conv cq cb = let
    fun f t =
      (QUANT_CONV f THENC cq) t handle
        HOL_ERR {origin_function="RAND_CONV",...} => cb t
  in f end

  fun last_forall_seq_conv cq cb = let
    exception Innermost
    fun f tm =
      if is_exists tm then STRIP_QUANT_CONV f tm
      else if is_forall tm then
        STRIP_QUANT_CONV
          (fn t => if is_exists t then f t else raise Innermost)
          tm
        handle Innermost => last_quant_seq_conv cq cb tm
      else cb tm
  in f end

  val qbf_prenex_conv =
    (* remove equalities THENC *)
    PRENEX_CONV THENC
    (last_forall_seq_conv
       remove_forall
       (NNF_CONV NO_CONV true THENC
        PROP_CNF_CONV THENC
        simp_clauses))

end
