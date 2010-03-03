structure lcsymtacs :> lcsymtacs =
struct

  open Abbrev HolKernel boolLib simpLib BasicProvers

  val strip_tac : tactic = STRIP_TAC
  val conj_tac : tactic = CONJ_TAC
  val gen_tac : tactic = GEN_TAC
  val exists_tac : term -> tactic = EXISTS_TAC

  val rewrite_tac : thm list -> tactic = REWRITE_TAC
  val asm_rewrite_tac : thm list -> tactic = ASM_REWRITE_TAC
  val match_mp_tac : thm_tactic = MATCH_MP_TAC
  val mp_tac = MP_TAC

  val first_assum : thm_tactic -> tactic = FIRST_ASSUM
  val first_x_assum : thm_tactic -> tactic = FIRST_X_ASSUM
  val disch_then = DISCH_THEN

  val qx_gen_tac : term quotation -> tactic = Q.X_GEN_TAC
  val qexists_tac : term quotation -> tactic = Q.EXISTS_TAC


  val metis_tac : thm list -> tactic = metisLib.METIS_TAC
  val prove_tac : thm list -> tactic = PROVE_TAC

  val simp_tac = SIMP_TAC
  val asm_simp_tac = ASM_SIMP_TAC
  val full_simp_tac = FULL_SIMP_TAC
  val srw_tac = SRW_TAC

end
