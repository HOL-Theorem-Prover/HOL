signature bvDecideLib =
sig
  include Abbrev
  (* Proves a goal about words of one width by bit-blasting it with a
     verified blaster, refuting the CNF with CaDiCaL and checking its LRAT
     certificate with a verified checker under cv_compute.  CaDiCaL comes
     from $HOL_CADICAL or `cadical` on PATH.  Only the conclusion is used,
     not the assumptions.  Fails if the goal is false once its
     unsupported subterms are abstracted, or if CaDiCaL is missing. *)
  (* when nonempty, the CaDiCaL executable to use instead *)
  val cadical_executable : string ref
  val BV_DECIDE_PROVE : term -> thm
  val BV_DECIDE_CONV  : conv
  val BV_DECIDE_TAC   : tactic
end
