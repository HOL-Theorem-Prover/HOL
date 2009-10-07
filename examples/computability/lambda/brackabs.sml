structure brackabs :> brackabs =
struct

open HolKernel boolLib simpLib

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars brackabsTheory.brackabs_grammars
end
open Parse

open brackabsTheory reductionEval


val eqn_elim = prove(
  ``(!Y. (X:term == Y) = (Z == Y)) ==> X == Z``,
  STRIP_TAC THEN POP_ASSUM (Q.SPEC_THEN `Z` MP_TAC) THEN
  REWRITE_TAC [chap2Theory.lameq_refl]);
fun brackabs_equiv ths def = let
  val lameq_t = ``chap2$==``
  val th = if is_eq (concl def) then let
               val (l,r) = dest_eq (concl def)
             in
               EQ_MP (AP_TERM (mk_comb(lameq_t, l)) def)
                     (SPEC l (GEN_ALL chap2Theory.lameq_refl))
             end
           else def
  val list1 = [S_I, K_I, B_I, C_I, fake_eta, B_eta, I_I]
in
  th |> SIMP_RULE (bsrw_ss()) (list1 @ ths)
     |> SIMP_RULE (bsrw_ss()) (B_I_uncond :: list1 @ ths)
end


end (* struct *)
