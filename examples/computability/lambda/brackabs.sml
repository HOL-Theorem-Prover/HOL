structure brackabs :> brackabs =
struct

open HolKernel boolLib simpLib

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars $ valOf $ grammarDB{thyname="brackabs"}
end
open Parse

open brackabsTheory reductionEval


(* eqn_elim : |- (!Y. X == Y = Z == Y) ==> X == Z, derived forward
   from chap2Theory.lameq_refl so we don't fire a load-time
   Tactical.prove. *)
val eqn_elim =
  let val Xv = ``X:term``
      val Zv = ``Z:term``
      val Yv = ``Y:term``
      val eqbody = ``(X:term == Y) = (Z == Y)``
      val hyp = mk_forall(Yv, eqbody)
      val h = ASSUME hyp
      val step = SPEC Zv h                                (* [h] |- (X == Z) = (Z == Z) *)
      val refl = SPEC Zv chap2Theory.lameq_refl           (* |- Z == Z *)
      val xz = EQ_MP (SYM step) refl                      (* [h] |- X == Z *)
  in DISCH hyp xz end
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
