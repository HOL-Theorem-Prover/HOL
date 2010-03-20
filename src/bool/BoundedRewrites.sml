structure BoundedRewrites :> BoundedRewrites =
struct

  open HolKernel boolSyntax Drule boolTheory
  datatype control = UNBOUNDED | BOUNDED of int ref
  type controlled_thm = thm * control



  fun MK_BOUNDED th n =
      if n<0 then raise ERR "MK_BOUNDED" "negative bound"
      else
    ADD_ASSUM (mk_comb(bounded_tm, mk_var(Int.toString n, bool))) th

  fun DEST_BOUNDED th =
      case HOLset.find (aconv bounded_tm o rator) (hypset th) of
        SOME h => let
          val arg = rand h
        in
          (PROVE_HYP (EQ_MP (SYM (SPEC arg BOUNDED_THM)) TRUTH) th,
           valOf (Int.fromString (#1 (dest_var arg))))
        end
      | NONE => raise ERR "DEST_BOUNDED" "Theorem not bounded"

  val Ntimes = MK_BOUNDED
  val Once = C Ntimes 1

  fun dest_tagged_rewrite thm = let
    val (th, n) = DEST_BOUNDED thm
  in
    (th, BOUNDED (ref n))
  end handle HOL_ERR _ => (thm, UNBOUNDED)


end
