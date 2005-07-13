signature bagSimps =
sig
   include Abbrev
   type cache = Cache.cache
   type ssfrag = simpLib.ssfrag

  val BAG_AC_ss : ssfrag (* AC-normalises BAG_UNION terms *)

  val CANCEL_CONV : conv
  (* cancels out common sub-terms in SUB_BAG, equalities and
     BAG_DIFFs between BAG_UNION terms.  Will return the reflexive
     equation when both arguments are {| |}.  *)

  val BAG_ss : ssfrag
  (* includes CANCEL_CONV and a bunch of rewriting theorems, mainly those
     to do with the standard operators and empty bags.  For example:
        {| |} + b = b
        (b + c = {| |}) = (b = {| |}) /\ (c = {| |})
  *)

  val SBAG_SOLVE_ss : ssfrag
  (* includes a decision procedure to automatically prove sub-bag and
     equality terms by using the arithmetic decision procedure.  Can
     only prove positive instances, and will not attempt proofs of
     terms that involve BAG_DIFF because these are too slow with
     arithLib's treatment of subtraction. *)

  val SBAG_SOLVE : thm list -> term -> thm
  (* the underlying conversion for doing the proofs in the ssfrag value
     above *)

  val sbag_cache : cache
  (* the cache used for caching SBAG_SOLVE's results *)
end
