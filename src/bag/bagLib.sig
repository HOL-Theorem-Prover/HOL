signature bagLib = sig
  include Abbrev

  (* Type operations *)
  val bag_ty : hol_type  (* type of alpha bags, i.e., :'a -> num *)
  val is_bag_ty : hol_type -> bool

  (* returns the "element" type of a bag term *)
  val base_type : term -> hol_type

  (* all terms are operators on 'a bags *)

  val BAG_DIFF_tm : term
  val BAG_INSERT_tm : term
  val BAG_UNION_tm : term
  val SUB_BAG_tm : term
  val EMPTY_BAG_tm : term
  val BAG_EQ_tm : term (* instantiation of = *)

  val mk_union : (term * term) -> term
  val list_mk_union : term list -> term (* fails on [] *)
  val dest_union : term -> (term * term)
  val strip_union : term -> term list
  val is_union : term -> bool

  val mk_diff : (term * term) -> term
  val dest_diff : term -> (term * term)
  val is_diff : term -> bool

  val mk_insert : (term * term) -> term
  val dest_insert : term -> (term * term)
  val is_insert : term -> bool
  val list_mk_insert : (term list * term) -> term

  val dest_sub_bag : term -> (term * term)
  val mk_sub_bag : (term * term) -> term
  val is_sub_bag : term -> bool


  (* stuff that will help prove theorems *)
  val BAG_AC_ss : simpLib.ssdata (* AC-normalises BAG_UNION terms *)

  val CANCEL_CONV : Abbrev.conv
  (* cancels out common sub-terms in SUB_BAG, equalities and
     BAG_DIFFs between BAG_UNION terms.  Will return the reflexive
     equation when both arguments are {| |}.  *)

  val BAG_ss : simpLib.ssdata
  (* includes CANCEL_CONV and a bunch of rewriting theorems, mainly those
     to do with the standard operators and empty bags.  For example:
        {| |} + b = b
        (b + c = {| |}) = (b = {| |}) /\ (c = {| |})
  *)

  val SBAG_SOLVE_ss : simpLib.ssdata
  (* includes a decision procedure to automatically prove sub-bag and
     equality terms by using the arithmetic decision procedure.  Can
     only prove positive instances, and will not attempt proofs of
     terms that involve BAG_DIFF because these are too slow with
     arithLib's treatment of subtraction. *)

  val SBAG_SOLVE : thm list -> term -> thm
  (* the underlying conversion for doing the proofs in the ssdata value
     above *)

  val sbag_cache : Cache.cache
  (* the cache used for caching SBAG_SOLVE's results *)

end;
