signature bagLib = sig

  (* Type operations *)
  val bag_ty : Type.hol_type  (* type of alpha bags, i.e., :'a -> num *)
  val is_bag_ty : Type.hol_type -> bool
  (* returns the "element" type of a bag term *)
  val base_type : Term.term -> Type.hol_type

  (* all terms are operators on 'a bags *)
  val BAG_DIFF_tm : Term.term
  val BAG_INSERT_tm : Term.term
  val BAG_UNION_tm : Term.term
  val SUB_BAG_tm : Term.term
  val EMPTY_BAG_tm : Term.term
  val BAG_EQ_tm : Term.term (* instantiation of = *)

  val mk_union : (Term.term * Term.term) -> Term.term
  val list_mk_union : Term.term list -> Term.term (* fails on [] *)
  val dest_union : Term.term -> (Term.term * Term.term)
  val strip_union : Term.term -> Term.term list
  val is_union : Term.term -> bool

  val mk_diff : (Term.term * Term.term) -> Term.term
  val dest_diff : Term.term -> (Term.term * Term.term)
  val is_diff : Term.term -> bool

  val mk_insert : (Term.term * Term.term) -> Term.term
  val dest_insert : Term.term -> (Term.term * Term.term)
  val is_insert : Term.term -> bool
  val list_mk_insert : (Term.term list * Term.term) -> Term.term

  val dest_sub_bag : Term.term -> (Term.term * Term.term)
  val mk_sub_bag : (Term.term * Term.term) -> Term.term
  val is_sub_bag : Term.term -> bool


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

  val SBAG_SOLVE : Thm.thm list -> Term.term -> Thm.thm
  (* the underlying conversion for doing the proofs in the ssdata value
     above *)

  val sbag_cache : Cache.cache
  (* the cache used for caching SBAG_SOLVE's results *)

end;