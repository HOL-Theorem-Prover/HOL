signature bagLib = sig
  val bag_ty : Type.hol_type  (* type of alpha bags, i.e., :'a -> num *)

  (* all terms are operators on 'a bags *)
  val BAG_DIFF_tm : Term.term
  val BAG_INSERT_tm : Term.term
  val BAG_UNION_tm : Term.term
  val SUB_BAG_tm : Term.term
  val EMPTY_BAG_tm : Term.term

  (* returns the "element" type of a bag term *)
  val base_type : Term.term -> Type.hol_type

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

  val BAG_AC_ss : simpLib.ssdata (* AC-normalises BAG_UNION terms *)

  val CANCEL_CONV : Abbrev.conv  (* cancels common sub-terms in SUB_BAG and
                                    equalities between BAG_UNION terms *)

  val BAG_ss : simpLib.ssdata

end;