signature listSyntax = sig
  val list_ty : Type.hol_type (* type of alpha lists, i.e. 'a list *)
  (* makes the list type with the given type of element *)
  val mk_list_ty : Type.hol_type -> Type.hol_type
  val is_list_ty : Type.hol_type -> bool
  (* returns the "element" type of a list term *)
  val base_type : Term.term -> Type.hol_type

  (* all terms are operators on 'a lists *)
  val MAP_tm : Term.term (* taking a function of type 'a -> 'b *)
  val CONS_tm : Term.term
  val APPEND_tm : Term.term
  val NIL_tm : Term.term
  val LIST_EQ_tm : Term.term (* instantiation of = *)

  (* functions for getting specific type instantiated versions of constants *)
  val mk_CONS_tm : Type.hol_type -> Term.term
  val mk_NIL_tm : Type.hol_type -> Term.term

  val is_nil : Term.term -> bool

  val mk_cons : Term.term * Term.term -> Term.term
  val dest_cons : Term.term -> Term.term * Term.term
  val is_cons : Term.term -> bool

  val mk_list : (Term.term list * Type.hol_type) -> Term.term
  val dest_list : Term.term -> (Term.term list * Type.hol_type)
end

