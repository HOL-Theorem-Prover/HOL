signature Refute_TypeBase = sig
  (* [TypeBase]'s accessors over [Refute_Session.context], so a call
     reads the datatypes of the context it was given. *)
  val theTypeBase : unit -> TypeBasePure.typeBase
  val fetch : Type.hol_type -> TypeBasePure.tyinfo option
  val elts : unit -> TypeBasePure.tyinfo list
  val constructors_of : Type.hol_type -> Term.term list
  val induction_of : Type.hol_type -> Thm.thm
  val nchotomy_of : Type.hol_type -> Thm.thm
  val is_constructor : Term.term -> bool
  val mk_case : Term.term * (Term.term * Term.term) list -> Term.term
  val is_case : Term.term -> bool
  val strip_case : Term.term -> Term.term * (Term.term * Term.term) list
  val is_record : Term.term -> bool
  val dest_record : Term.term -> Type.hol_type * (string * Term.term) list
end
