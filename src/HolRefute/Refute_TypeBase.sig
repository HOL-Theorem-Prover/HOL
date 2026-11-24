signature Refute_TypeBase = sig
  (* [TypeBase]'s accessors over [Refute_Session.context], so a call
     reads the datatypes of the context it was given.  Every accessor
     that reads a datatype's structure or semantics (its constructors,
     case constant, cases, induction, records, size) first checks the
     entry it reads ([check_entry]); [elts] does not, and its caller
     checks the entry it then uses. *)
  val fetch : Type.hol_type -> TypeBasePure.tyinfo option
  (* [fetch] without the check, for a classification only *)
  val peek : Type.hol_type -> TypeBasePure.tyinfo option
  val elts : unit -> TypeBasePure.tyinfo list
  (* The theorems of an entry's structure and semantics, each through
     the checked point (Refute_Facts): the recursion and induction
     theorems, the case, case congruence, case equality, case
     elimination and cases theorems, injectivity and distinctness, size
     and encoding, destructors, recognizers, and a record's accessors
     and updates.  Not its simplification set ([simpls_of]): those
     rewrites reach a problem only through [srw_ss], with their own
     tags. *)
  val entry_theorems : TypeBasePure.tyinfo -> Thm.thm list
  val check_entry : TypeBasePure.tyinfo -> unit
  val constructors_of : Type.hol_type -> Term.term list
  val induction_of : Type.hol_type -> Thm.thm
  val nchotomy_of : Type.hol_type -> Thm.thm
  val is_constructor : Term.term -> bool
  val mk_case : Term.term * (Term.term * Term.term) list -> Term.term
  val is_case : Term.term -> bool
  val strip_case : Term.term -> Term.term * (Term.term * Term.term) list
  val dest_case :
    Term.term -> Term.term * Term.term * (Term.term * Term.term) list
  val is_record : Term.term -> bool
  val dest_record : Term.term -> Type.hol_type * (string * Term.term) list
  val type_size : Type.hol_type -> Term.term
end
