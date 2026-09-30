signature Refute_Util = sig
  val same_type : Type.hol_type -> Type.hol_type -> bool
  val member_type : Type.hol_type -> Type.hol_type list -> bool
  val add_type :
    Type.hol_type -> Type.hol_type list -> Type.hol_type list
  val all_distinct_types : Type.hol_type list -> bool
  val aconv_member : Term.term -> Term.term list -> bool
  val beta_normalize : Term.term -> Term.term
  val distinct_terms : Term.term list -> Term.term list
  val union_terms : Term.term list -> Term.term list -> Term.term list
  val update_term : Term.term -> Term.term -> Term.term -> Term.term
  val close_free : Term.term -> Term.term
  val theorem_term : Thm.thm -> Term.term
  val acquire_interruptibly :
    ((unit -> unit) -> unit -> unit) -> (unit -> bool) -> unit
  val elapsed_msec : Time.time -> int
  val remaining : Time.time -> Time.time
  val rf_type : int -> Type.hol_type
end
