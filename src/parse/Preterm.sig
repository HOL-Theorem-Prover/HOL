signature Preterm =
sig
  type pretype = Pretype.pretype
  type hol_type = Type.hol_type
  type term = Term.term

  datatype preterm =
    Var of   {Name : string, Ty : pretype}
  | Const of {Name : string, Thy : string, Ty : pretype}
  | Overloaded of {Name : string, Ty : pretype,
                   Info : Overload.overloaded_op_info}
  | Comb of  {Rator: preterm, Rand : preterm}
  | Abs of   {Bvar : preterm, Body : preterm}
  | Constrained of preterm * pretype
  | Antiq of term

  (* Performs the first phase of type-checking, altering the types
     attached to the various components of the preterm, but without
     resolving overloading.  The two printing functions are used to
     report errors. *)

  val typecheck_phase1 :
    ((term -> string) * (hol_type -> string)) option -> preterm -> unit

  (* performs overloading resolution, possibly guessing overloads if
     this is both allowed by Globals.guessing_overloads and required by
     ambiguity in the term *)

  val overloading_resolution : preterm -> preterm


  (* converts a preterm into a term.  Will guess type variables for
     unassigned pretypes if Globals.guessing_tyvars is true.
     Will fail if the preterm contains any Overloaded constructors, or
     if the types attached to the leaves aren't valid for the kernel.  *)

  val to_term : preterm -> term

  (* essentially the composition of all three of the above *)

  val typecheck:
    ((term -> string) * (hol_type -> string)) option -> preterm -> term

  val remove_case_magic : term -> term

end;

