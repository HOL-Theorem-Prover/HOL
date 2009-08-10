signature Preterm =
sig
  type pretype = Pretype.pretype
  type hol_type = Type.hol_type
  type term = Term.term
  type overinfo = {Name : string,
                   Ty : pretype,
                   Info : Overload.overloaded_op_info,
                   Locn : locn.locn}

  datatype preterm =
    Var of   {Name : string, Ty : pretype, Locn : locn.locn}
  | Const of {Name : string, Thy : string, Ty : pretype, Locn : locn.locn}
  | Overloaded of overinfo
  | Comb of  {Rator: preterm, Rand : preterm, Locn : locn.locn}
  | Abs of   {Bvar : preterm, Body : preterm, Locn : locn.locn}
  | Constrained of {Ptm:preterm, Ty:pretype, Locn:locn.locn}
  | Antiq of {Tm:term, Locn:locn.locn}
  | Pattern of {Ptm:preterm, Locn:locn.locn}
  (* | HackHack of bool -> bool *)
  (* Because of the Locn fields, preterms should *not* be compared
     with the built-in equality, but should use eq defined below.
     To check this has been done everywhere, uncomment this constructor. *)

  val locn : preterm -> locn.locn
  val term_to_preterm : string list -> term -> preterm

  val eq : preterm -> preterm -> bool


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


  (* deals with case expressions, which need to be properly typed and
     analysed before they can be converted into type-specific case-
     constants *)
  val remove_case_magic : term -> term

  val post_process_term : (term -> term) ref

  (* essentially the composition of all four of the above *)
  val typecheck:
    ((term -> string) * (hol_type -> string)) option -> preterm -> term

  datatype tcheck_error =
           ConstrainFail of term * hol_type
         | AppFail of term * term
         | OvlNoType of string * hol_type

  val last_tcerror : (tcheck_error * locn.locn) option ref

end;

