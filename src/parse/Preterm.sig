signature Preterm =
sig

  datatype preterm = Var of   {Name : string, Ty : TCPretype.pretype}
                   | Const of {Name : string, Ty : TCPretype.pretype}
                   | Overloaded of {Name : string, Ty : TCPretype.pretype,
                                    Info : Overload.overloaded_op_info}
                   | Comb of  {Rator: preterm, Rand : preterm}
                   | Abs of   {Bvar : preterm, Body : preterm}
                   | Constrained of preterm * TCPretype.pretype
                   | Antiq of Term.term

  (* Performs a type-check, altering the types attached to the various
     components of the preterm, but without attempting to convert the preterm
     into a genuine term *)
  val TC :
    ((Term.term -> string) * (Type.hol_type -> string)) option ->
    preterm -> unit
  (* Does the type-checking and then generates a full-blown term, if
     possible. *)
  val typecheck:
    ((Term.term -> string) * (Type.hol_type -> string)) option ->
    preterm -> Term.term

end;

