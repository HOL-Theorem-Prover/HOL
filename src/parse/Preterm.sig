signature Preterm =
sig

  datatype preterm = Var of   {Name : string, Ty : TCPretype.pretype}
                   | Const of {Name : string, Ty : TCPretype.pretype}
                   | Comb of  {Rator: preterm, Rand : preterm}
                   | Abs of   {Bvar : preterm, Body : preterm}
                   | Constrained of preterm * TCPretype.pretype
                   | Antiq of Term.term

  val TC :
    ((Term.term -> string) * (Type.hol_type -> string)) option ->
    preterm -> unit
  val typecheck:
    ((Term.term -> string) * (Type.hol_type -> string)) option ->
    preterm -> Term.term

end;

