signature Preterm = 
sig

  datatype preterm = Var of   {Name : string, Ty : Type.hol_type}
                   | Const of {Name : string, Ty : Type.hol_type}
                   | Comb of  {Rator: preterm, Rand : preterm}
                   | Abs of   {Bvar : preterm, Body : preterm}
                   | Constrained of preterm * Type.hol_type
                   | Antiq of Term.term

  val typecheck :(int,Type.hol_type)Lib.istream -> preterm -> Term.term
end;
