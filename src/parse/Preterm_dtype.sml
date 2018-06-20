structure Preterm_dtype =
struct

  type overinfo = {Name : string,
                   Ty : Pretype.pretype,
                   Info : Overload.overloaded_op_info,
                   Locn : locn.locn}

  datatype preterm =
    Var of   {Name : string, Ty : Pretype.pretype, Locn : locn.locn}
  | Const of {Name : string, Thy : string, Ty : Pretype.pretype,
              Locn : locn.locn}
  | Overloaded of overinfo
  | Comb of  {Rator: preterm, Rand : preterm, Locn : locn.locn}
  | Abs of   {Bvar : preterm, Body : preterm, Locn : locn.locn}
  | Constrained of {Ptm:preterm, Ty: Pretype.pretype, Locn:locn.locn}
  | Antiq of {Tm:Term.term, Locn:locn.locn}
  | Pattern of {Ptm:preterm, Locn:locn.locn}
  (* | HackHack of bool -> bool *)
  (* Because of the Locn fields, preterms should *not* be compared
     with the built-in equality, but should use Preterm.eq.
     To check this has been done everywhere, uncomment this constructor. *)

end
