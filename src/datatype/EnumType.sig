signature EnumType = sig
  include Abbrev
  val define_enum_type :
      (string * string list * string * string) ->
      {TYPE     : hol_type,
       constrs  : term list,
       defs     : thm list,
       ABSconst : term,
       REPconst : term,
       ABS_REP  : thm,
       REP_ABS  : thm,
       ABS_11   : thm,
       REP_11   : thm,
       ABS_ONTO : thm,
       REP_ONTO : thm,
       simpls   : thm list}

  val enum_type_to_tyinfo : (string * string list) -> TypeBase.TypeInfo.tyinfo


end;

