signature EnumType =
sig
  include Abbrev
  type tyinfo = TypeBasePure.tyinfo

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
       REP_ONTO : thm}

  (* Takes a string-string list pair corresponding to the name of the  *)
  (* and its constructors.  Returns a tyinfo along with a list of the names *)
  (* of the extra theorems that have been added to the tyinfo as *)
  (* simplifications *)

  val enum_type_to_tyinfo : string * string list -> tyinfo * string list

end

