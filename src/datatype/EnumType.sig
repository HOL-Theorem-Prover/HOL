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

  (*  *)

  val enum_type_to_tyinfo : string * string list -> tyinfo * string

  val update_tyinfo : string -> thm -> thm -> tyinfo -> tyinfo

end

(*

   [enum_type_to_tyinfo] takes a string-string list pair corresponding
   to the name of the type and its constructors.  Returns a tyinfo
   along with a string that is the ML for the appropriate invocation
   of update_tyinfo.

   [update_tyinfo s eqth repth tyinfo0] takes s, the name of an enumerated
   type, and two theorems.  eqth is of the form
         !v1 v2. (v1 = v2) = (rep v1 = rep v2)
   and repth is of the form
         (rep C1 = 0) /\ (rep C2 = 1) /\ ... /\ (rep Cn = n - 1)
   This updates tyinfo0 to include a conversion in its simpls component
   which resolves  equalities between members of the enumerated type.

*)
