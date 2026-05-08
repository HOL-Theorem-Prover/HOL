structure typecheck_error =
struct
  datatype tcheck_error =
           ConstrainFail of Term.term * Type.hol_type * string
         | AppFail of Term.term * Term.term * string
         | OvlNoType of string * Type.hol_type
         | OvlTooMany
         | OvlFail
         | Misc of string

  type error = tcheck_error * locn.locn
  (* Some overloaded names are internal placeholders that the parser
     wraps around literals before type elaboration (e.g. the numeric
     literal injection `_ inject_number`, the various `_ inject_string…`
     entries for character/string literals).  Showing these raw to the
     user is unhelpful — they don't appear in any source they wrote.
     Map a recognised internal name to a description of what kind of
     literal it represents; return NONE for ordinary overloads. *)
  fun pretty_internal_overload s =
      if s = GrammarSpecials.fromNum_str then
        SOME "the numeric literal"
      else if String.isPrefix GrammarSpecials.stringinjn_base s then
        SOME "the string/character literal"
      else
        NONE

  fun errorMsg tc =
    case tc of
        ConstrainFail (_,_,msg) => msg
      | AppFail (_,_,msg) => msg
      | OvlNoType(s,_) =>
        (case pretty_internal_overload s of
             SOME desc => "Couldn't infer a type for " ^ desc
           | NONE => "Couldn't infer type for overloaded name "^s)
      | OvlFail => "Overloading constraints were unsatisfiable"
      | OvlTooMany =>
          "There was more than one resolution of overloaded constants"
      | Misc s => s

  local
    open Feedback
  in
  fun mkExn (tc, loc) =
    mk_HOL_ERRloc "Preterm" "type-analysis" loc (errorMsg tc)

  end (* local *)


end (* struct *)
