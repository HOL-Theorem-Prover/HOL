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
  fun errorMsg tc =
    case tc of
        ConstrainFail (_,_,msg) => msg
      | AppFail (_,_,msg) => msg
      | OvlNoType(s,_) =>
        ("Couldn't infer type for overloaded name "^s)
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
