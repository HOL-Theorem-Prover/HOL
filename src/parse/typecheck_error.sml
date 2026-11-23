structure typecheck_error =
struct
  (* The messages carry the terms and types they talk about rather
     than their printed form, so that a consumer with somewhere to put
     them -- an editor that can show the type of a free variable the
     message mentions -- can get at them.  `errorMsg' still flattens
     to exactly the string it used to produce. *)
  datatype tcheck_error =
           ConstrainFail of Term.term * Type.hol_type * HOLmessage.message
         | AppFail of Term.term * Term.term * HOLmessage.message
         | OvlNoType of string * Type.hol_type
         | OvlTooMany
         | OvlFail
         | Misc of HOLmessage.message

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

  fun errorMessage tc =
    let val txt = HOLmessage.txt in
    case tc of
        ConstrainFail (_,_,msg) => msg
      | AppFail (_,_,msg) => msg
      | OvlNoType(s,_) =>
        (case pretty_internal_overload s of
             SOME desc => txt ("Couldn't infer a type for " ^ desc)
           | NONE => txt ("Couldn't infer type for overloaded name "^s))
      | OvlFail => txt "Overloading constraints were unsatisfiable"
      | OvlTooMany =>
          txt "There was more than one resolution of overloaded constants"
      | Misc m => m
    end

  fun errorMsg tc = HOLmessage.toString (errorMessage tc)

  fun misc s = Misc (HOLmessage.txt s)

  local
    open Feedback
  in
  fun mkExn (tc, loc) =
    mk_HOL_ERRlocm "Preterm" "type-analysis" loc (errorMessage tc)

  end (* local *)


end (* struct *)
