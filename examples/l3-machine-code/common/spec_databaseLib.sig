signature spec_databaseLib =
sig
   datatype ''opt entry = Pending of Thm.thm * Term.term
                        | Built of (''opt list * Thm.thm) list
   val mk_spec_database:
      (unit -> ''a) -> ''a -> (''a -> ''b) -> (''a -> ''a -> int) ->
      (''a -> ''a -> Drule.rule) -> (Thm.thm -> Term.term) ->
      (Thm.thm * Term.term -> Thm.thm) ->
      (unit -> unit) * (''a -> unit) * (unit -> ''a) *
      (Thm.thm * Term.term -> unit) *
      (Term.term -> (bool * Thm.thm list) option) *
      (unit -> (Term.term * ''a entry) list)
end
