signature Termtable = sig
   type term = Term.term
   type 'a termtable
   val mk_termtable : (int * exn) -> '_a termtable
   val termtable_insert : '_a termtable -> (term list * term) * '_a -> unit
   val termtable_find : 'a termtable -> (term list * term) -> 'a
   val termtable_list : 'a termtable -> ((term list * term) * 'a) list

end (* sig *)




