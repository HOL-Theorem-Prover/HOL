(*------------------------------------------------------------------------
 *  First order unification restricted to specified "scheme" variables.
 *
 *----------------------------------------------------------------------*)

signature Unify = sig
 type term = Term.term

   (* these don't do type unification *)
   val simp_unify_terms_in_env : 
     term list -> term -> term -> (term * term)list -> (term * term)list
   val simp_unify_terms : term list -> term -> term -> (term * term)list

   (* use these to look up the results that are returned *)
   val deref_tmenv : (term * term)list -> term -> term

   (* discard some (local) instantiations from an environment *)
   val restrict_tmenv :(term -> bool) -> (term * term)list -> (term * term)list 

end (* sig *)

