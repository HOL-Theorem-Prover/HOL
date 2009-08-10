(*------------------------------------------------------------------------
 *  First order unification restricted to specified "scheme" variables.
 *
 *----------------------------------------------------------------------*)

signature Unify =
sig
  include Abbrev

   (* these don't do type unification *)

   val simp_unify_terms_in_env :
     term list -> term -> term -> (term,term)subst -> (term,term)subst
   val simp_unify_terms : term list -> term -> term -> (term,term)subst

   (* use these to look up the results that are returned *)

   val deref_tmenv : (term,term)subst -> term -> term

   (* discard some (local) instantiations from an environment *)

   val restrict_tmenv :(term -> bool) -> (term,term)subst -> (term,term)subst

end

