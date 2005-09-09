(* ----------------------------------------------------------------------
    CACHE

    Cache an operation which depends on a set of theorems as part of
    its input - e.g. "contextual" decision procedures such as
    CTXT_ARITH

    Two arguments are needed.  The first should determine if a given
    term is relevant to the decision procedure i.e., might be
    rewritten by it.  The second should be a conversion i.e. convert a
    term t to |- t = x for some value x.

    Returns a new conversion, and a reference to a table used as a
    cache.  The table is returned to enable users to analyse its
    contents

    The RCACHE variant of this function should be used for those
    functions where it is inappropriate to have hypotheses that don't
    include the variables mentioned in the "goal term", the one that
    is to be shown equal to some other value.  The extra, first,
    parameter to RCACHE is a function that when applied to a term that
    might be passed to the underlying decision procedure, returns a
    list of those terms within it that will be treated as variables.

    The relevance analysis behind RCACHE c will return a c' that
    strips out irrelevant hypotheses when checking to see if there is
    a cached failure.  Just in case the stripped out hypotheses are
    contradictory these will be tested for this (again, in independent
    groups).

   ---------------------------------------------------------------------- *)

signature Cache =
sig
  include Abbrev

  type cache
  val CACHE :(term -> bool) * (thm list->conv) -> (thm list -> conv) * cache
  val clear_cache : cache -> unit;
  val cache_values : cache -> (term * (term list * thm option) list) list
  val RCACHE : (term -> term list) * (term -> bool) * (thm list -> conv) ->
               (thm list -> conv) * cache
end
