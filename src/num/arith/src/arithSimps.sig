   (* ---------------------------------------------------------------------
    * ARITH_ss : simpset
    * arith_ss : simpset
    *
    * The super-dooper "arith" simpset.  Based on "hol_ss"
    * Call ARITH_CONV to normalize linear formulae and prove
    * linear (in)equalities.  Cache the results.
    *
    * Note: ARITH_CONV normally only works on propositions.  This
    * simpset also reduces arithmetic formulae which can be
    * simplified.  How? We use an ML calculator
    * (see calculator.sml) to check out
    * whether terms can simplify after AC reorganisation and expansions
    * of multiplications.  If it looks like we can simplify, then
    * we call ARITH_CONV on what we think the theorem will simplify
    * to.
    *
    * When proving propositions, we want to run ARITH_CONV in the
    * "current context", utilising all the facts we have got from
    * the assumption list (in ASM_SIMP_TAC) and facts we have assumed
    * via congruence rules.  We filter these looking
    * for those which have something
    * to do with arithmetic, using "is_presburger" from by the "arith" library.
    * via congruence rules.  We filter these looking
    * for those which have something
    * to do with arithmetic, using "is_arith_clause" which searches for
    * nat equalities, inequalities and their negation.
    *
    * The cache is quite smart, in that it not only checks for
    * a previous attempt that produced a result under the same
    * context, but also for successful results that were proved in
    * smaller contexts, and unsucccessful results which failed
    * in larger contexts.
    *
    * arith_cache
    *
    * The cache.  Made visible to allow later analysis and other ops.
    *
    * ARITH_CCONV : thm list -> conv
    *
    * Call ARITH_CONV on the target term, adding the given
    * assumptions as antecedents.
    *
    * EXAMPLES
    *
    * ARITH_CCONV [ASSUME(--`x > z`--),ASSUME(--`y > x`--)] (--`z < y`--);
    *
    * delete_arith_caches
    *
    * Empties all arithmetic caches.
    * --------------------------------------------------------------------*)

signature arithSimps =
sig
 include Abbrev
 type ctxt (* = thm list *) (* this may become more sophisticted *)

     val ARITH_ss           : simpLib.ssdata
     val REDUCE_ss          : simpLib.ssdata
     val CTXT_ARITH         : ctxt -> conv
     val CACHED_ARITH       : ctxt -> conv
     val clear_arith_caches : unit -> unit
     val is_arith           : term -> bool
     val arith_cache        : Cache.cache
end
