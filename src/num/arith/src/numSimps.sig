signature numSimps =
sig
 include Abbrev
 type ctxt

     val ARITH_ss           : simpLib.ssdata
     val REDUCE_ss          : simpLib.ssdata
     val SUC_FILTER_ss      : simpLib.ssdata
     val ARITH_DP_ss        : simpLib.ssdata
     val ARITH_RWTS_ss      : simpLib.ssdata
     val ARITH_AC_ss        : simpLib.ssdata
     val CTXT_ARITH         : ctxt -> conv
     val CACHED_ARITH       : ctxt -> conv
     val clear_arith_caches : unit -> unit
     val is_arith           : term -> bool
     val is_arith_asm       : term -> bool
     val arith_cache        : Cache.cache
end

(*

   [ARITH_ss] is a "simpset fragment" merging ARITH_DP_ss and
   ARITH_RWTS_ss.

   [ARITH_DP_ss] is a "simpset fragment" containing a cache-based
   instance of ARITH_CONV for deciding universal Presburger formulas
   over the natural numbers, and a "linear reducer", which attempts to
   normalise arithmetic expressions over the natural numbers
   (collecting up like terms etc).

   [ARITH_RWTS_ss] is a collection of "obvious" arithmetic identities.

   [ARITH_AC_ss] is an "AC" simpset fragment comprising the assoc-comm
   rules for addition and multiplication.

   [REDUCE_ss] is a "simpset fragment" that reduces ground arithmetic
   expressions.  I.e., ``2 EXP 100``, but not ``x * 3``.

   [SUC_FILTER_ss] is a "simpset fragment" that causes the simpset it
   is merged into to subsequently modify input rewrite theorems so
   that patterns over SUC match more readily.

   [is_arith t] is true if t is a term which ARITH_CONV might be able to
   prove true.

   [is_arith_asm t] is true if t might be added to a goal as an extra
   hypothesis without confusing ARITH_CONV.

   [arith_cache] is the cache on which ARITH_ss relies.

*)
