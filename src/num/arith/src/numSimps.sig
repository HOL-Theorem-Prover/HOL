signature numSimps =
sig
 include Abbrev
 type ctxt

     val ARITH_ss           : simpLib.ssdata
     val REDUCE_ss          : simpLib.ssdata
     val CTXT_ARITH         : ctxt -> conv
     val CACHED_ARITH       : ctxt -> conv
     val clear_arith_caches : unit -> unit
     val is_arith           : term -> bool
     val is_arith_asm       : term -> bool
     val arith_cache        : Cache.cache
end

(*

   [ARITH_ss] is a "simpset fragment" containing a cache-based instance of
   ARITH_CONV for deciding universal Presburger formulas over the natural
   numbers, as well as a "linear reducer", which attempts to normalise
   arithmetic expressions over the natural numbers (collecting up like
   terms etc).

   [REDUCE_ss] is a "simpset fragment" that reduces ground arithmetic
   expressions.  I.e., ``2 EXP 100``, but not ``x * 3``.

   [is_arith t] is true if t is a term which ARITH_CONV might be able to
   prove true.

   [is_arith_asm t] is true if t might be added to a goal as an extra
   hypothesis without confusing ARITH_CONV.

   [arith_cache] is the cache on which ARITH_ss relies.

*)