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
     val arith_cache        : Cache.cache
end
