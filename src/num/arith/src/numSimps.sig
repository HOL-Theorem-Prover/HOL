signature numSimps =
sig
  include Abbrev
  type ctxt = thm list

     val ARITH_ss           : simpLib.ssfrag
     val REDUCE_ss          : simpLib.ssfrag
     val SUC_FILTER_ss      : simpLib.ssfrag
     val ARITH_DP_ss        : simpLib.ssfrag
     val ARITH_DP_FILTER_ss : (thm -> bool) -> simpLib.ssfrag
     val ARITH_RWTS_ss      : simpLib.ssfrag
     val ARITH_AC_ss        : simpLib.ssfrag
     val ARITH_NORM_ss      : simpLib.ssfrag
     val MOD_ss             : simpLib.ssfrag

     val CTXT_ARITH         : ctxt -> conv
     val CACHED_ARITH       : ctxt -> conv
     val clear_arith_caches : unit -> unit
     val is_arith           : term -> bool
     val is_arith_asm       : term -> bool
     val arith_cache        : Cache.cache

     val ADDL_CANON_CONV     : conv
     val ADDR_CANON_CONV     : conv
     val MUL_CANON_CONV     : conv


    (* deprecated *)
    val old_ARITH_ss        : simpLib.ssfrag
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
   rules for addition and multiplication.  NB: in general this fragment
   cannot be used in conjunction with arith_ss or ARITH_ss.

   [REDUCE_ss] is a "simpset fragment" that reduces ground arithmetic
   expressions.  I.e., ``2 EXP 100``, but not ``x * 3``.

   [SUC_FILTER_ss] is a "simpset fragment" that causes the simpset it
   is merged into to subsequently modify input rewrite theorems so
   that patterns over SUC match more readily.

   [MOD_ss] is a "simpset fragment" that helps in the simplification
   of terms involving MOD.

   [is_arith t] is true if t is a term which ARITH_CONV might be able to
   prove true.

   [is_arith_asm t] is true if t might be added to a goal as an extra
   hypothesis without confusing ARITH_CONV.

   [arith_cache] is the cache on which ARITH_ss relies.

   [ADDR_CANON_CONV t] normalises additive term t, collecting up terms with
   common bases and summing coefficients.  Additions are right-associated with
   constants appearing to the right.

   [ADDL_CANON_CONV t] normalises additive term t, collecting up terms with
   common bases and summing coefficients.  Additions are left-associated with
   constants appearing to the right.

   [MUL_CANON_CONV t] normalises multiplicative term t, collecting up terms
   with common bases and summing exponents.  Multiplications are left-
   associated, except that constants appear separately to the left (thus
   making such terms appropriate coefficient-base pairs).



   [old_ARITH_ss] is an old version of ARITH_ss that does less
   normalisation of arithmetic expressions.  Here for some backwards
   compatibility support.

*)
