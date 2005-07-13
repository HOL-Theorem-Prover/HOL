signature realSimps =
sig

  (* Useful rewrites for basic real arithmetic *)
  val real_SS : simpLib.ssfrag

  (* performs calculations over rational values *)
  val REAL_REDUCE_ss : simpLib.ssfrag

  (* Incorporates simpsets for bool, pair, and arithmetic as well  *)
  val real_ss : simpLib.simpset

  (* AC rewrites for + and *: occasionally useful *)
  val real_ac_SS : simpLib.ssfrag

  (* the RealArith decision procedure *)
  val REAL_ARITH_ss : simpLib.ssfrag
  val arith_cache : Cache.cache (* the cache of results behind it *)

  (* Incorporates the real simpset *)
  val real_ac_ss : simpLib.simpset

  val real_compset : unit -> computeLib.compset

end
