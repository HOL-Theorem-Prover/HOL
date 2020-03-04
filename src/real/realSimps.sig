signature realSimps =
sig

  include Abbrev
  (* eliminates common factors in divisions *)
  val elim_common_factor : Term.term -> Thm.thm

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

  (* canonicalise additive and multiplicative terms; with addcanon calling
     mulcanon on each summand *)
  val REALADDCANON : conv
  val REALMULCANON : conv
  val RMULCANON_ss : simpLib.ssfrag
  val RADDCANON_ss : simpLib.ssfrag

  (* put literal values into a canonical form:
     - integral values are left alone
     - inverses applied to integers are turned into 1/n
     - negative signs are moved to denominators
     - fractions are reduced by gcds
  *)
  val REAL_LITCANON : conv

  (* eliminate common terms from either side of a relation symbol, factoring
     as necessary.  First argument is relation symbol, second is list of
     theorems justifying removal of common factors on left.
     Third argument is solver to discharge side conditions to
     do with non-zero ness and signs. The list passed to it is the stack of
     previous side condition attempts. *)
  val mulrelnorm : term -> thm list ->
                   (term list -> term -> thm) ->
                   term list -> term -> thm
  val RMULRELNORM_ss : simpLib.ssfrag


  val real_compset : unit -> computeLib.compset

end
