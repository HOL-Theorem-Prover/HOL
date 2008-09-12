signature intSimps =
sig
  include Abbrev

  (* stuff from intReduce for the sake of backwards compatibility *)
  val int_compset   : unit -> computeLib.compset

  val REDUCE_CONV   : term -> thm
  val RED_CONV      : term -> thm

  val INT_REDUCE_ss : simpLib.ssfrag

  val collect_additive_consts : term -> thm
  (* collects all integer literals in an additive term and sums them;
     e.g.:  3 + x + ~1  --> x + 2
     the collected numeral always appears on the right,
     fails if there is no collecting to be done *)

  val INT_RWTS_ss   : simpLib.ssfrag

  val int_ss        : simpLib.simpset

  val INT_MUL_AC_ss : simpLib.ssfrag
  val INT_ADD_AC_ss : simpLib.ssfrag
  val INT_AC_ss     : simpLib.ssfrag

  (* decision procedure fragments *)
  val INT_ARITH_ss  : simpLib.ssfrag  (* = OMEGA for the moment *)
  val OMEGA_ss      : simpLib.ssfrag
  val COOPER_ss     : simpLib.ssfrag
  val omega_cache   : Cache.cache
  val cooper_cache  : Cache.cache



  val ADDL_CANON_CONV : term -> thm
    (* collects up all terms, summing coefficients.  Does more than
       collect_additive_consts therefore.  Left-associates. *)
  val ADDR_CANON_CONV : term -> thm
    (* collects up all terms, summing coefficients.  Does more than
       collect_additive_consts therefore.  Right-associates. *)

end;
