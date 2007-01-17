(* ========================================================================= *)
(* FILE          : fcpLib.sml                                                *)
(* DESCRIPTION   : Tools for fcpTheory.                                      *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

structure fcpLib :> fcpLib =
struct

(* interactive use:
  app load ["pred_setTheory","fcpTheory"];
*)

open HolKernel Parse boolLib bossLib;
open Q numLib pred_setTheory;
open fcpTheory;

(* ------------------------------------------------------------------------- *)

fun index_type n =
  if n mod 2 = 0 then
    if n = 0 then
      raise ERR "mk_index" "index size must be non-zero"
    else
      mk_type("bit0", [index_type (n div 2)])
  else
    if n = 1 then
      mk_type("one", [])
    else
      mk_type("bit1", [index_type ((n - 1) div 2)]);

val INDEX_CONV =
   SIMP_CONV std_ss [index_one,index_bit0,index_bit1,
                     finite_one,finite_bit0,finite_bit1];

fun mk_index_type n =
  let val t = index_type n
      val N = Int.toString n
      val _ = type_abbrev("i" ^ N, t)
      val conv = INDEX_CONV o inst [alpha |-> t]
      val index_thm = save_thm("dimindex_" ^ N, conv ``dimindex(:'a)``)
      val finite_thm = save_thm("finite_" ^ N,
                         (EQT_ELIM o conv) ``FINITE(UNIV:'a->bool)``)
      val size_thm = save_thm("size" ^ N, PURE_REWRITE_RULE [index_thm]
            (MP (Thm.INST_TYPE [alpha |-> t] card_dimindex) finite_thm))
  in
    (finite_thm, size_thm, index_thm)
  end;

val FCP_ss = rewrites [FCP_BETA,FCP_ETA,CART_EQ];

end
