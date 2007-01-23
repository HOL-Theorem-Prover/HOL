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
  app load ["fcpTheory"];
*)

open HolKernel Parse boolLib bossLib;
open Q computeLib fcpTheory;

(* ------------------------------------------------------------------------- *)

fun index_type n =
  let open Arbnum in
    if mod2 n = zero then
      if n = zero then
        raise ERR "mk_index" "index size must be non-zero"
      else
        mk_type("bit0", [index_type (div2 n)])
    else
      if n = one then
        mk_type("one", [])
      else
        mk_type("bit1", [index_type (div2 (less1 n))])
  end;

fun index_compset () =
  let val compset = reduceLib.num_compset()
      val _ = add_thms [index_one,index_bit0,index_bit1,
                        finite_one,finite_bit0,finite_bit1] compset
in
  compset
end;

val INDEX_CONV = CHANGED_CONV (CBV_CONV (index_compset()));

fun conv n = INDEX_CONV o inst [alpha |-> index_type n];

fun DIMINDEX n = conv n ``dimindex(:'a)``;

fun FINITE n = (EQT_ELIM o conv n) ``FINITE(UNIV:'a->bool)``;

fun SIZE n = PURE_REWRITE_RULE [DIMINDEX n]
               (MP (Thm.INST_TYPE [alpha |-> index_type n] card_dimindex)
                   (FINITE n));

val FCP_ss = rewrites [FCP_BETA,FCP_ETA,CART_EQ];

end
