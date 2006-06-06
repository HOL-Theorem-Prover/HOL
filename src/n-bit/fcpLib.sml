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

fun enum_pred k =
 let val n = mk_var("n",num)
     val topnum = term_of_int k
 in mk_abs(n,mk_less(n,topnum))
 end;

fun type_exists k =
 let val n = mk_var("n",num)
 in Tactical.prove (mk_exists(n, mk_comb(enum_pred k, n)),
                    Tactic.EXISTS_TAC numSyntax.zero_tm THEN REDUCE_TAC)
 end;

fun prove_image_thm abs sz bij = prove(
  `IMAGE ^abs (count ^sz) = UNIV`,
  RW_TAC std_ss [IMAGE_DEF,EXTENSION,IN_UNIV,GSPECIFICATION,count_def]
    THEN PROVE_TAC [bij]);

fun prove_bij_image_thm abs sz bij = prove(
  `BIJ ^abs (count ^sz) (IMAGE ^abs (count ^sz))`,
  RW_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IMAGE_DEF,EXTENSION,
    GSPECIFICATION,count_def] THEN PROVE_TAC [bij]);

fun prove_finite_thm img_thm abs sz = (REWRITE_RULE [img_thm] o Drule.ISPEC abs)
  (MATCH_MP (ISPEC `count ^sz` IMAGE_FINITE) (Thm.SPEC sz FINITE_COUNT));

local val _ = set_trace "meson" 0 in
fun mk_index_type n =
  let val N = Int.toString n
      val ABS = "abs_"^N
      val REP = "rep_"^N
      val tydef = new_type_definition("i"^N, type_exists n)
      val bij = BETA_RULE (define_new_type_bijections {ABS=ABS, REP=REP,
                  name="index"^N^"_bij", tyax=tydef})
      val TYPE = mk_type("i"^N, [])
      val n_term = (mk_numeral o Arbnum.fromInt) n
      val abs_term = mk_const(ABS,num --> TYPE)
      val rep_term = mk_const(REP,TYPE --> num)
      val tyitself = mk_thy_type{Args = [TYPE], Thy = "bool", Tyop = "itself"}
      val univ_term = mk_thy_const{Name = "the_value", Thy = "bool",
                                   Ty = tyitself}
      val image_thm = prove_image_thm abs_term n_term bij
      val bij_abs_thm = prove_bij_image_thm abs_term n_term bij
      val finite_thm = save_thm("finite_"^N,
            prove_finite_thm image_thm abs_term n_term)
      val size_thm = save_thm("size_"^N,
            REWRITE_RULE [image_thm] (MATCH_MP index_size bij_abs_thm))
      val dimindex_thm =
            store_thm("dimindex_"^N, `dimindex ^univ_term = ^n_term`,
              PROVE_TAC [finite_thm,size_thm,dimindex])
      val _ = computeLib.add_thms [finite_thm, size_thm, dimindex_thm]
              computeLib.the_compset
  in
    (finite_thm, size_thm, dimindex_thm)
  end
end

val FCP_ss = rewrites [FCP_BETA,FCP_ETA,CART_EQ];

end
