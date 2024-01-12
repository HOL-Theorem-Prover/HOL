structure sptreeLib :> sptreeLib =
struct

open HolKernel Parse boolLib bossLib
open sptreeTheory sptreeSyntax numeral_bitTheory;

val ERR = mk_HOL_ERR "sptree"

(* ------------------------------------------------------------------------- *)

local
   val times2_thm =
      GSYM (REWRITE_RULE [GSYM arithmeticTheory.TIMES2] numeralTheory.iDUB)
   val foldi_thms =
      CONJUNCTS (SIMP_RULE (bool_ss++boolSimps.LET_ss) [times2_thm]
                   sptreeTheory.foldi_def)
   val lrnext_cnv =
      let open numeralTheory in
         PURE_REWRITE_CONV
            [REWRITE_RULE [times2_thm] sptreeTheory.lrnext_thm, numeral_distrib,
             numeral_add, numeral_suc, numeral_iisuc, iDUB_removal,
             numeral_distrib, arithmeticTheory.NORM_0,
             numeral_bitTheory.iDUB_NUMERAL]
      end
   val lrnext_cnv = RATOR_CONV (RATOR_CONV (RAND_CONV lrnext_cnv))
   fun REC_LIST_BETA_CONV tm =
      (Drule.LIST_BETA_CONV THENC TRY_CONV (RAND_CONV REC_LIST_BETA_CONV)) tm
in
   fun foldi_CONV tm =
      let
         val (f, _, _, _) = sptreeSyntax.dest_foldi tm
         val (ln_th, ls_th, bn_th, bs_th) =
            Lib.quadruple_of_list (List.map (Drule.ISPEC f) foldi_thms)
         val ln_cnv = Conv.REWR_CONV ln_th
         val ls_cnv = Conv.REWR_CONV ls_th THENC lrnext_cnv
         val bn_cnv = Conv.REWR_CONV bn_th
         val bs_cnv = Conv.REWR_CONV bs_th
         fun cnv tm =
            case boolSyntax.dest_strip_comb (rand tm) of
               ("sptree$LN", []) => ln_cnv tm
             | ("sptree$LS", [_]) => ls_cnv tm
             | ("sptree$BN", [_, _]) =>
                  (bn_cnv
                   THENC RATOR_CONV (RAND_CONV (lrnext_cnv THENC cnv))
                   THENC lrnext_cnv
                   THENC cnv) tm
             | ("sptree$BS", [_, _, _]) =>
                  (bs_cnv
                   THENC RATOR_CONV
                            (RAND_CONV (RAND_CONV (lrnext_cnv THENC cnv)))
                   THENC lrnext_cnv
                   THENC cnv) tm
             | _ => raise ERR "foldi_CONV" ""
      in
         (cnv THENC REC_LIST_BETA_CONV) tm
      end
end

val domain_CONV = Conv.REWR_CONV sptreeTheory.domain_foldi THENC foldi_CONV

val toAList_CONV =
  RATOR_CONV (Conv.REWR_CONV sptreeTheory.toAList_def) THENC foldi_CONV

fun add_sptree_compset compset =
    let
      open sptreeTheory
    in
      computeLib.add_thms [
        apsnd_cons_def,
        combine_rle_def,
        delete_compute,
        difference_def,
        filter_v_def,
        fromAList_def,
        fromList_def,
        insert_compute,
        inter_def,
        inter_eq_def,
        list_insert_def,
        list_to_num_set_def,
        lookup_compute,
        lrnext_thm,
        map_def,
        mapi_def,
        mapi0_def,
        mk_BN_def,
        mk_BS_def,
        mk_wf_def,
        size_def,
        spt_center_def,
        spt_centers_def,
        spt_left_def,
        spt_right_def,
        spts_to_alist_def,
        toListA_def,
        toList_def,
        toSortedAList_def,
        union_def,
        wf_def
      ] compset
    ; computeLib.add_conv (sptreeSyntax.foldi_tm, 4, foldi_CONV) compset
    ; computeLib.add_conv (sptreeSyntax.domain_tm, 1, domain_CONV) compset
    ; computeLib.add_conv (sptreeSyntax.toAList_tm, 1, toAList_CONV) compset
    ; computeLib.add_datatype_info compset
            (Option.valOf (TypeBase.fetch ``:'a sptree$spt``))
    end

val SPTREE_CONV =
   let
      val c = reduceLib.num_compset ()
   in
       add_sptree_compset c
     ; computeLib.CBV_CONV c
   end

(* ------------------------------------------------------------------------- *)

end
