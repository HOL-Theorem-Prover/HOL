structure sptreeLib :> sptreeLib =
struct

(* interactive use:
  app load ["ConseqConv", "wordsLib", "listLib"]
*)

open HolKernel Parse boolLib bossLib
open sptreeTheory sptreeSyntax;

val ERR = mk_HOL_ERR "sptree"

(* ------------------------------------------------------------------------- *)

local
   val times2_thm =
      GSYM (REWRITE_RULE [GSYM arithmeticTheory.TIMES2] numeralTheory.iDUB)
   val foldi_thms =
      CONJUNCTS
        (SIMP_RULE (bool_ss++boolSimps.LET_ss) [times2_thm]
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
         cnv tm
      end
end

local
   fun REC_LIST_BETA_CONV tm =
      (Drule.LIST_BETA_CONV
       THENC TRY_CONV (RAND_CONV REC_LIST_BETA_CONV)) tm
in
   val domain_CONV =
      Conv.REWR_CONV sptreeTheory.domain_foldi
      THENC foldi_CONV
      THENC REC_LIST_BETA_CONV
   val toAList_CONV =
      RATOR_CONV (Conv.REWR_CONV sptreeTheory.toAList_def)
      THENC foldi_CONV
      THENC REC_LIST_BETA_CONV
end

(* ------------------------------------------------------------------------- *)

end
