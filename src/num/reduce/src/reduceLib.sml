structure reduceLib :> reduceLib =
struct

open HolKernel Parse boolLib Boolconv Arithconv
     arithmeticTheory numeralTheory computeLib;

infix THEN |-> ;

fun failwith function = raise mk_HOL_ERR "reduceLib" function "";


(*-----------------------------------------------------------------------*)
(* RED_CONV - Try all the conversions in the library                     *)
(*-----------------------------------------------------------------------*)

val RED_CONV =
  let fun FAIL_CONV (s:string) tm = failwith s
  in
      FIRST_CONV
         [ADD_CONV,  AND_CONV,  BEQ_CONV,  COND_CONV, EVEN_CONV,
          DIV_CONV,  EXP_CONV,   GE_CONV,    GT_CONV, ODD_CONV,
          IMP_CONV,   LE_CONV,   LT_CONV,   MOD_CONV,
          MUL_CONV,  NEQ_CONV,  NOT_CONV,    OR_CONV,
          PRE_CONV,  SBC_CONV,  SUC_CONV] ORELSEC
      FAIL_CONV "RED_CONV"
  end;

(*-----------------------------------------------------------------------*)
(* REDUCE_CONV - Perform above reductions at any depth.                  *)
(* Uses computeLib.                                                      *)
(*-----------------------------------------------------------------------*)

val numeral_redns =
 lazyfy_thm arithmeticTheory.num_case_compute
  :: [numeral_distrib, numeral_eq, numeral_suc, numeral_pre, NORM_0,
      numeral_iisuc, numeral_add, internal_mult_characterisation, iDUB_removal,
      numeral_sub, numeral_lt, numeral_lte, iSUB_THM,
      numeral_exp, numeral_evenodd, iSQR, numeral_fact,numeral_funpow,
      numeral_MAX, numeral_MIN, numeral_div2, MOD_2EXP, numeral_imod_2exp,
      TWO_EXP_THM, numeral_texp_help, exactlog_def, onecount_def, DIV2_BIT1,
      enumeral_mult];

val div_thm =
    prove
      (Term `!x y q r.
          x DIV y = if (x = q * y + r) /\ (r < y) then q else x DIV y `,
       REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN
       MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC (Term `r:num`) THEN
       ASM_REWRITE_TAC []);

val mod_thm =
    prove
      (Term `!x y q r.
          x MOD y = if (x = q * y + r) /\ r<y then r else x MOD y`,
       REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN
       MATCH_MP_TAC MOD_UNIQUE THEN EXISTS_TAC (Term `q:num`) THEN
       ASM_REWRITE_TAC []);


fun cbv_DIV_CONV tm =
 let open Arbnum numSyntax
     val (x,y) = dest_div tm
     val (q,r) = divmod (dest_numeral x, dest_numeral y)
 in SPECL [x, y, mk_numeral q, mk_numeral r] div_thm
 end
 handle HOL_ERR _ => failwith "cbv_DIV_CONV"
      | Div => failwith "cbv_DIV_CONV"

fun cbv_MOD_CONV tm =
 let open Arbnum numSyntax
     val (x,y) = dest_mod tm
     val (q,r) = divmod (dest_numeral x, dest_numeral y)
 in SPECL [x, y, mk_numeral q, mk_numeral r] mod_thm
 end handle HOL_ERR _ => failwith "cbv_MOD_CONV"
          | Div => failwith "cbv_MOD_CONV";


fun num_compset () =
  let open computeLib
      val compset = bool_compset()
      val _ = add_thms numeral_redns compset
      val _ = add_conv (numSyntax.div_tm, 2, cbv_DIV_CONV) compset
      val _ = add_conv (numSyntax.mod_tm, 2, cbv_MOD_CONV) compset
  in
    compset
  end;


(*---------------------------------------------------------------------------
      Add numeral reductions to global compset
 ---------------------------------------------------------------------------*)

val _ = let open computeLib
        in add_funs numeral_redns;
           add_conv (numSyntax.div_tm, 2, cbv_DIV_CONV) the_compset;
           add_conv (numSyntax.mod_tm, 2, cbv_MOD_CONV) the_compset
        end;


(*-----------------------------------------------------------------------*)
(* REDUCE_{CONV,RULE,TAC} - conversions, rule and tactic versions of     *)
(* reduction.                                                            *)
(*-----------------------------------------------------------------------*)

val REDUCE_CONV = let
  val cs = num_compset ()
  val _ = computeLib.set_skip cs boolSyntax.conditional NONE
          (* ensure that REDUCE_CONV will look at all of a term, even
             conditionals' branches *)
in
  computeLib.CBV_CONV cs
end

val REDUCE_RULE = CONV_RULE REDUCE_CONV;

val REDUCE_TAC = CONV_TAC REDUCE_CONV;

val _ = Defn.const_eq_ref := NEQ_CONV;

end;
