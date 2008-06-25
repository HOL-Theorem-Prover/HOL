structure pred_setLib :> pred_setLib =
struct

local open pred_setTheory in end

open Abbrev HolKernel PFset_conv pred_setSyntax;

val SET_SPEC_CONV  = PGspec.SET_SPEC_CONV pred_setTheory.GSPECIFICATION
val SET_INDUCT_TAC = PSet_ind.SET_INDUCT_TAC pred_setTheory.FINITE_INDUCT
val PRED_SET_ss    = pred_setSimps.PRED_SET_ss

val ERR = mk_HOL_ERR "pred_setLib";

(*---------------------------------------------------------------------------*)
(* Evaluates terms of the form                                               *)
(*                                                                           *)
(*     tm IN {e1; ...; en}  and                                              *)
(*     tm IN {t | p}                                                         *)
(*---------------------------------------------------------------------------*)

fun in_conv tm = 
  case strip_comb tm
   of (c,[a1,a2]) =>
        if same_const c in_tm
        then if is_set_spec a2 then SET_SPEC_CONV tm else
             IN_CONV computeLib.EVAL_CONV tm 
        else raise ERR "in_conv" "not an IN term"
    | otherwise => raise ERR "in_conv" "not an IN term";

(*---------------------------------------------------------------------------*)
(* Set up computeLib for sets                                                *)
(*---------------------------------------------------------------------------*)

val _ = computeLib.add_convs
         [ (in_tm, 2, in_conv),
           (insert_tm, 2, fn tm => INSERT_CONV computeLib.EVAL_CONV tm),
           (card_tm, 1, CARD_CONV),
           (max_set_tm, 1, MAX_SET_CONV),
           (sum_image_tm, 2, SUM_IMAGE_CONV)
         ];


val T_INTRO = 
 let open boolLib Drule
 in Rewrite.PURE_ONCE_REWRITE_RULE 
              [SYM (hd(tl (CONJUNCTS (SPEC_ALL EQ_CLAUSES))))]
 end;

val _ = 
 let open pred_setTheory Drule
 in
  computeLib.add_funs 
     [INTER_EMPTY,INSERT_INTER, 
      CONJ (CONJUNCT1 UNION_EMPTY) INSERT_UNION,
      CONJ EMPTY_DELETE DELETE_INSERT,
      CONJ DIFF_EMPTY DIFF_INSERT,
      CONJ (T_INTRO (SPEC_ALL EMPTY_SUBSET)) INSERT_SUBSET,
      PSUBSET_EQN,
      CONJ IMAGE_EMPTY IMAGE_INSERT,
      CONJ BIGUNION_EMPTY BIGUNION_INSERT,
      LIST_CONJ [BIGINTER_EMPTY,BIGINTER_SING, BIGINTER_INSERT], 
      CONJ (T_INTRO (CONJUNCT1 (SPEC_ALL DISJOINT_EMPTY))) DISJOINT_INSERT,
      CROSS_EQNS,CONJUNCT1(SPEC_ALL CROSS_EMPTY),
      FINITE_INSERT, FINITE_EMPTY,
      MIN_SET_THM,
      count_EQN,
      CONJUNCT1 MAX_SET_THM,  
      CARD_EMPTY, SUM_SET_DEF,
      CONJUNCT1 (SPEC_ALL SUM_IMAGE_THM),
      SET_EQ_SUBSET, IN_COMPL, POW_EQNS
     ]
 end;

end
