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

fun mk_in_conv eval tm =
  case strip_comb tm
   of (c,[a1,a2]) =>
        if same_const c in_tm
        then if is_set_spec a2 then SET_SPEC_CONV tm else
             IN_CONV eval tm
        else raise ERR "in_conv" "not an IN term"
    | otherwise => raise ERR "in_conv" "not an IN term";

(*---------------------------------------------------------------------------*)

local open Tactic Conv Tactical in
fun MAX_SET_elim_tac (g as (_, w)) = let
  val t = find_term is_max_set w
in
  CONV_TAC (UNBETA_CONV t) THEN
  MATCH_MP_TAC pred_setTheory.MAX_SET_ELIM THEN BETA_TAC
end g
end

(*---------------------------------------------------------------------------*)
(* Set up computeLib for sets                                                *)
(*---------------------------------------------------------------------------*)

local
  val thms =
    let
      val T_INTRO =
       let open boolLib Drule
       in Rewrite.PURE_ONCE_REWRITE_RULE
                    [SYM (hd(tl (CONJUNCTS (SPEC_ALL EQ_CLAUSES))))]
       end
      open pred_setTheory Drule
    in
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
    end
in
  fun add_pred_set_compset compset =
    let
      val eval = computeLib.CBV_CONV compset
      val convs =
           [ (in_tm, 2, mk_in_conv eval),
             (insert_tm, 2, INSERT_CONV eval),
             (card_tm, 1, CARD_CONV),
             (max_set_tm, 1, MAX_SET_CONV),
             (sum_image_tm, 2, SUM_IMAGE_CONV)
           ]
    in
      List.app (Lib.C computeLib.add_conv compset) convs ;
      computeLib.add_thms thms compset
    end
end

val _ = add_pred_set_compset computeLib.the_compset


end
