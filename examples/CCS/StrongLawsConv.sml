(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure StrongLawsConv :> StrongLawsConv =
struct

open HolKernel Parse boolLib bossLib;
open prim_recTheory arithmeticTheory numTheory numLib;
open PFset_conv IndDefRules listSyntax stringLib;

open CCSLib CCSTheory CCSSyntax CCSConv;
open StrongEQTheory StrongEQLib StrongLawsTheory;

infixr 0 S_THENC S_ORELSEC;

(******************************************************************************)
(*                                                                            *)
(*       Conversions for the summation operator and strong equivalence        *)
(*                                                                            *)
(******************************************************************************)

fun STRONG_SUM_ASSOC_CONV tm = let
    val (a,b) = args_sum tm
in
    if is_sum b then
        let val (b1, b2) = args_sum b;
            val thm = ISPECL [a, b1, b2] STRONG_SUM_ASSOC_L;
            val thm' = STRONG_SUM_ASSOC_CONV (rhs_tm thm)
        in
            S_TRANS thm thm'
        end
    else if is_sum a then
        let val thm'' = STRONG_SUM_ASSOC_CONV a
        in
            ISPEC b (MATCH_MP STRONG_EQUIV_SUBST_SUM_R thm'')
        end
    else
        ISPEC tm STRONG_EQUIV_REFL
end;

(* Conversion for the application of STRONG_SUM_IDENT(_L/R). *)
fun STRONG_SUM_NIL_CONV tm =
  if is_sum tm then
    let
        val (t1, t2) = args_sum tm
    in
        if is_nil t1 then
            ISPEC t2 STRONG_SUM_IDENT_L
        else if is_nil t2 then
            ISPEC t1 STRONG_SUM_IDENT_R
        else
            failwith "STRONG_SUM_NIL_CONV"
    end
  else
      failwith "STRONG_SUM_NIL_CONV";

(* Find repeated occurrences of a summand to be then deleted by applying
   STRONG_SUM_IDEMP. *)
fun STRONG_FIND_IDEMP tm l =
  let
    val h::t = l
  in
    if null t then
      failwith "term not a CCS summation"
    else
      let
        val tm' = fst (args_sum tm)
      in
        if tmem h t then
          let val (l1, l2) = FIND_SMD [] h [] tm'
          in
                    if (null l2) then
                        if (null l1) then
                            ISPEC h STRONG_SUM_IDEMP
                        else
                            let val y = hd l1
                            in
                                S_TRANS (ISPECL [y, h, h] STRONG_SUM_ASSOC_R)
                                        (ISPEC y (MP (ISPECL [mk_sum (h, h), h] STRONG_EQUIV_SUBST_SUM_R)
                                                    (ISPEC h STRONG_SUM_IDEMP)))
                            end
                    else
                        let val thm1 =
                                if (null l1) then
                                    S_TRANS (S_SYM (STRONG_SUM_ASSOC_CONV
                                                        (mk_sum (mk_sum (h, hd l2), h))))
                                            (ISPECL [h, hd l2] STRONG_SUM_MID_IDEMP)
                                else
                                    S_TRANS (S_SYM (STRONG_SUM_ASSOC_CONV
                                                        (mk_sum (mk_sum (mk_sum (hd l1, h), hd l2), h))))
                                            (ISPECL [hd l1, h, hd l2] STRONG_LEFT_SUM_MID_IDEMP)
                        in
                            S_TRANS thm1 (STRONG_SUM_ASSOC_CONV (snd (args_thm thm1)))
                        end
                end
            else
                let val thm' = STRONG_FIND_IDEMP tm' t
                in
                    ISPEC h (MATCH_MP STRONG_EQUIV_SUBST_SUM_R thm')
                end
        end
end;

(* Conversion for the application of STRONG_SUM_IDEMP. *)
fun STRONG_SUM_IDEMP_CONV tm =
  if is_sum tm then
      let val thm = STRONG_SUM_ASSOC_CONV tm;
          val t1 = rhs_tm thm;
          val thm' = STRONG_FIND_IDEMP t1 (rev (flat_sum t1))
      in
          S_TRANS thm thm'
      end
  else
      failwith "STRONG_SUM_IDEMP_CONV";

(******************************************************************************)
(*                                                                            *)
(*       Conversions for the restriction operator and strong equivalence      *)
(*                                                                            *)
(******************************************************************************)

(* Conversion for the application of the laws for the restriction operator. *)
fun STRONG_RESTR_ELIM_CONV tm =
  if is_restr tm then
      let val (P, L) = args_restr tm
      in
          if (is_nil P) then
              ISPEC L STRONG_RESTR_NIL
          else if (is_sum P) then
              let val (P1, P2) = args_sum P in
                  ISPECL [P1, P2, L] STRONG_RESTR_SUM
              end
          else if (is_prefix P) then
              let val (u, P') = args_prefix P in
                  if (is_tau u) then
                      ISPECL [P', L] STRONG_RESTR_PREFIX_TAU
                  else
                      let val l = arg_action u;
                          val thm = Label_IN_CONV l L
                      in
                          if Teq (rconcl thm) then
                              ISPEC P' (MP (ISPECL [l, L] STRONG_RESTR_PR_LAB_NIL)
                                          (DISJ1 (EQT_ELIM thm) ``COMPL_LAB ^l IN ^L``))
                          else
                              let val thmc = REWRITE_RHS_RULE [COMPL_LAB_def] (REFL ``COMPL_LAB ^l``);
                                  val thm' = Label_IN_CONV (rconcl thmc) L
                              in
                                  if Teq (rconcl thm') then
                                      ISPEC P' (MP (ONCE_REWRITE_RULE [COMPL_LAB_def]
                                                        (ISPECL [l, L] STRONG_RESTR_PR_LAB_NIL))
                                                  (DISJ2 ``^l IN ^L`` (EQT_ELIM thm')))
                                  else
                                      ISPEC P' (MP (ONCE_REWRITE_RULE [COMPL_LAB_def]
                                                        (ISPECL [l, L] STRONG_RESTR_PREFIX_LABEL))
                                                  (CONJ (EQF_ELIM thm) (EQF_ELIM thm')))
                              end
                      end
              end
          else
              failwith "STRONG_RESTR_ELIM_CONV"
      end
  else
      failwith "STRONG_RESTR_ELIM_CONV";

(******************************************************************************)
(*                                                                            *)
(*      Conversions for the relabelling operator and strong equivalence       *)
(*                                                                            *)
(******************************************************************************)

(* Conversion for the application of the laws for the relabelling operator. *)
fun STRONG_RELAB_ELIM_CONV tm =
  if is_relab tm then
      let val (P, rf) = args_relab tm
      in
          if (is_nil P) then
              ISPEC rf STRONG_RELAB_NIL
          else if (is_sum P) then
              let val (P1, P2) = args_sum P in
                  ISPECL [P1, P2, rf] STRONG_RELAB_SUM
              end
          else if (is_prefix P) then
              let val (u, P') = args_prefix P
                  and labl = arg_relabelling rf;
                  val thm_act = REWRITE_RHS_RULE
                                    [relabel_def, Apply_Relab_def,
                                     Label_distinct, Label_distinct', Label_11,
                                     COMPL_LAB_def, COMPL_COMPL_LAB]
                                    (REFL ``relabel (Apply_Relab ^labl) ^u``);
                  val thm_act' = RELAB_EVAL_CONV (rconcl thm_act)
              in
                  ONCE_REWRITE_RULE [TRANS thm_act thm_act']
                                    (ISPECL [u, P', labl] STRONG_RELAB_PREFIX)
              end
          else
              failwith "STRONG_RELAB_ELIM_CONV"
      end
  else
      failwith "STRONG_RELAB_ELIM_CONV";

(******************************************************************************)
(*                                                                            *)
(*       Conversions for the parallel operator and strong equivalence         *)
(*                                                                            *)
(******************************************************************************)

(* Conversion to evaluate conditionals involving numbers. *)
fun COND_EVAL_CONV (c :term) :thm =
  if is_cond c then
      let val (b, l, r) = dest_cond c;
          val thm1 = num_CONV b
          and thm2 = ISPECL [l, r] CCS_COND_CLAUSES
      in
          if Teq (rconcl thm1) then
              SUBS [SYM thm1] (CONJUNCT1 thm2)
          else
              TRANS (SUBS [SYM thm1] (CONJUNCT2 thm2)) (COND_EVAL_CONV r)
      end
  else
      REFL c;

val BETA_COND_CONV = BETA_CONV THENC COND_EVAL_CONV;

(* Conversion that checks that, for all k <= n, the agents given by the
   function f are prefixed agents. *)
fun IS_PREFIX_CHECK k n f = prove (
  ``!^k. ^k <= ^n ==> Is_Prefix (^f ^k)``,
    GEN_TAC
 >> REWRITE_TAC [LESS_OR_EQ, LESS_THM, NOT_LESS_0]
 >> BETA_TAC
 >> STRIP_TAC
 >> ASM_REWRITE_TAC [INV_SUC_EQ, NOT_SUC, SUC_NOT, PREF_IS_PREFIX]);

(* Conversion for deleting nil subterms by means of the identity laws for the
   parallel operator. *)
fun STRONG_PAR_NIL_CONV tm =
  if is_par tm then
      let val (P, Q) = args_par tm
      in
          if is_nil P then ISPEC Q STRONG_PAR_IDENT_L
          else if is_nil Q then ISPEC P STRONG_PAR_IDENT_R
          else
              failwith "STRONG_PAR_NIL_CONV"
      end
  else
      failwith "STRONG_PAR_NIL_CONV";

(* Conversion for deleting nil subterms by means of the identity laws for the
   parallel and summation operators. *)
fun STRONG_NIL_SUM_PAR_CONV tm =
  if is_par tm then
      let val (P, Q) = args_par tm
      in
          if is_nil P then
              ISPEC Q STRONG_PAR_IDENT_L
          else if is_nil Q then
              ISPEC P STRONG_PAR_IDENT_R
          else
              failwith "STRONG_NIL_SUM_PAR_CONV"
      end
  else if is_sum tm then
      let val (P, Q) = args_sum tm
      in
          if is_nil P then
              ISPEC Q STRONG_SUM_IDENT_L
          else if is_nil Q then
              ISPEC P STRONG_SUM_IDENT_R
          else
              failwith "STRONG_NIL_SUM_PAR_CONV"
      end
  else
      failwith "STRONG_NIL_SUM_PAR_CONV";

(* Conversion for extracting the prefixed action and the prefixed process by
   applying PREF_ACT and PREF_PROC, respectively. *)
fun PREFIX_EXTRACT tm = let
    val (opr, opd) = dest_comb tm;
    val (act, proc) = args_prefix opd
in
    if opr ~~ mk_const ("PREF_ACT", type_of opr) then
        ISPECL [act, proc] PREF_ACT_def
    else if opr ~~ mk_const ("PREF_PROC", type_of opr) then
        ISPECL [act, proc] PREF_PROC_def
    else
        failwith "PREFIX_EXTRACT"
end;

(* Conversion for simplifying a summation term. *)
val SIMPLIFY_CONV =
    (DEPTH_CONV BETA_COND_CONV) THENC (DEPTH_CONV PREFIX_EXTRACT);

(* Conversion to compute the synchronizing summands. *)
fun ALL_SYNC_CONV f n1 f' n2 =
  let val c1 = REWRITE_CONV [ALL_SYNC_def] ``ALL_SYNC ^f ^n1 ^f' ^n2``;
      val c2 = TRANS c1 (SIMPLIFY_CONV (rconcl c1));
      val c3 = TRANS c2 (REWRITE_CONV [SYNC_def] (rconcl c2));
      val c4 = TRANS c3 (SIMPLIFY_CONV (rconcl c3));
      val c5 = TRANS c4 (REWRITE_CONV [LABEL_def, COMPL_LAB_def, Action_distinct_label,
                                       Label_distinct, Label_distinct', Label_11]
                                      (rconcl c4))
  in
      TRANS c5 (REWRITE_RHS_RULE [] (DEPTH_CONV string_EQ_CONV (rconcl c5)))
  end;

(* Conversion for the application of the law for the parallel operator in the
   general case of at least one summation agent in parallel. *)
fun STRONG_PAR_SUM_CONV tm = let
    fun comp_fun tm =
      let val thm = REWRITE_RHS_RULE [CCS_SIGMA_def] ((DEPTH_CONV BETA_CONV) tm);
          val thm' = REWRITE_RHS_RULE [INV_SUC_EQ, NOT_SUC, SUC_NOT,
                                       PREF_ACT_def, PREF_PROC_def]
                                      ((DEPTH_CONV BETA_CONV) (rconcl thm))
      in TRANS thm thm' end;
    val (ls1, ls2) = (fn (x, y) => (flat_sum x, flat_sum y)) (args_par tm)
    and (P1, P2) = args_par tm;
    val ARBtm = inst [``:'a`` |-> ``:CCS``] ``ARB: 'a``;
    val f = ``\x: num. ^(sum_to_fun ls1 ARBtm ``0: num``)``
    and f' = ``\x: num. ^(sum_to_fun ls2 ARBtm ``0: num``)``
    and [n1, n2] = map (term_of_int o length) [ls1, ls2];
    val [thm1, thm2] =
        map (fn t => REWRITE_RULE [INV_SUC_EQ, NOT_SUC, SUC_ID]
                                  (BETA_RULE (REWRITE_CONV [CCS_SIGMA_def] t)))
            [``SIGMA ^f ^n1``, ``SIGMA ^f' ^n2``]
    and thmp1 = IS_PREFIX_CHECK ``i: num`` n1 f
    and thmp2 = IS_PREFIX_CHECK ``j: num`` n2 f'
    and [thmc1, thmc2] =
        map comp_fun
            [``SIGMA (\i. prefix (PREF_ACT (^f i))
                                 (par (PREF_PROC (^f i)) (SIGMA ^f' ^n2))) ^n1``,
             ``SIGMA (\j. prefix (PREF_ACT (^f' j))
                                 (par (SIGMA ^f ^n1) (PREF_PROC (^f' j)))) ^n2``]
    and thm_sync = ALL_SYNC_CONV f n1 f' n2;
    val thmt =
        REWRITE_RULE [thmc1, thmc2, thm_sync]
                     (MATCH_MP (ISPECL [f, n1, f', n2] STRONG_EXPANSION_LAW)
                               (CONJ thmp1 thmp2))
in
    if is_prefix P1 then
        let val thma' = S_SUBST (STRONG_SUM_ASSOC_CONV P2) ``par ^P1 ^P2``
        in
            S_TRANS thma' (REWRITE_LHS_RULE [thm1, thm2] thmt)
        end
    else if is_prefix P2 then
        let val thma' = S_SUBST (STRONG_SUM_ASSOC_CONV P1) ``par ^P1 ^P2``
        in
            S_TRANS thma' (REWRITE_LHS_RULE [thm1, thm2] thmt)
        end
    else
        let val thma = S_SUBST (STRONG_SUM_ASSOC_CONV P1) ``par ^P1 ^P2``;
            val thma' = S_TRANS thma
                                (S_SUBST (STRONG_SUM_ASSOC_CONV P2) (rhs_tm thma))
        in
            S_TRANS thma' (REWRITE_LHS_RULE [thm1, thm2] thmt)
        end
end;

(* Conversion for the application of the laws for the parallel operator in the
   particular case of two prefixed agents in parallel. *)
fun STRONG_PAR_PREFIX_CONV (u, P) (v, Q) =
  if is_tau u andalso is_tau v then
      ISPECL [P, Q] STRONG_PAR_TAU_TAU
  else
      if is_tau u then
          ISPECL [P, v, Q] STRONG_PAR_TAU_PREF
      else if is_tau v then
          ISPECL [u, P, Q] STRONG_PAR_PREF_TAU
      else
          let val [l1, l2] = map arg_action [u, v];
              val thmc = REWRITE_RHS_RULE [COMPL_LAB_def] (REFL ``^l1 = COMPL ^l2``)
          in
            if Teq (rconcl thmc) then (* synchronization between l1 and l2 *)
              ISPECL [P, Q] (MP (ISPECL [l1, l2] STRONG_PAR_PREF_SYNCR)
                                (EQT_ELIM thmc))
            else (* no synchronization between l1 and l2 *)
                  let val thm_lab = TRANS thmc (Label_EQ_CONV (rconcl thmc)) in
                      ISPECL [P, Q] (MP (ISPECL [l1, l2] STRONG_PAR_PREF_NO_SYNCR)
                                       (EQF_ELIM thm_lab))
                  end
          end;

(* Conversion for the application of the laws for the parallel operator. *)
fun STRONG_PAR_ELIM_CONV tm =
  if is_par tm then
      let val (P1, P2) = args_par tm
      in
          if (is_prefix P1 andalso is_prefix P2) then
              let val thm = STRONG_PAR_PREFIX_CONV (args_prefix P1) (args_prefix P2) in
                  S_TRANS thm (S_DEPTH_CONV STRONG_NIL_SUM_PAR_CONV (rhs_tm thm))
              end
          else if (is_sum P1 andalso is_prefix P2) orelse
                  (is_prefix P1 andalso is_sum P2) orelse
                  (is_sum P1 andalso is_sum P2) then
              let val thm = STRONG_PAR_SUM_CONV tm in
                  S_TRANS thm (S_DEPTH_CONV STRONG_NIL_SUM_PAR_CONV (rhs_tm thm))
              end
          else
              failwith "STRONG_PAR_ELIM_CONV"
      end
  else
      failwith "STRONG_PAR_ELIM_CONV";

(* Conversion for applying the expansion theorem (parallel and restriction
   operators). *)
val STRONG_EXP_THM_CONV =
    (S_DEPTH_CONV STRONG_PAR_ELIM_CONV) S_THENC
    (S_TOP_DEPTH_CONV STRONG_RESTR_ELIM_CONV) S_THENC
    (S_DEPTH_CONV STRONG_SUM_NIL_CONV);

(******************************************************************************)
(*                                                                            *)
(*       Conversions for the recursion operator and strong equivalence        *)
(*                                                                            *)
(******************************************************************************)

(* Conversion for applying the unfolding law for the recursion operator. *)
fun STRONG_REC_UNF_CONV rtm =
  if is_rec rtm then
      let val (X, E) = args_rec rtm in
          REWRITE_RULE [CCS_Subst_def] (ISPECL [X, E] STRONG_UNFOLDING)
      end
  else
      failwith "STRONG_REC_UNF_CONV: no recursive terms";

(* Conversion for folding a recursive term. *)
fun STRONG_REC_FOLD_CONV rtm =
  if is_rec rtm then
      let val (X, E) = args_rec rtm in
          S_SYM (REWRITE_RULE [CCS_Subst_def] (ISPECL [X, E] STRONG_UNFOLDING))
      end
  else
      failwith "STRONG_REC_FOLD_CONV: no recursive terms";

(******************************************************************************)
(*                                                                            *)
(*           Tactics for applying the laws for strong equivalence             *)
(*                                                                            *)
(******************************************************************************)

(* Tactics for the application of the laws for STRONG_EQUIV on the left-hand
   side of a strong equivalence. *)
val [STRONG_SUM_IDEMP_TAC,
     STRONG_SUM_NIL_TAC,
     STRONG_RELAB_ELIM_TAC,
     STRONG_RESTR_ELIM_TAC,
     STRONG_PAR_ELIM_TAC,
     STRONG_REC_UNF_TAC] = map (S_LHS_CONV_TAC o S_DEPTH_CONV)
                                [STRONG_SUM_IDEMP_CONV,
                                 STRONG_SUM_NIL_CONV,
                                 STRONG_RELAB_ELIM_CONV,
                                 STRONG_RESTR_ELIM_CONV,
                                 STRONG_PAR_ELIM_CONV,
                                 STRONG_REC_UNF_CONV];

(* Tactic for applying the expansion theorem. *)
val STRONG_EXP_THM_TAC = S_LHS_CONV_TAC STRONG_EXP_THM_CONV;

end (* struct *)

(* last updated: Jun 18, 2017 *)
