(* ========================================================================= *)
(* LEAKAGE COMPUTATION CONVERSIONS                                           *)
(* ========================================================================= *)

structure leakageLib :> leakageLib =
struct

open HolKernel Parse boolTheory boolLib bossLib metisLib arithmeticTheory
     pred_setTheory pred_setLib pairTheory extra_pred_setTheory
     listTheory numTheory simpLib extra_listTheory hurdUtils
     stringTheory rich_listTheory stringSimps realTheory realLib
     listSimps extra_stringTheory extra_stringLib leakageTheory;

open real_sigmaTheory;

val safe_set_ss = (simpLib.++ (bool_ss, PRED_SET_ss));

val set_ss = (simpLib.++ (arith_ss, PRED_SET_ss));

val Suff = PARSE_TAC SUFF_TAC;

fun REPEAT_SAFE_EVAL tm =
        let val t = EVAL tm in
        if (snd (dest_thm t)) = (mk_eq (tm,tm)) then
                ALL_CONV tm
        else
                t
        end;


fun FIND_CONV (t:term) (c:term->thm) =
        DEPTH_CONV (test_eq t THENC c);

fun ONCE_FIND_CONV (t:term) (c:term->thm) =
        ONCE_DEPTH_CONV (test_eq t THENC c);

fun UNFOLD_CONV (defs :thm list) (c:term->thm) =
        REPEATC (ONCE_REWRITE_CONV defs
                 THENC c);

fun MAKE_ALL_DISTINCT_CONV (c:term->thm) =
        UNFOLD_CONV [MAKE_ALL_DISTINCT_def] c;

fun MEM_CONV (c:term->thm) =
        UNFOLD_CONV [MEM] c;

fun F_UNCHANGED_CONV (conv:term->thm) tm =
        if tm = ``F`` then ALL_CONV tm else conv tm;

fun T_UNCHANGED_CONV (conv:term->thm) tm =
        if tm = ``T`` then ALL_CONV tm else conv tm;

fun T_F_UNCHANGED_CONV (conv:term->thm) tm =
        T_UNCHANGED_CONV (F_UNCHANGED_CONV conv) tm;


val CROSS_NON_EMPTY_IMP = prove
   (``!P Q. FINITE P /\ FINITE Q /\ ~(P={}) /\ ~(Q={}) ==> ~(P CROSS Q = {})``,
    REPEAT STRIP_TAC
    THEN (MP_TAC o Q.SPEC `P`) SET_CASES
    THEN RW_TAC std_ss []
    THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
    THEN (MP_TAC o Q.ISPEC `Q:'b->bool`) SET_CASES
    THEN RW_TAC std_ss []
    THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
    THEN FULL_SIMP_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_INSERT, IN_CROSS]
    THEN METIS_TAC [PAIR, FST, SND, PAIR_EQ]);

val CROSS_HLR_NON_EMPTY_IMP = prove
   (``!h l r. FINITE h /\ FINITE l /\ FINITE r /\ ~(h={}) /\ ~(l={}) /\ ~(r={}) ==> ~((h CROSS l) CROSS r = {})``,
    METIS_TAC [CROSS_NON_EMPTY_IMP, FINITE_CROSS]);

val unif_prog_space_leakage_computation_reduce_COMPUTE = prove  (``!high low random f. FINITE high /\ FINITE low /\ FINITE random /\       ~((high CROSS low) CROSS random={}) ==>         (leakage (unif_prog_space high low random) f =           (1/(&(CARD high * CARD low * CARD random)))*            (SIGMA (\(out,h,l). (\x. x * lg (((1/(&(CARD random)))* x))) (SIGMA (\r. if (f((h,l),r)=out) then 1 else 0) random))
                  (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)) -
             SIGMA (\(out,l). (\x. x * lg (((1/(&(CARD high * CARD random)))* x)))
                        (SIGMA (\(h,r). if (f((h,l),r)=out) then 1 else 0) (high CROSS random)))
                  (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random))))``,   METIS_TAC [unif_prog_space_leakage_computation_reduce]);

fun LEAKAGE_COMPUTE_PROVE_FINITE (t:term) (tl:Abbrev.thm list) =
        (prove ((mk_comb ((inst [alpha |-> fst(dom_rng(type_of t))]``FINITE``),t)),
                CONV_TAC (SIMP_CONV set_ss tl)));

fun LEAKAGE_COMPUTE_FINITE_HLR ((h:term),(l:term),(r:term)) (tl:Abbrev.thm list) =
   [LEAKAGE_COMPUTE_PROVE_FINITE h tl, LEAKAGE_COMPUTE_PROVE_FINITE l tl, LEAKAGE_COMPUTE_PROVE_FINITE r tl];

fun LEAKAGE_COMPUTE_CROSS_NOT_EMPTY ((h:term),(l:term),(r:term)) (tl:Abbrev.thm list) =
        (prove (mk_comb (``$~:bool->bool``,
mk_comb ((mk_comb ((inst [alpha |-> ((pairSyntax.mk_prod((pairSyntax.mk_prod((fst(dom_rng(type_of h))),(fst(dom_rng(type_of l))))),(fst(dom_rng(type_of r)))))-->bool)] ``$=``),
         (mk_comb (mk_comb ((inst [alpha |-> (pairSyntax.mk_prod((fst(dom_rng(type_of h))),(fst(dom_rng(type_of l))))),beta |-> fst(dom_rng(type_of r))]``$CROSS``),(mk_comb (mk_comb ((inst [alpha |-> fst(dom_rng(type_of h)),beta |-> fst(dom_rng(type_of l))]``$CROSS``), h),l))),r)))),
(inst [alpha |-> (pairSyntax.mk_prod((pairSyntax.mk_prod((fst(dom_rng(type_of h))),(fst(dom_rng(type_of l))))),(fst(dom_rng(type_of r)))))] ``{}``))),
        MATCH_MP_TAC CROSS_HLR_NON_EMPTY_IMP
        THEN ONCE_REWRITE_TAC [EXTENSION]
        THEN RW_TAC set_ss (append [NOT_IN_EMPTY, EXISTS_OR_THM] tl)));

fun LEAKAGE_COMPUTE_INITIAL_REDUCE ((h:term),(l:term),(r:term)) (tl:Abbrev.thm list) =
        let val finite = LEAKAGE_COMPUTE_FINITE_HLR (h,l,r) tl in
        let val cross = LEAKAGE_COMPUTE_CROSS_NOT_EMPTY (h,l,r) (append finite tl) in
                SIMP_CONV bool_ss (unif_prog_space_leakage_computation_reduce_COMPUTE::cross::finite)
        end end;

fun COMPUTE_CARD (tm:term) (expand_conv:Abbrev.term->Abbrev.thm) (remove_dups_conv:Abbrev.term->Abbrev.thm) =
        (((RAND_CONV expand_conv) THENC
         REPEATC (SIMP_CONV bool_ss [Once CARD_DEF, FINITE_INSERT, FINITE_EMPTY, FINITE_SING]
                  THENC (FIND_CONV ``x IN y`` (IN_CONV remove_dups_conv)
                         THENC SIMP_CONV bool_ss [])))
        THENC SIMP_CONV arith_ss [])
        (mk_comb (inst [alpha |-> (fst(dom_rng(type_of tm)))] ``CARD``, tm));

fun COMPUTE_HLR_CARDS ((h:term),(l:term),(r:term))
        (h_expand_conv:Abbrev.term->Abbrev.thm)
        (l_expand_conv:Abbrev.term->Abbrev.thm)
        (r_expand_conv:Abbrev.term->Abbrev.thm)
        (h_dups_conv:Abbrev.term->Abbrev.thm)
        (l_dups_conv:Abbrev.term->Abbrev.thm)
        (r_dups_conv:Abbrev.term->Abbrev.thm) =
   [COMPUTE_CARD h h_expand_conv h_dups_conv, COMPUTE_CARD l l_expand_conv l_dups_conv, COMPUTE_CARD r r_expand_conv r_dups_conv];

fun LEAKAGE_COMPUTE_REDUCE_CARDS ((h:term),(l:term),(r:term)) (tl:Abbrev.thm list)
        (h_expand_conv:Abbrev.term->Abbrev.thm)
        (l_expand_conv:Abbrev.term->Abbrev.thm)
        (r_expand_conv:Abbrev.term->Abbrev.thm)
        (h_dups_conv:Abbrev.term->Abbrev.thm)
        (l_dups_conv:Abbrev.term->Abbrev.thm)
        (r_dups_conv:Abbrev.term->Abbrev.thm) =
                LEAKAGE_COMPUTE_INITIAL_REDUCE (h,l,r) tl
                THENC SIMP_CONV bool_ss (COMPUTE_HLR_CARDS (h,l,r) h_expand_conv l_expand_conv r_expand_conv h_dups_conv l_dups_conv r_dups_conv);

fun LEAKAGE_COMPUTE_HLR_CROSS ((h:term),(l:term),(r:term)) (tl:Abbrev.thm list)
        (h_expand_conv:Abbrev.term->Abbrev.thm)
        (l_expand_conv:Abbrev.term->Abbrev.thm)
        (r_expand_conv:Abbrev.term->Abbrev.thm)
        (h_dups_conv:Abbrev.term->Abbrev.thm)
        (l_dups_conv:Abbrev.term->Abbrev.thm)
        (r_dups_conv:Abbrev.term->Abbrev.thm) =
        FIND_CONV
        (mk_comb((mk_comb((inst [alpha |-> (pairSyntax.mk_prod((fst(dom_rng(type_of h))),
                                                              (fst(dom_rng(type_of l))))), beta |-> (fst(dom_rng(type_of r)))] ``$CROSS``),
         mk_comb(mk_comb((inst [alpha |-> (fst(dom_rng(type_of h))), beta |-> (fst(dom_rng(type_of l)))] ``$CROSS``),h),l))), r))
        (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV h_expand_conv)
                                THENC RAND_CONV l_expand_conv
                                THENC SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV h_dups_conv)
                                                     THENC (TRY_CONV l_dups_conv))))))
         THENC (RAND_CONV r_expand_conv)
         THENC SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
         THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV h_dups_conv)
                                                     THENC (TRY_CONV l_dups_conv)
                                                     THENC (TRY_CONV r_dups_conv)))));

val lg_times_compute_simp_lem = prove
   (``!x y. x * lg (y * x) = (\x. x * lg (y * x)) x``,
    RW_TAC std_ss []);

fun LEAKAGE_COMPUTE_IMAGE_HLR_CROSS ((h:term),(l:term),(r:term)) (tl:Abbrev.thm list) (prog_tl:Abbrev.thm list)
        (h_expand_conv:Abbrev.term->Abbrev.thm)
        (l_expand_conv:Abbrev.term->Abbrev.thm)
        (r_expand_conv:Abbrev.term->Abbrev.thm)
        (h_dups_conv:Abbrev.term->Abbrev.thm)
        (l_dups_conv:Abbrev.term->Abbrev.thm)
        (r_dups_conv:Abbrev.term->Abbrev.thm) =
        LEAKAGE_COMPUTE_HLR_CROSS (h,l,r) tl h_expand_conv l_expand_conv r_expand_conv h_dups_conv l_dups_conv r_dups_conv
        THENC (RAND_CONV (RAND_CONV (RAND_CONV (
                IMAGE_CONV (SIMP_CONV bool_ss prog_tl THENC EVAL) NO_CONV))))
        THENC (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV (
                IMAGE_CONV (SIMP_CONV bool_ss prog_tl THENC EVAL) NO_CONV)))))
        THENC (RAND_CONV (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (
                ONCE_REWRITE_CONV [lg_times_compute_simp_lem]
                THENC (FIND_CONV r (r_expand_conv THENC
                        SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                                    THENC (FIND_CONV ``x UNION y``
                                                (UNION_CONV (SIMP_CONV bool_ss [] THENC r_dups_conv)))))))))));

fun RECURSIVE_UNWIND_SUM (dups_conv:Abbrev.term->Abbrev.thm) (item_conv:Abbrev.term->Abbrev.thm) (tm:term) =
        if (rand tm) = (inst [alpha |-> fst(dom_rng(type_of (rand tm)))] ``{}``) then REWRITE_CONV [REAL_SUM_IMAGE_THM] tm else
        ((fn (tm:term) => (let val s = snd(dest_comb(snd (dest_comb tm))) in
                                          let val f = snd(dest_comb (fst(dest_comb tm))) in
                                          let val fin_thm = prove (mk_comb((inst [alpha |-> fst(dom_rng(type_of s))] ``FINITE``),s),
                                                                   CONV_TAC (SIMP_CONV set_ss [])) in
                                                REWRITE_CONV [REWRITE_RULE [fin_thm]
                                                (ISPEC s ((CONV_RULE SWAP_VARS_CONV) (CONJUNCT2 (ISPEC f REAL_SUM_IMAGE_THM))))] tm
                                          end
                                          end
                                          end))
        THENC (TRY_CONV (RATOR_CONV (RAND_CONV item_conv)))
        THENC (RAND_CONV (RAND_CONV (DELETE_CONV dups_conv)))
        THENC (RAND_CONV (RECURSIVE_UNWIND_SUM dups_conv item_conv))) tm;

fun LEAKAGE_COMPUTE_UNWIND_OUTER_SUM
        (h_dups_conv:Abbrev.term->Abbrev.thm)
        (l_dups_conv:Abbrev.term->Abbrev.thm)
        (o_dups_conv:Abbrev.term->Abbrev.thm) =
        RAND_CONV (RATOR_CONV (RAND_CONV (
                ONCE_REWRITE_CONV [lg_times_compute_simp_lem] THENC
                RECURSIVE_UNWIND_SUM (SIMP_CONV bool_ss [PAIR_EQ]
                                      THENC (TRY_CONV o_dups_conv)
                                      THENC (TRY_CONV h_dups_conv)
                                      THENC (TRY_CONV l_dups_conv))
                                PairRules.PBETA_CONV))
                   THENC (RAND_CONV (ONCE_REWRITE_CONV [lg_times_compute_simp_lem] THENC
                                     RECURSIVE_UNWIND_SUM (SIMP_CONV bool_ss [PAIR_EQ]
                                                           THENC (TRY_CONV o_dups_conv)
                                                           THENC (TRY_CONV l_dups_conv))
                                                          PairRules.PBETA_CONV)))
        THENC REWRITE_CONV [REAL_ADD_RID];

fun LEAKAGE_COMPUTE_UNWIND_INNER_SUM ((h:term),(r:term)) (tl:Abbrev.thm list) (prog_tl:Abbrev.thm list)
        (h_expand_conv:Abbrev.term->Abbrev.thm)
        (r_expand_conv:Abbrev.term->Abbrev.thm)
        (h_dups_conv:Abbrev.term->Abbrev.thm)
        (r_dups_conv:Abbrev.term->Abbrev.thm)
        (o_dups_conv:Abbrev.term->Abbrev.thm) =
        let val h_cross_r =  (RATOR_CONV(RAND_CONV (h_expand_conv)) THENC (RAND_CONV r_expand_conv)
                              THENC SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                              THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                                          THENC (TRY_CONV h_dups_conv)
                                                                          THENC (TRY_CONV r_dups_conv)))))
                             (mk_comb(mk_comb((inst [alpha |-> (fst(dom_rng(type_of h))),
                                                beta |-> (fst(dom_rng(type_of r)))] ``$CROSS``),h),r))
        in
                RAND_CONV (RATOR_CONV(RAND_CONV (FIND_CONV ``REAL_SUM_IMAGE f s`` (
                                RECURSIVE_UNWIND_SUM r_dups_conv
                                                     ((TRY_CONV BETA_CONV) THENC
        RATOR_CONV (RATOR_CONV (RAND_CONV (LHS_CONV (SIMP_CONV bool_ss prog_tl THENC (TRY_CONV PairRules.PBETA_CONV)) THENC o_dups_conv)))
           THENC SIMP_CONV bool_ss []))))
                           THENC (RAND_CONV (REWRITE_CONV [h_cross_r] THENC
                                             FIND_CONV ``REAL_SUM_IMAGE f s`` (
                                RECURSIVE_UNWIND_SUM (SIMP_CONV bool_ss [PAIR_EQ] THENC
                                                      (TRY_CONV h_dups_conv) THENC
                                                      (TRY_CONV r_dups_conv))
                                                     ((TRY_CONV PairRules.PBETA_CONV) THENC
        RATOR_CONV (RATOR_CONV (RAND_CONV (LHS_CONV (SIMP_CONV bool_ss prog_tl THENC (TRY_CONV PairRules.PBETA_CONV)) THENC o_dups_conv)))
           THENC SIMP_CONV bool_ss []))))) THENC REWRITE_CONV [REAL_ADD_RID]
        end;

fun LEAKAGE_COMPUTE_CONV ((h:term),(l:term),(r:term)) (tl:Abbrev.thm list) (prog_tl:Abbrev.thm list)
        (h_expand_conv:Abbrev.term->Abbrev.thm)
        (l_expand_conv:Abbrev.term->Abbrev.thm)
        (r_expand_conv:Abbrev.term->Abbrev.thm)
        (h_dups_conv:Abbrev.term->Abbrev.thm)
        (l_dups_conv:Abbrev.term->Abbrev.thm)
        (r_dups_conv:Abbrev.term->Abbrev.thm)
        (o_dups_conv:Abbrev.term->Abbrev.thm) =
        LEAKAGE_COMPUTE_REDUCE_CARDS (h,l,r) tl h_expand_conv l_expand_conv r_expand_conv h_dups_conv l_dups_conv r_dups_conv
        THENC LEAKAGE_COMPUTE_IMAGE_HLR_CROSS (h,l,r) tl prog_tl h_expand_conv l_expand_conv r_expand_conv h_dups_conv l_dups_conv r_dups_conv
        THENC LEAKAGE_COMPUTE_UNWIND_OUTER_SUM h_dups_conv l_dups_conv o_dups_conv
        THENC LEAKAGE_COMPUTE_UNWIND_INNER_SUM (h,r) tl prog_tl h_expand_conv r_expand_conv h_dups_conv r_dups_conv o_dups_conv
        THENC (SIMP_CONV real_ss []);


end
