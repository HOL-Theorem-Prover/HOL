(* ========================================================================= *)
(* Create "leakageTheory" setting up the theory of information leakage       *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open metisLib arithmeticTheory pred_setTheory listTheory state_transformerTheory
     combinTheory pairTheory jrhUtils numTheory simpLib subtypeTheory
     stringTheory rich_listTheory stringSimps listSimps hurdUtils;

open realTheory realLib realSimps transcTheory limTheory seqTheory real_sigmaTheory;

open extra_boolTheory extra_numTheory extra_pred_setTheory extra_realTheory
     extra_listTheory extra_stringTheory extra_stringLib;

open util_probTheory sigma_algebraTheory real_measureTheory real_lebesgueTheory
     real_probabilityTheory;

open informationTheory;

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "information"                                   *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "leakage";
val _ = temp_set_fixity "CROSS" (Infixl 600)
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"];
val real_ss = real_ss -* ["lift_disj_eq", "lift_imp_disj"];
val list_ss = list_ss -* ["lift_disj_eq", "lift_imp_disj"];

val _ = intLib.deprecate_int();
val _ = ratLib.deprecate_rat();

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

val () = type_abbrev ("state", Type `:string -> 'a`);

val () = type_abbrev ("prog_state", Type `:(('a state # 'b state) # 'c state)`);

val () = type_abbrev ("prog", Type `:(('a,'b,'c) prog_state) -> 'd state`);

val high_state_def = Define `H (s:(('a,'b,'c) prog_state)) = FST (FST s)`;

val low_state_def = Define `L (s:(('a,'b,'c) prog_state)) = SND (FST s)`;

val random_state_def = Define `R (s:(('a,'b,'c) prog_state)) = SND s`;

(* ------------------------------------------------------------------------- *)
(* --------  Interference of a program defined w/ prob_space p ------------- *)
(* ------------------------------------------------------------------------- *)


val leakage_def = Define
   `leakage p (f:('a,'b,'c,'d) prog) =
        conditional_mutual_information 2 p
                ((IMAGE f (p_space p)), POW (IMAGE f (p_space p)))
                ((IMAGE H (p_space p)), POW (IMAGE H (p_space p)))
                ((IMAGE L (p_space p)), POW (IMAGE L (p_space p)))
                f H L`;

val visible_leakage_def = Define
   `visible_leakage p (f:('a,'b,'c,'d) prog) =
        conditional_mutual_information 2 p
                ((IMAGE f (p_space p)), POW (IMAGE f (p_space p)))
                ((IMAGE H (p_space p)), POW (IMAGE H (p_space p)))
                ((IMAGE (\s:('a,'b,'c) prog_state. (L s, R s)) (p_space p)),
                 POW (IMAGE (\s:('a,'b,'c) prog_state. (L s, R s)) (p_space p)))
                 f H (\s:('a,'b,'c) prog_state. (L s, R s))`;


(* ************************************************************************* *)
(* Simplification of computation for Interference analysis:                  *)
(*      program space for uniform distribution for program M w/ finite       *)
(*      sets of possible initial input states                                *)
(* ************************************************************************* *)

val unif_prog_dist_def = Define
   `unif_prog_dist high low random =
        (\s. if s IN (high CROSS low) CROSS random then
             1/(&(CARD ((high CROSS low) CROSS random))) else 0)`;


val unif_prog_space_def = Define
   `unif_prog_space high low random =
        ((high CROSS low) CROSS random,
         POW ((high CROSS low) CROSS random),
         (\s. SIGMA (unif_prog_dist high low random) s))`;

(* ************************************************************************* *)
(* Proofs                                                                    *)
(* ************************************************************************* *)

val prob_space_unif_prog_space = store_thm
  ("prob_space_unif_prog_space",
   ``!high low random. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           prob_space (unif_prog_space high low random)``,
   RW_TAC std_ss [prob_space_def, unif_prog_space_def, unif_prog_dist_def,
                  measure_def, PSPACE]
   >- (MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces2
       >> RW_TAC std_ss [m_space_def, measurable_sets_def, measure_def, POW_SIGMA_ALGEBRA,
                         FINITE_CROSS, positive_def, REAL_SUM_IMAGE_THM]
       >- (MATCH_MP_TAC REAL_SUM_IMAGE_POS
           >> STRONG_CONJ_TAC >- METIS_TAC [IN_POW, FINITE_CROSS, SUBSET_FINITE]
           >> RW_TAC real_ss []
           >> RW_TAC real_ss []
           >> MATCH_MP_TAC REAL_LE_DIV
           >> RW_TAC real_ss [REAL_POS])
       >> RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
       >> `FINITE s /\ FINITE t` by METIS_TAC [IN_POW, FINITE_CROSS, SUBSET_FINITE]
       >> RW_TAC std_ss [(UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
           Q.ISPECL [`(s :('a # 'b) # 'c -> bool)`,`(t :('a # 'b) # 'c -> bool)`])
          REAL_SUM_IMAGE_DISJOINT_UNION])
   >> `(\s. (if s IN high CROSS low CROSS random then
                1 / & (CARD (high CROSS low CROSS random)) else 0)) =
           (\s. inv (& (CARD (high CROSS low CROSS random))) *
                (\s. if s IN high CROSS low CROSS random then 1 else 0) s)`
                by (RW_TAC std_ss [FUN_EQ_THM, real_div] >> RW_TAC real_ss [])
   >> POP_ORW >> RW_TAC std_ss [REAL_SUM_IMAGE_CMUL, FINITE_CROSS, REAL_SUM_IMAGE_EQ_CARD]
   >> MATCH_MP_TAC REAL_MUL_LINV >> RW_TAC std_ss [REAL_OF_NUM_EQ, REAL_0]
   >> METIS_TAC [CARD_EQ_0, FINITE_CROSS]);


val prob_unif_prog_space = store_thm
  ("prob_unif_prog_space",
   ``!high low random P. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) /\
           P SUBSET ((high CROSS low) CROSS random) ==>
           (prob (unif_prog_space high low random) P =
            (&(CARD P))/(&((CARD high)*(CARD low)*(CARD random))))``,
   RW_TAC std_ss [unif_prog_space_def, unif_prog_dist_def, PROB]
   >> `(\s. (if s IN high CROSS low CROSS random then
                1 / & (CARD (high CROSS low CROSS random)) else 0)) =
           (\s. inv (& (CARD (high CROSS low CROSS random))) *
                (\s. if s IN high CROSS low CROSS random then 1 else 0) s)`
                by (RW_TAC std_ss [FUN_EQ_THM, real_div] >> RW_TAC real_ss [])
   >> POP_ORW >> `FINITE P` by METIS_TAC [FINITE_CROSS, SUBSET_FINITE]
   >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_CMUL]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(P :('a # 'b) # 'c -> bool)`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN P then
            (\s. (if s IN high CROSS low CROSS random then 1 else 0)) x else 0)) =
       (\x. if x IN P then 1 else 0)` by METIS_TAC [SUBSET_DEF]
   >> POP_ORW
   >> RW_TAC std_ss [real_div, REAL_SUM_IMAGE_EQ_CARD, REAL_MUL_COMM,
                     FINITE_CROSS, CARD_CROSS, REAL_MUL_ASSOC]);


val unif_prog_space_low_distribution = store_thm
  ("unif_prog_space_low_distribution",
   ``!high low random f. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (!l. l IN low ==> (distribution(unif_prog_space high low random) L {l} =
                              ((1:real)/(&(CARD low)))))``,
   RW_TAC std_ss [distribution_def]
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> RW_TAC std_ss []
   >> `(PREIMAGE L {l} INTER (high CROSS low CROSS random)) SUBSET
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [SUBSET_DEF, IN_INTER]
   >> RW_TAC std_ss [prob_unif_prog_space]
   >> `(PREIMAGE L {l} INTER (high CROSS low CROSS random)) =
       (IMAGE (\x. ((FST x, l),SND x)) (high CROSS random))`
       by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING,
                          low_state_def, IN_CROSS, IN_IMAGE]
           >> EQ_TAC >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(FST(FST x),SND x)`
                         >> RW_TAC std_ss [FST, SND, PAIR])
           >> RW_TAC std_ss [] >> RW_TAC std_ss [FST, SND])
   >> POP_ORW
   >> `INJ (\x. ((FST x,l),SND x)) (high CROSS random)
           (IMAGE (\x. ((FST x,l),SND x)) (high CROSS random))`
           by (RW_TAC std_ss [INJ_DEF, IN_IMAGE]
               >> METIS_TAC [PAIR, PAIR_EQ])
   >> RW_TAC std_ss [(Q.SPECL [`(\(x :'a state # 'c state). ((FST x,(l :'b state)),SND x))`,
                                `((high :'a state -> bool) CROSS (random :'c state -> bool))`,
                                `(IMAGE (\(x :'a state # 'c state). ((FST x,l),SND x))
                                 (high CROSS random))`] o
                        INST_TYPE [``:'b`` |-> ``:('a state # 'b state) # 'c state``,
                                   ``:'a`` |-> ``:'a state # 'c state``]) CARD_IMAGE, FINITE_CROSS]
   >> RW_TAC std_ss [CARD_CROSS, GSYM REAL_MUL]
   >> Suff `((& (CARD high) * & (CARD random)) * 1) / ((& (CARD high) * & (CARD random)) * & (CARD low)) =
            1 / & (CARD low)`
   >- RW_TAC real_ss [REAL_MUL_COMM]
   >> MATCH_MP_TAC REAL_DIV_LMUL_CANCEL
   >> RW_TAC real_ss [REAL_ENTIRE, REAL_0, REAL_INJ, CARD_EQ_0]
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> FULL_SIMP_TAC std_ss [CROSS_EMPTY]);


val unif_prog_space_highlow_distribution = store_thm
  ("unif_prog_space_highlow_distribution",
   ``!high low random f. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (!h l. h IN high /\ l IN low ==>
               (distribution (unif_prog_space high low random) (\x. (H x,L x)) {(h,l)} =
                ((1:real)/(&((CARD high)*(CARD low))))))``,
   RW_TAC std_ss [distribution_def]
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> RW_TAC std_ss []
   >> `(PREIMAGE (\x. (H x,L x)) {(h,l)} INTER (high CROSS low CROSS random)) SUBSET
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [SUBSET_DEF, IN_INTER]
   >> RW_TAC std_ss [prob_unif_prog_space]
   >> `(PREIMAGE (\x. (H x,L x)) {(h,l)} INTER (high CROSS low CROSS random)) =
       (IMAGE (\x. ((h, l), x)) random)`
       by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING,
                          low_state_def, IN_CROSS, IN_IMAGE, high_state_def]
           >> EQ_TAC >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `SND x`
                         >> RW_TAC std_ss [FST, SND, PAIR])
           >> RW_TAC std_ss [] >> RW_TAC std_ss [FST, SND])
   >> POP_ORW
   >> `INJ (\x. ((h,l),x)) random
           (IMAGE (\x. ((h,l),x)) random)`
           by (RW_TAC std_ss [INJ_DEF, IN_IMAGE]
               >> METIS_TAC [PAIR, PAIR_EQ])
   >> RW_TAC std_ss [(Q.SPECL [`(\(x :'c state). (((h:'a state),(l :'b state)),x))`,
                                `(random :'c state -> bool)`,
                                `(IMAGE (\(x :'c state). (((h:'a state),(l :'b state)),x))
                                 random)`] o
                        INST_TYPE [``:'b`` |-> ``:('a state # 'b state) # 'c state``,
                                   ``:'a`` |-> ``:'c state``]) CARD_IMAGE]
   >> RW_TAC std_ss [CARD_CROSS, GSYM REAL_MUL]
   >> Suff `((& (CARD random)) * 1) / ((& (CARD random)) * (& (CARD high) * & (CARD low))) =
            1 / (& (CARD high) * & (CARD low))`
   >- RW_TAC real_ss [REAL_MUL_COMM]
   >> MATCH_MP_TAC REAL_DIV_LMUL_CANCEL
   >> RW_TAC real_ss [REAL_ENTIRE, REAL_0, REAL_INJ, CARD_EQ_0]
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> FULL_SIMP_TAC std_ss [CROSS_EMPTY]);


val unif_prog_space_lowrandom_distribution = store_thm
  ("unif_prog_space_lowrandom_distribution",
   ``!high low random f. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (!l r. l IN low /\ r IN random ==>
               (distribution (unif_prog_space high low random) (\x. (L x,R x)) {(l,r)} =
                ((1:real)/(&((CARD low)*(CARD random))))))``,
   RW_TAC std_ss [distribution_def]
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> RW_TAC std_ss []
   >> `(PREIMAGE (\x. (L x,R x)) {(l,r)} INTER (high CROSS low CROSS random)) SUBSET
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [SUBSET_DEF, IN_INTER]
   >> RW_TAC std_ss [prob_unif_prog_space]
   >> `(PREIMAGE (\x. (L x,R x)) {(l,r)} INTER (high CROSS low CROSS random)) =
       (IMAGE (\x. ((x, l), r)) high)`
       by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING,
                          low_state_def, IN_CROSS, IN_IMAGE, random_state_def]
           >> EQ_TAC >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `FST(FST x)`
                         >> RW_TAC std_ss [FST, SND, PAIR])
           >> RW_TAC std_ss [] >> RW_TAC std_ss [FST, SND])
   >> POP_ORW
   >> `INJ (\x. ((x,l),r)) high
           (IMAGE (\x. ((x,l),r)) high)`
           by (RW_TAC std_ss [INJ_DEF, IN_IMAGE]
               >> METIS_TAC [PAIR, PAIR_EQ])
   >> RW_TAC std_ss [(Q.SPECL [`(\(x :'a state). (((x:'a state),(l :'b state)),(r:'c state)))`,
                                `(high :'a state -> bool)`,
                                `(IMAGE (\(x :'a state). (((x:'a state),(l :'b state)),(r:'c state)))
                                 high)`] o
                        INST_TYPE [``:'b`` |-> ``:('a state # 'b state) # 'c state``,
                                   ``:'a`` |-> ``:'a state``]) CARD_IMAGE]
   >> RW_TAC std_ss [CARD_CROSS, GSYM REAL_MUL]
   >> Suff `((& (CARD high)) * 1) / ((& (CARD high)) * (& (CARD low) * & (CARD random))) =
            1 / (& (CARD low) * & (CARD random))`
   >- RW_TAC real_ss [REAL_MUL_COMM]
   >> MATCH_MP_TAC REAL_DIV_LMUL_CANCEL
   >> RW_TAC real_ss [REAL_ENTIRE, REAL_0, REAL_INJ, CARD_EQ_0]
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> FULL_SIMP_TAC std_ss [CROSS_EMPTY]);


val unif_prog_space_highlowrandom_distribution = store_thm
  ("unif_prog_space_highlowrandom_distribution",
   ``!high low random f. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (!h l r. h IN high /\ l IN low /\ r IN random ==>
               (distribution (unif_prog_space high low random) (\x. (H x, L x,R x)) {(h,l,r)} =
                ((1:real)/(&((CARD high)*(CARD low)*(CARD random))))))``,
   RW_TAC std_ss [distribution_def]
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> RW_TAC std_ss []
   >> `(PREIMAGE (\x. (H x,L x,R x)) {(h,l,r)} INTER (high CROSS low CROSS random)) SUBSET
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [SUBSET_DEF, IN_INTER]
   >> RW_TAC std_ss [prob_unif_prog_space]
   >> `(PREIMAGE (\x. (H x,L x,R x)) {(h,l,r)} INTER (high CROSS low CROSS random)) =
       {((h,l),r)}`
       by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING,
                          low_state_def, IN_CROSS, IN_IMAGE, random_state_def, high_state_def]
           >> METIS_TAC [FST, SND, PAIR])
   >> POP_ORW
   >> RW_TAC std_ss [CARD_CROSS, CARD_SING]);

Theorem unif_prog_space_leakage_reduce :
    !high low random f. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (leakage (unif_prog_space high low random) f =
            SIGMA (\x. (\(x,y,z).
                  joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
                      & (CARD high * CARD low))) x)
                  (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)) -
            SIGMA (\x. (\(x,z).
                  joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                      & (CARD low))) x)
                  (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)))
Proof
   RW_TAC std_ss [leakage_def]
   >> Q.ABBREV_TAC `foo =
                  SIGMA (\x. (\(x,y,z).
                  joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
                      & (CARD high * CARD low))) x)
                  (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)) -
                  SIGMA (\x. (\(x,z).
                  joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                      & (CARD low))) x)
                  (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random))`
   >> `random_variable (f :('a, 'b, 'c, 'd) prog) (unif_prog_space high low random)
                         (IMAGE (f :('a, 'b, 'c, 'd) prog) (p_space (unif_prog_space high low random)),
                          POW (IMAGE (f :('a, 'b, 'c, 'd) prog) (p_space (unif_prog_space high low random))))`
      by (RW_TAC std_ss [random_variable_def, prob_space_unif_prog_space]
          >> RW_TAC std_ss [p_space_def, events_def]
          >> MATCH_MP_TAC MEASURABLE_POW_TO_POW_IMAGE
          >> CONJ_TAC >- METIS_TAC [prob_space_unif_prog_space, prob_space_def]
          >> RW_TAC std_ss [unif_prog_space_def, measurable_sets_def, m_space_def])
   >> `random_variable (H :('a, 'b, 'c, 'a) prog) (unif_prog_space high low random)
                         (IMAGE (H :('a, 'b, 'c, 'a) prog) (p_space (unif_prog_space high low random)),
                          POW (IMAGE (H :('a, 'b, 'c, 'a) prog) (p_space (unif_prog_space high low random))))`
      by (RW_TAC std_ss [random_variable_def, prob_space_unif_prog_space]
          >> RW_TAC std_ss [p_space_def, events_def]
          >> MATCH_MP_TAC MEASURABLE_POW_TO_POW_IMAGE
          >> CONJ_TAC >- METIS_TAC [prob_space_unif_prog_space, prob_space_def]
          >> RW_TAC std_ss [unif_prog_space_def, measurable_sets_def, m_space_def])
   >> `random_variable (L :('a, 'b, 'c, 'b) prog) (unif_prog_space high low random)
                         (IMAGE (L :('a, 'b, 'c, 'b) prog) (p_space (unif_prog_space high low random)),
                          POW (IMAGE (L :('a, 'b, 'c, 'b) prog) (p_space (unif_prog_space high low random))))`
      by (RW_TAC std_ss [random_variable_def, prob_space_unif_prog_space]
          >> RW_TAC std_ss [p_space_def, events_def]
          >> MATCH_MP_TAC MEASURABLE_POW_TO_POW_IMAGE
          >> CONJ_TAC >- METIS_TAC [prob_space_unif_prog_space, prob_space_def]
          >> RW_TAC std_ss [unif_prog_space_def, measurable_sets_def, m_space_def])
   >> `FINITE (p_space (unif_prog_space high low random))`
      by RW_TAC std_ss [unif_prog_space_def, FINITE_CROSS, PSPACE]
   >> `POW (p_space (unif_prog_space high low random)) = events (unif_prog_space high low random)`
      by RW_TAC std_ss [unif_prog_space_def, PSPACE, EVENTS]
 (* stage work *)
   >> ‘prob_space (unif_prog_space high low random)’ by PROVE_TAC [prob_space_unif_prog_space]
   >> RW_TAC std_ss [finite_conditional_mutual_information_reduce]
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> RW_TAC std_ss []
   >> `IMAGE L (high CROSS low CROSS random) = low`
      by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE, low_state_def, IN_CROSS]
          >> EQ_TAC
          >- (RW_TAC std_ss [] >> RW_TAC std_ss [])
          >> `?x t. (high CROSS low CROSS random = x INSERT t) /\
                    ~(x IN t)` by METIS_TAC [SET_CASES]
          >> Know `x' IN (high CROSS low CROSS random)` >- METIS_TAC [EXTENSION, IN_INSERT]
          >> RW_TAC std_ss [IN_CROSS]
          >> Q.EXISTS_TAC `((FST (FST x'), x), SND x')`
          >> RW_TAC std_ss [])
   >> POP_ORW
   >> `IMAGE (\x. (H x,L x)) (high CROSS low CROSS random) = high CROSS low`
      by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE, low_state_def, high_state_def, IN_CROSS]
          >> EQ_TAC
          >- (RW_TAC std_ss [] >> RW_TAC std_ss [])
          >> `?x t. (high CROSS low CROSS random = x INSERT t) /\
                    ~(x IN t)` by METIS_TAC [SET_CASES]
          >> Know `x' IN (high CROSS low CROSS random)` >- METIS_TAC [EXTENSION, IN_INSERT]
          >> RW_TAC std_ss [IN_CROSS]
          >> Q.EXISTS_TAC `((FST x, SND x),SND x')`
          >> RW_TAC std_ss [])
   >> POP_ORW
   >> `(IMAGE f (high CROSS low CROSS random) CROSS low) =
       (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)) UNION
       ((IMAGE f (high CROSS low CROSS random) CROSS low) DIFF
        (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF, IN_IMAGE, IN_CROSS]
            >> EQ_TAC >- (RW_TAC std_ss [] >> METIS_TAC [])
            >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
            >> METIS_TAC [])
   >> POP_ORW
   >> `DISJOINT
       (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random))
       ((IMAGE f (high CROSS low CROSS random) CROSS low) DIFF
        (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
   >> `FINITE (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)) /\
       FINITE ((IMAGE f (high CROSS low CROSS random) CROSS low) DIFF
               (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)))`
        by METIS_TAC [IMAGE_FINITE, FINITE_CROSS, FINITE_DIFF]
   >> RW_TAC std_ss [(UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
           Q.ISPECL [`(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,SND (FST s)))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`,
             `(IMAGE (f :('a, 'b, 'c, 'd) prog)
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS
             (random :'c state -> bool)) CROSS low DIFF
          IMAGE (\(s :('a, 'b, 'c) prog_state). (f s,SND (FST s)))
            (high CROSS low CROSS random))`])
          REAL_SUM_IMAGE_DISJOINT_UNION]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (f :('a, 'b, 'c, 'd) prog)
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS
             (random :'c state -> bool)) CROSS low DIFF
          IMAGE (\(s :('a, 'b, 'c) prog_state). (f s,SND (FST s)))
            (high CROSS low CROSS random))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
       (if
          x IN
          IMAGE f (high CROSS low CROSS random) CROSS low DIFF
          IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)
        then
          (\(x,z).
             joint_distribution (unif_prog_space high low random) f L
               {(x,z)} *
             logr 2
               (joint_distribution (unif_prog_space high low random) f L
                  {(x,z)} /
                distribution (unif_prog_space high low random) L {z})) x
        else
          0)) = (\x. 0)`
          by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_DIFF, IN_IMAGE, IN_CROSS]
              >> RW_TAC std_ss []
              >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR] >> POP_ORW
              >> RW_TAC std_ss []
              >> Suff `joint_distribution (unif_prog_space high low random) f L {x} = 0`
              >- RW_TAC real_ss []
              >> RW_TAC std_ss [joint_distribution_def]
              >> Suff `PREIMAGE (\x. (f x,L x)) {x} INTER (high CROSS low CROSS random) = {}`
              >- METIS_TAC [prob_space_unif_prog_space, PROB_EMPTY]
              >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER, IN_PREIMAGE, IN_SING, IN_CROSS,
                                low_state_def]
              >> Q.PAT_X_ASSUM `FST x = f x'` (MP_TAC o GSYM) >> RW_TAC std_ss []
              >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (MP_TAC o Q.SPEC `x''`)
              >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
              >> METIS_TAC [PAIR, PAIR_EQ, FST, SND])
   >> RW_TAC real_ss [REAL_SUM_IMAGE_0] >> POP_ASSUM (K ALL_TAC)
   >> `(IMAGE f (high CROSS low CROSS random) CROSS (high CROSS low)) =
       (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)) UNION
       ((IMAGE f (high CROSS low CROSS random) CROSS (high CROSS low)) DIFF
        (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF, IN_IMAGE, IN_CROSS]
            >> EQ_TAC >- (RW_TAC std_ss [] >> METIS_TAC [])
            >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
            >> METIS_TAC [])
   >> POP_ORW
   >> `DISJOINT
       (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random))
       ((IMAGE f (high CROSS low CROSS random) CROSS (high CROSS low)) DIFF
        (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
   >> `FINITE (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)) /\
       FINITE ((IMAGE f (high CROSS low CROSS random) CROSS (high CROSS low)) DIFF
        (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)))`
        by METIS_TAC [IMAGE_FINITE, FINITE_CROSS, FINITE_DIFF]
   >> RW_TAC std_ss [(UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
           Q.ISPECL [`(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,FST s))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`,
             `(IMAGE (f :('a, 'b, 'c, 'd) prog)
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS
             (random :'c state -> bool)) CROSS (high CROSS low) DIFF
          IMAGE (\(s :('a, 'b, 'c) prog_state). (f s,FST s))
            (high CROSS low CROSS random))`])
          REAL_SUM_IMAGE_DISJOINT_UNION]
   >> Q.PAT_X_ASSUM `DISJOINT P Q` (K ALL_TAC)
   >> Q.PAT_X_ASSUM `DISJOINT P Q` (K ALL_TAC)
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (f :('a, 'b, 'c, 'd) prog)
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS
             (random :'c state -> bool)) CROSS (high CROSS low) DIFF
          IMAGE (\(s :('a, 'b, 'c) prog_state). (f s,FST s))
            (high CROSS low CROSS random))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
      (if
         x IN
         IMAGE f (high CROSS low CROSS random) CROSS
         (high CROSS low) DIFF
         IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)
       then
         (\(x,y,z).
            joint_distribution (unif_prog_space high low random) f
              (\x. (H x,L x)) {(x,y,z)} *
            logr 2
              (joint_distribution (unif_prog_space high low random) f
                 (\x. (H x,L x)) {(x,y,z)} /
               distribution (unif_prog_space high low random)
                 (\x. (H x,L x)) {(y,z)})) x
       else
         0)) = (\x. 0)`
          by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_DIFF, IN_IMAGE, IN_CROSS]
              >> RW_TAC std_ss []
              >> `x = (FST x, FST (SND x), SND (SND x))` by METIS_TAC [PAIR] >> POP_ORW
              >> RW_TAC std_ss []
              >> Suff `joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(f x',SND x)} = 0`
              >- RW_TAC real_ss []
              >> RW_TAC std_ss [joint_distribution_def]
              >> Suff `PREIMAGE (\x. (f x,H x,L x)) {(f x',SND x)} INTER (high CROSS low CROSS random) = {}`
              >- METIS_TAC [prob_space_unif_prog_space, PROB_EMPTY]
              >> ONCE_REWRITE_TAC [EXTENSION]
              >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER, IN_PREIMAGE, IN_SING, IN_CROSS,
                                low_state_def, high_state_def, PAIR]
              >> Q.PAT_X_ASSUM `FST x = f x'` (MP_TAC o GSYM) >> RW_TAC std_ss []
              >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (MP_TAC o Q.SPEC `x''`)
              >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
              >> METIS_TAC [PAIR, PAIR_EQ, FST, SND])
   >> RW_TAC real_ss [REAL_SUM_IMAGE_0] >> POP_ASSUM (K ALL_TAC)
   >> NTAC 2 (Q.PAT_X_ASSUM `FINITE (P DIFF Q)` (K ALL_TAC))
   >> ASM_SIMP_TAC std_ss [GSYM lg_def]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,SND (FST s)))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random) then
                (\(x,z). joint_distribution (unif_prog_space high low random) f L {(x,z)} *
            lg (joint_distribution (unif_prog_space high low random) f L {(x,z)} /
                distribution (unif_prog_space high low random) L {z})) x else 0)) =
         (\x. (if x IN IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random) then
                (\(x,z). joint_distribution (unif_prog_space high low random) f L {(x,z)} *
            lg (joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                (&(CARD low)))) x else 0))`
         by (RW_TAC std_ss [FUN_EQ_THM, IN_IMAGE, IN_CROSS] >> RW_TAC std_ss []
             >> RW_TAC std_ss [unif_prog_space_low_distribution, GSYM REAL_INV_1OVER, real_div, REAL_INV_INV])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,FST s))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> Know `(\x. (if x IN IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random) then
            (\(x,y,z). joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
           lg (joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} /
               distribution (unif_prog_space high low random) (\x. (H x,L x)) {(y,z)})) x else 0)) =
       (\x. (if x IN IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random) then
            (\(x,y,z). joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
           lg (joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
               (&((CARD high)*(CARD low))))) x else 0))`
   >- (RW_TAC std_ss [FUN_EQ_THM, IN_IMAGE, IN_CROSS] >> RW_TAC std_ss []
       >> rename1 `FST (FST s') IN high`
       >> `FST s' = (FST (FST s'), SND (FST s'))` by RW_TAC std_ss [PAIR] >> POP_ORW
       >> RW_TAC std_ss [unif_prog_space_highlow_distribution,
                         GSYM REAL_INV_1OVER, real_div, REAL_INV_INV])
   >> Rewr'
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> ONCE_REWRITE_TAC [REAL_ADD_COMM] >> RW_TAC std_ss [GSYM real_sub]
   >> Q.UNABBREV_TAC `foo` >> RW_TAC std_ss []
QED

Theorem unif_prog_space_visible_leakage_reduce :
    !high low random f. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (visible_leakage (unif_prog_space high low random) f =
            SIGMA
  (\x.
     (\(x,y,z).
        joint_distribution (unif_prog_space high low random) f
          (\s. (H s,L s,R s)) {(x,y,z)} *
        lg
          (joint_distribution (unif_prog_space high low random) f
             (\s. (H s,L s,R s)) {(x,y,z)} *
           & (CARD high * CARD low * CARD random))) x)
  (IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s))
     (high CROSS low CROSS random)) -
SIGMA
  (\x.
     (\(x,z).
        joint_distribution (unif_prog_space high low random) f (\s. (L s,R s))
          {(x,z)} *
        lg
          (joint_distribution (unif_prog_space high low random) f (\s. (L s,R s))
             {(x,z)} * & (CARD low * CARD random))) x)
  (IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random)))
Proof
   RW_TAC std_ss [visible_leakage_def]
   >> Q.ABBREV_TAC `foo = SIGMA
  (\x.
     (\(x,y,z).
        joint_distribution (unif_prog_space high low random) f
          (\s. (H s,L s,R s)) {(x,y,z)} *
        lg
          (joint_distribution (unif_prog_space high low random) f
             (\s. (H s,L s,R s)) {(x,y,z)} *
           & (CARD high * CARD low * CARD random))) x)
  (IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s))
     (high CROSS low CROSS random)) -
SIGMA
  (\x.
     (\(x,z).
        joint_distribution (unif_prog_space high low random) f (\s. (L s,R s))
          {(x,z)} *
        lg
          (joint_distribution (unif_prog_space high low random) f (\s. (L s,R s))
             {(x,z)} * & (CARD low * CARD random))) x)
  (IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random))`

   >> `random_variable (f :('a, 'b, 'c, 'd) prog) (unif_prog_space high low random)
                         (IMAGE (f :('a, 'b, 'c, 'd) prog) (p_space (unif_prog_space high low random)),
                          POW (IMAGE (f :('a, 'b, 'c, 'd) prog) (p_space (unif_prog_space high low random))))`
      by (RW_TAC std_ss [random_variable_def, prob_space_unif_prog_space]
          >> RW_TAC std_ss [p_space_def, events_def]
          >> MATCH_MP_TAC MEASURABLE_POW_TO_POW_IMAGE
          >> CONJ_TAC >- METIS_TAC [prob_space_unif_prog_space, prob_space_def]
          >> RW_TAC std_ss [unif_prog_space_def, measurable_sets_def, m_space_def])
   >> `random_variable (H :('a, 'b, 'c, 'a) prog) (unif_prog_space high low random)
                         (IMAGE (H :('a, 'b, 'c, 'a) prog) (p_space (unif_prog_space high low random)),
                          POW (IMAGE (H :('a, 'b, 'c, 'a) prog) (p_space (unif_prog_space high low random))))`
      by (RW_TAC std_ss [random_variable_def, prob_space_unif_prog_space]
          >> RW_TAC std_ss [p_space_def, events_def]
          >> MATCH_MP_TAC MEASURABLE_POW_TO_POW_IMAGE
          >> CONJ_TAC >- METIS_TAC [prob_space_unif_prog_space, prob_space_def]
          >> RW_TAC std_ss [unif_prog_space_def, measurable_sets_def, m_space_def])
   >> `random_variable (\s.((L :('a, 'b, 'c, 'b) prog) s,(R :('a, 'b, 'c, 'c) prog) s))
                        (unif_prog_space high low random)
                         (IMAGE (\s.((L :('a, 'b, 'c, 'b) prog) s,(R :('a, 'b, 'c, 'c) prog) s))
                                 (p_space (unif_prog_space high low random)),
                          POW (IMAGE (\s.((L :('a, 'b, 'c, 'b) prog) s,(R :('a, 'b, 'c, 'c) prog) s))
                                 (p_space (unif_prog_space high low random))))`
      by (RW_TAC std_ss [random_variable_def, prob_space_unif_prog_space]
          >> RW_TAC std_ss [p_space_def, events_def]
          >> MATCH_MP_TAC MEASURABLE_POW_TO_POW_IMAGE
          >> CONJ_TAC >- METIS_TAC [prob_space_unif_prog_space, prob_space_def]

          >> RW_TAC std_ss [unif_prog_space_def, measurable_sets_def, m_space_def])

   >> `FINITE (p_space (unif_prog_space high low random))`
      by RW_TAC std_ss [unif_prog_space_def, FINITE_CROSS, PSPACE]
   >> `POW (p_space (unif_prog_space high low random)) = events (unif_prog_space high low random)`
      by RW_TAC std_ss [unif_prog_space_def, PSPACE, EVENTS]
 (* stage work *)
   >> ‘prob_space (unif_prog_space high low random)’ by PROVE_TAC [prob_space_unif_prog_space]
   >> RW_TAC std_ss [finite_conditional_mutual_information_reduce]
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> RW_TAC std_ss []
   >> `IMAGE (\s. (L s,R s)) (high CROSS low CROSS random) = low CROSS random`
      by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE, low_state_def, random_state_def, IN_CROSS]
          >> EQ_TAC
          >- (RW_TAC std_ss [] >> RW_TAC std_ss [])
          >> `?x t. (high CROSS low CROSS random = x INSERT t) /\
                    ~(x IN t)` by METIS_TAC [SET_CASES]
          >> Know `x' IN (high CROSS low CROSS random)` >- METIS_TAC [EXTENSION, IN_INSERT]
          >> RW_TAC std_ss [IN_CROSS]
          >> Q.EXISTS_TAC `((FST (FST x'), FST x), SND x)`
          >> RW_TAC std_ss [])
   >> POP_ORW
   >> `IMAGE (\s. (H s,L s,R s)) (high CROSS low CROSS random) = (high CROSS (low CROSS random))`
      by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE, low_state_def, high_state_def, random_state_def, IN_CROSS]
          >> EQ_TAC
          >- (RW_TAC std_ss [] >> RW_TAC std_ss [])
          >> RW_TAC std_ss [IN_CROSS]
          >> Q.EXISTS_TAC `((FST x, FST(SND x)),SND(SND x))`
          >> RW_TAC std_ss [])
   >> POP_ORW
   >> `(IMAGE f (high CROSS low CROSS random) CROSS (low CROSS random)) =
       (IMAGE (\s. (f s,(SND (FST s),SND s))) (high CROSS low CROSS random)) UNION
       ((IMAGE f (high CROSS low CROSS random) CROSS (low CROSS random)) DIFF
        (IMAGE (\s. (f s,(SND (FST s),SND s))) (high CROSS low CROSS random)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF, IN_IMAGE, IN_CROSS]
            >> EQ_TAC >- (RW_TAC std_ss [] >> METIS_TAC [])
            >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
            >> METIS_TAC [])
   >> POP_ORW
   >> `DISJOINT
       (IMAGE (\s. (f s,(SND (FST s),SND s))) (high CROSS low CROSS random))
       ((IMAGE f (high CROSS low CROSS random) CROSS (low CROSS random)) DIFF
        (IMAGE (\s. (f s,(SND (FST s),SND s))) (high CROSS low CROSS random)))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
   >> `FINITE (IMAGE (\s. (f s,(SND (FST s),SND s))) (high CROSS low CROSS random)) /\
       FINITE ((IMAGE f (high CROSS low CROSS random) CROSS (low CROSS random)) DIFF
               (IMAGE (\s. (f s,(SND (FST s),SND s))) (high CROSS low CROSS random)))`
        by METIS_TAC [IMAGE_FINITE, FINITE_CROSS, FINITE_DIFF]
   >> RW_TAC std_ss [(UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
           Q.ISPECL [`(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,SND (FST s),SND s))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`,
             `(IMAGE (f :('a, 'b, 'c, 'd) prog)
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS
             (random :'c state -> bool)) CROSS (low CROSS random) DIFF
          IMAGE (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,SND (FST s),SND s))
            (high CROSS low CROSS random))`])
          REAL_SUM_IMAGE_DISJOINT_UNION]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (f :('a, 'b, 'c, 'd) prog)
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS
             (random :'c state -> bool)) CROSS (low CROSS random) DIFF
          IMAGE (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,SND (FST s),SND s))
            (high CROSS low CROSS random))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
       (if
          x IN
          IMAGE f (high CROSS low CROSS random) CROSS (low CROSS random) DIFF
          IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random)
        then
          (\(x,z).
             joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(x,z)} *
             logr 2
               (joint_distribution (unif_prog_space high low random) f
                  (\s. (L s,R s)) {(x,z)} /
                distribution (unif_prog_space high low random)
                  (\s. (L s,R s)) {z})) x
        else
          0)) = (\x. 0)`
          by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_DIFF, IN_IMAGE, IN_CROSS]
              >> RW_TAC std_ss []
              >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR] >> POP_ORW
              >> RW_TAC std_ss []
              >> Suff `joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {x} = 0`
              >- RW_TAC real_ss []
              >> RW_TAC std_ss [joint_distribution_def]
              >> Suff `PREIMAGE (\s. (f s,L s,R s)) {x} INTER
                       (high CROSS low CROSS random) = {}`
              >- METIS_TAC [prob_space_unif_prog_space, PROB_EMPTY]
              >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER, IN_PREIMAGE, IN_SING, IN_CROSS,
                                low_state_def, random_state_def]
              >> Q.PAT_X_ASSUM `FST x = f x'` (MP_TAC o GSYM) >> RW_TAC std_ss []
              >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (MP_TAC o Q.SPEC `x''`)
              >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
              >> METIS_TAC [PAIR, PAIR_EQ, FST, SND])
   >> RW_TAC real_ss [REAL_SUM_IMAGE_0] >> POP_ASSUM (K ALL_TAC)
   >> `(IMAGE f (high CROSS low CROSS random) CROSS (high CROSS (low CROSS random))) =
       (IMAGE (\s. (f s,(FST(FST s),(SND(FST s),SND s)))) (high CROSS low CROSS random)) UNION
       ((IMAGE f (high CROSS low CROSS random) CROSS (high CROSS (low CROSS random))) DIFF
        (IMAGE (\s. (f s,(FST(FST s),(SND(FST s),SND s)))) (high CROSS low CROSS random)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF, IN_IMAGE, IN_CROSS]
            >> EQ_TAC >- (RW_TAC std_ss [] >> METIS_TAC [])
            >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
            >> METIS_TAC [])
   >> POP_ORW
   >> `DISJOINT
       (IMAGE (\s. (f s,(FST(FST s),(SND(FST s),SND s)))) (high CROSS low CROSS random))
       ((IMAGE f (high CROSS low CROSS random) CROSS (high CROSS (low CROSS random))) DIFF
        (IMAGE (\s. (f s,(FST(FST s),(SND(FST s),SND s)))) (high CROSS low CROSS random)))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
   >> `FINITE (IMAGE (\s. (f s,(FST(FST s),(SND(FST s),SND s)))) (high CROSS low CROSS random)) /\
       FINITE ((IMAGE f (high CROSS low CROSS random) CROSS (high CROSS (low CROSS random))) DIFF
        (IMAGE (\s. (f s,(FST(FST s),(SND(FST s),SND s)))) (high CROSS low CROSS random)))`
        by METIS_TAC [IMAGE_FINITE, FINITE_CROSS, FINITE_DIFF]
   >> RW_TAC std_ss [(UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
           Q.ISPECL [`(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,FST (FST s),SND (FST s),
                SND s))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`,
             `(IMAGE (f :('a, 'b, 'c, 'd) prog)
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS
             (random :'c state -> bool)) CROSS (high CROSS (low CROSS random)) DIFF
          IMAGE (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,FST (FST s),SND (FST s),
                SND s))
            (high CROSS low CROSS random))`])
          REAL_SUM_IMAGE_DISJOINT_UNION]
   >> Q.PAT_X_ASSUM `DISJOINT P Q` (K ALL_TAC)
   >> Q.PAT_X_ASSUM `DISJOINT P Q` (K ALL_TAC)
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (f :('a, 'b, 'c, 'd) prog)
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS
             (random :'c state -> bool)) CROSS (high CROSS (low CROSS random)) DIFF
          IMAGE (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,FST (FST s),SND (FST s),
                SND s))
            (high CROSS low CROSS random))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
      (if
         x IN
         IMAGE f (high CROSS low CROSS random) CROSS
         (high CROSS (low CROSS random)) DIFF
         IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s)) (high CROSS low CROSS random)
       then
         (\(x,y,z).
            joint_distribution (unif_prog_space high low random) f
              (\s. (H s,L s,R s)) {(x,y,z)} *
            logr 2
              (joint_distribution (unif_prog_space high low random) f
           (\s. (H s,L s,R s)) {(x,y,z)} /
         distribution (unif_prog_space high low random)
           (\s. (H s,L s,R s)) {(y,z)})) x
       else
         0)) = (\x. 0)`
          by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_DIFF, IN_IMAGE, IN_CROSS]
              >> RW_TAC std_ss []
              >> `x = (FST x, FST (SND x), SND (SND x))` by METIS_TAC [PAIR] >> POP_ORW
              >> RW_TAC std_ss []
              >> Suff `joint_distribution (unif_prog_space high low random) f (\s. (H s,L s,R s)) {(f x',SND x)} = 0`
              >- RW_TAC real_ss []
              >> RW_TAC std_ss [joint_distribution_def]
              >> Suff `PREIMAGE (\s. (f s,H s,L s,R s)) {(f x',SND x)} INTER
                       (high CROSS low CROSS random) = {}`
              >- METIS_TAC [prob_space_unif_prog_space, PROB_EMPTY]
              >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER, IN_PREIMAGE, IN_SING, IN_CROSS,
                                low_state_def, high_state_def, PAIR, random_state_def]
              >> Q.PAT_X_ASSUM `FST x = f x'` (MP_TAC o GSYM) >> RW_TAC std_ss []
              >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (MP_TAC o Q.SPEC `x''`)
              >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
              >> METIS_TAC [PAIR, PAIR_EQ, FST, SND])
   >> RW_TAC real_ss [REAL_SUM_IMAGE_0] >> POP_ASSUM (K ALL_TAC)
   >> NTAC 2 (Q.PAT_X_ASSUM `FINITE (P DIFF Q)` (K ALL_TAC))
   >> ASM_SIMP_TAC std_ss [GSYM lg_def]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,SND (FST s),SND s))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random) then
                (\(x,z). joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(x,z)} *
            lg (joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(x,z)} /
                distribution (unif_prog_space high low random) (\s. (L s,R s)) {z})) x else 0)) =
         (\x. (if x IN IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random) then
                (\(x,z). joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(x,z)} *
            lg (joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(x,z)} *
                (&(CARD low * CARD random)))) x else 0))`
         by (RW_TAC std_ss [FUN_EQ_THM, IN_IMAGE, IN_CROSS] >> RW_TAC std_ss []
             >> RW_TAC std_ss [unif_prog_space_lowrandom_distribution, GSYM REAL_INV_1OVER, real_div, REAL_INV_INV])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,FST (FST s),SND (FST s),
                SND s))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s)) (high CROSS low CROSS random) then
            (\(x,y,z). joint_distribution (unif_prog_space high low random) f (\s. (H s,L s,R s)) {(x,y,z)} *
           lg (joint_distribution (unif_prog_space high low random) f (\s. (H s,L s,R s)) {(x,y,z)} /
               distribution (unif_prog_space high low random) (\s. (H s,L s,R s)) {(y,z)})) x else 0)) =
       (\x. (if x IN IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s)) (high CROSS low CROSS random) then
            (\(x,y,z). joint_distribution (unif_prog_space high low random) f (\s. (H s,L s,R s)) {(x,y,z)} *
           lg (joint_distribution (unif_prog_space high low random) f (\s. (H s,L s,R s)) {(x,y,z)} *
               (&((CARD high)*(CARD low)*(CARD random))))) x else 0))`
         by (RW_TAC std_ss [FUN_EQ_THM, IN_IMAGE, IN_CROSS] >> RW_TAC std_ss []
             >> `FST s' = (FST (FST s'), SND (FST s'))` by RW_TAC std_ss [PAIR] >> POP_ORW
             >> RW_TAC std_ss [unif_prog_space_highlowrandom_distribution, GSYM REAL_INV_1OVER, real_div, REAL_INV_INV])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> ONCE_REWRITE_TAC [REAL_ADD_COMM] >> RW_TAC std_ss [GSYM real_sub]
   >> Q.UNABBREV_TAC `foo` >> RW_TAC std_ss []
QED

val unif_prog_space_leakage_lemma1 = store_thm
  ("unif_prog_space_leakage_lemma1",
   ``!high low random (f :('a, 'b, 'c, 'd) prog). FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (SIGMA (\x. (\(x,z).
                  joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                     & (CARD low))) x)
                  (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random))=
            SIGMA (\x. (\(x,z).
                  ((1/(&(CARD high * CARD low * CARD random)))*
                            (SIGMA (\(h,r). if (f((h,z),r)=x) then 1 else 0)
                                   (high CROSS random))) *
                  lg (((1/(&(CARD high * CARD low * CARD random)))*
                            (SIGMA (\(h,r). if (f((h,z),r)=x) then 1 else 0)
                                   (high CROSS random))) *
                      & (CARD low))) x)
                  (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)))``,
   RW_TAC std_ss []
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> `FINITE (IMAGE (\s. (f s,SND(FST s))) (high CROSS low CROSS random))`
        by METIS_TAC [IMAGE_FINITE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
               ((f :('a, 'b, 'c, 'd) prog) s,SND(FST s)))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> Suff `(\x. (if x IN IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random) then
                 (\x. (\(x,z). joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                 lg (joint_distribution (unif_prog_space high low random) f L {(x,z)} * & (CARD low))) x) x
                 else 0)) =
            (\x. (if x IN IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random) then
                 (\x. (\(x,z). 1 / & (CARD high * CARD low * CARD random) *
                 SIGMA (\(h,r). (if f ((h,z),r) = x then 1 else 0)) (high CROSS random) *
                 lg (1 / & (CARD high * CARD low * CARD random) *
                 SIGMA (\(h,r). (if f ((h,z),r) = x then 1 else 0)) (high CROSS random) *
                       & (CARD low))) x) x else 0))`
   >- RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_IMAGE, IN_CROSS]
   >> RW_TAC std_ss []
   >> rename1 `FST (FST s') IN high`
   >> Q.ABBREV_TAC `j = joint_distribution (unif_prog_space high low random) f L {(f s',SND (FST s'))}`
   >> Q.ABBREV_TAC `s = 1 / & (CARD high * CARD low * CARD random) *
                                 SIGMA (\(h,r). (if f ((h,SND (FST s')),r) = f s' then 1 else 0))
                                       (high CROSS random)`
   >> Suff `j = s`
   >- RW_TAC std_ss []
   >> Q.UNABBREV_TAC `j` >> Q.UNABBREV_TAC `s`
   >> RW_TAC std_ss [joint_distribution_def, unif_prog_space_def, unif_prog_dist_def, PROB,
                     FINITE_CROSS, CARD_CROSS]
   >>  `(\s. (if s IN high CROSS low CROSS random then
                     1 / & (CARD high * CARD low * CARD random) else 0)) =
        (\s. (1 / & (CARD high * CARD low * CARD random)) *
                     (\s. if s IN high CROSS low CROSS random then 1 else 0) s)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [])
   >> POP_ORW
   >> RW_TAC std_ss [REAL_SUM_IMAGE_CMUL, FINITE_CROSS, FINITE_INTER]
   >> RW_TAC std_ss [REAL_EQ_LMUL]
   >> Cases_on `(1 / & (CARD high * CARD low * CARD random) = 0)`
   >> RW_TAC std_ss []
   >> `PREIMAGE (\x. (f x,L x)) {(f s',SND (FST s'))} =
       PREIMAGE f {f s'} INTER PREIMAGE L {SND (FST s')}`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_SING, IN_PREIMAGE] >> METIS_TAC [])
   >> POP_ORW
   >> `FINITE (PREIMAGE f {f s'} INTER PREIMAGE L {SND (FST s')} INTER (high CROSS low CROSS random))`
      by METIS_TAC [FINITE_INTER, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(PREIMAGE (f :('a, 'b, 'c, 'd) prog)
            {f (s' :('a, 'b, 'c) prog_state)} INTER
          PREIMAGE (L :('a, 'b, 'c, 'b) prog) {SND (FST s')} INTER
          ((high :'a state -> bool) CROSS (low :'b state -> bool) CROSS
           (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN PREIMAGE f {f s'} INTER PREIMAGE L {SND (FST s')} INTER (high CROSS low CROSS random)
            then (\s. (if s IN high CROSS low CROSS random then 1 else 0)) x else 0)) =
       (\x. (if x IN PREIMAGE f {f s'} INTER PREIMAGE L {SND (FST s')} INTER (high CROSS low CROSS random)
            then 1 else 0))`
            by METIS_TAC [IN_INTER]
   >> POP_ORW
   >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_CARD]
   >> `high CROSS random = IMAGE (\x. (FST (FST x),SND x)) (high CROSS {SND (FST s')} CROSS random)`
      by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_IMAGE, IN_SING]
          >> EQ_TAC >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `((FST x, SND (FST s')),SND x)`
                        >> RW_TAC std_ss [FST,SND,PAIR])
          >> RW_TAC std_ss [] >> RW_TAC std_ss [FST, SND])
   >> POP_ORW
   >> `(PREIMAGE f {f s'} INTER PREIMAGE L {SND (FST s')} INTER (high CROSS low CROSS random)) =
       (PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS random))`
       by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, low_state_def, IN_CROSS]
           >> METIS_TAC [])
   >> POP_ORW
   >> `INJ (\x. (FST (FST x),SND x)) (high CROSS {SND (FST s')} CROSS random)
           (IMAGE (\x. (FST (FST x),SND x)) (high CROSS {SND (FST s')} CROSS random))`
        by (RW_TAC std_ss [INJ_DEF, IN_IMAGE, IN_SING, IN_CROSS] >> METIS_TAC [PAIR])
   >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, FINITE_CROSS, FINITE_SING, o_DEF]
   >> Q.ABBREV_TAC `c = & (CARD (PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS random)))`
   >> `(high CROSS {SND (FST s')} CROSS random) =
       (PREIMAGE f {f s'} INTER
                (high CROSS {SND (FST s')} CROSS random)) UNION
       ((high CROSS {SND (FST s')} CROSS random) DIFF
        (PREIMAGE f {f s'} INTER
                (high CROSS {SND (FST s')} CROSS random)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_UNION, IN_DIFF] >> DECIDE_TAC)
   >> POP_ORW
   >> `DISJOINT (PREIMAGE f {f s'} INTER
                   (high CROSS {SND (FST s')} CROSS random))
                ((high CROSS {SND (FST s')} CROSS random) DIFF
                       (PREIMAGE f {f s'} INTER
                       (high CROSS {SND (FST s')} CROSS random)))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_INTER, IN_DIFF] >> DECIDE_TAC)
   >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION, FINITE_CROSS, FINITE_SING, FINITE_INTER, FINITE_DIFF]
   >> `FINITE (high CROSS {SND (FST s')} CROSS random DIFF
          PREIMAGE f {f s'} INTER
          (high CROSS {SND (FST s')} CROSS random))`
          by RW_TAC std_ss [FINITE_CROSS, FINITE_SING, FINITE_INTER, FINITE_DIFF]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `((high :'a state -> bool) CROSS
          {SND (FST (s' :('a, 'b, 'c) prog_state))} CROSS
          (random :'c state -> bool) DIFF
          PREIMAGE (f :('a, 'b, 'c, 'd) prog) {f s'} INTER
          (high CROSS {SND (FST s')} CROSS random))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN high CROSS {SND (FST s')} CROSS random DIFF
                     PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS random) then
             (\x. (if f ((FST (FST x),SND (FST s')),SND x) = f s' then 1 else 0)) x else 0)) =
       (\x. 0)`
       by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_DIFF, IN_INTER, IN_CROSS, IN_SING, IN_PREIMAGE]
           >> RW_TAC real_ss [] >> METIS_TAC [PAIR])
   >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
   >> NTAC 3 (POP_ASSUM (K ALL_TAC))
   >> `FINITE (PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS random))`
      by RW_TAC std_ss [FINITE_INTER, FINITE_CROSS, FINITE_SING]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(PREIMAGE (f :('a, 'b, 'c, 'd) prog)
            {f (s' :('a, 'b, 'c) prog_state)} INTER
          ((high :'a state -> bool) CROSS {SND (FST s')} CROSS
           (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS random) then
            (\x. (if f ((FST (FST x),SND (FST s')),SND x) = f s' then 1 else 0)) x
            else 0)) =
       (\x. (if x IN PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS random) then
            1 else 0))`
        by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_INTER, IN_SING, IN_CROSS, IN_PREIMAGE]
            >> RW_TAC std_ss []
            >> METIS_TAC [PAIR])
   >> POP_ORW
   >> Q.UNABBREV_TAC `c`
   >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_CARD]);

val unif_prog_space_visible_leakage_lemma1 = store_thm
  ("unif_prog_space_visible_leakage_lemma1",
   ``!high low random (f :('a, 'b, 'c, 'd) prog). FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (SIGMA (\x. (\(x,z).
                  joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(x,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(x,z)} *
                     & (CARD low * CARD random))) x)
                  (IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random))=
            SIGMA (\x. (\(x,z).
                  ((1/(&(CARD high * CARD low * CARD random)))*
                            (SIGMA (\h. if (f((h,FST z),SND z)=x) then 1 else 0) high)) *
                  lg (((1/(&(CARD high * CARD low * CARD random)))*
                            (SIGMA (\h. if (f((h,FST z),SND z)=x) then 1 else 0) high)) *
                      & (CARD low * CARD random))) x)
                  (IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random)))``,
   RW_TAC std_ss []
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> `FINITE (IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random))`
        by METIS_TAC [IMAGE_FINITE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE
            (\(s :('a, 'b, 'c) prog_state).
              ((f :('a, 'b, 'c, 'd) prog) s,SND (FST s),SND s))
            ((high :'a state -> bool) CROSS
             (low :'b state -> bool) CROSS (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> Suff `(\x. (if x IN IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random) then
                 (\x. (\(x,z). joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(x,z)} *
                 lg (joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(x,z)} * & (CARD low * CARD random))) x) x
                 else 0)) =
            (\x. (if x IN IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random) then
                 (\x. (\(x,z). 1 / & (CARD high * CARD low * CARD random) *
                 SIGMA (\h. (if f ((h,FST z),SND z) = x then 1 else 0)) high *
                 lg (1 / & (CARD high * CARD low * CARD random) *
                 SIGMA (\h. (if f ((h,FST z),SND z) = x then 1 else 0)) high *
                       & (CARD low * CARD random))) x) x else 0))`
   >- RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_IMAGE, IN_CROSS]
   >> RW_TAC std_ss []
   >> rename1 `FST (FST s') IN high`
   >> Q.ABBREV_TAC `j = joint_distribution (unif_prog_space high low random) f (\s. (L s,R s)) {(f s',(SND (FST s'),SND s'))}`
   >> Q.ABBREV_TAC `s = 1 / & (CARD high * CARD low * CARD random) *
                                 SIGMA (\h. (if f ((h,SND (FST s')),SND s') = f s' then 1 else 0)) high`
   >> Suff `j = s`
   >- RW_TAC std_ss []
   >> Q.UNABBREV_TAC `j` >> Q.UNABBREV_TAC `s`
   >> RW_TAC std_ss [joint_distribution_def, unif_prog_space_def, unif_prog_dist_def, PROB,
                     FINITE_CROSS, CARD_CROSS]
   >>  `(\s. (if s IN high CROSS low CROSS random then
                     1 / & (CARD high * CARD low * CARD random) else 0)) =
        (\s. (1 / & (CARD high * CARD low * CARD random)) *
                     (\s. if s IN high CROSS low CROSS random then 1 else 0) s)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [])
   >> POP_ORW
   >> RW_TAC std_ss [REAL_SUM_IMAGE_CMUL, FINITE_CROSS, FINITE_INTER]
   >> RW_TAC std_ss [REAL_EQ_LMUL]
   >> Cases_on `(1 / & (CARD high * CARD low * CARD random) = 0)`
   >> RW_TAC std_ss []
   >> `PREIMAGE (\s. (f s,L s,R s)) {(f s',SND (FST s'),SND s')} =
       PREIMAGE f {f s'} INTER PREIMAGE (\s. (L s,R s)) {(SND (FST s'),SND s')}`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_SING, IN_PREIMAGE] >> METIS_TAC [])
   >> POP_ORW
   >> `FINITE (PREIMAGE f {f s'} INTER PREIMAGE (\s. (L s,R s)) {(SND (FST s'),SND s')} INTER (high CROSS low CROSS random))`
      by METIS_TAC [FINITE_INTER, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(PREIMAGE (f :('a, 'b, 'c, 'd) prog)
            {f (s' :('a, 'b, 'c) prog_state)} INTER
          PREIMAGE (\(s :('a, 'b, 'c) prog_state). (L s,R s)) {(SND (FST s'),SND s')} INTER
          ((high :'a state -> bool) CROSS (low :'b state -> bool) CROSS
           (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN PREIMAGE f {f s'} INTER PREIMAGE (\s. (L s,R s)) {(SND (FST s'),SND s')} INTER (high CROSS low CROSS random)
            then (\s. (if s IN high CROSS low CROSS random then 1 else 0)) x else 0)) =
       (\x. (if x IN PREIMAGE f {f s'} INTER PREIMAGE (\s. (L s,R s)) {(SND (FST s'),SND s')} INTER (high CROSS low CROSS random)
            then 1 else 0))`
            by METIS_TAC [IN_INTER]
   >> POP_ORW
   >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_CARD]
   >> `(PREIMAGE f {f s'} INTER PREIMAGE (\s. (L s,R s)) {(SND (FST s'),SND s')} INTER (high CROSS low CROSS random)) =
       (PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS {SND s'}))`
       by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, low_state_def, random_state_def, IN_CROSS]
           >> METIS_TAC [])
   >> POP_ORW
   >> Q.ABBREV_TAC `c = CARD
     (PREIMAGE f {f s'} INTER
      (high CROSS {SND (FST s')} CROSS {SND s'}))`
   >> `high = IMAGE (FST o FST) (high CROSS {SND (FST s')} CROSS {SND s'})`
      by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_IMAGE, IN_SING, o_DEF]
          >> EQ_TAC >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `((x, SND (FST s')),SND s')`
                        >> RW_TAC std_ss [FST,SND,PAIR])
          >> RW_TAC std_ss [] >> RW_TAC std_ss [FST, SND])
   >> POP_ORW
   >> `INJ (FST o FST) (high CROSS {SND (FST s')} CROSS {SND s'})
           (IMAGE (FST o FST) (high CROSS {SND (FST s')} CROSS {SND s'}))`
        by (RW_TAC std_ss [INJ_DEF, IN_IMAGE, IN_SING, IN_CROSS, o_DEF] >> METIS_TAC [PAIR])
   >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, FINITE_CROSS, FINITE_SING, o_DEF]
   >> `(high CROSS {SND (FST s')} CROSS {SND s'}) =
       (PREIMAGE f {f s'} INTER
                (high CROSS {SND (FST s')} CROSS {SND s'})) UNION
       ((high CROSS {SND (FST s')} CROSS {SND s'}) DIFF
        (PREIMAGE f {f s'} INTER
                (high CROSS {SND (FST s')} CROSS {SND s'})))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_UNION, IN_DIFF] >> DECIDE_TAC)
   >> POP_ORW
   >> `DISJOINT (PREIMAGE f {f s'} INTER
                   (high CROSS {SND (FST s')} CROSS {SND s'}))
                ((high CROSS {SND (FST s')} CROSS {SND s'}) DIFF
                       (PREIMAGE f {f s'} INTER
                       (high CROSS {SND (FST s')} CROSS {SND s'})))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_INTER, IN_DIFF] >> DECIDE_TAC)
   >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION, FINITE_CROSS, FINITE_SING, FINITE_INTER, FINITE_DIFF]
   >> `FINITE (high CROSS {SND (FST s')} CROSS {SND s'} DIFF
          PREIMAGE f {f s'} INTER
          (high CROSS {SND (FST s')} CROSS {SND s'}))`
          by RW_TAC std_ss [FINITE_CROSS, FINITE_SING, FINITE_INTER, FINITE_DIFF]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `((high :'a state -> bool) CROSS
          {SND (FST (s' :('a, 'b, 'c) prog_state))} CROSS
          ({SND (s' :('a, 'b, 'c) prog_state)}) DIFF
          PREIMAGE (f :('a, 'b, 'c, 'd) prog) {f s'} INTER
          (high CROSS {SND (FST s')} CROSS {SND (s' :('a, 'b, 'c) prog_state)}))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN high CROSS {SND (FST s')} CROSS {SND s'} DIFF
                     PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS {SND s'}) then
             (\x. (if f ((FST (FST x),SND (FST s')),SND s') = f s' then 1 else 0)) x else 0)) =
       (\x. 0)`
       by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_DIFF, IN_INTER, IN_CROSS, IN_SING, IN_PREIMAGE]
           >> RW_TAC real_ss [] >> METIS_TAC [PAIR])
   >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
   >> NTAC 3 (POP_ASSUM (K ALL_TAC))
   >> `FINITE (PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS {SND s'}))`
      by RW_TAC std_ss [FINITE_INTER, FINITE_CROSS, FINITE_SING]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(PREIMAGE (f :('a, 'b, 'c, 'd) prog)
            {f (s' :('a, 'b, 'c) prog_state)} INTER
          ((high :'a state -> bool) CROSS {SND (FST s')} CROSS
           {SND (s' :('a, 'b, 'c) prog_state)}))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS {SND s'}) then
            (\x. (if f ((FST (FST x),SND (FST s')),SND s') = f s' then 1 else 0)) x
            else 0)) =
       (\x. (if x IN PREIMAGE f {f s'} INTER (high CROSS {SND (FST s')} CROSS {SND s'}) then
            1 else 0))`
        by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_INTER, IN_SING, IN_CROSS, IN_PREIMAGE]
            >> RW_TAC std_ss []
            >> METIS_TAC [PAIR])
   >> POP_ORW
   >> Q.UNABBREV_TAC `c`
   >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_CARD]);

val unif_prog_space_leakage_lemma2 = store_thm
  ("unif_prog_space_leakage_lemma2",
   ``!high low random (f :('a, 'b, 'c, 'd) prog). FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (SIGMA (\x. (\(x,y,z).
                  joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
                      & (CARD high * CARD low))) x)
                  (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random))=
            SIGMA (\x. (\(out,h,l).
                  ((1/(&(CARD high * CARD low * CARD random)))*
                   (SIGMA (\r. if (f((h,l),r)=out) then 1 else 0) random)) *
                  lg (((1/(&(CARD high * CARD low * CARD random)))*
                   (SIGMA (\r. if (f((h,l),r)=out) then 1 else 0) random)) *
                      & (CARD high * CARD low))) x)
                  (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)))``,
   RW_TAC std_ss []
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> `FINITE (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random))`
        by METIS_TAC [IMAGE_FINITE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE
           (\(s :('a, 'b, 'c) prog_state).
              ((f :('a, 'b, 'c, 'd) prog) s,FST s))
           ((high :'a state -> bool) CROSS (low :'b state -> bool) CROSS
            (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> Suff `(\x. (if x IN IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random) then
                     (\x. (\(x,y,z). joint_distribution (unif_prog_space high low random) f
                          (\x. (H x,L x)) {(x,y,z)} *
                lg (joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
                   & (CARD high * CARD low))) x) x else 0)) =
            (\x. (if x IN IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random) then
                      (\x. (\(out,h,l).
                           1 / & (CARD high * CARD low * CARD random) *
              SIGMA (\r. (if f ((h,l),r) = out then 1 else 0)) random *
                    lg (1 / & (CARD high * CARD low * CARD random) *
                    SIGMA (\r. (if f ((h,l),r) = out then 1 else 0))
                   random * & (CARD high * CARD low))) x) x else 0))`
   >- RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_IMAGE, IN_CROSS]
   >> rename1 `FST (FST s') IN high`
   >> `FST s' = (FST(FST s'),SND(FST s'))` by RW_TAC std_ss [PAIR]
   >> POP_ORW >> RW_TAC std_ss []
   >> Q.ABBREV_TAC `j = joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(f s',FST s')}`
   >> Q.ABBREV_TAC `s = 1 / & (CARD high * CARD low * CARD random) *
                        SIGMA (\r. (if f (FST s',r) = f s' then 1 else 0)) random`
   >> Suff `j = s`
   >- RW_TAC std_ss []
   >> Q.UNABBREV_TAC `j` >> Q.UNABBREV_TAC `s`
   >> RW_TAC std_ss [joint_distribution_def, unif_prog_space_def, unif_prog_dist_def, PROB,
                     FINITE_CROSS, CARD_CROSS]
   >>  `(\s. (if s IN high CROSS low CROSS random then
                     1 / & (CARD high * CARD low * CARD random) else 0)) =
        (\s. (1 / & (CARD high * CARD low * CARD random)) *
                     (\s. if s IN high CROSS low CROSS random then 1 else 0) s)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [])
   >> POP_ORW
   >> RW_TAC std_ss [REAL_SUM_IMAGE_CMUL, FINITE_CROSS, FINITE_INTER]
   >> RW_TAC std_ss [REAL_EQ_LMUL]
   >> Cases_on `(1 / & (CARD high * CARD low * CARD random) = 0)`
   >> RW_TAC std_ss []
   >> `PREIMAGE (\x. (f x,H x,L x)) {(f s',FST s')} =
       PREIMAGE f {f s'} INTER PREIMAGE (\x. (H x,L x)) {FST s'}`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_SING, IN_PREIMAGE] >> METIS_TAC [])
   >> POP_ORW
   >> `FINITE (PREIMAGE f {f s'} INTER PREIMAGE (\x. (H x,L x)) {FST s'} INTER (high CROSS low CROSS random))`
      by METIS_TAC [FINITE_INTER, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(PREIMAGE (f :('a, 'b, 'c, 'd) prog)
            {f (s' :('a, 'b, 'c) prog_state)} INTER
          PREIMAGE (\(x :('a, 'b, 'c) prog_state). (H x,L x))
            {FST s'} INTER
          ((high :'a state -> bool) CROSS (low :'b state -> bool) CROSS
           (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN PREIMAGE f {f s'} INTER PREIMAGE (\x. (H x,L x)) {FST s'} INTER
                     (high CROSS low CROSS random)
            then (\s. (if s IN high CROSS low CROSS random then 1 else 0)) x else 0)) =
       (\x. (if x IN PREIMAGE f {f s'} INTER PREIMAGE (\x. (H x,L x)) {FST s'} INTER
                      (high CROSS low CROSS random)
            then 1 else 0))`
            by METIS_TAC [IN_INTER]
   >> POP_ORW
   >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_CARD]
   >> `random = IMAGE SND ({FST (FST s')} CROSS {SND (FST s')} CROSS random)`
      by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_IMAGE, IN_SING]
          >> EQ_TAC >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `((FST (FST s'), SND (FST s')), x)`
                        >> RW_TAC std_ss [FST,SND,PAIR])
          >> RW_TAC std_ss [] >> RW_TAC std_ss [FST, SND])
   >> POP_ORW
   >> `(PREIMAGE f {f s'} INTER PREIMAGE (\x. (H x,L x)) {FST s'} INTER (high CROSS low CROSS random)) =
       (PREIMAGE f {f s'} INTER ({FST (FST s')} CROSS {SND (FST s')} CROSS random))`
       by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING,
                          high_state_def, low_state_def, IN_CROSS]
           >> METIS_TAC [PAIR])
   >> POP_ORW
   >> `INJ SND ({FST (FST s')} CROSS {SND (FST s')} CROSS random)
           (IMAGE SND ({FST (FST s')} CROSS {SND (FST s')} CROSS random))`
        by (RW_TAC std_ss [INJ_DEF, IN_IMAGE, IN_SING, IN_CROSS] >> METIS_TAC [PAIR])
   >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, FINITE_CROSS, FINITE_SING, o_DEF]
   >> Q.ABBREV_TAC `c = & (CARD (PREIMAGE f {f s'} INTER PREIMAGE (\x. (H x,L x)) {FST s'} INTER
                        (high CROSS low CROSS
                        IMAGE SND ({FST (FST s')} CROSS {SND (FST s')} CROSS random))))`
   >> `({FST (FST s')} CROSS {SND (FST s')} CROSS random) =
       (PREIMAGE f {f s'} INTER
                PREIMAGE (\x. (H x,L x)) {FST s'} INTER
                (high CROSS low CROSS
                 IMAGE SND
                   ({FST (FST s')} CROSS {SND (FST s')} CROSS
                    random))) UNION
       (({FST (FST s')} CROSS {SND (FST s')} CROSS random) DIFF
        (PREIMAGE f {f s'} INTER
                PREIMAGE (\x. (H x,L x)) {FST s'} INTER
                (high CROSS low CROSS
                 IMAGE SND
                   ({FST (FST s')} CROSS {SND (FST s')} CROSS
                    random))))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_UNION, IN_DIFF, IN_CROSS, IN_SING,
                           IN_PREIMAGE, low_state_def, high_state_def, IN_IMAGE,
                           SND] >> METIS_TAC [])
   >> POP_ORW
   >> `DISJOINT (PREIMAGE f {f s'} INTER
                PREIMAGE (\x. (H x,L x)) {FST s'} INTER
                (high CROSS low CROSS
                 IMAGE SND
                   ({FST (FST s')} CROSS {SND (FST s')} CROSS
                    random)))
                (({FST (FST s')} CROSS {SND (FST s')} CROSS random) DIFF
        (PREIMAGE f {f s'} INTER
                PREIMAGE (\x. (H x,L x)) {FST s'} INTER
                (high CROSS low CROSS
                 IMAGE SND
                   ({FST (FST s')} CROSS {SND (FST s')} CROSS
                    random))))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_INTER, IN_DIFF] >> DECIDE_TAC)
   >> `FINITE (PREIMAGE f {f s'} INTER
          PREIMAGE (\x. (H x,L x)) {FST s'} INTER
          (high CROSS low CROSS
           IMAGE SND
             ({FST (FST s')} CROSS {SND (FST s')} CROSS random)))`
             by METIS_TAC [FINITE_CROSS, FINITE_SING, FINITE_INTER, FINITE_DIFF, IMAGE_FINITE]
   >> `FINITE ({FST (FST s')} CROSS {SND (FST s')} CROSS random DIFF
          PREIMAGE f {f s'} INTER
          PREIMAGE (\x. (H x,L x)) {FST s'} INTER
          (high CROSS low CROSS
           IMAGE SND
             ({FST (FST s')} CROSS {SND (FST s')} CROSS random)))`
             by METIS_TAC [FINITE_CROSS, FINITE_SING, FINITE_INTER, FINITE_DIFF, IMAGE_FINITE]
   >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `({FST (FST (s' :('a, 'b, 'c) prog_state))} CROSS
          {SND (FST s')} CROSS (random :'c state -> bool) DIFF
          PREIMAGE (f :('a, 'b, 'c, 'd) prog) {f s'} INTER
          PREIMAGE (\(x :('a, 'b, 'c) prog_state). (H x,L x))
            {FST s'} INTER
          ((high :'a state -> bool) CROSS (low :'b state -> bool) CROSS
           IMAGE (SND :('a, 'b, 'c, 'c) prog)
             ({FST (FST s')} CROSS {SND (FST s')} CROSS random)))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN {FST (FST s')} CROSS {SND (FST s')} CROSS random DIFF
        PREIMAGE f {f s'} INTER PREIMAGE (\x. (H x,L x)) {FST s'} INTER
        (high CROSS low CROSS
         IMAGE SND ({FST (FST s')} CROSS {SND (FST s')} CROSS random)) then
             (\x. (if f (FST s',SND x) = f s' then 1 else 0)) x else 0)) =
       (\x. 0)`
       by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_DIFF, IN_INTER, IN_CROSS, IN_SING, IN_PREIMAGE,
                          IN_IMAGE, SND, high_state_def, low_state_def]
           >> RW_TAC real_ss [] >> METIS_TAC [PAIR])
   >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
   >> NTAC 2 (POP_ASSUM (K ALL_TAC))
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(PREIMAGE (f :('a, 'b, 'c, 'd) prog)
            {f (s' :('a, 'b, 'c) prog_state)} INTER
          PREIMAGE (\(x :('a, 'b, 'c) prog_state). (H x,L x))
            {FST s'} INTER
          ((high :'a state -> bool) CROSS (low :'b state -> bool) CROSS
           IMAGE (SND :('a, 'b, 'c, 'c) prog)
             ({FST (FST s')} CROSS {SND (FST s')} CROSS
              (random :'c state -> bool))))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN PREIMAGE f {f s'} INTER PREIMAGE (\x. (H x,L x)) {FST s'} INTER
        (high CROSS low CROSS
         IMAGE SND ({FST (FST s')} CROSS {SND (FST s')} CROSS random)) then
            (\x. (if f (FST s',SND x) = f s' then 1 else 0)) x
            else 0)) =
       (\x. (if x IN PREIMAGE f {f s'} INTER PREIMAGE (\x. (H x,L x)) {FST s'} INTER
        (high CROSS low CROSS
         IMAGE SND ({FST (FST s')} CROSS {SND (FST s')} CROSS random)) then
            1 else 0))`
        by (ONCE_REWRITE_TAC [FUN_EQ_THM]
            >> RW_TAC std_ss [IN_INTER, IN_SING, IN_CROSS, IN_PREIMAGE,
                              IN_IMAGE, SND, high_state_def, low_state_def]
            >> RW_TAC std_ss []
            >> METIS_TAC [PAIR])
   >> POP_ORW
   >> Q.UNABBREV_TAC `c`
   >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_CARD]);

val unif_prog_space_visible_leakage_lemma2 = store_thm
  ("unif_prog_space_visible_leakage_lemma2",
   ``!high low random (f :('a, 'b, 'c, 'd) prog). FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (SIGMA (\x. (\(x,y,z).
                  joint_distribution (unif_prog_space high low random) f (\s. (H s,L s,R s)) {(x,y,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f (\s. (H s,L s,R s)) {(x,y,z)} *
                      & (CARD high * CARD low * CARD random))) x)
                  (IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s)) (high CROSS low CROSS random))=
            SIGMA (\x. (\(out,h,l,r).
                  ((1/(&(CARD high * CARD low * CARD random)))*
                   (if (f((h,l),r)=out) then 1 else 0)) *
                  lg (((1/(&(CARD high * CARD low * CARD random)))*
                   (if (f((h,l),r)=out) then 1 else 0)) *
                      & (CARD high * CARD low * CARD random))) x)
                  (IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s)) (high CROSS low CROSS random)))``,
   RW_TAC std_ss []
   >> `p_space (unif_prog_space high low random) =
       (high CROSS low CROSS random)`
       by RW_TAC std_ss [unif_prog_space_def, PSPACE]
   >> `FINITE (IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s)) (high CROSS low CROSS random))`
        by METIS_TAC [IMAGE_FINITE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE
           (\(s :('a, 'b, 'c) prog_state).
              ((f :('a, 'b, 'c, 'd) prog) s,FST (FST s),SND (FST s),
               SND s))
           ((high :'a state -> bool) CROSS (low :'b state -> bool) CROSS
            (random :'c state -> bool)))`) REAL_SUM_IMAGE_IN_IF]
   >> Suff `(\x. (if x IN IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s)) (high CROSS low CROSS random) then
                     (\x. (\(x,y,z). joint_distribution (unif_prog_space high low random) f
                          (\s. (H s,L s,R s)) {(x,y,z)} *
                lg (joint_distribution (unif_prog_space high low random) f (\s. (H s,L s,R s)) {(x,y,z)} *
                   & (CARD high * CARD low * CARD random))) x) x else 0)) =
            (\x. (if x IN IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s)) (high CROSS low CROSS random) then
                      (\x. (\(out,h,l,r).
                           1 / & (CARD high * CARD low * CARD random) *
              (if f ((h,l),r) = out then 1 else 0) *
                    lg (1 / & (CARD high * CARD low * CARD random) *
                    (if f ((h,l),r) = out then 1 else 0) * & (CARD high * CARD low * CARD random))) x) x else 0))`
   >- RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_IMAGE, IN_CROSS]
   >> RW_TAC std_ss []
   >> rename1 `FST (FST s') IN high`
   >> `FST s' = (FST(FST s'),SND(FST s'))` by RW_TAC std_ss [PAIR]
   >> POP_ORW >> RW_TAC real_ss []
   >> Suff `joint_distribution (unif_prog_space high low random) f (\s. (H s,L s,R s)) {(f s',FST (FST s'),SND (FST s'),SND s')} =
                1 / & (CARD high * CARD low * CARD random)`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [joint_distribution_def, unif_prog_space_def, unif_prog_dist_def, PROB,
                     FINITE_CROSS, CARD_CROSS]
   >>  `(\s. (if s IN high CROSS low CROSS random then
                     1 / & (CARD high * CARD low * CARD random) else 0)) =
        (\s. (1 / & (CARD high * CARD low * CARD random)) *
                     (\s. if s IN high CROSS low CROSS random then 1 else 0) s)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [])
   >> POP_ORW
   >> RW_TAC std_ss [REAL_SUM_IMAGE_CMUL, FINITE_CROSS, FINITE_INTER]
   >> `PREIMAGE (\s. (f s,H s,L s,R s))
     {(f s',FST (FST s'),SND (FST s'),SND s')} =
       PREIMAGE f {f s'} INTER
        PREIMAGE (\s. (H s,L s,R s))
        {(FST (FST s'),SND (FST s'),SND s')}`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_SING, IN_PREIMAGE] >> METIS_TAC [])
   >> POP_ORW
   >> Q.ABBREV_TAC `foo = 1 / & (CARD high * CARD low * CARD random) *
        SIGMA (\s. (if s IN high CROSS low CROSS random then 1 else 0))
          (PREIMAGE f {f s'} INTER
        PREIMAGE (\s. (H s,L s,R s))
        {(FST (FST s'),SND (FST s'),SND s')} INTER
        (high CROSS low CROSS random))`
   >> `1 / & (CARD high * CARD low * CARD random) = 1 / & (CARD high * CARD low * CARD random) * 1`
        by RW_TAC real_ss []
   >> POP_ORW >> Q.UNABBREV_TAC `foo`
   >> RW_TAC std_ss [REAL_EQ_LMUL]
   >> Cases_on `(1 / & (CARD high * CARD low * CARD random) = 0)`
   >> RW_TAC std_ss []
   >> `(PREIMAGE f {f s'} INTER PREIMAGE (\s. (H s,L s,R s)) {(FST (FST s'),SND (FST s'),SND s')} INTER
        (high CROSS low CROSS random)) = {s'}`
        by (ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [IN_INTER, IN_SING, IN_PREIMAGE, high_state_def,
                           low_state_def, random_state_def, IN_CROSS]
            >> METIS_TAC [PAIR, FST, SND])
   >> RW_TAC std_ss [REAL_SUM_IMAGE_SING, IN_CROSS]);

val unif_prog_space_leakage_lemma3 = store_thm
  ("unif_prog_space_leakage_lemma3",
   ``!high low random (f :('a, 'b, 'c, 'd) prog). FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (SIGMA (\x. (\(x,z).
                  joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f L {(x,z)} *
                     & (CARD low))) x)
                  (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random))=
            (1/(&(CARD high * CARD low * CARD random)))*
            SIGMA (\x. (\(out,l).
                  ((SIGMA (\(h,r). if (f((h,l),r)=out) then 1 else 0)
                                   (high CROSS random))) *
                  lg (((1/(&(CARD high * CARD random)))*
                            (SIGMA (\(h,r). if (f((h,l),r)=out) then 1 else 0)
                                   (high CROSS random))))) x)
                  (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)))``,
   RW_TAC std_ss [unif_prog_space_leakage_lemma1]
   >> `1 / & (CARD high * CARD low * CARD random) *
      SIGMA (\x.
     (\(out,l).
        SIGMA (\(h,r). (if f ((h,l),r) = out then 1 else 0))
          (high CROSS random) *
        lg
          (1 / & (CARD high * CARD random) *
           SIGMA (\(h,r). (if f ((h,l),r) = out then 1 else 0))
             (high CROSS random))) x)
             (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random)) =
        SIGMA (\x. 1 / & (CARD high * CARD low * CARD random) *
     (\(out,l).
        SIGMA (\(h,r). (if f ((h,l),r) = out then 1 else 0))
          (high CROSS random) *
        lg
          (1 / & (CARD high * CARD random) *
           SIGMA (\(h,r). (if f ((h,l),r) = out then 1 else 0))
             (high CROSS random))) x)
             (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random))`
   by RW_TAC std_ss [IMAGE_FINITE, FINITE_CROSS, GSYM REAL_SUM_IMAGE_CMUL]
   >> POP_ORW
   >> Suff `(\x.
     (\(x,z).
        1 / & (CARD high * CARD low * CARD random) *
        SIGMA (\(h,r). (if f ((h,z),r) = x then 1 else 0))
          (high CROSS random) *
        lg
          (1 / & (CARD high * CARD low * CARD random) *
           SIGMA (\(h,r). (if f ((h,z),r) = x then 1 else 0))
             (high CROSS random) * & (CARD low))) x) =
      (\x.
     1 / & (CARD high * CARD low * CARD random) *
     (\(out,l).
        SIGMA (\(h,r). (if f ((h,l),r) = out then 1 else 0))
          (high CROSS random) *
        lg
          (1 / & (CARD high * CARD random) *
           SIGMA (\(h,r). (if f ((h,l),r) = out then 1 else 0))
             (high CROSS random))) x)`
   >- RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss []
   >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR]
   >> POP_ORW >> RW_TAC std_ss []
   >> Suff `1 / & (CARD high * CARD low * CARD random) *
               SIGMA (\(h,r). (if f ((h,SND x),r) = FST x then 1 else 0))
                     (high CROSS random) * & (CARD low) =
             1 / & (CARD high * CARD random) *
             SIGMA (\(h,r). (if f ((h,SND x),r) = FST x then 1 else 0))
                   (high CROSS random)`
   >- RW_TAC std_ss [REAL_MUL_ASSOC]
   >> Suff `1 / & (CARD high * CARD random) =
            & (CARD low) * (1 / & (CARD high * CARD low * CARD random))`
   >- (RW_TAC std_ss [] >> REAL_ARITH_TAC)
   >> RW_TAC real_ss [real_div]
   >> RW_TAC std_ss [GSYM REAL_MUL]
   >> `& (CARD high) * & (CARD low) * & (CARD random) =
       (& (CARD high) * & (CARD random)) * & (CARD low)`
       by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
   >> POP_ORW
   >> `inv (& (CARD high) * & (CARD random) * & (CARD low)) =
       inv (& (CARD high) * & (CARD random)) * inv (& (CARD low))`
       by (MATCH_MP_TAC REAL_INV_MUL
           >> RW_TAC real_ss [CARD_EQ_0, REAL_ENTIRE]
           >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
           >> FULL_SIMP_TAC std_ss [CROSS_EMPTY])
   >> POP_ORW
   >> `& (CARD low) * (inv (& (CARD high) * & (CARD random)) * inv (& (CARD low))) =
       ((inv (& (CARD low))) * ((& (CARD low)))) * (inv (& (CARD high) * & (CARD random)))`
       by REAL_ARITH_TAC
   >> POP_ORW
   >> Suff `inv (& (CARD low)) * & (CARD low) = 1` >- RW_TAC real_ss []
   >> MATCH_MP_TAC REAL_MUL_LINV
   >> RW_TAC real_ss [CARD_EQ_0]
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> FULL_SIMP_TAC std_ss [CROSS_EMPTY]);

val unif_prog_space_visible_leakage_lemma3 = store_thm
  ("unif_prog_space_visible_leakage_lemma3",
   ``!high low random (f :('a, 'b, 'c, 'd) prog). FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (SIGMA
        (\x.
           (\(x,z).
              joint_distribution (unif_prog_space high low random) f
                (\s. (L s,R s)) {(x,z)} *
              lg
                (joint_distribution (unif_prog_space high low random) f
                   (\s. (L s,R s)) {(x,z)} *
                 & (CARD low * CARD random))) x)
        (IMAGE (\s. (f s,SND (FST s),SND s))
           (high CROSS low CROSS random)) =
            (1/(&(CARD high * CARD low * CARD random)))*
            SIGMA (\x. (\(out,(l,r)).
                  ((SIGMA (\h. if (f((h,l),r)=out) then 1 else 0) high)) *
                  lg (((1/(&(CARD high)))*
                            (SIGMA (\h. if (f((h,l),r)=out) then 1 else 0) high)))) x)
                  (IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random)))``,
   RW_TAC std_ss [unif_prog_space_visible_leakage_lemma1]
   >> `1 / & (CARD high * CARD low * CARD random) *
      SIGMA
  (\x.
     (\(out,l,r).
        SIGMA (\h. (if f ((h,l),r) = out then 1 else 0)) high *
        lg
          (1 / & (CARD high) *
           SIGMA (\h. (if f ((h,l),r) = out then 1 else 0)) high)) x)
  (IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random)) =
        SIGMA
  (\x. 1 / & (CARD high * CARD low * CARD random) *
     (\(out,l,r).
        SIGMA (\h. (if f ((h,l),r) = out then 1 else 0)) high *
        lg
          (1 / & (CARD high) *
           SIGMA (\h. (if f ((h,l),r) = out then 1 else 0)) high)) x)
  (IMAGE (\s. (f s,SND (FST s),SND s)) (high CROSS low CROSS random))`
   by RW_TAC std_ss [IMAGE_FINITE, FINITE_CROSS, GSYM REAL_SUM_IMAGE_CMUL]
   >> POP_ORW
   >> Suff `(\x.
     (\(x,z).
        1 / & (CARD high * CARD low * CARD random) *
        SIGMA (\h. (if f ((h,FST z),SND z) = x then 1 else 0)) high *
        lg
          (1 / & (CARD high * CARD low * CARD random) *
           SIGMA (\h. (if f ((h,FST z),SND z) = x then 1 else 0)) high *
           & (CARD low * CARD random))) x) =
      (\x.
     1 / & (CARD high * CARD low * CARD random) *
     (\(out,l,r).
        SIGMA (\h. (if f ((h,l),r) = out then 1 else 0)) high *
        lg
          (1 / & (CARD high) *
           SIGMA (\h. (if f ((h,l),r) = out then 1 else 0)) high)) x)`
   >- RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss []
   >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR]
   >> POP_ORW >> RW_TAC std_ss []
   >> `SND x = (FST (SND x), SND (SND x))` by RW_TAC std_ss [PAIR]
   >> POP_ORW >> RW_TAC std_ss []
   >> Suff `1 / & (CARD high * CARD low * CARD random) *
   SIGMA
     (\h. (if f ((h,FST (SND x)),SND (SND x)) = FST x then 1 else 0))
     high * & (CARD low * CARD random) =
             1 / & (CARD high) *
    SIGMA
      (\h. (if f ((h,FST (SND x)),SND (SND x)) = FST x then 1 else 0))
      high`
   >- RW_TAC std_ss [REAL_MUL_ASSOC]
   >> Suff `1 / & (CARD high) =
            & (CARD low * CARD random) * (1 / & (CARD high * CARD low * CARD random))`
   >- (RW_TAC std_ss [] >> REAL_ARITH_TAC)
   >> RW_TAC real_ss [real_div]
   >> RW_TAC std_ss [GSYM REAL_MUL]
   >> `& (CARD high) * & (CARD low) * & (CARD random) =
       & (CARD high) * (& (CARD low) * & (CARD random))`
       by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
   >> POP_ORW
   >> `inv (& (CARD high) * (& (CARD low) * & (CARD random))) =
       inv (& (CARD high)) * inv(& (CARD low) * & (CARD random))`
       by (MATCH_MP_TAC REAL_INV_MUL
           >> RW_TAC real_ss [CARD_EQ_0, REAL_ENTIRE]
           >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
           >> FULL_SIMP_TAC std_ss [CROSS_EMPTY])
   >> POP_ORW
   >> `& (CARD low) * & (CARD random) *
        (inv (& (CARD high)) * inv (& (CARD low) * & (CARD random))) =
       inv (& (CARD high)) * (inv (& (CARD low) * & (CARD random) ) * (& (CARD low) * & (CARD random)) )`
       by REAL_ARITH_TAC
   >> POP_ORW
   >> Suff `(inv (& (CARD low) * & (CARD random)) *
        (& (CARD low) * & (CARD random))) = 1` >- RW_TAC real_ss []
   >> `inv (& (CARD low) * & (CARD random)) * & (CARD low) * & (CARD random) =
       (inv (& (CARD low) * & (CARD random))) * (& (CARD low) * & (CARD random))`
        by REAL_ARITH_TAC
   >> POP_ORW
   >> MATCH_MP_TAC REAL_MUL_LINV
   >> RW_TAC real_ss [CARD_EQ_0]
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> FULL_SIMP_TAC std_ss [CROSS_EMPTY]);

val unif_prog_space_leakage_lemma4 = store_thm
  ("unif_prog_space_leakage_lemma4",
   ``!high low random (f :('a, 'b, 'c, 'd) prog). FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (SIGMA (\x. (\(x,y,z).
                  joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
                  lg (joint_distribution (unif_prog_space high low random) f (\x. (H x,L x)) {(x,y,z)} *
                      & (CARD high * CARD low))) x)
                  (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random))=
            (1/(&(CARD high * CARD low * CARD random)))*
            SIGMA (\x. (\(out,h,l).
                  ((SIGMA (\r. if (f((h,l),r)=out) then 1 else 0) random)) *
                  lg (((1/(&(CARD random)))*
                   (SIGMA (\r. if (f((h,l),r)=out) then 1 else 0) random)))) x)
                  (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)))``,
   RW_TAC std_ss [unif_prog_space_leakage_lemma2]
   >> `1 / & (CARD high * CARD low * CARD random) *
      SIGMA
      (\x. (\(out,h,l).
        SIGMA (\r. (if f ((h,l),r) = out then 1 else 0)) random *
        lg
          (1 / & (CARD random) *
           SIGMA (\r. (if f ((h,l),r) = out then 1 else 0)) random)) x)
           (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)) =
        SIGMA
        (\x. (1 / & (CARD high * CARD low * CARD random)) * (\(out,h,l).
        SIGMA (\r. (if f ((h,l),r) = out then 1 else 0)) random *
        lg
          (1 / & (CARD random) *
           SIGMA (\r. (if f ((h,l),r) = out then 1 else 0)) random)) x)
  (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random))`
   by RW_TAC std_ss [IMAGE_FINITE, FINITE_CROSS, GSYM REAL_SUM_IMAGE_CMUL]
   >> POP_ORW
   >> Suff `(\x.
     (\(out,h,l).
        1 / & (CARD high * CARD low * CARD random) *
        SIGMA (\r. (if f ((h,l),r) = out then 1 else 0)) random *
        lg
          (1 / & (CARD high * CARD low * CARD random) *
           SIGMA (\r. (if f ((h,l),r) = out then 1 else 0)) random *
           & (CARD high * CARD low))) x) =
      (\x.
     1 / & (CARD high * CARD low * CARD random) *
     (\(out,h,l).
        SIGMA (\r. (if f ((h,l),r) = out then 1 else 0)) random *
        lg
          (1 / & (CARD random) *
           SIGMA (\r. (if f ((h,l),r) = out then 1 else 0)) random)) x)`
   >- RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss []
   >> `x = (FST x, FST(SND x), SND(SND x))` by RW_TAC std_ss [PAIR]
   >> POP_ORW >> RW_TAC std_ss []
   >> Suff `1 / & (CARD high * CARD low * CARD random) *
      SIGMA (\r. (if f (SND x,r) = FST x then 1 else 0)) random *
      & (CARD high * CARD low) =
      1 / & (CARD random) *
    SIGMA (\r. (if f (SND x,r) = FST x then 1 else 0)) random`
   >- RW_TAC std_ss [REAL_MUL_ASSOC]
   >> Suff `1 / & (CARD random) =
            & (CARD high * CARD low) * (1 / & (CARD high * CARD low * CARD random))`
   >- (RW_TAC std_ss [] >> REAL_ARITH_TAC)
   >> RW_TAC real_ss [real_div]
   >> RW_TAC std_ss [GSYM REAL_MUL]
   >> `& (CARD high) * & (CARD low) * & (CARD random) =
       (& (CARD high) * & (CARD low)) * & (CARD random)`
       by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
   >> POP_ORW
   >> `inv (& (CARD high) * & (CARD low) * & (CARD random)) =
       inv (& (CARD high) * & (CARD low)) * inv (& (CARD random))`
       by (MATCH_MP_TAC REAL_INV_MUL
           >> RW_TAC real_ss [CARD_EQ_0, REAL_ENTIRE]
           >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
           >> FULL_SIMP_TAC std_ss [CROSS_EMPTY])
   >> POP_ORW
   >> Suff `(& (CARD high) * & (CARD low)) * inv (& (CARD high) * & (CARD low)) = 1`
   >- METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM, REAL_MUL_LID]
   >> MATCH_MP_TAC REAL_MUL_RINV
   >> RW_TAC real_ss [CARD_EQ_0]
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> FULL_SIMP_TAC std_ss [CROSS_EMPTY]);

val unif_prog_space_visible_leakage_lemma4 = store_thm
  ("unif_prog_space_visible_leakage_lemma4",
   ``!high low random (f :('a, 'b, 'c, 'd) prog). FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (SIGMA
        (\x.
           (\(x,y,z).
              joint_distribution (unif_prog_space high low random) f
                (\s. (H s,L s,R s)) {(x,y,z)} *
              lg
                (joint_distribution (unif_prog_space high low random) f
                   (\s. (H s,L s,R s)) {(x,y,z)} *
                 & (CARD high * CARD low * CARD random))) x)
        (IMAGE (\s. (f s,FST (FST s),SND (FST s),SND s))
           (high CROSS low CROSS random)) =
            0)``,
   RW_TAC std_ss [unif_prog_space_visible_leakage_lemma2]
   >> Suff `(\x.
     (\(out,h,l,r).
        1 / & (CARD high * CARD low * CARD random) *
        (if f ((h,l),r) = out then 1 else 0) *
        lg
          (1 / & (CARD high * CARD low * CARD random) *
           (if f ((h,l),r) = out then 1 else 0) *
           & (CARD high * CARD low * CARD random))) x) = (\x. 0)`
   >- RW_TAC std_ss [REAL_SUM_IMAGE_0, IMAGE_FINITE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss []
   >> `x = (FST x, (FST(SND x), (FST(SND(SND x)),SND(SND(SND x)))))` by RW_TAC std_ss [PAIR]
   >> POP_ORW >> RW_TAC real_ss [real_div]
   >> Suff `inv (& (CARD high * CARD low * CARD random)) *
                & (CARD high * CARD low * CARD random) = 1`
   >- RW_TAC real_ss [lg_1]
   >> MATCH_MP_TAC REAL_MUL_LINV
   >> RW_TAC real_ss [CARD_EQ_0]
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> FULL_SIMP_TAC std_ss [CROSS_EMPTY]);


val unif_prog_space_leakage_computation_reduce = store_thm
  ("unif_prog_space_leakage_computation_reduce",
   ``!high low random f. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (leakage (unif_prog_space high low random) f =
            (1/(&(CARD high * CARD low * CARD random)))*
            (SIGMA (\x. (\(out,h,l).
                  ((SIGMA (\r. if (f((h,l),r)=out) then 1 else 0) random)) *
                  lg (((1/(&(CARD random)))*
                   (SIGMA (\r. if (f((h,l),r)=out) then 1 else 0) random)))) x)
                  (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)) -
            SIGMA (\x. (\(out,l).
                  ((SIGMA (\(h,r). if (f((h,l),r)=out) then 1 else 0)
                                   (high CROSS random))) *
                  lg (((1/(&(CARD high * CARD random)))*
                            (SIGMA (\(h,r). if (f((h,l),r)=out) then 1 else 0)
                                   (high CROSS random))))) x)
                  (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random))))``,
   RW_TAC std_ss [unif_prog_space_leakage_reduce, unif_prog_space_leakage_lemma3,
                  unif_prog_space_leakage_lemma4, REAL_SUB_LDISTRIB]);


val unif_prog_space_visible_leakage_computation_reduce = store_thm
  ("unif_prog_space_visible_leakage_computation_reduce",
   ``!high low random f. FINITE high /\ FINITE low /\ FINITE random /\
           ~((high CROSS low) CROSS random={}) ==>
           (visible_leakage (unif_prog_space high low random) f =
            ~(1 / & (CARD high * CARD low * CARD random) *
      SIGMA
        (\x.
           (\(out,l,r).
              SIGMA (\h. (if f ((h,l),r) = out then 1 else 0)) high *
              lg
                (1 / & (CARD high) *
                 SIGMA (\h. (if f ((h,l),r) = out then 1 else 0)) high))
             x)
        (IMAGE (\s. (f s,SND (FST s),SND s))
           (high CROSS low CROSS random))))``,
   RW_TAC real_ss [unif_prog_space_visible_leakage_reduce, unif_prog_space_visible_leakage_lemma3,
                  unif_prog_space_visible_leakage_lemma4, REAL_SUB_LDISTRIB, REAL_SUB_LZERO]);


Definition REAL_SUM_def:
  (REAL_SUM [] = 0:real) /\
  (REAL_SUM (x::l) = x + REAL_SUM l)
End

Theorem ALL_DISTINCT_imp_REAL_SUM_IMAGE_of_LIST_TO_SET_eq_REAL_SUM:
   !l. ALL_DISTINCT l ==>
       (REAL_SUM_IMAGE f (LIST_TO_SET l) = REAL_SUM (MAP f l))
Proof
   Induct >> simp[REAL_SUM_def, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT]
QED

Theorem unif_prog_space_leakage_LIST_TO_SET_computation_reduce:
  !high low random f.
    ALL_DISTINCT high /\ ALL_DISTINCT low /\
    ALL_DISTINCT random /\ ~(high = []) /\ ~(low = []) /\ ~(random = []) ==>
    (leakage (unif_prog_space (set high) (set low) (set random)) f =
     (1/(&(LENGTH high * LENGTH low * LENGTH random)))*
     ((REAL_SUM (MAP (λx.
                       (λ(out,h,l). (\s. s * lg ((1/(&(LENGTH random)))*s))
                                    (REAL_SUM (MAP (\r. if (f((h,l),r)=out) then 1
                                                        else 0) random))) x)
                 (nub
                  (MAP (\s. (f s,FST s))
                   (LIST_COMBS (LIST_COMBS high low) random))))) -
      (REAL_SUM (MAP (\x. (λ(out,l).
                            (\s. s * lg ((1/(&(LENGTH high * LENGTH random)))*s))
                            (REAL_SUM (MAP (λ(h,r). if (f((h,l),r)=out) then 1
                                                    else 0)
                                       (LIST_COMBS high random)))) x)
                 (nub
                  (MAP (\s. (f s,SND (FST s)))
                   (LIST_COMBS (LIST_COMBS high low) random)))))))
Proof
   REPEAT STRIP_TAC
   >> qspecl_then [`set high`,`set low`,`set random`,`f`] mp_tac
                  unif_prog_space_leakage_computation_reduce
   >> SIMP_TAC std_ss [FINITE_LIST_TO_SET, CROSS_LIST_TO_SET]
   >> `~(set (LIST_COMBS (LIST_COMBS high low) random) = {})`
      by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY]
          >> Cases_on `high` >> Cases_on `low` >> Cases_on `random`
          >> FULL_SIMP_TAC list_ss [LIST_COMBS_def, MAP]
          >> METIS_TAC [])
   >> RW_TAC std_ss [CARD_LIST_TO_SET, all_distinct_nub_id, REAL_EQ_LMUL]
   >> POP_ASSUM (K ALL_TAC)
   >> Cases_on `(1 / & (LENGTH high * LENGTH low * LENGTH random) = 0)`
   >> RW_TAC real_ss [IMAGE_LIST_TO_SET]
   >> ‘set (MAP (\s. (f s,SND (FST s)))
            (LIST_COMBS (LIST_COMBS high low) random)) =
       set (nub
             (MAP (\s. (f s,SND (FST s)))
              (LIST_COMBS (LIST_COMBS high low) random)))’
        by RW_TAC std_ss [nub_set]
   >> POP_ORW
   >> ‘set (MAP (\s. (f s,FST s))
            (LIST_COMBS (LIST_COMBS high low) random)) =
       set (nub
            (MAP (\s. (f s,FST s))
             (LIST_COMBS (LIST_COMBS high low) random)))’
        by RW_TAC std_ss [nub_set]
   >> POP_ORW
   >> RW_TAC std_ss [ALL_DISTINCT_imp_REAL_SUM_IMAGE_of_LIST_TO_SET_eq_REAL_SUM,
                     ALL_DISTINCT_LIST_COMBS, all_distinct_nub,
                     CARD_LIST_TO_SET_EQN, all_distinct_nub_id, REAL_MUL_LZERO]
QED


Theorem unif_prog_space_visible_leakage_LIST_TO_SET_computation_reduce:
  !high low random f.
    ALL_DISTINCT high /\ ALL_DISTINCT low /\ ALL_DISTINCT random /\
    high ≠ [] /\ low ≠ [] /\ random ≠ [] ==>
    (visible_leakage (unif_prog_space (set high) (set low) (set random)) f =
     -(1/(&(LENGTH high * LENGTH low * LENGTH random)))*
     ((REAL_SUM (MAP (\x. (λ(out,l,r).
                            (\s. s * lg ((1/(&(LENGTH high)))*s))
                            (REAL_SUM (MAP (\h. if (f((h,l),r)=out) then 1 else 0)
                                       high))) x)
                 (nub
                  (MAP (\s. (f s,SND (FST s),SND s))
                   (LIST_COMBS (LIST_COMBS high low) random)))))))
Proof
   REPEAT STRIP_TAC
   >> (MP_TAC o Q.SPECL [`set high`,`set low`,`LIST_TO_SET random`,`f`])
      unif_prog_space_visible_leakage_computation_reduce
   >> SIMP_TAC std_ss [FINITE_LIST_TO_SET, CROSS_LIST_TO_SET]
   >> `~(set (LIST_COMBS (LIST_COMBS high low) random) = {})`
      by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY]
          >> Cases_on `high` >> Cases_on `low` >> Cases_on `random`
          >> FULL_SIMP_TAC list_ss [LIST_COMBS_def, MAP]
          >> METIS_TAC [])
   >> RW_TAC std_ss [CARD_LIST_TO_SET, all_distinct_nub_id, REAL_EQ_LMUL,
                     GSYM REAL_MUL_LNEG,
                     REAL_NEG_EQ0, GSYM REAL_INV_1OVER, REAL_INV_EQ_0]
   >> POP_ASSUM (K ALL_TAC)
   >> Cases_on `(& (LENGTH high * LENGTH low * LENGTH random) = 0)`
   >> ASM_REWRITE_TAC []
   >- gs[]
   >> RW_TAC real_ss [IMAGE_LIST_TO_SET, CARD_LIST_TO_SET_EQN,
                      all_distinct_nub_id]
   >> simp[all_distinct_nub_id,
           ALL_DISTINCT_imp_REAL_SUM_IMAGE_of_LIST_TO_SET_eq_REAL_SUM]
   >> qmatch_abbrev_tac ‘_ = REAL_SUM (MAP ff (nub l))’
   >> ‘set l = set (nub l)’ by RW_TAC std_ss [nub_set]
   >> POP_ORW
   >> simp[ALL_DISTINCT_imp_REAL_SUM_IMAGE_of_LIST_TO_SET_eq_REAL_SUM]
QED

Theorem unif_prog_space_leakage_computation_reduce_COMPUTE:
  !high low random f.
    FINITE high /\ FINITE low /\ FINITE random /\
    ((high CROSS low) CROSS random <> {}) ==>
    (leakage (unif_prog_space high low random) f =
     (1/(&(CARD high * CARD low * CARD random)))*
     (SIGMA (λ(out,h,l). (\x. x * lg (((1/(&(CARD random)))* x)))
                         (SIGMA (\r. if (f((h,l),r)=out) then 1 else 0) random))
      (IMAGE (\s. (f s,FST s)) (high CROSS low CROSS random)) -
      SIGMA (λ(out,l). (\x. x * lg (((1/(&(CARD high * CARD random)))* x)))
                       (SIGMA (λ(h,r). if (f((h,l),r)=out) then 1 else 0)
                        (high CROSS random)))
      (IMAGE (\s. (f s,SND (FST s))) (high CROSS low CROSS random))))
Proof
   METIS_TAC [unif_prog_space_leakage_computation_reduce]
QED


val _ = export_theory ();
