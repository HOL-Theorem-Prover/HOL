open HolKernel Parse boolLib bossLib;

open arithmeticTheory pred_setTheory simpLib res_quanTheory
     listTheory rich_listTheory pairTheory combinTheory
     realTheory realLib seqTheory state_transformerTheory numSyntax;

open extra_listTheory hurdUtils extra_realTheory extra_boolTheory
     ho_proverTools extra_numTheory;

open util_probTheory sigma_algebraTheory real_measureTheory real_probabilityTheory;
open subtypeTheory extra_pred_setTheory extra_pred_setTools;
open prob_algebraTheory prob_canonTools prob_canonTheory;
open sequenceTheory sequenceTools;

val _ = new_theory "prob";
val _ = ParseExtras.temp_loose_equality()

val EXISTS_DEF = boolTheory.EXISTS_DEF;
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);
val Strip = REPEAT STRIP_TAC;

val INTER_ASSOC = GSYM INTER_ASSOC
val UNION_ASSOC = GSYM UNION_ASSOC

(* ------------------------------------------------------------------------- *)
(* The definition of probability.                                            *)
(* ------------------------------------------------------------------------- *)

local
  val thm =  prove
    (``?bern.
         prob_space bern /\
         ((p_space bern, events bern) = (sigma (space prob_algebra) (subsets prob_algebra))) /\
         (!s. s IN (subsets prob_algebra) ==> (prob bern s = prob_measure s))``,
     MP_TAC (Q.ISPEC `(space prob_algebra, subsets prob_algebra, prob_measure)` CARATHEODORY) \\
     ASSUME_TAC SPACE_SUBSETS_PROB_ALGEBRA \\
     RW_TAC std_ss [PROB_ALGEBRA_ALGEBRA, PROB_MEASURE_POSITIVE,
                    PROB_MEASURE_COUNTABLY_ADDITIVE, measurable_sets_def,
                    measure_def, m_space_def] \\
     Q.EXISTS_TAC `m` \\
     RW_TAC std_ss [prob_space_def, prob_def, events_def, p_space_def] \\
     ONCE_REWRITE_TAC [GSYM PROB_MEASURE_BASIC] \\
     Know `m_space m = UNIV`
     >- ( Q.PAT_X_ASSUM `(m_space m, measurable_sets m) = P` MP_TAC \\
          RW_TAC std_ss [sigma_def, prob_algebra_def, space_def, PAIR_EQ] ) \\
     Rewr \\
     Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC \\
     REWRITE_TAC [PROB_ALGEBRA_UNIV]);
in
  val bern_def = new_specification ("bern_def", ["bern"], thm);
end;

val prob_while_cut_def = Define
  `(prob_while_cut c b 0 a = UNIT a) /\
   (prob_while_cut c b (SUC n) a =
    if c a then BIND (b a) (prob_while_cut c b n) else UNIT a)`;

val many_def = Define `many f n = prob_while_cut I (K f) n T`;

val prefix_cover_def = Define
  `prefix_cover c =
   (!l1 l2. l1 IN c /\ l2 IN c /\ ~(l1 = l2) ==> ~IS_PREFIX l1 l2) /\
   (prob bern (BIGUNION (IMAGE prefix_set c)) = 1)`;

val indep_fn_def = Define
  `indep_fn =
   {f |
    countable (range (FST o f)) /\
    (FST o f) IN measurable (p_space bern, events bern) (UNIV, UNIV) /\
    (SND o f) IN measurable (p_space bern, events bern) (p_space bern, events bern) /\
    ?c.
      prefix_cover c /\
      !l s.
        l IN c /\ s IN prefix_set l ==>
        (f s = (FST (f (prefix_seq l)), sdrop (LENGTH l) s))}`;

val probably_bern_def = new_binder_definition
  ("probably_bern_def",
   ``!e. $!* e = probably bern {s | e s}``);

val possibly_bern_def = new_binder_definition
  ("possibly_bern_def",
   ``!e. $?* e = possibly bern {s | e s}``);

val append_sets_fn_def = Define
  `append_sets_fn a b = {l | ?x y. x IN a /\ y IN b x /\ (l = APPEND x y)}`;

val prefix_cover_level_def = Define
  `(prefix_cover_level c b ca a 0 = if c a then {} else {[]}) /\
   (prefix_cover_level c b ca a (SUC n) =
    if c a then append_sets_fn (ca a) (\l. prefix_cover_level c b ca (b a l) n)
    else {})`;

val prefix_cover_star_def = Define
  `prefix_cover_star c b ca a =
   BIGUNION (IMAGE (prefix_cover_level c b ca a) UNIV)`;

val prob_while_terminates_def = Define
  `prob_while_terminates c b =
   !a. !* s. ?n. ~c (FST (FUNPOW (UNCURRY b) n (a, s)))`;

Definition prob_while_witness_def:
  prob_while_witness c b a s = case OWHILE (c o FST) (UNCURRY b) (a,s) of
                                 NONE => ARB
                               | SOME x => x
End

val nonevent_def = Define
   `nonevent = IMAGE (\x. @y. eventually (x :num->'a) (y :num->'a)) UNIV`;

val nonevent_seq_def = Define
  `(nonevent_seq 0 = nonevent) /\
   (nonevent_seq (SUC n) =
    IMAGE stl (nonevent_seq n UNION (nonevent_seq n o mirror)))`;

val coin_flip_def = Define
  `coin_flip a b = BIND sdest (\x. if x then a else b)`;

val prob_cost_def = Define
  `prob_cost f b (a, n) = BIND (b a) (\a'. UNIT (a', f n : num))`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. prefix_set l IN events bern                                            *)
(* 2. prob bern (prefix_set l) = (1 / 2) pow (LENGTH l)                      *)
(* 3. countable c ==> (prob bern c = 0)                                      *)
(* 4. stl IN measurable (events bern) (events bern)                          *)
(* 5. (s o stl) IN (events bern) = s IN (events bern)                        *)
(* 6. s IN (events bern) ==> (prob (s o stl) = prob b)                       *)
(* 7. SDEST IN indep_function bern                                           *)
(* 8. UNIT x IN indep_function bern                                          *)
(* 9. ?f g. f IN indep_function bern /\ (!x. g x IN indep_function bern) /\  *)
(*          ~(BIND f g IN indep_function bern)                               *)
(* 10. indep_fn SUBSET indep_function bern                                   *)
(* 11. indep_fn PSUBSET indep_function bern                    ('a |-> bool) *)
(* 12. SDEST IN indep_fn                                                     *)
(* 13. UNIT x IN indep_fn                                                    *)
(* 14. f IN indep_fn /\ (!x. g x IN indep_fn) ==> BIND f g IN indep_fn       *)
(* ------------------------------------------------------------------------- *)

val PROB_SPACE_BERN = store_thm
  ("PROB_SPACE_BERN", ``prob_space bern``,
   PROVE_TAC [bern_def]);

val MEASURE_SPACE_BERN = store_thm
  ("MEASURE_SPACE_BERN", ``measure_space bern``,
   MP_TAC PROB_SPACE_BERN
   >> RW_TAC std_ss [prob_space_def]);

val EVENTS_BERN = store_thm
  ("EVENTS_BERN",
  ``events bern = subsets (sigma (space prob_algebra) (subsets prob_algebra))``,
   MP_TAC bern_def
   >> Strip
   >> Q.PAT_X_ASSUM `(p_space bern, events bern) = P` (REWRITE_TAC o wrap o SYM)
   >> REWRITE_TAC [subsets_def]);

val SPACE_BERN = store_thm
  ("SPACE_BERN", ``p_space bern = space prob_algebra``,
   MP_TAC bern_def
   >> REWRITE_TAC [sigma_def]
   >> RW_TAC std_ss [PAIR_EQ]);

(* |- p_space bern = 𝕌(:num -> bool) *)
val SPACE_BERN_UNIV = save_thm
  ("SPACE_BERN_UNIV", REWRITE_RULE [SPACE_PROB_ALGEBRA] SPACE_BERN);

val SIGMA_ALGEBRA_BERN = store_thm
  ("SIGMA_ALGEBRA_BERN", ``sigma_algebra (p_space bern, events bern)``,
   `subset_class (space prob_algebra) (subsets prob_algebra)`
        by REWRITE_TAC [subset_class_def, SPACE_PROB_ALGEBRA, SUBSET_UNIV]
   >> RW_TAC std_ss [bern_def, SIGMA_ALGEBRA_SIGMA]);

val SIGMA_PROB_ALGEBRA = store_thm
  ("SIGMA_PROB_ALGEBRA", ``sigma_algebra (sigma (space prob_algebra) (subsets prob_algebra))``,
   `subset_class (space prob_algebra) (subsets prob_algebra)`
        by REWRITE_TAC [subset_class_def, SPACE_PROB_ALGEBRA, SUBSET_UNIV]
   >> RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA]);

val PROB_BERN_ALGEBRA = store_thm
  ("PROB_BERN_ALGEBRA",
   ``!l. l IN (subsets prob_algebra) ==> (prob bern l = prob_measure l)``,
   PROVE_TAC [bern_def]);

val PROB_BERN_EMPTY = store_thm
  ("PROB_BERN_EMPTY",
   ``prob bern {} = 0``,
   RW_TAC std_ss [PROB_BERN_ALGEBRA, PROB_ALGEBRA_BASIC, PROB_MEASURE_BASIC]);

val PROB_BERN_UNIV = store_thm
  ("PROB_BERN_UNIV",
   ``prob bern UNIV = 1``,
   RW_TAC std_ss [PROB_BERN_ALGEBRA, PROB_ALGEBRA_BASIC, PROB_MEASURE_BASIC]);

val PROB_BERN_HALFSPACE = store_thm
  ("PROB_BERN_HALFSPACE",
   ``!b. prob bern (halfspace b) = 1 / 2``,
   RW_TAC std_ss [PROB_BERN_ALGEBRA, PROB_ALGEBRA_BASIC, PROB_MEASURE_BASIC]);

val PROB_BERN_BASIC = store_thm
  ("PROB_BERN_BASIC",
   ``(prob bern {} = 0) /\ (prob bern UNIV = 1) /\
     (!b. prob bern (halfspace b) = 1 / 2)``,
   RW_TAC std_ss [PROB_BERN_EMPTY, PROB_BERN_UNIV, PROB_BERN_HALFSPACE]);

val PROB_BERN_PREFIX_SET = store_thm
  ("PROB_BERN_PREFIX_SET",
   ``!l. prob bern (prefix_set l) = (1 / 2) pow (LENGTH l)``,
   RW_TAC std_ss [PROB_ALGEBRA_PREFIX_SET, PROB_BERN_ALGEBRA,
                  PROB_MEASURE_PREFIX_SET]);

val MEASURABLE_PREMEASURABLE_BERN = store_thm
  ("MEASURABLE_PREMEASURABLE_BERN",
  ``measurable (p_space bern, events bern) (p_space bern, events bern) =
 premeasurable (p_space bern, events bern) (p_space bern, events bern)``,
    PROVE_TAC [SIGMA_ALGEBRA_BERN, MEASURABLE_IS_PREMEASURABLE]);

val MEASURABLE_BERN_SUBSET = store_thm
  ("MEASURABLE_BERN_SUBSET",
   ``premeasurable prob_algebra prob_algebra
      SUBSET
     measurable (p_space bern, events bern) (p_space bern, events bern)``,
   REWRITE_TAC [MEASURABLE_PREMEASURABLE_BERN]
   >> RW_TAC std_ss [EVENTS_BERN]
   >> MATCH_MP_TAC SUBSET_TRANS
   >> Q.EXISTS_TAC `premeasurable (sigma (space prob_algebra) (subsets prob_algebra)) prob_algebra`
   >> CONJ_TAC >- PROVE_TAC [PREMEASURABLE_UP_SIGMA, space_def, subsets_def]
   >> REWRITE_TAC [SPACE_BERN]
   >> REWRITE_TAC [SIGMA_REDUCE]
   >> MP_TAC SIGMA_PROB_ALGEBRA
   >> REWRITE_TAC [PREMEASURABLE_SUBSET]);

val MEASURABLE_BERN_LIFT = store_thm
  ("MEASURABLE_BERN_LIFT",
   ``!f.
       f IN premeasurable prob_algebra prob_algebra ==>
       f IN measurable (p_space bern, events bern) (p_space bern, events bern)``,
   PROVE_TAC [MEASURABLE_BERN_SUBSET, SUBSET_DEF]);

val MEASURABLE_BERN_STL = store_thm
  ("MEASURABLE_BERN_STL",
   ``stl IN measurable (p_space bern, events bern) (p_space bern, events bern)``,
   PROVE_TAC [MEASURABLE_BERN_LIFT, PREMEASURABLE_PROB_ALGEBRA_STL]);

val MEASURABLE_BERN_SCONS = store_thm
  ("MEASURABLE_BERN_SCONS",
   ``!b. scons b IN measurable (p_space bern, events bern) (p_space bern, events bern)``,
   PROVE_TAC [MEASURABLE_BERN_LIFT, PREMEASURABLE_PROB_ALGEBRA_SCONS]);

val EVENTS_BERN_STL = store_thm
  ("EVENTS_BERN_STL",
  ``!p. (p o stl) IN events bern = p IN events bern``,
    STRIP_TAC
 >> reverse EQ_TAC
 >- ( RW_TAC std_ss [] \\
      `p o stl = PREIMAGE stl p` by PROVE_TAC [PREIMAGE_ALT] \\
      POP_ORW \\
      MP_TAC MEASURABLE_BERN_STL \\
      REWRITE_TAC [IN_MEASURABLE] \\
      RW_TAC std_ss [subsets_def, space_def] \\
      FULL_SIMP_TAC std_ss [REWRITE_RULE [SPACE_PROB_ALGEBRA] SPACE_BERN, INTER_UNIV] )
 >> DISCH_TAC
 >> Suff `p = PREIMAGE (scons T) (p o stl)`
 >- ( Rewr' \\
      MP_TAC (Q.SPEC `T` MEASURABLE_BERN_SCONS) \\
      REWRITE_TAC [IN_MEASURABLE] \\
      RW_TAC std_ss [subsets_def, space_def] \\
      FULL_SIMP_TAC std_ss [REWRITE_RULE [SPACE_PROB_ALGEBRA] SPACE_BERN, INTER_UNIV] )
 >> PSET_TAC [IN_PREIMAGE, STL_SCONS, EXTENSION]);

val EVENTS_BERN_SDROP = store_thm
  ("EVENTS_BERN_SDROP",
   ``!n p. (p o sdrop n) IN events bern = p IN events bern``,
   Induct >- RW_TAC std_ss [I_o_ID, sdrop_def]
   >> RW_TAC bool_ss [sdrop_def, EVENTS_BERN_STL, o_ASSOC]);

val PROB_PRESERVING_BERN_SUBSET = store_thm
  ("PROB_PRESERVING_BERN_SUBSET",
   ``prob_preserving (space prob_algebra, subsets prob_algebra, prob_measure)
                     (space prob_algebra, subsets prob_algebra, prob_measure)
     SUBSET prob_preserving bern bern``,
   MATCH_MP_TAC SUBSET_TRANS
   >> Q.EXISTS_TAC `prob_preserving bern (space prob_algebra, subsets prob_algebra, prob bern)`
   >> reverse CONJ_TAC
   >- ( REWRITE_TAC [SYM SPACE_BERN] \\
        MATCH_MP_TAC PROB_PRESERVING_SUBSET \\
        RW_TAC std_ss [EVENTS_BERN, SPACE_BERN, PROB_SPACE_BERN, PROB_ALGEBRA_ALGEBRA] )
   >> Know `(space prob_algebra, subsets (sigma (space prob_algebra) (subsets prob_algebra)))
                = (sigma (space prob_algebra) (subsets prob_algebra))`
   >- ( REWRITE_TAC [sigma_def, PAIR_EQ, subsets_def] )
   >> Know `subset_class (space prob_algebra) (subsets prob_algebra)`
   >- ( REWRITE_TAC [subset_class_def, SPACE_PROB_ALGEBRA, SUBSET_UNIV] )
   >> RW_TAC std_ss [SUBSET_DEF, PROB_PRESERVING, GSPECIFICATION, EVENTS, PROB, SPACE_BERN,
                     EVENTS_BERN, IN_PREMEASURABLE, p_space_def, m_space_def, space_def,
                     SIGMA_ALGEBRA_SIGMA, SPACE_SUBSETS_PROB_ALGEBRA] (* 3 goals here *)
   >- PROVE_TAC [SIGMA_PROB_ALGEBRA, SIGMA_ALGEBRA_ALGEBRA]
   >- (MATCH_MP_TAC IN_SIGMA >> PROVE_TAC [])
   >> PROVE_TAC [PROB_BERN_ALGEBRA]);

val PROB_PRESERVING_BERN_LIFT = store_thm
  ("PROB_PRESERVING_BERN_LIFT",
   ``!f.
       f IN
       prob_preserving (space prob_algebra, subsets prob_algebra, prob_measure)
                       (space prob_algebra, subsets prob_algebra, prob_measure)
       ==>
       f IN prob_preserving bern bern``,
   MP_TAC PROB_PRESERVING_BERN_SUBSET
   >> RW_TAC std_ss [SUBSET_DEF]);

val PROB_PRESERVING_BERN_STL = store_thm
  ("PROB_PRESERVING_BERN_STL",
   ``stl IN prob_preserving bern bern``,
   MATCH_MP_TAC PROB_PRESERVING_BERN_LIFT
   >> RW_TAC std_ss [PROB_PRESERVING_PROB_ALGEBRA_STL]);

val PROB_PRESERVING_BERN_SDROP = store_thm
  ("PROB_PRESERVING_BERN_SDROP",
   ``!n. sdrop n IN prob_preserving bern bern``,
   STRIP_TAC
   >> MATCH_MP_TAC PROB_PRESERVING_BERN_LIFT
   >> RW_TAC std_ss [PROB_PRESERVING_PROB_ALGEBRA_SDROP]);

val PROB_BERN_STL = store_thm
  ("PROB_BERN_STL",
  ``!p. p IN events bern ==> (prob bern (p o stl) = prob bern p)``,
   RW_TAC std_ss []
   >> MP_TAC PROB_PRESERVING_BERN_STL
   >> ASSUME_TAC (REWRITE_RULE [SPACE_PROB_ALGEBRA] SPACE_BERN)
   >> RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION, PREIMAGE_ALT, INTER_UNIV]);

val PROB_BERN_SDROP = store_thm
  ("PROB_BERN_SDROP",
  ``!n p. p IN events bern ==> (prob bern (p o sdrop n) = prob bern p)``,
   RW_TAC std_ss []
   >> MP_TAC PROB_PRESERVING_BERN_SDROP
   >> ASSUME_TAC (REWRITE_RULE [SPACE_PROB_ALGEBRA] SPACE_BERN)
   >> RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION, PREIMAGE_ALT, INTER_UNIV]);

val EVENTS_BERN_LIFT = store_thm
  ("EVENTS_BERN_LIFT",
  ``!x. x IN (subsets prob_algebra) ==> x IN events bern``,
   RW_TAC std_ss [EVENTS_BERN]
   >> PROVE_TAC [IN_SIGMA]);

val EVENTS_BERN_EMPTY = store_thm
  ("EVENTS_BERN_EMPTY",
   ``{} IN events bern``,
   PROVE_TAC [EVENTS_BERN_LIFT, PROB_ALGEBRA_EMPTY]);

val EVENTS_BERN_UNIV = store_thm
  ("EVENTS_BERN_UNIV",
   ``UNIV IN events bern``,
   PROVE_TAC [EVENTS_BERN_LIFT, PROB_ALGEBRA_UNIV]);

val EVENTS_BERN_HALFSPACE = store_thm
  ("EVENTS_BERN_HALFSPACE",
   ``!b. halfspace b IN events bern``,
   PROVE_TAC [EVENTS_BERN_LIFT, PROB_ALGEBRA_HALFSPACE]);

val EVENTS_BERN_BASIC = store_thm
  ("EVENTS_BERN_BASIC",
   ``{} IN events bern /\ UNIV IN events bern /\
     !b. halfspace b IN events bern``,
   RW_TAC std_ss [EVENTS_BERN_EMPTY, EVENTS_BERN_UNIV, EVENTS_BERN_HALFSPACE]);

val EVENTS_BERN_PREFIX_SET = store_thm
  ("EVENTS_BERN_PREFIX_SET",
   ``!l. prefix_set l IN events bern``,
   STRIP_TAC
   >> MATCH_MP_TAC EVENTS_BERN_LIFT
   >> RW_TAC std_ss [PROB_ALGEBRA_PREFIX_SET]);

val EVENTS_BERN_EMBED = store_thm
  ("EVENTS_BERN_EMBED",
   ``!x. prob_embed x IN events bern``,
   RW_TAC std_ss [EVENTS_BERN_LIFT, PROB_EMBED_ALGEBRA]);

val EVENTS_BERN_SING = store_thm
  ("EVENTS_BERN_SING", ``!x. {x} IN events bern``,
   RW_TAC std_ss []
   >> MP_TAC (CONV_RULE SKOLEM_CONV (Q.SPEC `x` EXIST_LONG_PREFIX_SETS))
   >> RW_TAC std_ss []
   >> Suff `{x} = BIGINTER (IMAGE (prefix_set o l) UNIV)`
   >- ( Rewr
        >> MATCH_MP_TAC EVENTS_COUNTABLE_INTER
        >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, o_THM, IN_UNIV, PROB_SPACE_BERN,
                          COUNTABLE_IMAGE_NUM] (* 2 sub-goals here *)
        >- RW_TAC std_ss [EVENTS_BERN_PREFIX_SET]
        >> REWRITE_TAC [IMAGE_DEF, o_THM, IN_UNIV]
        >> REWRITE_TAC [GSYM MEMBER_NOT_EMPTY]
        >> Q.EXISTS_TAC `prefix_set (l ARB)`
        >> RW_TAC std_ss [GSPECIFICATION]
        >> Q.EXISTS_TAC `ARB`
        >> RW_TAC std_ss [] )
   >> ONCE_REWRITE_TAC [EXTENSION]
   >> RW_TAC std_ss [IN_SING, IN_BIGINTER_IMAGE, IN_UNIV, o_THM]
   >> EQ_TAC >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> FUN_EQ_TAC
   >> GEN_TAC
   >> Know
      `!n. ?l. (LENGTH l = n) /\ x IN prefix_set l /\ x' IN prefix_set l`
   >- PROVE_TAC []
   >> Q.SPEC_TAC (`x'`, `w`)
   >> Q.SPEC_TAC (`x`, `v`)
   >> KILL_TAC
   >> Induct_on `x''`
   >- ( RW_TAC std_ss []
        >> POP_ASSUM (MP_TAC o Q.SPEC `1`)
        >> STRIP_TAC
        >> REPEAT (POP_ASSUM MP_TAC)
        >> Cases_on `l` >- RW_TAC arith_ss [LENGTH]
        >> reverse (Cases_on `t`) >- RW_TAC arith_ss [LENGTH]
        >> RW_TAC arith_ss [LENGTH, prefix_set_def, IN_INTER, IN_HALFSPACE, shd_def] )
   >> RW_TAC std_ss []
   >> SEQ_CASES_TAC `w`
   >> SEQ_CASES_TAC `v`
   >> RW_TAC std_ss [scons_def]
   >> Q.PAT_X_ASSUM `!v w. P v w` MATCH_MP_TAC
   >> GEN_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `SUC n`)
   >> STRIP_TAC
   >> REPEAT (POP_ASSUM MP_TAC)
   >> Cases_on `l` >- RW_TAC arith_ss [LENGTH]
   >> RW_TAC arith_ss [LENGTH, prefix_set_def, IN_HALFSPACE, IN_INTER, IN_o,
                       STL_SCONS, SHD_SCONS]
   >> PROVE_TAC []);

val EVENTS_BERN_COUNTABLE = store_thm
  ("EVENTS_BERN_COUNTABLE",
   ``!c. countable c ==> c IN events bern``,
   RW_TAC std_ss []
   >> Know `c = BIGUNION (IMAGE (\x. {x}) c)`
   >- (ONCE_REWRITE_TAC [EXTENSION]
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
   >> Rewr'
   >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, SUBSET_DEF, image_countable, IN_IMAGE]
   >> PROVE_TAC [EVENTS_BERN_SING]);

val EVENTS_BERN_FINITE = store_thm
  ("EVENTS_BERN_FINITE",
   ``!c. FINITE c ==> c IN events bern``,
   PROVE_TAC [EVENTS_BERN_COUNTABLE, finite_countable]);

val PROB_BERN_SING = store_thm
  ("PROB_BERN_SING",
   ``!x. prob bern {x} = 0``,
   RW_TAC std_ss []
   >> ASSUME_TAC (Q.SPEC `x` EVENTS_BERN_SING)
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   >> reverse CONJ_TAC >- PROVE_TAC [PROB_POSITIVE, PROB_SPACE_BERN]
   >> MATCH_MP_TAC REAL_LE_EPSILON
   >> RW_TAC real_ss []
   >> MP_TAC (Q.SPEC `e` POW_HALF_SMALL)
   >> RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`x`, `n`] EXIST_LONG_PREFIX_SETS)
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `prob bern (prefix_set l)`
   >> reverse CONJ_TAC
   >- (RW_TAC std_ss [PROB_BERN_PREFIX_SET]
       >> PROVE_TAC [REAL_LT_IMP_LE])
   >> MATCH_MP_TAC PROB_INCREASING
   >> RW_TAC std_ss [SUBSET_DEF, IN_SING, PROB_SPACE_BERN,
                     EVENTS_BERN_PREFIX_SET]);

val PROB_BERN_FINITE = store_thm
  ("PROB_BERN_FINITE",
   ``!c. FINITE c ==> (prob bern c = 0)``,
   HO_MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [PROB_BERN_EMPTY]
   >> Know `0 = prob bern {e} + prob bern c`
   >- RW_TAC real_ss [PROB_BERN_SING]
   >> Rewr
   >> MATCH_MP_TAC PROB_ADDITIVE
   >> RW_TAC std_ss [IN_DISJOINT, EVENTS_BERN_SING, PROB_SPACE_BERN,
                     EVENTS_BERN_FINITE, IN_SING]
   >> PROVE_TAC [INSERT_SING_UNION]);

val PROB_BERN_COUNTABLE = store_thm
  ("PROB_BERN_COUNTABLE",
   ``!c. countable c ==> (prob bern c = 0)``,
   RW_TAC std_ss [COUNTABLE_ALT_BIJ, BIJ_DEF, SURJ_DEF, INJ_DEF, IN_UNIV]
   >- PROVE_TAC [PROB_BERN_FINITE]
   >> Suff
      `prob bern o (\x. {enumerate c x}) sums 0 /\
       prob bern o (\x. {enumerate c x}) sums prob bern c`
   >- PROVE_TAC [SUM_UNIQ]
   >> CONJ_TAC
   >- (MP_TAC (Q.SPECL [`prob bern o (\x. {enumerate c x})`, `0`] SER_0)
       >> RW_TAC std_ss [sum]
       >> POP_ASSUM MATCH_MP_TAC
       >> RW_TAC arith_ss [o_THM, PROB_BERN_SING])
   >> MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, PROB_SPACE_BERN, IN_DISJOINT,
                     EVENTS_BERN_SING, IN_SING]
   >- PROVE_TAC []
   >> ONCE_REWRITE_TAC [EXTENSION]
   >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, IN_SING]
   >> PROVE_TAC []);

val EVENTS_BERN_HALFSPACE_INTER = store_thm
  ("EVENTS_BERN_HALFSPACE_INTER",
   ``!p b. p IN events bern ==> halfspace b INTER p IN events bern``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC EVENTS_INTER
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_HALFSPACE]);

val PROB_BERN_INTER_HALVES = store_thm
  ("PROB_BERN_INTER_HALVES",
   ``!p.
       p IN events bern ==>
       (prob bern (halfspace T INTER p) + prob bern (halfspace F INTER p) =
        prob bern p)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC EQ_SYM
   >> MATCH_MP_TAC PROB_ADDITIVE
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_HALFSPACE_INTER]
   >> PSET_TAC [IN_HALFSPACE, EXTENSION]
   >> PROVE_TAC []);

val PROB_PRESERVING_BERN_MIRROR = store_thm
  ("PROB_PRESERVING_BERN_MIRROR",
   ``mirror IN prob_preserving bern bern``,
   MATCH_MP_TAC PROB_PRESERVING_BERN_LIFT
   >> RW_TAC std_ss [PROB_PRESERVING_PROB_ALGEBRA_MIRROR]);

val MEASURABLE_BERN_MIRROR = store_thm
  ("MEASURABLE_BERN_MIRROR",
  ``mirror IN measurable (p_space bern, events bern) (p_space bern, events bern)``,
   REWRITE_TAC [MEASURABLE_PREMEASURABLE_BERN]
   >> MP_TAC PROB_PRESERVING_BERN_MIRROR
   >> RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION]);

val PROB_BERN_STL_HALFSPACE = store_thm
  ("PROB_BERN_STL_HALFSPACE",
   ``!b p.
       p IN events bern ==>
       (prob bern (halfspace b INTER (p o stl)) = 1 / 2 * prob bern p)``,
   RW_TAC std_ss []
   >> Suff
      `(prob bern (halfspace b INTER (p o stl)) =
        prob bern (halfspace (~b) INTER (p o stl))) /\
       (prob bern (halfspace b INTER (p o stl)) +
        prob bern (halfspace (~b) INTER (p o stl)) =
        2 * (1 / 2 * prob bern p))`
   >- REAL_ARITH_TAC
   >> Know `!b. (halfspace b INTER p o stl) IN events bern`
   >- PROVE_TAC [EVENTS_BERN_HALFSPACE_INTER, EVENTS_BERN_STL]
   >> STRIP_TAC
   >> CONJ_TAC
   >- (MP_TAC PROB_PRESERVING_BERN_MIRROR
       >> RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION]
       >> Suff
          `halfspace (~b) INTER p o stl =
           PREIMAGE mirror (halfspace b INTER p o stl)`
       >- ( DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
            FULL_SIMP_TAC std_ss [SPACE_BERN, SPACE_PROB_ALGEBRA, INTER_UNIV] )
       >> PSET_TAC [EXTENSION]
       >> SEQ_CASES_TAC `x`
       >> RW_TAC std_ss [MIRROR_SCONS, STL_SCONS, IN_HALFSPACE, SHD_SCONS]
       >> PROVE_TAC [])
   >> RW_TAC std_ss [REAL_MUL_ASSOC, HALF_CANCEL, REAL_MUL_LID]
   >> Know `prob bern p = prob bern (p o stl)`
   >- RW_TAC std_ss [PROB_BERN_STL]
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> Know `p o stl IN events bern`
   >- RW_TAC std_ss [EVENTS_BERN_STL]
   >> POP_ASSUM MP_TAC
   >> KILL_TAC
   >> Q.SPEC_TAC (`p o stl`, `p`)
   >> RW_TAC std_ss []
   >> Cases_on `b`
   >> PROVE_TAC [PROB_BERN_INTER_HALVES, REAL_ADD_SYM]);

val INDEP_FUNCTION_BERN_UNIT = store_thm
  ("INDEP_FUNCTION_BERN_UNIT",
   ``!x. UNIT x IN indep_function bern``,
   BasicProvers.NORM_TAC std_ss
    [indep_function_def, GSPECIFICATION, FST_o_UNIT, SND_o_UNIT,
     PREIMAGE_I, IMAGE_II, I_THM, indep_families_def, IN_IMAGE,
     IN_UNIV, PREIMAGE_K, INDEP_EMPTY, PROB_SPACE_BERN, PREIMAGE_ALT]
   >> REWRITE_TAC [SYM (REWRITE_RULE [SPACE_PROB_ALGEBRA] SPACE_BERN)]
   >> MATCH_MP_TAC INDEP_SPACE
   >> ASM_REWRITE_TAC [PROB_SPACE_BERN]);

val EVENTS_BERN_SHD = store_thm
  ("EVENTS_BERN_SHD",
   ``!x. (x o shd) IN events bern``,
   PROVE_TAC [EVENTS_BERN_LIFT, PROB_ALGEBRA_SHD]);

val EVENTS_BERN_MIRROR = store_thm
  ("EVENTS_BERN_MIRROR",
   ``!s. (s o mirror) IN events bern = s IN events bern``,
   RW_TAC std_ss []
   >> MP_TAC MEASURABLE_BERN_MIRROR
   >> RW_TAC std_ss [IN_MEASURABLE, PREIMAGE_ALT, subsets_def, space_def,
                     SPACE_BERN, SPACE_PROB_ALGEBRA, INTER_UNIV]
   >> reverse EQ_TAC >- RW_TAC std_ss []
   >> POP_ASSUM (MP_TAC o Q.SPEC `s o mirror`)
   >> RW_TAC std_ss [GSYM o_ASSOC, MIRROR_o_MIRROR, I_o_ID]);

val EVENTS_BERN_IMAGE_STL = store_thm
  ("EVENTS_BERN_IMAGE_STL",
   ``!x. x IN events bern ==> IMAGE stl x IN events bern``,
   RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [GSYM EVENTS_BERN_STL]
   >> RW_TAC std_ss [GSYM PREIMAGE_ALT]
   >> Know `PREIMAGE stl (IMAGE stl x) = x UNION PREIMAGE mirror x`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_PREIMAGE, IN_IMAGE, IN_UNION]
       >> SEQ_CASES_TAC `x'`
       >> RW_TAC std_ss [STL_SCONS, MIRROR_SCONS]
       >> EQ_TAC
       >- (RW_TAC std_ss []
           >> Know `(h = shd x'') \/ (~h = shd x'')` >- PROVE_TAC []
           >> STRIP_TAC
           >> RW_TAC std_ss [SCONS_SHD_STL])
       >> RW_TAC std_ss []
       >> PROVE_TAC [STL_SCONS])
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> MATCH_MP_TAC EVENTS_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, PREIMAGE_ALT, EVENTS_BERN_MIRROR]);

val INDEP_BERN_UNIV = save_thm ("INDEP_BERN_UNIV",
   REWRITE_RULE [SPACE_BERN, SPACE_PROB_ALGEBRA] (ISPEC ``bern`` INDEP_SPACE));

val INDEP_FUNCTION_BERN_SDEST = store_thm
  ("INDEP_FUNCTION_BERN_SDEST",
   ``sdest IN indep_function bern``,
   RW_TAC std_ss [indep_function_def, GSPECIFICATION, indep_families_def,
                  FST_o_SDEST, SND_o_SDEST, IN_IMAGE, IN_UNIV, o_THM]
   >> MP_TAC (Q.SPEC `x` PREIMAGE_SHD_CASES)
   >> RW_TAC std_ss [PREIMAGE_ALT] (* 3 sub-goals here *)
   >> RW_TAC std_ss [INDEP_EMPTY, INDEP_BERN_UNIV, EVENTS_BERN_STL, PROB_SPACE_BERN] (* 1 left *)
   >> RW_TAC std_ss [indep_def, EVENTS_BERN_BASIC, EVENTS_BERN_STL,
                     PROB_BERN_HALFSPACE, PROB_BERN_STL_HALFSPACE,
                     PROB_BERN_STL, INTER_UNIV, PROB_BERN_UNIV]);

val INDEP_FUNCTION_BERN_SCONS = store_thm
  ("INDEP_FUNCTION_BERN_SCONS",
   ``!b. (\s. (b, scons b s)) IN indep_function bern``,
   RW_TAC std_ss' [indep_function_def, GSPECIFICATION, indep_families_def,
                   IN_IMAGE, o_DEF, IN_UNIV, GSYM K_PARTIAL]
   >> Suff `PREIMAGE (scons b) x' IN events bern`
   >- RW_TAC std_ss [PREIMAGE_K, INDEP_EMPTY, INDEP_BERN_UNIV, PROB_SPACE_BERN]
   >> Know `PREIMAGE (scons b) x' = IMAGE stl (x' INTER halfspace b)`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_PREIMAGE, IN_IMAGE, IN_INTER, IN_HALFSPACE]
       >> EQ_TAC
       >- (RW_TAC std_ss []
           >> Q.EXISTS_TAC `scons b x`
           >> RW_TAC std_ss [SHD_SCONS, STL_SCONS])
       >> RW_TAC std_ss []
       >> RW_TAC std_ss [SCONS_SHD_STL])
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> MATCH_MP_TAC EVENTS_BERN_IMAGE_STL
   >> MATCH_MP_TAC EVENTS_INTER
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_HALFSPACE]);

val INDEP_FUNCTION_BERN_BIND = store_thm
  ("INDEP_FUNCTION_BERN_BIND",
   ``?f. ?g : bool -> (num -> bool) -> bool # (num -> bool).
       f IN indep_function bern /\ (!x. g x IN indep_function bern) /\
       ~(BIND f g IN indep_function bern)``,
   Q.EXISTS_TAC `sdest`
   >> Q.EXISTS_TAC
      `\x. if x then (\s. (T, scons T s)) else (\s. (F, scons F s))`
   >> RW_TAC std_ss [INDEP_FUNCTION_BERN_SDEST, INDEP_FUNCTION_BERN_SCONS]
   >> RW_TAC std_ss [indep_function_def, GSPECIFICATION, indep_families_def]
   >> Q.EXISTS_TAC `halfspace T`
   >> Q.EXISTS_TAC `halfspace T`
   >> RW_TAC std_ss [IN_IMAGE, IN_UNIV] >|
   [Q.EXISTS_TAC `{T}`
    >> SET_EQ_TAC
    >> RW_TAC std_ss [IN_HALFSPACE, IN_PREIMAGE, IN_SING, BIND_DEF, o_THM]
    >> SEQ_CASES_TAC `x`
    >> RW_TAC std_ss [sdest_def, SHD_SCONS, STL_SCONS],
    Q.EXISTS_TAC `halfspace T`
    >> RW_TAC std_ss [EVENTS_BERN_HALFSPACE]
    >> SET_EQ_TAC
    >> RW_TAC std_ss [IN_HALFSPACE, IN_PREIMAGE, IN_SING, BIND_DEF, o_THM]
    >> SEQ_CASES_TAC `x`
    >> RW_TAC std_ss [sdest_def, SHD_SCONS, STL_SCONS],
    RW_TAC std_ss [indep_def, EVENTS_BERN_HALFSPACE, PROB_BERN_HALFSPACE,
                   INTER_IDEMPOT]
    >> RW_TAC arith_ss [GSYM REAL_INV_1OVER, GSYM REAL_INV_MUL,
                        REAL_OF_NUM_EQ, REAL_INV_INJ, REAL_MUL]]);

val INDEP_FUNCTION_BERN_EXAMPLE = store_thm
  ("INDEP_FUNCTION_BERN_EXAMPLE",
   ``(\s. (shd s = shd (stl s), stl s)) IN indep_function bern``,
   RW_TAC std_ss' [indep_function_def, GSPECIFICATION, indep_families_def,
                   IN_IMAGE, IN_UNIV, o_DEF]
   >> Q.SPEC_TAC (`x`, `x`)
   >> HO_MATCH_MP_TAC BOOL_SET_CASES
   >> (RW_TAC std_ss [PREIMAGE_EMPTY, PREIMAGE_UNIV]
       >> RW_TAC std_ss [INDEP_EMPTY, INDEP_BERN_UNIV, PREIMAGE_ALT, PROB_SPACE_BERN,
                         EVENTS_BERN_STL]) >|
   [Know `{T} o (\x. shd x = shd (stl x)) = prob_embed [[T; T]; [F; F]]`
    >- (RW_TAC std_ss [EXTENSION, IN_o, IN_SING, prob_embed_def, MAP,
                       prefix_set_def, UNIONL_def, IN_HALFSPACE, IN_INTER,
                       IN_UNION, IN_UNIV, NOT_IN_EMPTY]
        >> PROVE_TAC [])
    >> Rewr
    >> RW_TAC prob_canon_ss [indep_def, EVENTS_BERN_STL, EVENTS_BERN_EMBED,
                             PROB_BERN_STL, PROB_BERN_ALGEBRA,
                             PROB_EMBED_ALGEBRA, PROB_MEASURE_ALT,
                             prob_premeasure_def]
    >> RW_TAC bool_ss [TWO,ONE,pow]
    >> RW_TAC std_ss [prob_embed_def, MAP, prefix_set_def, UNIONL_def,
                      GSYM PREIMAGE_ALT, PREIMAGE_UNIV, INTER_UNIV, UNION_EMPTY]
    >> RW_TAC std_ss [REAL_ADD_RID, REAL_MUL_RID, GSYM PREIMAGE_INTER,
                      INTER_UNION_RDISTRIB, INTER_ASSOC]
    >> Know
       `prob bern
        (halfspace T INTER PREIMAGE stl (halfspace T INTER x') UNION
         halfspace F INTER PREIMAGE stl (halfspace F INTER x')) =
        prob bern (halfspace T INTER PREIMAGE stl (halfspace T INTER x')) +
        prob bern (halfspace F INTER PREIMAGE stl (halfspace F INTER x'))`
    >- (MATCH_MP_TAC PROB_ADDITIVE
        >> RW_TAC std_ss [PROB_SPACE_BERN, PREIMAGE_ALT, EVENTS_INTER,
                          EVENTS_BERN_STL, EVENTS_BERN_BASIC]
        >> RW_TAC std_ss [IN_DISJOINT, IN_HALFSPACE, IN_INTER]
        >> PROVE_TAC [])
   >> Rewr
   >> RW_TAC std_ss [PREIMAGE_ALT, PROB_BERN_STL_HALFSPACE, EVENTS_INTER,
                     EVENTS_BERN_BASIC, PROB_SPACE_BERN, GSYM REAL_ADD_LDISTRIB,
                     PROB_BERN_INTER_HALVES, REAL_HALF_DOUBLE, REAL_MUL_RID],
    Know `{F} o (\x. shd x = shd (stl x)) = prob_embed [[F; T]; [T; F]]`
    >- (RW_TAC std_ss [EXTENSION, IN_o, IN_SING, prob_embed_def, MAP,
                       prefix_set_def, UNIONL_def, IN_HALFSPACE, IN_INTER,
                       IN_UNION, IN_UNIV, NOT_IN_EMPTY]
        >> ho_PROVE_TAC [])
    >> Rewr
    >> RW_TAC prob_canon_ss [indep_def, EVENTS_BERN_STL, EVENTS_BERN_EMBED,
                             PROB_BERN_STL, PROB_BERN_ALGEBRA,
                             PROB_EMBED_ALGEBRA, PROB_MEASURE_ALT,
                             prob_premeasure_def]
    >> RW_TAC bool_ss [TWO,ONE,pow]
    >> RW_TAC std_ss [prob_embed_def, MAP, prefix_set_def, UNIONL_def,
                      GSYM PREIMAGE_ALT, PREIMAGE_UNIV, INTER_UNIV, UNION_EMPTY]
    >> RW_TAC std_ss [REAL_ADD_RID, REAL_MUL_RID, GSYM PREIMAGE_INTER,
                      INTER_UNION_RDISTRIB, INTER_ASSOC]
    >> Know
       `prob bern
        (halfspace F INTER PREIMAGE stl (halfspace T INTER x') UNION
         halfspace T INTER PREIMAGE stl (halfspace F INTER x')) =
        prob bern (halfspace F INTER PREIMAGE stl (halfspace T INTER x')) +
        prob bern (halfspace T INTER PREIMAGE stl (halfspace F INTER x'))`
    >- (MATCH_MP_TAC PROB_ADDITIVE
        >> RW_TAC std_ss [PROB_SPACE_BERN, PREIMAGE_ALT, EVENTS_INTER,
                          EVENTS_BERN_STL, EVENTS_BERN_BASIC]
        >> RW_TAC std_ss [IN_DISJOINT, IN_HALFSPACE, IN_INTER]
        >> PROVE_TAC [])
   >> Rewr
   >> RW_TAC std_ss [PREIMAGE_ALT, PROB_BERN_STL_HALFSPACE, EVENTS_INTER,
                     EVENTS_BERN_BASIC, PROB_SPACE_BERN, GSYM REAL_ADD_LDISTRIB,
                     PROB_BERN_INTER_HALVES, REAL_HALF_DOUBLE, REAL_MUL_RID]]);

val EVENTS_BERN_PREFIX_COVER = store_thm
  ("EVENTS_BERN_PREFIX_COVER",
   ``!c. BIGUNION (IMAGE prefix_set c) IN events bern``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   >> RW_TAC std_ss [image_countable, COUNTABLE_BOOL_LIST, PROB_SPACE_BERN,
                     SUBSET_DEF, IN_IMAGE]
   >> RW_TAC std_ss [EVENTS_BERN_PREFIX_SET]);

val PROB_BERN_PREFIX_COVER = store_thm
  ("PROB_BERN_PREFIX_COVER",
   ``!c. prefix_cover c ==> (prob bern (BIGUNION (IMAGE prefix_set c)) = 1)``,
   PROVE_TAC [prefix_cover_def]);

val PROB_BERN_PREFIX_COVER_INTER = store_thm
  ("PROB_BERN_PREFIX_COVER_INTER",
   ``!c s.
       s IN events bern /\ prefix_cover c ==>
       (prob bern (s INTER BIGUNION (IMAGE prefix_set c)) = prob bern s)``,
   RW_TAC std_ss [prefix_cover_def]
   >> MATCH_MP_TAC PROB_ONE_INTER
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_PREFIX_COVER]);

val PREFIX_COVER_DISJOINT = store_thm
  ("PREFIX_COVER_DISJOINT",
   ``!c s t.
       prefix_cover c /\ s IN (IMAGE prefix_set c) /\
       t IN (IMAGE prefix_set c) /\ ~(s = t) ==>
       DISJOINT s t``,
   RW_TAC std_ss [prefix_cover_def, IN_IMAGE]
   >> MP_TAC (Q.SPECL [`x`, `x'`] PREFIX_SET_SUBSET)
   >> RW_TAC std_ss [PREFIX_SET_PREFIX_SUBSET]
   >> PROVE_TAC []);

val PROB_BERN_PREFIX_SET_INTER_SDROP = store_thm
  ("PROB_BERN_PREFIX_SET_INTER_SDROP",
   ``!l s.
       s IN events bern ==>
       (prob bern (prefix_set l INTER (s o sdrop (LENGTH l))) =
        prob bern (prefix_set l) * prob bern s)``,
   RW_TAC std_ss []
   >> Induct_on `l`
   >- RW_TAC real_ss [prefix_set_def, INTER_UNIV, LENGTH, sdrop_def, I_o_ID,
                      PROB_BERN_UNIV]
   >> RW_TAC std_ss [prefix_set_def, sdrop_def, LENGTH, INTER_ASSOC]
   >> Know
      `prefix_set l o stl INTER s o sdrop (LENGTH l) o stl =
       (prefix_set l INTER s o sdrop (LENGTH l)) o stl`
   >- RW_TAC std_ss [EXTENSION, IN_INTER, IN_o, o_THM]
   >> Rewr
   >> RW_TAC std_ss [PROB_BERN_STL_HALFSPACE, EVENTS_BERN_PREFIX_SET]
   >> POP_ASSUM (fn th => REWRITE_TAC [SYM th, GSYM REAL_MUL_ASSOC])
   >> MATCH_MP_TAC PROB_BERN_STL_HALFSPACE
   >> MATCH_MP_TAC EVENTS_INTER
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_PREFIX_SET,
                     EVENTS_BERN_SDROP]);

val IN_MEASURABLE_BERN_BERN = store_thm
  ("IN_MEASURABLE_BERN_BERN",
   ``!f. f IN measurable (p_space bern,events bern) (p_space bern,events bern) =
         f IN (p_space bern -> p_space bern) /\
        !s. s IN events bern ==> PREIMAGE f s IN events bern``,
   MP_TAC (REWRITE_RULE [SIGMA_ALGEBRA_BERN, space_def, subsets_def]
                        (Q.ISPECL [`(p_space bern,events bern)`, `(p_space bern,events bern)`]
                                  IN_MEASURABLE))
   >> RW_TAC std_ss [SPACE_BERN, SPACE_PROB_ALGEBRA, INTER_UNIV]);

val IN_PREMEASURABLE_BERN_BERN = store_thm
  ("IN_PREMEASURABLE_BERN_BERN",
   ``!f. f IN premeasurable (p_space bern,events bern) (p_space bern,events bern) =
         f IN (p_space bern -> p_space bern) /\
        !s. s IN events bern ==> PREIMAGE f s IN events bern``,
   REWRITE_TAC [SYM MEASURABLE_PREMEASURABLE_BERN]
   >> REWRITE_TAC [IN_MEASURABLE_BERN_BERN]);

val INDEP_FN_PROB_PRESERVING = store_thm
  ("INDEP_FN_PROB_PRESERVING",
   ``!f. f IN indep_fn ==> (SND o f) IN prob_preserving bern bern``,
   RW_TAC std_ss [indep_fn_def, IN_PROB_PRESERVING, GSPECIFICATION,
                  MEASURABLE_PREMEASURABLE_BERN]
   >> REWRITE_TAC [space_def, subsets_def, SPACE_BERN, SPACE_PROB_ALGEBRA, INTER_UNIV]
   >> Know `PREIMAGE (SND o f) s IN (events bern)`
   >- PROVE_TAC [IN_PREMEASURABLE_BERN_BERN]
   >> STRIP_TAC
   >> MP_TAC (Q.ISPEC `IMAGE prefix_set c` COUNTABLE_DISJOINT_ENUM)
   >> Know
      `countable (IMAGE prefix_set c) /\
       !s t.
         s IN IMAGE prefix_set c /\ t IN IMAGE prefix_set c /\ ~(s = t) ==>
         DISJOINT s t`
   >- (CONJ_TAC >- RW_TAC std_ss [image_countable, COUNTABLE_BOOL_LIST]
       >> RW_TAC std_ss [IN_IMAGE, o_THM]
       >> MP_TAC
          (Q.SPECL [`c`, `prefix_set x`, `prefix_set x'`]
           PREFIX_COVER_DISJOINT)
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [IN_IMAGE, DISJOINT_DEF, IN_INTER, EXTENSION,
                         NOT_IN_EMPTY]
       >> PROVE_TAC [])
   >> DISCH_THEN (fn th => DISCH_THEN (fn ith => MP_TAC (MP ith th)))
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `f' IN X` MP_TAC
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INSERT, IN_IMAGE]
   >> Know
      `prob bern (PREIMAGE (SND o f) s INTER BIGUNION (IMAGE prefix_set c)) =
       prob bern (PREIMAGE (SND o f) s)`
   >- (MATCH_MP_TAC PROB_BERN_PREFIX_COVER_INTER
       >> RW_TAC std_ss [])
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [INTER_BIGUNION, IMAGE_IMAGE]
   >> Suff
      `prob bern o (($INTER (PREIMAGE (SND o f) s)) o f') sums
       prob bern
       (BIGUNION (IMAGE ($INTER (PREIMAGE (SND o f) s) o f') UNIV)) /\
       prob bern o (($INTER (PREIMAGE (SND o f) s)) o f') sums prob bern s`
   >- PROVE_TAC [SUM_UNIQ]
   >> CONJ_TAC
   >- (MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV, o_THM]
       >- PROVE_TAC [IN_MEASURABLE, EVENTS_INTER, PROB_SPACE_BERN,
                     EVENTS_BERN_PREFIX_SET, IN_UNIV, EVENTS_BERN_EMPTY]
       >> Q.PAT_X_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m`, `n`])
       >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
       >> PROVE_TAC [])
   >> Know `(\n. (prob bern o f') n * prob bern s) sums prob bern s`
   >- (Suff `(\n. prob bern s * (prob bern o f') n) sums (prob bern s * 1)`
       >- (RW_TAC real_ss [o_THM]
           >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
           >> PROVE_TAC [])
       >> MATCH_MP_TAC SER_CMUL
       >> Suff `prob bern o f' sums prob bern (BIGUNION (IMAGE prefix_set c))`
       >- PROVE_TAC [PROB_BERN_PREFIX_COVER]
       >> MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV]
       >> PROVE_TAC [EVENTS_BERN_EMPTY, EVENTS_BERN_PREFIX_SET])
   >> Suff
      `(\n. (prob bern o f') n * prob bern s) =
       prob bern o $INTER (PREIMAGE (SND o f) s) o f'`
   >- RW_TAC std_ss []
   >> FUN_EQ_TAC
   >> RW_TAC std_ss [o_THM]
   >> POP_ASSUM (MP_TAC o Q.SPEC `x`)
   >> STRIP_TAC
   >- RW_TAC real_ss [INTER_EMPTY, PROB_BERN_EMPTY]
   >> ONCE_REWRITE_TAC [INTER_COMM]
   >> Know
      `f' x INTER PREIMAGE (SND o f) s =
       f' x INTER PREIMAGE (sdrop (LENGTH x')) s`
   >- (RW_TAC std_ss [EXTENSION, IN_INTER, IN_PREIMAGE, o_THM]
       >> Q.PAT_X_ASSUM `!l s. P l s /\ Q l s ==> R l s`
          (MP_TAC o Q.SPECL [`x'`, `x''`])
       >> RW_TAC std_ss []
       >> PROVE_TAC [SND])
   >> Rewr
   >> RW_TAC std_ss [PROB_BERN_PREFIX_SET_INTER_SDROP, PREIMAGE_ALT]);

val IN_MEASURABLE_BERN_UNIV = store_thm
  ("IN_MEASURABLE_BERN_UNIV",
   ``!f. f IN measurable (p_space bern, events bern) (UNIV, UNIV) =
         f IN (p_space bern -> UNIV) /\ !s. PREIMAGE f s IN events bern``,
   GEN_TAC
   >> REWRITE_TAC [REWRITE_RULE [SIGMA_ALGEBRA_BERN, space_def, subsets_def]
                                (ISPECL [``(p_space bern, events bern)``, ``(univ(:'a), univ(:'a set))``]
                                        IN_MEASURABLE)]
   >> EQ_TAC
   >- RW_TAC std_ss [IN_UNIV, SPACE_BERN, SPACE_PROB_ALGEBRA, INTER_UNIV]
   >> RW_TAC std_ss [SPACE_BERN, SPACE_PROB_ALGEBRA, INTER_UNIV]
   >> REWRITE_TAC [UNIV_SIGMA_ALGEBRA]);

val PROB_PRESERVING_BERN = store_thm (
   "PROB_PRESERVING_BERN",
   ``!f. f IN prob_preserving bern bern =
         f IN measurable (p_space bern, events bern) (p_space bern, events bern) /\
        !s. s IN events bern ==> (prob bern (PREIMAGE f s) = prob bern s)``,
   REWRITE_TAC [MEASURABLE_PREMEASURABLE_BERN]
   >> GEN_TAC
   >> RW_TAC std_ss [GSPECIFICATION, ISPECL [``bern``, ``bern``] PROB_PRESERVING]
   >> REWRITE_TAC [MEASURE_SPACE_BERN]
   >> EQ_TAC (* 2 sub-goals here *)
   >> RW_TAC std_ss [SPACE_BERN, SPACE_PROB_ALGEBRA, INTER_UNIV]);

val INDEP_FN_STRONG = store_thm
  ("INDEP_FN_STRONG", ``!f. f IN indep_fn ==> f IN indep_function bern``,
   RW_TAC std_ss [indep_fn_def, indep_function_def, GSPECIFICATION,
                  indep_families_def, IN_IMAGE, IN_UNIV]
   >> REWRITE_TAC [indep_def]
   >> STRONG_CONJ_TAC >- PROVE_TAC [IN_MEASURABLE_BERN_UNIV]
   >> STRIP_TAC
   >> STRONG_CONJ_TAC >- PROVE_TAC [IN_MEASURABLE_BERN_BERN]
   >> STRIP_TAC
   >> Suff
      `prob bern (PREIMAGE (FST o f) x) * prob bern (PREIMAGE (SND o f) x') =
       prob bern ((PREIMAGE (FST o f) x INTER PREIMAGE (SND o f) x') INTER
                  BIGUNION (IMAGE prefix_set c))`
   >- (MP_TAC (Q.SPEC `c` PROB_BERN_PREFIX_COVER_INTER)
       >> ASM_REWRITE_TAC []
       >> RW_TAC std_ss [EVENTS_INTER, PROB_SPACE_BERN])
   >> RW_TAC std_ss [INTER_BIGUNION, IMAGE_IMAGE]
   >> MP_TAC (Q.ISPEC `IMAGE prefix_set c` COUNTABLE_DISJOINT_ENUM)
   >> Know
      `countable (IMAGE prefix_set c) /\
       !s t.
         s IN IMAGE prefix_set c /\ t IN IMAGE prefix_set c /\ ~(s = t) ==>
         DISJOINT s t`
   >- (CONJ_TAC >- RW_TAC std_ss [image_countable, COUNTABLE_BOOL_LIST]
       >> RW_TAC std_ss [IN_IMAGE, o_THM]
       >> MP_TAC
          (Q.SPECL [`c`, `prefix_set x''`, `prefix_set x'''`]
           PREFIX_COVER_DISJOINT)
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [IN_IMAGE, DISJOINT_DEF, IN_INTER, EXTENSION,
                         NOT_IN_EMPTY]
       >> PROVE_TAC [])
   >> DISCH_THEN (fn th => DISCH_THEN (fn ith => MP_TAC (MP ith th)))
   >> STRIP_TAC
   >> RW_TAC std_ss []
   >> Know
      `BIGUNION
       (IMAGE
        ($INTER (PREIMAGE (FST o f) x INTER PREIMAGE (SND o f) x') o
         prefix_set) c) =
       BIGUNION
       (IMAGE
        (($INTER (PREIMAGE (FST o f) x INTER PREIMAGE (SND o f) x')) o f')
        UNIV)`
   >- (Q.PAT_X_ASSUM `X = Y` MP_TAC
       >> ONCE_REWRITE_TAC [EXTENSION]
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_INTER, o_THM, IN_UNIV]
       >> PROVE_TAC [])
   >> Rewr
   >> Suff
      `prob bern o
       (($INTER (PREIMAGE (FST o f) x INTER PREIMAGE (SND o f) x')) o f') sums
       prob bern
       (BIGUNION
        (IMAGE
         ($INTER (PREIMAGE (FST o f) x INTER PREIMAGE (SND o f) x') o f')
         UNIV)) /\
       prob bern o
       (($INTER (PREIMAGE (FST o f) x INTER PREIMAGE (SND o f) x')) o f') sums
       (prob bern (PREIMAGE (FST o f) x) * prob bern (PREIMAGE (SND o f) x'))`
   >- PROVE_TAC [SUM_UNIQ]
   >> Q.PAT_X_ASSUM `f' IN X` MP_TAC
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INSERT, IN_IMAGE]
   >- (MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV, o_THM]
       >- PROVE_TAC [IN_MEASURABLE, EVENTS_INTER, PROB_SPACE_BERN,
                     EVENTS_BERN_PREFIX_SET, IN_UNIV, EVENTS_BERN_EMPTY]
       >> Q.PAT_X_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m`, `n`])
       >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
       >> PROVE_TAC [])
   >> Know
      `(\n. (prob bern o $INTER (PREIMAGE (FST o f) x) o f') n
        * prob bern (PREIMAGE (SND o f) x')) sums
       (prob bern (PREIMAGE (FST o f) x) * prob bern (PREIMAGE (SND o f) x'))`
   >- (ONCE_REWRITE_TAC [REAL_MUL_SYM]
       >> MATCH_MP_TAC SER_CMUL
       >> Know
          `prob bern (PREIMAGE (FST o f) x INTER BIGUNION (IMAGE prefix_set c))
           =
           prob bern (PREIMAGE (FST o f) x)`
       >- (MATCH_MP_TAC PROB_ONE_INTER
           >> PROVE_TAC [PROB_SPACE_BERN, prefix_cover_def, IN_MEASURABLE,
                         IN_UNIV, EVENTS_BERN_PREFIX_COVER])
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
       >> MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV, o_THM] >|
       [PROVE_TAC [EVENTS_INTER, PROB_SPACE_BERN, EVENTS_BERN_EMPTY,
                   IN_MEASURABLE, IN_UNIV, EVENTS_BERN_PREFIX_SET],
        Q.PAT_X_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m`, `n`])
        >> RW_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_INTER, DISJOINT_DEF]
        >> PROVE_TAC [],
        RW_TAC std_ss [GSYM IMAGE_IMAGE, GSYM INTER_BIGUNION]])
   >> Suff
      `(\n.
         (prob bern o $INTER (PREIMAGE (FST o f) x) o f') n *
         prob bern (PREIMAGE (SND o f) x')) =
       prob bern o $INTER (PREIMAGE (FST o f) x INTER PREIMAGE (SND o f) x') o
       f'`
   >- RW_TAC std_ss []
   >> FUN_EQ_TAC
   >> RW_TAC std_ss [o_THM]
   >> Know
      `!p q r : (num -> bool) -> bool.
         (p INTER q) INTER r = (p INTER r) INTER q`
   >- (KILL_TAC
       >> PSET_TAC [EXTENSION]
       >> PROVE_TAC [])
   >> Rewr'
   >> POP_ASSUM (fn th => ASSUME_TAC th >> MP_TAC (Q.SPEC `x''` th))
   >> STRIP_TAC
   >- RW_TAC real_ss [INTER_EMPTY, PROB_BERN_EMPTY]
   >> Know
      `PREIMAGE (FST o f) x INTER f' x'' =
       if FST (f (prefix_seq x''')) IN x then f' x'' else {}`
   >- (REWRITE_TAC [EXTENSION]
       >> STRIP_TAC
       >> Q.PAT_X_ASSUM `!l s. P l s /\ Q l s ==> R l s`
          (MP_TAC o Q.SPECL [`x'''`, `x''''`])
       >> RW_TAC std_ss [IN_PREIMAGE, IN_INTER, IN_UNIV, o_THM,
                         NOT_IN_EMPTY]
       >> PROVE_TAC [FST])
   >> Rewr
   >> RW_TAC real_ss [PROB_BERN_EMPTY, INTER_EMPTY]
   >> Know
      `prefix_set x''' INTER PREIMAGE (SND o f) x' =
       prefix_set x''' INTER PREIMAGE (sdrop (LENGTH x''')) x'`
   >- (REWRITE_TAC [EXTENSION]
       >> STRIP_TAC
       >> Q.PAT_X_ASSUM `!l s. P l s /\ Q l s ==> R l s`
          (MP_TAC o Q.SPECL [`x'''`, `x''''`])
       >> RW_TAC std_ss [IN_PREIMAGE, IN_INTER, IN_UNIV, o_THM,
                         NOT_IN_EMPTY]
       >> PROVE_TAC [FST, SND])
   >> RW_TAC std_ss [PROB_BERN_PREFIX_SET_INTER_SDROP, PREIMAGE_ALT]
   >> REWRITE_TAC [GSYM PREIMAGE_ALT]
   >> Suff `prob bern (PREIMAGE (SND o f) x') = prob bern x'`
   >- RW_TAC std_ss []
   >> NTAC 4 (POP_ASSUM K_TAC)
   >> MP_TAC (Q.SPEC `f` INDEP_FN_PROB_PRESERVING)
   >> Know `f IN indep_fn`
   >- (RW_TAC std_ss [indep_fn_def, GSPECIFICATION]
       >> Q.EXISTS_TAC `c`
       >> RW_TAC std_ss [])
   >> RW_TAC std_ss []
   >> PROVE_TAC [PROB_PRESERVING_BERN]);

val INDEP_FN_UNIT = store_thm
  ("INDEP_FN_UNIT", ``!x. UNIT x IN indep_fn``,
   BasicProvers.NORM_TAC std_ss
   [indep_fn_def, GSPECIFICATION, FST_o_UNIT, SND_o_UNIT,
    IN_MEASURABLE, PREIMAGE_I, PREIMAGE_K, EVENTS_BERN_BASIC, I_THM,
    SIGMA_ALGEBRA_BERN, UNIV_SIGMA_ALGEBRA, IN_FUNSET, space_def, subsets_def,
    SPACE_BERN, SPACE_PROB_ALGEBRA, INTER_UNIV, PREIMAGE_ALT, IN_UNIV]
   >- ( RW_TAC std_ss [range_def, UNIT_DEF, o_ABS_R] \\
        Suff `IMAGE (\s. x) univ(:num set) = {x}`
        >- RW_TAC std_ss [COUNTABLE_SING] \\
        REWRITE_TAC [EXTENSION, IN_SING] \\
        GEN_TAC >> REWRITE_TAC [IN_IMAGE, IN_UNIV] )
   >> Q.EXISTS_TAC `{[]}`
   >> RW_TAC std_ss [IN_SING, prefix_cover_def, IMAGE_INSERT, IMAGE_EMPTY,
                     prefix_set_def, BIGUNION_INSERT, BIGUNION_EMPTY,
                     UNION_UNIV, PROB_BERN_BASIC]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [prefix_set_def, LENGTH, sdrop_def, I_THM, UNIT_DEF]);

val INDEP_FN_SDEST = store_thm
  ("INDEP_FN_SDEST",
   ``sdest IN indep_fn``,
   RW_TAC bool_ss [indep_fn_def, GSPECIFICATION, FST_o_SDEST, SND_o_SDEST,
                   IN_MEASURABLE, PREIMAGE_ALT, EVENTS_BERN_STL, EVENTS_BERN_SHD,
                   COUNTABLE_BOOL, UNIV_SIGMA_ALGEBRA, SIGMA_ALGEBRA_BERN,
                   space_def, subsets_def, SPACE_BERN_UNIV, IN_FUNSET, IN_UNIV, INTER_UNIV]
   >> Q.EXISTS_TAC `{[T]; [F]}`
   >> RW_TAC bool_ss [IN_INSERT, NOT_IN_EMPTY, prefix_cover_def,
                      IMAGE_INSERT, IMAGE_EMPTY, BIGUNION_INSERT,
                      BIGUNION_EMPTY, prefix_set_def, UNION_EMPTY] (* 5 goals here *)
   >> REPEAT (POP_ASSUM MP_TAC)
   >> RW_TAC bool_ss [IS_PREFIX, prefix_set_def, GSYM PREIMAGE_ALT,
                      PREIMAGE_UNIV, INTER_UNIV, prefix_seq_def, sdest_def,
                      SHD_SCONS, STL_SCONS, IN_HALFSPACE, LENGTH, sdrop_def,
                      I_o_ID, HALFSPACE_T_UNION_F, PROB_BERN_UNIV, FST]);

Theorem INDEP_FN_NONEXAMPLE:
  (\s. (shd s = shd (stl s), stl s)) NOTIN indep_fn
Proof
   RW_TAC std_ss [indep_fn_def, GSPECIFICATION, o_DEF]
   >> STRONG_DISJ_TAC
   >> STRONG_DISJ_TAC
   >> STRONG_DISJ_TAC
   >> STRIP_TAC
   >> STRONG_DISJ_TAC
   >> REPEAT (POP_ASSUM MP_TAC)
   >> RW_TAC std_ss [IN_MEASURABLE, prefix_cover_def, IN_UNIV]
   >> MP_TAC (Q.ISPEC `c : bool list -> bool` SET_CASES)
   >> RW_TAC std_ss []
   >- (RW_TAC std_ss []
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [IMAGE_EMPTY, BIGUNION_EMPTY, PROB_BERN_EMPTY]
       >> Suff `F` >- PROVE_TAC []
       >> POP_ASSUM MP_TAC
       >> REAL_ARITH_TAC)
   >> Cases_on `x`
   >- (Q.EXISTS_TAC `[]`
       >> Q.EXISTS_TAC `scons T (scons F s)`
       >> RW_TAC std_ss [IN_INSERT, prefix_set_def, IN_UNIV, STL_SCONS,
                         sdrop_def, LENGTH, I_THM, SCONS_EQ])
   >> reverse (Cases_on `t'`)
   >- (Q.EXISTS_TAC `h :: h' :: t''`
       >> MP_TAC
          (Q.SPECL [`h' :: t''`, `LENGTH (t'' : bool list)`]
           PREFIX_SET_UNFIXED_SDROP)
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `scons h s`
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [IN_INSERT, PREFIX_SET_SCONS, STL_SCONS, sdrop_def,
                         o_THM, LENGTH])
   >> Q.EXISTS_TAC `[h]`
   >> Q.EXISTS_TAC `scons h (scons (~shd (stl (prefix_seq [h]))) s)`
   >> RW_TAC std_ss [IN_INSERT, PREFIX_SET_SCONS, prefix_set_def, IN_UNIV,
                     STL_SCONS, SHD_SCONS, prefix_seq_def]
   >> pop_assum mp_tac >> Cases_on `h`
   >> RW_TAC std_ss [EQ_IMP_THM]
QED

val INDEP_FN_PSUBSET = store_thm
  ("INDEP_FN_PSUBSET",
   ``indep_fn
     PSUBSET
     (indep_function bern : ((num -> bool) -> bool # (num -> bool)) -> bool)``,
   RW_TAC std_ss [PSUBSET_DEF, SUBSET_DEF, INDEP_FN_STRONG, EXTENSION]
   >> Q.EXISTS_TAC `(\s. (shd s = shd (stl s), stl s))`
   >> RW_TAC std_ss [INDEP_FUNCTION_BERN_EXAMPLE, INDEP_FN_NONEXAMPLE]);

val PREFIX_COVER_NONEMPTY = store_thm
  ("PREFIX_COVER_NONEMPTY",
   ``!c. prefix_cover c ==> ~(c = {})``,
   RW_TAC std_ss [prefix_cover_def]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `prob bern X = 1` MP_TAC
   >> RW_TAC std_ss [IMAGE_EMPTY, BIGUNION_EMPTY, PROB_BERN_BASIC]
   >> REAL_ARITH_TAC);

val PREFIX_COVER_APPEND = store_thm
  ("PREFIX_COVER_APPEND",
   ``!c cf.
       prefix_cover c /\ (!l. prefix_cover (cf l)) ==>
       prefix_cover (BIGUNION (IMAGE (\l. IMAGE (APPEND l) (cf l)) c))``,
   REWRITE_TAC [prefix_cover_def]
   >> NTAC 3 STRIP_TAC
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_IMAGE]
       >> Cases_on `l = l'` >|
       [RW_TAC std_ss [IS_PREFIX_APPENDS]
        >> PROVE_TAC [],
        PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2]])
   >> RW_TAC std_ss []
   >> Know
   `BIGUNION
    (IMAGE prefix_set (BIGUNION (IMAGE (\l. IMAGE (APPEND l) (cf l)) c))) =
    BIGUNION (IMAGE (\l. BIGUNION (IMAGE (prefix_set o APPEND l) (cf l))) c)`
   >- (ONCE_REWRITE_TAC [EXTENSION]
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_IMAGE, o_THM]
       >> PROVE_TAC [])
   >> Rewr
   >> MP_TAC
      (Q.ISPEC
       `IMAGE (\l. BIGUNION (IMAGE (prefix_set o APPEND l) (cf l))) c`
       COUNTABLE_DISJOINT_ENUM)
   >> RW_TAC std_ss [image_countable, COUNTABLE_BOOL_LIST]
   >> POP_ASSUM MP_TAC
   >> Know
   `!s t.
      s IN IMAGE (\l. BIGUNION (IMAGE (prefix_set o APPEND l) (cf l))) c /\
      t IN IMAGE (\l. BIGUNION (IMAGE (prefix_set o APPEND l) (cf l))) c /\
      ~(s = t) ==>
      DISJOINT s t`
   >- (RW_TAC std_ss [IN_IMAGE, IN_BIGUNION_IMAGE, IN_DISJOINT]
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE, o_THM]
       >> CCONTR_TAC
       >> POP_ASSUM (MP_TAC o REWRITE_RULE [DE_MORGAN_THM])
       >> DISCH_THEN (MP_TAC o CONV_RULE (DEPTH_CONV NOT_FORALL_CONV))
       >> STRIP_TAC
       >> NTAC 2 (POP_ASSUM MP_TAC)
       >> PURE_REWRITE_TAC [DE_MORGAN_THM, NOT_CLAUSES]
       >> STRIP_TAC
       >> STRIP_TAC
       >> Know `l = l'`
       >- (MP_TAC
           (Q.SPECL [`APPEND l x'`, `APPEND l' x''`] PREFIX_SET_SUBSET)
           >> RW_TAC std_ss [PREFIX_SET_PREFIX_SUBSET, IN_DISJOINT]
           >> PROVE_TAC [IS_PREFIX_APPEND2, IS_PREFIX_APPEND1])
       >> STRIP_TAC
       >> RW_TAC std_ss [])
   >> Rewr
   >> RW_TAC std_ss [IN_UNIV, IN_FUNSET, IN_INSERT]
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!x. P x \/ Q x` MP_TAC
   >> REWRITE_TAC [IN_IMAGE]
   >> DISCH_THEN
      (MP_TAC o CONV_RULE (DEPTH_CONV RIGHT_OR_EXISTS_CONV THENC SKOLEM_CONV))
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss []
   >> Suff `prob bern o f sums 1`
   >- (Suff `prob bern o f sums (prob bern (BIGUNION (IMAGE f UNIV)))`
       >- PROVE_TAC [SUM_UNIQ]
       >> MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV]
       >> POP_ASSUM (MP_TAC o Q.SPEC `x`)
       >> STRIP_TAC >- RW_TAC std_ss [EVENTS_BERN_EMPTY]
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       >> RW_TAC std_ss [PROB_SPACE_BERN, SUBSET_DEF, image_countable,
                         COUNTABLE_BOOL_LIST, IN_IMAGE, o_THM]
       >> RW_TAC std_ss [EVENTS_BERN_PREFIX_SET])
   >> Know
      `prob bern o (\n. if f n = {} then {} else prefix_set (x' n)) sums
       prob bern (BIGUNION (IMAGE prefix_set c))`
   >- (MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
       >> (RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV]
           >> RW_TAC std_ss [EVENTS_BERN_EMPTY, EVENTS_BERN_PREFIX_SET,
                             DISJOINT_EMPTY]) >|
       [CCONTR_TAC
        >> Know `x' m = x' n`
        >- (MP_TAC (Q.SPECL [`x' (m:num)`, `x' (n:num)`] PREFIX_SET_SUBSET)
            >> RW_TAC std_ss [PREFIX_SET_PREFIX_SUBSET]
            >> PROVE_TAC [])
        >> STRIP_TAC
        >> Know `f m = f n` >- PROVE_TAC []
        >> STRIP_TAC
        >> Q.PAT_X_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m`, `n`])
        >> RW_TAC std_ss [GSYM DISJOINT_EMPTY_REFL],
        ONCE_REWRITE_TAC [EXTENSION]
        >> Suff `!s. s IN c ==> ?n. ~(f n = {}) /\ (x' n = s)`
        >- (RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV]
            >> EQ_TAC >- PROVE_TAC []
            >> BasicProvers.NORM_TAC std_ss [NOT_IN_EMPTY]
            >> PROVE_TAC [])
        >> RW_TAC std_ss []
        >> Q.PAT_X_ASSUM `X = Y` (MP_TAC o ONCE_REWRITE_RULE [EXTENSION])
        >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, o_THM]
        >> MP_TAC (Q.ISPEC `(cf : bool list -> bool list -> bool) s`
                   SET_CASES)
        >> STRIP_TAC
        >- (Suff `F` >- PROVE_TAC []
            >> POP_ASSUM MP_TAC
            >> RW_TAC std_ss []
            >> MATCH_MP_TAC PREFIX_COVER_NONEMPTY
            >> RW_TAC std_ss [prefix_cover_def]
            >> PROVE_TAC [])
        >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `prefix_seq (APPEND s x)`)
        >> Know
        `?x'.
           x' IN c /\
           ?x''.
             x'' IN cf x' /\
             prefix_seq (APPEND s x) IN prefix_set (APPEND x' x'')`
        >- PROVE_TAC [IN_INSERT, PREFIX_SEQ]
        >> Rewr
        >> RW_TAC std_ss []
        >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x''`)
        >> Know `~(f x'' = {})` >- PROVE_TAC [EXTENSION, NOT_IN_EMPTY]
        >> RW_TAC std_ss []
        >> Q.EXISTS_TAC `x''`
        >> RW_TAC std_ss []
        >> Q.PAT_X_ASSUM `X = Y`
           (MP_TAC o Q.SPEC `prefix_seq (APPEND s x)` o
            ONCE_REWRITE_RULE [EXTENSION])
        >> RW_TAC std_ss [IN_BIGUNION_IMAGE, o_THM]
        >> MP_TAC
           (Q.SPECL [`APPEND s x`, `APPEND (x' (x'':num)) x'''`]
            PREFIX_SET_SUBSET)
        >> RW_TAC std_ss [IN_DISJOINT, PREFIX_SET_PREFIX_SUBSET] >|
        [Suff `F` >- PROVE_TAC []
         >> POP_ASSUM (MP_TAC o Q.SPEC `prefix_seq (APPEND s x)`)
         >> POP_ASSUM (REWRITE_TAC o wrap)
         >> PROVE_TAC [PREFIX_SEQ],
         PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2],
         PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2]]])
   >> Suff
      `prob bern o (\n. (if f n = {} then {} else prefix_set (x' n))) =
       prob bern o f`
   >- RW_TAC std_ss []
   >> FUN_EQ_TAC
   >> RW_TAC std_ss [o_THM]
   >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!l. P l /\ Q l` (MP_TAC o Q.SPEC `x' (x:num)`)
   >> KILL_TAC
   >> Q.SPEC_TAC (`cf (x' x)`, `c`)
   >> RW_TAC std_ss []
   >> Q.SPEC_TAC (`x' x`, `l`)
   >> Induct >- RW_TAC std_ss' [prefix_set_def, PROB_BERN_UNIV, o_DEF, APPEND]
   >> RW_TAC std_ss [prefix_set_def, APPEND]
   >> Know
      `BIGUNION (IMAGE (prefix_set o APPEND (h::l)) c) =
       halfspace h INTER BIGUNION (IMAGE (prefix_set o APPEND l) c) o stl`
   >- (ONCE_REWRITE_TAC [EXTENSION]
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_INTER, IN_HALFSPACE, IN_o,
                         o_THM, APPEND, prefix_set_def]
       >> PROVE_TAC [])
   >> Rewr
   >> Suff `BIGUNION (IMAGE (prefix_set o APPEND l) c) IN events bern`
   >- RW_TAC std_ss [EVENTS_BERN_PREFIX_SET, PROB_BERN_STL_HALFSPACE]
   >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_BOOL_LIST, SUBSET_DEF, IN_IMAGE,
                     image_countable, o_THM]
   >> RW_TAC std_ss [EVENTS_BERN_PREFIX_SET]);

Theorem INDEP_FN_BIND :
    !f g. f IN indep_fn /\ (!x. g x IN indep_fn) ==> BIND f g IN indep_fn
Proof
  RW_TAC std_ss [indep_fn_def, GSPECIFICATION] >| (* 4 goals here *)
  [ (* goal 1 (of 4) *)
    MATCH_MP_TAC COUNTABLE_SUBSET
    >> Q.EXISTS_TAC
       `BIGUNION (IMAGE (range o (\x. FST o g x)) (range (FST o f)))`
    >> CONJ_TAC
    >- MATCH_ACCEPT_TAC
       (INST_TYPE [alpha |-> ``:num -> bool``, beta |-> alpha, gamma |-> beta]
        RANGE_BIND)
    >> MATCH_MP_TAC COUNTABLE_BIGUNION
    >> CONJ_TAC >- RW_TAC std_ss [image_countable]
    >> RW_TAC std_ss [IN_IMAGE, o_THM]
    >> RW_TAC std_ss [],
    (* goal 2 (of 4) *)
    RW_TAC bool_ss [BIND_DEF, o_ASSOC]
    >> MATCH_MP_TAC MEASURABLE_COMP_STRONGER
    >> Q.EXISTS_TAC `sigma (UNIV CROSS (p_space bern)) (prod_sets UNIV (events bern))`
    >> Q.EXISTS_TAC `range (FST o f) CROSS UNIV`
    >> CONJ_TAC
    >- ( ASSUME_TAC (ISPECL [``(p_space bern, events bern)``,
                             ``(univ(:'a), univ(:'a set))``, ``(p_space bern, events bern)``]
                            MEASURABLE_PROD_SIGMA) \\
         POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [space_def, subsets_def])) \\
         POP_ASSUM MATCH_MP_TAC \\
         rw [SIGMA_ALGEBRA_BERN, subset_class_def, SPACE_BERN_UNIV] )
    >> REWRITE_TAC [UNIV_SIGMA_ALGEBRA]
    >> CONJ_TAC
    >- RW_TAC std_ss [SUBSET_DEF, IN_CROSS, IN_UNIV, range_def, IN_IMAGE, o_THM,
                      space_def, IN_FUNSET]
    >> CONJ_TAC
    >- ( RW_TAC std_ss [SUBSET_DEF, IN_CROSS, IN_UNIV, range_def, IN_IMAGE, o_THM,
                        space_def, IN_FUNSET] \\
         Q.EXISTS_TAC `x'` >> RW_TAC std_ss [] )
    >> Q.PAT_X_ASSUM `countable X` MP_TAC
    >> Know `!x. FST o g x IN measurable (p_space bern, events bern) (univ(:'b), univ(:'b set))`
    >- PROVE_TAC []
    >> KILL_TAC
    >> RW_TAC std_ss [COUNTABLE_ENUM, RANGE_NONEMPTY]
    >> Know
    `PREIMAGE (FST o UNCURRY g) s INTER (range (FST o f) CROSS UNIV) =
     BIGUNION (IMAGE (\n. {f' n} CROSS (PREIMAGE (FST o g (f' n)) s)) UNIV)`
    >- (Q.PAT_X_ASSUM `range (FST o f) = IMAGE f' UNIV` MP_TAC
        >> KILL_TAC
        >> ONCE_REWRITE_TAC [EXTENSION]
        >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_INTER, o_THM,
                          UNCURRY, IN_SING, IN_CROSS, IN_UNIV, range_def,
                          IN_IMAGE]
        >> PROVE_TAC [FST, SND])
    >> Rewr
    >> MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
    >> RW_TAC std_ss [COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV] (* 2 sub-goals here *)
    >- ( MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
         KILL_TAC \\
         RW_TAC std_ss [subset_class_def, SPACE_BERN_UNIV, GSYM CROSS_UNIV, SUBSET_UNIV] )
    >> MATCH_MP_TAC IN_SIGMA
    >> RW_TAC std_ss [prod_sets_def, GSPECIFICATION, IN_UNIV]
    >> Q.EXISTS_TAC `({f' n}, PREIMAGE (FST o g (f' n)) s)`
    >> RW_TAC std_ss []
    >> POP_ASSUM K_TAC
    >> POP_ASSUM MP_TAC
    >> POP_ASSUM (MP_TAC o Q.SPEC `f' (n:num)`)
    >> RW_TAC std_ss [IN_MEASURABLE, IN_UNIV, subsets_def, space_def,
                      SPACE_BERN_UNIV, INTER_UNIV, IN_FUNSET],
    (* goal 3 (of 4) *)
    RW_TAC bool_ss [BIND_DEF, o_ASSOC]
    >> MATCH_MP_TAC MEASURABLE_COMP_STRONGER
    >> Q.EXISTS_TAC `sigma (UNIV CROSS (p_space bern)) (prod_sets UNIV (events bern))`
    >> Q.EXISTS_TAC `range (FST o f) CROSS UNIV`
    >> CONJ_TAC
    >- ( ASSUME_TAC (ISPECL [``(p_space bern, events bern)``,
                             ``(univ(:'a), univ(:'a set))``, ``(p_space bern, events bern)``]
                            MEASURABLE_PROD_SIGMA) \\
         POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [space_def, subsets_def])) \\
         POP_ASSUM MATCH_MP_TAC \\
         rw [SIGMA_ALGEBRA_BERN, subset_class_def, SPACE_BERN_UNIV] )
    >> REWRITE_TAC [SIGMA_ALGEBRA_BERN]
    >> CONJ_TAC
    >- ( RW_TAC std_ss [SUBSET_DEF, IN_CROSS, IN_UNIV, range_def, IN_IMAGE, o_THM,
                        space_def, IN_FUNSET]
         >> REWRITE_TAC [SPACE_BERN_UNIV, IN_UNIV] )
    >> CONJ_TAC
    >- ( RW_TAC std_ss [SUBSET_DEF, IN_CROSS, IN_UNIV, range_def, IN_IMAGE, o_THM,
                        space_def, IN_FUNSET] \\
         Q.EXISTS_TAC `x'` >> RW_TAC std_ss [] )
    >> Q.PAT_X_ASSUM `countable X` MP_TAC
    >> Know `!x. SND o g x IN measurable (p_space bern, events bern) (p_space bern, events bern)`
    >- ( RW_TAC std_ss []
         >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
         >> RW_TAC std_ss [] )
    >> POP_ASSUM MP_TAC
    >> KILL_TAC
    >> RW_TAC std_ss [COUNTABLE_ENUM, RANGE_NONEMPTY]
    >> Know
    `PREIMAGE (SND o UNCURRY g) s INTER (range (FST o f) CROSS UNIV) =
     BIGUNION (IMAGE (\n. {f' n} CROSS (PREIMAGE (SND o g (f' n)) s)) UNIV)`
    >- (Q.PAT_X_ASSUM `range (FST o f) = IMAGE f' UNIV` MP_TAC
        >> KILL_TAC
        >> ONCE_REWRITE_TAC [EXTENSION]
        >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_INTER, o_THM,
                          UNCURRY, IN_SING, IN_CROSS, IN_UNIV, range_def,
                          IN_IMAGE]
        >> PROVE_TAC [FST, SND])
    >> Rewr
    >> MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
    >> RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA, COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV] (* 2 sub-goals here *)
    >- ( MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
         KILL_TAC \\
         RW_TAC std_ss [subset_class_def, SPACE_BERN_UNIV, GSYM CROSS_UNIV, SUBSET_UNIV] )
    >> MATCH_MP_TAC IN_SIGMA
    >> RW_TAC std_ss [prod_sets_def, GSPECIFICATION, IN_UNIV]
    >> Q.EXISTS_TAC `({f' n}, PREIMAGE (SND o g (f' n)) s)`
    >> RW_TAC std_ss []
    >> POP_ASSUM MP_TAC
    >> POP_ASSUM K_TAC
    >> POP_ASSUM (MP_TAC o Q.SPEC `f' (n:num)`)
    >> RW_TAC std_ss [IN_MEASURABLE, IN_UNIV, subsets_def, space_def,
                      SPACE_BERN_UNIV, INTER_UNIV, IN_FUNSET],
    (* goal 4 (of 4) *)
    POP_ASSUM (MP_TAC o CONV_RULE (REDEPTH_CONV FORALL_AND_CONV))
    >> RW_TAC std_ss []
    >> POP_ASSUM (MP_TAC o CONV_RULE SKOLEM_CONV)
    >> RW_TAC std_ss []
    >> Q.EXISTS_TAC
     `BIGUNION (IMAGE (\l. IMAGE (APPEND l) ((c' o FST o f o prefix_seq) l)) c)`
    >> CONJ_TAC
    >- (MATCH_MP_TAC PREFIX_COVER_APPEND
        >> RW_TAC std_ss [o_THM])
    >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_IMAGE, o_THM, BIND_DEF]
    >> Q.PAT_X_ASSUM `!l s. P l s`
       ((fn th =>
         MP_TAC (Q.SPEC `s` th)
         >> MP_TAC (Q.SPEC `prefix_seq (APPEND l' x)` th)) o Q.SPEC `l'`)
    >> Know `prefix_seq (APPEND l' x) IN prefix_set l' = T`
    >- PROVE_TAC [PREFIX_SET_APPEND, PREFIX_SEQ]
    >> Rewr
    >> Know `s IN prefix_set l' = T`
    >- PROVE_TAC [PREFIX_SET_APPEND]
    >> Rewr
    >> RW_TAC std_ss []
    >> Suff
  `(sdrop (LENGTH l') (prefix_seq (APPEND l' x)) = prefix_seq x) /\
   (sdrop (LENGTH (APPEND l' x)) s = sdrop (LENGTH x) (sdrop (LENGTH l') s)) /\
   (sdrop (LENGTH l') s IN prefix_set x)`
    >- RW_TAC std_ss []
    >> CONJ_TAC
    >- (KILL_TAC
        >> Induct_on `l'` >- RW_TAC std_ss [sdrop_def, LENGTH, APPEND, I_THM]
        >> RW_TAC std_ss [sdrop_def, LENGTH, APPEND, I_THM, prefix_seq_def,
                          o_THM, STL_SCONS])
    >> CONJ_TAC
    >- (KILL_TAC
        >> Q.SPEC_TAC (`s`, `s`)
        >> Induct_on `l'` >- RW_TAC std_ss [sdrop_def, LENGTH, APPEND, I_THM]
        >> RW_TAC std_ss [sdrop_def, LENGTH, APPEND, I_THM, prefix_seq_def,
                          o_THM, STL_SCONS])
    >> Q.PAT_X_ASSUM `s IN X` MP_TAC
    >> KILL_TAC
    >> Q.SPEC_TAC (`s`, `s`)
    >> Induct_on `l'` >- RW_TAC std_ss [sdrop_def, LENGTH, APPEND, I_THM]
    >> RW_TAC std_ss [sdrop_def, LENGTH, APPEND, I_THM, o_THM]
    >> SEQ_CASES_TAC `s`
    >> POP_ASSUM MP_TAC
    >> RW_TAC std_ss [PREFIX_SET_SCONS, STL_SCONS] ]
QED

val INDEP_FN_PROB = store_thm
  ("INDEP_FN_PROB",
   ``!f p q.
       f IN indep_fn /\ q IN events bern ==>
       (prob bern (p o FST o f INTER q o SND o f) =
        prob bern (p o FST o f) * prob bern q)``,
   RW_TAC std_ss []
   >> Know `f IN indep_function bern` >- PROVE_TAC [INDEP_FN_STRONG]
   >> RW_TAC std_ss [indep_function_def, GSPECIFICATION, indep_families_def]
   >> POP_ASSUM
      (MP_TAC o
       Q.SPECL [`p o FST o (f : (num -> bool) -> 'a # (num -> bool))`,
                `q o SND o (f : (num -> bool) -> 'a # (num -> bool))`])
   >> impl_tac
   >- (RW_TAC std_ss [IN_IMAGE, IN_UNIV, PREIMAGE_ALT]
       >> PROVE_TAC [])
   >> RW_TAC std_ss [indep_def]
   >> POP_ASSUM K_TAC
   >> Suff `prob bern (q o SND o f) = prob bern q` >- RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `f` INDEP_FN_PROB_PRESERVING)
   >> RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION, PREIMAGE_ALT]
   >> POP_ASSUM MP_TAC
   >> REWRITE_TAC [SPACE_BERN_UNIV, INTER_UNIV]
   >> RW_TAC std_ss []);

val INDEP_FN_FST_EVENTS = store_thm
  ("INDEP_FN_FST_EVENTS",
   ``!f p. f IN indep_fn ==> (p o FST o f) IN events bern``,
   RW_TAC std_ss [indep_fn_def, GSPECIFICATION]
   >> Q.PAT_X_ASSUM `FST o f IN X` MP_TAC
   >> RW_TAC std_ss [IN_MEASURABLE, IN_UNIV, PREIMAGE_ALT]
   >> POP_ASSUM MP_TAC
   >> REWRITE_TAC [subsets_def, IN_UNIV, space_def, SPACE_BERN_UNIV, INTER_UNIV]
   >> RW_TAC std_ss []);

val INDEP_FN_FST_EVENTS' = store_thm
  ("INDEP_FN_FST_EVENTS'",
   ``!f p. f IN indep_fn ==> ((p o FST) o f) IN events bern``,
   RW_TAC std_ss [INDEP_FN_FST_EVENTS, GSYM o_ASSOC]);

val INDEP_FN_SND_EVENTS = store_thm
  ("INDEP_FN_SND_EVENTS",
   ``!f q.
       f IN indep_fn /\ q IN events bern ==> (q o SND o f) IN events bern``,
   RW_TAC std_ss [indep_fn_def, GSPECIFICATION]
   >> Q.PAT_X_ASSUM `SND o f IN X` MP_TAC
   >> RW_TAC std_ss [IN_MEASURABLE, PREIMAGE_ALT]
   >> POP_ASSUM MP_TAC
   >> REWRITE_TAC [subsets_def, IN_UNIV, space_def, SPACE_BERN_UNIV, INTER_UNIV]
   >> RW_TAC std_ss []);

val INDEP_FN_SND_EVENTS' = store_thm
  ("INDEP_FN_SND_EVENTS'",
   ``!f q.
       f IN indep_fn /\ q IN events bern ==> ((q o SND) o f) IN events bern``,
   RW_TAC std_ss [INDEP_FN_SND_EVENTS, GSYM o_ASSOC]);

Theorem INDEP_FN_PROB_FST_INSERT:
  !f x xs.
       f IN indep_fn /\ ~(x IN xs) ==>
       (prob bern {s | FST (f s) IN (x INSERT xs)} =
        prob bern {s | FST (f s) = x} + prob bern {s | FST (f s) IN xs})
Proof
   RW_TAC std_ss [IN_INSERT, GUNION]
   >> MATCH_MP_TAC PROB_ADDITIVE
   >> RW_TAC arith_ss [PROB_SPACE_BERN, IN_DISJOINT, GSPECIFICATION] >|
   [Suff `{s | FST (f s) = x} = (\m. m = x) o FST o f`
    >- RW_TAC std_ss [INDEP_FN_FST_EVENTS]
    >> ONCE_REWRITE_TAC [EXTENSION]
    >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM]
    >> RW_TAC std_ss [SPECIFICATION],
    Suff `{s | FST (f s) IN xs} = (\m. m IN xs) o FST o f`
    >- RW_TAC std_ss [INDEP_FN_FST_EVENTS]
    >> ONCE_REWRITE_TAC [EXTENSION]
    >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM]
    >> RW_TAC std_ss [SPECIFICATION]
   ]
QED

val INDEP_FN_PROB_FST_SUC = store_thm
  ("INDEP_FN_PROB_FST_SUC",
   ``!f n.
       f IN indep_fn ==>
       (prob bern {s | FST (f s) < SUC n} =
        prob bern {s | FST (f s) < n} + prob bern {s | FST (f s) = n})``,
   RW_TAC std_ss []
   >> MP_TAC
      (Q.SPECL [`f`, `n`, `count n`]
       (INST_TYPE [alpha |-> numSyntax.num] INDEP_FN_PROB_FST_INSERT))
   >> RW_TAC arith_ss [IN_COUNT, prim_recTheory.LESS_THM, IN_INSERT]
   >> ONCE_REWRITE_TAC [DISJ_COMM]
   >> RW_TAC std_ss []
   >> PROVE_TAC [REAL_ADD_SYM]);

val INDEP_FN_PROB_FST_NOT = store_thm
  ("INDEP_FN_PROB_FST_NOT",
   ``!f n.
         f IN indep_fn ==>
         (prob bern {s | ~FST (f s)} = 1 - prob bern {s | FST (f s)})``,
   RW_TAC std_ss []
   >> Suff
      `({s | ~FST (f s)} = COMPL {s | FST (f s)}) /\
       {s | FST (f s)} IN events bern`
   >- ( RW_TAC std_ss [] \\
        REWRITE_TAC [COMPL_DEF, SYM SPACE_BERN_UNIV] \\
        RW_TAC std_ss [PROB_COMPL, PROB_SPACE_BERN] )
   >> CONJ_TAC
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_COMPL])
   >> Suff `{s | FST (f s)} = I o FST o f`
   >- RW_TAC bool_ss [INDEP_FN_FST_EVENTS]
   >> SET_EQ_TAC
   >> RW_TAC bool_ss [GSPECIFICATION, IN_o]
   >> RW_TAC std_ss [SPECIFICATION, I_THM, o_THM]);

val PROB_BERN_BIND_BOOL_BOOL = store_thm
  ("PROB_BERN_BIND_BOOL_BOOL",
   ``!f g p.
       f IN indep_fn /\ (!x. g x IN indep_fn) /\
       (prob bern (FST o f) = p) ==>
       (prob bern (FST o BIND f g) =
        p * prob bern (FST o g T) + (1 - p) * prob bern (FST o g F))``,
   Strip
   >> Know `FST o BIND f g =
            (I o FST o f INTER (I o FST o g T) o SND o f) UNION
            ($~ o FST o f INTER (I o FST o g F) o SND o f)`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_INTER, IN_UNION]
       >> RW_TAC std_ss [SPECIFICATION, o_DEF, BIND_DEF]
       >> Cases_on `f x`
       >> RW_TAC std_ss [I_THM]
       >> Cases_on `q`
       >> RW_TAC std_ss [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Know `!x. (I o FST o g x) IN events bern`
   >- RW_TAC std_ss [INDEP_FN_FST_EVENTS]
   >> Strip
   >> Know `!x. ((I o FST o g x) o SND o f) IN events bern`
   >- RW_TAC std_ss [INDEP_FN_SND_EVENTS]
   >> Know `!p. (p o FST o f) IN events bern`
   >- RW_TAC std_ss [INDEP_FN_FST_EVENTS]
   >> Strip
   >> (MP_TAC o
       INST_TYPE [(alpha |-> ``:num -> bool``), (beta |-> ``:num -> bool``)] o
       Q.SPECL [`bern`,
                `I o FST o f INTER (I o FST o g T) o SND o f`,
                `$~ o FST o f INTER (I o FST o g F) o SND o f`,
                `I o FST o f INTER (I o FST o g T) o SND o f UNION
                 $~ o FST o f INTER (I o FST o g F) o SND o f`] o
       INST_TYPE [(alpha |-> ``:num -> bool``)])
      PROB_ADDITIVE
   >> impl_tac
   >- (RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_INTER, IN_DISJOINT, IN_INTER,
                      IN_o, o_THM]
       >> RW_TAC std_ss [SPECIFICATION, I_THM]
       >> PROVE_TAC [])
   >> Rewr
   >> Know `!a b c d : real. (a = c) /\ (b = d) ==> (a + b = c + d)`
   >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> Strip >| (* 2 sub-goals here *)
   [(* goal 1 (of 2) *)
    (MP_TAC o
     Q.SPECL [`f`, `I : bool -> bool`,
              `I o (FST : bool # (num -> bool) -> bool) o g T`] o
     INST_TYPE [(alpha |-> bool)])
    INDEP_FN_PROB
    >> RW_TAC std_ss []
    >> RW_TAC std_ss [I_o_ID],
    (* goal 2 (of 2) *)
    (MP_TAC o
     Q.SPECL [`f`, `$~ : bool -> bool`,
              `I o (FST : bool # (num -> bool) -> bool) o g F`] o
     INST_TYPE [(alpha |-> bool)])
    INDEP_FN_PROB
    >> RW_TAC std_ss []
    >> RW_TAC std_ss [I_o_ID]
    >> Know `$~ o FST o f = COMPL (I o FST o f)`
    >- (SET_EQ_TAC
        >> RW_TAC std_ss [IN_COMPL]
        >> RW_TAC std_ss [SPECIFICATION, o_THM, I_THM])
    >> Rewr
    >> REWRITE_TAC [COMPL_DEF, SYM SPACE_BERN_UNIV]
    >> RW_TAC std_ss [PROB_COMPL, PROB_SPACE_BERN] ]);

val INDEP_FN_PROB_WHILE_CUT = store_thm
  ("INDEP_FN_PROB_WHILE_CUT",
   ``!c b n a. (!a. b a IN indep_fn) ==> prob_while_cut c b n a IN indep_fn``,
   RW_TAC std_ss []
   >> Q.SPEC_TAC (`a`, `a`)
   >> Induct_on `n` >- RW_TAC std_ss [prob_while_cut_def, INDEP_FN_UNIT]
   >> RW_TAC std_ss [prob_while_cut_def, INDEP_FN_UNIT, INDEP_FN_BIND]);

val PROB_BERN_BIND_FINITE = store_thm
  ("PROB_BERN_BIND_FINITE",
   ``!p f g c n.
       f IN indep_fn /\ (!a. g a IN indep_fn) /\
       BIJ c (count n) (range (FST o f)) ==>
       (sum (0, n)
        (\m. prob bern ($= (c m) o FST o f) * prob bern (p o FST o g (c m))) =
        prob bern (p o FST o BIND f g))``,
   RW_TAC bool_ss []
   >> Know
      `(p o FST o BIND f g) =
       (p o FST o BIND f g) INTER
       BIGUNION (IMAGE (\m. $= (c m) o FST o f) (count n))`
   >- (Suff `BIGUNION (IMAGE (\m. $= (c m) o FST o f) (count n)) = UNIV`
       >- RW_TAC std_ss [INTER_UNIV]
       >> SET_EQ_TAC
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, IN_o]
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF]
       >> POP_ASSUM
          (MP_TAC o
           Q.SPEC `(FST o (f : (num -> bool) -> 'b # (num -> bool))) x`)
       >> RW_TAC std_ss [ALWAYS_IN_RANGE]
       >> Q.EXISTS_TAC `y`
       >> RW_TAC std_ss []
       >> RW_TAC std_ss [SPECIFICATION])
   >> Rewr'
   >> RW_TAC bool_ss [INTER_BIGUNION, IMAGE_IMAGE]
   >> Know `!a b. a < n /\ b < n /\ ~(a = b) ==> ~(c a = c b)`
   >- (POP_ASSUM MP_TAC
       >> RW_TAC std_ss [BIJ_DEF, INJ_DEF, IN_COUNT]
       >> PROVE_TAC [])
   >> POP_ASSUM K_TAC
   >> Induct_on `n`
   >- RW_TAC std_ss [COUNT_ZERO, sum, IMAGE_EMPTY, BIGUNION_EMPTY,
                     PROB_BERN_EMPTY]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `X ==> Y` MP_TAC
   >> impl_tac >- PROVE_TAC [prim_recTheory.LESS_THM]
   >> RW_TAC bool_ss [sum]
   >> POP_ASSUM K_TAC
   >> RW_TAC bool_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT]
   >> Know
      `prob bern
       (($INTER (p o FST o BIND f g) o (\m. $= (c m) o FST o f)) n UNION
        BIGUNION
        (IMAGE ($INTER (p o FST o BIND f g) o (\m. $= (c m) o FST o f))
         (count n))) =
       prob bern
       (BIGUNION
        (IMAGE ($INTER (p o FST o BIND f g) o (\m. $= (c m) o FST o f))
         (count n))) +
       prob bern
       (($INTER (p o FST o BIND f g) o (\m. $= (c m) o FST o f)) n)`
   >- (MATCH_MP_TAC PROB_ADDITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN, o_THM] >|
       [MATCH_MP_TAC EVENTS_COUNTABLE_UNION
        >> RW_TAC std_ss [PROB_SPACE_BERN, image_countable, COUNTABLE_COUNT,
                          SUBSET_DEF, IN_IMAGE, o_THM]
        >> MATCH_MP_TAC EVENTS_INTER
        >> Q.SPEC_TAC (`$= (c x')`, `q`)
        >> RW_TAC std_ss [PROB_SPACE_BERN]
        >> PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_BIND],
        MATCH_MP_TAC EVENTS_INTER
        >> Q.SPEC_TAC (`$= (c n)`, `q`)
        >> RW_TAC std_ss [PROB_SPACE_BERN]
        >> PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_BIND],
        RW_TAC std_ss [DISJOINT_ALT, IN_BIGUNION_IMAGE, IN_COUNT, IN_INTER,
                       o_THM]
        >> DISJ2_TAC
        >> POP_ASSUM MP_TAC
        >> RW_TAC std_ss [SPECIFICATION, o_THM]
        >> Suff `x' < SUC n /\ n < SUC n /\ ~(x' = n)` >- PROVE_TAC []
        >> DECIDE_TAC,
        PROVE_TAC [UNION_COMM]])
   >> Rewr
   >> Know `!a b c : real. (b = c) ==> (a + b = a + c)` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC arith_ss [o_THM]
   >> Know
      `p o FST o BIND f g INTER $= (c n) o FST o f =
       $= (c n) o FST o f INTER (p o FST o g (c n)) o SND o f`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_INTER]
       >> RW_TAC std_ss [SPECIFICATION, o_THM]
       >> reverse (Cases_on `FST (f x) = c n`) >- PROVE_TAC []
       >> RW_TAC std_ss [BIND_DEF, UNCURRY, o_THM])
   >> Rewr
   >> Suff `(p o FST o g (c n)) IN events bern`
   >- RW_TAC std_ss [INDEP_FN_PROB]
   >> PROVE_TAC [INDEP_FN_FST_EVENTS]);

val PROB_BERN_BIND_INFINITE = store_thm
  ("PROB_BERN_BIND_INFINITE",
   ``!p f g c.
       f IN indep_fn /\ (!a. g a IN indep_fn) /\
       BIJ c UNIV (range (FST o f)) ==>
       (\m. prob bern ($= (c m) o FST o f) * prob bern (p o FST o g (c m)))
       sums
       prob bern (p o FST o BIND f g)``,
   RW_TAC std_ss []
   >> Know
      `(p o FST o BIND f g) =
       (p o FST o BIND f g) INTER
       BIGUNION (IMAGE (\m. $= (c m) o FST o f) UNIV)`
   >- (Suff `BIGUNION (IMAGE (\m. $= (c m) o FST o f) UNIV) = UNIV`
       >- RW_TAC std_ss [INTER_UNIV]
       >> SET_EQ_TAC
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, IN_o]
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF]
       >> POP_ASSUM
          (MP_TAC o
           Q.SPEC `(FST o (f : (num -> bool) -> 'b # (num -> bool))) x`)
       >> RW_TAC std_ss [ALWAYS_IN_RANGE]
       >> Q.EXISTS_TAC `y`
       >> RW_TAC std_ss []
       >> RW_TAC std_ss [SPECIFICATION])
   >> Rewr'
   >> RW_TAC std_ss [INTER_BIGUNION, IMAGE_IMAGE]
   >> Suff
      `(\m. prob bern ($= (c m) o FST o f) * prob bern (p o FST o g (c m))) =
       prob bern o ($INTER (p o FST o BIND f g) o (\m. $= (c m) o FST o f))`
   >- (Rewr
       >> MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
       >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, PROB_SPACE_BERN, o_THM,
                         DISJOINT_ALT, IN_INTER] >|
       [MATCH_MP_TAC EVENTS_INTER
        >> Q.SPEC_TAC (`$= (c x)`, `q`)
        >> RW_TAC std_ss [PROB_SPACE_BERN]
        >> PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_BIND],
        POP_ASSUM MP_TAC
        >> RW_TAC std_ss [SPECIFICATION, o_THM]
        >> Q.PAT_X_ASSUM `BIJ c X Y` MP_TAC
        >> RW_TAC std_ss [BIJ_DEF, INJ_DEF, IN_UNIV]
        >> PROVE_TAC []])
   >> FUN_EQ_TAC
   >> RW_TAC std_ss [o_THM]
   >> Know
      `p o FST o BIND f g INTER $= (c x) o FST o f =
       $= (c x) o FST o f INTER (p o FST o g (c x)) o SND o f`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_INTER]
       >> RW_TAC std_ss [SPECIFICATION, o_THM]
       >> reverse (Cases_on `FST (f x') = c x`) >- PROVE_TAC []
       >> RW_TAC std_ss [BIND_DEF, UNCURRY, o_THM])
   >> Rewr
   >> Suff `(p o FST o g (c x)) IN events bern`
   >- RW_TAC std_ss [INDEP_FN_PROB]
   >> PROVE_TAC [INDEP_FN_FST_EVENTS]);

val INDEP_FN_ENUM_RANGE = store_thm
  ("INDEP_FN_ENUM_RANGE",
   ``!f.
       f IN indep_fn ==>
       (?c : num -> 'a. BIJ c UNIV (range (FST o f))) \/
       (?c n. BIJ c (count n) (range (FST o f)))``,
   reverse (RW_TAC std_ss [indep_fn_def, GSPECIFICATION, COUNTABLE_ALT_BIJ])
   >- PROVE_TAC []
   >> PROVE_TAC [FINITE_BIJ_COUNT_EQ]);

(* |- ∀s. s ∈ events bern ⇒ (prob bern (COMPL s) = 1 − prob bern s) *)
val PROB_COMPL_BERN = save_thm
  ("PROB_COMPL_BERN",
    REWRITE_RULE [PROB_SPACE_BERN, SPACE_BERN_UNIV, GSYM COMPL_DEF]
                 (SPEC ``bern`` (INST_TYPE [``:'a`` |-> ``:num set``] PROB_COMPL)));

val PROB_BERN_BIND_UPPER = store_thm
  ("PROB_BERN_BIND_UPPER",
   ``!p f g q x y.
       f IN indep_fn /\ (!a. g a IN indep_fn) /\
       (!a. a IN q ==> prob bern (p o FST o g a) <= x) /\
       (!a. ~(a IN q) ==> prob bern (p o FST o g a) <= y) ==>
       prob bern (p o FST o BIND f g) <=
       prob bern (q o FST o f) * x + (1 - prob bern (q o FST o f)) * y``,
   RW_TAC std_ss []
   >> MP_TAC
      (Q.ISPEC `f : (num -> bool) -> 'b # (num -> bool)` INDEP_FN_ENUM_RANGE)
   >> RW_TAC std_ss [] >| (* 2 goals here *)
   [(* goal 1 (of 2) *)
    MP_TAC (Q.SPECL [`p`, `f`, `g`, `c`] PROB_BERN_BIND_INFINITE)
    >> impl_tac >- RW_TAC std_ss []
    >> Know
       `(\m. prob bern ($= (c m) o FST o f) * (if c m IN q then x else y))
        sums
        (prob bern (q o FST o f) * x + (1 - prob bern (q o FST o f)) * y)`
    >- (Know
        `(\m. prob bern ($= (c m) o FST o f) * (if c m IN q then x else y)) =
         (\m.
            (if c m IN q then prob bern ($= (c m) o FST o f) else 0) * x +
            (if c m IN q then 0 else prob bern ($= (c m) o FST o f)) * y)`
        >- (FUN_EQ_TAC
            >> RW_TAC real_ss [])
        >> Rewr
        >> HO_MATCH_MP_TAC SER_ADD
        >> ONCE_REWRITE_TAC [REAL_MUL_SYM]
        >> RW_TAC bool_ss [] >| (* 2 sub-goals here *)
        [(* goal 1.1 (of 2) *)
         HO_MATCH_MP_TAC SER_CMUL
         >> Know
            `(\m. (if c m IN q then prob bern ($= (c m) o FST o f) else 0)) =
             prob bern o (\m. if c m IN q then ($= (c m) o FST o f) else {})`
         >- (FUN_EQ_TAC
             >> RW_TAC std_ss [o_THM, PROB_BERN_BASIC])
         >> Rewr
         >> MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
         >> BasicProvers.NORM_TAC bool_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV,
                                           EVENTS_BERN_EMPTY, DISJOINT_EMPTY] >|
         [Q.SPEC_TAC (`$= (c m)`, `r`)
          >> PROVE_TAC [INDEP_FN_FST_EVENTS],
          RW_TAC std_ss [IN_o, DISJOINT_ALT]
          >> POP_ASSUM MP_TAC
          >> RW_TAC std_ss [SPECIFICATION]
          >> Q.PAT_X_ASSUM `BIJ c X Y` MP_TAC
          >> RW_TAC std_ss [BIJ_DEF, INJ_DEF, IN_UNIV]
          >> PROVE_TAC [],
          POP_ASSUM MP_TAC
          >> RW_TAC bool_ss [BIJ_DEF, SURJ_DEF, IN_UNIV]
          >> SET_EQ_TAC
          >> RW_TAC bool_ss [IN_BIGUNION_IMAGE, IN_o, IN_UNIV]
          >> POP_ASSUM
             (MP_TAC o
              Q.ISPEC `(FST o (f : (num -> bool) -> 'b # (num -> bool))) x'`)
          >> RW_TAC bool_ss [ALWAYS_IN_RANGE]
          >> Cases_on `(FST o f) x' IN q` >|
          [RW_TAC bool_ss []
           >> Q.EXISTS_TAC `y'`
           >> RW_TAC bool_ss [IN_o, NOT_IN_EMPTY]
           >> RW_TAC std_ss [SPECIFICATION],
           BasicProvers.NORM_TAC bool_ss [NOT_IN_EMPTY, IN_o]
           >> RW_TAC bool_ss [SPECIFICATION]
           >> PROVE_TAC [o_THM]]],
         (* goal 1.2 (of 2) *)
         HO_MATCH_MP_TAC SER_CMUL
         >> Know
            `(\m. (if c m IN q then 0 else prob bern ($= (c m) o FST o f))) =
             prob bern o
             (\m. if c m IN COMPL q then ($= (c m) o FST o f) else {})`
         >- (FUN_EQ_TAC
             >> RW_TAC std_ss [o_THM, PROB_BERN_BASIC, IN_COMPL]
             >> PROVE_TAC [])
         >> Rewr
         >> Know
            `(1 - prob bern (q o FST o f)) = prob bern (COMPL q o FST o f)`
         >- (Know `COMPL q o FST o f = COMPL (q o FST o f)`
             >- (SET_EQ_TAC
                 >> RW_TAC std_ss [IN_o, IN_COMPL])
             >> Rewr
             >> MATCH_MP_TAC EQ_SYM
             >> MATCH_MP_TAC PROB_COMPL_BERN
             >> PROVE_TAC [INDEP_FN_FST_EVENTS])
         >> Rewr
         >> MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
         >> BasicProvers.NORM_TAC bool_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV,
                                           EVENTS_BERN_EMPTY, DISJOINT_EMPTY] >| (* 3 sub-goals here *)
         [(* goal 1.2.1 (of 3) *)
          Q.SPEC_TAC (`$= (c m)`, `r`)
          >> PROVE_TAC [INDEP_FN_FST_EVENTS],
          (* goal 1.2.2 (of 3) *)
          RW_TAC bool_ss [IN_o, DISJOINT_ALT]
          >> POP_ASSUM MP_TAC
          >> RW_TAC bool_ss [SPECIFICATION]
          >> Q.PAT_X_ASSUM `BIJ c X Y` MP_TAC
          >> RW_TAC bool_ss [BIJ_DEF, INJ_DEF, IN_UNIV]
          >> PROVE_TAC [],
          (* goal 1.2.3 (of 3) *)
          POP_ASSUM MP_TAC
          >> RW_TAC bool_ss [BIJ_DEF, SURJ_DEF, IN_UNIV]
          >> SET_EQ_TAC
          >> RW_TAC bool_ss [IN_BIGUNION_IMAGE, IN_o, IN_UNIV]
          >> POP_ASSUM
             (MP_TAC o
              Q.ISPEC `(FST o (f : (num -> bool) -> 'b # (num -> bool))) x'`)
          >> RW_TAC bool_ss [ALWAYS_IN_RANGE]
          >> Cases_on `(FST o f) x' IN COMPL q` >|
          [RW_TAC bool_ss []
           >> Q.EXISTS_TAC `y'`
           >> BasicProvers.NORM_TAC bool_ss [IN_o, NOT_IN_EMPTY]
           >> RW_TAC bool_ss [SPECIFICATION],
           BasicProvers.NORM_TAC bool_ss [NOT_IN_EMPTY, IN_o]
           >> RW_TAC bool_ss [SPECIFICATION]
           >> PROVE_TAC [o_THM]]] ])
    >> RW_TAC bool_ss [SUMS_EQ]
    >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
    >> POP_ASSUM MP_TAC
    >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
    >> RW_TAC bool_ss []
    >> MATCH_MP_TAC SER_LE
    >> RW_TAC bool_ss [] >| (* 2 sub-goals here *)
    [(* goal 1.1 (of 2) *)
     MATCH_MP_TAC REAL_LE_LMUL_IMP
     >> RW_TAC bool_ss []
     >> MATCH_MP_TAC PROB_POSITIVE
     >> RW_TAC bool_ss [PROB_SPACE_BERN]
     >> Q.SPEC_TAC (`$= (c n)`, `r`)
     >> PROVE_TAC [INDEP_FN_FST_EVENTS],
     (* goal 1.2 (of 2) *)
     MATCH_MP_TAC REAL_LE_LMUL_IMP
     >> RW_TAC bool_ss []
     >> MATCH_MP_TAC PROB_POSITIVE
     >> RW_TAC bool_ss [PROB_SPACE_BERN]
     >> Q.SPEC_TAC (`$= (c n)`, `r`)
     >> PROVE_TAC [INDEP_FN_FST_EVENTS]],
    (* goal 2 (of 2) *)
    MP_TAC (Q.SPECL [`p`, `f`, `g`, `c`, `n`] PROB_BERN_BIND_FINITE)
    >> impl_tac >- RW_TAC std_ss []
    >> Know
       `sum (0, n)
        (\m. prob bern ($= (c m) o FST o f) * (if c m IN q then x else y)) =
        (prob bern (q o FST o f) * x + (1 - prob bern (q o FST o f)) * y)`
    >- (Know
        `(\m. prob bern ($= (c m) o FST o f) * (if c m IN q then x else y)) =
         (\m.
            (if c m IN q then prob bern ($= (c m) o FST o f) else 0) * x +
            (if c m IN q then 0 else prob bern ($= (c m) o FST o f)) * y)`
        >- (FUN_EQ_TAC
            >> RW_TAC real_ss [])
        >> Rewr
        >> RW_TAC bool_ss [SUM_ADD]
        >> Know `!a b c d : real. (a = c) /\ (b = d) ==> (a + b = c + d)`
        >- REAL_ARITH_TAC
        >> DISCH_THEN MATCH_MP_TAC
        >> ONCE_REWRITE_TAC [REAL_MUL_SYM]
        >> RW_TAC bool_ss [] >| (* 2 sub-goals here *)
        [(* goal 2.1 (of 2) *)
         RW_TAC bool_ss [SUM_CMUL, REAL_EQ_LMUL]
         >> DISJ2_TAC
         >> Know
            `(\m. (if c m IN q then prob bern ($= (c m) o FST o f) else 0)) =
             prob bern o (\m. if c m IN q then ($= (c m) o FST o f) else {})`
         >- (FUN_EQ_TAC
             >> RW_TAC bool_ss [o_THM, PROB_BERN_BASIC])
         >> Rewr
         >> MATCH_MP_TAC PROB_FINITELY_ADDITIVE
         >> BasicProvers.NORM_TAC bool_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV,
                                          EVENTS_BERN_EMPTY, DISJOINT_EMPTY] >|
         [Q.SPEC_TAC (`$= (c m)`, `r`)
          >> PROVE_TAC [INDEP_FN_FST_EVENTS],
          RW_TAC bool_ss [IN_o, DISJOINT_ALT]
          >> POP_ASSUM MP_TAC
          >> RW_TAC bool_ss [SPECIFICATION]
          >> Q.PAT_X_ASSUM `BIJ c X Y` MP_TAC
          >> RW_TAC bool_ss [BIJ_DEF, INJ_DEF, IN_COUNT]
          >> PROVE_TAC [],
          POP_ASSUM MP_TAC
          >> RW_TAC bool_ss [BIJ_DEF, SURJ_DEF, IN_COUNT]
          >> SET_EQ_TAC
          >> RW_TAC bool_ss [IN_BIGUNION_IMAGE, IN_o, IN_COUNT]
          >> POP_ASSUM
             (MP_TAC o
              Q.ISPEC `(FST o (f : (num -> bool) -> 'b # (num -> bool))) x'`)
          >> RW_TAC bool_ss [ALWAYS_IN_RANGE]
          >> Cases_on `(FST o f) x' IN q` >|
          [RW_TAC bool_ss []
           >> Q.EXISTS_TAC `y'`
           >> BasicProvers.NORM_TAC bool_ss [IN_o, NOT_IN_EMPTY]
           >> RW_TAC bool_ss [SPECIFICATION],
           BasicProvers.NORM_TAC bool_ss [NOT_IN_EMPTY, IN_o]
           >> RW_TAC bool_ss [SPECIFICATION]
           >> PROVE_TAC [o_THM]]],
         (* goal 2.2 (of 2) *)
         RW_TAC bool_ss [SUM_CMUL, REAL_EQ_LMUL]
         >> DISJ2_TAC
         >> Know
            `(\m. (if c m IN q then 0 else prob bern ($= (c m) o FST o f))) =
             prob bern o
             (\m. if c m IN COMPL q then ($= (c m) o FST o f) else {})`
         >- (FUN_EQ_TAC
             >> RW_TAC bool_ss [o_THM, PROB_BERN_BASIC, IN_COMPL]
             >> PROVE_TAC [])
         >> Rewr
         >> Know
            `(1 - prob bern (q o FST o f)) = prob bern (COMPL q o FST o f)`
         >- (Know `COMPL q o FST o f = COMPL (q o FST o f)`
             >- (SET_EQ_TAC
                 >> RW_TAC bool_ss [IN_o, IN_COMPL])
             >> Rewr
             >> MATCH_MP_TAC EQ_SYM
             >> MATCH_MP_TAC PROB_COMPL_BERN
             >> PROVE_TAC [INDEP_FN_FST_EVENTS])
         >> Rewr
         >> MATCH_MP_TAC PROB_FINITELY_ADDITIVE
         >> BasicProvers.NORM_TAC bool_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV,
                                          EVENTS_BERN_EMPTY, DISJOINT_EMPTY] >| (* 3 sub-goals here *)
         [(* goal 2.2.1 (of 3) *)
          Q.SPEC_TAC (`$= (c m)`, `r`)
          >> PROVE_TAC [INDEP_FN_FST_EVENTS],
          (* goal 2.2.2 (of 3) *)
          RW_TAC bool_ss [IN_o, DISJOINT_ALT]
          >> POP_ASSUM MP_TAC
          >> RW_TAC bool_ss [SPECIFICATION]
          >> Q.PAT_X_ASSUM `BIJ c X Y` MP_TAC
          >> RW_TAC bool_ss [BIJ_DEF, INJ_DEF, IN_COUNT]
          >> PROVE_TAC [],
          (* goal 2.2.3 (of 3) *)
          POP_ASSUM MP_TAC
          >> RW_TAC bool_ss [BIJ_DEF, SURJ_DEF, IN_COUNT]
          >> SET_EQ_TAC
          >> RW_TAC bool_ss [IN_BIGUNION_IMAGE, IN_o, IN_COUNT]
          >> POP_ASSUM
             (MP_TAC o
              Q.ISPEC `(FST o (f : (num -> bool) -> 'b # (num -> bool))) x'`)
          >> RW_TAC bool_ss [ALWAYS_IN_RANGE]
          >> Cases_on `(FST o f) x' IN COMPL q` >|
          [RW_TAC bool_ss []
           >> Q.EXISTS_TAC `y'`
           >> BasicProvers.NORM_TAC bool_ss [IN_o, NOT_IN_EMPTY]
           >> RW_TAC bool_ss [SPECIFICATION],
           BasicProvers.NORM_TAC bool_ss [NOT_IN_EMPTY, IN_o]
           >> RW_TAC bool_ss [SPECIFICATION]
           >> PROVE_TAC [o_THM]]] ])
    >> RW_TAC bool_ss []
    >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
    >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
    >> MATCH_MP_TAC SUM_LE
    >> RW_TAC bool_ss [] >|
    [MATCH_MP_TAC REAL_LE_LMUL_IMP
     >> RW_TAC bool_ss []
     >> MATCH_MP_TAC PROB_POSITIVE
     >> RW_TAC bool_ss [PROB_SPACE_BERN]
     >> Q.SPEC_TAC (`$= (c n)`, `R`)
     >> PROVE_TAC [INDEP_FN_FST_EVENTS],
     MATCH_MP_TAC REAL_LE_LMUL_IMP
     >> RW_TAC bool_ss []
     >> MATCH_MP_TAC PROB_POSITIVE
     >> RW_TAC bool_ss [PROB_SPACE_BERN]
     >> Q.SPEC_TAC (`$= (c n)`, `R`)
     >> PROVE_TAC [INDEP_FN_FST_EVENTS]] ]);

val PROB_BERN_PROB_WHILE_CUT = store_thm
  ("PROB_BERN_PROB_WHILE_CUT",
   ``!c b n a p.
       (!a. b a IN indep_fn) /\ (!a. prob bern {s | c (FST (b a s))} <= p) ==>
       prob bern {s | c (FST (prob_while_cut c b n a s))} <= p pow n``,
   RW_TAC std_ss []
   >> Know `!a. countable (range (FST o b a))`
   >- (STRIP_TAC
       >> Q.PAT_X_ASSUM `!a. b a IN indep_fn` (MP_TAC o Q.SPEC `a`)
       >> RW_TAC std_ss [indep_fn_def, GSPECIFICATION])
   >> STRIP_TAC
   >> Know `!n. 0 <= p pow n`
   >- (MATCH_MP_TAC POW_POS
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `prob bern {s | c (FST (b a s))}`
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC PROB_POSITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN]
       >> Know `{s | c (FST (b a s))} = PREIMAGE (FST o b a) c`
       >- (SET_EQ_TAC
           >> PSET_TAC [o_THM]
           >> RW_TAC std_ss [SPECIFICATION])
       >> Rewr
       >> Q.PAT_X_ASSUM `!a. b a IN indep_fn` (MP_TAC o Q.SPEC `a`)
       >> RW_TAC std_ss [indep_fn_def, GSPECIFICATION, IN_MEASURABLE, IN_UNIV,
                         IN_FUNSET, space_def, subsets_def, SPACE_BERN_UNIV, INTER_UNIV])
   >> STRIP_TAC
   >> Q.SPEC_TAC (`a`, `a`)
   >> Induct_on `n`
   >- (RW_TAC std_ss [pow, o_DEF, prob_while_cut_def, UNIT_DEF]
       >> Cases_on `c a`
       >> RW_TAC std_ss [GEMPTY, GUNIV, PROB_BERN_BASIC]
       >> REAL_ARITH_TAC)
   >> RW_TAC std_ss [prob_while_cut_def, o_THM, UNCURRY, UNIT_DEF,
                     GEMPTY, PROB_BERN_BASIC]
   >> Know
      `{s | c (FST (BIND (b a) (prob_while_cut c b n) s))} =
       c o FST o BIND (b a) (prob_while_cut c b n)`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_o, GSPECIFICATION, o_THM]
       >> RW_TAC std_ss [SPECIFICATION])
   >> Rewr
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `prob bern (c o FST o b a) * p pow n +
       (1 - prob bern (c o FST o b a)) * 0`
   >> reverse CONJ_TAC
   >- (RW_TAC std_ss [pow, REAL_MUL_RZERO, REAL_ADD_RID]
       >> MATCH_MP_TAC REAL_LE_RMUL_IMP
       >> RW_TAC std_ss []
       >> Suff `(c o FST o b a) = {s | c (FST (b a s))}`
       >- RW_TAC std_ss []
       >> SET_EQ_TAC
       >> PSET_TAC [o_THM]
       >> RW_TAC std_ss [SPECIFICATION])
   >> (MATCH_MP_TAC o
       INST_TYPE [beta |-> alpha] o
       Q.SPECL [`c`, `b a`, `prob_while_cut c b n`, `c`, `p pow n`, `0`] o
       INST_TYPE [beta |-> alpha])
      PROB_BERN_BIND_UPPER
   >> RW_TAC std_ss [INDEP_FN_PROB_WHILE_CUT]
   >- (Suff
       `(c o FST o prob_while_cut c b n a') =
        {s | c (FST (prob_while_cut c b n a' s))}`
       >- RW_TAC std_ss []
       >> SET_EQ_TAC
       >> PSET_TAC [o_THM]
       >> RW_TAC std_ss [SPECIFICATION])
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [SPECIFICATION]
   >> Cases_on `n`
   >> RW_TAC std_ss [prob_while_cut_def, o_DEF, UNIT_DEF, GSYM EMPTY_DEF,
                     PROB_BERN_BASIC, REAL_LE_REFL]);

val MANY = store_thm
  ("MANY",
   ``!f n.
       (many f 0 = UNIT T) /\
       (many f (SUC n) = BIND f (\s. if s then many f n else UNIT F))``,
   FUN_EQ_TAC
   >> RW_TAC std_ss [many_def, prob_while_cut_def, K_THM, I_THM,
                     BIND_DEF, UNCURRY, o_THM, UNIT_DEF]
   >> Cases_on `n`
   >> RW_TAC std_ss [many_def, prob_while_cut_def, K_THM, I_THM,
                     BIND_DEF, UNCURRY, o_THM, UNIT_DEF]);

val INDEP_FN_MANY = store_thm
  ("INDEP_FN_MANY",
   ``!f n. f IN indep_fn ==> many f n IN indep_fn``,
   RW_TAC std_ss [many_def]
   >> MATCH_MP_TAC INDEP_FN_PROB_WHILE_CUT
   >> RW_TAC std_ss [K_THM]);

val PROB_BERN_MANY = store_thm
  ("PROB_BERN_MANY",
   ``!f n.
       f IN indep_fn ==>
       (prob bern (FST o many f n) = prob bern (FST o f) pow n)``,
   RW_TAC std_ss [many_def]
   >> Induct_on `n`
   >- RW_TAC std_ss [pow, UNIT_DEF, o_DEF, GSYM UNIV_DEF,
                     PROB_BERN_BASIC, prob_while_cut_def]
   >> RW_TAC std_ss [prob_while_cut_def, I_THM, K_THM]
   >> (MP_TAC o
       Q.SPECL
       [`f`, `prob_while_cut I (K f) n`,
        `prob bern (FST o (f : (num -> bool) -> bool # (num -> bool)))`])
      PROB_BERN_BIND_BOOL_BOOL
   >> BETA_TAC
   >> impl_tac
   >- RW_TAC std_ss [INDEP_FN_PROB_WHILE_CUT, INDEP_FN_UNIT, K_THM]
   >> Rewr
   >> Know `prob bern (FST o prob_while_cut I (K f) n F) = 0`
   >- (Cases_on `n`
       >> RW_TAC std_ss [UNIT_DEF, o_DEF, GSYM EMPTY_DEF, PROB_BERN_BASIC,
                         prob_while_cut_def, I_THM])
   >> Rewr
   >> RW_TAC real_ss [pow]);

val INDEP_FN_FUNPOW = store_thm
  ("INDEP_FN_FUNPOW",
   ``!f n a.
       (!a. f a IN indep_fn) ==>
       FUNPOW (UNCURRY f) n o UNIT a IN indep_fn``,
   RW_TAC std_ss []
   >> Induct_on `n` >- RW_TAC std_ss' [FUNPOW, o_DEF, INDEP_FN_UNIT]
   >> Suff `FUNPOW (UNCURRY f) (SUC n) o UNIT a =
            BIND (FUNPOW (UNCURRY f) n o UNIT a) f`
   >- RW_TAC std_ss [INDEP_FN_BIND]
   >> RW_TAC std_ss [FUNPOW_SUC, BIND_DEF, o_DEF]);

Theorem PREFIX_COVER_LEVELS_DISJOINT:
  !c b ca a m n.
    (!a. prefix_cover (ca a)) /\ ~(m = n) ==>
    DISJOINT (prefix_cover_level c b ca a m)
             (prefix_cover_level c b ca a n)
Proof
   RW_TAC std_ss [IN_DISJOINT, prefix_cover_def, FORALL_AND_THM]
   >> qid_spec_tac ‘x’ >> qid_spec_tac ‘a’
   >> POP_ASSUM MP_TAC
   >> map_every qid_spec_tac [‘n’, ‘m’]
   >> (Induct
       >> Cases
       >> BasicProvers.NORM_TAC std_ss
          [prefix_cover_level_def, append_sets_fn_def,
           GSPECIFICATION, NOT_IN_EMPTY, IN_SING])
   >> Know `!a b. a \/ b = ~a ==> b` >- PROVE_TAC []
   >> Rewr'
   >> RW_TAC std_ss []
   >> STRONG_DISJ_TAC
   >> STRIP_TAC
   >> Know `l' = l''`
   >- (Suff `IS_PREFIX l' l'' \/ IS_PREFIX l'' l'`
       >- PROVE_TAC []
       >> MATCH_MP_TAC IS_PREFIX_APPEND2
       >> Q.EXISTS_TAC `y`
       >> MATCH_MP_TAC IS_PREFIX_APPEND1
       >> Q.EXISTS_TAC `y'`
       >> RW_TAC std_ss [IS_PREFIX_REFL])
   >> STRIP_TAC
   >> RW_TAC std_ss []
   >> full_simp_tac std_ss [APPEND_11]
   >> PROVE_TAC []
QED

val PREFIX_COVER_STAR_PREFIXFREE = store_thm
  ("PREFIX_COVER_STAR_PREFIXFREE",
   ``!c b ca a l m.
       (!a. prefix_cover (ca a)) /\ ~(l = m) /\
       l IN prefix_cover_star c b ca a /\ m IN prefix_cover_star c b ca a ==>
       ~(IS_PREFIX l m)``,
   RW_TAC std_ss [prefix_cover_def, prefix_cover_star_def, IN_BIGUNION_IMAGE,
                  IN_UNIV, IN_DISJOINT, FORALL_AND_THM]
   >> NTAC 3 (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`a`, `a`)
   >> Q.SPEC_TAC (`m`, `m`)
   >> Q.SPEC_TAC (`l`, `l`)
   >> Q.SPEC_TAC (`x'`, `y`)
   >> Q.SPEC_TAC (`x`, `x`)
   >> (Induct
       >> Cases
       >> ASM_SIMP_TAC (std_ss ++ boolSimps.COND_elim_ss ++ boolSimps.CONJ_ss)
                       [prefix_cover_level_def, append_sets_fn_def,
                        GSPECIFICATION, NOT_IN_EMPTY, IN_SING])
   >> MAP_EVERY Q.X_GEN_TAC [`l`, `m`, `a`]
   >> STRIP_TAC
   >> DISCH_THEN
        (CONJUNCTS_THEN2
             (DISJ_CASES_THEN2 ASSUME_TAC
                               (Q.X_CHOOSE_THEN `l'` STRIP_ASSUME_TAC))
             STRIP_ASSUME_TAC)
   >> DISCH_THEN (Q.X_CHOOSE_THEN `l''` STRIP_ASSUME_TAC)
   >> RW_TAC std_ss []
   >> STRIP_TAC
   >> Know `l' = l''`
   >- PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `IS_PREFIX X Y` MP_TAC
   >> RW_TAC std_ss [IS_PREFIX_APPENDS]
   >> PROVE_TAC []);

val PREFIX_COVER_LEVELS_DISJOINT_SETS = store_thm
  ("PREFIX_COVER_LEVELS_DISJOINT_SETS",
   ``!c b ca a m n.
       (!a. prefix_cover (ca a)) /\ ~(m = n) ==>
       DISJOINT
       (BIGUNION (IMAGE prefix_set (prefix_cover_level c b ca a m)))
       (BIGUNION (IMAGE prefix_set (prefix_cover_level c b ca a n)))``,
   RW_TAC std_ss [DISJOINT_ALT, IN_BIGUNION_IMAGE]
   >> STRONG_DISJ_TAC
   >> STRIP_TAC
   >> Suff `x' = x''`
   >- PROVE_TAC [PREFIX_COVER_LEVELS_DISJOINT, IN_DISJOINT]
   >> Suff `IS_PREFIX x' x'' \/ IS_PREFIX x'' x'`
   >- (MP_TAC (Q.SPECL [`c`, `b`, `ca`, `a`] PREFIX_COVER_STAR_PREFIXFREE)
       >> RW_TAC std_ss [prefix_cover_star_def, IN_BIGUNION_IMAGE, IN_UNIV]
       >> PROVE_TAC [])
   >> MP_TAC (Q.SPECL [`x'`, `x''`] PREFIX_SET_SUBSET)
   >> RW_TAC std_ss [IN_DISJOINT, PREFIX_SET_PREFIX_SUBSET]
   >> PROVE_TAC []);

val PREFIX_COVER_STAR = store_thm
  ("PREFIX_COVER_STAR",
   ``!c b ca a.
       (!a. prefix_cover (ca a)) /\
       (!a. !* s. ?n.
          s IN BIGUNION (IMAGE prefix_set (prefix_cover_level c b ca a n))) ==>
       prefix_cover (prefix_cover_star c b ca a)``,
   RW_TAC std_ss []
   >> RW_TAC std_ss [prefix_cover_def]
   >- PROVE_TAC [PREFIX_COVER_STAR_PREFIXFREE]
   >> RW_TAC std_ss [prefix_cover_star_def, BIGUNION_IMAGE_INSIDE]
   >> Know
      `(prob bern o (BIGUNION o IMAGE prefix_set o prefix_cover_level c b ca a))
       sums
       prob bern
       (BIGUNION
        (IMAGE
         (BIGUNION o IMAGE prefix_set o prefix_cover_level c b ca a) UNIV))`
   >- (MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
       >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, PROB_SPACE_BERN, o_THM,
                         IN_DISJOINT, IN_BIGUNION_IMAGE]
       >- (MATCH_MP_TAC EVENTS_COUNTABLE_UNION
           >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_BOOL_LIST,
                             image_countable, SUBSET_DEF, IN_IMAGE]
           >> RW_TAC std_ss [EVENTS_BERN_PREFIX_SET])
       >> CCONTR_TAC
       >> POP_ASSUM (MP_TAC o REWRITE_RULE [DE_MORGAN_THM])
       >> STRIP_TAC
       >> NTAC 2 (POP_ASSUM (MP_TAC o CONV_RULE NOT_FORALL_CONV))
       >> PURE_REWRITE_TAC [DE_MORGAN_THM, NOT_CLAUSES]
       >> STRIP_TAC
       >> STRIP_TAC
       >> Suff `x' = x''`
       >- (STRIP_TAC
           >> RW_TAC std_ss []
           >> PROVE_TAC [PREFIX_COVER_LEVELS_DISJOINT, IN_DISJOINT])
       >> Suff `IS_PREFIX x' x'' \/ IS_PREFIX x'' x'`
       >- (MP_TAC (Q.SPECL [`c`, `b`, `ca`, `a`, `x'`, `x''`]
                   PREFIX_COVER_STAR_PREFIXFREE)
           >> MP_TAC (Q.SPECL [`c`, `b`, `ca`, `a`, `x''`, `x'`]
                      PREFIX_COVER_STAR_PREFIXFREE)
           >> RW_TAC std_ss [prefix_cover_star_def, IN_BIGUNION_IMAGE, IN_UNIV]
           >> PROVE_TAC [])
       >> MP_TAC (Q.SPECL [`x'`, `x''`] PREFIX_SET_SUBSET)
       >> RW_TAC std_ss [IN_DISJOINT, PREFIX_SET_PREFIX_SUBSET]
       >> PROVE_TAC [])
   >> Suff
    `(prob bern o BIGUNION o IMAGE prefix_set o prefix_cover_level c b ca a)
     sums 1`
   >- PROVE_TAC [SUM_UNIQ]
   >> POP_ASSUM (MP_TAC o Q.SPEC `a`)
   >> RW_TAC std_ss [probably_bern_def, probably_def]
   >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
   >> MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
   >> SET_EQ_TAC
   >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV, o_THM,
                     GSPECIFICATION, IN_BIGUNION_IMAGE] >| (* 2 sub-goals here *)
   [(* goal 1 (of 2) *)
    `events bern = subsets (p_space bern, events bern)` by PROVE_TAC [subsets_def]
    >> POP_ORW
    >> MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
    >> RW_TAC std_ss [COUNTABLE_BOOL_LIST, image_countable, SUBSET_DEF,
                      IN_IMAGE, EVENTS_SIGMA_ALGEBRA, PROB_SPACE_BERN, subsets_def]
    >> RW_TAC std_ss [EVENTS_BERN_PREFIX_SET],
    (* goal 2 (of 2) *)
    RW_TAC std_ss [DISJOINT_ALT, IN_BIGUNION_IMAGE]
    >> STRONG_DISJ_TAC
    >> STRIP_TAC
    >> Suff `x' = x''`
    >- (STRIP_TAC
        >> RW_TAC std_ss []
        >> PROVE_TAC [PREFIX_COVER_LEVELS_DISJOINT, IN_DISJOINT])
    >> Suff `IS_PREFIX x' x'' \/ IS_PREFIX x'' x'`
    >- (MP_TAC (Q.SPECL [`c`, `b`, `ca`, `a`, `x'`, `x''`]
                PREFIX_COVER_STAR_PREFIXFREE)
        >> MP_TAC (Q.SPECL [`c`, `b`, `ca`, `a`, `x''`, `x'`]
                   PREFIX_COVER_STAR_PREFIXFREE)
        >> RW_TAC std_ss [prefix_cover_star_def, IN_BIGUNION_IMAGE, IN_UNIV]
        >> PROVE_TAC [])
    >> MP_TAC (Q.SPECL [`x'`, `x''`] PREFIX_SET_SUBSET)
    >> RW_TAC std_ss [IN_DISJOINT, PREFIX_SET_PREFIX_SUBSET]
    >> PROVE_TAC []]);

Theorem MINIMAL_EQ:
  !P m. P m /\ (m = $LEAST P) <=> P m /\ (!n. n < m ⇒ ~P n)
Proof
  rpt gen_tac >> Cases_on ‘?k. P k’ >> gs[] >> numLib.LEAST_ELIM_TAC >>
  simp[SF SFY_ss] >> rw[] >> metis_tac[DECIDE “x:num < y \/ (x = y) \/ y < x”]
QED

Theorem PROB_WHILE_TERMINATES_PREFIX_COVER_STAR:
  !c b bc ca a.
       (!a. b a IN indep_fn) /\
       (!a. prefix_cover (ca a)) /\
       (!a l s.
          l IN ca a /\ s IN prefix_set l ==>
          (b a s = (FST (b a (prefix_seq l)),sdrop (LENGTH l) s))) /\
       (bc = (\a l. FST (b a (prefix_seq l)))) /\
       prob_while_terminates c b ==>
       prefix_cover (prefix_cover_star c bc ca a)
Proof
   RW_TAC std_ss []
   >> MATCH_MP_TAC PREFIX_COVER_STAR
   >> RW_TAC std_ss []
   >> Know
      `!n a.
         BIGUNION
         (IMAGE prefix_set
          (prefix_cover_level c (\a l. FST (b a (prefix_seq l))) ca a n)) IN
         events bern`
   >- (RW_TAC std_ss [COUNTABLE_IMAGE_NUM, PROB_SPACE_BERN, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV, GDEST]
       >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       >> RW_TAC std_ss [image_countable, PROB_SPACE_BERN, SUBSET_DEF,
                         COUNTABLE_BOOL_LIST, IN_IMAGE]
       >> RW_TAC std_ss [EVENTS_BERN_PREFIX_SET])
   >> RW_TAC std_ss [probably_def, probably_bern_def]
   >- (RW_TAC std_ss [GBIGUNION_IMAGE]
       >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                         IN_IMAGE, IN_UNIV, GDEST]
       >> RW_TAC std_ss [])
   >> Q.PAT_X_ASSUM `prob_while_terminates c b` MP_TAC
   >> RW_TAC std_ss [prob_while_terminates_def]
   >> POP_ASSUM (MP_TAC o Q.SPEC `a`)
   >> RW_TAC std_ss [probably_def, probably_bern_def]
   >> Q.PAT_X_ASSUM `X IN events bern` K_TAC
   >> Q.PAT_X_ASSUM `!n. P n` ASSUME_TAC
   >> Know `!n a. {s | ~c (FST (FUNPOW (UNCURRY b) n (a,s)))} IN events bern`
   >- (RW_TAC std_ss [COUNTABLE_IMAGE_NUM, PROB_SPACE_BERN, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV, GDEST]
       >> Know
          `{s | ~c (FST (FUNPOW (UNCURRY b) n (a',s)))} =
           PREIMAGE (FST o FUNPOW (UNCURRY b) n o UNIT a') (COMPL c)`
       >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_PREIMAGE, IN_COMPL,
                          o_THM, UNIT_DEF]
           >> RW_TAC std_ss [GSYM EXTENSION]
           >> RW_TAC std_ss [SPECIFICATION])
       >> Rewr
       >> Suff `(FUNPOW (UNCURRY b) n o UNIT a') IN indep_fn`
       >- ( RW_TAC std_ss [indep_fn_def, GSPECIFICATION, IN_MEASURABLE, IN_UNIV] \\
            FULL_SIMP_TAC std_ss [space_def, subsets_def, IN_FUNSET, IN_UNIV,
                                  SPACE_BERN_UNIV, INTER_UNIV] )
       >> MATCH_MP_TAC INDEP_FN_FUNPOW
       >> RW_TAC std_ss [])
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `X = Y` (ONCE_REWRITE_TAC o wrap o SYM)
   >> Know
      `{s | ?n. ~c (FST (FUNPOW (UNCURRY b) n (a,s)))} =
       {s |
        ?m.
          (m = LEAST n. ~c (FST (FUNPOW (UNCURRY b) n (a,s)))) /\
          ~c (FST (FUNPOW (UNCURRY b) m (a,s)))}`
   >- (RW_TAC std_ss [Once EXTENSION, GSPECIFICATION]
       >> Cases_on ‘∃n. ¬c (FST (FUNPOW (UNCURRY b) n (a,x)))’
       >> simp[SF SFY_ss] >> gs[]
       >> numLib.LEAST_ELIM_TAC >> simp[SF SFY_ss])
   >> Rewr
   >> Ho_Rewrite.REWRITE_TAC [GBIGUNION_IMAGE]
   >> RW_TAC std_ss [GDEST]
   >> MATCH_MP_TAC PROB_EQ_BIGUNION_IMAGE
   >> CONJ_TAC >- RW_TAC std_ss [PROB_SPACE_BERN]
   >> CONJ_TAC >- RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> Know
      `!a m.
         {s |
          (m = LEAST n. ~c (FST (FUNPOW (UNCURRY b) n (a,s)))) /\
          ~c (FST (FUNPOW (UNCURRY b) m (a,s)))} IN
         events bern`
   >- (RW_TAC std_ss []
       >> Know
          `{s |
            (m = LEAST n. ~c (FST (FUNPOW (UNCURRY b) n (a,s)))) /\
            ~c (FST (FUNPOW (UNCURRY b) m (a,s)))} =
           {s | ~c (FST (FUNPOW (UNCURRY b) m (a,s)))} DIFF
           BIGUNION
           (IMAGE (\n. {s | ~c (FST (FUNPOW (UNCURRY b) n (a,s)))}) (count m))`
      >- (SET_EQ_TAC
          >> KILL_TAC
          >> RW_TAC std_ss [GSPECIFICATION, IN_DIFF, IN_BIGUNION_IMAGE,
                            IN_COUNT]
          >> simp[Once CONJ_COMM, SimpLHS]
          >> qspecl_then [‘λn. ¬c(FST (FUNPOW (UNCURRY b) n (a,x)))’, ‘m’]
                         (simp o single o SIMP_RULE std_ss[]) MINIMAL_EQ
          >> eq_tac >> simp[] >> metis_tac[prim_recTheory.LESS_REFL])
      >> Rewr
      >> MATCH_MP_TAC EVENTS_DIFF
      >> RW_TAC std_ss [PROB_SPACE_BERN]
      >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
      >> RW_TAC std_ss [PROB_SPACE_BERN, finite_countable, FINITE_COUNT,
                        image_countable, SUBSET_DEF, IN_IMAGE]
      >> RW_TAC std_ss [])
   >> STRIP_TAC
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV, GINTER]
       >> MATCH_MP_TAC EVENTS_INTER
       >> RW_TAC std_ss [PROB_SPACE_BERN])
   >> CONJ_TAC
   >- (RW_TAC std_ss [GDEST]
       >> PROVE_TAC [PREFIX_COVER_LEVELS_DISJOINT_SETS])
   >> CONJ_TAC
   >- (RW_TAC std_ss [DISJOINT_ALT, GSPECIFICATION]
       >> STRONG_DISJ_TAC
       >> RW_TAC std_ss [])
   >> RW_TAC std_ss []
   >> Q.SPEC_TAC (`a`, `a`)
   >> Induct_on `n`
   >- (RW_TAC std_ss [FUNPOW, prefix_cover_level_def, IMAGE_EMPTY,
                      BIGUNION_EMPTY, NOT_IN_EMPTY, IMAGE_INSERT, IMAGE_EMPTY,
                      BIGUNION_SING, prefix_set_def, IN_UNIV, GEMPTY]
       >> AP_TERM_TAC
       >> SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_UNIV]
       >> numLib.LEAST_ELIM_TAC >> simp[]
       >> metis_tac[FUNPOW, NOT_ZERO_LT_ZERO, FST])
   >> STRIP_TAC
   >> (MP_TAC o
       INST_TYPE [beta |-> ``:num -> bool``] o
       Q.SPECL
       [`ca a`,
        `BIGUNION
         (IMAGE prefix_set
          (prefix_cover_level c (\a l. FST (b a (prefix_seq l))) ca a
           (SUC n)))`])
       PROB_BERN_PREFIX_COVER_INTER
   >> impl_tac >- RW_TAC std_ss []
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
   >> (MP_TAC o
       Q.SPECL
       [`ca a`,
        `{s |
         (SUC n = LEAST n. ~c (FST (FUNPOW (UNCURRY b) n (a,s)))) /\
         ~c (FST (FUNPOW (UNCURRY b) (SUC n) (a,s)))}`])
       PROB_BERN_PREFIX_COVER_INTER
   >> impl_tac >- RW_TAC std_ss []
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
   >> MP_TAC (Q.ISPEC `IMAGE prefix_set (ca a)` COUNTABLE_DISJOINT_ENUM)
   >> impl_tac
   >- (RW_TAC std_ss [image_countable, COUNTABLE_BOOL_LIST]
       >> PROVE_TAC [PREFIX_COVER_DISJOINT])
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INSERT, IN_IMAGE]
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [INTER_BIGUNION, IMAGE_IMAGE]
   >> MATCH_MP_TAC PROB_EQ_BIGUNION_IMAGE
   >> CONJ_TAC >- RW_TAC std_ss [PROB_SPACE_BERN]
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM]
       >> MATCH_MP_TAC EVENTS_INTER
       >> RW_TAC std_ss [PROB_SPACE_BERN]
       >> PROVE_TAC [EVENTS_BERN_EMPTY, EVENTS_BERN_PREFIX_SET])
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM]
       >> MATCH_MP_TAC EVENTS_INTER
       >> RW_TAC std_ss [PROB_SPACE_BERN]
       >> PROVE_TAC [EVENTS_BERN_EMPTY, EVENTS_BERN_PREFIX_SET])
   >> CONJ_TAC
   >- (RW_TAC std_ss [o_THM]
       >> PROVE_TAC [IN_DISJOINT, IN_INTER])
   >> CONJ_TAC
   >- (RW_TAC std_ss [o_THM]
       >> PROVE_TAC [IN_DISJOINT, IN_INTER])
   >> RW_TAC std_ss [o_THM]
   >> Q.PAT_X_ASSUM `!x. P x \/ Q x` (MP_TAC o Q.SPEC `n'`)
   >> RW_TAC std_ss [] >- RW_TAC std_ss [INTER_EMPTY]
   >> RW_TAC std_ss []
   >> reverse (RW_TAC std_ss [prefix_cover_level_def, GDEST])
   >- (Suff `!s. (LEAST n. ~c (FST (FUNPOW (UNCURRY b) n (a,s)))) = 0`
       >- RW_TAC std_ss [GEMPTY, IMAGE_EMPTY, BIGUNION_EMPTY, INTER_EMPTY]
       >> STRIP_TAC >> numLib.LEAST_ELIM_TAC >> simp[]
       >> metis_tac[FUNPOW, NOT_ZERO_LT_ZERO, FST])
   >> Know
      `!g.
         BIGUNION
         (IMAGE prefix_set (append_sets_fn (ca a) g)) INTER prefix_set x' =
         BIGUNION (IMAGE (prefix_set o APPEND x') (g x'))`
   >- (Q.PAT_X_ASSUM `x' IN ca a` MP_TAC
       >> Know `prefix_cover (ca a)` >- PROVE_TAC []
       >> KILL_TAC
       >> SET_EQ_TAC
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_INTER, append_sets_fn_def,
                         GSPECIFICATION, o_THM]
       >> EQ_TAC >|
       [RW_TAC std_ss []
        >> Suff `x' = x'''` >- PROVE_TAC []
        >> MP_TAC (Q.SPECL [`ca a`, `prefix_set x'`, `prefix_set x'''`]
                   PREFIX_COVER_DISJOINT)
        >> RW_TAC std_ss [IN_DISJOINT, IN_IMAGE, PREFIX_SET_INJ]
        >> PROVE_TAC [PREFIX_SET_APPEND],
        RW_TAC std_ss []
        >> PROVE_TAC [PREFIX_SET_APPEND]])
   >> Rewr
   >> RW_TAC std_ss []
   >> Know
      `!c.
         BIGUNION (IMAGE (prefix_set o APPEND x') c) =
         prefix_set x' INTER
         (BIGUNION (IMAGE prefix_set c) o sdrop (LENGTH x'))`
   >- (KILL_TAC
       >> SET_EQ_TAC
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_INTER, o_THM, IN_o]
       >> PROVE_TAC [SDROP_APPEND, PREFIX_SET_APPEND])
   >> Rewr
   >> RW_TAC std_ss [PROB_BERN_PREFIX_SET_INTER_SDROP]
   >> Know
      `!s.
         (SUC n = LEAST n. ~c (FST (FUNPOW (UNCURRY b) n (a,s)))) /\
         ~c (FST (FUNPOW (UNCURRY b) (SUC n) (a,s))) <=>
         c (FST (FUNPOW (UNCURRY b) 0 (a,s))) /\
         (n = $LEAST ((\n. ~c (FST (FUNPOW (UNCURRY b) n (a,s)))) o SUC)) /\
         ~c (FST (FUNPOW (UNCURRY b) (SUC n) (a,s))) `
   >- (STRIP_TAC >> simp[] >> ONCE_REWRITE_TAC [CONJ_COMM]
       >> simp[combinTheory.o_ABS_L]
       >> qspecl_then [‘λn. ¬c(FST (FUNPOW (UNCURRY b) n (a,s)))’, ‘SUC n’]
                      (simp o single o SIMP_RULE std_ss []) MINIMAL_EQ
       >> qspecl_then [‘λn. ¬c(FST (FUNPOW (UNCURRY b) (SUC n) (a,s)))’, ‘n’]
                      (simp o single o SIMP_RULE std_ss []) MINIMAL_EQ
       >> rw[EQ_IMP_THM]
       >> rename [‘k < SUC n’] >> Cases_on ‘k’ >> gvs[])
   >> RW_TAC std_ss []
   >> POP_ASSUM K_TAC
   >> RW_TAC std_ss [FUNPOW, o_DEF]
   >> Know
      `prefix_set x' INTER
       {s | (n = LEAST x. ~c (FST (FUNPOW (UNCURRY b) x (b a s)))) /\
            ~c (FST (FUNPOW (UNCURRY b) n (b a s)))} =
       prefix_set x' INTER
       {s |
        (n =
         LEAST x.
           ~c (FST (FUNPOW (UNCURRY b) x (FST (b a (prefix_seq x')),s)))) /\
        ~c (FST (FUNPOW (UNCURRY b) n (FST (b a (prefix_seq x')),s)))} o
       sdrop (LENGTH x')`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_o]
       >> Know `!a b c. (a ==> (b = c)) ==> (a /\ b = a /\ c)`
       >- PROVE_TAC []
       >> DISCH_THEN MATCH_MP_TAC
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!a l s. P a l s`  (MP_TAC o Q.SPECL [`a`, `x'`, `x`])
       >> RW_TAC std_ss [])
   >> DISCH_THEN (REWRITE_TAC o wrap o ONCE_REWRITE_RULE [INTER_COMM])
   >> ONCE_REWRITE_TAC [INTER_COMM]
   >> RW_TAC std_ss [PROB_BERN_PREFIX_SET_INTER_SDROP]
QED

val PROB_WHILE_WITNESS_CLOSED = store_thm
  ("PROB_WHILE_WITNESS_CLOSED",
   ``!c b a s.
       (?n. ~c (FST (FUNPOW (UNCURRY b) n (a, s)))) =
       ~c a \/ (?n. ~c (FST (FUNPOW (UNCURRY b) n (b a s))))``,
   RW_TAC std_ss []
   >> EQ_TAC >|
   [RW_TAC std_ss []
    >> POP_ASSUM MP_TAC
    >> Cases_on `n`
    >> RW_TAC std_ss [FUNPOW]
    >> PROVE_TAC [],
    RW_TAC std_ss [] >|
    [Q.EXISTS_TAC `0`
     >> RW_TAC std_ss [FUNPOW],
     Q.EXISTS_TAC `SUC n`
     >> RW_TAC std_ss [FUNPOW]]]);

Theorem PROB_WHILE_WITNESS_BIND:
  !c b a.
    prob_while_witness c b a =
    if c a then BIND (b a) (prob_while_witness c b) else UNIT a
Proof
  simp[FUN_EQ_THM, prob_while_witness_def, UNIT_DEF, BIND_DEF] >>
  simp[Once whileTheory.OWHILE_THM] >> rw[] >>
  rename [‘_ = _ _ (b a s)’] >>
  Cases_on ‘b a s’ >> simp[prob_while_witness_def]
QED

Theorem PREFIX_COVER_STAR_FIXES_FN:
  !c b bc ca a s l n.
    (!a. prefix_cover (ca a)) /\
    (!a l s.
       l IN ca a /\ s IN prefix_set l ==>
       (b a s = (FST (b a (prefix_seq l)), sdrop (LENGTH l) s))) /\
    (bc = (\a l. FST (b a (prefix_seq l)))) /\
    s IN prefix_set l /\
    l IN prefix_cover_level c bc ca a n ==>
    (prob_while_witness c b a s =
     (FST (prob_while_witness c b a (prefix_seq l)),
      sdrop (LENGTH l) s))
Proof
   REPEAT STRIP_TAC
   >> NTAC 2 (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`s`, `s`)
   >> Q.SPEC_TAC (`l`, `l`)
   >> Q.SPEC_TAC (`a`, `a`)
   >> Induct_on `n`
   >- (RW_TAC std_ss [prefix_cover_level_def, NOT_IN_EMPTY, IN_SING] >>
       ONCE_REWRITE_TAC [PROB_WHILE_WITNESS_BIND] >>
       simp[UNIT_DEF, sdrop_def])
   >> RW_TAC std_ss [prefix_cover_level_def, NOT_IN_EMPTY, append_sets_fn_def,
                     GSPECIFICATION, PROB_WHILE_WITNESS_BIND, BIND_DEF, o_THM]
   >> RW_TAC std_ss [UNCURRY]
   >> Q.PAT_X_ASSUM `s IN prefix_set (LL ++ y)` MP_TAC
   >> Q.MATCH_ABBREV_TAC `s IN prefix_set (l' ++ y) ==> Q`
   >> Q.UNABBREV_TAC `Q`
   >> markerLib.RM_ALL_ABBREVS_TAC
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `!a l s. P a l s /\ Q a l s ==> R a l s`
      (fn th =>
       MP_TAC (Q.SPECL [`a`, `l'`, `prefix_seq (APPEND l' y)`] th)
       >> MP_TAC (Q.SPECL [`a`, `l'`, `s`] th))
   >> impl_tac >- PROVE_TAC [SDROP_APPEND, PREFIX_SET_APPEND, PREFIX_SEQ]
   >> Rewr
   >> impl_tac >- PROVE_TAC [SDROP_APPEND, PREFIX_SET_APPEND, PREFIX_SEQ]
   >> Rewr
   >> RW_TAC std_ss [SDROP_PREFIX_SEQ_APPEND]
   >> Q.PAT_X_ASSUM `!a l s. P a l s`
      (MP_TAC o
       Q.SPECL [`FST ((b : 'a -> (num -> bool) -> 'a # (num -> bool)) a
                      (prefix_seq (l' : bool list)))`, `y`,
                `sdrop (LENGTH (l' : bool list)) s`])
   >> impl_tac >- PROVE_TAC [SDROP_APPEND]
   >> impl_tac >- PROVE_TAC []
   >> Rewr
   >> RW_TAC std_ss [LENGTH_APPEND]
   >> ONCE_REWRITE_TAC [ADD_COMM]
   >> RW_TAC std_ss [SDROP_ADD]
QED

Theorem PROB_WHILE_WITNESS_COUNTABLE_RANGE:
  !c b (a : 'a).
    (!a. b a IN indep_fn) ==>
    countable (range (FST o prob_while_witness c b a))
Proof
   RW_TAC std_ss []
   >> MATCH_MP_TAC COUNTABLE_SUBSET
   >> Q.EXISTS_TAC
      `FST (ARB : 'a # (num -> bool)) INSERT
       BIGUNION (IMAGE (\n. range (FST o FUNPOW (UNCURRY b) n o UNIT a)) UNIV)`
   >> reverse (RW_TAC bool_ss [countable_INSERT, SUBSET_DEF, IN_INSERT,
                               IN_BIGUNION_IMAGE, IN_UNIV])
   >- (MATCH_MP_TAC COUNTABLE_BIGUNION
       >> RW_TAC bool_ss [IN_IMAGE, IN_UNIV, COUNTABLE_IMAGE_NUM]
       >> Know `FUNPOW (UNCURRY b) n o UNIT a IN indep_fn`
       >- RW_TAC bool_ss [INDEP_FN_FUNPOW]
       >> RW_TAC bool_ss [indep_fn_def, GSPECIFICATION])
   >> POP_ASSUM MP_TAC
   >> simp[range_def, IN_IMAGE, IN_UNIV, o_THM, prob_while_witness_def,
           UNIT_DEF, PULL_EXISTS]
   >> qx_gen_tac ‘y’ >> Cases_on ‘OWHILE (c o FST) (UNCURRY b) (a,y)’
   >> simp[]
   >> gvs[whileTheory.OWHILE_def, AllCaseEqs()]
   >> PROVE_TAC []
QED

val EVENTS_COMPL_BERN = save_thm
  ("EVENTS_COMPL_BERN",
    REWRITE_RULE [PROB_SPACE_BERN, SPACE_BERN_UNIV, GSYM COMPL_DEF] (ISPEC ``bern`` EVENTS_COMPL));

Theorem PROB_WHILE_WITNESS_MEASURABLE_FST:
  !c b (a : 'a).
    (!a. b a IN indep_fn) ==>
    FST o prob_while_witness c b a IN
        measurable (p_space bern, events bern) (UNIV, UNIV)
Proof
  RW_TAC std_ss [IN_MEASURABLE, IN_UNIV, UNIV_SIGMA_ALGEBRA, SIGMA_ALGEBRA_BERN,
                 space_def, subsets_def, SPACE_BERN_UNIV, INTER_UNIV, IN_FUNSET]
  >> Know
      `PREIMAGE (FST o prob_while_witness c b a) s =
       (if FST (ARB : 'a # (num -> bool)) IN s then
          COMPL {x | ?n. ~c (FST (FUNPOW (UNCURRY b) n (a, x)))}
        else {}) UNION
       ({x | ?n. ~c (FST (FUNPOW (UNCURRY b) n (a, x)))} INTER
        BIGUNION
        (IMAGE
         (\m.
            {x | FST (FUNPOW (UNCURRY b) m (a, x)) IN s /\
                 (m = LEAST n. ~c (FST (FUNPOW (UNCURRY b) n (a, x)))) /\
                 ~c (FST (FUNPOW (UNCURRY b) m (a, x)))})
         UNIV))`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_PREIMAGE, o_THM, IN_UNION, IN_INTER,
                         GSPECIFICATION, NOT_IN_EMPTY,
                         prob_while_witness_def, IN_COMPL]
          (* 2 sub-goals here *)
       >> rename [‘OWHILE _ _ (a,x)’]
       >> Cases_on ‘OWHILE (c o FST) (UNCURRY b) (a,x)’
       >> gs[whileTheory.OWHILE_EQ_NONE, PULL_EXISTS]
       >> gvs[whileTheory.OWHILE_def, AllCaseEqs()]
       >> numLib.LEAST_ELIM_TAC
       >> simp[SF SFY_ss]
       >> metis_tac[])
   >> Rewr
   >> Know `!n. (FUNPOW (UNCURRY b) n o UNIT a) IN indep_fn`
   >- RW_TAC std_ss [INDEP_FN_FUNPOW]
   >> STRIP_TAC
   >> Know `!n. {x | ~c (FST (FUNPOW (UNCURRY b) n (a, x)))} IN events bern`
   >- (STRIP_TAC
       >> Know
          `{x | ~c (FST (FUNPOW (UNCURRY b) n (a, x)))} =
           PREIMAGE (FST o FUNPOW (UNCURRY b) n o UNIT a) {a' | ~c a'}`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [IN_PREIMAGE, GSPECIFICATION, UNIT_DEF, o_THM])
       >> POP_ASSUM (MP_TAC o Q.SPEC `n`)
       >> RW_TAC std_ss [indep_fn_def, GSPECIFICATION, IN_MEASURABLE, IN_UNIV]
       >> FULL_SIMP_TAC std_ss [space_def, subsets_def, IN_FUNSET, IN_UNIV,
                                SPACE_BERN_UNIV, INTER_UNIV])
   >> STRIP_TAC
   >> Know `{x | ?n. ~c (FST (FUNPOW (UNCURRY b) n (a, x)))} IN events bern`
   >- (RW_TAC std_ss [GBIGUNION_IMAGE]
       >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       >> RW_TAC std_ss [PROB_SPACE_BERN, SUBSET_DEF, IN_IMAGE, IN_UNIV,
                         COUNTABLE_IMAGE_NUM]
       >> RW_TAC std_ss [])
   >> STRIP_TAC
   >> MATCH_MP_TAC EVENTS_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_COMPL_BERN, EVENTS_EMPTY]
   >> MATCH_MP_TAC EVENTS_INTER
   >> RW_TAC std_ss [PROB_SPACE_BERN]
   >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_IMAGE_NUM, SUBSET_DEF, IN_IMAGE,
                     IN_UNIV]
   >> Ho_Rewrite.ONCE_REWRITE_TAC [GINTER]
   >> MATCH_MP_TAC EVENTS_INTER
   >> reverse (RW_TAC std_ss [PROB_SPACE_BERN]) (* 2 sub-goals here *)
   >- (ONCE_REWRITE_TAC [CONJ_COMM]
       >> qspecl_then [‘λn. ¬c (FST (FUNPOW (UNCURRY b) n (a,s)))’, ‘m’]
                      (simp o single o SIMP_RULE std_ss [] o Q.GEN ‘s’)
                      MINIMAL_EQ
       >> RW_TAC std_ss [GINTER]
       >> MATCH_MP_TAC EVENTS_INTER
       >> RW_TAC std_ss [PROB_SPACE_BERN]
       >> Know
          `{s | !n. n < m ==> c (FST (FUNPOW (UNCURRY b) n (a,s)))} =
           COMPL
           (BIGUNION
            (IMAGE (\n. {s | ~c (FST (FUNPOW (UNCURRY b) n (a,s)))})
             (count m)))`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [IN_BIGUNION_IMAGE, GSPECIFICATION, IN_COMPL,
                             IN_COUNT]
           >> PROVE_TAC [])
       >> Rewr
       >> MATCH_MP_TAC EVENTS_COMPL_BERN
       >> RW_TAC std_ss [PROB_SPACE_BERN]
       >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_COUNT, SUBSET_DEF,
                         IN_IMAGE, IN_UNIV, image_countable]
       >> RW_TAC std_ss [])
   >> Know
      `{x | FST (FUNPOW (UNCURRY b) m (a,x)) IN s} =
       PREIMAGE (FST o FUNPOW (UNCURRY b) m o UNIT a) s`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_PREIMAGE, o_THM, UNIT_DEF])
   >> Rewr
   >> Q.PAT_X_ASSUM `!n. X n IN indep_fn` (MP_TAC o Q.SPEC `m`)
   >> RW_TAC std_ss [indep_fn_def, GSPECIFICATION, IN_MEASURABLE, IN_UNIV]
   >> FULL_SIMP_TAC std_ss [space_def, subsets_def, IN_UNIV, SPACE_BERN_UNIV,
                            INTER_UNIV]
QED

Theorem PROB_WHILE_WITNESS_MEASURABLE_SND:
  !c b (a : 'a).
    (!a. b a IN indep_fn) ==>
    SND o prob_while_witness c b a IN
        measurable (p_space bern, events bern) (p_space bern, events bern)
Proof
  RW_TAC bool_ss [IN_MEASURABLE, IN_UNIV, SIGMA_ALGEBRA_BERN, space_def,
                  subsets_def, SPACE_BERN_UNIV, INTER_UNIV, IN_FUNSET, IN_UNIV]
  >> Know
      `PREIMAGE (SND o prob_while_witness c b a) s =
       (if SND (ARB : 'a # (num -> bool)) IN s then
          COMPL {x | ?n. ~c (FST (FUNPOW (UNCURRY b) n (a, x)))}
        else {}) UNION
       ({x | ?n. ~c (FST (FUNPOW (UNCURRY b) n (a, x)))} INTER
        BIGUNION
        (IMAGE
         (\m.
            {x | SND (FUNPOW (UNCURRY b) m (a, x)) IN s /\
                 (m = LEAST n. ~c (FST (FUNPOW (UNCURRY b) n (a, x)))) /\
                 ~c (FST (FUNPOW (UNCURRY b) m (a, x)))})
         UNIV))`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_PREIMAGE, o_THM, IN_UNION, IN_INTER,
                         GSPECIFICATION, NOT_IN_EMPTY,
                         prob_while_witness_def, IN_COMPL]
                         (* 2 sub-goals here *)
       >> rename [‘OWHILE _ _ (a,x)’]
       >> Cases_on ‘OWHILE (c o FST) (UNCURRY b) (a,x)’
       >> gs[whileTheory.OWHILE_EQ_NONE, PULL_EXISTS]
       >> gvs[whileTheory.OWHILE_def, AllCaseEqs()]
       >> numLib.LEAST_ELIM_TAC
       >> simp[SF SFY_ss]
       >> metis_tac[])
   >> Rewr
   >> Know `!n. (FUNPOW (UNCURRY b) n o UNIT a) IN indep_fn`
   >- RW_TAC std_ss [INDEP_FN_FUNPOW]
   >> STRIP_TAC
   >> Know `!n. {x | ~c (FST (FUNPOW (UNCURRY b) n (a, x)))} IN events bern`
   >- (STRIP_TAC
       >> Know
          `{x | ~c (FST (FUNPOW (UNCURRY b) n (a, x)))} =
           PREIMAGE (FST o FUNPOW (UNCURRY b) n o UNIT a) {a' | ~c a'}`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [IN_PREIMAGE, GSPECIFICATION, UNIT_DEF, o_THM])
       >> POP_ASSUM (MP_TAC o Q.SPEC `n`)
       >> RW_TAC std_ss [indep_fn_def, GSPECIFICATION, IN_MEASURABLE, IN_UNIV]
       >> FULL_SIMP_TAC std_ss [space_def, subsets_def, IN_UNIV, SPACE_BERN_UNIV, INTER_UNIV])
   >> STRIP_TAC
   >> Know `{x | ?n. ~c (FST (FUNPOW (UNCURRY b) n (a, x)))} IN events bern`
   >- (RW_TAC std_ss [GBIGUNION_IMAGE]
       >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       >> RW_TAC std_ss [PROB_SPACE_BERN, SUBSET_DEF, IN_IMAGE, IN_UNIV,
                         COUNTABLE_IMAGE_NUM]
       >> RW_TAC std_ss [])
   >> STRIP_TAC
   >> MATCH_MP_TAC EVENTS_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_COMPL_BERN, EVENTS_EMPTY]
   >> MATCH_MP_TAC EVENTS_INTER
   >> RW_TAC std_ss [PROB_SPACE_BERN]
   >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_IMAGE_NUM, SUBSET_DEF, IN_IMAGE,
                     IN_UNIV]
   >> Ho_Rewrite.ONCE_REWRITE_TAC [GINTER]
   >> MATCH_MP_TAC EVENTS_INTER
   >> reverse (RW_TAC std_ss [PROB_SPACE_BERN]) (* 2 sub-goals here *)
   >- (ONCE_REWRITE_TAC [CONJ_COMM]
       >> qspecl_then [‘λn. ¬c(FST (FUNPOW (UNCURRY b) n (a,ss)))’, ‘m’]
                      (simp o single o SIMP_RULE std_ss [] o Q.GEN ‘ss’)
                      MINIMAL_EQ
       >> RW_TAC std_ss [GINTER]
       >> MATCH_MP_TAC EVENTS_INTER
       >> RW_TAC std_ss [PROB_SPACE_BERN]
       >> Know
          `{s | !n. n < m ==> c (FST (FUNPOW (UNCURRY b) n (a,s)))} =
           COMPL
           (BIGUNION
            (IMAGE (\n. {s | ~c (FST (FUNPOW (UNCURRY b) n (a,s)))})
             (count m)))`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [IN_BIGUNION_IMAGE, GSPECIFICATION, IN_COMPL,
                             IN_COUNT]
           >> PROVE_TAC [])
       >> Rewr
       >> MATCH_MP_TAC EVENTS_COMPL_BERN
       >> RW_TAC std_ss [PROB_SPACE_BERN]
       >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_COUNT, SUBSET_DEF,
                         IN_IMAGE, IN_UNIV, image_countable]
       >> RW_TAC std_ss [])
   >> Know
      `{x | SND (FUNPOW (UNCURRY b) m (a,x)) IN s} =
       PREIMAGE (SND o FUNPOW (UNCURRY b) m o UNIT a) s`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_PREIMAGE, o_THM, UNIT_DEF])
   >> Rewr
   >> Q.PAT_X_ASSUM `!n. X n IN indep_fn` (MP_TAC o Q.SPEC `m`)
   >> RW_TAC std_ss [indep_fn_def, GSPECIFICATION, IN_MEASURABLE, IN_UNIV]
   >> FULL_SIMP_TAC std_ss [space_def, subsets_def, IN_UNIV, SPACE_BERN_UNIV,
                            INTER_UNIV]
QED

val PROB_WHILE_EXISTS = store_thm
  ("PROB_WHILE_EXISTS",
   ``!c : 'a -> bool. !b : 'a -> (num -> bool) -> 'a # (num -> bool).
       (!a. b a IN indep_fn) /\ prob_while_terminates c b ==>
       ?prob_while : 'a -> (num -> bool) -> 'a # (num -> bool).
         !a.
           prob_while a IN indep_fn /\
           (prob_while a = if c a then BIND (b a) prob_while else UNIT a)``,
   RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!a. P a`
      (fn th =>
       MP_TAC (REWRITE_RULE [indep_fn_def] th)
       >> ASSUME_TAC th)
   >> RW_TAC std_ss [GSPECIFICATION, FORALL_AND_THM]
   >> Q.PAT_X_ASSUM `!a. P a` (MP_TAC o CONV_RULE SKOLEM_CONV)
   >> RW_TAC std_ss [FORALL_AND_THM]
   >> Q.EXISTS_TAC `prob_while_witness c b`
   >> Ho_Rewrite.REWRITE_TAC [GSYM FORALL_AND_THM]
   >> STRIP_TAC
   >> (MP_TAC o
       INST_TYPE [beta |-> ``:num -> bool``] o
       Q.SPECL [`c`, `b`, `\a l. FST (b a (prefix_seq l))`, `c'`, `a`])
       PROB_WHILE_TERMINATES_PREFIX_COVER_STAR
   >> impl_tac >- RW_TAC std_ss []
   >> STRIP_TAC
   >> reverse CONJ_TAC >- RW_TAC std_ss [PROB_WHILE_WITNESS_BIND]
   >> SIMP_TAC std_ss [indep_fn_def, GSPECIFICATION]
   >> CONJ_TAC >- RW_TAC std_ss [PROB_WHILE_WITNESS_COUNTABLE_RANGE]
   >> CONJ_TAC >- RW_TAC std_ss [PROB_WHILE_WITNESS_MEASURABLE_FST]
   >> CONJ_TAC >- RW_TAC std_ss [PROB_WHILE_WITNESS_MEASURABLE_SND]
   >> Q.EXISTS_TAC `prefix_cover_star c (\a l. FST (b a (prefix_seq l))) c' a`
   >> RW_TAC std_ss [prefix_cover_star_def, IN_BIGUNION_IMAGE, IN_UNIV]
   >> (MP_TAC o
       INST_TYPE [beta |-> ``:num -> bool``] o
       Q.SPECL [`c`, `b`, `\a l. FST (b a (prefix_seq l))`, `c'`, `a`,
                `s`, `l`, `x`])
      PREFIX_COVER_STAR_FIXES_FN
   >> impl_tac >- RW_TAC std_ss []
   >> RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* A cluster of late definitions; prob_while requires some of the above      *)
(* theorems for an application of new_specification.                         *)
(* ------------------------------------------------------------------------- *)

local
  val thm =
    CONV_RULE
    (DEPTH_CONV RIGHT_IMP_EXISTS_CONV THENC
     REDEPTH_CONV (CHANGED_CONV SKOLEM_CONV))
    PROB_WHILE_EXISTS
in
  val prob_while_def =
      new_specification ("prob_while_def", ["prob_while"], thm);
end;

val prob_until_def = Define
  `prob_until b c = BIND b (prob_while ($~ o c) (K b))`;

val prob_repeat_def = Define
  `prob_repeat a = MMAP THE (prob_until a IS_SOME)`;

val prob_while_cost_def = Define
  `prob_while_cost c b = prob_while (c o FST) (prob_cost SUC b)`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* ------------------------------------------------------------------------- *)

val PROB_WHILE_CUT_REV = store_thm
  ("PROB_WHILE_CUT_REV",
   ``!c b n a.
       prob_while_cut c b (SUC n) a =
       BIND (prob_while_cut c b n a) (\a'. if c a' then b a' else UNIT a')``,
   Induct_on `n`
   >- (FUN_EQ_TAC
       >> RW_TAC std_ss [prob_while_cut_def, BIND_DEF, UNCURRY, o_THM,
                         UNIT_DEF])
   >> REPEAT GEN_TAC
   >> ONCE_REWRITE_TAC [prob_while_cut_def]
   >> reverse (Cases_on `c a`)
   >- RW_TAC std_ss [BIND_DEF, UNIT_DEF, o_DEF, UNCURRY]
   >> RW_TAC std_ss [GSYM BIND_ASSOC]
   >> AP_TERM_TAC
   >> FUN_EQ_TAC
   >> RW_TAC std_ss []);

val PROB_WHILE_TERMINATES_EVENTS = store_thm
  ("PROB_WHILE_TERMINATES_EVENTS",
   ``!c b.
       (!a. b a IN indep_fn) ==>
       {s | ?n. ~c (FST (FUNPOW (UNCURRY b) n (a,s)))} IN events bern``,
   RW_TAC std_ss [GBIGUNION_IMAGE]
   >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_IMAGE_NUM, SUBSET_DEF, IN_IMAGE,
                     IN_UNIV]
   >> Know
      `{s | ~c (FST (FUNPOW (UNCURRY b) n (a,s)))} =
       PREIMAGE (FST o FUNPOW (UNCURRY b) n o UNIT a) {s | ~c s}`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_PREIMAGE, o_THM, UNIT_DEF])
   >> Rewr
   >> Know `(FUNPOW (UNCURRY b) n o UNIT a) IN indep_fn`
   >- PROVE_TAC [INDEP_FN_FUNPOW]
   >> RW_TAC std_ss [indep_fn_def, GSPECIFICATION, IN_MEASURABLE, IN_UNIV]
   >> FULL_SIMP_TAC std_ss [space_def, subsets_def, IN_UNIV, SPACE_BERN_UNIV, INTER_UNIV]);

val PROB_WHILE_TERMINATES_SUFFICIENT = store_thm
  ("PROB_WHILE_TERMINATES_SUFFICIENT",
   ``!c b.
       (!a. b a IN indep_fn) /\ (?*s. !a. ~c (FST (b a s))) ==>
       prob_while_terminates c b``,
   SIMP_TAC std_ss [probably_bern_def, probably_def, possibly_bern_def,
                    possibly_def, prob_while_terminates_def]
   >> NTAC 4 STRIP_TAC
   >> STRONG_CONJ_TAC
   >- RW_TAC std_ss [PROB_WHILE_TERMINATES_EVENTS]
   >> RW_TAC std_ss []
   >> POP_ASSUM MP_TAC
   >> Know `!p. (?n : num. p n) = ~(!n. ~p n)` >- RW_TAC std_ss []
   >> DISCH_THEN (Ho_Rewrite.PURE_ONCE_REWRITE_TAC o wrap)
   >> Ho_Rewrite.ONCE_REWRITE_TAC [GCOMPL]
   >> RW_TAC std_ss []
   >> Know
      `COMPL (COMPL {s | !n. c (FST (FUNPOW (UNCURRY b) n (a,s)))}) IN
       events bern`
   >- RW_TAC std_ss [EVENTS_COMPL_BERN, PROB_SPACE_BERN]
   >> POP_ASSUM K_TAC
   >> RW_TAC std_ss [PROB_COMPL_BERN, PROB_SPACE_BERN, COMPL_COMPL]
   >> Know `!x : real. (x = 0) ==> (1 - x = 1)` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   >> reverse CONJ_TAC
   >- PROVE_TAC [PROB_POSITIVE, PROB_SPACE_BERN]
   >> MATCH_MP_TAC LE_SEQ_IMP_LE_LIM
   >> Q.EXISTS_TAC `\N. prob bern {s | c (FST (prob_while_cut c b N a s))}`
   >> RW_TAC std_ss []
   >- (MATCH_MP_TAC PROB_INCREASING
       >> RW_TAC std_ss [PROB_SPACE_BERN, SUBSET_DEF, GSPECIFICATION]
       >- (Suff
           `{s | c (FST (prob_while_cut c b n a s))} =
            (c o FST o prob_while_cut c b n a)`
           >- (RW_TAC std_ss []
               >> PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_WHILE_CUT])
           >> SET_EQ_TAC
           >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM]
           >> RW_TAC std_ss [SPECIFICATION])
       >> Suff `prob_while_cut c b n a x = FUNPOW (UNCURRY b) n (a, x)`
       >- RW_TAC std_ss []
       >> Induct_on `n` >- RW_TAC std_ss [prob_while_cut_def, FUNPOW, UNIT_DEF]
       >> RW_TAC std_ss [PROB_WHILE_CUT_REV, FUNPOW_SUC, BIND_DEF, o_THM,
                         UNCURRY])
   >> MATCH_MP_TAC SER_ZERO
   >> MATCH_MP_TAC SER_POS_COMPAR
   >> Q.EXISTS_TAC `\n. (1 - prob bern {s | !a. ~c (FST (b a s))}) pow n`
   >> BETA_TAC
   >> Know `!n. {s | c (FST (prob_while_cut c b n a s))} IN events bern`
   >- (STRIP_TAC
       >> Know
          `{s | c (FST (prob_while_cut c b n a s))} =
           c o FST o prob_while_cut c b n a`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [GSPECIFICATION]
           >> RW_TAC std_ss [SPECIFICATION, o_DEF])
       >> RW_TAC std_ss []
       >> PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_WHILE_CUT])
   >> STRIP_TAC
   >> CONJ_TAC
   >- (RW_TAC std_ss []
       >> MATCH_MP_TAC PROB_POSITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN])
   >> CONJ_TAC
   >- ((MP_TAC o
        INST_TYPE [beta |-> alpha, gamma |-> ``:num -> bool``] o
        Q.SPEC `1 - prob bern {s | !a. ~c (FST (b a s))}`) GP
       >> impl_tac
       >- (MATCH_MP_TAC ABS_1_MINUS_PROB
           >> RW_TAC std_ss [PROB_SPACE_BERN])
       >> RW_TAC std_ss [SUMS_EQ])
   >> STRIP_TAC
   >> MATCH_MP_TAC PROB_BERN_PROB_WHILE_CUT
   >> RW_TAC std_ss []
   >> Know `{s | c (FST (b a' s))} IN events bern`
   >- (Suff `{s | c (FST (b a' s))} = c o FST o b a'`
       >- PROVE_TAC [INDEP_FN_FST_EVENTS]
       >> SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION]
       >> RW_TAC std_ss [SPECIFICATION, o_THM])
   >> STRIP_TAC
   >> Know
      `prob bern {s | c (FST (b a' s))} =
       1 - prob bern (COMPL {s | c (FST (b a' s))})`
   >- (RW_TAC std_ss [PROB_COMPL_BERN, PROB_SPACE_BERN]
       >> REAL_ARITH_TAC)
   >> Rewr'
   >> Know `!a b : real. a <= b ==> 1 - b <= 1 - a` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> MATCH_MP_TAC PROB_INCREASING
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_COMPL_BERN, SUBSET_DEF, IN_COMPL,
                     GSPECIFICATION]);

val INDEP_FN_PROB_WHILE = store_thm
  ("INDEP_FN_PROB_WHILE",
   ``!c b a.
       (!a. b a IN indep_fn) /\ prob_while_terminates c b ==>
       prob_while c b a IN indep_fn``,
   RW_TAC std_ss [prob_while_def]);

val PROB_WHILE_ADVANCE = store_thm
  ("PROB_WHILE_ADVANCE",
   ``!c b a.
       (!a. b a IN indep_fn) /\ prob_while_terminates c b ==>
       (prob_while c b a =
        (if c a then BIND (b a) (prob_while c b) else UNIT a))``,
   PROVE_TAC [prob_while_def]);

val PROB_BERN_UNIVERSAL = store_thm
  ("PROB_BERN_UNIVERSAL",
   ``!p e e'.
       e IN events bern /\ e' IN events bern /\ $!* p /\
       (!x. p x ==> (x IN e = x IN e')) ==>
       (prob bern e = prob bern e')``,
   RW_TAC std_ss [probably_bern_def, probably_def]
   >> (MP_TAC o
       Q.SPECL [`e`, `{s | p s}`] o
       Q.ISPEC `bern`) PROB_ONE_INTER
   >> impl_tac >- RW_TAC std_ss [PROB_SPACE_BERN]
   >> DISCH_THEN (REWRITE_TAC o wrap o SYM)
   >> Know `e INTER {s | p s} IN events bern`
   >- PROVE_TAC [EVENTS_INTER, PROB_SPACE_BERN]
   >> Know `e INTER {s | p s} = e' INTER {s | p s}`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_INTER, GSPECIFICATION]
       >> ONCE_REWRITE_TAC [CONJ_COMM]
       >> MATCH_MP_TAC CONJ_EQ_IMP
       >> PROVE_TAC [])
   >> Rewr
   >> STRIP_TAC
   >> MATCH_MP_TAC PROB_ONE_INTER
   >> RW_TAC std_ss [PROB_SPACE_BERN]);

val EVENTS_BERN_IMAGE_SDROP = store_thm
  ("EVENTS_BERN_IMAGE_SDROP",
   ``!n s. s IN events bern ==> IMAGE (sdrop n) s IN events bern``,
   RW_TAC std_ss []
   >> Induct_on `n` >- RW_TAC std_ss [sdrop_def, IMAGE_I, I_THM]
   >> RW_TAC std_ss [GSYM STL_o_SDROP, GSYM IMAGE_IMAGE,
                     EVENTS_BERN_IMAGE_STL]);

val PROB_BERN_MIRROR_IMAGE_STL = store_thm
  ("PROB_BERN_MIRROR_IMAGE_STL",
   ``!s.
       s IN events bern /\ (s o mirror = s) ==>
       (prob bern (IMAGE stl s) = prob bern s)``,
   RW_TAC std_ss []
   >> Know `IMAGE stl s IN events bern` >- PROVE_TAC [EVENTS_BERN_IMAGE_STL]
   >> STRIP_TAC
   >> Suff `PREIMAGE stl (IMAGE stl s) = s`
   >- (DISCH_THEN (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [SYM th])))
       >> RW_TAC std_ss [PREIMAGE_ALT, PROB_BERN_STL])
   >> SET_EQ_TAC
   >> RW_TAC std_ss [IN_PREIMAGE, IN_IMAGE]
   >> reverse EQ_TAC >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> SEQ_CASES_TAC `x'`
   >> SEQ_CASES_TAC `x`
   >> FULL_SIMP_TAC std_ss [STL_SCONS]
   >> Q.PAT_X_ASSUM `s o mirror = s` MP_TAC
   >> SET_EQ_TAC
   >> RW_TAC std_ss [IN_o]
   >> Know `mirror (scons h t) IN s` >- PROVE_TAC []
   >> POP_ASSUM K_TAC
   >> RW_TAC std_ss [MIRROR_SCONS]
   >> NTAC 2 (POP_ASSUM MP_TAC)
   >> KILL_TAC
   >> Cases_on `h`
   >> Cases_on `h'`
   >> RW_TAC std_ss []);

val EVENTS_BERN_NONEVENT_SEQ = store_thm
  ("EVENTS_BERN_NONEVENT_SEQ",
   ``!n. nonevent IN events bern ==> nonevent_seq n IN events bern``,
   RW_TAC std_ss []
   >> Induct_on `n` >- RW_TAC std_ss [nonevent_seq_def]
   >> RW_TAC std_ss [nonevent_seq_def]
   >> MATCH_MP_TAC EVENTS_BERN_IMAGE_STL
   >> MATCH_MP_TAC EVENTS_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_MIRROR]);

val PROB_BERN_MIRROR = store_thm
  ("PROB_BERN_MIRROR",
   ``!s. s IN events bern ==> (prob bern (s o mirror) = prob bern s)``,
   RW_TAC std_ss []
   >> MP_TAC PROB_PRESERVING_BERN_MIRROR
   >> RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION, PREIMAGE_ALT,
                     SPACE_BERN_UNIV, INTER_UNIV]);

val NONEVENT_SEQ_ALT = store_thm
  ("NONEVENT_SEQ_ALT",
   ``!n. nonevent_seq n = IMAGE (sdrop n) nonevent``,
   Induct >- RW_TAC std_ss [nonevent_seq_def, sdrop_def, IMAGE_I, I_THM]
   >> RW_TAC std_ss [nonevent_seq_def, GSYM STL_o_SDROP]
   >> SET_EQ_TAC
   >> PSET_TAC [o_THM]
   >> PROVE_TAC [STL_MIRROR]);

val EVENTUALLY_IN_NONEVENT = store_thm
  ("EVENTUALLY_IN_NONEVENT",
   ``!x y. x IN nonevent /\ y IN nonevent /\ eventually x y ==> (x = y)``,
   RW_TAC std_ss [nonevent_def, IN_IMAGE, IN_UNIV]
   >> Know `?y. eventually x' y` >- PROVE_TAC [EVENTUALLY_REFL]
   >> RW_TAC std_ss [EXISTS_DEF]
   >> Know `?y. eventually x'' y` >- PROVE_TAC [EVENTUALLY_REFL]
   >> RW_TAC std_ss [EXISTS_DEF]
   >> Suff `eventually x' = eventually x''` >- RW_TAC std_ss []
   >> REPEAT (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`@y. eventually x' y`, `z`)
   >> Q.SPEC_TAC (`@y. eventually x'' y`, `w`)
   >> RW_TAC std_ss []
   >> FUN_EQ_TAC
   >> PROVE_TAC [EVENTUALLY_TRANS, EVENTUALLY_SYM]);

val NONEVENT_SEQ_SDROP_INJ = store_thm
  ("NONEVENT_SEQ_SDROP_INJ",
   ``!n. INJ (sdrop n) nonevent (nonevent_seq n)``,
   RW_TAC std_ss [INJ_DEF, NONEVENT_SEQ_ALT, IN_IMAGE] >- PROVE_TAC []
   >> Know `eventually x y` >- PROVE_TAC [eventually_def]
   >> PROVE_TAC [EVENTUALLY_IN_NONEVENT]);

Theorem PROB_BERN_NONEVENT_SEQ:
  !n.
    nonevent IN events bern ==>
    (prob bern (nonevent_seq n) = 2 pow n * prob bern nonevent)
Proof
   RW_TAC std_ss []
   >> Induct_on `n` >- RW_TAC real_ss [pow, nonevent_seq_def]
   >> RW_TAC real_ss [pow, nonevent_seq_def]
   >> MP_TAC
      (Q.SPEC `nonevent_seq n UNION nonevent_seq n o mirror`
       PROB_BERN_MIRROR_IMAGE_STL)
   >> Know `nonevent_seq n UNION nonevent_seq n o mirror IN events bern`
   >- RW_TAC std_ss [EVENTS_BERN_NONEVENT_SEQ, PROB_SPACE_BERN,
                     EVENTS_BERN_MIRROR, EVENTS_UNION]
   >> STRIP_TAC
   >> impl_tac
   >- (RW_TAC std_ss []
       >> SET_EQ_TAC
       >> PSET_TAC [MIRROR_MIRROR]
       >> PROVE_TAC [])
   >> Rewr
   >> Know
      `2 * 2 pow n * prob bern nonevent =
       2 pow n * prob bern nonevent + 2 pow n * prob bern nonevent`
   >- RW_TAC real_ss [REAL_DOUBLE, REAL_MUL_ASSOC]
   >> Rewr
   >> Q.PAT_X_ASSUM `X = Y` (REWRITE_TAC o wrap o SYM)
   >> MP_TAC (Q.SPEC `nonevent_seq n` PROB_BERN_MIRROR)
   >> impl_tac >- PROVE_TAC [EVENTS_BERN_NONEVENT_SEQ]
   >> DISCH_THEN
      (fn th => CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [SYM th]))))
   >> MATCH_MP_TAC PROB_ADDITIVE
   >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_MIRROR,
                     EVENTS_BERN_NONEVENT_SEQ, DISJOINT_ALT, IN_o]
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM K_TAC
   >> RW_TAC std_ss [NONEVENT_SEQ_ALT, IN_IMAGE]
   >> Cases_on `x' = x''` >- PROVE_TAC [MIRROR_NEQ]
   >> STRIP_TAC
   >> Suff `sdrop (SUC n) x' = sdrop (SUC n) x''`
   >- (MP_TAC (Q.SPEC `SUC n` NONEVENT_SEQ_SDROP_INJ)
       >> RW_TAC std_ss [INJ_DEF]
       >> PROVE_TAC [])
   >> RW_TAC std_ss [GSYM STL_o_SDROP, o_THM]
   >> PROVE_TAC [STL_MIRROR]
QED

val NONEVENT = store_thm
  ("NONEVENT",
   ``~(nonevent IN events bern)``,
   STRIP_TAC
   >> reverse (Cases_on `prob bern nonevent = 0`)
   >- (Know `0 < prob bern nonevent`
       >- (RW_TAC std_ss [REAL_LT_LE]
           >> MATCH_MP_TAC PROB_POSITIVE
           >> RW_TAC std_ss [PROB_SPACE_BERN])
       >> POP_ASSUM K_TAC
       >> STRIP_TAC
       >> MP_TAC (Q.SPEC `prob bern nonevent` POW_HALF_SMALL)
       >> RW_TAC std_ss []
       >> STRIP_TAC
       >> Know `2 pow n * (1 / 2) pow n < 2 pow n * prob bern nonevent`
       >- (MATCH_MP_TAC REAL_LT_LMUL_IMP
           >> RW_TAC std_ss []
           >> MATCH_MP_TAC REAL_POW_LT
           >> REAL_ARITH_TAC)
       >> RW_TAC std_ss [GSYM POW_MUL, HALF_CANCEL, POW_ONE]
       >> RW_TAC std_ss [GSYM PROB_BERN_NONEVENT_SEQ, REAL_NOT_LT]
       >> MATCH_MP_TAC PROB_LE_1
       >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_NONEVENT_SEQ])
   >> Suff `prob bern o (\n. nonevent_seq n o sdrop n) --> prob bern UNIV`
   >- (RW_TAC std_ss [PROB_BERN_BASIC]
       >> Suff `!n. (prob bern o (\n. nonevent_seq n o sdrop n)) n = 0`
       >- (RW_TAC std_ss [o_DEF]
           >> STRIP_TAC
           >> Suff `(0 : real) = 1` >- REAL_ARITH_TAC
           >> MP_TAC (Q.SPEC `0` SEQ_CONST)
           >> PROVE_TAC [SEQ_UNIQ])
       >> RW_TAC std_ss [o_THM, PROB_BERN_SDROP, EVENTS_BERN_NONEVENT_SEQ,
                         PROB_BERN_NONEVENT_SEQ]
       >> RW_TAC real_ss [])
   >> MATCH_MP_TAC PROB_INCREASING_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV, EVENTS_BERN_SDROP,
                     EVENTS_BERN_NONEVENT_SEQ, SUBSET_DEF, IN_o]
   >- (POP_ASSUM MP_TAC
       >> RW_TAC std_ss [NONEVENT_SEQ_ALT, IN_IMAGE]
       >> Know `n <= SUC n` >- DECIDE_TAC
       >> PROVE_TAC [SDROP_EQ_MONO])
   >> SET_EQ_TAC
   >> RW_TAC std_ss [IN_UNIV, IN_BIGUNION_IMAGE, IN_o, NONEVENT_SEQ_ALT,
                     IN_IMAGE]
   >> Know `(@y. eventually x y) IN nonevent`
   >- (RW_TAC std_ss [nonevent_def, IN_IMAGE, IN_UNIV]
       >> Q.EXISTS_TAC `x`
       >> RW_TAC std_ss [])
   >> STRIP_TAC
   >> Know `?y. eventually (x :num -> bool) (y :num -> bool)`
   >- PROVE_TAC [EVENTUALLY_REFL]
   >> DISCH_THEN (MP_TAC o REWRITE_RULE [EXISTS_DEF])
   >> BETA_TAC
   >> DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [eventually_def])
   >> PROVE_TAC []);

val PROB_WHILE_TERMINATES = store_thm
  ("PROB_WHILE_TERMINATES",
   ``!c b.
       prob_while_terminates c b =
       !a. !*s. ?n. ~c (FST (prob_while_cut c b n a s))``,
   RW_TAC std_ss [prob_while_terminates_def]
   >> Suff
      `!a s.
         (?n. ~c (FST (prob_while_cut c b n a s))) =
         (?n. ~c (FST (FUNPOW (UNCURRY b) n (a,s))))`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss []
   >> Know `!p q : bool. (~p = ~q) ==> (p = q)` >- PROVE_TAC []
   >> DISCH_THEN MATCH_MP_TAC
   >> CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
   >> RW_TAC std_ss [EQ_IMP_THM] >|
   [POP_ASSUM MP_TAC
    >> Q.SPEC_TAC (`s`, `s`)
    >> Q.SPEC_TAC (`a`, `a`)
    >> Induct_on `n`
    >- (RW_TAC std_ss [FUNPOW]
        >> POP_ASSUM (MP_TAC o Q.SPEC `0`)
        >> RW_TAC std_ss [prob_while_cut_def, UNIT_DEF])
    >> RW_TAC std_ss []
    >> RW_TAC std_ss [FUNPOW]
    >> Know `b a s = (FST (b a s), SND (b a s))`
    >- RW_TAC std_ss [PAIR]
    >> Rewr'
    >> Q.PAT_X_ASSUM `!a s. P a s` MATCH_MP_TAC
    >> RW_TAC std_ss []
    >> POP_ASSUM (fn th => MP_TAC (Q.SPEC `SUC n` th) >> MP_TAC (Q.SPEC `0` th))
    >> RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, BIND_DEF, UNCURRY, o_THM],
    POP_ASSUM MP_TAC
    >> Q.SPEC_TAC (`s`, `s`)
    >> Q.SPEC_TAC (`a`, `a`)
    >> Induct_on `n`
    >- (RW_TAC std_ss []
        >> POP_ASSUM (MP_TAC o Q.SPEC `0`)
        >> RW_TAC std_ss [FUNPOW, prob_while_cut_def, UNIT_DEF])
    >> RW_TAC std_ss []
    >> Know `c a`
    >- (POP_ASSUM (MP_TAC o Q.SPEC `0`)
        >> RW_TAC std_ss [FUNPOW])
    >> RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, BIND_DEF, o_THM, UNCURRY]
    >> Q.PAT_X_ASSUM `!a s. P a s` MATCH_MP_TAC
    >> RW_TAC std_ss []
    >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `SUC n`)
    >> RW_TAC std_ss [FUNPOW]]);

val PROBABLY_RES_FORALL = store_thm
  ("PROBABLY_RES_FORALL",
   ``!p m.
       countable p /\ (!x :: p. !*y. m x y) ==> (!*y. !x :: p. m x y)``,
   SIMP_TAC std_ss [probably_bern_def, probably_def, RES_FORALL]
   >> NTAC 3 STRIP_TAC
   >> Know
      `{s | !x. x IN p ==> m x s} =
       COMPL (BIGUNION (IMAGE (\x. COMPL {s | m x s}) p))`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_COMPL, IN_BIGUNION_IMAGE, GSPECIFICATION]
       >> PROVE_TAC [])
   >> Rewr
   >> Know `BIGUNION (IMAGE (\x. COMPL {s | m x s}) p) IN events bern`
   >- ( MATCH_MP_TAC EVENTS_COUNTABLE_UNION
        >> RW_TAC std_ss [PROB_SPACE_BERN, image_countable, SUBSET_DEF,
                          IN_IMAGE]
        >> MATCH_MP_TAC EVENTS_COMPL_BERN
        >> RW_TAC std_ss [])
   >> STRIP_TAC
   >> CONJ_TAC >- RW_TAC std_ss [EVENTS_COMPL_BERN]
   >> RW_TAC std_ss [PROB_COMPL_BERN]
   >> Know `!a : real. (a = 0) ==> (1 - a = 1)` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> MATCH_MP_TAC PROB_COUNTABLY_ZERO
   >> RW_TAC std_ss [PROB_SPACE_BERN, image_countable, IN_IMAGE, SUBSET_DEF]
   >- RW_TAC std_ss [EVENTS_COMPL_BERN]
   >> RW_TAC std_ss [PROB_COMPL_BERN]
   >> REAL_ARITH_TAC);

val PROBABLY_FORALL = store_thm
  ("PROBABLY_FORALL",
   ``!p : 'a -> (num -> bool) -> bool.
       countable (UNIV : 'a -> bool) /\ (!x. !*y. p x y) ==>
       (!*y. !x. p x y)``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`UNIV`, `p`] PROBABLY_RES_FORALL)
   >> RW_TAC std_ss [RES_FORALL_UNIV]);

val STRONG_PROB_WHILE = store_thm
  ("STRONG_PROB_WHILE",
   ``!p c b a.
       (!a. b a IN indep_fn) /\ prob_while_terminates c b /\
       (!*s. !n.
          ~c (FST (prob_while_cut c b n a s)) ==>
          p (FST (prob_while_cut c b n a s))) ==>
       !*s. p (FST (prob_while c b a s))``,
   RW_TAC std_ss []
   >> SIMP_TAC std_ss [probably_def, probably_bern_def]
   >> STRONG_CONJ_TAC
   >- (Suff `{s | p (FST (prob_while c b a s))} = p o FST o prob_while c b a`
       >- (Rewr
           >> PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_WHILE])
       >> SET_EQ_TAC
       >> PSET_TAC []
       >> RW_TAC std_ss [SPECIFICATION, o_THM])
   >> RW_TAC std_ss []
   >> Know `prob_while_terminates c b` >- PROVE_TAC []
   >> SIMP_TAC std_ss [PROB_WHILE_TERMINATES]
   >> DISCH_THEN (MP_TAC o Q.SPEC `a`)
   >> STRIP_TAC
   >> Know
      `{s | ?n. ~c (FST (prob_while_cut c b n a s))} INTER
       {s | p (FST (prob_while c b a s))} IN events bern`
   >- (MATCH_MP_TAC EVENTS_INTER
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [PROB_SPACE_BERN, probably_bern_def, probably_def])
   >> STRIP_TAC
   >> Know
      `prob bern {s | p (FST (prob_while c b a s))} =
       prob bern
       ({s | ?n. ~c (FST (prob_while_cut c b n a s))} INTER
        {s | p (FST (prob_while c b a s))})`
   >- (MATCH_MP_TAC PROB_BERN_UNIVERSAL
       >> Q.EXISTS_TAC `\s. ?n. ~c (FST (prob_while_cut c b n a s))`
       >> RW_TAC std_ss [GSPECIFICATION, IN_INTER])
   >> Rewr
   >> Know
      `{s | ?n. ~c (FST (prob_while_cut c b n a s)) /\
                p (FST (prob_while_cut c b n a s))} IN events bern`
   >- (RW_TAC std_ss [PROB_SPACE_BERN, GBIGUNION_IMAGE]
       >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                         IN_IMAGE, IN_UNIV]
       >> Suff
          `{s | ~c (FST (prob_while_cut c b n a s)) /\
                p (FST (prob_while_cut c b n a s))} =
           (\x. ~c x /\ p x) o FST o prob_while_cut c b n a`
       >- (Rewr
           >> PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_WHILE_CUT])
       >> KILL_TAC
       >> SET_EQ_TAC
       >> PSET_TAC []
       >> RW_TAC std_ss [SPECIFICATION, o_THM])
   >> STRIP_TAC
   >> Know
      `{s | ?n. ~c (FST (prob_while_cut c b n a s)) /\
                p (FST (prob_while_cut c b n a s))} INTER
       {s | p (FST (prob_while c b a s))} IN events bern`
   >- (MATCH_MP_TAC EVENTS_INTER
       >> RW_TAC std_ss [PROB_SPACE_BERN, GBIGUNION_IMAGE])
   >> STRIP_TAC
   >> Know
      `prob bern
       ({s | ?n. ~c (FST (prob_while_cut c b n a s))} INTER
        {s | p (FST (prob_while c b a s))}) =
       prob bern
       ({s | ?n. ~c (FST (prob_while_cut c b n a s)) /\
                 p (FST (prob_while_cut c b n a s))} INTER
        {s | p (FST (prob_while c b a s))})`
   >- (MATCH_MP_TAC PROB_BERN_UNIVERSAL
       >> Q.EXISTS_TAC
          `\s. !n.
             ~c (FST (prob_while_cut c b n a s)) ==>
             p (FST (prob_while_cut c b n a s))`
       >> RW_TAC std_ss [GSPECIFICATION, IN_INTER]
       >> PROVE_TAC [])
   >> Rewr
   >> Know
      `{s |
        ?n.
          ~c (FST (prob_while_cut c b n a s)) /\
          p (FST (prob_while_cut c b n a s))} INTER
       {s | p (FST (prob_while c b a s))} =
       {s |
        ?n.
          ~c (FST (prob_while_cut c b n a s)) /\
          p (FST (prob_while_cut c b n a s))}`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_INTER]
       >> Q.PAT_X_ASSUM `!a. b a IN indep_fn` MP_TAC
       >> Q.PAT_X_ASSUM `prob_while_terminates c b` MP_TAC
       >> KILL_TAC
       >> RW_TAC std_ss []
       >> Know `!b. b = b /\ T` >- PROVE_TAC []
       >> DISCH_THEN (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
       >> MATCH_MP_TAC CONJ_EQ_IMP
       >> RW_TAC std_ss []
       >> NTAC 2 (POP_ASSUM MP_TAC)
       >> Q.SPEC_TAC (`x`, `s`)
       >> Q.SPEC_TAC (`a`, `a`)
       >> Induct_on `n`
       >- RW_TAC std_ss [prob_while_cut_def, PROB_WHILE_ADVANCE, UNIT_DEF]
       >> RW_TAC std_ss [prob_while_cut_def, PROB_WHILE_ADVANCE]
       >> RW_TAC std_ss [BIND_DEF, UNCURRY, o_THM]
       >> Q.PAT_X_ASSUM `!a. P a` (MATCH_MP_TAC o REWRITE_RULE [AND_IMP_INTRO])
       >> NTAC 2 (POP_ASSUM MP_TAC)
       >> RW_TAC std_ss [BIND_DEF, UNCURRY, o_THM])
   >> Rewr
   >> Q.PAT_X_ASSUM `X IN events bern` K_TAC
   >> Q.PAT_X_ASSUM `!*s. ?n. P s n` MP_TAC
   >> RW_TAC std_ss [probably_bern_def, probably_def]
   >> Suff
      `prob bern
       {s |
        ?n.
          ~c (FST (prob_while_cut c b n a s)) /\
          p (FST (prob_while_cut c b n a s))} =
       prob bern {s | ?n. ~c (FST (prob_while_cut c b n a s))}`
   >- (Rewr
       >> RW_TAC std_ss [])
   >> POP_ASSUM K_TAC
   >> Q.PAT_X_ASSUM `X INTER Y IN Z` K_TAC
   >> Q.PAT_X_ASSUM `!n. P n` K_TAC
   >> Q.PAT_X_ASSUM `{s | p (FST (P s))} IN Z` K_TAC
   >> MATCH_MP_TAC PROB_BERN_UNIVERSAL
   >> Q.EXISTS_TAC
      `\s. !n.
         ~c (FST (prob_while_cut c b n a s)) ==>
         p (FST (prob_while_cut c b n a s))`
   >> RW_TAC std_ss [GSPECIFICATION]
   >> PROVE_TAC []);

val PROB_WHILE = store_thm
  ("PROB_WHILE",
   ``!p c b a.
       (!a. b a IN indep_fn) /\ prob_while_terminates c b /\
       (!n. !*s.
          ~c (FST (prob_while_cut c b n a s)) ==>
          p (FST (prob_while_cut c b n a s))) ==>
       !*s. p (FST (prob_while c b a s))``,
   RW_TAC std_ss []
   >> Suff
      `!*s. !n.
         ~c (FST (prob_while_cut c b n a s)) ==>
         p (FST (prob_while_cut c b n a s))`
   >- RW_TAC std_ss [STRONG_PROB_WHILE]
   >> HO_MATCH_MP_TAC PROBABLY_FORALL
   >> RW_TAC std_ss [COUNTABLE_NUM]);

val DEFINITELY_PROBABLY = store_thm
  ("DEFINITELY_PROBABLY",
   ``!p. $! p ==> $!* p``,
   REPEAT STRIP_TAC
   >> Know `{s | p s} = UNIV`
   >- (SET_EQ_TAC
       >> PSET_TAC []
       >> Q.SPEC_TAC (`x`, `x`)
       >> CONV_TAC (DEPTH_CONV ETA_CONV)
       >> POP_ASSUM ACCEPT_TAC)
   >> RW_TAC std_ss [probably_bern_def, probably_def, EVENTS_BERN_BASIC,
                     PROB_BERN_BASIC]);

val PROB_BERN_BIND_LOWER = store_thm
  ("PROB_BERN_BIND_LOWER",
   ``!p f g q x y.
       f IN indep_fn /\ (!a. g a IN indep_fn) /\
       (!a. a IN q ==> x <= prob bern (p o FST o g a)) /\
       (!a. ~(a IN q) ==> y <= prob bern (p o FST o g a)) ==>
       prob bern (q o FST o f) * x + (1 - prob bern (q o FST o f)) * y <=
       prob bern (p o FST o BIND f g)``,
   RW_TAC std_ss []
   >> (MP_TAC o
       Q.SPECL [`COMPL p`, `f`, `g`, `q`, `1 - x`, `1 - y`])
      PROB_BERN_BIND_UPPER
   >> SIMP_TAC std_ss [COMPL_o]
   >> impl_tac
   >- (RW_TAC std_ss [] >|
       [RES_TAC
        >> Know `p o FST o g a IN events bern`
        >- PROVE_TAC [INDEP_FN_FST_EVENTS]
        >> RW_TAC std_ss [PROB_COMPL_BERN]
        >> Q.PAT_X_ASSUM `X <= Y` MP_TAC
        >> REAL_ARITH_TAC,
        RES_TAC
        >> Know `p o FST o g a IN events bern`
        >- PROVE_TAC [INDEP_FN_FST_EVENTS]
        >> RW_TAC std_ss [PROB_COMPL_BERN]
        >> Q.PAT_X_ASSUM `X <= Y` MP_TAC
        >> REAL_ARITH_TAC])
   >> Know `p o FST o BIND f g IN events bern`
   >- PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_BIND]
   >> DISCH_THEN (fn th => SIMP_TAC std_ss [th, PROB_COMPL_BERN])
   >> KILL_TAC
   >> Q.SPEC_TAC (`prob bern (p o FST o BIND f g)`, `a`)
   >> Q.SPEC_TAC (`prob bern (q o FST o f)`, `b`)
   >> RW_TAC real_ss [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB,
                      REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB]
   >> POP_ASSUM MP_TAC
   >> REAL_ARITH_TAC);

val PROB_BERN_BIND = store_thm
  ("PROB_BERN_BIND",
   ``!p f g q x y.
       f IN indep_fn /\ (!a. g a IN indep_fn) /\
       (!a. a IN q ==> (prob bern (p o FST o g a) = x)) /\
       (!a. ~(a IN q) ==> (prob bern (p o FST o g a) = y)) ==>
       (prob bern (p o FST o BIND f g) =
        prob bern (q o FST o f) * x + (1 - prob bern (q o FST o f)) * y)``,
   RW_TAC std_ss [GSYM REAL_LE_ANTISYM] >|
   [MATCH_MP_TAC PROB_BERN_BIND_UPPER
    >> RW_TAC std_ss [],
    MATCH_MP_TAC PROB_BERN_BIND_LOWER
    >> RW_TAC std_ss []]);

val PROB_BERN_BIND_BOOL = store_thm
  ("PROB_BERN_BIND_BOOL",
   ``!f g p q.
       f IN indep_fn /\ (!x. g x IN indep_fn) /\
       (prob bern (FST o f) = p) ==>
       (prob bern (q o FST o BIND f g) =
        p * prob bern (q o FST o g T) + (1 - p) * prob bern (q o FST o g F))``,
   RW_TAC std_ss []
   >> (MP_TAC o
       INST_TYPE [beta |-> ``:num -> bool``] o
       Q.SPECL [`q`, `f`, `g`, `I`,
                `prob bern (q o FST o g T)`,
                `prob bern (q o FST o g F)`] o
       INST_TYPE [beta |-> bool])
      PROB_BERN_BIND
   >> RW_TAC std_ss [IN_I, I_o_ID]);

val PROBABLY_TRUE = store_thm
  ("PROBABLY_TRUE",
   ``!*s. T``,
   MATCH_MP_TAC DEFINITELY_PROBABLY
   >> RW_TAC std_ss []);

local
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val real_ss = real_ss -* ["lift_disj_eq", "lift_imp_disj"]
in
Theorem PROB_BERN_BIND_COUNTABLE:
   !p f g c.
       f IN indep_fn /\ (!a. g a IN indep_fn) /\
       (!x. x IN range (FST o f) ==> ?n. (c n = x)) ==>
       (\n.
         if (!m. m < n ==> ~(c m = c n)) then
           prob bern ($= (c n) o FST o f) *
           prob bern (p o FST o g (c n))
         else 0) sums
       prob bern (p o FST o BIND f g)
Proof
   RW_TAC std_ss []
   >> Know `countable (range (FST o f))`
   >- (RW_TAC std_ss [COUNTABLE_ALT]
       >> Q.EXISTS_TAC `c`
       >> PROVE_TAC [])
   >> RW_TAC std_ss [COUNTABLE_ALT_BIJ]
   >- ((MP_TAC o
        Q.ISPEC `range (FST o (f : (num -> bool) -> 'b # (num -> bool)))`)
       FINITE_BIJ_COUNT_EQ
       >> RW_TAC std_ss []
       >> MP_TAC (Q.SPECL [`p`, `f`, `g`, `c'`, `n`] PROB_BERN_BIND_FINITE)
       >> RW_TAC std_ss []
       >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
       >> Know
       `!n.
       (if !m. m < n ==> ~(c m = c n) then
          prob bern ($= (c n) o FST o f) * prob bern (p o FST o g (c n))
        else 0) =
       (if (!m. m < n ==> ~(c m = c n)) /\ c n IN range (FST o f) then
          prob bern ($= (c n) o FST o f) * prob bern (p o FST o g (c n))
        else 0)`
       >- (RW_TAC std_ss []
           >> Suff `($= (c n') o FST o f) = {}`
           >- RW_TAC real_ss [PROB_BERN_EMPTY]
           >> SET_EQ_TAC
           >> RW_TAC std_ss [NOT_IN_EMPTY]
           >> RW_TAC std_ss [SPECIFICATION, o_THM]
           >> POP_ASSUM MP_TAC
           >> RW_TAC std_ss [range_def, IN_IMAGE, IN_UNIV, o_THM])
       >> Rewr
       >> POP_ASSUM MP_TAC
       >> POP_ASSUM K_TAC
       >> POP_ASSUM MP_TAC
       >> Q.SPEC_TAC (`range (FST o f)`, `s`)
       >> Induct_on `n`
       >- (RW_TAC std_ss [sum, BIJ_DEF, SURJ_DEF, INJ_DEF, COUNT_ZERO,
                          NOT_IN_EMPTY]
           >> RW_TAC std_ss [GSYM K_PARTIAL, SUMS_ZERO])
       >> RW_TAC std_ss [sum, COUNT_SUC]
       >> (MP_TAC o
           Q.SPECL [`c'`, `n`, `count n`, `s`] o
           INST_TYPE [alpha |-> ``:num``])
          BIJ_INSERT_NOTIN
       >> impl_tac >- RW_TAC arith_ss [IN_COUNT]
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!x. P x` MP_TAC
       >> RW_TAC std_ss [IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM]
       >> Know `?n'. c' n = c n'` >- PROVE_TAC []
       >> DISCH_THEN (MP_TAC o
                      Ho_Rewrite.ONCE_REWRITE_RULE [whileTheory.LEAST_EXISTS])
       >> Q.SPEC_TAC (`LEAST n'. c' n = c n'`, `k`)
       >> Q.PAT_X_ASSUM `X = Y` K_TAC
       >> RW_TAC std_ss []
       >> Know
       `!n'.
          (!m. m < n' ==> ~(c m = c n')) /\ ((c n' = c k) \/ c n' IN u) =
          ((!m. m < n' ==> ~(c m = c n')) /\ (c n' = c k)) \/
          ((!m. m < n' ==> ~(c m = c n')) /\ (c n' IN u))`
       >- (RW_TAC real_ss []
           >> PROVE_TAC [])
       >> Rewr
       >> Know
       `!n'.
          (if
            (!m. m < n' ==> ~(c m = c n')) /\ (c n' = c k) \/
            (!m. m < n' ==> ~(c m = c n')) /\ c n' IN u
           then
             prob bern ($= (c n') o FST o f) * prob bern (p o FST o g (c n'))
           else
             0) =
          (if
            (!m. m < n' ==> ~(c m = c n')) /\ c n' IN u
           then
             prob bern ($= (c n') o FST o f) * prob bern (p o FST o g (c n'))
           else
             0) +
          (if
            (!m. m < n' ==> ~(c m = c n')) /\ (c n' = c k)
           then
             prob bern ($= (c n') o FST o f) * prob bern (p o FST o g (c n'))
           else
             0)`
       >- (Know
           `!n'.
              ~(((!m. m < n' ==> ~(c m = c n')) /\ (c n' = c k)) /\
                ((!m. m < n' ==> ~(c m = c n')) /\ (c n' IN u)))`
           >- PROVE_TAC []
           >> BasicProvers.NORM_TAC real_ss []
           >> PROVE_TAC [])
       >> Rewr
       >> HO_MATCH_MP_TAC SER_ADD
       >> CONJ_TAC
       >- (Q.PAT_X_ASSUM `!s. P s ==> Q s ==> R s` (MP_TAC o Q.SPEC `u`)
           >> RW_TAC std_ss [])
       >> Q.PAT_X_ASSUM `!s. P s ==> Q s ==> R s` K_TAC
       >> Know
          `!n'. ((!m. m < n' ==> ~(c m = c n')) /\ (c n' = c k)) = (n' = k)`
       >- (RW_TAC std_ss []
           >> reverse EQ_TAC >- (RW_TAC std_ss [] >> PROVE_TAC [])
           >> RW_TAC std_ss []
           >> Suff `~(n' < k) /\ ~(k < n')` >- DECIDE_TAC
           >> PROVE_TAC [])
       >> Rewr
       >> RW_TAC arith_ss [SUMS_PICK])
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`enumerate (range (FST o f))`, `j`)
   >> RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`p`, `f`, `g`, `j`] PROB_BERN_BIND_INFINITE)
   >> impl_tac >- RW_TAC std_ss []
   >> Q.SPEC_TAC (`prob bern (p o FST o BIND f g)`, `l`)
   >> REPEAT STRIP_TAC
   >> Know `!x. 0 <= prob bern ($= x o FST o f) * prob bern (p o FST o g x)`
   >- (RW_TAC std_ss []
       >> MATCH_MP_TAC REAL_LE_MUL
       >> PROVE_TAC [PROB_POSITIVE, PROB_SPACE_BERN, INDEP_FN_FST_EVENTS])
   >> Know `!m. ?h. (c h = j m) /\ !n. n < h ==> ~(c n = c h)`
   >- (STRIP_TAC
       >> Suff `?h. c h = j m`
       >- (DISCH_THEN (MP_TAC o
                       Ho_Rewrite.REWRITE_RULE [whileTheory.LEAST_EXISTS])
           >> PROVE_TAC [])
       >> Suff `j m IN range (FST o f)`
       >- PROVE_TAC []
       >> Q.PAT_X_ASSUM `BIJ j X Y` MP_TAC
       >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV])
   >> DISCH_THEN (MP_TAC o CONV_RULE SKOLEM_CONV)
   >> RW_TAC std_ss []
   >> Suff
   `((\n.
        if !m. m < n ==> ~(c m = c n) then
          prob bern ($= (c n) o FST o f) * prob bern (p o FST o g (c n))
        else 0) o h) sums l`
   >- (STRIP_TAC
       >> (MP_TAC o
           Q.SPECL
           [`\n.
               if !m. m < n ==> ~(c m = c n) then
                 prob bern
                 ($= (c n) o FST o (f : (num -> bool) -> 'b # (num -> bool))) *
                 prob bern
                 (p o FST o
                  (g : 'b -> (num -> bool) -> 'a # (num -> bool)) (c n))
               else 0`, `h : num -> num`, `IMAGE (h : num -> num) UNIV`, `l`])
          SER_BIJ_COMPRESS
       >> impl_tac
       >- (POP_ASSUM K_TAC
           >> CONJ_TAC >- RW_TAC std_ss [REAL_LE_REFL]
           >> CONJ_TAC
           >- (MATCH_MP_TAC INJ_IMAGE_BIJ
               >> Q.EXISTS_TAC `IMAGE h UNIV`
               >> Q.PAT_X_ASSUM `BIJ j X Y` MP_TAC
               >> Q.PAT_X_ASSUM `!m. P m /\ Q m` MP_TAC
               >> Q.PAT_X_ASSUM `!x. P x ==> Q x` MP_TAC
               >> KILL_TAC
               >> RW_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE, IN_UNIV]
               >- PROVE_TAC []
               >> PROVE_TAC [])
           >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
           >> Suff `($= (c n) o FST o f) = {}`
           >- RW_TAC real_ss [PROB_BERN_EMPTY]
           >> SET_EQ_TAC
           >> RW_TAC std_ss [NOT_IN_EMPTY]
           >> RW_TAC std_ss [SPECIFICATION, o_THM]
           >> Q.PAT_X_ASSUM `BIJ j X Y` MP_TAC
           >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, range_def, IN_IMAGE,
                             o_THM]
           >> POP_ASSUM
              (MP_TAC o
               Q.SPEC `FST ((f : (num -> bool) -> 'b # (num -> bool)) x)`)
           >> impl_tac >- (Q.EXISTS_TAC `x` >> RW_TAC std_ss [])
           >> STRIP_TAC
           >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
           >> Q.PAT_X_ASSUM `!m. P m /\ Q m` (MP_TAC o GSYM o Q.SPEC `y`)
           >> RW_TAC std_ss []
           >> STRIP_TAC
           >> Know `n < h y \/ (n = h y) \/ h y < n` >- (KILL_TAC >> DECIDE_TAC)
           >> Q.PAT_X_ASSUM `X = Y` MP_TAC
           >> Q.PAT_X_ASSUM `!n. P n` MP_TAC
           >> Q.PAT_X_ASSUM `!n. ~(X n = Y n)` MP_TAC
           >> Q.PAT_X_ASSUM `!n. X n ==> Y n` MP_TAC
           >> KILL_TAC
           >> PROVE_TAC [])
       >> RW_TAC std_ss [])
   >> Suff
      `(\n.
         (if !m. m < n ==> ~(c m = c n) then
            prob bern ($= (c n) o FST o f) * prob bern (p o FST o g (c n))
          else 0)) o h =
       (\m.
          prob bern ($= (j m) o FST o f) *
          prob bern (p o FST o g (j m)))`
   >- RW_TAC std_ss []
   >> FUN_EQ_TAC
   >> Q.PAT_X_ASSUM `X sums Y` K_TAC
   >> RW_TAC std_ss [o_THM]
QED
end (* local *)

val PROB_BERN_BIND_EQ = store_thm
  ("PROB_BERN_BIND_EQ",
   ``!p f1 f2 g1 g2.
       f1 IN indep_fn /\ f2 IN indep_fn /\
       (!m. g1 m IN indep_fn) /\ (!m. g2 m IN indep_fn) /\
       (!m. prob bern ($= m o FST o f1) = prob bern ($= m o FST o f2)) /\
       (!m. prob bern (p o FST o g1 m) = prob bern (p o FST o g2 m)) ==>
       (prob bern (p o FST o BIND f1 g1) = prob bern (p o FST o BIND f2 g2))``,
   RW_TAC std_ss []
   >> Know `countable (range (FST o f1) UNION range (FST o f2))`
   >- (REPEAT (Q.PAT_X_ASSUM `X IN indep_fn` MP_TAC)
       >> RW_TAC std_ss [indep_fn_def, union_countable, GSPECIFICATION])
   >> RW_TAC std_ss [COUNTABLE_ALT, IN_UNION, DISJ_IMP_THM, FORALL_AND_THM]
   >> MP_TAC (Q.SPECL [`p`, `f1`, `g1`, `f`] PROB_BERN_BIND_COUNTABLE)
   >> impl_tac >- RW_TAC std_ss []
   >> RW_TAC std_ss [SUMS_EQ]
   >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
   >> MP_TAC (Q.SPECL [`p`, `f2`, `g2`, `f`] PROB_BERN_BIND_COUNTABLE)
   >> impl_tac >- RW_TAC std_ss []
   >> RW_TAC std_ss [SUMS_EQ]
   >> POP_ASSUM (REWRITE_TAC o wrap o SYM));

val PROB_BERN_BIND_SDEST = store_thm
  ("PROB_BERN_BIND_SDEST",
   ``!f p.
       (!x. f x IN indep_fn) ==>
       (prob bern (p o FST o BIND sdest f) =
        (1 / 2) * prob bern (p o FST o f T) +
        (1 / 2) * prob bern (p o FST o f F))``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`sdest`, `f`, `1 / 2`, `p`] PROB_BERN_BIND_BOOL)
   >> Know `FST o sdest = halfspace T`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_HALFSPACE]
       >> RW_TAC std_ss [SPECIFICATION, sdest_def, o_THM])
   >> RW_TAC std_ss [INDEP_FN_SDEST, PROB_BERN_HALFSPACE, ONE_MINUS_HALF]);

val PROB_BERN_BIND_COMM = store_thm
  ("PROB_BERN_BIND_COMM",
   ``!f g h p.
       f IN indep_fn /\ g IN indep_fn /\ (!x y. h x y IN indep_fn) ==>
       (prob bern (p o FST o BIND f (\x. BIND g (\y. h x y))) =
        prob bern (p o FST o BIND g (\y. BIND f (\x. h x y))))``,
   RW_TAC std_ss' []
   >> Know `!x. BIND g (h x) = BIND (BIND g (\y. UNIT (x, y))) (UNCURRY h)`
   >- (FUN_EQ_TAC
       >> RW_TAC std_ss [BIND_DEF, UNCURRY, o_DEF, UNIT_DEF])
   >> Rewr
   >> Know
      `!y. BIND f (\x. h x y) = BIND (BIND f (\x. UNIT (x, y))) (UNCURRY h)`
   >- (FUN_EQ_TAC
       >> RW_TAC std_ss [BIND_DEF, UNCURRY, o_DEF, UNIT_DEF])
   >> Rewr
   >> RW_TAC std_ss [BIND_ASSOC]
   >> MATCH_MP_TAC PROB_BERN_BIND_EQ
   >> RW_TAC std_ss [INDEP_FN_BIND, INDEP_FN_UNIT, UNCURRY]
   >> POP_ASSUM K_TAC
   >> Cases_on `m`
   >> (MP_TAC o
       Q.SPECL
       [`$= (q, r)`, `f`, `\x. BIND g (\y. UNIT (x,y))`, `{q}`,
        `prob bern ($= (q, r) o FST o (\x. BIND g (\y. UNIT (x,y))) q)`, `0`] o
       INST_TYPE [alpha |-> ``:'a # 'b``, beta |-> alpha])
      PROB_BERN_BIND
   >> impl_tac
   >- (RW_TAC std_ss [INDEP_FN_BIND, INDEP_FN_UNIT, IN_SING]
       >> Suff `($= (q,r) o FST o BIND g (\y. UNIT (a,y))) = {}`
       >- RW_TAC std_ss [PROB_BERN_EMPTY]
       >> SET_EQ_TAC
       >> RW_TAC std_ss [NOT_IN_EMPTY]
       >> RW_TAC std_ss [SPECIFICATION, o_THM, UNIT_DEF, BIND_DEF, UNCURRY])
   >> Rewr
   >> (MP_TAC o
       Q.SPECL
       [`$= (q, r)`, `g`, `\y. BIND f (\x. UNIT (x,y))`, `{r}`,
        `prob bern ($= (q, r) o FST o (\y. BIND f (\x. UNIT (x,y))) r)`, `0`] o
       INST_TYPE [alpha |-> ``:'a # 'b``, beta |-> beta])
      PROB_BERN_BIND
   >> impl_tac
   >- (RW_TAC std_ss [INDEP_FN_BIND, INDEP_FN_UNIT, IN_SING]
       >> Suff `($= (q,r) o FST o BIND f (\x. UNIT (x,a))) = {}`
       >- RW_TAC std_ss [PROB_BERN_EMPTY]
       >> SET_EQ_TAC
       >> RW_TAC std_ss [NOT_IN_EMPTY]
       >> RW_TAC std_ss [SPECIFICATION, o_THM, UNIT_DEF, BIND_DEF, UNCURRY])
   >> Rewr
   >> RW_TAC real_ss []
   >> Know `($= (q,r) o FST o BIND g (\y. UNIT (q,y))) = {r} o FST o g`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_o, IN_SING]
       >> RW_TAC std_ss [SPECIFICATION, UNIT_DEF, BIND_DEF, UNCURRY, o_THM]
       >> PROVE_TAC [])
   >> Rewr
   >> Know `($= (q,r) o FST o BIND f (\x. UNIT (x,r))) = {q} o FST o f`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_o, IN_SING]
       >> RW_TAC std_ss [SPECIFICATION, UNIT_DEF, BIND_DEF, UNCURRY, o_THM]
       >> PROVE_TAC [])
   >> Rewr
   >> PROVE_TAC [REAL_MUL_SYM]);

val INDEP_FN_PROB_UNTIL = store_thm
  ("INDEP_FN_PROB_UNTIL",
   ``!b c.
       b IN indep_fn /\ (?*s. c (FST (b s))) ==> prob_until b c IN indep_fn``,
   RW_TAC std_ss [prob_until_def]
   >> MATCH_MP_TAC INDEP_FN_BIND
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC INDEP_FN_PROB_WHILE
   >> RW_TAC std_ss [K_THM]
   >> MATCH_MP_TAC PROB_WHILE_TERMINATES_SUFFICIENT
   >> RW_TAC std_ss [K_THM, o_THM]);

val PROB_UNTIL_ADVANCE = store_thm
  ("PROB_UNTIL_ADVANCE",
   ``!b c.
       b IN indep_fn /\ (?*s. c (FST (b s))) ==>
       (prob_until b c = BIND b (\x. if c x then UNIT x else prob_until b c))``,
   RW_TAC std_ss [prob_until_def]
   >> MP_TAC (Q.SPECL [`$~ o c`, `K b`] PROB_WHILE_ADVANCE)
   >> CONV_TAC (DEPTH_CONV FORALL_IMP_CONV)
   >> impl_tac
   >- (RW_TAC std_ss [K_THM]
       >> MATCH_MP_TAC PROB_WHILE_TERMINATES_SUFFICIENT
       >> RW_TAC std_ss [K_THM, o_THM])
   >> RW_TAC std_ss [K_THM]
   >> FUN_EQ_TAC
   >> ONCE_REWRITE_TAC [BIND_DEF]
   >> POP_ASSUM
      (fn th =>
       RW_TAC std_ss [UNCURRY, o_THM]
       >> ONCE_REWRITE_TAC [th])
   >> RW_TAC std_ss [o_THM]);

val PROB_BERN_UNTIL = store_thm
  ("PROB_BERN_UNTIL",
   ``!p b c.
       b IN indep_fn /\ (?*s. c (FST (b s))) ==>
       (prob bern (p o FST o prob_until b c) =
        prob bern ((p INTER {x | c x}) o FST o b) /
        prob bern ({x | c x} o FST o b))``,
   RW_TAC std_ss []
   >> Know
      `prob bern ({x | c x} o FST o b) =
       prob bern (COMPL (COMPL {x | c x} o FST o b))`
   >- RW_TAC std_ss [GSYM COMPL_o, GCOMPL, COMPL_COMPL]
   >> Rewr
   >> RW_TAC std_ss [PROB_COMPL_BERN, INDEP_FN_FST_EVENTS]
   >> MATCH_MP_TAC GP_REC
   >> CONJ_TAC
   >- (RW_TAC std_ss [COMPL_o, PROB_COMPL_BERN, INDEP_FN_FST_EVENTS]
       >> MATCH_MP_TAC ABS_1_MINUS_PROB
       >> POP_ASSUM MP_TAC
       >> Suff `{x | c x} o FST o b = {s | c (FST (b s))}`
       >- RW_TAC std_ss [PROB_SPACE_BERN, possibly_def, possibly_bern_def]
       >> SET_EQ_TAC
       >> PSET_TAC [o_THM])
   >> Know
      `(p o FST o prob_until b c) =
       ((p o FST o prob_until b c) INTER ({x | c x} o FST o b)) UNION
       ((p o FST o prob_until b c) INTER (COMPL {x | c x} o FST o b))`
   >- (SET_EQ_TAC
       >> PSET_TAC []
       >> PROVE_TAC [])
   >> DISCH_THEN (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV o wrap)
   >> Know
      `prob bern
       (((p o FST o prob_until b c) INTER ({x | c x} o FST o b)) UNION
        ((p o FST o prob_until b c) INTER (COMPL {x | c x} o FST o b))) =
       prob bern ((p o FST o prob_until b c) INTER ({x | c x} o FST o b)) +
       prob bern ((p o FST o prob_until b c) INTER (COMPL {x | c x} o FST o b))`
   >- (MATCH_MP_TAC PROB_ADDITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN, IN_DISJOINT, IN_INTER,
                         GSPECIFICATION, IN_o, IN_COMPL, o_THM,
                         EVENTS_INTER, INDEP_FN_FST_EVENTS, INDEP_FN_PROB_UNTIL]
       >> PROVE_TAC [])
   >> Rewr
   >> Know `!a b c d : real. (a = b) /\ (c = d) ==> (a + c = b + d)`
   >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> CONJ_TAC
   >- (AP_TERM_TAC
       >> SET_EQ_TAC
       >> MP_TAC (Q.SPECL [`b`, `c`] PROB_UNTIL_ADVANCE)
       >> impl_tac >- RW_TAC std_ss []
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       >> RW_TAC std_ss [IN_INTER, IN_o, o_THM, BIND_DEF, UNCURRY, UNIT_DEF,
                         GSPECIFICATION])
   >> Suff
      `prob bern (p o FST o prob_until b c INTER COMPL {x | c x} o FST o b) =
       prob bern
       (COMPL {x | c x} o FST o b INTER (p o FST o prob_until b c) o SND o b)`
   >- (Rewr
       >> MATCH_MP_TAC INDEP_FN_PROB
       >> RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_UNTIL])
   >> AP_TERM_TAC
   >> SET_EQ_TAC
   >> MP_TAC (Q.SPECL [`b`, `c`] PROB_UNTIL_ADVANCE)
   >> impl_tac >- RW_TAC std_ss []
   >> STRIP_TAC
   >> GEN_TAC
   >> POP_ASSUM (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV o wrap)
   >> RW_TAC std_ss [IN_INTER, IN_o, o_THM, BIND_DEF, UNCURRY, UNIT_DEF,
                     GSPECIFICATION, IN_COMPL]);

val EVENTS_BERN_IMAGE_SCONS = store_thm
  ("EVENTS_BERN_IMAGE_SCONS",
   ``!b s. IMAGE (scons b) s IN events bern = s IN events bern``,
   RW_TAC std_ss []
   >> EQ_TAC >|
   [RW_TAC std_ss []
    >> Suff `s o stl IN events bern` >- RW_TAC std_ss [EVENTS_BERN_STL]
    >> Suff `s o stl = IMAGE (scons b) s UNION (IMAGE (scons b) s o mirror)`
    >- (RW_TAC std_ss []
        >> MATCH_MP_TAC EVENTS_UNION
        >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_MIRROR])
    >> SET_EQ_TAC
    >> PSET_TAC []
    >> SEQ_CASES_TAC `x`
    >> RW_TAC std_ss [STL_SCONS, MIRROR_SCONS, SCONS_EQ]
    >> PROVE_TAC [],
    RW_TAC std_ss []
    >> Suff `IMAGE (scons b) s = s o stl INTER halfspace b`
    >- (RW_TAC std_ss []
        >> MATCH_MP_TAC EVENTS_INTER
        >> RW_TAC std_ss [PROB_SPACE_BERN, EVENTS_BERN_STL,
                          EVENTS_BERN_HALFSPACE])
    >> SET_EQ_TAC
    >> PSET_TAC []
    >> SEQ_CASES_TAC `x`
    >> RW_TAC std_ss [STL_SCONS, SCONS_EQ, IN_HALFSPACE, SHD_SCONS]
    >> PROVE_TAC []]);

val NONEVENT_ALT = store_thm
  ("NONEVENT_ALT",
   ``!x. ?!y. eventually x y /\ y IN nonevent``,
   CONV_TAC (DEPTH_CONV EXISTS_UNIQUE_CONV)
   >> reverse (RW_TAC std_ss [])
   >- PROVE_TAC [EVENTUALLY_IN_NONEVENT, EVENTUALLY_TRANS, EVENTUALLY_SYM]
   >> RW_TAC std_ss [nonevent_def, IN_IMAGE, IN_UNIV]
   >> Q.EXISTS_TAC `@y. eventually x y`
   >> Know `?y. eventually x y` >- PROVE_TAC [EVENTUALLY_REFL]
   >> DISCH_THEN (MP_TAC o REWRITE_RULE [EXISTS_DEF])
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `x`
   >> RW_TAC std_ss []);

val PROB_BERN_SINGLE = store_thm
  ("PROB_BERN_SINGLE",
   ``!n. prob bern {s | shd (sdrop n s)} = 1 / 2``,
   RW_TAC std_ss []
   >> Know `{s | shd (sdrop n s)} = halfspace T o sdrop n`
   >- (SET_EQ_TAC
       >> PSET_TAC [IN_HALFSPACE])
   >> Rewr
   >> RW_TAC std_ss [PROB_BERN_HALFSPACE, PROB_BERN_SDROP,
                     EVENTS_BERN_HALFSPACE]);

val PROB_BERN_PAIR = store_thm
  ("PROB_BERN_PAIR",
   ``!m n.
       prob bern {s | shd (sdrop m s) = shd (sdrop n s)} =
       if m = n then 1 else 1 / 2``,
   HO_MATCH_MP_TAC TRANSFORM_2D_NUM
   >> CONJ_TAC
   >- (REPEAT STRIP_TAC
       >> CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
       >> RW_TAC std_ss [])
   >> STRIP_TAC
   >> Cases >- RW_TAC arith_ss [GUNIV, PROB_BERN_UNIV]
   >> RW_TAC arith_ss []
   >> Know
      `{(s : num -> bool) | shd (sdrop m s) = shd (sdrop (m + SUC n') s)} =
       {s | shd s = shd (sdrop (SUC n') s)} o sdrop m`
   >- (SET_EQ_TAC
       >> PSET_TAC [GSYM SDROP_ADD]
       >> PROVE_TAC [ADD_COMM])
   >> Rewr
   >> Suff
      `{s | shd s = shd (sdrop (SUC n') s)} IN events bern /\
       (prob bern {s | shd s = shd (sdrop (SUC n') s)} = 1 / 2)`
   >- RW_TAC std_ss [PROB_BERN_SDROP]
   >> Know
      `{s | shd s = shd (sdrop (SUC n') s)} =
       (halfspace T INTER (halfspace T o sdrop n') o stl) UNION
       (halfspace F INTER (halfspace F o sdrop n') o stl)`
   >- (SET_EQ_TAC
       >> PSET_TAC [IN_HALFSPACE]
       >> Cases_on `shd x`
       >> RW_TAC std_ss [sdrop_def, o_THM])
   >> Rewr
   >> Know
      `halfspace T INTER (halfspace T o sdrop n') o stl IN events bern /\
       halfspace F INTER (halfspace F o sdrop n') o stl IN events bern`
   >- RW_TAC std_ss [EVENTS_INTER, PROB_SPACE_BERN, EVENTS_BERN_STL,
                     EVENTS_BERN_SDROP, EVENTS_BERN_HALFSPACE]
   >> RW_TAC std_ss [EVENTS_UNION, PROB_SPACE_BERN]
   >> Suff
      `1 / 2 =
       prob bern (halfspace T INTER (halfspace T o sdrop n') o stl) +
       prob bern (halfspace F INTER (halfspace F o sdrop n') o stl)`
   >- (Rewr
       >> MATCH_MP_TAC PROB_ADDITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN, DISJOINT_ALT, IN_HALFSPACE, IN_INTER])
   >> RW_TAC std_ss [PROB_BERN_STL_HALFSPACE, EVENTS_BERN_SDROP,
                     EVENTS_BERN_HALFSPACE, PROB_BERN_SDROP,
                     PROB_BERN_HALFSPACE, REAL_DOUBLE, REAL_MUL_ASSOC,
                     HALF_CANCEL, REAL_MUL_LID]);

val INDEP_FN_COIN_FLIP = store_thm
  ("INDEP_FN_COIN_FLIP",
   ``!a b. a IN indep_fn /\ b IN indep_fn ==> coin_flip a b IN indep_fn``,
   RW_TAC std_ss [coin_flip_def]
   >> MATCH_MP_TAC INDEP_FN_BIND
   >> RW_TAC std_ss [INDEP_FN_SDEST]);

val PROB_BERN_COIN_FLIP = store_thm
  ("PROB_BERN_COIN_FLIP",
   ``!f g p.
       f IN indep_fn /\ g IN indep_fn ==>
       (prob bern (p o FST o coin_flip f g) =
        (1 / 2) * prob bern (p o FST o f) +
        (1 / 2) * prob bern (p o FST o g))``,
   RW_TAC std_ss [coin_flip_def]
   >> MP_TAC (Q.SPECL [`\x. if x then f else g`, `p`] PROB_BERN_BIND_SDEST)
   >> impl_tac >- (Cases >> RW_TAC std_ss [])
   >> RW_TAC std_ss []);

val INDEP_FN_MMAP = store_thm
  ("INDEP_FN_MMAP",
   ``!f a. a IN indep_fn ==> MMAP f a IN indep_fn``,
   RW_TAC std_ss [MMAP_DEF, INDEP_FN_BIND, o_THM, INDEP_FN_UNIT]);

val INDEP_FN_PROB_REPEAT = store_thm
  ("INDEP_FN_PROB_REPEAT",
   ``!a.
       a IN indep_fn /\ (?*s. IS_SOME (FST (a s))) ==>
       prob_repeat a IN indep_fn``,
   RW_TAC std_ss [prob_repeat_def]
   >> MATCH_MP_TAC INDEP_FN_MMAP
   >> MATCH_MP_TAC INDEP_FN_PROB_UNTIL
   >> RW_TAC std_ss []);

val PROB_WHILE_POST = store_thm
  ("PROB_WHILE_POST",
   ``!c b a.
       (!a. b a IN indep_fn) /\ prob_while_terminates c b ==>
       !*s. ~c (FST (prob_while c b a s))``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `$~ o c` PROB_WHILE)
   >> RW_TAC std_ss [o_THM]
   >> POP_ASSUM MATCH_MP_TAC
   >> RW_TAC std_ss [PROBABLY_TRUE]);

val PROB_UNTIL_POST = store_thm
  ("PROB_UNTIL_POST",
   ``!b c.
       b IN indep_fn /\ (?*s. c (FST (b s))) ==>
       !*s. c (FST (prob_until b c s))``,
   RW_TAC std_ss []
   >> SIMP_TAC std_ss [probably_def, probably_bern_def]
   >> Know
      `{s | c (FST (prob_until b c s))} = ({x | c x} o FST o prob_until b c)`
   >- (SET_EQ_TAC
       >> PSET_TAC [o_THM])
   >> Rewr
   >> CONJ_TAC
   >- (MATCH_MP_TAC INDEP_FN_FST_EVENTS
       >> MATCH_MP_TAC INDEP_FN_PROB_UNTIL
       >> RW_TAC std_ss [])
   >> RW_TAC std_ss [prob_until_def]
   >> Know
      `1 =
       prob bern ({x | c x} o FST o b) * 1 +
       (1 - prob bern ({x | c x} o FST o b)) * 1`
   >- (RW_TAC real_ss []
       >> REAL_ARITH_TAC)
   >> Rewr'
   >> MATCH_MP_TAC PROB_BERN_BIND
   >> ASM_SIMP_TAC std_ss []
   >> Know `prob_while_terminates ($~ o c) (K b)`
   >- (MATCH_MP_TAC PROB_WHILE_TERMINATES_SUFFICIENT
       >> RW_TAC std_ss [K_THM, o_THM])
   >> STRIP_TAC
   >> CONJ_TAC
   >- (STRIP_TAC
       >> MATCH_MP_TAC INDEP_FN_PROB_WHILE
       >> RW_TAC std_ss [K_THM])
   >> SIMP_TAC std_ss [GSPECIFICATION]
   >> CONJ_TAC
   >- (RW_TAC std_ss [PROB_WHILE_ADVANCE, K_THM, o_DEF, UNIT_DEF]
       >> Suff `(\x : num -> bool. a IN {x | c x}) = UNIV`
       >- RW_TAC std_ss [SPECIFICATION, PROB_BERN_UNIV]
       >> RW_TAC std_ss [GSPECIFICATION, GSYM UNIV_DEF])
   >> RW_TAC std_ss []
   >> Suff `!*s. s IN ({x | c x} o FST o prob_while ($~ o c) (K b) a)`
   >- RW_TAC std_ss [probably_def, probably_bern_def, GDEST]
   >> RW_TAC std_ss [SPECIFICATION, o_THM]
   >> HO_MATCH_MP_TAC PROB_WHILE
   >> RW_TAC std_ss [K_THM, o_THM]
   >> Suff `{x | c x} = c` >- RW_TAC std_ss [PROBABLY_TRUE]
   >> SET_EQ_TAC
   >> PSET_TAC []
   >> RW_TAC std_ss [SPECIFICATION]);

val POSSIBLY_SOME_COIN_FLIP1 = store_thm
  ("POSSIBLY_SOME_COIN_FLIP1",
   ``!f g.
       f IN indep_fn /\ g IN indep_fn /\
       (?*s. IS_SOME (FST (f s))) ==>
       (?*s. IS_SOME (FST (coin_flip f g s)))``,
   RW_TAC std_ss []
   >> SIMP_TAC std_ss [possibly_def, possibly_bern_def]
   >> Know
      `{s | IS_SOME (FST (coin_flip f g s))} =
       IS_SOME o FST o coin_flip f g`
   >- (SET_EQ_TAC
       >> PSET_TAC [o_THM]
       >> RW_TAC std_ss [SPECIFICATION])
   >> Rewr
   >> RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_COIN_FLIP]
   >> RW_TAC std_ss [PROB_BERN_COIN_FLIP]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [possibly_bern_def, possibly_def]
   >> Know `!a b : real. ~(2 * a = 2 * b) ==> ~(a = b)` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL]
   >> RW_TAC real_ss []
   >> Know `!a : real. 0 < a ==> ~(a = 0)` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> MATCH_MP_TAC REAL_LTE_ADD
   >> RW_TAC std_ss [PROB_POSITIVE, INDEP_FN_FST_EVENTS, PROB_SPACE_BERN]
   >> Know `!a : real. 0 <= a /\ ~(a = 0) ==> 0 < a`  >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC std_ss [PROB_POSITIVE, INDEP_FN_FST_EVENTS, PROB_SPACE_BERN]
   >> Suff `IS_SOME o FST o f = {s | IS_SOME (FST (f s))}`
   >- RW_TAC std_ss []
   >> SET_EQ_TAC
   >> PSET_TAC [o_THM]
   >> RW_TAC std_ss [SPECIFICATION]);

val POSSIBLY_SOME_COIN_FLIP2 = store_thm
  ("POSSIBLY_SOME_COIN_FLIP2",
   ``!f g.
       f IN indep_fn /\ g IN indep_fn /\
       (?*s. IS_SOME (FST (g s))) ==>
       (?*s. IS_SOME (FST (coin_flip f g s)))``,
   RW_TAC std_ss []
   >> SIMP_TAC std_ss [possibly_def, possibly_bern_def]
   >> Know
      `{s | IS_SOME (FST (coin_flip f g s))} =
       IS_SOME o FST o coin_flip f g`
   >- (SET_EQ_TAC
       >> PSET_TAC [o_THM]
       >> RW_TAC std_ss [SPECIFICATION])
   >> Rewr
   >> RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_COIN_FLIP]
   >> RW_TAC std_ss [PROB_BERN_COIN_FLIP]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [possibly_bern_def, possibly_def]
   >> Know `!a b : real. ~(2 * a = 2 * b) ==> ~(a = b)` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL]
   >> RW_TAC real_ss []
   >> Know `!a : real. 0 < a ==> ~(a = 0)` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> MATCH_MP_TAC REAL_LET_ADD
   >> RW_TAC std_ss [PROB_POSITIVE, INDEP_FN_FST_EVENTS, PROB_SPACE_BERN]
   >> Know `!a : real. 0 <= a /\ ~(a = 0) ==> 0 < a`  >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC std_ss [PROB_POSITIVE, INDEP_FN_FST_EVENTS, PROB_SPACE_BERN]
   >> Suff `IS_SOME o FST o g = {s | IS_SOME (FST (g s))}`
   >- RW_TAC std_ss []
   >> SET_EQ_TAC
   >> PSET_TAC [o_THM]
   >> RW_TAC std_ss [SPECIFICATION]);

val POSSIBLY_IS_SOME_MMAP = store_thm
  ("POSSIBLY_IS_SOME_MMAP",
   ``!f. ?*s. IS_SOME (FST ((MMAP SOME f) s))``,
   RW_TAC std_ss [possibly_def, possibly_bern_def, MMAP_DEF, o_THM, UNCURRY,
                  BIND_DEF, UNIT_DEF, GUNIV, EVENTS_BERN_UNIV, PROB_BERN_UNIV]
   >> REAL_ARITH_TAC);

val PROB_BERN_REPEAT = store_thm
  ("PROB_BERN_REPEAT",
   ``!p f.
       f IN indep_fn /\ (?*s. IS_SOME (FST (f s))) ==>
       (prob bern (p o FST o prob_repeat f) =
        prob bern (((p o THE) INTER {x | IS_SOME x}) o FST o f) /
        prob bern ({x | IS_SOME x} o FST o f))``,
   RW_TAC bool_ss [prob_repeat_def, FST_o_MMAP]
   >> RW_TAC bool_ss [o_ASSOC]
   >> ONCE_REWRITE_TAC [GSYM o_ASSOC]
   >> RW_TAC bool_ss [PROB_BERN_UNTIL]);

val EVENT_TRANSITION = store_thm
  ("EVENT_TRANSITION",
   ``!p (f : (num -> bool) -> 'a # (num -> bool)).
       {s | p (FST (f s))} = {x | p x} o FST o f``,
   SET_EQ_TAC
   >> PSET_TAC [o_THM]);

val COIN_FLIP_CARNAGE = store_thm
  ("COIN_FLIP_CARNAGE",
   ``!x y z : real. ((1 / 2) * x + (1 / 2) * y = z) = (x + y = 2 * z)``,
   RW_TAC std_ss []
   >> Know `!a b : real. (a = b) = (2 * a = 2 * b)` >- REAL_ARITH_TAC
   >> DISCH_THEN (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV o wrap)
   >> RW_TAC std_ss [REAL_ADD_LDISTRIB, HALF_CANCEL, REAL_MUL_ASSOC]
   >> RW_TAC real_ss []);

val UNIVERSAL_PROBABLY = store_thm
  ("UNIVERSAL_PROBABLY",
   ``!p. (!s. p s) ==> (!*s. p s)``,
   RW_TAC std_ss [probably_def, probably_bern_def, PROBABLY_TRUE, GUNIV,
                  PROB_BERN_UNIV, EVENTS_BERN_UNIV]);

val INDEP_FN_PROB_COST = store_thm
  ("INDEP_FN_PROB_COST",
   ``!f b. (!a. b a IN indep_fn) ==> (!a. prob_cost f b a IN indep_fn)``,
   RW_TAC std_ss []
   >> Cases_on `a`
   >> RW_TAC std_ss [prob_cost_def, INDEP_FN_BIND, INDEP_FN_UNIT]);

val PROB_TERMINATES_COST = store_thm
  ("PROB_TERMINATES_COST",
   ``!b c.
       prob_while_terminates (c o FST) (prob_cost SUC b) =
       prob_while_terminates c b``,
   RW_TAC std_ss [PROB_WHILE_TERMINATES]
   >> reverse EQ_TAC >|
   [RW_TAC std_ss []
    >> Cases_on `a`
    >> POP_ASSUM (MP_TAC o Q.SPEC `q`)
    >> Know `!p q. (p = q) ==> (!*s. p s) ==> (!*s. q s)`
    >- SIMP_TAC std_ss []
    >> DISCH_THEN HO_MATCH_MP_TAC
    >> FUN_EQ_TAC
    >> RW_TAC std_ss []
    >> Know `!p q. (p = q) ==> ((?s : num. p s) = (?s. q s))`
    >- SIMP_TAC std_ss []
    >> DISCH_THEN HO_MATCH_MP_TAC
    >> FUN_EQ_TAC
    >> RW_TAC std_ss []
    >> Q.SPEC_TAC (`q`, `q`)
    >> Q.SPEC_TAC (`r`, `r`)
    >> Q.SPEC_TAC (`x`, `x`)
    >> Induct_on `x'`
    >- RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, o_THM]
    >> RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, o_THM, BIND_DEF,
                      prob_cost_def, UNCURRY]
    >> Q.PAT_X_ASSUM `!x. P x`
       (MP_TAC o
        Q.SPECL [`SND ((b:'a->(num->bool)->'a#(num->bool)) q x)`,
                 `SUC r`,
                 `FST ((b:'a->(num->bool)->'a#(num->bool)) q x)`])
    >> RW_TAC std_ss [o_THM],
    RW_TAC std_ss []
    >> POP_ASSUM (MP_TAC o Q.SPEC `(a, r)`)
    >> Know `!p q. (p = q) ==> (!*s. p s) ==> (!*s. q s)`
    >- SIMP_TAC std_ss []
    >> DISCH_THEN HO_MATCH_MP_TAC
    >> FUN_EQ_TAC
    >> RW_TAC std_ss []
    >> Know `!p q. (p = q) ==> ((?s : num. p s) = (?s. q s))`
    >- SIMP_TAC std_ss []
    >> DISCH_THEN HO_MATCH_MP_TAC
    >> FUN_EQ_TAC
    >> RW_TAC std_ss []
    >> Q.SPEC_TAC (`a`, `a`)
    >> Q.SPEC_TAC (`r`, `r`)
    >> Q.SPEC_TAC (`x`, `x`)
    >> Induct_on `x'`
    >- RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, o_THM]
    >> RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, o_THM, BIND_DEF,
                      prob_cost_def, UNCURRY]
    >> Q.PAT_X_ASSUM `!x. P x`
       (MP_TAC o
        Q.SPECL [`SND ((b:'a->(num->bool)->'a#(num->bool)) a x)`,
                 `SUC r`,
                 `FST ((b:'a->(num->bool)->'a#(num->bool)) a x)`])
    >> RW_TAC std_ss [o_THM]]);

val INDEP_FN_PROB_WHILE_COST = store_thm
  ("INDEP_FN_PROB_WHILE_COST",
   ``!b c.
       (!a. b a IN indep_fn) /\ prob_while_terminates c b ==>
       !a. prob_while_cost c b a IN indep_fn``,
   RW_TAC std_ss [prob_while_cost_def]
   >> MATCH_MP_TAC INDEP_FN_PROB_WHILE
   >> RW_TAC std_ss [PROB_TERMINATES_COST]
   >> MATCH_MP_TAC INDEP_FN_PROB_COST
   >> PROVE_TAC []);

val PROB_WHILE_CUT_MONO = store_thm
  ("PROB_WHILE_CUT_MONO",
   ``!m n c b a s.
       ~c (FST (prob_while_cut c b m a s)) /\ m <= n ==>
       ~c (FST (prob_while_cut c b n a s))``,
   Suff
   `!m n.
      m <= n ==>
      !c b a s.
        ~c (FST (prob_while_cut c b m a s)) ==>
        ~c (FST (prob_while_cut c b n a s))`
   >- PROVE_TAC []
   >> HO_MATCH_MP_TAC TRIANGLE_2D_NUM
   >> Induct >- RW_TAC arith_ss []
   >> RW_TAC arith_ss [BIND_DEF, ADD_CLAUSES, PROB_WHILE_CUT_REV, UNIT_DEF,
                       UNCURRY, o_THM]);

val PROB_WHILE_CUT_0 = store_thm
  ("PROB_WHILE_CUT_0",
   ``!c b. prob_while_cut c b 0 = UNIT``,
   FUN_EQ_TAC
   >> RW_TAC std_ss [prob_while_cut_def]);

val PROB_WHILE_CUT_ID = store_thm
  ("PROB_WHILE_CUT_ID",
   ``!c b n a. ~c a ==> (prob_while_cut c b n a = UNIT a)``,
   RW_TAC std_ss []
   >> Cases_on `n`
   >> RW_TAC std_ss [prob_while_cut_def]);

val PROB_WHILE_CUT_ADD = store_thm
  ("PROB_WHILE_CUT_ADD",
   ``!c b m n a.
       prob_while_cut c b (m + n) a =
       BIND (prob_while_cut c b m a) (prob_while_cut c b n)``,
   REPEAT GEN_TAC
   >> Q.SPEC_TAC (`a`, `a`)
   >> Induct_on `m`
   >- RW_TAC arith_ss [prob_while_cut_def, BIND_LEFT_UNIT]
   >> RW_TAC arith_ss [prob_while_cut_def, BIND_DEF, UNIT_DEF, UNCURRY, o_DEF,
                       ADD_CLAUSES, PROB_WHILE_CUT_ID]);

val PROB_TERMINATES_HART_LEMMA = store_thm
  ("PROB_TERMINATES_HART_LEMMA",
   ``!c b.
       (!a. b a IN indep_fn) /\
       (?e.
          0 < e /\
          !a. ?N.
            e <= prob bern {s | ~c (FST (prob_while_cut c b N a s))}) ==>
       prob_while_terminates c b``,
   RW_TAC std_ss [SKOLEM_THM]
   >> Suff
      `!c b.
         (!a. b a IN indep_fn) /\
         (?N e.
            0 < e /\
            !a.
              e <= prob bern {s | ~c (FST (prob_while_cut c b (N a) a s))}) ==>
         prob_while_terminates c b`
   >- (DISCH_THEN MATCH_MP_TAC
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `f`
       >> Q.EXISTS_TAC `e`
       >> RW_TAC std_ss [])
   >> KILL_TAC
   >> RW_TAC std_ss [PROB_WHILE_TERMINATES, probably_def, probably_bern_def]
   >- (RW_TAC std_ss [GBIGUNION_IMAGE]
       >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       >> RW_TAC std_ss [PROB_SPACE_BERN, SUBSET_DEF, IN_IMAGE, COUNTABLE_NUM,
                         IN_UNIV, image_countable]
       >> Suff `{s | ~c (FST (prob_while_cut c b n a s))} =
                {x | ~c x} o FST o prob_while_cut c b n a`
       >- RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_WHILE_CUT]
       >> SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
   >> Know
      `!a s.
         (?n. ~c (FST (prob_while_cut c b n a s))) =
         (?n.
            ~c (FST (prob_while_cut c (\a. prob_while_cut c b (N a) a) n a s)))`
   >- (REPEAT (STRIP_TAC ORELSE EQ_TAC) >|
       [Q.EXISTS_TAC `n`
        >> POP_ASSUM MP_TAC
        >> Q.SPEC_TAC (`a`, `a`)
        >> Q.SPEC_TAC (`s`, `s`)
        >> Induct_on `n`
        >- RW_TAC std_ss [prob_while_cut_def]
        >> REPEAT GEN_TAC
        >> reverse (Cases_on `c a`)
        >- RW_TAC std_ss [prob_while_cut_def, BIND_DEF, UNCURRY, o_THM]
        >> STRIP_TAC
        >> RW_TAC std_ss [prob_while_cut_def, BIND_DEF, UNCURRY, o_THM]
        >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
        >> Cases_on `N a`
        >- (Q.PAT_X_ASSUM `!a. P a` (MP_TAC o Q.SPEC `a`)
            >> RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, GEMPTY,
                              PROB_BERN_EMPTY, real_lte])
        >> MP_TAC
           (Q.SPECL [`SUC n`, `SUC n' + n`, `c`, `b`, `a`, `s`]
            (INST_TYPE [beta |-> ``:num->bool``] PROB_WHILE_CUT_MONO))
        >> impl_tac >- RW_TAC arith_ss []
        >> RW_TAC std_ss [PROB_WHILE_CUT_ADD, BIND_DEF, UNCURRY, o_THM],
        POP_ASSUM MP_TAC
        >> Q.SPEC_TAC (`a`, `a`)
        >> Q.SPEC_TAC (`s`, `s`)
        >> Induct_on `n`
        >- (RW_TAC std_ss []
            >> Q.EXISTS_TAC `0`
            >> FULL_SIMP_TAC std_ss [prob_while_cut_def])
        >> reverse (RW_TAC std_ss [prob_while_cut_def, UNIT_DEF])
        >- (Q.EXISTS_TAC `0`
            >> RW_TAC std_ss [prob_while_cut_def, UNIT_DEF])
        >> Suff `?n. ~c (FST (prob_while_cut c b (N a + n) a s))`
        >- PROVE_TAC []
        >> RW_TAC std_ss [PROB_WHILE_CUT_ADD, BIND_DEF, UNCURRY, o_THM]
        >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
        >> FULL_SIMP_TAC std_ss [BIND_DEF, UNCURRY, o_THM]])
   >> Rewr
   >> POP_ASSUM MP_TAC
   >> Know
      `!a.
         {s | ~c (FST (prob_while_cut c b (N a) a s))} =
         {x | ~c x} o FST o prob_while_cut c b (N a) a`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
   >> Rewr
   >> STRIP_TAC
   >> Know `e <= 1`
   >- (MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC
          `prob bern ({x | ~c x} o FST o prob_while_cut c b (N a) a)`
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC PROB_LE_1
       >> RW_TAC std_ss [PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                         INDEP_FN_PROB_WHILE_CUT])
   >> RW_TAC std_ss [GBIGUNION_IMAGE]
   >> MATCH_MP_TAC SEQ_UNIQ
   >> Q.EXISTS_TAC
      `prob bern o
       (\n.
        {s |
         ~c (FST (prob_while_cut c (\a. prob_while_cut c b (N a) a) n a s))})`
   >> CONJ_TAC
   >- (MATCH_MP_TAC PROB_INCREASING_UNION
       >> RW_TAC bool_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV, SUBSET_DEF,
                          GSPECIFICATION] >|
       [Know
        `{s |
          ~c (FST (prob_while_cut c (\a. prob_while_cut c b (N a) a) n a s))} =
         {x | ~c x} o FST o
         (prob_while_cut c (\a. prob_while_cut c b (N a) a) n a)`
        >- (SET_EQ_TAC
            >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
        >> Rewr
        >> MATCH_MP_TAC INDEP_FN_FST_EVENTS
        >> RW_TAC std_ss [INDEP_FN_PROB_WHILE_CUT],
        MATCH_MP_TAC PROB_WHILE_CUT_MONO
        >> Q.EXISTS_TAC `n`
        >> RW_TAC arith_ss []])
   >> RW_TAC std_ss [o_DEF]
   >> Know `!x : real. x = 1 - (1 - x)` >- REAL_ARITH_TAC
   >> Rewr'
   >> HO_MATCH_MP_TAC SEQ_SUB
   >> RW_TAC std_ss [SEQ_CONST, REAL_SUB_REFL]
   >> MATCH_MP_TAC SEQ_SANDWICH
   >> Q.EXISTS_TAC `\n. 0`
   >> Q.EXISTS_TAC `\n. (1 - e) pow n`
   >> REWRITE_TAC [SEQ_CONST]
   >> CONJ_TAC
   >- (MATCH_MP_TAC SEQ_POWER
       >> RW_TAC std_ss [abs]
       >- (Q.PAT_X_ASSUM `x < y` MP_TAC
           >> POP_ASSUM MP_TAC
           >> REAL_ARITH_TAC)
       >> Q.PAT_X_ASSUM `x < y` MP_TAC
       >> POP_ASSUM MP_TAC
       >> POP_ASSUM MP_TAC
       >> REAL_ARITH_TAC)
   >> GEN_TAC
   >> CONJ_TAC
   >- (RW_TAC std_ss []
       >> Know `!x : real. x <= 1 ==> 0 <= 1 - x` >- REAL_ARITH_TAC
       >> DISCH_THEN MATCH_MP_TAC
       >> Know
          `{s |
            ~c (FST
                (prob_while_cut c (\a. prob_while_cut c b (N a) a) n a s))} =
           {x | ~c x} o FST o
           prob_while_cut c (\a. prob_while_cut c b (N a) a) n a`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
       >> Rewr
       >> MATCH_MP_TAC PROB_LE_1
       >> RW_TAC std_ss [PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                         INDEP_FN_PROB_WHILE_CUT])
   >> RW_TAC std_ss []
   >> Know `!x y : real. 1 - y <= x ==> 1 - x <= y` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> Know
      `{s |
        ~c (FST
            (prob_while_cut c (\a. prob_while_cut c b (N a) a) n a s))} =
       {x | ~c x} o FST o
       prob_while_cut c (\a. prob_while_cut c b (N a) a) n a`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
   >> Rewr
   >> Q.SPEC_TAC (`a`, `a`)
   >> Induct_on `n`
   >- RW_TAC std_ss [pow, prob_while_cut_def, PROB_POSITIVE, PROB_SPACE_BERN,
                     INDEP_FN_FST_EVENTS, INDEP_FN_UNIT, REAL_SUB_REFL]
   >> reverse (RW_TAC std_ss [prob_while_cut_def])
   >- (Know `{x | ~c x} o FST o UNIT a = (UNIV:(num->bool)->bool)`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [UNIT_DEF, IN_o, o_THM, GSPECIFICATION, IN_UNIV])
       >> Rewr
       >> RW_TAC std_ss [PROB_BERN_UNIV]
       >> Suff `0 <= (1 - e) pow SUC n` >- REAL_ARITH_TAC
       >> MATCH_MP_TAC POW_POS
       >> Q.PAT_X_ASSUM `e <= 1` MP_TAC
       >> REAL_ARITH_TAC)
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `prob bern ({x | ~c x} o FST o prob_while_cut c b (N a) a) * 1
       +
       (1 - prob bern ({x | ~c x} o FST o prob_while_cut c b (N a) a)) *
       (1 - (1 - e) pow n)`
   >> reverse CONJ_TAC
   >- (MATCH_MP_TAC PROB_BERN_BIND_LOWER
       >> RW_TAC std_ss [INDEP_FN_PROB_WHILE_CUT, GSPECIFICATION]
       >> Suff
          `{x | ~c x} o FST o
           prob_while_cut c (\a. prob_while_cut c b (N a) a) n a' = UNIV`
       >- RW_TAC std_ss [PROB_BERN_UNIV, REAL_LE_REFL]
       >> SET_EQ_TAC
       >> RW_TAC std_ss [IN_UNIV, IN_o, o_THM, GSPECIFICATION,
                         PROB_WHILE_CUT_ID, UNIT_DEF])
   >> Q.PAT_X_ASSUM `!a. P a` K_TAC
   >> Q.PAT_X_ASSUM `!a. P a` (MP_TAC o Q.SPEC `a`)
   >> Q.SPEC_TAC (`prob bern ({x | ~c x} o FST o prob_while_cut c b (N a) a)`,
                  `r`)
   >> RW_TAC real_ss [pow, REAL_SUB_RDISTRIB, REAL_SUB_LDISTRIB]
   >> Suff `e * (1 - e) pow n <= r * (1 - e) pow n`
   >- REAL_ARITH_TAC
   >> MATCH_MP_TAC REAL_LE_RMUL_IMP
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC POW_POS
   >> Q.PAT_X_ASSUM `e <= 1` MP_TAC
   >> REAL_ARITH_TAC);

val PROB_TERMINATES_HART = store_thm
  ("PROB_TERMINATES_HART",
   ``!c b.
       (!a. b a IN indep_fn) ==>
       (prob_while_terminates c b =
        (?e.
           0 < e /\
           !a. e <= prob bern {s | ?n. ~c (FST (prob_while_cut c b n a s))}))``,
   RW_TAC std_ss []
   >> EQ_TAC
   >- (RW_TAC std_ss [PROB_WHILE_TERMINATES, probably_def, probably_bern_def]
       >> Q.EXISTS_TAC `1`
       >> REAL_ARITH_TAC)
   >> STRIP_TAC
   >> MATCH_MP_TAC PROB_TERMINATES_HART_LEMMA
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `(1 / 2) * e`
   >> RW_TAC std_ss [HALF_POS, REAL_LT_MUL]
   >> Suff
      `?l.
         e <= l /\
         prob bern o (\N. {s | ~c (FST (prob_while_cut c b N a s))}) --> l`
   >- (RW_TAC std_ss [SEQ, o_DEF]
       >> POP_ASSUM (MP_TAC o Q.SPEC `(1 / 2) * e`)
       >> RW_TAC std_ss [HALF_POS, REAL_LT_MUL, GREATER_EQ]
       >> POP_ASSUM (MP_TAC o Q.SPEC `N`)
       >> RW_TAC arith_ss []
       >> Q.EXISTS_TAC `N`
       >> POP_ASSUM MP_TAC
       >> POP_ASSUM MP_TAC
       >> POP_ASSUM K_TAC
       >> POP_ASSUM MP_TAC
       >> POP_ASSUM K_TAC
       >> Q.SPEC_TAC (`prob bern {s | ~c (FST (prob_while_cut c b N a s))}`,
                      `r`)
       >> RW_TAC std_ss []
       >> Suff `2 * ((1 / 2) * e) <= 2 * r`
       >- RW_TAC arith_ss [REAL_LE_LMUL, REAL_NZ_IMP_LT]
       >> Know `2 * abs (r - l) < 2 * ((1 / 2) * e)`
       >- RW_TAC arith_ss [REAL_LT_LMUL, REAL_NZ_IMP_LT]
       >> POP_ASSUM K_TAC
       >> RW_TAC std_ss [abs, REAL_MUL_ASSOC, HALF_CANCEL, REAL_MUL_LID]
       >> REPEAT (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC)
   >> Q.EXISTS_TAC `prob bern {s | ?n. ~c (FST (prob_while_cut c b n a s))}`
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC PROB_INCREASING_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, SUBSET_DEF, GSPECIFICATION,
                     GBIGUNION_IMAGE] >|
   [Know
    `{s | ~c (FST (prob_while_cut c b N a s))} =
     {x | ~c x} o FST o prob_while_cut c b N a`
    >- (SET_EQ_TAC
        >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
    >> Rewr
    >> RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_WHILE_CUT],
    MATCH_MP_TAC PROB_WHILE_CUT_MONO
    >> Q.EXISTS_TAC `n`
    >> RW_TAC arith_ss []]);

val PROBABLY_CONJ = store_thm
  ("PROBABLY_CONJ",
   ``!p q. (!*s. p s) /\ (!*s. q s) ==> (!*s. p s /\ q s)``,
   REPEAT STRIP_TAC
   >> RW_TAC std_ss [probably_def, probably_bern_def]
   >- (FULL_SIMP_TAC std_ss [probably_def, probably_bern_def, GINTER]
       >> MATCH_MP_TAC EVENTS_INTER
       >> RW_TAC std_ss [PROB_SPACE_BERN])
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC `prob bern {s | q s}`
   >> reverse CONJ_TAC
   >- (POP_ASSUM MP_TAC
       >> RW_TAC std_ss [probably_def, probably_bern_def])
   >> HO_MATCH_MP_TAC PROB_BERN_UNIVERSAL
   >> Q.EXISTS_TAC `\s. p s`
   >> RW_TAC std_ss [GSPECIFICATION]
   >> FULL_SIMP_TAC std_ss [probably_def, probably_bern_def, GINTER]
   >> MATCH_MP_TAC EVENTS_INTER
   >> RW_TAC std_ss [PROB_SPACE_BERN]);

val PROBABLY_IMP = store_thm
  ("PROBABLY_IMP",
   ``!p q. {s | p s} IN events bern /\ (!*s. q s) ==> (!*s. p s ==> q s)``,
   REPEAT STRIP_TAC
   >> RW_TAC std_ss [probably_def, probably_bern_def]
   >- (FULL_SIMP_TAC std_ss
       [probably_def, probably_bern_def, GUNION, IMP_DISJ_THM, GCOMPL]
       >> MATCH_MP_TAC EVENTS_UNION
       >> PROVE_TAC [EVENTS_COMPL_BERN, PROB_SPACE_BERN])
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC `prob bern {s | q s}`
   >> reverse CONJ_TAC
   >- (POP_ASSUM MP_TAC
       >> RW_TAC std_ss [probably_def, probably_bern_def])
   >> HO_MATCH_MP_TAC PROB_BERN_UNIVERSAL
   >> Q.EXISTS_TAC `\s. q s`
   >> RW_TAC std_ss [GSPECIFICATION] (* 2 sub-goals here *)
   >> FULL_SIMP_TAC std_ss
      [probably_def, probably_bern_def, GUNION, IMP_DISJ_THM, GCOMPL]
   >> MATCH_MP_TAC EVENTS_UNION
   >> PROVE_TAC [EVENTS_COMPL_BERN, PROB_SPACE_BERN]);

val PROBABLY_MP = store_thm
  ("PROBABLY_MP",
   ``!p q.
       {s | q s} IN events bern /\ (!*s. p s) /\ (!*s. p s ==> q s) ==>
       (!*s. q s)``,
   REPEAT STRIP_TAC
   >> Know `!s. q s = (p s \/ q s) /\ (~p s \/ q s)`
   >- PROVE_TAC []
   >> Rewr'
   >> HO_MATCH_MP_TAC PROBABLY_CONJ
   >> RW_TAC std_ss [GSYM IMP_DISJ_THM]
   >> RW_TAC std_ss [probably_def, probably_bern_def]
   >- (FULL_SIMP_TAC std_ss
       [probably_def, probably_bern_def, GUNION, IMP_DISJ_THM, GCOMPL]
       >> MATCH_MP_TAC EVENTS_UNION
       >> PROVE_TAC [EVENTS_COMPL, PROB_SPACE_BERN])
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC `prob bern {s | p s}`
   >> reverse CONJ_TAC
   >- (POP_ASSUM MP_TAC
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [probably_def, probably_bern_def])
   >> HO_MATCH_MP_TAC PROB_BERN_UNIVERSAL
   >> Q.EXISTS_TAC `\s. p s`
   >> RW_TAC std_ss [GSPECIFICATION] (* 2 sub-goals here *)
   >> FULL_SIMP_TAC std_ss
      [probably_def, probably_bern_def, GUNION, IMP_DISJ_THM, GCOMPL]
   >> MATCH_MP_TAC EVENTS_UNION
   >> PROVE_TAC [EVENTS_COMPL, PROB_SPACE_BERN]);

val PROB_WHILE_HOARE = store_thm
  ("PROB_WHILE_HOARE",
   ``!p c b a.
       (!a. b a IN indep_fn) /\ prob_while_terminates c b /\
       p a /\ (!a. !*s. p a /\ c a ==> p (FST (b a s))) ==>
       !*s. p (FST (prob_while c b a s))``,
   REPEAT STRIP_TAC
   >> MATCH_MP_TAC PROB_WHILE
   >> RW_TAC std_ss []
   >> HO_MATCH_MP_TAC PROBABLY_IMP
   >> CONJ_TAC
   >- (Know
       `{s | ~c (FST (prob_while_cut c b n a s))} =
        {a | ~c a} o FST o prob_while_cut c b n a`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
       >> Rewr
       >> MATCH_MP_TAC INDEP_FN_FST_EVENTS
       >> MATCH_MP_TAC INDEP_FN_PROB_WHILE_CUT
       >> RW_TAC std_ss [])
   >> POP_ASSUM (fn th => POP_ASSUM MP_TAC >> ASSUME_TAC th)
   >> Q.SPEC_TAC (`a`, `a`)
   >> Induct_on `n`
   >- RW_TAC std_ss [PROB_WHILE_CUT_0, UNIT_DEF, PROBABLY_TRUE]
   >> RW_TAC std_ss [probably_def, probably_bern_def]
   >- (Know
       `{s | p (FST (prob_while_cut c b (SUC n) a s))} =
        {a | p a} o FST o prob_while_cut c b (SUC n) a`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
       >> Rewr
       >> MATCH_MP_TAC INDEP_FN_FST_EVENTS
       >> MATCH_MP_TAC INDEP_FN_PROB_WHILE_CUT
       >> RW_TAC std_ss [])
   >> Know
      `{s | p (FST (prob_while_cut c b (SUC n) a s))} =
       {a | p a} o FST o prob_while_cut c b (SUC n) a`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
   >> Rewr
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   >> CONJ_TAC
   >- RW_TAC std_ss [PROB_LE_1, PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                     INDEP_FN_PROB_WHILE_CUT]
   >> reverse (Cases_on `c a`)
   >- (RW_TAC std_ss [PROB_WHILE_CUT_ID]
       >> Suff `{a | p a} o FST o UNIT a = (UNIV:(num->bool)->bool)`
       >- RW_TAC std_ss [PROB_BERN_UNIV, REAL_LE_REFL]
       >> SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_UNIV, IN_o, o_THM, UNIT_DEF])
   >> RW_TAC std_ss [prob_while_cut_def]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `prob bern ({a | p a} o FST o b a) * 1 +
       (1 - prob bern ({a | p a} o FST o b a)) * 0`
   >> CONJ_TAC
   >- (RW_TAC real_ss []
       >> Suff `prob bern ({a | p a} o FST o b a) = prob bern UNIV`
       >- RW_TAC std_ss [REAL_LE_REFL, PROB_BERN_UNIV]
       >> HO_MATCH_MP_TAC PROB_BERN_UNIVERSAL
       >> Q.EXISTS_TAC `\s. p a /\ c a ==> p (FST (b a s))`
       >> RW_TAC std_ss [EVENTS_BERN_UNIV, INDEP_FN_FST_EVENTS,
                         INDEP_FN_PROB_WHILE_CUT, IN_UNIV, IN_o, o_THM,
                         GSPECIFICATION])
   >> MATCH_MP_TAC PROB_BERN_BIND_LOWER
   >> reverse (RW_TAC std_ss [INDEP_FN_PROB_WHILE_CUT, GSPECIFICATION])
   >- (RW_TAC std_ss [PROB_POSITIVE, PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                      INDEP_FN_PROB_WHILE_CUT])
   >> Suff
      `prob bern
       ({a | p a} o FST o prob_while_cut c b n a') = prob bern UNIV`
   >- RW_TAC std_ss [REAL_LE_REFL, PROB_BERN_UNIV]
   >> HO_MATCH_MP_TAC PROB_BERN_UNIVERSAL
   >> Q.EXISTS_TAC `\s. p (FST (prob_while_cut c b n a' s))`
   >> RW_TAC std_ss [EVENTS_BERN_UNIV, INDEP_FN_FST_EVENTS,
                     INDEP_FN_PROB_WHILE_CUT, IN_UNIV, IN_o, o_THM,
                     GSPECIFICATION]);

val PROB_TERMINATES_MORGAN = store_thm
  ("PROB_TERMINATES_MORGAN",
   ``!c b.
       (!a. b a IN indep_fn) /\
       (?f (N:num) p.
          0 < p /\
          !a.
            c a ==> f a <= N /\ p <= prob bern {s | f (FST (b a s)) < f a}) ==>
       prob_while_terminates c b``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`c`, `b`] PROB_TERMINATES_HART)
   >> impl_tac >- RW_TAC std_ss []
   >> Rewr
   >> reverse (Cases_on `p <= 1`)
   >- (Suff `!a. ~c a`
       >- (RW_TAC std_ss [PROB_WHILE_CUT_ID, GUNIV, PROB_BERN_UNIV]
           >> Q.EXISTS_TAC `1`
           >> REAL_ARITH_TAC)
       >> CCONTR_TAC
       >> POP_ASSUM MP_TAC
       >> CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
       >> REWRITE_TAC []
       >> STRIP_TAC
       >> Q.PAT_X_ASSUM `!a. P a` (MP_TAC o Q.SPEC `a`)
       >> RW_TAC std_ss []
       >> DISJ2_TAC
       >> STRIP_TAC
       >> Q.PAT_X_ASSUM `~x` MP_TAC
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `prob bern {s | f (FST (b a s)) < f a}`
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC PROB_LE_1
       >> RW_TAC std_ss [PROB_SPACE_BERN]
       >> Know `{s | f (FST (b a s)) < f a} = {x | f x < f a} o FST o b a`
       >- (SET_EQ_TAC >> RW_TAC std_ss [GSPECIFICATION, o_THM, IN_o])
       >> Rewr
       >> RW_TAC std_ss [INDEP_FN_FST_EVENTS])
   >> Q.EXISTS_TAC `p pow N`
   >> RW_TAC std_ss [REAL_POW_LT]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `prob bern {s | ~c (FST (prob_while_cut c b (SUC (f a)) a s))}`
   >> reverse CONJ_TAC
   >- (MATCH_MP_TAC PROB_INCREASING
       >> SIMP_TAC std_ss [GBIGUNION_IMAGE]
       >> Know `!f:(num->bool)->'a#(num->bool).
                  {s | ~c (FST (f s))} = {a | ~c a} o FST o f`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
       >> RW_TAC std_ss' [PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                          INDEP_FN_PROB_WHILE_CUT, SUBSET_DEF, IN_UNIV,
                          IN_BIGUNION_IMAGE, IN_o, o_THM, GSPECIFICATION] >|
       [MATCH_MP_TAC EVENTS_COUNTABLE_UNION
        >> RW_TAC std_ss [PROB_SPACE_BERN, IN_IMAGE, COUNTABLE_NUM, IN_UNIV,
                          image_countable, SUBSET_DEF]
        >> RW_TAC std_ss [PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                          INDEP_FN_PROB_WHILE_CUT],
        PROVE_TAC []])
   >> reverse (Cases_on `c a`)
   >- RW_TAC std_ss [PROB_WHILE_CUT_ID, UNIT_DEF, GUNIV, PROB_BERN_UNIV,
                     POW_LE_1]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `p pow f a`
   >> CONJ_TAC
   >- (MATCH_MP_TAC POW_LE_1_MONO
       >> PROVE_TAC [])
   >> POP_ASSUM K_TAC
   >> completeInduct_on `f a`
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!m : num. P m`
      (MP_TAC o
       CONV_RULE
       (DEPTH_CONV RIGHT_IMP_FORALL_CONV THENC HO_REWR_CONV SWAP_FORALL_THM) o
       Q.SPEC `f` o
       CONV_RULE
       (DEPTH_CONV RIGHT_IMP_FORALL_CONV THENC HO_REWR_CONV SWAP_FORALL_THM))
   >> RW_TAC std_ss []
   >> reverse (Cases_on `c a`)
   >- RW_TAC std_ss [PROB_WHILE_CUT_ID, UNIT_DEF, GUNIV, PROB_BERN_UNIV,
                     REAL_LE_REFL, POW_LE_1]
   >> Know `!f:(num->bool)->'a#(num->bool).
              {s | ~c (FST (f s))} = {a | ~c a} o FST o f`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
   >> Rewr
   >> RW_TAC std_ss [prob_while_cut_def]
   >> Cases_on `f a`
   >- (RW_TAC std_ss [pow, PROB_WHILE_CUT_0, BIND_RIGHT_UNIT]
       >> FULL_SIMP_TAC arith_ss []
       >> Q.PAT_X_ASSUM `!a. P a` (MP_TAC o Q.SPEC `a`)
       >> RW_TAC arith_ss [GEMPTY, PROB_BERN_EMPTY]
       >> Suff `0:real < 0` >- REAL_ARITH_TAC
       >> MATCH_MP_TAC REAL_LTE_TRANS
       >> PROVE_TAC [])
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `prob bern ({x | f x < f a} o FST o b a) * (p pow n) +
       (1 - prob bern ({x | f x < f a} o FST o b a)) * 0`
   >> CONJ_TAC
   >- (RW_TAC std_ss [pow, REAL_MUL_RZERO, REAL_ADD_RID]
       >> RW_TAC std_ss [REAL_LE_RMUL, REAL_POW_LT]
       >> Suff `{x | f x < SUC n} o FST o b a = {s | f (FST (b a s)) < f a}`
       >- (POP_ASSUM K_TAC
           >> RW_TAC std_ss [])
       >> SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
   >> MATCH_MP_TAC PROB_BERN_BIND_LOWER
   >> reverse (RW_TAC std_ss [INDEP_FN_PROB_WHILE_CUT, GSPECIFICATION])
   >- (MATCH_MP_TAC PROB_POSITIVE
       >> RW_TAC std_ss [PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                         INDEP_FN_PROB_WHILE_CUT])
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `p pow f a'`
   >> CONJ_TAC >- RW_TAC arith_ss [POW_LE_1_MONO]
   >> Know `({a | ~c a} o FST o prob_while_cut c b (SUC n) a') =
            {s | ~c (FST (prob_while_cut c b (SUC n) a' s))}`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
   >> Rewr
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `prob bern {s | ~c (FST (prob_while_cut c b (SUC (f a')) a' s))}`
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC PROB_INCREASING
   >> PURE_REWRITE_TAC [CONJ_ASSOC]
   >> CONJ_TAC
   >- (Know `!f:(num->bool)->'a#(num->bool).
               {s | ~c (FST (f s))} = {a | ~c a} o FST o f`
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
       >> Rewr
       >> RW_TAC std_ss [PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                         INDEP_FN_PROB_WHILE_CUT])
   >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
   >> MATCH_MP_TAC PROB_WHILE_CUT_MONO
   >> Q.EXISTS_TAC `SUC (f a')`
   >> RW_TAC arith_ss []);

val _ = export_theory ();
