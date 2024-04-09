(* ========================================================================= *)
(* Create "informationTheory" setting up the theory of information           *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib metisLib arithmeticTheory pred_setTheory
     listTheory state_transformerTheory combinTheory
     pairTheory realTheory realLib jrhUtils iterateTheory
     realSimps numTheory simpLib seqTheory subtypeTheory
     transcTheory limTheory stringTheory rich_listTheory stringSimps listSimps;

open extra_boolTheory extra_numTheory extra_pred_setTheory extra_realTheory;
open real_sigmaTheory;

open hurdUtils util_probTheory sigma_algebraTheory real_measureTheory
     real_borelTheory real_lebesgueTheory real_probabilityTheory;

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "information"                                   *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "information";

Overload indicator_fn[local] = “indicator”
Theorem indicator_fn_def[local] = indicator

val _ = temp_set_fixity "CROSS" (Infixl 600)

val _ = intLib.deprecate_int();
val _ = ratLib.deprecate_rat();

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

val KL_divergence_def = Define
   `KL_divergence b s u v =
        integral (space s, subsets s, u) (\x. logr b ((RN_deriv (space s, subsets s, v) u) x))`;

val mutual_information_def = Define
   `mutual_information b p s1 s2 X Y  =
        let prod_space =
                prod_measure_space (space s1, subsets s1, distribution p X)
                                   (space s2, subsets s2, distribution p Y) in
        KL_divergence b
                (p_space prod_space, events prod_space)
                (joint_distribution p X Y)
                (prob prod_space)`;

val entropy_def = Define
   `entropy b p s X = mutual_information b p s s X X`;


val conditional_mutual_information_def = Define
   `conditional_mutual_information b p s1 s2 s3 X Y Z =
        let prod_space =
            prod_measure_space (space s2, subsets s2, distribution p Y)
                               (space s3, subsets s3, distribution p Z) in
        mutual_information b p s1 (p_space prod_space, events prod_space) X (\x. (Y x, Z x)) -
        mutual_information b p s1 s3 X Z`;


(* ************************************************************************* *)
(* Proofs                                                                    *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(* Reductions                                                                *)
(* ************************************************************************* *)

(* NOTE: added ‘prob_space p’ into antecedents due to changes of ‘measurable’ *)
Theorem finite_mutual_information_reduce :
    !b p s1 s2 X Y. prob_space p /\ (POW (p_space p) = events p) /\
             random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p))) /\
             random_variable Y p (IMAGE Y (p_space p), POW (IMAGE Y (p_space p))) /\
                    FINITE (p_space p) ==>
        (mutual_information b p (IMAGE X (p_space p), POW (IMAGE X (p_space p)))
                                (IMAGE Y (p_space p), POW (IMAGE Y (p_space p))) X Y =
         SIGMA (\(x,y). (joint_distribution p X Y {(x,y)}) *
                         logr b ((joint_distribution p X Y {(x,y)})/
                                 ((distribution p X {x})*(distribution p Y {y}))))
               ((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p))))
Proof
   RW_TAC std_ss [mutual_information_def, KL_divergence_def, space_def, subsets_def]
   >> `FINITE (IMAGE X (p_space p)) /\ FINITE (IMAGE Y (p_space p))`
        by RW_TAC std_ss [IMAGE_FINITE]
   >> Q.ABBREV_TAC `s1 = IMAGE X (p_space p)`
   >> Q.ABBREV_TAC `s2 = IMAGE Y (p_space p)`
   >> Know `prod_space = (s1 CROSS s2, POW (s1 CROSS s2), prod_measure (s1, POW s1, distribution p X)
                                                                  (s2, POW s2, distribution p Y))`
   >- ( Q.UNABBREV_TAC `prod_space`
        >> RW_TAC std_ss [prod_measure_space_def, m_space_def, subsets_def, EXTENSION, subsets_def,
                          sigma_def, prod_sets_def, IN_POW, IN_BIGINTER, measurable_sets_def, SUBSET_DEF,
                          IN_CROSS, GSPECIFICATION]
        >> RW_TAC std_ss [GSYM EXTENSION]
        >> EQ_TAC
        >- (RW_TAC std_ss [] >> Q.PAT_X_ASSUM `!s. P ==> x IN s` (MP_TAC o Q.SPEC `POW (s1 CROSS s2)`)
            >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS, POW_SIGMA_ALGEBRA]
            >> Suff `(!x''. (?x'. (x'',T) = (\(s,t). (s CROSS t,
                        (!x. x IN s ==> x IN s1) /\ !x. x IN t ==> x IN s2))
                        x') ==> !x. x IN x'' ==> FST x IN s1 /\ SND x IN s2)` >- METIS_TAC []
            >> RW_TAC std_ss [] >> (MP_TAC o Q.ISPEC `(x''' :('d -> bool) # ('e -> bool))`) pair_CASES
            >> STRIP_TAC >> FULL_SIMP_TAC std_ss [] >> METIS_TAC [IN_CROSS] )
        >> RW_TAC std_ss []
        >> `x = BIGUNION (IMAGE (\a. {a}) x)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
        >> POP_ORW
        >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
        >> POP_ASSUM MATCH_MP_TAC
        >> CONJ_TAC
        >- (MATCH_MP_TAC FINITE_COUNTABLE >> MATCH_MP_TAC IMAGE_FINITE
                >> (MP_TAC o Q.ISPEC `(s1 :'d -> bool) CROSS (s2 :'e -> bool)`) SUBSET_FINITE
                >> RW_TAC std_ss [FINITE_CROSS]
                >> POP_ASSUM MATCH_MP_TAC
                >> METIS_TAC [SUBSET_DEF, IN_CROSS])
        >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
        >> Q.PAT_X_ASSUM `!x. Q ==> x IN P` MATCH_MP_TAC
        >> Q.EXISTS_TAC `({FST a}, {SND a})` >> RW_TAC std_ss [PAIR_EQ, IN_SING]
        >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_SING]
        >> METIS_TAC [PAIR_EQ, PAIR, FST, SND] )
   >> DISCH_TAC
   >> POP_ORW
   >> RW_TAC std_ss [PSPACE, EVENTS]
   >> (MP_TAC o Q.SPECL [`p`, `s1`, `s2`, `X`, `Y`] o
        INST_TYPE [``:'c`` |-> ``:'e``, ``:'b``|->``:'d``]) finite_marginal_product_space_POW2
   >> ASM_SIMP_TAC std_ss []
   >> STRIP_TAC
   >> (MP_TAC o Q.SPEC `(s1 CROSS s2,POW (s1 CROSS s2),joint_distribution p X Y)`
        o INST_TYPE [``:'a`` |-> ``:'d # 'e``]) finite_space_POW_integral_reduce
   >> ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, FINITE_CROSS]
   >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
   >> `FINITE (s1 CROSS s2)`
        by RW_TAC std_ss [FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s1 :'d -> bool)
                        CROSS (s2 :'e -> bool)`) REAL_SUM_IMAGE_IN_IF]
   >> Suff `(\x.
     (if x IN s1 CROSS s2 then
        (\x.
           logr b
             (RN_deriv
                (s1 CROSS s2,POW (s1 CROSS s2),
                 prob
                   (s1 CROSS s2,POW (s1 CROSS s2),
                    prod_measure (s1,POW s1,distribution p X)
                      (s2,POW s2,distribution p Y)))
                (joint_distribution p X Y) x) *
           measure
             (s1 CROSS s2,POW (s1 CROSS s2),joint_distribution p X Y)
             {x}) x
      else
        0)) =
        (\x.
     (if x IN s1 CROSS s2 then
        (\(x,y).
           joint_distribution p X Y {(x,y)} *
           logr b
             (joint_distribution p X Y {(x,y)} /
              (distribution p X {x} * distribution p Y {y}))) x
      else
        0))`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [FUN_EQ_THM]
   >> RW_TAC std_ss [PROB, measure_def]
   >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR]
   >> POP_ORW
   >> RW_TAC std_ss []
   >> Cases_on `joint_distribution p X Y {x} = 0`
   >- RW_TAC real_ss []
   >> RW_TAC std_ss [REAL_MUL_COMM, REAL_EQ_LMUL]
   >> Suff `(RN_deriv
     (s1 CROSS s2,POW (s1 CROSS s2),
      prod_measure (s1,POW s1,distribution p X)
        (s2,POW s2,distribution p Y)) (joint_distribution p X Y) x) =
        (joint_distribution p X Y {x} /
        (distribution p X {FST x} * distribution p Y {SND x}))`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [RN_deriv_def]
   >> Suff `(\f. f x = joint_distribution p X Y {x} /
        (distribution p X {FST x} * distribution p Y {SND x}))
        (@f.
   measure_space
     (s1 CROSS s2,POW (s1 CROSS s2),
      prod_measure (s1,POW s1,distribution p X)
        (s2,POW s2,distribution p Y)) /\
   measure_space
     (m_space
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p Y)),
      measurable_sets
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p Y)),joint_distribution p X Y) /\
   f IN
   borel_measurable
     (m_space
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p Y)),
      measurable_sets
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p Y))) /\
   !a.
     a IN
     measurable_sets
       (s1 CROSS s2,POW (s1 CROSS s2),
        prod_measure (s1,POW s1,distribution p X)
          (s2,POW s2,distribution p Y)) ==>
     (integral
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p Y)) (\x. f x * indicator_fn a x) =
      joint_distribution p X Y a))`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC SELECT_ELIM_THM
   >> `measure_space (s1 CROSS s2, POW (s1 CROSS s2),
                   prod_measure
                     (s1,POW s1,distribution p X)
                     (s2,POW s2,distribution p Y))`
        by (METIS_TAC [measurable_sets_def, distribution_prob_space,
                       space_def, subsets_def, m_space_def, prob_space_def,
                       measure_space_finite_prod_measure_POW2,
                       POW_SIGMA_ALGEBRA])
   >> RW_TAC std_ss [measurable_sets_def, m_space_def]
   >- (Q.EXISTS_TAC `\x'. joint_distribution p X Y {x'} /
                         ((distribution p X {FST x'})*(distribution p Y {SND x'}))`
       >> STRONG_CONJ_TAC
       >- (`(s1 CROSS s2,POW (s1 CROSS s2)) =
            (m_space (s1 CROSS s2,POW (s1 CROSS s2),
                prod_measure (s1,POW s1,distribution p X)
                (s2,POW s2,distribution p Y)),
             measurable_sets (s1 CROSS s2,POW (s1 CROSS s2),
                prod_measure (s1,POW s1,distribution p X)
                (s2,POW s2,distribution p Y)))` by RW_TAC std_ss [measurable_sets_def, m_space_def]
            >> POP_ORW
            >> ASM_SIMP_TAC std_ss [borel_measurable_le_iff, IN_POW, SUBSET_DEF, GSPECIFICATION,
                                    measurable_sets_def, m_space_def])
       >> RW_TAC std_ss [IN_POW]
       >> (MP_TAC o Q.SPEC `(s1 CROSS s2,POW (s1 CROSS s2),prod_measure (s1,POW s1,distribution p X)
                        (s2,POW s2,distribution p Y))`
        o INST_TYPE [``:'a`` |-> ``:'d # 'e``]) finite_space_POW_integral_reduce
       >> ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, FINITE_CROSS, measure_def]
       >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
       >> `(s1 CROSS s2) = a UNION ((s1 CROSS s2) DIFF a)`
                by (ONCE_REWRITE_TAC [EXTENSION]
                    >> RW_TAC std_ss [IN_UNION, IN_DIFF] >> METIS_TAC [SUBSET_DEF])
       >> POP_ORW
       >> `DISJOINT a ((s1 CROSS s2) DIFF a)`
                by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
       >> `FINITE a` by METIS_TAC [SUBSET_FINITE, FINITE_CROSS, IMAGE_FINITE]
       >> RW_TAC std_ss [FINITE_DIFF, REAL_SUM_IMAGE_DISJOINT_UNION]
       >> `FINITE ((s1 CROSS s2) DIFF a)`
                by RW_TAC std_ss [FINITE_DIFF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `((s1 :'d -> bool) CROSS (s2 :'e -> bool)) DIFF a`)
                                REAL_SUM_IMAGE_IN_IF]
       >> `(\x. (if x IN s1 CROSS s2 DIFF a then
            (\x'.
               joint_distribution p X Y {x'} /
               (distribution p X {FST x'} * distribution p Y {SND x'}) * indicator_fn a x' *
               prod_measure (s1,POW s1,distribution p X)
             (s2,POW s2,distribution p Y) {x'}) x else 0)) = (\x. 0)`
                by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DIFF, indicator_fn_def])
       >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
       >> POP_ASSUM (K ALL_TAC)
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(a :'d # 'e -> bool)`) REAL_SUM_IMAGE_IN_IF]
       >> Know `(\x. (if x IN a then (\x'.
           joint_distribution p X Y {x'} /
           (distribution p X {FST x'} * distribution p Y {SND x'}) *
           indicator_fn a x' *
           prod_measure (s1,POW s1,distribution p X)
             (s2,POW s2,distribution p Y) {x'}) x else 0)) =
            (\x. if x IN a then
                (\x. joint_distribution p X Y {x}) x else 0)`

       >- ( RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [indicator_fn_def]
            >> `{x'} = {FST x'} CROSS {SND x'}`
                        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_SING, IN_CROSS]
                            >> (MP_TAC o Q.ISPEC `(x'' :'d # 'e)`) pair_CASES
                            >> (MP_TAC o Q.ISPEC `(x' :'d # 'e)`) pair_CASES
                            >> RW_TAC std_ss [])
            >> POP_ORW
            >> `prod_measure (s1,POW s1,distribution p X) (s2,POW s2,distribution p Y)
                ({FST x'} CROSS {SND x'}) =
                measure (s1,POW s1,distribution p X) {FST x'} *
                measure (s2,POW s2,distribution p Y) {SND x'}`
                by (`measure_space (s1,POW s1,distribution p X) /\
                     measure_space (s2,POW s2,distribution p Y)`
                        by METIS_TAC [distribution_prob_space, POW_SIGMA_ALGEBRA,
                                      prob_space_def, space_def, subsets_def]
                    >> `{FST x'} IN measurable_sets (s1,POW s1,distribution p X) /\
                        {SND x'} IN measurable_sets (s2,POW s2,distribution p Y)`
                        by (RW_TAC std_ss [measurable_sets_def, IN_POW, SUBSET_DEF, IN_SING]
                            >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_CROSS])
                    >> METIS_TAC [finite_POW_prod_measure_reduce, m_space_def,
                                  measurable_sets_def])
            >> POP_ORW
            >> RW_TAC std_ss [measure_def]
            >> Cases_on `(distribution p X {FST x'} * distribution p Y {SND x'}) = 0`
            >- (Suff `joint_distribution p X Y ({FST x'} CROSS {SND x'}) = 0`
                >- RW_TAC real_ss []
                >> `PREIMAGE X {FST x'} INTER p_space p IN events p`
                  by (Q.UNABBREV_TAC `s1`
                      >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, space_def,
                                               subsets_def, IN_POW]
                      >> Suff `{FST x'} SUBSET IMAGE X (p_space p)` >- METIS_TAC []
                      >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_CROSS])
                >> `PREIMAGE Y {SND x'} INTER p_space p IN events p`
                  by (Q.UNABBREV_TAC `s2`
                      >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, space_def,
                                               subsets_def, IN_POW]
                      >> Suff `{SND x'} SUBSET IMAGE Y (p_space p)` >- METIS_TAC []
                      >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_CROSS])
                >> `(PREIMAGE X {FST x'} INTER PREIMAGE Y {SND x'} INTER p_space p) IN events p`
                  by (`PREIMAGE X {FST x'} INTER PREIMAGE Y {SND x'} INTER p_space p =
                      (PREIMAGE X {FST x'} INTER p_space p) INTER
                      (PREIMAGE Y {SND x'} INTER p_space p)`
                        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER] >> DECIDE_TAC)
                      >> POP_ORW
                      >> FULL_SIMP_TAC std_ss [random_variable_def, prob_space_def, measure_space_def,
                                               events_def]
                      >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, space_def, subsets_def])
                >> FULL_SIMP_TAC std_ss [REAL_ENTIRE, distribution_def, joint_distribution_def]
                >- (`(PREIMAGE (\x. (X x,Y x)) ({FST x'} CROSS {SND x'}) INTER p_space p) =
                     (PREIMAGE X {FST x'} INTER PREIMAGE Y {SND x'} INTER p_space p)`
                        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_CROSS, IN_SING])
                    >> POP_ORW
                    >> RW_TAC std_ss [GSYM REAL_LE_ANTISYM]
                    >- (Suff `(PREIMAGE X {FST x'} INTER PREIMAGE Y {SND x'} INTER p_space p) SUBSET
                              (PREIMAGE X {FST x'} INTER p_space p)`
                        >- METIS_TAC [REAL_LE_TRANS, REAL_LE_REFL, PROB_INCREASING, random_variable_def]
                        >> RW_TAC std_ss [SUBSET_DEF, IN_INTER])
                    >> METIS_TAC [random_variable_def, PROB_POSITIVE])
                    >> `(PREIMAGE (\x. (X x,Y x)) ({FST x'} CROSS {SND x'}) INTER p_space p) =
                        (PREIMAGE X {FST x'} INTER PREIMAGE Y {SND x'} INTER p_space p)`
                          by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_CROSS, IN_SING])
                    >> POP_ORW
                    >> RW_TAC std_ss [GSYM REAL_LE_ANTISYM]
                    >- (Suff `(PREIMAGE X {FST x'} INTER PREIMAGE Y {SND x'} INTER p_space p) SUBSET
                              (PREIMAGE Y {SND x'} INTER p_space p)`
                        >- METIS_TAC [REAL_LE_TRANS, REAL_LE_REFL, PROB_INCREASING, random_variable_def]
                        >> RW_TAC std_ss [SUBSET_DEF, IN_INTER])
                    >> METIS_TAC [random_variable_def, PROB_POSITIVE])
            >> RW_TAC std_ss [real_div, measure_def]
            >> `joint_distribution p X Y ({FST x'} CROSS {SND x'}) *
                        inv (distribution p X {FST x'} * distribution p Y {SND x'}) *
                        (distribution p X {FST x'} * distribution p Y {SND x'}) =
                        (inv (distribution p X {FST x'} * distribution p Y {SND x'}) *
                        (distribution p X {FST x'} * distribution p Y {SND x'})) *
                        joint_distribution p X Y ({FST x'} CROSS {SND x'})`
                        by REAL_ARITH_TAC
            >> POP_ORW
            >> RW_TAC real_ss [REAL_MUL_LINV])
       >> DISCH_TAC
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
       >> Q.PAT_X_ASSUM `a SUBSET s1 CROSS s2` MP_TAC
       >> CONV_TAC (UNBETA_CONV ``(a :'d # 'e -> bool)``)
       >> Q.PAT_X_ASSUM `FINITE a` MP_TAC
       >> Q.SPEC_TAC (`a`,`a`)
       >> MATCH_MP_TAC FINITE_INDUCT
       >> FULL_SIMP_TAC std_ss [random_variable_def]
       >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, PREIMAGE_EMPTY, INTER_EMPTY, PROB_EMPTY, DELETE_NON_ELEMENT,
                         joint_distribution_def]
       >> `(PREIMAGE (\x. (X x,Y x)) (e INSERT s) INTER p_space p) =
           (PREIMAGE (\x. (X x,Y x)) {e} INTER p_space p) UNION
           (PREIMAGE (\x. (X x,Y x)) s INTER p_space p)`
                by (ONCE_REWRITE_TAC [EXTENSION]
                    >> RW_TAC std_ss [IN_UNION, IN_INTER, IN_PREIMAGE, IN_INSERT, NOT_IN_EMPTY]
                    >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, SUBSET_DEF, IN_INSERT, IN_CROSS, IN_IMAGE]
                    >> METIS_TAC [FST, SND])
       >> POP_ORW
       >> `DISJOINT (PREIMAGE (\x. (X x,Y x)) {e} INTER p_space p)
                    (PREIMAGE (\x. (X x,Y x)) s INTER p_space p)`
                by (RW_TAC std_ss [IN_DISJOINT, IN_INTER, IN_PREIMAGE, IN_SING]
                    >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
                    >> METIS_TAC [])
       >> `prob p (PREIMAGE (\x. (X x,Y x)) {e} INTER p_space p UNION
                   PREIMAGE (\x. (X x,Y x)) s INTER p_space p) =
           prob p (PREIMAGE (\x. (X x,Y x)) {e} INTER p_space p) +
           prob p (PREIMAGE (\x. (X x,Y x)) s INTER p_space p)`
                by (MATCH_MP_TAC PROB_ADDITIVE
                    >> RW_TAC std_ss []
                    >> METIS_TAC [SUBSET_DEF, IN_INTER, IN_POW])
       >> POP_ORW
       >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT])
   >> POP_ASSUM (MP_TAC o Q.SPEC `{x}`)
   >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_SING, finite_space_POW_integral_reduce,
                     FINITE_CROSS, IMAGE_FINITE, measurable_sets_def, m_space_def,
                     measure_def]
   >> POP_ASSUM MP_TAC
   >> `(s1 CROSS s2) =
        x INSERT ((s1 CROSS s2) DELETE x)`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INSERT, IN_DELETE] >> METIS_TAC [])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_THM, FINITE_CROSS, FINITE_DELETE, DELETE_DELETE]
   >> `FINITE (s1 CROSS s2 DELETE x)`
        by RW_TAC std_ss [FINITE_DELETE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `((s1 :'d -> bool) CROSS
                        (s2 :'e -> bool) DELETE (x :'d # 'e))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x''.
      (if x'' IN s1 CROSS s2 DELETE x then
         (\x''.
            x' x'' * indicator_fn {x} x'' *
            prod_measure (s1,POW s1,distribution p X)
              (s2,POW s2,distribution p Y) {x''}) x''
       else
         0)) = (\x'. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [indicator_fn_def, IN_SING, IN_DELETE])
   >> POP_ORW
   >> ASM_SIMP_TAC real_ss [REAL_SUM_IMAGE_0, indicator_fn_def, IN_SING]
   >> `{(x :'d # 'e)} = {FST x} CROSS {SND x}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_SING, IN_CROSS]
                            >> (MP_TAC o Q.ISPEC `(x'' :'d # 'e)`) pair_CASES
                            >> (MP_TAC o Q.ISPEC `(x :'d # 'e)`) pair_CASES
                            >> RW_TAC std_ss [])
   >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> `prod_measure (s1,POW s1,distribution p X) (s2,POW s2,distribution p Y)
                        ({FST x} CROSS {SND x}) =
                        measure (s1,POW s1,distribution p X) {FST x} *
                        measure (s2,POW s2,distribution p Y) {SND x}`
                        by (`measure_space (s1,POW s1,distribution p X) /\
                             measure_space (s2,POW s2,distribution p Y)`
                                by METIS_TAC [distribution_prob_space, prob_space_def,
                                              space_def, subsets_def, POW_SIGMA_ALGEBRA]
                            >> `{FST x} IN measurable_sets (s1,POW s1,distribution p X) /\
                                {SND x} IN measurable_sets (s2,POW s2,distribution p Y)`
                                by (RW_TAC std_ss [measurable_sets_def, IN_POW, SUBSET_DEF, IN_SING]
                                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_CROSS])
                            >> METIS_TAC [finite_POW_prod_measure_reduce, m_space_def, measurable_sets_def])
   >> POP_ORW
   >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR]
   >> POP_ORW
   >> FULL_SIMP_TAC std_ss [measure_def, joint_distribution_def, distribution_def]
   >> `PREIMAGE (\x. (X x,Y x)) ({FST x} CROSS {SND x}) INTER
        p_space p =
        PREIMAGE X {FST x} INTER PREIMAGE Y {SND x} INTER p_space p`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, IN_CROSS])
   >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> POP_ORW
   >> Suff `0 < (prob p (PREIMAGE X {FST x} INTER p_space p) *
            prob p (PREIMAGE Y {SND x} INTER p_space p))`
   >- RW_TAC real_ss [REAL_EQ_RDIV_EQ]
   >> MATCH_MP_TAC REAL_LT_MUL
   >> SIMP_TAC std_ss [REAL_LT_LE]
   >> `PREIMAGE X {FST x} INTER p_space p IN events p`
                by (Q.UNABBREV_TAC `s1`
                    >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, space_def, subsets_def,
                                                          IN_POW]
                    >> Suff `{FST x} SUBSET IMAGE X (p_space p)` >- METIS_TAC []
                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_CROSS])
   >> `PREIMAGE Y {SND x} INTER p_space p IN events p`
                by (Q.UNABBREV_TAC `s2`
                    >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, space_def, subsets_def,
                                                          IN_POW]
                    >> Suff `{SND x} SUBSET IMAGE Y (p_space p)` >- METIS_TAC []
                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_CROSS])
   >> `PREIMAGE X {FST x} INTER PREIMAGE Y {SND x} INTER p_space p IN events p`
                by (`PREIMAGE X {FST x} INTER PREIMAGE Y {SND x} INTER p_space p =
                                    (PREIMAGE X {FST x} INTER p_space p) INTER
                                    (PREIMAGE Y {SND x} INTER p_space p)`
                                        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER] >> DECIDE_TAC)
                    >> POP_ORW
                    >> FULL_SIMP_TAC std_ss [random_variable_def, prob_space_def, measure_space_def,
                                             events_def]
                    >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, space_def, subsets_def])
    >> Suff `~(0 = prob p (PREIMAGE X {FST x} INTER p_space p)) /\
                     ~(0 = prob p (PREIMAGE Y {SND x} INTER p_space p))`
    >- METIS_TAC [random_variable_def, PROB_POSITIVE]
    >> `0 <= prob p
              (PREIMAGE X {FST x} INTER PREIMAGE Y {SND x} INTER
               p_space p)`
                by METIS_TAC [random_variable_def, PROB_POSITIVE]
    >> (CONJ_TAC >> SPOSE_NOT_THEN STRIP_ASSUME_TAC)
    >- (Suff `prob p (PREIMAGE (X :'a -> 'd) {FST x} INTER PREIMAGE (Y :'a -> 'e) {SND x} INTER p_space p) <=
              prob p (PREIMAGE (X :'a -> 'd) {FST x} INTER p_space p)`
                >- METIS_TAC [REAL_LE_ANTISYM]
                >> MATCH_MP_TAC PROB_INCREASING
                >> FULL_SIMP_TAC std_ss [random_variable_def, SUBSET_DEF, IN_INTER])
    >> Suff `prob p (PREIMAGE X {FST x} INTER PREIMAGE Y {SND x} INTER p_space p) <=
                      prob p (PREIMAGE Y {SND x} INTER p_space p)`
    >- METIS_TAC [REAL_LE_ANTISYM]
    >> MATCH_MP_TAC PROB_INCREASING
    >> FULL_SIMP_TAC std_ss [random_variable_def, SUBSET_DEF, IN_INTER]
QED

(* NOTE: added ‘prob_space p’ into antecedents due to changes of ‘measurable’ *)
Theorem finite_entropy_reduce :
    !b p X. prob_space p /\ (POW (p_space p) = events p) /\
             random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p))) /\
                    FINITE (p_space p) ==>
        (entropy b p (IMAGE X (p_space p), POW (IMAGE X (p_space p))) X =
         ~ SIGMA (\x. distribution p X {x} * logr b (distribution p X {x}))
               (IMAGE X (p_space p)))
Proof
   RW_TAC std_ss [entropy_def, finite_mutual_information_reduce]
   >> `(IMAGE X (p_space p) CROSS IMAGE X (p_space p)) =
        (IMAGE (\x. (x,x)) (IMAGE X (p_space p))) UNION
        ((IMAGE X (p_space p) CROSS IMAGE X (p_space p)) DIFF
         (IMAGE (\x. (x,x)) (IMAGE X (p_space p))))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_IMAGE, IN_UNION, IN_DIFF]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> METIS_TAC [])
            >> RW_TAC std_ss [FST, SND] >> RW_TAC std_ss [FST, SND]
            >> METIS_TAC [])
   >> POP_ORW
   >> `DISJOINT (IMAGE (\x. (x,x)) (IMAGE X (p_space p)))
                (IMAGE X (p_space p) CROSS IMAGE X (p_space p) DIFF
                 IMAGE (\x. (x,x)) (IMAGE X (p_space p)))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
   >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION, FINITE_CROSS, IMAGE_FINITE, FINITE_DIFF]
   >> `FINITE (IMAGE X (p_space p) CROSS IMAGE X (p_space p) DIFF
               IMAGE (\x. (x,x)) (IMAGE X (p_space p)))`
        by RW_TAC std_ss [FINITE_CROSS, IMAGE_FINITE, FINITE_DIFF]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p) CROSS IMAGE (X :'a -> 'b) (p_space p) DIFF
               IMAGE (\x. (x,x)) (IMAGE (X :'a -> 'b) (p_space p)))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
         (if
            x IN
            IMAGE X (p_space p) CROSS IMAGE X (p_space p) DIFF
            IMAGE (\x. (x,x)) (IMAGE X (p_space p))
          then
            (\(x,y).
               joint_distribution p X X {(x,y)} *
               logr b
                 (joint_distribution p X X {(x,y)} / (distribution p X {x} * distribution p X {y})))
              x
          else
            0)) = (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM, IN_IMAGE, IN_DIFF] >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [IN_CROSS, IN_IMAGE]
            >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR]
            >> POP_ORW
            >> ASM_SIMP_TAC std_ss [joint_distribution_def]
            >> `PREIMAGE (\x. (X x,X x)) {x} INTER p_space p =
                PREIMAGE X {X x'} INTER PREIMAGE X {X x''} INTER p_space p`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, IN_CROSS]
                    >> METIS_TAC [PAIR, FST, SND, PAIR_EQ])
            >> POP_ORW
            >> Suff `PREIMAGE X {X x'} INTER PREIMAGE X {X x''} INTER p_space p = {}`
            >- FULL_SIMP_TAC real_ss [PROB_EMPTY, random_variable_def]
            >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_PREIMAGE, IN_INTER, IN_SING, NOT_IN_EMPTY]
            >> METIS_TAC [PAIR])
   >> POP_ORW >> ASM_SIMP_TAC real_ss [REAL_SUM_IMAGE_0]
   >> `INJ (\x. (x,x)) (IMAGE X (p_space p)) (IMAGE (\x. (x,x)) (IMAGE X (p_space p)))`
        by RW_TAC std_ss [INJ_DEF, IN_IMAGE]
   >> ASM_SIMP_TAC std_ss [IMAGE_FINITE, REAL_SUM_IMAGE_IMAGE, o_DEF]
   >> `~SIGMA (\x. distribution p X {x} * logr b (distribution p X {x})) (IMAGE X (p_space p)) =
       ~1 * SIGMA (\x. distribution p X {x} * logr b (distribution p X {x})) (IMAGE X (p_space p))`
        by REAL_ARITH_TAC
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_CMUL, IMAGE_FINITE]
   >> Suff `(\x.
         joint_distribution p X X {(x,x)} *
         logr b (joint_distribution p X X {(x,x)} / (distribution p X {x} * distribution p X {x}))) =
        (\x. ~1 * (distribution p X {x} * logr b (distribution p X {x})))`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [FUN_EQ_THM, joint_distribution_def, distribution_def]
   >> `PREIMAGE (\x. (X x,X x)) {(x,x)} INTER p_space p =
                PREIMAGE X {x} INTER p_space p`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, IN_CROSS, INTER_IDEMPOT]
                    >> METIS_TAC [PAIR, FST, SND, PAIR_EQ])
   >> POP_ORW
   >> RW_TAC real_ss []
   >> Cases_on `prob p (PREIMAGE X {x} INTER p_space p) = 0`
   >- RW_TAC real_ss []
   >> `0 < prob p (PREIMAGE X {x} INTER p_space p)`
        by METIS_TAC [REAL_LT_LE, PROB_POSITIVE, random_variable_def, SUBSET_DEF, IN_POW, IN_INTER]
   >> Suff `prob p (PREIMAGE X {x} INTER p_space p) /
       (prob p (PREIMAGE X {x} INTER p_space p) *
        prob p (PREIMAGE X {x} INTER p_space p)) =
        inv (prob p (PREIMAGE X {x} INTER p_space p))`
   >- RW_TAC std_ss [REAL_NEG_RMUL, logr_inv]
   >> RW_TAC std_ss [real_div, REAL_INV_MUL]
   >> RW_TAC real_ss [REAL_MUL_RINV, REAL_MUL_ASSOC]
QED

(* NOTE: added ‘prob_space p’ into antecedents due to changes of ‘measurable’ *)
Theorem finite_mutual_information_reduce2 :
    !b p s1 s2 X Y Z. prob_space p /\ (POW (p_space p) = events p) /\
             random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p))) /\
             random_variable Y p (IMAGE Y (p_space p), POW (IMAGE Y (p_space p))) /\
             random_variable Z p (IMAGE Z (p_space p), POW (IMAGE Z (p_space p))) /\

                    FINITE (p_space p) ==>
        (mutual_information b p (IMAGE X (p_space p), POW (IMAGE X (p_space p)))
                                (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p),
                                 POW (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p))) X (\x. (Y x,Z x)) =
         SIGMA (\(x,(y,z)). (joint_distribution p X (\x. (Y x,Z x)) {(x,(y,z))}) *
                         logr b ((joint_distribution p X (\x. (Y x,Z x)) {(x,(y,z))})/
                                 ((distribution p X {x})*(distribution p (\x. (Y x,Z x)) {(y,z)}))))
               ((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p))))
Proof
   RW_TAC std_ss [mutual_information_def, KL_divergence_def, space_def, subsets_def]
   >> `FINITE (IMAGE X (p_space p)) /\ FINITE (IMAGE Y (p_space p)) /\ FINITE (IMAGE Z (p_space p)) /\
       FINITE (IMAGE (\x. (Y x,Z x)) (p_space p))`
        by RW_TAC std_ss [IMAGE_FINITE]
   >> Q.ABBREV_TAC `s1 = IMAGE X (p_space p)`
   >> Q.ABBREV_TAC `s2 = (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p))`
   >> `FINITE s2` by METIS_TAC [FINITE_CROSS]
   >> Know `prod_space = (s1 CROSS s2, POW (s1 CROSS s2),
                     prod_measure (s1, POW s1, distribution p X)
                                  (s2, POW s2, distribution p (\x. (Y x,Z x))))`
   >- ( Q.UNABBREV_TAC `prod_space`
        >> RW_TAC std_ss [prod_measure_space_def, m_space_def, subsets_def, EXTENSION, subsets_def,
                          sigma_def, prod_sets_def, IN_POW, IN_BIGINTER, measurable_sets_def,
                          SUBSET_DEF, IN_CROSS, GSPECIFICATION]
        >> RW_TAC std_ss [GSYM EXTENSION]
        >> EQ_TAC
        >- (RW_TAC std_ss []
            >> Q.PAT_X_ASSUM `!s. P ==> x IN s` (MP_TAC o Q.SPEC `POW (s1 CROSS s2)`)
            >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS, POW_SIGMA_ALGEBRA]
            >> Suff `(!x''. (?x'. (x'',T) = (\(s,t). (s CROSS t,
                        (!x. x IN s ==> x IN s1) /\ !x. x IN t ==> x IN s2))
                        x') ==> !x. x IN x'' ==> FST x IN s1 /\ SND x IN s2)` >- METIS_TAC []
            >> RW_TAC std_ss []
            >> (MP_TAC o Q.ISPEC `(x''' :('d -> bool) # ('e # 'f -> bool))`) pair_CASES
            >> STRIP_TAC >> FULL_SIMP_TAC std_ss [] >> METIS_TAC [IN_CROSS])

        >> RW_TAC std_ss []
        >> `x = BIGUNION (IMAGE (\a. {a}) x)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
        >> POP_ORW
        >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
        >> POP_ASSUM MATCH_MP_TAC
        >> CONJ_TAC
        >- (MATCH_MP_TAC FINITE_COUNTABLE >> MATCH_MP_TAC IMAGE_FINITE
                >> (MP_TAC o Q.ISPEC `(s1 :'d -> bool) CROSS (s2 :'e # 'f -> bool)`) SUBSET_FINITE
                >> RW_TAC std_ss [FINITE_CROSS]
                >> POP_ASSUM MATCH_MP_TAC
                >> METIS_TAC [SUBSET_DEF, IN_CROSS])
        >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
        >> Q.PAT_X_ASSUM `!x. Q ==> x IN P` MATCH_MP_TAC
        >> Q.EXISTS_TAC `({FST a}, {SND a})` >> RW_TAC std_ss [PAIR_EQ, IN_SING]
        >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_SING]
        >> METIS_TAC [PAIR_EQ, PAIR, FST, SND] )
   >> DISCH_TAC
   >> POP_ORW
   >> RW_TAC std_ss [PSPACE, EVENTS]
   >> `random_variable (\x. (Y x, Z x)) p (s2, POW(s2))`
        by (RW_TAC std_ss [random_variable_def]
            >> FULL_SIMP_TAC std_ss [IN_MEASURABLE, random_variable_def, POW_SIGMA_ALGEBRA, IN_FUNSET,
                                     space_def, subsets_def, IN_POW]
            >> CONJ_TAC >- (Q.UNABBREV_TAC `s2` >> RW_TAC std_ss [IN_IMAGE, IN_CROSS] >> METIS_TAC [])
            >> METIS_TAC [SUBSET_DEF, IN_INTER, IN_POW])
   >> (MP_TAC o Q.SPECL [`p`, `s1`, `s2`, `X`, `(\x. (Y x,Z x))`] o
        INST_TYPE [``:'c`` |-> ``:'e#'f``, ``:'b``|->``:'d``]) finite_marginal_product_space_POW2
   >> ASM_SIMP_TAC std_ss []
   >> STRIP_TAC
   >> (MP_TAC o Q.SPEC `(s1 CROSS s2,POW (s1 CROSS s2),joint_distribution p X (\x. (Y x,Z x)))`
        o INST_TYPE [``:'a`` |-> ``:'d # 'e # 'f``]) finite_space_POW_integral_reduce
   >> ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, FINITE_CROSS]
   >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
   >> `FINITE (s1 CROSS s2)`
        by RW_TAC std_ss [FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s1 :'d -> bool)
                        CROSS (s2 :'e # 'f -> bool)`) REAL_SUM_IMAGE_IN_IF]
   >> Suff `(\x.
     (if x IN s1 CROSS s2 then
        (\x.
           logr b
             (RN_deriv
                (s1 CROSS s2,POW (s1 CROSS s2),
                 prob
                   (s1 CROSS s2,POW (s1 CROSS s2),
                    prod_measure (s1,POW s1,distribution p X)
                      (s2,POW s2,distribution p (\x. (Y x,Z x)))))
                (joint_distribution p X (\x. (Y x,Z x))) x) *
           measure
             (s1 CROSS s2,POW (s1 CROSS s2),
              joint_distribution p X (\x. (Y x,Z x))) {x}) x
      else
        0)) =
        (\x.
     (if x IN s1 CROSS s2 then
        (\(x,y,z).
           joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
           logr b
             (joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} /
              (distribution p X {x} *
               distribution p (\x. (Y x,Z x)) {(y,z)}))) x
      else
        0))`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [FUN_EQ_THM]
   >> RW_TAC std_ss [PROB, measure_def]
   >> `x = (FST x, FST(SND x), SND(SND x))` by RW_TAC std_ss [PAIR]
   >> POP_ORW
   >> RW_TAC std_ss []
   >> Cases_on `joint_distribution p X (\x. (Y x,Z x)) {x} = 0`
   >- RW_TAC real_ss []
   >> RW_TAC std_ss [REAL_MUL_COMM, REAL_EQ_LMUL]
   >> Suff `(RN_deriv
     (s1 CROSS s2,POW (s1 CROSS s2),
      prod_measure (s1,POW s1,distribution p X)
        (s2,POW s2,distribution p (\x. (Y x,Z x))))
     (joint_distribution p X (\x. (Y x,Z x))) x) =
        (joint_distribution p X (\x. (Y x,Z x)) {x} /
   (distribution p X {FST x} * distribution p (\x. (Y x,Z x)) {SND x}))`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [RN_deriv_def]
   >> Suff `(\f. f x = joint_distribution p X (\x. (Y x,Z x)) {x} /
(distribution p X {FST x} * distribution p (\x. (Y x,Z x)) {SND x}))
        (@f.
   measure_space
     (s1 CROSS s2,POW (s1 CROSS s2),
      prod_measure (s1,POW s1,distribution p X)
        (s2,POW s2,distribution p (\x. (Y x,Z x)))) /\
   measure_space
     (m_space
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p (\x. (Y x,Z x)))),
      measurable_sets
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p (\x. (Y x,Z x)))),
      joint_distribution p X (\x. (Y x,Z x))) /\
   f IN
   borel_measurable
     (m_space
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p (\x. (Y x,Z x)))),
      measurable_sets
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p (\x. (Y x,Z x))))) /\
   !a.
     a IN
     measurable_sets
       (s1 CROSS s2,POW (s1 CROSS s2),
        prod_measure (s1,POW s1,distribution p X)
          (s2,POW s2,distribution p (\x. (Y x,Z x)))) ==>
     (integral
        (s1 CROSS s2,POW (s1 CROSS s2),
         prod_measure (s1,POW s1,distribution p X)
           (s2,POW s2,distribution p (\x. (Y x,Z x))))
        (\x. f x * indicator_fn a x) =
      joint_distribution p X (\x. (Y x,Z x)) a))`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC SELECT_ELIM_THM
   >> `measure_space (s1 CROSS s2, POW (s1 CROSS s2),
                   prod_measure (s1,POW s1,distribution p X)
          (s2,POW s2,distribution p (\x. (Y x,Z x))))`
        by METIS_TAC [measurable_sets_def, distribution_prob_space, space_def, subsets_def, m_space_def,
                      prob_space_def, measure_space_finite_prod_measure_POW2,
                      POW_SIGMA_ALGEBRA]
   >> RW_TAC std_ss [measurable_sets_def, m_space_def]
   >- (Q.EXISTS_TAC `\x'. joint_distribution p X (\x. (Y x,Z x)) {x'} /
                        ((distribution p X {FST x'})*(distribution p (\x. (Y x,Z x)) {SND x'}))`
       >> STRONG_CONJ_TAC
       >- (`(s1 CROSS s2,POW (s1 CROSS s2)) =
            (m_space (s1 CROSS s2,POW (s1 CROSS s2),
          prod_measure (s1,POW s1,distribution p X)
            (s2,POW s2,distribution p (\x. (Y x,Z x)))),
             measurable_sets (s1 CROSS s2,POW (s1 CROSS s2),
          prod_measure (s1,POW s1,distribution p X)
            (s2,POW s2,distribution p (\x. (Y x,Z x)))))` by RW_TAC std_ss [measurable_sets_def, m_space_def]
            >> POP_ORW
            >> ASM_SIMP_TAC std_ss [borel_measurable_le_iff, IN_POW, SUBSET_DEF, GSPECIFICATION, measurable_sets_def, m_space_def])
       >> RW_TAC std_ss [IN_POW]
       >> (MP_TAC o Q.SPEC `(s1 CROSS s2,POW (s1 CROSS s2),
          prod_measure (s1,POW s1,distribution p X)
            (s2,POW s2,distribution p (\x. (Y x,Z x))))`
        o INST_TYPE [``:'a`` |-> ``:'d # 'e # 'f``]) finite_space_POW_integral_reduce
       >> ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, FINITE_CROSS, measure_def]
       >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
       >> `(s1 CROSS s2) =
        a UNION ((s1 CROSS s2) DIFF a)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF] >> METIS_TAC [SUBSET_DEF])
        >> POP_ORW
        >> `DISJOINT a ((s1 CROSS s2) DIFF a)`
                by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
        >> `FINITE a` by METIS_TAC [SUBSET_FINITE, FINITE_CROSS, IMAGE_FINITE]
        >> RW_TAC std_ss [FINITE_DIFF, REAL_SUM_IMAGE_DISJOINT_UNION]
        >> `FINITE ((s1 CROSS s2) DIFF a)`
                by RW_TAC std_ss [FINITE_DIFF]
        >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `((s1 :'d -> bool) CROSS (s2 :'e # 'f -> bool)) DIFF a`) REAL_SUM_IMAGE_IN_IF]
        >> `(\x. (if x IN s1 CROSS s2 DIFF a then (\x'.
           joint_distribution p X (\x. (Y x,Z x)) {x'} /
           (distribution p X {FST x'} *
            distribution p (\x. (Y x,Z x)) {SND x'}) *
           indicator_fn a x' *
           prod_measure (s1,POW s1,distribution p X)
             (s2,POW s2,distribution p (\x. (Y x,Z x))) {x'}) x else 0)) = (\x. 0)`
                by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DIFF, indicator_fn_def])
        >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
        >> POP_ASSUM (K ALL_TAC)
        >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(a :'d # 'e # 'f -> bool)`) REAL_SUM_IMAGE_IN_IF]
        >> `(\x. (if x IN a then (\x'.
           joint_distribution p X (\x. (Y x,Z x)) {x'} /
           (distribution p X {FST x'} *
            distribution p (\x. (Y x,Z x)) {SND x'}) *
           indicator_fn a x' *
           prod_measure (s1,POW s1,distribution p X)
             (s2,POW s2,distribution p (\x. (Y x,Z x))) {x'}) x else 0)) =
            (\x. if x IN a then
                (\x. joint_distribution p X (\x. (Y x,Z x)) {x}) x else 0)`
                by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [indicator_fn_def]
                    >> `{x'} = {FST x'} CROSS {SND x'}`
                        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_SING, IN_CROSS]
                            >> (MP_TAC o Q.ISPEC `(x'' :'d # 'e # 'f)`) pair_CASES
                            >> (MP_TAC o Q.ISPEC `(x' :'d # 'e # 'f)`) pair_CASES
                            >> RW_TAC std_ss [])
                    >> POP_ORW
                    >> `prod_measure (s1,POW s1,distribution p X) (s2,POW s2,distribution p (\x. (Y x,Z x)))
                        ({FST x'} CROSS {SND x'}) =
                        measure (s1,POW s1,distribution p X) {FST x'} *
                        measure (s2,POW s2,distribution p (\x. (Y x,Z x))) {SND x'}`
                        by (`measure_space (s1,POW s1,distribution p X) /\
                             measure_space (s2,POW s2,distribution p (\x. (Y x,Z x)))`
                                by METIS_TAC [distribution_prob_space,
                                              prob_space_def, space_def, subsets_def,
                                              POW_SIGMA_ALGEBRA]
                            >> `{FST x'} IN measurable_sets (s1,POW s1,distribution p X) /\
                                {SND x'} IN measurable_sets (s2,POW s2,distribution p (\x. (Y x,Z x)))`
                                by (RW_TAC std_ss [measurable_sets_def, IN_POW, SUBSET_DEF, IN_SING]
                                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_CROSS])
                            >> METIS_TAC [finite_POW_prod_measure_reduce, m_space_def, measurable_sets_def])
                    >> POP_ORW
                    >> RW_TAC std_ss [measure_def]
                    >> Cases_on `(distribution p X {FST x'} * distribution p (\x. (Y x,Z x)) {SND x'}) = 0`
                    >- (Suff `joint_distribution p X (\x. (Y x,Z x)) ({FST x'} CROSS {SND x'}) = 0`
                        >- RW_TAC real_ss []
                        >> `PREIMAGE X {FST x'} INTER p_space p IN events p`
                                by (Q.UNABBREV_TAC `s1`
                                    >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, space_def, subsets_def,
                                                          IN_POW]
                                    >> Suff `{FST x'} SUBSET IMAGE X (p_space p)` >- METIS_TAC []
                                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_CROSS])
                        >> `PREIMAGE (\x. (Y x,Z x)) {SND x'} INTER p_space p IN events p`
                                by (Q.UNABBREV_TAC `s2`
                                    >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, space_def, subsets_def,
                                                          IN_POW]
                                    >> Suff `{SND x'} SUBSET IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)` >- METIS_TAC []
                                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_CROSS])
                        >> `(PREIMAGE X {FST x'} INTER PREIMAGE (\x. (Y x,Z x)) {SND x'} INTER p_space p) IN events p`
                                by (`PREIMAGE X {FST x'} INTER PREIMAGE (\x. (Y x,Z x)) {SND x'} INTER p_space p =
                                    (PREIMAGE X {FST x'} INTER p_space p) INTER
                                    (PREIMAGE (\x. (Y x,Z x)) {SND x'} INTER p_space p)`
                                        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER] >> DECIDE_TAC)
                                    >> POP_ORW
                                    >> FULL_SIMP_TAC std_ss [random_variable_def, prob_space_def, measure_space_def,
                                                             events_def]
                                    >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, space_def, subsets_def])
                        >> FULL_SIMP_TAC std_ss [REAL_ENTIRE, distribution_def, joint_distribution_def]
                        >- (`(PREIMAGE (\x. (X x,Y x,Z x)) ({FST x'} CROSS {SND x'}) INTER p_space p) =
                            (PREIMAGE X {FST x'} INTER PREIMAGE (\x. (Y x,Z x)) {SND x'} INTER p_space p)`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_CROSS, IN_SING])
                            >> POP_ORW
                            >> RW_TAC std_ss [GSYM REAL_LE_ANTISYM]
                            >- (Suff `(PREIMAGE X {FST x'} INTER PREIMAGE (\x. (Y x,Z x)) {SND x'} INTER p_space p) SUBSET
                                      (PREIMAGE X {FST x'} INTER p_space p)`
                                >- METIS_TAC [REAL_LE_TRANS, REAL_LE_REFL, PROB_INCREASING, random_variable_def]
                                >> RW_TAC std_ss [SUBSET_DEF, IN_INTER])
                            >> METIS_TAC [random_variable_def, PROB_POSITIVE])
                        >> `(PREIMAGE (\x. (X x,Y x,Z x)) ({FST x'} CROSS {SND x'}) INTER p_space p) =
                            (PREIMAGE X {FST x'} INTER PREIMAGE (\x. (Y x,Z x)) {SND x'} INTER p_space p)`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_CROSS, IN_SING])
                        >> POP_ORW
                        >> RW_TAC std_ss [GSYM REAL_LE_ANTISYM]
                        >- (Suff `(PREIMAGE X {FST x'} INTER PREIMAGE (\x. (Y x,Z x)) {SND x'} INTER p_space p) SUBSET
                                  (PREIMAGE (\x. (Y x,Z x)) {SND x'} INTER p_space p)`
                            >- METIS_TAC [REAL_LE_TRANS, REAL_LE_REFL, PROB_INCREASING, random_variable_def]
                            >> RW_TAC std_ss [SUBSET_DEF, IN_INTER])
                        >> METIS_TAC [random_variable_def, PROB_POSITIVE])
                    >> RW_TAC std_ss [real_div, measure_def]
                    >> `joint_distribution p X (\x. (Y x,Z x)) ({FST x'} CROSS {SND x'}) *
                        inv (distribution p X {FST x'} * distribution p (\x. (Y x,Z x)) {SND x'}) *
                        (distribution p X {FST x'} * distribution p (\x. (Y x,Z x)) {SND x'}) =
                        (inv (distribution p X {FST x'} * distribution p (\x. (Y x,Z x)) {SND x'}) *
                        (distribution p X {FST x'} * distribution p (\x. (Y x,Z x)) {SND x'})) *
                        joint_distribution p X (\x. (Y x,Z x)) ({FST x'} CROSS {SND x'})`
                        by REAL_ARITH_TAC
                    >> POP_ORW
                    >> RW_TAC real_ss [REAL_MUL_LINV])
        >> POP_ORW
        >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
        >> Q.PAT_X_ASSUM `a SUBSET s1 CROSS s2` MP_TAC
        >> CONV_TAC (UNBETA_CONV ``(a :'d # 'e # 'f -> bool)``)
        >> Q.PAT_X_ASSUM `FINITE a` MP_TAC
        >> Q.SPEC_TAC (`a`,`a`)
        >> MATCH_MP_TAC FINITE_INDUCT
        >> FULL_SIMP_TAC std_ss [random_variable_def]
        >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, PREIMAGE_EMPTY, INTER_EMPTY, PROB_EMPTY, DELETE_NON_ELEMENT,
                          joint_distribution_def]
        >> `(PREIMAGE (\x. (X x,Y x,Z x)) (e INSERT s) INTER p_space p) =
            (PREIMAGE (\x. (X x,Y x,Z x)) {e} INTER p_space p) UNION
            (PREIMAGE (\x. (X x,Y x,Z x)) s INTER p_space p)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_INTER, IN_PREIMAGE, IN_INSERT, NOT_IN_EMPTY]
                    >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, SUBSET_DEF, IN_INSERT, IN_CROSS, IN_IMAGE]
                    >> METIS_TAC [FST, SND])
        >> POP_ORW
        >> `DISJOINT (PREIMAGE (\x. (X x,Y x,Z x)) {e} INTER p_space p)
                     (PREIMAGE (\x. (X x,Y x,Z x)) s INTER p_space p)`
                by (RW_TAC std_ss [IN_DISJOINT, IN_INTER, IN_PREIMAGE, IN_SING]
                    >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
                    >> METIS_TAC [])
        >> `prob p (PREIMAGE (\x. (X x,Y x,Z x)) {e} INTER p_space p UNION
                    PREIMAGE (\x. (X x,Y x,Z x)) s INTER p_space p) =
            prob p (PREIMAGE (\x. (X x,Y x,Z x)) {e} INTER p_space p) +
            prob p (PREIMAGE (\x. (X x,Y x,Z x)) s INTER p_space p)`
                by (MATCH_MP_TAC PROB_ADDITIVE
                    >> RW_TAC std_ss []
                    >> METIS_TAC [SUBSET_DEF, IN_INTER, IN_POW])
        >> POP_ORW
        >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT])
   >> POP_ASSUM (MP_TAC o Q.SPEC `{x}`)
   >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_SING, finite_space_POW_integral_reduce,
                     FINITE_CROSS, IMAGE_FINITE, measurable_sets_def, m_space_def,
                     measure_def]
   >> POP_ASSUM MP_TAC
   >> `(s1 CROSS s2) =
        x INSERT ((s1 CROSS s2) DELETE x)`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INSERT, IN_DELETE] >> METIS_TAC [])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_THM, FINITE_CROSS, FINITE_DELETE, DELETE_DELETE]
   >> `FINITE (s1 CROSS s2 DELETE x)`
        by RW_TAC std_ss [FINITE_DELETE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `((s1 :'d -> bool) CROSS
                        (s2 :'e # 'f -> bool) DELETE (x :'d # 'e # 'f))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x''.
      (if x'' IN s1 CROSS s2 DELETE x then
         (\x''.
            x' x'' * indicator_fn {x} x'' *
            prod_measure (s1,POW s1,distribution p X)
              (s2,POW s2,distribution p (\x. (Y x,Z x))) {x''}) x''
       else
         0)) = (\x'. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [indicator_fn_def, IN_SING, IN_DELETE])
   >> POP_ORW
   >> ASM_SIMP_TAC real_ss [REAL_SUM_IMAGE_0, indicator_fn_def, IN_SING]
   >> `{(x :'d # 'e # 'f)} = {FST x} CROSS {SND x}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_SING, IN_CROSS]
                            >> (MP_TAC o Q.ISPEC `(x'' :'d # 'e # 'f)`) pair_CASES
                            >> (MP_TAC o Q.ISPEC `(x :'d # 'e # 'f)`) pair_CASES
                            >> RW_TAC std_ss [])
   >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> `prod_measure (s1,POW s1,distribution p X) (s2,POW s2,distribution p (\x. (Y x,Z x)))
                        ({FST x} CROSS {SND x}) =
                        measure (s1,POW s1,distribution p X) {FST x} *
                        measure (s2,POW s2,distribution p (\x. (Y x,Z x))) {SND x}`
                        by (`measure_space (s1,POW s1,distribution p X) /\
                             measure_space (s2,POW s2,distribution p (\x. (Y x,Z x)))`
                                by METIS_TAC [distribution_prob_space, POW_SIGMA_ALGEBRA,
                                              prob_space_def, space_def, subsets_def]
                            >> `{FST x} IN measurable_sets (s1,POW s1,distribution p X) /\
                                {SND x} IN measurable_sets (s2,POW s2,distribution p (\x. (Y x,Z x)))`
                                by (RW_TAC std_ss [measurable_sets_def, IN_POW, SUBSET_DEF, IN_SING]
                                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_CROSS])
                            >> METIS_TAC [finite_POW_prod_measure_reduce, m_space_def, measurable_sets_def])
   >> POP_ORW
   >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR]
   >> POP_ORW
   >> FULL_SIMP_TAC std_ss [measure_def, joint_distribution_def, distribution_def]
   >> `PREIMAGE (\x. (X x,Y x,Z x)) ({FST x} CROSS {SND x}) INTER
        p_space p =
        PREIMAGE X {FST x} INTER PREIMAGE (\x. (Y x,Z x)) {SND x} INTER p_space p`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, IN_CROSS])
   >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> POP_ORW
   >> Suff `0 < (prob p (PREIMAGE X {FST x} INTER p_space p) *
            prob p (PREIMAGE (\x. (Y x,Z x)) {SND x} INTER p_space p))`
   >- RW_TAC real_ss [REAL_EQ_RDIV_EQ]
   >> MATCH_MP_TAC REAL_LT_MUL
   >> SIMP_TAC std_ss [REAL_LT_LE]
   >> `PREIMAGE X {FST x} INTER p_space p IN events p`
                by (Q.UNABBREV_TAC `s1`
                    >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, space_def, subsets_def,
                                                          IN_POW]
                    >> Suff `{FST x} SUBSET IMAGE X (p_space p)` >- METIS_TAC []
                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_CROSS])
   >> `PREIMAGE (\x. (Y x,Z x)) {SND x} INTER p_space p IN events p`
                                by (Q.UNABBREV_TAC `s2`
                                    >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, space_def, subsets_def,
                                                          IN_POW]
                                    >> Suff `{SND x} SUBSET IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)` >- METIS_TAC []
                                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_CROSS])
   >> `(PREIMAGE X {FST x} INTER PREIMAGE (\x. (Y x,Z x)) {SND x} INTER p_space p) IN events p`
                                by (`PREIMAGE X {FST x} INTER PREIMAGE (\x. (Y x,Z x)) {SND x} INTER p_space p =
                                    (PREIMAGE X {FST x} INTER p_space p) INTER
                                    (PREIMAGE (\x. (Y x,Z x)) {SND x} INTER p_space p)`
                                        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER] >> DECIDE_TAC)
                                    >> POP_ORW
                                    >> FULL_SIMP_TAC std_ss [random_variable_def, prob_space_def, measure_space_def,
                                                             events_def]
                                    >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, space_def, subsets_def])
    >> Suff `~(0 = prob p (PREIMAGE X {FST x} INTER p_space p)) /\
                     ~(0 = prob p (PREIMAGE (\x. (Y x,Z x)) {SND x} INTER p_space p))`
    >- METIS_TAC [random_variable_def, PROB_POSITIVE]
    >> `0 <= prob p
              (PREIMAGE X {FST x} INTER PREIMAGE (\x. (Y x,Z x)) {SND x} INTER
               p_space p)`
                by METIS_TAC [random_variable_def, PROB_POSITIVE]
    >> (CONJ_TAC >> SPOSE_NOT_THEN STRIP_ASSUME_TAC)
    >- (Suff `prob p (PREIMAGE (X :'a -> 'd) {FST x} INTER PREIMAGE ((\x. (Y x,Z x)) :'a -> 'e # 'f) {SND x} INTER p_space p) <=
              prob p (PREIMAGE (X :'a -> 'd) {FST x} INTER p_space p)`
                >- METIS_TAC [REAL_LE_ANTISYM]
                >> MATCH_MP_TAC PROB_INCREASING
                >> FULL_SIMP_TAC std_ss [random_variable_def, SUBSET_DEF, IN_INTER])
    >> Suff `prob p (PREIMAGE X {FST x} INTER PREIMAGE (\x. (Y x,Z x)) {SND x} INTER p_space p) <=
                      prob p (PREIMAGE (\x. (Y x,Z x)) {SND x} INTER p_space p)`
    >- METIS_TAC [REAL_LE_ANTISYM]
    >> MATCH_MP_TAC PROB_INCREASING
    >> FULL_SIMP_TAC std_ss [random_variable_def, SUBSET_DEF, IN_INTER]
QED

(* NOTE: added ‘prob_space p’ into antecedents due to changes of ‘measurable’ *)
Theorem finite_conditional_mutual_information_reduce :
    !b p X Y Z. prob_space p /\ (POW (p_space p) = events p) /\
               random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p))) /\
               random_variable Y p (IMAGE Y (p_space p), POW (IMAGE Y (p_space p))) /\
               random_variable Z p (IMAGE Z (p_space p), POW (IMAGE Z (p_space p))) /\
               FINITE (p_space p) ==>
        (conditional_mutual_information b p (IMAGE X (p_space p), POW (IMAGE X (p_space p)))
                                            (IMAGE Y (p_space p), POW (IMAGE Y (p_space p)))
                                            (IMAGE Z (p_space p), POW (IMAGE Z (p_space p)))
                                             X Y Z =
        ~ SIGMA (\(x,z). joint_distribution p X Z {(x,z)} *
                         logr b (joint_distribution p X Z {(x,z)} / distribution p Z {z}))
                (IMAGE X (p_space p) CROSS IMAGE Z (p_space p))
        -
        ~ SIGMA (\(x,(y,z)). joint_distribution p X (\x. (Y x, Z x)) {(x,(y,z))} *
                           logr b (joint_distribution p X (\x. (Y x, Z x)) {(x,(y,z))}/
                                   distribution p (\x. (Y x, Z x)) {(y,z)}))
                ((IMAGE X (p_space p)) CROSS (IMAGE (\x. (Y x, Z x)) (p_space p))))
Proof
   REPEAT STRIP_TAC
   >> `random_variable (\x. (Y x, Z x)) p (IMAGE (\x. (Y x, Z x)) (p_space p), POW (IMAGE (\x. (Y x, Z x)) (p_space p)))`
        by (RW_TAC std_ss [random_variable_def]
            >> FULL_SIMP_TAC std_ss [IN_MEASURABLE, random_variable_def, POW_SIGMA_ALGEBRA, IN_FUNSET, space_def,
                                     subsets_def, IN_POW]
            >> CONJ_TAC >- (RW_TAC std_ss [IN_IMAGE] >> METIS_TAC [])
            >> METIS_TAC [SUBSET_DEF, IN_INTER, IN_POW])
   >> RW_TAC std_ss [conditional_mutual_information_def, finite_mutual_information_reduce, space_def, subsets_def]
   >> Know `prod_space =
       ((IMAGE Y (p_space p)) CROSS (IMAGE Z (p_space p)), POW ((IMAGE Y (p_space p)) CROSS (IMAGE Z (p_space p))),
        prod_measure (IMAGE Y (p_space p), POW (IMAGE Y (p_space p)), distribution p Y)
                     (IMAGE Z (p_space p), POW (IMAGE Z (p_space p)), distribution p Z))`
   >- ( Q.UNABBREV_TAC `prod_space`
        >> Q.ABBREV_TAC `s1 = IMAGE Y (p_space p)` >> Q.ABBREV_TAC `s2 = IMAGE Z (p_space p)`
        >> RW_TAC std_ss [prod_measure_space_def, m_space_def, subsets_def, EXTENSION, subsets_def,
                          sigma_def, prod_sets_def, IN_POW, IN_BIGINTER, measurable_sets_def,
                          SUBSET_DEF, IN_CROSS, GSPECIFICATION]
        >> RW_TAC std_ss [GSYM EXTENSION]
        >> EQ_TAC
        >- (ASM_SIMP_TAC std_ss [] >> STRIP_TAC
            >> Q.PAT_X_ASSUM `!s. Q ==> x IN P` (MP_TAC o Q.SPEC `POW (s1 CROSS s2)`)

            >> ASM_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS, POW_SIGMA_ALGEBRA]
            >> STRIP_TAC >> POP_ASSUM MATCH_MP_TAC
            >> NTAC 2 STRIP_TAC >> POP_ASSUM MP_TAC
            >> `(x' :('c -> bool) # ('d -> bool)) = (FST x', SND x')` by RW_TAC std_ss [PAIR]
            >> POP_ORW >> RW_TAC std_ss [IN_CROSS] )
        >> RW_TAC std_ss []
        >> `x = BIGUNION (IMAGE (\a. {a}) x)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
        >> POP_ORW
        >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
        >> POP_ASSUM MATCH_MP_TAC
        >> CONJ_TAC
        >- (MATCH_MP_TAC FINITE_COUNTABLE >> MATCH_MP_TAC IMAGE_FINITE
                >> (MP_TAC o Q.ISPEC `(s1 :'c -> bool) CROSS (s2 :'d -> bool)`) SUBSET_FINITE
                >> Q.UNABBREV_TAC `s1` >> Q.UNABBREV_TAC `s2`
                >> RW_TAC std_ss [FINITE_CROSS, IMAGE_FINITE]
                >> POP_ASSUM MATCH_MP_TAC
                >> METIS_TAC [SUBSET_DEF, IN_CROSS])
        >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
        >> Q.PAT_X_ASSUM `!x. Q ==> x IN P` MATCH_MP_TAC
        >> Q.EXISTS_TAC `({FST a}, {SND a})` >> RW_TAC std_ss [PAIR_EQ, IN_SING]
        >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_SING]
        >> METIS_TAC [PAIR_EQ, PAIR, FST, SND])
   >> DISCH_TAC
   >> RW_TAC std_ss [conditional_mutual_information_def, finite_mutual_information_reduce2,
                     PSPACE, EVENTS]
   >> `!a. a INTER p_space p IN events p`
        by METIS_TAC [IN_INTER, IN_POW, SUBSET_DEF]
   >> `!a. 0 <= prob p (a INTER p_space p)`
        by METIS_TAC [random_variable_def, PROB_POSITIVE]
   >> `!a b. (prob p (b INTER p_space p) = 0) ==>
             (prob p (a INTER b INTER p_space p) = 0)`
        by (RW_TAC std_ss [] >> ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
            >> RW_TAC std_ss [] >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [GSYM thm])
            >> MATCH_MP_TAC PROB_INCREASING
            >> FULL_SIMP_TAC std_ss [random_variable_def, SUBSET_DEF, IN_INTER])
   >> `FINITE (IMAGE X (p_space p) CROSS IMAGE Z (p_space p))`
                by RW_TAC std_ss [IMAGE_FINITE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p)
                        CROSS IMAGE (Z :'a -> 'd) (p_space p))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
         (if x IN IMAGE X (p_space p) CROSS IMAGE Z (p_space p) then
            (\(x,y).
               joint_distribution p X Z {(x,y)} *
               logr b
                 (joint_distribution p X Z {(x,y)} / (distribution p X {x} * distribution p Z {y})))
              x
          else
            0)) =
        (\x. if x IN IMAGE X (p_space p) CROSS IMAGE Z (p_space p) then
                (\(x,z). joint_distribution p X Z {(x,z)} * logr b (joint_distribution p X Z {(x,z)} /
                                (distribution p Z {z}))
                       - joint_distribution p X Z {(x,z)} * logr b (distribution p X {x})) x
                else 0)`
        by (RW_TAC std_ss [FUN_EQ_THM, IN_IMAGE, IN_CROSS] >> RW_TAC std_ss []
            >> (MP_TAC o Q.ISPEC `x:'b#'d`) pair_CASES >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss []
            >> RW_TAC std_ss [GSYM REAL_SUB_LDISTRIB]
            >> `joint_distribution p X Z {(X x',Z x'')} /
                (distribution p X {X x'} * distribution p Z {Z x''}) =
                (joint_distribution p X Z {(X x',Z x'')} /
                                (distribution p Z {Z x''})) /
                (distribution p X {X x'})`
                by (RW_TAC std_ss [real_div]
                    >> Cases_on `distribution p X {X x'} = 0`
                    >- (FULL_SIMP_TAC real_ss [joint_distribution_def, distribution_def]
                        >> `PREIMAGE (\x. (X x,Z x)) {(X x',Z x'')} INTER p_space p =
                            PREIMAGE X {X x'} INTER PREIMAGE Z {Z x''} INTER p_space p`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING])
                        >> POP_ORW
                        >> `PREIMAGE X {X x'} INTER PREIMAGE Z {Z x''} INTER p_space p =
                            PREIMAGE Z {Z x''} INTER PREIMAGE X {X x'} INTER p_space p`
                                by METIS_TAC [INTER_ASSOC, INTER_COMM]
                        >> POP_ORW
                        >> RW_TAC real_ss [])
                    >> Cases_on `distribution p Z {Z x''} = 0`
                    >- (FULL_SIMP_TAC real_ss [joint_distribution_def, distribution_def]
                        >> `PREIMAGE (\x. (X x,Z x)) {(X x',Z x'')} INTER p_space p =
                            PREIMAGE X {X x'} INTER PREIMAGE Z {Z x''} INTER p_space p`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING])
                        >> ASM_SIMP_TAC real_ss [])
                    >> RW_TAC real_ss [REAL_INV_MUL]
                    >> REAL_ARITH_TAC)
            >> POP_ORW
            >> Cases_on `distribution p X {X x'} = 0`
            >- (FULL_SIMP_TAC real_ss [joint_distribution_def, distribution_def]
                >> `PREIMAGE (\x. (X x,Z x)) {(X x',Z x'')} INTER p_space p =
                            PREIMAGE X {X x'} INTER PREIMAGE Z {Z x''} INTER p_space p`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING])
                >> POP_ORW
                >> `PREIMAGE X {X x'} INTER PREIMAGE Z {Z x''} INTER p_space p =
                    PREIMAGE Z {Z x''} INTER PREIMAGE X {X x'} INTER p_space p`
                        by METIS_TAC [INTER_ASSOC, INTER_COMM]
                >> POP_ORW
                >> RW_TAC real_ss [])
            >> Cases_on `joint_distribution p X Z {(X x',Z x'')} / distribution p Z {Z x''} = 0`
            >- (FULL_SIMP_TAC real_ss [joint_distribution_def, distribution_def]
                >> `PREIMAGE (\x. (X x,Z x)) {(X x',Z x'')} INTER p_space p =
                            PREIMAGE X {X x'} INTER PREIMAGE Z {Z x''} INTER p_space p`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING])
                >> FULL_SIMP_TAC std_ss []
                >> Cases_on `prob p (PREIMAGE Z {Z x''} INTER p_space p) = 0`
                >- RW_TAC real_ss []
                >> `0 < prob p (PREIMAGE Z {Z x''} INTER p_space p)`
                        by METIS_TAC [REAL_LT_LE]
                >> FULL_SIMP_TAC real_ss [REAL_EQ_LDIV_EQ])
            >> `0 < distribution p X {X x'}`
                by RW_TAC std_ss [distribution_def, REAL_LT_LE]
            >> `0 < joint_distribution p X Z {(X x',Z x'')} / distribution p Z {Z x''}`
                by RW_TAC std_ss [REAL_LT_LE, joint_distribution_def, distribution_def, REAL_LE_DIV]
            >> RW_TAC std_ss [logr_div])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> RW_TAC std_ss [REAL_SUB_RNEG]
   >> `!x y. ~ x + y = y - x`
        by REAL_ARITH_TAC
   >> POP_ORW
   >> `SIGMA
      (\x.
         (\(x,z).
            joint_distribution p X Z {(x,z)} *
            logr b (joint_distribution p X Z {(x,z)} / distribution p Z {z}) -
            joint_distribution p X Z {(x,z)} * logr b (distribution p X {x})) x)
      (IMAGE X (p_space p) CROSS IMAGE Z (p_space p)) =
        SIGMA
      (\x.
         (\(x,z).
            joint_distribution p X Z {(x,z)} *
            logr b (joint_distribution p X Z {(x,z)} / distribution p Z {z})) x)
      (IMAGE X (p_space p) CROSS IMAGE Z (p_space p)) -
        SIGMA
      (\x.
         (\(x,z). joint_distribution p X Z {(x,z)} * logr b (distribution p X {x})) x)
      (IMAGE X (p_space p) CROSS IMAGE Z (p_space p))`
        by (RW_TAC std_ss [real_sub]
            >> `(\x. (\(x,z).
                joint_distribution p X Z {(x,z)} *
                logr b (joint_distribution p X Z {(x,z)} / distribution p Z {z}) +
                ~(joint_distribution p X Z {(x,z)} * logr b (distribution p X {x}))) x) =
                (\x. (\(x,z).
                joint_distribution p X Z {(x,z)} *
                logr b (joint_distribution p X Z {(x,z)} / distribution p Z {z})) x +
                (\(x,z). ~(joint_distribution p X Z {(x,z)} * logr b (distribution p X {x}))) x)`
                by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss []
                    >> (MP_TAC o Q.ISPEC `x:'b#'d`) pair_CASES >> RW_TAC std_ss []
                    >> FULL_SIMP_TAC std_ss [])
            >> POP_ORW
            >> RW_TAC std_ss [REAL_SUM_IMAGE_ADD, FINITE_CROSS, IMAGE_FINITE, REAL_EQ_LADD]
            >> `(\x. (\(x,z). ~(joint_distribution p X Z {(x,z)} * logr b (distribution p X {x}))) x) =
                (\x. ~1 * (\(x,z). (joint_distribution p X Z {(x,z)} * logr b (distribution p X {x}))) x)`
                by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss []
                    >> (MP_TAC o Q.ISPEC `x:'b#'d`) pair_CASES >> RW_TAC std_ss []
                    >> FULL_SIMP_TAC real_ss [])
            >> POP_ORW
            >> RW_TAC std_ss [REAL_SUM_IMAGE_CMUL, IMAGE_FINITE, FINITE_CROSS]
            >> RW_TAC real_ss [])
   >> POP_ORW
   >> `!(x:real) y z. x - (y - z) = (x + z) - y`
        by REAL_ARITH_TAC
   >> POP_ORW
   >> Suff `SIGMA
  (\(x,y,z).
     joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
     logr b
       (joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} /
        (distribution p X {x} *
         distribution p (\x. (Y x,Z x)) {(y,z)})))
  (IMAGE X (p_space p) CROSS
   (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p))) +
SIGMA
  (\x.
     (\(x,z).
        joint_distribution p X Z {(x,z)} *
        logr b (distribution p X {x})) x)
  (IMAGE X (p_space p) CROSS IMAGE Z (p_space p)) =
        SIGMA
  (\(x,y,z).
     joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
     logr b
       (joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} /
        distribution p (\x. (Y x,Z x)) {(y,z)}))
  (IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p))`
   >- RW_TAC std_ss []
   >> `FINITE (IMAGE X (p_space p) CROSS IMAGE Z (p_space p))`
        by RW_TAC std_ss [FINITE_CROSS, IMAGE_FINITE]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p)
                        CROSS IMAGE (Z :'a -> 'd) (p_space p))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
         (if x IN IMAGE X (p_space p) CROSS IMAGE Z (p_space p) then
            (\x.
               (\(x,z). joint_distribution p X Z {(x,z)} * logr b (distribution p X {x})) x)
              x
          else
            0)) =
        (\x. if x IN IMAGE X (p_space p) CROSS IMAGE Z (p_space p) then
                (\x. (\(x,z). SIGMA (\y. joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
                                         logr b (distribution p X {x})) (IMAGE Y (p_space p))) x) x else 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss []
            >> (MP_TAC o Q.ISPEC `x:'b#'d`) pair_CASES >> RW_TAC std_ss []
            >> RW_TAC std_ss []
            >> `(\y. joint_distribution p X (\x. (Y x,Z x)) {(q,y,r)} * logr b (distribution p X {q})) =
                (\y. logr b (distribution p X {q}) * (\y. joint_distribution p X (\x. (Y x,Z x)) {(q,y,r)}) y)`
                by RW_TAC std_ss [REAL_MUL_COMM]
            >> POP_ORW
            >> ASM_SIMP_TAC std_ss [IMAGE_FINITE, REAL_SUM_IMAGE_CMUL]
            >> Suff `joint_distribution p X Z {(q,r)} =
                     SIGMA (\y. joint_distribution p X (\x. (Y x,Z x)) {(q,y,r)})
                        (IMAGE Y (p_space p))`
            >- RW_TAC std_ss [REAL_MUL_COMM]
            >> RW_TAC std_ss [joint_distribution_def]
            >> `PREIMAGE (\x. (X x,Z x)) {(q,r)} INTER p_space p =
                            PREIMAGE X {q} INTER PREIMAGE Z {r} INTER p_space p`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING])
            >> POP_ORW
            >> `!y. PREIMAGE (\x. (X x,Y x,Z x)) {(q,y,r)} INTER p_space p =
                            PREIMAGE X {q} INTER PREIMAGE Y {y} INTER PREIMAGE Z {r} INTER p_space p`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING] >> METIS_TAC [])
            >> POP_ORW
            >> `FINITE (IMAGE Y (p_space p))` by RW_TAC std_ss [IMAGE_FINITE]
            >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `IMAGE (Y :'a -> 'c) (p_space p)`) REAL_SUM_IMAGE_IN_IF]
            >> (MP_TAC o Q.ISPECL [`(p :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`,
                                   `\(y:'c). PREIMAGE (Y:'a->'c) {y}`,
                                    `(PREIMAGE (X :'a -> 'b) {(q :'b)} INTER
                                        PREIMAGE (Z :'a -> 'd) {(r :'d)} INTER p_space p)`,
                                   `IMAGE (Y:'a->'c) (p_space p)`]) PROB_REAL_SUM_IMAGE_FN
            >> ASM_SIMP_TAC std_ss [IMAGE_FINITE]
            >> `prob_space p` by FULL_SIMP_TAC std_ss [random_variable_def]
            >> `(!x. x IN IMAGE Y (p_space p) ==>
                        PREIMAGE X {q} INTER PREIMAGE Z {r} INTER p_space p INTER
                        PREIMAGE Y {x} IN events p)`
                by METIS_TAC [INTER_COMM, INTER_ASSOC]
            >> `(!x y. x IN IMAGE Y (p_space p) /\ y IN IMAGE Y (p_space p) /\ ~(x = y) ==>
                DISJOINT (PREIMAGE Y {x}) (PREIMAGE Y {y}))`
                by (RW_TAC std_ss [IN_IMAGE, IN_DISJOINT, IN_PREIMAGE, IN_SING] >> METIS_TAC [])
            >> `(BIGUNION (IMAGE (\y. PREIMAGE Y {y}) (IMAGE Y (p_space p))) INTER p_space p = p_space p)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNIV, IN_BIGUNION, IN_IMAGE, IN_PREIMAGE, IN_SING, IN_INTER]
                    >> EQ_TAC >- RW_TAC std_ss []
                    >> RW_TAC std_ss [] >> Q.EXISTS_TAC `PREIMAGE Y {Y x}`
                    >> RW_TAC std_ss [IN_PREIMAGE, IN_SING] >> METIS_TAC [])
            >> ASM_SIMP_TAC std_ss []
            >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
            >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `IMAGE (Y :'a -> 'c) (p_space p)`) REAL_SUM_IMAGE_IN_IF]
            >> Suff `(\x.
     (if x IN IMAGE Y (p_space p) then
        prob p
          (PREIMAGE X {q} INTER PREIMAGE Z {r} INTER p_space p INTER
           PREIMAGE Y {x})
      else
        0)) =
                     (\x.
     (if x IN IMAGE Y (p_space p) then
        prob p
          (PREIMAGE X {q} INTER PREIMAGE Y {x} INTER
           PREIMAGE Z {r} INTER p_space p)
      else
        0))`
            >- RW_TAC std_ss []
            >> RW_TAC std_ss [FUN_EQ_THM]
            >> RW_TAC std_ss [IN_IMAGE]
            >> Suff `PREIMAGE X {q} INTER PREIMAGE Z {r} INTER p_space p INTER PREIMAGE Y {Y x'} =
                     PREIMAGE X {q} INTER PREIMAGE Y {Y x'} INTER PREIMAGE Z {r} INTER p_space p`
            >- RW_TAC std_ss []
            >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING] >> DECIDE_TAC)
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF, FINITE_CROSS, IMAGE_FINITE]
   >> `(\x.
         (\(x,z).
            SIGMA
              (\y.
                 joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
                 logr b (distribution p X {x})) (IMAGE Y (p_space p))) x) =
        (\x. SIGMA ((\(x,z). (\y.
                 joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
                 logr b (distribution p X {x})) ) x) (IMAGE Y (p_space p)))`
        by (RW_TAC std_ss [FUN_EQ_THM] >> (MP_TAC o Q.ISPEC `x:'b#'d`) pair_CASES >> RW_TAC std_ss []
            >> RW_TAC std_ss [])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_REAL_SUM_IMAGE, FINITE_CROSS, IMAGE_FINITE]
   >> `(IMAGE X (p_space p) CROSS IMAGE Z (p_space p) CROSS
       IMAGE Y (p_space p)) =
        IMAGE (\a. ((FST a, SND(SND a)), FST (SND a)))
                (IMAGE X (p_space p) CROSS (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE, IN_CROSS]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(FST (FST x), (SND x, SND(FST x)))`
                >> RW_TAC std_ss [FST,SND] >> METIS_TAC [PAIR])
            >> RW_TAC std_ss [FST, SND]
            >> RW_TAC std_ss [FST, SND] >> METIS_TAC [])
   >> POP_ORW
   >> `INJ (\a. ((FST a,SND (SND a)),FST (SND a)))
                ((IMAGE X (p_space p) CROSS
          (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p))))
        (IMAGE (\a. ((FST a,SND (SND a)),FST (SND a))) ((IMAGE X (p_space p) CROSS
          (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)))))`
        by (RW_TAC std_ss [INJ_DEF, IN_IMAGE, IN_CROSS] >- METIS_TAC []
            >> METIS_TAC [PAIR, PAIR_EQ])
   >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, IMAGE_FINITE, FINITE_CROSS, o_DEF]
   >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_ADD, FINITE_CROSS, IMAGE_FINITE]
   >> `(IMAGE X (p_space p) CROSS
       (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p))) =
        (IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p)) UNION
        (((IMAGE X (p_space p) CROSS
       (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)))) DIFF
        (IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF, IN_CROSS, IN_IMAGE] >> METIS_TAC [PAIR_EQ, PAIR])
   >> POP_ORW
   >> `DISJOINT (IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p))
                ((IMAGE X (p_space p) CROSS
        (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)) DIFF
        IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p)))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
   >> `SIGMA
      (\a.
     (\(x,y,z).
        joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
        logr b
          (joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} /
           (distribution p X {x} *
            distribution p (\x. (Y x,Z x)) {(y,z)}))) a +
     joint_distribution p X (\x. (Y x,Z x)) {a} *
     logr b (distribution p X {FST a}))
      (IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p) UNION
       (IMAGE X (p_space p) CROSS
        (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)) DIFF
        IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p))) =
        SIGMA (\a.
     (\(x,y,z).
        joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
        logr b
          (joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} /
           (distribution p X {x} *
            distribution p (\x. (Y x,Z x)) {(y,z)}))) a +
     joint_distribution p X (\x. (Y x,Z x)) {a} *
     logr b (distribution p X {FST a})) (IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p)) +
        SIGMA (\a.
     (\(x,y,z).
        joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
        logr b
          (joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} /
           (distribution p X {x} *
            distribution p (\x. (Y x,Z x)) {(y,z)}))) a +
     joint_distribution p X (\x. (Y x,Z x)) {a} *
     logr b (distribution p X {FST a})) ((IMAGE X (p_space p) CROSS
        (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)) DIFF
        IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p)))`
        by (MATCH_MP_TAC REAL_SUM_IMAGE_DISJOINT_UNION
            >> RW_TAC std_ss [FINITE_DIFF, IMAGE_FINITE, FINITE_CROSS])
   >> POP_ORW
   >> `FINITE (IMAGE X (p_space p) CROSS
        (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)) DIFF
        IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p))`
        by RW_TAC std_ss [FINITE_DIFF, FINITE_CROSS, IMAGE_FINITE]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b)
                (p_space
                   (p :
                     ('a -> bool) #
                     (('a -> bool) -> bool) # (('a -> bool) -> real))) CROSS
              (IMAGE (Y :'a -> 'c) (p_space p) CROSS
               IMAGE (Z :'a -> 'd) (p_space p)) DIFF
              IMAGE X (p_space p) CROSS
              IMAGE (\(x :'a). (Y x,Z x)) (p_space p))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
     (if
        x IN
        IMAGE X (p_space p) CROSS
        (IMAGE Y (p_space p) CROSS IMAGE Z (p_space p)) DIFF
        IMAGE X (p_space p) CROSS IMAGE (\x. (Y x,Z x)) (p_space p)
      then
        (\a.
           (\(x,y,z).
              joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
              logr b
                (joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} /
                 (distribution p X {x} *
                  distribution p (\x. (Y x,Z x)) {(y,z)}))) a +
           joint_distribution p X (\x. (Y x,Z x)) {a} *
           logr b (distribution p X {FST a})) x
      else
        0)) = (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM, IN_DIFF, IN_CROSS, IN_IMAGE]
            >> (MP_TAC o Q.ISPEC `(x :'b # 'c # 'd)`) pair_CASES
            >> STRIP_TAC
            >> (MP_TAC o Q.ISPEC `(r :'c # 'd)`) pair_CASES
            >> STRIP_TAC
            >> RW_TAC std_ss [FST, SND, joint_distribution_def]
            >- (`PREIMAGE (\x. (X x,Y x,Z x)) {(X x',Y x'',Z x''')} INTER p_space p = {}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER, IN_PREIMAGE, IN_SING]
                    >> METIS_TAC [])
                >> FULL_SIMP_TAC real_ss [random_variable_def, PROB_EMPTY])
            >> `PREIMAGE (\x. (X x,Y x,Z x)) {(X x',Y x'',Z x''')} INTER p_space p = {}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER, IN_PREIMAGE, IN_SING]
                    >> METIS_TAC [])
            >> FULL_SIMP_TAC real_ss [random_variable_def, PROB_EMPTY])
   >> POP_ORW
   >> RW_TAC real_ss [REAL_SUM_IMAGE_0, FINITE_CROSS, IMAGE_FINITE, FINITE_DIFF]
   >> Suff `(\a.
     (\(x,y,z).
        joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
        logr b
          (joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} /
           (distribution p X {x} *
            distribution p (\x. (Y x,Z x)) {(y,z)}))) a +
     joint_distribution p X (\x. (Y x,Z x)) {a} *
     logr b (distribution p X {FST a})) =
        (\(x,y,z).
     joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} *
     logr b
       (joint_distribution p X (\x. (Y x,Z x)) {(x,y,z)} /
        distribution p (\x. (Y x,Z x)) {(y,z)}))`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [FUN_EQ_THM]
   >> (MP_TAC o Q.ISPEC `(a :'b # 'c # 'd)`) pair_CASES
   >> STRIP_TAC
   >> (MP_TAC o Q.ISPEC `(r :'c # 'd)`) pair_CASES
   >> STRIP_TAC
   >> RW_TAC std_ss [GSYM REAL_ADD_LDISTRIB]
   >> Cases_on `distribution p X {q} = 0`
   >- (FULL_SIMP_TAC real_ss [joint_distribution_def, distribution_def]
       >> `PREIMAGE (\x. (X x,Y x,Z x)) {(q,q',r')} INTER p_space p =
           PREIMAGE X {q} INTER PREIMAGE (\x. (Y x,Z x)) {(q',r')} INTER
                p_space p`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING] >> METIS_TAC [])
       >> FULL_SIMP_TAC std_ss []
       >> `PREIMAGE X {q} INTER PREIMAGE (\x. (Y x,Z x)) {(q',r')} INTER
                p_space p = PREIMAGE (\x. (Y x,Z x)) {(q',r')} INTER PREIMAGE X {q} INTER p_space p`
                by METIS_TAC [INTER_ASSOC, INTER_COMM]
       >> RW_TAC real_ss [])
   >> Cases_on `(joint_distribution p X (\x. (Y x,Z x)) {(q,q',r')} /
        (distribution p X {q} * distribution p (\x. (Y x,Z x)) {(q',r')})) = 0`
   >- (FULL_SIMP_TAC real_ss [joint_distribution_def, distribution_def]
       >> `PREIMAGE (\x. (X x,Y x,Z x)) {(q,q',r')} INTER p_space p =
           PREIMAGE X {q} INTER PREIMAGE (\x. (Y x,Z x)) {(q',r')} INTER
                p_space p`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING] >> METIS_TAC [])
       >> FULL_SIMP_TAC std_ss []
       >> Cases_on `prob p (PREIMAGE (\x. (Y x,Z x)) {(q',r')} INTER p_space p) = 0`
       >- RW_TAC real_ss []
       >> `0 < (prob p (PREIMAGE X {q} INTER p_space p) *
            prob p (PREIMAGE (\x. (Y x,Z x)) {(q',r')} INTER p_space p))`
                by RW_TAC std_ss [REAL_ENTIRE, REAL_LT_LE, REAL_LE_MUL]
       >> FULL_SIMP_TAC real_ss [REAL_EQ_LDIV_EQ])
   >> `0 < distribution p X {q}`
        by RW_TAC std_ss [distribution_def, REAL_LT_LE]
   >> `0 < joint_distribution p X (\x. (Y x,Z x)) {(q,q',r')} /
             (distribution p X {q} * distribution p (\x. (Y x,Z x)) {(q',r')})`
        by RW_TAC std_ss [REAL_LT_LE, REAL_LE_DIV, REAL_LE_MUL, distribution_def, joint_distribution_def]
   >> RW_TAC std_ss [GSYM logr_mul]
   >> Suff `joint_distribution p X (\x. (Y x,Z x)) {(q,q',r')} /
       (distribution p X {q} * distribution p (\x. (Y x,Z x)) {(q',r')}) * distribution p X {q} =
        joint_distribution p X (\x. (Y x,Z x)) {(q,q',r')}/(distribution p (\x. (Y x,Z x)) {(q',r')})`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [real_div]
   >> Cases_on `distribution p X {q} = 0`
   >- FULL_SIMP_TAC real_ss [distribution_def, joint_distribution_def]
   >> Cases_on `distribution p (\x. (Y x,Z x)) {(q',r')} = 0`
   >- (FULL_SIMP_TAC real_ss [distribution_def, joint_distribution_def]
       >> `PREIMAGE (\x. (X x,Y x,Z x)) {(q,q',r')} INTER p_space p =
           PREIMAGE X {q} INTER PREIMAGE (\x. (Y x,Z x)) {(q',r')} INTER
                p_space p`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING] >> METIS_TAC [])
       >> FULL_SIMP_TAC real_ss [])
   >> RW_TAC std_ss [REAL_INV_MUL]
   >> `joint_distribution p X (\x. (Y x,Z x)) {(q,q',r')} *
    (inv (distribution p X {q}) * inv (distribution p (\x. (Y x,Z x)) {(q',r')})) *
    distribution p X {q} =
        (joint_distribution p X (\x. (Y x,Z x)) {(q,q',r')} *
    inv (distribution p (\x. (Y x,Z x)) {(q',r')})) *
        (inv (distribution p X {q}) * distribution p X {q})` by REAL_ARITH_TAC
   >> POP_ORW
   >> RW_TAC real_ss [REAL_MUL_LINV]
QED

(* ************************************************************************* *)

(* -------------Entropy of a RV with a certain event is zero---------------- *)

(* NOTE: added ‘prob_space p’ due to changes of ‘measurable’ *)
Theorem finite_entropy_certainty_eq_0 :
    !b p X. prob_space p /\ (POW (p_space p) = events p) /\
         random_variable X p
           (IMAGE X (p_space p),POW (IMAGE X (p_space p))) /\
         FINITE (p_space p) /\
         (?x. x IN IMAGE X (p_space p) /\ (distribution p X {x} = 1)) ==>
         (entropy b p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) X = 0)
Proof
   RW_TAC std_ss [finite_entropy_reduce]
   >> `FINITE (IMAGE X (p_space p))` by RW_TAC std_ss [IMAGE_FINITE]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `IMAGE (X :'a -> 'b) (p_space p)`) REAL_SUM_IMAGE_IN_IF]
   >> Suff `(\x.
          (if x IN IMAGE X (p_space p) then
             (\x. distribution p X {x} * logr b (distribution p X {x})) x
           else
             0)) = (\x. 0)`
   >- RW_TAC real_ss [REAL_SUM_IMAGE_0, IMAGE_FINITE]
   >> RW_TAC std_ss [FUN_EQ_THM]
   >> RW_TAC std_ss []
   >> Cases_on `x' = x`
   >- RW_TAC real_ss [logr_1]
   >> (MP_TAC o Q.SPECL [`X`,`p`,`x`]) distribution_x_eq_1_imp_distribution_y_eq_0
   >> ASM_SIMP_TAC real_ss [GSPECIFICATION]
QED

(* --------------- upper bound on entropy for a rv ------------------------- *)

Theorem finite_entropy_le_card :
    !b p X. 1 <= b /\ prob_space p /\ (POW (p_space p) = events p) /\
         random_variable X p
           (IMAGE X (p_space p),POW (IMAGE X (p_space p))) /\
         FINITE (p_space p) ==>
        entropy b p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) X <=
        logr b (& (CARD ((IMAGE X (p_space p)) INTER {x| ~(distribution p X {x} = 0)})))
Proof
   RW_TAC std_ss [finite_entropy_reduce]
   >> `!x. ~x = ~1*x` by REAL_ARITH_TAC >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_CMUL, IMAGE_FINITE]
   >> RW_TAC real_ss []
   >> ONCE_REWRITE_TAC [GSYM REAL_MUL_RNEG]
   >> `FINITE (IMAGE X (p_space p))`
        by RW_TAC std_ss [INTER_FINITE, IMAGE_FINITE]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p))`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
         (if x IN IMAGE X (p_space p) then
            (\x. distribution p X {x} * ~logr b (distribution p X {x})) x
          else
            0)) =
        (\x.
         (if x IN IMAGE X (p_space p) then
            (\x. distribution p X {x} * logr b (inv (distribution p X {x}))) x
          else
            0))`
        by (RW_TAC std_ss [FUN_EQ_THM] >> Cases_on `distribution p X {x} = 0` >- RW_TAC real_ss []
            >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, REAL_EQ_LMUL]
            >> MATCH_MP_TAC (GSYM logr_inv)
            >> RW_TAC std_ss [REAL_LT_LE, distribution_def]
            >> MATCH_MP_TAC PROB_POSITIVE
            >> METIS_TAC [random_variable_def, IN_POW, SUBSET_DEF, IN_INTER])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> Q.ABBREV_TAC `P = \x:'b. distribution p (X :'a -> 'b) {x}`
   >> Q.ABBREV_TAC `g = \x:'b. inv (P x)`
   >> `(\x. distribution p X {x} * logr b (inv (distribution p X {x}))) =
        (\x. P x * logr b (g x))`
        by (RW_TAC std_ss [FUN_EQ_THM] >> Q.UNABBREV_TAC `g`
            >> Q.UNABBREV_TAC `P` >> RW_TAC std_ss [])
   >> POP_ORW
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `logr b (SIGMA (\x. P x * g x) (IMAGE X (p_space p)))`
   >> CONJ_TAC
   >- ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p))`)
                jensen_pos_concave_SIGMA
       >> Q.UNABBREV_TAC `g` >> Q.UNABBREV_TAC `P`
       >> `prob_space (IMAGE X (p_space p), POW (IMAGE X (p_space p)), distribution p X)`
                        by METIS_TAC [distribution_prob_space, space_def, subsets_def,
                                      POW_SIGMA_ALGEBRA]
       >> CONJ_TAC
       >- ((MP_TAC o GSYM o Q.ISPECL [`(IMAGE (X :'a -> 'b)
               (p_space
                  (p :
                    ('a -> bool) #
                    (('a -> bool) -> bool) # (('a -> bool) -> real))),
                POW (IMAGE X (p_space p)),distribution p X)`,`IMAGE (X :'a -> 'b) (p_space p)`]) PROB_REAL_SUM_IMAGE
           >> RW_TAC std_ss [EVENTS, IN_POW, SUBSET_REFL, PROB, SUBSET_DEF, IN_SING]
           >> METIS_TAC [PROB_UNIV, PROB, PSPACE])
       >> CONJ_TAC
       >- METIS_TAC [PROB_POSITIVE, EVENTS, IN_POW, SUBSET_DEF, IN_SING, PROB_LE_1, PROB]
       >> RW_TAC std_ss [REAL_INV_POS, pos_concave_logr])
   >> Q.UNABBREV_TAC `g` >> Q.UNABBREV_TAC `P`
   >> Q.ABBREV_TAC `foo = logr b (& (CARD (IMAGE X (p_space p) INTER {x | ~(distribution p X {x} = 0)})))`
   >> `(IMAGE X (p_space p)) = ((IMAGE X (p_space p)) INTER {x| ~(distribution p X {x} = 0)}) UNION
                               ((IMAGE X (p_space p)) DIFF {x| ~(distribution p X {x} = 0)})`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_INTER, IN_DIFF] >> DECIDE_TAC)
   >> POP_ORW
   >> Q.UNABBREV_TAC `foo`
   >> `DISJOINT ((IMAGE X (p_space p)) INTER {x| ~(distribution p X {x} = 0)})
                ((IMAGE X (p_space p)) DIFF {x| ~(distribution p X {x} = 0)})`
        by (RW_TAC std_ss [IN_DISJOINT, IN_INTER, IN_DIFF] >> DECIDE_TAC)
   >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION, IMAGE_FINITE, INTER_FINITE, FINITE_DIFF]
   >> `FINITE (IMAGE X (p_space p) DIFF {x | ~(distribution p X {x} = 0)})`
        by RW_TAC std_ss [FINITE_DIFF, IMAGE_FINITE]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p) DIFF
                                {x | ~(distribution p (X :'a -> 'b) {x} = (0 :real))})`) REAL_SUM_IMAGE_IN_IF]
   >> RW_TAC real_ss [IN_DIFF, GSPECIFICATION, REAL_SUM_IMAGE_0]
   >> `FINITE (IMAGE X (p_space p) INTER {x | ~(distribution p X {x} = 0)})`
        by RW_TAC std_ss [INTER_FINITE, IMAGE_FINITE]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p) INTER
                                {x | ~(distribution p (X :'a -> 'b) {x} = (0 :real))})`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
            (if x IN IMAGE X (p_space p) INTER {x | ~(distribution p X {x} = 0)} then
               (\x. distribution p X {x} * inv (distribution p X {x})) x
             else
               0)) =
        (\x.
            (if x IN IMAGE X (p_space p) INTER {x | ~(distribution p X {x} = 0)} then
               1
             else
               0))`
        by (RW_TAC real_ss [FUN_EQ_THM]
            >> RW_TAC std_ss [IN_INTER, GSPECIFICATION]
            >> MATCH_MP_TAC REAL_MUL_RINV
            >> ASM_REWRITE_TAC [])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_EQ_CARD, REAL_LE_REFL]
QED

(* --------------- entropy is maximal for a uniform rv --------------------- *)

Theorem finite_entropy_uniform_max :
    !b p X. prob_space p /\ (POW (p_space p) = events p) /\
         random_variable X p
           (IMAGE X (p_space p),POW (IMAGE X (p_space p))) /\
         FINITE (p_space p) /\
        (!x y. x IN IMAGE X (p_space p) /\ y IN IMAGE X (p_space p) ==>
                (distribution p X {x} = distribution p X {y})) ==>
        (entropy b p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) X =
         logr b (& (CARD ((IMAGE X (p_space p))))))
Proof
   RW_TAC std_ss [finite_entropy_reduce]
   >> `!x. ~x = ~1*x` by REAL_ARITH_TAC >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_CMUL, IMAGE_FINITE]
   >> RW_TAC real_ss []
   >> ONCE_REWRITE_TAC [GSYM REAL_MUL_RNEG]
   >> `FINITE (IMAGE X (p_space p))` by RW_TAC std_ss [IMAGE_FINITE]
   >> (MP_TAC o Q.SPEC `(\x. distribution p X {x})` o UNDISCH o
        Q.ISPEC `IMAGE (X :'a -> 'b) (p_space p)`)
        REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD
   >> `prob_space (IMAGE X (p_space p), POW (IMAGE X (p_space p)), distribution p X)`
                        by METIS_TAC [distribution_prob_space, space_def, subsets_def,
                                      POW_SIGMA_ALGEBRA]
   >> `(SIGMA (\x. distribution p X {x}) (IMAGE X (p_space p)) = 1)`
        by ((MP_TAC o GSYM o Q.ISPECL [`(IMAGE (X :'a -> 'b)
               (p_space
                  (p :
                    ('a -> bool) #
                    (('a -> bool) -> bool) # (('a -> bool) -> real))),
                POW (IMAGE X (p_space p)),distribution p X)`,
              `IMAGE (X :'a -> 'b) (p_space p)`]) PROB_REAL_SUM_IMAGE
           >> RW_TAC std_ss [EVENTS, IN_POW, SUBSET_REFL, PROB, SUBSET_DEF, IN_SING]
           >> METIS_TAC [PROB_UNIV, PROB, PSPACE])
   >> ASM_SIMP_TAC std_ss []
   >> STRIP_TAC
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p))`) REAL_SUM_IMAGE_IN_IF]
   >> Q.ABBREV_TAC `foo = (& (CARD (IMAGE (X :'a -> 'b) (p_space p))))`
   >> `(\x.
         (if x IN IMAGE X (p_space p) then
            (\x. distribution p X {x} * ~logr b (distribution p X {x})) x
          else
            0)) =
        (\x.
         (if x IN IMAGE X (p_space p) then
            (\x. inv foo * ~logr b (inv foo)) x
          else
            0))`
        by METIS_TAC []
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> (MP_TAC o Q.SPECL [`(\x. inv foo * ~ logr b (inv foo))`,`inv foo * ~ logr b (inv foo)`] o UNDISCH o
        Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p))`) REAL_SUM_IMAGE_FINITE_CONST
   >> RW_TAC std_ss []
   >> POP_ASSUM (K ALL_TAC)
   >> `0 < foo`
        by (Q.UNABBREV_TAC `foo` >> MATCH_MP_TAC REAL_NZ_IMP_LT
            >> RW_TAC std_ss [(UNDISCH o Q.ISPEC `(IMAGE (X :'a -> 'b) (p_space p))`) CARD_EQ_0]
            >> SPOSE_NOT_THEN STRIP_ASSUME_TAC >> FULL_SIMP_TAC real_ss [REAL_SUM_IMAGE_THM])
   >> `~logr b (inv foo) = logr b (inv (inv foo))`
        by (MATCH_MP_TAC neg_logr >> RW_TAC std_ss [REAL_LT_INV_EQ])
   >> POP_ORW
   >> RW_TAC real_ss [REAL_INVINV, REAL_LT_IMP_NE, REAL_MUL_ASSOC, REAL_MUL_RINV]
QED

val _ = export_theory ();
