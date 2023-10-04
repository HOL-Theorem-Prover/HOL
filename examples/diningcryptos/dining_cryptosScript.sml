(* ----------------------------------------------------------------------
    Case Study: The Dining Cryptographers
   ---------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open metisLib arithmeticTheory pred_setTheory pred_setLib
     state_transformerTheory combinTheory pairTheory realTheory realLib jrhUtils
     extra_pred_setTheory realSimps numTheory simpLib seqTheory subtypeTheory
     transcTheory limTheory stringTheory stringSimps real_sigmaTheory
     informationTheory leakageTheory listTheory rich_listTheory listSimps;

open extra_boolTheory extra_numTheory extra_listTheory extra_stringLib
     extra_stringTheory extra_realTheory leakageLib;

open hurdUtils util_probTheory sigma_algebraTheory
     real_measureTheory real_lebesgueTheory real_probabilityTheory;

val _ = new_theory "dining_cryptos";

val _ = temp_set_fixity "CROSS" (Infixl 600)

(* ----------------------------------------------------------------------
    Helpful proof tools
   ---------------------------------------------------------------------- *)

fun disjsafe ss = ss -* ["lift_disj_eq", "lift_imp_disj"]
val arith_ss = disjsafe arith_ss
val bool_ss = disjsafe bool_ss
val list_ss = disjsafe list_ss
val real_ss = disjsafe real_ss
val std_ss = disjsafe std_ss

val Simplify = RW_TAC arith_ss;
val safe_set_ss = bool_ss ++ PRED_SET_ss;
val set_ss = arith_ss ++ PRED_SET_ss;

(* ----------------------------------------------------------------------
    Definitions
   ---------------------------------------------------------------------- *)
val set_announcements_def = Define
   `(set_announcements (high: bool state) (low:bool state)
                       (random:bool state) (n:num) (0:num) (s:string) =
                if (s = (STRCAT "announces" (toString 0))) then
                        ((high (STRCAT "pays" (toString 0)))) xor
                        ((random (STRCAT "coin" (toString 0))) xor
                         (random (STRCAT "coin" (toString n))))
                else low s) /\
    (set_announcements high low random n (SUC i) s =
                if (s = (STRCAT "announces" (toString (SUC i)))) then
                        ((high (STRCAT "pays" (toString (SUC i))))) xor
                        ((random (STRCAT "coin" (toString (SUC i)))) xor
                         (random (STRCAT "coin" (toString i))))
                else (set_announcements high low random n i) s)`;

val XOR_announces_def = Define
  `(XOR_announces (low:bool state) (0:num) = low (STRCAT "announces" (toString 0))) /\
   (XOR_announces low (SUC i) = (low (STRCAT "announces" (toString (SUC i)))) xor
                                (XOR_announces low i))`;

val compute_result_def = Define
   `compute_result (low:bool state) (n:num) (s:string) =
        if (s = "result") then XOR_announces low n else low s`;

val dcprog_def = Define
   `dcprog (SUC(SUC(SUC n))) = (λ((high:bool state, low:bool state), random:bool state).
        compute_result (set_announcements high low random (SUC(SUC n)) (SUC(SUC n)))
                       (SUC(SUC n)))`;

val dc_high_states_set_def = Define
   `(dc_high_states_set (0:num) = {(\s:string. s = (STRCAT "pays" (toString 0)))}) /\
    (dc_high_states_set (SUC n) = (\s:string. s = (STRCAT "pays" (toString (SUC n))))
                                  INSERT (dc_high_states_set n))`;

val dc_high_states_def = Define
   `dc_high_states nsapays (SUC(SUC n)) =
     if nsapays then {(\s: string. s = STRCAT "pays" (toString (SUC(SUC n))))}
     else dc_high_states_set (SUC n)`;

val dc_low_states_def = Define
   `dc_low_states = {(\s:string. F)}`;

val dc_random_states_def = Define
  `(dc_random_states (0:num) = {(\s:string. s = (STRCAT "coin" (toString 0))); (\s:string. F)}) /\
   (dc_random_states (SUC n) = (IMAGE (\s:bool state.
                                        (\x:string. if x = (STRCAT "coin" (toString (SUC n))) then
                                                        T
                                                    else (s x)))
                                       (dc_random_states n))
                                    UNION
                               (IMAGE (\s:bool state.
                                        (\x:string. if x = (STRCAT "coin" (toString (SUC n))) then
                                                        F
                                                    else (s x)))
                                       (dc_random_states n)))`;

val dc_prog_space_def = Define
   `dc_prog_space (SUC(SUC n)) nsapays =
      unif_prog_space
        (dc_high_states nsapays (SUC(SUC n)))
        dc_low_states
        (dc_random_states (SUC n))`;

(* ************************************************************************* *)
(* Case Study: The Dining Cryptographers - Basic Lemmas                      *)
(* ************************************************************************* *)

val set_announcements_alt = store_thm  ("set_announcements_alt",
   ``!high low random n i.
        (set_announcements high low random n 0 =
         (\s. if (s = (STRCAT "announces" (toString 0))) then
                        ((high (STRCAT "pays" (toString 0)))) xor
                        ((random (STRCAT "coin" (toString 0))) xor (random (STRCAT "coin" (toString n))))
                else
                        low s)) /\
        (set_announcements high low random n (SUC i) =
         (\s. if (s = (STRCAT "announces" (toString (SUC i)))) then
                        ((high (STRCAT "pays" (toString (SUC i))))) xor
                        ((random (STRCAT "coin" (toString (SUC i)))) xor (random (STRCAT "coin" (toString i))))
                else
                        (set_announcements high low random n i) s))``,
   RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss [set_announcements_def]);

val compute_result_alt = store_thm  ("compute_result_alt",
   ``!low n. compute_result low n = (\s. if (s = "result") then XOR_announces low n else low s)``,
   RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss [compute_result_def]);

val dc_high_states_set_finite = store_thm  ("dc_high_states_set_finite",
   ``!n. FINITE (dc_high_states_set n)``,
   Induct
   >> FULL_SIMP_TAC safe_set_ss [dc_high_states_set_def]);

val dc_low_states_finite = prove  (``FINITE dc_low_states``,
   RW_TAC set_ss [dc_low_states_def]);

val dc_random_states_finite = prove  (``!n. FINITE (dc_random_states n)``,
   Induct
   >> FULL_SIMP_TAC safe_set_ss [dc_random_states_def]);

val IN_dc_high_states_set = store_thm  ("IN_dc_high_states_set",
   ``!n x. x IN (dc_high_states_set n) <=>
           (?i. i <= n /\ (x = (\s. s = STRCAT "pays" (toString i))))``,
   Induct
   >> RW_TAC set_ss [dc_high_states_set_def]
   >> METIS_TAC [DECIDE ``!(x:num) y. x <= SUC y <=> x <= y \/ (x = SUC y)``, STRCAT_toString_inj]);

val IN_dc_random_states = store_thm
  ("IN_dc_random_states",
   ``!n s. s IN (dc_random_states n) <=>
           !x. ~(?i. i <= n /\ (x = STRCAT "coin" (toString i))) ==> (~(s x))``,
   Induct
   >- (RW_TAC set_ss [dc_random_states_def] >> METIS_TAC [])
   >> RW_TAC set_ss [Once dc_random_states_def]
   >> EQ_TAC
   >- METIS_TAC [DECIDE ``!(i:num) n. i <= n ==> i <= SUC n``, LESS_EQ_REFL]
   >> RW_TAC std_ss []
   >> Cases_on `s (STRCAT "coin" (toString (SUC n)))`
   >- (DISJ1_TAC >> Q.EXISTS_TAC `(\x. if x = STRCAT "coin" (toString (SUC n)) then F else s x)`
       >> RW_TAC std_ss [FUN_EQ_THM] >- METIS_TAC []
       >> METIS_TAC [DECIDE ``!(i:num) n. i <= SUC n <=> ((i = SUC n) \/ i <= n)``])
   >> DISJ2_TAC >> Q.EXISTS_TAC `s`
   >> RW_TAC std_ss [FUN_EQ_THM] >- METIS_TAC []
   >> METIS_TAC [DECIDE ``!(i:num) n. i <= SUC n <=> ((i = SUC n) \/ i <= n)``]);

val dc_high_states_set_not_empty = store_thm
  ("dc_high_states_set_not_empty",
   ``!n. ~((dc_high_states_set n)={})``,
   Induct >> RW_TAC set_ss [dc_high_states_set_def]);

val dc_low_states_not_empty = store_thm
  ("dc_low_states_not_empty",
   ``~(dc_low_states={})``,
   RW_TAC set_ss [dc_low_states_def]);

val coin_out_of_range_eq_zero_dc_random_states = store_thm
  ("coin_out_of_range_eq_zero_dc_random_states",
   ``!n s. s IN (dc_random_states n) ==>
                !i. (n < i) ==> ~ (s (STRCAT "coin" (toString i)))``,
   Induct
   >- (RW_TAC set_ss [dc_random_states_def]
       >> RW_TAC std_ss [STRCAT_toString_inj]
       >> POP_ASSUM MP_TAC >> DECIDE_TAC)
   >> RW_TAC set_ss [dc_random_states_def]
   >> RW_TAC std_ss [STRCAT_toString_inj, DECIDE ``!i:num n. SUC n < i ==> ~(i = SUC n)``,                                        DECIDE ``!i:num n. SUC n < i ==> n < i``]);

val dc_random_states_not_empty = store_thm
  ("dc_random_states_not_empty",
   ``!n. ~((dc_random_states n)={})``,
   Induct >> RW_TAC set_ss [dc_random_states_def]);

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

val dc_states_cross_not_empty = store_thm
  ("dc_states_cross_not_empty",
   ``!n. ~((((dc_high_states_set (SUC(SUC n))) CROSS dc_low_states) CROSS (dc_random_states (SUC(SUC n))))={})``,
   RW_TAC std_ss [CROSS_HLR_NON_EMPTY_IMP, dc_high_states_set_finite, dc_random_states_finite,
                  dc_low_states_finite, dc_high_states_set_not_empty, dc_random_states_not_empty,
                  dc_low_states_not_empty]);

val dc_prog_space_F_set_thm = store_thm
  ("dc_prog_space_F_set_thm",
   ``!n. dc_prog_space (SUC(SUC n)) F =
         unif_prog_space (dc_high_states_set (SUC n))
                         dc_low_states
                         (dc_random_states (SUC n))``,
   RW_TAC std_ss [dc_prog_space_def, dc_high_states_def]);

val dc_prog_space_T_set_thm = store_thm
  ("dc_prog_space_T_set_thm",
   ``!n. dc_prog_space (SUC(SUC n)) T =
         unif_prog_space {(\s:string. s = STRCAT "pays" (toString (SUC(SUC n))))}
                         {(\s:string. F)}
                         (dc_random_states (SUC n))``,
   RW_TAC std_ss [dc_prog_space_def, dc_high_states_def, dc_low_states_def]);

(* ************************************************************************* *)
(* Case Study: The Dining Cryptographers - Computation for 3 cryptos         *)
(* ************************************************************************* *)

val fun_eq_lem = METIS_PROVE [] ``!y z. (!x. (x = y) <=> (x = z)) <=> (y = z)``;

val card_dc_high_states_set3 = store_thm
  ("card_dc_high_states_set3",
   ``& (CARD (dc_high_states_set (SUC (SUC 0)))) = 3``,
   RW_TAC set_ss [dc_high_states_set_def, FUN_EQ_THM, fun_eq_lem, STRCAT_toString_inj]);

val fun_eq_lem5 = METIS_PROVE []
        ``!x a b P Q. (x = a) \/ ~ (x = b) /\ P \/ Q <=> (a = b) /\ ((x = a) \/ P)
                        \/ ~(x = b) /\ ((x = a) \/ P) \/ Q``;

val CARD_dc_set_cross = store_thm
  ("CARD_dc_set_cross",
   ``1 / & (CARD (IMAGE (\s. (FST s,SND s,dcprog (SUC (SUC (SUC 0))) s))
                ((dc_high_states_set (SUC (SUC 0)) CROSS dc_low_states) CROSS
                   dc_random_states (SUC (SUC 0))))) = 1 / 24``,
   RW_TAC set_ss [dcprog_def, dc_low_states_def, dc_high_states_def, dc_high_states_set_def, dc_random_states_def,
                  CROSS_EQNS, compute_result_alt, XOR_announces_def, set_announcements_def, xor_def]
   >> CONV_TAC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV set_ss [fun_eq_lem])))
   >> RW_TAC set_ss [CROSS_EQNS, STRCAT_toString_inj]
   >> CONV_TAC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV set_ss [fun_eq_lem])))
   >> REPEAT (SIMP_TAC std_ss [FINITE_EMPTY, FINITE_INSERT, Once CARD_DEF]
              >> CONV_TAC (FIND_CONV ``x IN y`` (IN_CONV (SIMP_CONV std_ss [FUN_EQ_THM]
                                        THENC SIMP_CONV bool_ss [EQ_IMP_THM]
                                        THENC SIMP_CONV bool_ss [DISJ_IMP_THM]
                                        THENC EVAL
                                        THENC SIMP_CONV bool_ss [LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                        THENC EVAL
                                        THENC SIMP_CONV bool_ss [fun_eq_lem5, GSYM LEFT_AND_OVER_OR]
                                        THENC EVAL
                                        THENC SIMP_CONV bool_ss [FORALL_AND_THM])))
               >> SIMP_TAC std_ss []));

val CARD_dc_high_states_set = store_thm
  ("CARD_dc_high_states_set",
   ``!n. CARD (dc_high_states_set n) = SUC n``,
   Induct >> RW_TAC set_ss [dc_high_states_set_def, dc_high_states_set_finite, CARD_INSERT,
                            IN_dc_high_states_set, FUN_EQ_THM, fun_eq_lem, STRCAT_toString_inj]);

val CARD_DISJOINT_UNION = store_thm
  ("CARD_DISJOINT_UNION",
   ``!P Q. FINITE P /\ FINITE Q /\ DISJOINT P Q ==>
                (CARD (P UNION Q) = CARD P + CARD Q)``,
   REPEAT STRIP_TAC >> ASM_SIMP_TAC std_ss [GSYM CARD_UNION]
   >> Suff `P INTER Q = {}` >> RW_TAC set_ss [] >> ONCE_REWRITE_TAC [EXTENSION]
   >> FULL_SIMP_TAC set_ss [DISJOINT_DEF, EXTENSION]);

val CARD_dc_random_states = store_thm
  ("CARD_dc_random_states",
   ``!n. CARD (dc_random_states n) = 2 ** (SUC n)``,
   Induct >> RW_TAC set_ss [dc_random_states_def, EXP, FUN_EQ_THM]
   >> `DISJOINT (IMAGE (\s x. (x = STRCAT "coin" (toString (SUC n))) \/ s x)
                        (dc_random_states n))
                (IMAGE (\s x. ~(x = STRCAT "coin" (toString (SUC n))) /\ s x)
                        (dc_random_states n))`
        by (RW_TAC std_ss [DISJOINT_DEF]
   >> ONCE_REWRITE_TAC [EXTENSION]
   >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER, IN_IMAGE] >> METIS_TAC [])
   >> RW_TAC std_ss [IMAGE_FINITE, dc_random_states_finite, CARD_DISJOINT_UNION]
   >> Know `CARD (IMAGE (\s x. (x = STRCAT "coin" (toString (SUC n))) \/ s x)
                        (dc_random_states n)) = CARD (dc_random_states n)`
   >- (MATCH_MP_TAC CARD_IMAGE
       >> Q.EXISTS_TAC `(IMAGE (\s x. (x = STRCAT "coin" (toString (SUC n))) \/ s x)
                               (dc_random_states n))`
       >> RW_TAC set_ss [dc_random_states_finite, INJ_DEF, FUN_EQ_THM, fun_eq_lem]
       >- (rename1 `s' IN dc_random_states n` \\
           Q.EXISTS_TAC `s'` >> RW_TAC std_ss [])
       >> METIS_TAC [coin_out_of_range_eq_zero_dc_random_states, DECIDE ``!n:num. n < SUC n``])
   >> DISCH_TAC
   >> Know `CARD (IMAGE (\s x. ~(x = STRCAT "coin" (toString (SUC n))) /\ s x) (dc_random_states n)) =
            CARD (dc_random_states n)`
   >- (MATCH_MP_TAC CARD_IMAGE
       >> Q.EXISTS_TAC `(IMAGE (\s x. ~(x = STRCAT "coin" (toString (SUC n))) /\ s x) (dc_random_states n))`
       >> RW_TAC set_ss [dc_random_states_finite, INJ_DEF, FUN_EQ_THM, fun_eq_lem]
       >- (rename1 `s' IN dc_random_states n` \\
           Q.EXISTS_TAC `s'` >> RW_TAC std_ss [])
       >> METIS_TAC [coin_out_of_range_eq_zero_dc_random_states, DECIDE ``!n:num. n < SUC n``])
   >> DISCH_TAC
   >> RW_TAC arith_ss [EXP]);

val CARD_dc_low_states = store_thm
  ("CARD_dc_low_states",
   ``CARD dc_low_states = 1``,
   RW_TAC set_ss [dc_low_states_def]);

val dc_states3_cross_not_empty = store_thm
  ("dc_states3_cross_not_empty",
   ``~((((dc_high_states_set (SUC(SUC 0))) CROSS dc_low_states) CROSS (dc_random_states (SUC(SUC 0))))={})``,
   ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [dc_high_states_set_def, dc_low_states_def, dc_random_states_def, CROSS_EQNS]
   >> Q.EXISTS_TAC `(((\s. s = STRCAT "pays" (toString 0)),(\s.F)),(\s.F))`
   >> RW_TAC std_ss [FST,SND]);

val fun_eq_lem6 = METIS_PROVE []
  ``!x a b P Q. (x = a) \/ ~ (x = b) /\ P <=>
        (a = b) /\ ((x = a) \/ P) \/ ~(x = b) /\ ((x = a) \/ P)``;

val _ = print "Starting very long dc3_leakage_result (expect 10min)\n"
(* NOTE: this theorem needs a long time (~10min) to finish *)
val dc3_leakage_result = store_thm
  ("dc3_leakage_result",
   ``leakage (dc_prog_space (SUC (SUC (SUC 0))) F) (dcprog (SUC(SUC(SUC 0)))) = 0``,
   RW_TAC bool_ss [dc_prog_space_F_set_thm, unif_prog_space_leakage_computation_reduce,
                   dc_high_states_set_finite, dc_random_states_finite, dc_low_states_finite,
                   dc_states3_cross_not_empty, CARD_dc_high_states_set, CARD_dc_low_states,
                   CARD_dc_random_states]
   >> RW_TAC set_ss [dcprog_def, dc_low_states_def, dc_high_states_def, dc_high_states_set_def,
                     dc_random_states_def, CROSS_EQNS, compute_result_alt, XOR_announces_def,
                     set_announcements_def, xor_def, STRCAT_toString_inj]
   >> CONV_TAC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV set_ss [fun_eq_lem])))
   >> RW_TAC set_ss [CROSS_EQNS, STRCAT_toString_inj]
   >> CONV_TAC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV set_ss [fun_eq_lem])))
   >> CONV_TAC
        (REPEATC ((SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]) THENC
                  ((ONCE_FIND_CONV ``x DELETE y``
                     (DELETE_CONV
                       ((SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND,
                                             EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM])
                        THENC EVAL
                        THENC (SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR,
                                                  FORALL_AND_THM, DISJ_IMP_THM])
                        THENC EVAL
                        THENC (REPEATC (T_F_UNCHANGED_CONV
                                         ((SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR,
                                                              FORALL_AND_THM])
                                          THENC EVAL)))))))
                  THENC SIMP_CONV arith_ss []))
   >> CONV_TAC (ONCE_FIND_CONV ``if (x=y) then (1:real) else 0``
                 (RATOR_CONV (RATOR_CONV (RAND_CONV
        (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
         THENC EVAL
         THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
         THENC EVAL
         THENC (REPEATC (T_F_UNCHANGED_CONV
         (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
         THENC EVAL))))))
                THENC SIMP_CONV bool_ss []))
   >> RW_TAC real_ss [REAL_ADD_ASSOC, GSYM REAL_NEG_ADD, GSYM REAL_ADD_RDISTRIB, REAL_MUL_ASSOC]);

(* ************************************************************************* *)
(* Case Study: The Dining Cryptographers - Updated Computation for 3 cryptos *)
(* ************************************************************************* *)

val hl_dups_lemma = prove
   (``!(s1:string)(s2:string). ((\x. x = s1) = (\x. x = s2)) = (s1=s2)``,
    METIS_TAC []);

val fun_eq_lem6 = METIS_PROVE []
  ``!x a b P Q. (x = a) \/ ~ (x = b) /\ P <=> (a = b) /\ ((x = a) \/ P) \/ ~(x = b) /\ ((x = a) \/ P)``;

val dc_dup_conv =
  SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
  THENC EVAL
  THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
  THENC EVAL
  THENC (REPEATC (T_F_UNCHANGED_CONV
                  (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                   THENC EVAL)));

val dc_hl_dup_conv = SIMP_CONV arith_ss [hl_dups_lemma, STRCAT_toString_inj];

fun dc_input_unroll (remove_dups_conv:Abbrev.term->Abbrev.thm) =
   (REPEATC (SIMP_CONV bool_ss [dc_high_states_set_def, dc_low_states_def, dc_random_states_def,
                                CARD_DEF, FINITE_INSERT, FINITE_EMPTY, FINITE_SING,
                                IMAGE_UNION, IMAGE_IMAGE, combinTheory.o_DEF, IMAGE_INSERT,
                                IMAGE_EMPTY, INSERT_UNION, UNION_EMPTY, IN_UNION]
    THENC (FIND_CONV ``x IN y`` (IN_CONV remove_dups_conv)
           THENC SIMP_CONV bool_ss [])
    THENC SIMP_CONV arith_ss []));

val _ = print "Starting very long new_dc3_leakage_result (expect 10min)\n"
(* NOTE: this theorem needs a long time (~10min) to finish *)
val new_dc3_leakage_result = store_thm
  ("new_dc3_leakage_result",
   ``leakage (dc_prog_space (SUC (SUC (SUC 0))) F) (dcprog (SUC(SUC(SUC 0)))) = 0``,
   CONV_TAC
    (SIMP_CONV bool_ss [dc_prog_space_F_set_thm] THENC
     RATOR_CONV (RAND_CONV (
     LEAKAGE_COMPUTE_CONV (``dc_high_states_set (SUC(SUC 0))``,
                           ``dc_low_states``,``dc_random_states (SUC(SUC 0))``)
      [dc_high_states_set_def, dc_low_states_def, dc_random_states_def]
      [dcprog_def, compute_result_alt, XOR_announces_def, set_announcements_alt, FST, SND, xor_def]
      (dc_input_unroll dc_hl_dup_conv) (dc_input_unroll dc_hl_dup_conv) (dc_input_unroll dc_dup_conv)
       dc_hl_dup_conv dc_hl_dup_conv dc_dup_conv dc_dup_conv))
    THENC SIMP_CONV real_ss [REAL_ADD_ASSOC, GSYM REAL_NEG_ADD,
                             GSYM REAL_ADD_RDISTRIB, REAL_MUL_ASSOC]));

(* ************************************************************************* *)
(* Case Study: The Dining Cryptographers - Proofs                            *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(* Case Study: The Dining Cryptographers - Proofs (Correctness)              *)
(* ************************************************************************* *)

val dc_set_announcements_result1 = store_thm
  ("dc_set_announcements_result1",
   ``!h l r n. !i. i <= (SUC (SUC n)) ==>
                ((set_announcements h l r (SUC (SUC n)) i (STRCAT "announces" (toString 0)) =
                 ((h (STRCAT "pays" (toString 0)))) xor
                 ((r (STRCAT "coin" (toString 0))) xor (r (STRCAT "coin" (toString (SUC (SUC n))))))))``,
   NTAC 4 STRIP_TAC >> Induct
   >> ASM_SIMP_TAC arith_ss [set_announcements_def, STRCAT_toString_inj]);

val dc_set_announcements_result2 = store_thm
  ("dc_set_announcements_result2",
   ``!h l r n. ((set_announcements h l r (SUC (SUC n)) (SUC (SUC n)) (STRCAT "announces" (toString 0)) =
               ((h (STRCAT "pays" (toString 0)))) xor
               ((r (STRCAT "coin" (toString 0))) xor (r (STRCAT "coin" (toString (SUC (SUC n))))))))``,
   ASM_SIMP_TAC arith_ss [dc_set_announcements_result1]);

val dc_set_announcements_result3 = store_thm
  ("dc_set_announcements_result3",
   ``!h l r n m i. (SUC i) <= m /\ m < (SUC (SUC (SUC n))) ==>
                  ((set_announcements h l r (SUC (SUC n)) m) (STRCAT "announces" (toString (SUC i))) =
                   ((h (STRCAT "pays" (toString (SUC i))))) xor
                        ((r (STRCAT "coin" (toString (SUC i)))) xor (r (STRCAT "coin" (toString i)))))``,
   NTAC 4 STRIP_TAC >> Induct
   >- RW_TAC arith_ss []
   >> STRIP_TAC >> Cases_on `i = m`
   >> ASM_SIMP_TAC arith_ss [set_announcements_def, STRCAT_toString_inj]);

val dc_set_announcements_result4 = store_thm
  ("dc_set_announcements_result4",
   ``!h l r n i. (SUC i) < (SUC (SUC (SUC n))) ==>
                  ((set_announcements h l r (SUC (SUC n)) (SUC (SUC n))) (STRCAT "announces" (toString (SUC i))) =
                   ((h (STRCAT "pays" (toString (SUC i))))) xor
                        ((r (STRCAT "coin" (toString (SUC i)))) xor (r (STRCAT "coin" (toString i)))))``,
   ASM_SIMP_TAC arith_ss [dc_set_announcements_result3]);

val dc_set_announcements_result5 = store_thm
  ("dc_set_announcements_result5",
   ``!h l r n m s. m <= SUC (SUC n) /\ (!i. i <= m ==> ~(s = STRCAT "announces" (toString i))) ==>
                 ((set_announcements h l r (SUC (SUC n)) m) s = l s)``,
   NTAC 4 STRIP_TAC >> Induct
   >- (STRIP_TAC >> ASM_SIMP_TAC arith_ss [set_announcements_def, STRCAT_toString_inj])
   >> STRIP_TAC >> ASM_SIMP_TAC arith_ss [set_announcements_def, STRCAT_toString_inj]);

val dc_set_announcements_result6 = store_thm
  ("dc_set_announcements_result6",
   ``!h l r n. ((set_announcements h l r (SUC (SUC n)) (SUC (SUC n))) (STRCAT "announces" (toString (SUC (SUC n)))) =
                   ((h (STRCAT "pays" (toString (SUC (SUC n)))))) xor
                        ((r (STRCAT "coin" (toString (SUC (SUC n))))) xor (r (STRCAT "coin" (toString (SUC n))))))``,
   ASM_SIMP_TAC arith_ss [dc_set_announcements_result4]);

(* ------------------------------------------------------------------------- *)

Theorem dc_XOR_announces_result1:
  !high low random n i.
    i <= SUC (SUC n) /\ (high (STRCAT "pays" (toString i))) /\
    (!j. (~(j = i)) ==> ~(high (STRCAT "pays" (toString j)))) ==>
    !k. k < i ==>
        (XOR_announces
         (set_announcements high low random (SUC (SUC n)) (SUC (SUC n))) k =
         ((random (STRCAT "coin" (toString k))) xor
          (random (STRCAT "coin" (toString (SUC (SUC n)))))))
Proof
   NTAC 6 (STRIP_TAC)
   >> Induct
   >- (SIMP_TAC bool_ss [XOR_announces_def, dc_set_announcements_result2]
       >> POP_ASSUM (ASSUME_TAC o Q.SPEC `0`)
       >> RW_TAC arith_ss [DECIDE ``!n:num. 0 < n <=> ~(n = 0)``, F_xor])
   >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []
   >> RW_TAC arith_ss [XOR_announces_def, dc_set_announcements_result4, F_xor]
   >> METIS_TAC [DECIDE ``!(n:num) m. n < m ==> ~(n = m)``, xor_def]
QED

val dc_XOR_announces_result2 = store_thm
  ("dc_XOR_announces_result2",
   ``!high low random n i. i <= SUC (SUC n) /\ (high (STRCAT "pays" (toString i))) /\ (!j. (~(j = i)) ==> ~(high (STRCAT "pays" (toString j)))) ==>
        (XOR_announces (set_announcements high low random (SUC (SUC n)) (SUC (SUC n))) i =
                 ~((random (STRCAT "coin" (toString i))) xor (random (STRCAT "coin" (toString (SUC (SUC n)))))))``,
   REPEAT STRIP_TAC >> Cases_on `i`
   >- (SIMP_TAC bool_ss [XOR_announces_def, dc_set_announcements_result2]
       >> RW_TAC bool_ss [EQ_SYM_EQ, xor_def])
   >> ONCE_REWRITE_TAC [XOR_announces_def]
   >> (ASSUME_TAC o REWRITE_RULE [DECIDE ``!n:num. n < SUC n``] o Q.SPEC `n'` o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO]
       o Q.SPECL [`high`, `low`, `random`, `n`, `(SUC n')`]) dc_XOR_announces_result1
   >> FULL_SIMP_TAC bool_ss [DECIDE ``!(n:num) m. n <= m <=> n < SUC m``, dc_set_announcements_result4, DECIDE ``!(n:num) m. SUC n < m ==> n < m``]
   >> RW_TAC bool_ss [xor_def] >> DECIDE_TAC);

val dc_XOR_announces_result3 = store_thm
  ("dc_XOR_announces_result3",
   ``!high low random n i. i <= SUC (SUC n) /\ (high (STRCAT "pays" (toString i))) /\ (!j. (~(j = i)) ==> ~(high (STRCAT "pays" (toString j)))) ==>
        !k. i <= k /\ k <= SUC (SUC n) ==>
                (XOR_announces (set_announcements high low random (SUC (SUC n)) (SUC (SUC n))) k =
                 ~((random (STRCAT "coin" (toString k))) xor (random (STRCAT "coin" (toString (SUC (SUC n)))))))``,
   NTAC 6 (STRIP_TAC) >> Induct
   >- (RW_TAC arith_ss [XOR_announces_def, dc_set_announcements_result2]
       >> RW_TAC bool_ss [T_xor])
   >> Cases_on `SUC k = i`
   >- ((ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.SPECL [`high`, `low`, `random`, `n`, `i`]) dc_XOR_announces_result2
       >> ASM_REWRITE_TAC [])
   >> Cases_on `k = SUC n`
   >- (ONCE_REWRITE_TAC [XOR_announces_def]
       >> `i <= SUC n /\ SUC n <= SUC (SUC n)` by FULL_SIMP_TAC arith_ss [] >> FULL_SIMP_TAC bool_ss []
       >> ASM_SIMP_TAC arith_ss [dc_set_announcements_result6, F_xor]
       >> RW_TAC bool_ss [xor_def] >> DECIDE_TAC)
   >> STRIP_TAC >> ONCE_REWRITE_TAC [XOR_announces_def]
   >> `i <= k /\ k <= SUC (SUC n)` by FULL_SIMP_TAC arith_ss [] >> FULL_SIMP_TAC bool_ss []
   >> ASM_SIMP_TAC arith_ss [dc_set_announcements_result4, F_xor]
   >> RW_TAC bool_ss [xor_def] >> DECIDE_TAC);

val dc_XOR_announces_result4 = store_thm
  ("dc_XOR_announces_result4",
   ``!high low random n i. i <= SUC (SUC n) /\ (high (STRCAT "pays" (toString i))) /\ (!j. (~(j = i)) ==> ~(high (STRCAT "pays" (toString j)))) ==>
                (XOR_announces (set_announcements high low random (SUC (SUC n)) (SUC (SUC n))) (SUC (SUC n)))``,
   NTAC 6 STRIP_TAC
   >> RW_TAC std_ss [(REWRITE_RULE [LESS_EQ_REFL] o UNDISCH o Q.SPEC `SUC (SUC n)`
                      o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO]
                      o Q.SPECL [`high`, `low`, `random`, `n`, `i`]) dc_XOR_announces_result3, xor_refl]);

val dc_XOR_announces_result5 = store_thm
  ("dc_XOR_announces_result5",
   ``!high low random n. high IN dc_high_states F (SUC (SUC (SUC n)))  ==>
                (XOR_announces (set_announcements high low random (SUC (SUC n)) (SUC (SUC n))) (SUC (SUC n)))``,
   NTAC 5 STRIP_TAC
   >> MATCH_MP_TAC dc_XOR_announces_result4
   >> FULL_SIMP_TAC bool_ss [dc_high_states_def, IN_dc_high_states_set, GSPECIFICATION, PAIR_EQ]
   >> Q.EXISTS_TAC `i`
   >> RW_TAC bool_ss []
   >> RW_TAC std_ss [STRCAT_toString_inj]);

(* ------------------------------------------------------------------------- *)

val dcprog_result1 = store_thm
  ("dcprog_result1",
   ``!high low random n. dcprog (SUC (SUC (SUC n))) ((high, low), random) "result" =
                         XOR_announces (set_announcements high low random
                                        (SUC (SUC n)) (SUC (SUC n))) (SUC (SUC n))``,
   RW_TAC std_ss [dcprog_def, compute_result_def]);

val dcprog_result2 = store_thm
  ("dcprog_result2",
   ``!high low random n x. (~(x = "result")) ==>
        (dcprog (SUC (SUC (SUC n))) ((high, low), random) x =
         (set_announcements high low random (SUC (SUC n)) (SUC (SUC n))) x)``,
   RW_TAC std_ss [dcprog_def, compute_result_def]);

val dcprog_result3 = store_thm
  ("dcprog_result3",
   ``!high low random n i. XOR_announces (dcprog (SUC (SUC (SUC n))) ((high, low), random)) i =
                         XOR_announces (set_announcements high low random
                                        (SUC (SUC n)) (SUC (SUC n))) i``,
   NTAC 4 STRIP_TAC >> Induct
   >- RW_TAC string_ss [XOR_announces_def, dcprog_result2]
   >> ONCE_REWRITE_TAC [XOR_announces_def]
   >> RW_TAC string_ss [dcprog_result2]);

val dcprog_result4 = store_thm
  ("dcprog_result4",
   ``!high low random n. XOR_announces (dcprog (SUC (SUC (SUC n))) ((high, low), random)) (SUC (SUC n)) =
                         (dcprog (SUC (SUC (SUC n))) ((high, low), random)) "result"``,
   REPEAT STRIP_TAC >> ONCE_REWRITE_TAC [dcprog_result3]
   >> RW_TAC std_ss [dcprog_def, compute_result_def]);

val dcprog_result5 = store_thm
  ("dcprog_result5",
   ``!high low random n. high IN dc_high_states F (SUC (SUC (SUC n))) ==>
        ((dcprog (SUC (SUC (SUC n))) ((high, low), random)) "result")``,
   RW_TAC std_ss [dcprog_def, compute_result_def, dc_XOR_announces_result5]);

val dcprog_result6 = store_thm
  ("dcprog_result6",
   ``!high low random n i.
        (dcprog (SUC (SUC (SUC n))) ((high, low), random) (STRCAT "announces" (toString i)) =
         (set_announcements high low random (SUC (SUC n)) (SUC (SUC n))) (STRCAT "announces" (toString i)))``,
   RW_TAC string_ss [dcprog_result2]);

(* ************************************************************************* *)
(* Case Study: The Dining Cryptographers - Proofs (Anonymity)                *)
(* ************************************************************************* *)

val dc_valid_outputs_def = Define
   `dc_valid_outputs n = {s: bool state | (s "result" = XOR_announces s n) /\
                                          (XOR_announces s n) /\
                                          (!x. (~(x = "result")) /\
                                               (!i:num. i <= n ==>
                                                        ~(x = (STRCAT "announces" (toString i)))) ==>
                                                ~ s x)}`;

val dc_random_witness_def = Define
   `(dc_random_witness x (0:num) = (\s:string. if s = (STRCAT "coin" (toString 0)) then
                                                        ~(x (STRCAT "announces" (toString 0)))
                                                   else F)) /\
    (dc_random_witness x (SUC i) = (\s. if s = (STRCAT "coin" (toString (SUC i))) then
                                                ~ (XOR_announces x (SUC i))
                                            else
                                                dc_random_witness x i s))`;

val dc_random_witness_lem0 = prove
  (``!x n i. (SUC n) <= i ==> ~(dc_random_witness x n (STRCAT "coin" (toString i)))``,
   STRIP_TAC >> Induct >> RW_TAC arith_ss [dc_random_witness_def, STRCAT_toString_inj]);

val dc_random_witness_lem1 = prove
  (``!x n. ~(dc_random_witness x n (STRCAT "coin" (toString (SUC n))))``,
   ASM_SIMP_TAC arith_ss [dc_random_witness_lem0]);

val dc_random_witness_lem2 = prove
  (``!x n. (dc_random_witness x n (STRCAT "coin" (toString 0))) = ~(x (STRCAT "announces" (toString 0)))``,
   STRIP_TAC >> Induct >> RW_TAC arith_ss [dc_random_witness_def, STRCAT_toString_inj]);

val dc_random_witness_lem3 = prove
  (``!x n i. i <= n ==> ((dc_random_witness x n (STRCAT "coin" (toString i))) =
                         ~ (XOR_announces x i))``,
   STRIP_TAC >> Induct
   >- RW_TAC std_ss [dc_random_witness_lem2, XOR_announces_def]
   >> RW_TAC std_ss [dc_random_witness_def, STRCAT_toString_inj]
   >> FULL_SIMP_TAC arith_ss []);

val dc_random_witness_lem4 = prove
  (``!x x' n. (!i. i <= n ==> ~(x' = (STRCAT "coin" (toString i)))) ==>
                ~ dc_random_witness x n x'``,
   STRIP_TAC >> STRIP_TAC >> Induct
   >> RW_TAC std_ss [dc_random_witness_def]
   >> FULL_SIMP_TAC std_ss [DECIDE ``!(n:num) m. n <= m ==> n <= SUC m``]);

val dc_random_witness_result = prove
  (``!x n i. i <= (SUC(SUC n)) /\ XOR_announces x (SUC(SUC n)) ==>
             (dcprog (SUC (SUC (SUC n))) (((\s. s = STRCAT "pays" (toString 0)),(\s. F)),dc_random_witness x (SUC n))
                (STRCAT "announces" (toString i)) =
              x (STRCAT "announces" (toString i)))``,
   REPEAT STRIP_TAC >> Cases_on `i`
   >- RW_TAC arith_ss [dcprog_result6, dc_set_announcements_result2, dc_random_witness_lem1, T_xor, F_xor, dc_random_witness_lem2, xor_comm]
   >> RW_TAC arith_ss [dcprog_result6, dc_set_announcements_result4, STRCAT_toString_inj, F_xor, dc_random_witness_lem3]
   >> (ASSUME_TAC o Q.SPECL [`x`, `SUC n`, `SUC n'`]) dc_random_witness_lem3
   >> Cases_on `n' = SUC n`
   >- (FULL_SIMP_TAC arith_ss [dc_random_witness_lem1, F_xor] >> METIS_TAC [XOR_announces_def, xor_def])
   >> FULL_SIMP_TAC arith_ss [] >> ONCE_REWRITE_TAC [XOR_announces_def]
   >> RW_TAC bool_ss [xor_def] >> DECIDE_TAC);

val dc_valid_outputs_eq_outputs = store_thm
  ("dc_valid_outputs_eq_outputs",
   ``!n. (IMAGE (λ(h,r). dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r))
               (dc_high_states F (SUC (SUC (SUC n))) CROSS
                dc_random_states (SUC (SUC n)))) =
          dc_valid_outputs (SUC (SUC n))``,
   RW_TAC std_ss [EXTENSION, IN_IMAGE, IN_CROSS, dc_valid_outputs_def, GSPECIFICATION]
   >> RW_TAC std_ss [GSYM EXTENSION]
   >> EQ_TAC
   >- (STRIP_TAC >> (ASSUME_TAC o Q.ISPEC `(x' :bool state # bool state)`) pair_CASES
       >> FULL_SIMP_TAC std_ss [dcprog_result4]
       >> FULL_SIMP_TAC std_ss [FST, SND, dcprog_result5]
       >> RW_TAC std_ss [dcprog_def, compute_result_def]
       >> ASM_SIMP_TAC arith_ss [dc_set_announcements_result5])
   >> STRIP_TAC
   >> Q.EXISTS_TAC `((\s:string. s = (STRCAT "pays" (toString 0))), dc_random_witness x (SUC n))`
   >> `(\s. s = STRCAT "pays" (toString 0)) IN dc_high_states F (SUC (SUC (SUC n)))`
        by (RW_TAC std_ss [dc_high_states_def, IN_dc_high_states_set] >> Q.EXISTS_TAC `0` >> RW_TAC std_ss [])
   >> `(dc_random_witness x (SUC n)) IN (dc_random_states (SUC (SUC n)))`
        by (RW_TAC std_ss [IN_dc_random_states]
            >> POP_ASSUM MP_TAC
            >> SPEC_TAC (``n:num``,``n:num``)
            >> Induct
            >- (RW_TAC bool_ss [dc_random_witness_def]
                >- (POP_ASSUM (ASSUME_TAC o Q.SPEC `SUC 0`) >> FULL_SIMP_TAC arith_ss [STRCAT_toString_inj])
                >> POP_ASSUM (ASSUME_TAC o Q.SPEC `0`) >> FULL_SIMP_TAC arith_ss [STRCAT_toString_inj])
            >> STRIP_TAC
            >> `(!i. ~(i <= SUC (SUC n')) \/ ~(x' = STRCAT "coin" (toString i)))`
                by (STRIP_TAC >> reverse (Cases_on `i <= SUC (SUC n')`) >- ASM_REWRITE_TAC []
                    >> Q.PAT_X_ASSUM `!i. ~(i <= SUC (SUC (SUC n'))) \/ ~(x' = STRCAT "coin" (toString i))`
                        (ASSUME_TAC o Q.SPEC `i`)
                    >> FULL_SIMP_TAC arith_ss [])
            >> FULL_SIMP_TAC bool_ss []
            >> ONCE_REWRITE_TAC [dc_random_witness_def]
            >> RW_TAC bool_ss []
            >> METIS_TAC [LESS_EQ_REFL, STRCAT_toString_inj,
                          DECIDE ``!(i:num) n. i <= SUC n <=> ((i = SUC n) \/ i <= n)``])
   >> ASM_REWRITE_TAC [FST, SND]
   >> RW_TAC std_ss [FUN_EQ_THM]
   >> Q.PAT_X_ASSUM `!x'. b` (ASSUME_TAC o Q.SPEC `x'`)
   >> Cases_on `x' = "result"`
   >- (ASM_REWRITE_TAC [] >> MATCH_MP_TAC dcprog_result5 >> ASM_REWRITE_TAC [])
   >> Cases_on `(!i. i <= SUC (SUC n) ==> ~(x' = STRCAT "announces" (toString i)))`
   >- FULL_SIMP_TAC arith_ss [dcprog_result2, dc_set_announcements_result5]
   >> FULL_SIMP_TAC bool_ss [dc_random_witness_result]);

(* ------------------------------------------------------------------------- *)

val n_minus_1_announces_list = Define
   `(n_minus_1_announces_list (0:num) = [(\s:string. s = (STRCAT "announces" (toString 0))); (\s:string. F)]) /\
    (n_minus_1_announces_list (SUC n) = (MAP (\s:bool state.
                                              (\x:string. if x = (STRCAT "announces" (toString (SUC n))) then
                                                                T
                                                          else s x))
                                          (n_minus_1_announces_list n)) ++
                                     (MAP (\s:bool state.
                                              (\x:string. if x = (STRCAT "announces" (toString (SUC n))) then
                                                                F
                                                          else s x))
                                          (n_minus_1_announces_list n)))`;

val dc_valid_outputs_list = Define
   `dc_valid_outputs_list (SUC(SUC(SUC n))) =
        MAP (\l s. (s = "result") \/
                   (if (s = (STRCAT "announces" (toString (SUC(SUC n))))) then
                        ~(XOR_announces l (SUC n))
                    else
                        l s))
             (n_minus_1_announces_list (SUC n))`;

val MEM_n_minus_1_announces_list = prove
  (``!n x. MEM x (n_minus_1_announces_list n) =
           (!s. (!i. i <= n ==> ~(s = STRCAT "announces" (toString i))) ==> ~x s)``,
   Induct
   >- (RW_TAC std_ss [n_minus_1_announces_list, MEM] >> METIS_TAC [])
   >> RW_TAC list_ss [n_minus_1_announces_list, MEM_MAP]
   >> EQ_TAC
   >- (RW_TAC std_ss [] >> RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM `!s'. b ==> ~s s'` MATCH_MP_TAC \\
       STRIP_TAC >> FULL_SIMP_TAC arith_ss [])
   >> RW_TAC std_ss [] >> Cases_on `x (STRCAT "announces" (toString (SUC n)))`
   >- (DISJ1_TAC >> Q.EXISTS_TAC `(\x'. if (x' = STRCAT "announces" (toString (SUC n))) then F else x x')`
       >> RW_TAC std_ss [] >- (FULL_SIMP_TAC string_ss [] >> METIS_TAC [])
       >> Cases_on `(s' = STRCAT "announces" (toString (SUC n)))` >> ASM_REWRITE_TAC []
       >> Q.PAT_X_ASSUM `!s. b ==> ~x s` MATCH_MP_TAC
       >> RW_TAC std_ss [DECIDE ``!(n:num) m. n <= SUC m <=> ((n = SUC m) \/ n < SUC m)``] >> FULL_SIMP_TAC string_ss [])
   >> DISJ2_TAC >> Q.EXISTS_TAC `x` >> RW_TAC std_ss [] >- (FULL_SIMP_TAC string_ss [] >> METIS_TAC [])
   >> Cases_on `(s' = STRCAT "announces" (toString (SUC n)))` >> ASM_REWRITE_TAC []
   >> Q.PAT_X_ASSUM `!s. b ==> ~x s` MATCH_MP_TAC
   >> RW_TAC std_ss [DECIDE ``!(n:num) m. n <= SUC m <=> ((n = SUC m) \/ n < SUC m)``] >> FULL_SIMP_TAC string_ss []);

val dc_valid_outputs_eq_dc_valid_outputs_list = prove
  (``!n. dc_valid_outputs (SUC(SUC n)) = set (dc_valid_outputs_list (SUC(SUC(SUC n))))``,
   REPEAT STRIP_TAC
   >> SIMP_TAC std_ss [EXTENSION, dc_valid_outputs_def, GSPECIFICATION]
   >> SIMP_TAC std_ss [GSYM EXTENSION, dc_valid_outputs_list, MEM_MAP, MEM_n_minus_1_announces_list]
   >> STRIP_TAC
   >> EQ_TAC
   >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(\s. if s = "result" then F else
                                                if s = STRCAT "announces" (toString (SUC (SUC n))) then F
                                                else  x s)` >> CONJ_TAC
       >- (`x (STRCAT "announces" (toString (SUC (SUC n)))) = ~XOR_announces (\s. if s = "result" then F else
                                                if s = STRCAT "announces" (toString (SUC (SUC n))) then F
                                                else  x s) (SUC n)`
                by (Q.PAT_X_ASSUM `XOR_announces x (SUC (SUC n))` MP_TAC
                    >> CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [XOR_announces_def]))
                    >> Suff `!k n. n <= k ==>
                                 (XOR_announces x (SUC n) = XOR_announces (\s. if s = "result" then F else
                                                if s = STRCAT "announces" (toString (SUC (SUC k))) then F
                                                else  x s) (SUC n))`
                    >- METIS_TAC [xor_def, LESS_EQ_REFL]
                    >> STRIP_TAC >> Induct
                    >- RW_TAC string_ss [XOR_announces_def, STRCAT_toString_inj]
                    >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []
                    >> ONCE_REWRITE_TAC [XOR_announces_def]
                    >> ASM_REWRITE_TAC []
                    >> RW_TAC string_ss [STRCAT_toString_inj])
           >> METIS_TAC [])
       >> STRIP_TAC >> STRIP_TAC >> SIMP_TAC std_ss [] >> Cases_on `s = "result"` >> ASM_REWRITE_TAC []
       >> Cases_on `s = STRCAT "announces" (toString (SUC (SUC n)))` >> ASM_REWRITE_TAC []
       >> Q.PAT_X_ASSUM `!x'. b ==> ~x x'` MATCH_MP_TAC >> RW_TAC std_ss []
       >> Cases_on `i = SUC(SUC n)` >> FULL_SIMP_TAC arith_ss [])
   >> STRIP_TAC
   >> Know `XOR_announces x (SUC (SUC n))`
   >- (ASM_REWRITE_TAC [] >> ONCE_REWRITE_TAC [XOR_announces_def] >> SIMP_TAC std_ss []
       >> `~((STRCAT "announces" (toString (SUC (SUC n))) = "result"))` by SIMP_TAC string_ss []
       >> ASM_REWRITE_TAC []
       >> rename1 `!s.
            (!i. i <= SUC n ==> s <> STRCAT "announces" (toString i)) ==>
            ~l' s`
       >> Suff `!n k. k <= n ==>
                                (XOR_announces (\s. (s = "result") \/ (if s = STRCAT "announces" (toString (SUC (SUC n))) then
                                ~XOR_announces l' (SUC n) else l' s)) (SUC k) =
                                XOR_announces l' (SUC k))`
       >- RW_TAC arith_ss [xor_inv, xor_comm]
       >> STRIP_TAC >> Induct >- RW_TAC string_ss [XOR_announces_def, STRCAT_toString_inj]
       >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []
       >> ONCE_REWRITE_TAC [XOR_announces_def]
       >> ASM_REWRITE_TAC []
       >> RW_TAC string_ss [STRCAT_toString_inj])
   >> ASM_REWRITE_TAC []
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!s. b ==> ~l' s` MATCH_MP_TAC >> STRIP_TAC >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []);

val LENGTH_n_minus_1_announces_list = prove
  (``!n. LENGTH (n_minus_1_announces_list n) = 2 ** (SUC n)``,
   Induct >> RW_TAC list_ss [n_minus_1_announces_list, EXP]);

val LENGTH_dc_valid_outputs_list = prove
  (``!n. LENGTH (dc_valid_outputs_list (SUC(SUC(SUC n)))) = 2 ** (SUC(SUC n))``,
   RW_TAC list_ss [dc_valid_outputs_list, LENGTH_n_minus_1_announces_list]);

val n_minus_1_announces_list_SUC_n = prove
  (``!n k (x:bool state). n <= k /\ MEM x (n_minus_1_announces_list n) ==> ~(x (STRCAT "announces" (toString (SUC k))))``,
   Induct >- (RW_TAC std_ss [n_minus_1_announces_list]
              >> FULL_SIMP_TAC list_ss [n_minus_1_announces_list, STRCAT_toString_inj, toString_inj])
   >> STRIP_TAC >> STRIP_TAC >> SIMP_TAC list_ss [n_minus_1_announces_list, MEM_MAP]
   >> STRIP_TAC >> ASM_REWRITE_TAC [] >> SIMP_TAC std_ss [STRCAT_toString_inj] >> FULL_SIMP_TAC string_ss [toString_inj]);

val ALL_DISTINCT_n_minus_1_announces_list = prove
  (``!n. ALL_DISTINCT (n_minus_1_announces_list n)``,
   Induct >- (RW_TAC list_ss [ALL_DISTINCT, n_minus_1_announces_list] >> METIS_TAC [])
   >> RW_TAC bool_ss [n_minus_1_announces_list]
   >> MATCH_MP_TAC ALL_DISTINCT_APPEND
   >> CONJ_TAC
   >- (MATCH_MP_TAC ALL_DISTINCT_MAP2 >> RW_TAC bool_ss [FUN_EQ_THM] >> METIS_TAC [n_minus_1_announces_list_SUC_n, LESS_EQ_REFL])
   >> CONJ_TAC
   >- (MATCH_MP_TAC ALL_DISTINCT_MAP2 >> RW_TAC bool_ss [FUN_EQ_THM] >> METIS_TAC [n_minus_1_announces_list_SUC_n, LESS_EQ_REFL])
   >> RW_TAC bool_ss [MEM_MAP]
   >> Cases_on `(!s.
       ~(x = (\x. (x = STRCAT "announces" (toString (SUC n))) \/ s x)) \/
       ~MEM s (n_minus_1_announces_list n))`
   >> ASM_REWRITE_TAC []
   >> FULL_SIMP_TAC bool_ss []
   >> RW_TAC bool_ss [] >> reverse (Cases_on `MEM s' (n_minus_1_announces_list n)`) >> ASM_REWRITE_TAC []
   >> RW_TAC bool_ss [FUN_EQ_THM] >> Q.EXISTS_TAC `STRCAT "announces" (toString (SUC n))`
   >> RW_TAC bool_ss [n_minus_1_announces_list_SUC_n]);

val n_minus_1_announces_list_result = prove
  (``!n x. MEM x (n_minus_1_announces_list n) ==> ~(x "result")``,
   Induct >- (RW_TAC list_ss [n_minus_1_announces_list] >> RW_TAC arith_string_ss [])
   >> SIMP_TAC list_ss [n_minus_1_announces_list, MEM_MAP]
   >> STRIP_TAC >> STRIP_TAC >> ASM_REWRITE_TAC [] >> SIMP_TAC arith_string_ss [] >> RW_TAC std_ss []);

val ALL_DISTINCT_dc_valid_outputs_list = prove
  (``!n. ALL_DISTINCT (dc_valid_outputs_list (SUC(SUC(SUC n))))``,
   STRIP_TAC >> ONCE_REWRITE_TAC [dc_valid_outputs_list] >> MATCH_MP_TAC ALL_DISTINCT_MAP2
   >> RW_TAC std_ss [ALL_DISTINCT_n_minus_1_announces_list, FUN_EQ_THM]
   >> POP_ASSUM (ASSUME_TAC o Q.SPEC `x'`)
   >> METIS_TAC [n_minus_1_announces_list_result, n_minus_1_announces_list_SUC_n, LESS_EQ_REFL]);

val CARD_dc_valid_outputs = store_thm
  ("CARD_dc_valid_outputs",
   ``!n. CARD (IMAGE (λ(h,r). dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r))
               (dc_high_states F (SUC (SUC (SUC n))) CROSS
                dc_random_states (SUC (SUC n)))) =
          2 ** (SUC(SUC n))``,
   RW_TAC std_ss [dc_valid_outputs_eq_outputs,
                  dc_valid_outputs_eq_dc_valid_outputs_list,
                  GSYM LENGTH_dc_valid_outputs_list,
                  ALL_DISTINCT_CARD_LIST_TO_SET,
                  ALL_DISTINCT_dc_valid_outputs_list,
                  all_distinct_nub_id]);

(* ------------------------------------------------------------------------- *)

val valid_coin_assignment = Define
  `(valid_coin_assignment r out h n (0:num) =
    (r (STRCAT "coin" (toString 0)) <=>
       ((r (STRCAT "coin" (toString (SUC (SUC n))))) xor (XOR_announces out (0:num)) xor ~((0:num) < h)))) /\
   (valid_coin_assignment r out h n (SUC i) =
       ((r (STRCAT "coin" (toString (SUC i))) <=>
        ((r (STRCAT "coin" (toString (SUC (SUC n))))) xor (XOR_announces out (SUC i)) xor ~((SUC i) < h))) /\
        (valid_coin_assignment r out h n i)))`;

val valid_coin_assignment_result1 = prove
  (``!x out p n i j. j <= i /\ valid_coin_assignment x out p n i ==> valid_coin_assignment x out p n j``,
   NTAC 4 STRIP_TAC >> Induct >- RW_TAC arith_ss []
   >> REPEAT STRIP_TAC >> Cases_on `j = SUC i` >> FULL_SIMP_TAC arith_ss []
   >> Q.PAT_X_ASSUM `!j. b` MATCH_MP_TAC >> FULL_SIMP_TAC arith_ss [valid_coin_assignment]);

val valid_coin_set_eq_valid_coin_assignment = store_thm
  ("valid_coin_set_eq_valid_coin_assignment",
   ``!n p out. p <= SUC (SUC n) /\
               out IN (IMAGE (λ(h,r). dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r))
                             (dc_high_states F (SUC (SUC (SUC n))) CROSS dc_random_states (SUC (SUC n)))) ==>
             ({r | r IN (dc_random_states (SUC (SUC n))) /\
                   (dcprog (SUC (SUC (SUC n))) (((\s. s = STRCAT "pays" (toString p)), (\s.F)), r) = out)} =
              {r | r IN (dc_random_states (SUC (SUC n))) /\
                   valid_coin_assignment r out p n (SUC (SUC n))})``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION]
   >> RW_TAC std_ss [GSYM EXTENSION]
   >> reverse (Cases_on `x IN dc_random_states (SUC (SUC n))`) >> ASM_REWRITE_TAC []
   >> `(\s. s = STRCAT "pays" (toString p)) IN dc_high_states F (SUC (SUC (SUC n)))`
        by (RW_TAC std_ss [dc_high_states_def, IN_dc_high_states_set] >> Q.EXISTS_TAC `p` >> RW_TAC std_ss [])
   >> EQ_TAC
   >- (STRIP_TAC >> POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
       >> Suff `!i. i <= SUC (SUC n) ==> valid_coin_assignment x out p n i` >- RW_TAC std_ss [LESS_EQ_REFL]
       >> FULL_SIMP_TAC std_ss [] >> Induct
       >- (RW_TAC std_ss [valid_coin_assignment, XOR_announces_def, dcprog_result6, dc_set_announcements_result2,
                          STRCAT_toString_inj]
           >> Cases_on `p = 0` >> RW_TAC arith_ss [T_xor, F_xor, xor_def] >> DECIDE_TAC)
       >> STRIP_TAC >> FULL_SIMP_TAC arith_ss [] >> ONCE_REWRITE_TAC [valid_coin_assignment]
       >> ASM_REWRITE_TAC [] >> ONCE_REWRITE_TAC [XOR_announces_def]
       >> `SUC i < SUC (SUC (SUC n))` by FULL_SIMP_TAC arith_ss []
       >> `i < SUC (SUC (SUC n))` by FULL_SIMP_TAC arith_ss []
       >> RW_TAC bool_ss [dcprog_result6, dc_set_announcements_result4, STRCAT_toString_inj]
       >> Cases_on `i`
       >- (RW_TAC std_ss [valid_coin_assignment, XOR_announces_def, dcprog_result6, dc_set_announcements_result2,
                          STRCAT_toString_inj, F_xor]
           >> Cases_on `p = 0` >- (RW_TAC arith_ss [xor_def] >> DECIDE_TAC)
           >> Cases_on `p = 1` >- (RW_TAC arith_ss [xor_def] >> DECIDE_TAC)
           >> FULL_SIMP_TAC arith_ss [xor_def] >> DECIDE_TAC)
       >> FULL_SIMP_TAC bool_ss [valid_coin_assignment]
       >> RW_TAC bool_ss [F_xor, xor_def] >> Cases_on `p = SUC (SUC n')` >- (FULL_SIMP_TAC arith_ss [] >> DECIDE_TAC)
       >> FULL_SIMP_TAC arith_ss [] >> Cases_on `SUC (SUC n') < p` >> FULL_SIMP_TAC arith_ss [] >> DECIDE_TAC)
   >> STRIP_TAC >> RW_TAC std_ss [FUN_EQ_THM] >> Cases_on `x' = "result"`
   >- (ASM_SIMP_TAC std_ss [dcprog_result5] >> FULL_SIMP_TAC std_ss [dc_valid_outputs_eq_outputs, dc_valid_outputs_def, GSPECIFICATION])
   >> Cases_on `!i. i <= SUC (SUC n) ==> ~(x' = STRCAT "announces" (toString i))`
   >- (ASM_SIMP_TAC std_ss [dcprog_result2, dc_set_announcements_result5, LESS_EQ_REFL]
       >> FULL_SIMP_TAC std_ss [dc_valid_outputs_eq_outputs, dc_valid_outputs_def, GSPECIFICATION])
   >> FULL_SIMP_TAC std_ss [] >> Induct_on `i`
   >- (RW_TAC std_ss [dcprog_result6, dc_set_announcements_result2, STRCAT_toString_inj]
       >> `valid_coin_assignment x out p n 0` by METIS_TAC [valid_coin_assignment_result1, ZERO_LESS_EQ]
       >> POP_ASSUM (ASSUME_TAC o REWRITE_RULE [valid_coin_assignment, XOR_announces_def])
       >> POP_ORW >> Cases_on `p = 0` >> FULL_SIMP_TAC arith_ss [xor_def] >> DECIDE_TAC)
   >> STRIP_TAC >> STRIP_TAC
   >> `SUC i < SUC (SUC (SUC n))` by FULL_SIMP_TAC arith_ss []
   >> `i < SUC (SUC (SUC n))` by FULL_SIMP_TAC arith_ss []
   >> RW_TAC bool_ss [dcprog_result6, dc_set_announcements_result4, STRCAT_toString_inj]
   >> `valid_coin_assignment x out p n (SUC i)`
        by (MATCH_MP_TAC valid_coin_assignment_result1 >> Q.EXISTS_TAC `SUC (SUC n)` >> FULL_SIMP_TAC arith_ss [])
   >> POP_ASSUM (ASSUME_TAC o REWRITE_RULE [valid_coin_assignment, XOR_announces_def])
   >> POP_ORW
   >> `valid_coin_assignment x out p n i`
        by (MATCH_MP_TAC valid_coin_assignment_result1 >> Q.EXISTS_TAC `SUC (SUC n)` >> FULL_SIMP_TAC arith_ss [])
   >> Cases_on `i`
   >- (RW_TAC std_ss [XOR_announces_def]
       >> POP_ASSUM (ASSUME_TAC o REWRITE_RULE [valid_coin_assignment, XOR_announces_def]) >> POP_ORW
       >> Cases_on `p = 1` >- (FULL_SIMP_TAC arith_ss [xor_def] >> DECIDE_TAC)
       >> FULL_SIMP_TAC arith_ss [xor_def] >> Cases_on `p = 0` >> FULL_SIMP_TAC arith_ss [xor_def] >> DECIDE_TAC)
   >> POP_ASSUM (ASSUME_TAC o REWRITE_RULE [valid_coin_assignment, XOR_announces_def]) >> POP_ORW
   >> ONCE_REWRITE_TAC [XOR_announces_def]
   >> Cases_on `p = SUC (SUC n')` >- (FULL_SIMP_TAC arith_ss [xor_def] >> DECIDE_TAC)
   >> FULL_SIMP_TAC arith_ss [xor_def] >> Cases_on `SUC (SUC n') < p` >> FULL_SIMP_TAC arith_ss [xor_def] >> DECIDE_TAC);

val coin_assignment = Define
   `(coin_assignment out h n choice (0:num) =
        (\s. if s = (STRCAT "coin" (toString 0)) then
                (choice xor (XOR_announces out (0:num)) xor ~((0:num) < h))
             else F)) /\
    (coin_assignment out h n choice (SUC i) =
        (\s. if s = (STRCAT "coin" (toString (SUC i))) then
                (choice xor (XOR_announces out (SUC i)) xor ~((SUC i) < h))
             else
                coin_assignment out h n choice i s))`;

Definition coin_assignment_set:
  coin_assignment_set out p n =
        {coin_assignment out p n T (SUC(SUC n));
          coin_assignment out p n F (SUC(SUC n))}
End

val coin_assignment_result1 = prove
  (``!out h choice x' n i. (!j. j <= i ==> ~(x' = STRCAT "coin" (toString j))) ==> ~(coin_assignment out h n choice i x')``,
   NTAC 5 STRIP_TAC >> Induct
   >- RW_TAC arith_ss [coin_assignment, STRCAT_toString_inj]
   >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []
   >> RW_TAC arith_ss [coin_assignment, STRCAT_toString_inj]);

val coin_assignment_result2 = prove
  (``!out h choice n j i. i <= j ==>
        (coin_assignment out p n choice j (STRCAT "coin" (toString i)) =
         coin_assignment out p n choice i (STRCAT "coin" (toString i)))``,
   NTAC 4 STRIP_TAC >> Induct >- RW_TAC arith_ss []
   >> RW_TAC std_ss [coin_assignment, STRCAT_toString_inj]
   >> FULL_SIMP_TAC arith_ss []);

val valid_coin_assignment_eq_2_element_set = store_thm
  ("valid_coin_assignment_eq_2_element_set",
   ``!n p out.
         p <= SUC (SUC n) /\
         out IN
         IMAGE (λ(h,r). dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r))
           (dc_high_states F (SUC (SUC (SUC n))) CROSS
            dc_random_states (SUC (SUC n))) ==>
        ({r |
           r IN dc_random_states (SUC (SUC n)) /\
           valid_coin_assignment r out p n (SUC (SUC n))} =
         coin_assignment_set out p n)``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, coin_assignment_set]
   >> RW_TAC std_ss [GSYM EXTENSION, IN_INSERT, NOT_IN_EMPTY]
   >> EQ_TAC
   >- (STRIP_TAC
       >> Cases_on `x (STRCAT "coin" (toString (SUC(SUC n))))`
       >- (DISJ1_TAC
           >> RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `!i. i <= SUC (SUC n) ==> ~(x' = STRCAT "coin" (toString i))`
           >- (ASM_SIMP_TAC arith_ss [coin_assignment_result1]
               >> FULL_SIMP_TAC std_ss [IN_dc_random_states]
               >> Q.PAT_X_ASSUM `!x''. b ==> ~x x''` MATCH_MP_TAC
               >> STRIP_TAC >> reverse (Cases_on `i <= SUC (SUC n)`) >> ASM_REWRITE_TAC []
               >> FULL_SIMP_TAC arith_ss [])
           >> FULL_SIMP_TAC std_ss [] >> Q.PAT_X_ASSUM `i <= SUC (SUC n)` MP_TAC
           >> Q.SPEC_TAC (`i:num`,`i:num`) >> Induct
           >- (ASM_SIMP_TAC arith_ss [coin_assignment_result2, coin_assignment, T_xor, XOR_announces_def]
               >> `valid_coin_assignment x out p n 0` by METIS_TAC [valid_coin_assignment_result1, ZERO_LESS_EQ]
               >> FULL_SIMP_TAC std_ss [valid_coin_assignment, XOR_announces_def, T_xor])
           >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []
           >> ASM_SIMP_TAC arith_ss [coin_assignment_result2, coin_assignment, T_xor, XOR_announces_def]
           >> `valid_coin_assignment x out p n (SUC i')`
                by (MATCH_MP_TAC valid_coin_assignment_result1 >> Q.EXISTS_TAC `SUC (SUC n)` >> FULL_SIMP_TAC arith_ss [])
           >> POP_ASSUM (ASSUME_TAC o REWRITE_RULE [valid_coin_assignment, XOR_announces_def])
           >> POP_ORW >> RW_TAC bool_ss [T_xor])
       >> DISJ2_TAC
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> Cases_on `!i. i <= SUC (SUC n) ==> ~(x' = STRCAT "coin" (toString i))`
       >- (ASM_SIMP_TAC arith_ss [coin_assignment_result1]
           >> FULL_SIMP_TAC std_ss [IN_dc_random_states]
           >> Q.PAT_X_ASSUM `!x''. b ==> ~x x''` MATCH_MP_TAC
           >> STRIP_TAC >> reverse (Cases_on `i <= SUC (SUC n)`) >> ASM_REWRITE_TAC []
           >> FULL_SIMP_TAC arith_ss [])
       >> FULL_SIMP_TAC std_ss [] >> Q.PAT_X_ASSUM `i <= SUC (SUC n)` MP_TAC
       >> Q.SPEC_TAC (`i:num`,`i:num`) >> Induct
       >- (ASM_SIMP_TAC arith_ss [coin_assignment_result2, coin_assignment, T_xor, XOR_announces_def]
           >> `valid_coin_assignment x out p n 0` by METIS_TAC [valid_coin_assignment_result1, ZERO_LESS_EQ]
           >> FULL_SIMP_TAC std_ss [valid_coin_assignment, XOR_announces_def, T_xor])
       >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []
       >> ASM_SIMP_TAC arith_ss [coin_assignment_result2, coin_assignment, T_xor, XOR_announces_def]
       >> `valid_coin_assignment x out p n (SUC i')`
           by (MATCH_MP_TAC valid_coin_assignment_result1 >> Q.EXISTS_TAC `SUC (SUC n)` >> FULL_SIMP_TAC arith_ss [])
       >> POP_ASSUM (ASSUME_TAC o REWRITE_RULE [valid_coin_assignment, XOR_announces_def])
       >> POP_ORW >> RW_TAC bool_ss [T_xor])
   >> STRIP_TAC
   >- (`x IN dc_random_states (SUC (SUC n))`
        by (RW_TAC std_ss [IN_dc_random_states] >> MATCH_MP_TAC coin_assignment_result1 >> METIS_TAC [])
       >> ASM_REWRITE_TAC []
       >> Suff `!i. i <= SUC (SUC n) ==> valid_coin_assignment (coin_assignment out p n T (SUC(SUC n))) out p n i`
       >- RW_TAC std_ss []
       >> Induct
       >- (RW_TAC arith_ss [valid_coin_assignment, XOR_announces_def, coin_assignment_result2]
           >> ONCE_REWRITE_TAC [coin_assignment]
           >> FULL_SIMP_TAC arith_ss [STRCAT_toString_inj, T_xor, xor_T]
           >> CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [XOR_announces_def]))
           >> REPEAT (POP_ASSUM MP_TAC)
           >> RW_TAC std_ss [dc_valid_outputs_eq_outputs, dc_valid_outputs_def, GSPECIFICATION, T_xor])
       >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []
       >> ONCE_REWRITE_TAC [valid_coin_assignment] >> ASM_REWRITE_TAC []
       >> RW_TAC arith_ss [coin_assignment_result2]
       >> ONCE_REWRITE_TAC [coin_assignment]
       >> FULL_SIMP_TAC arith_ss [STRCAT_toString_inj, T_xor, xor_T]
       >> REPEAT (POP_ASSUM MP_TAC)
       >> RW_TAC std_ss [dc_valid_outputs_eq_outputs, dc_valid_outputs_def, GSPECIFICATION, T_xor])
   >> `x IN dc_random_states (SUC (SUC n))`
        by (RW_TAC std_ss [IN_dc_random_states] >> MATCH_MP_TAC coin_assignment_result1 >> METIS_TAC [])
   >> ASM_REWRITE_TAC []
   >> Suff `!i. i <= SUC (SUC n) ==> valid_coin_assignment (coin_assignment out p n F (SUC(SUC n))) out p n i`
   >- RW_TAC std_ss []
   >> Induct
   >- (RW_TAC arith_ss [valid_coin_assignment, XOR_announces_def, coin_assignment_result2]
       >> ONCE_REWRITE_TAC [coin_assignment]
       >> FULL_SIMP_TAC arith_ss [STRCAT_toString_inj, T_xor, xor_T]
       >> CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [XOR_announces_def]))
       >> REPEAT (POP_ASSUM MP_TAC)
       >> RW_TAC std_ss [dc_valid_outputs_eq_outputs, dc_valid_outputs_def, GSPECIFICATION, T_xor, F_xor, xor_comm])
   >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []
   >> ONCE_REWRITE_TAC [valid_coin_assignment] >> ASM_REWRITE_TAC []
   >> RW_TAC arith_ss [coin_assignment_result2]
   >> ONCE_REWRITE_TAC [coin_assignment]
   >> FULL_SIMP_TAC arith_ss [STRCAT_toString_inj, T_xor, xor_T]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> RW_TAC std_ss [dc_valid_outputs_eq_outputs, dc_valid_outputs_def, GSPECIFICATION, T_xor, F_xor, xor_comm]);

val coin_assignment_result3 = prove
  (``!out p n i. i <= SUC (SUC n) ==>
        ~(coin_assignment out p n T i = coin_assignment out p n F i)``,

   NTAC 3 STRIP_TAC >> Induct >- (RW_TAC bool_ss [coin_assignment, F_xor, xor_comm, T_xor, xor_def] >> METIS_TAC [])
   >> STRIP_TAC >> FULL_SIMP_TAC arith_ss []
   >> ONCE_REWRITE_TAC [coin_assignment]
   >> RW_TAC std_ss [FUN_EQ_THM] >> Q.EXISTS_TAC `STRCAT "coin" (toString (SUC i))`
   >> RW_TAC std_ss [T_xor, F_xor, xor_comm, xor_def] >> DECIDE_TAC);

(* ------------------------------------------------------------------------- *)

val lg_times_compute_simp_lem = prove
   (``!x y. x * lg (y * x) = (\x. x * lg (y * x)) x``,
    RW_TAC std_ss []);

val dc_leakage_result = store_thm
  ("dc_leakage_result",
   ``!n. leakage (dc_prog_space (SUC (SUC (SUC n))) F) (dcprog (SUC (SUC (SUC n)))) = 0``,
   RW_TAC bool_ss [dc_prog_space_F_set_thm, unif_prog_space_leakage_computation_reduce,
                     dc_high_states_set_finite, dc_random_states_finite, dc_low_states_finite,
                     dc_states_cross_not_empty, CARD_dc_high_states_set, CARD_dc_low_states, CARD_dc_random_states,
                     FINITE_CROSS, IMAGE_FINITE]
   >> `FINITE (IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,FST s))
      (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
       dc_random_states (SUC (SUC n))))`
                by RW_TAC std_ss [FINITE_CROSS, IMAGE_FINITE, dc_high_states_set_finite, dc_low_states_finite,
                                  dc_random_states_finite]
   >> `FINITE (IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,FST s))
      (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
       dc_random_states (SUC (SUC n))))`
                by RW_TAC std_ss [FINITE_CROSS, IMAGE_FINITE, dc_high_states_set_finite, dc_low_states_finite,
                                  dc_random_states_finite]
   >> `FINITE (IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,SND (FST s)))
      (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
       dc_random_states (SUC (SUC n))))`
                by RW_TAC std_ss [FINITE_CROSS, IMAGE_FINITE, dc_high_states_set_finite, dc_low_states_finite,
                                  dc_random_states_finite]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,FST s))
      (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
       dc_random_states (SUC (SUC n))))`) REAL_SUM_IMAGE_IN_IF]
   >> ONCE_REWRITE_TAC [lg_times_compute_simp_lem]
   >> Know `(\x. (if x IN IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,FST s))
                                 (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
                                  dc_random_states (SUC (SUC n)))
                   then
                        (λ(out,h,l). (\x. x * lg (1 / & (2 ** SUC (SUC (SUC n))) * x))
                        (SIGMA (\r. (if dcprog (SUC (SUC (SUC n))) ((h,l),r) = out then 1  else 0))
                                (dc_random_states (SUC (SUC n))))) x
                   else 0))=
        (λ(x :bool state # bool state # bool state).
        (if x IN IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,FST s))
                (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
                 dc_random_states (SUC (SUC n)))
         then (\x. 2 * lg ((1 :real) / & ((2 :num) ** SUC (SUC (SUC n))) * 2)) x
         else (0 : real)))`
   >- (ONCE_REWRITE_TAC [FUN_EQ_THM]
       >> RW_TAC std_ss [IN_IMAGE, IN_CROSS, IN_dc_high_states_set, dc_low_states_def, IN_SING]
       >> rename1 `SND (FST s') = (\s. F)`
            >> `FST s' = (FST (FST s'), SND (FST s'))` by RW_TAC std_ss [PAIR]
            >> POP_ORW
            >> RW_TAC std_ss []
            >> Suff `SIGMA (λ(r :bool state). (if dcprog
                                (SUC (SUC (SUC (n :num)))) (FST (s' :(bool, bool, bool) prog_state),r) =
                                dcprog (SUC (SUC (SUC n))) s'
                        then (1 : real) else (0 : real))) (dc_random_states (SUC (SUC n))) = 2`
             >- RW_TAC std_ss []
             >> `(dc_random_states (SUC (SUC n))) =
                 {r: bool state | r IN dc_random_states (SUC (SUC n)) /\
                      (dcprog (SUC (SUC (SUC n)))
                        (((\s. s = STRCAT "pays" (toString i)),(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')} UNION
                 {r:bool state | r IN dc_random_states (SUC (SUC n)) /\
                      ~(dcprog (SUC (SUC (SUC n)))
                        (((\s. s = STRCAT "pays" (toString i)),(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION] >> DECIDE_TAC)
             >> POP_ORW
             >> `DISJOINT {r: bool state | r IN dc_random_states (SUC (SUC n)) /\
                      (dcprog (SUC (SUC (SUC n)))
                        (((\s. s = STRCAT "pays" (toString i)),(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}
                        {r:bool state | r IN dc_random_states (SUC (SUC n)) /\
                      ~(dcprog (SUC (SUC (SUC n)))
                        (((\s. s = STRCAT "pays" (toString i)),(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`
                by (RW_TAC std_ss [DISJOINT_DEF]
                    >> ONCE_REWRITE_TAC [EXTENSION]
                    >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, DISJOINT_DEF, NOT_IN_EMPTY] >> DECIDE_TAC)
             >> `FINITE {r: bool state | r IN dc_random_states (SUC (SUC n)) /\
                      (dcprog (SUC (SUC (SUC n)))
                        (((\s. s = STRCAT "pays" (toString i)),(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')} /\
                 FINITE {r:bool state | r IN dc_random_states (SUC (SUC n)) /\
                      ~(dcprog (SUC (SUC (SUC n)))
                        (((\s. s = STRCAT "pays" (toString i)),(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`
                by (CONJ_TAC
                    >> (MATCH_MP_TAC o
                        REWRITE_RULE [dc_random_states_finite] o
                        Q.ISPEC `dc_random_states (SUC (SUC n))`) SUBSET_FINITE
                    >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
               >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION]
               >> (MP_TAC o Q.ISPEC `0:real` o
                   Q.ISPEC `(λ(r :bool state). (if dcprog (SUC (SUC (SUC (n :num))))
                                                    (FST (s' :(bool, bool, bool) prog_state),r) =
                                                    dcprog (SUC (SUC (SUC n))) s'
                                                then (1 : real) else (0 : real)))` o
                   UNDISCH o Q.ISPEC `{r:bool state | r IN dc_random_states (SUC (SUC n)) /\
                      ~(dcprog (SUC (SUC (SUC n)))
                        (((\s. s = STRCAT "pays" (toString i)),(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`)
                   REAL_SUM_IMAGE_FINITE_CONST2
               >> SIMP_TAC std_ss [GSPECIFICATION]
               >> `FST s' = ((\s. s = STRCAT "pays" (toString i)),(\s. F))`
                by (CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM PAIR])) >> RW_TAC std_ss [])
               >> POP_ORW
               >> RW_TAC real_ss []
               >> POP_ASSUM (K ALL_TAC)
               >> (MP_TAC o Q.ISPEC `1:real` o
                   Q.ISPEC `(λ(r :bool state). (if dcprog (SUC (SUC (SUC (n :num))))
                                                    (FST (s' :(bool, bool, bool) prog_state),r) =
                                                    dcprog (SUC (SUC (SUC n))) s'
                                                then (1 : real) else (0 : real)))` o
                   UNDISCH o Q.ISPEC `{r:bool state | r IN dc_random_states (SUC (SUC n)) /\
                       (dcprog (SUC (SUC (SUC n)))
                        (((\s. s = STRCAT "pays" (toString i)),(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`)
                   REAL_SUM_IMAGE_FINITE_CONST2
               >> SIMP_TAC std_ss [GSPECIFICATION]
               >> `FST s' = ((\s. s = STRCAT "pays" (toString i)),(\s. F))`
                by (CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM PAIR])) >> RW_TAC std_ss [])
               >> POP_ORW
               >> RW_TAC real_ss []
               >> POP_ASSUM (K ALL_TAC)
               >> `dcprog (SUC (SUC (SUC n))) s' IN
                        IMAGE (λ(h,r). dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r))
                                (dc_high_states F (SUC (SUC (SUC n))) CROSS
                                dc_random_states (SUC (SUC n)))`
                        by (RW_TAC std_ss [IN_CROSS, IN_IMAGE, dc_high_states_def, IN_dc_high_states_set]
                            >> `s' = ((FST (FST s'), SND (FST s')), SND s')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW
                            >> Q.EXISTS_TAC `(FST(FST s'),SND s')`
                            >> ASM_SIMP_TAC bool_ss [] >> ASM_SIMP_TAC std_ss []
                            >> Q.EXISTS_TAC `i` >> RW_TAC std_ss [])
               >> (MP_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.SPECL [`n`, `i`,
                                      `dcprog (SUC (SUC (SUC n)))
                                        (s' :(bool, bool, bool) prog_state)`])
                   valid_coin_set_eq_valid_coin_assignment
               >> RW_TAC std_ss [valid_coin_assignment_eq_2_element_set, coin_assignment_set]
               >> RW_TAC set_ss [coin_assignment, FUN_EQ_THM, T_xor, xor_T, F_xor]
               >> METIS_TAC [])
   >> DISCH_TAC
   >> `!x. (\x.
           (λ(out,h,l).
              (\x. x * lg (1 / &(2 ** SUC (SUC (SUC n))) * x))
                (SIGMA
                   (\r.
                      if dcprog (SUC (SUC (SUC n))) ((h,l),r) = out then
                        1
                      else
                        0) (dc_random_states (SUC (SUC n))))) x) x =
        (λ(out,h,l).
              (\x. x * lg (1 / &(2 ** SUC (SUC (SUC n))) * x))
                (SIGMA
                   (\r.
                      if dcprog (SUC (SUC (SUC n))) ((h,l),r) = out then
                        1
                      else
                        0) (dc_random_states (SUC (SUC n))))) x` by METIS_TAC []
   >> POP_ORW
   >> POP_ORW
   >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF, dc_high_states_set_finite, dc_random_states_finite, dc_low_states_finite,
                     FINITE_CROSS, IMAGE_FINITE]
   >> (MP_TAC o Q.ISPEC `(IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,FST s))
      (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
       dc_random_states (SUC (SUC n))))`) REAL_SUM_IMAGE_FINITE_CONST
   >> RW_TAC std_ss [dc_high_states_set_finite, dc_random_states_finite, dc_low_states_finite,
                     FINITE_CROSS, IMAGE_FINITE]
   >> POP_ASSUM (MP_TAC o Q.SPECL [`(\x. 2 * lg (1 / & (2 ** SUC (SUC (SUC n))) * 2))`,
                                   `2 * lg (1 / & (2 ** SUC (SUC (SUC n))) * 2)`])
   >> RW_TAC real_ss []
   >> POP_ASSUM (K ALL_TAC)
   >> RW_TAC bool_ss [dc_prog_space_F_set_thm, unif_prog_space_leakage_computation_reduce,
                     dc_high_states_set_finite, dc_random_states_finite, dc_low_states_finite,
                     dc_states_cross_not_empty, CARD_dc_high_states_set, CARD_dc_low_states, CARD_dc_random_states,
                     FINITE_CROSS, IMAGE_FINITE]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,SND (FST s)))
      (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
       dc_random_states (SUC (SUC n))))`) REAL_SUM_IMAGE_IN_IF]
   >> ONCE_REWRITE_TAC [lg_times_compute_simp_lem]
   >> Know `(\x. (if x IN IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,SND (FST s)))
                        (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
                        dc_random_states (SUC (SUC n)))
             then (λ(out,l). (\x. x * lg (1 / & (SUC (SUC (SUC n)) * 2 ** SUC (SUC (SUC n))) * x))
                (SIGMA (λ(h,r). (if dcprog (SUC (SUC (SUC n))) ((h,l),r) = out then 1 else 0))
                 (dc_high_states_set (SUC (SUC n)) CROSS
                  dc_random_states (SUC (SUC n))))) x
             else 0)) =
        (\x. (if x IN IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,SND (FST s)))
                        (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
                        dc_random_states (SUC (SUC n)))
             then (\x. (&(2 * (SUC(SUC(SUC n))))) * lg (1 / & (SUC (SUC (SUC n)) * 2 ** SUC (SUC (SUC n))) *
                        (&(2 * (SUC(SUC(SUC n))))))) x
             else 0))`
   >- (ONCE_REWRITE_TAC [FUN_EQ_THM]
       >> RW_TAC std_ss [IN_IMAGE, IN_CROSS, IN_dc_high_states_set, dc_low_states_def, IN_SING]
       >> rename1 `SND (FST s') = (\s. F)`
            >> `FST s' = (FST (FST s'), SND (FST s'))` by RW_TAC std_ss [PAIR]
            >> POP_ORW
            >> RW_TAC std_ss []
            >> Suff `SIGMA (λ(h,r). (if dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r) =
                                        dcprog (SUC (SUC (SUC n))) s'
                                     then 1 else 0))
                        (dc_high_states_set (SUC (SUC n)) CROSS
                        dc_random_states (SUC (SUC n))) = & (2 * SUC (SUC (SUC n)))`
            >- RW_TAC real_ss []
            >> `(dc_high_states_set (SUC (SUC n)) CROSS dc_random_states (SUC (SUC n))) =
                 {(h:bool state, r: bool state) |
                        h IN dc_high_states_set (SUC (SUC n)) /\
                        r IN dc_random_states (SUC (SUC n)) /\
                      (dcprog (SUC (SUC (SUC n)))
                        ((h,(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')} UNION
                 {(h:bool state, r: bool state) |
                        h IN dc_high_states_set (SUC (SUC n)) /\
                        r IN dc_random_states (SUC (SUC n)) /\
                      ~(dcprog (SUC (SUC (SUC n)))
                        ((h,(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION, IN_CROSS]
                    >> EQ_TAC
                    >- (RW_TAC std_ss []
                        >> Cases_on `dcprog (SUC (SUC (SUC n))) ((FST x,(\s. F)),SND x) =
                                     dcprog (SUC (SUC (SUC n))) s'`
                        >- (DISJ1_TAC
                            >> Q.EXISTS_TAC `(FST x,SND x)`
                            >> RW_TAC std_ss [PAIR_EQ])
                        >> DISJ2_TAC
                        >> Q.EXISTS_TAC `(FST x,SND x)`
                        >> RW_TAC std_ss [PAIR_EQ])
                    >> RW_TAC std_ss []
                    >> POP_ASSUM MP_TAC
                    >> (MP_TAC o Q.ISPEC `x': bool state # bool state`) pair_CASES
                    >> RW_TAC bool_ss []
                    >> POP_ASSUM MP_TAC >> RW_TAC std_ss [])
             >> POP_ORW
             >> `DISJOINT {(h:bool state, r: bool state) |
                        h IN dc_high_states_set (SUC (SUC n)) /\
                        r IN dc_random_states (SUC (SUC n)) /\
                      (dcprog (SUC (SUC (SUC n)))
                        ((h,(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}
                 {(h:bool state, r: bool state) |
                        h IN dc_high_states_set (SUC (SUC n)) /\
                        r IN dc_random_states (SUC (SUC n)) /\
                      ~(dcprog (SUC (SUC (SUC n)))
                        ((h,(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`
                by (RW_TAC std_ss [DISJOINT_DEF]
                    >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, DISJOINT_DEF, NOT_IN_EMPTY]
                    >> Cases_on `(FST x) IN dc_high_states_set (SUC (SUC n)) /\
                                 (SND x) IN dc_random_states (SUC (SUC n)) /\
                                 (dcprog (SUC (SUC (SUC n))) ((FST x,(\s. F)),SND x) =
                                  dcprog (SUC (SUC (SUC n))) s')`
                    >- (DISJ2_TAC
                        >> RW_TAC std_ss []
                        >> (MP_TAC o Q.ISPEC `x': bool state # bool state`) pair_CASES
                        >> RW_TAC bool_ss [] >> RW_TAC std_ss []
                        >> reverse (Cases_on `(x = (q,r))`) >> RW_TAC std_ss []
                        >> FULL_SIMP_TAC std_ss [FST,SND])
                    >> DISJ1_TAC
                    >> RW_TAC std_ss []
                    >> (MP_TAC o Q.ISPEC `x': bool state # bool state`) pair_CASES
                    >> RW_TAC bool_ss [] >> RW_TAC std_ss []
                    >> reverse (Cases_on `(x = (q,r))`) >> RW_TAC std_ss []
                    >> FULL_SIMP_TAC std_ss [FST,SND])
             >> `FINITE {(h:bool state, r: bool state) |
                        h IN dc_high_states_set (SUC (SUC n)) /\
                        r IN dc_random_states (SUC (SUC n)) /\
                      (dcprog (SUC (SUC (SUC n)))
                        ((h,(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')} /\
                 FINITE {(h:bool state, r: bool state) |
                        h IN dc_high_states_set (SUC (SUC n)) /\
                        r IN dc_random_states (SUC (SUC n)) /\
                      ~(dcprog (SUC (SUC (SUC n)))
                        ((h,(\s. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`
                by (CONJ_TAC
                    >> (MATCH_MP_TAC o
                        CONV_RULE (SIMP_CONV std_ss [dc_random_states_finite, dc_high_states_set_finite, FINITE_CROSS]) o
                        Q.ISPEC `(dc_high_states_set (SUC(SUC n))) CROSS
                                 (dc_random_states (SUC (SUC n)))`) SUBSET_FINITE
                    >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                    >> POP_ASSUM MP_TAC
                    >> (MP_TAC o Q.ISPEC `x': bool state # bool state`) pair_CASES
                    >> RW_TAC bool_ss []
                    >> POP_ASSUM MP_TAC >> RW_TAC std_ss [])
               >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION]
               >> `(!y. y IN {(h,r) | h IN dc_high_states_set (SUC (SUC n)) /\
                                       r IN dc_random_states (SUC (SUC n)) /\
                                       ~(dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r) =
                                         dcprog (SUC (SUC (SUC n))) s')} ==>
                        ((λ(h,r). (if dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r) =
                                      dcprog (SUC (SUC (SUC n))) s'
                                   then 1 else 0)) y = 0))`
                        by (RW_TAC std_ss [GSPECIFICATION]
                            >> (MP_TAC o Q.ISPEC `x: bool state # bool state`) pair_CASES
                            >> RW_TAC bool_ss [] >> FULL_SIMP_TAC std_ss [])
               >> ((fn thm => ONCE_REWRITE_TAC [thm]) o UNDISCH o Q.ISPEC `0:real` o
                   Q.ISPEC `(λ(h:bool state, r :bool state). (if dcprog (SUC (SUC (SUC (n :num))))
                                                    ((h, (\s:string. F)) ,r) =
                                                    dcprog (SUC (SUC (SUC n))) s'
                                                then (1 : real) else (0 : real)))` o
                   UNDISCH o Q.ISPEC `{(h:bool state, r: bool state) |
                        h IN dc_high_states_set (SUC (SUC n)) /\
                        r IN dc_random_states (SUC (SUC n)) /\
                      ~(dcprog (SUC (SUC (SUC n)))
                        ((h,(\s:string. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`)
                   REAL_SUM_IMAGE_FINITE_CONST2
               >> POP_ASSUM (K ALL_TAC) >> RW_TAC real_ss []
               >> `(!y. y IN {(h,r) | h IN dc_high_states_set (SUC (SUC n)) /\
                                       r IN dc_random_states (SUC (SUC n)) /\
                                       (dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r) =
                                         dcprog (SUC (SUC (SUC n))) s')} ==>
                        ((λ(h,r). (if dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r) =
                                      dcprog (SUC (SUC (SUC n))) s'
                                   then 1 else 0)) y = 1))`
                        by (RW_TAC std_ss [GSPECIFICATION]
                            >> (MP_TAC o Q.ISPEC `x: bool state # bool state`) pair_CASES
                            >> RW_TAC bool_ss [] >> FULL_SIMP_TAC std_ss [])
               >> ((fn thm => ONCE_REWRITE_TAC [thm]) o UNDISCH o Q.ISPEC `1:real` o
                   Q.ISPEC `(λ(h:bool state, r :bool state). (if dcprog (SUC (SUC (SUC (n :num))))
                                                    ((h, (\s:string. F)) ,r) =
                                                    dcprog (SUC (SUC (SUC n))) s'
                                                then (1 : real) else (0 : real)))` o
                   UNDISCH o Q.ISPEC `{(h:bool state, r: bool state) |
                        h IN dc_high_states_set (SUC (SUC n)) /\
                        r IN dc_random_states (SUC (SUC n)) /\
                      (dcprog (SUC (SUC (SUC n)))
                        ((h,(\s:string. F)),r) =
                        dcprog (SUC (SUC (SUC n))) s')}`)
                   REAL_SUM_IMAGE_FINITE_CONST2
               >> POP_ASSUM (K ALL_TAC) >> RW_TAC real_ss []
               >> `(dcprog (SUC (SUC (SUC n))) s') IN
                                IMAGE (λ(h,r). dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r))
                                        (dc_high_states F (SUC (SUC (SUC n))) CROSS
                                         dc_random_states (SUC (SUC n)))`
                                by (RW_TAC std_ss [IN_IMAGE, IN_CROSS, dc_high_states_def]
                                            >> Q.EXISTS_TAC `(FST(FST s'),SND s')`
                                            >> RW_TAC std_ss [IN_dc_high_states_set]
                                            >- (`s' = ((FST (FST s'), SND (FST s')), SND s')` by RW_TAC std_ss [PAIR]
                                                >> POP_ORW
                                                >> RW_TAC bool_ss [FST,SND])
                                            >> Q.EXISTS_TAC `i` >> RW_TAC std_ss [])
               >> `!h r.  (h IN dc_high_states_set (SUC (SUC n)) /\
                           r IN dc_random_states (SUC (SUC n))  /\
                         (dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r) =
                          dcprog (SUC (SUC (SUC n))) s')) =
                        (?p. p <= SUC (SUC n) /\ (h = (\s. s = STRCAT "pays" (toString p))) /\
                             r IN {r | r IN dc_random_states (SUC (SUC n))  /\
                          (dcprog (SUC (SUC (SUC n))) (((\s. s = STRCAT "pays" (toString p)),(\s. F)),r) =
                           dcprog (SUC (SUC (SUC n))) s')})`
                by (RW_TAC std_ss [IN_dc_high_states_set, GSPECIFICATION] >> EQ_TAC
                    >- (STRIP_TAC >> `(h = (\s. s = STRCAT "pays" (toString i')))` by METIS_TAC []
                        >> Q.EXISTS_TAC `i'` >> RW_TAC std_ss [])
                    >> RW_TAC std_ss [] >- (Q.EXISTS_TAC `p` >> RW_TAC std_ss []) >> ASM_REWRITE_TAC [])
               >> POP_ORW
               >> `!h r. (?p. p <= SUC (SUC n) /\ (h = (\s. s = STRCAT "pays" (toString p))) /\
                             r IN {r | r IN dc_random_states (SUC (SUC n))  /\
                          (dcprog (SUC (SUC (SUC n))) (((\s. s = STRCAT "pays" (toString p)),(\s. F)),r) =
                           dcprog (SUC (SUC (SUC n))) s')}) =
                          (?p.  p <= SUC (SUC n) /\
                                (h = (\s. s = STRCAT "pays" (toString p))) /\
                                r IN coin_assignment_set (dcprog (SUC (SUC (SUC n))) s') p n)`
                        by (REPEAT STRIP_TAC
                            >> EQ_TAC
                            >- (STRIP_TAC >> Q.EXISTS_TAC `p` >> ASM_REWRITE_TAC []
                                >> `{r | r IN dc_random_states (SUC (SUC n))  /\
                                         (dcprog (SUC (SUC (SUC n))) (((\s. s = STRCAT "pays" (toString p)),(\s. F)),r) =
                                          dcprog (SUC (SUC (SUC n))) s')} =
                                    {r | r IN dc_random_states (SUC (SUC n)) /\
                                         valid_coin_assignment r (dcprog (SUC (SUC (SUC n))) s') p n (SUC (SUC n))}`
                                        by (MATCH_MP_TAC valid_coin_set_eq_valid_coin_assignment
                                            >> ASM_REWRITE_TAC [])
                                >> FULL_SIMP_TAC std_ss []
                                >> Suff `{r | r IN dc_random_states (SUC (SUC n)) /\
                                                  valid_coin_assignment r (dcprog (SUC (SUC (SUC n))) s') p n (SUC (SUC n))} =
                                             coin_assignment_set (dcprog (SUC (SUC (SUC n))) s') p n`
                                >- (STRIP_TAC >> FULL_SIMP_TAC std_ss [])
                                >> MATCH_MP_TAC valid_coin_assignment_eq_2_element_set
                                >> ASM_REWRITE_TAC [])
                            >> STRIP_TAC >> Q.EXISTS_TAC `p` >> RW_TAC std_ss []
                            >> Suff `{r | r IN dc_random_states (SUC (SUC n)) /\
                                              (dcprog (SUC (SUC (SUC n))) (((\s. s = STRCAT "pays" (toString p)),(\s. F)),r) =
                                              (dcprog (SUC (SUC (SUC n))) s'))} =
                                                 coin_assignment_set (dcprog (SUC (SUC (SUC n))) s') p n`
                            >- (STRIP_TAC >> FULL_SIMP_TAC std_ss [])
                            >> ASM_SIMP_TAC std_ss [valid_coin_set_eq_valid_coin_assignment,
                                                    valid_coin_assignment_eq_2_element_set])
               >> POP_ORW
               >> RW_TAC std_ss [coin_assignment_set, IN_INSERT, NOT_IN_EMPTY]
               >> `{(h,r) | ?p. p <= SUC (SUC n) /\
                                (h = (\s. s = STRCAT "pays" (toString p))) /\
                                ((r = coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n T (SUC (SUC n))) \/
                                (r = coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n F (SUC (SUC n))))} =
                   {(h,r) | ?p. p <= SUC (SUC n) /\
                                (h = (\s. s = STRCAT "pays" (toString p))) /\
                                ((r = coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n T (SUC (SUC n))))} UNION
                   {(h,r) | ?p. p <= SUC (SUC n) /\
                                (h = (\s. s = STRCAT "pays" (toString p))) /\
                                ((r = coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n F (SUC (SUC n))))}`
                 by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION] >> RW_TAC std_ss [GSYM EXTENSION]
                     >> EQ_TAC
                     >- (STRIP_TAC >> (ASSUME_TAC o Q.ISPEC `x':bool state # bool state`) pair_CASES
                         >> FULL_SIMP_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
                         >- (DISJ1_TAC >> Q.EXISTS_TAC `(q,r)` >> RW_TAC std_ss []
                             >> `(?p'. p' <= SUC (SUC n) /\
                                        ((\s. s = STRCAT "pays" (toString p)) =
                                         (\s. s = STRCAT "pays" (toString p'))) /\
                                (coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n T (SUC (SUC n)) =
                                 coin_assignment (dcprog (SUC (SUC (SUC n))) s') p' n T (SUC (SUC n)))) = T`
                                by (RW_TAC std_ss [] >> Q.EXISTS_TAC `p` >> RW_TAC std_ss [])
                             >> POP_ORW
                             >> RW_TAC std_ss [] >> Q.EXISTS_TAC `p`
                             >> RW_TAC std_ss [])
                         >> DISJ2_TAC >> Q.EXISTS_TAC `(q,r)` >> RW_TAC std_ss []
                         >> `(?p'. p' <= SUC (SUC n) /\
                                ((\s. s = STRCAT "pays" (toString p)) =
                                 (\s. s = STRCAT "pays" (toString p'))) /\
                                (coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n F (SUC (SUC n)) =
                                 coin_assignment (dcprog (SUC (SUC (SUC n))) s') p' n F (SUC (SUC n)))) = T`
                                by (RW_TAC std_ss [] >> Q.EXISTS_TAC `p` >> RW_TAC std_ss [])
                         >> POP_ORW
                         >> RW_TAC std_ss [] >> Q.EXISTS_TAC `p`
                         >> RW_TAC std_ss [])
                     >> STRIP_TAC
                     >- ((ASSUME_TAC o Q.ISPEC `x':bool state # bool state`) pair_CASES
                         >> FULL_SIMP_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
                         >> Q.EXISTS_TAC `(q,r)` >> RW_TAC std_ss []
                         >> `(?p'. p' <= SUC (SUC n) /\
                        ((\s. s = STRCAT "pays" (toString p)) =
                        (\s. s = STRCAT "pays" (toString p'))) /\
                        (coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n T (SUC (SUC n)) =
                         coin_assignment (dcprog (SUC (SUC (SUC n))) s') p' n T (SUC (SUC n)))) = T`
                        by (RW_TAC std_ss [] >> Q.EXISTS_TAC `p` >> RW_TAC std_ss [])
                         >> POP_ORW
                         >> RW_TAC std_ss [] >> Q.EXISTS_TAC `p`
                         >> RW_TAC std_ss [])
                     >> (ASSUME_TAC o Q.ISPEC `x':bool state # bool state`) pair_CASES
                     >> FULL_SIMP_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
                     >> Q.EXISTS_TAC `(q,r)` >> RW_TAC std_ss []
                     >> `(?p'. p' <= SUC (SUC n) /\
                        ((\s. s = STRCAT "pays" (toString p)) =
                        (\s. s = STRCAT "pays" (toString p'))) /\
                        (coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n F (SUC (SUC n)) =
                         coin_assignment (dcprog (SUC (SUC (SUC n))) s') p' n F (SUC (SUC n)))) = T`
                        by (RW_TAC std_ss [] >> Q.EXISTS_TAC `p` >> RW_TAC std_ss [])
                     >> POP_ORW
                     >> RW_TAC std_ss [] >> Q.EXISTS_TAC `p`
                     >> RW_TAC std_ss [])
               >> POP_ORW
               >> `!b. {(h,r) | ?p. p <= SUC (SUC n) /\
                                (h = (\s. s = STRCAT "pays" (toString p))) /\
                                (r = coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n b (SUC (SUC n)))} =
                        IMAGE (\p:num. ((\s:string. s = STRCAT "pays" (toString p)),
                        coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n b (SUC (SUC n))))
                        (pred_set$count (SUC(SUC(SUC n))))`
                by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_IMAGE, pred_setTheory.IN_COUNT]
                    >> RW_TAC std_ss [GSYM EXTENSION]
                    >> EQ_TAC >- (STRIP_TAC >> (ASSUME_TAC o Q.ISPEC `x':bool state # bool state`) pair_CASES
                                  >> FULL_SIMP_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
                                  >> Q.EXISTS_TAC `p` >> FULL_SIMP_TAC arith_ss [])
                    >> STRIP_TAC >> Q.EXISTS_TAC `x` >> RW_TAC std_ss [PAIR_EQ] >> Q.EXISTS_TAC `p`
                    >> FULL_SIMP_TAC arith_ss [])
               >> POP_ORW >> RW_TAC std_ss [IMAGE_UNION]
               >> (ASSUME_TAC o Q.ISPEC `IMAGE (\p. (((\s. s = STRCAT "pays" (toString p))),
                        coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n T (SUC (SUC n))))
                                (pred_set$count (SUC (SUC (SUC n))))`) CARD_UNION
               >> FULL_SIMP_TAC std_ss [IMAGE_FINITE, pred_setTheory.FINITE_COUNT]
               >> POP_ASSUM (ASSUME_TAC o Q.ISPEC `IMAGE (\p. (((\s. s = STRCAT "pays" (toString p))),
                        coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n F (SUC (SUC n))))
                                (pred_set$count (SUC (SUC (SUC n))))`)
               >> FULL_SIMP_TAC std_ss [IMAGE_FINITE, pred_setTheory.FINITE_COUNT]
               >> `(IMAGE (\p.
                  (((\s. s = STRCAT "pays" (toString p))),
                   coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n T (SUC (SUC n))))
                        (pred_set$count (SUC (SUC (SUC n)))) INTER
                    IMAGE (\p.
                  (((\s. s = STRCAT "pays" (toString p))),
                   coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n F (SUC (SUC n))))
                        (pred_set$count (SUC (SUC (SUC n))))) = {}`
                by (RW_TAC std_ss [EXTENSION, INTER_DEF, IN_IMAGE, NOT_IN_EMPTY, pred_setTheory.IN_COUNT, GSPECIFICATION]
                    >> Cases_on `(!p.  ~(x = (((\s. s = STRCAT "pays" (toString p))),
                                coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n T (SUC (SUC n)))) \/
                                ~(p < SUC (SUC (SUC n))))`
                    >> ASM_REWRITE_TAC [] >> FULL_SIMP_TAC std_ss []
                    >> RW_TAC std_ss [] >> reverse (Cases_on `p' < SUC (SUC (SUC n))`) >> ASM_REWRITE_TAC []
                    >> reverse (Cases_on `((\s. s = STRCAT "pays" (toString p)) =
                                  (\s. s = STRCAT "pays" (toString p')))`) >> ASM_REWRITE_TAC []
                    >> `p' = p` by METIS_TAC [STRCAT_toString_inj]
                    >> ASM_SIMP_TAC arith_ss [coin_assignment_result3, LESS_EQ_REFL])
               >> FULL_SIMP_TAC std_ss [CARD_EMPTY] >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (K ALL_TAC)
               >> `!b. CARD (IMAGE (\p. (((\s. s = STRCAT "pays" (toString p))),
                        coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n b (SUC (SUC n))))
                        (pred_set$count (SUC (SUC (SUC n))))) = CARD (pred_set$count (SUC (SUC (SUC n))))`
                by (STRIP_TAC
                    >> (MATCH_MP_TAC o REWRITE_RULE [pred_setTheory.FINITE_COUNT] o
                        Q.ISPECL [`(\p. (((\s. s = STRCAT "pays" (toString p))),
                                        coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n b
                                        (SUC (SUC n))))`,
                                  `(pred_set$count (SUC (SUC (SUC (n:num)))))`,
                                  `IMAGE (\p. (((\s. s = STRCAT "pays" (toString p))),
                                                coin_assignment (dcprog (SUC (SUC (SUC n))) s') p n b
                                                (SUC (SUC n))))
                                         (pred_set$count (SUC (SUC (SUC (n:num)))))`]) CARD_IMAGE
                     >> RW_TAC std_ss [INJ_DEF, pred_setTheory.IN_COUNT, PAIR_EQ, IN_IMAGE]
                     >> METIS_TAC [STRCAT_toString_inj])
               >> POP_ORW >> RW_TAC arith_ss [pred_setTheory.CARD_COUNT])
   >> DISCH_TAC
   >> `!x. (\x.
           (λ(out,l).
              (\x.
                 x *
                 lg
                   (1 / &(SUC (SUC (SUC n)) * 2 ** SUC (SUC (SUC n))) *
                    x))
                (SIGMA
                   (λ(h,r).
                      if dcprog (SUC (SUC (SUC n))) ((h,l),r) = out then
                        1
                      else
                        0)
                   (dc_high_states_set (SUC (SUC n)) CROSS
                    dc_random_states (SUC (SUC n))))) x) x =
        (λ(out,l).
              (\x.
                 x *
                 lg
                   (1 / &(SUC (SUC (SUC n)) * 2 ** SUC (SUC (SUC n))) *
                    x))
                (SIGMA
                   (λ(h,r).
                      if dcprog (SUC (SUC (SUC n))) ((h,l),r) = out then
                        1
                      else
                        0)
                   (dc_high_states_set (SUC (SUC n)) CROSS
                    dc_random_states (SUC (SUC n))))) x`
        by METIS_TAC []
   >> POP_ORW
   >> POP_ORW
   >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF, dc_high_states_set_finite, dc_random_states_finite, dc_low_states_finite,
                     FINITE_CROSS, IMAGE_FINITE]
   >> (MP_TAC o Q.ISPEC `(IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,SND (FST s)))
      (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
       dc_random_states (SUC (SUC n))))`) REAL_SUM_IMAGE_FINITE_CONST
   >> RW_TAC std_ss [dc_high_states_set_finite, dc_random_states_finite, dc_low_states_finite,
                     FINITE_CROSS, IMAGE_FINITE]
   >> POP_ASSUM (MP_TAC o Q.SPECL [`(\x. & (2 * SUC (SUC (SUC n))) *
                                        lg (1 / & (SUC (SUC (SUC n)) * 2 ** SUC (SUC (SUC n))) *
                                        & (2 * SUC (SUC (SUC n)))))`,
                                   `& (2 * SUC (SUC (SUC n))) *
                                        lg (1 / & (SUC (SUC (SUC n)) * 2 ** SUC (SUC (SUC n))) *
                                        & (2 * SUC (SUC (SUC n))))`])
   >> RW_TAC real_ss []
   >> POP_ASSUM (K ALL_TAC)
   >> Suff `& (CARD
      (IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,FST s))
         (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
          dc_random_states (SUC (SUC n))))) * (2 * lg (1 / & (2 ** SUC (SUC (SUC n))) * 2)) =
        & (CARD
      (IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,SND (FST s)))
         (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
          dc_random_states (SUC (SUC n))))) * (& (2 * SUC (SUC (SUC n))) *
        lg (1 / & (SUC (SUC (SUC n)) * 2 ** SUC (SUC (SUC n))) *
        & (2 * SUC (SUC (SUC n)))))`
   >- RW_TAC real_ss []
   >> Know `(IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,SND (FST s)))
        (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
         dc_random_states (SUC (SUC n)))) =
        (IMAGE (λ(h,r). dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r))
          (dc_high_states F (SUC (SUC (SUC n))) CROSS
           dc_random_states (SUC (SUC n)))) CROSS dc_low_states`
   >- (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_IMAGE, dc_low_states_def, IN_SING]
       >> EQ_TAC
            >- (RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
                >> rename1 `SND (FST s') = (\s. F)`
                >> Q.EXISTS_TAC `(FST (FST s'), SND s')`
                >> RW_TAC bool_ss [FST,SND, dc_high_states_def]
                >> RW_TAC std_ss []
                >> `s' = ((FST (FST s'), SND (FST s')), SND s')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC bool_ss [FST, SND])
            >> RW_TAC std_ss [dc_high_states_def] >> RW_TAC std_ss [FST,SND]
            >> Q.EXISTS_TAC `((FST x', (\s:string.F)),SND x')`
            >> RW_TAC std_ss [] >> CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM PAIR]))
            >> ASM_SIMP_TAC bool_ss [PAIR_EQ]
            >> `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
            >> POP_ORW >> RW_TAC bool_ss [FST,SND] >> RW_TAC std_ss [])
   >> Rewr'
   >> Know `IMAGE (\s. (dcprog (SUC (SUC (SUC n))) s,FST s))
        (dc_high_states_set (SUC (SUC n)) CROSS dc_low_states CROSS
         dc_random_states (SUC (SUC n))) =
             (IMAGE (λ(h,r). dcprog (SUC (SUC (SUC n))) ((h,(\s:string. F)),r))
          (dc_high_states F (SUC (SUC (SUC n))) CROSS
           dc_random_states (SUC (SUC n)))) CROSS ((dc_high_states_set (SUC (SUC n)) CROSS dc_low_states))`
   >- (ONCE_REWRITE_TAC [EXTENSION]
       >> RW_TAC std_ss [dc_low_states_def, dc_high_states_def, IN_CROSS, IN_SING, IN_IMAGE]
       >> EQ_TAC
            >- (RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [FST, SND]
                >> rename1 `SND (FST s') = (\s. F)`
                >> Q.EXISTS_TAC `(FST (FST s'),SND s')`
                >> RW_TAC std_ss [FST, SND, dc_high_states_def]
                >- (POP_ASSUM (K ALL_TAC) >> POP_ASSUM (MP_TAC o GSYM) >> RW_TAC bool_ss [PAIR])
                >> FULL_SIMP_TAC std_ss [IN_dc_random_states]
                >> RW_TAC std_ss []
                >> Q.PAT_X_ASSUM `!x. P ==> ~SND s' x` MATCH_MP_TAC
                >> METIS_TAC [DECIDE ``!(i:num) (n:num). i <= n ==> i <= SUC n``])
            >> RW_TAC std_ss [IN_dc_high_states_set]
            >> REPEAT (POP_ASSUM MP_TAC)
            >> ONCE_REWRITE_TAC [(DECIDE ``(x' :bool state # bool state) = (FST x', SND x')``)]
            >> RW_TAC std_ss [FST, SND]
            >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR]
            >> POP_ORW
            >> RW_TAC bool_ss [PAIR_EQ]
            >> Q.ABBREV_TAC `r = coin_assignment (dcprog (SUC (SUC (SUC n))) ((FST x',(\s:string. F)),SND x'))
                                                i' n T (SUC(SUC n))`
            >> Q.ABBREV_TAC `out = dcprog (SUC (SUC (SUC n))) (((\s. s = STRCAT "pays" (toString i)),(\s:string. F)),SND x')`
            >> `out IN (IMAGE (λ(h,r). dcprog (SUC (SUC (SUC n))) ((h,(\s. F)),r))
                             (dc_high_states F (SUC (SUC (SUC n))) CROSS dc_random_states (SUC (SUC n))))`
                by (Q.UNABBREV_TAC `out`
                    >> RW_TAC std_ss [IN_IMAGE, IN_CROSS, dc_high_states_def, IN_dc_high_states_set, dc_low_states_def, IN_SING]
                    >> Q.EXISTS_TAC `((\s. s = STRCAT "pays" (toString i)),SND x')`
                    >> RW_TAC std_ss [FST,SND] >> Q.EXISTS_TAC `i` >> RW_TAC std_ss [])
            >> `r IN {r:bool state| r IN (dc_random_states (SUC (SUC n))) /\
                                    (dcprog (SUC(SUC(SUC n))) (((\s. s = STRCAT "pays" (toString i')), (\s:string. F)), r)=out)}`
                by (RW_TAC std_ss [valid_coin_set_eq_valid_coin_assignment, valid_coin_assignment_eq_2_element_set,
                                   coin_assignment_set]
                    >> Q.UNABBREV_TAC `r`
                    >> ASM_SIMP_TAC set_ss [])
            >> `SND x = (FST(SND x),SND(SND x))` by RW_TAC std_ss [PAIR]
            >> POP_ORW
            >> Q.EXISTS_TAC `(((\s. s = STRCAT "pays" (toString i')),(\s:string.F)),r)`
            >> RW_TAC bool_ss [FST,SND] >> FULL_SIMP_TAC std_ss [GSPECIFICATION]
            >> Q.EXISTS_TAC `i'` >> ASM_REWRITE_TAC [])
   >> RW_TAC std_ss [CARD_CROSS, dc_high_states_set_finite, dc_random_states_finite, dc_low_states_finite,
                      FINITE_CROSS, IMAGE_FINITE, CARD_dc_low_states, dc_high_states_def, CARD_dc_high_states_set,
                      REWRITE_RULE [dc_high_states_def] CARD_dc_valid_outputs]
   >> `~(2 ** SUC (SUC (SUC n)) = 0)` by RW_TAC arith_ss [EXP_EQ_0]
   >> `~(2 ** (SUC (SUC n)) = 0)` by RW_TAC arith_ss [EXP_EQ_0]
   >> `~(2 pow (SUC (SUC n)) = 0)`
                by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC REAL_LT_IMP_NE
                    >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&((SUC(SUC n)))` >> RW_TAC real_ss [POW_2_LT])
   >> `~(2 pow (SUC(SUC (SUC n))) = 0)`
                by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC REAL_LT_IMP_NE
                    >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&((SUC(SUC(SUC n))))` >> RW_TAC real_ss [POW_2_LT])
   >> RW_TAC std_ss [GSYM REAL_MUL]
   >> RW_TAC real_ss [GSYM REAL_INV_1OVER, REAL_INV_MUL, real_div, REAL_INV_INV, GSYM REAL_OF_NUM_POW,
                           lg_mul, REAL_INV_EQ_0, REAL_INV_MUL]
   >> RW_TAC std_ss [GSYM REAL_MUL]
   >> RW_TAC std_ss [GSYM REAL_OF_NUM_POW]
   >> Suff `lg (inv (& (SUC (SUC (SUC n)))) * inv (2 pow SUC (SUC (SUC n))) *
                 (2 * & (SUC (SUC (SUC n))))) = lg (inv (2 pow SUC (SUC (SUC n))) * 2)`
   >- (RW_TAC std_ss [] >> REAL_ARITH_TAC)
   >> `inv (& (SUC (SUC (SUC n)))) * inv (2 pow SUC (SUC (SUC n))) * (2 * & (SUC (SUC (SUC n)))) =
            (& (SUC (SUC (SUC n))) * inv (& (SUC (SUC (SUC n))))) * inv (2 pow SUC (SUC (SUC n))) * 2`
                by REAL_ARITH_TAC
   >> POP_ORW >> RW_TAC real_ss [REAL_MUL_RINV]);

(* ************************************************************************* *)
(* Case Study: The Dining Cryptographers - From the view of a cryptographer  *)
(* for the sake of simplicity, assume crypto 0 is observing ant he has not   *)
(* paid. this is fine because the ring is symmetric and the numbering is     *)
(* arbitrary.                                                                *)
(* ************************************************************************* *)

val insider_high_states_set_def = Define
  `(insider_high_states_set (0:num) = {}) /\
   (insider_high_states_set (SUC n) = (\s:string. s = (STRCAT "pays" (toString (SUC n))))
                                      INSERT (insider_high_states_set n))`;

val insider_high_states_def = Define
   `insider_high_states nsapays (SUC(SUC n)) =
     if nsapays then {(\s: string. s = STRCAT "pays" (toString (SUC(SUC n))))}
     else insider_high_states_set (SUC n)`;

val insider_low_states_def = Define
   `insider_low_states = {(\s:string. s = (STRCAT "coin" (toString 0))); (\s:string. F)}`;

val insider_random_states_def = Define
  `(insider_random_states (0:num) = {(\s:string. F)}) /\
   (insider_random_states (SUC n) =
     (IMAGE (\s:bool state. (\x:string. if x = (STRCAT "coin" (toString (SUC n))) then T
                                        else s x))
            (insider_random_states n)) UNION
     (IMAGE (\s:bool state. (\x:string. if x = (STRCAT "coin" (toString (SUC n))) then F
                                        else s x))
            (insider_random_states n)))`;

val insider_set_announcements_def = Define
  `(insider_set_announcements (high: bool state) (low:bool state)
                              (random:bool state) (n:num) (0:num) (s:string) =
       if (s = (STRCAT "announces" (toString 0))) then
          ((high (STRCAT "pays" (toString 0)))) xor
          ((low (STRCAT "coin" (toString 0))) xor (random (STRCAT "coin" (toString n))))
       else low s) /\
   (insider_set_announcements (high: bool state) (low:bool state)
                              (random:bool state) (n:num) (SUC(0:num)) (s:string) =
       if (s = (STRCAT "announces" (toString (SUC 0)))) then
          ((high (STRCAT "pays" (toString (SUC 0))))) xor
          ((random (STRCAT "coin" (toString (SUC 0)))) xor (low (STRCAT "coin" (toString 0))))
       else
          (insider_set_announcements high low random n 0) s) /\
   (insider_set_announcements high low random n (SUC (SUC i)) s =
       if (s = (STRCAT "announces" (toString (SUC (SUC i))))) then
          ((high (STRCAT "pays" (toString (SUC (SUC i)))))) xor
          ((random (STRCAT "coin" (toString (SUC (SUC i))))) xor
           (random (STRCAT "coin" (toString (SUC i)))))
       else
          (insider_set_announcements high low random n (SUC i)) s)`;

val insider_set_announcements_alt = store_thm
  ("insider_set_announcements_alt",
   ``!high low random n i.
      (insider_set_announcements high low random n 0 =
         (\s. if (s = (STRCAT "announces" (toString 0))) then
                 ((high (STRCAT "pays" (toString 0)))) xor
                 ((low (STRCAT "coin" (toString 0))) xor (random (STRCAT "coin" (toString n))))
              else low s)) /\
      (insider_set_announcements high low random n (SUC 0) =
         (\s. if (s = (STRCAT "announces" (toString (SUC 0)))) then
                 ((high (STRCAT "pays" (toString (SUC 0))))) xor
                 ((random (STRCAT "coin" (toString (SUC 0)))) xor (low (STRCAT "coin" (toString 0))))
              else
                 (insider_set_announcements high low random n 0) s)) /\
      (insider_set_announcements high low random n (SUC(SUC i)) =
         (\s. if (s = (STRCAT "announces" (toString (SUC(SUC i))))) then
                 ((high (STRCAT "pays" (toString (SUC(SUC i)))))) xor
                 ((random (STRCAT "coin" (toString (SUC(SUC i))))) xor
                  (random (STRCAT "coin" (toString (SUC i)))))
              else
                 (insider_set_announcements high low random n (SUC i)) s))``,
     RW_TAC std_ss [FUN_EQ_THM, insider_set_announcements_def]);

val insider_dcprog_def = Define
   `insider_dcprog (SUC(SUC(SUC n))) =
      (λ((high:bool state, low:bool state), random:bool state).
         compute_result (insider_set_announcements high low random (SUC(SUC n)) (SUC(SUC n)))
                        (SUC(SUC n)))`;

val insider_dc_prog_space_def = Define
   `insider_dc_prog_space (SUC(SUC n)) nsapays =
    unif_prog_space
      (insider_high_states nsapays (SUC(SUC n)))
      insider_low_states
      (insider_random_states (SUC n))`;

val insider_dc_prog_space_F_set_thm = store_thm
  ("insider_dc_prog_space_F_set_thm",
   ``!n. insider_dc_prog_space (SUC(SUC n)) F =
         unif_prog_space (insider_high_states_set (SUC n))
                         insider_low_states
                         (insider_random_states (SUC n))``,
   RW_TAC std_ss [insider_dc_prog_space_def, insider_high_states_def]);

(* ------------------------------------------------------------------------- *)

val hl_dups_lemma = prove
   (``!(s1:string)(s2:string). ((\x. x = s1) = (\x. x = s2)) = (s1=s2)``,
    METIS_TAC []);

val hl_dups_lemma2 = prove
   (``!(s:string). ~((\x. x = s) = (\x. F))``,
    METIS_TAC []);

val fun_eq_lem6 = METIS_PROVE []
  ``!x a b P Q. (x = a) \/ ~ (x = b) /\ P <=> (a = b) /\ ((x = a) \/ P) \/ ~(x = b) /\ ((x = a) \/ P)``;

fun insider_input_unroll (remove_dups_conv:Abbrev.term->Abbrev.thm) =
   (REPEATC (SIMP_CONV bool_ss [insider_high_states_set_def,
                                insider_low_states_def, insider_random_states_def,
                                CARD_DEF, FINITE_INSERT, FINITE_EMPTY, FINITE_SING,
                                IMAGE_UNION, IMAGE_IMAGE, combinTheory.o_DEF, IMAGE_INSERT, IMAGE_EMPTY,
                                INSERT_UNION, UNION_EMPTY, IN_UNION]
   THENC (FIND_CONV ``x IN y`` (IN_CONV remove_dups_conv)
          THENC SIMP_CONV bool_ss [])
   THENC SIMP_CONV arith_ss []));

val dc_dup_conv =
    SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
    THENC EVAL
    THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
    THENC EVAL
    THENC (REPEATC (T_F_UNCHANGED_CONV
                    (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                     THENC EVAL)));

val insider_hl_dup_conv = SIMP_CONV arith_ss [hl_dups_lemma, hl_dups_lemma2, STRCAT_toString_inj];

val insider_dc3_leakage_result = store_thm
  ("insider_dc3_leakage_result",
   ``leakage (insider_dc_prog_space (SUC (SUC (SUC 0))) F) (insider_dcprog (SUC(SUC(SUC 0)))) = 0``,
   CONV_TAC (SIMP_CONV bool_ss [insider_dc_prog_space_F_set_thm] THENC
             RATOR_CONV (RAND_CONV (
             LEAKAGE_COMPUTE_CONV (``insider_high_states_set (SUC(SUC 0))``,
                                   ``insider_low_states``,``insider_random_states (SUC(SUC 0))``)
              [insider_high_states_set_def, insider_low_states_def, insider_random_states_def]
              [insider_dcprog_def, compute_result_alt, XOR_announces_def,
               insider_set_announcements_alt, FST, SND, xor_def]
              (insider_input_unroll insider_hl_dup_conv)
              (insider_input_unroll insider_hl_dup_conv)
              (insider_input_unroll dc_dup_conv)
               insider_hl_dup_conv insider_hl_dup_conv dc_dup_conv dc_dup_conv))
             THENC SIMP_CONV real_ss [REAL_ADD_ASSOC, GSYM REAL_NEG_ADD,
                                      GSYM REAL_ADD_RDISTRIB, REAL_MUL_ASSOC])
>> RW_TAC real_ss [lg_1, lg_inv, GSYM REAL_INV_1OVER]
>> `lg 4 = 2` by (`4 = 2 pow 2` by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> RW_TAC real_ss []);

(* ************************************************************************* *)
(* Case Study: The Dining Cryptographers - Biased coins                      *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(* Tampering w/ a visible coin doesn't create a leak                         *)
(* ************************************************************************* *)

val biased_high_states_def = Define
   `biased_high_states n = insider_high_states_set n`;

val biased_low_states_def = Define
   `biased_low_states = {(\s:string. s = (STRCAT "coin" (toString 0))); (\s:string. F)}`;

val biased_random_states_def = Define
   `(biased_random_states (0:num) = {(\s:string. F)}) /\
    (biased_random_states (SUC n) = (IMAGE (\s:bool state.
                                              (\x:string. if x = (STRCAT "coin" (toString (SUC n))) then
                                                                T
                                                          else s x))
                                          (biased_random_states n))
                                        UNION
                                     (IMAGE (\s:bool state.
                                              (\x:string. if x = (STRCAT "coin" (toString (SUC n))) then
                                                                F
                                                          else s x))
                                          (biased_random_states n)))`;

val biased_dist_def = Define
   `biased_dist high low random =
        (\s. if L s = (\s:string. s = (STRCAT "coin" (toString 0))) then
                (1 / 2) * (unif_prog_dist high low random s)
             else
                (3 / 2) * (unif_prog_dist high low random s))`;

val biased_dc_prog_space_def = Define
   `biased_dc_prog_space (SUC(SUC n)) =
        (((biased_high_states (SUC(SUC n))) CROSS biased_low_states) CROSS (biased_random_states (SUC (SUC n))),
         POW (((biased_high_states (SUC(SUC n))) CROSS biased_low_states) CROSS (biased_random_states (SUC (SUC n)))),
         (\s. SIGMA (biased_dist (biased_high_states (SUC(SUC n))) biased_low_states (biased_random_states (SUC (SUC n)))) s))`;

val prob_space_biased_dc_prog_space3 = store_thm
  ("prob_space_biased_dc_prog_space3",
   ``prob_space (biased_dc_prog_space (SUC(SUC 0)))``,
   (RW_TAC bool_ss [prob_space_def]
    >> `FINITE ((biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0))))`
        by RW_TAC set_ss [biased_high_states_def, biased_low_states_def,
                             biased_random_states_def, insider_high_states_set_def])
   >- (MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces2
       >> RW_TAC bool_ss [biased_dc_prog_space_def, m_space_def, measurable_sets_def, POW_SIGMA_ALGEBRA,
                          PSPACE, measure_def, positive_def, REAL_SUM_IMAGE_THM, IN_POW,
                          additive_def, IN_FUNSET, IN_UNIV]
       >- (MATCH_MP_TAC REAL_SUM_IMAGE_POS
           >> CONJ_TAC
           >- METIS_TAC [SUBSET_FINITE]
           >> RW_TAC real_ss [biased_dist_def, unif_prog_dist_def, GSYM REAL_INV_1OVER, REAL_LE_INV_EQ, REAL_LE_MUL])
       >> METIS_TAC [SUBSET_FINITE, REAL_SUM_IMAGE_DISJOINT_UNION])
   >> RW_TAC bool_ss [biased_dc_prog_space_def, m_space_def, measurable_sets_def,
                      PSPACE, measure_def, biased_dist_def]
   >> `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0))) =
        (((biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
         biased_random_states (SUC (SUC 0))))INTER
         {s| L s = (\s. s = STRCAT "coin" (toString 0))}) UNION
        (((biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0))))INTER{s| ~(L s = (\s. s = STRCAT "coin" (toString 0)))})`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_INTER, GSPECIFICATION] >> DECIDE_TAC)
   >> POP_ORW
   >> `FINITE (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | L s = (\s. s = STRCAT "coin" (toString 0))}) /\
        FINITE (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | ~(L s = (\s. s = STRCAT "coin" (toString 0)))})`
        by RW_TAC std_ss [INTER_FINITE]
   >> `DISJOINT (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | L s = (\s. s = STRCAT "coin" (toString 0))})
        (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | ~(L s = (\s. s = STRCAT "coin" (toString 0)))})`
        by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
            >> DECIDE_TAC)
   >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION]
   >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF, unif_prog_dist_def]
   >> `(\s.
     (if
        s IN
        biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | L s = (\s. s = STRCAT "coin" (toString 0))}
      then
        (if L s = (\s. s = STRCAT "coin" (toString 0)) then
           1 / 2 *
           (if
              s IN
              biased_high_states (SUC (SUC 0)) CROSS
              biased_low_states CROSS biased_random_states (SUC (SUC 0))
            then
              1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0))))
            else
              0)
         else
           3 / 2 *
           (if
              s IN
              biased_high_states (SUC (SUC 0)) CROSS
              biased_low_states CROSS biased_random_states (SUC (SUC 0))
            then
              1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0))))
            else
              0))
      else
        0)) =
        (\s. (if s IN
        biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | L s = (\s. s = STRCAT "coin" (toString 0))}
      then
        (\s. 1 / 2 * (1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0)))))) s
      else 0))`
        by (ONCE_REWRITE_TAC [FUN_EQ_THM]
            >> RW_TAC bool_ss [IN_INTER, GSPECIFICATION])
   >> POP_ORW
   >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> RW_TAC bool_ss [REAL_SUM_IMAGE_FINITE_CONST3]
   >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
   >> `(\s.
     (if
        s IN
        biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | ~(L s = (\s. s = STRCAT "coin" (toString 0)))}
      then
        (if L s = (\s. s = STRCAT "coin" (toString 0)) then
           1 / 2 *
           (if
              s IN
              biased_high_states (SUC (SUC 0)) CROSS
              biased_low_states CROSS biased_random_states (SUC (SUC 0))
            then
              1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0))))
            else
              0)
         else
           3/2 *
           (if
              s IN
              biased_high_states (SUC (SUC 0)) CROSS
              biased_low_states CROSS biased_random_states (SUC (SUC 0))
            then
              1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0))))
            else
              0))
      else
        0)) =
        (\s. (if s IN
        biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | ~(L s = (\s. s = STRCAT "coin" (toString 0)))}
      then
        (\s. 3/2 * (1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0)))))) s
      else 0))`
        by (ONCE_REWRITE_TAC [FUN_EQ_THM]
            >> RW_TAC bool_ss [IN_INTER, GSPECIFICATION])
   >> POP_ORW
   >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> RW_TAC bool_ss [REAL_SUM_IMAGE_FINITE_CONST3]
   >> `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
      biased_random_states (SUC (SUC 0)) INTER
      {s | L s = (\s. s = STRCAT "coin" (toString 0))}) =
       (biased_high_states (SUC (SUC 0)) CROSS {(\s. s = STRCAT "coin" (toString 0))} CROSS
      biased_random_states (SUC (SUC 0)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [IN_INTER, L_def, GSPECIFICATION, IN_CROSS, IN_SING, biased_low_states_def]
            >> DECIDE_TAC)
   >> POP_ORW
   >> `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
      biased_random_states (SUC (SUC 0)) INTER
      {s | ~(L s = (\s. s = STRCAT "coin" (toString 0)))}) =
       (biased_high_states (SUC (SUC 0)) CROSS {(\s:string. F)} CROSS
      biased_random_states (SUC (SUC 0)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [IN_INTER, L_def, GSPECIFICATION, IN_CROSS, IN_SING, biased_low_states_def]
            >> METIS_TAC [])
   >> POP_ORW
  >> RW_TAC bool_ss [(COMPUTE_CARD ``(biased_high_states (SUC (SUC 0)) CROSS
                                {(\s. s = STRCAT "coin" (toString 0))} CROSS
                                biased_random_states (SUC (SUC 0)))``
                              (SIMP_CONV bool_ss [biased_high_states_def, biased_low_states_def,
                                biased_random_states_def, insider_high_states_set_def] THENC
                                SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv))))
                THENC SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
         THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV dc_dup_conv)))))
                dc_dup_conv),
                (COMPUTE_CARD ``(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                                biased_random_states (SUC (SUC 0)))``
                              (SIMP_CONV bool_ss [biased_high_states_def, biased_low_states_def,
                                biased_random_states_def, insider_high_states_set_def] THENC
                                SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv))))
                THENC SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
         THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV dc_dup_conv)))))
                dc_dup_conv),
        (COMPUTE_CARD ``(biased_high_states (SUC (SUC 0)) CROSS {(\s. F)} CROSS
                        biased_random_states (SUC (SUC 0)))``
                              (SIMP_CONV bool_ss [biased_high_states_def, biased_low_states_def,
                                biased_random_states_def, insider_high_states_set_def] THENC
                                SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv))))
                THENC SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
         THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV dc_dup_conv)))))
                dc_dup_conv)]
   >> RW_TAC real_ss []);

(* ------------------------------------------------------------------------- *)

val biased_dc3_leakage_result = store_thm
  ("biased_dc3_leakage_result",
   ``(leakage (biased_dc_prog_space (SUC (SUC 0))) (insider_dcprog (SUC(SUC(SUC 0)))) = 0)``,
   RW_TAC bool_ss [leakage_def]
   >> `FINITE ((biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0))))`
        by RW_TAC set_ss [biased_high_states_def, biased_low_states_def,
                             biased_random_states_def, insider_high_states_set_def]
   >> `FINITE (biased_high_states (SUC (SUC 0)))`
        by RW_TAC set_ss [biased_high_states_def, insider_high_states_set_def]
   >> `FINITE (biased_random_states (SUC (SUC 0)))`
        by RW_TAC set_ss [biased_random_states_def]
   >> `FINITE (biased_low_states)`
        by RW_TAC set_ss [biased_low_states_def]
   >> (MP_TAC o
       Q.SPECL [`2`,`(biased_dc_prog_space (SUC (SUC 0)))`, `(insider_dcprog (SUC (SUC (SUC 0))))`, `H`,`L`] o
       INST_TYPE [alpha |-> ``:(bool, bool, bool) prog_state``, beta |-> ``:bool state``, gamma |-> ``:bool state``,
                  delta |-> ``:bool state``])
        finite_conditional_mutual_information_reduce
   >> (MP_TAC o INST_TYPE [beta |-> ``:bool state``] o Q.ISPEC `(biased_dc_prog_space (SUC (SUC 0)))`)
        MEASURABLE_POW_TO_POW_IMAGE
   >> RW_TAC bool_ss [random_variable_def, prob_space_biased_dc_prog_space3, biased_dc_prog_space_def, PSPACE, EVENTS,
                      prob_space_def, measurable_sets_def, m_space_def,
                      REWRITE_RULE [prob_space_def] prob_space_biased_dc_prog_space3]
   >> POP_ASSUM (K ALL_TAC)
   >> RW_TAC bool_ss [biased_dist_def, unif_prog_dist_def,
        (COMPUTE_CARD ``(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                                biased_random_states (SUC (SUC 0)))``
                              (SIMP_CONV bool_ss [biased_high_states_def, biased_low_states_def,
                                biased_random_states_def, insider_high_states_set_def] THENC
                                SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv))))
                THENC SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
         THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV dc_dup_conv)))))
                dc_dup_conv)]
   >> Q.ABBREV_TAC `foo = (SUC (SUC 0))`
   >> RW_TAC std_ss [joint_distribution_def, L_def, H_def, PAIR, ETA_THM, FST, SND, PROB, PSPACE, distribution_def]
   >> `IMAGE L
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo) =
        biased_low_states`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE, IN_CROSS, L_def]
            >> EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss []
            >> Q.UNABBREV_TAC `foo`
            >> Q.EXISTS_TAC `(((\s:string. s = STRCAT "pays" (toString (SUC (SUC 0)))),x),(\s:string. F))`
            >> RW_TAC bool_ss [SND, FST, biased_high_states_def, insider_high_states_set_def, IN_INSERT]
            >> Suff `!n. (\s:string. F) IN biased_random_states n` >- RW_TAC std_ss []
            >> REPEAT (POP_ASSUM (K ALL_TAC))
            >> Induct >> RW_TAC bool_ss [biased_random_states_def, IN_SING, IN_IMAGE, IN_UNION]
            >> DISJ2_TAC >> Q.EXISTS_TAC `(\s:string.F)` >> RW_TAC std_ss [])
   >> POP_ORW
   >> `(IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo) CROSS
      IMAGE FST
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo)) =
        (IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo) CROSS
      (biased_high_states foo CROSS biased_low_states))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE, IN_CROSS, FST]
            >> EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss []
            >> Q.EXISTS_TAC `(SND x, SND x')`
            >> RW_TAC bool_ss [SND, FST])
   >> POP_ORW
   >> `!x z.
        SIGMA
          (\s.
             (if SND (FST s) = (\s. s = STRCAT "coin" (toString 0)) then
                1 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)
              else
                3 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)))
          (PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
           PREIMAGE L {z} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo)) =
        (if (z = (\s. s = STRCAT "coin" (toString 0))) then
                1/32
         else (if (z = (\s:string. F)) then
                3/32
         else 0)) *
        &(CARD {(h,r)| h IN biased_high_states foo /\ r IN biased_random_states foo /\
                            (insider_dcprog (SUC foo) ((h,z),r) = x)})`
        by (RW_TAC real_ss []
            >| [`(PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
                 PREIMAGE L {(\s. s = STRCAT "coin" (toString 0))} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 IMAGE (λ(h,r). ((h, (\s. s = STRCAT "coin" (toString 0))),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((h,(\s. s = STRCAT "coin" (toString 0))),r) = x)}`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, L_def]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Q.PAT_X_ASSUM `P = (\s:string. s = STRCAT "coin" (toString 0))` (ASSUME_TAC o GSYM)
                         >> Q.EXISTS_TAC `(FST(FST x'),SND x')`
                         >> RW_TAC std_ss [PAIR]
                         >> Q.EXISTS_TAC `(FST(FST x'),SND x')`
                         >> RW_TAC std_ss [PAIR_EQ])
                     >> POP_ASSUM MP_TAC
                     >> `x''' = (FST x''',SND x''')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [FST,SND, PAIR_EQ]
                     >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
                     >> RW_TAC set_ss [biased_low_states_def])
                >> POP_ORW
                >> `FINITE {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((h,(\s. s = STRCAT "coin" (toString 0))),r) = x)}`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss [FINITE_CROSS]
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                       >> POP_ASSUM MP_TAC
                       >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                       >> POP_ORW >> RW_TAC std_ss [])
                >> `INJ (λ(h,r). ((h,(\s. s = STRCAT "coin" (toString 0))),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                 (insider_dcprog (SUC foo) ((h,(\s. s = STRCAT "coin" (toString 0))),r) = x)}
                        (IMAGE (λ(h,r). ((h,(\s. s = STRCAT "coin" (toString 0))),r))
                                {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((h,(\s. s = STRCAT "coin" (toString 0))),r) = x)})`
                        by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE] >- METIS_TAC []
                            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(y :bool state # bool state) = (FST y,SND y)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> METIS_TAC [PAIR, PAIR_EQ])
                >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, o_DEF, Once REAL_SUM_IMAGE_IN_IF] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state # bool state).
                         SND (FST ((λ(h,r). ((h,(\s. s = STRCAT "coin" (toString 0))),r)) x')) =
                         (\s. s = STRCAT "coin" (toString 0))`
                        by (RW_TAC std_ss [] >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state # bool state).
                         ((λ(h,r). ((h,(\s. s = STRCAT "coin" (toString 0))),r)) x' IN
                        biased_high_states foo CROSS biased_low_states CROSS
                        biased_random_states foo) = (FST x' IN (biased_high_states foo) /\
                                                     SND x' IN (biased_random_states foo))`
                        by (RW_TAC std_ss [] >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> RW_TAC set_ss [IN_CROSS, biased_low_states_def, FST, SND])
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `(λ(x' :bool state # bool state). (if x' IN
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((h,(\s. s = STRCAT "coin" (toString 0))),r) = x)}
                        then 1 / 2 * (if FST x' IN biased_high_states foo /\ SND x' IN biased_random_states foo
                        then 1 / 16 else 0) else 0)) =
                    (λ(x' :bool state # bool state). (if x' IN
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((h,(\s. s = STRCAT "coin" (toString 0))),r) = x)}
                        then (\x. 1 / 32) x' else 0))`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [] >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> RW_TAC std_ss [GSPECIFICATION]
                            >> POP_ASSUM MP_TAC >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss [])
                >> POP_ORW >> RW_TAC real_ss [GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3, REAL_MUL_COMM],
                `(PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
                 PREIMAGE L {(\s:string. F)} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 IMAGE (λ(h,r). ((h, (\s:string. F)),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((h,(\s:string. F)),r) = x)}`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, L_def]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Q.PAT_X_ASSUM `P = (\s:string. F)` (ASSUME_TAC o GSYM)
                         >> Q.EXISTS_TAC `(FST(FST x'),SND x')`
                         >> RW_TAC std_ss [PAIR]
                         >> Q.EXISTS_TAC `(FST(FST x'),SND x')`
                         >> RW_TAC std_ss [PAIR_EQ])
                     >> POP_ASSUM MP_TAC
                     >> `x''' = (FST x''',SND x''')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [FST,SND, PAIR_EQ]
                     >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
                     >> RW_TAC set_ss [biased_low_states_def])
                >> POP_ORW
                >> `FINITE {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((h,(\s:string. F)),r) = x)}`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss [FINITE_CROSS]
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                       >> POP_ASSUM MP_TAC
                       >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                       >> POP_ORW >> RW_TAC std_ss [])
                >> `INJ (λ(h,r). ((h,(\s:string. F)),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                 (insider_dcprog (SUC foo) ((h,(\s:string. F)),r) = x)}
                        (IMAGE (λ(h,r). ((h,(\s:string. F)),r))
                                {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((h,(\s:string. F)),r) = x)})`
                        by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE] >- METIS_TAC []
                            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(y :bool state # bool state) = (FST y,SND y)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> METIS_TAC [PAIR, PAIR_EQ])
                >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, o_DEF, Once REAL_SUM_IMAGE_IN_IF] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state # bool state).
                         SND (FST ((λ(h,r). ((h,(\s:string.F)),r)) x')) =
                         (\s:string. F)`
                        by (RW_TAC std_ss [] >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state # bool state).
                         ((λ(h,r). ((h,(\s:string.F)),r)) x' IN
                        biased_high_states foo CROSS biased_low_states CROSS
                        biased_random_states foo) = (FST x' IN (biased_high_states foo) /\
                                                     SND x' IN (biased_random_states foo))`
                        by (RW_TAC std_ss [] >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> RW_TAC set_ss [IN_CROSS, biased_low_states_def, FST, SND])
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `(λ(x' :bool state # bool state). (if x' IN
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((h,(\s:string.F)),r) = x)}
                        then 3 / 2 * (if FST x' IN biased_high_states foo /\ SND x' IN biased_random_states foo
                        then 1 / 16 else 0) else 0)) =
                    (λ(x' :bool state # bool state). (if x' IN
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((h,(\s:string.F)),r) = x)}
                        then (\x. 3 / 32) x' else 0))`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [] >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> RW_TAC std_ss [GSPECIFICATION]
                            >> POP_ASSUM MP_TAC >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss [])
                >> POP_ORW >> RW_TAC real_ss [GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3, REAL_MUL_COMM],
                RW_TAC bool_ss [GSYM INTER_ASSOC]
                >> Suff `PREIMAGE L {z} INTER (biased_high_states foo CROSS biased_low_states CROSS
                                                biased_random_states foo) = {}`
                >- RW_TAC bool_ss [INTER_EMPTY, REAL_SUM_IMAGE_THM]
                >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [NOT_IN_EMPTY, L_def, IN_CROSS, IN_INTER, IN_PREIMAGE, IN_SING, biased_low_states_def]
                >> METIS_TAC []])
   >> `!x z. (PREIMAGE (\x. (insider_dcprog (SUC foo) x,SND (FST x)))
           {(x,z)} INTER
         (biased_high_states foo CROSS biased_low_states CROSS
          biased_random_states foo)) =
        (PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
           PREIMAGE L {z} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_CROSS, IN_PREIMAGE, IN_SING, L_def])
   >> POP_ORW
   >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> `!x z.
        SIGMA
             (\s.
                (if
                   SND (FST s) = (\s. s = STRCAT "coin" (toString 0))
                 then
                   1 / 2 *
                   (if
                      s IN
                      biased_high_states foo CROSS
                      biased_low_states CROSS biased_random_states foo
                    then
                      1 / 16
                    else
                      0)
                 else
                   3 / 2 *
                   (if
                      s IN
                      biased_high_states foo CROSS
                      biased_low_states CROSS biased_random_states foo
                    then
                      1 / 16
                    else
                      0)))
             (PREIMAGE L {z} INTER
              (biased_high_states foo CROSS biased_low_states CROSS
               biased_random_states foo)) =
        (if (z = (\s. s = STRCAT "coin" (toString 0))) then
                1/32
         else (if (z = (\s:string. F)) then
                3/32
         else 0)) *
        &(CARD (biased_high_states foo) * CARD (biased_random_states foo))`
        by (RW_TAC real_ss []
            >| [`(PREIMAGE L {(\s. s = STRCAT "coin" (toString 0))} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 IMAGE (λ(h,r). ((h, (\s. s = STRCAT "coin" (toString 0))),r))
                        (biased_high_states foo CROSS biased_random_states foo)`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, L_def]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Q.PAT_X_ASSUM `P = (\s:string. s = STRCAT "coin" (toString 0))` (ASSUME_TAC o GSYM)
                         >> Q.EXISTS_TAC `(FST(FST x),SND x)`
                         >> RW_TAC std_ss [PAIR]
                         >> Q.EXISTS_TAC `(FST(FST x),SND x)`
                         >> RW_TAC std_ss [PAIR_EQ])
                     >>  `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
                     >> RW_TAC set_ss [biased_low_states_def])
                >> POP_ORW
                >> `INJ (λ(h,r). ((h,(\s. s = STRCAT "coin" (toString 0))),r))
                        (biased_high_states foo CROSS biased_random_states foo)
                        (IMAGE (λ(h,r). ((h,(\s. s = STRCAT "coin" (toString 0))),r))
                                (biased_high_states foo CROSS biased_random_states foo))`
                        by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE] >- METIS_TAC []
                            >> POP_ASSUM MP_TAC
                            >> `(x :bool state # bool state) = (FST x,SND x)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> POP_ASSUM MP_TAC
                            >> `(y :bool state # bool state) = (FST y,SND y)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> METIS_TAC [PAIR, PAIR_EQ])
                >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, o_DEF, Once REAL_SUM_IMAGE_IN_IF, FINITE_CROSS] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state # bool state).
                         SND (FST ((λ(h,r). ((h,(\s. s = STRCAT "coin" (toString 0))),r)) x')) =
                         (\s. s = STRCAT "coin" (toString 0))`
                        by (RW_TAC std_ss [] >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state # bool state).
                         ((λ(h,r). ((h,(\s. s = STRCAT "coin" (toString 0))),r)) x' IN
                        biased_high_states foo CROSS biased_low_states CROSS
                        biased_random_states foo) = (FST x' IN (biased_high_states foo) /\
                                                     SND x' IN (biased_random_states foo))`
                        by (RW_TAC std_ss [] >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> RW_TAC set_ss [IN_CROSS, biased_low_states_def, FST, SND])
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `(λ(x' :bool state # bool state). (if x' IN
                        biased_high_states foo CROSS biased_random_states foo
                        then 1 / 2 * (if FST x' IN biased_high_states foo /\ SND x' IN biased_random_states foo
                        then 1 / 16 else 0) else 0)) =
                    (λ(x' :bool state # bool state). (if x' IN
                        biased_high_states foo CROSS biased_random_states foo
                        then (\x. 1 / 32) x' else 0))`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_CROSS])
                >> POP_ORW >> RW_TAC real_ss [GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3,
                                              REAL_MUL_COMM, FINITE_CROSS, CARD_CROSS],
                `(PREIMAGE L {(\s:string. F)} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 IMAGE (λ(h,r). ((h, (\s:string. F)),r))
                        (biased_high_states foo CROSS biased_random_states foo)`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, L_def]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Q.PAT_X_ASSUM `P = (\s:string. F)` (ASSUME_TAC o GSYM)
                         >> Q.EXISTS_TAC `(FST(FST x),SND x)`
                         >> RW_TAC std_ss [PAIR]
                         >> Q.EXISTS_TAC `(FST(FST x),SND x)`
                         >> RW_TAC std_ss [PAIR_EQ])
                     >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
                     >> RW_TAC set_ss [biased_low_states_def])
                >> POP_ORW
                >> `INJ (λ(h,r). ((h,(\s:string. F)),r))
                        (biased_high_states foo CROSS biased_random_states foo)
                        (IMAGE (λ(h,r). ((h,(\s:string. F)),r))
                                (biased_high_states foo CROSS biased_random_states foo))`
                        by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE] >- METIS_TAC []
                            >> POP_ASSUM MP_TAC
                            >> `(x :bool state # bool state) = (FST x,SND x)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> POP_ASSUM MP_TAC
                            >> `(y :bool state # bool state) = (FST y,SND y)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> METIS_TAC [PAIR, PAIR_EQ])
                >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, o_DEF, Once REAL_SUM_IMAGE_IN_IF, FINITE_CROSS] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state # bool state).
                         SND (FST ((λ(h,r). ((h,(\s:string.F)),r)) x')) =
                         (\s:string. F)`
                        by (RW_TAC std_ss [] >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state # bool state).
                         ((λ(h,r). ((h,(\s:string.F)),r)) x' IN
                        biased_high_states foo CROSS biased_low_states CROSS
                        biased_random_states foo) = (FST x' IN (biased_high_states foo) /\
                                                     SND x' IN (biased_random_states foo))`
                        by (RW_TAC std_ss [] >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> RW_TAC set_ss [IN_CROSS, biased_low_states_def, FST, SND])
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `(λ(x' :bool state # bool state). (if x' IN
                        (biased_high_states foo CROSS biased_random_states foo)
                        then 3 / 2 * (if FST x' IN biased_high_states foo /\ SND x' IN biased_random_states foo
                        then 1 / 16 else 0) else 0)) =
                    (λ(x' :bool state # bool state). (if x' IN
                        (biased_high_states foo CROSS biased_random_states foo)
                        then (\x. 3 / 32) x' else 0))`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_CROSS])
                >> POP_ORW >> RW_TAC real_ss [GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3, REAL_MUL_COMM, CARD_CROSS, FINITE_CROSS],
                Suff `PREIMAGE L {z} INTER (biased_high_states foo CROSS biased_low_states CROSS
                                                biased_random_states foo) = {}`
                >- RW_TAC bool_ss [REAL_SUM_IMAGE_THM]
                >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [NOT_IN_EMPTY, L_def, IN_CROSS, IN_INTER, IN_PREIMAGE, IN_SING, biased_low_states_def]
                >> METIS_TAC []])
   >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> `!x y z.
        SIGMA
          (\s.
             (if SND (FST s) = (\s. s = STRCAT "coin" (toString 0)) then
                1 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)
              else
                3 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)))
          (PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
           PREIMAGE FST {(y,z)} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo)) =
        (if (z = (\s. s = STRCAT "coin" (toString 0))) /\ y IN (biased_high_states foo) then
                1/32
         else (if (z = (\s:string. F)) /\ y IN (biased_high_states foo) then
                3/32
         else 0)) *
        &(CARD {r | r IN biased_random_states foo /\
                            (insider_dcprog (SUC foo) ((y,z),r) = x)})`
        by (RW_TAC real_ss []
            >| [`(PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
                 PREIMAGE FST {(y,(\s. s = STRCAT "coin" (toString 0)))} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 IMAGE (\r. ((y, (\s. s = STRCAT "coin" (toString 0))),r))
                        {r | r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((y,(\s. s = STRCAT "coin" (toString 0))),r) = x)}`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, FST]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Q.PAT_X_ASSUM `P = (y,(\s:string. s = STRCAT "coin" (toString 0)))` (ASSUME_TAC o GSYM)
                         >> Q.EXISTS_TAC `SND x'`
                         >> RW_TAC std_ss [PAIR])
                     >> RW_TAC set_ss [biased_low_states_def])
                >> POP_ORW
                >> `FINITE {r | r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((y,(\s. s = STRCAT "coin" (toString 0))),r) = x)}`
                   by ((MP_TAC o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss []
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
                >> `INJ (\r. ((y,(\s. s = STRCAT "coin" (toString 0))),r))
                        {r | r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((y,(\s. s = STRCAT "coin" (toString 0))),r) = x)}
                        (IMAGE (\r. ((y,(\s. s = STRCAT "coin" (toString 0))),r))
                                {r | r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((y,(\s. s = STRCAT "coin" (toString 0))),r) = x)})`
                        by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE])
                >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, o_DEF, Once REAL_SUM_IMAGE_IN_IF] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state).
                         (((y,(\s. s = STRCAT "coin" (toString 0))),x') IN
                                biased_high_states foo CROSS biased_low_states CROSS
                                biased_random_states foo) = (x' IN (biased_random_states foo))`
                        by RW_TAC set_ss [IN_CROSS, biased_low_states_def, FST, SND]
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `(λ(x' :bool state). (if x' IN
                        {r |r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((y,(\s. s = STRCAT "coin" (toString 0))),r) = x)}
                        then 1 / 2 * (if x' IN biased_random_states foo
                        then 1 / 16 else 0) else 0)) =
                    (λ(x' :bool state). (if x' IN
                        {r |r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((y,(\s. s = STRCAT "coin" (toString 0))),r) = x)}
                        then (\x. 1 / 32) x' else 0))`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [GSPECIFICATION])
                >> POP_ORW >> RW_TAC real_ss [GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3, REAL_MUL_COMM],
                `(PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
                 PREIMAGE FST {(y,(\s:string. F))} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 IMAGE (\r. ((y, (\s:string. F)),r))
                        {r | r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((y,(\s:string. F)),r) = x)}`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, FST]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Q.PAT_X_ASSUM `P = (y,(\s:string. F))` (ASSUME_TAC o GSYM)
                         >> Q.EXISTS_TAC `SND x'`
                         >> RW_TAC std_ss [PAIR])
                     >> RW_TAC set_ss [biased_low_states_def])
                >> POP_ORW
                >> `FINITE {r | r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((y,(\s:string. F)),r) = x)}`
                   by ((MP_TAC o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss []
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
                >> `INJ (\r. ((y,(\s:string. F)),r))
                        {r | r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((y,(\s:string. F)),r) = x)}
                        (IMAGE (\r. ((y,(\s:string. F)),r))
                                {r | r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((y,(\s:string. F)),r) = x)})`
                        by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE])
                >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, o_DEF, Once REAL_SUM_IMAGE_IN_IF] >> POP_ASSUM (K ALL_TAC)
                >> FULL_SIMP_TAC bool_ss [DE_MORGAN_THM]
                >> `!(x' :bool state).
                         (((y,(\s. F)),x') IN
                        biased_high_states foo CROSS biased_low_states CROSS
                        biased_random_states foo) = (x' IN (biased_random_states foo))`
                        by RW_TAC set_ss [IN_CROSS, biased_low_states_def, FST, SND]
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `(λ(x' :bool state). (if x' IN
                        {r | r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((y,(\s:string. F)),r) = x)}
                        then 3 / 2 * (if x' IN biased_random_states foo
                        then 1 / 16 else 0) else 0)) =
                    (λ(x' :bool state). (if x' IN
                        {r | r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((y,(\s:string. F)),r) = x)}
                        then (\x. 3 / 32) x' else 0))`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [GSPECIFICATION])
                >> POP_ORW >> RW_TAC real_ss [GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3, REAL_MUL_COMM],
                RW_TAC bool_ss [GSYM INTER_ASSOC]
                >> Suff `PREIMAGE FST {(y,z)} INTER (biased_high_states foo CROSS biased_low_states CROSS
                                                biased_random_states foo) = {}`
                >- RW_TAC bool_ss [INTER_EMPTY, REAL_SUM_IMAGE_THM]
                >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [NOT_IN_EMPTY, FST, IN_CROSS, IN_INTER, IN_PREIMAGE, IN_SING, biased_low_states_def]
                >> METIS_TAC [PAIR, FST,SND]])
   >> `!x y z. (PREIMAGE (\x. (insider_dcprog (SUC foo) x,FST x))
           {(x,y,z)} INTER
         (biased_high_states foo CROSS biased_low_states CROSS
          biased_random_states foo)) =
        (PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
           PREIMAGE FST {(y,z)} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_CROSS, IN_PREIMAGE, IN_SING, L_def])
   >> POP_ORW
   >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> `!x y z.
        SIGMA
             (\s.
                (if
                   SND (FST s) = (\s. s = STRCAT "coin" (toString 0))
                 then
                   1 / 2 *
                   (if
                      s IN
                      biased_high_states foo CROSS
                      biased_low_states CROSS biased_random_states foo
                    then
                      1 / 16
                    else
                      0)
                 else
                   3 / 2 *
                   (if
                      s IN
                      biased_high_states foo CROSS
                      biased_low_states CROSS biased_random_states foo
                    then
                      1 / 16
                    else
                      0)))
             (PREIMAGE FST {(y,z)} INTER
              (biased_high_states foo CROSS biased_low_states CROSS
               biased_random_states foo)) =
        (if (z = (\s. s = STRCAT "coin" (toString 0))) /\ y IN (biased_high_states foo) then
                1/32
         else (if (z = (\s:string. F)) /\ y IN (biased_high_states foo) then
                3/32
         else 0)) *
        &(CARD (biased_random_states foo))`
        by (RW_TAC real_ss []
            >| [`(PREIMAGE FST {(y,(\s. s = STRCAT "coin" (toString 0)))} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 IMAGE (\r. ((y, (\s. s = STRCAT "coin" (toString 0))),r))
                        (biased_random_states foo)`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, FST]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Q.PAT_X_ASSUM `P = (y,(\s:string. s = STRCAT "coin" (toString 0)))` (ASSUME_TAC o GSYM)
                         >> Q.EXISTS_TAC `SND x`
                         >> RW_TAC std_ss [PAIR])
                     >> RW_TAC set_ss [biased_low_states_def])
                >> POP_ORW
                >> `INJ (\r. ((y,(\s. s = STRCAT "coin" (toString 0))),r))
                        (biased_random_states foo)
                        (IMAGE (\r. ((y,(\s. s = STRCAT "coin" (toString 0))),r))
                                (biased_random_states foo))`
                        by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE])
                >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, o_DEF, Once REAL_SUM_IMAGE_IN_IF, FINITE_CROSS] >> POP_ASSUM (K ALL_TAC)
                >> `!(x' :bool state).
                        (((y,(\s. s = STRCAT "coin" (toString 0))),x') IN
                        biased_high_states foo CROSS biased_low_states CROSS
                        biased_random_states foo) = (x' IN (biased_random_states foo))`
                        by RW_TAC set_ss [IN_CROSS, biased_low_states_def, FST, SND]
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> `(\x: bool state. (if x IN biased_random_states foo then 1 / 2 * (1 / 16) else 0)) =
                    (λ(x' :bool state). (if x' IN biased_random_states foo then (\x. 1 / 32) x' else 0))`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_CROSS])
                >> POP_ORW >> RW_TAC real_ss [GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3,
                                              REAL_MUL_COMM],
                `(PREIMAGE FST {(y,(\s:string. F))} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 IMAGE (\r. ((y, (\s:string. F)),r))
                        (biased_random_states foo)`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, FST]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Q.PAT_X_ASSUM `P = (y,(\s:string. F))` (ASSUME_TAC o GSYM)
                         >> Q.EXISTS_TAC `SND x`
                         >> RW_TAC std_ss [PAIR])
                     >> RW_TAC set_ss [biased_low_states_def])
                >> POP_ORW
                >> `INJ (\r. ((y,(\s:string. F)),r))
                        (biased_random_states foo)
                        (IMAGE (\r. ((y,(\s:string. F)),r))
                                (biased_random_states foo))`
                        by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE])
                >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, o_DEF, Once REAL_SUM_IMAGE_IN_IF, FINITE_CROSS] >> POP_ASSUM (K ALL_TAC)
                >> FULL_SIMP_TAC std_ss [DE_MORGAN_THM]
                >> `!(x' :bool state).
                         (((y,(\s:string.F)),x') IN
                        biased_high_states foo CROSS biased_low_states CROSS
                        biased_random_states foo) = (x' IN (biased_random_states foo))`
                        by RW_TAC set_ss [IN_CROSS, biased_low_states_def, FST, SND]
                >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
                >> Q.UNABBREV_TAC `foo`
                >> `(\x:bool state. (if x IN biased_random_states 2 then 3 / 2 * (1 / 16) else 0)) =
                    (λ(x' :bool state). (if x' IN biased_random_states 2
                        then (\x. 3 / 32) x' else 0))`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_CROSS])
                >> POP_ORW >> RW_TAC real_ss [GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3, REAL_MUL_COMM],
                Suff `PREIMAGE FST {(y,z)} INTER (biased_high_states foo CROSS biased_low_states CROSS
                                                biased_random_states foo) = {}`
                >- RW_TAC bool_ss [REAL_SUM_IMAGE_THM]
                >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [NOT_IN_EMPTY, FST, IN_CROSS, IN_INTER, IN_PREIMAGE, IN_SING, biased_low_states_def]
                >> METIS_TAC [PAIR, FST, SND]])
   >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> Q.UNABBREV_TAC `foo`
   >> RW_TAC bool_ss [(COMPUTE_CARD ``(biased_high_states (SUC (SUC 0)))``
                              (SIMP_CONV set_ss [biased_high_states_def, insider_high_states_set_def]
                               THENC (TRY_CONV insider_hl_dup_conv))
                                dc_dup_conv),
                        (COMPUTE_CARD ``(biased_random_states (SUC (SUC 0)))``
                              (SIMP_CONV bool_ss [biased_random_states_def] THENC
                                SIMP_CONV bool_ss [PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV dc_dup_conv)))))
                        dc_dup_conv)]
   >> Q.ABBREV_TAC `foo = SUC (SUC 0)`
   >> RW_TAC real_ss []
   >> `(IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo) CROSS biased_low_states) =
        (IMAGE (\out. (out, (\s.s = STRCAT "coin" (toString 0)))) (IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo))) UNION
        (IMAGE (\out. (out, (\s:string.F))) (IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo)))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [biased_low_states_def, IN_UNION, IN_IMAGE, IN_CROSS, IN_IMAGE, IN_INSERT, IN_SING]
            >> `x = (FST x,SND x)` by RW_TAC std_ss [PAIR] >> POP_ORW
            >> RW_TAC bool_ss [PAIR_EQ]
            >> EQ_TAC >> RW_TAC std_ss [FST, SND] >> RW_TAC std_ss [] >> METIS_TAC [PAIR, FST,SND])
   >> POP_ORW
   >> `DISJOINT (IMAGE (\out. (out,(\s. s = STRCAT "coin" (toString 0))))
        (IMAGE (insider_dcprog (SUC foo))
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo)))
      (IMAGE (\out. (out,(\s. F)))
        (IMAGE (insider_dcprog (SUC foo))
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo)))`
        by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER, IN_IMAGE]
            >> `x = (FST x,SND x)` by RW_TAC std_ss [PAIR] >> POP_ORW
            >> RW_TAC bool_ss [PAIR_EQ]
            >> METIS_TAC [])
   >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION, IMAGE_FINITE, FINITE_CROSS]
   >> POP_ASSUM (K ALL_TAC)
   >> `!c:bool state. INJ (\out. (out,c))
            (IMAGE (insider_dcprog (SUC foo))
            (biased_high_states foo CROSS biased_low_states CROSS
             biased_random_states foo))
          (IMAGE (\out. (out,c))
            (IMAGE (insider_dcprog (SUC foo))
            (biased_high_states foo CROSS biased_low_states CROSS
             biased_random_states foo)))`
        by RW_TAC std_ss [INJ_DEF, IN_IMAGE]
   >> RW_TAC real_ss [IMAGE_FINITE, REAL_SUM_IMAGE_IMAGE, FINITE_CROSS, o_DEF]
   >- METIS_TAC []
   >> POP_ASSUM MP_TAC >> POP_ASSUM (K ALL_TAC) >> STRIP_TAC
   >> `(IMAGE (insider_dcprog (SUC foo))
       (biased_high_states foo CROSS biased_low_states CROSS
        biased_random_states foo) CROSS
     (biased_high_states foo CROSS biased_low_states)) =
        (IMAGE (λ(out,h). (out, (h,(\s.s = STRCAT "coin" (toString 0))))) ((IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo)) CROSS (biased_high_states foo))) UNION
        (IMAGE (λ(out,h). (out, (h,(\s:string.F)))) ((IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo)) CROSS (biased_high_states foo)))`
        by ((ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [biased_low_states_def, IN_UNION, IN_IMAGE, IN_CROSS, IN_IMAGE, IN_INSERT, IN_SING]
            >> EQ_TAC >> RW_TAC std_ss [FST, SND] >> RW_TAC std_ss [])
            >| [DISJ1_TAC >> Q.EXISTS_TAC `(insider_dcprog (SUC foo) x', FST (SND x))`
                >> RW_TAC std_ss []
                >- (`x = (FST x, (FST(SND x),SND(SND x)))` by METIS_TAC [PAIR]
                    >> POP_ORW >> RW_TAC bool_ss [PAIR_EQ]
                    >> RW_TAC std_ss [FST, SND])
                >> METIS_TAC [],
                DISJ2_TAC >> Q.EXISTS_TAC `(insider_dcprog (SUC foo) x', FST (SND x))`
                >> RW_TAC std_ss []
                >- (`x = (FST x, (FST(SND x),SND(SND x)))` by METIS_TAC [PAIR]
                    >> POP_ORW >> RW_TAC bool_ss [PAIR_EQ]
                    >> RW_TAC std_ss [FST, SND])
                >> METIS_TAC [],
                DISJ1_TAC >> Q.EXISTS_TAC `(insider_dcprog (SUC foo) x', FST (SND x))`
                >> RW_TAC std_ss []
                >- (`x = (FST x, (FST(SND x),SND(SND x)))` by METIS_TAC [PAIR]
                    >> POP_ORW >> RW_TAC bool_ss [PAIR_EQ]
                    >> RW_TAC std_ss [FST, SND])
                >> METIS_TAC [],
                DISJ2_TAC >> Q.EXISTS_TAC `(insider_dcprog (SUC foo) x', FST (SND x))`
                >> RW_TAC std_ss []
                >- (`x = (FST x, (FST(SND x),SND(SND x)))` by METIS_TAC [PAIR]
                    >> POP_ORW >> RW_TAC bool_ss [PAIR_EQ]
                    >> RW_TAC std_ss [FST, SND])
                >> METIS_TAC [],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                >> METIS_TAC [],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [FST, SND],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [FST, SND],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                >> METIS_TAC [],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [FST, SND],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [FST, SND],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                >> METIS_TAC [],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [FST, SND],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [FST, SND],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                >> METIS_TAC [],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [FST, SND],
                `x' = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                >> POP_ORW >> RW_TAC std_ss [FST, SND]])
   >> POP_ORW
   >> `DISJOINT (IMAGE (λ(out,h). (out, (h,(\s.s = STRCAT "coin" (toString 0))))) ((IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo)) CROSS (biased_high_states foo)))
        (IMAGE (λ(out,h). (out, (h,(\s:string.F)))) ((IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo)) CROSS (biased_high_states foo)))`
        by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER, IN_IMAGE, IN_CROSS, biased_low_states_def,
                           IN_INSERT, IN_SING]
            >> `x = (FST x,SND x)` by RW_TAC std_ss [PAIR] >> POP_ORW
            >> RW_TAC bool_ss []
            >> Cases_on `SND(SND x) = (\s. s = STRCAT "coin" (toString 0))`
            >- (DISJ2_TAC >> STRIP_TAC >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR] >> POP_ORW
                >> RW_TAC std_ss [] >> `x = (FST x,SND x)` by RW_TAC std_ss [PAIR] >> POP_ORW
                >> RW_TAC bool_ss [PAIR_EQ] >> `SND x = (FST(SND x),SND(SND x))` by RW_TAC std_ss [PAIR] >> POP_ORW
                >> RW_TAC bool_ss [PAIR_EQ])
            >> DISJ1_TAC >> STRIP_TAC >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR] >> POP_ORW
            >> RW_TAC std_ss [] >> `x = (FST x,SND x)` by RW_TAC std_ss [PAIR] >> POP_ORW
            >> RW_TAC bool_ss [PAIR_EQ] >> `SND x = (FST(SND x),SND(SND x))` by RW_TAC std_ss [PAIR] >> POP_ORW
            >> RW_TAC bool_ss [PAIR_EQ])
   >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION, IMAGE_FINITE, FINITE_CROSS]
   >> POP_ASSUM (K ALL_TAC)
   >> `!c:bool state. INJ (λ(out,h). (out,h,c))
            (IMAGE (insider_dcprog (SUC foo))
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo) CROSS biased_high_states foo)
          (IMAGE (λ(out,h). (out,h,c))
            (IMAGE (insider_dcprog (SUC foo))
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo) CROSS biased_high_states foo))`
        by (RW_TAC std_ss [INJ_DEF, IN_IMAGE] >- METIS_TAC []
            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
            >> `(x :bool state # bool state) = (FST x,SND x)` by RW_TAC std_ss [PAIR]
            >> POP_ORW >> RW_TAC std_ss []
            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
            >> `(y :bool state # bool state) = (FST y,SND y)` by RW_TAC std_ss [PAIR]
            >> POP_ORW >> RW_TAC std_ss []
            >> METIS_TAC [PAIR, PAIR_EQ])
   >> RW_TAC real_ss [IMAGE_FINITE, REAL_SUM_IMAGE_IMAGE, FINITE_CROSS, o_DEF]
   >> POP_ASSUM (K ALL_TAC)
   >> `!x:bool state # bool state. x = (FST x, SND x)` by RW_TAC std_ss [PAIR]
   >> POP_ORW >> RW_TAC std_ss []
   >> Q.ABBREV_TAC `sumone = SIGMA
      (\out.
         1 / 32 *
         &
           (CARD
              {(h,r) |
               h IN biased_high_states foo /\
               r IN biased_random_states foo /\
               (insider_dcprog (SUC foo)
                  ((h,(\s. s = STRCAT "coin" (toString 0))),r) =
                out)}) *
         logr 2
           (1 / 32 *
            &
              (CARD
                 {(h,r) |
                  h IN biased_high_states foo /\
                  r IN biased_random_states foo /\
                  (insider_dcprog (SUC foo)
                     ((h,(\s. s = STRCAT "coin" (toString 0))),r) =
                   out)}) / (1 / 4)))
      (IMAGE (insider_dcprog (SUC foo))
         (biased_high_states foo CROSS biased_low_states CROSS
          biased_random_states foo)) +
    SIGMA
      (\out.
         3 / 32 *
         &
           (CARD
              {(h,r) |
               h IN biased_high_states foo /\
               r IN biased_random_states foo /\
               (insider_dcprog (SUC foo) ((h,(\s. F)),r) = out)}) *
         logr 2
           (3 / 32 *
            &
              (CARD
                 {(h,r) |
                  h IN biased_high_states foo /\
                  r IN biased_random_states foo /\
                  (insider_dcprog (SUC foo) ((h,(\s. F)),r) = out)}) /
            (3 / 4)))
      (IMAGE (insider_dcprog (SUC foo))
         (biased_high_states foo CROSS biased_low_states CROSS
          biased_random_states foo))`
   >> `FINITE (IMAGE (insider_dcprog (SUC foo))
      (biased_high_states foo CROSS biased_low_states CROSS
       biased_random_states foo) CROSS biased_high_states foo)`
        by RW_TAC std_ss [IMAGE_FINITE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (insider_dcprog (SUC foo))
      (biased_high_states foo CROSS biased_low_states CROSS
       biased_random_states foo) CROSS biased_high_states foo)`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
      if
        x IN
        IMAGE (insider_dcprog (SUC foo))
          (biased_high_states foo CROSS biased_low_states CROSS
           biased_random_states foo) CROSS biased_high_states foo
      then
        (\x.
           (if SND x IN biased_high_states foo then 1 / 32 else 0) *
           &CARD
              {r |
               r IN biased_random_states foo /\
               (insider_dcprog (SUC foo)
                  ((SND x,(\s. s = STRCAT "coin" (toString 0))),r) =
                FST x)} *
           logr 2
             ((if SND x IN biased_high_states foo then 1 / 32 else 0) *
              &CARD
                 {r |
                  r IN biased_random_states foo /\
                  (insider_dcprog (SUC foo)
                     ((SND x,(\s. s = STRCAT "coin" (toString 0))),r) =
                   FST x)} /
              ((if SND x IN biased_high_states foo then 1 / 32 else 0) *
               4))) x
      else
        0) =
        (\x.
        (if
           x IN
           IMAGE (insider_dcprog (SUC foo))
             (biased_high_states foo CROSS biased_low_states CROSS
              biased_random_states foo) CROSS biased_high_states foo
         then
           (\x. (1 / 32) *
           &
             (CARD
                {r |
                 r IN biased_random_states foo /\
                 (insider_dcprog (SUC foo)
                    ((SND x,(\s. s = STRCAT "coin" (toString 0))),r) =
                  FST x)}) *
           logr 2
             ((1 / 32) *
              &
                (CARD
                   {r |
                    r IN biased_random_states foo /\
                    (insider_dcprog (SUC foo)
                       ((SND x,(\s. s = STRCAT "coin" (toString 0))),
                        r) =
                     FST x)}) /
              ((1 / 32) *
               4))) x
         else
           0))` by (RW_TAC std_ss [FUN_EQ_THM, IN_CROSS] >> RW_TAC std_ss [])
   >> POP_ORW
   >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF, IMAGE_FINITE, FINITE_CROSS]
   >> Q.ABBREV_TAC `sumtwo = SIGMA
     (\x.
        1 / 32 *
        &
          (CARD
             {r |
              r IN biased_random_states foo /\
              (insider_dcprog (SUC foo)
                 ((SND x,(\s. s = STRCAT "coin" (toString 0))),r) =
               FST x)}) *
        logr 2
          (1 / 32 *
           &
             (CARD
                {r |
                 r IN biased_random_states foo /\
                 (insider_dcprog (SUC foo)
                    ((SND x,(\s. s = STRCAT "coin" (toString 0))),r) =
                  FST x)}) / (1 / 32 * 4)))
     (IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo) CROSS biased_high_states foo)`
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(IMAGE (insider_dcprog (SUC foo))
      (biased_high_states foo CROSS biased_low_states CROSS
       biased_random_states foo) CROSS biased_high_states foo)`) REAL_SUM_IMAGE_IN_IF]


   >> `(\x.
      if
        x IN
        IMAGE (insider_dcprog (SUC foo))
          (biased_high_states foo CROSS biased_low_states CROSS
           biased_random_states foo) CROSS biased_high_states foo
      then
        (\x.
           (if SND x IN biased_high_states foo then 3 / 32 else 0) *
           &CARD
              {r |
               r IN biased_random_states foo /\
               (insider_dcprog (SUC foo) ((SND x,(\s. F)),r) = FST x)} *
           logr 2
             ((if SND x IN biased_high_states foo then 3 / 32 else 0) *
              &CARD
                 {r |
                  r IN biased_random_states foo /\
                  (insider_dcprog (SUC foo) ((SND x,(\s. F)),r) =
                   FST x)} /
              ((if SND x IN biased_high_states foo then 3 / 32 else 0) *
               4))) x
      else
        0) =
        (\x.
        (if
           x IN
           IMAGE (insider_dcprog (SUC foo))
             (biased_high_states foo CROSS biased_low_states CROSS
              biased_random_states foo) CROSS biased_high_states foo
         then
           (\x. (3 / 32) *
           &
             (CARD
                {r |
                 r IN biased_random_states foo /\
                 (insider_dcprog (SUC foo) ((SND x,(\s. F)),r) =
                  FST x)}) *
           logr 2
             ((3 / 32) *
              &
                (CARD
                   {r |
                    r IN biased_random_states foo /\
                    (insider_dcprog (SUC foo) ((SND x,(\s. F)),r) =
                     FST x)}) /
              ((3 / 32) *
               4))) x
         else
           0))` by (RW_TAC std_ss [FUN_EQ_THM, IN_CROSS] >> RW_TAC std_ss [])
   >> POP_ORW
   >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF, IMAGE_FINITE, FINITE_CROSS]
   >> Q.UNABBREV_TAC `sumtwo` >> Q.UNABBREV_TAC `sumone`
   >> RW_TAC real_ss [] >> Q.PAT_X_ASSUM `!f. f IN P` (K ALL_TAC)
   >> RW_TAC std_ss [GSYM lg_def]
   >> `!(out:bool state) (x:real) y c. x * c * lg (x * c / y) =
                (\c. x * c * lg (x * c / y)) c` by RW_TAC std_ss []
   >> POP_ORW
   >> Q.ABBREV_TAC `c1 = (\c. 1 / 32 * c * lg (1 / 32 * c / (1 / 4)))`
   >> Q.ABBREV_TAC `c2 = (\c. 3 / 32 * c * lg (3 / 32 * c / (3 / 4)))`
   >> Q.ABBREV_TAC `c3 = (\c. 1 / 32 * c * lg (1 / 32 * c / (1 / 8)))`
   >> Q.ABBREV_TAC `c4 = (\c. 3 / 32 * c * lg (3 / 32 * c / (3 / 8)))`
   >> `!(out:bool state) (b:bool state).
        &(CARD {(h,r) |
                  h IN biased_high_states foo /\
                  r IN biased_random_states foo /\
                  (insider_dcprog (SUC foo)
                     ((h,b),r) =
                   out)}) =
        REAL_SUM_IMAGE
        (λ(h,r). if (insider_dcprog (SUC foo)
                        ((h,b),r) = out) then 1 else 0)
        (biased_high_states foo CROSS biased_random_states foo)`
        by (STRIP_TAC >> STRIP_TAC
            >> `FINITE {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((h,b),r) = out)}`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss [FINITE_CROSS]
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                       >> POP_ASSUM MP_TAC
                       >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                       >> POP_ORW >> RW_TAC std_ss [])
            >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
            >> `FINITE {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        ~(insider_dcprog (SUC foo) ((h,b),r) = out)}`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss [FINITE_CROSS]
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                       >> POP_ASSUM MP_TAC
                       >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                       >> POP_ORW >> RW_TAC std_ss [])
            >> `(biased_high_states foo CROSS biased_random_states foo) =
                {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((h,b),r) = out)} UNION
                {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        ~(insider_dcprog (SUC foo) ((h,b),r) = out)}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION, IN_CROSS]
                    >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                    >- (Cases_on `insider_dcprog (SUC foo)
                                        ((FST x,b),SND x) = out`
                        >- (DISJ1_TAC >> Q.EXISTS_TAC `(FST x, SND x)` >> RW_TAC std_ss [PAIR_EQ])
                        >> DISJ2_TAC >> Q.EXISTS_TAC `(FST x, SND x)` >> RW_TAC std_ss [PAIR_EQ])
                    >> POP_ASSUM MP_TAC
                    >> `x':bool state # bool state = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ])
            >> POP_ORW
            >> `DISJOINT {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        (insider_dcprog (SUC foo) ((h,b),r) = out)}
                {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                        ~(insider_dcprog (SUC foo) ((h,b),r) = out)}`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
                    >> Cases_on `insider_dcprog (SUC foo)
                                        ((FST x,b),SND x) = out`
                    >- (DISJ2_TAC >> STRIP_TAC
                        >> `x':bool state # bool state = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                        >> POP_ORW >> RW_TAC std_ss [PAIR_EQ] >> METIS_TAC [PAIR, PAIR_EQ])
                    >> DISJ1_TAC >> STRIP_TAC
                    >> `x':bool state # bool state = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ] >> METIS_TAC [PAIR, PAIR_EQ])
            >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
            >> `SIGMA (λ(h,r). (if insider_dcprog (SUC foo)
                        ((h,b),r) = out then 1 else 0))
                {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~(insider_dcprog (SUC foo)
                        ((h,b),r) = out)} = 0`
                by (RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
                    >> Suff `!x. (if x IN
                        {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~(insider_dcprog (SUC foo)
                        ((h,b),r) = out)} then
                        (λ(h,r). (if insider_dcprog (SUC foo)
                        ((h,b),r) =
                        out then 1 else 0)) x else 0) = 0`
                    >- RW_TAC std_ss [REAL_SUM_IMAGE_0]
                    >> RW_TAC std_ss [GSPECIFICATION]
                    >> POP_ASSUM MP_TAC >> `x':bool state # bool state = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                    >> `x:bool state # bool state = (FST x, SND x)` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [])
            >> POP_ORW >> RW_TAC real_ss []
            >> Suff `(\x. (if x IN {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        (insider_dcprog (SUC foo) ((h,b),r) = out)}
                        then 1 else 0)) =
                     (\x. (if x IN {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        (insider_dcprog (SUC foo) ((h,b),r) = out)}
                        then (λ(h,r). (if insider_dcprog (SUC foo)
                                ((h,b),r) =
                        out then 1 else 0)) x else 0))`
             >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                 >> METIS_TAC [])
             >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [GSPECIFICATION]
             >> POP_ASSUM MP_TAC >> `x':bool state # bool state = (FST x', SND x')` by RW_TAC std_ss [PAIR]
             >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
             >> `x:bool state # bool state = (FST x, SND x)` by RW_TAC std_ss [PAIR]
             >> POP_ORW >> RW_TAC std_ss [])
   >> POP_ORW
   >> `!(x:bool state # bool state) (b:bool state).
        &(CARD {r | r IN biased_random_states foo /\
                  (insider_dcprog (SUC foo)
                     ((SND x,b),r) = FST x)}) =
        REAL_SUM_IMAGE
        (\r. if (insider_dcprog (SUC foo)
                        ((SND x,b),r) = FST x) then 1 else 0)
        (biased_random_states foo)`
        by (STRIP_TAC >> STRIP_TAC
            >> `FINITE {r | r IN biased_random_states foo /\
                            (insider_dcprog (SUC foo) ((SND x,b),r) = FST x)}`
                   by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
            >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
            >> `FINITE {r | r IN biased_random_states foo /\
                            ~(insider_dcprog (SUC foo) ((SND x,b),r) = FST x)}`
                   by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
            >>  Q.ABBREV_TAC `s = {r | r IN biased_random_states foo /\
                                (insider_dcprog (SUC foo) ((SND x,b),r) = FST x)}`
            >> `(biased_random_states foo) =
                {r | r IN biased_random_states foo /\
                            (insider_dcprog (SUC foo) ((SND x,b),r) = FST x)} UNION
                {r | r IN biased_random_states foo /\
                            ~(insider_dcprog (SUC foo) ((SND x,b),r) = FST x)}`
                by (Q.UNABBREV_TAC `s` >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION] >> DECIDE_TAC)
            >> POP_ORW
            >> Q.UNABBREV_TAC `s`
            >> `DISJOINT {r | r IN biased_random_states foo /\
                            (insider_dcprog (SUC foo) ((SND x,b),r) = FST x)}
                {r | r IN biased_random_states foo /\
                            ~(insider_dcprog (SUC foo) ((SND x,b),r) = FST x)}`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
                    >> METIS_TAC [])
            >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
            >> `SIGMA (\r. (if insider_dcprog (SUC foo) ((SND x,b),r) = FST x then 1 else 0))
                {r | r IN biased_random_states foo /\
                            ~(insider_dcprog (SUC foo) ((SND x,b),r) = FST x)} = 0`
                by (RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
                    >> Suff `!r. (if r IN
                        {r | r IN biased_random_states foo /\
                            ~(insider_dcprog (SUC foo) ((SND x,b),r) = FST x)} then
                        (if insider_dcprog (SUC foo)
                        ((SND x,b),r) =
                        FST x then 1 else 0) else 0) = 0`
                    >- RW_TAC std_ss [REAL_SUM_IMAGE_0]
                    >> RW_TAC std_ss [GSPECIFICATION])
            >> POP_ORW >> RW_TAC real_ss []
            >> Suff `(\x'. (if x' IN {r | r IN biased_random_states foo /\
                            (insider_dcprog (SUC foo) ((SND x,b),r) = FST x)}
                        then 1 else 0)) =
                     (\x'. (if x' IN {r | r IN biased_random_states foo /\
                            (insider_dcprog (SUC foo) ((SND x,b),r) = FST x)}
                        then (\r. (if insider_dcprog (SUC foo) ((SND x,b),r) = FST x then 1 else 0)) x' else 0))`
             >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                 >> METIS_TAC [])
             >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [GSPECIFICATION])
   >> POP_ORW
   >> Q.UNABBREV_TAC `foo`
   >> Q.ABBREV_TAC `s1 = (IMAGE (insider_dcprog (SUC (SUC (SUC 0))))
         (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
          biased_random_states (SUC (SUC 0))))`
   >> Q.ABBREV_TAC `s2 = (s1 CROSS biased_high_states (SUC (SUC 0)))`
   >> RW_TAC bool_ss [biased_high_states_def, biased_random_states_def, insider_high_states_set_def,
                      insider_dcprog_def, compute_result_alt, insider_set_announcements_alt, XOR_announces_def,
                      H_def, L_def, PAIR, ETA_THM, xor_def, STRCAT_toString_inj]
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)))))
   >> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                         THENC ((ONCE_FIND_CONV ``x DELETE y``
                                (DELETE_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))
                         THENC SIMP_CONV arith_ss []))
   >> Q.UNABBREV_TAC `s2` >> Q.UNABBREV_TAC `s1`
   >> RW_TAC bool_ss [biased_high_states_def, biased_low_states_def, biased_random_states_def, insider_high_states_set_def,
                      insider_dcprog_def, compute_result_alt, insider_set_announcements_alt, XOR_announces_def,
                      H_def, L_def, PAIR, ETA_THM, xor_def, STRCAT_toString_inj]
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)))))
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)))))
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))))
  >> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                         THENC ((ONCE_FIND_CONV ``x DELETE y``
                                (DELETE_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))
                         THENC SIMP_CONV arith_ss []))
   >> CONV_TAC (ONCE_FIND_CONV ``if (x=y) then (1:real) else 0`` (RATOR_CONV (RATOR_CONV (RAND_CONV
        (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
         THENC EVAL
         THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
         THENC EVAL
         THENC (REPEATC (T_F_UNCHANGED_CONV
         (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
         THENC EVAL))))))
                                                                  THENC SIMP_CONV bool_ss []))
   >> RW_TAC real_ss []
   >> Q.UNABBREV_TAC `c4` >> Q.UNABBREV_TAC `c3` >> Q.UNABBREV_TAC `c2` >> Q.UNABBREV_TAC `c1`
   >> RW_TAC real_ss []
   >> `lg(1/4) = ~2` by (RW_TAC real_ss [GSYM REAL_INV_1OVER, lg_inv] >> `4 = 2 pow 2` by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
   >> POP_ORW
   >> RW_TAC real_ss []);

(* ************************************************************************* *)
(* Biasing a hidden coin creates a partial leak                              *)
(* ************************************************************************* *)

val biased_dist2_def = Define
   `biased_dist2 high low random =
        (\s. if R s (STRCAT "coin" (toString (SUC 0))) then
                (1 / 2) * (unif_prog_dist high low random s)
             else
                (3 / 2) * (unif_prog_dist high low random s))`;

val biased_dc_prog_space2_def = Define
   `biased_dc_prog_space2 (SUC(SUC n)) =
        (((biased_high_states (SUC(SUC n))) CROSS biased_low_states) CROSS (biased_random_states (SUC (SUC n))),
         POW (((biased_high_states (SUC(SUC n))) CROSS biased_low_states) CROSS (biased_random_states (SUC (SUC n)))),
         (\s. SIGMA (biased_dist2 (biased_high_states (SUC(SUC n)))
   biased_low_states (biased_random_states (SUC (SUC n)))) s))`;

val prob_space_biased_dc_prog_space23 = store_thm
  ("prob_space_biased_dc_prog_space23",
   ``prob_space (biased_dc_prog_space2 (SUC(SUC 0)))``,
   (RW_TAC bool_ss [prob_space_def]
    >> `FINITE ((biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0))))`
        by RW_TAC set_ss [biased_high_states_def, biased_low_states_def,
                             biased_random_states_def, insider_high_states_set_def])
   >- (MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces2
       >> RW_TAC bool_ss [biased_dc_prog_space2_def, m_space_def, measurable_sets_def, POW_SIGMA_ALGEBRA,
                          PSPACE, measure_def, positive_def, REAL_SUM_IMAGE_THM, IN_POW,
                          additive_def, IN_FUNSET, IN_UNIV]
       >- (MATCH_MP_TAC REAL_SUM_IMAGE_POS
           >> CONJ_TAC
           >- METIS_TAC [SUBSET_FINITE]
           >> RW_TAC real_ss [biased_dist2_def, unif_prog_dist_def, GSYM REAL_INV_1OVER, REAL_LE_INV_EQ, REAL_LE_MUL])
       >> METIS_TAC [SUBSET_FINITE, REAL_SUM_IMAGE_DISJOINT_UNION])
   >> RW_TAC bool_ss [biased_dc_prog_space2_def, m_space_def, measurable_sets_def,
                      PSPACE, measure_def, biased_dist2_def]
   >> `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0))) =
        (((biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
         biased_random_states (SUC (SUC 0))))INTER
         {s| R s (STRCAT "coin" (toString (SUC 0)))}) UNION
        (((biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0))))INTER{s| ~R s (STRCAT "coin" (toString (SUC 0)))})`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_INTER, GSPECIFICATION] >> DECIDE_TAC)
   >> POP_ORW
   >> `FINITE (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | R s (STRCAT "coin" (toString (SUC 0)))}) /\
        FINITE (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | ~R s (STRCAT "coin" (toString (SUC 0)))})`
        by RW_TAC std_ss [INTER_FINITE]
   >> `DISJOINT (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | R s (STRCAT "coin" (toString (SUC 0)))})
        (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | ~R s (STRCAT "coin" (toString (SUC 0)))})`
        by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
            >> DECIDE_TAC)
   >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | R s (STRCAT "coin" (toString (SUC 0)))}`) REAL_SUM_IMAGE_IN_IF]
   >> RW_TAC bool_ss [unif_prog_dist_def]
   >> `(\x.
     if
       x IN
       biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
       biased_random_states (SUC (SUC 0)) INTER
       {s | R s (STRCAT "coin" (toString (SUC 0)))}
     then
       if R x (STRCAT "coin" (toString (SUC 0))) then
         1 / 2 *
         if
           x IN
           biased_high_states (SUC (SUC 0)) CROSS
           biased_low_states CROSS biased_random_states (SUC (SUC 0))
         then
           1 /
           &CARD
              (biased_high_states (SUC (SUC 0)) CROSS
               biased_low_states CROSS
               biased_random_states (SUC (SUC 0)))
         else
           0
       else
         3 / 2 *
         if
           x IN
           biased_high_states (SUC (SUC 0)) CROSS
           biased_low_states CROSS biased_random_states (SUC (SUC 0))
         then
           1 /
           &CARD
              (biased_high_states (SUC (SUC 0)) CROSS
               biased_low_states CROSS
               biased_random_states (SUC (SUC 0)))
         else
           0
     else
       0) =
        (\s. (if s IN
        biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | R s (STRCAT "coin" (toString (SUC 0)))}
      then
        (\s. 1 / 2 * (1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0)))))) s
      else 0))`
        by (RW_TAC bool_ss [Once FUN_EQ_THM]
            >> RW_TAC arith_ss [IN_INTER, GSPECIFICATION])
   >> POP_ORW
   >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> RW_TAC bool_ss [REAL_SUM_IMAGE_FINITE_CONST3]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s |~ R s (STRCAT "coin" (toString (SUC 0)))}`) REAL_SUM_IMAGE_IN_IF]
   >> RW_TAC bool_ss [unif_prog_dist_def]
   >> `(\s.
     (if
        s IN
        biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | ~R s (STRCAT "coin" (toString (SUC 0)))}
      then
        (if R s (STRCAT "coin" (toString (SUC 0))) then
           1 / 2 *
           (if
              s IN
              biased_high_states (SUC (SUC 0)) CROSS
              biased_low_states CROSS biased_random_states (SUC (SUC 0))
            then
              1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0))))
            else
              0)
         else
           3/2 *
           (if
              s IN
              biased_high_states (SUC (SUC 0)) CROSS
              biased_low_states CROSS biased_random_states (SUC (SUC 0))
            then
              1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0))))
            else
              0))
      else
        0)) =
        (\s. (if s IN
        biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
        biased_random_states (SUC (SUC 0)) INTER
        {s | ~R s (STRCAT "coin" (toString (SUC 0)))}
      then
        (\s. 3/2 * (1 /
              &
                (CARD
                   (biased_high_states (SUC (SUC 0)) CROSS
                    biased_low_states CROSS
                    biased_random_states (SUC (SUC 0)))))) s
      else 0))`
        by (RW_TAC bool_ss [Once FUN_EQ_THM]
            >> RW_TAC bool_ss [IN_INTER, GSPECIFICATION])
   >> POP_ORW
   >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> RW_TAC bool_ss [REAL_SUM_IMAGE_FINITE_CONST3]
   >> `!b. & (CARD
     (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
      biased_random_states (SUC (SUC 0)) INTER
      {s | R s b})) =
        REAL_SUM_IMAGE
        (\s. if R s b then 1 else 0)
        (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
      biased_random_states (SUC (SUC 0)))`
        by (STRIP_TAC
            >> `FINITE (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER
                {s | R s b})`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                        biased_random_states (SUC (SUC 0)))`) SUBSET_FINITE
                       >> RW_TAC std_ss [FINITE_CROSS] >> POP_ASSUM MATCH_MP_TAC
                       >> RW_TAC std_ss [SUBSET_DEF, IN_INTER])
            >> `FINITE (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER
                {s | ~R s b})`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                        biased_random_states (SUC (SUC 0)))`) SUBSET_FINITE
                       >> RW_TAC std_ss [FINITE_CROSS] >> POP_ASSUM MATCH_MP_TAC
                       >> RW_TAC std_ss [SUBSET_DEF, IN_INTER])
            >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
            >>  Q.ABBREV_TAC `s = (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                                biased_random_states (SUC (SUC 0)) INTER {s | R s b})`
            >> `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0))) =
                (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER {s | R s b}) UNION
                (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER {s | ~R s b})`
                by (Q.UNABBREV_TAC `s` >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_INTER, GSPECIFICATION] >> DECIDE_TAC)
            >> POP_ORW
            >> Q.UNABBREV_TAC `s`
            >> `DISJOINT (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER {s | R s b})
                (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER {s | ~R s b})`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
                    >> METIS_TAC [])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
            >> `SIGMA (\s. (if R s b then 1 else 0))
                        (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                        biased_random_states (SUC (SUC 0)) INTER {s | ~R s b}) = 0`
                by (RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
                    >> RW_TAC bool_ss [IN_INTER, GSPECIFICATION, REAL_SUM_IMAGE_0])
            >> POP_ORW >> RW_TAC real_ss []
            >> FULL_SIMP_TAC std_ss []
            >> Suff `(\x. (if x IN biased_high_states 2 CROSS biased_low_states CROSS
                        biased_random_states 2 INTER {s | R s b}
                        then 1 else 0)) =
                     (\x. (if x IN biased_high_states 2 CROSS biased_low_states CROSS
                        biased_random_states 2 INTER {s | R s b}
                        then (\s. if R s b then 1 else 0) x else 0))`
             >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                 >> METIS_TAC [])
             >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_INTER,GSPECIFICATION])
   >> POP_ORW
   >> `!b. & (CARD
     (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
      biased_random_states (SUC (SUC 0)) INTER
      {s | ~R s b})) =
        REAL_SUM_IMAGE
        (\s. if ~R s b then 1 else 0)
        (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
      biased_random_states (SUC (SUC 0)))`
        by (STRIP_TAC
            >> `FINITE (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER
                {s | R s b})`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                        biased_random_states (SUC (SUC 0)))`) SUBSET_FINITE
                       >> RW_TAC std_ss [FINITE_CROSS] >> POP_ASSUM MATCH_MP_TAC
                       >> RW_TAC std_ss [SUBSET_DEF, IN_INTER])
            >> `FINITE (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER
                {s | ~R s b})`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                        biased_random_states (SUC (SUC 0)))`) SUBSET_FINITE
                       >> RW_TAC std_ss [FINITE_CROSS] >> POP_ASSUM MATCH_MP_TAC
                       >> RW_TAC std_ss [SUBSET_DEF, IN_INTER])
            >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
            >>  Q.ABBREV_TAC `s = (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                                biased_random_states (SUC (SUC 0)) INTER {s | ~R s b})`
            >> `(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0))) =
                (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER {s | R s b}) UNION
                (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER {s | ~R s b})`
                by (Q.UNABBREV_TAC `s` >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_INTER, GSPECIFICATION] >> DECIDE_TAC)
            >> POP_ORW
            >> Q.UNABBREV_TAC `s`
            >> `DISJOINT (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER {s | R s b})
                (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0)) INTER {s | ~R s b})`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
                    >> METIS_TAC [])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
            >> `SIGMA (\s. (if ~R s b then 1 else 0))
                        (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                        biased_random_states (SUC (SUC 0)) INTER {s | R s b}) = 0`
                by (RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
                    >> RW_TAC bool_ss [IN_INTER, GSPECIFICATION, REAL_SUM_IMAGE_0])
            >> POP_ORW >> RW_TAC real_ss []
            >> FULL_SIMP_TAC std_ss []
            >> Suff `(\x. (if x IN biased_high_states 2 CROSS biased_low_states CROSS
                        biased_random_states 2 INTER {s | ~R s b}
                        then 1 else 0)) =
                     (\x. (if x IN biased_high_states 2 CROSS biased_low_states CROSS
                        biased_random_states 2 INTER {s | ~R s b}
                        then (\s. if ~R s b then 1 else 0) x else 0))`
             >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                 >> METIS_TAC [])
             >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [IN_INTER,GSPECIFICATION])
   >> POP_ORW
   >> RW_TAC bool_ss [          (COMPUTE_CARD ``(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                                biased_random_states (SUC (SUC 0)))``
                              (SIMP_CONV bool_ss [biased_high_states_def, biased_low_states_def,
                                biased_random_states_def, insider_high_states_set_def] THENC
                                SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv))))
                THENC SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
         THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV dc_dup_conv)))))
                dc_dup_conv)]
   >> RW_TAC bool_ss [biased_high_states_def, biased_low_states_def, biased_random_states_def, insider_high_states_set_def,
                      insider_dcprog_def, compute_result_alt, insider_set_announcements_alt, XOR_announces_def,
                      H_def, L_def, R_def, PAIR, ETA_THM, xor_def, STRCAT_toString_inj]
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   H_def, L_def, R_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)))))
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   H_def, L_def, R_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)))))
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   H_def, L_def, R_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))))
  >> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                         THENC ((ONCE_FIND_CONV ``x DELETE y``
                                (DELETE_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))
                         THENC SIMP_CONV arith_ss []))
   >> RW_TAC real_ss [STRCAT_toString_inj]);

(* ------------------------------------------------------------------------- *)

val biased_dc3_leakage_result2 = store_thm
  ("biased_dc3_leakage_result2",
   ``(leakage (biased_dc_prog_space2 (SUC (SUC 0))) (insider_dcprog (SUC(SUC(SUC 0)))) = 3 / 4 * lg 3 - 1)``,
   RW_TAC bool_ss [leakage_def]
   >> Q.ABBREV_TAC `v = 3 / 4 * lg 3 - 1`
   >> `FINITE ((biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                biased_random_states (SUC (SUC 0))))`
        by RW_TAC set_ss [biased_high_states_def, biased_low_states_def,
                             biased_random_states_def, insider_high_states_set_def]
   >> `FINITE (biased_high_states (SUC (SUC 0)))`
        by RW_TAC set_ss [biased_high_states_def, insider_high_states_set_def]
   >> `FINITE (biased_random_states (SUC (SUC 0)))`
        by RW_TAC set_ss [biased_random_states_def]
   >> `FINITE (biased_low_states)`
        by RW_TAC set_ss [biased_low_states_def]
   >> (MP_TAC o
       Q.SPECL [`2`,`(biased_dc_prog_space2 (SUC (SUC 0)))`, `(insider_dcprog (SUC (SUC (SUC 0))))`, `H`,`L`] o
       INST_TYPE [alpha |-> ``:(bool, bool, bool) prog_state``, beta |-> ``:bool state``, gamma |-> ``:bool state``,
                  delta |-> ``:bool state``])
        finite_conditional_mutual_information_reduce
   >> (MP_TAC o INST_TYPE [beta |-> ``:bool state``] o Q.ISPEC `(biased_dc_prog_space2 (SUC (SUC 0)))`)
        MEASURABLE_POW_TO_POW_IMAGE
   >> RW_TAC bool_ss [random_variable_def, prob_space_biased_dc_prog_space23, biased_dc_prog_space2_def, PSPACE, EVENTS,
                      prob_space_def, measurable_sets_def, m_space_def,
                      REWRITE_RULE [prob_space_def] prob_space_biased_dc_prog_space23]
   >> POP_ASSUM (K ALL_TAC)
   >> RW_TAC bool_ss [biased_dist2_def, unif_prog_dist_def,
        (COMPUTE_CARD ``(biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
                                biased_random_states (SUC (SUC 0)))``
                              (SIMP_CONV bool_ss [biased_high_states_def, biased_low_states_def,
                                biased_random_states_def, insider_high_states_set_def] THENC
                                SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv))))
                THENC SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY]
         THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV dc_dup_conv)))))
                dc_dup_conv)]
   >> Q.ABBREV_TAC `foo = (SUC (SUC 0))`
   >> RW_TAC std_ss [joint_distribution_def, L_def, H_def, R_def, PAIR, ETA_THM, FST, SND, PROB, PSPACE, distribution_def]
   >> `IMAGE L
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo) =
        biased_low_states`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE, IN_CROSS, L_def]
            >> EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss []
            >> Q.UNABBREV_TAC `foo`
            >> Q.EXISTS_TAC `(((\s:string. s = STRCAT "pays" (toString (SUC (SUC 0)))),x),(\s:string. F))`
            >> RW_TAC bool_ss [SND, FST, biased_high_states_def, insider_high_states_set_def, IN_INSERT]
            >> Suff `!n. (\s:string. F) IN biased_random_states n` >- RW_TAC std_ss []
            >> REPEAT (POP_ASSUM (K ALL_TAC))
            >> Induct >> RW_TAC bool_ss [biased_random_states_def, IN_SING, IN_IMAGE, IN_UNION]
            >> DISJ2_TAC >> Q.EXISTS_TAC `(\s:string.F)` >> RW_TAC std_ss [])
   >> POP_ORW
   >> `(IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo) CROSS
      IMAGE FST
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo)) =
        (IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo) CROSS
      (biased_high_states foo CROSS biased_low_states))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE, IN_CROSS, FST]
            >> EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss []
            >> Q.EXISTS_TAC `(SND x, SND x')`
            >> RW_TAC bool_ss [SND, FST])
   >> POP_ORW
   >> `!x z.
        SIGMA
          (\s.
             (if SND s (STRCAT "coin" (toString 1)) then
                1 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)
              else
                3 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)))
          (PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
           PREIMAGE L {z} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo)) =
        (if z IN biased_low_states then
                1/32 * &(CARD {(h,r)| h IN biased_high_states foo /\ r IN biased_random_states foo /\
                       r (STRCAT "coin" (toString 1)) /\
                            (insider_dcprog (SUC foo) ((h,z),r) = x)}) +
                3/32 * &(CARD {(h,r)| h IN biased_high_states foo /\ r IN biased_random_states foo /\
                       ~ r (STRCAT "coin" (toString 1)) /\
                            (insider_dcprog (SUC foo) ((h,z),r) = x)}) else 0)`
        by (reverse (RW_TAC real_ss [])
            >- (RW_TAC bool_ss [GSYM INTER_ASSOC]
                >> Suff `PREIMAGE L {z} INTER (biased_high_states foo CROSS biased_low_states CROSS
                                                biased_random_states foo) = {}`
                >- RW_TAC bool_ss [INTER_EMPTY, REAL_SUM_IMAGE_THM]
                >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [NOT_IN_EMPTY, L_def, IN_CROSS, IN_INTER, IN_PREIMAGE]
                >> METIS_TAC [])
            >> `(PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
                 PREIMAGE L {z} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 (IMAGE (λ(h,r). ((h, z),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)}) UNION
                 (IMAGE (λ(h,r). ((h, z),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)})`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, L_def, IN_UNION]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Cases_on `SND x' (STRCAT "coin" (toString 1))`
                         >- (DISJ1_TAC >> Q.EXISTS_TAC `(FST(FST x'), SND x')`
                             >> RW_TAC std_ss [PAIR]
                             >> Q.EXISTS_TAC `(FST (FST x'),SND x')`
                             >> RW_TAC std_ss [PAIR_EQ])
                         >> DISJ2_TAC >> Q.EXISTS_TAC `(FST(FST x'), SND x')`
                         >> RW_TAC std_ss [PAIR]
                         >> Q.EXISTS_TAC `(FST (FST x'),SND x')`
                         >> RW_TAC std_ss [PAIR_EQ])
                     >>  POP_ASSUM MP_TAC
                     >> `x''' = (FST x''',SND x''')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [FST,SND, PAIR_EQ]
                     >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
            >> POP_ORW
            >> `FINITE {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)} /\
                FINITE {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)}`
                by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                     >> RW_TAC bool_ss [FINITE_CROSS]
                     >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                     >> POP_ASSUM MP_TAC
                     >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [FST,SND, PAIR_EQ]
                     >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
            >> `DISJOINT (IMAGE (λ(h,r). ((h, z),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)})
                         (IMAGE (λ(h,r). ((h, z),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)})`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, IN_IMAGE, GSPECIFICATION]
                    >> Cases_on `SND x' (STRCAT "coin" (toString 1))`
                    >- (DISJ2_TAC >> STRIP_TAC >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                        >> POP_ORW >> RW_TAC std_ss [] >> reverse (Cases_on `x' = ((FST x'',z),SND x'')`) >> RW_TAC std_ss []
                        >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                        >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                        >> METIS_TAC [FST, SND, PAIR_EQ, PAIR])
                    >> DISJ1_TAC >> STRIP_TAC >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [] >> reverse (Cases_on `x' = ((FST x'',z),SND x'')`) >> RW_TAC std_ss []
                    >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                    >> METIS_TAC [FST, SND, PAIR_EQ, PAIR])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION, IMAGE_FINITE] >> POP_ASSUM (K ALL_TAC)
            >> `INJ (λ(h,r). ((h,z),r)) {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)}
                    (IMAGE (λ(h,r). ((h,z),r)) {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)}) /\
                INJ (λ(h,r). ((h,z),r)) {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)}
                    (IMAGE (λ(h,r). ((h,z),r)) {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((h,z),r) = x)})`
                by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE]
                    >| [METIS_TAC [],
                        POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(y :bool state # bool state) = (FST y,SND y)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> METIS_TAC [PAIR, PAIR_EQ],
                        METIS_TAC [],
                        POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(y :bool state # bool state) = (FST y,SND y)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> METIS_TAC [PAIR, PAIR_EQ]])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_IMAGE, IMAGE_FINITE, o_DEF] >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (K ALL_TAC)
            >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
            >> `!x': bool state # bool state.
                (if x' IN {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                   r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x)}
                then (if SND ((λ(h,r). ((h,z),r)) x') (STRCAT "coin" (toString 1)) then
                1 / 2 * (if (λ(h,r). ((h,z),r)) x' IN biased_high_states foo CROSS biased_low_states CROSS
                                                        biased_random_states foo
                then 1 / 16 else 0) else 3 / 2 *
                (if (λ(h,r). ((h,z),r)) x' IN biased_high_states foo CROSS biased_low_states CROSS biased_random_states foo
                then 1 / 16 else 0)) else 0) =
                1/32 * (\x'. if
                 x' IN {(h,r) |
                    h IN biased_high_states foo /\ r IN biased_random_states foo /\
                       r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((h,z),r) = x)}
                then (\x'. 1) x' else 0) x'`
                by (STRIP_TAC >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC real_ss [GSPECIFICATION, IN_CROSS]
                    >> POP_ASSUM MP_TAC >> RW_TAC std_ss []
                    >> `(x'':bool state # bool state) = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                    >> METIS_TAC [])
            >> POP_ORW >> RW_TAC bool_ss [REAL_SUM_IMAGE_CMUL, GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3]
            >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
            >> `!x': bool state # bool state.
                (if x' IN {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                   ~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x)}
                then (if SND ((λ(h,r). ((h,z),r)) x') (STRCAT "coin" (toString 1)) then
                1 / 2 * (if (λ(h,r). ((h,z),r)) x' IN biased_high_states foo CROSS biased_low_states CROSS
                                                        biased_random_states foo
                then 1 / 16 else 0) else 3 / 2 *
                (if (λ(h,r). ((h,z),r)) x' IN biased_high_states foo CROSS biased_low_states CROSS biased_random_states foo
                then 1 / 16 else 0)) else 0) =
                3/32 * (\x'. if
                 x' IN {(h,r) |
                    h IN biased_high_states foo /\ r IN biased_random_states foo /\
                       ~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((h,z),r) = x)}
                then (\x'. 1) x' else 0) x'`
                by (STRIP_TAC >> `(x' :bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC real_ss [GSPECIFICATION, IN_CROSS]
                    >> POP_ASSUM MP_TAC >> RW_TAC std_ss []
                    >> `(x'':bool state # bool state) = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                    >> METIS_TAC [])
            >> POP_ORW >> RW_TAC bool_ss [REAL_SUM_IMAGE_CMUL, GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3]
            >> RW_TAC real_ss [])
   >> `!x z. (PREIMAGE (\x. (insider_dcprog (SUC foo) x,SND (FST x)))
           {(x,z)} INTER
         (biased_high_states foo CROSS biased_low_states CROSS
          biased_random_states foo)) =
        (PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
           PREIMAGE L {z} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_CROSS, IN_PREIMAGE, IN_SING, L_def])
   >> POP_ORW
   >> POP_ORW
   >> `!x z.
        SIGMA
          (\s.
             (if SND s (STRCAT "coin" (toString 1)) then
                1 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)
              else
                3 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)))
          (PREIMAGE L {z} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo)) =
        (if z IN biased_low_states then
                1/32 * & (CARD (biased_high_states foo)) *
                        &(CARD {r| r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}) +
                3/32 * & (CARD (biased_high_states foo)) *
                        &(CARD {r| r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))})
         else 0)`
        by (reverse (RW_TAC real_ss [])
            >- (Suff `PREIMAGE L {z} INTER (biased_high_states foo CROSS biased_low_states CROSS
                                                biased_random_states foo) = {}`
                >- RW_TAC bool_ss [INTER_EMPTY, REAL_SUM_IMAGE_THM]
                >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [NOT_IN_EMPTY, L_def, IN_CROSS, IN_INTER, IN_PREIMAGE]
                >> METIS_TAC [])
            >> `(PREIMAGE L {z} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 (IMAGE (λ(h,r). ((h, z),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))}) UNION
                 (IMAGE (λ(h,r). ((h, z),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))})`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, L_def, IN_UNION]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >- (Cases_on `SND x (STRCAT "coin" (toString 1))`
                         >- (DISJ1_TAC >> Q.EXISTS_TAC `(FST(FST x), SND x)`
                             >> RW_TAC std_ss [PAIR]
                             >> Q.EXISTS_TAC `(FST (FST x),SND x)`
                             >> RW_TAC std_ss [PAIR_EQ])
                         >> DISJ2_TAC >> Q.EXISTS_TAC `(FST(FST x), SND x)`
                         >> RW_TAC std_ss [PAIR]
                         >> Q.EXISTS_TAC `(FST (FST x),SND x)`
                         >> RW_TAC std_ss [PAIR_EQ])
                     >>  POP_ASSUM MP_TAC
                     >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [FST,SND, PAIR_EQ]
                     >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
            >> POP_ORW
            >> `FINITE {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))} /\
                FINITE {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))}`
                by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                     >> RW_TAC bool_ss [FINITE_CROSS]
                     >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                     >> POP_ASSUM MP_TAC
                     >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [FST,SND, PAIR_EQ]
                     >> `x = (FST x,SND x)` by RW_TAC std_ss [PAIR]
                     >> POP_ORW >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
            >> `DISJOINT (IMAGE (λ(h,r). ((h, z),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))})
                         (IMAGE (λ(h,r). ((h, z),r))
                        {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))})`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, IN_IMAGE, GSPECIFICATION]
                    >> Cases_on `SND x (STRCAT "coin" (toString 1))`
                    >- (DISJ2_TAC >> STRIP_TAC >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                        >> POP_ORW >> RW_TAC std_ss [] >> reverse (Cases_on `x = ((FST x',z),SND x')`) >> RW_TAC std_ss []
                        >> `x = (FST x,SND x)` by RW_TAC std_ss [PAIR]
                        >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                        >> METIS_TAC [FST, SND, PAIR_EQ, PAIR])
                    >> DISJ1_TAC >> STRIP_TAC >> `x' = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [] >> reverse (Cases_on `x = ((FST x',z),SND x')`) >> RW_TAC std_ss []
                    >> `x = (FST x,SND x)` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                    >> METIS_TAC [FST, SND, PAIR_EQ, PAIR])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION, IMAGE_FINITE] >> POP_ASSUM (K ALL_TAC)
            >> `INJ (λ(h,r). ((h,z),r)) {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))}
                    (IMAGE (λ(h,r). ((h,z),r)) {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))}) /\
                INJ (λ(h,r). ((h,z),r)) {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))}
                    (IMAGE (λ(h,r). ((h,z),r)) {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))})`
                by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE]
                    >| [METIS_TAC [],
                        POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(x :bool state # bool state) = (FST x,SND x)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(y :bool state # bool state) = (FST y,SND y)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> METIS_TAC [PAIR, PAIR_EQ],
                        METIS_TAC [],
                        POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(x :bool state # bool state) = (FST x,SND x)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC
                            >> `(y :bool state # bool state) = (FST y,SND y)` by RW_TAC std_ss [PAIR]
                            >> POP_ORW >> RW_TAC std_ss []
                            >> METIS_TAC [PAIR, PAIR_EQ]])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_IMAGE, IMAGE_FINITE, o_DEF] >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (K ALL_TAC)
            >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
            >> `!x: bool state # bool state.
                (if x IN {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                   r (STRCAT "coin" (toString 1))}
                then (if SND ((λ(h,r). ((h,z),r)) x) (STRCAT "coin" (toString 1)) then
                1 / 2 * (if (λ(h,r). ((h,z),r)) x IN biased_high_states foo CROSS biased_low_states CROSS
                                                        biased_random_states foo
                then 1 / 16 else 0) else 3 / 2 *
                (if (λ(h,r). ((h,z),r)) x IN biased_high_states foo CROSS biased_low_states CROSS biased_random_states foo
                then 1 / 16 else 0)) else 0) =
                1/32 * (\x. if
                 x IN {(h,r) |
                    h IN biased_high_states foo /\ r IN biased_random_states foo /\
                       r (STRCAT "coin" (toString 1))}
                then (\x. 1) x else 0) x`
                by (STRIP_TAC >> `(x :bool state # bool state) = (FST x,SND x)` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC real_ss [GSPECIFICATION, IN_CROSS]
                    >> POP_ASSUM MP_TAC >> RW_TAC std_ss []
                    >> `(x':bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                    >> METIS_TAC [])
            >> POP_ORW >> RW_TAC bool_ss [REAL_SUM_IMAGE_CMUL, GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3]
            >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
            >> `!x: bool state # bool state.
                (if x IN {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                                   ~r (STRCAT "coin" (toString 1))}
                then (if SND ((λ(h,r). ((h,z),r)) x) (STRCAT "coin" (toString 1)) then
                1 / 2 * (if (λ(h,r). ((h,z),r)) x IN biased_high_states foo CROSS biased_low_states CROSS
                                                        biased_random_states foo
                then 1 / 16 else 0) else 3 / 2 *
                (if (λ(h,r). ((h,z),r)) x IN biased_high_states foo CROSS biased_low_states CROSS biased_random_states foo
                then 1 / 16 else 0)) else 0) =
                3/32 * (\x'. if
                 x IN {(h,r) |
                    h IN biased_high_states foo /\ r IN biased_random_states foo /\
                       ~r (STRCAT "coin" (toString 1))}
                then (\x. 1) x else 0) x`
                by (STRIP_TAC >> `(x :bool state # bool state) = (FST x,SND x)` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC real_ss [GSPECIFICATION, IN_CROSS]
                    >> POP_ASSUM MP_TAC >> RW_TAC std_ss []
                    >> `(x':bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                    >> METIS_TAC [])
            >> POP_ORW >> RW_TAC bool_ss [REAL_SUM_IMAGE_CMUL, GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3]
            >> RW_TAC real_ss []
            >> `{(h,r) |  h IN biased_high_states foo /\ r IN biased_random_states foo /\
                          r (STRCAT "coin" (toString 1))} =
                (biased_high_states foo) CROSS {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [GSPECIFICATION, IN_CROSS]
                    >> reverse (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                    >- (Q.EXISTS_TAC `(FST x, SND x)` >> RW_TAC std_ss [PAIR_EQ])
                    >> POP_ASSUM MP_TAC >> `(x':bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ])
            >> POP_ORW
            >> `{(h,r) |  h IN biased_high_states foo /\ r IN biased_random_states foo /\
                          ~r (STRCAT "coin" (toString 1))} =
                (biased_high_states foo) CROSS {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [GSPECIFICATION, IN_CROSS]
                    >> reverse (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                    >- (Q.EXISTS_TAC `(FST x, SND x)` >> RW_TAC std_ss [PAIR_EQ])
                    >> POP_ASSUM MP_TAC >> `(x':bool state # bool state) = (FST x',SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ])
             >> POP_ORW
             >> `FINITE {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))} /\
                 FINITE {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}`
                by (CONJ_TAC
                    >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                    >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
             >> RW_TAC std_ss [CARD_CROSS, GSYM REAL_MUL, REAL_MUL_ASSOC, REAL_MUL_COMM])
   >> POP_ORW
   >> `!x y z.
        SIGMA
          (\s.
             (if SND s (STRCAT "coin" (toString 1)) then
                1 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)
              else
                3 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)))
          (PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
           PREIMAGE FST {(y,z)} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo)) =
        (if z IN biased_low_states /\ y IN (biased_high_states foo) then
                1/32 * & (CARD {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1)) /\
                                    (insider_dcprog (SUC foo) ((y,z),r) = x)})
                + 3/32 * & (CARD {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1)) /\
                                      (insider_dcprog (SUC foo) ((y,z),r) = x)})
         else 0)`
        by (reverse (RW_TAC real_ss [])
            >- (RW_TAC bool_ss [GSYM INTER_ASSOC]
                >> Suff `PREIMAGE FST {(y,z)} INTER (biased_high_states foo CROSS biased_low_states CROSS
                                                biased_random_states foo) = {}`
                >- RW_TAC bool_ss [INTER_EMPTY, REAL_SUM_IMAGE_THM]
                >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [NOT_IN_EMPTY, FST, IN_CROSS, IN_INTER, IN_PREIMAGE, IN_SING]
                >> METIS_TAC [PAIR, FST,SND])
            >> `(PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
                 PREIMAGE FST {(y,z)} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)}) UNION
                 (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)})`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, FST, IN_UNION]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >> Cases_on `SND x' (STRCAT "coin" (toString 1))`
                     >- (DISJ1_TAC >> Q.EXISTS_TAC `SND x'`
                         >> METIS_TAC [PAIR])
                     >> DISJ2_TAC >> Q.EXISTS_TAC `SND x'`
                     >> METIS_TAC [PAIR])
            >> POP_ORW
            >> `FINITE {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)} /\
                FINITE {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)}`
                by (CONJ_TAC
                    >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                    >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
            >> `DISJOINT (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)})
                         (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)})`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, IN_IMAGE, GSPECIFICATION]
                    >> METIS_TAC [PAIR_EQ])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION, IMAGE_FINITE] >> POP_ASSUM (K ALL_TAC)
            >> `INJ (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)}
                    (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)}) /\
                INJ (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)}
                    (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x)})`
                by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_IMAGE, IMAGE_FINITE, o_DEF] >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (K ALL_TAC)
            >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
            >> `!r: bool state.
                (if r IN {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1)) /\
                              (insider_dcprog (SUC foo) ((y,z),r) = x)}
                then (if SND ((y,z),r) (STRCAT "coin" (toString 1)) then
                1 / 2 * (if ((y,z),r) IN biased_high_states foo CROSS biased_low_states CROSS
                                                        biased_random_states foo
                then 1 / 16 else 0) else 3 / 2 *
                (if ((y,z),r) IN biased_high_states foo CROSS biased_low_states CROSS biased_random_states foo
                then 1 / 16 else 0)) else 0) =
                1/32 * (\r. if
                 r IN {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1)) /\
                              (insider_dcprog (SUC foo) ((y,z),r) = x)}
                then (\r. 1) r else 0) r`
                by (RW_TAC real_ss [GSPECIFICATION, IN_CROSS])
            >> POP_ORW >> RW_TAC bool_ss [REAL_SUM_IMAGE_CMUL, GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3]
            >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
            >> `!r: bool state.
                (if r IN {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1)) /\
                              (insider_dcprog (SUC foo) ((y,z),r) = x)}
                then (if r (STRCAT "coin" (toString 1)) then
                1 / 2 * (if ((y,z),r) IN biased_high_states foo CROSS biased_low_states CROSS
                                                        biased_random_states foo
                then 1 / 16 else 0) else 3 / 2 *
                (if ((y,z),r) IN biased_high_states foo CROSS biased_low_states CROSS biased_random_states foo
                then 1 / 16 else 0)) else 0) =
                3/32 * (\r. if
                 r IN {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1)) /\
                              (insider_dcprog (SUC foo) ((y,z),r) = x)}
                then (\r. 1) r else 0) r`
                by (RW_TAC real_ss [GSPECIFICATION, IN_CROSS])
            >> POP_ORW >> RW_TAC real_ss [REAL_SUM_IMAGE_CMUL, GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3])
   >> `!x y z. (PREIMAGE (\x. (insider_dcprog (SUC foo) x,FST x))
           {(x,y,z)} INTER
         (biased_high_states foo CROSS biased_low_states CROSS
          biased_random_states foo)) =
        (PREIMAGE (insider_dcprog (SUC foo)) {x} INTER
           PREIMAGE FST {(y,z)} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_CROSS, IN_PREIMAGE, IN_SING, L_def])
   >> POP_ORW
   >> POP_ORW
   >> `!x y z.
        SIGMA
          (\s.
             (if SND s (STRCAT "coin" (toString 1)) then
                1 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)
              else
                3 / 2 *
                (if
                   s IN
                   biased_high_states foo CROSS biased_low_states CROSS
                   biased_random_states foo
                 then
                   1 / 16
                 else
                   0)))
          (PREIMAGE FST {(y,z)} INTER
           (biased_high_states foo CROSS biased_low_states CROSS
            biased_random_states foo)) =
        (if z IN biased_low_states /\ y IN (biased_high_states foo) then
                1/32 * & (CARD {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))})
                + 3/32 * & (CARD {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))})
         else 0)`
        by (reverse (RW_TAC real_ss [])
            >- (Suff `PREIMAGE FST {(y,z)} INTER (biased_high_states foo CROSS biased_low_states CROSS
                                                biased_random_states foo) = {}`
                >- RW_TAC bool_ss [INTER_EMPTY, REAL_SUM_IMAGE_THM]
                >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC set_ss [NOT_IN_EMPTY, FST, IN_CROSS, IN_INTER, IN_PREIMAGE, IN_SING]
                >> METIS_TAC [PAIR, FST,SND])
            >> `(PREIMAGE FST {(y,z)} INTER
                (biased_high_states foo CROSS biased_low_states CROSS
                 biased_random_states foo)) =
                 (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))}) UNION
                 (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))})`
                 by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_IMAGE, IN_PREIMAGE, IN_SING,
                                    IN_CROSS, FST, IN_UNION]
                     >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                     >> METIS_TAC [PAIR])
            >> POP_ORW
            >> `FINITE {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))} /\
                FINITE {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))}`
                by (CONJ_TAC
                    >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                    >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
            >> `DISJOINT (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))})
                         (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))})`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, IN_IMAGE, GSPECIFICATION]
                    >> METIS_TAC [PAIR_EQ])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_DISJOINT_UNION, IMAGE_FINITE] >> POP_ASSUM (K ALL_TAC)
            >> `INJ (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))}
                    (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                r (STRCAT "coin" (toString 1))}) /\
                INJ (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))}
                    (IMAGE (\r. ((y, z),r))
                        {r | r IN biased_random_states foo /\
                                ~r (STRCAT "coin" (toString 1))})`
                by (RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE])
            >> RW_TAC bool_ss [REAL_SUM_IMAGE_IMAGE, IMAGE_FINITE, o_DEF] >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (K ALL_TAC)
            >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
            >> `!r: bool state.
                (if r IN {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}
                then (if SND ((y,z),r) (STRCAT "coin" (toString 1)) then
                1 / 2 * (if ((y,z),r) IN biased_high_states foo CROSS biased_low_states CROSS
                                                        biased_random_states foo
                then 1 / 16 else 0) else 3 / 2 *
                (if ((y,z),r) IN biased_high_states foo CROSS biased_low_states CROSS biased_random_states foo
                then 1 / 16 else 0)) else 0) =
                1/32 * (\r. if
                 r IN {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}
                then (\r. 1) r else 0) r`
                by (RW_TAC real_ss [GSPECIFICATION, IN_CROSS])
            >> POP_ORW >> RW_TAC bool_ss [REAL_SUM_IMAGE_CMUL, GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3]
            >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF]
            >> `!r: bool state.
                (if r IN {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}
                then (if r (STRCAT "coin" (toString 1)) then
                1 / 2 * (if ((y,z),r) IN biased_high_states foo CROSS biased_low_states CROSS
                                                        biased_random_states foo
                then 1 / 16 else 0) else 3 / 2 *
                (if ((y,z),r) IN biased_high_states foo CROSS biased_low_states CROSS biased_random_states foo
                then 1 / 16 else 0)) else 0) =
                3/32 * (\r. if
                 r IN {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}
                then (\r. 1) r else 0) r`
                by (RW_TAC real_ss [GSPECIFICATION, IN_CROSS])
            >> POP_ORW >> RW_TAC real_ss [REAL_SUM_IMAGE_CMUL, GSYM REAL_SUM_IMAGE_IN_IF, REAL_SUM_IMAGE_FINITE_CONST3])
   >> POP_ORW
   >> `FINITE (IMAGE (insider_dcprog (SUC foo))
             (biased_high_states foo CROSS biased_low_states CROSS
              biased_random_states foo) CROSS biased_low_states)`
        by RW_TAC std_ss [IMAGE_FINITE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `IMAGE (insider_dcprog (SUC foo))
             (biased_high_states foo CROSS biased_low_states CROSS
              biased_random_states foo) CROSS biased_low_states`) REAL_SUM_IMAGE_IN_IF]
   >> Q.UNABBREV_TAC `foo`
   >> RW_TAC bool_ss [(COMPUTE_CARD ``(biased_high_states (SUC (SUC 0)))``
                              (SIMP_CONV set_ss [biased_high_states_def, insider_high_states_set_def]
                               THENC (TRY_CONV insider_hl_dup_conv))
                                dc_dup_conv)]
   >> Q.ABBREV_TAC `foo = SUC (SUC 0)`
   >> RW_TAC real_ss []
   >> RW_TAC bool_ss [Once REAL_SUM_IMAGE_IN_IF, IMAGE_FINITE, FINITE_CROSS]
   >> `!x:bool state # bool state.
        (if
           x IN
           IMAGE (insider_dcprog (SUC foo))
             (biased_high_states foo CROSS biased_low_states CROSS
              biased_random_states foo) CROSS biased_low_states
         then
           (λ(x,z).
              (if z IN biased_low_states then
                 1 / 32 *
                 &
                   (CARD
                      {(h,r) |
                       h IN biased_high_states foo /\
                       r IN biased_random_states foo /\
                       r (STRCAT "coin" (toString 1)) /\
                       (insider_dcprog (SUC foo) ((h,z),r) = x)}) +
                 3 / 32 *
                 &
                   (CARD
                      {(h,r) |
                       h IN biased_high_states foo /\
                       r IN biased_random_states foo /\
                       ~r (STRCAT "coin" (toString 1)) /\
                       (insider_dcprog (SUC foo) ((h,z),r) = x)})
               else
                 0) *
              logr 2
                ((if z IN biased_low_states then
                    1 / 32 *
                    &
                      (CARD
                         {(h,r) |
                          h IN biased_high_states foo /\
                          r IN biased_random_states foo /\
                          r (STRCAT "coin" (toString 1)) /\
                          (insider_dcprog (SUC foo) ((h,z),r) = x)}) +
                    3 / 32 *
                    &
                      (CARD
                         {(h,r) |
                          h IN biased_high_states foo /\
                          r IN biased_random_states foo /\
                          ~r (STRCAT "coin" (toString 1)) /\
                          (insider_dcprog (SUC foo) ((h,z),r) = x)})
                  else
                    0) /
                 (if z IN biased_low_states then
                    1 / 16 *
                    &
                      (CARD
                         {r |
                          r IN biased_random_states foo /\
                          r (STRCAT "coin" (toString 1))}) +
                    3 / 16 *
                    &
                      (CARD
                         {r |
                          r IN biased_random_states foo /\
                          ~r (STRCAT "coin" (toString 1))})
                  else
                    0))) x
         else
           0) =
        (if
           x IN
           IMAGE (insider_dcprog (SUC foo))
             (biased_high_states foo CROSS biased_low_states CROSS
              biased_random_states foo) CROSS biased_low_states
         then
           (λ(x,z).
              (1 / 32 *
                 &
                   (CARD
                      {(h,r) |
                       h IN biased_high_states foo /\
                       r IN biased_random_states foo /\
                       r (STRCAT "coin" (toString 1)) /\
                       (insider_dcprog (SUC foo) ((h,z),r) = x)}) +
                 3 / 32 *
                 &
                   (CARD
                      {(h,r) |
                       h IN biased_high_states foo /\
                       r IN biased_random_states foo /\
                       ~r (STRCAT "coin" (toString 1)) /\
                       (insider_dcprog (SUC foo) ((h,z),r) = x)})) *
              logr 2
                ((1 / 32 *
                    &
                      (CARD
                         {(h,r) |
                          h IN biased_high_states foo /\
                          r IN biased_random_states foo /\
                          r (STRCAT "coin" (toString 1)) /\
                          (insider_dcprog (SUC foo) ((h,z),r) = x)}) +
                    3 / 32 *
                    &
                      (CARD
                         {(h,r) |
                          h IN biased_high_states foo /\
                          r IN biased_random_states foo /\
                          ~r (STRCAT "coin" (toString 1)) /\
                          (insider_dcprog (SUC foo) ((h,z),r) = x)})) /
                 (1 / 16 *
                    &
                      (CARD
                         {r |
                          r IN biased_random_states foo /\
                          r (STRCAT "coin" (toString 1))}) +
                    3 / 16 *
                    &
                      (CARD
                         {r |
                          r IN biased_random_states foo /\
                          ~r (STRCAT "coin" (toString 1))})))) x
         else
           0)`
        by (RW_TAC std_ss [IN_CROSS] >> `x = (FST x, SND x)` by RW_TAC std_ss [PAIR] >> POP_ORW >> RW_TAC std_ss [])
   >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF, IMAGE_FINITE, FINITE_CROSS]
   >> Q.ABBREV_TAC `sumone =
        SIGMA
     (\x.
        (λ(x,z).
           (1 / 32 *
            &
              (CARD
                 {(h,r) |
                  h IN biased_high_states foo /\
                  r IN biased_random_states foo /\
                  r (STRCAT "coin" (toString 1)) /\
                  (insider_dcprog (SUC foo) ((h,z),r) = x)}) +
            3 / 32 *
            &
              (CARD
                 {(h,r) |
                  h IN biased_high_states foo /\
                  r IN biased_random_states foo /\
                  ~r (STRCAT "coin" (toString 1)) /\
                  (insider_dcprog (SUC foo) ((h,z),r) = x)})) *
           logr 2
             ((1 / 32 *
               &
                 (CARD
                    {(h,r) |
                     h IN biased_high_states foo /\
                     r IN biased_random_states foo /\
                     r (STRCAT "coin" (toString 1)) /\
                     (insider_dcprog (SUC foo) ((h,z),r) = x)}) +
               3 / 32 *
               &
                 (CARD
                    {(h,r) |
                     h IN biased_high_states foo /\
                     r IN biased_random_states foo /\
                     ~r (STRCAT "coin" (toString 1)) /\
                     (insider_dcprog (SUC foo) ((h,z),r) = x)})) /
              (1 / 16 *
               &
                 (CARD
                    {r |
                     r IN biased_random_states foo /\
                     r (STRCAT "coin" (toString 1))}) +
               3 / 16 *
               &
                 (CARD
                    {r |
                     r IN biased_random_states foo /\
                     ~r (STRCAT "coin" (toString 1))})))) x)
     (IMAGE (insider_dcprog (SUC foo))
        (biased_high_states foo CROSS biased_low_states CROSS
         biased_random_states foo) CROSS biased_low_states)`
   >> `FINITE (IMAGE (insider_dcprog (SUC foo))
            (biased_high_states foo CROSS biased_low_states CROSS
             biased_random_states foo) CROSS
          (biased_high_states foo CROSS biased_low_states))`
        by RW_TAC std_ss [IMAGE_FINITE, FINITE_CROSS]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `IMAGE (insider_dcprog (SUC foo))
            (biased_high_states foo CROSS biased_low_states CROSS
             biased_random_states foo) CROSS
          (biased_high_states foo CROSS biased_low_states)`) REAL_SUM_IMAGE_IN_IF]
   >> `!x. (if
          x IN
          IMAGE (insider_dcprog (SUC foo))
            (biased_high_states foo CROSS biased_low_states CROSS
             biased_random_states foo) CROSS
          (biased_high_states foo CROSS biased_low_states)
        then
          (λ(x,y,z).
             (if
                z IN biased_low_states /\ y IN biased_high_states foo
              then
                1 / 32 *
                &
                  (CARD
                     {r |
                      r IN biased_random_states foo /\
                      r (STRCAT "coin" (toString 1)) /\
                      (insider_dcprog (SUC foo) ((y,z),r) = x)}) +
                3 / 32 *
                &
                  (CARD
                     {r |
                      r IN biased_random_states foo /\
                      ~r (STRCAT "coin" (toString 1)) /\
                      (insider_dcprog (SUC foo) ((y,z),r) = x)})
              else
                0) *
             logr 2
               ((if
                   z IN biased_low_states /\ y IN biased_high_states foo
                 then
                   1 / 32 *
                   &
                     (CARD
                        {r |
                         r IN biased_random_states foo /\
                         r (STRCAT "coin" (toString 1)) /\
                         (insider_dcprog (SUC foo) ((y,z),r) = x)}) +
                   3 / 32 *
                   &
                     (CARD
                        {r |
                         r IN biased_random_states foo /\
                         ~r (STRCAT "coin" (toString 1)) /\
                         (insider_dcprog (SUC foo) ((y,z),r) = x)})
                 else
                   0) /
                (if
                   z IN biased_low_states /\ y IN biased_high_states foo
                 then
                   1 / 32 *
                   &
                     (CARD
                        {r |
                         r IN biased_random_states foo /\
                         r (STRCAT "coin" (toString 1))}) +
                   3 / 32 *
                   &
                     (CARD
                        {r |
                         r IN biased_random_states foo /\
                         ~r (STRCAT "coin" (toString 1))})
                 else
                   0))) x
        else
          0) =
        (if
          x IN
          IMAGE (insider_dcprog (SUC foo))
            (biased_high_states foo CROSS biased_low_states CROSS
             biased_random_states foo) CROSS
          (biased_high_states foo CROSS biased_low_states)
        then
          (λ(x,y,z).
             (1 / 32 *
                &
                  (CARD
                     {r |
                      r IN biased_random_states foo /\
                      r (STRCAT "coin" (toString 1)) /\
                      (insider_dcprog (SUC foo) ((y,z),r) = x)}) +
                3 / 32 *
                &
                  (CARD
                     {r |
                      r IN biased_random_states foo /\
                      ~r (STRCAT "coin" (toString 1)) /\
                      (insider_dcprog (SUC foo) ((y,z),r) = x)})) *
             logr 2
               ((1 / 32 *
                   &
                     (CARD
                        {r |
                         r IN biased_random_states foo /\
                         r (STRCAT "coin" (toString 1)) /\
                         (insider_dcprog (SUC foo) ((y,z),r) = x)}) +
                   3 / 32 *
                   &
                     (CARD
                        {r |
                         r IN biased_random_states foo /\
                         ~r (STRCAT "coin" (toString 1)) /\
                         (insider_dcprog (SUC foo) ((y,z),r) = x)})) /
                (1 / 32 *
                   &
                     (CARD
                        {r |
                         r IN biased_random_states foo /\
                         r (STRCAT "coin" (toString 1))}) +
                   3 / 32 *
                   &
                     (CARD
                        {r |
                         r IN biased_random_states foo /\
                         ~r (STRCAT "coin" (toString 1))})))) x
        else
          0)`
        by (RW_TAC std_ss [IN_CROSS] >> `x = (FST x, FST(SND x), SND (SND x))` by RW_TAC std_ss [PAIR] >> POP_ORW >> RW_TAC std_ss [])
   >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF, IMAGE_FINITE, FINITE_CROSS]
   >> Q.UNABBREV_TAC `sumone`
   >> RW_TAC real_ss [] >> Q.PAT_X_ASSUM `!f. f IN P` (K ALL_TAC)
   >> RW_TAC std_ss [GSYM lg_def]
   >> PURE_REWRITE_TAC [ETA_THM]
   >> `!(x:bool state) (y:bool state) (z:bool state).
        &(CARD
                {r |
                 r IN biased_random_states foo /\
                 r (STRCAT "coin" (toString 1))}) = 2`
        by (REPEAT STRIP_TAC
            >> `&(CARD
                {r |
                 r IN biased_random_states foo /\
                 r (STRCAT "coin" (toString 1))}) =
                REAL_SUM_IMAGE (\r. if r (STRCAT "coin" (toString 1)) then 1 else 0)
                (biased_random_states foo)`
                by (`FINITE {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}`
                    by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
                    >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
                    >> `FINITE {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}`
                    by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
                    >>  Q.ABBREV_TAC `s = {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}`
                    >> `(biased_random_states foo) =
                        {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))} UNION
                        {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}`
                        by (Q.UNABBREV_TAC `s` >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION] >> DECIDE_TAC)
                    >> POP_ORW
                    >> Q.UNABBREV_TAC `s`
                    >> `DISJOINT {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}
                        {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}`
                        by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
                            >> METIS_TAC [])
                    >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
                    >> `SIGMA (\r. (if r (STRCAT "coin" (toString 1)) then 1 else 0))
                        {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))} = 0`
                        by (RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
                            >> Suff `!r. (if r IN
                                {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))} then
                                (if r (STRCAT "coin" (toString 1)) then 1 else 0) else 0) = 0`
                            >- RW_TAC std_ss [REAL_SUM_IMAGE_0]
                            >> RW_TAC std_ss [GSPECIFICATION])
                    >> POP_ORW >> RW_TAC real_ss []
                    >> Suff `(\x. (if x IN {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}
                                then 1 else 0)) =
                             (\x. (if x IN {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}
                                then (\r. (if r (STRCAT "coin" (toString 1)) then 1 else 0)) x else 0))`
                     >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                         >> METIS_TAC [])
                     >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [GSPECIFICATION])
            >> POP_ORW
            >> Q.UNABBREV_TAC `foo` >> RW_TAC bool_ss [biased_random_states_def]
            >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))))
            >> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                         THENC ((ONCE_FIND_CONV ``x DELETE y``
                                (DELETE_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))
                         THENC SIMP_CONV arith_ss []))
            >> RW_TAC real_ss [STRCAT_toString_inj])
   >> POP_ORW
   >> `!(x:bool state) (y:bool state) (z:bool state).
        &(CARD
                {r |
                 r IN biased_random_states foo /\
                 ~r (STRCAT "coin" (toString 1))}) = 2`
        by (REPEAT STRIP_TAC
            >> `&(CARD
                {r |
                 r IN biased_random_states foo /\
                 ~r (STRCAT "coin" (toString 1))}) =
                REAL_SUM_IMAGE (\r. if ~r (STRCAT "coin" (toString 1)) then 1 else 0)
                (biased_random_states foo)`
                by (`FINITE {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}`
                    by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
                    >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
                    >> `FINITE {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}`
                    by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
                    >>  Q.ABBREV_TAC `s = {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}`
                    >> `(biased_random_states foo) =
                        {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))} UNION
                        {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}`
                        by (Q.UNABBREV_TAC `s` >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION] >> DECIDE_TAC)
                    >> POP_ORW
                    >> Q.UNABBREV_TAC `s`
                    >> `DISJOINT {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))}
                        {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}`
                        by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
                            >> METIS_TAC [])
                    >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
                    >> `SIGMA (\r. (if ~r (STRCAT "coin" (toString 1)) then 1 else 0))
                        {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))} = 0`
                        by (RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
                            >> Suff `!r. (if r IN
                                {r | r IN biased_random_states foo /\ r (STRCAT "coin" (toString 1))} then
                                (if ~r (STRCAT "coin" (toString 1)) then 1 else 0) else 0) = 0`
                            >- RW_TAC std_ss [REAL_SUM_IMAGE_0]
                            >> RW_TAC std_ss [GSPECIFICATION])
                    >> POP_ORW >> RW_TAC real_ss []
                    >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
                    >> Suff `(\x. (if x IN {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}
                                then 1 else 0)) =
                             (\x. (if x IN {r | r IN biased_random_states foo /\ ~r (STRCAT "coin" (toString 1))}
                                then (\r. (if ~r (STRCAT "coin" (toString 1)) then 1 else 0)) x else 0))`
                     >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                         >> METIS_TAC [])
                     >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [GSPECIFICATION])
            >> POP_ORW
            >> Q.UNABBREV_TAC `foo` >> RW_TAC bool_ss [biased_random_states_def]
            >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))))
            >> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                         THENC ((ONCE_FIND_CONV ``x DELETE y``
                                (DELETE_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))
                         THENC SIMP_CONV arith_ss []))
            >> RW_TAC real_ss [STRCAT_toString_inj])
   >> POP_ORW
   >> RW_TAC real_ss []
   >> `!(x: bool state) (z:bool state) (a:real) b c1 c2 d. (a * c1  + b * c2) * lg ((a * c1  + b * c2)/d) =
                (\c1 c2. (a * c1  + b * c2) * lg ((a * c1  + b * c2)/d)) c1 c2`
        by  RW_TAC std_ss []
   >> POP_ORW
   >> Q.ABBREV_TAC `c1 = (\c1 c2.
           (1 / 32 * c1 + 3 / 32 * c2) *
           lg ((1 / 32 * c1 + 3 / 32 * c2) / (1 / 2)))`
   >> Q.ABBREV_TAC `c2 = (\c1 c2.
          (1 / 32 * c1 + 3 / 32 * c2) *
          lg ((1 / 32 * c1 + 3 / 32 * c2) / (1 / 4)))`
   >> `!(x: bool state) (z:bool state).
        &(CARD {(h,r) |
                  h IN biased_high_states foo /\
                  r IN biased_random_states foo /\
                  r (STRCAT "coin" (toString 1)) /\
                  (insider_dcprog (SUC foo) ((h,z),r) = x)}) =
        REAL_SUM_IMAGE
        (λ(h,r). if r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x) then 1 else 0)
        (biased_high_states foo CROSS biased_random_states foo)`
        by (STRIP_TAC >> STRIP_TAC
            >> `FINITE {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x)}`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss [FINITE_CROSS]
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                       >> POP_ASSUM MP_TAC
                       >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                       >> POP_ORW >> RW_TAC std_ss [])
            >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
            >> `FINITE {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~(r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x))}`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss [FINITE_CROSS]
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                       >> POP_ASSUM MP_TAC
                       >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                       >> POP_ORW >> RW_TAC std_ss [])
            >> `(biased_high_states foo CROSS biased_random_states foo) =
                {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x)} UNION
                {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~(r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x))}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION, IN_CROSS]
                    >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                    >- (Cases_on `(SND x') (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo)
                                        ((FST x',z),SND x') = x)`
                        >- (DISJ1_TAC >> Q.EXISTS_TAC `(FST x', SND x')` >> RW_TAC std_ss [PAIR_EQ])
                        >> DISJ2_TAC >> Q.EXISTS_TAC `(FST x', SND x')` >> RW_TAC std_ss [PAIR_EQ]
                        >> FULL_SIMP_TAC std_ss [DE_MORGAN_THM])
                    >> POP_ASSUM MP_TAC
                    >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ])
            >> POP_ORW
            >> `DISJOINT {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x)}
                {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~(r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x))}`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
                    >> Cases_on `(SND x') (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo)
                                        ((FST x',z),SND x') = x)`
                    >- (DISJ2_TAC >> STRIP_TAC
                        >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
                        >> POP_ORW >> RW_TAC std_ss [PAIR_EQ] >> METIS_TAC [PAIR, PAIR_EQ])
                    >> DISJ1_TAC >> STRIP_TAC
                    >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ] >> METIS_TAC [PAIR, PAIR_EQ])
            >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
            >> `SIGMA (λ(h,r). (if r (STRCAT "coin" (toString 1)) /\
                        (insider_dcprog (SUC foo) ((h,z),r) = x) then 1 else 0))
                  {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                           (~r (STRCAT "coin" (toString 1)) \/
                           ~(insider_dcprog (SUC foo) ((h,z),r) = x))} = 0`
                by (FULL_SIMP_TAC bool_ss [DE_MORGAN_THM]
                    >> RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
                    >> Suff `!x'. (if x' IN
                        {(h,r) |
                         h IN biased_high_states foo /\ r IN biased_random_states foo /\
                         (~r (STRCAT "coin" (toString 1)) \/
                          ~(insider_dcprog (SUC foo) ((h,z),r) = x))} then
                        (λ(h,r). (if r (STRCAT "coin" (toString 1)) /\
                        (insider_dcprog (SUC foo) ((h,z),r) = x) then 1 else 0)) x' else 0) = 0`
                    >- RW_TAC std_ss [REAL_SUM_IMAGE_0]
                    >> RW_TAC std_ss [GSPECIFICATION]
                    >> POP_ASSUM MP_TAC >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                    >> `x':bool state # bool state = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [])
            >> POP_ORW >> RW_TAC real_ss []
            >> Suff `(\x'. (if x' IN {(h,r) |
                h IN biased_high_states foo /\ r IN biased_random_states foo /\
                r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((h,z),r) = x)}
                        then 1 else 0)) =
                     (\x'. (if x' IN {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        r (STRCAT "coin" (toString 1)) /\
                        (insider_dcprog (SUC foo) ((h,z),r) = x)}
                        then (λ(h,r). (if r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((h,z),r) = x) then 1 else 0)) x' else 0))`
             >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                 >> METIS_TAC [])
             >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [GSPECIFICATION]
             >> POP_ASSUM MP_TAC >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
             >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
             >> `x':bool state # bool state = (FST x', SND x')` by RW_TAC std_ss [PAIR]
             >> POP_ORW >> RW_TAC std_ss [])
   >> POP_ORW
   >> `!(x: bool state) (z:bool state).
        &(CARD {(h,r) |
                  h IN biased_high_states foo /\
                  r IN biased_random_states foo /\
                  ~r (STRCAT "coin" (toString 1)) /\
                  (insider_dcprog (SUC foo) ((h,z),r) = x)}) =
        REAL_SUM_IMAGE
        (λ(h,r). if ~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x) then 1 else 0)
        (biased_high_states foo CROSS biased_random_states foo)`
        by (STRIP_TAC >> STRIP_TAC
            >> `FINITE {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~(~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x))}`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss [FINITE_CROSS]
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                       >> POP_ASSUM MP_TAC
                       >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                       >> POP_ORW >> RW_TAC std_ss [])
            >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
            >> `FINITE {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x)}`
                   by ((MP_TAC o Q.ISPEC `(biased_high_states foo) CROSS (biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC bool_ss [FINITE_CROSS]
                       >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS]
                       >> POP_ASSUM MP_TAC
                       >> `x'' = (FST x'',SND x'')` by RW_TAC std_ss [PAIR]
                       >> POP_ORW >> RW_TAC std_ss [])
            >> `(biased_high_states foo CROSS biased_random_states foo) =
                {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x)} UNION
                {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~(~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x))}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION, IN_CROSS]
                    >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss [])
                    >- (Cases_on `~(SND x') (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((FST x',z),SND x') = x)`
                        >- (DISJ1_TAC >> Q.EXISTS_TAC `(FST x', SND x')` >> RW_TAC std_ss [PAIR_EQ])
                        >> DISJ2_TAC >> Q.EXISTS_TAC `(FST x', SND x')` >> RW_TAC std_ss [PAIR_EQ]
                        >> FULL_SIMP_TAC std_ss [DE_MORGAN_THM])
                    >> POP_ASSUM MP_TAC
                    >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ])
            >> POP_ORW
            >> `DISJOINT {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x)}
                {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~(~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((h,z),r) = x))}`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION]
                    >> Cases_on `~(SND x') (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((FST x',z),SND x') = x)`
                    >- (DISJ2_TAC >> STRIP_TAC
                        >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
                        >> POP_ORW >> RW_TAC std_ss [PAIR_EQ] >> METIS_TAC [PAIR, PAIR_EQ])
                    >> DISJ1_TAC >> STRIP_TAC
                    >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ] >> METIS_TAC [PAIR, PAIR_EQ])
            >> FULL_SIMP_TAC std_ss [DE_MORGAN_THM]
            >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
            >> `SIGMA (λ(h,r). (if ~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((h,z),r) = x) then 1 else 0))
                {(h,r) | h IN biased_high_states foo /\ r IN biased_random_states foo /\
                (r (STRCAT "coin" (toString 1)) \/ ~(insider_dcprog (SUC foo) ((h,z),r) = x))} = 0`
                by (FULL_SIMP_TAC bool_ss [DE_MORGAN_THM]
                    >> RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
                    >> Suff `!x'. (if x' IN
                        {(h,r) |
                         h IN biased_high_states foo /\ r IN biased_random_states foo /\
                         (r (STRCAT "coin" (toString 1)) \/
                         ~(insider_dcprog (SUC foo) ((h,z),r) = x))} then
                        (λ(h,r). (if ~r (STRCAT "coin" (toString 1)) /\
                        (insider_dcprog (SUC foo) ((h,z),r) = x) then 1 else 0)) x' else 0) = 0`
                    >- RW_TAC std_ss [REAL_SUM_IMAGE_0]
                    >> RW_TAC std_ss [GSPECIFICATION]
                    >> POP_ASSUM MP_TAC >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
                    >> `x':bool state # bool state = (FST x', SND x')` by RW_TAC std_ss [PAIR]
                    >> POP_ORW >> RW_TAC std_ss [])
            >> POP_ORW >> RW_TAC real_ss []
            >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
            >> Suff `(\x'. (if x' IN {(h,r) |
                h IN biased_high_states foo /\ r IN biased_random_states foo /\
                ~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((h,z),r) = x)}
                        then 1 else 0)) =
                     (\x'. (if x' IN {(h,r) |
                        h IN biased_high_states foo /\ r IN biased_random_states foo /\
                        ~r (STRCAT "coin" (toString 1)) /\
                        (insider_dcprog (SUC foo) ((h,z),r) = x)}
                        then (λ(h,r). (if ~r (STRCAT "coin" (toString 1)) /\
                        (insider_dcprog (SUC foo) ((h,z),r) = x) then 1 else 0)) x' else 0))`
             >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                 >> METIS_TAC [])
             >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [GSPECIFICATION]
             >> POP_ASSUM MP_TAC >> `x'':bool state # bool state = (FST x'', SND x'')` by RW_TAC std_ss [PAIR]
             >> POP_ORW >> RW_TAC std_ss [PAIR_EQ]
             >> `x':bool state # bool state = (FST x', SND x')` by RW_TAC std_ss [PAIR]
             >> POP_ORW >> RW_TAC std_ss [])
   >> POP_ORW
   >> `!(x: bool state) (y: bool state) (z:bool state).
        &(CARD {r |
                r IN biased_random_states foo /\
                r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x)}) =
        REAL_SUM_IMAGE
        (\r. if r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((y,z),r) = x) then 1 else 0)
        (biased_random_states foo)`
        by (STRIP_TAC >> STRIP_TAC >> STRIP_TAC
            >> `FINITE {r |
                r IN biased_random_states foo /\
                r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x)}`
                   by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
            >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
            >> `FINITE {r |
                r IN biased_random_states foo /\
                ~(r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x))}`
                   by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
           >> Q.ABBREV_TAC `s = {r | r IN biased_random_states foo /\
                                     r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((y,z),r) = x)}`
            >> `(biased_random_states foo) =
                {r |
                r IN biased_random_states foo /\
                r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x)} UNION
                {r |
                r IN biased_random_states foo /\
                ~(r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x))}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION, IN_CROSS]
                    >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss []) >> METIS_TAC [])
            >> POP_ORW
            >> `DISJOINT {r |
                r IN biased_random_states foo /\
                r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x)}
                {r |
                r IN biased_random_states foo /\
                ~(r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x))}`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> Q.UNABBREV_TAC `s` >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION] >> DECIDE_TAC)
            >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
            >> `SIGMA (\r. (if r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((y,z),r) = x) then 1 else 0))
                {r | r IN biased_random_states foo /\ (~r (STRCAT "coin" (toString 1)) \/
                        ~(insider_dcprog (SUC foo) ((y,z),r) = x))} = 0`
                by (FULL_SIMP_TAC bool_ss [DE_MORGAN_THM]
                    >> RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
                    >> Suff `!r. (if r IN
                        {r | r IN biased_random_states foo /\ (~r (STRCAT "coin" (toString 1)) \/
                            ~(insider_dcprog (SUC foo) ((y,z),r) = x))} then
                        (if r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((y,z),r) = x) then 1 else 0) else 0) = 0`
                    >- RW_TAC std_ss [REAL_SUM_IMAGE_0]
                    >> RW_TAC std_ss [GSPECIFICATION])
            >> POP_ORW >> RW_TAC real_ss []
            >> Suff `(\x'. (if x' IN s then 1 else 0)) =
                     (\x'. (if x' IN s then (\r. (if r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x) then 1 else 0)) x' else 0))`
             >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                 >> METIS_TAC [])
             >> Q.UNABBREV_TAC `s`
             >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [GSPECIFICATION])
   >> POP_ORW
   >> `!(x: bool state) (y: bool state) (z:bool state).
        &(CARD {r |
                r IN biased_random_states foo /\
                ~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x)}) =
        REAL_SUM_IMAGE
        (\r. if ~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((y,z),r) = x) then 1 else 0)
        (biased_random_states foo)`
        by (STRIP_TAC >> STRIP_TAC >> STRIP_TAC
            >> `FINITE {r |
                r IN biased_random_states foo /\
                ~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x)}`
                   by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
            >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_CARD]
            >> `FINITE {r |
                r IN biased_random_states foo /\
                ~(~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x))}`
                   by ((MATCH_MP_TAC o UNDISCH o Q.ISPEC `(biased_random_states foo)`) SUBSET_FINITE
                       >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION])
           >> Q.ABBREV_TAC `s = {r | r IN biased_random_states foo /\
                                     ~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((y,z),r) = x)}`
            >> `(biased_random_states foo) =
                {r |
                r IN biased_random_states foo /\
                ~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x)} UNION
                {r |
                r IN biased_random_states foo /\
                ~(~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x))}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, GSPECIFICATION, IN_CROSS]
                    >> (EQ_TAC >> RW_TAC std_ss [] >> RW_TAC std_ss []) >> METIS_TAC [])
            >> POP_ORW
            >> `DISJOINT {r |
                r IN biased_random_states foo /\
                ~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x)}
                {r |
                r IN biased_random_states foo /\
                ~(~r (STRCAT "coin" (toString 1)) /\
                (insider_dcprog (SUC foo) ((y,z),r) = x))}`
                by (RW_TAC std_ss [DISJOINT_DEF] >> ONCE_REWRITE_TAC [EXTENSION] >> Q.UNABBREV_TAC `s` >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, GSPECIFICATION] >> DECIDE_TAC)
            >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION] >> POP_ASSUM (K ALL_TAC)
            >> `SIGMA (\r. (if ~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((y,z),r) = x) then 1 else 0))
                {r | r IN biased_random_states foo /\ (r (STRCAT "coin" (toString 1)) \/
                        ~(insider_dcprog (SUC foo) ((y,z),r) = x))} = 0`
                by (FULL_SIMP_TAC bool_ss [DE_MORGAN_THM]
                    >> RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
                    >> Suff `!r. (if r IN
                        {r | r IN biased_random_states foo /\ (r (STRCAT "coin" (toString 1)) \/
                            ~(insider_dcprog (SUC foo) ((y,z),r) = x))} then
                        (if ~r (STRCAT "coin" (toString 1)) /\ (insider_dcprog (SUC foo) ((y,z),r) = x) then 1 else 0) else 0) = 0`
                    >- RW_TAC std_ss [REAL_SUM_IMAGE_0]
                    >> RW_TAC std_ss [GSPECIFICATION])
            >> POP_ORW >> RW_TAC real_ss []
            >> Suff `(\x'. (if x' IN s then 1 else 0)) =
                     (\x'. (if x' IN s then (\r. (if ~r (STRCAT "coin" (toString 1)) /\
                                (insider_dcprog (SUC foo) ((y,z),r) = x) then 1 else 0)) x' else 0))`
             >- (STRIP_TAC >> POP_ORW >> RW_TAC bool_ss [GSYM REAL_SUM_IMAGE_IN_IF]
                 >> METIS_TAC [])
             >> Q.UNABBREV_TAC `s`
             >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> RW_TAC std_ss [GSPECIFICATION])
   >> POP_ORW
   >> Q.UNABBREV_TAC `foo`
   >> Q.ABBREV_TAC `s1 = (IMAGE (insider_dcprog (SUC (SUC (SUC 0))))
         (biased_high_states (SUC (SUC 0)) CROSS biased_low_states CROSS
          biased_random_states (SUC (SUC 0))))`
   >> Q.ABBREV_TAC `s2 = (s1 CROSS biased_low_states)`
   >> Q.ABBREV_TAC `s3 = (s1 CROSS (biased_high_states (SUC (SUC 0)) CROSS biased_low_states))`
   >> RW_TAC bool_ss [biased_high_states_def, biased_random_states_def, insider_high_states_set_def,
                      insider_dcprog_def, compute_result_alt, insider_set_announcements_alt, XOR_announces_def,
                      H_def, L_def, PAIR, ETA_THM, xor_def, STRCAT_toString_inj]
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)))))
   >> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                         THENC ((ONCE_FIND_CONV ``x DELETE y``
                                (DELETE_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))
                         THENC SIMP_CONV arith_ss []))
   >> RW_TAC real_ss [STRCAT_toString_inj]
   >> Q.UNABBREV_TAC `s3` >> Q.UNABBREV_TAC `s2` >> Q.UNABBREV_TAC `s1`
   >> RW_TAC bool_ss [biased_high_states_def, biased_low_states_def, biased_random_states_def, insider_high_states_set_def,
                      insider_dcprog_def, compute_result_alt, insider_set_announcements_alt, XOR_announces_def,
                      H_def, L_def, PAIR, ETA_THM, xor_def, STRCAT_toString_inj]
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)))))
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)))))
   >> RW_TAC std_ss []
   >> CONV_TAC (SIMP_CONV bool_ss [CROSS_EQNS, PAIR_EQ, IMAGE_UNION, IMAGE_INSERT, IMAGE_EMPTY, UNION_EMPTY, FST,
                                                   L_def, SND]
                                THENC (FIND_CONV ``x UNION y`` (UNION_CONV (SIMP_CONV bool_ss [PAIR_EQ]
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV insider_hl_dup_conv)
                                                     THENC (TRY_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))))
   >> RW_TAC real_ss [STRCAT_toString_inj]
  >> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                         THENC ((ONCE_FIND_CONV ``x DELETE y``
                                (DELETE_CONV (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
                                              THENC EVAL
                                              THENC (REPEATC (T_F_UNCHANGED_CONV
                                                        (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
                                                         THENC EVAL)))))))
                         THENC SIMP_CONV arith_ss []))
   >> SIMP_TAC real_ss [STRCAT_toString_inj]
   >> CONV_TAC (ONCE_FIND_CONV ``if (x=y) then (1:real) else 0`` (RATOR_CONV (RATOR_CONV (RAND_CONV
        (SIMP_CONV arith_ss [FUN_EQ_THM, PAIR_EQ, COND_EXPAND, EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM]
         THENC EVAL
         THENC SIMP_CONV bool_ss [COND_EXPAND, LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]
         THENC EVAL
         THENC (REPEATC (T_F_UNCHANGED_CONV
         (SIMP_CONV bool_ss [fun_eq_lem6, GSYM LEFT_AND_OVER_OR, FORALL_AND_THM]
         THENC EVAL))))))
                                                                  THENC SIMP_CONV bool_ss []))
   >> RW_TAC real_ss []
   >> Q.UNABBREV_TAC `c2` >> Q.UNABBREV_TAC `c1`
   >> RW_TAC real_ss []
   >> `lg(1/4) = ~2` by (RW_TAC real_ss [GSYM REAL_INV_1OVER, lg_inv] >> `4 = 2 pow 2` by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
   >> POP_ORW
   >> RW_TAC real_ss []
   >> RW_TAC std_ss [real_div]
   >> RW_TAC real_ss [lg_mul, REAL_INV_POS, lg_inv]
   >> `lg(8) = 3` by (`8 = 2 pow 3` by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
   >> POP_ORW >> RW_TAC real_ss [GSYM real_sub, REAL_SUB_LDISTRIB, lg_1]
   >> RW_TAC real_ss [REAL_ADD_ASSOC, GSYM real_sub, REAL_ARITH ``!x (y:real). x - y - y = x - 2 * y``,
                      REAL_ARITH ``!x (y:real) c. x - c * y - y = x - (c + 1) * y``,
                      REAL_ARITH ``!x (y:real) z. x - y + z = x + z - y``]
   >> RW_TAC std_ss [GSYM REAL_ADD_ASSOC, REAL_ARITH ``!(y:real). y + y = 2 * y``,
                     REAL_ARITH ``!(y:real) c. y + c * y = (c + 1) * y``]
   >> RW_TAC real_ss [REAL_SUB_LDISTRIB, REAL_MUL_ASSOC, REAL_INV_1OVER,
                      REAL_ARITH ``!(x:real) y z a. x + (y - z) - a = y + (x - (z + a))``, GSYM real_sub]
   >> Q.UNABBREV_TAC `v` >> RW_TAC std_ss []);

val _ = export_theory ();
