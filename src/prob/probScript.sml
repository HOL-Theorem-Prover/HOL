open HolKernel Parse boolLib bossLib arithmeticTheory realTheory
     seqTheory pred_setTheory ind_typeTheory listTheory
     rich_listTheory pairTheory combinTheory realLib probTools
     boolean_sequenceTheory boolean_sequenceTools prob_extraTheory
     prob_extraTools prob_canonTheory prob_canonTools
     prob_algebraTheory realSimps;

val _ = new_theory "prob";

infixr 0 ++ << || ORELSEC ##;
infix 1 >>;
nonfix THEN ORELSE;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);

(* ------------------------------------------------------------------------- *)
(* The definition of probability.                                            *)
(* ------------------------------------------------------------------------- *)

val alg_measure_def = Define `(alg_measure ([]:bool list list) = 0)
  /\ (alg_measure (l::rest) = (1/2) pow (LENGTH l) + alg_measure rest)`;

val algebra_measure_def = Define `algebra_measure b
  = inf (\r. ?c. (algebra_embed b = algebra_embed c) /\ (alg_measure c = r))`;

val prob_def = Define `prob s = sup (\r. ?b. (algebra_measure b = r)
  /\ (algebra_embed b SUBSET s))`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. alg_measure (alg_canon b) <= alg_measure b                             *)
(* 2. algebra_measure b = alg_measure (alg_canon b)                          *)
(* 3. measurable a /\ measurable b /\ (a INTER b = {})                       *)
(*    ==> prob (a UNION b) = prob a + prob b                                 *)
(* 4. a SUBSET b ==> prob a <= prob b                                        *)
(* ------------------------------------------------------------------------- *)

val ALG_TWINS_MEASURE = store_thm
  ("ALG_TWINS_MEASURE",
   ``!l. (1 / 2) pow LENGTH (SNOC T l) + (1 / 2) pow LENGTH (SNOC F l)
         = (1 / 2) pow LENGTH l``,
   RW_TAC std_ss [LENGTH_SNOC]
   ++ REWRITE_TAC [Q.SPEC `LENGTH (l:bool list)` POW_HALF_TWICE]
   ++ REAL_ARITH_TAC);

val ALG_MEASURE_BASIC = store_thm
  ("ALG_MEASURE_BASIC",
   ``(alg_measure [] = 0) /\ (alg_measure [[]] = 1)
     /\ (!b. alg_measure [[b]] = 1 / 2)``,
   RW_TAC real_ac_ss [alg_measure_def, LENGTH, POW_1, pow]);

val ALG_MEASURE_POS = store_thm
  ("ALG_MEASURE_POS",
   ``!l. 0 <= alg_measure l``,
   Induct >> PROVE_TAC [alg_measure_def, REAL_ARITH ``(0:real) <= 0``]
   ++ RW_TAC list_ss [alg_measure_def]
   ++ PROVE_TAC [REAL_ARITH ``(0:real) < a /\ 0 <= b ==> 0 <= a + b``,
		   POW_HALF_POS]);

val ALG_MEASURE_APPEND = store_thm
  ("ALG_MEASURE_APPEND",
   ``!l1 l2. alg_measure (APPEND l1 l2) = alg_measure l1 + alg_measure l2``,
   NTAC 2 STRIP_TAC
   ++ Induct_on `l1`
     >> (RW_TAC list_ss [alg_measure_def, APPEND] ++ REAL_ARITH_TAC)
   ++ RW_TAC list_ss [alg_measure_def, APPEND]
   ++ REAL_ARITH_TAC);

val ALG_MEASURE_TLS = store_thm
  ("ALG_MEASURE_TLS",
   ``!l b. 2 * alg_measure (MAP (CONS b) l) = alg_measure l``,
   Induct >> (RW_TAC list_ss [alg_measure_def] ++ REAL_ARITH_TAC)
   ++ RW_TAC list_ss [alg_measure_def, MAP, pow]
   ++ REWRITE_TAC [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL,
		     REAL_MUL_LID]
   ++ PROVE_TAC []);

val ALG_CANON_PREFS_MONO = store_thm
  ("ALG_CANON_PREFS_MONO",
   ``!l b. alg_measure (alg_canon_prefs l b) <= alg_measure (l::b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_prefs_def, REAL_LE_REFL]
   ++ REVERSE (RW_TAC list_ss [alg_canon_prefs_def])
     >> PROVE_TAC [REAL_LE_REFL]
   ++ SUFF_TAC `alg_measure (l::b) <= alg_measure (l::h::b)`
     >> PROVE_TAC [REAL_LE_TRANS]
   ++ KILL_ALL_TAC
   ++ RW_TAC list_ss [alg_measure_def]
   ++ ASSUME_TAC (SPEC ``LENGTH (h:bool list)`` POW_HALF_POS)
   ++ PROVE_TAC [REAL_ARITH ``0 < (x:real) ==> a + b <= a + (x + b)``]);

val ALG_CANON_FIND_MONO = store_thm
  ("ALG_CANON_FIND_MONO",
   ``!l b. alg_measure (alg_canon_find l b) <= alg_measure (l::b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_find_def, REAL_LE_REFL]
   ++ RW_TAC list_ss [alg_canon_find_def] <<
   [KILL_ALL_TAC
    ++ REWRITE_TAC [alg_measure_def]
    ++ ASSUME_TAC (SPEC ``LENGTH (l:bool list)`` POW_HALF_POS)
    ++ PROVE_TAC [REAL_ARITH ``0 < (x:real) ==> a <= x + a``],
    NTAC 2 (POP_ASSUM (K ALL_TAC))
    ++ POP_ASSUM MP_TAC
    ++ REWRITE_TAC [alg_measure_def]
    ++ REAL_ARITH_TAC,
    PROVE_TAC [ALG_CANON_PREFS_MONO]]);

val ALG_CANON1_MONO = store_thm
  ("ALG_CANON1_MONO",
   ``!l. alg_measure (alg_canon1 l) <= alg_measure l``,
   REWRITE_TAC [alg_canon1_def]
   ++ Induct >> RW_TAC list_ss [REAL_LE_REFL, FOLDR]
   ++ RW_TAC list_ss [FOLDR]
   ++ SUFF_TAC `alg_measure (h::FOLDR alg_canon_find [] l)
		   <= alg_measure (h::l)`
     >> PROVE_TAC [ALG_CANON_FIND_MONO, REAL_LE_TRANS]
   ++ PROVE_TAC [alg_measure_def, REAL_LE_LADD]);

val ALG_CANON_MERGE_MONO = store_thm
  ("ALG_CANON_MERGE_MONO",
   ``!l b. alg_measure (alg_canon_merge l b) <= alg_measure (l::b)``,
   Induct_on `b` >> RW_TAC real_ac_ss [alg_canon_merge_def, REAL_LE_REFL]
   ++ RW_TAC real_ac_ss [alg_canon_merge_def, alg_twin_def]
   ++ RW_TAC std_ss [BUTLAST]
   ++ SUFF_TAC `alg_measure (l'::b) <= alg_measure (SNOC T l'::SNOC F l'::b)`
   >> PROVE_TAC [REAL_LE_TRANS]
   ++ KILL_ALL_TAC
   ++ RW_TAC std_ss [alg_measure_def, REAL_ADD_ASSOC, ALG_TWINS_MEASURE,
                     REAL_LE_REFL]);

val ALG_CANON2_MONO = store_thm
  ("ALG_CANON2_MONO",
   ``!l. alg_measure (alg_canon2 l) <= alg_measure l``,
   REWRITE_TAC [alg_canon2_def]
   ++ Induct >> RW_TAC list_ss [REAL_LE_REFL, FOLDR]
   ++ RW_TAC list_ss [FOLDR]
   ++ SUFF_TAC `alg_measure (h::FOLDR alg_canon_merge [] l)
		   <= alg_measure (h::l)`
     >> PROVE_TAC [ALG_CANON_MERGE_MONO, REAL_LE_TRANS]
   ++ PROVE_TAC [alg_measure_def, REAL_LE_LADD]);

val ALG_CANON_MONO = store_thm
  ("ALG_CANON_MONO",
   ``!l. alg_measure (alg_canon l) <= alg_measure l``,
   RW_TAC std_ss [alg_canon_def]
   ++ PROVE_TAC [ALG_CANON1_MONO, ALG_CANON2_MONO, REAL_LE_TRANS]);

val ALGEBRA_MEASURE_DEF_ALT = store_thm
  ("ALGEBRA_MEASURE_DEF_ALT",
   ``!l. algebra_measure l = alg_measure (alg_canon l)``,
   RW_TAC std_ss [algebra_measure_def]
   ++ HO_MATCH_MP_TAC REAL_INF_MIN
   ++ RW_TAC std_ss []
   >> (EXISTS_TAC ``alg_canon l``
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [ALG_CANON_REP, ALG_CANON_IDEMPOT])
   ++ SUFF_TAC `alg_measure (alg_canon c) <= alg_measure c`
   >> PROVE_TAC [ALG_CANON_REP]
   ++ PROVE_TAC [ALG_CANON_MONO]);

val ALGEBRA_MEASURE_BASIC = store_thm
  ("ALGEBRA_MEASURE_BASIC",
   ``(algebra_measure [] = 0) /\ (algebra_measure [[]] = 1)
     /\ (!b. algebra_measure [[b]] = 1 / 2)``,
   RW_TAC std_ss [ALGEBRA_MEASURE_DEF_ALT, ALG_CANON_BASIC, ALG_MEASURE_BASIC]);

val ALGEBRA_CANON_MEASURE_MAX = store_thm
  ("ALGEBRA_CANON_MEASURE_MAX",
   ``!l. algebra_canon l ==> alg_measure l <= 1``,
   HO_MATCH_MP_TAC ALGEBRA_CANON_INDUCTION
   ++ CONJ_TAC >> (RW_TAC list_ss [alg_measure_def] ++ REAL_ARITH_TAC)
   ++ CONJ_TAC >> (RW_TAC list_ss [alg_measure_def, pow] ++ REAL_ARITH_TAC)
   ++ RW_TAC list_ss [ALG_MEASURE_APPEND]
   ++ SUFF_TAC `(2 * alg_measure (MAP (CONS T) l) = alg_measure l)
                   /\ (2 * alg_measure (MAP (CONS F) l') = alg_measure l')`
   >> PROVE_TAC [REAL_ARITH ``(2 * a = b) /\ (2 * c = d) /\ b <= 1 /\ d <= 1
                              ==> a + c <= (1:real)``]
   ++ PROVE_TAC [ALG_MEASURE_TLS]);

val ALGEBRA_MEASURE_MAX = store_thm
  ("ALGEBRA_MEASURE_MAX",
   ``!l. algebra_measure l <= 1``,
   RW_TAC std_ss [ALGEBRA_MEASURE_DEF_ALT]
   ++ MP_TAC (Q.SPEC `alg_canon l` ALGEBRA_CANON_MEASURE_MAX)
   ++ RW_TAC std_ss [algebra_canon_def, ALG_CANON_IDEMPOT]);

val ALGEBRA_MEASURE_MONO_EMBED = store_thm
  ("ALGEBRA_MEASURE_MONO_EMBED",
   ``!b c. algebra_embed b SUBSET algebra_embed c
           ==> algebra_measure b <= algebra_measure c``,
   ONCE_REWRITE_TAC [GSYM ALG_CANON_EMBED, ALGEBRA_MEASURE_DEF_ALT]
   ++ SUFF_TAC `!c. algebra_canon c ==> !b. algebra_canon b
           ==> algebra_embed b SUBSET algebra_embed c
           ==> alg_measure b <= alg_measure c`
   >> PROVE_TAC [algebra_canon_def, ALG_CANON_IDEMPOT]
   ++ HO_MATCH_MP_TAC ALGEBRA_CANON_INDUCTION
   ++ PSET_TAC [algebra_embed_def, ALG_MEASURE_BASIC, alg_embed_def] <<
   [Cases_on `b` >> RW_TAC std_ss [REAL_LE_REFL, ALG_MEASURE_BASIC]
    ++ MP_TAC (Q.SPEC `h` ALG_EMBED_POPULATED)
    ++ PSET_TAC [algebra_embed_def],
    RW_TAC std_ss [ALGEBRA_CANON_MEASURE_MAX],
    NTAC 2 (POP_ASSUM MP_TAC)
    ++ Q.SPEC_TAC (`b`, `b`)
    ++ HO_MATCH_MP_TAC ALGEBRA_CANON_CASES
    ++ PSET_TAC [ALG_MEASURE_BASIC, ALG_MEASURE_POS, ALGEBRA_EMBED_BASIC] <<
    [KNOW_TAC `alg_canon (APPEND (MAP (CONS T) c) (MAP (CONS F) c'))
               = alg_canon [[]]`
     >> (RW_TAC std_ss [ALG_CANON_REP, ALGEBRA_EMBED_BASIC] ++ PSET_TAC [])
     ++ NTAC 3 (POP_ASSUM MP_TAC)
     ++ RW_TAC std_ss [algebra_canon_def, ALG_CANON_BASIC]
     ++ PROVE_TAC [MEM_NIL_STEP, MEM],
     MATCH_MP_TAC (REAL_ARITH ``(2:real) * a <= 2 * b ==> a <= b``)
     ++ PSET_TAC [ALGEBRA_EMBED_APPEND, ALG_MEASURE_APPEND, REAL_ADD_LDISTRIB,
                  ALG_MEASURE_TLS]
     ++ KNOW_TAC `!x. algebra_embed l1 x ==> algebra_embed c x`
     >> (STRIP_TAC
         ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T x`)
         ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS, STL_SCONS, SHD_SCONS])
     ++ KNOW_TAC `!x. algebra_embed l2 x ==> algebra_embed c' x`
     >> (POP_ASSUM (K ALL_TAC)
         ++ STRIP_TAC
         ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS F x`)
         ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS, STL_SCONS, SHD_SCONS])
     ++ RES_TAC
     ++ SUFF_TAC `alg_measure l1 <= alg_measure c
                  /\ alg_measure l2 <= alg_measure c'`
     >> (KILL_ALL_TAC ++ REAL_ARITH_TAC)
     ++ RW_TAC std_ss []]]);

val ALG_MEASURE_COMPL = store_thm
  ("ALG_MEASURE_COMPL",
   ``!b. algebra_canon b ==> !c. algebra_canon c
         ==> (COMPL (algebra_embed b) = algebra_embed c)
         ==> (alg_measure b + alg_measure c = 1)``,
   HO_MATCH_MP_TAC ALGEBRA_CANON_INDUCTION
   ++ PSET_TAC [ALG_MEASURE_BASIC, ALGEBRA_EMBED_BASIC] <<
   [KNOW_TAC `alg_canon c = alg_canon [[]]`
    >> PSET_TAC [ALG_CANON_REP, ALGEBRA_EMBED_BASIC]
    ++ PSET_TAC [ALG_CANON_BASIC, algebra_canon_def, ALGEBRA_EMBED_BASIC,
                 ALG_MEASURE_BASIC, REAL_ADD_LID],
    KNOW_TAC `alg_canon c = alg_canon []`
    >> PSET_TAC [ALG_CANON_REP, ALGEBRA_EMBED_BASIC]
    ++ PSET_TAC [ALG_CANON_BASIC, algebra_canon_def, ALGEBRA_EMBED_BASIC,
                 ALG_MEASURE_BASIC, REAL_ADD_RID],
    NTAC 2 (POP_ASSUM MP_TAC)
    ++ Q.SPEC_TAC (`c`, `c`)
    ++ HO_MATCH_MP_TAC ALGEBRA_CANON_CASES
    ++ PSET_TAC [ALGEBRA_EMBED_BASIC, ALG_MEASURE_BASIC] <<
    [SUFF_TAC `APPEND (MAP (CONS T) b) (MAP (CONS F) b') = [[]]`
     >> PROVE_TAC [MEM_NIL_STEP, MEM]
     ++ PROVE_TAC [ALGEBRA_CANON_EMBED_UNIV],
     KNOW_TAC `APPEND (MAP (CONS T) b) (MAP (CONS F) b') = []`
     >> PROVE_TAC [ALGEBRA_CANON_EMBED_EMPTY]
     ++ RW_TAC std_ss [ALG_MEASURE_BASIC, REAL_ADD_LID],
     MATCH_MP_TAC
       (REAL_ARITH ``(2 * (a:real) + 2 * b = 1 + 1) ==> (a + b = 1)``)
     ++ PSET_TAC [ALGEBRA_EMBED_APPEND, ALG_MEASURE_APPEND, ALG_MEASURE_TLS,
                  REAL_ADD_LDISTRIB]
     ++ SUFF_TAC `(alg_measure b + alg_measure l1 = 1)
                  /\ (alg_measure b' + alg_measure l2 = 1)`
     >> REAL_ARITH_TAC
     ++ CONJ_TAC <<
     [SUFF_TAC `!v. ~algebra_embed b v = algebra_embed l1 v`
      >> PROVE_TAC []
      ++ STRIP_TAC
      ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
      ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS, SHD_SCONS, STL_SCONS],
      SUFF_TAC `!v. ~algebra_embed b' v = algebra_embed l2 v`
      >> PROVE_TAC []
      ++ STRIP_TAC
      ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS F v`)
      ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS, SHD_SCONS, STL_SCONS]]]]);

val ALG_MEASURE_ADDITIVE = store_thm
  ("ALG_MEASURE_ADDITIVE",
   ``!b. algebra_canon b ==> !c. algebra_canon c ==> !d. algebra_canon d
	 ==> (algebra_embed c INTER algebra_embed d = {})
	     /\ (algebra_embed b = algebra_embed c UNION algebra_embed d)
	     ==> (alg_measure b = alg_measure c + alg_measure d)``,
   HO_MATCH_MP_TAC ALGEBRA_CANON_INDUCTION
   ++ PSET_TAC [ALG_MEASURE_BASIC, ALGEBRA_EMBED_BASIC] <<
   [KNOW_TAC `c = []` >> PROVE_TAC [ALGEBRA_CANON_EMBED_EMPTY]
    ++ KNOW_TAC `d = []` >> PROVE_TAC [ALGEBRA_CANON_EMBED_EMPTY]
    ++ RW_TAC real_ac_ss [ALG_MEASURE_BASIC],
    MP_TAC (Q.SPEC `c` ALG_MEASURE_COMPL)
    ++ ASM_REWRITE_TAC []
    ++ DISCH_THEN (MP_TAC o Q.SPEC `d`)
    ++ PSET_TAC []
    ++ PROVE_TAC [],
    NTAC 4 (POP_ASSUM MP_TAC)
    ++ Q.SPEC_TAC (`c`, `c`)
    ++ HO_MATCH_MP_TAC ALGEBRA_CANON_CASES
    ++ PSET_TAC [ALG_MEASURE_BASIC, ALGEBRA_EMBED_BASIC] <<
    [SUFF_TAC `d = APPEND (MAP (CONS T) b) (MAP (CONS F) b')`
     >> RW_TAC real_ac_ss []
     ++ SUFF_TAC `alg_canon d
                  = alg_canon (APPEND (MAP (CONS T) b) (MAP (CONS F) b'))`
     >> PROVE_TAC [algebra_canon_def]
     ++ PSET_TAC [ALG_CANON_REP],
     SUFF_TAC `APPEND (MAP (CONS T) b) (MAP (CONS F) b') = [[]]`
     >> PROVE_TAC [MEM_NIL_STEP, MEM]
     ++ PROVE_TAC [ALGEBRA_CANON_EMBED_UNIV],
     NTAC 3 (POP_ASSUM MP_TAC)
     ++ Q.SPEC_TAC (`d`, `d`)
     ++ HO_MATCH_MP_TAC ALGEBRA_CANON_CASES
     ++ PSET_TAC [ALG_MEASURE_BASIC, ALGEBRA_EMBED_BASIC] <<
     [SUFF_TAC `APPEND (MAP (CONS T) b) (MAP (CONS F) b') =
                APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)`
      >> RW_TAC real_ac_ss []
      ++ SUFF_TAC `alg_canon (APPEND (MAP (CONS T) b) (MAP (CONS F) b')) =
                   alg_canon (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))`
      >> PSET_TAC [algebra_canon_def]
      ++ PSET_TAC [ALG_CANON_REP],
      SUFF_TAC `APPEND (MAP (CONS T) b) (MAP (CONS F) b') = [[]]`
      >> PROVE_TAC [MEM_NIL_STEP, MEM]
      ++ PROVE_TAC [ALGEBRA_CANON_EMBED_UNIV],
      MATCH_MP_TAC (REAL_ARITH ``(2 * (a:real) = 2 * b) ==> (a = b)``)
      ++ PSET_TAC [REAL_ADD_LDISTRIB, ALG_MEASURE_APPEND, ALG_MEASURE_TLS,
                   ALGEBRA_EMBED_APPEND]
      ++ SUFF_TAC `(alg_measure b = alg_measure l1 + alg_measure l1') /\
                   (alg_measure b' = alg_measure l2 + alg_measure l2')`
      >> RW_TAC real_ac_ss []
      ++ CONJ_TAC <<
      [SUFF_TAC `(!v. ~algebra_embed l1 v \/ ~algebra_embed l1' v) /\
         (!v. algebra_embed b v = algebra_embed l1 v \/ algebra_embed l1' v)`
       >> (Q.PAT_ASSUM `!c. algebra_canon c ==> !d. algebra_canon d ==>
               (!v. ~algebra_embed c v \/ ~algebra_embed d v) /\
               (!v. algebra_embed b v =
                    algebra_embed c v \/ algebra_embed d v) ==>
               (alg_measure b = alg_measure c + alg_measure d)`
             (MP_TAC o Q.SPEC `l1`)
           ++ RW_TAC std_ss [])
       ++ RW_TAC std_ss [] <<
       [POP_ASSUM (K ALL_TAC)
        ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
        ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS, STL_SCONS, SHD_SCONS],
        POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
        ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS, STL_SCONS, SHD_SCONS]],
       SUFF_TAC `(!v. ~algebra_embed l2 v \/ ~algebra_embed l2' v) /\
         (!v. algebra_embed b' v = algebra_embed l2 v \/ algebra_embed l2' v)`
       >> (Q.PAT_ASSUM `!c. algebra_canon c ==> !d. algebra_canon d ==>
               (!v. ~algebra_embed c v \/ ~algebra_embed d v) /\
               (!v. algebra_embed b' v =
                    algebra_embed c v \/ algebra_embed d v) ==>
               (alg_measure b' = alg_measure c + alg_measure d)`
             (MP_TAC o Q.SPEC `l2`)
           ++ RW_TAC std_ss [])
       ++ RW_TAC std_ss [] <<
       [POP_ASSUM (K ALL_TAC)
        ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS F v`)
        ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS, STL_SCONS, SHD_SCONS],
        POP_ASSUM (MP_TAC o Q.SPEC `SCONS F v`)
        ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS, STL_SCONS, SHD_SCONS]]]]]]);

val PROB_ALGEBRA = store_thm
  ("PROB_ALGEBRA",
   ``!l. prob (algebra_embed l) = algebra_measure l``,
   RW_TAC list_ss [prob_def]
   ++ HO_MATCH_MP_TAC REAL_SUP_MAX
   ++ CONJ_TAC <<
   [RW_TAC std_ss [SUBSET_DEF, SPECIFICATION]
    ++ PROVE_TAC [],
    RW_TAC std_ss []
    ++ PROVE_TAC [ALGEBRA_MEASURE_MONO_EMBED]]);

val PROB_BASIC = store_thm
  ("PROB_BASIC",
   ``(prob {} = 0) /\ (prob UNIV = 1) /\ (!b. prob (\s. SHD s = b) = 1 / 2)``,
   RW_TAC std_ss [GSYM ALGEBRA_EMBED_BASIC, PROB_ALGEBRA,
                  ALGEBRA_MEASURE_BASIC]);

val PROB_ADDITIVE = store_thm
  ("PROB_ADDITIVE",
   ``!s t. measurable s /\ measurable t /\ (s INTER t = {})
           ==> (prob (s UNION t) = prob s + prob t)``,
   RW_TAC std_ss []
   ++ KNOW_TAC `measurable (s UNION t)` >> PROVE_TAC [MEASURABLE_UNION]
   ++ NTAC 4 (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss [measurable_def]
   ++ RW_TAC std_ss [PROB_ALGEBRA]
   ++ RW_TAC std_ss [ALGEBRA_MEASURE_DEF_ALT]
   ++ MP_TAC (SPEC ``alg_canon b''`` ALG_MEASURE_ADDITIVE)
   ++ RW_TAC std_ss [ALG_CANON_IDEMPOT, ALG_CANON_EMBED, algebra_canon_def]);

val PROB_COMPL = store_thm
  ("PROB_COMPL",
   ``!s. measurable s ==> (prob (COMPL s) = 1 - prob s)``,
   RW_TAC std_ss []
   ++ KNOW_TAC `measurable (COMPL s)`
     >> PROVE_TAC [MEASURABLE_COMPL]
   ++ SUFF_TAC `1 = prob (COMPL s) + prob s` >> REAL_ARITH_TAC
   ++ KNOW_TAC `1 = prob UNIV` >> PROVE_TAC [PROB_BASIC]
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [COMPL_CLAUSES, PROB_ADDITIVE]);

val PROB_SUP_EXISTS1 = store_thm
  ("PROB_SUP_EXISTS1",
   ``!s. ?r. ?b. (algebra_measure b = r) /\ algebra_embed b SUBSET s``,
   STRIP_TAC
   ++ Q.EXISTS_TAC `0`
   ++ Q.EXISTS_TAC `[]`
   ++ PSET_TAC [ALGEBRA_MEASURE_BASIC, ALGEBRA_EMBED_BASIC]);

val PROB_SUP_EXISTS2 = store_thm
  ("PROB_SUP_EXISTS2",
   ``!s. ?z. !r. (?b. (algebra_measure b = r) /\ algebra_embed b SUBSET s)
                 ==> r <= z``,
   STRIP_TAC
   ++ Q.EXISTS_TAC `1`
   ++ RW_TAC std_ss []
   ++ RW_TAC std_ss [ALGEBRA_MEASURE_MAX]);

val PROB_LE_X = store_thm
  ("PROB_LE_X",
   ``!s x. (!s'. measurable s' /\ s' SUBSET s ==> prob s' <= x)
           ==> prob s <= x``,
   REPEAT STRIP_TAC
   ++ RW_TAC std_ss [prob_def]
   ++ MATCH_MP_TAC REAL_SUP_LE_X
   ++ CONJ_TAC >> RW_TAC real_ac_ss [PROB_SUP_EXISTS1]
   ++ RW_TAC real_ac_ss []
   ++ SUFF_TAC `prob (algebra_embed b) <= x`
     >> RW_TAC real_ac_ss [PROB_ALGEBRA]
   ++ SUFF_TAC `measurable (algebra_embed b)` >> PROVE_TAC []
   ++ PROVE_TAC [measurable_def]);

val X_LE_PROB = store_thm
  ("X_LE_PROB",
   ``!s x. (?s'. measurable s' /\ s' SUBSET s /\ x <= prob s')
           ==> x <= prob s``,
   RW_TAC std_ss [measurable_def]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [PROB_ALGEBRA]
   ++ RW_TAC std_ss [prob_def]
   ++ MATCH_MP_TAC REAL_X_LE_SUP
   ++ CONJ_TAC >> RW_TAC real_ac_ss [PROB_SUP_EXISTS1]
   ++ CONJ_TAC >> RW_TAC real_ac_ss [PROB_SUP_EXISTS2]
   ++ RW_TAC real_ac_ss []
   ++ EXISTS_TAC ``algebra_measure b``
   ++ PROVE_TAC []);

val PROB_SUBSET_MONO = store_thm
  ("PROB_SUBSET_MONO",
   ``!s t. s SUBSET t ==> prob s <= prob t``,
   RW_TAC pset_ss []
   ++ MATCH_MP_TAC PROB_LE_X
   ++ RW_TAC std_ss [measurable_def]
   ++ MATCH_MP_TAC X_LE_PROB
   ++ EXISTS_TAC ``algebra_embed b``
   ++ RW_TAC std_ss [measurable_def] <<
   [PROVE_TAC [],
    POP_ASSUM MP_TAC
    ++ RW_TAC pset_ss [],
    REAL_ARITH_TAC]);

val PROB_ALG = store_thm
  ("PROB_ALG",
   ``!x. prob (alg_embed x) = (1 / 2) pow LENGTH x``,
   STRIP_TAC
   ++ KNOW_TAC `alg_embed x = algebra_embed [x]`
   >> PSET_TAC [algebra_embed_def]
   ++ RW_TAC std_ss [PROB_ALGEBRA, ALGEBRA_MEASURE_DEF_ALT]
   ++ RW_TAC prob_canon_ss []
   ++ RW_TAC real_ac_ss [alg_measure_def]);

val PROB_STL = store_thm
  ("PROB_STL",
   ``!p. measurable p ==> (prob (p o STL) = prob p)``,
   RW_TAC std_ss []
   ++ KNOW_TAC `measurable (p o STL)` >> RW_TAC std_ss [MEASURABLE_STL]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss [measurable_def]
   ++ RW_TAC std_ss [PROB_ALGEBRA, ALGEBRA_MEASURE_DEF_ALT]
   ++ POP_ASSUM MP_TAC
   ++ SUFF_TAC `!c. algebra_canon c ==> !b. algebra_canon b
                ==> (algebra_embed b o STL = algebra_embed c)
                ==> (alg_measure b = alg_measure c)`
   >> (DISCH_THEN (MP_TAC o Q.SPEC `alg_canon b'`)
       ++ RW_TAC std_ss [algebra_canon_def, ALG_CANON_EMBED, ALG_CANON_IDEMPOT]
       ++ PROVE_TAC [algebra_canon_def, ALG_CANON_EMBED, ALG_CANON_IDEMPOT])
   ++ HO_MATCH_MP_TAC ALGEBRA_CANON_CASES
   ++ PSET_TAC [ALGEBRA_EMBED_BASIC, ALG_MEASURE_BASIC, o_DEF] <<
   [SUFF_TAC `b = []` >> RW_TAC std_ss [ALG_MEASURE_BASIC]
    ++ KNOW_TAC `!v. ~algebra_embed b v`
    >> (RW_TAC std_ss []
        ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
        ++ RW_TAC std_ss [STL_SCONS])
    ++ PROVE_TAC [ALGEBRA_CANON_EMBED_EMPTY],
    SUFF_TAC `b = [[]]` >> RW_TAC std_ss [ALG_MEASURE_BASIC]
    ++ KNOW_TAC `!v. algebra_embed b v`
    >> (RW_TAC std_ss []
        ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
        ++ RW_TAC std_ss [STL_SCONS])
    ++ PROVE_TAC [ALGEBRA_CANON_EMBED_UNIV],
    KNOW_TAC `l1 = l2`
    >> (SUFF_TAC `alg_canon l1 = alg_canon l2` >> PROVE_TAC [algebra_canon_def]
        ++ PSET_TAC [ALG_CANON_REP]
        ++ POP_ASSUM (fn th => MP_TAC (Q.SPEC `SCONS T v` th)
                      ++ MP_TAC (Q.SPEC `SCONS F v` th))
        ++ PSET_TAC [SHD_SCONS, STL_SCONS, ALGEBRA_EMBED_APPEND,
                     ALGEBRA_EMBED_TLS])
    ++ RW_TAC std_ss []
    ++ KNOW_TAC `b = l1`
    >> (SUFF_TAC `alg_canon b = alg_canon l1` >> PROVE_TAC [algebra_canon_def]
        ++ PSET_TAC [ALG_CANON_REP]
        ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
        ++ PSET_TAC [SHD_SCONS, STL_SCONS, ALGEBRA_EMBED_APPEND,
                     ALGEBRA_EMBED_TLS])
    ++ MATCH_MP_TAC (REAL_ARITH ``((2:real) * a = 2 * b) ==> (a = b)``)
    ++ RW_TAC std_ss [ALG_MEASURE_APPEND, ALG_MEASURE_TLS, REAL_ADD_LDISTRIB]
    ++ REAL_ARITH_TAC]);

val PROB_SDROP = store_thm
  ("PROB_SDROP",
   ``!n p. measurable p ==> (prob (p o SDROP n) = prob p)``,
   Induct >> RW_TAC std_ss' [o_DEF, I_THM, SDROP_def]
   ++ RW_TAC bool_ss [o_ASSOC, SDROP_def]
   ++ KNOW_TAC `measurable (p o SDROP n)` >> PROVE_TAC [MEASURABLE_SDROP]
   ++ PROVE_TAC [PROB_STL]);

val PROB_INTER_HALVES = store_thm
  ("PROB_INTER_HALVES",
   ``!p. measurable p
         ==> (prob ((\x. SHD x = T) INTER p) + prob ((\x. SHD x = F) INTER p)
	      = prob p)``,
   RW_TAC std_ss' []
   ++ SUFF_TAC `prob (SHD INTER p UNION (\x. ~SHD x) INTER p)
                = prob (SHD INTER p) + prob ((\x. ~SHD x) INTER p)`
   >> (SUFF_TAC `SHD INTER p UNION (\x. ~SHD x) INTER p  = p`
       >> PROVE_TAC []
       ++ PSET_TAC []
       ++ PROVE_TAC [])
   ++ MATCH_MP_TAC PROB_ADDITIVE
   ++ MP_TAC (Q.SPEC `p` MEASURABLE_INTER_HALVES)
   ++ RW_TAC std_ss' []
   ++ PSET_TAC []
   ++ PROVE_TAC []);

val PROB_INTER_SHD = store_thm
  ("PROB_INTER_SHD",
   ``!b p. measurable p
           ==> (prob ((\x. SHD x = b) INTER p o STL) = 1 / 2 * prob p)``,
   RW_TAC std_ss []
   ++ KNOW_TAC `measurable ((\x. SHD x = b) INTER p o STL)`
   >> RW_TAC std_ss [MEASURABLE_INTER_SHD]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss [measurable_def]
   ++ RW_TAC std_ss [PROB_ALGEBRA, ALGEBRA_MEASURE_DEF_ALT]
   ++ MATCH_MP_TAC (REAL_ARITH ``((2:real) * a = 2 * b) ==> (a = b)``)
   ++ SUFF_TAC `alg_canon b'' = MAP (CONS b) (alg_canon b')`
   >> RW_TAC std_ss [ALG_MEASURE_TLS, REAL_MUL_ASSOC, HALF_CANCEL, REAL_MUL_LID]
   ++ POP_ASSUM MP_TAC
   ++ SUFF_TAC `!c d. algebra_canon c ==> algebra_canon d
                ==> ((\x. SHD x = b) INTER algebra_embed d o STL
		     = algebra_embed c)
                ==> (c = MAP (CONS b) d)`
   >> (DISCH_THEN (MP_TAC o Q.SPECL [`alg_canon b''`, `alg_canon b'`])
       ++ RW_TAC std_ss [algebra_canon_def, ALG_CANON_IDEMPOT, ALG_CANON_EMBED])
   ++ RW_TAC std_ss []
   ++ SUFF_TAC `alg_canon c = alg_canon (MAP (CONS b) d)`
   >> PROVE_TAC [algebra_canon_def, ALGEBRA_CANON_TLS]
   ++ PSET_TAC [ALG_CANON_REP]
   ++ SEQ_CASES_TAC `v`
   ++ PSET_TAC [ALGEBRA_EMBED_TLS, o_DEF]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS h t`)
   ++ RW_TAC std_ss [SHD_SCONS, STL_SCONS]);

val ALGEBRA_MEASURE_POS = store_thm
  ("ALGEBRA_MEASURE_POS",
   ``!l. 0 <= algebra_measure l``,
   RW_TAC std_ss [ALGEBRA_MEASURE_DEF_ALT, ALG_MEASURE_POS]);

val ALGEBRA_MEASURE_RANGE = store_thm
  ("ALGEBRA_MEASURE_RANGE",
   ``!l. 0 <= algebra_measure l /\ algebra_measure l <= 1``,
   PROVE_TAC [ALGEBRA_MEASURE_POS, ALGEBRA_MEASURE_MAX]);

val PROB_POS = store_thm
  ("PROB_POS",
   ``!p. 0 <= prob p``,
   STRIP_TAC
   ++ MATCH_MP_TAC X_LE_PROB
   ++ Q.EXISTS_TAC `{}`
   ++ PSET_TAC [MEASURABLE_BASIC, PROB_BASIC, REAL_LE_REFL]);

val PROB_MAX = store_thm
  ("PROB_MAX",
   ``!p. prob p <= 1``,
   STRIP_TAC
   ++ MATCH_MP_TAC PROB_LE_X
   ++ RW_TAC std_ss [measurable_def]
   ++ RW_TAC std_ss [PROB_ALGEBRA, ALGEBRA_MEASURE_MAX]);

val PROB_RANGE = store_thm
  ("PROB_RANGE",
   ``!p. 0 <= prob p /\ prob p <= 1``,
   PROVE_TAC [PROB_POS, PROB_MAX]);

val ABS_PROB = store_thm
  ("ABS_PROB",
   ``!p. abs (prob p) = prob p``,
   RW_TAC std_ss [abs, PROB_POS]);

val PROB_SHD = store_thm
  ("PROB_SHD",
   ``!b. prob (\s. SHD s = b) = 1 / 2``,
   RW_TAC std_ss [PROB_BASIC]);

val PROB_COMPL_LE1 = store_thm
  ("PROB_COMPL_LE1",
   ``!p r. measurable p ==> (prob (COMPL p) <= r = 1 - r <= prob p)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `p` PROB_COMPL)
   ++ RW_TAC std_ss []
   ++ REAL_ARITH_TAC);

val _ = export_theory ();

