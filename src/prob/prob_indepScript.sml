open HolKernel Parse boolLib bossLib arithmeticTheory realTheory
     seqTheory pred_setTheory ind_typeTheory listTheory
     rich_listTheory pairTheory combinTheory realLib probTools
     boolean_sequenceTheory boolean_sequenceTools prob_extraTheory
     prob_extraTools prob_canonTheory prob_canonTools
     prob_algebraTheory probTheory state_transformerTheory realSimps;

val _ = new_theory "prob_indep";

infixr 0 ++ << || ORELSEC ##;
infix 1 >>;
nonfix THEN THENL ORELSE;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

local
  infix ++;
  open simpLib;
in
  val std_ss' =
    (boolSimps.bool_ss ++ pairSimps.PAIR_ss ++ optionSimps.OPTION_ss ++
     numSimps.REDUCE_ss ++ sumSimps.SUM_ss ++ boolSimps.ETA_ss ++
     boolSimps.LET_ss);
end;

(* ------------------------------------------------------------------------- *)
(* The definition of independence.                                           *)
(* ------------------------------------------------------------------------- *)

val indep_set_def = Define `indep_set p q
  = measurable p /\ measurable q /\ (prob (p INTER q) = prob p * prob q)`;

val alg_cover_set_def = Define `alg_cover_set l
      = alg_sorted l /\ alg_prefixfree l /\ (algebra_embed l = UNIV)`;

val alg_cover_def = Define `alg_cover l x = @b. MEM b l /\ alg_embed b x`;

val indep_def = Define `indep (f:(num->bool) -> 'a # (num->bool))
      = ?l r. alg_cover_set l
           /\ (!s. f s = let c = alg_cover l s in (r c, SDROP (LENGTH c) s))`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. Induction theorem on alg_cover_set                                     *)
(* 2. indep f /\ measurable q ==> indep_set (p o FST o f) (q o SND o f)      *)
(* 3. indep (UNIT x)                                                         *)
(* 4. indep SDEST                                                            *)
(* 5. (!x. indep (f x)) ==> indep (BIND SDEST f)                             *)
(* 6. indep f /\ (!x. indep (g x)) ==> indep (BIND f g)                      *)
(* ------------------------------------------------------------------------- *)

val INDEP_SET_BASIC = store_thm
  ("INDEP_SET_BASIC",
   ``!p. measurable p ==> indep_set {} p /\ indep_set UNIV p``,
   PSET_TAC [indep_set_def, PROB_BASIC, MEASURABLE_BASIC]
   ++ RW_TAC real_ac_ss []);

val INDEP_SET_SYM = store_thm
  ("INDEP_SET_SYM",
   ``!p q. indep_set p q = indep_set p q``,
   RW_TAC std_ss' [indep_set_def]
   ++ PROVE_TAC [INTER_COMM, REAL_MUL_SYM]);

val INDEP_SET_DISJOINT_DECOMP = store_thm
  ("INDEP_SET_DISJOINT_DECOMP",
   ``!p q r. indep_set p r /\ indep_set q r /\ (p INTER q = {})
             ==> indep_set (p UNION q) r``,
   RW_TAC std_ss' [indep_set_def, INTER_UNION_RDISTRIB]
   >> PROVE_TAC [MEASURABLE_UNION]
   ++ RW_TAC std_ss' [PROB_ADDITIVE, REAL_ADD_RDISTRIB]
   ++ KNOW_TAC `(p INTER r) INTER (q INTER r) = {}`
   >> (Q.PAT_ASSUM `p INTER q = {}` MP_TAC
       ++ RW_TAC pset_ss []
       ++ PROVE_TAC [])
   ++ KNOW_TAC `measurable (p INTER r) /\ measurable (q INTER r)`
   >> PROVE_TAC [MEASURABLE_INTER]
   ++ RW_TAC std_ss' [PROB_ADDITIVE]);

val ALG_COVER_SET_BASIC = store_thm
  ("ALG_COVER_SET_BASIC",
   ``~alg_cover_set [] /\ alg_cover_set [[]] /\ alg_cover_set [[T]; [F]]``,
   PSET_TAC [alg_cover_set_def, algebra_embed_def, alg_embed_def,
             alg_sorted_def, alg_prefixfree_def, IS_PREFIX, alg_order_def]);

val ALG_COVER_WELL_DEFINED = store_thm
  ("ALG_COVER_WELL_DEFINED",
   ``!l x. alg_cover_set l
           ==> MEM (alg_cover l x) l /\ alg_embed (alg_cover l x) x``,
   NTAC 3 STRIP_TAC
   ++ SUFF_TAC `(\b. MEM b l /\ alg_embed b x)
                ($@ (\b. MEM b l /\ alg_embed b x))`
     >> RW_TAC std_ss' [alg_cover_def]
   ++ MATCH_MP_TAC SELECT_AX
   ++ RW_TAC std_ss' []
   ++ SUFF_TAC `algebra_embed l x` >> PROVE_TAC [ALGEBRA_EMBED_MEM]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC pset_ss [alg_cover_set_def]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss' [SPECIFICATION]);

val ALG_COVER_UNIV = store_thm
  ("ALG_COVER_UNIV",
   ``alg_cover [[]] = K []``,
   RW_TAC std_ss' [GSYM EQ_EXT_EQ]
   ++ MP_TAC (Q.SPECL [`[[]]`, `x`] ALG_COVER_WELL_DEFINED)
   ++ RW_TAC std_ss' [MEM, K_DEF, ALG_COVER_SET_BASIC]);

val MAP_CONS_TL_FILTER = store_thm
  ("MAP_CONS_TL_FILTER",
   ``!l (b:bool). ~MEM [] l ==>
           (MAP (CONS b) (MAP TL (FILTER (\x. HD x = b) l))
	    = FILTER (\x. HD x = b) l)``,
   Induct >> RW_TAC list_ss [MEM, FILTER]
   ++ RW_TAC list_ss [MEM, FILTER]
   ++ (Cases_on `h` ++ RW_TAC list_ss []));

val ALG_COVER_SET_CASES_THM = store_thm
  ("ALG_COVER_SET_CASES_THM",
   ``!l. alg_cover_set l = (l = [[]]) \/
           ?l1 l2. alg_cover_set l1 /\ alg_cover_set l2
                   /\ (l = APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))``,
   RW_TAC std_ss' [alg_cover_set_def]
   ++ REVERSE EQ_TAC <<
   [PSET_TAC [alg_sorted_def, alg_prefixfree_def, ALGEBRA_EMBED_BASIC] <<
    [PSET_TAC [],
     Cases_on `l1` >> PSET_TAC [ALGEBRA_EMBED_BASIC]
     ++ Cases_on `l2` >> PSET_TAC [ALGEBRA_EMBED_BASIC]
     ++ RW_TAC std_ss' [MAP, ALG_SORTED_APPEND] <<
     [SUFF_TAC `alg_sorted (MAP (CONS T) (h::t))` >> RW_TAC list_ss []
      ++ RW_TAC std_ss' [ALG_SORTED_TLS],
      SUFF_TAC `alg_sorted (MAP (CONS F) (h'::t'))` >> RW_TAC list_ss []
      ++ RW_TAC std_ss' [ALG_SORTED_TLS],
      SUFF_TAC `alg_order (LAST (MAP (CONS T) (h::t))) (F::h')`
      >> RW_TAC list_ss []
      ++ MP_TAC (Q.SPECL [`T`, `h`, `t`] LAST_MAP_CONS)
      ++ RW_TAC std_ss' []
      ++ RW_TAC std_ss' [alg_order_def]],
     Cases_on `l1` >> PSET_TAC [ALGEBRA_EMBED_BASIC]
     ++ Cases_on `l2` >> PSET_TAC [ALGEBRA_EMBED_BASIC]
     ++ RW_TAC std_ss' [MAP, ALG_PREFIXFREE_APPEND] <<
     [SUFF_TAC `alg_prefixfree (MAP (CONS T) (h::t))` >> RW_TAC list_ss []
      ++ RW_TAC std_ss' [ALG_PREFIXFREE_TLS],
      SUFF_TAC `alg_prefixfree (MAP (CONS F) (h'::t'))` >> RW_TAC list_ss []
      ++ RW_TAC std_ss' [ALG_PREFIXFREE_TLS],
      SUFF_TAC `~IS_PREFIX (F::h') (LAST (MAP (CONS T) (h::t)))`
      >> RW_TAC list_ss []
      ++ MP_TAC (Q.SPECL [`T`, `h`, `t`] LAST_MAP_CONS)
      ++ RW_TAC std_ss' []
      ++ RW_TAC std_ss' [IS_PREFIX]],
     SEQ_CASES_TAC `v`
     ++ PSET_TAC [ALGEBRA_EMBED_APPEND, ALGEBRA_EMBED_TLS]],
    Cases_on `MEM [] l`
    >> (MP_TAC (Q.SPEC `l` ALG_SORTED_PREFIXFREE_MEM_NIL)
        ++ RW_TAC std_ss' []
        ++ RES_TAC
        ++ RW_TAC std_ss' [])
    ++ PSET_TAC []
    ++ DISJ2_TAC
    ++ Q.EXISTS_TAC `MAP TL (FILTER (\x. HD x = T) l)`
    ++ Q.EXISTS_TAC `MAP TL (FILTER (\x. HD x = F) l)`
    ++ MP_TAC (Q.SPECL [`l`, `T`] MAP_CONS_TL_FILTER)
    ++ MP_TAC (Q.SPECL [`l`, `F`] MAP_CONS_TL_FILTER)
    ++ ASM_REWRITE_TAC []
    ++ NTAC 2 STRIP_TAC
    ++ KNOW_TAC `alg_sorted (MAP TL (FILTER (\x. HD x) l))`
    >> (PURE_ONCE_REWRITE_TAC [GSYM (Q.SPECL [`MAP TL (FILTER (\x. HD x) l)`,
                                              `T`] ALG_SORTED_TLS)]
        ++ RW_TAC std_ss' [ALG_SORTED_FILTER])
    ++ KNOW_TAC `alg_sorted (MAP TL (FILTER (\x. ~HD x) l))`
    >> (PURE_ONCE_REWRITE_TAC [GSYM (Q.SPECL [`MAP TL (FILTER (\x. ~HD x) l)`,
                                              `F`] ALG_SORTED_TLS)]
        ++ RW_TAC std_ss' [ALG_SORTED_FILTER])
    ++ KNOW_TAC `alg_prefixfree (MAP TL (FILTER (\x. HD x) l))`
    >> (PURE_ONCE_REWRITE_TAC [GSYM (Q.SPECL [`MAP TL (FILTER (\x. HD x) l)`,
                                              `T`] ALG_PREFIXFREE_TLS)]
        ++ RW_TAC std_ss' [ALG_PREFIXFREE_FILTER])
    ++ KNOW_TAC `alg_prefixfree (MAP TL (FILTER (\x. ~HD x) l))`
    >> (PURE_ONCE_REWRITE_TAC [GSYM (Q.SPECL [`MAP TL (FILTER (\x. ~HD x) l)`,
                                              `F`] ALG_PREFIXFREE_TLS)]
        ++ RW_TAC std_ss' [ALG_PREFIXFREE_FILTER])
    ++ SUFF_TAC `l = APPEND (MAP (CONS T) (MAP TL (FILTER (\x. HD x) l)))
                       (MAP (CONS F) (MAP TL (FILTER (\x. ~HD x) l)))`
    >> (DISCH_THEN (fn th => ASM_REWRITE_TAC [GSYM th] ++ MP_TAC th)
        ++ DISCH_THEN (fn th => Q.PAT_ASSUM `!v. algebra_embed l v`
                     (MP_TAC o ONCE_REWRITE_RULE [th]))
        ++ Q.PAT_ASSUM `~MEM [] l` MP_TAC
        ++ KILL_ALL_TAC
        ++ PSET_TAC [ALGEBRA_EMBED_APPEND] <<
        [POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
         ++ PSET_TAC [ALGEBRA_EMBED_TLS],
         POP_ASSUM (MP_TAC o Q.SPEC `SCONS F v`)
         ++ PSET_TAC [ALGEBRA_EMBED_TLS]])
    ++ MATCH_MP_TAC ALG_SORTED_PREFIXFREE_EQUALITY
    ++ RW_TAC std_ss' [] <<
    [RW_TAC list_ss [APPEND_MEM]
     ++ REVERSE EQ_TAC >> PROVE_TAC [MEM_FILTER]
     ++ Cases_on `x` >> RW_TAC std_ss' []
     ++ KILL_ALL_TAC
     ++ Induct_on `l` >> RW_TAC list_ss [MEM]
     ++ Cases_on `h` <<
     [RW_TAC list_ss [MEM, FILTER]
      ++ PROVE_TAC [],
      RW_TAC list_ss [MEM, FILTER]
      ++ PROVE_TAC []],
     Q.PAT_ASSUM `~MEM [] l` MP_TAC
     ++ Q.PAT_ASSUM `alg_sorted l` MP_TAC
     ++ KILL_ALL_TAC
     ++ Induct_on `l` >> RW_TAC list_ss [FILTER]
     ++ Cases_on `h` >> RW_TAC list_ss [MEM]
     ++ Cases_on `h'` <<
     [RW_TAC list_ss [FILTER, ALG_SORTED_DEF_ALT, APPEND_MEM]
      ++ PROVE_TAC [MEM_FILTER, MEM],
      RW_TAC list_ss [FILTER, ALG_SORTED_DEF_ALT]
      ++ Cases_on `FILTER HD l`
      >> (RW_TAC list_ss [ALG_SORTED_DEF_ALT]
          ++ PROVE_TAC [MEM_FILTER, ALG_SORTED_FILTER])
      ++ KNOW_TAC `MEM h l` >> PROVE_TAC [MEM_FILTER, MEM]
      ++ KNOW_TAC `alg_order (F::t) h` >> PROVE_TAC []
      ++ Cases_on `h` >> PROVE_TAC [MEM]
      ++ Cases_on `h'`
      >> (POP_ASSUM MP_TAC ++ REWRITE_TAC [alg_order_def])
      ++ KNOW_TAC `HD (F::t'')` >> PROVE_TAC [FILTER_MEM, MEM]
      ++ POP_ASSUM MP_TAC
      ++ RW_TAC std_ss' [HD]],
     Cases_on `FILTER HD l`
     >> (RW_TAC list_ss [APPEND] ++ PROVE_TAC [ALG_PREFIXFREE_FILTER])
     ++ Cases_on `FILTER (\x. ~HD x) l`
     >> (RW_TAC list_ss [APPEND_NIL]
         ++ PROVE_TAC [ALG_PREFIXFREE_FILTER])
     ++ RW_TAC std_ss' [ALG_PREFIXFREE_APPEND] <<
     [PROVE_TAC [ALG_PREFIXFREE_FILTER],
      PROVE_TAC [ALG_PREFIXFREE_FILTER],
      Cases_on `h'` >> PROVE_TAC [MEM, MEM_FILTER]
      ++ Cases_on `LAST (h::t)` >> PROVE_TAC [MEM, MEM_FILTER, LAST_MEM]
      ++ KNOW_TAC `HD (h'::t''')` >> PROVE_TAC [LAST_MEM, FILTER_MEM]
      ++ KNOW_TAC `(\x. ~HD x) (h''::t'')`
      >> (MATCH_MP_TAC FILTER_MEM
          ++ Q.EXISTS_TAC `l`
          ++ PROVE_TAC [MEM])
      ++ NTAC 2 (POP_ASSUM MP_TAC)
      ++ KILL_ALL_TAC
      ++ RW_TAC list_ss [IS_PREFIX]]]]);

val ALG_COVER_SET_CASES = store_thm
  ("ALG_COVER_SET_CASES",
   ``!P. P [[]]
         /\ (!l1 l2. alg_cover_set l1 /\ alg_cover_set l2
	     /\ alg_cover_set (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             ==> P (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)))
         ==> !l. (alg_cover_set l ==> P l)``,
   RW_TAC list_ss []
   ++ MP_TAC (SPEC ``l:bool list list`` ALG_COVER_SET_CASES_THM)
   ++ (RW_TAC list_ss [] ++ PROVE_TAC []));

val ALG_COVER_SET_INDUCTION = store_thm
  ("ALG_COVER_SET_INDUCTION",
   ``!P. P [[]]
         /\ (!l1 l2. alg_cover_set l1 /\ alg_cover_set l2 /\ P l1 /\ P l2
	     /\ alg_cover_set (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             ==> P (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)))
         ==> !l. (alg_cover_set l ==> P l)``,
   RW_TAC list_ss []
   ++ completeInduct_on `alg_longest l`
   ++ RW_TAC list_ss []
   ++ REVERSE (SUFF_TAC `(l = [[]]) \/ ?l1 l2.
          alg_cover_set l1 /\ alg_cover_set l2 /\
          (l = APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))`)
   >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [ALG_COVER_SET_CASES_THM])
       ++ RW_TAC std_ss' [])
   ++ RW_TAC std_ss' [] >> PROVE_TAC []
   ++ SUFF_TAC `P l1 /\ P l2` >> PROVE_TAC []
   ++ CONJ_TAC <<
   [Cases_on `l1` >> PROVE_TAC [ALG_COVER_SET_BASIC]
    ++ SUFF_TAC `alg_longest (h::t) < alg_longest
                   (APPEND (MAP (CONS T) (h::t)) (MAP (CONS F) l2))`
    >> PROVE_TAC []
    ++ KILL_ALL_TAC
    ++ MP_TAC (SPECL [``MAP (CONS T) (h::t)``, ``MAP (CONS F) l2``]
               ALG_LONGEST_APPEND)
    ++ RW_TAC arith_ss [ALG_LONGEST_TLS],
    Cases_on `l2` >> PROVE_TAC [ALG_COVER_SET_BASIC]
    ++ SUFF_TAC `alg_longest (h::t) < alg_longest
                   (APPEND (MAP (CONS T) l1) (MAP (CONS F) (h::t)))`
    >> PROVE_TAC []
    ++ KILL_ALL_TAC
    ++ MP_TAC (SPECL [``MAP (CONS T) l1``, ``MAP (CONS F) (h::t)``]
               ALG_LONGEST_APPEND)
    ++ RW_TAC arith_ss [ALG_LONGEST_TLS]]);

val ALG_COVER_EXISTS_UNIQUE = store_thm
  ("ALG_COVER_EXISTS_UNIQUE",
   ``!l. alg_cover_set l ==> !s. ?!x. MEM x l /\ alg_embed x s``,
   HO_MATCH_MP_TAC ALG_COVER_SET_INDUCTION
   ++ CONV_TAC (DEPTH_CONV EXISTS_UNIQUE_CONV)
   ++ CONJ_TAC >> RW_TAC list_ss [MEM, ALG_COVER_UNIV, K_DEF, alg_embed_def]
   ++ RW_TAC std_ss' [] >> PROVE_TAC [ALG_COVER_WELL_DEFINED]
   ++ SEQ_CASES_TAC `s`
   ++ Cases_on `x'` >> PROVE_TAC [MEM_NIL_STEP]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss' [alg_embed_def, SHD_SCONS, STL_SCONS]
   ++ Cases_on `x` >> PROVE_TAC [MEM_NIL_STEP]
   ++ Q.PAT_ASSUM `alg_embed (a::b) c` MP_TAC
   ++ RW_TAC std_ss' [alg_embed_def, SHD_SCONS, STL_SCONS]
   ++ Cases_on `h` <<
   [KNOW_TAC `MEM t' l /\ MEM t'' l`
    >> (Q.PAT_ASSUM `MEM x y` MP_TAC
        ++ Q.PAT_ASSUM `MEM x y` MP_TAC
        ++ RW_TAC list_ss [APPEND_MEM, MAP_MEM])
    ++ PROVE_TAC [],
    KNOW_TAC `MEM t' l' /\ MEM t'' l'`
    >> (Q.PAT_ASSUM `MEM x y` MP_TAC
        ++ Q.PAT_ASSUM `MEM x y` MP_TAC
        ++ RW_TAC list_ss [APPEND_MEM, MAP_MEM])
    ++ PROVE_TAC []]);

val ALG_COVER_UNIQUE = store_thm
  ("ALG_COVER_UNIQUE",
   ``!l x s. alg_cover_set l /\ MEM x l /\ alg_embed x s
             ==> (alg_cover l s = x)``,
   RW_TAC std_ss' []
   ++ MP_TAC (Q.SPEC `l` ALG_COVER_EXISTS_UNIQUE)
   ++ CONV_TAC (DEPTH_CONV EXISTS_UNIQUE_CONV)
   ++ ASM_REWRITE_TAC []
   ++ PROVE_TAC [ALG_COVER_WELL_DEFINED]);

val ALG_COVER_STEP = store_thm
  ("ALG_COVER_STEP",
   ``!l1 l2 h t. alg_cover_set l1 /\ alg_cover_set l2
     ==> (alg_cover (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)) (SCONS h t)
          = if h then T::alg_cover l1 t else F::alg_cover l2 t)``,
   NTAC 5 STRIP_TAC
   ++ KNOW_TAC `alg_cover_set (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))`
   >> PROVE_TAC [ALG_COVER_SET_CASES_THM]
   ++ RW_TAC std_ss' [] <<
   [MATCH_MP_TAC ALG_COVER_UNIQUE
    ++ RW_TAC std_ss' [APPEND_MEM, MAP_MEM, alg_embed_def, SHD_SCONS, STL_SCONS]
    ++ PROVE_TAC [ALG_COVER_WELL_DEFINED],
    MATCH_MP_TAC ALG_COVER_UNIQUE
    ++ RW_TAC std_ss' [APPEND_MEM, MAP_MEM, alg_embed_def, SHD_SCONS, STL_SCONS]
    ++ PROVE_TAC [ALG_COVER_WELL_DEFINED]]);

val ALG_COVER_HEAD = store_thm
  ("ALG_COVER_HEAD",
   ``!l. alg_cover_set l
     ==> !f. (f o alg_cover l = algebra_embed (FILTER f l))``,
   HO_MATCH_MP_TAC ALG_COVER_SET_INDUCTION
   ++ CONJ_TAC
   >> PSET_TAC [ALG_COVER_UNIV, K_DEF, o_DEF, FILTER, ALGEBRA_EMBED_BASIC]
   ++ Q.X_GEN_TAC `l1` ++ Q.X_GEN_TAC `l2`
   ++ RW_TAC std_ss' [o_DEF, GSYM EQ_EXT_EQ]
   ++ SEQ_CASES_TAC `x`
   ++ RW_TAC list_ss [FILTER_APPEND, FILTER_MAP, ALGEBRA_EMBED_APPEND,
                      UNION_DEF_ALT, ALGEBRA_EMBED_TLS]
   ++ (MP_TAC o Q.SPECL [`l1`, `l2`, `h`, `t`]) ALG_COVER_STEP
   ++ RW_TAC std_ss' [] <<
   [SUFF_TAC `f (T::alg_cover l1 t) = (f o CONS T) (alg_cover l1 t)`
    >> RW_TAC std_ss' []
    ++ KILL_ALL_TAC
    ++ RW_TAC std_ss' [o_DEF],
    SUFF_TAC `f (F::alg_cover l2 t) = (f o CONS F) (alg_cover l2 t)`
    >> RW_TAC std_ss' []
    ++ KILL_ALL_TAC
    ++ RW_TAC std_ss' [o_DEF]]);

val ALG_COVER_TAIL_STEP = store_thm
  ("ALG_COVER_TAIL_STEP",
   ``!l1 l2 q. alg_cover_set l1 /\ alg_cover_set l2 ==>
       (q o (\x. SDROP (LENGTH (alg_cover
                         (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)) x)) x)
        = (\x. SHD x = T)
            INTER q o (\x. SDROP (LENGTH (alg_cover l1 x)) x) o STL
          UNION (\x. SHD x = F)
            INTER q o (\x. SDROP (LENGTH (alg_cover l2 x)) x) o STL)``,
   PSET_TAC [o_DEF]
   ++ SEQ_CASES_TAC `v`
   ++ (MP_TAC o Q.SPECL [`l1`, `l2`, `h`, `t`]) ALG_COVER_STEP
   ++ PSET_TAC [SHD_SCONS, STL_SCONS, LENGTH, SDROP_def, o_DEF]);

val ALG_COVER_TAIL_MEASURABLE = store_thm
  ("ALG_COVER_TAIL_MEASURABLE",
   ``!l. alg_cover_set l
     ==> !q. (measurable (q o (\x. SDROP (LENGTH (alg_cover l x)) x))
              = measurable q)``,
   HO_MATCH_MP_TAC ALG_COVER_SET_INDUCTION
   ++ CONJ_TAC
   >> (PSET_TAC [ALG_COVER_UNIV, K_DEF, LENGTH, SDROP_def, o_DEF, I_THM]
       ++ RW_TAC std_ss' [])
   ++ Q.X_GEN_TAC `l1` ++ Q.X_GEN_TAC `l2`
   ++ RW_TAC std_ss' []
   ++ MP_TAC (Q.SPECL [`l1`, `l2`, `q`] ALG_COVER_TAIL_STEP)
   ++ MP_TAC MEASURABLE_HALVES
   ++ MP_TAC (Q.SPEC `T` MEASURABLE_INTER_SHD)
   ++ MP_TAC (Q.SPEC `F` MEASURABLE_INTER_SHD)
   ++ RW_TAC std_ss' []
   ++ RW_TAC std_ss' [o_ASSOC]);

val ALG_COVER_TAIL_PROB = store_thm
  ("ALG_COVER_TAIL_PROB",
   ``!l. alg_cover_set l
     ==> !q. measurable q
     ==> (prob (q o (\x. SDROP (LENGTH (alg_cover l x)) x)) = prob q)``,
   HO_MATCH_MP_TAC ALG_COVER_SET_INDUCTION
   ++ CONJ_TAC
   >> (PSET_TAC [ALG_COVER_UNIV, K_DEF, LENGTH, SDROP_def, o_DEF, I_THM]
       ++ RW_TAC std_ss' [])
   ++ Q.X_GEN_TAC `l1` ++ Q.X_GEN_TAC `l2`
   ++ RW_TAC std_ss' []
   ++ MP_TAC (Q.SPECL [`l1`, `l2`, `q`] ALG_COVER_TAIL_STEP)
   ++ RW_TAC std_ss' []
   ++ POP_ASSUM (K ALL_TAC)
   ++ SUFF_TAC `prob
          (SHD INTER q o (\x. SDROP (LENGTH (alg_cover l1 x)) x) o STL UNION
	   (\x. ~SHD x) INTER q o (\x. SDROP (LENGTH (alg_cover l2 x)) x) o STL)
	= prob (SHD INTER q
		o (\x. SDROP (LENGTH (alg_cover l1 x)) x) o STL)
	  + prob ((\x. ~SHD x) INTER q
		  o (\x. SDROP (LENGTH (alg_cover l2 x)) x) o STL)` <<
   [RES_TAC
    ++ RW_TAC std_ss' []
    ++ MP_TAC (Q.SPECL [`T`, `q o (\x. SDROP (LENGTH (alg_cover l1 x)) x)`]
	       PROB_INTER_SHD)
    ++ MP_TAC (Q.SPECL [`F`, `q o (\x. SDROP (LENGTH (alg_cover l2 x)) x)`]
	       PROB_INTER_SHD)
    ++ RW_TAC std_ss' [ALG_COVER_TAIL_MEASURABLE, o_ASSOC, X_HALF_HALF],
    MATCH_MP_TAC PROB_ADDITIVE
    ++ MP_TAC (Q.SPEC `T` MEASURABLE_INTER_SHD)
    ++ MP_TAC (Q.SPEC `F` MEASURABLE_INTER_SHD)
    ++ RW_TAC std_ss' [o_ASSOC, ALG_COVER_TAIL_MEASURABLE]
    ++ PSET_TAC []
    ++ PROVE_TAC []]);

val INTER_ASSOC = GSYM INTER_ASSOC
val INDEP_INDEP_SET_LEMMA = store_thm
  ("INDEP_INDEP_SET_LEMMA",
   ``!l. alg_cover_set l
     ==> !q. measurable q
     ==> !x. MEM x l
     ==> (prob (alg_embed x INTER q o (\x. SDROP (LENGTH (alg_cover l x)) x))
          = (1 / 2) pow LENGTH x * prob q)``,
   HO_MATCH_MP_TAC ALG_COVER_SET_INDUCTION
   ++ CONJ_TAC
   >> (PSET_TAC [MEM, ALG_COVER_UNIV, K_DEF, LENGTH, SDROP_def, I_THM, o_DEF,
                 ALG_EMBED_BASIC, pow, REAL_MUL_LID]
       ++ RW_TAC std_ss' [])
   ++ Q.X_GEN_TAC `l1` ++ Q.X_GEN_TAC `l2`
   ++ RW_TAC std_ss' []
   ++ MP_TAC ALG_COVER_TAIL_STEP
   ++ RW_TAC std_ss' []
   ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC std_ss' [UNION_OVER_INTER]
   ++ Cases_on `x` >> PROVE_TAC [MEM_NIL_STEP]
   ++ RW_TAC std_ss' [ALG_EMBED_BASIC]
   ++ MP_TAC HALVES_INTER
   ++ Cases_on `h` <<
   [RW_TAC std_ss' []
    ++ RW_TAC std_ss' [GSYM INTER_ASSOC]
    ++ KNOW_TAC `(SHD INTER alg_embed t o STL) INTER (\x. ~SHD x)
                 = (SHD INTER (\x. ~SHD x)) INTER alg_embed t o STL`
    >> (PSET_TAC [] ++ PROVE_TAC [])
    ++ RW_TAC std_ss' []
    ++ PSET_TAC []
    ++ KNOW_TAC `(SHD INTER alg_embed t o STL) INTER SHD
                 = SHD INTER alg_embed t o STL`
    >> (PSET_TAC [] ++ PROVE_TAC [])
    ++ RW_TAC std_ss' []
    ++ RW_TAC std_ss' [INTER_ASSOC, GSYM INTER_STL, o_ASSOC]
    ++ NTAC 2 (POP_ASSUM (K ALL_TAC))
    ++ POP_ASSUM MP_TAC
    ++ RW_TAC std_ss' [GSYM o_ASSOC, APPEND_MEM, MAP_MEM, LENGTH, pow,
		      GSYM REAL_MUL_ASSOC]
    ++ MP_TAC (Q.SPECL [`T`, `alg_embed t INTER q o (\x. SDROP (LENGTH
                         (alg_cover l1 x)) x)`] PROB_INTER_SHD)
    ++ SUFF_TAC `measurable (alg_embed t INTER q o (\x. SDROP (LENGTH
                         (alg_cover l1 x)) x))`
    >> RW_TAC std_ss' []
    ++ MATCH_MP_TAC MEASURABLE_INTER
    ++ RW_TAC std_ss' [ALG_COVER_TAIL_MEASURABLE]
    ++ KILL_ALL_TAC
    ++ RW_TAC std_ss' [measurable_def]
    ++ Q.EXISTS_TAC `[t]`
    ++ PSET_TAC [algebra_embed_def],
    RW_TAC std_ss' []
    ++ RW_TAC std_ss' [GSYM INTER_ASSOC]
    ++ KNOW_TAC `((\x. ~SHD x) INTER alg_embed t o STL) INTER SHD
                 = (SHD INTER (\x. ~SHD x)) INTER alg_embed t o STL`
    >> (PSET_TAC [] ++ PROVE_TAC [])
    ++ RW_TAC std_ss' []
    ++ KNOW_TAC `((\x. ~SHD x) INTER alg_embed t o STL) INTER (\x. ~SHD x)
                 = (\x. ~SHD x) INTER alg_embed t o STL`
    >> (PSET_TAC [] ++ PROVE_TAC [])
    ++ RW_TAC std_ss' []
    ++ PSET_TAC []
    ++ RW_TAC std_ss' [INTER_ASSOC, GSYM INTER_STL, o_ASSOC]
    ++ NTAC 2 (POP_ASSUM (K ALL_TAC))
    ++ POP_ASSUM MP_TAC
    ++ RW_TAC std_ss' [GSYM o_ASSOC, APPEND_MEM, MAP_MEM, LENGTH, pow,
		      GSYM REAL_MUL_ASSOC]
    ++ MP_TAC (Q.SPECL [`F`, `alg_embed t INTER q o (\x. SDROP (LENGTH
                          (alg_cover l2 x)) x)`] PROB_INTER_SHD)
    ++ SUFF_TAC `measurable (alg_embed t INTER q o (\x. SDROP (LENGTH
                          (alg_cover l2 x)) x))`
    >> RW_TAC std_ss' []
    ++ MATCH_MP_TAC MEASURABLE_INTER
    ++ RW_TAC std_ss' [ALG_COVER_TAIL_MEASURABLE]
    ++ KILL_ALL_TAC
    ++ RW_TAC std_ss' [measurable_def]
    ++ Q.EXISTS_TAC `[t]`
    ++ RW_TAC pset_ss [algebra_embed_def]]);

val INDEP_SET_LIST = store_thm
  ("INDEP_SET_LIST",
   ``!q l. alg_sorted l /\ alg_prefixfree l /\ measurable q
           /\ (!x. MEM x l ==> indep_set (alg_embed x) q)
           ==> indep_set (algebra_embed l) q``,
   STRIP_TAC
   ++ Induct >> PSET_TAC [ALGEBRA_EMBED_BASIC, INDEP_SET_BASIC]
   ++ RW_TAC std_ss' [algebra_embed_def]
   ++ MATCH_MP_TAC INDEP_SET_DISJOINT_DECOMP
   ++ PSET_TAC [MEM] <<
   [PROVE_TAC [ALG_SORTED_TL, ALG_PREFIXFREE_TL],
    REVERSE (Cases_on `algebra_embed l v`) >> PROVE_TAC []
    ++ MP_TAC (Q.SPECL [`l`, `v`] ALGEBRA_EMBED_MEM)
    ++ MP_TAC (Q.SPECL [`h`, `l`] ALG_PREFIXFREE_ELT)
    ++ RW_TAC std_ss' []
    ++ PROVE_TAC [ALG_EMBED_PREFIX]]);

val INDEP_INDEP_SET = store_thm
  ("INDEP_INDEP_SET",
   ``!f (p:'a->bool) q.
       indep f /\ measurable q ==> indep_set (p o FST o f) (q o SND o f)``,
   RW_TAC std_ss' [indep_def, o_DEF]
   ++ RW_TAC std_ss' []
   ++ RW_TAC std_ss' [GSYM o_DEF, o_ASSOC, ALG_COVER_HEAD]
   ++ MATCH_MP_TAC INDEP_SET_LIST
   ++ RW_TAC std_ss' [] <<
   [PROVE_TAC [alg_cover_set_def, ALG_SORTED_FILTER],
    PROVE_TAC [alg_cover_set_def, ALG_PREFIXFREE_FILTER],
    RW_TAC std_ss' [ALG_COVER_TAIL_MEASURABLE],
    RW_TAC std_ss' [indep_set_def, ALG_COVER_TAIL_MEASURABLE, measurable_def]
    >> (Q.EXISTS_TAC `[x]` ++ PSET_TAC [algebra_embed_def])
    ++ MP_TAC (Q.SPEC `l` INDEP_INDEP_SET_LEMMA)
    ++ MP_TAC (Q.SPEC `l` ALG_COVER_TAIL_PROB)
    ++ ASM_REWRITE_TAC []
    ++ DISCH_THEN (fn th => DISCH_THEN (MP_TAC o Q.SPEC `q`)
		   ++ MP_TAC (Q.SPEC `q` th))
    ++ ASM_REWRITE_TAC []
    ++ DISCH_THEN (fn th => REWRITE_TAC [th])
    ++ DISCH_THEN (MP_TAC o Q.SPEC `x`)
    ++ KNOW_TAC `MEM x l` >> PROVE_TAC [MEM_FILTER]
    ++ RW_TAC std_ss' [PROB_ALG]]);

val INDEP_UNIT = store_thm
  ("INDEP_UNIT",
   ``!(x:'a). indep (UNIT x)``,
   RW_TAC std_ss' [indep_def]
   ++ Q.EXISTS_TAC `[[]]`
   ++ Q.EXISTS_TAC `K x`
   ++ RW_TAC std_ss' [ALG_COVER_SET_BASIC, ALG_COVER_UNIV, K_DEF, UNIT_DEF,
		     SDROP_def, LENGTH, I_THM]);

val SDROP_def' = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV SDROP_def
val INDEP_SDEST = store_thm
  ("INDEP_SDEST",
   ``indep SDEST``,
   RW_TAC std_ss' [indep_def, SDEST_def]
   ++ Q.EXISTS_TAC `[[T]; [F]]`
   ++ Q.EXISTS_TAC `HD`
   ++ MP_TAC (Q.SPEC `[[T]; [F]]` ALG_COVER_WELL_DEFINED)
   ++ REWRITE_TAC [ALG_COVER_SET_BASIC]
   ++ NTAC 2 STRIP_TAC
   ++ POP_ASSUM (MP_TAC o Q.SPEC `s`)
   ++ SEQ_CASES_TAC `s`
   ++ STRIP_TAC
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ REWRITE_TAC [MEM, SHD_SCONS, STL_SCONS]
   ++ (STRIP_TAC ++ RW_TAC std_ss' [alg_embed_def, SHD_SCONS, HD, LENGTH,
				   SDROP_def', o_DEF, I_THM, STL_SCONS]));

val BIND_STEP = store_thm
  ("BIND_STEP",
   ``!(f:(num->bool)->'a#(num->bool)).
       BIND SDEST (\k. f o SCONS k) = f``,
   RW_TAC std_ss' [BIND_DEF, o_DEF, GSYM EQ_EXT_EQ, SDEST_def]
   ++ SEQ_CASES_TAC `x`
   ++ RW_TAC std_ss' [SHD_SCONS, STL_SCONS]);

val INDEP_BIND_SDEST = store_thm
  ("INDEP_BIND_SDEST",
   ``!(f:bool->(num->bool)->'a#(num->bool)).
       (!x. indep (f x)) ==> indep (BIND SDEST f)``,
   RW_TAC std_ss' [indep_def, SDEST_def]
   ++ POP_ASSUM (fn th => MP_TAC (Q.SPEC `T` th) ++ MP_TAC (Q.SPEC `F` th))
   ++ RW_TAC std_ss' []
   ++ Q.EXISTS_TAC `APPEND (MAP (CONS T) l') (MAP (CONS F) l)`
   ++ Q.EXISTS_TAC `\l. if HD l then r' (TL l) else r (TL l)`
   ++ RW_TAC std_ss' [] <<
   [ONCE_REWRITE_TAC [ALG_COVER_SET_CASES_THM] ++ PROVE_TAC [],
    SEQ_CASES_TAC `s`
    ++ POP_ASSUM MP_TAC
    ++ RW_TAC std_ss' [ALG_COVER_STEP, HD]
    ++ RW_TAC std_ss' [BIND_DEF, o_DEF, TL, LENGTH, SDROP_def, STL_SCONS,
                      SHD_SCONS],
    SEQ_CASES_TAC `s`
    ++ POP_ASSUM MP_TAC
    ++ RW_TAC std_ss' [ALG_COVER_STEP, HD]
    ++ RW_TAC std_ss' [BIND_DEF, o_DEF, TL, LENGTH, SDROP_def, STL_SCONS,
                      SHD_SCONS]]);

val INDEP_BIND = store_thm
  ("INDEP_BIND",
   ``!f (g:'a->(num->bool)->'b#(num->bool)).
       indep f /\ (!x. indep (g x)) ==> indep (BIND f g)``,
   RW_TAC std_ss' [indep_def]
   ++ KNOW_TAC `f = \s. (r (alg_cover l s),SDROP (LENGTH (alg_cover l s)) s)`
   >> (ONCE_REWRITE_TAC [GSYM EQ_EXT_EQ] ++ RW_TAC std_ss' [])
   ++ RW_TAC std_ss' []
   ++ Q.PAT_ASSUM `!s. f s = P s` (K ALL_TAC)
   ++ Q.SPEC_TAC (`r`, `r`)
   ++ Q.PAT_ASSUM `alg_cover_set l` MP_TAC
   ++ Q.SPEC_TAC (`l`, `l`)
   ++ HO_MATCH_MP_TAC ALG_COVER_SET_INDUCTION
   ++ CONJ_TAC <<
   [RW_TAC std_ss' []
    ++ POP_ASSUM (MP_TAC o Q.SPEC `r ([]:bool list)`)
    ++ RW_TAC std_ss' [BIND_DEF, o_DEF, ALG_COVER_UNIV, K_DEF, LENGTH, SDROP_def,
                      I_THM],
    Q.X_GEN_TAC `l1` ++ Q.X_GEN_TAC `l2`
    ++ RW_TAC std_ss' []
    ++ SUFF_TAC `indep (BIND (\s. let c = alg_cover (APPEND (MAP (CONS T) l1)
      (MAP (CONS F) l2)) s in (r c, SDROP (LENGTH c) s)) g)`
    >> RW_TAC std_ss' [indep_def]
    ++ (CONV_TAC o RAND_CONV o RATOR_CONV o RAND_CONV o REWR_CONV o GSYM)
       BIND_STEP
    ++ REWRITE_TAC [GSYM BIND_ASSOC]
    ++ MATCH_MP_TAC INDEP_BIND_SDEST
    ++ RW_TAC std_ss' [indep_def]
    ++ RW_TAC std_ss' [BIND_DEF, o_DEF, ALG_COVER_STEP]
    ++ Cases_on `x` <<
    [RW_TAC std_ss' [LENGTH, SDROP_def, STL_SCONS, o_DEF]
     ++ POP_ASSUM (K ALL_TAC)
     ++ POP_ASSUM (K ALL_TAC)
     ++ POP_ASSUM (MP_TAC o Q.SPEC `r o CONS T`)
     ++ RW_TAC std_ss' [BIND_DEF, o_DEF],
     RW_TAC std_ss' [LENGTH, SDROP_def, STL_SCONS, o_DEF]
     ++ POP_ASSUM (K ALL_TAC)
     ++ POP_ASSUM (MP_TAC o Q.SPEC `r o CONS F`)
     ++ POP_ASSUM (K ALL_TAC)
     ++ RW_TAC std_ss' [BIND_DEF, o_DEF]]]);

val INDEP_PROB = store_thm
  ("INDEP_PROB",
   ``!(f:(num->bool)->'a#(num->bool)) p q.
       indep f /\ measurable q
       ==> (prob (p o FST o f INTER q o SND o f)
            = prob (p o FST o f) * prob q)``,
   RW_TAC std_ss' []
   ++ MP_TAC (Q.SPECL [`f`, `p`, `q`] INDEP_INDEP_SET)
   ++ RW_TAC std_ss' [indep_set_def]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss' [indep_def, o_DEF]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss' []
   ++ MP_TAC (Q.SPECL [`l`] ALG_COVER_TAIL_PROB)
   ++ RW_TAC std_ss' [o_DEF]);

val INDEP_MEASURABLE1 = store_thm
  ("INDEP_MEASURABLE1",
   ``!(f:(num->bool)->'a#(num->bool)) p.
       indep f ==> measurable (p o FST o f)``,
   RW_TAC std_ss' [indep_def]
   ++ RW_TAC std_ss' [o_DEF]
   ++ RW_TAC std_ss' [GSYM o_DEF, o_ASSOC]
   ++ RW_TAC std_ss' [ALG_COVER_HEAD]
   ++ RW_TAC std_ss' [MEASURABLE_ALGEBRA]);

val INDEP_MEASURABLE2 = store_thm
  ("INDEP_MEASURABLE2",
   ``!(f:(num->bool)->'a#(num->bool)) q.
       indep f /\ measurable q ==> measurable (q o SND o f)``,
   RW_TAC std_ss' [indep_def]
   ++ RW_TAC std_ss' [o_DEF]
   ++ MP_TAC (Q.SPEC `l` ALG_COVER_TAIL_MEASURABLE)
   ++ RW_TAC std_ss' [o_DEF]);

val PROB_INDEP_BOUND = store_thm
  ("PROB_INDEP_BOUND",
   ``!f n. indep f
       ==> (prob (\s. FST (f s) < SUC n)
            = prob (\s. FST (f s) < n) + prob (\s. FST (f s) = n))``,
   RW_TAC std_ss' []
   ++ KNOW_TAC `(\s. FST (f s) < SUC n)
                = (\s. FST (f s) < n) UNION (\s. FST (f s) = n)`
   >> (PSET_TAC [] ++ RW_TAC arith_ss [])
   ++ KNOW_TAC `(\s. FST (f s) < n) = (\m. m < n) o FST o f`
   >> RW_TAC std_ss' [o_DEF]
   ++ KNOW_TAC `(\s. FST (f s) = n) = (\m. m = n) o FST o f`
   >> RW_TAC std_ss' [o_DEF]
   ++ ASM_REWRITE_TAC []
   ++ MATCH_MP_TAC PROB_ADDITIVE
   ++ NTAC 3 (POP_ASSUM (K ALL_TAC))
   ++ RW_TAC std_ss' [INDEP_MEASURABLE1]
   ++ PSET_TAC [o_DEF]
   ++ RW_TAC arith_ss []);

val _ = export_theory ();
